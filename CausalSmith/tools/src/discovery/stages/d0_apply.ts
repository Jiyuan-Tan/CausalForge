// Apply D0-SOLVE proposed changes to the frozen proto + record an escalation entry.
//
// Shared by the CLI (`bin/d0_apply_change.ts`, human-driven) and the automated D0
// revise loop (`runStage0SolveLoop`). Applying a change edits the FROZEN PROTO (the
// spec the next solve reads), appends an escalation-log entry (so the next solve sees
// what changed / why), and clears the stale round outputs while KEEPING the incremental
// working state (carried proofs). The hybrid auto/gate partition lives in the loop;
// this module just executes an already-decided set of changes.
import { existsSync } from "node:fs";
import { readFile, writeFile, rm, readdir, rename } from "node:fs/promises";
import path from "node:path";
import { artifactPath, statePath } from "../../paths.js";
import { loadState, saveState } from "../../state.js";
import type { PipelineContext } from "../../types.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import { coreJsonPath } from "./d0_core.js";
import {
  hotProofBytes,
  appendEscalationLog,
  loadWorkingState,
  memberValid,
  saveWorkingState,
  snapshotMember,
  type EscalationLogEntry,
  type WorkingState,
} from "./d0_working.js";
import {
  CoreSchema,
  type Core,
  type CoreAssumption,
  type CoreDefinition,
  type CoreStatement,
  type CoreSymbol,
} from "../core/schema.js";
import { archiveProofs, proofBytesInRoundFile, type ProofToArchive } from "../proof_archive.js";
import { proofContentClosureIntersects, rebuildAssumptionUsedBy } from "../core/dependencies.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairCoreLatexSerialization,
} from "../core/latex_serialization.js";
import { extractNodeRefs } from "../core/node_ids.js";
import { findAuthoredNodeReferences, type AuthoredNodeReference } from "../core/text_references.js";

export interface RawChange {
  id: string;
  current?: string;
  proposed: string;
  reason?: string;
  direction?: string;
}

/** A solver-proposed NEW assumption (a single law/estimator condition the proof needs).
 *  Flows through the same auto/gate loop as statement/def changes (applied to the proto,
 *  pending approval). `standard_or_novel` is the solver's freeform tag, parsed below. */
export interface RawAssumption {
  id: string;
  condition: string;
  reason?: string;
  standard_or_novel?: string;
  not_crux?: string;
}

/** Typed frozen-core edits that cannot be expressed as a claim-only statement
 * narrowing or construction-only definition correction. Every replacement is a
 * complete schema-valid node; deletion and metadata rebuild are explicit variants. */
export type RawCoreEdit =
  | { kind: "assumption-replace"; id: string; proposed: CoreAssumption; reason?: string; direction: "correct" }
  | { kind: "assumption-delete"; id: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "statement-replace"; id: string; proposed: Omit<CoreStatement, "proof_tex">; reason?: string; direction: "correct" }
  | { kind: "statement-delete"; id: string; replacement_id?: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "definition-add"; id: string; proposed: CoreDefinition; reason?: string; direction: "correct" }
  | { kind: "definition-replace"; id: string; proposed: CoreDefinition; reason?: string; direction: "correct" }
  | { kind: "definition-delete"; id: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "bibliography-replace"; key: string; proposed: { key: string; citation?: string }; reason?: string; direction: "correct" }
  | { kind: "symbol-add"; name: string; proposed: CoreSymbol; reason?: string; direction: "correct" }
  | { kind: "symbol-replace"; name: string; proposed: CoreSymbol; reason?: string; direction: "correct" }
  | { kind: "symbol-delete"; name: string; reason?: string; direction: "delete-obsolete" }
  | { kind: "rebuild-reverse-dependencies"; id: "metadata:reverse-dependencies"; reason?: string; direction: "correct" };

export function coreEditTarget(edit: RawCoreEdit): string {
  if (edit.kind === "bibliography-replace") return `bib:${edit.key}`;
  if (edit.kind === "symbol-add" || edit.kind === "symbol-replace" || edit.kind === "symbol-delete") return `sym:${edit.name}`;
  return edit.id;
}

/** Literal references that make deleting/remapping a node a claim/proof edit rather
 * than a graph edit. The working record's `proof_tex` is scanned separately because
 * frozen proto members keep their durable proof there, not on the proto statement. */
export function findUnsafeDeleteTextReferences(
  proto: Core,
  working: WorkingState | null,
  targetId: string,
): AuthoredNodeReference[] {
  const refs = findAuthoredNodeReferences(proto, targetId, { excludeNodeId: targetId });
  const target = targetId.toLowerCase();
  const seen = new Set(refs.map((ref) => ref.location));
  const add = (location: string, text: string | undefined): void => {
    if (!text || seen.has(location) || !extractNodeRefs(text).includes(target)) return;
    seen.add(location);
    refs.push({ location, text });
  };
  for (const [id, rec] of Object.entries(working?.solved ?? {})) {
    if (id === targetId) continue;
    if (rec.node) {
      add(`working.${id}.node.statement`, rec.node.statement);
      add(`working.${id}.node.proof_tex`, rec.node.proof_tex);
      add(`working.${id}.node.route`, rec.node.route);
      add(`working.${id}.node.justification`, rec.node.justification);
      add(`working.${id}.node.gap`, rec.node.gap);
      add(`working.${id}.node.consumer`, rec.node.consumer);
      add(`working.${id}.node.source.verbatim_statement`, rec.node.source?.verbatim_statement);
    }
    add(`working.${id}.proof_tex`, rec.proof_tex);
  }
  return refs;
}

/**
 * Why a `statement-replace` echo failed, or `null` when it matches.
 *
 * `statement-replace` is a DEPENDENCY/METADATA-only channel: it requires `kind`,
 * `statement`, and `status` to echo the node's CURRENT values byte-for-byte, and composes the final
 * node from the carried values. Proof text is deliberately absent from this channel:
 * requiring a model to reproduce a long LaTeX proof solely to discard it made valid
 * dependency rewiring effectively unappliable.
 *
 * That silent skip cost three solve rounds on 2026-07-19. The bundle guard caught the
 * drop — it refuses a partial apply — but reported only a COUNT ("selected 2, only 1
 * applicable"), so diagnosing it meant reading this source and hand-comparing fields.
 * The solver had bundled a re-proof into the edit: first sending `status: "to-prove"`
 * against a `proved` node, then `status: "proved"` plus a new proof against a `to-prove`
 * one. Naming the offending field turns that into one line of output.
 */
export function describeEchoMismatch(
  proposed: { id: string; kind?: string; statement?: string; status?: string },
  current: { id: string; kind?: string; statement?: string; status?: string },
  editId: string,
): string | null {
  if (proposed.id !== editId) return `payload id '${proposed.id}' does not match the edit target '${editId}'`;
  if (proposed.kind !== current.kind) {
    return `kind must echo the node's current value '${current.kind}', got '${proposed.kind}' ` +
      "(this channel is dependency/metadata-only)";
  }
  if (proposed.statement !== current.statement) {
    return "statement must echo the node's current text byte-for-byte (claim text changes go through proposed_statement_changes)";
  }
  if (proposed.status !== current.status) {
    return `status must echo the node's current value '${current.status}', got '${proposed.status}' ` +
      "(this channel cannot change status; a paired proof in `proofs` does that)";
  }
  return null;
}

const CORE_EDIT_KINDS = [
  "assumption-replace",
  "assumption-delete",
  "statement-replace",
  "statement-delete",
  "definition-add",
  "definition-replace",
  "definition-delete",
  "bibliography-replace",
  "symbol-add",
  "symbol-replace",
  "symbol-delete",
  "rebuild-reverse-dependencies",
] as const;

/** The four proposal CHANNELS a round can carry. A single node id can appear in more
 *  than one of them in the same round — a claim change on `thm:x` and a metadata-only
 *  `statement-replace` on `thm:x` are independent proposals that happen to share a
 *  target — which is precisely why a selector needs a channel as well as an id. */
const CHANNEL_QUALIFIERS = ["statement", "definition", "assumption", "core-edit"] as const;

/** Resolves `--ids`/`--id` selectors against proposal variants, and remembers which
 *  selectors actually matched something so the caller can name the ones that did not.
 *
 *  A selector is either a BARE id (`thm:x`) — which matches that id in EVERY channel,
 *  preserving the original behaviour — or a KIND-QUALIFIED id, written `<qualifier>:<id>`:
 *
 *    statement:thm:x           the claim-text change on thm:x, and nothing else
 *    core-edit:thm:x           any typed core edit targeting thm:x
 *    statement-replace:thm:x   only the statement-replace core edit on thm:x
 *    bibliography-replace:bib:K   only that bibliography edit
 *
 *  Qualifiers are unambiguous because no node id begins with one: statement/definition/
 *  assumption ids are `(thm|lem|prop|conj|oeq|def|ass):…`, and the synthetic core-edit
 *  targets are `bib:…`, `sym:…`, `metadata:…`. Parsing splits on the FIRST colon only,
 *  so the id half keeps its own colons. */
export interface ProposalSelector {
  matchesStatement(id: string): boolean;
  matchesDefinition(id: string): boolean;
  matchesAssumption(id: string): boolean;
  matchesCoreEdit(edit: RawCoreEdit): boolean;
  /** Selectors that matched no proposal variant in any channel. */
  unmatched(): string[];
}

type ParsedSelector = { raw: string; channel: (typeof CHANNEL_QUALIFIERS)[number] | null; editKind: string | null; id: string };

function parseOneSelector(raw: string): ParsedSelector {
  const colon = raw.indexOf(":");
  if (colon > 0) {
    const head = raw.slice(0, colon);
    const rest = raw.slice(colon + 1);
    if (rest.length > 0) {
      if ((CHANNEL_QUALIFIERS as readonly string[]).includes(head)) {
        return { raw, channel: head as ParsedSelector["channel"], editKind: null, id: rest };
      }
      if ((CORE_EDIT_KINDS as readonly string[]).includes(head)) {
        return { raw, channel: "core-edit", editKind: head, id: rest };
      }
    }
  }
  return { raw, channel: null, editKind: null, id: raw };
}

/** Reject a qualified selector whose id half is itself qualified (`statement:core-edit:thm:x`).
 *  Such a selector can never match, and silently treating it as unmatched hides a typo behind
 *  the generic "matched no proposal" error. */
export function validateProposalSelectors(raw: Iterable<string>): string[] {
  const bad: string[] = [];
  for (const s of raw) {
    const parsed = parseOneSelector(s);
    if (parsed.channel === null) continue;
    const inner = parseOneSelector(parsed.id);
    if (inner.channel !== null) bad.push(s);
  }
  return bad;
}

export function parseProposalSelectors(raw: Iterable<string>): ProposalSelector {
  const parsed = [...raw].map(parseOneSelector);
  const hit = new Set<string>();
  const match = (p: ParsedSelector, channel: ParsedSelector["channel"], id: string, editKind?: string): boolean => {
    if (p.id !== id) return false;
    if (p.channel !== null && p.channel !== channel) return false;
    if (p.editKind !== null && p.editKind !== editKind) return false;
    return true;
  };
  const any = (channel: ParsedSelector["channel"], id: string, editKind?: string): boolean => {
    let found = false;
    for (const p of parsed) {
      if (!match(p, channel, id, editKind)) continue;
      hit.add(p.raw);
      found = true;
    }
    return found;
  };
  return {
    matchesStatement: (id) => any("statement", id),
    matchesDefinition: (id) => any("definition", id),
    matchesAssumption: (id) => any("assumption", id),
    matchesCoreEdit: (edit) => any("core-edit", coreEditTarget(edit), edit.kind),
    unmatched: () => parsed.filter((p) => !hit.has(p.raw)).map((p) => p.raw),
  };
}

function toSelector(ids: Set<string> | ProposalSelector | null | undefined): ProposalSelector | null {
  if (ids === null || ids === undefined) return null;
  return ids instanceof Set ? parseProposalSelectors(ids) : ids;
}

/** Parse a solver's freeform `standard_or_novel` tag into a gate-valid assumption tag
 *  (exactly one of {standard, novel}, G6). Defaults to `novel` when no bibliography KEY is
 *  recognized — safe, since `novel` needs no cite resolution; reclassified at approval. */
export function parseAssumptionTag(
  s: string | undefined,
  bibKeys: string[],
): { standard: { name: string; cite: string } } | { novel: { flag: true; justification: string } } {
  const text = (s ?? "").trim();
  if (/^standard/i.test(text)) {
    const key = bibKeys.find((k) => text.includes(k));
    if (key) return { standard: { name: text.replace(/^standard:?\s*/i, "").slice(0, 80) || "standard condition", cite: key } };
  }
  return { novel: { flag: true, justification: text || "solver-proposed (pending approval)" } };
}


import { readRoundProposals, emptyProposals } from "../solve/proposals.js";

export async function readProposedChanges(
  ctx: PipelineContext,
): Promise<{
  statements: RawChange[];
  definitions: RawChange[];
  assumptions: RawAssumption[];
  coreEdits: RawCoreEdit[];
  proofs: Array<{ id: string; proof_tex?: string }>;
}> {
  // Single accessor: `working.proposals` when present, legacy files otherwise.
  // Every consumer must see the SAME payload — reading a subset here is what let an
  // apply approve a statement change while discarding the proof written for it.
  const working = await loadWorkingState(ctx);
  const p = await readRoundProposals(ctx, working);
  return {
    statements: p.statements as RawChange[],
    definitions: p.definitions as RawChange[],
    assumptions: p.assumptions as RawAssumption[],
    coreEdits: p.coreEdits as RawCoreEdit[],
    proofs: p.proofs as Array<{ id: string; proof_tex?: string }>,
  };
}

/** Clear the stale round outputs (proposed-change files, assembled core, raw solve
 *  files); KEEP the working state + escalation log + proto. Proof bytes living only in
 *  the deleted files are copied to the cold archive first — see proof_archive.ts. */
export async function clearRoundOutputs(ctx: PipelineContext): Promise<void> {
  const dir = path.dirname(coreJsonPath(ctx));
  // Bytes still living in the working cursor are NOT displaced by deleting a raw file
  // that mirrors them — archiving them here would poison provenance (see hotProofBytes).
  const hot = hotProofBytes(await loadWorkingState(ctx));
  for (const f of await readdir(dir)) {
    if (
      /proposed_(statement|definition)_changes\.json$/.test(f) ||
      /proposed_assumptions\.json$/.test(f) ||
      /proposed_core_edits\.json$/.test(f) ||
      /proposed_proofs\.json$/.test(f) ||
      /proposal_review_packet\.json$/.test(f) ||
      /open_obligations\.json$/.test(f) ||
      // Per-round withheld-content diagnostic: stale copies presented a PREVIOUS
      // round's conflicts as current to the next inspector of the run directory.
      /withheld_content\.json$/.test(f) ||
      f === "core.json" ||
      f === `${ctx.qid}_core.json` ||
      /(^|_)solve_.*\.json$/.test(f)
    ) {
      // Only the raw payload channels can hold proof bytes that exist nowhere else
      // (withheld collisions, unmatched ids, duplicate re-proofs). core.json mirrors
      // the working cursor and the review packet mirrors `working.proposals`, so they
      // are not swept; and payloads that DID land in hot state are filtered out — the
      // archive records only bytes actually leaving hot state.
      if (/(^|_)solve_.*\.json$/.test(f) || /proposed_proofs\.json$/.test(f)) {
        const bytes = proofBytesInRoundFile(f, await readFile(path.join(dir, f), "utf8"))
          .filter((p) => !hot.get(p.nodeId)?.has(p.proofTex));
        if (bytes.length > 0) await archiveProofs(dir, bytes);
      }
      await rm(path.join(dir, f), { force: true });
    }
  }
}

/** Apply the selected statement/definition changes to the proto, append the escalation
 *  entry, clear stale outputs. `ids` selects which proposed changes to apply (null = all).
 *  Returns the changed entries (empty if nothing matched). */
export async function applyProposedChanges(args: {
  ctx: PipelineContext;
  /** Selection. A plain `Set` of raw selector strings is wrapped with the default
   *  parsing; pass a `ProposalSelector` when the caller also needs `unmatched()`. */
  ids?: Set<string> | ProposalSelector | null;
  note?: string;
  directive?: string;
  /** Validate the complete selected bundle in memory and return its change list
   * without mutating state, proto, working cursor, journal, or round outputs. */
  checkOnly?: boolean;
}): Promise<EscalationLogEntry["changed"]> {
  const { ctx, ids = null, note, directive, checkOnly = false } = args;
  const sel = toSelector(ids);
  const protoPath = protoCoreJsonPath(ctx);
  const protoBytesAtRead = await readFile(protoPath, "utf8");
  // Parse through the raw-byte normalizer so a legacy proto persisted with an
  // under-escaped TeX escape (`"\theta"`) decodes to the intended backslash form.
  // `protoBytesAtRead` itself stays raw: the stale-write check below compares bytes.
  const proto = CoreSchema.parse(JSON.parse(normalizeRawModelJson(protoBytesAtRead))) as Core;
  // Canonicalize the frozen comparison basis before any `current` echo/staleness
  // checks. Legacy/model-authored JSON can decode `\texttt` as U+0009 + `exttt`;
  // the solver sees and re-emits the intended TeX spelling, so comparing before
  // repair falsely labels the proposal stale. The normalized proto is persisted
  // by the ordinary successful apply below.
  repairCoreLatexSerialization(proto);
  const working = await loadWorkingState(ctx);
  const stmtById = new Map(proto.statements.map((s) => [s.id, s]));
  const defById = new Map(proto.definitions.map((d) => [d.id, d]));
  const assIds = new Set(proto.assumptions.map((a) => a.id));
  const bibKeys = (proto.bibliography ?? []).map((b) => b?.key).filter((k): k is string => typeof k === "string");
  const proposals = await readProposedChanges(ctx);
  const dedupe = <T>(values: T[]): T[] => {
    const seen = new Set<string>();
    return values.filter((value) => {
      const key = JSON.stringify(value);
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  };
  const statements = dedupe(proposals.statements);
  const definitions = dedupe(proposals.definitions);
  const assumptions = dedupe(proposals.assumptions);
  const coreEdits = dedupe(proposals.coreEdits);
  // A `statement-replace` changes dependencies/metadata but — by its statement/status
  // echo requirement — never the claim text. When the SAME round also emits a proof for that
  // node, the solver wrote that proof against exactly this rewiring, in one unit, in one
  // output. Landing the edit while discarding its paired proof marks the node `partial`
  // and spends a whole solve round re-confirming a proof that was already correct for the
  // statement it is attached to. Commit them together instead.
  //
  // Deliberately NOT extended to `proposed_statement_changes`: those change the CLAIM, and
  // a unit owes "a proof OR a proposed change" per target, so a proof present in the same
  // round was written against the OLD text. That pairing would certify a proof against a
  // claim it never saw — which is the exact substitution the snapshot invariant exists to
  // catch. Claim changes stay partial.
  // A paired proof may only clear `partial` if the closure it now rests on is itself
  // sound after THIS apply. Two ways it would not be: the rewiring points at a node that
  // is itself partial this round, or the orchestrator accepted this edit while rejecting
  // another the new proof relies on (an apply-subset). `computeValidNodes` would re-stale
  // the node at the next solve either way — staleness propagates along `depends_on` to a
  // fixpoint — so this guard is not the only line of defence, but asserting validity we
  // have not checked is the wrong default when the whole point of the flag is to certify.
  // Definition/assumption corrections this bundle PROPOSED but is not applying. A proof
  // emitted in the same round was written against the CORRECTED formula, so settling it
  // when the operator accepted the statement edit and rejected the correction rests it on
  // content that never changed. Selection is per-id, so this is reachable with `--ids`.
  //
  // Covers ALL THREE channels a support correction can arrive through: the raw definition
  // and assumption change lists, AND typed core edits (definition-add/replace/delete,
  // assumption-replace). Omitting the core-edit channel left the same hole this guard was
  // written to close -- three auditors flagged it independently.
  const rejectedSupportIds = new Set<string>([
    ...definitions.filter((c) => sel && !sel.matchesDefinition(c.id)).map((c) => c.id),
    ...assumptions.filter((a) => sel && !sel.matchesAssumption(a.id)).map((a) => a.id),
    ...coreEdits
      .filter((e) => sel && !sel.matchesCoreEdit(e))
      .filter((e) => e.kind.startsWith("definition-") || e.kind.startsWith("assumption-"))
      .map((e) => coreEditTarget(e)),
    // A CITED node's `source` is support too: a proof written against a corrected locator
    // rests on that correction. A statement-replace carrying a new `source` is therefore a
    // fourth channel, and rejecting it while accepting the consumer settles the proof
    // against the locator it was written to replace.
    ...coreEdits
      .filter((e) => sel && !sel.matchesCoreEdit(e))
      .filter((e): e is Extract<RawCoreEdit, { kind: "statement-replace" }> => e.kind === "statement-replace")
      .filter((e) => {
        const current = proto.statements.find((st) => st.id === e.id);
        return current?.status === "cited" &&
          JSON.stringify(current.source ?? null) !== JSON.stringify(e.proposed?.source ?? null);
      })
      .map((e) => e.id),
  ]);
  // KNOWN GAP, deliberately not closed: a correction rejected on def:inner is not detected
  // when a consumer reaches it only through def:outer's `inputs`. A transitive closure over
  // the definition graph was implemented and REVERTED. It introduced a dependency notion --
  // statement/definition ids reachable through definition inputs -- that nothing else in
  // the pipeline implements, and the next audit round demanded that notion be honoured by
  // pruneOrphanLemmas, computeValidNodes and snapshotMember too, while disagreeing with
  // itself about whether the closure should read the pre- or post-apply definition graph
  // (using the old graph rejects proofs that an accepted rewiring has just made valid).
  //
  // A guard with one documented level of indirection missing is better than a guard that
  // asserts an invariant the rest of the system does not hold. Closing this properly means
  // giving definitions a first-class dependency edge everywhere, which is a design change,
  // not a patch.
  const dependencyClosureValid = (node: CoreStatement): boolean =>
    (node.depends_on ?? []).every((dep) => {
      // A REJECTED correction invalidates the proof whatever KIND of node it sits on. This
      // test was inside the def:/ass: branch only, so adding cited statement ids to the set
      // produced a guard that could never read them -- the same cannot-fire shape this
      // sweep kept finding elsewhere. Check it for every dependency first.
      if (rejectedSupportIds.has(dep)) return false;
      if (dep.startsWith("def:") || dep.startsWith("ass:")) {
        return true; // otherwise carried in the snapshot itself
      }
      // A FROZEN dependency used to pass on existence alone, while an agent dependency had
      // to carry a non-partial record. But a frozen member's proof lives in the WORKING
      // cursor, not in the proto -- so an unproved or partial frozen dependency was treated
      // as discharged, and its consumer's `partial` flag was cleared on that basis.
      // A `cited` frozen node is genuinely self-discharged: its justification is the
      // citation, so it needs no working proof.
      const frozen = proto.statements.find((s) => s.id === dep);
      const rec = working?.solved[dep];
      // `partial` OUTRANKS the cited exemption: a cited leaf carrying a partial record is
      // awaiting revalidation of its claim or source (that is exactly how a reopened cited
      // node is represented), so it is not discharged yet.
      if (rec?.partial) return false;
      if (frozen?.status === "cited") return true;
      return rec !== undefined && !rec.partial;
    });
  const pairedProofById = new Map(
    (proposals.proofs ?? [])
      .filter((p) => typeof p?.id === "string" && (p.proof_tex ?? "").trim().length > 0)
      .map((p) => [
        p.id,
        {
          proofTex: p.proof_tex as string,
          arguesProposed: (p as { argues_proposed?: unknown }).argues_proposed === true,
        },
      ] as const),
  );
  // Dedupe is keyed on CONTENT, so two proposals for the SAME id with DIFFERENT
  // proposed text both survive it, both apply in sequence (last writer wins on the
  // proto), and — because each contributes equally to the selected and applied
  // counts — the atomicity guard below cannot detect it. Silently applying the
  // second of two conflicting edits to one node is exactly the kind of unlogged
  // divergence that made core.json and proto_core.json disagree. Refuse instead.
  //
  // The guard covered `statements` and `definitions` only, leaving three channels where
  // the same silent last-writer-wins was still reachable: two PROOFS for one id collapse
  // in the Map built above, and two ASSUMPTIONS or two CORE EDITS on one target apply in
  // array order. Every channel that keys by id needs it.
  for (const [label, keys] of [
    ["statement", statements.filter((c) => !sel || sel.matchesStatement(c.id)).map((c) => c.id)],
    ["definition", definitions.filter((c) => !sel || sel.matchesDefinition(c.id)).map((c) => c.id)],
    ["assumption", assumptions.filter((a) => !sel || sel.matchesAssumption(a.id)).map((a) => a.id)],
    ["proof", (proposals.proofs ?? [])
      .filter((p) => typeof p?.id === "string" && (p.proof_tex ?? "").trim().length > 0)
      .map((p) => p.id)],
    // Keyed by KIND+target: a statement-replace and a rebuild on one node are independent
    // and legitimate; two statement-replaces on it are not. `rebuild-reverse-dependencies`
    // is exempt — it is idempotent, so repeats are harmless whatever their stated reason.
    // Keyed by KIND+target so a statement-replace and a metadata rebuild on one node stay
    // independent. But DIFFERENT kinds can also be mutually exclusive -- a replace and a
    // delete, or an add and a replace, on the same object -- and those keys differ, so both
    // applied in array order and the later silently erased the earlier while the
    // selected-vs-applied count still matched. Collapse the mutually exclusive kinds onto
    // one key per target so any two of them conflict.
    ["core-edit", coreEdits
      .filter((e) => !sel || sel.matchesCoreEdit(e))
      .filter((e) => e.kind !== "rebuild-reverse-dependencies")
      .map((e) => {
        const EXCLUSIVE: Record<string, string> = {
          "statement-replace": "statement", "statement-delete": "statement",
          "definition-add": "definition", "definition-replace": "definition",
          "definition-delete": "definition",
          "symbol-add": "symbol", "symbol-replace": "symbol", "symbol-delete": "symbol",
          "assumption-replace": "assumption", "assumption-delete": "assumption",
        };
        return `${EXCLUSIVE[e.kind] ?? e.kind}:${coreEditTarget(e)}`;
      })],
  ] as const) {
    const byId = new Map<string, number>();
    for (const k of keys) byId.set(k, (byId.get(k) ?? 0) + 1);
    const conflicted = [...byId.entries()].filter(([, n]) => n > 1).map(([id]) => id);
    if (conflicted.length > 0) {
      throw new Error(
        `Refusing D0 apply: ${conflicted.length} ${label} id(s) carry MULTIPLE conflicting proposals ` +
          `(${conflicted.join(", ")}). Applying them in sequence would silently keep only the last. ` +
          `Resolve to one proposal per id before applying. Nothing was mutated.`,
      );
    }
  }
  const originalStatements = new Map(proto.statements.map((s) => [s.id, structuredClone(s)] as const));
  const originalCarriedStatements = new Map(
    Object.entries(working?.solved ?? {})
      .filter((entry): entry is [string, NonNullable<(typeof entry)[1]>] => entry[1] !== undefined)
      .flatMap(([id, rec]) => rec.node ? [[id, structuredClone(rec.node)] as const] : []),
  );
  const selectedVariantCount =
    statements.filter((c) => !sel || sel.matchesStatement(c.id)).length +
    definitions.filter((c) => !sel || sel.matchesDefinition(c.id)).length +
    assumptions.filter((a) => !sel || sel.matchesAssumption(a.id)).length +
    coreEdits.filter((edit) => !sel || sel.matchesCoreEdit(edit)).length;
  let workingChanged = false;

  /** Demote an adjudicated, reopened OEQ's former answer to an ordinary carried
   * theorem. The theorem record is intentionally untouched. */
  const detachResolvedOeq = (sourceId: string): void => {
    if (working?.resolved_oeqs?.[sourceId] === undefined) return;
    delete working.resolved_oeqs[sourceId];
    workingChanged = true;
  };

  const changed: EscalationLogEntry["changed"] = [];

  /** Selected edits dropped by a validation, with the clause that rejected them. */

  const skipped: Array<{ id: string; kind: string; why: string }> = [];
  // Ids whose CLAIM this bundle rewrites. A proof paired in the same bundle was written
  // against the OLD claim, so attaching it to the new one — and clearing `partial` — would
  // present a proof of one statement as a proof of another.
  const claimChangedIds = new Set<string>();
  // Cited leaves this bundle reopens (claim changed, citation kept). They MUST become
  // exact required targets of the next solve: the supported revalidation channel is a
  // byte-faithful `added_lemmas` re-emission, and the dispatcher only puts a reopened
  // cited node on the solve frontier when it is explicitly required — without this, a
  // solver-proposed narrowing (no referee escalation naming the node) leaves the leaf
  // partial with no round ever directed at it.
  const reopenedCitedIds: string[] = [];
  for (const c of statements) {
    if (sel && !sel.matchesStatement(c.id)) continue;
    const s = stmtById.get(c.id);
    if (!s) {
      // Agent-added nodes intentionally do not live in the frozen proposal proto.
      // Their durable definition is the carried working-state node, independently
      // of whether its current proof is complete. Apply the correction there and
      // mark the proof partial so the next D0 assembly re-proves the new claim.
      const carried = working?.solved[c.id];
      const node = carried?.node;
      if (!carried || !node || node.id !== c.id) {
        skipped.push({ id: c.id, kind: "statement-change", why: "no carried node for this id in the working cursor" });
        continue;
      }
      if (c.current !== undefined && c.current !== originalCarriedStatements.get(c.id)?.statement) {
        // A stale proposal: the node moved since this change was generated. Applying it
        // would silently discard whatever moved it. Record the drop so the bundle guard
        // can name it instead of failing with a bare count.
        skipped.push({
          id: c.id, kind: "statement-change",
          why: "stale proposal — `current` no longer matches the carried node's statement, so applying it would discard the intervening change",
        });
        continue;
      }
      const prior = node.statement;
      claimChangedIds.add(c.id);
      node.statement = c.proposed;
      node.proof_tex = undefined;
      if (node.source !== undefined) {
        // A cited node awaiting source/claim revalidation remains a schema-valid
        // cited leaf in the durable catalog; `partial` carries the invalidation.
        // Encoding it as to-prove while retaining source violates G-cited and can
        // poison interruption recovery before the solver re-emits the citation.
        node.status = "cited";
        reopenedCitedIds.push(c.id);
      } else {
        node.status = "to-prove";
      }
      carried.node = node;
      // Deliberately NOT re-snapshotting: the record's bytes argued the PREVIOUS claim,
      // and the old-basis snapshot is what lets dispatch label them as such (mirroring
      // the frozen branch). `partial` alone carries the invalidation; the snapshot is
      // rewritten when a proof of the new claim lands.
      carried.partial = true;
      workingChanged = true;
      changed.push({
        id: c.id,
        kind: "statement",
        from: prior,
        to: c.proposed,
        reason: c.reason ?? "",
      });
      continue;
    }
    // FROZEN statements got no echo check while carried nodes did (above). A proposal
    // generated when the node said X, applied after it moved to Y, overwrote Y with the
    // proposal's text and the intervening change was lost with no error anywhere. Same
    // guard, same reporting, both branches.
    if (c.current !== undefined && c.current !== s.statement) {
      skipped.push({
        id: c.id, kind: "statement-change",
        why: "stale proposal — `current` no longer matches the frozen proto statement, so applying it would discard the intervening change",
      });
      continue;
    }
    const priorFrozenStatement = s.statement;
    changed.push({ id: c.id, kind: "statement", from: priorFrozenStatement, to: c.proposed, reason: c.reason ?? "" });
    claimChangedIds.add(c.id);
    s.statement = c.proposed;
    // An accepted narrowing of a resolved OEQ is a role transition, not a theorem
    // deletion: the old answer no longer discharges the whole residual question, but
    // its own unchanged theorem/proof remains valid partial-result mathematics. Remove
    // only the source->answer replacement now, while the adjudicated narrowing and the
    // durable theorem record are both in hand. On the next assembly the theorem follows
    // the ordinary agent-node carry path and the narrowed OEQ reopens. Out-of-band or
    // legacy fingerprint mismatches remain conservative in `planCarry`.
    if (s.kind === "openendedquestion" && c.direction === "narrow") detachResolvedOeq(c.id);
    // REOPEN a settled frozen node. Only the statement text was rewritten, so a node that
    // was `proved` kept its old proof_tex and status — the previous proof, of the PREVIOUS
    // claim, presented as proving the new one. The carried-node branch above already
    // clears its proof on a claim change; this branch did not. Real protos carry settled
    // statements (12 proved and one cited across the repo, proofs up to ~2.9k chars), so
    // this is reachable, not theoretical.
    //
    // `cited` reopens too: the citation documents the claim as it stood, and `source` must
    // go with it or the node fails the schema's cited <=> source rule.
    if (s.status === "proved" || s.status === "cited") {
      if (s.status === "cited" && s.source !== undefined) {
        // MIRROR THE CARRIED BRANCH, which documents this: a cited node awaiting
        // revalidation stays a schema-valid cited leaf and `partial` on its working record
        // carries the invalidation. Converting it to `to-prove` and deleting `source`
        // destroys the only durable copy of the locator, so the next solve cannot even
        // re-check the citation -- it can only re-prove the result from scratch.
        s.proof_tex = undefined;
        reopenedCitedIds.push(c.id);
      } else {
        s.status = "to-prove";
        s.proof_tex = undefined;
      }
      // Either way the CURSOR must reopen: a frozen member's proof lives there, and it
      // argued the previous claim. The BYTES stay as the node's single hot partial
      // repair basis — a narrowing usually preserves most of the argument, and blanking
      // them both restarted the next round from nothing and lost them forever. The
      // record's snapshot deliberately keeps the OLD basis, so staleness reads correctly
      // and dispatch can label the partial as arguing a previous claim. `partial` alone
      // carries the invalidation (a partial record is never a reusable proof).
      const rec = working?.solved[c.id];
      if (rec) {
        rec.partial = true;
        workingChanged = true;
      } else if (working && s.status === "cited") {
        // A frozen CITED member normally has NO working record (a citation needs no
        // proof of ours), so the `partial` marker above had nothing to land on and the
        // OLD citation silently re-certified the NEW claim — the exact laundering the
        // reopen contract forbids. Seed the record the contract expects: an OLD-basis
        // snapshot (so dispatch labels it as arguing the previous claim) carrying
        // `partial`, which outranks the cited exemption at every discharge gate until
        // the byte-faithful revalidation receipt lands.
        working.solved[c.id] = {
          proof_tex: "",
          snapshot: snapshotMember(proto, { ...s, statement: priorFrozenStatement }),
          partial: true,
        };
        workingChanged = true;
      }
    }
  }
  for (const c of definitions) {
    if (sel && !sel.matchesDefinition(c.id)) continue;
    const d = defById.get(c.id);
    if (!d) {
      skipped.push({ id: c.id, kind: "definition-change", why: "no frozen proto definition with this id" });
      continue;
    }
    if (c.current !== undefined && c.current !== d.construction) {
      skipped.push({
        id: c.id, kind: "definition-change",
        why: "stale proposal — `current` no longer matches the definition's construction, so applying it would discard the intervening change",
      });
      continue;
    }
    changed.push({ id: c.id, kind: "definition", from: d.construction, to: c.proposed, reason: c.reason ?? "" });
    d.construction = c.proposed;
  }
  // NEW ASSUMPTIONS — add a solver-proposed assumption node to the proto (skip if it already
  // exists). Built as a gate-valid node (free_symbols:[] + a parsed standard/novel tag); the
  // escalation-log entry records it for approval-at-bank (the add-prove-approve-later trail).
  for (const a of assumptions) {
    if (sel && !sel.matchesAssumption(a.id)) continue;
    if (assIds.has(a.id)) {
      // Every selected-but-inapplicable variant must record WHY, or the partial-apply
      // refusal below fires with "No per-edit reason was recorded".
      skipped.push({ id: a.id, kind: "assumption", why: "an assumption with this id is already present in the frozen proto (no-op re-proposal)" });
      continue;
    }
    const node = { id: a.id, condition: a.condition, free_symbols: [], ...parseAssumptionTag(a.standard_or_novel, bibKeys) };
    proto.assumptions.push(node as (typeof proto.assumptions)[number]);
    assIds.add(a.id);
    changed.push({ id: a.id, kind: "assumption", from: "", to: a.condition, reason: a.reason ?? "" });
  }

  // Assumption deletion validates that every structured and authored reference has
  // already been removed. Evaluate it after the bundle's statement/definition/prose
  // repairs, independent of the model's array order; reverse-edge rebuild remains last.
  const orderedCoreEdits = [...coreEdits].sort((a, b) => {
    const rank = (edit: RawCoreEdit): number =>
      edit.kind === "rebuild-reverse-dependencies" ? 2 : edit.kind === "assumption-delete" ? 1 : 0;
    return rank(a) - rank(b);
  });
  for (const edit of orderedCoreEdits) {
    const target = coreEditTarget(edit);
    if (sel && !sel.matchesCoreEdit(edit)) continue;
    if (edit.kind === "assumption-replace") {
      const i = proto.assumptions.findIndex((a) => a.id === edit.id);
      if (i === -1 || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id,
          kind: "assumption-replace",
          why: i === -1 ? "no frozen assumption with this id" : `payload id '${edit.proposed.id}' does not match the edit target`,
        });
        continue;
      }
      changed.push({
        id: edit.id,
        kind: "assumption",
        from: JSON.stringify(proto.assumptions[i]),
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
      proto.assumptions[i] = edit.proposed;
    } else if (edit.kind === "assumption-delete") {
      const prior = proto.assumptions.find((a) => a.id === edit.id);
      if (!prior) {
        skipped.push({ id: edit.id, kind: "assumption-delete", why: "no frozen assumption with this id" });
        continue;
      }
      const inbound = proto.statements
        .filter((s) => s.depends_on.includes(edit.id))
        .map((s) => s.id);
      const carriedInbound = Object.entries(working?.solved ?? {})
        .filter(([, rec]) => rec.node?.depends_on.includes(edit.id))
        .map(([id]) => id);
      const textInbound = findUnsafeDeleteTextReferences(proto, working, edit.id);
      if (inbound.length > 0 || carriedInbound.length > 0 || textInbound.length > 0) {
        const locations = [
          ...inbound.map((id) => `${id}.depends_on`),
          ...carriedInbound.map((id) => `working.${id}.node.depends_on`),
          ...textInbound.map((ref) => ref.location),
        ];
        throw new Error(
          `Cannot delete assumption ${edit.id}: live premise references remain in ${[...new Set(locations)].join(", ")}. ` +
            "Remove the premise through explicit reviewed statement/definition/prose/proof edits in the same bundle; " +
            "assumption deletion never rewrites mathematical content implicitly.",
        );
      }
      proto.assumptions = proto.assumptions.filter((a) => a.id !== edit.id);
      assIds.delete(edit.id);
      rebuildAssumptionUsedBy(proto);
      changed.push({
        id: edit.id,
        kind: "assumption",
        from: JSON.stringify(prior),
        to: "<deleted>",
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "statement-replace") {
      const i = proto.statements.findIndex((s) => s.id === edit.id);
      const prior = proto.statements[i];
      if (i === -1) {
        const carried = working?.solved[edit.id];
        const carriedNode = carried?.node;
        const originalNode = originalCarriedStatements.get(edit.id);
        if (!carried || !carriedNode || !originalNode) {
          skipped.push({ id: edit.id, kind: "statement-replace", why: "no carried node for this id in the working cursor" });
          continue;
        }
        const mismatch = describeEchoMismatch(edit.proposed, originalNode, edit.id);
        if (mismatch) {
          skipped.push({ id: edit.id, kind: "statement-replace", why: mismatch });
          continue;
        }
        const composed = {
          ...edit.proposed,
          statement: carriedNode.statement,
          status: carriedNode.status,
          proof_tex: carriedNode.proof_tex,
        };
        changed.push({
          id: edit.id,
          kind: "statement",
          from: JSON.stringify(carriedNode),
          to: JSON.stringify(composed),
          reason: edit.reason ?? "",
        });
        const pairedCarried = pairedProofById.get(edit.id)?.proofTex;
        if (composed.status === "cited" && composed.source !== undefined && !claimChangedIds.has(edit.id)) {
          // A source-corrected cited leaf is discharged by the corrected source
          // object itself; converting it to `to-prove` both violates G-cited and
          // creates an unnecessary D0 re-solve loop.
          //
          // But NOT when this bundle also rewrote the claim. This branch runs BEFORE the
          // paired-proof guard below, so a cited node whose claim changed took the
          // shortcut, cleared `partial`, and was settled by a citation that certifies the
          // OLD statement. The claim-change guard added for paired proofs did not cover
          // it; three independent auditors caught that in the same pass.
          carried.node = composed;
          carried.proof_tex = composed.proof_tex ?? "";
          carried.snapshot = snapshotMember(proto, composed);
          delete carried.partial;
        } else if (
          pairedCarried !== undefined &&
          // Same rule as the frozen branch: a proof paired in a bundle that ALSO rewrites
          // this node's claim argues the old statement. Fall through to the open branch,
          // which keeps the node `to-prove` and partial so the next round re-derives it.
          !claimChangedIds.has(edit.id) &&
          dependencyClosureValid(composed)
        ) {
          const proved = { ...composed, status: "proved" as const, proof_tex: pairedCarried };
          carried.node = proved;
          carried.proof_tex = pairedCarried;
          carried.snapshot = snapshotMember(proto, proved);
          delete carried.partial;
        } else if (
          // A metadata-only replacement does not owe a re-proof when the theorem's
          // proof-relevant snapshot is byte-for-byte unchanged. Previously even a
          // consumer/gap/route edit converted a finished agent theorem into partial
          // debt solely because no redundant paired proof was emitted.
          composed.status === "proved" &&
          (carried.proof_tex ?? "").trim().length > 0 &&
          memberValid(working, proto, composed) &&
          dependencyClosureValid(composed)
        ) {
          carried.node = { ...composed, proof_tex: carried.proof_tex };
          carried.snapshot = snapshotMember(proto, composed);
          delete carried.partial;
        } else {
          // Reopening a CITED node must drop `source` too: the schema ties
          // cited <=> source, so `to-prove` with a surviving source is invalid.
          carried.node = { ...composed, status: "to-prove", proof_tex: undefined, source: undefined };
          // When the SAME bundle also rewrote this node's claim, the claim-change branch
          // preserved the OLD-basis snapshot with the retained bytes; re-snapshotting
          // here against the new claim would erase what the bytes argued and mute the
          // previous-statement dispatch warning.
          if (!claimChangedIds.has(edit.id)) carried.snapshot = snapshotMember(proto, carried.node);
          carried.partial = true;
        }
        workingChanged = true;
        continue;
      }
      const original = originalStatements.get(edit.id);
      if (!original) {
        skipped.push({ id: edit.id, kind: "statement-replace", why: "no frozen proto statement with this id" });
        continue;
      }
      const protoMismatch = describeEchoMismatch(edit.proposed, original, edit.id);
      if (protoMismatch) {
        skipped.push({ id: edit.id, kind: "statement-replace", why: protoMismatch });
        continue;
      }
      const composed = {
        ...edit.proposed,
        statement: prior.statement,
        status: prior.status,
        proof_tex: prior.proof_tex,
      };
      const depSet = (deps: string[]): string => [...new Set(deps)].sort().join("\u0000");
      if (
        prior.kind === "openendedquestion" &&
        depSet(prior.depends_on) !== depSet(composed.depends_on)
      ) detachResolvedOeq(edit.id);
      changed.push({
        id: edit.id,
        kind: "statement",
        from: JSON.stringify(prior),
        to: JSON.stringify(composed),
        reason: edit.reason ?? "",
      });
      proto.statements[i] = composed;
      // Same pairing for a PROTO-frozen node. Its proof lives in the working cursor, not
      // in the proto, so commit it there; the snapshot must be taken AFTER the proto slot
      // is updated, since it closes over the node's own statement and dependency content.
      const pairedProto = pairedProofById.get(edit.id)?.proofTex;
      const protoRec = working?.solved[edit.id];
      if (claimChangedIds.has(edit.id)) {
        skipped.push({
          id: edit.id, kind: "proof-pairing",
          why: "this bundle also rewrites the node's claim, so the paired proof argues the OLD " +
            "statement — it is left unpaired and the node stays open for re-derivation",
        });
      } else if (pairedProto !== undefined && protoRec && dependencyClosureValid(composed)) {
        protoRec.proof_tex = pairedProto;
        protoRec.snapshot = snapshotMember(proto, composed);
        delete protoRec.partial;
        workingChanged = true;
      }
    } else if (edit.kind === "statement-delete") {
      const priorFrozen = proto.statements.find((s) => s.id === edit.id);
      const priorCarried = working?.solved[edit.id]?.node;
      const prior = priorFrozen ?? priorCarried;
      if (!prior) {
        skipped.push({ id: edit.id, kind: "statement-delete", why: "no frozen or carried statement with this id" });
        continue;
      }
      const replacementId = edit.replacement_id;
      if (replacementId === edit.id) {
        throw new Error(`Cannot delete statement ${edit.id} by replacing it with itself`);
      }
      if (
        replacementId !== undefined &&
        !proto.statements.some((s) => s.id === replacementId) &&
        working?.solved[replacementId]?.node?.id !== replacementId
      ) {
        throw new Error(
          `Cannot delete statement ${edit.id}: replacement ${replacementId} is not a frozen or carried statement node`,
        );
      }
      const inbound = proto.statements
        .filter((s) => s.id !== edit.id && s.depends_on.includes(edit.id))
        .map((s) => s.id);
      const carriedInbound = Object.entries(working?.solved ?? {})
        .filter(([id, rec]) => id !== edit.id && rec.node?.depends_on.includes(edit.id))
        .map(([id]) => id);
      const symbolInbound = proto.symbols.filter((s) => s.ref === edit.id).map((s) => s.name);
      const textInbound = findUnsafeDeleteTextReferences(proto, working, edit.id);
      if (textInbound.length > 0) {
        throw new Error(
          `Cannot delete statement ${edit.id}${replacementId ? ` in favour of ${replacementId}` : ""}: ` +
            `literal claim/proof references remain in ${textInbound.map((ref) => ref.location).join(", ")}. ` +
            "Remapping depends_on cannot decide whether the replacement states the same conditions. " +
            "Restate/re-prove every citing node through explicit reviewed proposals, then apply the delete atomically.",
        );
      }
      if (replacementId === undefined && (inbound.length > 0 || carriedInbound.length > 0 || symbolInbound.length > 0)) {
        throw new Error(
          `Cannot delete statement ${edit.id} without replacement_id; live inbound references remain from ` +
            [...inbound, ...carriedInbound, ...symbolInbound.map((name) => `sym:${name}`)].join(", "),
        );
      }
      proto.statements = proto.statements
        .filter((s) => s.id !== edit.id)
        .map((s) => ({
          ...s,
          depends_on: s.depends_on.map((d) => d === edit.id ? replacementId! : d),
        }));
      for (const symbol of proto.symbols) {
        if (symbol.ref !== edit.id) continue;
        if (replacementId === undefined) delete symbol.ref;
        else symbol.ref = replacementId;
      }
      // A removed frozen node must also be tombstoned in the incremental state;
      // otherwise the next D0 rebuild classifies it as an agent-added stale target
      // and silently resurrects it. Remap carried-node edges but retain their old
      // snapshots so ordinary validity propagation forces a re-proof when needed.
      if (working) {
        delete working.solved[edit.id];
        for (const rec of Object.values(working.solved)) {
          if (!rec.node) continue;
          rec.node.depends_on = replacementId === undefined
            ? rec.node.depends_on.filter((d) => d !== edit.id)
            : rec.node.depends_on.map((d) => d === edit.id ? replacementId : d);
        }
        for (const [sourceId, resolution] of Object.entries(working.resolved_oeqs ?? {})) {
          const theoremId = typeof resolution === "string" ? resolution : resolution.theorem_id;
          if (sourceId === edit.id || theoremId === edit.id) delete working.resolved_oeqs![sourceId];
        }
        workingChanged = true;
      }
      rebuildAssumptionUsedBy(proto);
      changed.push({
        id: edit.id,
        kind: "statement",
        from: JSON.stringify(prior),
        to: replacementId ? `<deleted; inbound edges remapped to ${replacementId}>` : "<deleted>",
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "definition-add") {
      if (proto.definitions.some((d) => d.id === edit.id) || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id, kind: "definition-add",
          why: edit.proposed.id !== edit.id
            ? `payload id '${edit.proposed.id}' does not match the edit target`
            : "a definition with this id is already present in the frozen proto (no-op re-proposal)",
        });
        continue;
      }
      proto.definitions.push(edit.proposed);
      changed.push({
        id: edit.id,
        kind: "definition",
        from: "",
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
    } else if (edit.kind === "definition-replace") {
      const i = proto.definitions.findIndex((d) => d.id === edit.id);
      if (i === -1 || edit.proposed.id !== edit.id) {
        skipped.push({
          id: edit.id, kind: "definition-replace",
          why: i === -1 ? "no frozen definition with this id" : `payload id '${edit.proposed.id}' does not match the edit target`,
        });
        continue;
      }
      changed.push({
        id: edit.id,
        kind: "definition",
        from: JSON.stringify(proto.definitions[i]),
        to: JSON.stringify(edit.proposed),
        reason: edit.reason ?? "",
      });
      proto.definitions[i] = edit.proposed;
    } else if (edit.kind === "definition-delete") {
      const prior = proto.definitions.find((d) => d.id === edit.id);
      if (!prior) {
        skipped.push({ id: edit.id, kind: "definition-delete", why: "no frozen definition with this id" });
        continue;
      }
      const textInbound = findUnsafeDeleteTextReferences(proto, working, edit.id);
      if (textInbound.length > 0) {
        throw new Error(
          `Cannot delete definition ${edit.id}: literal claim/proof references remain in ` +
            `${textInbound.map((ref) => ref.location).join(", ")}. ` +
            "Deleting a graph edge cannot safely rewrite authored mathematics; restate/re-prove the citing nodes first.",
        );
      }
      proto.definitions = proto.definitions.filter((d) => d.id !== edit.id);
      for (const s of proto.statements) s.depends_on = s.depends_on.filter((d) => d !== edit.id);
      for (const symbol of proto.symbols) if (symbol.ref === edit.id) delete symbol.ref;
      changed.push({ id: edit.id, kind: "definition", from: JSON.stringify(prior), to: "<deleted>", reason: edit.reason ?? "" });
    } else if (edit.kind === "bibliography-replace") {
      const i = proto.bibliography.findIndex((b) => b.key === edit.key);
      if (edit.proposed.key !== edit.key) {
        skipped.push({ id: target, kind: "bibliography-replace", why: `payload key '${edit.proposed.key}' does not match the edit target` });
        continue;
      }
      if (i === -1) {
        // The typed core-edit schema has no separate bibliography-add variant.
        // Solvers therefore use bibliography-replace for a newly required source
        // key as well as for corrections to an existing entry.
        proto.bibliography.push(edit.proposed);
        changed.push({ id: target, kind: "bibliography", from: "", to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
      } else {
        changed.push({ id: target, kind: "bibliography", from: JSON.stringify(proto.bibliography[i]), to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
        proto.bibliography[i] = edit.proposed;
      }
    } else if (edit.kind === "symbol-add") {
      if (proto.symbols.some((s) => s.name === edit.name) || edit.proposed.name !== edit.name) {
        skipped.push({
          id: target, kind: "symbol-add",
          why: edit.proposed.name !== edit.name
            ? `payload name '${edit.proposed.name}' does not match the edit target`
            : "a symbol with this name is already present in the frozen proto (no-op re-proposal)",
        });
        continue;
      }
      proto.symbols.push(edit.proposed);
      changed.push({ id: target, kind: "symbol", from: "", to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
    } else if (edit.kind === "symbol-replace") {
      const i = proto.symbols.findIndex((s) => s.name === edit.name);
      if (i === -1 || edit.proposed.name !== edit.name) {
        skipped.push({
          id: target, kind: "symbol-replace",
          why: i === -1 ? "no frozen symbol with this name" : `payload name '${edit.proposed.name}' does not match the edit target`,
        });
        continue;
      }
      changed.push({ id: target, kind: "symbol", from: JSON.stringify(proto.symbols[i]), to: JSON.stringify(edit.proposed), reason: edit.reason ?? "" });
      proto.symbols[i] = edit.proposed;
    } else if (edit.kind === "symbol-delete") {
      const prior = proto.symbols.find((s) => s.name === edit.name);
      if (!prior) {
        skipped.push({ id: target, kind: "symbol-delete", why: "no frozen symbol with this name" });
        continue;
      }
      proto.symbols = proto.symbols.filter((s) => s.name !== edit.name);
      changed.push({ id: target, kind: "symbol", from: JSON.stringify(prior), to: "<deleted>", reason: edit.reason ?? "" });
    } else {
      rebuildAssumptionUsedBy(proto);
      changed.push({ id: edit.id, kind: "metadata", from: "stale reverse dependencies", to: "rebuilt direct used_by inverse", reason: edit.reason ?? "" });
    }
  }
  if (changed.length !== selectedVariantCount) {
    // Name WHICH selected edit was dropped and WHY. The count alone is safe but not
    // diagnosable: it cost three solve rounds of source-reading on 2026-07-19.
    const why = skipped.length > 0
      ? ` Dropped: ${skipped.map((d) => `${d.id} (${d.kind}) — ${d.why}`).join("; ")}.`
      : " No per-edit reason was recorded, which is itself a gap: report it.";
    throw new Error(
      `Refusing partial D0 apply: selected ${selectedVariantCount} proposal variant(s), but only ` +
        `${changed.length} were applicable.${why} No proto, working cursor, escalation log, or outputs were mutated on disk.`,
    );
  }
  if (changed.length === 0 && !directive) return changed;

  // PAIRED-PROOF PROMOTION for applied claim changes. A paired proof that DECLARED it
  // argues the PROPOSED text (`argues_proposed`, set by the solver in the same bundle as
  // the statement change) is attached now — to the claim it argued, which adjudication
  // just made current — instead of reopening the node for a full re-derivation round
  // whose only job would be re-emitting this proof. The blanket "a paired proof argues
  // the OLD statement" rule above still governs undeclared proofs.
  //
  // Verified, not trusted: promotion requires that the basis the proof declared actually
  // materialized — the statement change applied (id ∈ claimChangedIds), the node stands
  // reopened as `to-prove` (cited nodes keep the conservative source-revalidation path),
  // the proof's content closure touches NO bundle proposal that adjudication left
  // unapplied (a partially-accepted basis is ambiguous), and the dependency closure is
  // discharged. D0.5 still reviews the promoted proof like any other.
  if (working) {
    // Count proposal VARIANTS per target id across every channel and compare with the
    // applied (`changed`) entries per id. A bare-id applied set aliased distinct same-id
    // variants: accepting `statement:thm:x` while rejecting `core-edit:thm:x` removed
    // thm:x from the unapplied set, so a proof authored against the rejected rewire
    // could be promoted. An id counts as materialized only when EVERY variant targeting
    // it applied.
    const proposedCount = new Map<string, number>();
    const bump = (id: string): void => { proposedCount.set(id, (proposedCount.get(id) ?? 0) + 1); };
    statements.forEach((c) => bump(c.id));
    definitions.forEach((c) => bump(c.id));
    assumptions.forEach((a) => bump(a.id));
    coreEdits.filter((e) => e.kind !== "rebuild-reverse-dependencies").forEach((e) => bump(coreEditTarget(e)));
    const appliedCount = new Map<string, number>();
    for (const entry of changed) {
      if (entry.kind === "metadata") continue; // rebuild edits are excluded from proposedCount too
      appliedCount.set(entry.id, (appliedCount.get(entry.id) ?? 0) + 1);
    }
    const unappliedIds = new Set(
      [...proposedCount.entries()].filter(([id, n]) => (appliedCount.get(id) ?? 0) < n).map(([id]) => id),
    );
    for (const dep of rejectedSupportIds) unappliedIds.add(dep);
    // GLOBAL invalidators mirror the merge-side deferral rule (merge.ts,
    // `hasGlobalProofInvalidation`): symbol and bibliography meaning, and a newly
    // proposed assumption, are not addressed by literal `ass:/def:/thm:` references,
    // so the closure walk below cannot see them. If any such proposal was left
    // unapplied, the basis the proof declared did not fully materialize — no
    // promotion this apply (the ordinary reopen/re-solve path stands).
    const GLOBAL_EDIT_KINDS = new Set(["symbol-add", "symbol-replace", "symbol-delete", "bibliography-replace"]);
    const hasUnappliedGlobalInvalidator =
      assumptions.some((a) => unappliedIds.has(a.id)) ||
      coreEdits.some((e) => GLOBAL_EDIT_KINDS.has(e.kind) && unappliedIds.has(coreEditTarget(e)));
    const carriedNodes = Object.values(working.solved).flatMap((r) => (r.node ? [r.node] : []));
    for (const id of hasUnappliedGlobalInvalidator ? [] : claimChangedIds) {
      const paired = pairedProofById.get(id);
      if (!paired?.arguesProposed) continue;
      const frozen = proto.statements.find((s) => s.id === id);
      const rec = working.solved[id];
      const node = frozen ?? rec?.node;
      if (!node || node.status !== "to-prove") continue;
      if (proofContentClosureIntersects({
        core: proto, node, proofText: paired.proofTex, changedIds: unappliedIds, extraStatements: carriedNodes,
      })) continue;
      if (!dependencyClosureValid(node)) continue;
      node.status = "proved";
      node.proof_tex = paired.proofTex;
      const snapshot = snapshotMember(proto, node);
      if (rec) {
        if (rec.node) rec.node = node;
        rec.proof_tex = paired.proofTex;
        rec.snapshot = snapshot;
        delete rec.partial;
      } else {
        working.solved[id] = { proof_tex: paired.proofTex, snapshot };
      }
      workingChanged = true;
    }
  }

  // Persist the same narrow JSON/LaTeX repairs used by assembled cores. This is
  // especially important for legacy proto strings containing a decoded control
  // byte (for example under-escaped `\\forall`): a later rebuild must not
  // reintroduce the corruption after a clean render.
  repairCoreLatexSerialization(proto);
  // Fail loudly before persisting: a control character still present after both
  // repair layers means an escaping corruption neither could safely resolve.
  assertNoDecodedControlChars(proto, `proto core after apply (${protoPath})`);
  CoreSchema.parse(proto);
  const declaredSymbols = new Set(proto.symbols.map((symbol) => symbol.name));
  const undeclaredFreeSymbols = proto.assumptions.flatMap((assumption) =>
    assumption.free_symbols
      .filter((name) => !declaredSymbols.has(name))
      .map((name) => `${assumption.id}:${name}`),
  );
  if (undeclaredFreeSymbols.length > 0) {
    throw new Error(
      `Refusing D0 apply: assumption free symbols remain undeclared after the selected bundle: ` +
        undeclaredFreeSymbols.join(", "),
    );
  }
  if (checkOnly) return changed;
  // Rewind the stage pointer BEFORE publishing any part of the multi-file
  // apply. If the process dies after this point, plain resume is constrained to
  // D0 and cannot review/advance an old core against a partially updated proto.
  // PROTO CONFLICT RE-CHECK. Runs before EVERY persistent mutation — the stage-cursor
  // rewind and the working save both follow it. It previously sat after both, so a
  // detected conflict threw while claiming "nothing was mutated" having already durably
  // rewound the pipeline cursor and changed the working state.
  //
  // Honest about what this is: a re-read and compare, NOT an atomic compare-and-swap. Two
  // applies can both pass this check and then both rename, and the second still wins. It
  // narrows the window from "the whole apply" to "between this read and the rename"; it
  // does not serialize concurrent applies. Closing it properly needs an exclusive lock,
  // which brings stale-lock recovery of its own — deliberately not taken on here, because
  // the orchestrator is single-threaded and different qids use different run directories.
  const protoBytesNow = await readFile(protoPath, "utf8");
  if (protoBytesNow !== protoBytesAtRead) {
    throw new Error(
      "d0_apply_change: proto_core.json changed while this apply was preparing — another apply, a " +
        "directive, or a hand edit committed first. Nothing was mutated on disk. Re-read the current " +
        "proposals and re-run so the adjudication is made against the live proto.",
    );
  }

  const sp = statePath(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
  if (existsSync(sp)) {
    const state = await loadState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1");
    if (state.stage_completed !== "-0.5") {
      state.stage_completed = "-0.5";
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization ?? "v1", state);
    }
  }
  // COMMIT ORDER. The durable agent-node cursor is persisted BEFORE the frozen proto.
  // That order is deliberate: if the process stops between the two atomic renames the old
  // proto remains authoritative and the next solve re-derives validity, whereas the
  // reverse order could delete a proto node while a carried copy survives to resurrect it.
  //
  // Honest limit: "the old proto remains authoritative" holds only for FROZEN nodes. A
  // CARRIED (agent-authored) node's sole durable catalog IS this working save, so a stop
  // in the window commits its adjudicated edits (including a paired-proof promotion)
  // before the journal entry lands. The unconsumed bundle survives, but a mechanical
  // re-apply does NOT replay it: the carried node now reads the NEW text, so the stale-
  // `current` guard skips the proposal and the count guard refuses the partial apply.
  // Recovery is operator-level — the applied edit is visibly in the cursor; deselect it
  // (or drop the bundle) and re-record the journal entry. What a crash here loses is
  // the journal record, never the decision. Pre-existing exposure (the cited-shortcut
  // and statement-replace pairing branches settle carried nodes in this same window).
  //
  // The hole was never the order. The SAME working save also consumed
  // `working.proposals`, so a stop in that window left the adjudicated bundle consumed
  // and the proto un-updated — the accepted decision lost, with nothing to replay.
  // The proposals are therefore consumed only AFTER the proto lands.
  if (workingChanged && working) await saveWorkingState(ctx, working);

  const protoTemp = `${protoPath}.tmp-${process.pid}-${Date.now()}`;
  try {
    await writeFile(protoTemp, JSON.stringify(proto, null, 2), "utf8");
    await rename(protoTemp, protoPath);
  } finally {
    await rm(protoTemp, { force: true });
  }
  // The adjudicated payload must not outlive its round: `clearRoundOutputs` deletes the
  // derived per-kind files, so the authoritative copy goes with them — but only now that
  // the proto has durably received the changes.
  // Journal the accepted decision BEFORE consuming the bundle: a stop between these two
  // would otherwise leave the proto changed, the proposals gone, and no record of the
  // rationale or directive the next solve reads.
  await appendEscalationLog(ctx, {
    round: working?.round ?? 0,
    changed,
    note,
    directive,
    // Reopened cited leaves are dischargeable ONLY through a directed round: the
    // dispatcher promotes a stale cited lemma to a repair root — and merge accepts its
    // byte-faithful revalidation receipt — strictly for EXACT REQUIRED targets. A
    // referee escalation names them in its own entry; a solver-proposed narrowing has
    // no such entry, so the apply journal must require them itself.
    ...(reopenedCitedIds.length > 0 ? { required_core_targets: [...new Set(reopenedCitedIds)] } : {}),
  });
  // The adjudicated payload must not outlive its round: `clearRoundOutputs` deletes the
  // derived per-kind files, so the authoritative copy goes with them — but only now that
  // the proto has durably received the changes.
  // CONSUMED MARKER, not a deletion. `readRoundProposals` treats an ABSENT
  // `working.proposals` as "this run predates the fold" and falls back to the per-kind
  // mirrors — it cannot tell a legacy run from a modern one caught mid-crash. Deleting the
  // field and then clearing the mirrors left a window where the canonical copy was gone
  // and the mirrors were not, so the already-applied bundle became authoritative again.
  //
  // Clearing the mirrors first is no better: a stop before the delete leaves the canonical
  // bundle present and consumed, and the next round re-reads it.
  //
  // Writing EMPTY channels is safe in both windows. An empty object is still "present", so
  // the fallback stays suppressed, and it reads as consumed rather than as legacy.
  if (working?.proposals !== undefined) {
    working.proposals = emptyProposals() as unknown as typeof working.proposals;
    await saveWorkingState(ctx, working);
  }
  await clearRoundOutputs(ctx);
  return changed;
}
