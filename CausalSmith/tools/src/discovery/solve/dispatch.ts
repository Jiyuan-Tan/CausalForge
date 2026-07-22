// D0-SOLVE step 2/5 — dispatchAgents (spec §Stage kernel).
//
// WCC partitioning of the open frontier, per-round prose/emission ownership
// selection, per-unit prompt assembly, the solveUnit agent dispatch (with the
// id parse/heal at the unit output boundary), moved verbatim from
// stage0_solve.ts in the T1 carve. Capability projection and conflict
// resolution over the raw outputs happen in solve/merge.ts.
import { existsSync } from "node:fs";
import { mkdir, readFile, rm } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../../constants.js";
import { artifactPath } from "../../paths.js";
import { discoveryBrief, parseStageOutput, readPrompt, type StageDeps } from "../../pipeline_support.js";
import type { PipelineContext, StateJson } from "../../types.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { healStatementId } from "../core/node_ids.js";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../core/latex_serialization.js";
import { archiveProofs, proofBytesInRoundFile } from "../proof_archive.js";
import { hotProofBytes, loadWorkingState } from "../stages/d0_working.js";
import { dispatchAgent } from "../../framework/agent_dispatch.js";
import type { SolveUnitOutput } from "./schemas.js";
import { SolveUnitOutputSchema } from "./schemas.js";
import {
  type SolveDispatchUnit,
  selectDirectiveEmissionOwnerLabel,
  selectSemanticTargetOwners,
} from "./ownership.js";
import { openSolveTarget, type SolveRoundContext } from "./context.js";

/** Per-unit output JSON path ('thm:x' → 'thm_x', 'props' → 'props'). */
function unitOutPath(ctx: PipelineContext, label: string): string {
  const slug = label.replace(/[^a-z0-9]+/gi, "_");
  return artifactPath(ctx.repoRoot, ctx.qid, "discovery", `solve_${slug}.json`, [`${ctx.qid}_solve_${slug}.json`]);
}

/** Canonicalize every model-authored string before solve-unit schema validation and
 * proposal persistence. The repair itself is deliberately narrow, so traversing the
 * full payload catches `current`, `proposed`, nested core edits, proofs, and prose
 * without changing ordinary tabs or non-LaTeX text. */
export function repairSolveUnitLatexSerialization(value: unknown): void {
  repairLatexStringsDeep(value);
}

/** Read-only frozen-core context block shared by every solver unit. */
function frozenContextBlock(core: Core): string {
  return JSON.stringify(
    {
      symbols: core.symbols,
      assumptions: core.assumptions,
      definitions: core.definitions,
      target_estimand: core.target_estimand,
      estimand_functional: core.estimand_functional,
      statements: core.statements.map((s) => ({
        id: s.id,
        kind: s.kind,
        statement: s.statement,
        depends_on: s.depends_on,
      })),
    },
    null,
    2,
  );
}

/** When F3 bounced a node back to D0 with a refuting witness (`flags.redo_math_witness`), surface it
 *  so the re-solve CONSUMES it: re-derive only the refuted node + its dependents (never from scratch),
 *  treating the obstruction as a hard constraint — so the solver cannot regenerate the same false claim.
 *  Empty string when there is no parked witness. */
function redoMathWitnessBlock(state: StateJson): string {
  const w = state.flags.redo_math_witness;
  if (!w) return "";
  return [
    "=== F3 REFUTATION — RE-DERIVE THIS NODE (do NOT re-emit the refuted claim) ===",
    `Node \`${w.obj_id}\` was PROVEN-FALSE downstream by a concrete witness; your prior derivation of it`,
    `is WRONG. Re-derive ONLY this node and its dependents [${w.dependents.join(", ") || "none"}]; leave`,
    "every other established proof intact (incremental re-solve, not from scratch). The refuting witness",
    `(type: ${w.type}) is a HARD CONSTRAINT your new statement/proof MUST respect:`,
    w.detail,
    "If the node cannot be salvaged as stated, weaken/correct it (proposed_statement_changes) so the",
    "witness no longer refutes it — never restate the same claim.",
  ].join("\n");
}

/** Dispatch one solver agent for a set of target statements (a headline, or all props). */
async function solveUnit(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  core: Core;
  targets: CoreStatement[];
  label: string;
  clusterSetupBlock: string;
  /** Incremental context: the orchestrator escalation log + this group's
   *  already-established (still-valid) proofs the agent should reuse, not re-derive. */
  priorContext?: string;
  /** Paper-wide prose has one deterministic owner per directed round. Other
   * units solve mathematics only and must omit `prose_updates`. */
  proseRole: "owner" | "omit" | "none";
  /** A directed round also has one writer for cross-cutting additions/edits.
   * Non-owners may still prove their targets and add genuinely local, non-cited
   * proof helpers. */
  directiveEmissionRole: "owner" | "local" | "none";
  requiredCoreTargets: string[];
  ownedSemanticTargets: string[];
  siblingSemanticTargets: Array<{ id: string; owner: string }>;
}): Promise<SolveUnitOutput> {
  const { ctx, targets, label } = args;
  const outPath = unitOutPath(ctx, label);
  await mkdir(path.dirname(outPath), { recursive: true });
  // Output paths are stable across D0 rounds. Remove the prior invocation's
  // artifact before dispatch so a worker that reports completion but fails to
  // write cannot be credited with stale proofs/proposals from an earlier round.
  // Archive its proof bytes first: if the prior round died before commit, this file is
  // the ONLY copy of what that dispatch paid for. Bytes that DID reach the working
  // cursor are filtered out — they are hot, not displaced, and a false archive row
  // would later suppress the record of a real displacement (dedup is (bytes, node)).
  if (existsSync(outPath)) {
    const hot = hotProofBytes(await loadWorkingState(ctx));
    const stale = proofBytesInRoundFile(path.basename(outPath), await readFile(outPath, "utf8"), "stale-dispatch-cleared")
      .filter((p) => !hot.get(p.nodeId)?.has(p.proofTex));
    if (stale.length > 0) await archiveProofs(path.dirname(outPath), stale);
  }
  await rm(outPath, { force: true });

  const prompt = [
    await readPrompt(ctx, "stage0_common_discovery.txt"),
    "",
    args.clusterSetupBlock,
    "",
    await readPrompt(ctx, "stage0_solve.txt"),
    "",
    discoveryBrief(ctx, args.state),
    ...(redoMathWitnessBlock(args.state) ? ["", redoMathWitnessBlock(args.state)] : []),
    "",
    "=== FROZEN CORE (read-only context) ===",
    frozenContextBlock(args.core),
    ...(args.priorContext && args.priorContext.trim().length > 0 ? ["", args.priorContext] : []),
    ...(args.proseRole === "owner" ? [
      "",
      "=== PAPER-WIDE PROSE OWNERSHIP ===",
      "You are the ONLY solve unit allowed to emit `prose_updates` this round. Synthesize one canonical",
      "paper-wide update that incorporates the orchestrator directive and the full frozen-core context.",
      "Other units are forbidden to emit prose_updates, so do not expect or require identical prose from them.",
      "Top-level prose fields may summarize the whole paper. In `statement_notes`, name only statements present",
      "in this round's FROZEN CORE or a replacement theorem/helper that YOUR unit emits; omit prior-round or",
      "sibling-only ids that are visible only in escalation/reuse context.",
    ] : args.proseRole === "omit" ? [
      "",
      "=== PAPER-WIDE PROSE OWNERSHIP ===",
      "Another solve unit owns the single canonical paper-wide prose update. OMIT `prose_updates` entirely",
      "from your output, even though the orchestrator directive requests narrative synchronization. Solve only",
      "your mathematical targets; the designated prose owner will synchronize the paper-wide narrative.",
    ] : []),
    ...(args.directiveEmissionRole === "owner" ? [
      "",
      "=== DIRECTIVE-WIDE STRUCTURED-EMISSION OWNERSHIP ===",
      "You are the ONLY solve unit allowed to emit directive-wide shared payloads this round. Emit each",
      "cross-cutting comparator/cited `added_lemmas` node, new exact required node, proposed assumption,",
      "definition correction, or non-local `proposed_core_edits` symbol/definition/bibliography/metadata edit",
      "exactly once in YOUR output. Other units may cite or depend on those ids but are forbidden to emit them.",
      `Exact required target ids for this round: ${args.requiredCoreTargets.join(", ") || "(none listed)"}.`,
      `Statement target ids semantically owned by YOUR unit: ${args.ownedSemanticTargets.join(", ") || "(none)"}.`,
      "IMPORTANT: being the cross-cutting owner does NOT authorize you to prove, replace, edit, or re-emit a",
      "statement target owned by a sibling unit. You may only depend on those sibling-owned ids:",
      ...(args.siblingSemanticTargets.length > 0
        ? args.siblingSemanticTargets.map(({ id, owner }) => `- ${id} -> semantic owner ${owner}`)
        : ["- (no sibling-owned statement targets)"]),
    ] : args.directiveEmissionRole === "local" ? [
      "",
      "=== DIRECTIVE-WIDE STRUCTURED-EMISSION OWNERSHIP ===",
      "Another solve unit is the canonical writer for directive-wide shared payloads. You are FORBIDDEN to",
      "emit cited `added_lemmas`, an added node named by the exact required-target list, proposed assumptions,",
      "definition changes, or any `proposed_core_edits` whose target is not one of YOUR target statement ids.",
      `Exact required target ids for this round: ${args.requiredCoreTargets.join(", ") || "(none listed)"}.`,
      "If your proof uses a shared comparator/symbol/definition, cite or add that exact id to `depends_on` and",
      "let the canonical owner emit it. You may still emit genuinely local non-cited proof helpers and a",
      "statement change/edit for one of YOUR exact target ids. Do not duplicate the shared payload.",
      // This block OVERRIDES the base prompt's CROSS-TARGET SHARED HELPERS rule, which
      // told every unit to emit a shared helper "rather than assume the other target/unit
      // proves it" and promised duplicates are deduped. Both halves misled: dedup is
      // content-keyed, so two units wording the same lemma differently is a CONFLICT that
      // aborts the round. Units followed the more emphatic base rule and collided —
      // the comparator lemma, sym:\bar d and the metadata rebuild all fit this shape.
      "THIS OVERRIDES the base prompt's instruction to emit a shared helper rather than assume another unit",
      "proves it: for the ids above, citing is CORRECT and emitting is not. Every unit's output is merged",
      "into one core before validation, so a citation to an id the owner emits resolves there. Emitting it",
      "anyway is not a harmless duplicate — payloads are compared by CONTENT, and the same lemma in different",
      "words is a CONFLICT that aborts the round and discards every unit's work.",
      `Statement target ids semantically owned by YOUR unit: ${args.ownedSemanticTargets.join(", ") || "(none)"}.`,
      "Every proof, replacement, `proposed_statement_changes` item, or statement-target core edit for a",
      "sibling-owned id is forbidden. You may only depend on these sibling-owned ids:",
      ...(args.siblingSemanticTargets.length > 0
        ? args.siblingSemanticTargets.map(({ id, owner }) => `- ${id} -> semantic owner ${owner}`)
        : ["- (no sibling-owned statement targets)"]),
    ] : []),
    "",
    `=== TARGET STATEMENT(S) TO SOLVE (unit: ${label}) ===`,
    JSON.stringify(targets, null, 2),
    "",
    `SOLVE_OUTPUT_PATH: ${outPath}`,
    'Return only JSON on stdout: {"status":"completed","message":"...","artifacts":["<solve.json>"]}.',
  ].join("\n");

  const out = await dispatchAgent({
    ctx,
    deps: args.deps,
    stage: "0",
    label: `D0-SOLVE unit ${label}`,
    prompt,
    promptSources: ["prompts/D0/stage0_solve.txt", `unit:${label}`],
    model: MODEL_PLAN.stage0_solve.model,
    reasoningEffort: MODEL_PLAN.stage0_solve.effort,
    inactivityTimeoutMs: 30 * 60 * 1000,
  });
  const parsed = parseStageOutput(out.stdout);
  if (parsed.status === "parse_failed") {
    // AUDIT-A: fail closed on unparseable stage output; why: D0 solve must not advance on garbage.
    throw new Error(`Stage 0-SOLVE: worker output for unit ${label} did not parse (parse_failed) - refusing to advance on unparseable output`);
  }
  if (parsed.status === "failed") {
    throw new Error(
      `Stage 0-SOLVE failed on unit ${label}: ${parsed.message ?? "(no message)"} — ` +
        `the target is not provable from its declared dependencies; fix the core, do not launder.`,
    );
  }
/** Rewrite every statement id a solve unit emitted into the schema's lowercase-kebab
 *  grammar, in place, including the dependency edges and proof ids that reference them.
 *  Mutates `body` before validation; ids already canonical are untouched. */
function healSolveUnitIds(body: unknown): void {
  if (body === null || typeof body !== "object") return;
  const b = body as Record<string, unknown>;
  const rename = new Map<string, string>();
  const note = (id: unknown): void => {
    if (typeof id !== "string") return;
    const healed = healStatementId(id);
    if (healed !== null && healed !== id) rename.set(id, healed);
  };
  const stmts = [
    ...(Array.isArray(b.added_lemmas) ? b.added_lemmas : []),
    ...(Array.isArray(b.resolved_oeqs) ? b.resolved_oeqs.map((r) => (r as { theorem?: unknown }).theorem) : []),
  ];
  for (const st of stmts) if (st && typeof st === "object") note((st as { id?: unknown }).id);
  if (rename.size === 0) return;
  const swap = (id: unknown): unknown => (typeof id === "string" ? rename.get(id) ?? id : id);
  for (const st of stmts) {
    if (!st || typeof st !== "object") continue;
    const node = st as { id?: unknown; depends_on?: unknown };
    node.id = swap(node.id);
    if (Array.isArray(node.depends_on)) node.depends_on = node.depends_on.map(swap);
  }
  if (Array.isArray(b.proofs)) {
    for (const pr of b.proofs) if (pr && typeof pr === "object") {
      (pr as { id?: unknown }).id = swap((pr as { id?: unknown }).id);
    }
  }
  // Obligations and prose notes are keyed by statement id too. Renaming the node but not
  // these left an obligation recorded under an id that no longer exists (so the round
  // halts asking for guidance on a ghost node) and a prose note attached to nothing.
  if (Array.isArray(b.open_obligations)) {
    for (const o of b.open_obligations) if (o && typeof o === "object") {
      (o as { node_id?: unknown }).node_id = swap((o as { node_id?: unknown }).node_id);
    }
  }
  const notes = (b.prose_updates as { statement_notes?: unknown } | undefined)?.statement_notes;
  if (Array.isArray(notes)) {
    for (const n of notes) if (n && typeof n === "object") {
      (n as { id?: unknown }).id = swap((n as { id?: unknown }).id);
    }
  }
  if (Array.isArray(b.proposed_core_edits)) {
    for (const e of b.proposed_core_edits) if (e && typeof e === "object") {
      const edit = e as {
        id?: unknown; replacement_id?: unknown;
        proposed?: { id?: unknown; depends_on?: unknown; ref?: unknown; by_member_properties?: unknown };
      };
      edit.id = swap(edit.id);
      // A statement-delete names its successor, and a symbol/definition payload can point
      // at a statement through `ref`/`refs`/`by_member_properties`. Renaming the node but
      // not these left a reference to an id that no longer exists, which the strict solve
      // schema or the apply's closure check then rejects.
      edit.replacement_id = swap(edit.replacement_id);
      if (edit.proposed && typeof edit.proposed === "object") {
        edit.proposed.id = swap(edit.proposed.id);
        if (Array.isArray(edit.proposed.depends_on)) edit.proposed.depends_on = edit.proposed.depends_on.map(swap);
        edit.proposed.ref = swap(edit.proposed.ref);
        // NOT `refs`: on a symbol payload that field holds SYMBOL NAMES, not statement ids,
        // so rewriting it renamed an unrelated symbol that happened to share the spelling.
        if (Array.isArray(edit.proposed.by_member_properties)) {
          edit.proposed.by_member_properties = edit.proposed.by_member_properties.map(swap);
        }
        // NOT `inputs` either. It was added on the reasoning that a definition input can
        // name an emitted statement -- but inputs also carry SYMBOL names, so an
        // unconditional swap repeats exactly the collision just removed from `refs`: a
        // symbol spelled like a healed helper gets silently renamed. Distinguishing the two
        // needs the symbol table, which is not available at this boundary.
      }
    }
  }
  console.warn(
    `[D0-SOLVE] normalised ${rename.size} non-kebab emitted id(s) at the unit boundary: ` +
      `${[...rename].map(([a, c]) => `${a}->${c}`).join(", ")}`,
  );
}

  if (!existsSync(outPath)) {
    throw new Error(`Stage 0-SOLVE unit ${label} completed without writing ${outPath}`);
  }
  try {
    // Pre-parse raw-byte normalization: an under-escaped TeX backslash (`\theta`)
    // is only distinguishable from an intended control escape BEFORE JSON.parse
    // destroys the information. The post-parse repair below stays as legacy cover.
    const body = JSON.parse(normalizeRawModelJson(await readFile(outPath, "utf8")));
    repairSolveUnitLatexSerialization(body);
    assertNoDecodedControlChars(body, `Stage 0-SOLVE unit ${label} output`);
    // NORMALISE IDS FIRST. The schema's id grammar is lowercase-kebab, and a solver
    // reliably names a helper after a capital-letter symbol (`lem:Ghat-envelope` for an
    // estimator Ĝ). A downstream auto-heal exists for exactly that — but it ran over
    // core.statements, which are already schema-validated, so it could never fire: the
    // strict parse below rejected the payload first and the ENTIRE round was lost as
    // "invalid solve JSON". Heal at the input boundary so the heal is reachable and a
    // capitalised id costs a rename instead of a round.
    healSolveUnitIds(body);
    // why: validate solve-unit item shapes at the file boundary before merging.
    return SolveUnitOutputSchema.parse(body);
  } catch (err) {
    throw new Error(`Stage 0-SOLVE unit ${label} wrote invalid solve JSON at ${outPath}: ${err instanceof Error ? err.message : String(err)}`);
  }
}

/** Partition to-prove statements into weakly-connected components of their mutual
 *  dependency graph. Only an edge between two TO-PROVE statements couples them — a
 *  `depends_on` reference to an already-proved statement, an assumption, or a
 *  definition is stable frozen context, not a reconciliation hazard. Each component
 *  becomes one solver unit; its label is the component's lead headline (`theorem`/
 *  `conjecture`), or its first member when the component is props/lemmas only. */
export function groupToProveByComponent(
  toProve: CoreStatement[],
): Array<{ targets: CoreStatement[]; label: string }> {
  const order = new Map(toProve.map((s, i) => [s.id, i]));
  const idSet = new Set(toProve.map((s) => s.id));
  const parent = new Map(toProve.map((s) => [s.id, s.id]));
  const find = (x: string): string => {
    let r = x;
    while (parent.get(r) !== r) r = parent.get(r)!;
    let c = x;
    while (parent.get(c) !== r) {
      const nxt = parent.get(c)!;
      parent.set(c, r);
      c = nxt;
    }
    return r;
  };
  const union = (a: string, b: string): void => {
    parent.set(find(a), find(b));
  };
  for (const s of toProve) {
    for (const d of s.depends_on ?? []) {
      if (idSet.has(d)) union(s.id, d);
    }
  }
  const byRoot = new Map<string, CoreStatement[]>();
  for (const s of toProve) {
    const r = find(s.id);
    const bucket = byRoot.get(r) ?? [];
    bucket.push(s);
    byRoot.set(r, bucket);
  }
  const comps = [...byRoot.values()];
  for (const c of comps) c.sort((a, b) => order.get(a.id)! - order.get(b.id)!);
  comps.sort((a, b) => order.get(a[0].id)! - order.get(b[0].id)!);
  return comps.map((targets) => {
    // Choose the lead by CONTENT, never by array position. `find` returned the first
    // headline in SOURCE order, so two semantically identical cores that happened to list
    // their statements differently elected different unit labels — and the label decides
    // ownership, so a reorder alone could move who is allowed to emit what.
    // `selectDirectiveEmissionOwnerLabel` already holds this discipline; this did not.
    const HEADLINE_RANK: Record<string, number> = {
      theorem: 3, openendedquestion: 2, conjecture: 1,
    };
    const lead =
      [...targets].sort((a, b) => {
        const byKind = (HEADLINE_RANK[b.kind] ?? 0) - (HEADLINE_RANK[a.kind] ?? 0);
        if (byKind !== 0) return byKind;
        return a.id.localeCompare(b.id); // stable tie-break independent of input order
      })[0] ?? targets[0];
    return { targets, label: lead.id };
  });
}

export interface SolveDispatchResult {
  dispatch: SolveDispatchUnit[];
  rawOutputs: SolveUnitOutput[];
  proseOwnerIndex: number | null;
  directiveOwnerLabel: string | null;
  semanticTargetOwners: Map<string, string>;
}

export async function dispatchSolveUnits(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  sctx: SolveRoundContext;
}): Promise<SolveDispatchResult> {
  const { ctx, state, deps, sctx } = args;
  const {
    proto,
    core,
    prev,
    next,
    validIds,
    persistedOeqReplacements,
    staleAgentTargets,
    hasPendingDirective,
    requiredCoreTargets,
    escContext,
    clusterSetupBlock,
  } = sctx;
  // One agent per weakly-connected component of the OPEN spec statements. Coupling
  // edges run only through open (still-changeable) statements, so consumers connected
  // ONLY through a now-valid node split into separate groups and parallelize.
  const openById = new Map<string, CoreStatement>();
  for (const statement of [
    ...proto.statements.filter((m) => !validIds.has(m.id) && !persistedOeqReplacements.has(m.id)),
    ...staleAgentTargets,
  ]) openById.set(statement.id, statement);
  if (hasPendingDirective) {
    const forcedIds = requiredCoreTargets.size > 0
      ? [...requiredCoreTargets]
      : core.statements.map((statement) => statement.id);
    const statementById = new Map(core.statements.map((statement) => [statement.id, statement] as const));
    for (const id of forcedIds) {
      const statement = statementById.get(id);
      if (!statement) continue; // a genuinely new required node must be emitted as an addition.
      openById.set(id, openSolveTarget(statement));
    }
  }
  const openStmts = [...openById.values()];
  const groups = groupToProveByComponent(openStmts);
  const dispatch: SolveDispatchUnit[] = [];
  for (const g of groups) {
    // Established context = proofs of the still-valid nodes this group's open members
    // depend on (so the agent reuses/cites them instead of re-deriving).
    const openDeps = new Set(g.targets.flatMap((m) => m.depends_on ?? []));
    const targetIds = new Set(g.targets.map((m) => m.id));
    const established = [...openDeps]
      // A directed repair can force an otherwise-valid dependency back onto the
      // target frontier. Never tell the worker that the same node is both owed and
      // established/do-not-rederive; that contradictory I/O previously caused a
      // requested proof replacement to be copied through unchanged.
      .filter((id) => !targetIds.has(id) && next.solved[id] !== undefined && !next.solved[id].partial)
      .map((id) => `- ${id}: ${next.solved[id].proof_tex}`);
    const priorTargetProofs = g.targets
      .filter((m) => next.solved[m.id] !== undefined && !next.solved[m.id].partial)
      .map((m) => `- ${m.id}: ${next.solved[m.id].proof_tex}`);
    // Prior PARTIAL progress on this group's open targets (from a previous round): the
    // agent must EXTEND it, not restart — this is what makes the iteration accumulate.
    // A partial whose snapshot records a DIFFERENT statement text than the current
    // target argued a previous form of the claim (its bytes survive a statement change
    // as the repair basis). Say so, and show which text it argued — otherwise the agent
    // extends a stale argument past the change instead of realigning it.
    const partials = g.targets
      .filter((m) => prev?.solved[m.id]?.partial && (prev.solved[m.id].proof_tex ?? "").trim().length > 0)
      .map((m) => {
        const rec = prev!.solved[m.id];
        const staleBasis = rec.snapshot?.stmt !== undefined && rec.snapshot.stmt !== m.statement
          ? ` [this partial argued a PREVIOUS statement of ${m.id} — "${rec.snapshot.stmt}" — which has since ` +
            `changed; REALIGN the argument to the current statement, dropping any step that relied on the old form]`
          : "";
        return `- ${m.id}:${staleBasis} ${rec.proof_tex}`;
      });
    const body = [
      escContext,
      established.length > 0
        ? "=== ALREADY-ESTABLISHED (still valid — cite for REUSE, do NOT re-derive) ===\n" + established.join("\n\n")
        : "",
      priorTargetProofs.length > 0
        ? "=== PRIOR PROOF OF A DIRECTED TARGET (revise/replace it; it is NOT established for this round) ===\n" + priorTargetProofs.join("\n\n")
        : "",
      partials.length > 0
        ? "=== PRIOR PARTIAL PROGRESS on your targets (EXTEND this, do NOT restart; prove the residual on top of it) ===\n" + partials.join("\n\n")
        : "",
    ].filter((x) => x.trim().length > 0);
    // The context below is REUSE background; it must not shrink the work. The agent
    // still owes a proof OR a proposed change for EVERY listed target.
    const priorContext =
      body.length > 0
        ? [
            "=== PRIOR-ROUND CONTEXT (reuse only — does NOT reduce your TARGET list below; " +
              "you still owe a proof or a proposed change for EVERY target) ===",
            ...body,
          ].join("\n\n")
        : "";
    dispatch.push({ targets: g.targets, label: g.label, priorContext });
  }

  // Every directed round has one canonical writer for paper-wide prose AND
  // cross-cutting structured emissions. Selection depends on component content,
  // not dispatch/Promise order. All other workers remain free to solve their own
  // targets and add genuinely local non-cited helpers.
  const directiveOwnerLabel = hasPendingDirective
    ? selectDirectiveEmissionOwnerLabel(dispatch)
    : null;
  const semanticTargetOwners = hasPendingDirective
    ? selectSemanticTargetOwners(dispatch)
    : new Map<string, string>();
  const semanticTargetEntries = [...semanticTargetOwners.entries()]
    .sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0);
  const proseOwnerIndex = directiveOwnerLabel === null
    ? null
    : dispatch.findIndex((unit) => unit.label === directiveOwnerLabel);

  const rawOutputs = await Promise.all(
    dispatch.map((u, i) =>
      solveUnit({
        ctx,
        state,
        deps,
        core,
        targets: u.targets,
        label: u.label,
        clusterSetupBlock,
        priorContext: u.priorContext,
        proseRole: proseOwnerIndex === null ? "none" : i === proseOwnerIndex ? "owner" : "omit",
        directiveEmissionRole: directiveOwnerLabel === null
          ? "none"
          : u.label === directiveOwnerLabel ? "owner" : "local",
        requiredCoreTargets: [...requiredCoreTargets].sort(),
        ownedSemanticTargets: semanticTargetEntries
          .filter(([, owner]) => owner === u.label)
          .map(([id]) => id),
        siblingSemanticTargets: semanticTargetEntries
          .filter(([, owner]) => owner !== u.label)
          .map(([id, owner]) => ({ id, owner })),
      }),
    ),
  );
  return { dispatch, rawOutputs, proseOwnerIndex, directiveOwnerLabel, semanticTargetOwners };
}
