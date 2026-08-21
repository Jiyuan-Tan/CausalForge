import { readFile, writeFile, mkdir, unlink } from "node:fs/promises";
import { join } from "node:path";
import type { StageIO } from "../pipeline.js";
import { PRESENTATION_PROSE_POLICY_VERSION, presentationPrompt, promptContractFiles, promptFingerprint } from "../prompt_io.js";
import { parseOutline, unwrapArtifact, lintMainBodyDependencies } from "../stage_util.js";
import {
  lintAnchors,
  lintClarity,
  lintSelfContainment,
  lintCrossRefs,
  lintReferences,
  normalizeCrefs,
  lintHypothesisPresentation,
  hashEnvBody,
  containsNotation,
  definingNotationKey,
  notationHomes,
  usesSymbolUndecorated,
  type LintProblem,
} from "../tex_anchors.js";
import { parseBib } from "../citations.js";
import { parseJsonLoose, mapLimit } from "../gates.js";
import { buildLeanContextIndex, type LeanContext } from "../lean_context.js";
import { citedDependencies, renderedNodes, topoOrder, refTargets, envForNode, isCitedNode } from "../graph_view.js";
import { citedStdFromNode, reconcileCite, indexBib } from "../assumption_citations.js";
import { FIRST_DRAFT_BRIEF } from "../revision_brief.js";
import { blocksFromGraph, blocksToTex, FormalLayerSource, type FormalBlock } from "../formal_layer.js";
import {
  runP1Loop,
  renderMechanicalLayer,
  atomicRequestedNotationSymbols,
  type P1Env,
  type P1Finding,
  type P1LoopHooks,
} from "../p1_loop.js";
import { runStatementAudit } from "../audit.js";
import { writeJsonAtomic } from "../json_io.js";
import { loadJsonCache } from "../cache.js";
import { loadBankNarrative } from "../bank.js";
import {
  discoverRealizedSymbols,
  buildRealizedNotationMatcher,
} from "../../formalization/crosswalk.js";

const OPEN_DIRECTION_RE = /\b(?:open (?:question|problem|direction)|unresolved (?:question|issue)|remains? (?:open|unknown|unresolved)|remain(?:s)? to (?:be )?(?:shown|determined|understood|resolved)|ask(?:s|ed)? whether|question (?:is|of) whether|future work|further work|future research|next step|worth (?:investigating|studying)|natural (?:question|direction|extension|strengthening))\b/i;
const ASSERTED_RESULT_RE = /\b(?:(?:we|this (?:paper|work)|our (?:paper|work|result|analysis))\s+(?:prove|proves|establish|establishes|show|shows|derive|derives|demonstrate|demonstrates)|(?:theorem|corollary|proposition|our result)\b[^.!?]{0,100}\b(?:prove|proves|establish|establishes|show|shows|imply|implies)|it follows that|we conclude that|is established here|has been proved)\b/i;
const ASSERTIVE_REVERSAL_RE = /\b(?:nevertheless|in fact|indeed|therefore|thus|hence)\b/i;
const LEGALISTIC_UNDELIVERED_RE = /^\s*this work does not (?:establish|prove|deliver)/i;

/** A model-written remark is acceptable only when it clearly frames the claim as an open
 * direction and does not turn around and assert it as a theorem/result. */
export function safelyFramesUndeliveredRemark(body: string): boolean {
  const text = body.trim();
  return text.length > 0 && OPEN_DIRECTION_RE.test(text) && !ASSERTED_RESULT_RE.test(text) && !ASSERTIVE_REVERSAL_RE.test(text) && !LEGALISTIC_UNDELIVERED_RE.test(text);
}

/** Boundary parse of the P1 notation-reviewer reply. An unusable reply must throw,
 *  not collapse to a clean review: this path previously defaulted to `[]`, so a
 *  reviewer that answered in prose silently passed the notation gate. */
export interface NotationReviewerProblem { symbol?: string; used_in?: string[]; case?: string; fix?: string }
export function parseNotationReviewerOutput(stdout: string): NotationReviewerProblem[] {
  const parsed = parseJsonLoose(stdout) as { clean?: unknown; problems?: unknown } | null;
  if (parsed === null) {
    throw new Error("P1 notation reviewer output is not parseable JSON — re-run P1 (inputs are cached)");
  }
  if (Array.isArray(parsed.problems)) {
    return parsed.problems as NotationReviewerProblem[];
  }
  if (parsed.clean === true) return [];
  throw new Error("P1 notation reviewer output has neither clean:true nor a problems array — re-run P1");
}

/** Reader-facing rendering of a node this run explicitly does not deliver. The agent normally
 * supplies varied prose; deterministic variants are only the fail-closed fallback for an unsafe
 * or missing render. Previously frozen theorem bodies never cross this boundary. */
export function undeliveredRemarkBody(statement: string, reason: string, candidate?: string): string {
  if (candidate && safelyFramesUndeliveredRemark(candidate)) return candidate.trim();
  const claim = statement.trim().replace(/\s+/g, " ");
  const why = reason.trim().replace(/^[a-z0-9-]+:\s*/i, "").replace(/\s+/g, " ");
  const variants = [
    `A natural open question is whether the following proposed conclusion holds: \\emph{${claim}}. Addressing it would require ${why}, and we leave it for future work.`,
    `It remains open in the present framework whether \\emph{${claim}}. The missing ingredient is ${why}; resolving it is a direction for further work.`,
    `One worthwhile direction for future research is to determine whether \\emph{${claim}}. Doing so requires ${why}, which lies beyond the present development.`,
  ];
  const variant = [...claim].reduce((sum, ch) => sum + ch.codePointAt(0)!, 0) % variants.length;
  return variants[variant];
}

/** Select the final JSON/TeX body without letting a stale theorem freeze override a newly
 * undelivered remark. Kept pure so the final-emission boundary has direct regression coverage. */
export function presentedBody(
  deliveryStatus: string | undefined,
  frozenBody: string | undefined,
  loopBody: string | undefined,
): string {
  return deliveryStatus === "undelivered" ? (loopBody ?? "") : (frozenBody ?? loopBody ?? "");
}

/** Outline must place every frozen env exactly once and cite only pool keys. */
function validateOutline(outlineMd: string, ids: string[], poolKeys: Set<string>): string[] {
  const problems: string[] = [];
  const outline = parseOutline(outlineMd);
  if (!outlineMd.trimStart().startsWith("# Title")) {
    problems.push("outline does not start with `# Title` — output-format drift");
  }
  if (outline.sections.length < 3) problems.push(`only ${outline.sections.length} sections parsed`);
  const placed = outline.sections.flatMap((s) => s.objs);
  for (const id of ids) {
    const n = placed.filter((p) => p === id).length;
    if (n !== 1) problems.push(`obj ${id} placed ${n} times (must be exactly 1)`);
  }
  for (const extra of placed.filter((p) => !ids.includes(p) && !/^synth_\d+$/.test(p))) {
    problems.push(`obj ${extra} is not in the frozen layer`);
  }
  for (const key of new Set(outline.sections.flatMap((s) => s.bib))) {
    if (!poolKeys.has(key)) problems.push(`bib key ${key} is not in the citation pool`);
  }
  return problems;
}

/** Place presentation-synthesized setup definitions in the paper outline. They are not graph
 * theorem nodes, but P2 still requires every formal-layer environment to be assigned exactly once. */
export function removeSynthesizedPlacements(outlineMd: string): string {
  return outlineMd.split("\n").map((line) => {
    const prefix = line.match(/^objs:\s*/)?.[0];
    if (!prefix || !line.slice(prefix.length).split(",").some((item) => /^synth_\d+$/.test(item.trim())))
      return line;
    const kept = line.slice(prefix.length).split(",").filter((item) => !/^synth_\d+$/.test(item.trim()));
    return `${prefix}${kept.length > 0 ? kept.join(",") : "none"}`;
  }).join("\n");
}

export function placeSynthesizedDefinitions(
  outlineMd: string,
  ids: string[],
  preferredSectionById: ReadonlyMap<string, string> = new Map(),
  // The deterministic layer order (orderedEnvs ids). When supplied, each synth id is
  // inserted into the objs list at its layer position — immediately before the first
  // env that follows it in the layer — so the PAPER's emission order (objs drives
  // P2's frozen_envs_for_section) matches the dependency order the layer certifies.
  // Without it, legacy behavior: prepend the batch (front of the section).
  layerOrder: readonly string[] = [],
): string {
  const lines = outlineMd.split("\n");
  const current = [...new Set(ids)];
  let sectionName = "";
  const occurrenceSections = new Map<string, string[]>();
  const sectionOrder: string[] = [];
  for (const line of lines) {
    const heading = line.match(/^## section:\s*(.+)$/);
    if (heading) { sectionName = heading[1].trim(); sectionOrder.push(sectionName); continue; }
    const prefix = line.match(/^objs:\s*/)?.[0];
    if (!prefix) continue;
    for (const item of line.slice(prefix.length).split(",").map((part) => part.trim()))
      if (/^synth_\d+$/.test(item)) occurrenceSections.set(item, [...(occurrenceSections.get(item) ?? []), sectionName]);
  }
  const sectionIndex = new Map(sectionOrder.map((name, index) => [name, index] as const));
  const retained = new Set(current.filter((id) => {
    const occurrences = occurrenceSections.get(id) ?? [];
    if (occurrences.length !== 1) return false;
    const preferred = preferredSectionById.get(id);
    return !preferred || (sectionIndex.get(occurrences[0]) ?? Infinity) <= (sectionIndex.get(preferred) ?? -1);
  }));
  // Remove stale, duplicate, and too-late synth placements token-by-token. Raw
  // graph tokens and every line without a removed synth remain byte-identical.
  for (let i = 0; i < lines.length; i++) {
    const prefix = lines[i].match(/^objs:\s*/)?.[0];
    if (!prefix) continue;
    const items = lines[i].slice(prefix.length).split(",");
    if (!items.some((item) => /^synth_\d+$/.test(item.trim()) && !retained.has(item.trim()))) continue;
    const kept = items.filter((item) => !/^synth_\d+$/.test(item.trim()) || retained.has(item.trim()));
    lines[i] = `${prefix}${kept.length > 0 ? kept.join(",") : "none"}`;
  }
  let sectionStart = lines.findIndex((line) => /^## section:.*(?:setup|assumption)/i.test(line));
  if (sectionStart < 0) sectionStart = lines.findIndex((line) => /^## section:/.test(line));
  if (sectionStart < 0) throw new Error("P1 cannot place synthesized definitions: outline has no section");
  const defaultSection = lines[sectionStart].match(/^## section:\s*(.+)$/)![1].trim();
  const missingBySection = new Map<string, string[]>();
  for (const id of current.filter((candidate) => !retained.has(candidate))) {
    const target = sectionIndex.has(preferredSectionById.get(id) ?? "") ? preferredSectionById.get(id)! : defaultSection;
    missingBySection.set(target, [...(missingBySection.get(target) ?? []), id]);
  }
  for (const [target, missing] of missingBySection) {
    const targetStart = lines.findIndex((line) => line.match(/^## section:\s*(.+)$/)?.[1].trim() === target);
    const nextSection = lines.findIndex((line, i) => i > targetStart && /^## section:/.test(line));
    const sectionEnd = nextSection < 0 ? lines.length : nextSection;
    const objsLine = lines.findIndex((line, i) => i > targetStart && i < sectionEnd && /^objs:\s*/.test(line));
    if (objsLine < 0) throw new Error(`P1 cannot place synthesized definitions: section ${target} has no objs line`);
    const prefix = lines[objsLine].match(/^objs:\s*/)![0];
    const existingRaw = lines[objsLine].slice(prefix.length);
    const empty = /^(?:none|\(none\))$/i.test(existingRaw.trim());
    if (layerOrder.length === 0) {
      lines[objsLine] = `${prefix}${missing.join(", ")}${!empty ? "," : ""}${empty ? "" : existingRaw}`;
      continue;
    }
    const pos = new Map(layerOrder.map((id, i) => [id, i] as const));
    const items = empty ? [] : existingRaw.split(",").map((t) => t.trim()).filter(Boolean);
    // Insert earlier-layer synths first so equal insertion points keep layer order.
    for (const id of [...missing].sort((a, b) => (pos.get(a) ?? -1) - (pos.get(b) ?? -1))) {
      const my = pos.get(id);
      let at = 0; // unknown to the layer → front (a prerequisite of another synth)
      if (my !== undefined) {
        const successor = items.findIndex((item) => (pos.get(item) ?? Infinity) > my);
        at = successor < 0 ? items.length : successor;
      }
      items.splice(at, 0, id);
    }
    lines[objsLine] = `${prefix}${items.join(", ")}`;
  }
  return lines.join("\n");
}

/** Deterministic section preference for each synthesized definition: the PAPER-order
 * minimum section over ALL envs that use any of its covered symbols. The planner cannot
 * place synth envs — they are absent from its frozen-layer view — so without this every
 * synthesized definition landed in the setup section regardless of use, making the
 * APPENDIX-ONLY APPARATUS rule unactionable for synthesized apparatus (escalation,
 * 2026-08-20). The preference must NOT follow layer order (topological — a lemma
 * precedes the theorems citing it, inverting paper order routinely): a synth reaches
 * the appendix only when EVERY user is appendix-placed, which is exactly the rule's
 * premise; any main-body user pulls the definition to that earlier section (audit
 * counterexample, 2026-08-20). No user found, a user unplaced, or ANOTHER synth env
 * using the symbol (mutual synth sections are undetermined at preference time) → no
 * preference (fail-safe to the setup default, which precedes everything). No model
 * call. */
export function preferredSectionsForSynths(
  outlineMd: string,
  graphEnvs: readonly { id: string; body: string; title?: string }[],
  symbolsBySynthId: ReadonlyMap<string, readonly string[]>,
  synthEnvs: readonly { id: string; body: string; title?: string }[] = [],
): Map<string, string> {
  const sectionByEnv = new Map<string, string>();
  const sectionIndex = new Map<string, number>();
  let section = "";
  for (const line of outlineMd.split("\n")) {
    const heading = line.match(/^## section:\s*(.+)$/);
    if (heading) {
      section = heading[1].trim();
      if (!sectionIndex.has(section)) sectionIndex.set(section, sectionIndex.size);
      continue;
    }
    const prefix = line.match(/^objs:\s*/)?.[0];
    if (!prefix || !section) continue;
    for (const item of line.slice(prefix.length).split(",").map((t) => t.trim()))
      if (item && !/^(?:none|\(none\))$/i.test(item)) sectionByEnv.set(item, section);
  }
  const out = new Map<string, string>();
  for (const [synthId, symbols] of symbolsBySynthId) {
    const synthUser = synthEnvs.some((e) =>
      e.id !== synthId && symbols.some((symbol) => usesSymbolUndecorated(`${e.title ?? ""} ${e.body}`, symbol)));
    if (synthUser) continue;
    let best: string | undefined;
    let unplacedUser = false;
    for (const e of graphEnvs) {
      const text = `${e.title ?? ""} ${e.body}`;
      if (!symbols.some((symbol) => usesSymbolUndecorated(text, symbol))) continue;
      const s = sectionByEnv.get(e.id);
      if (!s) { unplacedUser = true; break; }
      if (best === undefined || (sectionIndex.get(s) ?? Infinity) < (sectionIndex.get(best) ?? Infinity)) best = s;
    }
    if (best !== undefined && !unplacedUser) out.set(synthId, best);
  }
  return out;
}

/** Normalized ledger key for a requested notation symbol: one synthesis attempt per key, ever. */
export const synthLedgerKey = (symbol: string): string => definingNotationKey(symbol);

/** One synthesis attempt, recorded durably in p1_cache.json. `accepted:false` means the
 * attempt failed (rejected output or model error); the symbol becomes a checkpoint
 * advisory and is never re-dispatched. `accepted:true` carries the definition itself —
 * the cache, not the emitted TeX, is the recovery source across re-runs. */
export interface SynthLedgerEntry {
  symbol: string;
  accepted: boolean;
  id?: string;
  title?: string;
  body?: string;
}

/** Deterministic layer order: graph environments keep their topological graph order;
 * each synthesized definition is inserted immediately before its first user (the first
 * environment whose title/body uses the symbol it was synthesized for), so a definition
 * always precedes its uses without any prose-certification machinery. A synthesized
 * definition nothing visibly uses goes to the front (it is a prerequisite of another
 * synthesized block whose spelling drifted — harmless placement, never a lost env). */
export function orderEnvsForLayer(
  graphEnvsInOrder: P1Env[],
  synthEnvs: P1Env[],
  // A CONSOLIDATED synthesized definition covers several symbols; placement must
  // precede the FIRST use of ANY of them (splicing by one arbitrary sibling let the
  // others be used before their definition — a hard P3 definition-order failure).
  symbolsBySynthId: ReadonlyMap<string, readonly string[]>,
  titleById: ReadonlyMap<string, string>,
): P1Env[] {
  const out = [...graphEnvsInOrder];
  const sorted = [...synthEnvs].sort((a, b) =>
    Number(a.id.slice("synth_".length)) - Number(b.id.slice("synth_".length)));
  for (const synth of sorted) {
    const symbols = symbolsBySynthId.get(synth.id) ?? [];
    const firstUses = symbols
      .map((symbol) => out.findIndex((e) => e.id !== synth.id &&
        containsNotation(`${titleById.get(e.id) ?? ""} ${e.body}`, symbol)))
      .filter((i) => i >= 0);
    const at = firstUses.length > 0 ? Math.min(...firstUses) : -1;
    out.splice(at >= 0 ? at : 0, 0, synth);
  }
  return out;
}

/** Route the notation reviewer's problems to loop findings. Pure so the routing policy —
 * the single semantic notation authority — has direct regression coverage.
 *
 * - `undefined`/`no-anchor`: synthesize a paper definition, UNLESS the symbol is
 *   Lean-realized (then the designated graph home must display it — re-render that env in
 *   place; presentation-only synthesis would compete with the Lean-backed authority), or
 *   the ledger already holds an attempt (one attempt per symbol, ever — further reports
 *   become non-blocking checkpoint advisories).
 * - `wrong-ref`/`mismatch`: re-render each using env with the defect.
 * - anything else: halt (fail loud on reviewer drift).
 */
export function routeNotationProblems(
  problems: NotationReviewerProblem[],
  opts: {
    isLeanRealized: (symbol: string) => boolean;
    designatedHomeFor: (symbol: string) => string | undefined;
    ledgerHas: (key: string) => boolean;
    graphNodeIds: ReadonlySet<string>;
    lockedIds: ReadonlySet<string>;
  },
): P1Finding[] {
  return problems.flatMap<P1Finding>((p) => {
    // A problem without a symbol cannot be routed — fail loud rather than silently
    // discard a defect the reviewer reported.
    if (!p.symbol) {
      return [{ gate: "notation-reviewer", fixLocus: "halt", detail: `reviewer reported a symbol-less problem [${p.case ?? "?"}] — ${p.fix ?? "unroutable"}` }];
    }
    const symbol = p.symbol;
    const detail = `${symbol} [${p.case ?? "?"}] in ${(p.used_in ?? []).join("/")} — ${p.fix ?? ""}`;
    if (p.case === "undefined" || p.case === "no-anchor") {
      // HOME-FIRST for ANY symbol, not only Lean-realized ones: when the notation table
      // designates an editable graph-env home, the symbol is defined THERE (journal
      // style — notation lives with the object that owns it: witness values inside the
      // witness definition, arm masses inside the estimator). Synthesizing a standalone
      // micro-definition is the LAST resort, for symbols with no natural owner; the
      // over-synthesis it produced (34 of 68 envs) read as machine clutter.
      const home = opts.designatedHomeFor(symbol);
      const editable = home && opts.graphNodeIds.has(home) && !opts.lockedIds.has(home);
      if (editable) {
        return [{
          gate: "notation-reviewer", objId: home, symbol, fixLocus: "wording-revise",
          detail: `${detail} (display its defining content in its home ${home}, do not synthesize a standalone duplicate)`,
        }];
      }
      if (opts.isLeanRealized(symbol)) {
        return [{
          gate: "notation-reviewer", symbol, fixLocus: "halt",
          detail: `${detail} (Lean-realized symbol with no editable designated home — fix the notation table or the graph env)`,
        }];
      }
      // The ledger is keyed per ATOM (the loop splits a compound reviewer symbol
      // before synthesis), so check the atoms: a compound report whose every atom
      // already used its one attempt must become an advisory, not an eternal
      // synthesize-def that idles the loop to its cap. A symbol that splits to
      // NOTHING (delimiter/whitespace-only) can never be synthesized — halt loud
      // rather than dispatch a no-op that idles the loop.
      const atoms = atomicRequestedNotationSymbols(symbol);
      if (atoms.length === 0) {
        return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail: `${detail} (symbol has no synthesizable atom)` }];
      }
      if (atoms.every((atom) => opts.ledgerHas(synthLedgerKey(atom)))) {
        return [{ gate: "notation-unresolved", symbol, detail: `${detail} (synthesis already attempted once — resolve at the checkpoint)` }];
      }
      return [{ gate: "notation-reviewer", symbol, fixLocus: "synthesize-def", detail }];
    }
    if (p.case === "wrong-ref" || p.case === "mismatch") {
      // No usable env target → halt (fail loud) instead of mapping to zero findings.
      const targets = (p.used_in ?? []).filter(Boolean);
      if (targets.length === 0) {
        return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail: `${detail} (no used_in env to revise)` }];
      }
      return targets.map((objId) => ({
        gate: "notation-reviewer", objId, fixLocus: "wording-revise" as const, detail,
      }));
    }
    return [{ gate: "notation-reviewer", symbol, fixLocus: "halt", detail }];
  });
}

/** Convert a deterministic LintProblem to a loop finding (gate/objId/detail carry over). */
const toFinding = (p: LintProblem): P1Finding => ({ gate: p.gate, objId: p.objId, detail: p.detail });


/** Failure-path diagnostic dumps land under logs/ so the bundle root stays durable-only. */
async function writeDiagnostic(outDir: string, name: string, content: string): Promise<void> {
  const dir = join(outDir, "logs");
  await mkdir(dir, { recursive: true });
  await writeFile(join(dir, name), content, "utf8");
}

/**
 * P1 — paper plan + frozen formal layer, as the executor→reviewer→router loop.
 * Statements come from the graph (`nl.statement`); the codex executor renders them to
 * paper prose; ONE semantic authority — the codex notation reviewer — plus a floor of
 * mechanical lints check readability / self-containment / notation; the router
 * re-renders, or synthesizes a missing definition (once per symbol, ledgered), or
 * halts. Frozen bodies are then hash-pinned, audited against Lean, and the dispatcher
 * halts at the outline checkpoint, where unresolved-notation advisories surface for
 * the orchestrator.
 */

/** P1 render-cache key. `envHint` is appended ONLY when non-empty so objects without an
 * env override hash byte-identically to the legacy (pre-override) formula — an
 * unconditional "" element would still emit a "§" and cold every render cache. */
export function renderCacheKey(
  renderModelKey: string,
  r: { statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: unknown },
  citedPrompt: string,
  envHint: string,
): string {
  return hashEnvBody([
    renderModelKey,
    r.statement,
    [...r.refSet].sort().join(","),
    r.priorBody ?? "",
    (r.defects ?? []).join("|"),
    JSON.stringify(r.delivery ?? null),
    citedPrompt,
    ...(envHint ? [envHint] : []),
  ].join("§"));
}

export async function stageP1(io: StageIO): Promise<void> {
  await mkdir(io.outDir, { recursive: true });
  if (io.ctx.deps.dryRun) {
    await writeFile(join(io.outDir, "p1.stub"), "dry-run\n");
    return;
  }
  const { deps, repoRoot } = io.ctx;
  const graph = io.bank.graph;
  // D-stage narrative layer (UNTRUSTED pre-formalization prose; authoring uses are
  // subordinated to the frozen layer, restriction-shaped fields feed detectors).
  const narrative = await loadBankNarrative(io.ctx.repoRoot, io.ctx.qid, io.ctx.spec);
  const dstageDefinitionContext = [
    narrative.definitionList && `D-stage definition constructions (source of truth for named objects):\n${narrative.definitionList}`,
    narrative.symbolTable && `D-stage symbol table:\n${narrative.symbolTable}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  const nodes = topoOrder(graph, renderedNodes(graph));
  if (nodes.length === 0) throw new Error("P1: graph has no frozen paper-env nodes to render");
  const nodeIds = nodes.map((n) => n.id);
  const refTargetsById = new Map(
    nodes.map((n) => [n.id, new Set(refTargets(graph, n.id).map((t) => t.id))]),
  );
  const citedDepsById = new Map(nodes.map((n) => [n.id, citedDependencies(graph, n.id)] as const));
  const citedPromptFor = (id: string): string => {
    const deps = citedDepsById.get(id) ?? [];
    if (deps.length === 0) return "(none — do not erase any Lean hypothesis)";
    return deps.map((d) =>
      `- ${d.lean.decl_name ?? d.id}: ${d.nl.statement.replace(/\s+/g, " ").trim()} ` +
      `[source ${d.gate?.source ?? "missing"}; source-matched status ${d.review.status}]`,
    ).join("\n");
  };

  const brief = await readFile(join(io.outDir, "related_work_brief.md"), "utf8");
  const bibText = await readFile(join(io.outDir, "references.bib"), "utf8");
  const poolKeys = new Set(parseBib(bibText).map((e) => e.key));
  // Inline-citation key per CITED node: reconcile its `gate.source` slug to the P0-curated
  // bib key (surname ⊂ author AND equal year) so the touch-up render attributes the imported
  // result with `\citet{<key>}` rather than hardcoded author-year text. Graph-only, match-only:
  // a slug with no confident bib match is simply omitted (the render falls back to plain prose).
  const bibIndex = indexBib(bibText);
  const citeKeyById = new Map<string, string>();
  for (const n of graph.nodes) {
    if (!isCitedNode(n)) continue;
    const std = citedStdFromNode(n);
    if (!std) continue;
    const { citeKey } = reconcileCite(std, bibIndex);
    if (poolKeys.has(citeKey)) citeKeyById.set(n.id, citeKey);
  }
  const locatorById = new Map<string, string>();
  const passedCitedChecks = new Set<string>();
  for (const check of io.bank.citedChecks ?? []) {
    if (check.locator && !locatorById.has(check.name)) locatorById.set(check.name, check.locator);
    if (["cited-verified", "cited-verified-attested"].includes(check.check_status)) {
      passedCitedChecks.add(check.name);
    }
  }
  const usedCited = [...new Map(
    [...citedDepsById.values()].flat().map((n) => [n.id, n] as const),
  ).values()];
  const unsafeCited = usedCited.filter((n) => !passedCitedChecks.has(n.id) || !citeKeyById.has(n.id));
  if (unsafeCited.length > 0) {
    throw new Error(
      "P1 citation erasure refused: each hidden cited premise needs a persisted verified/attested " +
      "source-match and a resolvable references.bib key — " +
      unsafeCited.map((n) => `${n.id} (check=${passedCitedChecks.has(n.id)}, bib=${citeKeyById.has(n.id)})`).join(", "),
    );
  }

  // P5 revision is owned by the single holistic reviser. P1 is initial planning
  // only and must not independently reinterpret a prior referee report, so the
  // outline prompt's revision slot always carries the inert first-draft brief.
  const outlineBrief = FIRST_DRAFT_BRIEF;

  const t0 = Date.now();
  const log = (m: string) => console.error(`[causalsmith P1] +${Math.round((Date.now() - t0) / 1000)}s ${m}`);
  log(`graph: ${nodes.length} frozen paper-env nodes → ${nodeIds.join(", ")}`);

  // Content-keyed cache (cost economy — a re-run only re-pays for changed inputs).
  // `render`: keyed by the touch-up input → {title, body}. `notation`: keyed by the layer
  // hash → the RAW reviewer problems (routing is re-derived on every read, so ledger/policy
  // changes apply to cached reviews too). `synth`: the per-symbol synthesis ledger AND the
  // durable store of accepted definitions (recovery source across re-runs — no TeX
  // re-parsing). Delete the file to force a full re-render.
  const cachePath = join(io.outDir, "p1_cache.json");
  type RenderHit = { title?: string; body: string };
  const cache: {
    render: Record<string, RenderHit>;
    notation: Record<string, NotationReviewerProblem[]>;
    synth: Record<string, SynthLedgerEntry>;
    /** Mechanical-failure retry counts per ledger key: the unparseable-reply un-burn
     * grants ONE retry, ever — unbounded un-burning re-dispatched the same symbols
     * round after round (measured 2-3x per symbol, 2026-08-20 token audit). */
    synthRetries?: Record<string, number>;
    outlineStructureKey?: string;
  } = await loadJsonCache(cachePath, { defaults: { render: {}, notation: {}, synth: {} } });
  const saveCache = () => writeJsonAtomic(cachePath, cache); // why: a crash mid-write must not corrupt the render cache (next run would throw on parse).

  // Model + prompt fingerprints: hashing the actual prompt templates into each cache key
  // makes prompt edits self-invalidating — no manually bumped version strings. One
  // fingerprint PER CONSUMER (outline / render / notation), so editing e.g. the synthesis
  // prompt does not needlessly cold every render cache and force an outline regeneration.
  // Shared with the P3 rubric key; the formula lives in prompt_io so both consumers hash
  // identically (see `promptFingerprint`).
  const promptFp = promptFingerprint;
  const modelKeyBase = `${io.ctx.deps.codexModel ?? "unspecified-codex-model"}|${PRESENTATION_PROSE_POLICY_VERSION}`;
  const outlineModelKey = `${modelKeyBase}|${await promptFp("p1_plan")}`;
  const renderModelKey = `${modelKeyBase}|${await promptFp("p1_touchup", "p1_render_from_lean")}`;
  const notationModelKey = `${modelKeyBase}|${await promptFp("p1_notation_check")}`;
  const renderKey = (r: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] }) =>
    renderCacheKey(renderModelKey, r, citedPromptFor(r.id), envHintFor(r.id));

  // ── Outline (executor / codex): structure + notation table over the mechanical layer.
  // Cache by presence: a valid existing outline.md is REUSED (structure must not silently
  // change on a re-run). `validateOutline` guards staleness: if the env set changed since
  // the outline was written, an env is no longer placed exactly once → regenerate.
  // Delete outline.md to force a fresh structure.
  const mechanical = renderMechanicalLayer(nodes);
  // D-stage contribution narrative for the outline planner (subordinated; honest_scope
  // doubles as a framing constraint alongside the REFUTED/DEAD-OBJECTS rule).
  const outlineNarrative = [
    narrative.tldr && `TLDR (pre-formalization research summary):\n${narrative.tldr}`,
    narrative.projectJustification && `Project justification:\n${narrative.projectJustification}`,
    narrative.interpretation && `Interpretation:\n${narrative.interpretation}`,
    narrative.honestScope && `Honest scope (claims the research stage itself disclaims):\n${narrative.honestScope}`,
  ].filter(Boolean).join("\n\n") || "(none recorded)";
  const outlineStructureKey = hashEnvBody([
    outlineModelKey,
    nodes.map((n) => `${n.id}:${n.kind}`).join(","),
    [...poolKeys].sort().join(","),
    brief,
    outlineBrief,
    outlineNarrative,
  ].join("§"));
  const existingOutline = (await readFile(join(io.outDir, "outline.md"), "utf8").catch(() => "")).trim();
  let outlineMd: string;
  if (existingOutline && cache.outlineStructureKey === outlineStructureKey &&
      validateOutline(existingOutline, nodeIds, poolKeys).length === 0) {
    outlineMd = existingOutline;
    log("outline: reusing existing valid outline.md (no restructure on re-run)");
  } else {
    log(
      `outline: calling codex…${
        existingOutline ? " (existing outline invalid for current env set — regenerating)" : ""
      }`,
    );
    const baseOutlinePrompt = await presentationPrompt("p1_plan", {
        note_md: io.bank.noteMd,
        contribution_narrative: outlineNarrative,
        related_work_brief: brief,
        frozen_layer_tex: mechanical,
        pool_keys: [...poolKeys].join(", "),
        revision_brief: outlineBrief,
        // why: reruns with a valid existing outline must preserve structure unless a structural P5 brief requested movement.
        prior_outline: existingOutline || "(first draft — no prior structure to preserve)",
      });
    let outlineProblems: string[] = [];
    outlineMd = "";
    for (let attempt = 0; attempt < 2; attempt++) {
      const repair = attempt === 0 ? "" : [
        "\n\nREPAIR THE PREVIOUS OUTLINE. The deterministic validator rejected it for:",
        ...outlineProblems.map((p) => `- ${p}`),
        "Return a complete replacement outline. In particular, every `bib:` key must be copied verbatim from the verified pool above; keys mentioned in the note or related-work brief but absent from that pool do not exist.",
        "\nPrevious rejected outline:\n",
        outlineMd,
      ].join("\n");
      const outlineRes = await deps.runCodex({
        prompt: baseOutlinePrompt + repair,
        cwd: repoRoot,
        reasoningEffort: "medium",
        leanLsp: false,
        webSearch: true,
      });
      outlineMd = unwrapArtifact(outlineRes.stdout, ["markdown", "md"], "outline_md");
      outlineProblems = validateOutline(outlineMd, nodeIds, poolKeys);
      if (outlineProblems.length === 0) break;
      await writeDiagnostic(io.outDir, "outline_rejected.md", outlineMd + "\n");
      log(`outline: rejected attempt ${attempt + 1}/2 — ${outlineProblems.join("; ")}`);
    }
    if (outlineProblems.length > 0) {
      throw new Error(`P1 outline invalid after repair: ${outlineProblems.join("; ")}`);
    }
    await writeFile(join(io.outDir, "outline.md"), outlineMd + "\n", "utf8");
    cache.outlineStructureKey = outlineStructureKey;
    await saveCache();
    log("outline: ok");
  }
  // Placement enforcement: an object a MAIN-BODY theorem uses IN ITS STATEMENT must not be
  // defined only in an appendix (user directive 2026-08-21 — "important objects like theta hat
  // must be in the main body"). Advisory rather than fatal: the outline may be operator-curated
  // mid-run, and halting P1 over placement would cost a full cycle for something a checkpoint
  // reader can fix in one line. It is logged loudly and carried into the checkpoint findings.
  {
    const statementUsesOf = (id: string): string[] =>
      graph.edges.filter((e) => e.kind === "statement-uses" && e.from === id).map((e) => e.to);
    const kindOf = (id: string): string | undefined => graph.nodes.find((n) => n.id === id)?.kind;
    const placementProblems = lintMainBodyDependencies(parseOutline(outlineMd), statementUsesOf, kindOf);
    for (const m of placementProblems) log(`placement: ${m}`);
  }
  const notation = parseOutline(outlineMd).notation;
  // Objects the planner re-kinded to `algorithmv` render as numbered-step procedures: the touchup
  // prompt is told so (`environment: algorithmv`) and the hint joins the render cache key.
  const envHintFor = (id: string): string =>
    parseOutline(outlineMd).envOverrides[id] === "algorithmv" ? "environment: algorithmv" : "";
  const leanDir = join(repoRoot, io.bank.leanSubdir);
  const realizedSymbols = await discoverRealizedSymbols(leanDir);
  const isLeanRealizedNotation = buildRealizedNotationMatcher(realizedSymbols);
  const realizedList = realizedSymbols.length > 0
    ? realizedSymbols.map((s) => `- ${s}`).join("\n")
    : "(none — this paper has no @realizes-tagged symbols)";
  if (realizedSymbols.length > 0) {
    log(`notation: ${realizedSymbols.length} Lean-realized symbol(s) available as authoritative homes`);
  }
  // Designated home for a symbol: the notation-table row whose symbol normalizes to the
  // same key. Simple table lookup — the reviewer owns all semantic judgment.
  const designatedHomeFor = (symbol: string): string | undefined =>
    notationHomes(notation).find((row) => definingNotationKey(row.symbol) === definingNotationKey(symbol))?.home;

  // ── Loop hooks (the model calls runP1Loop orchestrates).
  // Titles are carried in a side-map (the render emits them; the loop tracks only bodies).
  const titleById = new Map<string, string>();
  const graphNodeIds = new Set(nodes.map((n) => n.id));
  let lockedIds = new Set<string>();
  // Locked envs: a P3-validated frozen body persisted on the node (`nl.frozen_body`) — used VERBATIM
  // so a P1 re-run cannot revert the tightening P3 reconciled to Lean. They are NOT rendered or
  // re-gated; they appear in the reviewed layer only so a loose env's `\ref` to a locked env resolves.
  // A delivery-role change invalidates the old P3 body. In particular, a theorem body frozen
  // before the node became `undelivered` must never be copied verbatim into a remark: that would
  // re-publish the very claim the delivery decision omitted. Undelivered nodes therefore always
  // take the loose path, where the deterministic renderer below replaces the body completely.
  // Cited-dependency envs USED to be excluded so citation-erasure policy changes would force a
  // fresh render — but that safety now lives in the statement audit, which still audits locked
  // envs and keys on the cited-dependency text plus the erasure-policy token (a policy change
  // misses the verdict cache; genuine drift halts as locked-env-drift). The exclusion's only
  // remaining effect was making operator wording fixes on such envs unfixable (the freeze was
  // silently ignored and the renderer regenerated the flagged identifiers every run).
  // An `algorithmv` override on a node with a frozen body is self-defeating: the box prints
  // numbered steps, but a frozen body is emitted VERBATIM, so the reader gets an "Algorithm"
  // wrapping unstepped prose. Release the BODY lock for exactly those nodes so the renderer can
  // step them under the ALGORITHM BODY rule. Never touch `nl.frozen` — that field is paper-env
  // membership (`renderedNodes`), and clearing it deletes the environment from the paper. The
  // statement audit still gates the re-rendered body, and P3 re-freezes what it validates.
  const outlineEnvOverrides = parseOutline(outlineMd).envOverrides;
  // The layer written DURING the P1 loop must agree with the layer built after it: the post-loop
  // view derives from `formal_layer.json`, whose blocks apply `env_overrides` (blocksFromGraph),
  // while the in-loop `assemble` used the raw `envForNode`. On a NON-CONVERGED run only the
  // in-loop view survives, so an operator inspecting formal_layer.tex saw `definitionv` for an
  // object the pipeline had correctly re-kinded — and read it as "the renderer ignored the
  // override" (sa_plm 2026-08-21). One resolver, both views.
  const envForNodeWithOverride = (n: Parameters<typeof envForNode>[0]) =>
    (outlineEnvOverrides[n.id] as ReturnType<typeof envForNode>) ?? envForNode(n);
  const steppedNodes = nodes.filter((n) => n.nl.frozen_body && outlineEnvOverrides[n.id] === "algorithmv");
  const lockedNodes = nodes.filter((n) =>
    n.nl.frozen_body && n.delivery?.status !== "undelivered" && outlineEnvOverrides[n.id] !== "algorithmv",
  );
  if (steppedNodes.length > 0) {
    log(`algorithmv: body lock released so the renderer can step ${steppedNodes.map((n) => n.id).join(", ")} (frozen membership kept; audit still gates)`);
  }
  const looseNodes = nodes.filter((n) => !lockedNodes.includes(n));
  lockedIds = new Set(lockedNodes.map((n) => n.id));
  for (const n of lockedNodes) if (n.nl.frozen_title != null) titleById.set(n.id, n.nl.frozen_title);
  const lockedEnvs: P1Env[] = lockedNodes.map((n) => ({
    id: n.id,
    env: envForNodeWithOverride(n)!,
    statement: n.nl.statement,
    body: normalizeCrefs(n.nl.frozen_body!),
    refSet: [...(refTargetsById.get(n.id) ?? [])],
  }));
  if (lockedNodes.length > 0) log(`locked (P3-validated frozen_body, verbatim — not re-rendered): ${[...lockedIds].join(", ")}`);

  // Lean-aware rendering: a theorem/lemma's PAPER statement is rendered DIRECTLY from its
  // machine-verified Lean signature (complete + curated), not from a possibly-loose NL "headline" —
  // so it carries every load-bearing hypothesis on the FIRST render and P3 confirms rather than
  // reconstructs (the headline gap is what made re-runs drift). Built for the loose theorem/lemma
  // nodes with a resolvable Lean decl; definitions/assumptions/statement-only keep the NL render.
  const kindById = new Map(nodes.map((n) => [n.id, n.kind] as const));
  const leanIndex = await buildLeanContextIndex(repoRoot, io.bank.leanSubdir);
  const leanCtxById = new Map<string, LeanContext>();
  for (const n of looseNodes) {
    if ((n.kind === "theorem" || n.kind === "lemma") && n.lean.decl_name && n.lean.file) {
      const ctx = await leanIndex.contextFor({ decl_name: n.lean.decl_name, file: n.lean.file });
      if (ctx) leanCtxById.set(n.id, ctx);
    }
  }
  if (leanCtxById.size > 0) log(`Lean-aware render: ${leanCtxById.size} theorem/lemma statement(s) will render from Lean`);

  // Synthesized-definition bookkeeping (backed by cache.synth — the ledger).
  const symbolsBySynthId = new Map<string, string[]>();
  for (const e of Object.values(cache.synth)) {
    if (e.accepted && e.id) symbolsBySynthId.set(e.id, [...(symbolsBySynthId.get(e.id) ?? []), e.symbol]);
  }
  // A consolidated synthesized definition may cover SEVERAL ledger symbols; map the env
  // id to every backing ledger key so body write-backs update all of them together.
  const ledgerKeysBySynthId = new Map<string, string[]>();
  for (const [k, e] of Object.entries(cache.synth)) {
    if (e.accepted && e.id) ledgerKeysBySynthId.set(e.id, [...(ledgerKeysBySynthId.get(e.id) ?? []), k]);
  }
  let synthCount = Math.max(0, ...[...symbolsBySynthId.keys()].map((id) => Number(id.slice("synth_".length))).filter(Number.isFinite));

  const nodeOrder = new Map(nodes.map((n, i) => [n.id, i] as const));
  const orderLayerEnvs = (envs: P1Env[]): P1Env[] => {
    const all = [...envs, ...lockedEnvs];
    const graphEnvs = all.filter((e) => !e.id.startsWith("synth_"))
      .sort((a, b) => (nodeOrder.get(a.id) ?? 0) - (nodeOrder.get(b.id) ?? 0));
    const synthEnvs = all.filter((e) => e.id.startsWith("synth_"));
    return orderEnvsForLayer(graphEnvs, synthEnvs, symbolsBySynthId, titleById);
  };
  const assemble = (envs: P1Env[]): string =>
    [
      "% Frozen formal layer — causalsmith P1 (graph render). Bodies are hash-pinned; do not edit.",
      ...orderLayerEnvs(envs).flatMap((e) => {
        const t = titleById.get(e.id);
        return [`\\begin{${e.env}}{${e.id}}${t ? `[${t}]` : ""}`, e.body, `\\end{${e.env}}`, ""];
      }),
    ].join("\n");

  // The semantic reviewer treats `D_{G_i t}` and `D_{G_i,t}` as distinct notation.
  // Synthesized prose used to oscillate between the two spellings across repair rounds,
  // consuming the bounded loop without changing any mathematical content. Keep the graph's
  // comma-free cohort-time convention for synthetic setup definitions only.
  const normalizeSynthNotation = (body: string): string =>
    body
      // Raw LaTeX such as `\to` is a valid JSON `\t` escape followed by `o`;
      // JSON.parse then produces a literal tab and invalid TeX. Restore ONE
      // backslash: in a JS replacement string a backslash is not special, so
      // the earlier `"\\\\t"` inserted the two chars `\\` — a TeX row break —
      // and froze `x \\to y` into formal_layer.json.
      .replace(/\t(?=[A-Za-z])/g, "\\t")
      .replace(/D_\{G_i,\s*t\}/g, "D_{G_i t}");

  /** Parse the delimiter-based render output (robust to multi-line LaTeX, which a
   *  JSON container mangles via unescaped newlines). Format per env:
   *    @@@ENV <obj_id>@@@\nTITLE: <title>\n@@@BODY@@@\n<body…>\n@@@END@@@        */
  const parseRender = (text: string): Map<string, { title?: string; body: string }> => {
    const out = new Map<string, { title?: string; body: string }>();
    const re = /@@@ENV\s+(\S+?)@@@\s*\n(?:TITLE:\s*(.*)\n)?@@@BODY@@@\s*\n([\s\S]*?)\n?@@@END@@@/g;
    let m: RegExpExecArray | null;
    while ((m = re.exec(text))) {
      const body = m[3].trim();
      if (body !== "") out.set(m[1].trim(), { title: m[2]?.trim() || undefined, body });
    }
    return out;
  };

  const BATCH = 6;
  type RenderReq = { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] };
  const enforceUndeliveredDisclosure = (r: RenderReq, body: string): string => {
    if (r.delivery?.status !== "undelivered") return body;
    const framed = undeliveredRemarkBody(r.statement, r.delivery.reason, body);
    if (framed !== body.trim()) titleById.set(r.id, "Open direction");
    return framed;
  };
  const renderBatch = async (reqs: RenderReq[]): Promise<Map<string, RenderHit>> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_touchup", {
        notation_table: notation,
        envs_block: reqs
          .map((r) =>
            [
              `### ${r.id}`,
              `ref_set: ${r.refSet.join(", ") || "(none)"}`,
              `cited_dependencies: ${citedPromptFor(r.id)}`,
              r.delivery ? `delivery_status: ${r.delivery.status}\ndelivery_role: ${r.delivery.role ?? "secondary"}\ndelivery_reason: ${r.delivery.reason}\nenvironment: remarkv` : envHintFor(r.id),
              `statement: ${r.statement}`,
              r.priorBody ? `prior_body: ${r.priorBody}` : "",
              r.defects ? `defects: ${r.defects.join(" | ")}` : "",
            ]
              .filter(Boolean)
              .join("\n"),
          )
          .join("\n\n"),
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const parsed = parseRender(res.stdout);
    if (parsed.size < reqs.length) {
      await writeDiagnostic(io.outDir, "p1_render_raw.txt", res.stdout.slice(0, 20000));
    }
    return parsed;
  };

  // Cache key for a Lean-rendered env: depends on the LEAN statement (so an edited Lean re-renders),
  // not the NL headline. Separate from `renderKey` so the two render modes never collide.
  const leanKey = (r: RenderReq, ctx: LeanContext): string =>
    hashEnvBody([
      renderModelKey,
      ctx.statement,
      [...r.refSet].sort().join(","),
      citedPromptFor(r.id),
      r.priorBody ?? "",
      (r.defects ?? []).join("|"),
      JSON.stringify(r.delivery ?? null),
      "lean-render",
    ].join("§"));
  /** Render one theorem/lemma statement directly from its Lean signature + referenced defs. Output is
   *  the same `@@@ENV/TITLE/BODY` envelope the NL render uses, so `parseRender` handles both. */
  const renderFromLean = async (r: RenderReq, ctx: LeanContext): Promise<RenderHit | null> => {
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_render_from_lean", {
        obj_id: r.id,
        kind: kindById.get(r.id) ?? "theorem",
        lean_statement: ctx.statement,
        referenced_defs: ctx.referencedDefs || "(none indexed — the statement references no local definitions)",
        nl_statement: r.statement,
        ref_set: r.refSet.join(", ") || "(none)",
        cited_dependencies: citedPromptFor(r.id),
        notation_table: notation,
        prior_and_defects: r.defects ? `prior_body: ${r.priorBody ?? ""}\ndefects: ${r.defects.join(" | ")}` : "(first render — none)",
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const hit = parseRender(res.stdout).get(r.id);
    if (!hit) await writeDiagnostic(io.outDir, "p1_render_from_lean_raw.txt", res.stdout.slice(0, 20000));
    return hit ?? null;
  };

  const render: P1LoopHooks["render"] = async (reqs) => {
    const out = new Map<string, string>();
    const canonicalOut = (): Map<string, string> =>
      new Map([...out].map(([id, body]) => [id, normalizeCrefs(body)]));
    const keyById = new Map<string, string>();
    const leanMiss: { r: RenderReq; ctx: LeanContext }[] = [];
    const nlMiss: RenderReq[] = [];
    for (const r of reqs) {
      // A synthesized definition's body IS its authored content (cache.synth) — it is not
      // re-rendered unless the reviewer raised defects against it.
      if (r.id.startsWith("synth_") && !r.defects) {
        const entry = cache.synth[ledgerKeysBySynthId.get(r.id)?.[0] ?? ""];
        if (entry?.body != null) {
          out.set(r.id, normalizeSynthNotation(entry.body));
          continue;
        }
      }
      const ctx = leanCtxById.get(r.id);
      const k = ctx ? leanKey(r, ctx) : renderKey(r);
      keyById.set(r.id, k);
      // A defect-driven render is itself evidence that the prior body is unsuitable. Never let
      // that response become a fixed point by reusing its cache entry on the next repair round.
      const hit = r.defects ? undefined : cache.render[k];
      if (hit) {
        out.set(r.id, r.id.startsWith("synth_")
          ? normalizeSynthNotation(hit.body)
          : enforceUndeliveredDisclosure(r, hit.body));
        if (hit.title) titleById.set(r.id, hit.title);
      } else if (ctx) leanMiss.push({ r, ctx });
      else nlMiss.push(r);
    }
    const acceptHit = (r: RenderReq, hit: RenderHit) => {
      out.set(r.id, r.id.startsWith("synth_")
        ? normalizeSynthNotation(hit.body)
        : enforceUndeliveredDisclosure(r, hit.body));
      if (hit.title) titleById.set(r.id, hit.title);
      const k = keyById.get(r.id);
      if (k) cache.render[k] = hit;
      // Keep the ledger's stored body in step with a defect-driven synth re-render,
      // so a later re-run recovers the repaired definition, not the flagged one.
      for (const ledgerKey of ledgerKeysBySynthId.get(r.id) ?? []) {
        if (cache.synth[ledgerKey]) {
          cache.synth[ledgerKey] = { ...cache.synth[ledgerKey], body: normalizeSynthNotation(hit.body), title: hit.title ?? cache.synth[ledgerKey].title };
        }
      }
    };
    const total = leanMiss.length + nlMiss.length;
    if (total === 0) {
      log(`render: all ${reqs.length} env(s) cached`);
      log(`render: ${out.size}/${reqs.length} bodies`);
      return canonicalOut();
    }
    log(`render: ${reqs.length - total} cached, ${leanMiss.length} from Lean + ${nlMiss.length} from NL via codex${reqs[0]?.defects ? " (re-render)" : ""}…`);
    // Lean-aware renders run per-node (bounded concurrency); a parse-miss falls back to the NL batch.
    const leanFallback: RenderReq[] = [];
    await mapLimit(leanMiss, 4, async ({ r, ctx }) => {
      const hit = await renderFromLean(r, ctx);
      if (hit) acceptHit(r, hit);
      else leanFallback.push(r);
    });
    const nlAll = [...nlMiss, ...leanFallback];
    if (nlAll.length > 0) {
      const chunks: RenderReq[][] = [];
      for (let i = 0; i < nlAll.length; i += BATCH) chunks.push(nlAll.slice(i, i + BATCH));
      const maps = await Promise.all(chunks.map((c) => renderBatch(c)));
      const missById = new Map(nlAll.map((r) => [r.id, r]));
      for (const m of maps) {
        for (const [id, hit] of m) {
          const req = missById.get(id);
          if (req) acceptHit(req, hit);
        }
      }
      // A long batched model response can occasionally omit one otherwise-valid envelope.
      // Recover only the missing members once, instead of discarding every successful body and
      // repaying for the whole batch. runP1Loop still fail-closes if the targeted retry misses.
      const missing = nlAll.filter((r) => !out.has(r.id));
      if (missing.length > 0) {
        log(`render: targeted retry for ${missing.length} omitted env(s) — ${missing.map((r) => r.id).join(", ")}`);
        const retries = await Promise.all(missing.map((r) => renderBatch([r])));
        for (let i = 0; i < missing.length; i++) {
          const r = missing[i];
          const hit = retries[i].get(r.id);
          if (hit) acceptHit(r, hit);
        }
      }
    }
    await saveCache();
    log(`render: ${out.size}/${reqs.length} bodies`);
    return canonicalOut();
  };

  // The most recent env set the review hook saw — the synthesize hook's evidence base
  // for usage excerpts (the loop always reviews before it synthesizes).
  let latestEnvs: P1Env[] = [];
  const routeOpts = {
    isLeanRealized: (symbol: string) => isLeanRealizedNotation(symbol),
    designatedHomeFor,
    ledgerHas: (key: string) => Object.hasOwn(cache.synth, key),
    graphNodeIds,
    lockedIds,
  };
  /** One cached call to the SINGLE semantic notation authority. Raw problems are cached
   * by layer content; routing is recomputed on every read so the ledger state applies. */
  const reviewNotation = async (layer: string): Promise<NotationReviewerProblem[]> => {
    const layerKey = hashEnvBody(`${notationModelKey}§${layer}§${notation}§${realizedList}`);
    if (Object.hasOwn(cache.notation, layerKey)) return cache.notation[layerKey];
    const res = await deps.runCodex({
      prompt: await presentationPrompt("p1_notation_check", {
        frozen_layer: layer,
        notation_table: notation,
        lean_realized_symbols: realizedList,
      }),
      cwd: repoRoot,
      reasoningEffort: "medium",
      leanLsp: false,
    });
    const problems = parseNotationReviewerOutput(res.stdout);
    cache.notation[layerKey] = problems;
    await saveCache();
    return problems;
  };
  const review: P1LoopHooks["review"] = async (layer, envs) => {
    latestEnvs = envs;
    log("review: lints + codex notation…");
    // `known` must include the LOCKED env ids too: they are present in the assembled layer (as fixed
    // context so loose-env xrefs resolve), so `lintAnchors` would otherwise flag each as
    // `unknown-objid` — a finding with no objId that the locked-filter below cannot drop.
    const known = new Set([...envs.map((e) => e.id), ...lockedIds]);
    const findings: P1Finding[] = [
      ...lintAnchors(layer, known, null),
      ...lintClarity(layer),
      ...lintSelfContainment(layer),
      ...lintCrossRefs(layer, refTargetsById),
      ...lintReferences(layer),
      ...lintHypothesisPresentation(layer),
    ].map(toFinding);
    // The reviewer is the ONLY notation check — a failed/unparseable review must
    // fail the stage, never let the loop converge with notation unexamined
    // (successful renders/reviews are cached, so the re-run is cheap).
    findings.push(...routeNotationProblems(await reviewNotation(layer), routeOpts));
    // Locked envs are P3-validated and used verbatim — never surface a finding against them (they
    // are not in the loop's env set, so any lint hit on the context copy would just stall the loop).
    return findings.filter((f) => !f.objId || !lockedIds.has(f.objId));
  };

  const synthesize: P1LoopHooks["synthesize"] = async (symbols) => {
    const out: P1Env[] = [];
    // The ledger grants ONE synthesis attempt per symbol, ever. A prior accepted entry
    // means the definition already exists in the layer; a prior failed entry means the
    // symbol is a checkpoint advisory. Either way: no repeat model call.
    const fresh = symbols.slice(0, 8).filter((symbol) => !Object.hasOwn(cache.synth, synthLedgerKey(symbol)));
    if (fresh.length === 0) return out;
    for (const symbol of fresh) cache.synth[synthLedgerKey(symbol)] = { symbol, accepted: false };
    await saveCache();
    const usagesFor = (symbol: string) => {
      const usageEnvs = latestEnvs
        .filter((e) => containsNotation(`${titleById.get(e.id) ?? ""} ${e.body}`, symbol))
        .slice(0, 3);
      return usageEnvs.length > 0
        ? usageEnvs.map((e) => `  - ${e.id}: ${e.body.replace(/\s+/g, " ").slice(0, 600)}`).join("\n")
        : "  (used in the frozen layer; see the notation table)";
    };
    // ONE batched call for the whole round: the model groups symbols of a single object
    // FAMILY into one definition (journal style — witness values, companion polynomials,
    // one apparatus) instead of minting a micro-definition per symbol (the per-symbol
    // path produced 34 synthesized envs in a 68-env layer).
    const symbolsBlock = fresh.map((symbol) => `SYMBOL: ${symbol}\n${usagesFor(symbol)}`).join("\n\n");
    try {
      const res = await deps.runCodex({
        prompt: await presentationPrompt("p1_synthesize_definition", {
          symbols_block: symbolsBlock,
          dstage_constructions: dstageDefinitionContext,
          note_md: io.bank.noteMd,
          lean_subdir: io.bank.leanSubdir,
        }),
        cwd: repoRoot,
        reasoningEffort: "medium",
        leanLsp: true,
      });
      const groups = parseJsonLoose(res.stdout) as { symbols?: string[]; title?: string; body?: string }[] | null;
      if (!Array.isArray(groups)) {
        // MECHANICAL failure (unparseable reply), not a judgment of undefinability:
        // un-burn the pre-marks so ONE retry may happen — but only one, tracked in
        // synthRetries. Unbounded un-burning re-dispatched the same symbols round
        // after round; a second mechanical failure burns the symbol to a checkpoint
        // advisory like any other failed attempt.
        const retried: string[] = [];
        const burned: string[] = [];
        cache.synthRetries ??= {};
        for (const symbol of fresh) {
          const k = synthLedgerKey(symbol);
          const n = (cache.synthRetries[k] ?? 0) + 1;
          cache.synthRetries[k] = n;
          if (n <= 1) {
            delete cache.synth[k];
            retried.push(symbol);
          } else {
            burned.push(symbol); // pre-mark stays: accepted:false advisory
          }
        }
        io.state.notes.push(
          `P1: batched synthesis reply unparseable — ${retried.length} symbol(s) left for one retry` +
          (burned.length > 0 ? `; ${burned.length} burned after repeated mechanical failure (advisory)` : ""),
        );
        await saveCache();
        return out;
      }
      const freshSet = new Set(fresh.map((x) => synthLedgerKey(x)));
      for (const g of Array.isArray(groups) ? groups : []) {
        const covered = (g.symbols ?? []).filter((x) => freshSet.has(synthLedgerKey(x)));
        // Reject labels and STRUCTURAL environments, but keep subsidiary math
        // environments: `cases`/`aligned`/matrices are the natural body of a
        // piecewise class definition.
        const structuralEnv = [...(g.body ?? "").matchAll(/\\(?:begin|end)\{([A-Za-z]+)\*?\}/g)].some(
          (m) => !/^(?:cases|dcases|aligned|alignedat|gathered|split|array|[pbBvV]?matrix|smallmatrix)$/.test(m[1]),
        );
        if (covered.length === 0 || !g.body || structuralEnv || /\\label\b/.test(g.body)) {
          if (covered.length > 0) {
            io.state.notes.push(`P1: synthesis for ${covered.join(", ")} rejected (structural env/label/empty) — left for the checkpoint`);
          }
          continue;
        }
        const id = `synth_${++synthCount}`;
        const body = normalizeSynthNotation(g.body.trim());
        if (g.title) titleById.set(id, g.title);
        for (const symbol of covered) {
          cache.synth[synthLedgerKey(symbol)] = { symbol, accepted: true, id, title: g.title, body };
          ledgerKeysBySynthId.set(id, [...(ledgerKeysBySynthId.get(id) ?? []), synthLedgerKey(symbol)]);
        }
        symbolsBySynthId.set(id, covered);
        out.push({ id, env: "definitionv", statement: body, body, refSet: [] });
        io.state.notes.push(`P1: synthesized definition ${id} for orphan symbol(s) ${covered.join(", ")}`);
      }
      const coveredKeys = new Set<string>();
      for (const g of Array.isArray(groups) ? groups : []) {
        for (const x of g.symbols ?? []) coveredKeys.add(synthLedgerKey(x));
      }
      const omitted = fresh.filter((x) => !coveredKeys.has(synthLedgerKey(x)));
      if (omitted.length > 0) {
        io.state.notes.push(`P1: synthesis deliberately omitted ${omitted.join(", ")} (model judged them not faithfully definable) — checkpoint advisories`);
      }
    } catch (e) {
      // MECHANICAL failure (thrown dispatch): same ONE-retry accounting as the
      // unparseable-reply branch above — an unconditional un-burn here re-armed a
      // repeatedly-crashing batch forever, the exact loop the retry bound exists
      // to kill (audit finding, 2026-08-20).
      const retried: string[] = [];
      const burned: string[] = [];
      cache.synthRetries ??= {};
      for (const symbol of fresh) {
        const k = synthLedgerKey(symbol);
        const n = (cache.synthRetries[k] ?? 0) + 1;
        cache.synthRetries[k] = n;
        if (n <= 1) {
          delete cache.synth[k];
          retried.push(symbol);
        } else {
          burned.push(symbol); // pre-mark stays: accepted:false advisory
        }
      }
      io.state.notes.push(
        `P1: batched synthesis failed (${(e as Error).message?.slice(0, 80)}) — ${retried.length} symbol(s) left for one retry` +
        (burned.length > 0 ? `; ${burned.length} burned after repeated mechanical failure (advisory)` : ""),
      );
      await saveCache();
      return out;
    }
    await saveCache();
    return out;
  };

  // ── Build the initial env set and run the loop (over the LOOSE nodes only; locked envs bypass it).
  // Accepted ledger entries are the durable recovery source: a rewound/converged prior run's
  // synthesized definitions re-enter the loop verbatim (delete p1_cache.json to regenerate).
  const seenSynthIds = new Set<string>();
  const recoveredSynth: P1Env[] = Object.values(cache.synth)
    .filter((e): e is Required<Pick<SynthLedgerEntry, "id" | "body">> & SynthLedgerEntry => e.accepted && !!e.id && e.body != null)
    .filter((e) => !seenSynthIds.has(e.id) && (seenSynthIds.add(e.id), true)) // consolidated synths: one env per id
    .map((e) => {
      if (e.title) titleById.set(e.id, e.title);
      const body = normalizeSynthNotation(e.body);
      return { id: e.id, env: "definitionv" as const, statement: body, body, refSet: [] };
    });
  if (recoveredSynth.length > 0) log(`resume: recovered ${recoveredSynth.length} synthesized definition(s) from the ledger`);
  const envs0: P1Env[] = [...recoveredSynth, ...looseNodes.map((n) => ({
    id: n.id,
    env: envForNodeWithOverride(n)!,
    statement: n.nl.statement,
    body: n.nl.statement,
    refSet: [...(refTargetsById.get(n.id) ?? [])],
    ...(n.delivery?.status === "undelivered"
      ? { delivery: { status: "undelivered" as const, role: n.delivery.role, reason: n.delivery.reason ?? "the item is outside the delivered theorem inventory" } }
      : {}),
  }))];
  const formalLayerPath = join(io.outDir, "formal_layer.tex");
  const onRound: P1LoopHooks["onRound"] = async ({ phase, iter, envs, findings }) => {
    // Always persist the latest layer so a slow/timed-out run leaves the render on disk.
    await writeFile(formalLayerPath, assemble(envs) + "\n", "utf8");
    if (phase === "render0") log(`render0: persisted ${envs.length}-env layer to formal_layer.tex`);
    else {
      const blocking = (findings ?? []).filter((f) => f.gate !== "xref-missing" && f.gate !== "notation-unresolved");
      log(`review iter ${iter}: ${findings?.length ?? 0} finding(s) (${blocking.length} actionable) — ${[...new Set(blocking.map((f) => f.gate))].join(", ") || "clean"}`);
    }
  };
  // notation_review.json is written on EVERY exit path (success, non-convergence,
  // audit failure, mid-loop throw) so a failed re-run can never leave a prior
  // converged run's `ok: true` file on disk to mislead the checkpoint reader.
  const dedupeAdvisories = (fs: P1Finding[]): P1Finding[] => {
    const seen = new Set<string>();
    return fs.filter((f) => {
      const key = `${f.gate}|${f.objId ?? ""}|${f.detail}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  };
  const writeNotationReview = (ok: boolean, advisories: P1Finding[], iterations: number) =>
    writeJsonAtomic(join(io.outDir, "notation_review.json"), {
      ok,
      iterations,
      advisories: dedupeAdvisories(advisories),
      synth_ledger: cache.synth,
    });
  let result;
  try {
    result = await runP1Loop(envs0, { render, review, synthesize, assemble, onRound, maxIterations: 6 });
  } catch (e) {
    await writeNotationReview(false, [], 0).catch(() => undefined); // why: best-effort — the loop error is the primary signal.
    throw e;
  }
  log(`loop: ${result.ok ? "converged" : "did NOT converge"} in ${result.iterations} iter(s); ${result.advisories.length} advisory`);

  if (!result.ok) {
    await writeNotationReview(false, result.advisories, result.iterations);
    throw new Error(
      `P1 loop did not converge in ${result.iterations} iterations (latest layer persisted to formal_layer.tex; ` +
        `renders/reviews/synthesis are cached — fix the blocking input and re-run): ` +
        result.unresolved.map((f) => `[${f.gate}] ${f.objId ?? ""} ${f.detail}`).join("; "),
    );
  }
  // Source of truth: the formal layer as typed JSON blocks (obj_id = node id, lean/status/ref_set
  // from the graph). The `.tex` is a DERIVED read-only view for human review; the freeze IS each
  // block's `body` — downstream stages compare paper env bodies against it directly.
  // Frozen layer = loop-rendered bodies for loose nodes + verbatim frozen_body for locked nodes.
  const looseBody = new Map(result.envs.map((e) => [e.id, e.body]));
  const bodies = new Map(nodes.map((n) => [
    n.id,
    normalizeCrefs(presentedBody(n.delivery?.status, n.nl.frozen_body, looseBody.get(n.id))),
  ] as const));
  const orderedEnvs = orderLayerEnvs(result.envs);
  const syntheticEnvs = orderedEnvs.filter((e) => e.id.startsWith("synth_"));
  const syntheticBlocks: FormalBlock[] = syntheticEnvs.map((e) => ({
    obj_id: e.id,
    alias: null,
    kind: "definition",
    env: "definitionv",
    title: titleById.get(e.id) ?? null,
    body: e.body,
    ref_set: [],
    lean: null,
    status: "presentation-synthesized",
    provenance: "presentation-synthesized",
    cited_dependencies: [],
  }));
  const graphBlocks = blocksFromGraph(
    graph,
    bodies,
    titleById,
    parseOutline(outlineMd).envOverrides,
    log,
    { citeKeyByNodeId: citeKeyById, locatorByNodeId: locatorById },
  );
  const blockById = new Map([...graphBlocks, ...syntheticBlocks].map((b) => [b.obj_id, b] as const));
  const blocks = orderedEnvs.flatMap((e) => {
    const block = blockById.get(e.id);
    return block ? [block] : [];
  });
  const layerIds = orderedEnvs.map((e) => e.id);
  const placedOutline = placeSynthesizedDefinitions(
    outlineMd, syntheticEnvs.map((e) => e.id),
    preferredSectionsForSynths(
      outlineMd,
      orderedEnvs.filter((e) => !e.id.startsWith("synth_"))
        .map((e) => ({ id: e.id, body: e.body, title: titleById.get(e.id) })),
      symbolsBySynthId,
      syntheticEnvs.map((e) => ({ id: e.id, body: e.body, title: titleById.get(e.id) })),
    ),
    layerIds,
  );
  await writeFile(join(io.outDir, "outline.md"), placedOutline, "utf8");
  await writeFile(
    join(io.outDir, "formal_layer.json"),
    JSON.stringify(FormalLayerSource.parse({ commit: null, blocks }), null, 2) + "\n",
    "utf8",
  );
  const preAuditTex = "% DERIVED from formal_layer.json — read-only, do not edit.\n" + blocksToTex(blocks) + "\n";
  await writeFile(formalLayerPath, preAuditTex, "utf8");
  // ── STATEMENT EQUIVALENCE AUDIT (co-located with statement production). Each frozen env body is
  // reconciled against its Lean declaration the moment it is rendered; drift is refined toward Lean
  // and the validated body is persisted onto the graph (nl.frozen_body) so a re-run stays tight. A
  // residual drift the auto-refiner could not close halts P1 for adjudication — the statement reaches
  // the outline checkpoint already verified against Lean, so P2/P3 confirm rather than reconstruct.
  log("statement audit: reconciling frozen envs against Lean…");
  const eqProblems = await runStatementAudit(io);
  if (eqProblems.length > 0) {
    io.state.hard_gate_failures = eqProblems;
    await writeNotationReview(false, result.advisories, result.iterations);
    throw new Error(
      `P1 statement equivalence audit failed (${eqProblems.length} statement(s) still drift after up to 2 ` +
        `refinement rounds; the frozen layer disagrees with Lean beyond what auto-refinement could tighten — ` +
        `adjudicate or fix the graph statement): ` +
        eqProblems.map((p) => p.detail).join("; "),
    );
  }
  // Statement refinement is model-authored and can add or drop a defining display. Re-run
  // the ONE semantic notation authority on the audited layer — but only when the audit
  // actually changed something (the common case is byte-identical, and an unchanged layer
  // needs no second opinion). Problems for ledgered symbols are already advisories.
  const auditedLayerTex = await readFile(formalLayerPath, "utf8");
  if (auditedLayerTex !== preAuditTex) {
    log("statement audit changed the layer — re-running the notation reviewer on the audited layer…");
    const postProblems = routeNotationProblems(await reviewNotation(auditedLayerTex), routeOpts);
    const blocking = postProblems.filter((f) => f.gate !== "notation-unresolved");
    result.advisories.push(...postProblems.filter((f) => f.gate === "notation-unresolved"));
    if (blocking.length > 0) {
      await writeNotationReview(false, result.advisories, result.iterations);
      throw new Error(`P1 post-audit notation resolvability failed: ${blocking.map((f) => f.detail).join("; ")}`);
    }
  }
  log("statement audit: all frozen envs faithful to Lean");

  // Advisory findings (xref + unresolved notation) → checkpoint notes (never blocking).
  const advisories = dedupeAdvisories(result.advisories);
  if (advisories.length > 0) {
    io.state.notes.push(
      `P1 advisories (${advisories.length}, for checkpoint review): ` +
        advisories.map((f) => f.detail).join("; "),
    );
  }
  await writeNotationReview(result.ok, advisories, result.iterations);
}
