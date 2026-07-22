// Pure, testable core of the P1 executor→reviewer→router loop (the codex
// calls live in stages/p1_plan.ts; this module holds the logic they orchestrate).
// See doc/presentation/2026-06-17-causalsmith-graph-simplification-design.md §4.6.
import type { GraphNode } from "../graph/types.js";
import { envForNode, type EnvName } from "./graph_view.js";

/** Model assignment for the P1 loop. The touch-up render runs on codex (medium); the
 *  notation review runs on codex at HIGH effort (user choice 2026-06-25). Independence now
 *  comes from the role + effort split and the deterministic lint floor, not a separate model.
 *  See doc/presentation/2026-06-17-causalsmith-graph-simplification-design.md §4.6.0. */
export const P1_MODELS = { executor: "codex", reviewer: "codex" } as const;

/**
 * The deterministic mechanical frozen layer, rendered from already-topo-ordered
 * paper nodes (caller applies `topoOrder(renderedNodes(graph))`). Each env body is
 * the graph's `nl.statement`; the executor's touch-up replaces the WORDING in
 * place afterward (same obj_id). Titleless — the graph carries no title and the
 * env macro's `[title]` is optional; a title can be added by the render later.
 * Non-env kinds and all gates are skipped. A cited gate remains dependency metadata and is
 * disclosed by a generated footnote on each formally conditional consumer.
 */
export function renderMechanicalLayer(nodes: GraphNode[]): string {
  const out: string[] = [
    "% AUTO-GENERATED mechanical frozen layer — causalsmith P1 (graph render). Wording is touched up in place.",
  ];
  for (const n of nodes) {
    const env = envForNode(n);
    if (!env) continue;
    out.push(`\\begin{${env}}{${n.id}}`, n.nl.statement.trim(), `\\end{${env}}`, "");
  }
  return out.join("\n");
}

export type FixLocus = "wording-revise" | "synthesize-def" | "halt";

/** Findings the (codex) reviser can repair by re-rendering an env's wording.
 *  Gate names must match what the lints actually emit (`tex_anchors.ts`/`gates.ts`).
 *  `xref-missing` is advisory at the stage (it can over-fire on natural prose that
 *  names a dep instead of `\ref`-ing it); `xref-dangling` is enforced, and
 *  `xref-missing-assumption` (a statement-uses dep on an ASSUMPTION that the body never `\ref`s) is
 *  enforced too — an unreferenced hypothesis must be surfaced before the body freezes. */
const WORDING_GATES = new Set([
  "lean-identifier",
  "formalization-leak",
  "assumption-numbering",
  "bare-ref",
  "legacy-ref",
  "manual-cref-kind",
  "objid-in-prose",
  "xref-dangling",
  "xref-missing",
  "xref-missing-assumption",
  "faithfulness",
  // A bare "A1" in prose with no matching env is a render artifact: the reviser
  // should \ref the real assumption env, not invent a new one (all from-note
  // assumptions are already rendered as envs).
  "undefined-assumption",
  // Statement-presentation floor (`lintHypothesisPresentation`): a hypothesis-heavy theorem whose
  // conditions run together inline, or a `\ref`'d assumption restated inline. Both are repaired by
  // RE-RENDERING the env (itemize the hypotheses / drop the duplicated content) before the freeze —
  // exactly what that lint's docstring promises. Without these the router defaulted them to `halt`,
  // so P1 bailed on the first such finding instead of letting the reviser reformat.
  "hypothesis-not-itemized",
  "hypothesis-restated",
]);
/** Findings that need a NEW env (a missing class definition) — back to the executor. */
const SYNTH_GATES = new Set(["notation-undefined"]);

/**
 * Route a finding to its handler by gate name (the deterministic part of the
 * router — §4.6.0). The codex reviewer may also emit an explicit `fix_locus` on a
 * semantic finding; the caller prefers that when present and falls back here.
 * Anything unrecognized → `halt` (fail loud: unknown-objid, env-set-changed,
 * bare-env, not-frozen, …) rather than silently revising.
 */
export function routeFinding(gate: string): FixLocus {
  if (WORDING_GATES.has(gate)) return "wording-revise";
  if (SYNTH_GATES.has(gate)) return "synthesize-def";
  return "halt";
}

// ---------------------------------------------------------------------------
// The executor → reviewer → router loop (control flow; model calls are injected
// as hooks so this is unit-testable with mocks). §4.6.1.
// ---------------------------------------------------------------------------

/** One paper env in flight. `statement` is the immutable graph nl.statement (the
 *  faithfulness anchor); `body` is its current rendered prose; `refSet` is the
 *  allowed `\ref` target ids (paper-env edge targets, from `refTargets`). */
export interface P1Env {
  id: string;
  env: EnvName;
  statement: string;
  body: string;
  refSet: string[];
  delivery?: { status: "undelivered"; role?: string; reason: string };
}

/** Gates that are surfaced for the checkpoint but never block the loop. Deterministic
 *  `notation-undefined` remains advisory unless its producer explicitly opts into synthesis.
 *  Semantic `notation-reviewer` findings are deliberately NOT advisory: the presentation
 *  contract requires every named object to resolve before the P1 checkpoint can pass. */
const ADVISORY_GATES = new Set(["xref-missing", "notation-undefined"]);

/** A reviewer/lint finding. `fixLocus` is the codex reviewer's explicit route when
 *  present; otherwise the router falls back to `routeFinding(gate)`. `symbol` names
 *  the orphan class/assumption for a `synthesize-def`. */
export interface P1Finding {
  gate: string;
  objId?: string;
  detail: string;
  fixLocus?: FixLocus;
  symbol?: string;
}

/** Injected model/IO operations the loop orchestrates. */
export interface P1LoopHooks {
  /** (Re-)render envs to paper prose (codex). Round 1 passes all; later rounds pass
   *  only flagged/new envs with their prior body + defects. Returns id → new body. */
  render(
    reqs: { id: string; statement: string; refSet: string[]; priorBody?: string; defects?: string[]; delivery?: P1Env["delivery"] }[],
  ): Promise<Map<string, string>>;
  /** Review the assembled layer (codex notation + faithfulness) + deterministic floor lints. */
  review(layer: string, envs: P1Env[]): Promise<P1Finding[]>;
  /** Synthesize new definition envs for orphan symbols (codex+lean-lsp); returns rendered envs. */
  synthesize(symbols: string[]): Promise<P1Env[]>;
  /** Assemble the layer tex from envs (so review sees the current layer). */
  assemble(envs: P1Env[]): string;
  /** Progress/persistence hook (optional): called after the round-0 render and
   *  after each review, so the stage can log and write the current layer to disk
   *  (observability — a slow/timed-out run still leaves the rendered output). */
  onRound?(info: { phase: "render0" | "review"; iter: number; envs: P1Env[]; findings?: P1Finding[] }): Promise<void> | void;
  maxIterations: number;
}

export interface P1LoopResult {
  envs: P1Env[];
  ok: boolean;
  /** On `ok:false`, the blocking findings (a halt, or unresolved after the cap). */
  unresolved: P1Finding[];
  /** Advisory findings (xref-missing) surfaced for the checkpoint, never blocking. */
  advisories: P1Finding[];
  iterations: number;
}

const locusOf = (f: P1Finding): FixLocus => f.fixLocus ?? routeFinding(f.gate);
const isAdvisoryFinding = (f: P1Finding): boolean =>
  ADVISORY_GATES.has(f.gate) && f.fixLocus == null; // why: deterministic orphan notation opts into synthesis explicitly.

/**
 * Run the loop: render-all (round 0) → {review → route → handle} until the
 * reviewer is clean, a `halt` fires, or the iteration cap is hit. The
 * `synthesize-def` handler adds rendered envs (so a synthesized env is never
 * un-rendered); `wording-revise` re-renders flagged envs with their defects;
 * `xref-missing` is advisory (collected, never blocking). Pure control flow —
 * all model calls go through `h`.
 */
export async function runP1Loop(initial: P1Env[], h: P1LoopHooks): Promise<P1LoopResult> {
  let envs = initial.map((e) => ({ ...e }));
  const applyRender = (reqIds: string[], m: Map<string, string>) => {
    const requested = new Set(reqIds);
    const missing = reqIds.filter((id) => !m.has(id) || (m.get(id) ?? "").trim() === "");
    const extra = [...m.keys()].filter((id) => !requested.has(id));
    if (missing.length || extra.length) {
      throw new Error(`P1 render returned invalid id set — missing/empty: [${missing.join(", ")}], extra: [${extra.join(", ")}]`); // why: silently keeping old bodies publishes stale formal prose.
    }
    envs = envs.map((e) => (m.has(e.id) ? { ...e, body: m.get(e.id)! } : e));
  };
  // Round 0: render everything.
  applyRender(envs.map((e) => e.id), await h.render(envs.map((e) => ({ id: e.id, statement: e.statement, refSet: e.refSet, delivery: e.delivery }))));
  await h.onRound?.({ phase: "render0", iter: 0, envs });

  let advisories: P1Finding[] = [];
  const addAdvisories = (fs: P1Finding[]) => {
    const seen = new Set(advisories.map((f) => `${f.gate}|${f.objId ?? ""}|${f.detail}`));
    for (const f of fs) {
      const key = `${f.gate}|${f.objId ?? ""}|${f.detail}`;
      if (!seen.has(key)) {
        advisories.push(f);
        seen.add(key);
      }
    }
  };
  for (let iter = 1; iter <= h.maxIterations; iter++) {
    const findings = await h.review(h.assemble(envs), envs);
    await h.onRound?.({ phase: "review", iter, envs, findings });
    addAdvisories(findings.filter(isAdvisoryFinding));
    const actionable = findings.filter((f) => !isAdvisoryFinding(f));
    if (actionable.length === 0) return { envs, ok: true, unresolved: [], advisories, iterations: iter };

    const halts = actionable.filter((f) => locusOf(f) === "halt");
    if (halts.length > 0) return { envs, ok: false, unresolved: halts, advisories, iterations: iter };

    // synthesize-def → add rendered envs before the layer they explain. A definition appended
    // after its first use is still unresolved to a reader, and nested repair rounds naturally
    // discover prerequisites of earlier synthetic definitions. Prepending each later batch gives
    // those prerequisites the correct dependency order without another model call.
    const symbols = [
      ...new Set(actionable.filter((f) => locusOf(f) === "synthesize-def").map((f) => f.symbol).filter((s): s is string => !!s)),
    ];
    if (symbols.length > 0) envs = [...(await h.synthesize(symbols)), ...envs];

    // wording-revise → re-render the flagged envs with their accumulated defects.
    const defectsById = new Map<string, string[]>();
    for (const f of actionable) {
      if (locusOf(f) === "wording-revise" && f.objId) {
        (defectsById.get(f.objId) ?? defectsById.set(f.objId, []).get(f.objId)!).push(f.detail);
      }
    }
    if (defectsById.size > 0) {
      const reqs = envs
        .filter((e) => defectsById.has(e.id))
        .map((e) => ({ id: e.id, statement: e.statement, refSet: e.refSet, priorBody: e.body, defects: defectsById.get(e.id)!, delivery: e.delivery }));
      applyRender(reqs.map((r) => r.id), await h.render(reqs));
    }
    // If a round only produced synth (no wording defects), the next iteration
    // re-reviews the enlarged layer — progress is guaranteed by the cap.
  }
  // Cap reached: re-review once to report what still blocks.
  const finalFindings = await h.review(h.assemble(envs), envs);
  addAdvisories(finalFindings.filter(isAdvisoryFinding));
  const residual = finalFindings.filter((f) => !isAdvisoryFinding(f));
  return { envs, ok: residual.length === 0, unresolved: residual, advisories, iterations: h.maxIterations };
}
