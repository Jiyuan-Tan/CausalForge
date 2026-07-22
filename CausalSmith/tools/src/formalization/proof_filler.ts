import { readFile } from "node:fs/promises";
import { MODELS } from "../models.js";
import { existsSync } from "node:fs";
import { addAssumption, markUnreviewed } from "../graph/mutate.js";
import { nodeIdToObjId, objIdToNodeId } from "../graph/from_note.js";
import { isUndeliveredNode, type AssumptionClass, type FormalizationGraph } from "../graph/types.js";
import type { CodexRunInput } from "../shared/codex.js";
import { promptPath } from "../paths.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";

/** The proof-filler agent's escalation when it hits a wall it cannot resolve.
 *  `unparsable-output` is synthesized by the DISPATCHER (not the model) when the filler's
 *  stdout carries no parseable FillerOutput — a mechanical fault that must surface as a
 *  resumable checkpoint, not crash the run (the loop has no stage-level catch). */
export interface FillerEscalation {
  kind: "statement-wrong" | "needs-substrate" | "ambiguous-spec" | "unparsable-output";
  reason: string;
  node?: string;
}

interface FillerAddedAssumption {
  id: string;
  statement: string;
  classification: string; // faithful[-refinement] | regularity[-bookkeeping] | substrate-gate
  attached_to: string; // obj_id of the node whose proof needs it
  anchor?: string;
  tier?: 1 | 2;
}

interface FillerOutput {
  added_assumptions?: FillerAddedAssumption[];
  escalate?: FillerEscalation | null;
  summary?: string;
}

export interface FillerResult {
  graph: FormalizationGraph;
  escalate: FillerEscalation | null;
  summary: string;
}

/**
 * `content-gate` is the LAUNDERING tag: an added premise standing in for a result the note DERIVES.
 * It must never be recorded as `substrate-gate` (accepted, dischargeable debt) — that silently turns
 * a reject into a bankable disclosure. Callers escalate instead of persisting it.
 */
export function isContentGateTag(tag: string): boolean {
  return tag.trim().toLowerCase().startsWith("content");
}

/**
 * Map the filler's `classification` tag to an {@link AssumptionClass}.
 *
 * Precondition: `!isContentGateTag(tag)` — a content-gate has no honest {@link AssumptionClass}, so
 * it is filtered out upstream and escalated rather than mapped.
 *
 * An unrecognized tag falls back to `substrate-gate`, the CONSERVATIVE choice: a substrate-gate is
 * owed a build and blocks banking (see `auditSubstrateGates`). Silently downgrading an unknown tag
 * to `regularity-bookkeeping` would be the unsafe direction.
 */
export function toAssumptionClass(tag: string): AssumptionClass {
  const t = tag.trim().toLowerCase();
  if (t.startsWith("faithful")) return "faithful-refinement";
  if (t.startsWith("regularity")) return "regularity-bookkeeping";
  return "substrate-gate";
}

/** Tolerant JSON parse: balanced, string-aware extraction from fenced/prose-wrapped output. */
function parseFillerOutput(stdout: string): FillerOutput {
  const fenced = stdout.replace(/```(?:json)?/gi, "");
  const candidates: string[] = [];
  let depth = 0, startIdx = -1, inStr = false, esc = false;
  for (let i = 0; i < fenced.length; i++) {
    const c = fenced[i];
    if (inStr) {
      if (esc) esc = false;
      else if (c === "\\") esc = true;
      else if (c === '"') inStr = false;
      continue;
    }
    if (c === '"') inStr = true;
    else if (c === "{") { if (depth === 0) startIdx = i; depth++; }
    else if (c === "}") {
      if (depth > 0) {
        depth--;
        if (depth === 0 && startIdx >= 0) {
          candidates.push(fenced.slice(startIdx, i + 1));
          startIdx = -1;
        }
      }
    }
  }
  candidates.sort((a, b) => b.length - a.length);
  for (const cand of candidates) {
    try {
      const o = JSON.parse(cand) as Record<string, unknown>;
      if (!o || typeof o !== "object" || Array.isArray(o)) continue;
      // why: copied examples/prose objects are unsafe unless they have the filler result shape.
      if (!("added_assumptions" in o) && !("escalate" in o) && !("summary" in o)) continue;
      if ("added_assumptions" in o && o.added_assumptions != null && !Array.isArray(o.added_assumptions)) continue;
      if ("summary" in o && o.summary != null && typeof o.summary !== "string") continue;
      return o as FillerOutput;
    } catch {
      // try the next balanced object
    }
  }
  throw new Error("filler: no parseable FillerOutput JSON object in output");
}

/** A compact context string for the filler: the open nodes (with their frozen
 *  statements to PRESERVE), and the substrate/required modules. */
export function renderFillerContext(graph: FormalizationGraph): string {
  const lines: string[] = ["OPEN WORK (nodes with unfinished proofs):"];
  for (const n of graph.nodes) {
    if (n.kind !== "theorem" && n.kind !== "lemma") continue;
    if (isUndeliveredNode(n)) continue;
    if (n.proof.state === "complete") continue;
    const uses = [...new Set(graph.edges
      .filter((e) => (e.kind === "statement-uses" || e.kind === "proof-uses") && e.from === n.id)
      .map((e) => e.to))];
    const frozen = n.provenance === "from-note" ? " [FROZEN STATEMENT — do not weaken]" : "";
    const decl = n.lean.decl_name ?? "(unlinked)";
    lines.push(`- ${n.id} (${n.kind}, ${decl}, ${n.proof.state})${frozen}: ${n.nl.statement}${uses.length ? `  uses: ${uses.join(", ")}` : ""}`);
  }
  const setups = graph.nodes.filter((n) => n.kind === "setup");
  if (setups.length) {
    lines.push("", "ENVIRONMENT:");
    for (const s of setups) lines.push(`- ${s.id}: ${s.nl.statement}${s.setup?.required_modules.length ? `  (modules: ${s.setup.required_modules.join(", ")})` : ""}`);
  }
  return lines.join("\n");
}

/**
 * One proof-filler session: dispatch the Codex filler over the graph, then record
 * any assumptions it added (writing them into Lean is the filler's job) onto the
 * graph — minting an `agent-introduced` assumption node + a `proof-uses` edge to the
 * node it serves, and flipping that parent to `unreviewed` so the reviewer re-checks
 * it on the dirty frontier. Returns the updated graph + any escalation.
 *
 * Missing-primitive policy (NOT "always escalate"): if the filler CAN build the
 * needed helper here — a project-specific lemma in the research subtree (or a
 * Mathlib-shaped helper under `CausalSmith/Mathlib`), or by composing existing
 * Causalean/Mathlib lemmas — it BUILDS it inline as an `agent-introduced` node and
 * the reviewer judges it next iteration (the normal path). It leaves
 * `sorry -- BLOCKER: needs-substrate(<primitive>)` and escalates `needs-substrate`
 * ONLY for substrate it cannot build here: cluster-scale / `Causalean/`-bound
 * (outside its edit scope) or genuinely open math, where the orchestrator builds it
 * as a named Causalean lemma and independently verifies it 0-sorry/axiom-clean before
 * dependents lean on it (invariant #10). It must SEARCH + try composing first.
 * In all cases it MUST NOT assume the crux (no crux as a hypothesis, no vacuous stub).
 */
export async function runFiller(args: {
  ctx: { repoRoot: string; qid: string; specialization: string };
  deps: { runCodex: (o: CodexRunInput) => Promise<{ stdout: string; stderr: string }> };
  graph: FormalizationGraph;
  leanDir: string;
  // AUDIT-FORM: texPath is still passed by bin/formalization callers, but filler prompt construction does not consume it.
  texPath?: string;
  corePath?: string;
  promptPath?: string;
  /** Load-bearing orchestrator PROOF hint (lemma names / tactic strategy / Mathlib API),
   *  injected verbatim near the top of the prompt. A proof hint ONLY — must not be read as
   *  license to weaken a statement, add an unsanctioned hypothesis, or axiomatize a goal. */
  directive?: string | null;
}): Promise<FillerResult> {
  // repoRoot IS the CausalSmith package dir → resolve via the shared promptPath helper, not a
  // hardcoded "CausalSmith/tools/..." prefix (which double-nests and leaves basePrompt empty).
  const promptFile = args.promptPath ?? promptPath(args.ctx.repoRoot, "proof_filler.txt");
  // Fail CLOSED, like the reviewer. The base prompt carries the no-axiom, disclosure and
  // frozen-statement contract; degrading it to "" would still dispatch a write-capable agent,
  // just one that was never told the rules.
  if (!existsSync(promptFile)) throw new Error(`proof-filler prompt missing: ${promptFile}`);
  const basePrompt = await readFile(promptFile, "utf8");
  if (!basePrompt.trim()) throw new Error(`proof-filler prompt is empty: ${promptFile}`);
  const directiveBlock =
    args.directive && args.directive.trim().length > 0
      ? [
          "=== ORCHESTRATOR PROOF DIRECTIVE (load-bearing — apply as a top-priority PROOF hint) ===",
          args.directive.trim(),
          "This is a PROOF hint only (lemma names / tactic strategy / Mathlib API). It does NOT",
          "authorize weakening a frozen statement, adding an unsanctioned hypothesis, or axiomatizing",
          "a goal — those are still rejected downstream. Prove the stated goals as written.",
          "=== END ORCHESTRATOR PROOF DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  const prompt = [
    basePrompt,
    "",
    directiveBlock,
    renderFillerContext(args.graph),
    "",
    "SOURCES (read the relevant proof step before filling a sorry):",
    // The typed core.json is the SINGLE source of truth; its per-node `proof_tex` IS the human proof
    // and `statement` IS the paper statement. The `.tex` is merely a deterministic render of this core
    // (stage0_render `renderCoreTex`), so it is NOT fed here — feeding both would double-feed the same
    // content.
    args.corePath ? `- Typed core.json (the spec — per-node \`proof_tex\` = the human proof roadmap; \`statement\`/conditions = the paper statements): ${args.corePath}` : "",
    `Lean source tree: ${args.leanDir}`,
    "Return ONLY the JSON object specified in the prompt.",
  ].filter(Boolean).join("\n");

  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "3",
    label: "F3 proof filler",
    prompt,
    promptSources: [promptFile, ...(args.corePath ? [args.corePath] : []), args.leanDir],
    model: MODELS.codexKernel,
    reasoningEffort: "medium",
  });
  // Mirror the reviewer's parse boundary (runUnit → `unparsable-output`): a throw here would
  // unwind through the proof-review loop — which has no stage-level catch — and abort the whole
  // run on one flaky model reply. Escalate as a structured, resumable outcome instead; the raw
  // stdout is already preserved in the agent logs by the dispatch wrapper.
  let parsed: FillerOutput;
  try {
    parsed = parseFillerOutput(out.stdout);
  } catch (err) {
    return {
      graph: args.graph,
      escalate: {
        kind: "unparsable-output",
        reason:
          `filler output failed to parse (${err instanceof Error ? err.message : String(err)}); ` +
          `any Lean edits it made are on disk and will be re-reviewed on resume — raw output is in the agent logs`,
      },
      summary: "",
    };
  }

  let graph = args.graph;

  // A `content-gate` tag is the filler admitting it assumed the crux. Escalate as a STRUCTURED
  // result (`statement-wrong` → `fix-source`, a human decides) rather than throwing: the loop has no
  // stage-level catch, so a throw would unwind past `saveState`, leave `stage_completed` unadvanced,
  // and make `--resume` re-enter the same filler — a crash loop on a deterministic content-gate.
  // Nothing is persisted: the offending premise is never added to the graph.
  const contentGates = (parsed.added_assumptions ?? []).filter((a) => isContentGateTag(a.classification));
  if (contentGates.length > 0) {
    return {
      graph: args.graph,
      escalate: {
        kind: "statement-wrong",
        reason:
          `filler classified ${contentGates.length} added premise(s) as content-gate (laundering the ` +
          `crux — a result the note DERIVES, assumed instead of proven): ` +
          contentGates.map((a) => `${a.id} on ${a.attached_to}`).join("; "),
        node: contentGates[0].attached_to,
      },
      summary: parsed.summary ?? "",
    };
  }

  for (const a of parsed.added_assumptions ?? []) {
    // why: core-built graph ids can be semantic (`thm:*`) while the filler prompt names the paper obj_id
    // alias (`T-1`). Resolve in PRIORITY ORDER — an exact node-id match must win over an earlier node
    // whose obj_id (or derived alias) happens to match, else the hypothesis attaches to the wrong node.
    const attached =
      graph.nodes.find((n) => n.id === a.attached_to) ??
      graph.nodes.find((n) => n.obj_id === a.attached_to) ??
      graph.nodes.find((n) => nodeIdToObjId(n.id) === a.attached_to);
    const parentId = attached?.id ?? objIdToNodeId(a.attached_to);
    if (!graph.nodes.some((n) => n.id === parentId)) {
      // Unknown parent: the hypothesis is already in the LEAN (writing it is the filler's job),
      // but its graph node — including a substrate-gate disclosure — cannot be recorded. Never
      // drop that silently (the "graded N, applied M" class): surface it loudly for the
      // orchestrator; the parent's changed signature still lands on the dirty review frontier.
      console.warn(
        `[f3] filler added assumption '${a.id}' (${a.classification}) attached to unknown node ` +
          `'${a.attached_to}' — NOT recorded on the graph; verify the disclosure is not lost.`,
      );
      continue;
    }
    if (!graph.nodes.some((n) => n.id === a.id)) {
      graph = addAssumption(graph, {
        node: parentId,
        id: a.id,
        statement: a.statement,
        tier: a.tier ?? 2,
        classification: toAssumptionClass(a.classification),
        anchor: a.anchor ?? "",
        provenance: "agent-introduced",
      });
    }
    graph = markUnreviewed(graph, parentId); // the parent gained a hypothesis → re-review
  }

  return { graph, escalate: parsed.escalate ?? null, summary: parsed.summary ?? "" };
}
