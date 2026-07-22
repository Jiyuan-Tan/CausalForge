import type { CrosswalkEntry, CrosswalkVerdict } from "../types.js";
import { nodeIdToObjId } from "./from_note.js";
import type { FormalizationGraph, GraphNode } from "./types.js";

/** A crosswalk row enriched with the node's dependency edges. The `CrosswalkEntry`
 *  core is what the reviewer / cache consume unchanged; the edges are graph-only. */
export interface GraphSkeletonRow extends CrosswalkEntry {
  uses: string[]; // obj_ids the STATEMENT references (outgoing statement-uses) — a faithfulness criterion
  proofUses: string[]; // obj_ids the PROOF will use (outgoing proof-uses) — proof-completeness, NOT statement drift
  usedBy: string[]; // obj_ids that depend on it (incoming)
  boundTo: string[]; // the environment node(s) (incoming setup-of)
}

/** Node kinds that become crosswalk rows (setup is the environment; gate is a
 *  SUBSTRATE_DEBT entry — neither is a crosswalk object). */
const ROW_KINDS = new Set(["definition", "assumption", "lemma", "theorem"]);

/** The obj_id a node is keyed by in the crosswalk: `aux_<decl>` hidden-defs mirror
 *  the legacy `AUX-<decl>` rows; everything else derives from raw ids like `thm:...`. */
function rowObjId(n: GraphNode): string {
  if (n.id.startsWith("aux_")) return `AUX-${n.lean.decl_name ?? n.id.slice(4)}`;
  return nodeIdToObjId(n.id);
}

function declKindFor(kind: string): string {
  return kind === "theorem" ? "theorem" : kind === "lemma" ? "lemma" : "def";
}

const DEP_KINDS = new Set(["statement-uses", "proof-uses"]);

/**
 * Render the per-row dependency edges as a reviewer instruction block, so the
 * reviewer can check DEPENDENCY faithfulness (a flat crosswalk can't): each
 * theorem/lemma must rest only on assumptions/lemmas/defs the note licenses for
 * it, and must not omit one the note requires.
 */
export function renderDependencyBlock(rows: GraphSkeletonRow[]): string {
  const lines = rows
    .filter((r) => r.uses.length > 0 || r.proofUses.length > 0 || r.boundTo.length > 0)
    .map(
      (r) =>
        `  - ${r.obj_id}${r.boundTo.length ? ` [setup: ${r.boundTo.join(",")}]` : ""}` +
        `${r.uses.length ? ` statement-uses: ${r.uses.join(", ")}` : ""}` +
        `${r.proofUses.length ? ` proof-uses: ${r.proofUses.join(", ")}` : ""}`,
    );
  if (lines.length === 0) return "";
  return (
    "\nDEPENDENCY EDGES (from the formalization graph) — context for judging the STATEMENT, not a verdict criterion on their own:\n" +
    "• `statement-uses` — objects the STATEMENT references. Use them to check the statement says what the note says. A `drift` verdict requires an ACTUAL CONTENT defect — the Lean statement proves something WEAKER or DIFFERENT than the note (a dropped/weakened term, a flipped quantifier, a gerrymandered def, a missing hypothesis that changes the claim). Do NOT emit `drift` merely because the edge SET differs from the note's prose: an EXTRA edge to a STRUCTURAL parameter or setup object (the iid sample `S`/`IIDSample`, the measure space, a σ-algebra, a carrier law) is an encoding necessity, NOT a content dependency — note it if you like, but it is NOT drift. Reserve `drift` for a genuine MISSING content dependency (a def/lemma/assumption the note's claim needs but the Lean statement omits) or weakened content.\n" +
    "• `proof-uses` — objects the PROOF is expected to invoke. Their realization is PROOF-COMPLETENESS, NOT statement faithfulness. A `sorry`/`sorryAx` proof leaves proof-uses edges unrealized BY DESIGN (the filler completes them later) — this is NEVER statement drift. Do NOT flag a theorem `drift` because its proof is incomplete or its proof-uses edges are 'absent/unverifiable'. Judge ONLY the statement.\n" +
    "Express every observation in the OUTPUT JSON schema below (statement_verdicts / assumption_verdicts / substrate_gates / escalate) — invent no other field.\n" +
    lines.join("\n") +
    "\n"
  );
}

/**
 * Project the graph into the legacy `CrosswalkEntry` shape (so it slots into
 * `splitCrosswalkByCache` / `crosswalkReviewInstruction` / `mergeCrosswalkVerdicts`
 * unchanged) PLUS per-row dependency edges. The `verdict` is the skeleton
 * placeholder `unmatched`; durable review state lives on `node.review`.
 */
export function graphDerivedSkeleton(graph: FormalizationGraph): GraphSkeletonRow[] {
  const idToRow = new Map(graph.nodes.map((n) => [n.id, rowObjId(n)] as const));
  const rows: GraphSkeletonRow[] = [];
  for (const n of graph.nodes) {
    // A `cited` gate (borrowed comparator/input) IS a crosswalk row — its Lean def must be
    // source-matched at F2.5, reviewed in the assumption tier. A `gated` gate stays
    // SUBSTRATE_DEBT (not a row). Everything else follows ROW_KINDS.
    const isCitedGate = n.kind === "gate" && n.gate?.gate_class === "cited";
    if (!ROW_KINDS.has(n.kind) && !isCitedGate) continue;
    const uses: string[] = [];
    const proofUses: string[] = [];
    const usedBy: string[] = [];
    const boundTo: string[] = [];
    for (const e of graph.edges) {
      if (e.kind === "setup-of" && e.to === n.id) boundTo.push(idToRow.get(e.from) ?? e.from);
      else if (DEP_KINDS.has(e.kind)) {
        if (e.from === n.id) {
          // statement-uses → the STATEMENT references it (faithfulness criterion);
          // proof-uses → the PROOF will use it (proof-completeness, never statement drift).
          (e.kind === "proof-uses" ? proofUses : uses).push(idToRow.get(e.to) ?? e.to);
        }
        if (e.to === n.id) usedBy.push(idToRow.get(e.from) ?? e.from);
      }
    }
    rows.push({
      obj_id: rowObjId(n),
      // A cited gate reviews as an assumption (shallow tier — where the cited source-match block injects).
      kind: (isCitedGate ? "assumption" : n.kind) as CrosswalkEntry["kind"],
      title: n.nl.statement.split("\n")[0].slice(0, 120),
      tex: { label: n.nl.tex_anchor, line_range: n.nl.tex_anchor },
      lean: n.lean.decl_name
        ? { file: n.lean.file ?? "", decl: n.lean.decl_name, decl_kind: declKindFor(n.kind), line: 0 }
        : null,
      verdict: "unmatched" as CrosswalkVerdict,
      uses: [...new Set(uses)].sort(),
      proofUses: [...new Set(proofUses)].sort(),
      usedBy: [...new Set(usedBy)].sort(),
      boundTo: [...new Set(boundTo)].sort(),
    });
  }
  return rows;
}
