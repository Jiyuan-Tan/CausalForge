// Render a bridge `.md` note from the (core-keyed, obj_id-aliased) formalization
// graph — the banked human-readable record + causalsmith input + F5 premise-check
// source. The plan-driven pipeline no longer hand-writes a `.md`; this reconstructs
// one deterministically so the bank loader (which requires a note) and causalsmith
// (which `parseNoteBlocks` the P/L/T blocks) keep working unchanged.
//
// Block forms MUST match causalsmith's `parseNoteBlocks` (note_parser.ts):
//   P/L → `**P-1 (Title).** <stmt>`            (HEADER_BOLD_PL → obj_id "P-1")
//   T   → `### T-block: t1 — Title` + Statement  (HEADER_TBLOCK → obj_id "T-1")
//   A/S → `**A-1 (Title).**` / `**S-1 (Title).**` (parseNoteBlocks ignores these;
//         they are human-readable + consumed by the graph's A/S scan)
// The obj_id used here is the node's `obj_id` alias, so a note block correlates with
// the graph node that carries the same alias (causalsmith keys both by obj_id).
import type { FormalizationGraph, GraphNode } from "./types.js";

/** A short title from the node's NL statement (first clause, truncated). */
function shortTitle(n: GraphNode): string {
  const s = (n.nl?.statement ?? "").replace(/\s+/g, " ").trim();
  if (!s) return n.obj_id ?? n.id;
  const firstClause = s.split(/[.;:]\s/)[0];
  return firstClause.length > 60 ? firstClause.slice(0, 57).trimEnd() + "…" : firstClause;
}

function renderNode(n: GraphNode): string {
  const objId = n.obj_id ?? n.id;
  const stmt = (n.nl?.statement ?? "").replace(/\s+/g, " ").trim();
  const title = shortTitle(n);
  switch (n.kind) {
    case "setup": {
      const mods = n.setup?.required_modules ?? [];
      return `**${objId} (${title}).** ${stmt}\n**required modules.** ${mods.join(", ")}`;
    }
    case "assumption":
      return `**${objId} (assumption).** ${stmt}`;
    case "definition": {
      // At F1-emit time a Lean link with a null file means a `reuse` decision.
      const reuse = n.lean?.decl_name && !n.lean.file ? `\n**reuse.** ${n.lean.decl_name}` : "";
      return `**${objId} (${title}).** ${stmt}${reuse}`;
    }
    case "lemma":
      return `**${objId} (${title}).** ${stmt}`;
    case "theorem": {
      const num = objId.split("-")[1] ?? objId;
      return `### T-block: t${num} — ${title}\n**Statement.** ${stmt}`;
    }
    default:
      return ""; // gate / unknown → no block
  }
}

/**
 * Render the whole graph to a bridge `.md`. Blocks are emitted grouped by kind
 * (S, A, P, L, T) so the note reads top-down (environment → assumptions →
 * definitions → lemmas → theorems), each in obj_id order.
 */
export function renderBridgeNote(graph: FormalizationGraph): string {
  const order: GraphNode["kind"][] = ["setup", "assumption", "definition", "lemma", "theorem"];
  const headings: Partial<Record<GraphNode["kind"], string>> = {
    setup: "## Environment (S)",
    assumption: "## Assumptions (A)",
    definition: "## Definitions (P)",
    lemma: "## Lemmas (L)",
    theorem: "## Theorems (T)",
  };
  const lines: string[] = [
    `# ${graph.qid} — formalization note (bridge; rendered from core + plan)`,
    "",
    "_Auto-generated from the typed core + F1 plan. The structural source of truth is the formalization graph; this note is the human-readable / causalsmith bridge._",
    "",
  ];
  for (const kind of order) {
    const nodes = graph.nodes.filter((n) => n.kind === kind);
    if (nodes.length === 0) continue;
    lines.push(headings[kind] ?? "", "");
    for (const n of nodes) {
      const block = renderNode(n);
      if (block) lines.push(block, "");
    }
  }
  return lines.join("\n");
}
