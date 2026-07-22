import type { FormalizationGraph, NodeKind } from "./types.js";

const KIND_ORDER: NodeKind[] = ["setup", "definition", "assumption", "lemma", "theorem", "gate"];

export function toMarkdown(graph: FormalizationGraph): string {
  const lines: string[] = [`# ${graph.qid} (${graph.specialization}) — formalization graph`, ""];
  for (const kind of KIND_ORDER) {
    const ns = graph.nodes.filter((n) => n.kind === kind);
    if (!ns.length) continue;
    lines.push(`## ${kind}`, "");
    for (const n of ns) {
      const lean = n.lean.decl_name ? ` — \`${n.lean.decl_name}\`` : " — _(unlinked)_";
      const proof = n.kind === "theorem" || n.kind === "lemma" ? ` [${n.proof.state}]` : "";
      lines.push(`- **${n.id}** (${n.provenance})${lean}${proof}: ${n.nl.statement}`);
    }
    lines.push("");
  }
  return lines.join("\n");
}

export function toDot(graph: FormalizationGraph): string {
  const lines = ["digraph formalization {", "  rankdir=BT;"];
  for (const n of graph.nodes) {
    // Second line: the linked Lean decl (truncated + quote-escaped), or "(unlinked)".
    const raw = n.lean.decl_name ? n.lean.decl_name.slice(0, 40) : "(unlinked)";
    const decl = raw.replace(/["\\]/g, "");
    lines.push(`  "${n.id}" [label="${n.id} — ${decl}\\n(${n.kind})"];`);
  }
  for (const e of graph.edges) {
    const style = e.source === "declared" ? "solid" : "dashed";
    lines.push(`  "${e.from}" -> "${e.to}" [label="${e.kind}", style=${style}];`);
  }
  lines.push("}");
  return lines.join("\n");
}
