import type { GoldPair } from "./gold.js";
import { MODELS } from "../../models.js";
import type { Rendering } from "./metrics.js";
import { runClaude } from "../../workers/claude.js"; // existing worker entry; adjust to actual export

export interface QueryRecord {
  qid: string; theorem: string; rendering: Rendering; variant: number; text: string;
}

export function renderDocQueries(pairs: GoldPair[]): QueryRecord[] {
  return pairs
    .filter((p) => p.doc.length > 0)
    .map((p) => ({ qid: `${p.theorem}#doc#0`, theorem: p.theorem, rendering: "doc", variant: 0, text: p.doc }));
}

const PARA_PROMPT = (doc: string, stmt: string, n: number) =>
  `You are writing items for a formalization plan. Rewrite the theorem below as ${n} DISTINCT terse ` +
  `"P-/L-/A-"-style plan items: each one short paragraph describing WHAT it asserts in econometrician prose. ` +
  `Hard rules: name NO Lean identifier, NO field projection, NO code — prose only; vary phrasing across the ${n}. ` +
  `Return exactly ${n} lines, one item per line.\n\nNL meaning: ${doc}\nFormal statement: ${stmt}`;

/** Paraphrase a sampled subset (cost control). Caller passes the sample; results are content-cached upstream. */
export async function renderParaphraseQueries(sample: GoldPair[], n: number): Promise<QueryRecord[]> {
  const out: QueryRecord[] = [];
  for (const p of sample) {
    const raw = await runClaude({ prompt: PARA_PROMPT(p.doc, p.statement, n), model: MODELS.claudeCheap, cwd: process.cwd(), allowedTools: [], leanLsp: false });
    const lines = raw.split(/\r?\n/).map((l) => l.replace(/^\s*(?:[-*]\s+|\d+[.)]\s+)/, "").trim()).filter(Boolean).slice(0, n);
    lines.forEach((text, i) =>
      out.push({ qid: `${p.theorem}#para#${i}`, theorem: p.theorem, rendering: "para", variant: i, text }));
  }
  return out;
}
