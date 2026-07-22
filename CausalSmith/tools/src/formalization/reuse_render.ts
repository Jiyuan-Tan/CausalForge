/*!
 * Scaffold-brief rendering over the reuse-retrieval engine (`reuse_retrieval.ts`).
 *
 * This file is downstream of the engine: it turns ranked candidates into the
 * "Causalean reuse candidates" text block injected into the Stage 2 scaffold brief
 * (concept mode), for both the F1 markdown artifact path and the typed-core path.
 */

import { existsSync, readFileSync } from "node:fs";
import type { ClusterKey } from "../constants.js";
import type { Core } from "../discovery/core/schema.js";
import { expandQuery } from "./causal_aliases.js";
import { loadSemanticTier, embedQueries, type SemanticTier } from "./semantic_tier.js";
import { poolModules } from "./module_tier.js";
import {
  createRetrieval,
  parseF1Items,
  symbolSet,
  backtickSpans,
  type Candidate,
  type F1Item,
  type Retrieval,
} from "./reuse_retrieval.js";

// ─── scaffold-brief rendering (concept mode) ────────────────────────────────

export interface CandidateBlockOpts {
  topKPerItem?: number;
  totalCap?: number;
  /** Blend the semantic tier into each item's concept search (confidence-aware fusion).
   *  The pipeline scaffold-push turns this ON (see stage1.ts, env `RETRIEVAL_SEMANTIC_PUSH`);
   *  the human CLI leaves it opt-in. Query embedding goes through the warm daemon (~1 s;
   *  first call ~30 s cold-start), and needs the embeddings sidecar present. Degrades to
   *  lexical-only if embeddings are missing/stale — never breaks the brief. */
  semantic?: boolean;
}

/** Min `typePattern` score for a supplementary candidate to be worth showing (≥2 shared
 * distinctive symbols). Below this the match is a single common symbol — noise. */
const SYMBOL_MIN_SCORE = 12;

/**
 * Render the per-F1-item "Causalean reuse candidates" block injected into the Stage 2
 * scaffold brief. Reads the F1 artifact at `mdPath`, runs concept-mode retrieval for
 * each P-/L- item, and emits a candidate table + the per-item reuse/bypass contract.
 * Returns "" (so the brief is unchanged) when the index or F1 artifact is unavailable,
 * unparseable, or empty — retrieval must never break dispatch.
 */
export function reuseCandidateBlock(
  root: string,
  mdPath: string,
  cluster: ClusterKey | null,
  opts: CandidateBlockOpts = {},
): string {
  if (!existsSync(mdPath)) return "";
  const r = createRetrieval(root);
  if (!r.library) return "";
  let md: string;
  try {
    md = readFileSync(mdPath, "utf8");
  } catch {
    return "";
  }
  const items = parseF1Items(md);
  if (items.length === 0) return "";
  return renderReuseCandidates(r, items, cluster, root, opts);
}

/**
 * Build the candidate block directly from a typed core (the F1 plan stage): one
 * retrieval query per core node (assumption / definition / statement), reusing the
 * same ranking engine and output format as the markdown path. The S-block world
 * choice has no dedicated core node, so it is left to the agent's CLI / lean-lsp
 * search. Returns "" when the index is unavailable or the core has no nodes.
 */
export function coreReuseCandidateBlock(
  root: string,
  core: Core,
  cluster: ClusterKey | null,
  opts: CandidateBlockOpts = {},
): string {
  const r = createRetrieval(root);
  if (!r.library) return "";
  // The node-id slug carries the human concept words ("minimax-lower" → "minimax lower",
  // "clip-bias" → "clip bias"); it is a far stronger retrieval signal than the bare node
  // KIND ("theorem"/"assumption") or a symbol name ("M_n"). Prepend it to every query title
  // so both lexical and semantic ranking see the concept, not just the raw statement body.
  const slug = (id: string) => (id.split(":")[1] ?? "").replace(/-/g, " ").trim();
  const items: F1Item[] = [
    ...core.assumptions.map((a) => ({ kind: "A" as const, label: a.id, title: `${slug(a.id)} ${a.kind ?? "assumption"}`.trim(), body: a.condition })),
    ...core.definitions.map((d) => ({ kind: "P" as const, label: d.id, title: `${slug(d.id)} ${d.name}`.trim(), body: `${d.construction} ${(d.by_member_properties ?? []).join(" ")}`.trim() })),
    ...core.statements.map((s) => ({ kind: "L" as const, label: s.id, title: `${slug(s.id)} ${s.kind}`.trim(), body: s.statement })),
  ];
  if (items.length === 0) return "";
  return renderReuseCandidates(r, items, cluster, root, opts);
}

/**
 * Shared renderer: rank + format candidates for a list of items, whether parsed from
 * the F1 markdown or derived from a typed core. Extracted so both entry points share
 * one ranking + output-format path.
 */
function renderReuseCandidates(
  r: Retrieval,
  items: F1Item[],
  cluster: ClusterKey | null,
  root: string,
  opts: CandidateBlockOpts,
): string {
  if (!r.library) return "";
  // Push is the baseline forcing-function; the agent can pull more via the CLI
  // (`npm run search`), so keep the injected block lean — top 3 keyword candidates/item.
  const topKPerItem = opts.topKPerItem ?? 3;
  // `totalCap` is a SOFT total budget; the per-item budget is derived from it. The DEFAULT
  // scales with the node count so EVERY item gets its full `topKPerItem` regardless of core
  // size — the push block is the reuse forcing-function, and a large stat core (30-51 nodes)
  // must NOT starve to 1 candidate/node (the old fixed `80` collapsed perItem to 1 at ~50
  // nodes via `floor(80/items)`, hiding the correct PO/Estimation candidate that ranked #2-3).
  // An explicit `opts.totalCap` still caps a pathological core.
  const totalCap = opts.totalCap ?? Math.max(80, topKPerItem * items.length);
  const perItem = Math.max(1, Math.min(topKPerItem, Math.floor(totalCap / Math.max(1, items.length))));
  // Optional semantic blend: load the tier once and batch-embed every item's query text in a
  // SINGLE call to the warm embedding daemon (~1 s; ~30 s only on a cold daemon start). Any
  // failure (no embeddings, stale, python missing) degrades to lexical-only — never breaks.
  let semTier: SemanticTier | null = null;
  let semVecs: Float32Array[] | null = null;
  if (opts.semantic) {
    try {
      semTier = loadSemanticTier(root, (n) => r.get(n)?.file);
      if (semTier) semVecs = embedQueries(items.map((it) => `${it.title} ${it.body}`), root);
    } catch {
      semTier = null;
      semVecs = null;
    }
  }
  const lines: string[] = [
    "=== CAUSALEAN REUSE CANDIDATES (index-backed, per F1 plan node / item) ===",
    `Source: doc/library_index.json @ ${r.library.commit}. The existing Causalean ` +
      `declarations most likely to fit each F1 item — so you confront real candidates ` +
      `instead of relying on a search you might not think to run.`,
    "CONTRACT: in your Stage-2 Causalean survey table give EACH item below a verdict — " +
      "`reuse <name>` | `bypass-justified: <reason>` | `no-candidate-fits`. Prefer reuse " +
      "when a candidate fits the artifact's abstraction; verify the chosen decl's signature " +
      "with lean_hover_info before building on it. A `⚠usesSorry` candidate carries debt — " +
      "reuse only deliberately.",
    "Each item lists keyword candidates (`•`); a `↳ by type-signature` sub-list (when " +
      "present) matches the item's Lean/math symbols — use it for symbol-heavy items the " +
      "keyword pass missed, and confirm the shape fits. A `↳ relevant areas` line names the " +
      "module(s) whose contents are collectively closest to the item — read there (CLI / " +
      "lean_local_search) when no listed decl fits. To query the Causalean index " +
      "yourself, run the same engine via CLI: " +
      '`cd CausalSmith/tools && npm run search -- "<concept words>"` ' +
      '(also `--type "<sig pattern>"`, `--goal "<goal type>"`, `--cluster <cluster>`). ' +
      "NOTE: `lean_loogle`/`lean_leansearch` index MATHLIB ONLY — they do not see " +
      "Causalean declarations; use them for Mathlib lemmas, the CLI for Causalean.",
  ];
  const symbolTopK = Math.min(2, perItem);
  const render = (c: Candidate, bullet: string) => {
    const tags = [c.file, c.tier1 ? "tier-1" : "", c.usesSorry ? "⚠usesSorry" : ""]
      .filter(Boolean)
      .join(" · ");
    lines.push(`${bullet}${c.name} : ${c.statement.replace(/\s+/g, " ").slice(0, 200)}   [${tags}]`);
    if (c.docFirstPara) lines.push(`      ${c.docFirstPara.slice(0, 240)}`);
  };

  for (let itIdx = 0; itIdx < items.length; itIdx++) {
    const it = items[itIdx];
    lines.push("", `${it.label} — ${it.title}:`);
    // One search per item over a POOL (top-50): the top `perItem` are the decl candidates shown,
    // and the whole pool is aggregated to modules (top-3 pooling) for the "relevant areas"
    // fallback. Slicing the top-`perItem` is identical to the old topK=perItem search (fusion is
    // deterministic), so decl output is unchanged — the pool only adds the module signal.
    const pool = r.search(
      { mode: "concept", title: it.title, label: it.label, bodyTerms: [it.body] },
      {
        cluster,
        topK: 50,
        semantic: semTier && semVecs ? { tier: semTier, queryVec: semVecs[itIdx] } : undefined,
      },
    );
    const cands = pool.slice(0, perItem);
    const areas = poolModules(pool.map((c) => ({ module: c.module, name: c.name, score: c.score })), 2, 3);

    // Type-signature pass: for items whose discriminating content is Lean/math symbols
    // (inner products, projections, `Set.Icc`) rather than prose, concept-mode keyword
    // overlap finds little. Search the item's backtick symbols and surface fits that the
    // concept pass missed — this is what turns word-poor geometry items from noise into
    // exact hits. Gated on ≥3 distinct symbols so word-rich items don't accrete noise.
    const seen = new Set(cands.map((c) => c.name));
    const symText = backtickSpans(`${it.title} ${it.body}`);
    // A real geometry match shares ≥2 distinctive symbols (scores ≥12); a grab-bag item
    // whose backticks hold prose/ranges (`.tex Thm-2 proof KL step`, `[1/4,3/4]`) yields
    // lone-symbol (n=1) hits that score low. The floor keeps the rescue, drops the noise.
    const symCands =
      symbolSet(symText).size >= 3
        ? r
            .search({ mode: "typePattern", pattern: symText }, { cluster, topK: perItem + symbolTopK })
            .filter((s) => !seen.has(s.name) && s.score >= SYMBOL_MIN_SCORE)
            .slice(0, symbolTopK)
        : [];

    // "Relevant areas" fallback (Phase 3 module tier): the modules whose members are, collectively,
    // most relevant to this item — a top-3 pooled module contains a gold decl ~0.80 of the time vs
    // ~0.62 for the exact decl, so this is the warm floor to read when no decl above clearly fits.
    const renderAreas = (bullet: string) => {
      for (const a of areas) {
        const proto = a.prototypes.slice(0, 2).map((n) => n.split(".").slice(-1)[0]).join(", ");
        lines.push(`${bullet}${a.module}${proto ? ` — e.g. ${proto}` : ""}`);
      }
    };

    if (cands.length === 0 && symCands.length === 0) {
      if (areas.length) {
        lines.push("  • (no single decl matched) relevant areas to read — search here with the CLI / lean_local_search:");
        renderAreas("    ↳ ");
      } else {
        const exp = expandQuery(`${it.title} ${it.body}`);
        if (exp.modules.length) {
          lines.push(`  • (no indexed decl matched) likely module(s): ${exp.modules.join(", ")} — search here with lean_local_search.`);
        } else {
          lines.push("  • (no indexed candidate matched — search the cluster substrate root directly.)");
        }
      }
      continue;
    }
    for (const c of cands) render(c, "  • ");
    if (symCands.length) {
      lines.push("  ↳ by type-signature (vocabulary-independent — confirm the shape fits):");
      for (const c of symCands) render(c, "    • ");
    }
    if (areas.length) {
      lines.push(`  ↳ relevant areas (read if none above fits): ${areas.map((a) => a.module).join(" · ")}`);
    }
  }
  lines.push("=== END CAUSALEAN REUSE CANDIDATES ===");
  return lines.join("\n");
}
