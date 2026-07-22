import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { join } from "node:path";
import { bankAcceptedDir } from "./paths.js";
import { Crosswalk, type CrosswalkEntry } from "./types.js";
import { loadBankGraph, isCitedNode, renderedNodes, type FormalizationGraph, type GraphNode } from "./graph_view.js";
import { isUndeliveredNode } from "../graph/types.js";

/** decl_kind hint for a node kind (extractDeclSnippet scans by name, so this is
 *  only a display/grep hint, not load-bearing). A cited gate's Lean object is an
 *  assumed `def : Prop`, hence `def`. */
const DECL_KIND: Record<string, string> = {
  theorem: "theorem",
  lemma: "lemma",
  assumption: "structure",
  definition: "def",
  gate: "def",
};

/**
 * Derive the crosswalk view from the formalization graph — the graph is the
 * source of truth, so the crosswalk is keyed by NODE id (matching the env
 * labels P1/P2 emit) with each node's Lean anchor. Replaces the legacy F5
 * crosswalk file (which keyed by obj-id `P-3` and went stale on relabeling).
 * Every rendered paper object becomes a row; decl-less rendered objects carry
 * `lean:null` so downstream anchor checks still know the object exists.
 */
export function graphCrosswalk(graph: FormalizationGraph): CrosswalkEntry[] {
  // Cited gates have no numbered paper environment, but retain a crosswalk row so the web formal
  // panel and exact Lean/source dependency remain inspectable. Deduplicate defensively for legacy
  // graphs whose presentation policy still rendered cited gates.
  const nodes = [...renderedNodes(graph), ...graph.nodes.filter(isCitedNode)];
  return [...new Map(nodes.map((n) => [n.id, n] as const)).values()]
    .map((n: GraphNode) => ({
      // Key by NODE id — this is the join key the rest of causalsmith uses: P1/P2 label every
      // env `\begin{...}{<node id>}` and its in-body `\cref{obj:<node id>}` use the same, so the
      // rendered HTML `data-objid` is the node id too. The obj_id alias (`A-1`/`P-1`/`T-1`) is a
      // NOTE-side anchor only; the note blocks are remapped alias→node-id at the P4 seam. (Legacy
      // alias-less graphs have `id` already in obj-id-derived form, so this is unchanged for them.)
      obj_id: n.id,
      kind: n.kind,
      title: n.obj_id ?? n.id,
      tex: { label: "", line_range: n.nl?.tex_anchor ?? "" },
      lean: !isUndeliveredNode(n) && n.lean?.decl_name
        ? {
            file: n.lean.file ?? "Basic.lean",
            decl: n.lean.decl_name,
            decl_kind: DECL_KIND[n.kind] ?? "def",
            line: 0,
          }
        : null, // why: decl-less rendered assumptions still need crosswalk/anchor rows.
      // A cited gate is an IMPORTED result (verified against its source at F2.5, not proved here),
      // so it gets its own verdict rather than the proved-object "equivalent"/"unmatched": `cited`
      // when source-matched, `cited-unverified` otherwise — the site shows this honestly instead of
      // mislabeling an assumed `def` as an unmatched proof obligation.
      verdict: isUndeliveredNode(n)
        ? "unmatched"
        : isCitedNode(n)
        ? n.review?.status === "matched" || n.review?.status === "derived"
          ? "cited"
          : "cited-unverified"
        : n.review?.status === "matched" || n.review?.status === "derived"
          ? "equivalent"
          : "unmatched",
    }));
}

/** Loaded view of one accepted bank entry — causalsmith's sole input. */
export interface BankEntry {
  dir: string;
  noteMd: string;
  /** The formalization graph (the trust anchor). Statements, lean anchors,
   *  review verdicts, and dependency edges all come from here. */
  graph: FormalizationGraph;
  /** Legacy F5 crosswalk. Being migrated out (consumers move to `graph`); kept
   *  until the last consumer is on the graph. Do NOT add new readers. */
  crosswalk: CrosswalkEntry[];
  leanSubdir: string; // repo-relative, from banked state.json `lean_subdir`
  readme: Record<string, string>; // flat scalar frontmatter keys (qid, spec, topic, …)
  proposalTex: string | null;
  derivationTex: string | null;
  /** Discovery's curated bibliography, including sources attached to cited
   *  graph nodes. P0 must see this alongside proposal.tex: later frozen
   *  environments may legitimately cite one of these keys. */
  sourceBibliography: { key: string; citation: string }[];
  /** Persisted source-match records; presentation uses their locator in theorem-local scope notes. */
  citedChecks?: Array<{
    name: string;
    check_status: string;
    cite_id?: string;
    locator?: string;
    reviewer?: "codex" | "claude";
  }>;
}

function parseFrontmatter(md: string): Record<string, string> {
  const m = md.match(/^---\n([\s\S]*?)\n---/);
  const out: Record<string, string> = {};
  if (!m) return out;
  for (const line of m[1].split("\n")) {
    const kv = line.match(/^(\w+):\s*(.*)$/);
    if (kv && kv[2] !== "") out[kv[1]] = kv[2].replace(/^"|"$/g, "");
  }
  return out;
}

const optional = async (path: string): Promise<string | null> =>
  readFile(path, "utf8").catch(() => null);

/**
 * Resolve an artifact within a banked entry, honoring the phase-subfolder split
 * (new entries nest under `discovery/` or `formalization/`; older entries are
 * flat). Returns the nested path when it exists, else the flat path — mirrors
 * `artifactPath`'s back-compat for the bank-read side.
 */
const entryFile = (
  dir: string,
  phase: "discovery" | "formalization",
  bare: string,
  legacy: string,
): string => {
  // Prefer the bare causalsmith-style name (nested then flat), then the legacy
  // `<qid>_<spec>_`-prefixed name, mirroring `artifactPath`'s resolution.
  for (const name of [bare, legacy]) {
    const nested = join(dir, phase, name);
    if (existsSync(nested)) return nested;
    const flat = join(dir, name);
    if (existsSync(flat)) return flat;
  }
  return join(dir, phase, bare);
};

export async function loadBankEntry(
  repoRoot: string,
  qid: string,
  spec: string,
): Promise<BankEntry> {
  const dir = bankAcceptedDir(repoRoot, qid, spec);
  const base = `${qid}_${spec}`;
  const noteMd = await optional(entryFile(dir, "formalization", "formalization.md", `${base}.md`));
  const cwRaw = await optional(
    entryFile(dir, "formalization", "crosswalk_full.json", `${base}_crosswalk_full.json`),
  );
  // Root (state stays flat); bare `state.json` preferred over the legacy prefixed name.
  const stateRaw = await optional(
    existsSync(join(dir, "state.json")) ? join(dir, "state.json") : join(dir, `${base}_state.json`),
  );
  if (!noteMd || !stateRaw) {
    throw new Error(
      `bank entry ${base} at ${dir} is missing ` +
        `${[!noteMd && "note", !stateRaw && "state"].filter(Boolean).join("/")}`,
    );
  }
  const graph = await loadBankGraph(dir, qid, spec);
  // The graph is the trust anchor: derive the crosswalk from it (node-id keyed,
  // always consistent with the rendered env labels). Fall back to the legacy F5
  // crosswalk file only for an entry whose graph carries no Lean-anchored nodes.
  const derived = graphCrosswalk(graph);
  const crosswalk =
    derived.length > 0 ? derived : cwRaw ? Crosswalk.parse(JSON.parse(cwRaw)) : [];
  const state = JSON.parse(stateRaw) as {
    lean_subdir?: string;
    cited_checks?: BankEntry["citedChecks"];
  };
  if (!state.lean_subdir) throw new Error(`state.json for ${base} has no lean_subdir`);
  const coreRaw = await optional(entryFile(dir, "discovery", "core.json", `${base}_core.json`));
  const core = coreRaw
    ? (JSON.parse(coreRaw) as { bibliography?: { key?: unknown; citation?: unknown }[] })
    : {};
  const sourceBibliography = (core.bibliography ?? []).flatMap((entry) =>
    typeof entry.key === "string" && typeof entry.citation === "string"
      ? [{ key: entry.key, citation: entry.citation }]
      : [],
  );
  return {
    dir,
    noteMd,
    graph,
    crosswalk,
    leanSubdir: state.lean_subdir,
    readme: parseFrontmatter((await optional(join(dir, "README.md"))) ?? ""),
    proposalTex: await optional(entryFile(dir, "discovery", "proposal.tex", `${base}_proposal.tex`)),
    derivationTex: await optional(entryFile(dir, "discovery", "writeup.tex", `${base}.tex`)),
    sourceBibliography,
    citedChecks: state.cited_checks ?? [],
  };
}
