import { readFile, readdir, access } from "node:fs/promises";
import { join } from "node:path";
import { parsePaperGraph, reconcilePaperGraph, type PaperGraph } from "./proofGraph.js";
import {
  applyNlLinks,
  NL_LINKS_POLICY,
  parseNlLinks,
  validateBlocks,
  type NlBlock,
  type NlLinkTable,
} from "./nlLinks.js";
import {
  enrichSnippets,
  resolveDisplayLinks,
  WEB_ONLY_ENVS,
  type ComponentView,
  type DeclSource,
  type LinkProblem,
  type StructuredView,
} from "./paperLean.js";

/**
 * Bundle loader + site-side integrity gate. A bundle is what papersmith P4
 * emits; the site is a pure renderer over it. The gate makes stale links
 * unshippable: a crosswalk entry that doesn't resolve to a block in the HTML
 * and (when Lean-backed) a snippet fails the BUILD, not the reader.
 */

export interface LeanRef {
  file: string;
  decl: string;
  decl_kind: string;
  line: number;
}

export interface CrosswalkEntry {
  obj_id: string;
  env: string;
  paper_label: string;
  title: string | null;
  lean: LeanRef | null;
  fallback: string | null;
  uses: string[];
  /** P4 match provenance; `"presentation-synthesized"` means the block exists
   *  only in the paper, so it must never open a Lean drawer. */
  status?: string;
  sorry_free?: boolean;
}

export interface Snippet {
  decl: string;
  file: string;
  line: number;
  statement: string;
  sorry_free: boolean;
  axioms: string[] | null;
  /** Composite objects: the Lean pieces that jointly formalize the statement. */
  components?: { label: string; statement: string }[];
  /** Build-time enrichment (see `paperLean.ts`): the statement split into
   *  hypotheses and one card per conclusion. Absent when the parser wasn't
   *  confident — render `statement` as-is then. */
  structured?: StructuredView;
  /** Build-time enrichment: every paper declaration this entry's statements
   *  reference, transitively, each classified. A view's source is looked up in
   *  `Bundle.declSources` by its `key` — the same helper is reached from dozens
   *  of statements, so it is stored once per paper, not once per drawer. */
  componentViews?: ComponentView[];
  /** Build-time enrichment: a helper this statement pulls in is itself proved
   *  only up to `sorry`, so the statement is not fully verified. */
  closureHasSorry?: boolean;
  /** Build-time enrichment: how many further declarations the reference walk
   *  left unexplored at the depth cap. Absent when the closure is complete. */
  closureTruncated?: number;
}

export interface FormalLayerItem {
  obj_id: string;
  kind: string;
  label: string;
  nl: string;
  lean: LeanRef | null;
  status: string;
  sorry_free: boolean | null;
}

export interface Meta {
  qid: string;
  spec: string;
  title: string;
  tldr?: string | null;
  abstract: string;
  area: string;
  authorship: string | null;
  created: string;
  wp_number: string | null;
  /** P5 referee's holistic overall score (0–10) + rationale; null = unreviewed.
   *  Drives the "AI reviewer score" badge and best-first ordering. */
  score?: number | null;
  score_rationale?: string | null;
}

export interface Bundle {
  id: string; // <qid>_<spec>
  dir: string;
  meta: Meta;
  commit: string;
  leanSubdir: string;
  entries: CrosswalkEntry[];
  snippets: Record<string, Snippet>;
  bodyHtml: string;
  hasPdf: boolean;
  /** Optional paper-module index (paper_library_index.json, emitted by P4) —
   *  powers the per-paper Formalization page. Same shape as the library index. */
  paperLib: { commit: string; modules: Record<string, string | null>; entries: unknown[] } | null;
  /** Optional "Formal layer" panel data (formal_layer_web.json, emitted by P4) — every from-note
   *  object with its NL + Lean + status, for the web-only correspondence panel. (Distinct from the
   *  SOURCE `formal_layer.json` `{commit, blocks}` that the pipeline reads/writes.) */
  formalLayer: { commit: string; groups: { kind: string; items: FormalLayerItem[] }[] } | null;
  /** Optional seminar deck source (slides.md, authored by P6) — parsed and rendered
   *  by the /papers/[id]/slides page. Absent for papers without a deck. */
  slidesMd: string | null;
  /** Optional proof map (paper_graph.json, emitted by P4) — the paper's
   *  theorem/proposition/lemma blocks plus one edge per "this proof cites that
   *  result", powering the in-page Proof map panel. Bundles emitted before the
   *  artifact existed simply have no panel. */
  paperGraph: PaperGraph | null;
  /** Shared source table for `Snippet.componentViews` (see `paperLean.ts`),
   *  keyed by fully-qualified declaration name. Absent if enrichment failed. */
  declSources?: Record<string, DeclSource>;
}

export async function loadBundle(dir: string, id: string): Promise<Bundle> {
  const j = async (name: string) => JSON.parse(await readFile(join(dir, name), "utf8"));
  const meta = (await j("meta.json")) as Meta;
  const crosswalk = (await j("presentation_crosswalk.json")) as {
    commit: string;
    lean_subdir: string;
    entries: CrosswalkEntry[];
  };
  const snippets = (await j("lean_snippets.json")) as {
    commit: string;
    snippets: Record<string, Snippet>;
  };
  const bodyHtml = await readFile(join(dir, "paper_body.html"), "utf8");

  let paperLib: Bundle["paperLib"] = null;
  try {
    paperLib = await j("paper_library_index.json");
  } catch {
    paperLib = null; // optional artifact
  }

  let formalLayer: Bundle["formalLayer"] = null;
  try {
    // The emitted web panel is `formal_layer_web.json` (`{commit, groups}`). Older bundles emitted
    // it to `formal_layer.json`; new bundles keep the SOURCE `{commit, blocks}` there, so only fall
    // back to it when it actually carries `groups` (never render the source blocks as the panel).
    formalLayer = await j("formal_layer_web.json");
  } catch {
    try {
      const legacy = await j("formal_layer.json");
      formalLayer = legacy && Array.isArray(legacy.groups) ? legacy : null;
    } catch {
      formalLayer = null; // optional artifact (older bundles predate the Formal-layer panel)
    }
  }

  // NL↔Lean crosslinks (`nl_links.json`) — optional, and most bundles predate
  // it. Parsed defensively: an absent, unreadable or malformed artifact simply
  // means the paper renders without the hover pairing. It is also BOUND to this
  // bundle by policy and commit: its `nl`/`lean` strings are verbatim slices of
  // one paper body and one Lean tree, so an artifact from another commit (or
  // another paper) must be ignored, not applied to text it was never checked
  // against.
  let nlLinks: NlLinkTable | null = null;
  try {
    const rawLinks = await j("nl_links.json");
    nlLinks = parseNlLinks(rawLinks, { commit: crosswalk.commit, qid: meta.qid, spec: meta.spec });
    if (!nlLinks) {
      const got = (k: string) => (rawLinks as Record<string, unknown>)?.[k];
      const why =
        got("policy") !== NL_LINKS_POLICY
          ? `its policy is ${JSON.stringify(got("policy"))}, not "${NL_LINKS_POLICY}" ` +
            `(an earlier format carries phrases to search for rather than offsets, so it is not applied)`
          : got("commit") !== crosswalk.commit
            ? `it was written against commit ${JSON.stringify(got("commit"))}, not this bundle's ${JSON.stringify(crosswalk.commit)}`
            : got("qid") !== meta.qid || got("spec") !== meta.spec
              ? `it belongs to a different paper (${JSON.stringify(got("qid"))}/${JSON.stringify(got("spec"))}, ` +
                `not ${JSON.stringify(meta.qid)}/${JSON.stringify(meta.spec)})`
              : `it is not in a shape this understands`;
      console.warn(
        `[bundles] ${id}: ignoring nl_links.json — ${why}. ` +
          `The paper renders without NL↔Lean pairing.`,
      );
    }
  } catch {
    nlLinks = null;
  }

  // Slides, like the proof map, are decoration over the paper, never a gate.
  const slidesMd = await readFile(join(dir, "slides.md"), "utf8").catch(() => null);

  // The proof map is decoration over the paper, never a gate: an artifact that
  // is absent, unreadable, or malformed costs the reader the panel and nothing
  // else, so it is parsed defensively and never contributes a build failure.
  //
  // It is then RECONCILED against the crosswalk and the body. The graph is a
  // separate file from the paper the reader sees, so the two can disagree — a
  // bundle read mid-rewrite pairs a stale graph with a renumbered body, and the
  // map would then label a chip "Lemma 15" while the block it jumps to reads
  // "Lemma 16". Reconciling makes the body the single authority for numbering.
  let paperGraph: PaperGraph | null = null;
  try {
    paperGraph = parsePaperGraph(await j("paper_graph.json"));
  } catch {
    paperGraph = null; // optional artifact (older bundles predate the Proof map)
  }
  if (paperGraph) {
    paperGraph = reconcilePaperGraph(paperGraph, crosswalk.entries, bodyHtml);
  }

  const problems: string[] = [];
  if (crosswalk.commit !== snippets.commit) {
    problems.push(`commit mismatch: crosswalk@${crosswalk.commit} vs snippets@${snippets.commit}`);
  }
  for (const e of crosswalk.entries) {
    const hasLeanTarget = Boolean(e.lean || snippets.snippets[e.obj_id]);
    // "citedv" (source-matched external dependencies), "auxiliary" (agent-introduced proof
    // helpers), and "symbol" (`@realizes` realization clusters) are web-only — surfaced in the
    // Formal-layer panel, deliberately NOT anchored in the paper body — so they are exempt from
    // the body-block check. Their lean→snippet requirement below still applies.
    if (hasLeanTarget && !WEB_ONLY_ENVS.includes(e.env) && !bodyHtml.includes(`data-objid="${e.obj_id}"`)) {
      problems.push(`${e.obj_id}: no data-objid block in paper_body.html`);
    }
    if (e.status === "presentation-synthesized" && bodyHtml.includes(`data-objid="${e.obj_id}"`)) {
      problems.push(`${e.obj_id}: presentation-only block must not enable a Lean drawer`);
    }
    if (e.lean && !snippets.snippets[e.obj_id]) {
      problems.push(`${e.obj_id}: Lean-backed entry has no snippet`);
    }
    if (!e.lean && !e.fallback) {
      problems.push(`${e.obj_id}: neither Lean reference nor fallback text`);
    }
  }
  // A paper with Lean-backed statements must ship a non-empty paper-module index,
  // or the Formalization page renders blank. An empty/absent index here is the
  // silent-empty-page failure (P4 paper_index ran against unbuilt oleans) — make
  // it unshippable rather than letting a blank page reach the reader.
  if (crosswalk.entries.some((e) => e.lean) && (!paperLib || paperLib.entries.length === 0)) {
    problems.push(
      `crosswalk has Lean-backed entries but paper_library_index.json is empty or absent ` +
        `(the Formalization page would be blank) — rebuild the paper's modules and re-run P4's paper_index step`,
    );
  }
  if (problems.length > 0) {
    throw new Error(`bundle ${id} failed integrity gate:\n- ${problems.join("\n- ")}`);
  }
  const hasPdf = await access(join(dir, "paper.pdf")).then(
    () => true,
    () => false,
  );

  // Drawer enrichment (transitive component closure + structured statements) is
  // DECORATION over a bundle that already passed the gate: it makes the drawer
  // self-contained, but a bundle whose enrichment fails is still a correct
  // paper. So it runs after the gate, and any failure costs the reader the
  // extra components and nothing else — it must never be the reason a build
  // stops shipping a verified paper.
  let declSources: Record<string, DeclSource> | undefined;
  let linkSkips: LinkProblem[] = nlLinks ? [...nlLinks.dropped] : [];
  let linkedBody = bodyHtml;

  // Both halves of a crosslink — the prose spans and the Lean-side tokens —
  // must be built from the SAME surviving blocks, or a block dropped on one
  // side would leave the other half pointing at nothing. So the body-dependent
  // checks (digest, offsets) run once, here, and both halves take the result.
  let validBlocks: Record<string, NlBlock> = {};
  if (nlLinks) {
    const checked = validateBlocks(bodyHtml, nlLinks.blocks);
    // Display links are resolved here too, not inside the enrichment: a link
    // whose declaration does not exist must vanish from BOTH halves, or the
    // prose keeps a token whose Lean counterpart was never minted.
    const resolved = resolveDisplayLinks(checked.blocks, paperLib?.entries);
    validBlocks = resolved.blocks;
    linkSkips = [...linkSkips, ...checked.problems, ...resolved.problems];
  }

  try {
    const enrichment = enrichSnippets({
      entries: crosswalk.entries,
      snippets: snippets.snippets,
      paperLibEntries: paperLib?.entries,
      nlLinks: validBlocks,
    });
    for (const [objId, extra] of Object.entries(enrichment.snippets)) {
      const snip = snippets.snippets[objId];
      if (!snip) continue;
      if (extra.structured) snip.structured = extra.structured;
      if (extra.componentViews) snip.componentViews = extra.componentViews;
      // These two are WARNINGS for the reader — a helper proved only up to
      // `sorry`, or a closure cut off at the depth cap. Computing them and
      // leaving them here would mean the drawer silently claims completeness
      // it does not have, which is the exact failure this module exists to fix.
      if (extra.closureHasSorry) snip.closureHasSorry = true;
      if (extra.closureTruncated) snip.closureTruncated = extra.closureTruncated;
    }
    declSources = enrichment.declSources;
    linkSkips = [...linkSkips, ...enrichment.linkProblems];
  } catch (e) {
    console.error(`[bundles] ${id}: Lean drawer enrichment failed, drawers fall back to the raw statement\n${(e as Error).message}`);
  }

  // The prose half of the same crosslinks. Kept separate from the Lean half so
  // one side failing never costs the other: a phrase that no longer matches is
  // dropped, and the block still renders exactly as it did before.
  if (nlLinks) {
    const applied = applyNlLinks(bodyHtml, validBlocks);
    linkedBody = applied.html;
    linkSkips = [...linkSkips, ...applied.skipped];
  }
  if (linkSkips.length > 0) {
    console.warn(
      `[bundles] ${id}: dropped NL\u2194Lean crosslinks for ${linkSkips.length} block(s) ` +
        `(the paper still renders; the pairing is missing there) \u2014 ` +
        linkSkips.map((s) => `${s.objId}: ${s.reason}`).join("; "),
    );
  }

  return {
    id,
    dir,
    meta,
    commit: crosswalk.commit,
    leanSubdir: crosswalk.lean_subdir,
    entries: crosswalk.entries,
    snippets: snippets.snippets,
    bodyHtml: linkedBody,
    hasPdf,
    paperLib,
    formalLayer,
    slidesMd,
    paperGraph,
    declSources,
  };
}

/** Loads every bundle directory (a dir qualifies if it has meta.json). */
export async function loadBundles(roots: string[]): Promise<Bundle[]> {
  const bundles: Bundle[] = [];
  for (const root of roots) {
    let names: string[] = [];
    try {
      names = await readdir(root);
    } catch {
      continue; // a root may not exist yet (e.g. no papers published)
    }
    for (const name of names) {
      const dir = join(root, name);
      const ok = await access(join(dir, "meta.json")).then(
        () => true,
        () => false,
      );
      if (!ok) continue;
      // A bundle that fails the integrity gate must never SHIP, so a build still
      // throws. But `loadBundles` feeds every page's getStaticPaths, so in dev one
      // unreadable bundle would 500 the whole site — including the landing page and
      // unrelated papers. A presentation run rewrites its bundle in place over
      // several minutes, and a reader hitting that window saw a torn crosswalk/body
      // take everything down. In dev, drop the offender loudly and serve the rest.
      try {
        bundles.push(await loadBundle(dir, name));
      } catch (e) {
        if (!import.meta.env?.DEV) throw e;
        console.error(
          `[bundles] SKIPPING "${name}" in dev — it failed the integrity gate, so its ` +
            `pages are absent from this dev server (a build would fail here). This is ` +
            `expected while a presentation run is mid-write; it clears when the run ` +
            `finishes.\n${(e as Error).message}`,
        );
      }
    }
  }
  // Best-first: highest P5 score on top, unscored papers last. Ties break OLDEST-first
  // (operator decision, 2026-08-26): the longer-standing paper keeps the flagship panel —
  // a new paper must strictly beat it to take the featured slot, not merely tie it.
  bundles.sort((a, b) => {
    const sa = typeof a.meta.score === "number" ? a.meta.score : -Infinity;
    const sb = typeof b.meta.score === "number" ? b.meta.score : -Infinity;
    if (sa !== sb) return sb - sa;
    return a.meta.created < b.meta.created ? -1 : 1;
  });
  return bundles;
}

/** Theorem-count badge text shown on the landing page. */
export function verifiedBadge(b: Bundle): string {
  const thms = b.entries.filter((e) => e.env === "theoremv").length;
  const lemmas = b.entries.filter((e) => e.env === "lemmav").length;
  const clean = Object.values(b.snippets).every((s) => s.sorry_free);
  return `✓ ${thms} theorem${thms === 1 ? "" : "s"}, ${lemmas} lemma${lemmas === 1 ? "" : "s"} machine-verified in Lean 4${clean ? "" : " (partial)"}`;
}
