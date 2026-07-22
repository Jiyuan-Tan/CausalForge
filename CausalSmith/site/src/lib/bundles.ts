import { readFile, readdir, access } from "node:fs/promises";
import { join } from "node:path";

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
   *  Drives the "self-reported score" badge and best-first ordering. */
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
    if (hasLeanTarget && !["citedv", "auxiliary", "symbol"].includes(e.env) && !bodyHtml.includes(`data-objid="${e.obj_id}"`)) {
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
  return {
    id,
    dir,
    meta,
    commit: crosswalk.commit,
    leanSubdir: crosswalk.lean_subdir,
    entries: crosswalk.entries,
    snippets: snippets.snippets,
    bodyHtml,
    hasPdf,
    paperLib,
    formalLayer,
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
  // Best-first: highest P5 score on top, unscored papers last, recency as the tiebreak.
  bundles.sort((a, b) => {
    const sa = typeof a.meta.score === "number" ? a.meta.score : -Infinity;
    const sb = typeof b.meta.score === "number" ? b.meta.score : -Infinity;
    if (sa !== sb) return sb - sa;
    return a.meta.created < b.meta.created ? 1 : -1;
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
