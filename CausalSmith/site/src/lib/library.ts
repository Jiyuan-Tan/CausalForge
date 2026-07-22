import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { join, resolve } from "node:path";

/**
 * Library index loader + integrity gate for the /library explorer pages.
 * Deliberately duplicates CausalSmith/tools/src/library/schema.ts — the two
 * packages stay decoupled. Keep the hash algorithm in sync.
 */

export interface LibDecl {
  name: string;
  kind: string; // def | theorem | structure | class | inductive | instance | axiom | opaque
  module: string;
  file: string;
  line: number;
  statement: string;
  /** Verbatim declaration source (definition-like kinds; null for theorems). */
  source?: string | null;
  doc: string | null;
  refs: string[];
  /** Mathlib/core constants in the statement (name + defining module) for doc links. */
  extRefs?: { n: string; m: string }[];
  axioms: string[];
  usesSorry: boolean;
}

export interface ReviewEntry {
  decl: string;
  statement_hash: string;
  reviewed_at_commit: string;
  reviewer: string;
  note?: string;
}

export interface AreaSidecar {
  headline_theorems: string[];
  reviews: ReviewEntry[];
  flags: { decl: string; note: string; flagged_at_commit: string }[];
  /** Curated one-line description of the top-level module, shown in the module table. */
  intro?: string;
  /** Descriptions of inner namespace levels (no Lean file of their own), keyed by the
   *  dotted path below the area (`"CATE"`, `"CATE.OSL"`). */
  namespace_intros?: Record<string, string>;
}

export interface Library {
  commit: string;
  toolchain: string;
  entries: LibDecl[];
  sidecars: Record<string, AreaSidecar>;
  /** First module docstring (`/-! … -/`) per Lean module, from the extractor. */
  modules: Record<string, string | null>;
}

function isSubstrateModule(module: string): boolean {
  return module === "Causalean.Substrate" || module.startsWith("Causalean.Substrate.");
}

function isPublicLibraryDecl(d: LibDecl): boolean {
  return !d.file.startsWith("Causalean/Substrate/") && !isSubstrateModule(d.module);
}

function publicModules(modules: Record<string, string | null>): Record<string, string | null> {
  return Object.fromEntries(
    Object.entries(modules).filter(([module]) => !isSubstrateModule(module)),
  );
}

export type ReviewStatus = "reviewed" | "stale" | "unreviewed";

/** Default root: the Causalean package root (the workspace root, four levels up). */
export function libraryRoot(): string {
  return resolve(import.meta.dirname, "..", "..", "..", "..");
}

/** Whitespace-insensitive content key of a formal statement. */
export function statementHash(statement: string): string {
  return (
    "sha256:" +
    createHash("sha256").update(statement.replace(/\s+/g, " ").trim()).digest("hex")
  );
}

/** Top-level library area of a decl (`Causalean/PO/Basic.lean` → `PO`). */
export function declArea(d: LibDecl): string {
  const parts = d.file.split("/");
  return parts.length > 2 ? parts[1] : "Root";
}

/** Modules that are "dir-files": a Foo.lean with a sibling Foo/ directory of
 *  child modules. Their decl cards render on their OWN page; plain files render
 *  on their parent directory's page. Cached per Library. */
const dirFileCache = new WeakMap<Library, Set<string>>();
function dirFiles(lib: Library): Set<string> {
  let s = dirFileCache.get(lib);
  if (!s) {
    s = new Set();
    const mods = [...new Set(lib.entries.map((e) => e.module))].sort();
    for (let i = 0; i + 1 < mods.length; i++) {
      if (mods[i + 1].startsWith(mods[i] + ".")) s.add(mods[i]);
    }
    dirFileCache.set(lib, s);
  }
  return s;
}

/** Slash-joined path (area-first) of the library page that renders this decl's
 *  cards — pages are per DIRECTORY level, so a decl in Causalean.PO.ID.Manski
 *  lives at "PO/ID" (or "PO/ID/Manski" when Manski.lean has child modules). */
export function declPagePath(d: LibDecl, lib: Library): string {
  const area = declArea(d);
  const prefix = area === "Root" ? "Causalean." : `Causalean.${area}.`;
  const segs = d.module.startsWith(prefix) ? d.module.slice(prefix.length).split(".") : [];
  const dirSegs = dirFiles(lib).has(d.module) ? segs : segs.slice(0, -1);
  return [area, ...dirSegs].join("/");
}

const TIER1_KINDS = new Set(["def", "structure", "class", "inductive", "axiom"]);

/** Tier-1 = trust anchors: every definition-like decl + sidecar-listed headline theorems. */
export function isTier1(d: LibDecl, sidecars: Record<string, AreaSidecar>): boolean {
  if (TIER1_KINDS.has(d.kind)) return true;
  return (sidecars[declArea(d)]?.headline_theorems ?? []).includes(d.name);
}

/** The declaration's natural-language explanation. Named local instances do
not always retain a Lean environment docstring, but their indexed source still
contains the authored `/-- ... -/` block. */
export function naturalLanguageDoc(d: Pick<LibDecl, "doc" | "source">): string | null {
  if (d.doc?.trim()) return d.doc;
  const sourceDoc = d.source?.match(/^\s*\/--([\s\S]*?)-\//)?.[1]?.trim();
  return sourceDoc || null;
}

/** Open flag notes recorded against a decl (newest first), for server-side render. */
export function flagsOf(d: LibDecl, sidecars: Record<string, AreaSidecar>): string[] {
  return (sidecars[declArea(d)]?.flags ?? [])
    .filter((f) => f.decl === d.name)
    .map((f) => f.note);
}

function isGeneratedNativeDecideAxiom(axiom: string): boolean {
  return /(?:^|\.)_native\.native_decide\.ax(?:$|_)/.test(axiom);
}

/** Axioms worth surfacing as a public correctness badge.
 *
 * `sorryAx` has its own badge, and Lean emits `_native.native_decide.ax_*`
 * implementation witnesses for some closed finite computations; those are noisy
 * implementation artifacts on the explorer page rather than hand-authored
 * mathematical assumptions.
 */
export function publicAxioms(axioms: string[]): string[] {
  return axioms.filter((a) => a !== "sorryAx" && !isGeneratedNativeDecideAxiom(a));
}

/** reviewed = stamp exists at the current statement hash; stale = statement changed since. */
export function reviewStatus(
  d: LibDecl,
  sidecars: Record<string, AreaSidecar>,
): ReviewStatus {
  const r = sidecars[declArea(d)]?.reviews.find((x) => x.decl === d.name);
  if (!r) return "unreviewed";
  return r.statement_hash === statementHash(d.statement) ? "reviewed" : "stale";
}

/** How many curated (tier-1) decls in `decls` still need review — i.e. have no
 *  review stamp at the current statement hash (status `unreviewed` or `stale`).
 *  Drives the per-file / per-submodule "to review" tag shown in review mode. */
export function unreviewedCount(
  decls: LibDecl[],
  sidecars: Record<string, AreaSidecar>,
): number {
  return decls.filter(
    (d) => isTier1(d, sidecars) && reviewStatus(d, sidecars) !== "reviewed",
  ).length;
}

/** Reads the review sidecars fresh from disk; throws on integrity problems.
 *  Exported separately so dev-mode pages can re-read them per request — the
 *  dev server caches getStaticPaths props, which would otherwise show review
 *  stamps written after server start as unreviewed. */
export function loadSidecars(root: string, names: Set<string>): Record<string, AreaSidecar> {
  const sidecars: Record<string, AreaSidecar> = {};
  const reviewDir = join(root, "doc", "library_review");
  let files: string[] = [];
  try {
    files = readdirSync(reviewDir).filter((f) => f.endsWith(".json"));
  } catch {
    files = [];
  }
  // A STRUCTURAL malformation (a non-array field) is a hard error — the schema is
  // broken. But a sidecar entry that REFERENCES a decl absent from the index
  // (a headline/review/flag whose decl was renamed or removed) is DRIFT, not
  // corruption: it happens routinely mid-refactor (the index regenerates ahead of
  // the curation sidecars). Throwing on drift used to 500 the ENTIRE site for one
  // stale entry, so instead drop the stale entry with a warning and keep serving.
  const fatal: string[] = [];
  for (const f of files) {
    const area = f.replace(/\.json$/, "");
    const sc = JSON.parse(readFileSync(join(reviewDir, f), "utf8")) as AreaSidecar;
    for (const key of ["headline_theorems", "reviews", "flags"] as const) {
      if (!Array.isArray(sc[key])) fatal.push(`${f}: missing array field ${key}`);
    }
    if (Array.isArray(sc.headline_theorems)) {
      sc.headline_theorems = sc.headline_theorems.filter((t) => {
        if (names.has(t)) return true;
        console.warn(`[library] ${f}: dropping stale headline theorem not in index: ${t}`);
        return false;
      });
    }
    if (Array.isArray(sc.reviews)) {
      sc.reviews = sc.reviews.filter((r) => {
        if (names.has(r.decl)) return true;
        console.warn(`[library] ${f}: dropping review for unknown decl: ${r.decl}`);
        return false;
      });
    }
    if (Array.isArray(sc.flags)) {
      sc.flags = sc.flags.filter((fl) => {
        if (names.has(fl.decl)) return true;
        console.warn(`[library] ${f}: dropping flag for unknown decl: ${fl.decl}`);
        return false;
      });
    }
    sidecars[area] = sc;
  }
  if (fatal.length > 0) {
    throw new Error(`library_review integrity (structural):\n- ${fatal.join("\n- ")}`);
  }
  return sidecars;
}

/** Loads index + sidecars from the Causalean package root; throws on integrity problems. */
export function loadLibrary(root: string): Library {
  const raw = JSON.parse(
    readFileSync(join(root, "doc", "library_index.json"), "utf8"),
  ) as {
    commit: string;
    toolchain: string;
    entries: LibDecl[];
    modules?: Record<string, string | null>;
  };
  const entries = raw.entries.filter(isPublicLibraryDecl);
  return {
    commit: raw.commit,
    toolchain: raw.toolchain,
    entries,
    sidecars: loadSidecars(root, new Set(entries.map((e) => e.name))),
    modules: publicModules(raw.modules ?? {}),
  };
}

/** A node of the hierarchical module tree of one top-level library module. */
export interface ModTree {
  /** Last path segment (`CATE`). */
  seg: string;
  /** Dotted path below the area (`CATE.OSL`). */
  path: string;
  /** Full Lean module name when a source file lives exactly here. */
  module?: string;
  children: ModTree[];
}

export function displayModuleSegment(seg: string): string {
  const display = seg === "DiscreteID" ? "Discrete ID" : seg;
  return display.replace(/([a-z0-9])([A-Z])/g, "$1\u00ad$2");
}

export function displayModulePath(path: string): string {
  return path.split(".").map(displayModuleSegment).join(".");
}

/**
 * Builds the nested module tree of one area from its leaf module names
 * (`Causalean.Estimation.CATE.OSL.DRLearner.Analytic` → CATE → OSL → DRLearner →
 * Analytic). A node carries `module` when a file lives at that exact path; inner
 * namespace nodes carry only children.
 */
export function buildModuleTree(area: string, modules: string[]): ModTree[] {
  const prefix = area === "Root" ? "Causalean." : `Causalean.${area}.`;
  return buildModuleTreeFromPrefix(prefix, modules);
}

/** Generic tree builder for an arbitrary dotted-module prefix (paper runs etc.). */
export function buildModuleTreeFromPrefix(prefix: string, modules: string[]): ModTree[] {
  interface Mut { seg: string; path: string; module?: string; children: Map<string, Mut> }
  const roots = new Map<string, Mut>();
  for (const m of [...modules].sort()) {
    if (!m.startsWith(prefix)) continue;
    const segs = m.slice(prefix.length).split(".");
    let level = roots;
    let path = "";
    let node: Mut | undefined;
    for (const seg of segs) {
      path = path ? `${path}.${seg}` : seg;
      node = level.get(seg);
      if (!node) {
        node = { seg, path, children: new Map() };
        level.set(seg, node);
      }
      level = node.children;
    }
    if (node) node.module = m;
  }
  const freeze = (n: Mut): ModTree => ({
    seg: n.seg,
    path: n.path,
    module: n.module,
    children: [...n.children.values()].sort((a, b) => a.seg.localeCompare(b.seg)).map(freeze),
  });
  return [...roots.values()].sort((a, b) => a.seg.localeCompare(b.seg)).map(freeze);
}

/** Orders sibling tree nodes in reading order: a topological sort of the
 *  statement-level dependency edges between their subtrees (prerequisites
 *  first), with alphabetical tiebreak; cycles fall back to alphabetical. */
export function orderByDependency(nodes: ModTree[], lib: Library): ModTree[] {
  const modsOf = new Map(nodes.map((n) => [n, new Set(treeModules(n))]));
  const owner = new Map<string, ModTree>(); // decl name -> sibling subtree
  for (const e of lib.entries) {
    for (const [n, mods] of modsOf) if (mods.has(e.module)) owner.set(e.name, n);
  }
  const deps = new Map<ModTree, Set<ModTree>>(nodes.map((n) => [n, new Set()]));
  for (const e of lib.entries) {
    const from = [...modsOf].find(([, mods]) => mods.has(e.module))?.[0];
    if (!from) continue;
    for (const r of e.refs) {
      const to = owner.get(r);
      if (to && to !== from) deps.get(from)!.add(to);
    }
  }
  // dependents count: how many siblings build on this node (foundations first)
  const dependents = new Map<ModTree, number>(nodes.map((n) => [n, 0]));
  for (const ds of deps.values()) for (const d of ds) dependents.set(d, dependents.get(d)! + 1);
  const sorted: ModTree[] = [];
  const done = new Set<ModTree>();
  const pending = [...nodes].sort(
    (x, y) => dependents.get(y)! - dependents.get(x)! || x.seg.localeCompare(y.seg),
  );
  while (pending.length > 0) {
    const i = pending.findIndex((n) => [...deps.get(n)!].every((d) => done.has(d)));
    const next = pending.splice(i >= 0 ? i : 0, 1)[0]; // i<0: cycle — take queue head
    sorted.push(next);
    done.add(next);
  }
  return sorted;
}

/** All Lean module names in a subtree (the node's own file plus every descendant). */
export function treeModules(node: ModTree): string[] {
  return [node.module, ...node.children.flatMap(treeModules)].filter(
    (x): x is string => !!x,
  );
}

/** Strips the leading doc comment from a source slice (the NL is rendered separately). */
/** The literal declaration keyword from the source slice (`lemma` vs `theorem`,
 *  `abbrev` vs `def`, ...). The kernel erases this — both lemma and theorem
 *  elaborate to the same object — so display fidelity needs the source text. */
export function sourceKind(d: LibDecl): string {
  // Strip the docstring FIRST: a doc paragraph reflowed at this file's column
  // width can easily start a line with a keyword-shaped word (e.g. "...positive
  // model\nclass. This is a *sound...*"), which the line-start regex below
  // would otherwise mistake for the real declaration keyword.
  const stripped = d.source ? stripLeadingDoc(d.source) : undefined;
  const m = stripped?.match(
    /(?:^|\n)\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque)\b/,
  );
  return m ? m[1] : d.kind;
}

export function stripLeadingDoc(source: string): string {
  return source.replace(/^\s*\/--[\s\S]*?-\/\s*\n?/, "").trimEnd();
}

/** First sentence of a module/intro doc, markdown headers stripped — for summaries. */
export function firstSentence(doc: string | null | undefined): string | null {
  if (!doc) return null;
  const text = doc
    .replace(/^#+\s+[^\n]*$/gm, "") // drop markdown headers
    .replace(/\s+/g, " ")
    .trim();
  if (!text) {
    // header-only module doc: the header text itself is the best brief
    const h = doc.match(/^#+\s+(.+)$/m);
    return h ? h[1].replace(/`/g, "").trim().slice(0, 220) : null;
  }
  const plain = text.replace(/\*\*([^*]+)\*\*/g, "$1").replace(/`([^`]+)`/g, "$1");
  const m = plain.match(/^.*?[.!?](?=\s|$)/);
  return (m ? m[0] : plain).slice(0, 220);
}

function esc(s: string): string {
  return s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

/**
 * Maps short name and full name → decl, for identifier linkification.
 * Short names that collide across decls are dropped (ambiguous → no link).
 */
export function nameMap(lib: Library): Map<string, LibDecl> {
  const m = new Map<string, LibDecl | null>();
  for (const e of lib.entries) {
    m.set(e.name, e);
    const short = e.name.split(".").pop()!;
    // Single-codepoint leaf names (W, X, μ, Γ, 𝒦, …) are invariably structure
    // fields written `s.W` in real use; as a bare token in a statement such a
    // letter is a bound variable, not a reference. Registering the short key
    // would link every `W`/`X`/… to an unrelated field, so keep these decls
    // linkable only under their full name.
    if ([...short].length > 1) {
      if (!m.has(short)) m.set(short, e);
      else if (m.get(short) !== e) m.set(short, null); // ambiguous
    }
  }
  const out = new Map<string, LibDecl>();
  for (const [k, v] of m) if (v) out.set(k, v);
  return out;
}

/** Official-docs URL for a Mathlib/Std/core declaration; null for other deps. */
export function mathlibDocUrl(name: string, module: string): string | null {
  const root = module.split(".")[0];
  if (!["Mathlib", "Std", "Lean", "Init", "Batteries"].includes(root)) return null;
  return `https://leanprover-community.github.io/mathlib4_docs/${module.replace(/\./g, "/")}.html#${name}`;
}

/** Maps identifier tokens → external doc URLs for every Mathlib/core constant any
 *  statement references. Full names always; short names only when unambiguous and
 *  not shadowing a Causalean name. */
export function extNameMap(lib: Library, causalean: Map<string, LibDecl>): Map<string, string> {
  const m = new Map<string, string | null>();
  for (const e of lib.entries) {
    for (const r of e.extRefs ?? []) {
      const url = mathlibDocUrl(r.n, r.m);
      if (!url) continue;
      if (!m.has(r.n)) m.set(r.n, url);
      const short = r.n.split(".").pop()!;
      if ([...short].length <= 1) continue; // bound-variable letter, not a reference
      if (causalean.has(short)) continue;
      if (!m.has(short)) m.set(short, url);
      else if (m.get(short) !== url) m.set(short, null); // ambiguous
    }
  }
  const out = new Map<string, string>();
  for (const [k, v] of m) if (v) out.set(k, v);
  return out;
}

/**
 * Escapes a pretty-printed statement and wraps known identifiers in links:
 * Causalean names → their decl cards; Mathlib/core names → the official
 * mathlib4 docs. Only exact hits in the maps get linked, so the deliberately
 * broad unicode token regex is harmless.
 */
// nameMap/extNameMap are O(all entries) to build and linkifyStatement runs per
// declaration — cache both per Library or page renders are quadratic.
const nameMapCache = new WeakMap<Library, Map<string, LibDecl>>();
const extMapCache = new WeakMap<Library, Map<string, string>>();

export function linkifyStatement(
  statement: string,
  lib: Library,
  base: string,
  selfNames?: Set<string>,
): string {
  let map = nameMapCache.get(lib);
  if (!map) {
    map = nameMap(lib);
    nameMapCache.set(lib, map);
  }
  let ext = extMapCache.get(lib);
  if (!ext) {
    ext = extNameMap(lib, map);
    extMapCache.set(lib, ext);
  }
  const re = /[A-Za-z_¡-￿][A-Za-z0-9_.'¡-￿]*/g;
  // A token followed by the REST of its binder group and then a `:` is a BINDER:
  // a structure field (`factual :`), an explicit binder (`(r : …)`), a type
  // ascription, or any name in a multi-name group (`{… Dtilde Hβ : …}`). The
  // intervening `(?:\s+ident)*` is what generalizes past the single-name case —
  // only the last name in `(a b c : T)` sits immediately before the colon.
  const BINDER_AHEAD = /^(?:\s+[A-Za-z_¡-￿][A-Za-z0-9_.'¡-￿]*)*\s*:(?![:=])/;
  // A name BOUND by this statement is a local variable for the whole statement,
  // so it must never link — not at its binder, nor where it recurs in a
  // hypothesis/body later. Collect all such names first (binders precede their
  // uses, but a separate pass is order-independent and cheap). Without this, a
  // bound regressor like `Dtilde` mislinks every occurrence to the global
  // `GoodmanBacon.Dtilde` — a jump to an unrelated paper.
  const bound = new Set<string>();
  for (const m of statement.matchAll(re)) {
    if (BINDER_AHEAD.test(statement.slice(m.index! + m[0].length))) bound.add(m[0]);
  }
  const out: string[] = [];
  let last = 0;
  for (const m of statement.matchAll(re)) {
    out.push(esc(statement.slice(last, m.index)));
    const tok = m[0];
    const end = m.index! + tok.length;
    const isBinder = bound.has(tok);
    const hit = isBinder ? undefined : map.get(tok);
    const extHit = hit ? null : isBinder ? undefined : ext.get(tok);
    // Linked references display the leaf only — the full namespace path
    // (`Causalean.Stat.` …) bloats statements and is redundant with the link
    // target. Keep the full name on hover via `title`.
    const leaf = esc(tok.split(".").pop()!);
    const titleAttr = tok.includes(".") ? ` title="${esc(tok)}"` : "";
    if (hit && selfNames?.has(hit.name)) {
      out.push(`<a href="#${hit.name}"${titleAttr}>${leaf}</a>`);
    } else if (hit) {
      out.push(
        `<a href="${base}/library/${declPagePath(hit, lib)}#${hit.name}"${titleAttr}>${leaf}</a>`,
      );
    } else if (extHit) {
      out.push(
        `<a class="ext-link" href="${extHit}" target="_blank" rel="noopener"${titleAttr}>${leaf}</a>`,
      );
    } else {
      out.push(esc(tok));
    }
    last = end;
  }
  out.push(esc(statement.slice(last)));
  return out.join("");
}
