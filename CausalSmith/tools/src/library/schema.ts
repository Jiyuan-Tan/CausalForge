import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";

/**
 * Library-index schema + loader shared by check_library_index and the NL sweep.
 * The site (CausalSmith/site/src/lib/library.ts) duplicates this deliberately —
 * the two packages stay decoupled. Keep the hash algorithm in sync.
 *
 * The index artifact (`doc/library_index.json` at the Causalean package root) is
 * produced by `lake exe library_index`; the sidecars (`doc/library_review/<Area>.json`)
 * carry human curation: headline-theorem lists and review stamps whose semantics are
 * "the NL translation faithfully renders this formal statement at this hash".
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
  /** Proof-term dependencies (premises used in theorem proofs), disjoint from statement refs. */
  proofRefs: string[];
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
  /** Curated description for an area-root explorer page. */
  intro?: string;
  /** Curated descriptions for nested explorer pages, keyed below the area. */
  namespace_intros?: Record<string, string>;
}

export interface Library {
  commit: string;
  toolchain: string;
  entries: LibDecl[];
  /** module name → module docstring (null when the file has none) */
  modules: Record<string, string | null>;
  sidecars: Record<string, AreaSidecar>; // keyed by area
}

export type ReviewStatus = "reviewed" | "stale" | "unreviewed";

/** Whitespace-insensitive content key of a formal statement. */
export function statementHash(statement: string): string {
  return (
    "sha256:" +
    createHash("sha256").update(statement.replace(/\s+/g, " ").trim()).digest("hex")
  );
}

/** Top-level library area of a decl (`Causalean/PO/Core/System.lean` → `PO`). */
export function declArea(d: LibDecl): string {
  const parts = d.file.split("/");
  return parts.length > 2 ? parts[1] : "Root";
}

const TIER1_KINDS = new Set(["def", "structure", "class", "inductive", "axiom"]);

/** Tier-1 = trust anchors: every definition-like decl + sidecar-listed headline theorems. */
export function isTier1(d: LibDecl, sidecars: Record<string, AreaSidecar>): boolean {
  if (TIER1_KINDS.has(d.kind)) return true;
  return (sidecars[declArea(d)]?.headline_theorems ?? []).includes(d.name);
}

/** The authored natural-language explanation for a declaration. Lean's
environment metadata omits docstrings on some named local instances, while the
index's source slice preserves the same `/-- ... -/` block. */
export function naturalLanguageDoc(d: { doc?: string | null; source?: string | null }): string | null {
  if (d.doc?.trim()) return d.doc;
  const sourceDoc = d.source?.match(/^\s*\/--([\s\S]*?)-\//)?.[1]?.trim();
  return sourceDoc || null;
}

/**
 * Source files containing public theorem/lemma declarations but no curated theorem/lemma anchor.
 *
 * A definition may be tier 1 automatically, but it must not make a theorem-bearing page look
 * curated: its public mathematical result needs an explicit `headline_theorems` entry.
 */
export function theoremFilesWithoutCuratedAnchor(lib: Library): string[] {
  const byFile = new Map<string, LibDecl[]>();
  for (const d of lib.entries) {
    if (d.kind !== "theorem" && d.kind !== "lemma") continue;
    const entries = byFile.get(d.file) ?? [];
    entries.push(d);
    byFile.set(d.file, entries);
  }
  return [...byFile]
    .filter(([, decls]) => !decls.some((d) => isTier1(d, lib.sidecars)))
    .map(([file]) => file)
    .sort();
}

/**
 * Published explorer pages which have neither a curated short description nor a
 * module docstring. Covers both intermediate namespace pages — a new subtree
 * often creates one (for example `Causalean.Mathlib.AlgebraicGeometry`) without
 * a Lean file at that exact path, so no file docstring can describe it — and
 * leaf modules backed by a real file, whose `/-! -/` block may be missing or
 * (the common failure) merged into the copyright `/- -/` header, where it reads
 * fine in source but never registers as a module docstring.
 */
export function publishedModulesWithoutShortDescription(lib: Library): string[] {
  const modules = [...new Set(
    lib.entries
      .map((d) => d.module),
  )].sort();
  const firstSentence = (doc: string | null | undefined): string =>
    (doc ?? "").split(/\n\s*\n/)[0].trim();

  const publishedModules = new Set<string>();
  for (const module of modules) {
    const parts = module.split(".");
    // `end <= parts.length` so the module itself is gated, not just its
    // ancestors. Start at 3 to omit `Causalean.<Area>`, whose description is
    // the area `intro` rather than a module docstring.
    for (let end = 3; end <= parts.length; end++) {
      publishedModules.add(parts.slice(0, end).join("."));
    }
  }

  return [...publishedModules].filter((module) => {
    const descendant = lib.entries.find((d) => d.module === module || d.module.startsWith(`${module}.`));
    if (!descendant) return false;
    // The production index always has `file`; retain a module-name fallback
    // for lightweight callers that construct only the route-relevant fields.
    const area = descendant.file ? declArea(descendant) : (descendant.module.split(".")[1] ?? "Root");
    const prefix = area === "Root" ? "Causalean." : `Causalean.${area}.`;
    const path = module.startsWith(prefix) ? module.slice(prefix.length) : "";
    const curated = path ? lib.sidecars[area]?.namespace_intros?.[path] : lib.sidecars[area]?.intro;
    return !(curated?.trim() || firstSentence(lib.modules[module]));
  });
}

/**
 * Public declaration cards which would render the explorer's
 * "No natural-language translation yet" fallback. The explorer exposes every
 * definition-like declaration and sidecar-curated theorem, so this is its
 * exact publication boundary rather than merely a source-style convention.
 */
export function tier1DeclarationsWithoutNaturalLanguage(lib: Library): string[] {
  return lib.entries
    .filter(
      (d) =>
        isTier1(d, lib.sidecars) &&
        !naturalLanguageDoc(d),
    )
    .map((d) => d.name)
    .sort();
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

/** Loads index + sidecars from the Causalean package root; throws on integrity problems. */
export function loadLibrary(root: string): Library {
  const raw = JSON.parse(
    readFileSync(join(root, "doc", "library_index.json"), "utf8"),
  ) as {
    commit: string;
    toolchain: string;
    entries: (Omit<LibDecl, "proofRefs"> & { proofRefs?: unknown })[];
    modules?: Record<string, string | null>;
  };
  const entries: LibDecl[] = raw.entries.map((e) => ({
    ...e,
    proofRefs: Array.isArray(e.proofRefs) ? e.proofRefs.filter((r): r is string => typeof r === "string") : [],
  }));
  const names = new Set(entries.map((e) => e.name));
  const sidecars: Record<string, AreaSidecar> = {};
  const reviewDir = join(root, "doc", "library_review");
  let files: string[] = [];
  try {
    files = readdirSync(reviewDir).filter((f) => f.endsWith(".json"));
  } catch {
    files = [];
  }
  const problems: string[] = [];
  for (const f of files) {
    const area = f.replace(/\.json$/, "");
    const sc = JSON.parse(readFileSync(join(reviewDir, f), "utf8")) as AreaSidecar;
    for (const key of ["headline_theorems", "reviews", "flags"] as const) {
      if (!Array.isArray(sc[key])) problems.push(`${f}: missing array field ${key}`);
    }
    for (const t of sc.headline_theorems ?? []) {
      if (!names.has(t)) problems.push(`${f}: headline theorem ${t} not in index`);
    }
    for (const r of sc.reviews ?? []) {
      if (!names.has(r.decl)) problems.push(`${f}: review for unknown decl ${r.decl}`);
    }
    for (const fl of sc.flags ?? []) {
      if (!names.has(fl.decl)) problems.push(`${f}: flag for unknown decl ${fl.decl}`);
    }
    sidecars[area] = sc;
  }
  if (problems.length > 0) {
    throw new Error(`library_review integrity:\n- ${problems.join("\n- ")}`);
  }
  return { commit: raw.commit, toolchain: raw.toolchain, entries, modules: raw.modules ?? {}, sidecars };
}
