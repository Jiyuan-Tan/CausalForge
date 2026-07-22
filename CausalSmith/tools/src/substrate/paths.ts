// CausalSmith/tools/src/substrate/paths.ts
import path from "node:path";

const SUBSTRATE_SLUG_RE = /^[A-Za-z0-9][A-Za-z0-9_-]*$/;

function assertValidSlug(slug: string): void {
  // why: slugs are used in filesystem paths and Lean module names.
  if (!SUBSTRATE_SLUG_RE.test(slug)) throw new Error(`invalid substrate slug: ${slug}`);
}

export function slugToPascal(slug: string): string {
  assertValidSlug(slug);
  return slug
    .split(/[_-]+/)
    .filter(Boolean)
    .map((p) => p.charAt(0).toUpperCase() + p.slice(1))
    .join("");
}

// Run artifacts live in their OWN folder per --study call, under the study
// tree (NOT the main-thread `doc/research/active/` run area). Retired
// study-pipeline runs, if restored, remain under `doc/study/runs/`.
export function substrateRunDir(repoRoot: string, slug: string): string {
  assertValidSlug(slug);
  return path.join(repoRoot, "doc", "study", slug);
}
export function requirementPath(repoRoot: string, slug: string): string {
  return path.join(substrateRunDir(repoRoot, slug), "requirement.md");
}
export function substrateStatePath(repoRoot: string, slug: string): string {
  return path.join(substrateRunDir(repoRoot, slug), "state.json");
}
export function substrateLeanDir(repoRoot: string, slug: string): string {
  assertValidSlug(slug);
  return path.join(repoRoot, "CausalSmith", "Substrate", slugToPascal(slug));
}
export function substrateModulePrefix(slug: string): string {
  assertValidSlug(slug);
  return `CausalSmith.Substrate.${slugToPascal(slug)}`;
}
export function causaleanRoot(repoRoot: string): string {
  return path.dirname(repoRoot);
}
