import { resolve } from "node:path";

/** Where bundles are discovered at build time. SITE_FIXTURES=1 adds the demo bundle. */
export function bundleRoots(): string[] {
  const roots = [resolve(import.meta.dirname, "..", "..", "..", "doc", "presentation")];
  if (process.env.SITE_FIXTURES === "1") {
    roots.push(resolve(import.meta.dirname, "..", "..", "fixtures"));
  }
  return roots;
}

/** "org/repo" for commit-pinned GitHub source links; null hides the link. */
export const GITHUB_REPO: string | null = process.env.SITE_GITHUB_REPO ?? null;

/**
 * Git ref that source links resolve against, overriding each artifact's own pinned commit.
 *
 * Artifacts (library index, paper bundles) stamp the commit of the repo they were GENERATED
 * in. When the site is built from a repo whose history is a re-commit of that one, those SHAs
 * do not exist under `SITE_GITHUB_REPO` and every source link 404s. The deploy workflow sets
 * this to the commit actually being published, so links resolve against the tree the reader
 * is looking at. Unset (dev, or a build from the repo the artifacts were stamped in) keeps the
 * pinned commit, which is the more precise target.
 */
export const GITHUB_REF: string | null = process.env.SITE_GITHUB_REF ?? null;

/** The ref a source link should use for an artifact pinned at `commit`. */
export function sourceRef(commit: string): string {
  return GITHUB_REF ?? commit;
}

export const SERIES_NAME = "CausalSmith";
export const SERIES_TAGLINE = "AI Causal Scientist";
