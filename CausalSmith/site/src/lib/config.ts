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

export const SERIES_NAME = "CausalForge";
export const SERIES_TAGLINE = "AI Causal Scientist";
