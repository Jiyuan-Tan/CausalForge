import { describe, it, expect, vi, afterEach } from "vitest";

/**
 * `sourceRef` decides which git ref every GitHub source link on the site resolves
 * against. Getting it wrong is not a visible build failure — it ships a page whose
 * links all 404 — so pin both branches of the fallback.
 */

const PINNED = "6e3ba5a09e998cb7c7b15f45d6a11634157a62aa";

/** Re-imports config with SITE_GITHUB_REF set (or cleared) for this call only. */
async function withRef(ref: string | undefined) {
  vi.resetModules();
  const prev = process.env.SITE_GITHUB_REF;
  if (ref === undefined) delete process.env.SITE_GITHUB_REF;
  else process.env.SITE_GITHUB_REF = ref;
  try {
    return await import("../src/lib/config.js");
  } finally {
    if (prev === undefined) delete process.env.SITE_GITHUB_REF;
    else process.env.SITE_GITHUB_REF = prev;
  }
}

afterEach(() => {
  vi.resetModules();
});

describe("sourceRef", () => {
  it("keeps the artifact's pinned commit when no override is set", async () => {
    const { sourceRef, GITHUB_REF } = await withRef(undefined);
    expect(GITHUB_REF).toBeNull();
    expect(sourceRef(PINNED)).toBe(PINNED);
  });

  it("overrides the pinned commit with SITE_GITHUB_REF", async () => {
    // The deploy workflow passes the commit being published; artifacts stamped with a
    // commit from another repo would otherwise produce links that do not resolve.
    const { sourceRef } = await withRef("222c7d1abc0000000000000000000000000000de");
    expect(sourceRef(PINNED)).toBe("222c7d1abc0000000000000000000000000000de");
  });

  it("accepts a branch name as the override", async () => {
    const { sourceRef } = await withRef("main");
    expect(sourceRef(PINNED)).toBe("main");
  });
});
