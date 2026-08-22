import { describe, it, expect } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  canonicalProofHelperContext, existingProofForP2, proofRenderCacheKey, sectionCacheKey,
} from "../src/presentation/stages/p2_draft.js";

describe("sectionCacheKey (P2 content-keyed section cache)", () => {
  const base = () => sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "(no review)");

  it("is stable for identical inputs; re-keys when the objs are reordered (safe re-draft)", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "(no review)")).toBe(base());
    expect(sectionCacheKey("02_main.tex", ["thm:b", "def:a"], "brief", "k1", "(no review)")).not.toBe(base());
  });
  it("changes when an env is added to / removed from the section (the restructure case)", () => {
    // def:a moved away → this section now has only thm:b → must re-draft.
    expect(sectionCacheKey("02_main.tex", ["thm:b"], "brief", "k1", "(no review)")).not.toBe(base());
  });
  it("changes when the brief, the cites, or the revision brief changes", () => {
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "BRIEF2", "k1", "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k2", "(no review)")).not.toBe(base());
    expect(sectionCacheKey("02_main.tex", ["def:a", "thm:b"], "brief", "k1", "[major] fix wording")).not.toBe(base());
  });
  it("takes NO environment-body input: a re-rendered env swaps into cached prose without a re-draft", () => {
    // The signature itself is the contract — bodies are substituted mechanically at assembly
    // (normalizeFrozenEnvs), so they must not be able to invalidate authored prose.
    expect(sectionCacheKey.length).toBe(5);
  });
});

describe("proofRenderCacheKey", () => {
  const baseParts = () => ({
    modelKey: "model", objId: "thm:main", envTex: "THEOREM", leanPath: "/repo/Main.lean",
    leanDecl: "main", exactDecl: "theorem main : P := by trivial",
    helperContext: [{ obj_id: "lem:b", tex: "B" }, { obj_id: "lem:a", tex: "A" }],
    notation: "NOTATION", revisionBrief: "BRIEF", citedDependencies: "CITED",
    informalDerivation: "DERIVATION",
  });
  it("is invariant under helper presentation-order permutations", () => {
    const parts = baseParts();
    expect(proofRenderCacheKey({ ...parts, helperContext: [...parts.helperContext].reverse() }))
      .toBe(proofRenderCacheKey(parts));
  });
  it("changes for helper body or membership changes", () => {
    const parts = baseParts(), key = proofRenderCacheKey(parts);
    expect(proofRenderCacheKey({ ...parts, helperContext: [{ obj_id: "lem:b", tex: "B2" }, parts.helperContext[1]] })).not.toBe(key);
    expect(proofRenderCacheKey({ ...parts, helperContext: parts.helperContext.slice(1) })).not.toBe(key);
    expect(proofRenderCacheKey({ ...parts, helperContext: [{ obj_id: "lem:c", tex: "B" }, parts.helperContext[1]] })).not.toBe(key);
  });
  it("rejects duplicate helper identities instead of depending on their input order", () => {
    expect(() => canonicalProofHelperContext([{ obj_id: "lem:a", tex: "A" }, { obj_id: "lem:a", tex: "B" }]))
      .toThrow(/duplicate obj_id lem:a/);
  });
  it("changes only the affected theorem identity/body/brief/notation/Lean mapping inputs", () => {
    const parts = baseParts(), key = proofRenderCacheKey(parts);
    for (const changed of [
      { objId: "thm:other" }, { envTex: "THEOREM2" }, { revisionBrief: "BRIEF2" },
      { notation: "NOTATION2" }, { leanPath: "/repo/Other.lean" }, { leanDecl: "main2" },
      { exactDecl: "theorem main : Q := by trivial" }, { citedDependencies: "CITED2" },
      { informalDerivation: "DERIVATION2" },
    ]) expect(proofRenderCacheKey({ ...parts, ...changed })).not.toBe(key);
  });
});

describe("explicit existing-proof audit candidate", () => {
  it("reuses a file on a key miss only when explicitly enabled and never calls it a cache hit", async () => {
    const dir = await mkdtemp(join(tmpdir(), "p2-existing-proof-"));
    const path = join(dir, "proof.tex");
    await writeFile(path, "existing proof\n");
    try {
      expect(await existingProofForP2(path, "old", "new", false)).toBeNull();
      expect(await existingProofForP2(path, "old", "new", true)).toEqual({
        text: "existing proof\n", cacheHit: false,
      });
      expect(await existingProofForP2(path, "new", "new", false)).toEqual({
        text: "existing proof\n", cacheHit: true,
      });
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
