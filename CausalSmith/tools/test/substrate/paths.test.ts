// CausalSmith/tools/test/substrate/paths.test.ts
import { describe, it, expect } from "vitest";
import {
  slugToPascal, substrateRunDir, requirementPath, substrateStatePath,
  substrateLeanDir, substrateModulePrefix, causaleanRoot,
} from "../../src/substrate/paths.js";

const ROOT = "/ws/CausalSmith";

describe("substrate paths", () => {
  it("converts slug to PascalCase", () => {
    expect(slugToPascal("bh_affinity")).toBe("BhAffinity");
    expect(slugToPascal("foo-bar_baz")).toBe("FooBarBaz");
  });
  it("builds run-dir + artifact paths under the study folder", () => {
    expect(substrateRunDir(ROOT, "bh_affinity")).toBe("/ws/CausalSmith/doc/study/bh_affinity");
    expect(requirementPath(ROOT, "bh_affinity")).toBe("/ws/CausalSmith/doc/study/bh_affinity/requirement.md");
    expect(substrateStatePath(ROOT, "bh_affinity")).toBe("/ws/CausalSmith/doc/study/bh_affinity/state.json");
  });
  it("builds lean staging dir + module prefix", () => {
    expect(substrateLeanDir(ROOT, "bh_affinity")).toBe("/ws/CausalSmith/CausalSmith/Substrate/BhAffinity");
    expect(substrateModulePrefix("bh_affinity")).toBe("CausalSmith.Substrate.BhAffinity");
  });
  it("resolves the Causalean root as the parent of repoRoot", () => {
    expect(causaleanRoot(ROOT)).toBe("/ws");
  });
});
