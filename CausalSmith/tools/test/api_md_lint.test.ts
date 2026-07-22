import { describe, it, expect } from "vitest";
import {
  extractApiMdPathRefs,
  apiMdMissingPaths,
  apiMdCheckTarget,
} from "../src/formalization/api_md_lint.js";

describe("extractApiMdPathRefs", () => {
  it("takes the first backtick path token per ## header, ignores topic headers", () => {
    const md = [
      "## 1. `Graph/DAG.lean` — Directed Acyclic Graphs",
      "## Workspace context",
      "## 2. Panel theorems",
      "## 3. `SCM/Do/Rule2.lean` — Rule 2 plumbing",
    ].join("\n");
    expect(extractApiMdPathRefs(md).map((r) => r.token)).toEqual([
      "Graph/DAG.lean",
      "SCM/Do/Rule2.lean",
    ]);
  });

  it("expands a brace group into one ref per file", () => {
    const md = "## 8d. `SCM/Do/{FullCondIndep, GlobalMarkov}.lean` — Markov split";
    expect(extractApiMdPathRefs(md).map((r) => r.token)).toEqual([
      "SCM/Do/FullCondIndep.lean",
      "SCM/Do/GlobalMarkov.lean",
    ]);
  });

  it("ignores a non-path backtick (no slash, no .lean)", () => {
    expect(extractApiMdPathRefs("## 9. `doMono` — the multi-target do operator")).toEqual([]);
  });

  it("accepts a trailing-slash directory token", () => {
    expect(extractApiMdPathRefs("## 2. `Graph/DSep/` — d-separation").map((r) => r.token)).toEqual([
      "Graph/DSep/",
    ]);
  });
});

describe("apiMdCheckTarget", () => {
  it("reduces a glob token to its parent directory", () => {
    expect(apiMdCheckTarget("SCM/Factored/*.lean")).toBe("SCM/Factored/");
    expect(apiMdCheckTarget("SCM/Do/Rule2Kernel/Structural/*.lean")).toBe(
      "SCM/Do/Rule2Kernel/Structural/",
    );
  });
  it("leaves a non-glob token unchanged", () => {
    expect(apiMdCheckTarget("Graph/DAG.lean")).toBe("Graph/DAG.lean");
  });
});

describe("apiMdMissingPaths", () => {
  it("flags only tokens whose resolved path does not exist", () => {
    const refs = extractApiMdPathRefs("## 1. `a/x.lean` — A\n## 2. `b/y.lean` — B");
    const exists = (t: string) => t === "a/x.lean";
    expect(apiMdMissingPaths(refs, exists).map((f) => f.token)).toEqual(["b/y.lean"]);
  });
  it("checks the parent directory for a glob token (not the literal `*`)", () => {
    const refs = extractApiMdPathRefs("## 1. `SCM/Factored/*.lean` — Factored kernel");
    const exists = (t: string) => t === "SCM/Factored/";
    expect(apiMdMissingPaths(refs, exists)).toEqual([]);
  });
});
