import { describe, it, expect } from "vitest";
import { mkdtemp, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import {
  parseRealizesTags,
  buildSymbolClusters,
  realizedNotationKey,
  buildRealizedNotationMatcher,
  canonicalSymbolTagKey,
  discoverRealizedSymbols,
} from "../src/formalization/crosswalk.js";

describe("canonicalSymbolTagKey", () => {
  it("matches only harmless math wrappers/bracing and preserves case/comma structure", () => {
    expect(canonicalSymbolTagKey(String.raw`\(P\)`)).toBe("P");
    expect(canonicalSymbolTagKey(String.raw`\(I_0,I_1\)`)).toBe("I_0,I_1");
    expect(canonicalSymbolTagKey(String.raw`\(\pi_k\)`)).toBe("pi_k");
    expect(canonicalSymbolTagKey(String.raw`\(\mu_{ak}\)`)).toBe("mu_{ak}");
    expect(canonicalSymbolTagKey(String.raw`\mathcal{H}`)).toBe(canonicalSymbolTagKey(String.raw`\mathcal H`));
    expect(canonicalSymbolTagKey("pi")).not.toBe(canonicalSymbolTagKey("Pi"));
    expect(canonicalSymbolTagKey("I_0,I_1")).not.toBe(canonicalSymbolTagKey("I_0I_1"));
  });
});

describe("realizedNotationKey", () => {
  it("matches TeX paper notation to ASCII @realizes tags without fuzzy declaration matching", () => {
    expect(realizedNotationKey(String.raw`E_{\mathcal P_N}`)).toBe(realizedNotationKey("E_Pcal_N"));
    expect(realizedNotationKey(String.raw`\mathcal E(\delta)`)).toBe(realizedNotationKey("Ecal(delta)"));
    expect(realizedNotationKey(String.raw`B^{obs}_{gt}`)).toBe(realizedNotationKey("Bobs_gt"));
    expect(realizedNotationKey(String.raw`\omega_{gt}`)).toBe(realizedNotationKey("omega_gt"));
    expect(realizedNotationKey(String.raw`\mathcal R_4`)).toBe(realizedNotationKey("Rcal_4"));
  });

  it("resolves exact Lean symbol families and rejects unrelated missing notation", () => {
    const isRealized = buildRealizedNotationMatcher([
      "Ecal(delta)",
      "m_gt(delta)",
      "Z",
      "Rcal_4",
    ]);
    expect(isRealized(String.raw`\mathcal E`)).toBe(true);
    expect(isRealized(String.raw`m_{gt}`)).toBe(true);
    expect(isRealized("Z")).toBe(true);
    expect(isRealized(String.raw`\mathcal R_4`)).toBe(true);
    expect(isRealized("unformalized_target")).toBe(false);
  });
});

describe("parseRealizesTags (@realizes docstring parser)", () => {
  it("parses a comma list with optional clause hints (commas inside a hint stay)", () => {
    const doc = "/-- foo.\n@realizes tau_P(contrast x = mu1 x - mu0 x, range [-2,2]), e_P, mu_0(in [-1,1]) -/";
    expect(parseRealizesTags(doc)).toEqual([
      { symbol: "tau_P", hint: "contrast x = mu1 x - mu0 x, range [-2,2]" },
      { symbol: "e_P" },
      { symbol: "mu_0", hint: "in [-1,1]" },
    ]);
  });

  it("returns [] when there is no tag", () => {
    expect(parseRealizesTags("/-- a plain docstring with no tag -/")).toEqual([]);
  });

  it("strips a trailing -/ glued to the list", () => {
    expect(parseRealizesTags("/-- x. @realizes A(A:Bool) -/")).toEqual([{ symbol: "A", hint: "A:Bool" }]);
  });

  it("parses EVERY `; @realizes`-separated tag on ONE line (regression: only the first used to survive)", () => {
    const line =
      "  -- @realizes T_i(Z)(product over N_i of Z_k); @realizes Z_k(coordinate z k : Bool); @realizes Z(assignment vector z : I→Bool = {0,1}^{m_n})";
    expect(parseRealizesTags(line)).toEqual([
      { symbol: "T_i(Z)", hint: "product over N_i of Z_k" },
      { symbol: "Z_k", hint: "coordinate z k : Bool" },
      { symbol: "Z", hint: "assignment vector z : I→Bool = {0,1}^{m_n}" },
    ]);
  });

  it("keeps a `;` that lives INSIDE a hint (only a trailing separator `;` is dropped)", () => {
    expect(parseRealizesTags("@realizes A(carrier; range ℝ); @realizes B(x)")).toEqual([
      { symbol: "A", hint: "carrier; range ℝ" },
      { symbol: "B", hint: "x" },
    ]);
  });

  it("keeps comma-indexed TeX names and applied arguments as one symbol", () => {
    expect(parseRealizesTags("@realizes kappa_{r,a}(P)(cumulant coordinate), R^right_{m,L}(t), M^{sep}_{m,K}(model domain)")).toEqual([
      { symbol: "kappa_{r,a}(P)", hint: "cumulant coordinate" },
      { symbol: "R^right_{m,L}(t)" },
      { symbol: "M^{sep}_{m,K}", hint: "model domain" },
    ]);
  });

  it("does not split a comma enclosed by literal escaped TeX braces", () => {
    expect(parseRealizesTags("@realizes S_{\\{0,1\\}}(binary support), T(real carrier)")).toEqual([
      { symbol: "S_{\\{0,1\\}}", hint: "binary support" },
      { symbol: "T", hint: "real carrier" },
    ]);
  });

  it("keeps applied symbol ids stable when prose hints have unbalanced delimiters", () => {
    expect(
      parseRealizesTags(
        "@realizes pi_i^1(p)(product over N_i; range (0,1] under the positivity floor)",
      ),
    ).toEqual([
      {
        symbol: "pi_i^1(p)",
        hint: "product over N_i; range (0,1] under the positivity floor",
      },
    ]);

    // A line-local parser can see only the first line of a continued comment hint.  The
    // application id must still survive so P2 and P4 construct the same `sym:` target.
    expect(parseRealizesTags("@realizes D_1(p,Z)(first component of the denominator")).toEqual([
      { symbol: "D_1(p,Z)", hint: "first component of the denominator" },
    ]);

    // A mismatched interval can close the outer prose parenthesis early. The first complete
    // application group still identifies the symbol boundary.
    expect(
      parseRealizesTags(
        "@realizes V_env(G_n,p)(range [0,∞) co-realizer: every overlap load is nonnegative)",
      ),
    ).toEqual([
      {
        symbol: "V_env(G_n,p)",
        hint: "range [0,∞) co-realizer: every overlap load is nonnegative",
      },
    ]);
  });

  it("uses wrapped core names to preserve unwrapped comma-bearing tags", () => {
    expect(parseRealizesTags("-- @realizes I_0,I_1(split)", [String.raw`\(I_0,I_1\)`, "I_0,I_1"])).toEqual([
      { symbol: "I_0,I_1", hint: "split" },
    ]);
  });
});

describe("buildSymbolClusters (@realizes scan → per-symbol cluster)", () => {
  it("groups the conjunction of decls realizing each symbol; case-sensitive (pi ≠ Pi); untagged → empty", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-"));
    try {
      await writeFile(
        path.join(dir, "Basic.lean"),
        [
          "/-- Observation. @realizes O(carrier), A(A:Bool ↔ {0,1}), Y(carrier ℝ) -/",
          "structure Observation where",
          "  A : Bool",
          "",
          "/-- Law fields. @realizes e_P(propensity : 𝒳 → ℝ carrier), tau_P(contrast carrier) -/",
          "structure ObservedLaw where",
          "  propensity : Nat",
          "",
          "/-- @realizes e_P(propensity x ∈ Icc 0 1), tau_P(contrast = mu1 - mu0) -/",
          "def WellFormedLaw : Prop := True",
          "",
          "/-- @realizes e_P(a.s. 0 < e < 1) -/",
          "def Positivity : Prop := True",
          "",
          "/-- Binary policy. @realizes pi(𝒳→Bool) -/",
          "abbrev Policy := Nat",
          "",
          "/-- Policy class. @realizes Pi(finite-VC) -/",
          "def PolicyClassVC : Prop := True",
          "",
          "/-- a theorem that merely USES e_P but does not realize it -/",
          "theorem usesEp : True := trivial",
        ].join("\n"),
        "utf8",
      );
      const clusters = await buildSymbolClusters(dir, [
        { name: "e_P", space: "X -> (0,1)" },
        { name: "tau_P", space: "X -> [-2,2]" },
        { name: "pi", space: "X -> {0,1}" },
        { name: "Pi", space: "set of (X->{0,1})" },
        { name: "mu_0", space: "X -> [-1,1]" }, // untagged here
      ]);
      const byName = Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => m.decl)]));

      // e_P is realized by the CONJUNCTION of three decls (carrier field + two predicates).
      expect(byName["e_P"]).toEqual(["ObservedLaw", "WellFormedLaw", "Positivity"]);
      // tau_P spans the carrier field decl AND the well-formedness predicate.
      expect(byName["tau_P"]).toEqual(["ObservedLaw", "WellFormedLaw"]);
      // pi and Pi are DISTINCT symbols — case-sensitive, no cross-contamination.
      expect(byName["pi"]).toEqual(["Policy"]);
      expect(byName["Pi"]).toEqual(["PolicyClassVC"]);
      // An untagged symbol yields an EMPTY cluster (a tagging gap, never a fuzzy name match).
      expect(byName["mu_0"]).toEqual([]);

      // The clause hint travels with the member.
      const ep = clusters.find((c) => c.symbol === "e_P")!;
      expect(ep.members.find((m) => m.decl === "Positivity")!.hint).toBe("a.s. 0 < e < 1");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("binds a TRAILING `-- @realizes` comment (below a def body, blank line before the next def) to the ENCLOSING def, not the following one", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-trailing-"));
    try {
      await writeFile(
        path.join(dir, "Basic.lean"),
        [
          "/-- Treated load. -/",
          "noncomputable def r1 (p : Nat) : Nat :=",
          "  p + 1",
          "  -- @realizes r_{ij}^1(G,p)(treated load; range [0,∞))",
          "",
          "/-- Control load. -/",
          "noncomputable def r0 (p : Nat) : Nat :=",
          "  p + 2",
          "  -- @realizes r_{ij}^0(G,p)(control load; range [0,∞))",
          "",
          "/-- Cross load. -/",
          "noncomputable def r10 : Nat := 3   -- @realizes r_{ij}^{10}(G)(cross)",
        ].join("\n"),
        "utf8",
      );
      const clusters = await buildSymbolClusters(dir, [
        { name: "r_{ij}^1(G,p)" },
        { name: "r_{ij}^0(G,p)" },
        { name: "r_{ij}^{10}(G)" },
      ]);
      const byName = Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => m.decl)]));
      // Each trailing tag binds to the def it sits UNDER — the blank line before the next def breaks the
      // docstring-above heuristic. Regression: these used to cross-map r1→r0 and r0→r10.
      expect(byName["r_{ij}^1(G,p)"]).toEqual(["r1"]);
      expect(byName["r_{ij}^0(G,p)"]).toEqual(["r0"]);
      expect(byName["r_{ij}^{10}(G)"]).toEqual(["r10"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("binds a `-- @realizes` trailing a standalone `variable` command to THAT binder, not the preceding closed def", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-variable-"));
    try {
      await writeFile(
        path.join(dir, "Basic.lean"),
        [
          "/-- Variance scale σ². -/",
          "noncomputable def varScale (p : Nat) : Nat :=",
          "  p * p",
          "",
          "end SomeSection",
          "",
          "-- @env: S1",
          "variable (D : FiniteDesign Omega) (p : Nat)   -- @realizes Z(assignment/sample space Omega, carrier of D)",
          "",
          "/-- Bernoulli law. -/",
          "def IndepBernoulli (D : FiniteDesign Omega) : Prop := True",
        ].join("\n"),
        "utf8",
      );
      const clusters = await buildSymbolClusters(dir, [{ name: "Z" }, { name: "sigma^2" }]);
      const byName = Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => `${m.decl}:${m.declKind}`)]));
      // Regression: the Z-tag sits on a `variable` line (not a DECL_HEADER_RE anchor); without the
      // variable-anchor rule it fell through to the preceding `varScale` def and poisoned Z's
      // conjunction with a false drift (varScale realizes σ², not Z).
      expect(byName["Z"]).toEqual(["variable@8:variable"]);
      expect(byName["sigma^2"]).toEqual([]); // varScale is NOT dragged into Z, and carries no σ² tag here
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("attributes an INLINE field tag to the enclosing structure — even on the LAST field before the next decl's docstring", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-inline-"));
    try {
      await writeFile(
        path.join(dir, "Basic.lean"),
        [
          "/-- Law. -/",
          "structure ObservedLaw where",
          "  contrast : Nat -- @realizes tau_P(carrier; =mu1-mu0 via WF)",
          "  mu1 : Nat -- @realizes mu_1(carrier; [-1,1] via Bounded)", // LAST field, then blanks + next docstring
          "",
          "",
          "/-- Overlap def. @realizes p_P(min e 1-e) -/",
          "def overlap : Nat := 0",
        ].join("\n"),
        "utf8",
      );
      const clusters = await buildSymbolClusters(dir, [
        { name: "tau_P", space: "X -> [-2,2]" },
        { name: "mu_1", space: "X -> [-1,1]" },
        { name: "p_P", space: "X -> [0,1/2]" },
      ]);
      const byName = Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => m.decl)]));
      // The inline tag on the last field sits on a CODE line, so it belongs to ObservedLaw,
      // NOT to `overlap` (whose docstring follows after the blank lines).
      expect(byName["tau_P"]).toEqual(["ObservedLaw"]);
      expect(byName["mu_1"]).toEqual(["ObservedLaw"]);
      // The docstring-above tag belongs to the following decl.
      expect(byName["p_P"]).toEqual(["overlap"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("matches math-wrapped core symbols to ordinary tags without conflating case", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-wrapped-"));
    try {
      await writeFile(path.join(dir, "Basic.lean"), [
        "/-- @realizes P(law); @realizes I_0,I_1(split); @realizes pi(policy) -/",
        "def wrappedTargets : Nat := 0",
        "/-- @realizes Pi(policy class) -/",
        "def policyClass : Nat := 0",
      ].join("\n"));
      const clusters = await buildSymbolClusters(dir, [
        { name: String.raw`\(P\)` },
        { name: String.raw`\(I_0,I_1\)` },
        { name: "pi" },
        { name: "Pi" },
      ]);
      const byName = Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => m.decl)]));
      expect(byName[String.raw`\(P\)`]).toEqual(["wrappedTargets"]);
      expect(byName[String.raw`\(I_0,I_1\)`]).toEqual(["wrappedTargets"]);
      expect(byName.pi).toEqual(["wrappedTargets"]);
      expect(byName.Pi).toEqual(["policyClass"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("ignores fake comment/header tokens in strings and supports multiline/quoted decl headers", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-lexical-"));
    try {
      await writeFile(path.join(dir, "Basic.lean"), [
        "def marker : String := \"/- def fake := 0 -/\"",
        "/-- @realizes X(real decl) -/",
        "noncomputable def",
        "  «real decl» : Nat := 1",
      ].join("\n"));
      const clusters = await buildSymbolClusters(dir, [{ name: "X" }]);
      expect(clusters[0].members.map((m) => m.decl)).toEqual(["real decl"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("ignores @realizes text inside strings in both discovery and clustering", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-fake-tags-"));
    try {
      await writeFile(path.join(dir, "Basic.lean"), [
        'def fake : String := "-- @realizes Fake(not a tag)"',
        "/-- @realizes Real(actual tag) -/",
        "def real : Nat := 1",
      ].join("\n"));
      expect(await discoverRealizedSymbols(dir)).toEqual(["Real"]);
      const clusters = await buildSymbolClusters(dir, [{ name: "Fake" }, { name: "Real" }]);
      expect(clusters[0].members).toEqual([]);
      expect(clusters[1].members.map((m) => m.decl)).toEqual(["real"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("binds comment-only tags immediately following a variable command to that binder", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "clusters-variable-follow-"));
    try {
      await writeFile(path.join(dir, "Basic.lean"), [
        "variable (epsilon c : ℝ)",
        "-- @realizes epsilon(overlap)",
        "-- @realizes c(constant)",
        "def after : Nat := 0",
      ].join("\n"));
      const clusters = await buildSymbolClusters(dir, [{ name: "epsilon" }, { name: "c" }]);
      for (const cluster of clusters) {
        expect(cluster.members).toHaveLength(1);
        expect(cluster.members[0].declKind).toBe("variable");
        expect(cluster.members[0].decl).toContain("variable@");
      }
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
