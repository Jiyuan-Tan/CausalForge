import { describe, it, expect } from "vitest";
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { extractDeclSnippet, extractFullDeclSource, tryExtractDeclSnippet, sorryFree } from "../src/presentation/lean_extract.js";
import { loadBankEntry } from "../src/presentation/bank.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";

const SRC = `import Mathlib
/-- doc -/
theorem foo_thm (a b : ℕ) (h : a ≤ b) :
    a + 1 ≤ b + 1 := by
  omega

def myDef (x : ℝ) : ℝ :=
  x + 1
`;

describe("tryExtractDeclSnippet (non-throwing web-bundle variant)", () => {
  it("returns the snippet when the decl is present", () => {
    expect(tryExtractDeclSnippet(SRC, "foo_thm", 3)).toContain("foo_thm");
  });
  it("returns null (not throw) when the decl is absent — e.g. promoted/re-exported elsewhere", () => {
    // A file that only `export`s a promoted decl: the name appears but is never declared here.
    const exportOnly = `import Foo\nexport Causalean.Mathlib.Probability (bernoulli_mean_channel_kl)\n`;
    expect(tryExtractDeclSnippet(exportOnly, "bernoulli_mean_channel_kl", 2)).toBeNull();
    expect(() => extractDeclSnippet(exportOnly, "bernoulli_mean_channel_kl", 2)).toThrow(/not found/);
  });
});

describe("lean snippet extraction", () => {
  it("extracts one exact declaration including its proof body", () => {
    const src = `theorem first (h : True) : True := by\n  exact h\n\n/-- next -/\ntheorem second : True := by\n  trivial\n`;
    const full = extractFullDeclSource(src, "first", 1);
    expect(full).toContain("exact h");
    expect(full).not.toContain("next");
    expect(full).not.toContain("second");
    expect(extractFullDeclSource(src.replace("trivial", "exact True.intro"), "first", 1)).toBe(full);
  });

  it("ignores comment/string delimiter text when finding the next declaration", () => {
    const src = `theorem first : True := by\n  -- documentation mentions /- but opens no block\n  have s : String := "also /- not a comment"\n  trivial\n\ninstance : Inhabited Nat := ⟨0⟩\n\ntheorem second : True := by\n  trivial\n`;
    const full = extractFullDeclSource(src, "first", 1);
    expect(full).toContain("documentation mentions /-");
    expect(full).not.toContain("instance");
    expect(full).not.toContain("second");
  });

  it("tracks a block comment opened on the declaration line", () => {
    const src = `theorem first : True := /- route note\n  still comment -/ by\n  trivial\n\ntheorem second : True := by trivial\n`;
    const full = extractFullDeclSource(src, "first", 1);
    expect(full).toContain("still comment -/ by");
    expect(full).not.toContain("second");
  });

  it("takes theorem statement up to :=", () => {
    const s = extractDeclSnippet(SRC, "foo_thm", 3);
    expect(s).toContain("theorem foo_thm");
    expect(s).toContain("/-- doc -/");
    expect(s).toContain("a + 1 ≤ b + 1");
    expect(s).not.toContain("omega");
  });

  it("takes def with body, capped", () => {
    const s = extractDeclSnippet(SRC, "myDef", 7);
    expect(s).toContain("x + 1");
  });

  // A def followed by the NEXT decl's `-- @node:` tag + a MULTI-LINE `/-- … -/` docstring used to
  // bleed that next-decl preamble into this def's snippet (the interior docstring lines don't
  // individually look like a comment, so the line-by-line strip stopped early). Real P4 drawer
  // incident 2026-06-25: clicking "IID" showed the bounded-outcome docstring.
  const BLEED_SRC = `-- @node: ass:iid
/-- A1 i.i.d. sampling: the observations are
an i.i.d. sample drawn from P. -/
def IsIIDSample (P : Law) : Prop :=
  IsProbabilityMeasure P.data ∧ True

-- @node: ass:bounded-outcome
/-- A2 bounded outcomes: the outcome Y(a) lies in [-1,1]
for both treatment arms, stated as Set.Icc membership
so the encoding is exact (not merely an abs surrogate). -/
def BoundedOutcome (P : Law) : Prop :=
  True
`;

  it("does NOT bleed the next decl's @node tag + multi-line docstring into a def snippet", () => {
    const s = extractDeclSnippet(BLEED_SRC, "IsIIDSample", 4);
    expect(s).toContain("def IsIIDSample");
    expect(s).toContain("IsProbabilityMeasure P.data"); // own body present
    // none of the NEXT declaration leaks in:
    expect(s).not.toContain("@node: ass:bounded-outcome");
    expect(s).not.toContain("A2 bounded outcomes");
    expect(s).not.toContain("BoundedOutcome");
    // own docstring shown in FULL (block-aware), not just its last line:
    expect(s).toContain("/-- A1 i.i.d. sampling");
    // and the decl's OWN @node tag is excluded (pipeline metadata, not the statement):
    expect(s).not.toContain("@node: ass:iid");
  });

  it("shows the full own multi-line docstring, not a mid-sentence fragment", () => {
    const s = extractDeclSnippet(BLEED_SRC, "BoundedOutcome", 12);
    expect(s.split("\n")[0]).toContain("/-- A2 bounded outcomes"); // starts at the opener
    expect(s).toContain("not merely an abs surrogate"); // interior + closing kept
    expect(s).not.toContain("@node"); // no pipeline tags
    expect(s).not.toContain("IsIIDSample"); // no bleed from the PREVIOUS decl
  });

  // A `structure`/`def` has no `:=`, so extraction reads to the NEXT decl keyword. The next decl's
  // docstring is PROSE that can start a line with a decl word ("…the policy class Π…"); that used to
  // falsely truncate mid-docstring, leaking the next `@node:` + doc-comment (real LawStruct incident
  // 2026-06-26). Block-comment tracking now treats those words as prose, not a boundary.
  const STRUCT_SRC = [
    "-- @node: def:law-class",
    "/-- the law class. -/",
    "structure LawClass (P : Law) : Prop where",
    "  bdd : BoundedOutcome P",
    "  strict : StrictOverlapEndpoint P",
    "",
    "-- @node: def:upper-risk",
    "/-- The supremum domain bundles the side conditions: the policy",
    "class Π satisfying PolicyClassVC, and a def upperRisk note that",
    "ends the doc. -/",
    "noncomputable def upperRisk (P : Law) : ℝ :=",
    "  0",
  ].join("\n");

  it("does not truncate a structure on a decl-keyword WORD inside the next decl's docstring", () => {
    const s = extractDeclSnippet(STRUCT_SRC, "LawClass", 3);
    expect(s).toContain("structure LawClass");
    expect(s).toContain("strict : StrictOverlapEndpoint P"); // own last field present
    // none of the NEXT decl (its @node tag, its docstring prose, its name) leaks in:
    expect(s).not.toContain("@node: def:upper-risk");
    expect(s).not.toContain("policy");
    expect(s).not.toContain("PolicyClassVC");
    expect(s).not.toContain("upperRisk");
  });

  it("does not leak the next decl's docstring after a def body", () => {
    // regression: betaWeak was rendered with a dangling `/-- next … -/` because
    // the forward scan pushed the next decl's docstring before breaking on its
    // keyword line.
    const src = `/-- first -/
noncomputable def first (a : ℝ) : ℝ :=
  if a = 0 then 0 else a

/-- second -/
noncomputable def second (b : ℝ) : ℝ := b + 1
`;
    const s = extractDeclSnippet(src, "first", 2);
    expect(s).toContain("/-- first -/");
    expect(s.trimEnd().endsWith("if a = 0 then 0 else a")).toBe(true);
    expect(s).not.toContain("/-- second -/");
  });

  it("tolerates a stale line hint", () => {
    const s = extractDeclSnippet(SRC, "foo_thm", 30);
    expect(s).toContain("theorem foo_thm");
  });

  it("resolves a FULLY-QUALIFIED crosswalk name by its leaf (source declares only the leaf)", () => {
    // Real crosswalk rows carry `Ns.Sub.FeasibleDesign`, but the Lean source declares
    // `structure FeasibleDesign`. Without the leaf fallback every FQN row throws `not found`.
    const src = `/-- design -/\nstructure FeasibleDesign (e : Nat) : Prop where\n  ok : True\n\ndef other := 1`;
    const s = extractDeclSnippet(src, "CausalSmith.Experimentation.BipartiteMinimaxDesign.FeasibleDesign", 2);
    expect(s).toContain("structure FeasibleDesign");
    expect(s).not.toContain("def other");
  });

  it("prefers the FULL name over the leaf when both could match (no false leaf hit)", () => {
    // Two decls whose leaves collide only if we ignored the namespace: the full-name pass must win.
    const src = `def Foo := 1\n\ndef Bar := 2`;
    const s = extractDeclSnippet(src, "Ns.Foo", 1);
    expect(s).toContain("def Foo");
    expect(s).not.toContain("def Bar");
  });

  it("extracts a `noncomputable abbrev` (modifier is a general prefix, not just `noncomputable def`)", () => {
    const src = `/-- alias -/\nnoncomputable abbrev p10_triangularClass : Set Nat := triangularClass\n\ndef other := 1`;
    const s = extractDeclSnippet(src, "p10_triangularClass", 2);
    expect(s).toContain("noncomputable abbrev p10_triangularClass");
    expect(s).not.toContain("def other");
  });

  it("sorryFree ignores comments", () => {
    expect(sorryFree("theorem a : True := trivial -- no sorry here")).toBe(true);
    expect(sorryFree("theorem a : True := sorry")).toBe(false);
  });

  it("extracts a real banked declaration's statement via the crosswalk (integration)", async () => {
    const root = causalSmithRoot();
    const { qid, spec } = acceptedBankEntry();
    const entry = await loadBankEntry(root, qid, spec);
    // The crosswalk is graph-derived, keyed by NODE id; pick the first row whose Lean decl
    // extractDeclSnippet can locate by name (a row recorded with a fully-qualified name is resolved
    // by leaf elsewhere — here any one resolvable row suffices to exercise the extractor on real data).
    let snippet: string | null = null;
    for (const cw of entry.crosswalk) {
      if (!cw.lean) continue;
      const src = await readFile(join(root, entry.leanSubdir, cw.lean.file), "utf8").catch(() => null);
      if (!src) continue;
      try {
        const s = extractDeclSnippet(src, cw.lean.decl, cw.lean.line);
        if (s && s.trim().length > 0) { snippet = s; break; }
      } catch {
        /* unresolved by name → try the next crosswalk row */
      }
    }
    expect(snippet).not.toBeNull();
    // The snippet is a declaration's STATEMENT, not its proof body: it opens with a Lean decl keyword,
    // is bounded (did not run into a multi-thousand-line proof), and stops before the `:= by` proof.
    expect(snippet!).toMatch(/\b(theorem|lemma|def|abbrev|structure|noncomputable|instance)\b/);
    expect(snippet!.split("\n").length).toBeLessThan(400);
    expect(snippet!).not.toContain(":= by");
  });
});
