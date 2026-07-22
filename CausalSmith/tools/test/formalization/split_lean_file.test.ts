import { describe, it, expect } from "vitest";
import { splitFlatNamespaceFile } from "../../src/formalization/splitLeanFile.js";

const opts = { modulePrefix: "CausalSmith.Demo", baseName: "Helpers", lineBudget: 12 };

/** A flat-namespace file with `n` decls, each `bodyLines` long, plus optional injected text. */
function file(decls: string[], preamble = "import Mathlib.Tactic\n"): string {
  return `${preamble}\nnamespace Demo\n\n${decls.join("\n\n")}\n\nend Demo\n`;
}

const decl = (name: string, pad = 6) =>
  [`theorem ${name} : True := by`, ...Array.from({ length: pad }, () => "  -- filler"), "  trivial"].join("\n");

describe("splitFlatNamespaceFile — scope safety", () => {
  it("splits a genuinely flat file", () => {
    const r = splitFlatNamespaceFile(file([decl("a"), decl("b"), decl("c")]), opts);
    expect(r.ok).toBe(true);
    expect(r.parts.length).toBeGreaterThanOrEqual(2);
  });

  it("refuses a file with a bare `section`", () => {
    const src = file([decl("a"), decl("b"), decl("c")]).replace("namespace Demo\n", "namespace Demo\nsection\n");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/non-flat/);
  });

  // `noncomputable section` opens a scope exactly like `section`, but a `/^section\b/` test does
  // not match it. Compounding it, the anonymous `end` that closes such a scope is excluded from
  // the namespace-`end` count, so the file passes the "exactly one namespace…end" check and gets
  // split into parts that do not reproduce or close the scope.
  it("refuses a file with a `noncomputable section`", () => {
    const src = file([decl("a"), decl("b"), decl("c")])
      .replace("namespace Demo\n", "namespace Demo\nnoncomputable section\n")
      .replace("\nend Demo\n", "\nend\n\nend Demo\n");
    const r = splitFlatNamespaceFile(src, opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/non-flat/);
  });
});

describe("splitFlatNamespaceFile — command prefixes", () => {
  // `set_option … in` applies to the NEXT command. If a chunk boundary lands between the two,
  // the prefix is applied to whatever command follows it in the old file while the decl it was
  // meant for moves to another part without its budget — a build that fails or hangs.
  it("keeps a `set_option … in` attached to the decl it modifies", () => {
    const decls = [decl("a"), `set_option maxHeartbeats 1000000 in\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const withPrefix = [...r.parts.map((p) => p.content), r.aggregator].filter((t) =>
      t.includes("set_option maxHeartbeats 1000000 in"),
    );
    expect(withPrefix).toHaveLength(1);
    // the prefix and its theorem must live in the SAME emitted text, adjacent
    expect(withPrefix[0]).toMatch(/set_option maxHeartbeats 1000000 in\s*\ntheorem b\b/);
  });

  it("keeps stacked command prefixes with their decl", () => {
    const decls = [decl("a"), `open Classical in\nset_option maxHeartbeats 400000 in\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const owner = [...r.parts.map((p) => p.content), r.aggregator].find((t) => t.includes("open Classical in"))!;
    expect(owner).toMatch(/open Classical in\s*\nset_option maxHeartbeats 400000 in\s*\ntheorem b\b/);
  });

  it("keeps a docstring, an attribute and a command prefix together with the decl", () => {
    const decls = [
      decl("a"),
      `/-- doc for b -/\n@[simp]\nset_option maxHeartbeats 400000 in\n${decl("b")}`,
      decl("c"),
    ];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(true);
    const owner = [...r.parts.map((p) => p.content), r.aggregator].find((t) => t.includes("doc for b"))!;
    expect(owner).toMatch(/\/-- doc for b -\/\s*\n@\[simp\]\s*\nset_option maxHeartbeats 400000 in\s*\ntheorem b\b/);
  });

  // Refuse rather than guess: a prefix that binds across a blank line cannot be attributed to a
  // decl header by the upward walk, so splitting could silently detach it.
  it("refuses when a command prefix cannot be attached to a following decl", () => {
    const decls = [decl("a"), `set_option maxHeartbeats 400000 in\n\n${decl("b")}`, decl("c")];
    const r = splitFlatNamespaceFile(file(decls), opts);
    expect(r.ok).toBe(false);
    expect(r.reason).toMatch(/command prefix/i);
  });
});
