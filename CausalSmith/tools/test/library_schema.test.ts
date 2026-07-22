import { describe, expect, it } from "vitest";
import { mkdtempSync, mkdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  loadLibrary,
  statementHash,
  reviewStatus,
  declArea,
  isTier1,
  publishedModulesWithoutShortDescription,
} from "../src/library/schema.js";

function fixtureRoot(opts: { badReviewDecl?: boolean } = {}): string {
  const root = mkdtempSync(join(tmpdir(), "libidx-"));
  mkdirSync(join(root, "doc", "library_review"), { recursive: true });
  const entries = [
    {
      name: "Causalean.PO.Foo",
      kind: "def",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 10,
      statement: "ℕ →  ℕ",
      doc: "Adds one.\n\nImplementation note.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.PO.foo_thm",
      kind: "theorem",
      module: "Causalean.PO.Basic",
      file: "Causalean/PO/Basic.lean",
      line: 20,
      statement: "∀ n, Causalean.PO.Foo n = n + 1",
      doc: null,
      refs: ["Causalean.PO.Foo"],
      axioms: [],
      usesSorry: false,
    },
  ];
  writeFileSync(
    join(root, "doc", "library_index.json"),
    JSON.stringify({ commit: "abc", toolchain: "t", entries }),
  );
  writeFileSync(
    join(root, "doc", "library_review", "PO.json"),
    JSON.stringify({
      headline_theorems: ["Causalean.PO.foo_thm"],
      reviews: [
        {
          decl: opts.badReviewDecl ? "Causalean.PO.Missing" : "Causalean.PO.Foo",
          statement_hash: statementHash("ℕ → ℕ"),
          reviewed_at_commit: "abc",
          reviewer: "jytan",
          note: "",
        },
      ],
      flags: [],
    }),
  );
  return root;
}

describe("library schema", () => {
  it("hash is whitespace-insensitive", () => {
    expect(statementHash("ℕ  →\n ℕ")).toBe(statementHash("ℕ → ℕ"));
  });

  it("loads a valid fixture and computes statuses", () => {
    const lib = loadLibrary(fixtureRoot());
    expect(lib.entries).toHaveLength(2);
    const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
    expect(declArea(foo)).toBe("PO");
    expect(isTier1(foo, lib.sidecars)).toBe(true);
    expect(reviewStatus(foo, lib.sidecars)).toBe("reviewed");
    const thm = lib.entries.find((e) => e.name === "Causalean.PO.foo_thm")!;
    expect(isTier1(thm, lib.sidecars)).toBe(true); // headline
    expect(reviewStatus(thm, lib.sidecars)).toBe("unreviewed");
  });

  it("flips to stale when the statement changes", () => {
    const root = fixtureRoot();
    const lib = loadLibrary(root);
    const foo = lib.entries.find((e) => e.name === "Causalean.PO.Foo")!;
    foo.statement = "ℕ → ℤ";
    expect(reviewStatus(foo, lib.sidecars)).toBe("stale");
  });

  it("throws when a review references a missing decl", () => {
    expect(() => loadLibrary(fixtureRoot({ badReviewDecl: true }))).toThrow(/Missing/);
  });
});

describe("published modules without a short description", () => {
  // Builds a two-level tree: leaf `Causalean.PO.ID.Leaf` under namespace page
  // `Causalean.PO.ID`. `modules` carries the module docstrings.
  function descRoot(modules: Record<string, string>, intros?: Record<string, string>): string {
    const root = mkdtempSync(join(tmpdir(), "libdesc-"));
    mkdirSync(join(root, "doc", "library_review"), { recursive: true });
    writeFileSync(
      join(root, "doc", "library_index.json"),
      JSON.stringify({
        commit: "abc",
        toolchain: "t",
        modules,
        entries: [
          {
            name: "Causalean.PO.ID.Leaf.Foo",
            kind: "def",
            module: "Causalean.PO.ID.Leaf",
            file: "Causalean/PO/ID/Leaf.lean",
            line: 1,
            statement: "ℕ → ℕ",
            doc: "Adds one.",
            refs: [],
            axioms: [],
            usesSorry: false,
          },
        ],
      }),
    );
    writeFileSync(
      join(root, "doc", "library_review", "PO.json"),
      JSON.stringify({
        headline_theorems: [],
        reviews: [],
        flags: [],
        ...(intros ? { namespace_intros: intros } : {}),
      }),
    );
    return root;
  }

  const described = {
    "Causalean.PO.ID": "The identification layer.",
    "Causalean.PO.ID.Leaf": "A leaf module.",
  };

  it("passes when every page has a module docstring", () => {
    const lib = loadLibrary(descRoot(described));
    expect(publishedModulesWithoutShortDescription(lib)).toEqual([]);
  });

  // The 2026-07-22 regression: the gate walked only ancestor prefixes, so a leaf
  // module backed by a real .lean file was never checked. Three files shipped with
  // their description merged into the copyright `/- -/` header — which reads fine
  // in source but never registers as a module docstring — and the explorer showed
  // blank pages with the gate green.
  it("flags a leaf module whose docstring is missing", () => {
    const lib = loadLibrary(descRoot({ ...described, "Causalean.PO.ID.Leaf": "" }));
    expect(publishedModulesWithoutShortDescription(lib)).toEqual(["Causalean.PO.ID.Leaf"]);
  });

  it("still flags an intermediate namespace page with no description", () => {
    const lib = loadLibrary(descRoot({ ...described, "Causalean.PO.ID": "" }));
    expect(publishedModulesWithoutShortDescription(lib)).toEqual(["Causalean.PO.ID"]);
  });

  it("accepts a curated namespace_intros entry in place of a docstring", () => {
    const lib = loadLibrary(
      descRoot({ ...described, "Causalean.PO.ID": "" }, { ID: "The identification layer." }),
    );
    expect(publishedModulesWithoutShortDescription(lib)).toEqual([]);
  });
});
