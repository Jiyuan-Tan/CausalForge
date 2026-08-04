// Phase 3 (TeX-out-of-JSON) round-trip tests: companion slicing, ref
// resolution, fail-loud on missing/duplicate refs, byte-identical TeX through
// the production ingest, and the stale-sweep archiving of companion bytes.

import { describe, it, expect } from "vitest";
import { mkdtemp, mkdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  companionPathFor,
  sliceTexCompanion,
  resolveTexRefs,
  isTexRef,
} from "../../src/discovery/solve/tex_companion.js";
import { readSolveUnitOutput } from "../../src/discovery/solve/dispatch.js";
import { proofBytesInRoundFile } from "../../src/discovery/proof_archive.js";
import { assertSealableLatexPayload } from "../../src/discovery/core/latex_serialization.js";

const COMPANION = [
  "%%% FIELD thm:main.proof",
  "By construction, \\(\\theta \\le 1\\).",
  "Multi-line with a blank:",
  "",
  "\\[ x^2 \\]",
  "%%% FIELD lem:helper.statement",
  "For every \\(n\\), the bound holds with backslashes \\alpha\\beta and \\t literal.",
  "",
].join("\n");

describe("sliceTexCompanion", () => {
  it("slices blocks byte-identically (delimiter newline excluded, inner blanks kept)", () => {
    const blocks = sliceTexCompanion(COMPANION, "t.tex");
    expect([...blocks.keys()]).toEqual(["thm:main.proof", "lem:helper.statement"]);
    expect(blocks.get("thm:main.proof")).toBe(
      "By construction, \\(\\theta \\le 1\\).\nMulti-line with a blank:\n\n\\[ x^2 \\]",
    );
    expect(blocks.get("lem:helper.statement")).toBe(
      "For every \\(n\\), the bound holds with backslashes \\alpha\\beta and \\t literal.",
    );
  });

  it("fails loud on a duplicate ref", () => {
    const dup = "%%% FIELD a\nx\n%%% FIELD a\ny\n";
    expect(() => sliceTexCompanion(dup, "t.tex")).toThrow(/duplicate block ref 'a'/);
  });

  it("fails loud on content before the first header", () => {
    expect(() => sliceTexCompanion("stray\n%%% FIELD a\nx\n", "t.tex")).toThrow(/before the first/);
  });

  it("accepts CRLF line endings, normalized to LF (audit P23F3)", () => {
    const blocks = sliceTexCompanion("%%% FIELD a\r\nline one\r\nline two\r\n", "t.tex");
    expect(blocks.get("a")).toBe("line one\nline two");
  });

  it("normalizes horizontal tabs to spaces so the JSON-channel repair heuristic can never fire (audit P23F4)", () => {
    const blocks = sliceTexCompanion("%%% FIELD a\n\twhere the tab preceded a letter\n", "t.tex");
    expect(blocks.get("a")).toBe("  where the tab preceded a letter");
    expect(blocks.get("a")).not.toContain("\t");
  });

  it("defuses the newline-before-`e`/`otin` repair heuristic with a TeX-neutral leading space (audit R3P23F1)", async () => {
    const content = "Let e denote the error.\ne \\in \\mathcal E.\notin \\mathcal E either\neconomics stays untouched\n";
    const blocks = sliceTexCompanion(`%%% FIELD a\n${content}`, "t.tex");
    const sliced = blocks.get("a")!;
    expect(sliced).toBe(
      "Let e denote the error.\n e \\in \\mathcal E.\n otin \\mathcal E either\neconomics stays untouched",
    );
    // The point of the defusal: the writer-side core repair is now a no-op over
    // companion content — the corrupting `\ne`/`\notin` inference cannot fire.
    const { repairCoreLatexSerialization } = await import("../../src/discovery/core/latex_serialization.js");
    const core = {
      statements: [{ id: "thm:x", kind: "theorem", statement: "S", status: "proved", depends_on: [], proof_tex: sliced }],
      assumptions: [], definitions: [], symbols: [], bibliography: [], target_estimand: "tau",
    } as never;
    repairCoreLatexSerialization(core);
    expect((core as { statements: Array<{ proof_tex: string }> }).statements[0].proof_tex).toBe(sliced);
    expect((core as { statements: Array<{ proof_tex: string }> }).statements[0].proof_tex).not.toContain("\\ne");
  });
});

describe("resolveTexRefs", () => {
  it("resolves refs in place and reports used refs", () => {
    const body = {
      proofs: [{ id: "thm:main", proof_tex: { tex_ref: "thm:main.proof" } }],
      added_lemmas: [{ id: "lem:helper", statement: { tex_ref: "lem:helper.statement" }, proof_tex: "inline stays" }],
    };
    const used = resolveTexRefs(body, sliceTexCompanion(COMPANION, "t.tex"), "t.tex");
    expect(body.proofs[0].proof_tex).toContain("\\(\\theta \\le 1\\)");
    expect(body.added_lemmas[0].statement).toContain("\\alpha\\beta");
    expect(body.added_lemmas[0].proof_tex).toBe("inline stays");
    expect([...used].sort()).toEqual(["lem:helper.statement", "thm:main.proof"]);
  });

  it("fails loud on a ref with no block — including when no companion exists at all", () => {
    expect(() => resolveTexRefs({ a: { tex_ref: "missing" } }, new Map(), "t.tex")).toThrow(
      /references tex_ref 'missing'.*no companion file/,
    );
  });

  it("only exact single-key {tex_ref} objects are references", () => {
    expect(isTexRef({ tex_ref: "a" })).toBe(true);
    expect(isTexRef({ tex_ref: "a", extra: 1 })).toBe(false);
    expect(isTexRef("tex_ref")).toBe(false);
  });
});

describe("production ingest round-trip (readSolveUnitOutput)", () => {
  it("ignores unmatched braces inside TeX literal/code regions", () => {
    expect(() => assertSealableLatexPayload({
      inline: String.raw`Use \verb|{| and \lstinline|}|.`,
      environment: "\\begin{verbatim}\n{ literal\n\\end{verbatim}",
    }, "literal-regression")).not.toThrow();
  });

  it("ignores math delimiters and environment syntax inside literals and comments", () => {
    expect(() => assertSealableLatexPayload({
      inline: String.raw`Use \verb|\(|.`,
      bracketDelimiter: String.raw`Use \verb[abc[.`,
      environment: "\\begin{verbatim}\n\\begin{foo}\n\\end{verbatim}",
      comment: "% \\begin{foo}\nordinary prose",
    }, "literal-structure-regression")).not.toThrow();
  });

  it("does not let a commented literal-environment opener hide later malformed TeX", () => {
    expect(() => assertSealableLatexPayload(
      `% \\begin{verbatim}\n${String.raw`Real \(\operatorname{broken\).`}`,
      "comment-before-literal-regression",
    )).toThrow(/unbalanced TeX grouping braces/);
  });

  it("rejects recognized inline literal commands without a complete delimiter pair", () => {
    for (const malformed of [
      String.raw`Use \verb|abc.`,
      String.raw`Use \lstinline!abc.`,
      String.raw`Use \mintinline{tex}|abc.`,
      "Use \\verb|abc\nnext | done.",
      "Use \\lstinline!abc\nnext ! done.",
      "Use \\mintinline{tex}|abc\nnext | done.",
    ]) {
      expect(() => assertSealableLatexPayload(malformed, "unterminated-inline-literal"))
        .toThrow(/unterminated or malformed inline TeX literal/);
    }
  });

  it("byte-identical TeX flows through ingest; the JSON channel never sees the bytes", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "texcomp-"));
    const outPath = path.join(tmp, "solve_thm_main.json");
    // Deliberately UNDER-ESCAPED TeX that would corrupt through the JSON channel:
    // raw \theta, \table-like sequences survive because the companion is never
    // JSON-decoded.
    const rawTex = "Assume \\theta and \\tau; then\n\\[ \\theta \\le \\tau. \\]";
    await mkdir(path.dirname(companionPathFor(outPath)), { recursive: true });
    await writeFile(companionPathFor(outPath), `%%% FIELD p1\n${rawTex}\n`, "utf8");
    await writeFile(outPath, JSON.stringify({
      proofs: [{ id: "thm:main", proof_tex: { tex_ref: "p1" } }],
      added_lemmas: [],
    }), "utf8");
    const output = await readSolveUnitOutput(outPath, "unit");
    expect(output.proofs[0].proof_tex).toBe(rawTex);
  });

  it("companion files live under discovery/solve_tex/", () => {
    expect(companionPathFor("/x/discovery/solve_thm_a.json")).toBe("/x/discovery/solve_tex/solve_thm_a.tex");
  });

  it("a JSON ref without its block fails the unit loud (before any store is touched)", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "texcomp-"));
    const outPath = path.join(tmp, "solve_thm_main.json");
    await writeFile(outPath, JSON.stringify({
      proofs: [{ id: "thm:main", proof_tex: { tex_ref: "nowhere" } }],
      added_lemmas: [],
    }), "utf8");
    await expect(readSolveUnitOutput(outPath, "unit")).rejects.toThrow(/tex_ref 'nowhere'/);
  });

  it("an UNUSED companion block fails the unit loud — the truncation guard (audit P23F2)", async () => {
    // A '%%% FIELD note'-lookalike TeX comment inside a proof mis-slices the
    // block; the stranded remainder becomes an extra block no ref cites, which
    // must fail loud instead of silently truncating the proof.
    const tmp = await mkdtemp(path.join(os.tmpdir(), "texcomp-"));
    const outPath = path.join(tmp, "solve_thm_main.json");
    await mkdir(path.dirname(companionPathFor(outPath)), { recursive: true });
    await writeFile(
      companionPathFor(outPath),
      "%%% FIELD p1\nthe first half of the proof\n%%% FIELD note\nthe silently stranded second half\n",
      "utf8",
    );
    await writeFile(outPath, JSON.stringify({
      proofs: [{ id: "thm:main", proof_tex: { tex_ref: "p1" } }],
      added_lemmas: [],
    }), "utf8");
    await expect(readSolveUnitOutput(outPath, "unit")).rejects.toThrow(/no tex_ref cites: note/);
  });

  it("rejects malformed TeX inside an otherwise schema-valid structured proposal", async () => {
    const tmp = await mkdtemp(path.join(os.tmpdir(), "texcomp-"));
    const outPath = path.join(tmp, "solve_thm_main.json");
    await writeFile(outPath, JSON.stringify({
      proofs: [],
      added_lemmas: [],
      proposed_core_edits: [{
        kind: "symbol-add",
        name: "M",
        proposed: {
          name: "M",
          type: "model",
          def: String.raw`The family \(\operatorname{binary\).`,
        },
        reason: "describe an accepted witness",
        direction: "correct",
      }],
    }), "utf8");
    await expect(readSolveUnitOutput(outPath, "unit"))
      .rejects.toThrow(/unbalanced TeX grouping braces/);
  });
});

describe("stale-sweep archiving with a companion", () => {
  it("extracts real proof bytes through the companion", () => {
    const raw = JSON.stringify({ proofs: [{ id: "thm:main", proof_tex: { tex_ref: "p1" } }] });
    const companion = "%%% FIELD p1\nThe paid-for argument.\n";
    const bytes = proofBytesInRoundFile("solve_x.json", raw, "round-cleared", companion);
    expect(bytes).toContainEqual({ nodeId: "thm:main", proofTex: "The paid-for argument.", reason: "round-cleared" });
  });

  it("archives an UNUSED block as a blob — the stranded-truncation bytes survive the sweep (audit R2P23F2)", () => {
    const raw = JSON.stringify({ proofs: [{ id: "thm:main", proof_tex: { tex_ref: "p1" } }] });
    const companion = "%%% FIELD p1\nfirst half\n%%% FIELD note\nthe stranded second half\n";
    const bytes = proofBytesInRoundFile("solve_x.json", raw, "round-cleared", companion);
    expect(bytes).toContainEqual({ nodeId: "thm:main", proofTex: "first half", reason: "round-cleared" });
    expect(bytes).toContainEqual({
      nodeId: "file:solve_x.json.companion:note",
      proofTex: "the stranded second half",
      reason: "round-cleared-unused-block",
    });
  });

  it("archives the whole companion as a blob when resolution fails", () => {
    const raw = JSON.stringify({ proofs: [{ id: "thm:main", proof_tex: { tex_ref: "missing" } }] });
    const companion = "%%% FIELD other\nBytes that must not vanish.\n";
    const bytes = proofBytesInRoundFile("solve_x.json", raw, "round-cleared", companion);
    expect(bytes.some((b) => b.nodeId === "file:solve_x.json.companion" && b.proofTex === companion)).toBe(true);
  });
});
