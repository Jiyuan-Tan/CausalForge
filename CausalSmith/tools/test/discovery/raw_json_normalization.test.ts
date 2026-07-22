import { describe, expect, it } from "vitest";
import { mkdtemp, readFile as readFsFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairSerializedLatex,
} from "../../src/discovery/core/latex_serialization.js";
import {
  parseRepairedModelJson,
  readRepairedModelJson,
  readTypedCore,
} from "../../src/discovery/core/core_io.js";

/** Parse raw model-authored JSON bytes through the pre-parse normalizer. */
function parseNormalized(raw: string): unknown {
  return JSON.parse(normalizeRawModelJson(raw));
}

describe("normalizeRawModelJson (pre-parse raw-byte repair)", () => {
  it("restores under-escaped b/f/r/t-family TeX commands generically", () => {
    const raw = String.raw`{"s":"\theta + \text{id} \to \beta \begin{aligned} \frac{1}{2} \forall \rho \rightarrow"}`;
    expect(parseNormalized(raw)).toEqual({
      s: String.raw`\theta + \text{id} \to \beta \begin{aligned} \frac{1}{2} \forall \rho \rightarrow`,
    });
  });

  it("leaves correctly escaped TeX commands untouched", () => {
    const raw = String.raw`{"s":"\\theta + \\text{id}","rows":"a \\\\ b"}`;
    expect(normalizeRawModelJson(raw)).toBe(raw);
  });

  it("preserves genuine newline escapes, including before prose words", () => {
    const raw = String.raw`{"s":"line1\nline2\neither way"}`;
    expect(parseNormalized(raw)).toEqual({ s: "line1\nline2\neither way" });
  });

  it("restores dictionary n-family TeX commands at word boundaries", () => {
    const raw = String.raw`{"s":"a \neq b, x \notin S, \nabla f, p \ne q"}`;
    expect(parseNormalized(raw)).toEqual({
      s: String.raw`a \neq b, x \notin S, \nabla f, p \ne q`,
    });
  });

  it("rescues invalid JSON escapes (\\alpha, \\geq, \\{, \\[) instead of throwing", () => {
    const raw = String.raw`{"s":"\alpha \geq 0, \{x\}, \[y\]"}`;
    expect(() => JSON.parse(raw)).toThrow();
    expect(parseNormalized(raw)).toEqual({ s: String.raw`\alpha \geq 0, \{x\}, \[y\]` });
  });

  it("preserves valid \\uXXXX escapes but rescues \\u TeX-like remainders", () => {
    const raw = String.raw`{"a":"café","b":"\underline{x}"}`;
    expect(parseNormalized(raw)).toEqual({ a: "café", b: String.raw`\underline{x}` });
  });

  it("only rewrites inside string literals and tracks escaped quotes", () => {
    const raw = String.raw`{"s":"he said \"hi\" \theta","n":1}` + "\n\t";
    expect(parseNormalized(raw)).toEqual({ s: String.raw`he said "hi" \theta`, n: 1 });
    expect(normalizeRawModelJson(raw).endsWith("\n\t")).toBe(true);
  });

  it("is idempotent", () => {
    const raw = String.raw`{"s":"\theta \neq \alpha \n \\already"}`;
    const once = normalizeRawModelJson(raw);
    expect(normalizeRawModelJson(once)).toBe(once);
  });

  it("recovers v-family commands re-serialized as Unicode vertical tabs", () => {
    const parsed = parseNormalized(String.raw`{"s":"\u000barnothing and \u000barepsilon"}`) as { s: string };
    parsed.s = repairSerializedLatex(parsed.s);
    expect(parsed.s).toBe(String.raw`\varnothing and \varepsilon`);
    expect(() => assertNoDecodedControlChars(parsed, "solve unit")).not.toThrow();
  });

  it("recovers b/f/r/t-family commands re-serialized as Unicode control escapes", () => {
    const parsed = parseNormalized(
      String.raw`{"s":"\u0008eta \u000crac{1}{2} \u000dho \u0009heta \u0009o x"}`,
    ) as { s: string };
    parsed.s = repairSerializedLatex(parsed.s);
    expect(parsed.s).toBe(String.raw`\beta \frac{1}{2} \rho \theta \to x`);
    expect(() => assertNoDecodedControlChars(parsed, "solve unit")).not.toThrow();
  });

  it("restores an under-escaped \\not and leaves prose-word lookalikes as line breaks", () => {
    // `\not` is a real n-family command (audit finding: it was missing) ...
    expect(parseNormalized(String.raw`{"s":"x \not = y"}`)).toEqual({ s: String.raw`x \not = y` });
    // ... while suffixes that are common prose words must NOT be inferred from a
    // line break: a legitimate newline before "exists"/"less"/"parallel" stays a newline.
    expect(parseNormalized(String.raw`{"s":"there\nexists a witness"}`)).toEqual({
      s: "there\nexists a witness",
    });
    expect(parseNormalized(String.raw`{"s":"far\nless restrictive"}`)).toEqual({
      s: "far\nless restrictive",
    });
    expect(parseNormalized(String.raw`{"s":"are\nparallel to"}`)).toEqual({
      s: "are\nparallel to",
    });
  });

  it("never rewrites a newline before the variables u or e (corpus-verified patterns)", () => {
    // Real accepted-paper content: display math starting with the margin variable
    // u (stat_policy_regret) and the exponential e (exp_interference). Inferring
    // \nu / \ne here would silently change published math, so `u` is not in the
    // dictionary at all and `e` keeps only the legacy tight guard.
    expect(parseNormalized(String.raw`{"s":"Then\n\\[\nu^\\alpha v^{1/\\gamma}\n\\]"}`)).toEqual({
      s: "Then\n\\[\nu^\\alpha v^{1/\\gamma}\n\\]",
    });
    expect(parseNormalized(String.raw`{"s":"bounded by\n\\[\ne^{s\\lambda n}\n\\]"}`)).toEqual({
      s: "bounded by\n\\[\ne^{s\\lambda n}\n\\]",
    });
    // The legacy `\ne` guard still restores the genuine relation spelling.
    expect(parseNormalized(String.raw`{"s":"p \ne q"}`)).toEqual({ s: String.raw`p \ne q` });
  });

  it("restores an \\asymp lost to a C-style BEL interpretation", () => {
    // Corpus instance (stat_ate_overlap_decay_v1): a boundary interpreted the
    // non-JSON `\a` escape as BEL and re-serialized it as the valid escape \\u0007.
    const parsed = parseNormalized(String.raw`{"s":"U_n \u0007symp R_n"}`) as { s: string };
    parsed.s = repairSerializedLatex(parsed.s);
    expect(parsed.s).toBe(String.raw`U_n \asymp R_n`);
  });

  it("still fails closed on control characters not followed by a letter", () => {
    const parsed = parseNormalized(String.raw`{"s":"col1\u0009 col2"}`) as { s: string };
    parsed.s = repairSerializedLatex(parsed.s);
    expect(() => assertNoDecodedControlChars(parsed, "solve unit")).toThrow(/U\+0009/);
  });
});

describe("readTypedCore (canonical core/proto loader)", () => {
  it("repairs a legacy artifact's pre-encoded control escape and fails loudly on unrecoverable ones", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "coreio-"));
    try {
      const golden = await readFsFile(
        new URL("../fixtures/stat_ate_overlap_decay_proto_core.json", import.meta.url),
        "utf8",
      );
      // A pre-defense artifact where `\theta` was decoded to a tab and persisted:
      // on disk that is the VALID escape `\t` + "heta" — pre-parse normalization
      // recovers it, so the loader returns the intended TeX.
      const core = JSON.parse(golden) as { target_estimand: string };
      const legacy = golden.replace(
        JSON.stringify(core.target_estimand),
        JSON.stringify(core.target_estimand).replace(/"$/, String.raw` for \theta"`),
      );
      const legacyPath = path.join(dir, "proto_core.json");
      await writeFile(legacyPath, legacy, "utf8");
      const loaded = await readTypedCore(legacyPath);
      expect(loaded.target_estimand).toBe(`${core.target_estimand} for ` + String.raw`\theta`);

      // An unrecoverable control character (tab before a non-letter) throws with
      // the artifact path instead of flowing silently into live state.
      const corruptPath = path.join(dir, "corrupt_core.json");
      await writeFile(
        corruptPath,
        golden.replace(
          JSON.stringify(core.target_estimand),
          JSON.stringify(core.target_estimand).replace(/"$/, String.raw` col\t 1"`),
        ),
        "utf8",
      );
      await expect(readTypedCore(corruptPath)).rejects.toThrow(/corrupt_core\.json.*U\+0009/s);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("parseRepairedModelJson / readRepairedModelJson (schema-free three-layer loaders)", () => {
  it("parses under-escaped TeX, repairs valid-escape corruption, and keeps ALL keys", () => {
    // `\alpha` is an INVALID JSON escape (would throw in bare JSON.parse);
    // `\texttt` is a VALID escape (tab) that bare JSON.parse silently corrupts.
    const raw = String.raw`{"proof_tex":"\alpha \texttt{id}","custom_nonschema_key":1}`;
    const v = parseRepairedModelJson(raw, "unit test payload") as Record<string, unknown>;
    expect(v.proof_tex).toBe(String.raw`\alpha \texttt{id}`);
    // Unlike readTypedCore, no CoreSchema strip: unknown keys survive.
    expect(v.custom_nonschema_key).toBe(1);
  });

  it("fails loudly (naming the source) on unrecoverable control characters", () => {
    const raw = String.raw`{"s":"col\t 1"}`;
    expect(() => parseRepairedModelJson(raw, "handoff blob")).toThrow(/handoff blob.*U\+0009/s);
  });

  it("readRepairedModelJson applies the same defense to a file and names its path", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "coreio-free-"));
    try {
      const okPath = path.join(dir, "unit.json");
      await writeFile(okPath, String.raw`{"seeds":["\forall x"],"extra":{"note":"\texttt{y}"}}`, "utf8");
      const v = (await readRepairedModelJson(okPath)) as { seeds: string[]; extra: { note: string } };
      expect(v.seeds[0]).toBe(String.raw`\forall x`);
      expect(v.extra.note).toBe(String.raw`\texttt{y}`);

      const badPath = path.join(dir, "bad.json");
      await writeFile(badPath, String.raw`{"s":"col\t 1"}`, "utf8");
      await expect(readRepairedModelJson(badPath)).rejects.toThrow(/bad\.json.*U\+0009/s);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("assertNoDecodedControlChars (post-parse backstop)", () => {
  it("accepts strings containing newlines", () => {
    expect(() =>
      assertNoDecodedControlChars({ a: "line1\nline2", b: [{ c: "ok" }] }, "unit x"),
    ).not.toThrow();
  });

  it("rejects a decoded tab, naming the source and JSON path", () => {
    const value = { statements: [{ id: "thm:a", statement: "bad \t here" }] };
    expect(() => assertNoDecodedControlChars(value, "unit thm:a")).toThrow(
      /unit thm:a.*statements\[0\]\.statement.*U\+0009/s,
    );
  });

  it("rejects backspace, form feed, and carriage return", () => {
    for (const ch of ["\b", "\f", "\r"]) {
      expect(() => assertNoDecodedControlChars({ s: `x${ch}y` }, "src")).toThrow(/src/);
    }
  });
});
