// The model-output JSON escape defense, tested at the FUNNEL rather than per call site.
//
// Recurrence history: a model writes ordinary inline LaTeX into a JSON prose field
// (`\(d/\epsilon\)`), JSON's escape grammar rejects the payload, and a completed stage
// dies at the finish line. Fixed at least three times — 2026-07-19 (`expectStringJsonOutput`),
// 2026-07-21/22 (`normalizeRawModelJson` at the D-stage boundaries), 2026-07-25 (the D0.5.G
// stdout referee, "Bad escaped character in JSON at position 1273") — each time by patching
// the ONE call site that had just failed.
//
// The reason it kept coming back is structural: the pipeline has several independent
// model-output parsers, and the repair had been added to some of them. `extractJsonObject`
// — the funnel behind `parseAgentJson`, every D-stage stdout boundary and every F-stage
// review/intervention payload — had none, so the class resurfaced at whichever boundary
// next quoted math. These tests pin the funnel-level fix and, in the last block, guard the
// INVENTORY so a newly added boundary cannot silently reopen it.

import { describe, it, expect } from "vitest";
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { extractJsonObject } from "../../src/judgment.js";
import { parseAgentJson } from "../../src/framework/agent_dispatch.js";
import { parseJsonWithEscapeRepair, expectStringJsonOutput } from "../../src/shared/codex_json.js";

const srcDir = fileURLToPath(new URL("../../src", import.meta.url));
const binDir = fileURLToPath(new URL("../../bin", import.meta.url));

describe("extractJsonObject — invalid LaTeX escapes no longer lose the payload", () => {
  it("recovers the round-60 shape that killed a completed D0.5.G verdict", () => {
    const raw = String.raw`{"tier":"subfield","salvageable":true,"critique":"The pointwise local \(d/\epsilon\) lower bound remains narrow.","flagship_potential":false}`;
    // Non-vacuity: this must genuinely defeat a plain parse, or the test proves nothing.
    expect(() => JSON.parse(raw), "fixture no longer reproduces the fault").toThrow();

    const out = extractJsonObject(raw) as Record<string, unknown>;
    expect(out.tier).toBe("subfield");
    // The LaTeX must survive intact — a repair that mangled the prose would be its own bug.
    expect(String(out.critique)).toContain(String.raw`\(d/\epsilon\)`);
  });

  it("covers parseAgentJson, the funnel every D-stage stdout boundary uses", () => {
    const raw = String.raw`Narration first.\n{"status":"completed","note":"rate \(n^{-1/3}\) is attained"}`;
    const parsed = parseAgentJson(raw);
    expect(parsed.parseError).toBeUndefined();
    expect(String(parsed.json?.note)).toContain(String.raw`\(n^{-1/3}\)`);
  });

  it("handles the mixed-spelling case models actually emit (raw `\\(` beside escaped `\\\\le`)", () => {
    const raw = String.raw`{"critique":"Since \(x\) satisfies \\le 1, the bound \sum_i w_i holds."}`;
    const out = extractJsonObject(raw) as Record<string, unknown>;
    expect(String(out.critique)).toContain(String.raw`\(x\)`);
    expect(String(out.critique)).toContain(String.raw`\le 1`);
    expect(String(out.critique)).toContain(String.raw`\sum_i`);
  });

  it("repairs the BALANCED slice, not just the legacy first-{/last-} fallback", () => {
    // Isolates the balanced-object scan. The legacy fallback slices first `{` to last `}`,
    // so trailing prose braces make it produce a slice that is not the payload; only
    // repairing the balanced candidate itself recovers the verdict here.
    const raw =
      String.raw`{"verdict":"PASS","note":"the \(d/\epsilon\) term dominates"}` +
      "\nFollow-up: consider the set {x | P x} next round.";
    const out = extractJsonObject(raw) as Record<string, unknown>;
    expect(out.verdict).toBe("PASS");
    expect(String(out.note)).toContain(String.raw`\(d/\epsilon\)`);
  });

  it("still finds the real object when prose braces precede it (no regression)", () => {
    const text = 'Considering the set {x | P x} we conclude:\n{"route":"stage_0","reason":"r"}';
    expect(extractJsonObject(text)).toEqual({ route: "stage_0", reason: "r" });
  });

  it("still throws on genuinely malformed output, reporting the ORIGINAL parse error", () => {
    // Unrepairable by escapes: a structural fault must not be masked or relabelled.
    expect(() => extractJsonObject('{"a": 1, "b": }')).toThrow();
  });
});

describe("the repair is a strict extension of JSON.parse", () => {
  // The safety argument for wiring this into a funnel shared with F-stage payloads
  // (which embed Lean source) is that the repair fires ONLY on bytes JSON.parse already
  // rejects. So on anything that parsed before, it must be a bit-for-bit no-op.
  it("is identical to JSON.parse on already-valid payloads", () => {
    const valid = [
      String.raw`{"a":"plain"}`,
      String.raw`{"tex":"\\alpha + \\beta"}`,
      String.raw`{"multi":"line one\nline two\ttabbed"}`,
      String.raw`{"unicode":"\u00e9 caf\u00e9"}`,
      String.raw`{"path":"C:\\Users\\x"}`,
      String.raw`{"nested":{"arr":[1,2,{"k":"\\frac{1}{2}"}]}}`,
      String.raw`{"quoted":"he said \"hi\""}`,
      String.raw`{"solidus":"a\/b"}`,
    ];
    for (const v of valid) {
      expect(parseJsonWithEscapeRepair(v), `changed under repair: ${v}`).toEqual(JSON.parse(v));
      expect(extractJsonObject(v), `changed under funnel: ${v}`).toEqual(JSON.parse(v));
    }
  });

  it("leaves an F-stage Lean payload untouched", () => {
    // F-stage outputs embed Lean source; the funnel is shared with them, so a repair
    // that reinterpreted this content would be far worse than the parse error it fixes.
    const lean = {
      decl: "theorem foo (x : ℝ) : x ≤ x := le_refl x",
      body: 'by\n  simp [Set.mem_setOf_eq]\n  exact ⟨h₁, h₂⟩',
      doc: "/-- The bound \\(x \\le x\\). -/",
    };
    const serialized = JSON.stringify(lean);
    expect(parseJsonWithEscapeRepair(serialized)).toEqual(lean);
    expect(extractJsonObject(serialized)).toEqual(lean);
  });

  it("is idempotent on a repaired payload", () => {
    const raw = String.raw`{"critique":"bound \(d/\epsilon\)"}`;
    const once = extractJsonObject(raw);
    expect(extractJsonObject(JSON.stringify(once))).toEqual(once);
  });
});

describe("every model-output parser carries the escape defense", () => {
  // The historical defect was an INVENTORY defect: several parsers, the repair present in
  // some. Assert the property directly so adding a parser without it is a red test.
  it("all model-output funnels survive the same inline-math payload", () => {
    const raw = String.raw`{"verdict":"PASS","note":"the \(d/\epsilon\) term"}`;
    const funnels: Array<[string, (s: string) => unknown]> = [
      ["extractJsonObject", extractJsonObject],
      ["parseJsonWithEscapeRepair", parseJsonWithEscapeRepair],
      ["expectStringJsonOutput", expectStringJsonOutput],
      ["parseAgentJson", (s) => parseAgentJson(s).json],
    ];
    for (const [name, parse] of funnels) {
      const out = parse(raw) as Record<string, unknown>;
      expect(out?.verdict, `${name} lost the payload`).toBe("PASS");
    }
  });
});

describe("source guard — no bare JSON.parse at a model-output boundary", () => {
  // A call site is only safe if the escape defense is visible ON that expression.
  const DEFENSES = [
    "parseJsonWithEscapeRepair",
    "normalizeRawModelJson",
    "parseRepairedModelJson",
    "readRepairedModelJson",
    "readTypedCore",
    "repairInvalidStringEscapes",
    "extractJsonObject",
    "expectStringJsonOutput",
    "parseJsonLoose",
  ];
  // Expressions that identify a MODEL-authored source: agent stdout, or a file an agent
  // wrote itself. Pipeline-written state (state.json, caches, stores) is deliberately
  // excluded — those are re-serialized by us and fail loud by design.
  const MODEL_SOURCES = [
    /\bstdout\b/,
    /\bout\.stdout\b/,
    /paths\.plan\b/,
    /\bplanPath\b/,
    /\bverdictFile\b/,
    // No leading \b: these appear as suffixes of longer identifiers (`absoluteSolvePath`).
    /SolvePath\b/,
    /solveJsonPath\b/,
  ];

  const walk = (dir: string): string[] =>
    readdirSync(dir).flatMap((name) => {
      const p = join(dir, name);
      return statSync(p).isDirectory() ? walk(p) : p.endsWith(".ts") ? [p] : [];
    });

  it("has no unguarded JSON.parse over agent stdout or an agent-written plan", () => {
    const offenders: string[] = [];
    for (const file of [...walk(srcDir), ...walk(binDir)]) {
      readFileSync(file, "utf8").split("\n").forEach((line, i) => {
        if (!line.includes("JSON.parse(")) return;
        if (!MODEL_SOURCES.some((re) => re.test(line))) return;
        if (DEFENSES.some((d) => line.includes(d))) return;
        const rel = file.startsWith(srcDir) ? `src/${file.slice(srcDir.length + 1)}` : `bin/${file.slice(binDir.length + 1)}`;
        offenders.push(`${rel}:${i + 1}: ${line.trim()}`);
      });
    }
    expect(
      offenders,
      "Model-authored JSON must go through the escape defense — a raw LaTeX backslash " +
        "otherwise kills the whole payload. Wrap the read in parseJsonWithEscapeRepair (any " +
        "model output) or normalizeRawModelJson (known-TeX D-stage boundaries).",
    ).toEqual([]);
  });
});
