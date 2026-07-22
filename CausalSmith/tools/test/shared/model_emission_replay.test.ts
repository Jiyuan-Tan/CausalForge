// Replay REAL recorded model emissions through the production parser.
//
// The offline soak harness covers state machinery, but it cannot reach the seam where
// the pipeline meets actual model output — a stub only ever emits what we thought to
// write. That seam produced one of the worst faults of 2026-07-19: both D0.5 referees
// PASSED, the cold general referee produced a complete verdict, and the run died parsing
// it because the critique contained `\(q_d(P)=r_n\)` — legal LaTeX, illegal JSON escape.
// A finished judgment lost to punctuation.
//
// So the fixtures here are captured emissions, not synthetic ones. Each real run is
// expensive; harvesting its output turns that one-time cost into permanent coverage.
//
// CAPTURE AT FAILURE TIME. These were nearly lost: after the escape bug was fixed the
// stage was re-run, and each log's final emission became a SUCCESSFUL one, overwriting
// the failing payload. The fixture below survives only because it had been copied aside
// while the failure was live. Anything interesting should be snapshotted when it happens,
// not reconstructed from logs afterwards.

import { describe, it, expect } from "vitest";
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { expectStringJsonOutput } from "../../src/shared/codex_json.js";

const dir = fileURLToPath(new URL("../fixtures/model_emissions", import.meta.url));
const read = (name: string): string => readFileSync(`${dir}/${name}`, "utf8");

describe("recorded model emissions — production parser", () => {
  it("recovers the D0.5.G verdict whose critique carried raw LaTeX", () => {
    const raw = read("d05g_latex_in_json.txt");
    // Non-vacuity: the payload must genuinely defeat a plain parse, or this proves nothing.
    // This is verbatim the error the live run died on:
    //   causalsmith: Bad escaped character in JSON at position 213
    expect(() => JSON.parse(raw), "fixture no longer reproduces the fault").toThrow(/Bad escaped character/);

    const out = expectStringJsonOutput(raw) as Record<string, unknown>;
    expect(out.tier).toBe("field");
    expect(out.flagship_potential).toBe(false);
    // The LaTeX must survive intact — a repair that mangled the prose would be its own bug.
    expect(String(out.critique)).toContain("\\(q_d(P)=r_n\\)");
    // The model mixed spellings in ONE string: `\(` raw, `\\le` correctly escaped.
    expect(String(out.critique)).toContain("\\le");
  });

  it("parses every captured emission", () => {
    const files = readdirSync(dir).filter((f) => f.endsWith(".txt"));
    expect(files.length, "no fixtures captured").toBeGreaterThan(0);
    for (const f of files) {
      expect(() => expectStringJsonOutput(read(f)), `failed to parse ${f}`).not.toThrow();
    }
  });

  it("leaves already-valid emissions byte-identical after parsing", () => {
    // The escape repair must be a no-op on well-formed output; a parser that silently
    // rewrites correct payloads would corrupt verdicts nobody was worried about.
    for (const f of readdirSync(dir).filter((n) => n.startsWith("clean_"))) {
      const raw = read(f);
      expect(expectStringJsonOutput(raw), `${f} changed under the parser`).toEqual(JSON.parse(raw));
    }
  });
});
