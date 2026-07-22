// Corpus regression for the TeX-JSON escape defense.
//
// Every escape-family gap so far (\forall, \texttt, \v...) was discovered by a
// LIVE pipeline incident. This test runs the full three-layer defense
// (normalizeRawModelJson → parse → repairLatexStringsDeep →
// assertNoDecodedControlChars) over every real discovery artifact in the repo
// — active runs and the bank — so the next gap surfaces as a red test offline
// instead of a mid-run halt. It also pins idempotence of the raw normalizer on
// real-world payloads (the unit suite pins it only on synthetic cases).
import { readFileSync, readdirSync, existsSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  assertNoDecodedControlChars,
  normalizeRawModelJson,
  repairLatexStringsDeep,
} from "../../src/discovery/core/latex_serialization.js";

const RESEARCH_ROOT = fileURLToPath(new URL("../../../doc/research", import.meta.url));

function walkJson(dir: string, out: string[]): void {
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    // .premigration holds pre-normalization snapshots kept verbatim on purpose.
    if (e.isDirectory()) {
      if (e.name !== ".premigration") walkJson(p, out);
    } else if (e.name.endsWith(".json")) {
      out.push(p);
    }
  }
}

function corpusFiles(): string[] {
  const files: string[] = [];
  for (const root of ["active", "_bank"]) {
    const dir = path.join(RESEARCH_ROOT, root);
    if (existsSync(dir)) walkJson(dir, files);
  }
  // Model-authored TeX-bearing artifacts live under each run's discovery/ dir;
  // state/review JSON elsewhere is pipeline-authored and out of scope here.
  return files.filter((f) => f.split(path.sep).includes("discovery"));
}

describe("escape-defense corpus regression (doc/research discovery artifacts)", () => {
  const files = corpusFiles();

  it("finds a non-trivial corpus (walker-rot canary)", () => {
    // The repo always carries banked runs; an empty list means the walker or
    // the layout drifted, not that there is nothing to check.
    expect(files.length).toBeGreaterThanOrEqual(20);
  });

  it("every artifact survives the full three-layer defense with no control chars", () => {
    const failures: string[] = [];
    for (const f of files) {
      const rel = path.relative(RESEARCH_ROOT, f);
      try {
        const raw = readFileSync(f, "utf8");
        const normalized = normalizeRawModelJson(raw);
        if (normalizeRawModelJson(normalized) !== normalized) {
          failures.push(`${rel} :: normalizeRawModelJson is not idempotent on this payload`);
          continue;
        }
        const value = JSON.parse(normalized) as unknown;
        repairLatexStringsDeep(value);
        assertNoDecodedControlChars(value, rel);
      } catch (e) {
        failures.push(`${rel} :: ${e instanceof Error ? e.message.slice(0, 200) : String(e)}`);
      }
    }
    expect(
      failures,
      `escape defense failed on real artifacts — a new TeX escape family or a ` +
        `corrupted persisted payload. Fix the normalizer/repair (or the artifact) ` +
        `before it halts a live run:\n${failures.join("\n")}`,
    ).toEqual([]);
  });
});
