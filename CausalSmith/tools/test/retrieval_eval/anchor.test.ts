import { describe, it, expect } from "vitest";
import fs from "node:fs";
import path from "node:path";
import { loadAnchor } from "../../src/formalization/retrieval_eval/harness.js";

describe("loadAnchor", () => {
  it("parses jsonl into {item, cluster, gold}", () => {
    const rows = loadAnchor(path.join(__dirname, "fixtures", "anchor.sample.jsonl"));
    expect(rows).toHaveLength(2);
    expect(rows[0].item).toContain("propensity");
    expect(rows[0].cluster).toBe("stat");
    expect(Array.isArray(rows[0].gold)).toBe(true);
    expect(rows[0].gold[0]).toBe("Causalean.Stat.PolynomialTail.PolyTail");
  });
});

// Guard against silent anchor rot: the hand-labeled gold decls are the retrieval transfer
// gate, but decl renames/moves make them unhittable without any error (3/12 had gone stale).
// This asserts every gold name still exists in the current index. Skips only if the index
// artifact isn't present in this checkout (it is committed, so normally it always runs).
describe("anchor gold freshness", () => {
  const repoRoot = path.resolve(__dirname, "..", "..", "..", ".."); // tools/test/retrieval_eval -> Causalean pkg root
  const idxPath = path.join(repoRoot, "doc", "library_index.json");
  const anchorPath = path.resolve(__dirname, "..", "..", "..", "doc", "research", "retrieval_eval", "anchor.jsonl");

  it("every anchor.jsonl gold decl exists in the current library index (no stale renames)", () => {
    if (!fs.existsSync(idxPath) || !fs.existsSync(anchorPath)) return; // artifact not built here — skip
    const names = new Set(
      (JSON.parse(fs.readFileSync(idxPath, "utf8")).entries as { name: string }[]).map((e) => e.name),
    );
    const missing = loadAnchor(anchorPath).flatMap((r) => r.gold).filter((g) => !names.has(g));
    expect(missing).toEqual([]);
  });
});
