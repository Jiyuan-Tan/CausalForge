import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { writeRunBarrel } from "../../src/formalization/proof_review_loop.js";

// A run's Lean modules are NOT reachable from the top-level `CausalSmith.lean` barrel, so the
// DEFAULT lake target skips them: `lake -d CausalSmith build` reports green while the run's oleans
// stay STALE, and a `#print axioms` against those lies. A per-run sibling barrel makes the whole run
// buildable/verifiable as ONE target — without wiring research runs into the top-level barrel, which
// would make one broken run break everyone's default build.
let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(tmpdir(), "barrel-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("writeRunBarrel: per-run aggregator so the run is one buildable target", () => {
  it("emits a sibling barrel importing every module in the run (incl. nested Helpers/)", async () => {
    const leanDir = path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research");
    await mkdir(path.join(leanDir, "Helpers"), { recursive: true });
    await writeFile(path.join(leanDir, "TApolar.lean"), "-- x\n", "utf8");
    await writeFile(path.join(leanDir, "Helpers", "ApolarQD.lean"), "-- x\n", "utf8");

    const out = await writeRunBarrel(root, leanDir);
    expect(out).toBe(path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research.lean"));

    const src = await readFile(out!, "utf8");
    expect(src).toContain("import CausalSmith.ExactID.EID_Foo_Research.TApolar");
    expect(src).toContain("import CausalSmith.ExactID.EID_Foo_Research.Helpers.ApolarQD");
    // Lean requires `import` at the very top: a `/-! -/` module docstring is a DECLARATION, so it
    // must come AFTER the imports. (A first cut emitted it before them and Lean rejected the file
    // with "invalid 'import' command, it must be used in the beginning of the file".)
    const firstImport = src.indexOf("\nimport ");
    const moduleDoc = src.indexOf("/-!");
    expect(firstImport).toBeGreaterThan(-1);
    expect(moduleDoc).toBeGreaterThan(firstImport);
    // deterministic: sorted, so re-running produces no spurious diff
    expect(src).toBe(await readFile((await writeRunBarrel(root, leanDir))!, "utf8"));
  });

  it("never imports the barrel into itself", async () => {
    const leanDir = path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research");
    await mkdir(leanDir, { recursive: true });
    await writeFile(path.join(leanDir, "T.lean"), "-- x\n", "utf8");
    const out = await writeRunBarrel(root, leanDir);
    const src = await readFile(out!, "utf8");
    expect(src).not.toContain("import CausalSmith.ExactID.EID_Foo_Research\n");
  });

  it("returns null when there is nothing to aggregate", async () => {
    const empty = path.join(root, "CausalSmith", "ExactID", "Empty_Research");
    await mkdir(empty, { recursive: true });
    expect(await writeRunBarrel(root, empty)).toBeNull();
  });
});
