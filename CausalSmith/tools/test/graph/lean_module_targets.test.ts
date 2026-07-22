import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { leanModuleTargets } from "../../src/formalization/proof_review_loop.js";

// The compile gate must build only THIS RUN's modules (+ their deps, which lake resolves), not the
// whole CausalSmith package. A bare `lake build` fails on an unrelated run's broken module — a
// spurious escalation — and contends with concurrent lake builds from other sessions.
let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(tmpdir(), "modtgt-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("leanModuleTargets: derive lake module names for the run's own Lean only", () => {
  it("maps the run's .lean files (incl. nested Helpers/) to dotted module names", async () => {
    const leanDir = path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research");
    await mkdir(path.join(leanDir, "Helpers"), { recursive: true });
    await mkdir(path.join(leanDir, "tmp"), { recursive: true });
    await writeFile(path.join(leanDir, "TApolar.lean"), "-- x\n", "utf8");
    await writeFile(path.join(leanDir, "Helpers", "ApolarQD.lean"), "-- x\n", "utf8");
    await writeFile(path.join(leanDir, "tmp", "Main.lean"), "-- disposable probe\n", "utf8");

    const mods = await leanModuleTargets(root, leanDir);
    expect(mods.sort()).toEqual([
      "CausalSmith.ExactID.EID_Foo_Research.Helpers.ApolarQD",
      "CausalSmith.ExactID.EID_Foo_Research.TApolar",
    ]);
    expect(mods.some((m) => m.endsWith(".tmp.Main"))).toBe(false);
  });

  it("does NOT pick up another run's modules sitting elsewhere in the package", async () => {
    const mine = path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research");
    const theirs = path.join(root, "CausalSmith", "Stat", "STAT_Other_Research");
    await mkdir(mine, { recursive: true });
    await mkdir(theirs, { recursive: true });
    await writeFile(path.join(mine, "T.lean"), "-- x\n", "utf8");
    await writeFile(path.join(theirs, "Broken.lean"), "-- x\n", "utf8");

    const mods = await leanModuleTargets(root, mine);
    expect(mods).toEqual(["CausalSmith.ExactID.EID_Foo_Research.T"]);
    expect(mods.some((m) => m.includes("STAT_Other_Research"))).toBe(false);
  });

  it("returns [] when there is nothing to build (caller must NOT treat that as a pass)", async () => {
    const empty = path.join(root, "CausalSmith", "ExactID", "Empty_Research");
    await mkdir(empty, { recursive: true });
    expect(await leanModuleTargets(root, empty)).toEqual([]);
  });
});
