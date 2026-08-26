import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { sweepDeadHelpers } from "../src/formalization/dead_helpers.js";

/** F4 dead-helper sweep: flags public decls nothing consumes; spares graph-node realizations,
 *  attributed/instance decls, `-- keep:` justified helpers, tmp/ probes, and commented mentions. */
describe("sweepDeadHelpers", () => {
  it("flags the dead helper and spares consumed, exempt, attributed, and kept decls", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-"));
    try {
      await mkdir(path.join(dir, "Helpers"));
      await mkdir(path.join(dir, "tmp"));
      await writeFile(
        path.join(dir, "Helpers", "Envelope.lean"),
        `/-- An abandoned-route helper: nothing references it. -/
lemma coeff_envelope : True := by trivial

lemma consumed_bound : True := by trivial

-- keep: substrate for the follow-on one-arm run (2026-08-25)
lemma kept_substrate : True := by trivial

@[simp] lemma simp_fact : True := by trivial

instance : Inhabited Unit := ⟨()⟩

private lemma local_step : True := by trivial
`,
      );
      await writeFile(
        path.join(dir, "Main.lean"),
        `-- coeff_envelope is only mentioned in this comment, which is not a use.
theorem headline : True := by
  have h := consumed_bound
  trivial
`,
      );
      await writeFile(
        path.join(dir, "tmp", "Probe.lean"),
        "lemma disposable_probe : True := by trivial\n",
      );

      const dead = await sweepDeadHelpers(
        dir,
        new Set(["CausalSmith.Stat.X_Research.headline"]), // graph node ⇒ headline exempt by short name
      );
      expect(dead).toEqual([
        { decl: "coeff_envelope", file: "Helpers/Envelope.lean", line: 2 },
      ]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("binds a keep marker to exactly the NEXT decl, across a long docstring, leaking to none after", async () => {
    // Audited 2026-08-25: a fixed 3-line lookback let one marker exempt up to three following
    // decls, and failed to exempt a decl behind its own multi-line docstring. Adjacency binding
    // fixes both directions.
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-keep-"));
    try {
      await writeFile(
        path.join(dir, "Keeps.lean"),
        `-- keep: reused by the sibling run
/-- A docstring
spanning three
whole lines. -/
lemma kept_but_documented : True := by trivial

lemma dead_two : True := by trivial
lemma dead_three : True := by trivial
`,
      );
      const dead = await sweepDeadHelpers(dir, new Set());
      expect(dead.map((d) => d.decl).sort()).toEqual(["dead_three", "dead_two"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("skips dotted declarations, sees unicode names, and counts consumers from searchRoot", async () => {
    const root = await mkdtemp(path.join(tmpdir(), "dead-helpers-root-"));
    try {
      const runDir = path.join(root, "Stat", "X_Research");
      const sibling = path.join(root, "Stat", "Y_Research");
      await mkdir(runDir, { recursive: true });
      await mkdir(sibling, { recursive: true });
      await writeFile(
        path.join(runDir, "Mixed.lean"),
        `theorem Coeff.bound_of_le : True := by trivial
lemma τ_dead_greek : True := by trivial
lemma cross_run_helper : True := by trivial
`,
      );
      // The only consumer of cross_run_helper lives in the SIBLING run's tree.
      await writeFile(
        path.join(sibling, "Consumer.lean"),
        "theorem t : True := by\n  have h := cross_run_helper\n  trivial\n",
      );
      // leanDir-only view: cross_run_helper looks dead; dotted decl is skipped (never reported
      // under its namespace prefix); the unicode-named lemma IS visible and dead.
      const local = await sweepDeadHelpers(runDir, new Set());
      expect(local.map((d) => d.decl).sort()).toEqual(["cross_run_helper", "τ_dead_greek"]);
      // Package-wide consumer scan clears the cross-run helper.
      const wide = await sweepDeadHelpers(runDir, new Set(), { searchRoot: root });
      expect(wide.map((d) => d.decl)).toEqual(["τ_dead_greek"]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("is quiet on an empty/missing tree and does not count a decl's own definition as a use", async () => {
    await expect(sweepDeadHelpers("", new Set())).resolves.toEqual([]);
    await expect(sweepDeadHelpers("/nonexistent/run/dir", new Set())).resolves.toEqual([]);
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-solo-"));
    try {
      await writeFile(path.join(dir, "Solo.lean"), "lemma solo_lemma : True := by trivial\n");
      await expect(sweepDeadHelpers(dir, new Set())).resolves.toEqual([
        { decl: "solo_lemma", file: "Solo.lean", line: 1 },
      ]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
