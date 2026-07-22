import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import {
  snapshotPriorProofs,
  injectCarryoverComments,
  restoreCarryoverProofs,
} from "../../src/formalization/proof_carryover.js";

// Prior (post-F3) scaffold: l_keep has a REAL proof, l_fix has a real proof too,
// t_thm is still sorry. After a rewind, F2 rewrites everything `:= by sorry`;
// l_keep's signature is unchanged (carry over), l_fix's signature changed (do not).
const PRIOR = `import Basic

/-- keep me -/
private lemma l_keep (n : Nat) : n + 0 = n := by
  simp

private lemma l_fix (a : Nat) (h : 0 < a) : a ≤ a := by
  exact le_refl a

theorem t_thm (n : Nat) : 0 + n = n := by
  sorry
`;

// New scaffold after the rewind: l_keep identical signature (sorry body),
// l_fix has a CHANGED signature (extra hyp), t_thm unchanged sorry.
const NEW = `import Basic

/-- keep me -/
private lemma l_keep (n : Nat) : n + 0 = n := by
  sorry

private lemma l_fix (a : Nat) (h : 0 < a) (hb : a ≤ 1) : a ≤ a := by
  sorry

theorem t_thm (n : Nat) : 0 + n = n := by
  sorry
`;

async function write(dir: string, name: string, content: string) {
  await writeFile(path.join(dir, name), content, "utf8");
}

describe("Stage 2 proof carry-over", () => {
  let dir: string;
  beforeEach(async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "carryover-"));
  });
  afterEach(async () => {
    await rm(dir, { recursive: true, force: true });
  });

  it("snapshots only real (non-sorry) proof bodies, keyed by signature", async () => {
    await write(dir, "T.lean", PRIOR);
    const snap = await snapshotPriorProofs(dir);
    const names = [...snap.values()].map((v) => v.name).sort();
    expect(names).toEqual(["l_fix", "l_keep"]); // t_thm is sorry → excluded
  });

  it("re-attaches a prior proof for a signature-UNCHANGED decl, not a changed one", async () => {
    await write(dir, "T.lean", PRIOR);
    const snap = await snapshotPriorProofs(dir);
    await write(dir, "T.lean", NEW); // the rewind overwrote everything to sorry
    const res = await injectCarryoverComments(dir, snap);
    expect(res.names).toEqual(["l_keep"]); // l_fix sig changed → not carried; t_thm never had a proof
    const after = await readFile(path.join(dir, "T.lean"), "utf8");
    // l_keep's proof is re-attached as an inert carry-over comment with its body.
    expect(after).toContain("PRIOR PROOF (carry-over: auto");
    expect(after).toContain("simp");
    // The live decl is still sorry-only (contract preserved).
    expect(after).toMatch(/private lemma l_keep \(n : Nat\) : n \+ 0 = n := by\s+sorry/);
    // l_fix (changed) did NOT get the old `exact le_refl a` re-attached.
    expect(after).not.toContain("exact le_refl a");
  });

  it("is idempotent — a second pass does not double-inject", async () => {
    await write(dir, "T.lean", PRIOR);
    const snap = await snapshotPriorProofs(dir);
    await write(dir, "T.lean", NEW);
    await injectCarryoverComments(dir, snap);
    const once = await readFile(path.join(dir, "T.lean"), "utf8");
    const res2 = await injectCarryoverComments(dir, snap);
    expect(res2.count).toBe(0);
    const twice = await readFile(path.join(dir, "T.lean"), "utf8");
    expect(twice).toBe(once);
  });

  it("mechanically restores signature-matched proofs before F3", async () => {
    await write(dir, "T.lean", PRIOR);
    const snap = await snapshotPriorProofs(dir);
    await write(dir, "T.lean", NEW);
    await injectCarryoverComments(dir, snap);

    const restored = await restoreCarryoverProofs(dir);
    expect(restored.names).toEqual(["l_keep"]);
    const after = await readFile(path.join(dir, "T.lean"), "utf8");
    expect(after).toMatch(/private lemma l_keep \(n : Nat\) : n \+ 0 = n := by\s+simp/);
    expect(after).not.toContain("PRIOR PROOF (carry-over: auto");
    expect(after).toMatch(/private lemma l_fix[\s\S]*:= by\s+sorry/);
  });

  // A single-line decl tail (`… := by sorry`) is snapshot/injected too; restore must handle
  // it or the carried proof stays an inert comment and F3 re-proves the decl from scratch.
  it("restores a carried proof onto a single-line `:= by sorry` decl", async () => {
    await write(dir, "I.lean", "private lemma l_inline (n : Nat) : n + 0 = n := by\n  simp\n");
    const snap = await snapshotPriorProofs(dir);
    await write(dir, "I.lean", "private lemma l_inline (n : Nat) : n + 0 = n := by sorry\n");
    const injected = await injectCarryoverComments(dir, snap);
    expect(injected.names).toEqual(["l_inline"]);

    const restored = await restoreCarryoverProofs(dir);
    expect(restored.names).toEqual(["l_inline"]);
    const after = await readFile(path.join(dir, "I.lean"), "utf8");
    expect(after).not.toContain("sorry");
    expect(after).not.toContain("PRIOR PROOF (carry-over: auto");
    expect(after).toMatch(/private lemma l_inline \(n : Nat\) : n \+ 0 = n := by\s+simp/);
  });

  it("restoration is idempotent", async () => {
    await write(dir, "T.lean", PRIOR);
    const snap = await snapshotPriorProofs(dir);
    await write(dir, "T.lean", NEW);
    await injectCarryoverComments(dir, snap);
    await restoreCarryoverProofs(dir);
    await expect(restoreCarryoverProofs(dir)).resolves.toEqual({ count: 0, names: [] });
  });

  it("no-op when there are no prior proofs (first scaffold / sorry-only prior)", async () => {
    await write(dir, "T.lean", NEW); // all sorry
    const snap = await snapshotPriorProofs(dir);
    const res = await injectCarryoverComments(dir, snap);
    expect(res.count).toBe(0);
  });

  it("skips a body containing `-/` (comment-nesting hazard)", async () => {
    const hazard = `import Basic

private lemma l_haz (n : Nat) : n = n := by
  -- closes a comment: -/ oops
  rfl
`;
    await write(dir, "T.lean", hazard);
    const snap = await snapshotPriorProofs(dir);
    expect(snap.size).toBe(0); // skipped — never re-attached
  });

  it("does not absorb the next declaration's docstring into the prior proof body", async () => {
    await write(dir, "T.lean", `theorem t1 : True := by
  trivial

/-- docs for t2 -/
theorem t2 : True := by
  trivial
`);
    const snap = await snapshotPriorProofs(dir);
    const t1 = [...snap.values()].find((v) => v.name === "t1");
    expect(t1?.body).not.toContain("docs for t2");
  });
});
