import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { bankSoundnessIssues, textHasRealSorry } from "../../src/formalization/bank_soundness.js";

let root = "";
let leanDir = "";

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "bank-soundness-"));
  leanDir = join(root, "CausalSmith", "Stat", "Demo");
  await mkdir(leanDir, { recursive: true });
});
afterEach(async () => {
  await rm(root, { recursive: true, force: true });
});

const clean = "import Mathlib.Tactic\n\nnamespace Demo\n\ntheorem ok : True := by trivial\n\nend Demo\n";

describe("textHasRealSorry", () => {
  it("finds an uncommented sorry", () => {
    expect(textHasRealSorry("theorem t : True := by\n  sorry\n")).toBe(true);
  });

  it("ignores a sorry inside a line comment", () => {
    expect(textHasRealSorry("theorem t : True := by\n  trivial -- no sorry here\n")).toBe(false);
  });

  it("ignores a sorry inside a block comment / docstring", () => {
    expect(textHasRealSorry("/-- closes the sorry -/\ntheorem t : True := by trivial\n")).toBe(false);
  });

  // REGRESSION (2026-07-21 audit): the old line-granular scanner skipped an ENTIRE line that
  // merely STARTED inside a block comment, so real code after a mid-line `-/` close escaped it.
  it("catches a sorry on a line that starts inside a block comment but closes it mid-line", () => {
    expect(textHasRealSorry("/- note\nspans lines -/ theorem t : True := by sorry\n")).toBe(true);
  });

  it("does not treat a longer identifier as a sorry", () => {
    expect(textHasRealSorry("def sorryFree : Nat := 0\n")).toBe(false);
  });
});

describe("bankSoundnessIssues", () => {
  it("passes a clean artifact", async () => {
    await writeFile(join(leanDir, "T.lean"), clean);
    expect(await bankSoundnessIssues(leanDir, root)).toEqual([]);
  });

  it("reports a sorry in the artifact", async () => {
    await writeFile(join(leanDir, "T.lean"), "namespace D\ntheorem t : True := by sorry\nend D\n");
    const issues = await bankSoundnessIssues(leanDir, root);
    expect(issues.some((i) => i.startsWith("sorry in"))).toBe(true);
  });

  it.each(["axiom foo : True", "opaque bar : Nat", "theorem t : True := by native_decide", "theorem t : True := by admit"])(
    "reports the cheat token in %j",
    async (line) => {
      await writeFile(join(leanDir, "T.lean"), `namespace D\n${line}\nend D\n`);
      expect(await bankSoundnessIssues(leanDir, root)).not.toEqual([]);
    },
  );

  // The paper's disposable agent workspace (`<leanDir>/tmp`) is excluded from the bank
  // inventory: agents are TOLD to leave sorry-laden Lean probes there, and a scratch file
  // must not spuriously block banking of an otherwise clean artifact.
  it("ignores scratch files under the paper tmp/ workspace", async () => {
    await writeFile(join(leanDir, "T.lean"), clean);
    const scratch = join(leanDir, "tmp");
    await mkdir(scratch, { recursive: true });
    await writeFile(join(scratch, "Main.lean"), "theorem probe : True := by sorry\n");
    expect(await bankSoundnessIssues(leanDir, root)).toEqual([]);
  });

  // The gate follows imports into CausalSmith.Mathlib.*, so debt cannot be laundered by moving it
  // one module out of the artifact directory.
  it("follows a CausalSmith.Mathlib import and reports debt found there", async () => {
    const mathlibDir = join(root, "CausalSmith", "Mathlib");
    await mkdir(mathlibDir, { recursive: true });
    await writeFile(join(mathlibDir, "Helper.lean"), "namespace H\ntheorem h : True := by sorry\nend H\n");
    await writeFile(join(leanDir, "T.lean"), "import CausalSmith.Mathlib.Helper\n\nnamespace D\ntheorem t : True := by trivial\nend D\n");
    const issues = await bankSoundnessIssues(leanDir, root);
    expect(issues.some((i) => i.includes("Mathlib/Helper.lean"))).toBe(true);
  });
});
