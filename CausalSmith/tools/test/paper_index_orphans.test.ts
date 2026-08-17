import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { findOrphanPaperModules } from "../src/presentation/paper_index_orphans.js";

describe("findOrphanPaperModules", () => {
  it("catches a public orphan and spares private-only and indexed modules", async () => {
    const runDir = await mkdtemp(path.join(tmpdir(), "paper-index-orphans-"));
    try {
      await mkdir(path.join(runDir, "Helpers"));
      await mkdir(path.join(runDir, "tmp"));
      await writeFile(
        path.join(runDir, "Orphan.lean"),
        `-- theorem commentedOut : True := by trivial
/- def blockCommented := 1 -/
private lemma hidden : True := by trivial
lemma exposed : True := by trivial
`,
      );
      await writeFile(
        path.join(runDir, "Helpers", "PrivateOnly.lean"),
        `/- theorem notCode : True := by trivial -/
private theorem hiddenTheorem : True := by trivial
private noncomputable def hiddenDef : Nat := 0
`,
      );
      await writeFile(
        path.join(runDir, "CommentsOnly.lean"),
        `-- lemma lineCommented : True := by trivial
/- def blockCommentedAgain := 2 -/
`,
      );
      await writeFile(
        path.join(runDir, "Indexed.lean"),
        "def represented : Nat := 1\n",
      );
      await writeFile(
        path.join(runDir, "tmp", "Probe.lean"),
        "lemma disposableProbe : True := by trivial\n",
      );

      const prefix = "CausalSmith.Stat.SCRATCH_Research";
      await expect(
        findOrphanPaperModules(
          runDir,
          prefix,
          new Set([`${prefix}.Indexed`]),
        ),
      ).resolves.toEqual([
        { module: `${prefix}.Orphan`, file: "Orphan.lean" },
      ]);
    } finally {
      await rm(runDir, { recursive: true, force: true });
    }
  });
});
