import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  migrateMarkdown,
  runMigration,
} from "../scripts/dev/migrate_bank_stage_prose.mjs";

describe("migrateMarkdown", () => {
  it("rewrites stage labels only in prose", () => {
    const input = [
      "---",
      "summary: Stage 0.5 should stay in YAML",
      "artifact: oneshot_stage0_5_field_2026-05-14T15-55-41-123Z.txt",
      "---",
      "",
      "**Stage -0.5 verdict.** ACCEPT",
      "The Stage 0.5 review followed Stage -1.2 and Stage 4d.",
      "A sentence-leading stage 3 label appears here.",
      "Keep `Stage 2` and `oneshot_stage0_5_field.txt` inline.",
      "```",
      "Stage 5 remains in a fence.",
      "```",
      "- `entry_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).",
      "",
    ].join("\n");

    const result = migrateMarkdown(input);

    expect(result.substitutions).toBe(7);
    expect(result.content).toContain("summary: Stage 0.5 should stay in YAML");
    expect(result.content).toContain("artifact: oneshot_stage0_5_field_2026-05-14T15-55-41-123Z.txt");
    expect(result.content).toContain("**D-0.5 verdict.** ACCEPT");
    expect(result.content).toContain("The D0.5 review followed D-1.2 and F4.d.");
    expect(result.content).toContain("A sentence-leading F3 label appears here.");
    expect(result.content).toContain("Keep `Stage 2` and `oneshot_stage0_5_field.txt` inline.");
    expect(result.content).toContain("Stage 5 remains in a fence.");
    expect(result.content).toContain("`entry_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).");
  });
});

describe("runMigration", () => {
  it("targets entry READMEs in requested bank tiers and leaves index/jsonl files alone", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "bank-stage-migration-"));
    const bankRoot = path.join(repoRoot, "CausalSmith", "doc", "research", "_bank");
    const entryDir = path.join(bankRoot, "failed", "pid_example_v1");
    await mkdir(entryDir, { recursive: true });
    await mkdir(path.join(bankRoot, "legacy", "pid_old_v1"), { recursive: true });
    await writeFile(path.join(entryDir, "README.md"), "Stage -0.5 and Stage 1\n");
    await writeFile(path.join(entryDir, "pid_example_v1_reviews.jsonl"), "{\"stage\":\"-0.5\"}\n");
    await writeFile(path.join(bankRoot, "failed", "README.md"), "Stage -0.5 index\n");
    await writeFile(path.join(bankRoot, "legacy", "pid_old_v1", "README.md"), "Stage 5 legacy\n");

    const dryRun = await runMigration({ repoRoot, write: false });
    expect(dryRun.filesTouched).toBe(1);
    expect(dryRun.totalSubstitutions).toBe(2);

    expect(await readFile(path.join(entryDir, "README.md"), "utf8")).toBe("Stage -0.5 and Stage 1\n");

    const writeRun = await runMigration({ repoRoot, write: true });
    expect(writeRun.filesTouched).toBe(1);
    expect(writeRun.totalSubstitutions).toBe(2);
    expect(await readFile(path.join(entryDir, "README.md"), "utf8")).toBe("D-0.5 and F1\n");
    expect(await readFile(path.join(entryDir, "pid_example_v1_reviews.jsonl"), "utf8")).toBe("{\"stage\":\"-0.5\"}\n");
    expect(await readFile(path.join(bankRoot, "failed", "README.md"), "utf8")).toBe("Stage -0.5 index\n");
    expect(await readFile(path.join(bankRoot, "legacy", "pid_old_v1", "README.md"), "utf8")).toBe("Stage 5 legacy\n");
  });
});
