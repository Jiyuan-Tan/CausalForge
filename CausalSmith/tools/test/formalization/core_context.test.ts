import { mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { readFormalizationCoreContext } from "../../src/formalization/core_context.js";

let tempDir: string | undefined;

afterEach(async () => {
  if (tempDir) await rm(tempDir, { recursive: true, force: true });
  tempDir = undefined;
});

describe("formalization structural core context", () => {
  it("retains declarations while omitting proof bodies and publication prose", async () => {
    tempDir = await mkdtemp(path.join(os.tmpdir(), "formalization-core-context-"));
    const fixture = JSON.parse(await import("node:fs/promises").then(({ readFile }) =>
      readFile(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8")));
    fixture.tldr = "PUBLICATION_PROSE_SENTINEL";
    fixture.statements[0].proof_tex = "PROOF_BODY_SENTINEL";
    fixture.statements[0].statement = "STATEMENT_SENTINEL";
    fixture.assumptions[0].condition = "CONDITION_SENTINEL";
    fixture.definitions[0].construction = "CONSTRUCTION_SENTINEL";
    fixture.statements[0].justification = "POSITIONING_SENTINEL_J";
    fixture.statements[0].gap = "POSITIONING_SENTINEL_G";
    fixture.statements[0].consumer = "POSITIONING_SENTINEL_C";
    fixture.bibliography = [{ key: "bib_sentinel", citation: "BIBLIOGRAPHY_SENTINEL" }];
    fixture.comparator_promise_table = [];
    const target = path.join(tempDir, "core.json");
    await writeFile(target, JSON.stringify(fixture), "utf8");

    const context = await readFormalizationCoreContext(target, "test");
    expect(context).not.toContain("PUBLICATION_PROSE_SENTINEL");
    expect(context).not.toContain("PROOF_BODY_SENTINEL");
    expect(context).toContain("STATEMENT_SENTINEL");
    expect(context).toContain("CONDITION_SENTINEL");
    expect(context).toContain("CONSTRUCTION_SENTINEL");
    // Positioning prose + bibliography are D-side/F1 material; F1.5/F2 never consume them.
    expect(context).not.toContain("POSITIONING_SENTINEL");
    expect(context).not.toContain("BIBLIOGRAPHY_SENTINEL");
    expect(context).not.toContain("comparator_promise_table");
    // Compact serialization: no indentation newlines.
    expect(context).not.toMatch(/\n {2}"/);
    // Dependency wiring survives.
    expect(context).toContain('"depends_on"');
  });
});
