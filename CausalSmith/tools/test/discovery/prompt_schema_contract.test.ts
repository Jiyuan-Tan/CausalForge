// Prompt↔schema drift guard for the D-1.2 proto-core persist boundary.
//
// runStageNeg1_2ProtoCore persists `{...CoreSchema.parse(core)}` plus the
// CORE_HANDOFF_KEYS allowlist; every other top-level key the author emits is
// deliberately dropped (prompt-injection / payload-bloat defense). That design
// silently swallows any field the D-1 prompt mandates but the schema does not
// know — the 2026-07-22 comparator_promise_table incident cost two paid D-0.5
// review rounds this way. This test extracts the prompt's mandated top-level
// fields and proves each one has a persistence home, turning future
// prompt-vs-schema drift into a red test at edit time.
import { readFile } from "node:fs/promises";
import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../src/discovery/core/schema.js";
import { CORE_HANDOFF_KEYS } from "../../src/discovery/stages/neg1_2_author.js";

const PROMPT_URL = new URL(
  "../../src/discovery/prompts/D-1/stage_neg1_2_proto_core.txt",
  import.meta.url,
);

/** Top-level fields the prompt mandates: the leading run of backticked
 * identifiers in each `- \`field\`` bullet (nested row-field mentions later in
 * the same line are intentionally not captured). */
function extractPromptFields(prompt: string): string[] {
  const fields: string[] = [];
  for (const line of prompt.split("\n")) {
    const m = /^- ((?:`[a-z_][a-z0-9_]*`)(?:,\s*`[a-z_][a-z0-9_]*`)*)/.exec(line);
    if (!m) continue;
    for (const tok of m[1].matchAll(/`([a-z_][a-z0-9_]*)`/g)) fields.push(tok[1]);
  }
  return [...new Set(fields)];
}

/** CoreSchema is wrapped in `.refine(...)` effects; unwrap to the object shape. */
function coreSchemaKeys(): Set<string> {
  let s: unknown = CoreSchema;
  while (typeof (s as { innerType?: unknown }).innerType === "function") {
    s = (s as { innerType: () => unknown }).innerType();
  }
  return new Set(Object.keys((s as { shape: Record<string, unknown> }).shape));
}

/** Prompt-mandated fields that are intentionally NOT persisted go here, each
 * with a reason. Empty today: everything the prompt mandates must survive. */
const EXPECTED_DROPS: ReadonlySet<string> = new Set<string>();

describe("D-1 proto-core prompt ↔ CoreSchema persistence contract", () => {
  it("extracts a plausible field list from the prompt (extraction-rot canary)", async () => {
    const fields = extractPromptFields(await readFile(PROMPT_URL, "utf8"));
    for (const canary of ["qid", "symbols", "statements", "comparator_promise_table", "tldr"]) {
      expect(fields, `canary field ${canary} not extracted — bullet format changed?`).toContain(canary);
    }
    expect(fields.length).toBeGreaterThanOrEqual(12);
  });

  it("every prompt-mandated top-level field survives the persist boundary", async () => {
    const fields = extractPromptFields(await readFile(PROMPT_URL, "utf8"));
    const schemaKeys = coreSchemaKeys();
    const handoffKeys = new Set<string>(CORE_HANDOFF_KEYS);
    const orphans = fields.filter(
      (f) => !schemaKeys.has(f) && !handoffKeys.has(f) && !EXPECTED_DROPS.has(f),
    );
    expect(
      orphans,
      `prompt mandates field(s) with no persistence home — the author's output would be ` +
        `silently dropped at the CoreSchema/allowlist boundary (comparator_promise_table ` +
        `incident class). Add to CoreSchema, CORE_HANDOFF_KEYS, or EXPECTED_DROPS (with reason): ` +
        orphans.join(", "),
    ).toEqual([]);
  });

  it("EXPECTED_DROPS stays minimal: no entry that already has a persistence home", () => {
    const schemaKeys = coreSchemaKeys();
    const handoffKeys = new Set<string>(CORE_HANDOFF_KEYS);
    const stale = [...EXPECTED_DROPS].filter((f) => schemaKeys.has(f) || handoffKeys.has(f));
    expect(stale).toEqual([]);
  });
});
