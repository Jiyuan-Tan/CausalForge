import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { extractCodexTokenUsage } from "../src/shared/codex.js";
import { extractClaudeTokenUsage } from "../src/workers/claude.js";
import {
  appendTokenUsageRecord,
  markTokenUsageIncomplete,
  patchReadmeTokenUsage,
  summarizeTokenUsage,
} from "../src/token_usage.js";

const dirs: string[] = [];
afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

async function tempDir(): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "causalsmith-token-usage-"));
  dirs.push(dir);
  return dir;
}

describe("token usage", () => {
  it("extracts the final Codex cumulative counter", async () => {
    const dir = await tempDir();
    const file = path.join(dir, "rollout.jsonl");
    await writeFile(file, [
      JSON.stringify({ type: "event_msg", payload: { type: "token_count", info: {
        total_token_usage: { input_tokens: 10, cached_input_tokens: 4, output_tokens: 2, total_tokens: 12 },
      } } }),
      JSON.stringify({ type: "event_msg", payload: { type: "token_count", info: {
        total_token_usage: {
          input_tokens: 30, cached_input_tokens: 20, cache_write_input_tokens: 3,
          output_tokens: 7, reasoning_output_tokens: 5, total_tokens: 37,
        },
      } } }),
    ].join("\n"));
    expect(await extractCodexTokenUsage(file)).toEqual({
      input_tokens: 30,
      cached_input_tokens: 20,
      cache_creation_input_tokens: 3,
      output_tokens: 7,
      reasoning_output_tokens: 5,
      total_tokens: 37,
    });
  });

  it("extracts Claude cache and output usage without double counting", () => {
    const stdout = JSON.stringify({
      type: "result",
      usage: {
        input_tokens: 11,
        cache_creation_input_tokens: 13,
        cache_read_input_tokens: 17,
        output_tokens: 19,
      },
    });
    expect(extractClaudeTokenUsage(stdout)).toEqual({
      input_tokens: 11,
      cached_input_tokens: 17,
      cache_creation_input_tokens: 13,
      output_tokens: 19,
      reasoning_output_tokens: 0,
      total_tokens: 60,
    });
  });

  it("aggregates providers and patches the bank README", async () => {
    const dir = await tempDir();
    const usage = {
      input_tokens: 10,
      cached_input_tokens: 4,
      cache_creation_input_tokens: 0,
      output_tokens: 2,
      reasoning_output_tokens: 1,
      total_tokens: 12,
    };
    await appendTokenUsageRecord(dir, {
      timestamp: "2026-01-01T00:00:00Z", provider: "codex", model: "codex",
      stage: "F2", duration_ms: 1, success: true, usage,
    });
    await appendTokenUsageRecord(dir, {
      timestamp: "2026-01-01T00:00:01Z", provider: "claude", model: "claude",
      stage: "F4", duration_ms: 1, success: true, usage: { ...usage, total_tokens: 15 },
    });
    const summary = await summarizeTokenUsage(dir, 100);
    expect(summary.complete).toBe(true);
    expect(summary.pipeline_codex.total_tokens).toBe(12);
    expect(summary.pipeline_claude.total_tokens).toBe(15);
    expect(summary.total_tokens_consumed).toBe(127);

    const readme = path.join(dir, "README.md");
    await writeFile(readme, "---\nqid: q\nbanked_on: now\n---\n");
    await patchReadmeTokenUsage(readme, summary);
    const text = await readFile(readme, "utf8");
    expect(text).toContain("pipeline_codex_tokens: 12");
    expect(text).toContain("pipeline_claude_tokens: 15");
    expect(text).toContain("total_tokens_consumed: 127");
  });

  it("never labels a run exact after a ledger-write failure marker", async () => {
    const dir = await tempDir();
    const usage = {
      input_tokens: 10, cached_input_tokens: 0, cache_creation_input_tokens: 0,
      output_tokens: 2, reasoning_output_tokens: 0, total_tokens: 12,
    };
    await appendTokenUsageRecord(dir, {
      timestamp: "2026-01-01T00:00:00Z", provider: "codex", model: "codex",
      stage: "F2", duration_ms: 1, success: true, usage,
    });
    await markTokenUsageIncomplete(dir, "simulated append failure");
    const summary = await summarizeTokenUsage(dir, 100);
    expect(summary.complete).toBe(false);
    expect(summary.total_tokens_consumed).toBeNull();
  });
});
