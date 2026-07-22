// CausalSmith/tools/test/substrate/log.test.ts
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile, readdir } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { logAgentCall } from "../../src/substrate/log.js";

let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "sublog-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("logAgentCall", () => {
  it("writes a full record + a JSONL index line", async () => {
    const file = await logAgentCall(root, {
      agent: "scaffolder", round: 1, callId: "main", model: "opus",
      prompt: "PROMPT", promptBytes: 6, rawOutput: "OUT",
      parsed: { decision: "build" }, ok: true, durationMs: 12,
    });
    expect(file).toBeTruthy();
    const rec = JSON.parse(await readFile(file!, "utf8"));
    expect(rec.prompt).toBe("PROMPT");
    expect(rec.rawOutput).toBe("OUT");
    const idxLines = (await readFile(path.join(root, "_calls.log"), "utf8")).trim().split("\n");
    expect(idxLines).toHaveLength(1);
    const idx = JSON.parse(idxLines[0]);
    expect(idx.agent).toBe("scaffolder");
    expect(idx.outputBytes).toBe(3);
    expect(idx.promptBytes).toBe(6);
    expect((await readdir(path.join(root, "agent_io"))).length).toBe(1);
  });

  it("appends successive calls to the index", async () => {
    await logAgentCall(root, { agent: "filler", round: 1, callId: "p1", model: "codex", prompt: "a", promptBytes: 1, rawOutput: "x", ok: true, durationMs: 1 });
    await logAgentCall(root, { agent: "filler", round: 1, callId: "p2", model: "codex", prompt: "b", promptBytes: 1, rawOutput: "y", ok: true, durationMs: 1 });
    const idxLines = (await readFile(path.join(root, "_calls.log"), "utf8")).trim().split("\n");
    expect(idxLines).toHaveLength(2);
  });

  it("never throws on an unwritable dir (best-effort)", async () => {
    const res = await logAgentCall("/proc/nonexistent-\0-bad", {
      agent: "reviewer", round: 1, callId: "main", model: "codex",
      prompt: "p", promptBytes: 1, rawOutput: "", ok: false, durationMs: 1,
    });
    expect(res).toBeNull();
  });
});
