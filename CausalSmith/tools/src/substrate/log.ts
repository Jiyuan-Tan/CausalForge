// CausalSmith/tools/src/substrate/log.ts
import { mkdir, writeFile, appendFile } from "node:fs/promises";
import path from "node:path";

export interface AgentCallLog {
  agent: "scaffolder" | "filler" | "reviewer" | "coordinator";
  round: number;
  callId: string;
  model: string;
  prompt: string;
  promptBytes: number;
  rawOutput: string;
  parsed?: unknown;
  parseError?: string;
  ok: boolean;
  durationMs: number;
}

/**
 * Persist a full agent-call record under `<runDir>/agent_io/` and append a
 * one-line JSONL index to `<runDir>/_calls.log`. Mirrors the main pipeline's
 * `_agent_logs` / `_reviewer_calls.log` convention: the resolved INPUT prompt
 * (+ byte length) and the RAW output are captured before any parse, so a parse
 * failure or a wrong proof leaves a forensic trail. Best-effort — never throws.
 */
export async function logAgentCall(runDir: string, rec: AgentCallLog): Promise<string | null> {
  try {
    const dir = path.join(runDir, "agent_io");
    await mkdir(dir, { recursive: true });
    const iso = new Date().toISOString();
    const stamp = iso.replace(/[:.]/g, "-");
    const safeCall = rec.callId.replace(/[^A-Za-z0-9._-]+/g, "_").slice(0, 40) || "call";
    const file = path.join(dir, `r${rec.round}__${rec.agent}__${safeCall}__${stamp}.json`);
    await writeFile(file, `${JSON.stringify(rec, null, 2)}\n`, "utf8");
    const idx = {
      ts: iso, agent: rec.agent, round: rec.round, callId: rec.callId, model: rec.model,
      promptBytes: rec.promptBytes, outputBytes: Buffer.byteLength(rec.rawOutput),
      ok: rec.ok, parseError: rec.parseError ?? null, durationMs: rec.durationMs,
      file: path.basename(file),
    };
    await appendFile(path.join(runDir, "_calls.log"), `${JSON.stringify(idx)}\n`, "utf8");
    return file;
  } catch {
    return null;
  }
}
