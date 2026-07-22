import { appendFileSync, existsSync, mkdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { formalizationDir } from "./paths.js";

export const DECISION_LOG_TYPES = [
  "judgment",
  "escalation",
  "command",
  "terminal",
  "dispatch",
] as const;

export type DecisionLogEntry = {
  ts?: string;
  type: (typeof DECISION_LOG_TYPES)[number];
  phase?: "D" | "F";
  stage?: string;
  round?: number;
  from?: "main" | "D" | "F";
  // judgment
  class?: string;
  tried?: string;
  codex?: string;
  why?: string;
  // escalation
  subtype?: string;
  receipts?: string[];
  // command
  cmd?: string;
  target?: string;
  note?: string;
  // terminal
  tier?: "accepted" | "failed" | "downgraded";
  reraise?: string;
};

function logFile(repoRoot: string, qid: string, spec?: string): string {
  const active = formalizationDir(repoRoot, qid);
  if (existsSync(path.join(active, "state.json")) || !spec) {
    return path.join(active, "orchestrator", "decision_log.jsonl");
  }
  // Banking moves the entire run before main appends its terminal receipt.
  // Resolve the exact archived qid/spec instead of recreating an active stub.
  for (const tier of ["accepted", "downgraded", "failed", "legacy"]) {
    const archived = path.join(repoRoot, "doc", "research", "_bank", tier, `${qid}_${spec}`);
    if (existsSync(path.join(archived, "state.json"))) {
      return path.join(archived, "orchestrator", "decision_log.jsonl");
    }
  }
  return path.join(active, "orchestrator", "decision_log.jsonl");
}

export function appendEntry(
  repoRoot: string,
  qid: string,
  entry: DecisionLogEntry,
  spec?: string,
): DecisionLogEntry {
  if (!DECISION_LOG_TYPES.includes(entry.type)) {
    throw new Error(`decision_log: unknown entry type "${entry.type}"`);
  }
  if (entry.type === "dispatch") {
    if (entry.from !== "main" || (entry.phase !== "D" && entry.phase !== "F")) {
      throw new Error("decision_log: dispatch requires from=main and phase=D|F");
    }
    if (entry.subtype !== "lease-grant") {
      throw new Error('decision_log: dispatch requires subtype="lease-grant"');
    }
  }
  const stamped: DecisionLogEntry = { ts: entry.ts ?? new Date().toISOString(), ...entry };
  // A present-but-undefined entry.ts would clobber the default via the spread; re-assert the stamp.
  if (!stamped.ts) stamped.ts = new Date().toISOString();
  const file = logFile(repoRoot, qid, spec);
  mkdirSync(path.dirname(file), { recursive: true });
  appendFileSync(file, JSON.stringify(stamped) + "\n");
  return stamped;
}

export function readEntries(
  repoRoot: string,
  qid: string,
  opts: { phase?: "D" | "F"; type?: DecisionLogEntry["type"]; tail?: number } = {},
  spec?: string,
): DecisionLogEntry[] {
  const file = logFile(repoRoot, qid, spec);
  if (!existsSync(file)) return [];
  const lines = readFileSync(file, "utf8")
    .split("\n")
    .filter((l) => l.trim().length > 0);
  let entries = lines.flatMap((line, index): DecisionLogEntry[] => {
    try {
      return [JSON.parse(line) as DecisionLogEntry];
    } catch (err) {
      // A process can die during its final append. Preserve all prior durable
      // receipts and ignore only that torn tail; corruption in the middle is
      // not safely recoverable because it would hide later lease transitions.
      if (index === lines.length - 1) {
        console.warn(
          `[decision_log] ignoring truncated final entry at ${file}:${index + 1}: ` +
            `${err instanceof Error ? err.message : String(err)}`,
        );
        return [];
      }
      throw new Error(
        `decision_log: malformed entry at ${file}:${index + 1}: ` +
          `${err instanceof Error ? err.message : String(err)}`,
      );
    }
  });
  if (opts.phase) entries = entries.filter((e) => e.phase === opts.phase);
  if (opts.type) entries = entries.filter((e) => e.type === opts.type);
  if (opts.tail !== undefined) entries = entries.slice(-opts.tail);
  return entries;
}
