import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { appendFileSync, mkdtempSync, rmSync, readFileSync, existsSync, mkdirSync, writeFileSync } from "node:fs";
import path from "node:path";
import os from "node:os";
import { appendEntry, readEntries, type DecisionLogEntry } from "../src/decision_log.js";

// eid_backdoor_x → research kind → doc/research/active/eid_backdoor_x/orchestrator/decision_log.jsonl
const QID = "eid_backdoor_demo";
let root: string;
const logPath = () =>
  path.join(root, "doc/research/active", QID, "orchestrator/decision_log.jsonl");

beforeEach(() => {
  root = mkdtempSync(path.join(os.tmpdir(), "declog-"));
});
afterEach(() => {
  rmSync(root, { recursive: true, force: true });
});

describe("decision_log", () => {
  it("append creates the dir+file and writes a parseable line", () => {
    appendEntry(root, QID, { type: "judgment", phase: "D", stage: "D0", why: "x" });
    expect(existsSync(logPath())).toBe(true);
    const lines = readFileSync(logPath(), "utf8").trim().split("\n");
    expect(lines).toHaveLength(1);
    expect(JSON.parse(lines[0]).why).toBe("x");
  });

  it("stamps ts when absent, preserves it when present", () => {
    const a = appendEntry(root, QID, { type: "dispatch", from: "main", phase: "D", subtype: "lease-grant" });
    expect(a.ts).toMatch(/^\d{4}-\d{2}-\d{2}T/);
    const b = appendEntry(root, QID, { type: "dispatch", from: "main", phase: "F", subtype: "lease-grant", ts: "2020-01-01T00:00:00.000Z" });
    expect(b.ts).toBe("2020-01-01T00:00:00.000Z");
  });

  it("read returns all entries in file order", () => {
    appendEntry(root, QID, { type: "judgment", phase: "D", round: 1 });
    appendEntry(root, QID, { type: "judgment", phase: "D", round: 2 });
    const all = readEntries(root, QID);
    expect(all.map((e) => e.round)).toEqual([1, 2]);
  });

  it("read filters by phase and type and honors tail", () => {
    appendEntry(root, QID, { type: "judgment", phase: "D" });
    appendEntry(root, QID, { type: "judgment", phase: "F" });
    appendEntry(root, QID, { type: "escalation", phase: "F", subtype: "tex-claim-wrong" });
    expect(readEntries(root, QID, { phase: "F" })).toHaveLength(2);
    expect(readEntries(root, QID, { type: "escalation" })).toHaveLength(1);
    expect(readEntries(root, QID, { tail: 1 })[0].subtype).toBe("tex-claim-wrong");
  });

  it("read on a missing file returns []", () => {
    expect(readEntries(root, "nonexistent_qid")).toEqual([]);
  });

  it("appends to an exact banked qid/spec instead of recreating an active stub", () => {
    const spec = "v1";
    const archived = path.join(root, "doc/research/_bank/downgraded", `${QID}_${spec}`);
    mkdirSync(path.join(archived, "orchestrator"), { recursive: true });
    writeFileSync(path.join(archived, "state.json"), JSON.stringify({ banked: true }));

    appendEntry(root, QID, { type: "terminal", tier: "downgraded" }, spec);

    expect(existsSync(path.join(archived, "orchestrator/decision_log.jsonl"))).toBe(true);
    expect(existsSync(logPath())).toBe(false);
    expect(readEntries(root, QID, {}, spec)).toHaveLength(1);
  });

  it("append rejects an unknown entry type", () => {
    expect(() =>
      appendEntry(root, QID, { type: "bogus" as unknown as DecisionLogEntry["type"] }),
    ).toThrow(/type/);
  });

  it("rejects an incomplete lease-grant journal entry", () => {
    expect(() => appendEntry(root, QID, { type: "dispatch", from: "main" }))
      .toThrow(/phase=D\|F/);
    expect(() => appendEntry(root, QID, { type: "dispatch", from: "main", phase: "D" }))
      .toThrow(/lease-grant/);
  });

  it("recovers prior receipts from a torn final journal append", () => {
    appendEntry(root, QID, { type: "judgment", phase: "D", round: 1 });
    appendFileSync(logPath(), '{"type":"escalation"');
    expect(readEntries(root, QID).map((entry) => entry.round)).toEqual([1]);
  });
});
