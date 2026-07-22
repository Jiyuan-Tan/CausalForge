import { mkdtemp, writeFile, mkdir } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { McpClient, McpError } from "../src/workers/mcp.js";
import { McpLeanLspClient } from "../src/workers/leanLsp.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const MOCK_SERVER = path.join(here, "fixtures", "mock-mcp-server.mjs");

function newMockClient(repoRoot: string) {
  return new McpLeanLspClient({
    repoRoot,
    argv: [process.execPath, MOCK_SERVER],
    timeouts: {
      diagnostics: 10_000,
      goal: 10_000,
      termGoal: 10_000,
      hoverInfo: 10_000,
      multiAttempt: 10_000,
      localSearch: 10_000,
      stateSearch: 10_000,
      hammerPremise: 10_000,
      build: 10_000,
    },
  });
}

describe("McpClient (raw JSON-RPC)", () => {
  let repoRoot: string;
  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "mcp-raw-"));
  });

  it("performs handshake and calls a tool", async () => {
    const client = new McpClient({
      cmd: process.execPath,
      args: [MOCK_SERVER],
      cwd: repoRoot,
    });
    try {
      await client.start();
      // Mock server is custom; the LeanLsp wrapper exercises tools/call,
      // here we just verify the protocol layer.
      const result = await client.callTool("lean_local_search", { query: "Foo", limit: 2 });
      expect(result.isError).toBe(false);
      expect(result.value).toMatchObject({
        items: expect.arrayContaining([
          expect.objectContaining({ name: "Foo_match_0" }),
        ]),
      });
    } finally {
      await client.shutdown();
    }
  });

  it("rejects when the server returns isError: true", async () => {
    const client = new McpClient({
      cmd: process.execPath,
      args: [MOCK_SERVER],
      cwd: repoRoot,
    });
    try {
      await client.start();
      await expect(client.callTool("lean_make_error", {})).rejects.toBeInstanceOf(McpError);
    } finally {
      await client.shutdown();
    }
  });

  it("propagates JSON-RPC errors for unknown methods", async () => {
    const client = new McpClient({
      cmd: process.execPath,
      args: [MOCK_SERVER],
      cwd: repoRoot,
    });
    try {
      await client.start();
      await expect(client.callTool("nope", {})).rejects.toBeInstanceOf(McpError);
    } finally {
      await client.shutdown();
    }
  });
});

describe("McpLeanLspClient (high-level methods)", () => {
  let repoRoot: string;
  let client: McpLeanLspClient;

  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "mcp-lean-"));
    client = newMockClient(repoRoot);
  });
  afterEach(async () => {
    await client.close();
  });

  it("goal() parses goals_before/goals_after when column omitted", async () => {
    const g = await client.goal("Causalean/X.lean", 12);
    expect(g.goals_before).toEqual(["⊢ True"]);
    expect(g.goals_after).toEqual(["no goals"]);
  });

  it("goal() parses goals when column supplied", async () => {
    const g = await client.goal("Causalean/X.lean", 12, 5);
    expect(g.goals).toEqual(["⊢ 1 + 1 = 2"]);
  });

  it("termGoal() returns expected_type", async () => {
    const t = await client.termGoal("Causalean/X.lean", 12);
    expect(t.expected_type).toBe("Nat");
  });

  it("diagnostics() parses entries", async () => {
    const d = await client.diagnostics("Causalean/X.lean");
    expect(d).toHaveLength(2);
    expect(d[0]).toMatchObject({ severity: "error", line: 7 });
    expect(d[1]).toMatchObject({ severity: "warning", line: 9 });
  });

  it("hoverInfo() returns symbol + info", async () => {
    const h = await client.hoverInfo("Causalean/X.lean", 1, 1);
    expect(h.symbol).toBe("Nat.add");
    expect(h.info).toContain("Nat");
  });

  it("multiAttempt() returns per-snippet outcomes", async () => {
    const r = await client.multiAttempt("Causalean/X.lean", 4, ["simp", "ring"]);
    expect(r.outcomes).toHaveLength(2);
    expect(r.outcomes[1].snippet).toBe("ring");
    expect(r.outcomes[1].goals).toEqual([]);
    expect(r.outcomes[0].diagnostics[0]?.severity).toBe("error");
  });

  it("localSearch() returns typed hits", async () => {
    const hits = await client.localSearch("FWL", 2);
    expect(hits).toHaveLength(2);
    expect(hits[0]).toMatchObject({ name: "FWL_match_0", kind: "theorem" });
  });

  it("stateSearch() returns lemma names", async () => {
    const r = await client.stateSearch("Causalean/X.lean", 1, 1, 5);
    expect(r.map((x) => x.name)).toEqual(["rfl", "Nat.add_comm"]);
  });

  it("hammerPremise() returns scored premises", async () => {
    const r = await client.hammerPremise("Causalean/X.lean", 1, 1, 8);
    expect(r[0]).toMatchObject({ name: "Nat.add_zero", score: 0.9 });
  });

  it("build() returns success + log tail", async () => {
    const b = await client.build();
    expect(b.success).toBe(true);
    expect(b.log).toContain("built Causalean");
  });

  it("findSorries() enriches each sorry line with goal + suggestions", async () => {
    const dir = path.join(repoRoot, "Causalean");
    await mkdir(dir, { recursive: true });
    const file = path.join(dir, "Demo.lean");
    await writeFile(
      file,
      [
        "theorem foo : True := by",
        "  sorry",
        "",
        "theorem bar : 1 = 1 := by",
        "  sorry",
      ].join("\n"),
      "utf8",
    );
    const sorries = await client.findSorries([file]);
    expect(sorries).toHaveLength(2);
    expect(sorries[0]).toMatchObject({ file: "Causalean/Demo.lean", line: 2, label: "foo" });
    expect(sorries[1]).toMatchObject({ file: "Causalean/Demo.lean", line: 5, label: "bar" });
    expect(sorries[0].goal).toContain("True");
    expect(sorries[0].suggestions.length).toBeGreaterThan(0);
  });
});
