// CausalSmith/tools/test/workers/leanLspConfig.test.ts
import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { writeLeanLspMcpConfig, writeLeanLspSharedConfig } from "../../src/workers/claude.js";

// The claude allow-list grants `mcp__lean-lsp__*`, so BOTH the stdio (per-call)
// and the shared (HTTP) MCP configs MUST register the server under the exact name
// `lean-lsp` — otherwise the tools are advertised under a different prefix and
// claude is never permitted to call them. These guard that contract.
describe("lean-lsp MCP config writers", () => {
  it("stdio config registers the server as `lean-lsp` with a command", () => {
    const p = writeLeanLspMcpConfig("/some/repo");
    const cfg = JSON.parse(readFileSync(p, "utf8"));
    expect(Object.keys(cfg.mcpServers)).toEqual(["lean-lsp"]);
    expect(typeof cfg.mcpServers["lean-lsp"].command).toBe("string");
    expect(cfg.mcpServers["lean-lsp"].url).toBeUndefined();
  });

  it("shared config registers `lean-lsp` as an HTTP server pointing at the shared URL", () => {
    const url = "http://127.0.0.1:54321/mcp";
    const p = writeLeanLspSharedConfig(url);
    const cfg = JSON.parse(readFileSync(p, "utf8"));
    expect(Object.keys(cfg.mcpServers)).toEqual(["lean-lsp"]);
    expect(cfg.mcpServers["lean-lsp"]).toEqual({ type: "http", url });
    // No stdio command → attaches to the shared server, does not spawn its own.
    expect(cfg.mcpServers["lean-lsp"].command).toBeUndefined();
  });
});
