// Live MCP smoke test — exercised manually via `npx tsx test/fixtures/smoke.ts`.
// Not part of `npm test`; requires `lean-lsp-mcp` on PATH and a built Lean project.
import path from "node:path";
import { fileURLToPath } from "node:url";
import { McpLeanLspClient } from "../../src/workers/leanLsp.js";
import { findCausalSmithRoot } from "../../src/shared/repo_root.js";

async function main() {
  const repoRoot =
    process.env.SMOKE_REPO ??
    path.dirname(findCausalSmithRoot(path.dirname(fileURLToPath(import.meta.url))));
  const client = new McpLeanLspClient({
    repoRoot,
    onStderr: () => {},
  });
  try {
    console.log(`[smoke] repoRoot=${repoRoot}`);
    console.log("[smoke] localSearch FWL...");
    const hits = await client.localSearch("FWL", 3);
    console.log("  hits:", JSON.stringify(hits.slice(0, 3), null, 2));
    console.log("[smoke] localSearch FrischWaughLovell...");
    const more = await client.localSearch("FrischWaughLovell", 2);
    console.log("  more:", JSON.stringify(more.slice(0, 2), null, 2));
    console.log("[smoke] OK");
  } finally {
    await client.close();
  }
}

main().catch((err) => {
  console.error("SMOKE FAILED:", err);
  process.exit(1);
});
