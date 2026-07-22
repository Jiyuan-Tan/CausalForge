#!/usr/bin/env node
// Minimal MCP stdio server used by the leanLsp.test.ts harness.
// Speaks newline-delimited JSON-RPC 2.0. Recognizes `initialize`,
// `notifications/initialized`, `tools/call` for a fixed set of lean_* tools.

import readline from "node:readline";

const rl = readline.createInterface({ input: process.stdin });

function send(payload) {
  process.stdout.write(`${JSON.stringify(payload)}\n`);
}

function ok(id, result) {
  send({ jsonrpc: "2.0", id, result });
}

function errResp(id, code, message) {
  send({ jsonrpc: "2.0", id, error: { code, message } });
}

function toolResult(payload) {
  return {
    content: [{ type: "text", text: JSON.stringify(payload) }],
    structuredContent: payload,
    isError: false,
  };
}

function toolError(message) {
  return {
    content: [{ type: "text", text: message }],
    isError: true,
  };
}

const handlers = {
  lean_goal: ({ file_path, line, column }) => {
    if (column === undefined) {
      return toolResult({
        line_context: `theorem foo : ${file_path}@${line}`,
        goals_before: ["⊢ True"],
        goals_after: ["no goals"],
      });
    }
    return toolResult({
      line_context: `theorem foo : ${file_path}@${line}`,
      goals: ["⊢ 1 + 1 = 2"],
    });
  },
  lean_term_goal: ({ line }) => toolResult({
    line_context: `line ${line}`,
    expected_type: "Nat",
  }),
  lean_diagnostic_messages: ({ file_path }) => {
    // Files matching Demo.lean carry sorries; emit the "declaration uses
    // 'sorry'" warning that findSorries() gates on. Other files (e.g. X.lean
    // used by diagnostics() test) get the original fixed pair.
    if (/Demo\.lean$/.test(file_path ?? "")) {
      return toolResult({
        diagnostics: [
          { file: file_path, line: 2, severity: "warning", message: "declaration uses 'sorry'" },
          { file: file_path, line: 5, severity: "warning", message: "declaration uses 'sorry'" },
        ],
        success: true,
      });
    }
    return toolResult({
      diagnostics: [
        { file: file_path, line: 7, severity: "error", message: "type mismatch" },
        { file: file_path, line: 9, severity: "warning", message: "unused variable" },
      ],
      success: true,
    });
  },
  lean_hover_info: ({ file_path, line, column }) => toolResult({
    symbol: "Nat.add",
    info: "Nat → Nat → Nat",
    diagnostics: [],
    _meta: { file_path, line, column },
  }),
  lean_multi_attempt: ({ snippets }) => toolResult({
    outcomes: snippets.map((s) => ({
      snippet: s,
      goals: s === "ring" ? [] : ["⊢ x = x"],
      diagnostics: s === "ring" ? [] : [
        { severity: "error", message: `tactic '${s}' failed` },
      ],
    })),
  }),
  lean_local_search: ({ query, limit }) => toolResult({
    items: Array.from({ length: Math.min(limit ?? 3, 3) }, (_, i) => ({
      name: `${query}_match_${i}`,
      kind: "theorem",
      file: `Causalean/Fake/${query}.lean`,
    })),
  }),
  lean_state_search: () => toolResult({
    items: [{ name: "rfl" }, { name: "Nat.add_comm" }],
  }),
  lean_hammer_premise: () => toolResult({
    items: [
      { name: "Nat.add_zero", score: 0.9 },
      { name: "Nat.zero_add", score: 0.8 },
    ],
  }),
  lean_build: () => toolResult({
    success: true,
    log: "[1/1] built Causalean",
    errors: [],
  }),
  lean_make_error: () => toolError("synthetic failure"),
};

rl.on("line", (line) => {
  if (!line.trim()) return;
  let msg;
  try {
    msg = JSON.parse(line);
  } catch {
    return;
  }
  if (msg.method === "initialize") {
    ok(msg.id, {
      protocolVersion: "2024-11-05",
      capabilities: { tools: { listChanged: false } },
      serverInfo: { name: "mock-mcp", version: "0.0.0" },
    });
    return;
  }
  if (msg.method === "notifications/initialized") return;
  if (msg.method === "tools/call") {
    const { name, arguments: args = {} } = msg.params ?? {};
    const handler = handlers[name];
    if (!handler) {
      errResp(msg.id, -32601, `unknown tool: ${name}`);
      return;
    }
    try {
      const result = handler(args);
      ok(msg.id, result);
    } catch (err) {
      errResp(msg.id, -32000, err?.message ?? String(err));
    }
    return;
  }
  if (typeof msg.id === "number") {
    errResp(msg.id, -32601, `unknown method: ${msg.method}`);
  }
});

// Keep process alive until stdin closes.
process.stdin.on("close", () => process.exit(0));
