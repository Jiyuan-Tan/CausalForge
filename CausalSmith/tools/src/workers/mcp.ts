import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";

export interface McpClientOpts {
  cmd: string;
  args: string[];
  cwd?: string;
  env?: NodeJS.ProcessEnv;
  /** Total budget for `initialize` handshake. Default 15s. */
  initTimeoutMs?: number;
  /** Default per-call timeout if a caller does not supply one. Default 5min. */
  defaultCallTimeoutMs?: number;
  /** Optional stderr sink; defaults to ignoring stderr (the server logs INFO there). */
  onStderr?: (chunk: string) => void;
}

export interface McpToolCallResult {
  /** Parsed structuredContent when present, else parsed JSON of content[0].text. */
  value: unknown;
  /** `true` when the server flagged the call as an error. */
  isError: boolean;
  /** Raw text body, useful for diagnostics. */
  rawText: string;
}

export class McpError extends Error {
  constructor(
    message: string,
    public readonly cause?: unknown,
  ) {
    super(message);
    this.name = "McpError";
  }
}

interface Pending {
  resolve: (value: unknown) => void;
  reject: (err: Error) => void;
  timer: NodeJS.Timeout;
}

/**
 * Minimal MCP stdio client. Speaks newline-delimited JSON-RPC 2.0 with a
 * spawned child process (e.g. the `lean-lsp-mcp` binary). One client = one
 * long-lived child; many `callTool` invocations are multiplexed by id.
 */
export class McpClient {
  private child: ChildProcessWithoutNullStreams | null = null;
  private nextId = 1;
  private pending = new Map<number, Pending>();
  private buffer = "";
  private started = false;
  private startPromise: Promise<void> | null = null;
  private closed = false;
  private exitError: Error | null = null;
  /** Set by shutdown(): a deliberately-closed client must NOT respawn. */
  private userClosed = false;
  private restarts = 0;
  private static readonly MAX_RESTARTS = 3;

  constructor(private readonly opts: McpClientOpts) {}

  async start(): Promise<void> {
    if (this.started) return;
    if (this.startPromise) return this.startPromise;
    // why: concurrent first calls must all wait for initialize + initialized before tools/call.
    this.startPromise = this.startInner();
    try {
      await this.startPromise;
    } finally {
      this.startPromise = null;
    }
  }

  private async startInner(): Promise<void> {
    this.child = spawn(this.opts.cmd, this.opts.args, {
      cwd: this.opts.cwd,
      env: this.opts.env ?? process.env,
      stdio: ["pipe", "pipe", "pipe"],
    });
    this.child.stdout.setEncoding("utf8");
    this.child.stderr.setEncoding("utf8");
    this.child.stdout.on("data", (chunk: string) => this.onStdout(chunk));
    this.child.stderr.on("data", (chunk: string) => {
      this.opts.onStderr?.(chunk);
    });
    this.child.on("exit", (code, signal) => this.onExit(code, signal));
    this.child.on("error", (err) => {
      this.exitError = err;
      this.failAllPending(err);
    });

    const initBudget = this.opts.initTimeoutMs ?? 15_000;
    try {
      await this.request(
        "initialize",
        {
          protocolVersion: "2024-11-05",
          capabilities: {},
          clientInfo: { name: "causalsmith", version: "0.1.0" },
        },
        initBudget,
      );
    } catch (err) {
      await this.shutdown().catch(() => {});
      throw new McpError(
        `MCP initialize failed: ${err instanceof Error ? err.message : String(err)}`,
        err,
      );
    }
    this.notify("notifications/initialized", {});
    this.started = true;
  }

  /**
   * Call a tool. Returns the parsed result body (preferring
   * `structuredContent`, falling back to JSON-parsed `content[0].text`).
   * Throws `McpError` on transport failure or when `isError === true`.
   */
  async callTool(
    name: string,
    args: Record<string, unknown>,
    opts: { timeoutMs?: number } = {},
  ): Promise<McpToolCallResult> {
    if (!this.started) await this.start();
    // A crashed child previously left every future request rejecting forever
    // — compile-error detection went silently blind for the rest of the run.
    // Respawn (bounded) instead.
    else if (this.closed || this.exitError) await this.restartAfterCrash();
    const result = (await this.request(
      "tools/call",
      { name, arguments: args },
      opts.timeoutMs ?? this.opts.defaultCallTimeoutMs ?? 5 * 60 * 1000,
    )) as {
      content?: Array<{ type: string; text?: string }>;
      structuredContent?: unknown;
      isError?: boolean;
    };
    const rawText = result.content?.find((c) => c.type === "text")?.text ?? "";
    let value: unknown = result.structuredContent;
    if (value === undefined && rawText) {
      try {
        value = JSON.parse(rawText);
      } catch {
        value = rawText;
      }
    }
    const isError = result.isError === true;
    if (isError) {
      throw new McpError(
        `MCP tool '${name}' returned isError=true: ${rawText.slice(0, 800) || "(no body)"}`,
      );
    }
    return { value, isError: false, rawText };
  }

  private async restartAfterCrash(): Promise<void> {
    if (this.userClosed) throw new McpError("MCP client was shut down");
    if (this.restarts >= McpClient.MAX_RESTARTS) {
      throw new McpError(
        `MCP child crashed and the restart budget (${McpClient.MAX_RESTARTS}) is exhausted: ${this.exitError?.message ?? "child exited"}`,
      );
    }
    this.restarts += 1;
    console.warn(
      `[mcp] child died (${this.exitError?.message ?? "exited"}) — respawning ` +
        `(${this.restarts}/${McpClient.MAX_RESTARTS}): ${this.opts.cmd}`,
    );
    this.failAllPending(new McpError("MCP child died; restarting"));
    this.child = null;
    this.started = false;
    this.closed = false;
    this.exitError = null;
    this.buffer = "";
    await this.start();
  }

  async shutdown(): Promise<void> {
    this.userClosed = true;
    if (this.closed || !this.child) {
      this.closed = true;
      return;
    }
    this.closed = true;
    const child = this.child;
    return new Promise((resolve) => {
      const cleanup = () => {
        this.failAllPending(new McpError("MCP client shutting down"));
        resolve();
      };
      let killed = false;
      const onExit = () => {
        clearTimeout(grace);
        cleanup();
      };
      const grace = setTimeout(() => {
        if (!killed) {
          killed = true;
          try { child.kill("SIGKILL"); } catch { /* noop */ }
        }
      }, 2_000);
      child.once("exit", onExit);
      try {
        child.stdin.end();
        child.kill("SIGTERM");
      } catch {
        clearTimeout(grace);
        cleanup();
      }
    });
  }

  // --- internals ---

  private request(method: string, params: unknown, timeoutMs: number): Promise<unknown> {
    if (this.exitError) {
      return Promise.reject(new McpError(`MCP child failed: ${this.exitError.message}`));
    }
    if (this.closed || !this.child) {
      return Promise.reject(new McpError("MCP client is not running"));
    }
    const id = this.nextId++;
    const payload = { jsonrpc: "2.0", id, method, params };
    return new Promise<unknown>((resolve, reject) => {
      const timer = setTimeout(() => {
        this.pending.delete(id);
        reject(new McpError(`MCP request '${method}' timed out after ${timeoutMs}ms`));
      }, timeoutMs);
      this.pending.set(id, {
        resolve: (v) => {
          clearTimeout(timer);
          resolve(v);
        },
        reject: (e) => {
          clearTimeout(timer);
          reject(e);
        },
        timer,
      });
      try {
        this.child!.stdin.write(`${JSON.stringify(payload)}\n`);
      } catch (err) {
        this.pending.delete(id);
        clearTimeout(timer);
        reject(
          new McpError(
            `Failed to write MCP request '${method}': ${err instanceof Error ? err.message : String(err)}`,
            err,
          ),
        );
      }
    });
  }

  private notify(method: string, params: unknown): void {
    if (!this.child) return;
    const payload = { jsonrpc: "2.0", method, params };
    try {
      this.child.stdin.write(`${JSON.stringify(payload)}\n`);
    } catch {
      // notifications are best-effort
    }
  }

  private onStdout(chunk: string): void {
    this.buffer += chunk;
    let idx: number;
    while ((idx = this.buffer.indexOf("\n")) >= 0) {
      const line = this.buffer.slice(0, idx).trim();
      this.buffer = this.buffer.slice(idx + 1);
      if (!line) continue;
      this.handleLine(line);
    }
  }

  private handleLine(line: string): void {
    let msg: {
      id?: number | string;
      result?: unknown;
      error?: { code?: number; message?: string; data?: unknown };
      method?: string;
    };
    try {
      msg = JSON.parse(line);
    } catch {
      // Server occasionally prints a non-JSON line (shouldn't happen on stdout,
      // but tolerate it). Drop and continue.
      return;
    }
    if (typeof msg.id === "number" && this.pending.has(msg.id)) {
      const pending = this.pending.get(msg.id)!;
      this.pending.delete(msg.id);
      if (msg.error) {
        pending.reject(
          new McpError(`MCP error ${msg.error.code ?? ""}: ${msg.error.message ?? "(no message)"}`),
        );
      } else {
        pending.resolve(msg.result);
      }
      return;
    }
    // Server-initiated notifications (logging, progress) — ignore.
  }

  private onExit(code: number | null, signal: NodeJS.Signals | null): void {
    this.closed = true;
    if (this.pending.size === 0) return;
    const err = new McpError(
      `MCP child exited (code=${code ?? "null"}, signal=${signal ?? "null"}) with ${this.pending.size} request(s) pending`,
    );
    this.failAllPending(err);
  }

  private failAllPending(err: Error): void {
    for (const [id, pending] of this.pending) {
      pending.reject(err);
      this.pending.delete(id);
    }
  }
}
