import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import {
  codexHome,
  resolveApiKey,
  resolveAuthMode,
  resolveProviderAuth,
  workerEnv,
} from "../../src/auth.js";
import { claudeAuthArgs } from "../../src/workers/claude.js";

const NO_CONFIG = { env: {} as NodeJS.ProcessEnv, config: {} };

const tempDirs: string[] = [];
function tempDir(): string {
  const dir = mkdtempSync(path.join(os.tmpdir(), "causalsmith-auth-"));
  tempDirs.push(dir);
  return dir;
}

afterEach(() => {
  vi.resetModules();
  vi.doUnmock("../../src/local_config.js");
  while (tempDirs.length > 0) {
    rmSync(tempDirs.pop() as string, { recursive: true, force: true });
  }
});

/**
 * Load `src/auth.ts` against a STUBBED `local.json`.
 *
 * This is the regression harness for the defect the first cut of this feature
 * shipped with: every resolver defaulted its config to `{}`, so the dispatchers
 * — which call `resolveProviderAuth("anthropic")` with NO arguments — never saw
 * a file-configured mode, and a `local.json` saying `authMode: "api"` silently
 * produced subscription flags while the startup banner claimed `api`. Tests that
 * always pass `config:` explicitly cannot see that; these must not.
 */
async function authWithLocalJson(file: Record<string, string>) {
  vi.resetModules();
  vi.doMock("../../src/local_config.js", () => ({
    localConfig: () => file,
    leanProjectPathFor: (root: string) => root,
    applyWorkerEnv: () => {},
  }));
  return import("../../src/auth.js");
}

describe("resolveAuthMode", () => {
  it("keeps the subscription login as the default", () => {
    expect(resolveAuthMode("anthropic", NO_CONFIG)).toBe("subscription");
    expect(resolveAuthMode("openai", NO_CONFIG)).toBe("subscription");
  });

  it("honors the global local-config opt-in for both providers", () => {
    const inputs = { env: {}, config: { authMode: "api" } };
    expect(resolveAuthMode("anthropic", inputs)).toBe("api");
    expect(resolveAuthMode("openai", inputs)).toBe("api");
  });

  it("lets a per-provider field override the global mode", () => {
    const inputs = { env: {}, config: { authMode: "api", openaiAuth: "subscription" } };
    expect(resolveAuthMode("anthropic", inputs)).toBe("api");
    expect(resolveAuthMode("openai", inputs)).toBe("subscription");
  });

  it("lets the environment override the file", () => {
    expect(
      resolveAuthMode("anthropic", {
        env: { CAUSALSMITH_AUTH_MODE: "api" },
        config: { authMode: "subscription" },
      }),
    ).toBe("api");
  });

  it("ranks a per-provider env var above the global one", () => {
    expect(
      resolveAuthMode("openai", {
        env: { CAUSALSMITH_AUTH_MODE: "api", CAUSALSMITH_OPENAI_AUTH: "subscription" },
        config: {},
      }),
    ).toBe("subscription");
  });

  it("fails closed on an unrecognized mode", () => {
    expect(() =>
      resolveAuthMode("anthropic", { env: { CAUSALSMITH_AUTH_MODE: "oauth" }, config: {} }),
    ).toThrow(/must be "subscription" or "api"/);
  });
});

describe("resolveApiKey", () => {
  it("prefers the environment over the config file", () => {
    expect(
      resolveApiKey("anthropic", {
        env: { ANTHROPIC_API_KEY: "sk-from-env" },
        config: { anthropicApiKey: "sk-from-file" },
      }),
    ).toBe("sk-from-env");
  });

  it("reads the first non-empty line of a key file", () => {
    const keyFile = path.join(tempDir(), "openai.key");
    writeFileSync(keyFile, "\n  sk-from-file  \nignored second line\n", "utf8");
    expect(resolveApiKey("openai", { env: {}, config: { openaiApiKeyFile: keyFile } })).toBe(
      "sk-from-file",
    );
  });

  it("pins the run to the key it started with rather than re-reading mid-run", () => {
    const keyFile = path.join(tempDir(), "rotating.key");
    writeFileSync(keyFile, "sk-first\n", "utf8");
    const config = { openaiApiKeyFile: keyFile };
    expect(resolveApiKey("openai", { env: {}, config })).toBe("sk-first");
    writeFileSync(keyFile, "sk-second\n", "utf8");
    // why: `workerEnv()` runs on every spawn; re-reading would move later workers
    // onto a different key (and make an NFS blip abort healthy ones) mid-run.
    expect(resolveApiKey("openai", { env: {}, config })).toBe("sk-first");
  });

  it("reports an unreadable key file instead of returning nothing", () => {
    expect(() =>
      resolveApiKey("openai", {
        env: {},
        config: { openaiApiKeyFile: path.join(os.tmpdir(), "causalsmith-absent-key") },
      }),
    ).toThrow(/could not be read/);
  });
});

describe("resolveProviderAuth", () => {
  it("refuses api mode with no key rather than billing the subscription", () => {
    expect(() =>
      resolveProviderAuth("anthropic", { env: { CAUSALSMITH_AUTH_MODE: "api" }, config: {} }),
    ).toThrow(/no API key is configured/);
  });

  it("carries no key in subscription mode even when one is configured", () => {
    expect(
      resolveProviderAuth("anthropic", { env: {}, config: { anthropicApiKey: "sk-x" } }),
    ).toEqual({ mode: "subscription" });
  });
});

describe("local.json reaches the dispatchers (no-argument resolution)", () => {
  it("resolves a file-configured api mode for a caller that passes no config", async () => {
    const auth = await authWithLocalJson({
      authMode: "api",
      anthropicApiKey: "sk-ant-file",
      openaiApiKey: "sk-oai-file",
    });
    // Exactly how runClaude / runCodex call it.
    expect(auth.resolveProviderAuth("anthropic", { env: {} })).toEqual({
      mode: "api",
      apiKey: "sk-ant-file",
    });
    expect(auth.resolveProviderAuth("openai", { env: {} })).toEqual({
      mode: "api",
      apiKey: "sk-oai-file",
    });
  });

  it("keeps the startup banner and the dispatchers on the same answer", async () => {
    const auth = await authWithLocalJson({
      anthropicAuth: "api",
      anthropicApiKey: "sk-ant-file",
      openaiAuth: "subscription",
    });
    // The banner said `claude=api` while the dispatcher built subscription flags:
    // the two MUST agree, or the operator is told the opposite of what happens.
    expect(auth.authSummary({ env: {} })).toBe("claude=api codex=subscription");
    expect(auth.resolveProviderAuth("anthropic", { env: {} }).mode).toBe("api");
  });

  it("does not redirect CODEX_HOME for a mode it would not bootstrap", async () => {
    const auth = await authWithLocalJson({ authMode: "api", anthropicApiKey: "sk-ant-file" });
    // openai has no key here, so api mode must be refused outright rather than
    // leaving codex pointed at an un-logged-in home.
    expect(() => auth.workerEnv({ env: {} })).toThrow(/no API key is configured/);
  });

  it("turns a file-configured api mode into the claude flag that actually bills the key", async () => {
    const auth = await authWithLocalJson({
      anthropicAuth: "api",
      anthropicApiKey: "sk-ant-file",
    });
    // The composition that shipped wrong: resolution said `api` in isolation while
    // the dispatcher still emitted subscription flags. Assert the whole chain.
    expect(claudeAuthArgs(auth.resolveProviderAuth("anthropic", { env: {} }).mode)).toEqual([
      "--bare",
    ]);
  });

  it("refuses to bootstrap the operator's own codex home", async () => {
    const auth = await authWithLocalJson({
      openaiAuth: "api",
      openaiApiKey: "sk-oai-file",
      codexApiHome: "~/.codex",
    });
    // Logging into ~/.codex with an API key deletes the stored ChatGPT credentials —
    // the exact loss the separate-home design exists to prevent.
    expect(() => auth.codexHome({ env: {} })).toThrow(/must NOT be the operator's codex home/);
  });

  it("leaves a file-configured subscription run entirely untouched", async () => {
    const auth = await authWithLocalJson({ authMode: "subscription" });
    expect(auth.resolveProviderAuth("anthropic", { env: {} })).toEqual({ mode: "subscription" });
    const env = { PATH: "/usr/bin" } as NodeJS.ProcessEnv;
    expect(auth.workerEnv({ env })).toEqual(env);
  });
});

describe("claudeAuthArgs", () => {
  it("reads the stored OAuth login through user settings in subscription mode", () => {
    expect(claudeAuthArgs("subscription")).toEqual(["--setting-sources", "user"]);
  });

  it("pins api mode to --bare so it can never fall through to the subscription", () => {
    expect(claudeAuthArgs("api")).toEqual(["--bare"]);
  });
});

describe("codexHome", () => {
  it("leaves the operator's codex home alone in subscription mode", () => {
    expect(codexHome({ env: {}, config: {} })).toBe(path.join(os.homedir(), ".codex"));
  });

  it("uses a separate home in api mode so the ChatGPT login is not evicted", () => {
    const home = codexHome({
      env: { CAUSALSMITH_OPENAI_AUTH: "api" },
      config: { openaiApiKey: "sk-x" },
    });
    expect(home).toBe(path.join(os.homedir(), ".codex-causalsmith-api"));
    expect(home).not.toBe(path.join(os.homedir(), ".codex"));
  });

  it("honors a configured api home", () => {
    expect(
      codexHome({
        env: { CAUSALSMITH_OPENAI_AUTH: "api" },
        config: { openaiApiKey: "sk-x", codexApiHome: "/srv/codex-api" },
      }),
    ).toBe("/srv/codex-api");
  });
});

describe("workerEnv", () => {
  it("passes the environment through untouched in subscription mode", () => {
    const env = { PATH: "/usr/bin" } as NodeJS.ProcessEnv;
    const out = workerEnv({ env, config: {} });
    expect(out).toEqual(env);
    expect(out.ANTHROPIC_API_KEY).toBeUndefined();
    expect(out.CODEX_HOME).toBeUndefined();
  });

  it("exports the keys and redirects CODEX_HOME in api mode", () => {
    const out = workerEnv({
      env: { PATH: "/usr/bin" },
      config: { authMode: "api", anthropicApiKey: "sk-ant", openaiApiKey: "sk-oai" },
    });
    expect(out.ANTHROPIC_API_KEY).toBe("sk-ant");
    expect(out.OPENAI_API_KEY).toBe("sk-oai");
    expect(out.CODEX_HOME).toBe(path.join(os.homedir(), ".codex-causalsmith-api"));
    expect(out.PATH).toBe("/usr/bin");
  });

  it("leaves CODEX_HOME alone when only the claude side is on api billing", () => {
    const out = workerEnv({
      env: { PATH: "/usr/bin" },
      config: { anthropicAuth: "api", anthropicApiKey: "sk-ant" },
    });
    expect(out.ANTHROPIC_API_KEY).toBe("sk-ant");
    expect(out.CODEX_HOME).toBeUndefined();
  });
});
