// How the pipeline PAYS for its model calls.
//
// Every model call in this repo goes out through one of two CLIs — `claude`
// (Anthropic) and `codex` (OpenAI) — and both of them, by default, ride on the
// interactive subscription login stored in the operator's home directory
// (`claude` keychain/OAuth; `~/.codex/auth.json`). That is the `subscription`
// mode and remains the default: nothing changes for an operator who does not
// configure anything here.
//
// The alternative is `api` mode: the call is billed to an API key you supply.
// Configure it in `tools/config/local.json` (gitignored — copy from
// `local.example.json`) or via env vars, which always win over the file:
//
//   authMode           "subscription" | "api"   default for BOTH providers
//   anthropicAuth      per-provider override (claude workers)
//   openaiAuth         per-provider override (codex workers)
//   anthropicApiKey    the key itself
//   anthropicApiKeyFile  …or a path to a file holding it (first line)
//   openaiApiKey / openaiApiKeyFile   same, for codex
//   codexApiHome       CODEX_HOME used in api mode (see below)
//
//   CAUSALSMITH_AUTH_MODE, CAUSALSMITH_ANTHROPIC_AUTH, CAUSALSMITH_OPENAI_AUTH,
//   ANTHROPIC_API_KEY, OPENAI_API_KEY, CAUSALSMITH_CODEX_HOME_API
//
// Mixed modes are legitimate and supported: `anthropicAuth: "api"` with
// `openaiAuth: "subscription"` runs the claude workers on an API key while codex
// keeps using the ChatGPT plan.
//
// TWO THINGS THIS MODULE IS CAREFUL ABOUT.
//
// 1. Fail loudly, never silently downgrade. `api` mode with no key throws at
//    startup naming every place a key may live. The failure mode we refuse to
//    ship is a run that quietly bills the subscription because a key was
//    missing — the operator would only find out from an invoice.
//
// 2. Never touch the subscription credentials. `codex` enforces one login
//    method per CODEX_HOME: pointing the SHARED `~/.codex` at api auth makes it
//    DELETE the stored ChatGPT credentials ("API key login is required, but
//    ChatGPT is currently being used. Logging out."). So codex api mode gets its
//    OWN CODEX_HOME (`codexApiHome`, default `~/.codex-causalsmith-api`), leaving
//    `~/.codex` untouched. `claude` needs no such trick: `--bare` restricts that
//    process to ANTHROPIC_API_KEY without disturbing the stored OAuth.

import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { localConfig, type LocalConfig } from "./local_config.js";

export type AuthMode = "subscription" | "api";
export type Provider = "anthropic" | "openai";

/** Resolved auth for one provider. `apiKey` is set only in `api` mode. */
export interface ProviderAuth {
  mode: AuthMode;
  apiKey?: string;
}

export interface AuthResolution {
  anthropic: ProviderAuth;
  openai: ProviderAuth;
}

/** Injectable inputs so the resolution is unit-testable without a real machine. */
export interface AuthInputs {
  env?: NodeJS.ProcessEnv;
  config?: Partial<LocalConfig>;
}

const PROVIDER_SPEC = {
  anthropic: {
    label: "claude (Anthropic)",
    modeEnv: "CAUSALSMITH_ANTHROPIC_AUTH",
    modeField: "anthropicAuth",
    keyEnv: "ANTHROPIC_API_KEY",
    keyField: "anthropicApiKey",
    keyFileField: "anthropicApiKeyFile",
  },
  openai: {
    label: "codex (OpenAI)",
    modeEnv: "CAUSALSMITH_OPENAI_AUTH",
    modeField: "openaiAuth",
    keyEnv: "OPENAI_API_KEY",
    keyField: "openaiApiKey",
    keyFileField: "openaiApiKeyFile",
  },
} as const;

export class AuthConfigError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "AuthConfigError";
  }
}

function parseMode(source: string, value: string): AuthMode {
  const mode = value.trim();
  if (mode === "subscription" || mode === "api") return mode;
  throw new AuthConfigError(
    `${source} must be "subscription" or "api"; got ${JSON.stringify(value)}.`,
  );
}

/**
 * Which billing path THIS provider uses. Precedence, first match wins:
 * per-provider env → global env → per-provider config → global config →
 * `subscription`.
 */
export function resolveAuthMode(provider: Provider, inputs: AuthInputs = {}): AuthMode {
  const env = inputs.env ?? process.env;
  // MUST default to the real config, not `{}`: the dispatchers call this with no
  // arguments, and a `{}` default made `local.json`-configured api mode invisible
  // to them — claude kept its subscription flags while the startup banner claimed
  // `api`, which is precisely the silent-billing failure this module exists to
  // prevent. Tests pass an explicit `config` and are unaffected.
  const config = inputs.config ?? localConfig();
  const spec = PROVIDER_SPEC[provider];
  const perProviderEnv = env[spec.modeEnv]?.trim();
  if (perProviderEnv) return parseMode(spec.modeEnv, perProviderEnv);
  const globalEnv = env.CAUSALSMITH_AUTH_MODE?.trim();
  if (globalEnv) return parseMode("CAUSALSMITH_AUTH_MODE", globalEnv);
  const perProviderFile = (config as Record<string, unknown>)[spec.modeField];
  if (typeof perProviderFile === "string" && perProviderFile.trim()) {
    return parseMode(`local.json ${spec.modeField}`, perProviderFile);
  }
  if (typeof config.authMode === "string" && config.authMode.trim()) {
    return parseMode("local.json authMode", config.authMode);
  }
  return "subscription";
}

/**
 * The API key for this provider, or undefined when none is configured.
 * Precedence: env var → inline `local.json` value → first line of the file named
 * by `<provider>ApiKeyFile`. The file form exists so the secret can live outside
 * the repo tree entirely.
 */
export function resolveApiKey(provider: Provider, inputs: AuthInputs = {}): string | undefined {
  const env = inputs.env ?? process.env;
  // Same reason as `resolveAuthMode`: the no-argument dispatcher calls must see
  // the file, or a file-configured key reads as "no key configured".
  const config = (inputs.config ?? localConfig()) as Record<string, unknown>;
  const spec = PROVIDER_SPEC[provider];
  const fromEnv = env[spec.keyEnv]?.trim();
  if (fromEnv) return fromEnv;
  const inline = config[spec.keyField];
  if (typeof inline === "string" && inline.trim()) return inline.trim();
  const keyFile = config[spec.keyFileField];
  if (typeof keyFile === "string" && keyFile.trim()) {
    const resolved = keyFile.trim().replace(/^~(?=\/|\\|$)/, os.homedir());
    return readKeyFileOnce(resolved, spec.keyFileField);
  }
  return undefined;
}

/**
 * Read a key file at most once per process.
 *
 * `workerEnv()` runs on EVERY worker spawn, so an uncached read meant hundreds
 * of synchronous NFS reads per run — and, worse, made the run's billing depend
 * on the file's contents at each spawn: a transient NFS failure mid-run would
 * abort otherwise-healthy workers, and an edit to the file would silently move
 * later workers onto a different key. Caching pins the whole run to the key it
 * started with, which is also the only auditable behaviour.
 */
const keyFileCache = new Map<string, string>();

function readKeyFileOnce(resolved: string, field: string): string {
  const cached = keyFileCache.get(resolved);
  if (cached !== undefined) return cached;
  let contents: string;
  try {
    contents = fs.readFileSync(resolved, "utf8");
  } catch (err) {
    // why: a silent miss here downgrades the run to subscription billing.
    throw new AuthConfigError(
      `${field} points at ${resolved}, which could not be read: ` +
        `${err instanceof Error ? err.message : String(err)}`,
    );
  }
  const first = contents.split(/\r?\n/).find((line) => line.trim().length > 0);
  if (!first) throw new AuthConfigError(`${field} (${resolved}) is empty.`);
  const key = first.trim();
  keyFileCache.set(resolved, key);
  return key;
}

/** Resolve one provider, refusing `api` mode with no key rather than falling back. */
export function resolveProviderAuth(provider: Provider, inputs: AuthInputs = {}): ProviderAuth {
  const mode = resolveAuthMode(provider, inputs);
  if (mode === "subscription") return { mode };
  const apiKey = resolveApiKey(provider, inputs);
  const spec = PROVIDER_SPEC[provider];
  if (!apiKey) {
    throw new AuthConfigError(
      `Auth mode "api" is selected for ${spec.label}, but no API key is configured. ` +
        `Set one of: env ${spec.keyEnv}; "${spec.keyField}" in tools/config/local.json; ` +
        `or "${spec.keyFileField}" in local.json pointing at a file holding the key. ` +
        `(To go back to the subscription login, unset CAUSALSMITH_AUTH_MODE/${spec.modeEnv} ` +
        `and set "${spec.modeField}": "subscription" — or drop "authMode" — in local.json.)`,
    );
  }
  return { mode, apiKey };
}

/** Both providers at once. Throws on the first misconfigured one. */
export function resolveAuth(inputs: AuthInputs = {}): AuthResolution {
  const withConfig: AuthInputs = { env: inputs.env, config: inputs.config ?? localConfig() };
  return {
    anthropic: resolveProviderAuth("anthropic", withConfig),
    openai: resolveProviderAuth("openai", withConfig),
  };
}

/**
 * CODEX_HOME the codex workers must run against.
 *
 * Subscription mode keeps whatever the operator already uses (`CODEX_HOME` if
 * they set it, else `~/.codex`). API mode uses a SEPARATE home so that codex's
 * one-login-method-per-home rule cannot evict the stored ChatGPT credentials —
 * see this file's header.
 */
export function codexHome(inputs: AuthInputs = {}): string {
  const env = inputs.env ?? process.env;
  const config = inputs.config ?? localConfig();
  if (resolveAuthMode("openai", { env, config }) === "subscription") {
    return env.CODEX_HOME?.trim() || path.join(os.homedir(), ".codex");
  }
  const configured = env.CAUSALSMITH_CODEX_HOME_API?.trim() || config.codexApiHome?.trim();
  const home = (configured || path.join(os.homedir(), ".codex-causalsmith-api")).replace(
    /^~(?=\/|\\|$)/,
    os.homedir(),
  );
  // Refuse the one value that defeats the whole separate-home design. Bootstrapping
  // an api home runs `codex login --with-api-key` in it, and codex evicts a stored
  // ChatGPT login when the method changes — so pointing this at the operator's real
  // codex home would destroy the subscription credentials the split exists to
  // protect. Cheap guard against an unrecoverable misconfiguration.
  const operatorHome = path.join(os.homedir(), ".codex");
  if (path.resolve(home) === path.resolve(operatorHome)) {
    throw new AuthConfigError(
      `codexApiHome must NOT be the operator's codex home (${operatorHome}). ` +
        `Bootstrapping an api home logs into it with an API key, and codex deletes any ` +
        `stored ChatGPT credentials when the login method changes. Point codexApiHome / ` +
        `CAUSALSMITH_CODEX_HOME_API at a separate directory (default ~/.codex-causalsmith-api).`,
    );
  }
  return home;
}

/**
 * Environment for a spawned worker: the current environment plus whatever the
 * resolved auth requires. In api mode this exports the provider key (so the CLI
 * sees it even when the operator's shell never did) and, for codex, redirects
 * CODEX_HOME. In subscription mode it is `process.env` unchanged.
 *
 * Both keys are exported whenever they are configured, regardless of which
 * worker is being spawned: the child CLIs ignore the other provider's key.
 */
export function workerEnv(inputs: AuthInputs = {}): NodeJS.ProcessEnv {
  const env = inputs.env ?? process.env;
  const config = inputs.config ?? localConfig();
  const auth = resolveAuth({ env, config });
  const out: NodeJS.ProcessEnv = { ...env };
  if (auth.anthropic.apiKey) out.ANTHROPIC_API_KEY = auth.anthropic.apiKey;
  if (auth.openai.apiKey) {
    out.OPENAI_API_KEY = auth.openai.apiKey;
    out.CODEX_HOME = codexHome({ env, config });
  }
  return out;
}

/**
 * Inject the resolved auth into THIS process's environment at CLI startup, so
 * every worker spawned later inherits it and any misconfiguration (api mode, no
 * key) fails before a run begins rather than at the first dispatch. Idempotent.
 * The dispatchers still call `workerEnv()` themselves, which covers the `bin/`
 * entry points that never route through `src/cli.ts`.
 */
export function applyAuthEnv(): void {
  const resolved = workerEnv();
  for (const key of ["ANTHROPIC_API_KEY", "OPENAI_API_KEY", "CODEX_HOME"] as const) {
    const value = resolved[key];
    if (value) process.env[key] = value;
  }
}

/**
 * Scrub any configured API key out of text bound for a log or an error message.
 *
 * The dispatchers hand the key to their children through `workerEnv()`, and a
 * failing child's stdout/stderr is embedded verbatim in `CodexRunError` /
 * `ClaudeRunError` — which is what lands in `doc/research/_agent_logs/`. A CLI
 * that echoes a rejected credential in its diagnostic would persist it there.
 * Never throws: it runs on error paths, where a misconfiguration must not mask
 * the original failure.
 */
export function redactSecrets(text: string, inputs: AuthInputs = {}): string {
  if (!text) return text;
  let out = text;
  for (const provider of ["anthropic", "openai"] as const) {
    let key: string | undefined;
    try {
      key = resolveApiKey(provider, inputs);
    } catch {
      continue;
    }
    // Short values would blanket-replace innocuous substrings; real keys are long.
    if (key && key.length >= 8) out = out.split(key).join("***");
  }
  return out;
}

/** One-line, secret-free description for run logs / heartbeats. */
export function authSummary(inputs: AuthInputs = {}): string {
  const auth = resolveAuth(inputs);
  return `claude=${auth.anthropic.mode} codex=${auth.openai.mode}`;
}
