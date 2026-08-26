// The comments worker's attestation endpoints, exercised through its real
// `fetch` entry point against a fake KV namespace and a stubbed GitHub.
//
// The property under test throughout: an attestation is keyed by the login the
// WORKER resolves from the caller's token, never by anything the client says.
// A reader can create and withdraw their own mark and nobody else's.

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import worker from "../comments-worker/worker.js";

const ORIGIN = "https://jiyuan-tan.github.io";
const PAPER = "stat_discrete_ate_v1";

/** Minimal in-memory stand-in for a Workers KV namespace. */
function fakeKv() {
  const store = new Map<string, string>();
  return {
    store,
    async get(key: string, type?: string) {
      const raw = store.get(key);
      if (raw === undefined) return null;
      return type === "json" ? JSON.parse(raw) : raw;
    },
    async put(key: string, value: string) {
      store.set(key, value);
    },
    async delete(key: string) {
      store.delete(key);
    },
    async list({ prefix = "", limit = 1000 }: { prefix?: string; limit?: number }) {
      const keys = [...store.keys()]
        .filter((k) => k.startsWith(prefix))
        .sort()
        .slice(0, limit)
        .map((name) => ({ name }));
      return { keys, list_complete: true };
    },
  };
}

type Kv = ReturnType<typeof fakeKv>;
type Env = Record<string, unknown> & { ATTESTATIONS?: Kv };

function makeEnv(extra: Env = {}): Env {
  return {
    ALLOWED_ORIGINS: ORIGIN,
    ATTESTATIONS: fakeKv(),
    ...extra,
  };
}

const ctx = { waitUntil: (p: unknown) => void p };

function call(env: Env, path: string, init: RequestInit = {}) {
  const headers = new Headers(init.headers);
  if (!headers.has("Origin")) headers.set("Origin", ORIGIN);
  return worker.fetch(
    new Request(`https://worker.example.workers.dev${path}`, { ...init, headers }),
    env,
    ctx,
  );
}

const post = (env: Env, token: string, body: unknown, init: RequestInit = {}) =>
  call(env, "/api/attestations", {
    method: "POST",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json", ...(init.headers as Record<string, string>) },
    body: JSON.stringify(body),
    ...init,
  });

const del = (env: Env, token: string, body: unknown) =>
  call(env, "/api/attestations", {
    method: "DELETE",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });

const list = (env: Env, paper = PAPER) =>
  call(env, `/api/attestations?paper=${encodeURIComponent(paper)}`);

/** GitHub `/user`: a token of the form `tok-<login>` authenticates that login. */
function stubGithub() {
  vi.stubGlobal(
    "fetch",
    vi.fn(async (input: string, init?: RequestInit) => {
      const url = String(input);
      if (url !== "https://api.github.com/user") return new Response("{}", { status: 404 });
      const auth = String(new Headers(init?.headers).get("Authorization") ?? "");
      const m = /^Bearer tok-([a-z0-9-]+)$/.exec(auth);
      if (!m) return new Response(JSON.stringify({ message: "Bad credentials" }), { status: 401 });
      return new Response(
        JSON.stringify({
          login: m[1],
          avatar_url: `https://avatars.githubusercontent.com/u/${m[1].length}?v=4`,
        }),
        { status: 200 },
      );
    }),
  );
}

beforeEach(stubGithub);
afterEach(() => vi.unstubAllGlobals());

describe("GET /api/attestations", () => {
  it("returns an empty list for a paper nobody has verified", async () => {
    const res = await list(makeEnv());
    expect(res.status).toBe(200);
    await expect(res.json()).resolves.toEqual({ paper: PAPER, attestations: [] });
    expect(res.headers.get("Access-Control-Allow-Origin")).toBe(ORIGIN);
  });

  it("rejects a bad paper id", async () => {
    const res = await call(makeEnv(), "/api/attestations?paper=../../etc/passwd");
    expect(res.status).toBe(400);
  });

  it("answers 501 when no KV namespace is bound (feature not deployed)", async () => {
    const res = await list({ ALLOWED_ORIGINS: ORIGIN });
    expect(res.status).toBe(501);
    await expect(res.json()).resolves.toMatchObject({ error: expect.stringMatching(/configured/) });
  });

  it("hands a disallowed origin no CORS grant", async () => {
    const res = await call(makeEnv(), `/api/attestations?paper=${PAPER}`, {
      headers: { Origin: "https://evil.example" },
    });
    expect(res.headers.get("Access-Control-Allow-Origin")).toBeNull();
  });

  it("answers the preflight with the write methods", async () => {
    const res = await call(makeEnv(), "/api/attestations", { method: "OPTIONS" });
    expect(res.headers.get("Access-Control-Allow-Methods")).toContain("DELETE");
    expect(res.headers.get("Access-Control-Allow-Headers")).toContain("Authorization");
  });

  it("refuses an unsupported method", async () => {
    const res = await call(makeEnv(), "/api/attestations", { method: "PUT" });
    expect(res.status).toBe(405);
    expect(res.headers.get("Allow")).toContain("POST");
  });
});

describe("POST /api/attestations", () => {
  it("records a mark under the login GitHub reports, not one the client claims", async () => {
    const env = makeEnv();
    const res = await post(env, "tok-saskia-v", {
      paper: PAPER,
      objId: "lem:pilot-sandwich",
      login: "impersonated", // ignored: the worker never reads an identity off the body
    });
    expect(res.status).toBe(200);
    await expect(res.json()).resolves.toMatchObject({
      ok: true,
      objId: "lem:pilot-sandwich",
      login: "saskia-v",
    });
    const body = (await (await list(env)).json()) as { attestations: unknown[] };
    expect(body.attestations).toEqual([
      {
        objId: "lem:pilot-sandwich",
        login: "saskia-v",
        avatarUrl: expect.stringContaining("https://avatars.githubusercontent.com/"),
        at: expect.stringMatching(/^\d{4}-/),
      },
    ]);
  });

  it("is idempotent: re-posting keeps the original timestamp and one entry", async () => {
    const env = makeEnv();
    const first = (await (await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" })).json()) as {
      at: string;
    };
    await new Promise((r) => setTimeout(r, 2));
    const second = (await (await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" })).json()) as {
      at: string;
    };
    expect(second.at).toBe(first.at);
    const body = (await (await list(env)).json()) as { attestations: unknown[] };
    expect(body.attestations).toHaveLength(1);
  });

  it("refuses an unauthenticated or rejected token", async () => {
    const env = makeEnv();
    const anon = await call(env, "/api/attestations", {
      method: "POST",
      body: JSON.stringify({ paper: PAPER, objId: "lem:a" }),
    });
    expect(anon.status).toBe(401);
    const bad = await post(env, "not-a-real-token", { paper: PAPER, objId: "lem:a" });
    expect(bad.status).toBe(401);
    expect(env.ATTESTATIONS!.store.size).toBe(0);
  });

  it("refuses a malformed body", async () => {
    const env = makeEnv();
    for (const body of [{}, { paper: PAPER }, { paper: "..", objId: "lem:a" }, { paper: PAPER, objId: "a b" }]) {
      expect((await post(env, "tok-saskia-v", body)).status).toBe(400);
    }
    expect(env.ATTESTATIONS!.store.size).toBe(0);
  });

  it("refuses a write from an origin outside the allowlist", async () => {
    const env = makeEnv();
    const res = await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" }, {
      headers: { Origin: "https://evil.example" },
    });
    expect(res.status).toBe(403);
    expect(env.ATTESTATIONS!.store.size).toBe(0);
  });

  it("refuses a blocklisted login and hides any mark it already left", async () => {
    const env = makeEnv();
    await post(env, "tok-spammer", { paper: PAPER, objId: "lem:a" });
    const muted = makeEnv({ ATTEST_BLOCKLIST: "Spammer, someone-else" });
    muted.ATTESTATIONS = env.ATTESTATIONS;
    expect((await post(muted, "tok-spammer", { paper: PAPER, objId: "lem:b" })).status).toBe(403);
    const body = (await (await list(muted)).json()) as { attestations: unknown[] };
    expect(body.attestations).toEqual([]);
  });
});

describe("DELETE /api/attestations", () => {
  it("withdraws the caller's own mark and nobody else's", async () => {
    const env = makeEnv();
    await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" });
    await post(env, "tok-m-oberst", { paper: PAPER, objId: "lem:a" });
    await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:b" });

    const res = await del(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" });
    expect(res.status).toBe(200);
    const body = (await (await list(env)).json()) as {
      attestations: { objId: string; login: string }[];
    };
    expect(body.attestations.map((a) => `${a.login}/${a.objId}`).sort()).toEqual([
      "m-oberst/lem:a",
      "saskia-v/lem:b",
    ]);
  });

  it("drops the reader's key entirely once their last mark is withdrawn", async () => {
    const env = makeEnv();
    await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" });
    expect([...env.ATTESTATIONS!.store.keys()]).toEqual([
      `att:${PAPER}:saskia-v`,
    ]);
    await del(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" });
    expect(env.ATTESTATIONS!.store.size).toBe(0);
  });

  it("is a no-op on a mark that was never made", async () => {
    const env = makeEnv();
    expect((await del(env, "tok-saskia-v", { paper: PAPER, objId: "lem:ghost" })).status).toBe(200);
    expect(env.ATTESTATIONS!.store.size).toBe(0);
  });
});

describe("attestations are scoped to one paper", () => {
  it("a mark on one paper never shows on another", async () => {
    const env = makeEnv();
    await post(env, "tok-saskia-v", { paper: PAPER, objId: "lem:a" });
    await post(env, "tok-saskia-v", { paper: "other_paper_v1", objId: "lem:a" });
    const here = (await (await list(env)).json()) as { attestations: unknown[] };
    const there = (await (await list(env, "other_paper_v1")).json()) as { attestations: unknown[] };
    expect(here.attestations).toHaveLength(1);
    expect(there.attestations).toHaveLength(1);
    expect(env.ATTESTATIONS!.store.size).toBe(2);
  });
});
