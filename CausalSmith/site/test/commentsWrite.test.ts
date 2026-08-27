// The comments worker's comment endpoints, exercised through its real `fetch`
// entry point against a fake KV namespace and a stubbed GitHub.
//
// The property under test throughout, and the reason the storage moved off
// GitHub Discussions: a comment is attributed to the login the WORKER resolves
// from the caller's token, and lives in that author's own record — so "may I
// delete this?" is answered by which key the item is in, not by trusting
// anything in the request. Nobody holds a credential that can write anywhere.

import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import worker from "../comments-worker/worker.js";

const ORIGIN = "https://jiyuan-tan.github.io";
const PAPER = "stat_discrete_ate_v1";

const IDS: Record<string, number> = {
  maintainer: 900002,
  alice: 100001,
  bob: 100002,
  mallory: 666666,
  spammer: 666667,
  stranger: 666668,
};
const idOf = (login: string) => IDS[login] ?? 999999;

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
    // Paginates and HONOURS `limit`, like the real one. A double that ignores
    // the caller's limit will happily prove that a cursor loop iterates when
    // against real KV it never does — which is exactly how a broken listing
    // fix passed its own regression tests.
    async list({
      prefix = "",
      limit = 1000,
      cursor,
    }: {
      prefix?: string;
      limit?: number;
      cursor?: string;
    }) {
      const all = [...store.keys()].filter((k) => k.startsWith(prefix)).sort();
      const start = cursor ? Number(cursor) : 0;
      const page = all.slice(start, start + limit);
      const end = start + page.length;
      const complete = end >= all.length;
      return {
        keys: page.map((name) => ({ name })),
        list_complete: complete,
        cursor: complete ? undefined : String(end),
      };
    },
  };
}

type Kv = ReturnType<typeof fakeKv>;
type Env = Record<string, unknown> & { COMMENTS?: Kv };

const ctx = { waitUntil: (p: unknown) => void p };

function makeEnv(extra: Env = {}): Env {
  return {
    ALLOWED_ORIGINS: ORIGIN,
    COMMENTS: fakeKv(),
    COMMENT_MODERATOR_IDS: String(IDS.maintainer),
    ...extra,
  };
}

/**
 * Stub api.github.com's `/user`: the token string IS the login, which keeps the
 * tests readable. Nothing else is ever called — the worker no longer talks to
 * GitHub for storage at all, and a request to any other URL fails the test.
 */
function stubGithub() {
  vi.stubGlobal("fetch", async (input: any, init: any = {}) => {
    const url = String(input);
    if (url === "https://api.github.com/user") {
      const token = String(init.headers?.Authorization ?? "").replace(/^Bearer\s+/, "");
      if (!token || token === "bad-token") return new Response("no", { status: 401 });
      return Response.json({
        login: token,
        id: idOf(token),
        avatar_url: `https://avatars.githubusercontent.com/u/${idOf(token)}`,
      });
    }
    throw new Error(`unexpected fetch: ${url}`);
  });
}

beforeEach(stubGithub);
afterEach(() => vi.unstubAllGlobals());

function call(env: Env, method: string, token: string, body: unknown) {
  const headers: Record<string, string> = { Origin: ORIGIN, "Content-Type": "application/json" };
  if (token) headers.Authorization = `Bearer ${token}`;
  return worker.fetch(
    new Request("https://worker.example.workers.dev/api/comments", {
      method,
      headers,
      body: JSON.stringify(body),
    }),
    env,
    ctx,
  );
}

const post = (env: Env, token: string, body: Record<string, unknown> = {}) =>
  call(env, "POST", token, { paper: PAPER, text: "a comment", ...body });

const del = (env: Env, token: string, body: Record<string, unknown>) =>
  call(env, "DELETE", token, { paper: PAPER, ...body });

async function read(env: Env, paper = PAPER) {
  const res = await worker.fetch(
    new Request(`https://worker.example.workers.dev/api/comments?paper=${paper}`, {
      headers: { Origin: ORIGIN },
    }),
    env,
    ctx,
  );
  return {
    status: res.status,
    body: (await res.json()) as { comments: any[]; truncated?: boolean },
  };
}

/** Post and return the new item's id. */
async function postId(env: Env, token: string, body: Record<string, unknown> = {}) {
  const res = await post(env, token, body);
  expect(res.status).toBe(200);
  return (await res.json()).id as string;
}

describe("posting a comment", () => {
  it("attributes it to the login resolved from the token, never to the request", async () => {
    const env = makeEnv();
    // The client names someone else, in every field it could hope to be believed on.
    const res = await post(env, "alice", {
      author: "famous-professor",
      login: "famous-professor",
      text: "Looks right to me.",
    });
    expect(res.status).toBe(200);
    expect(await res.json()).toMatchObject({ login: "alice" });

    const { body } = await read(env);
    expect(body.comments).toHaveLength(1);
    expect(body.comments[0].author.login).toBe("alice");
    expect(body.comments[0].text).toBe("Looks right to me.");
  });

  it("stores it under the author's own key and nobody else's", async () => {
    const env = makeEnv();
    await post(env, "alice");
    await post(env, "bob");
    expect([...env.COMMENTS!.store.keys()].sort()).toEqual(
      [`cmt:${PAPER}:${IDS.alice}`, `cmt:${PAPER}:${IDS.bob}`].sort(),
    );
  });

  it("keeps the tag, anchor and revision, and mints its own id", async () => {
    const env = makeEnv();
    const anchor = { exact: "the estimator is consistent", prefix: "so ", suffix: " here", count: 2 };
    const id = await postId(env, "bob", {
      tag: "problem",
      anchor,
      revision: "d2bf655",
      text: "Anchored remark.",
    });
    const { body } = await read(env);
    expect(body.comments[0]).toMatchObject({ id, tag: "problem", anchor, revision: "d2bf655" });
    // Ids are minted server-side; a client cannot choose one.
    expect(id).toMatch(/^[0-9a-f]{24}$/);
  });

  it("degrades an unrecognized tag rather than storing it", async () => {
    const env = makeEnv();
    await post(env, "alice", { tag: "endorsed-by-editor" });
    expect((await read(env)).body.comments[0].tag).toBe("none");
  });

  it("ignores a client-supplied id", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice", { id: "aaaaaaaaaaaaaaaaaaaaaaaa" });
    expect(id).not.toBe("aaaaaaaaaaaaaaaaaaaaaaaa");
  });

  it("bounds a hostile anchor instead of storing it whole", async () => {
    const env = makeEnv();
    await post(env, "alice", {
      anchor: { exact: "x".repeat(5000), prefix: "p".repeat(5000), suffix: "", count: 1e9 },
    });
    const a = (await read(env)).body.comments[0].anchor;
    expect(a.exact.length).toBe(400);
    expect(a.prefix.length).toBe(200);
    expect(a.count).toBeLessThanOrEqual(8);
  });

  it("keeps each paper's comments to itself", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "on paper one" });
    await call(env, "POST", "alice", { paper: "another_paper_v1", text: "on paper two" });
    expect((await read(env)).body.comments.map((c) => c.text)).toEqual(["on paper one"]);
    expect((await read(env, "another_paper_v1")).body.comments.map((c) => c.text)).toEqual([
      "on paper two",
    ]);
  });
});

describe("replies", () => {
  it("nests under the parent and carries its own author", async () => {
    const env = makeEnv();
    const parent = await postId(env, "alice", { text: "parent" });
    await post(env, "bob", { parentId: parent, text: "a reply" });

    const { comments } = (await read(env)).body;
    expect(comments).toHaveLength(1);
    expect(comments[0].replies).toHaveLength(1);
    expect(comments[0].replies[0]).toMatchObject({ text: "a reply" });
    expect(comments[0].replies[0].author.login).toBe("bob");
  });

  it("lives in the replier's own record, not the parent author's", async () => {
    const env = makeEnv();
    const parent = await postId(env, "alice", { text: "parent" });
    await post(env, "bob", { parentId: parent, text: "a reply" });
    const alice = JSON.parse(env.COMMENTS!.store.get(`cmt:${PAPER}:${IDS.alice}`)!);
    expect(alice.items).toHaveLength(1);
    expect(alice.items[0].text).toBe("parent");
  });

  it("carries no tag or anchor of its own", async () => {
    const env = makeEnv();
    const parent = await postId(env, "alice", { text: "parent" });
    await post(env, "bob", {
      parentId: parent,
      text: "a reply",
      tag: "verified",
      anchor: { exact: "mine now", prefix: "", suffix: "", count: 1 },
    });
    const reply = (await read(env)).body.comments[0].replies[0];
    expect(reply).not.toHaveProperty("tag");
    expect(reply).not.toHaveProperty("anchor");
  });

  it("survives its parent's deletion as a page-level comment", async () => {
    // Hiding it was worse in both directions: its author could neither see nor
    // delete something that still consumed their quota, and the server-side
    // sweep that would have reclaimed it had to scan the paper on the rejection
    // path — which both amplified a refused write into ~1000 KV reads and, on
    // an incomplete scan, deleted replies whose parents were alive.
    const env = makeEnv();
    const parent = await postId(env, "alice", { text: "parent" });
    await post(env, "bob", { parentId: parent, text: "a reply" });
    expect((await del(env, "alice", { id: parent })).status).toBe(200);

    const { comments } = (await read(env)).body;
    expect(comments).toHaveLength(1);
    expect(comments[0]).toMatchObject({ text: "a reply", tag: "none", anchor: null });
    expect(comments[0].author.login).toBe("bob");
    // Promotion must not let a reply claim anything an ordinary comment could not.
    expect(comments[0].replies).toEqual([]);
  });

  it("400s a malformed parent id", async () => {
    const env = makeEnv();
    expect((await post(env, "alice", { parentId: "../../etc" })).status).toBe(400);
  });
});

describe("posting is refused when it should be", () => {
  it("401s without a token", async () => {
    expect((await call(makeEnv(), "POST", "", { paper: PAPER, text: "hi" })).status).toBe(401);
  });

  it("401s on a token GitHub rejects", async () => {
    expect((await post(makeEnv(), "bad-token")).status).toBe(401);
  });

  it("403s a muted login, and stores nothing", async () => {
    const env = makeEnv({ MUTED_LOGINS: "spammer" });
    expect((await post(env, "spammer")).status).toBe(403);
    expect(env.COMMENTS!.store.size).toBe(0);
  });

  it("still honours the older ATTEST_BLOCKLIST name", async () => {
    expect((await post(makeEnv({ ATTEST_BLOCKLIST: "spammer" }), "spammer")).status).toBe(403);
  });

  it("403s a disallowed origin", async () => {
    const res = await worker.fetch(
      new Request("https://worker.example.workers.dev/api/comments", {
        method: "POST",
        headers: { Origin: "https://evil.example", Authorization: "Bearer alice" },
        body: JSON.stringify({ paper: PAPER, text: "hi" }),
      }),
      makeEnv(),
      ctx,
    );
    expect(res.status).toBe(403);
  });

  it("400s an empty or oversized comment", async () => {
    const env = makeEnv();
    expect((await post(env, "alice", { text: "   " })).status).toBe(400);
    expect((await post(env, "alice", { text: "x".repeat(20000) })).status).toBe(400);
  });

  it("400s a bad paper id", async () => {
    expect((await call(makeEnv(), "POST", "alice", { paper: "../etc", text: "hi" })).status).toBe(
      400,
    );
  });

  it("429s past the per-author cap for one paper", async () => {
    const env = makeEnv();
    const items = Array.from({ length: 200 }, (_, i) => ({ id: `${i}`, at: "", text: "x" }));
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${IDS.alice}`,
      JSON.stringify({ login: "alice", avatarUrl: null, items }),
    );
    expect((await post(env, "alice")).status).toBe(429);
  });

  it("501s when no comment store is configured", async () => {
    const env = makeEnv();
    delete env.COMMENTS;
    expect((await post(env, "alice")).status).toBe(501);
  });
});

describe("deleting a comment", () => {
  it("lets the author delete their own", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice");
    expect((await del(env, "alice", { id })).status).toBe(200);
    expect((await read(env)).body.comments).toEqual([]);
  });

  it("removes the author's record entirely once nothing is left", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice");
    await del(env, "alice", { id });
    expect(env.COMMENTS!.store.has(`cmt:${PAPER}:${IDS.alice}`)).toBe(false);
  });

  it("keeps the author's other comments", async () => {
    const env = makeEnv();
    const first = await postId(env, "alice", { text: "first" });
    await post(env, "alice", { text: "second" });
    await del(env, "alice", { id: first });
    expect((await read(env)).body.comments.map((c) => c.text)).toEqual(["second"]);
  });

  it("refuses someone else's, even naming their record explicitly", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice");
    expect((await del(env, "bob", { id, authorId: IDS.alice })).status).toBe(403);
    expect((await read(env)).body.comments).toHaveLength(1);
  });

  it("cannot delete another author's comment by id alone", async () => {
    // Without `author` the request addresses the CALLER's own record, so an id
    // belonging to someone else simply is not there.
    const env = makeEnv();
    const id = await postId(env, "alice");
    expect((await del(env, "bob", { id })).status).toBe(404);
  });

  it("lets a moderator delete anyone's, by id", async () => {
    const env = makeEnv({ COMMENT_MODERATOR_IDS: String(IDS.maintainer) });
    const id = await postId(env, "alice");
    expect((await del(env, "maintainer", { id, authorId: IDS.alice })).status).toBe(200);
  });

  it("lets a moderator delete anyone's, by login when no ids are configured", async () => {
    // `Number("")` is 0, so an unset id list once parsed as `[0]` and this
    // fallback never fired.
    const env = makeEnv({ COMMENT_MODERATORS: "maintainer" });
    delete (env as Record<string, unknown>).COMMENT_MODERATOR_IDS;
    const id = await postId(env, "alice");
    expect((await del(env, "maintainer", { id, authorId: IDS.alice })).status).toBe(200);
  });

  it("refuses a login-squatting ex-moderator when ids are configured", async () => {
    const env = makeEnv({ COMMENT_MODERATOR_IDS: String(IDS.maintainer) });
    const id = await postId(env, "alice");
    expect((await del(env, "stranger", { id, authorId: IDS.alice })).status).toBe(403);
  });

  it("404s an id that is not there", async () => {
    const env = makeEnv();
    await postId(env, "alice");
    expect((await del(env, "alice", { id: "0".repeat(24) })).status).toBe(404);
  });

  it("400s a malformed id", async () => {
    expect((await del(makeEnv(), "alice", { id: "../../etc/passwd" })).status).toBe(400);
  });
});

describe("a reused GitHub username inherits nothing", () => {
  // GitHub frees a username the moment an account is renamed or deleted, and
  // anyone may register it next. Keyed on the login, that new person would
  // inherit every comment the previous holder wrote — including their ✅
  // Verified tags — and be able to delete them. Records are keyed on the
  // immutable numeric id instead.
  /** Same login as `alice`, different account. */
  function squatter(env: Env) {
    vi.stubGlobal("fetch", async (input: any, init: any = {}) => {
      const token = String(init.headers?.Authorization ?? "").replace(/^Bearer\s+/, "");
      if (String(input) !== "https://api.github.com/user") throw new Error("unexpected fetch");
      const id = token === "alice" ? 424242 : idOf(token); // "alice" is now someone else
      return Response.json({
        login: "alice",
        id,
        avatar_url: `https://avatars.githubusercontent.com/u/${id}`,
      });
    });
    return env;
  }

  it("does not re-attribute the original author's comments", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "I verified Theorem 3.", tag: "verified" });
    squatter(env);
    await post(env, "alice", { text: "…and the estimator is fine." });

    const { comments } = (await read(env)).body;
    const verified = comments.find((c) => c.text === "I verified Theorem 3.")!;
    // The original claim keeps the ORIGINAL account's avatar, not the squatter's.
    expect(verified.author.avatarUrl).toBe(`https://avatars.githubusercontent.com/u/${IDS.alice}`);
    expect(comments).toHaveLength(2);
  });

  it("does not let the new holder delete the old holder's comments", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice", { text: "I verified Theorem 3." });
    squatter(env);
    expect((await del(env, "alice", { id })).status).toBe(404);
    expect((await read(env)).body.comments).toHaveLength(1);
  });

  it("refuses a token whose account has no numeric id", async () => {
    // No id, no identity — never a silent fall back to the login.
    const env = makeEnv();
    vi.stubGlobal("fetch", async () => Response.json({ login: "alice" }));
    expect((await post(env, "alice")).status).toBe(401);
  });
});

describe("a storage read that fails is not a storage read that found nothing", () => {
  /** A KV whose `get` throws, as a transient Cloudflare 5xx would. */
  function breakGet(env: Env) {
    const kv = env.COMMENTS!;
    const real = kv.get.bind(kv);
    kv.get = async () => {
      throw new Error("KV unavailable");
    };
    return () => {
      kv.get = real;
    };
  }

  it("refuses the write rather than overwriting the author's record", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "first" });
    await post(env, "alice", { text: "second" });

    const restore = breakGet(env);
    const res = await post(env, "alice", { text: "posted during a KV blip" });
    expect(res.status).toBe(503);
    restore();

    // Both originals survive, and the blip's comment was never stored.
    expect((await read(env)).body.comments.map((c) => c.text)).toEqual(["first", "second"]);
  });

  it("cannot be used to bypass the per-author cap", async () => {
    const env = makeEnv();
    const items = Array.from({ length: 200 }, (_, i) => ({ id: `${i}`, at: "", text: "x" }));
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${IDS.alice}`,
      JSON.stringify({ login: "alice", avatarUrl: null, items }),
    );
    expect((await post(env, "alice")).status).toBe(429);
    const restore = breakGet(env);
    expect((await post(env, "alice")).status).toBe(503);
    restore();
  });

  it("refuses a delete rather than reporting nothing to delete", async () => {
    const env = makeEnv();
    const id = await postId(env, "alice");
    const restore = breakGet(env);
    expect((await del(env, "alice", { id })).status).toBe(503);
    restore();
    expect((await read(env)).body.comments).toHaveLength(1);
  });
});

describe("resource budgets", () => {
  it("refuses a paper the site does not publish, when a list is configured", async () => {
    // Without this one account can mint unlimited KV keys under invented paper
    // ids and burn the day's write quota, taking the whole store down.
    const env = makeEnv({ PAPERS: `${PAPER},panel_ppml_forbidden_comparison_v1` });
    expect((await post(env, "alice")).status).toBe(200);
    expect((await call(env, "POST", "alice", { paper: "invented_v1", text: "hi" })).status).toBe(
      404,
    );
  });

  it("accepts any paper when no list is configured", async () => {
    const env = makeEnv();
    expect((await call(env, "POST", "alice", { paper: "anything_v1", text: "hi" })).status).toBe(
      200,
    );
  });

  it("caps what one thread will serve, and says when it truncated", async () => {
    const env = makeEnv();
    const items = Array.from({ length: 60 }, (_, i) => ({
      id: `${i}`.padStart(24, "0"),
      at: `2026-08-2${i % 9}T00:00:00Z`,
      text: "x".repeat(10000),
    }));
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${IDS.alice}`,
      JSON.stringify({ login: "alice", avatarUrl: null, items }),
    );
    const { body } = await read(env);
    expect(body.truncated).toBe(true);
    expect(body.comments.length).toBeLessThan(60);
    const served = body.comments.reduce((n, c) => n + c.text.length, 0);
    expect(served).toBeLessThanOrEqual(400000);
  });
});

describe("no author can crowd another out of the thread", () => {
  /** Seed a record directly, so we can choose the account id (= sort order). */
  async function seed(env: Env, id: number, login: string, texts: string[]) {
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${id}`,
      JSON.stringify({
        login,
        avatarUrl: null,
        items: texts.map((text, i) => ({
          id: `${id}${i}`.padStart(24, "0"),
          at: `2026-08-20T00:00:0${i}Z`,
          text,
        })),
      }),
    );
  }

  it("does not let a low-sorting account erase everyone else", async () => {
    // KV lists by key, keys are numeric ids compared as STRINGS, and GitHub ids
    // are public — so an attacker can pick an account that sorts ahead of the
    // person they want silenced. Spending the thread budget in list order made
    // that a censorship primitive costing one account and forty writes.
    const env = makeEnv();
    await seed(env, 100000001, "attacker", Array.from({ length: 40 }, () => "x".repeat(10000)));
    await seed(env, 17078473, "maintainer", ["the maintainer's reply"]);
    await seed(env, 966666666, "reader", ["a reader's question"]);

    const { comments } = (await read(env)).body;
    const logins = new Set(comments.map((c) => c.author.login));
    expect(logins.has("maintainer")).toBe(true);
    expect(logins.has("reader")).toBe(true);
    expect(comments.find((c) => c.author.login === "maintainer")!.text).toBe(
      "the maintainer's reply",
    );
  });

  it("still bounds what one author contributes, and says it truncated", async () => {
    const env = makeEnv();
    await seed(env, 100000001, "verbose", Array.from({ length: 40 }, () => "x".repeat(10000)));
    const { body } = await read(env);
    expect(body.truncated).toBe(true);
    const served = body.comments.reduce((n, c) => n + c.text.length, 0);
    expect(served).toBeLessThanOrEqual(40000);
  });

  it("skips a pre-migration login-keyed record rather than serving it", async () => {
    // Such a record cannot be addressed by any delete (which requires a numeric
    // id), so rendering it would create permanent unmoderatable content.
    const env = makeEnv();
    await env.COMMENTS!.put(
      `cmt:${PAPER}:alice`,
      JSON.stringify({
        login: "alice",
        avatarUrl: null,
        items: [{ id: "a".repeat(24), at: "2026-08-20T00:00:00Z", text: "legacy" }],
      }),
    );
    expect((await read(env)).body.comments).toEqual([]);
  });
});

describe("the render budget cannot be shrunk or gamed", () => {
  async function seedMany(env: Env, count: number, chars: number, startId = 200000000) {
    for (let i = 0; i < count; i++) {
      await env.COMMENTS!.put(
        `cmt:${PAPER}:${startId + i}`,
        JSON.stringify({
          login: `sock${i}`,
          avatarUrl: null,
          items: [{ id: `${i}`.padStart(24, "0"), at: "2026-08-20T00:00:00Z", text: "x".repeat(chars) }],
        }),
      );
    }
  }

  it("never rations an author below one comment's length", async () => {
    // Below MAX_TEXT_CHARS the composer would accept comments the reader could
    // never show, and one maximum-length post would pin the truncation notice.
    const env = makeEnv();
    await seedMany(env, 60, 100);
    await env.COMMENTS!.put(
      `cmt:${PAPER}:17078473`,
      JSON.stringify({
        login: "maintainer",
        avatarUrl: null,
        items: [{ id: "m".repeat(24), at: "2026-08-20T00:00:00Z", text: "y".repeat(10000) }],
      }),
    );
    const { body } = await read(env);
    const mine = body.comments.find((c) => c.author.login === "maintainer");
    expect(mine?.text).toHaveLength(10000);
    expect(body.truncated).toBe(false);
  });

  it("restores everyone's share when the sock accounts are muted", async () => {
    // The divisor must count authors SERVED, not fetched — otherwise muting an
    // attacker leaves their suppression in place and moderation is inert.
    const env = makeEnv();
    await seedMany(env, 60, 100);
    const mutedIds = Array.from({ length: 60 }, (_, i) => 200000000 + i).join(",");
    const muted = { ...env, MUTED_IDS: mutedIds };
    const { body } = await read(muted);
    expect(body.comments).toEqual([]);
    // …and a real author now gets the full single-author share. Four maximum
    // length comments, since one item is capped at MAX_TEXT_CHARS on the way in
    // and on the way out.
    await env.COMMENTS!.put(
      `cmt:${PAPER}:17078473`,
      JSON.stringify({
        login: "maintainer",
        avatarUrl: null,
        items: Array.from({ length: 4 }, (_, i) => ({
          id: `m${i}`.padStart(24, "0"),
          at: `2026-08-20T00:00:0${i}Z`,
          text: "y".repeat(10000),
        })),
      }),
    );
    const after = (await read({ ...env, MUTED_IDS: mutedIds })).body;
    expect(after.comments.reduce((n, c) => n + c.text.length, 0)).toBe(40000);
    expect(after.truncated).toBe(false);
  });

  it("caps what one author can STORE, so a read can never fan out unbounded", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "x".repeat(10000) });
    await post(env, "alice", { text: "x".repeat(10000) });
    await post(env, "alice", { text: "x".repeat(10000) });
    await post(env, "alice", { text: "x".repeat(10000) });
    const res = await post(env, "alice", { text: "x".repeat(10000) });
    expect(res.status).toBe(429);
    expect((await res.json()).error).toMatch(/space used up/);
  });

  it("reports truncation when a record cannot be read, instead of claiming nothing was withheld", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "alice is here" });
    await post(env, "bob", { text: "bob is here" });
    const kv = env.COMMENTS!;
    const real = kv.get.bind(kv);
    kv.get = async (key: string, type?: string) => {
      if (key.endsWith(String(IDS.bob))) throw new Error("KV unavailable");
      return real(key, type);
    };
    const { body } = await read(env);
    expect(body.comments.map((c) => c.author.login)).toEqual(["alice"]);
    expect(body.truncated).toBe(true);
  });

  it("reports truncation for a corrupt record too", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "alice is here" });
    await env.COMMENTS!.put(`cmt:${PAPER}:999000`, JSON.stringify({ login: 42, items: "nope" }));
    expect((await read(env)).body.truncated).toBe(true);
  });

  it("stays silent about a muted or legacy record — moderation does not announce itself", async () => {
    const env = makeEnv({ MUTED_IDS: String(IDS.spammer) });
    await post(env, "alice", { text: "alice is here" });
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${IDS.spammer}`,
      JSON.stringify({ login: "spammer", avatarUrl: null, items: [{ id: "s".repeat(24), at: "", text: "spam" }] }),
    );
    await env.COMMENTS!.put(
      `cmt:${PAPER}:legacy-login`,
      JSON.stringify({ login: "legacy", avatarUrl: null, items: [{ id: "l".repeat(24), at: "", text: "old" }] }),
    );
    const { body } = await read(env);
    expect(body.comments.map((c) => c.author.login)).toEqual(["alice"]);
    expect(body.truncated).toBe(false);
  });
});

describe("the author listing is enumerated, not sampled", () => {
  it("serves an author who sorts past the first listing page", async () => {
    // `list({limit})` returns the lexicographically FIRST keys, so a single
    // page made "smallest account ids win" the selection rule — an attacker
    // with enough low-sorting accounts evicted everyone else before any mute
    // could run, which made moderation inert against it.
    const env = makeEnv();
    for (let i = 0; i < 120; i++) {
      await env.COMMENTS!.put(
        `cmt:${PAPER}:1000000${String(i).padStart(3, "0")}`,
        JSON.stringify({
          login: `sock${i}`,
          avatarUrl: null,
          items: [{ id: `${i}`.padStart(24, "0"), at: "2026-08-20T00:00:00Z", text: "spam" }],
        }),
      );
    }
    // Sorts after every sock id above.
    await env.COMMENTS!.put(
      `cmt:${PAPER}:966666666`,
      JSON.stringify({
        login: "maintainer",
        avatarUrl: null,
        items: [{ id: "m".repeat(24), at: "2026-08-20T00:00:00Z", text: "the maintainer reply" }],
      }),
    );

    const { comments } = (await read(env)).body;
    expect(comments.map((c) => c.author.login)).toContain("maintainer");
  });

  it("does not serve simply the lexicographically smallest keys", async () => {
    // The property that matters: which records get served must not be an order
    // the attacker controls. Our keys ARE account ids, so head-of-sorted-list
    // selection let anyone with enough low-sorting accounts decide who is seen
    // — and decide it before the mute filter ran, which is what made muting
    // inert against it.
    const env = makeEnv();
    const ids: number[] = [];
    for (let i = 0; i < 600; i++) {
      const id = 100000000 + i;
      ids.push(id);
      await env.COMMENTS!.put(
        `cmt:${PAPER}:${id}`,
        JSON.stringify({
          login: `a${i}`,
          avatarUrl: null,
          items: [{ id: `${i}`.padStart(24, "0"), at: "2026-08-20T00:00:00Z", text: `c${i}` }],
        }),
      );
    }
    const { body } = await read(env);
    expect(body.truncated).toBe(true);
    expect(body.comments).toHaveLength(500);

    const servedIds = new Set(body.comments.map((c) => Number(c.author.login.slice(1)) + 100000000));
    const smallest500 = new Set(ids.slice(0, 500));
    const overlap = [...servedIds].filter((id) => smallest500.has(id)).length;
    // Head-of-list selection would make this exactly 500.
    expect(overlap).toBeLessThan(500);
  });

  it("enumerates past one page instead of sampling the first", async () => {
    const env = makeEnv();
    const kv = env.COMMENTS!;
    const realList = kv.list.bind(kv);
    let calls = 0;
    kv.list = async (opts: any) => {
      calls++;
      return realList(opts);
    };
    for (let i = 0; i < 1200; i++) {
      await kv.put(
        `cmt:${PAPER}:${100000000 + i}`,
        JSON.stringify({
          login: `a${i}`,
          avatarUrl: null,
          items: [{ id: `${i}`.padStart(24, "0"), at: "", text: "c" }],
        }),
      );
    }
    await read(env);
    // 1200 records at the worker's own page size must take more than one call.
    expect(calls).toBeGreaterThan(1);
  });

  it("lets muting the socks restore the page", async () => {
    const env = makeEnv();
    const ids: number[] = [];
    for (let i = 0; i < 120; i++) {
      const id = Number(`1000000${String(i).padStart(3, "0")}`);
      ids.push(id);
      await env.COMMENTS!.put(
        `cmt:${PAPER}:${id}`,
        JSON.stringify({
          login: `sock${i}`,
          avatarUrl: null,
          items: [{ id: `${i}`.padStart(24, "0"), at: "", text: "spam" }],
        }),
      );
    }
    await env.COMMENTS!.put(
      `cmt:${PAPER}:966666666`,
      JSON.stringify({
        login: "maintainer",
        avatarUrl: null,
        items: [{ id: "m".repeat(24), at: "", text: "the maintainer reply" }],
      }),
    );
    const muted = { ...env, MUTED_IDS: ids.join(",") };
    const { comments } = (await read(muted)).body;
    expect(comments.map((c) => c.author.login)).toEqual(["maintainer"]);
  });
});

describe("the storage cap is metered on the whole item", () => {
  it("counts an anchor, not just the text", async () => {
    // Counting text alone let a maximal record reach several times the nominal
    // cap, because every item may carry an 800-character anchor.
    const env = makeEnv();
    const anchor = {
      exact: "x".repeat(400),
      prefix: "p".repeat(200),
      suffix: "s".repeat(200),
      count: 1,
    };
    let posted = 0;
    for (let i = 0; i < 100; i++) {
      const res = await post(env, "alice", { text: "y".repeat(200), anchor });
      if (res.status === 429) break;
      posted++;
    }
    const rec = JSON.parse(env.COMMENTS!.store.get(`cmt:${PAPER}:${IDS.alice}`)!);
    const size = rec.items.reduce((n: number, i: unknown) => n + JSON.stringify(i).length, 0);
    expect(size).toBeLessThanOrEqual(40000);
    expect(posted).toBeGreaterThan(0);
  });

  it("leaves an author able to recover from someone else deleting the parent", async () => {
    // The lockout this replaces: the replies were invisible, still counted
    // against the quota, and the page offered no way to remove something it
    // never showed.
    const env = makeEnv();
    const parent = await postId(env, "bob", { text: "bob's comment" });
    const replyIds: string[] = [];
    for (let i = 0; i < 3; i++) {
      const res = await post(env, "alice", { parentId: parent, text: "z".repeat(10000) });
      expect(res.status).toBe(200);
      replyIds.push((await res.json()).id);
    }
    expect((await post(env, "alice", { text: "z".repeat(10000) })).status).toBe(429);

    expect((await del(env, "bob", { id: parent })).status).toBe(200);

    // Her replies are still visible, so she can act on them...
    const shown = (await read(env)).body.comments;
    expect(shown.map((c) => c.author.login)).toEqual(["alice", "alice", "alice"]);
    // ...and deleting one frees her quota.
    expect((await del(env, "alice", { id: replyIds[0] })).status).toBe(200);
    expect((await post(env, "alice", { text: "a fresh comment" })).status).toBe(200);
  });
});

describe("muting binds to the account, not the username", () => {
  it("keeps a muted account's back catalogue hidden after a rename", async () => {
    // Records are keyed on the id, so a login-only mute is retroactive as well
    // as escapable: rename, post once, and everything reappears.
    const env = makeEnv({ MUTED_IDS: String(IDS.spammer), MUTED_LOGINS: "spammer" });
    await env.COMMENTS!.put(
      `cmt:${PAPER}:${IDS.spammer}`,
      JSON.stringify({
        login: "spammer",
        avatarUrl: null,
        items: [{ id: "s".repeat(24), at: "2026-08-20T00:00:00Z", text: "BUY MY COURSE" }],
      }),
    );
    expect((await read(env)).body.comments).toEqual([]);

    // The same account, now presenting a different login.
    vi.stubGlobal("fetch", async () =>
      Response.json({ login: "reformed", id: IDS.spammer, avatar_url: null }),
    );
    expect((await post(env, "reformed")).status).toBe(403);
    expect((await read(env)).body.comments).toEqual([]);
  });

  it("still honours a login-only mute for someone not yet identified by id", async () => {
    const env = makeEnv({ MUTED_LOGINS: "spammer" });
    expect((await post(env, "spammer")).status).toBe(403);
  });
});

describe("a mistyped moderator list fails closed", () => {
  it("does not fall back to logins when ids are set but unparseable", async () => {
    const env = makeEnv({
      COMMENT_MODERATOR_IDS: "not-a-number",
      COMMENT_MODERATORS: "maintainer",
    });
    const id = await postId(env, "alice");
    expect((await del(env, "maintainer", { id, authorId: IDS.alice })).status).toBe(403);
  });

  it("treats a whitespace-only ids var as a typo, not as unset", async () => {
    const env = makeEnv({ COMMENT_MODERATOR_IDS: " ", COMMENT_MODERATORS: "maintainer" });
    const id = await postId(env, "alice");
    expect((await del(env, "maintainer", { id, authorId: IDS.alice })).status).toBe(403);
  });

  it("rejects exponent and hex id forms rather than coercing them", async () => {
    const env = makeEnv({ COMMENT_MODERATOR_IDS: "9.00002e5" });
    const id = await postId(env, "alice");
    expect((await del(env, "maintainer", { id, authorId: IDS.alice })).status).toBe(403);
  });
});

describe("reading a thread", () => {
  it("is anonymous and needs no token", async () => {
    const env = makeEnv();
    await post(env, "alice");
    expect((await read(env)).status).toBe(200);
  });

  it("returns comments oldest first, with replies in order under each", async () => {
    const env = makeEnv();
    const a = await postId(env, "alice", { text: "first" });
    await post(env, "bob", { parentId: a, text: "reply one" });
    await post(env, "bob", { parentId: a, text: "reply two" });
    const { comments } = (await read(env)).body;
    expect(comments.map((c) => c.text)).toEqual(["first"]);
    expect(comments[0].replies.map((r: any) => r.text)).toEqual(["reply one", "reply two"]);
  });

  it("hides a muted author's comments from everyone", async () => {
    const env = makeEnv();
    await post(env, "spammer", { text: "buy my thing" });
    await post(env, "alice", { text: "a real comment" });
    const muted = { ...env, MUTED_LOGINS: "spammer" };
    expect((await read(muted)).body.comments.map((c) => c.text)).toEqual(["a real comment"]);
  });

  it("reads empty rather than failing when no store is configured", async () => {
    const env = makeEnv();
    delete env.COMMENTS;
    expect((await read(env)).body.comments).toEqual([]);
  });

  it("400s a bad paper id", async () => {
    const res = await worker.fetch(
      new Request("https://worker.example.workers.dev/api/comments?paper=../etc", {
        headers: { Origin: ORIGIN },
      }),
      makeEnv(),
      ctx,
    );
    expect(res.status).toBe(400);
  });

  it("survives a corrupt record instead of failing the whole thread", async () => {
    const env = makeEnv();
    await post(env, "alice", { text: "a real comment" });
    await env.COMMENTS!.put(`cmt:${PAPER}:corrupt`, JSON.stringify({ login: 42, items: "nope" }));
    expect((await read(env)).body.comments.map((c) => c.text)).toEqual(["a real comment"]);
  });
});

describe("the browser holds no repository credential", () => {
  // The whole point of the design: a visitor's token is an identity document.
  // Driving the controller end to end needs a live selection and the whole
  // composer, so this reads the shipped sources — coarse, but it fails loudly
  // the day someone adds a convenient direct call back.
  const files = [
    "src/scripts/comments.ts",
    "src/scripts/comments/model.ts",
    "src/scripts/comments/auth.ts",
    "src/scripts/comments/replies.ts",
    "src/scripts/comments/parts.ts",
    "src/scripts/comments/render.ts",
    "src/scripts/proofmap/attest.ts",
  ];

  it("touches api.github.com only to ask who the visitor is", async () => {
    const { readFileSync } = await import("node:fs");
    for (const f of files) {
      const src = readFileSync(new URL(`../${f}`, import.meta.url), "utf8");
      for (const use of src.match(/https:\/\/api\.github\.com[^"'`\s)]*/g) ?? []) {
        expect(use).toBe("https://api.github.com/user");
      }
    }
  });

  it("never calls the GitHub GraphQL API, from the client or the worker", async () => {
    const { readFileSync } = await import("node:fs");
    for (const f of [...files, "comments-worker/worker.js"]) {
      expect(readFileSync(new URL(`../${f}`, import.meta.url), "utf8")).not.toContain(
        "api.github.com/graphql",
      );
    }
  });
});

describe("the CORS preflight", () => {
  it("allows the headers a write actually carries", async () => {
    // Without Authorization named here the browser refuses to send the POST at
    // all, and commenting fails with nothing in the worker's logs.
    const res = await worker.fetch(
      new Request("https://worker.example.workers.dev/api/comments", {
        method: "OPTIONS",
        headers: { Origin: ORIGIN },
      }),
      makeEnv(),
      ctx,
    );
    const allowHeaders = (res.headers.get("Access-Control-Allow-Headers") ?? "").toLowerCase();
    expect(allowHeaders).toContain("authorization");
    expect(allowHeaders).toContain("content-type");
    const allowMethods = res.headers.get("Access-Control-Allow-Methods") ?? "";
    expect(allowMethods).toContain("POST");
    expect(allowMethods).toContain("DELETE");
    expect(res.headers.get("Access-Control-Allow-Origin")).toBe(ORIGIN);
  });

  it("grants nothing to an origin outside the allowlist", async () => {
    const res = await worker.fetch(
      new Request("https://worker.example.workers.dev/api/comments", {
        method: "OPTIONS",
        headers: { Origin: "https://evil.example" },
      }),
      makeEnv(),
      ctx,
    );
    expect(res.headers.get("Access-Control-Allow-Origin")).toBeNull();
  });

  it("405s a method that is not a read or a write", async () => {
    const res = await call(makeEnv(), "PUT", "alice", { paper: PAPER });
    expect(res.status).toBe(405);
  });
});
