/**
 * CausalSmith comments worker — the ONE server-side piece of the paper-page
 * commenting system. Two jobs:
 *
 *   1. GitHub user-authorization handshake (`/login` → github.com →
 *      `/callback`), because the token exchange needs the client secret, which
 *      cannot live in the static site. The callback page hands the token to the
 *      opener page via postMessage and closes; the token itself is the
 *      visitor's, carries the GitHub App's permissions (Discussions on the one
 *      repo the App is installed on), and is stored only in their browser.
 *
 *      The handshake is nonce-bound end to end: `/login` requires a caller
 *      nonce, carries it through OAuth `state`, and `/callback` echoes it in
 *      the postMessage payload, so a page can refuse a token it did not ask
 *      for.
 *
 *   2. Read proxy (`/api/comments?paper=<id>&n=<discussionNumber>`), because
 *      browsers cannot query the Discussions GraphQL API. Reads resolve the
 *      paper's thread by its discussion NUMBER (baked into the page at build
 *      time), use a server-side read-only token, and are edge-cached briefly.
 *      Posting does NOT go through the worker: the visitor's browser talks to
 *      api.github.com directly with their own token. Threads are
 *      pre-provisioned by the maintainer (see provision.mjs); the worker never
 *      creates one.
 *
 *   3. Reader attestations (`/api/attestations`), the storage behind the paper
 *      page's Proof map: one record per reader per statement, saying they read
 *      that statement and its proof and certify them correct, taking the
 *      results the proof invokes as given. Unlike a comment — which IS a GitHub
 *      object and is posted browser → api.github.com — an attestation is our
 *      own record, so the write goes through here: the worker authenticates the
 *      visitor's GitHub token, resolves the login ITSELF, and keys the record
 *      by that. A reader can therefore only ever create or withdraw their own
 *      mark, and cannot forge someone else's.
 *
 * Environment (set via `wrangler secret put` / wrangler.toml vars):
 *   GITHUB_CLIENT_ID      – GitHub App client id                   (var)
 *   GITHUB_CLIENT_SECRET  – GitHub App client secret               (secret)
 *   GITHUB_READ_TOKEN     – fine-grained PAT, read-only Discussions (secret)
 *   GITHUB_REPO           – "owner/name" of the public repo         (var)
 *   ALLOWED_ORIGINS       – comma list of site origins allowed to auth/read (var)
 *   API_RATELIMIT         – Rate Limiting binding for /api/comments  (binding)
 *   LOGIN_RATELIMIT       – Rate Limiting binding for /login         (binding)
 *   ATTESTATIONS          – KV namespace holding reader attestations (binding)
 *   ATTEST_RATELIMIT      – Rate Limiting binding for attestation writes (binding)
 *   ATTEST_BLOCKLIST      – comma list of GitHub logins refused/hidden (var)
 *
 * The attestation endpoints are OPTIONAL: with no `ATTESTATIONS` KV binding
 * they answer 501 and the Proof map panel simply renders read-only.
 *
 * Rate limiting is enforced in code via the Workers Rate Limiting bindings
 * above (per-IP, 429 on excess). If a binding is absent the code no-ops it; the
 * backstop is the tightened `n` bound plus a Cloudflare dashboard rate-limit
 * rule.
 */

const CACHE_TTL_SECONDS = 60;
/** Caller-supplied handshake nonce: url-safe, long enough not to collide. */
const NONCE_RE = /^[A-Za-z0-9_-]{8,64}$/;

export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    try {
      if (url.pathname === "/login") return await login(request, url, env);
      if (url.pathname === "/callback") return await callback(url, env);
      if (url.pathname === "/api/comments") return await comments(request, url, env, ctx);
      if (url.pathname === "/api/attestations") return await attestations(request, url, env, ctx);
      return json({ error: "not found" }, 404, corsHeaders(request, env));
    } catch (e) {
      return json({ error: String(e && e.message ? e.message : e) }, 500, corsHeaders(request, env));
    }
  },
};

/**
 * Per-IP rate limit via Cloudflare's Workers Rate Limiting binding (GA).
 *
 * `binding` is `env.API_RATELIMIT` / `env.LOGIN_RATELIMIT` (see wrangler.toml).
 * If the binding is absent (local dev, or an account/plan where it is not
 * enabled), this is a no-op and the documented backstop applies: the tightened
 * `n` bound plus a Cloudflare dashboard rate-limit rule. Returns a 429 Response
 * when over the limit, else null.
 */
async function rateLimited(binding, request, extra) {
  if (!binding || typeof binding.limit !== "function") return null;
  const ip = request.headers.get("CF-Connecting-IP") || "anon";
  let ok = true;
  try {
    const res = await binding.limit({ key: ip });
    ok = res && res.success !== false;
  } catch {
    ok = true; // never let the limiter itself break the endpoint
  }
  if (ok) return null;
  return json({ error: "rate limited" }, 429, { ...extra, "Retry-After": "10" });
}

function allowedOrigins(env) {
  return (env.ALLOWED_ORIGINS || "")
    .split(",")
    .map((s) => s.trim())
    .filter(Boolean);
}

function corsHeaders(request, env) {
  const origin = request.headers.get("Origin") || "";
  const ok = origin && allowedOrigins(env).includes(origin);
  // A disallowed origin gets NO Access-Control-Allow-Origin header at all, so
  // the browser's own CORS check blocks the read — rather than the literal
  // "null", which some browsers treat as a grantable origin.
  const headers = { Vary: "Origin" };
  if (ok) headers["Access-Control-Allow-Origin"] = origin;
  return headers;
}

function json(obj, status = 200, extra = {}) {
  return new Response(JSON.stringify(obj), {
    status,
    headers: { "Content-Type": "application/json; charset=utf-8", ...extra },
  });
}

/* ── OAuth ────────────────────────────────────────────────────────────── */

async function login(request, url, env) {
  const limited = await rateLimited(env.LOGIN_RATELIMIT, request);
  if (limited) return limited;
  const origin = url.searchParams.get("origin") || "";
  const nonce = url.searchParams.get("nonce") || "";
  if (!allowedOrigins(env).includes(origin)) {
    return json({ error: "origin not allowed" }, 403);
  }
  if (!NONCE_RE.test(nonce)) {
    return json({ error: "missing or malformed nonce" }, 400);
  }
  const auth = new URL("https://github.com/login/oauth/authorize");
  auth.searchParams.set("client_id", env.GITHUB_CLIENT_ID);
  auth.searchParams.set("redirect_uri", `${url.origin}/callback`);
  // No `scope`: this is a GitHub App user-authorization flow, where permissions
  // come from the App's installation, not from the request.
  //
  // state carries the requesting origin and the caller's nonce; /callback
  // re-validates the origin against the allowlist, so a tampered state cannot
  // exfiltrate the token anywhere else, and echoes the nonce so the opener can
  // reject a handshake it did not start.
  auth.searchParams.set("state", `${origin}|${nonce}`);
  return Response.redirect(auth.toString(), 302);
}

async function callback(url, env) {
  const code = url.searchParams.get("code");
  const state = url.searchParams.get("state") || "";
  const sep = state.lastIndexOf("|");
  const origin = sep < 0 ? state : state.slice(0, sep);
  const nonce = sep < 0 ? "" : state.slice(sep + 1);
  if (!code) return new Response("missing code", { status: 400 });
  if (!allowedOrigins(env).includes(origin)) {
    return new Response("origin not allowed", { status: 403 });
  }
  if (!NONCE_RE.test(nonce)) {
    return new Response("missing or malformed nonce", { status: 400 });
  }
  const res = await fetch("https://github.com/login/oauth/access_token", {
    method: "POST",
    headers: { "Content-Type": "application/json", Accept: "application/json" },
    body: JSON.stringify({
      client_id: env.GITHUB_CLIENT_ID,
      client_secret: env.GITHUB_CLIENT_SECRET,
      code,
    }),
  });
  const data = await res.json().catch(() => ({}));
  const token = data.access_token || "";
  // Surface GitHub's own error (never the token) in the popup and the logs —
  // "failed" with no reason is undebuggable.
  const failReason = token ? "" : String(data.error_description || data.error || `exchange HTTP ${res.status}`);
  if (!token) {
    console.error("oauth exchange failed", JSON.stringify({ status: res.status, error: data.error, description: data.error_description }));
  }
  const message = token
    ? "Signed in — you can close this window."
    : `Sign-in failed: ${failReason} — you can close this window.`;
  const page = `<!doctype html><meta charset="utf-8"><title>Signed in</title>
<body style="font-family:Georgia,serif;background:#fdfcfa;color:#1a1a1a;padding:2rem">
<p id="msg"></p>
<script>
  document.getElementById("msg").textContent = ${jsLiteral(message)};
  var payload = {
    type: "causalsmith-auth",
    nonce: ${jsLiteral(nonce)},
    token: ${jsLiteral(token)}
  };
  if (window.opener) window.opener.postMessage(payload, ${jsLiteral(origin)});
  setTimeout(function () { window.close(); }, 400);
</script></body>`;
  return new Response(page, {
    headers: {
      "Content-Type": "text/html; charset=utf-8",
      "Cache-Control": "no-store",
      // The page runs only its own inline script and reaches nothing else, so a
      // stray `</script>` in an interpolated value cannot start new markup that
      // does anything — jsLiteral escapes `<`/`>` as the primary defense.
      "Content-Security-Policy": "default-src 'none'; script-src 'unsafe-inline'",
    },
  });
}

/** JSON string literal with `<`/`>` escaped, so no interpolated value — a token
 *  or a GitHub error string — can emit `</script>` and break out of the tag. */
function jsLiteral(value) {
  return JSON.stringify(String(value)).replace(/</g, "\\x3c").replace(/>/g, "\\x3e");
}

/* ── Read proxy ───────────────────────────────────────────────────────── */

/** One Discussion comment for the wire. GitHub Discussions threads exactly one
 *  level deep, so a reply is the same shape minus its own replies. Minimized
 *  (hidden/moderated) comments and replies are dropped, so hiding one on GitHub
 *  removes it from the paper page. */
function shapeComment(c) {
  return {
    id: c.id,
    body: c.body,
    createdAt: c.createdAt,
    author: c.author ? { login: c.author.login, avatarUrl: c.author.avatarUrl } : null,
    replies:
      c.replies && c.replies.nodes
        ? c.replies.nodes.filter((r) => !r.isMinimized).map(shapeReply)
        : [],
  };
}

function shapeReply(r) {
  return {
    id: r.id,
    body: r.body,
    createdAt: r.createdAt,
    author: r.author ? { login: r.author.login, avatarUrl: r.author.avatarUrl } : null,
  };
}

// Resolve the paper's thread by its DISCUSSION NUMBER — a stable, unforgeable
// handle. No discussions() scan, no pagination, no title-search: the whole
// class of rename / duplicate-title / pagination attacks disappears, and it is
// one narrow query. The title is fetched only to cross-check against the paper
// id as defense in depth.
const DISCUSSION_QUERY = `
query($owner: String!, $name: String!, $number: Int!) {
  repository(owner: $owner, name: $name) {
    discussion(number: $number) {
      id
      number
      title
      comments(first: 100) {
        nodes {
          id
          body
          createdAt
          isMinimized
          author { login avatarUrl }
          replies(first: 20) {
            nodes {
              id
              body
              createdAt
              isMinimized
              author { login avatarUrl }
            }
          }
        }
      }
    }
  }
}`;

async function githubGraphql(env, query, variables) {
  const res = await fetch("https://api.github.com/graphql", {
    method: "POST",
    headers: {
      Authorization: `Bearer ${env.GITHUB_READ_TOKEN}`,
      "Content-Type": "application/json",
      "User-Agent": "causalsmith-comments-worker",
    },
    body: JSON.stringify({ query, variables }),
  });
  const data = await res.json().catch(() => ({}));
  if (!res.ok) {
    throw new Error(`GitHub API ${res.status}: ${data.message || "request failed"}`);
  }
  // A missing discussion number comes back as partial data
  // (`repository.discussion: null`) alongside a NOT_FOUND error. That is the
  // not-yet-provisioned / stale-number case, and the caller handles the null —
  // so tolerate errors as long as GraphQL still returned a data payload. Only a
  // total failure (no data at all) is fatal.
  if (!data.data) {
    const msg = data.errors ? data.errors.map((e) => e.message).join("; ") : "GitHub API returned no data";
    throw new Error(msg);
  }
  return data.data;
}

const EMPTY_THREAD = { discussionId: null, discussionNumber: null, comments: [] };

async function comments(request, url, env, ctx) {
  const cors = corsHeaders(request, env);
  if (request.method === "OPTIONS") {
    return new Response(null, {
      headers: { ...cors, "Access-Control-Allow-Methods": "GET" },
    });
  }
  // Only GET (and the OPTIONS preflight above) is a read; anything else is 405.
  if (request.method !== "GET") {
    return json({ error: "method not allowed" }, 405, { ...cors, Allow: "GET, OPTIONS" });
  }
  const limited = await rateLimited(env.API_RATELIMIT, request, cors);
  if (limited) return limited;

  const paper = url.searchParams.get("paper") || "";
  if (!/^[A-Za-z0-9_.-]{1,128}$/.test(paper)) return json({ error: "bad paper id" }, 400, cors);
  const nRaw = url.searchParams.get("n") || "";
  // Discussion numbers are small; 7 digits is far more than any repo will reach,
  // and bounding it shrinks the cache-partition surface (and the backstop when
  // the rate-limit binding is unavailable).
  const hasNumber = /^[0-9]{1,7}$/.test(nRaw);

  // A paper with no valid discussion number is treated as not-yet-provisioned:
  // an empty thread, no upstream query. This is also what an invalid `n` gets,
  // so a junk number cannot probe arbitrary discussions.
  if (!hasNumber) return json(EMPTY_THREAD, 200, cors);

  // Cache key is built from the VALIDATED params only, so junk query params
  // (a `&cb=…` cache-buster) can never fragment or bust the shared edge cache.
  const cacheKey = new Request(`${url.origin}/api/comments?paper=${paper}&n=${nRaw}`, {
    method: "GET",
  });
  const cache = caches.default;
  const cached = await cache.match(cacheKey);
  if (cached) {
    const r = new Response(cached.body, cached);
    for (const [k, v] of Object.entries(cors)) r.headers.set(k, v);
    return r;
  }

  const [owner, name] = (env.GITHUB_REPO || "").split("/");
  const data = await githubGraphql(env, DISCUSSION_QUERY, {
    owner,
    name,
    number: Number(nRaw),
  });
  const discussion = data.repository && data.repository.discussion;

  // Defense in depth: the number must resolve to a discussion whose title is
  // exactly this paper id. A number pointing elsewhere reads as empty.
  const body =
    discussion && discussion.title === paper
      ? {
          discussionId: discussion.id,
          discussionNumber: discussion.number,
          comments: (discussion.comments.nodes || [])
            .filter((c) => !c.isMinimized)
            .map(shapeComment),
        }
      : EMPTY_THREAD;

  const res = json(body, 200, {
    ...cors,
    "Cache-Control": `public, max-age=${CACHE_TTL_SECONDS}`,
  });
  ctx.waitUntil(cache.put(cacheKey, res.clone()));
  return res;
}

/* ── Reader attestations ──────────────────────────────────────────────────
 *
 * Storage is one KV key per (paper, reader):
 *
 *   att:<paper>:<login lowercased>  →  { login, avatarUrl, marks: {objId: iso} }
 *
 * A reader's writes therefore only ever touch their OWN key — two readers
 * attesting the same statement at the same moment cannot lose each other's
 * mark, which a single per-paper document would allow. Reading a paper is one
 * prefix list plus a bounded fan-out of gets, cached at the edge.
 */

/** Paper ids are bundle directory names, so they start alphanumeric — which
 *  also keeps `.` / `..` out of a KV key path. Obj ids look like
 *  `lem:pilot-sandwich` or `synth_7`. */
const PAPER_RE = /^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}$/;
const OBJID_RE = /^[A-Za-z0-9_:.-]{1,128}$/;
/** Most statements one reader may mark on one paper. */
const MAX_MARKS_PER_READER = 500;
/** Most readers listed for one paper (KV list page size cap is 1000). */
const MAX_READERS_LISTED = 500;
const ATTEST_CACHE_TTL_SECONDS = 30;
const AVATAR_PREFIX = "https://avatars.githubusercontent.com/";

const attestKey = (paper, login) => `att:${paper}:${login.toLowerCase()}`;
const attestPrefix = (paper) => `att:${paper}:`;

/** The edge cache, when there is one (absent under test / `wrangler dev`). */
function edgeCache() {
  try {
    return typeof caches !== "undefined" && caches.default ? caches.default : null;
  } catch {
    return null;
  }
}

/** Logins the maintainer has muted: refused on write, hidden on read. */
function blocklist(env) {
  return (env.ATTEST_BLOCKLIST || "")
    .split(",")
    .map((s) => s.trim().toLowerCase())
    .filter(Boolean);
}

function isBlocked(env, login) {
  return blocklist(env).includes(String(login).toLowerCase());
}

/** GitHub only ever serves avatars from this host; anything else is dropped. */
function safeAvatar(url) {
  return typeof url === "string" && url.startsWith(AVATAR_PREFIX) && !/[\s"'<>\\]/.test(url)
    ? url
    : null;
}

function bearer(request) {
  const h = request.headers.get("Authorization") || "";
  const m = /^Bearer\s+([A-Za-z0-9_.\-]+)$/.exec(h.trim());
  return m ? m[1] : "";
}

/**
 * Resolve the visitor's GitHub identity from their own token.
 *
 * This is what makes an attestation unforgeable: the client never states who it
 * is, the worker asks GitHub. A rejected or expired token yields null and the
 * caller answers 401.
 */
async function githubUser(token) {
  const res = await fetch("https://api.github.com/user", {
    headers: {
      Authorization: `Bearer ${token}`,
      Accept: "application/vnd.github+json",
      "User-Agent": "causalsmith-comments-worker",
    },
  });
  if (!res.ok) return null;
  const data = await res.json().catch(() => ({}));
  if (!data || typeof data.login !== "string" || !data.login) return null;
  return { login: data.login, avatarUrl: safeAvatar(data.avatar_url) };
}

/** Body of a write request: `{paper, objId}`, both validated. */
async function attestBody(request) {
  const data = await request.json().catch(() => null);
  if (!data || typeof data !== "object") return null;
  const paper = typeof data.paper === "string" ? data.paper : "";
  const objId = typeof data.objId === "string" ? data.objId : "";
  if (!PAPER_RE.test(paper) || !OBJID_RE.test(objId)) return null;
  return { paper, objId };
}

async function attestations(request, url, env, ctx) {
  const cors = corsHeaders(request, env);
  if (request.method === "OPTIONS") {
    return new Response(null, {
      headers: {
        ...cors,
        "Access-Control-Allow-Methods": "GET, POST, DELETE, OPTIONS",
        "Access-Control-Allow-Headers": "Authorization, Content-Type",
        "Access-Control-Max-Age": "600",
      },
    });
  }
  // No KV binding → the feature is simply not deployed. Say so rather than
  // failing obscurely; the panel renders read-only either way.
  if (!env.ATTESTATIONS) {
    return json({ error: "attestations are not configured" }, 501, cors);
  }
  if (request.method === "GET") return await listAttestations(request, url, env, ctx, cors);
  if (request.method === "POST" || request.method === "DELETE") {
    return await writeAttestation(request, url, env, ctx, cors);
  }
  return json({ error: "method not allowed" }, 405, {
    ...cors,
    Allow: "GET, POST, DELETE, OPTIONS",
  });
}

async function listAttestations(request, url, env, ctx, cors) {
  const limited = await rateLimited(env.API_RATELIMIT, request, cors);
  if (limited) return limited;

  const paper = url.searchParams.get("paper") || "";
  if (!PAPER_RE.test(paper)) return json({ error: "bad paper id" }, 400, cors);

  // Cache key built from the VALIDATED paper only, so junk query params cannot
  // fragment the shared edge cache.
  const cacheKey = new Request(`${url.origin}/api/attestations?paper=${paper}`, {
    method: "GET",
  });
  const cache = edgeCache();
  const cached = cache ? await cache.match(cacheKey) : null;
  if (cached) {
    const r = new Response(cached.body, cached);
    for (const [k, v] of Object.entries(cors)) r.headers.set(k, v);
    return r;
  }

  const listing = await env.ATTESTATIONS.list({
    prefix: attestPrefix(paper),
    limit: MAX_READERS_LISTED,
  });
  const records = await Promise.all(
    (listing.keys || []).map((k) => env.ATTESTATIONS.get(k.name, "json").catch(() => null)),
  );
  const muted = blocklist(env);
  const out = [];
  for (const rec of records) {
    if (!rec || typeof rec.login !== "string") continue;
    if (muted.includes(rec.login.toLowerCase())) continue;
    const marks = rec.marks && typeof rec.marks === "object" ? rec.marks : {};
    for (const [objId, at] of Object.entries(marks)) {
      if (!OBJID_RE.test(objId)) continue;
      out.push({
        objId,
        login: rec.login,
        avatarUrl: safeAvatar(rec.avatarUrl),
        at: typeof at === "string" ? at : "",
      });
    }
  }
  out.sort((a, b) => (a.at < b.at ? -1 : a.at > b.at ? 1 : 0));

  const res = json({ paper, attestations: out }, 200, {
    ...cors,
    "Cache-Control": `public, max-age=${ATTEST_CACHE_TTL_SECONDS}`,
  });
  if (cache && ctx && typeof ctx.waitUntil === "function") {
    ctx.waitUntil(cache.put(cacheKey, res.clone()));
  }
  return res;
}

async function writeAttestation(request, url, env, ctx, cors) {
  // A browser page may write only from an allowlisted origin. (The token lives
  // in an Authorization header, never a cookie, so there is no ambient
  // credential to abuse; this simply keeps the surface as narrow as /login's.)
  const origin = request.headers.get("Origin") || "";
  if (origin && !allowedOrigins(env).includes(origin)) {
    return json({ error: "origin not allowed" }, 403, cors);
  }
  const limited = await rateLimited(env.ATTEST_RATELIMIT, request, cors);
  if (limited) return limited;

  const token = bearer(request);
  if (!token) return json({ error: "sign in to record an attestation" }, 401, cors);
  const body = await attestBody(request);
  if (!body) return json({ error: "bad request body" }, 400, cors);

  const user = await githubUser(token);
  if (!user) return json({ error: "GitHub rejected the token" }, 401, cors);
  if (isBlocked(env, user.login)) return json({ error: "not permitted" }, 403, cors);

  const key = attestKey(body.paper, user.login);
  const existing = (await env.ATTESTATIONS.get(key, "json").catch(() => null)) || {};
  const marks =
    existing.marks && typeof existing.marks === "object" ? { ...existing.marks } : {};

  let at = "";
  if (request.method === "POST") {
    if (!marks[body.objId] && Object.keys(marks).length >= MAX_MARKS_PER_READER) {
      return json({ error: "attestation limit reached for this paper" }, 429, cors);
    }
    at = typeof marks[body.objId] === "string" ? marks[body.objId] : new Date().toISOString();
    marks[body.objId] = at;
  } else {
    delete marks[body.objId];
  }

  if (Object.keys(marks).length === 0) {
    await env.ATTESTATIONS.delete(key);
  } else {
    await env.ATTESTATIONS.put(
      key,
      JSON.stringify({ login: user.login, avatarUrl: user.avatarUrl, marks }),
    );
  }

  // The paper's read is edge-cached; drop that entry so the next reader sees
  // the change rather than waiting out the TTL.
  const cache = edgeCache();
  if (cache && ctx && typeof ctx.waitUntil === "function") {
    ctx.waitUntil(
      cache.delete(
        new Request(`${url.origin}/api/attestations?paper=${body.paper}`, { method: "GET" }),
      ),
    );
  }

  return json(
    {
      ok: true,
      paper: body.paper,
      objId: body.objId,
      login: user.login,
      avatarUrl: user.avatarUrl,
      at,
    },
    200,
    cors,
  );
}
