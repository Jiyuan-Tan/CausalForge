# Comments worker

The single server-side piece of the paper-page commenting system (margin
comments with optional ✅ Verified / ⚠️ Problem tags, sentence-anchored) and of
the Proof map's reader attestations. It runs on Cloudflare Workers' free tier
and does exactly three things:

1. **Sign-in handshake** — exchanges the GitHub authorization code for the
   visitor's token (the step that needs the client secret). The token is
   handed to the paper page via `postMessage`, bound to a nonce the page
   generated, and lives only in the visitor's browser; posting comments goes
   browser → api.github.com directly.
2. **Read proxy** — serves each paper's comment thread from GitHub Discussions
   to anonymous visitors (Discussions GraphQL requires auth), edge-cached 60 s.
   It resolves the thread by its **discussion number** (baked into each page at
   build time), not by searching titles.

3. **Reader attestations** — stores, per paper and per statement, that a
   signed-in reader read that statement and its proof and certifies them
   correct (taking the results the proof invokes as given). This is the Proof map
   panel's "I verified this statement & proof" control. Storage is a KV
   namespace, and the write path authenticates the reader's token and derives
   the login server-side, so nobody can post a mark under someone else's name.

Comment storage is GitHub Discussions on the public repo — one discussion per
paper (title = paper id) in the **Paper comments** category. Threads are
**pre-provisioned by the maintainer** (see [Provisioning](#provisioning-threads));
a visitor's browser never creates one, so no reader can ever become a thread's
owner. The wire format is defined in `site/src/lib/comments/schema.ts`.

## One-time setup (operator)

1. **Enable Discussions** on the public repo (Settings → General → Features)
   and create a category named **Paper comments** (type: open discussion).
2. **Create a GitHub App** (github.com → Settings → Developer settings →
   GitHub Apps → New GitHub App). A GitHub App, not an OAuth App: its user
   tokens can only ever touch the repo the App is installed on, and only
   through the permissions below — an OAuth App token would carry the
   visitor's whole account.
   - Homepage URL: the public site URL
   - Callback URL: `https://<worker-url>/callback`
     (the worker URL is printed by the first `wrangler deploy`; you can deploy
     first with a placeholder and update the App after)
   - Enable **"Request user authorization (OAuth) during installation"**.
   - **Disable** the webhook (Webhook → uncheck Active).
   - Repository permissions: **Discussions: Read & write**, **Metadata:
     Read-only** (metadata is mandatory and granted automatically). Nothing
     else — no contents, no issues, no pull requests.
   - Under **Optional features**, consider disabling user-token expiration.
     Expiring tokens plus a refresh flow is the safer setting in general, but
     v1 keeps the token in `sessionStorage`, so exposure is already bounded by
     the browser tab either way; non-expiring tokens simply avoid a refresh
     path the site does not yet have.
   - Install the App on the **public repo only** (Install App → Only select
     repositories).
   - **Make the App public** (App settings → Advanced → "Make public"). New
     GitHub Apps are private by default, and a private App's authorize
     endpoint returns a bare 404 to every GitHub account except the owner —
     the symptom is "sign-in works for me but everyone else lands on a 404
     right after entering their GitHub password". Public here only means
     others may authorize/install it; the token permissions above are
     unchanged.
   - Note the **Client ID** and generate a **Client secret**.

   There is no OAuth `scope` in this flow: with a GitHub App, permissions come
   from the installation, so the worker never requests one.
3. **Create a fine-grained PAT** for reads: repo = the public repo only,
   permission = Discussions: Read-only. (Used solely by the worker's read
   proxy; never reaches a browser.)
4. **Deploy** (needs a free Cloudflare account):
   ```
   cd site/comments-worker
   npx wrangler login
   # fill GITHUB_CLIENT_ID + ALLOWED_ORIGINS in wrangler.toml first
   npx wrangler deploy
   npx wrangler secret put GITHUB_CLIENT_SECRET
   npx wrangler secret put GITHUB_READ_TOKEN
   ```
5. **Rate limiting** is enforced in the worker via Cloudflare's Workers **Rate
   Limiting bindings** (`API_RATELIMIT` 30 req/10 s, `LOGIN_RATELIMIT` 10 req/
   10 s, per IP — see `wrangler.toml`); over the limit returns 429. Confirm the
   binding is active on your account (`wrangler deploy --dry-run` validates the
   config). If the binding is **not available** on the account/plan, the worker
   no-ops it — add a per-IP rate-limit rule in the dashboard (Security → WAF →
   Rate limiting rules) on `/api/comments` and `/login` as the backstop; the
   tightened `n` bound (`^[0-9]{1,7}$`) limits the cache-partition surface
   either way.
6. **Create the attestations KV namespace** (only if you want the Proof map's
   reader-verification control; skip it and the panel stays read-only):
   ```
   npx wrangler kv namespace create ATTESTATIONS
   # paste the printed id into wrangler.toml's [[kv_namespaces]] block
   npx wrangler deploy
   ```
   The `ATTEST_RATELIMIT` binding in `wrangler.toml` (12 writes/10 s per IP)
   and the `ATTEST_BLOCKLIST` var (comma-separated GitHub logins, empty by
   default) come with it; both are optional in the same way the comment
   limiters are — an absent limiter binding is a no-op.
7. **Provision the threads** — see [Provisioning](#provisioning-threads) — so
   each paper has a discussion number to resolve.
8. Build the site with `PUBLIC_COMMENTS_WORKER=https://<worker-url>` set. That
   env var is the feature flag for BOTH features: unset (the CI/dev default)
   the paper pages ship with the commenting controller inert — no requests, no
   UI — and the Proof map renders read-only (graph, statements, and navigation,
   with no verification control).

## Provisioning threads

Each paper page resolves its comments by a **discussion number** recorded in
`site/src/lib/comments/discussions.json` (`{ "<paperId>": <number> }`) and baked
into the page at build. The map ships empty; papers without an entry show
"Commenting isn't open on this paper yet" and read as empty (no network call).

`provision.mjs` fills the map. It reads the paper ids from the freshly built
`dist/papers/` directory (the exact set of published pages), creates one
discussion per missing paper (title = paper id, in **Paper comments**), and
writes the numbers back. It is idempotent — existing entries are preserved and
a thread that already exists on GitHub is reused, never duplicated.

**Provision BEFORE the paper pages are publicly linked.** A visitor's browser
can create a discussion directly on GitHub, so anyone who learns a paper's id
early could pre-create a discussion under that title and then delete it later,
taking the comments with it. The script defends against this: it adopts an
existing same-titled discussion **only if the maintainer (the token's viewer) or
the repo owner authored it**. If a same-titled discussion exists under a
**foreign author**, the script prints a `SKIP … foreign-authored discussion #N
by @user` warning naming the paper, author, and discussion URL, leaves that
paper unprovisioned ("commenting isn't open"), and **exits non-zero** so you
investigate — a squatted title is a signal, not something to auto-resolve.
Delete the squatted discussion on github.com, then re-run.

```
cd site
npm run build                        # produces dist/papers/*
GITHUB_TOKEN=<PAT: Discussions write> \
GITHUB_REPO=Jiyuan-Tan/CausalSmith \
DISCUSSION_CATEGORY="Paper comments" \
  node comments-worker/provision.mjs
npm run build                        # rebake the numbers into the pages
```

The `GITHUB_TOKEN` here is a **maintainer-only, one-off write token**. It never
touches the worker or the site — only this script uses it. The deployed worker
keeps its read-only PAT.

## Local development

The **deployed** worker's `ALLOWED_ORIGINS` lists the production site only —
never `http://localhost`. A localhost origin on the deployed allowlist would let
any page on any developer's machine obtain a real user token from it. For local
work, run a separate worker (`wrangler dev`, or a throwaway `wrangler deploy` of
a second `name`) with its own temporary allowlist that includes your localhost
origin, and point the dev site's `PUBLIC_COMMENTS_WORKER` at that.

## Endpoints

- `GET /login?origin=<site origin>&nonce=<8–64 url-safe chars>` — 302 to
  GitHub authorize; origin must be in `ALLOWED_ORIGINS` and the nonce must
  match `[A-Za-z0-9_-]{8,64}`. `state` carries `origin|nonce`.
- `GET /callback?code&state` — exchanges the code, posts
  `{type:"causalsmith-auth", nonce, token}` to the opener at the state origin
  (re-validated against the allowlist), closes the popup. The paper page
  accepts the message only when the origin AND the nonce both match the
  handshake it started. The callback page carries a strict CSP and escapes
  every interpolated value.
- `GET /api/comments?paper=<id>&n=<discussionNumber>` — resolves the thread by
  number and returns `{discussionId, discussionNumber, comments:[{id, body,
  createdAt, author, replies:[…]}]}`. A missing/invalid `n`, or a number whose
  discussion title does not match `<id>`, returns an empty thread. `n` is bounded
  to `^[0-9]{1,7}$`. Only `GET` (and the `OPTIONS` preflight) is accepted; other
  methods get 405. Per-IP rate limited (429 over the limit). The cache key is
  built from the validated `paper` and `n` only, so junk query params cannot
  bust the shared cache. Minimized (hidden) comments and replies are dropped.
- `GET /api/attestations?paper=<id>` — every reader attestation on a paper:
  `{paper, attestations:[{objId, login, avatarUrl, at}]}`, oldest first. No
  token needed. Edge-cached 30 s and per-IP rate limited. Blocklisted logins
  are omitted.
- `POST /api/attestations` — body `{paper, objId}`, `Authorization: Bearer
  <visitor token>`. The worker calls GitHub's `/user` with that token and keys
  the record by the login it gets back, so the client cannot claim an identity.
  Idempotent: re-posting keeps the original timestamp. Returns `{ok, paper,
  objId, login, avatarUrl, at}`.
- `DELETE /api/attestations` — same body and header; withdraws the caller's own
  mark. A reader can only ever touch their own key.
- All three refuse a cross-origin write from an origin outside
  `ALLOWED_ORIGINS`, are rate limited (`ATTEST_RATELIMIT` on writes), and answer
  **501** when the `ATTESTATIONS` KV binding is absent — which the panel treats
  as "read-only", not as an error.

### Attestation storage

One KV key per (paper, reader):

```
att:<paper>:<login lowercased>  →  { login, avatarUrl, marks: { "<objId>": "<iso>" } }
```

A reader's writes touch only their own key, so two readers marking the same
statement at the same moment cannot lose each other's mark (a single per-paper
document would). A read is one prefix `list` (≤ 500 readers) plus a bounded
fan-out of `get`s, cached at the edge for 30 s and invalidated on write. One
reader may hold at most 500 marks per paper.

## Security model

**What the worker holds.** The GitHub App client secret and a fine-grained
read-only PAT, both as Wrangler secrets. Neither is ever sent to a browser. An
attacker who obtained them could read the public repo's (already public)
discussions and could complete a sign-in exchange — but the callback only ever
posts a token back to an origin on `ALLOWED_ORIGINS`, so a stolen secret alone
does not deliver a token anywhere.

**What the browser holds.** The visitor's own user token, in `sessionStorage`
under `cs-gh-token`, for the tab's lifetime. It carries the App's permissions
only: Discussions read/write on the single repo the App is installed on. It is
never placed in a URL, a cookie, or a log line. Worst case — an XSS on the
paper page, or a malicious extension — the attacker can post and edit comments
as that visitor on that one repo. They cannot touch code, other repos, or the
rest of the account, and the token dies with the tab.

**What the handshake refuses.** `/login` requires an allowlisted origin and a
caller nonce; `/callback` re-validates the origin against the allowlist and
echoes the nonce; the page accepts the `postMessage` only from the worker's
exact origin and only with the nonce it generated. A page that did not start a
sign-in cannot be handed a token, and a token cannot be redirected to a site
that is not on the allowlist.

**Who owns a thread.** Nobody but the maintainer. Threads are pre-provisioned,
and the client has no `createDiscussion` path, so a visitor can only ever add a
comment or a reply to an existing thread — never create, rename, or delete the
discussion that holds everyone else's comments.

**What the page never does.** Comment text, reply text, and author fields are
rendered as plain text (`textContent`) — no markdown, no HTML — so a hostile
body cannot become markup on the paper page. Avatars load only from
`https://avatars.githubusercontent.com/`; anything else degrades to initials.

**Bounded per-load work.** Re-anchoring stored quotes is capped: quotes over
400 chars are ignored, and at most 40 comments per page are re-anchored (the
rest render as unanchored "general" comments, surfaced in the rail head, never
silently dropped). Placement runs in batches yielded to the event loop, and
segmentation is deferred off first paint. So a flood of comments cannot freeze
or blank the page — the worst case is some comments shown unanchored.

**What an attestation is worth.** It is a claim by a named GitHub account that
the reader checked ONE statement and its proof, taking the results that proof
invokes as given. It is not a machine check, it does not compose into "the paper
is verified", and the page never presents it as either — the Lean layer is what
carries machine-checked truth. Because the login is resolved from the token
server-side, a mark cannot be forged under another handle; because a reader may
only write their own key, one reader can never remove another's mark.

**Attestation moderation** is the `ATTEST_BLOCKLIST` var: a comma-separated list
of GitHub logins, refused on write and hidden on read (`wrangler.toml`, then
`npx wrangler deploy`). To erase a specific record outright, delete its KV key
(`npx wrangler kv key delete --binding ATTESTATIONS "att:<paper>:<login>"`).

**Moderation** of comments is GitHub's: **hiding/minimizing** a comment or reply on
github.com removes it from the paper page (the worker drops minimized nodes);
deleting it removes it outright; you can also lock the discussion or block the
user from the repo. Because storage IS the Discussion, moderation done on
github.com takes effect at the next read (within the 60 s edge cache).

**Spam control = GitHub account + manual moderation** (delete / minimize / lock
on github.com); there is no automated spam filter. Posting needs a signed-in
GitHub user, and the worker's per-IP rate limit slows bulk posting. What the
page *guarantees* instead is that mass posting cannot freeze readers: per-load
work is bounded (400-char anchor limit, 40-comment re-anchor cap with the rest
shown unanchored, batched placement, and deferred hydration off first paint).
