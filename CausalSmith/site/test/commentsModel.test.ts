// Pure model layer for paper-page comments: placement against the current
// text, grouping/ordering for the rail, the label strings, the hostile-input
// caps, and the GraphQL bodies. No DOM here — the DOM layer is covered in
// test/commentsDom.test.ts.

import { describe, expect, it } from "vitest";
import { makeAnchor, type SentenceRef } from "../src/lib/comments/anchor.js";
import { parseComment, serializeComment } from "../src/lib/comments/schema.js";
import * as model from "../src/scripts/comments/model.js";
import {
  MAX_ANCHOR_COUNT,
  MAX_ANCHORED_COMMENTS,
  MAX_EXACT_CHARS,
  MAX_TEXT_CHARS,
  activeComments,
  addCommentMutation,
  addReplyMutation,
  archivedNote,
  countLabel,
  deleteCommentMutation,
  driftNote,
  formatWhen,
  groupComments,
  highlightPlan,
  initialsOf,
  isSafeAvatarUrl,
  mergeComments,
  newCommentBody,
  ownsComment,
  placeComments,
  placeCommentsAsync,
  placeCommentsBudgeted,
  placeReplies,
  replyCountLabel,
  serializeReply,
  sanitizeAnchor,
  snapNote,
  truncate,
  type FetchedComment,
} from "../src/scripts/comments/model.js";

const SENTENCES: string[] = [
  "We study the ATE under weak overlap.",
  "The lower bound uses Le Cam's two-point method.",
  "The separation constant is C = 4√2, an absolute constant.",
  "Summing the cellwise contributions yields the display.",
];

function refs(texts: string[] = SENTENCES): SentenceRef[] {
  return texts.map((text, i) => ({ id: `b0-s${i}`, text }));
}

function fetched(over: Partial<FetchedComment> & { body: string }): FetchedComment {
  return {
    id: over.id ?? "C_1",
    body: over.body,
    createdAt: over.createdAt ?? "2026-08-21T10:00:00Z",
    url: over.url ?? "https://github.com/o/r/discussions/1#discussioncomment-1",
    author: over.author ?? { login: "j-metrics", avatarUrl: "https://avatars.githubusercontent.com/u/1?v=4" },
  };
}

function anchoredBody(start: number, end: number, tag: "none" | "verified" | "problem" = "none") {
  return serializeComment({
    meta: { v: 1, paper: "wp7", tag, anchor: makeAnchor(refs(), start, end), revision: "abc1234" },
    text: "Body text.",
  });
}

describe("sanitizeAnchor", () => {
  it("keeps a well-formed anchor", () => {
    const a = makeAnchor(refs(), 1, 2);
    expect(sanitizeAnchor(a)).toEqual(a);
  });

  it("refuses an absurd count or quote, so re-anchoring stays cheap", () => {
    const base = makeAnchor(refs(), 0, 1);
    expect(sanitizeAnchor({ ...base, count: MAX_ANCHOR_COUNT + 1 })).toBeNull();
    expect(sanitizeAnchor({ ...base, count: 1e9 })).toBeNull();
    expect(sanitizeAnchor({ ...base, count: 0 })).toBeNull();
    expect(sanitizeAnchor({ ...base, count: 1.5 })).toBeNull();
    expect(sanitizeAnchor({ ...base, exact: "x".repeat(MAX_EXACT_CHARS + 1) })).toBeNull();
    expect(sanitizeAnchor({ ...base, exact: "" })).toBeNull();
    expect(sanitizeAnchor(null)).toBeNull();
    expect(sanitizeAnchor("nope")).toBeNull();
  });

  it("truncates oversized context fields instead of trusting them", () => {
    const a = sanitizeAnchor({ exact: "q", prefix: "p".repeat(5000), suffix: 42, count: 1 });
    expect(a?.prefix.length).toBe(200);
    expect(a?.suffix).toBe("");
  });
});

describe("placeComments", () => {
  it("anchors an untouched quote and reports the sentences it covers", () => {
    const placed = placeComments([fetched({ body: anchoredBody(1, 3) })], "wp7", refs());
    expect(placed).toHaveLength(1);
    expect(placed[0].kind).toBe("anchored");
    expect(placed[0].sids).toEqual(["b0-s1", "b0-s2"]);
    expect(placed[0].order).toBe(1);
    expect(placed[0].login).toBe("j-metrics");
    expect(placed[0].text).toBe("Body text.");
    expect(placed[0].revision).toBe("abc1234");
  });

  it("marks a reworded passage as drifted", () => {
    const body = anchoredBody(2, 3, "verified");
    const edited = refs([
      SENTENCES[0],
      SENTENCES[1],
      "The separation constant may be taken as C = 4√2, an absolute constant.",
      SENTENCES[3],
    ]);
    const placed = placeComments([fetched({ body })], "wp7", edited);
    expect(placed[0].kind).toBe("drifted");
    expect(placed[0].sids).toEqual(["b0-s2"]);
  });

  it("archives a quote that no longer exists anywhere", () => {
    const body = anchoredBody(2, 3, "problem");
    const rewritten = refs([SENTENCES[0], SENTENCES[1], "Nothing like the old sentence at all.", SENTENCES[3]]);
    const placed = placeComments([fetched({ body })], "wp7", rewritten);
    expect(placed[0].kind).toBe("archived");
    expect(placed[0].sids).toEqual([]);
    // The archive still shows what the passage used to say.
    expect(placed[0].quote).toBe(SENTENCES[2]);
  });

  it("renders a hand-written GitHub reply as a general comment", () => {
    const placed = placeComments(
      [fetched({ body: "Just replying from github.com, no metadata header." })],
      "wp7",
      refs(),
    );
    expect(placed[0].kind).toBe("general");
    expect(placed[0].tag).toBe("none");
    expect(placed[0].text).toBe("Just replying from github.com, no metadata header.");
  });

  it("degrades a hostile anchor to a general comment instead of hanging", () => {
    const hostile = serializeComment({
      meta: {
        v: 1,
        paper: "wp7",
        tag: "problem",
        anchor: { exact: "x".repeat(50000), prefix: "", suffix: "", count: 100000 },
      },
      text: "boom",
    });
    const started = Date.now();
    const placed = placeComments([fetched({ body: hostile })], "wp7", refs());
    expect(placed[0].kind).toBe("general");
    expect(Date.now() - started).toBeLessThan(500);
  });

  it("falls back to initials for an avatar that is not on GitHub's avatar host", () => {
    const placed = placeComments(
      [
        fetched({
          body: "hi",
          author: { login: "evil", avatarUrl: "javascript:alert(1)" },
        }),
      ],
      "wp7",
      refs(),
    );
    expect(placed[0].avatarUrl).toBeNull();
  });

  it("survives a missing author and a body that is not a string", () => {
    const placed = placeComments(
      [{ id: "C_x", body: undefined as unknown as string, createdAt: "", url: "", author: null }],
      "wp7",
      refs(),
    );
    expect(placed[0].login).toBe("ghost");
    expect(placed[0].kind).toBe("general");
  });
});

describe("grouping, ordering and counts", () => {
  const groups = () => {
    const placed = placeComments(
      [
        fetched({ id: "c3", body: anchoredBody(3, 4, "problem"), createdAt: "2026-08-20T00:00:00Z" }),
        fetched({ id: "c1", body: anchoredBody(0, 1, "verified"), createdAt: "2026-08-19T00:00:00Z" }),
        fetched({ id: "cg", body: "page level", createdAt: "2026-08-18T00:00:00Z" }),
      ],
      "wp7",
      refs(),
    );
    return groupComments(placed);
  };

  it("orders rail cards by position in the paper, not by post time", () => {
    expect(groups().placed.map((c) => c.id)).toEqual(["c1", "c3"]);
  });

  it("keeps unanchored comments in their own tail group", () => {
    expect(groups().general.map((c) => c.id)).toEqual(["cg"]);
    expect(groups().archived).toEqual([]);
  });

  it("writes the rail-head counts", () => {
    expect(countLabel(activeComments(groups()))).toBe("1 verified · 1 problem · 3 total");
  });

  it("counts plural problems and drops empty groups", () => {
    const placed = placeComments(
      [
        fetched({ id: "p1", body: anchoredBody(0, 1, "problem") }),
        fetched({ id: "p2", body: anchoredBody(1, 2, "problem") }),
      ],
      "wp7",
      refs(),
    );
    expect(countLabel(placed)).toBe("2 problems · 2 total");
    expect(countLabel([])).toBe("0 total");
  });

  it("does not count a drifted verification as verified", () => {
    const edited = refs([
      "We study the ATE under a weak-overlap condition.",
      ...SENTENCES.slice(1),
    ]);
    const placed = placeComments([fetched({ body: anchoredBody(0, 1, "verified") })], "wp7", edited);
    expect(placed[0].kind).toBe("drifted");
    expect(countLabel(placed)).toBe("1 total");
  });
});

describe("highlightPlan", () => {
  it("gives each sentence one highlight, strongest tag winning", () => {
    const placed = placeComments(
      [
        fetched({ id: "a", body: anchoredBody(1, 2, "none") }),
        fetched({ id: "b", body: anchoredBody(1, 2, "problem") }),
        fetched({ id: "c", body: anchoredBody(2, 3, "verified") }),
      ],
      "wp7",
      refs(),
    );
    const plan = highlightPlan(placed);
    expect(plan.get("b0-s1")).toEqual({ tag: "problem", drift: false });
    expect(plan.get("b0-s2")).toEqual({ tag: "verified", drift: false });
    expect(plan.has("b0-s0")).toBe(false);
  });

  it("keeps a sentence solid when any comment on it still anchors exactly", () => {
    const edited = refs([
      SENTENCES[0],
      "The lower bound uses Le Cam's classic two-point method.",
      SENTENCES[2],
      SENTENCES[3],
    ]);
    const placed = placeComments(
      [
        fetched({ id: "drift", body: anchoredBody(1, 2, "none") }),
        fetched({ id: "exact", body: serializeComment({
          meta: { v: 1, paper: "wp7", tag: "none", anchor: makeAnchor(edited, 1, 2) },
          text: "current",
        }) }),
      ],
      "wp7",
      edited,
    );
    expect(highlightPlan(placed).get("b0-s1")).toEqual({ tag: "none", drift: false });
  });
});

describe("notes and labels", () => {
  it("demotes a drifted verification loudly and everything else mildly", () => {
    expect(driftNote("verified").strong).toBe(true);
    expect(driftNote("verified").text).toContain("may need re-checking");
    expect(driftNote("problem").strong).toBe(false);
    expect(driftNote("none").strong).toBe(false);
  });

  it("tells an archived reader what became of the passage", () => {
    expect(archivedNote("problem")).toContain("possibly addressed");
    expect(archivedNote("verified")).toContain("earlier version");
    expect(archivedNote("none")).toContain("rewritten");
  });

  it("writes the snap note, initials, dates and truncation", () => {
    expect(snapNote(1)).toBe("(snapped to 1 sentence)");
    expect(snapNote(3)).toBe("(snapped to 3 sentences)");
    expect(initialsOf("j-metrics")).toBe("JM");
    expect(initialsOf("octocat")).toBe("OC");
    expect(formatWhen("2026-08-21T10:00:00Z")).toBe("2026-08-21");
    expect(formatWhen("not a date")).toBe("");
    expect(truncate("abcdef", 4)).toBe("abc…");
    expect(truncate("abc", 10)).toBe("abc");
  });

  it("accepts only GitHub's avatar host", () => {
    expect(isSafeAvatarUrl("https://avatars.githubusercontent.com/u/1?v=4")).toBe(true);
    expect(isSafeAvatarUrl("https://avatars.githubusercontent.evil.com/u/1")).toBe(false);
    expect(isSafeAvatarUrl("http://avatars.githubusercontent.com/u/1")).toBe(false);
    expect(isSafeAvatarUrl('https://avatars.githubusercontent.com/u/1" onerror="x')).toBe(false);
    expect(isSafeAvatarUrl(undefined)).toBe(false);
  });
});

describe("replies", () => {
  const withReplies = (replies: unknown) =>
    placeComments(
      [{ ...fetched({ body: "parent" }), replies } as never],
      "wp7",
      refs(),
    )[0];

  it("carries the worker's replies through onto the comment", () => {
    const c = withReplies([
      {
        id: "R_1",
        body: "Agreed — the constant checks out.",
        createdAt: "2026-08-22T09:00:00Z",
        url: "https://github.com/o/r/discussions/1#discussioncomment-9",
        author: { login: "s-reader", avatarUrl: "https://avatars.githubusercontent.com/u/2?v=4" },
      },
    ]);
    expect(c.replies).toHaveLength(1);
    expect(c.replies[0].login).toBe("s-reader");
    expect(c.replies[0].text).toBe("Agreed — the constant checks out.");
    expect(c.replies[0].avatarUrl).toBe("https://avatars.githubusercontent.com/u/2?v=4");
  });

  it("defaults to an empty thread when the worker sends none", () => {
    expect(placeComments([fetched({ body: "hi" })], "wp7", refs())[0].replies).toEqual([]);
    expect(withReplies(undefined).replies).toEqual([]);
    expect(withReplies("not an array").replies).toEqual([]);
  });

  it("strips a metadata header someone attached to a reply on github.com", () => {
    const smuggled = serializeComment({
      meta: { v: 1, paper: "wp7", tag: "verified", anchor: makeAnchor(refs(), 0, 1) },
      text: "Just a reply, really.",
    });
    const c = withReplies([
      { id: "R_2", body: smuggled, createdAt: "", url: "", author: null },
    ]);
    // Only the readable remainder survives — no tag, no anchor, nothing a reply
    // could use to claim a passage of its own.
    expect(c.replies[0].text).toBe("Just a reply, really.");
    expect(c.replies[0]).not.toHaveProperty("tag");
    expect(c.replies[0]).not.toHaveProperty("anchor");
    expect(c.replies[0].login).toBe("ghost");
  });

  it("keeps a hostile reply body as inert text", () => {
    const c = withReplies([
      {
        id: "R_3",
        body: '<script>alert(1)</script><img src=x onerror=alert(1)>',
        createdAt: "",
        url: "",
        author: { login: "evil", avatarUrl: "javascript:alert(1)" },
      },
    ]);
    expect(c.replies[0].text).toBe('<script>alert(1)</script><img src=x onerror=alert(1)>');
    expect(c.replies[0].avatarUrl).toBeNull();
  });

  it("drops malformed entries instead of rendering junk", () => {
    expect(placeReplies([null, { body: "no id" }, 7], "wp7")).toEqual([]);
  });

  it("posts a reply as bare text — no metadata header", () => {
    const body = serializeReply("  Agreed.  ");
    expect(body).toBe("Agreed.");
    expect(body).not.toContain("causalsmith:comment");
    expect(serializeReply("x".repeat(20000)).length).toBe(MAX_TEXT_CHARS);
  });

  it("passes both ids and the body as GraphQL variables", () => {
    const req = addReplyMutation('D_1") { x } #', 'DC_2") { y } #', 'body") { z } #');
    expect(req.query).toContain("addDiscussionComment");
    expect(req.query).toContain("$replyToId: ID!");
    expect(req.query).not.toContain("{ x }");
    expect(req.query).not.toContain("{ y }");
    expect(req.query).not.toContain("{ z }");
    expect(req.variables).toEqual({
      discussionId: 'D_1") { x } #',
      replyToId: 'DC_2") { y } #',
      body: 'body") { z } #',
    });
  });

  it("labels the collapsed toggle", () => {
    expect(replyCountLabel(1)).toBe("1 reply");
    expect(replyCountLabel(3)).toBe("3 replies");
  });
});

describe("ownsComment", () => {
  const mine = () => placeComments([fetched({ body: "hi" })], "wp7", refs())[0];

  it("offers nothing while no viewer is loaded", () => {
    expect(ownsComment(mine(), null)).toBe(false);
    expect(ownsComment(mine(), {})).toBe(false);
    expect(ownsComment(mine(), { login: "" })).toBe(false);
  });

  it("matches the author's login, ignoring case", () => {
    expect(ownsComment(mine(), { login: "j-metrics" })).toBe(true);
    expect(ownsComment(mine(), { login: "J-Metrics" })).toBe(true);
  });

  it("refuses someone else's comment", () => {
    expect(ownsComment(mine(), { login: "someone-else" })).toBe(false);
    // A comment whose author GitHub could not resolve is nobody's to delete.
    const ghost = placeComments(
      [{ id: "g", body: "hi", createdAt: "", url: "", author: null }],
      "wp7",
      refs(),
    )[0];
    expect(ownsComment(ghost, { login: "ghost-hunter" })).toBe(false);
  });
});

describe("outgoing wire format", () => {
  it("round-trips through the schema with the anchor and revision attached", () => {
    const anchor = makeAnchor(refs(), 0, 2);
    const body = newCommentBody({
      paper: "wp7",
      tag: "verified",
      text: "Checked against the Lean declaration.",
      anchor,
      revision: "d2bf655",
    });
    const parsed = parseComment(body, "wp7");
    expect(parsed.meta.tag).toBe("verified");
    expect(parsed.meta.anchor).toEqual(anchor);
    expect(parsed.meta.revision).toBe("d2bf655");
    expect(parsed.text).toBe("Checked against the Lean declaration.");
  });

  it("caps the posted text length", () => {
    const body = newCommentBody({ paper: "wp7", tag: "none", text: "x".repeat(20000) });
    expect(parseComment(body, "wp7").text.length).toBe(10000);
  });

  it("passes user text as a GraphQL VARIABLE, never spliced into the query", () => {
    const body = newCommentBody({ paper: "wp7", tag: "none", text: 'a") { evil } #' });
    const req = addCommentMutation("D_kwDO", body);
    expect(req.query).not.toContain("evil");
    expect(req.variables).toEqual({ discussionId: "D_kwDO", body });
    expect(req.query).toContain("$body: String!");
  });

  it("passes the comment id to the delete mutation as a variable", () => {
    const req = deleteCommentMutation('DC_evil") { x } #');
    expect(req.query).toContain("deleteDiscussionComment");
    expect(req.query).toContain("$id: ID!");
    expect(req.query).not.toContain("evil");
    expect(req.variables).toEqual({ id: 'DC_evil") { x } #' });
  });

  it("exposes no way for the client to create a discussion", () => {
    // Threads are maintainer-provisioned; the client must not be able to create
    // one (that would make a random visitor the thread owner).
    expect((model as Record<string, unknown>).createDiscussionMutation).toBeUndefined();
  });
});

describe("placement is bounded against a flood of comments", () => {
  // A 400-char anchor whose text matches nothing in the page — the worst case
  // for re-anchoring, and exactly what a DoS attempt would post en masse.
  function junkComment(i: number): FetchedComment {
    const junk = `zzz ${"q".repeat(400)} ${i}`.slice(0, MAX_EXACT_CHARS);
    const body = serializeComment({
      meta: {
        v: 1,
        paper: "wp7",
        tag: "none",
        anchor: { exact: junk, prefix: "", suffix: "", count: MAX_ANCHOR_COUNT },
      },
      text: `comment ${i}`,
    });
    return fetched({ id: `C_${i}`, body });
  }

  const flood = (n: number) => Array.from({ length: n }, (_, i) => junkComment(i));

  it("places 100 junk-anchor comments well under a second", () => {
    const started = performance.now();
    const placed = placeComments(flood(100), "wp7", refs());
    const elapsed = performance.now() - started;
    expect(placed).toHaveLength(100);
    expect(elapsed).toBeLessThan(1000);
  });

  it("re-anchors at most the cap, showing the rest unanchored (no silent drop)", () => {
    const { placed, overflow } = placeCommentsBudgeted(flood(100), "wp7", refs());
    // None of the junk anchors match, so the re-anchored ones archive; the rest
    // are shown as general comments and counted as overflow.
    const archived = placed.filter((c) => c.kind === "archived").length;
    const general = placed.filter((c) => c.kind === "general").length;
    expect(archived).toBe(MAX_ANCHORED_COMMENTS);
    expect(general).toBe(100 - MAX_ANCHORED_COMMENTS);
    expect(overflow).toBe(100 - MAX_ANCHORED_COMMENTS);
    // Nothing is lost — every comment is still present, just placed differently.
    expect(placed).toHaveLength(100);
  });

  it("places asynchronously in batches, yielding to the event loop", async () => {
    const batches: number[] = [];
    const { placed, overflow } = await placeCommentsAsync(
      flood(35),
      "wp7",
      refs(),
      (soFar, done) => batches.push(done ? -soFar.length : soFar.length),
    );
    expect(placed).toHaveLength(35);
    // The default batch size is 10, so several progress callbacks land before
    // the final (negative-marked) one — proof the pass was chunked, not one shot.
    expect(batches.length).toBeGreaterThan(2);
    expect(batches[batches.length - 1]).toBe(-35);
    expect(overflow).toBe(0); // 35 < the cap, so all re-anchored
  });
});

describe("mergeComments keeps optimistic posts across hydration batches", () => {
  const server = (id: string): model.PlacedComment => ({
    id,
    login: "s-reader",
    avatarUrl: null,
    createdAt: "2026-08-20T00:00:00Z",
    tag: "none",
    text: `server ${id}`,
    kind: "anchored",
    sids: ["b0-s0"],
    quote: "q",
    revision: null,
    order: 0,
    replies: [],
  });
  const localComment = (id: string): model.PlacedComment => ({ ...server(id), login: "you", text: "my new comment" });
  const localReply = (id: string): model.PlacedReply => ({
    id,
    login: "you",
    avatarUrl: null,
    createdAt: "2026-08-24T00:00:00Z",
    text: "my new reply",
  });
  const base = () => ({
    serverAll: [] as model.PlacedComment[],
    localComments: [] as model.PlacedComment[],
    localReplies: new Map<string, model.PlacedReply[]>(),
    deleted: new Set<string>(),
  });

  it("a comment posted mid-hydration survives the next server batch", () => {
    const s = base();
    // Post before any server data has arrived.
    s.localComments.push(localComment("local-1"));
    expect(mergeComments(s).map((c) => c.id)).toEqual(["local-1"]);
    // A hydration batch overwrites the server snapshot wholesale…
    s.serverAll = [server("C_1"), server("C_2")];
    const merged = mergeComments(s);
    // …and the optimistic comment is STILL there (was the bug: it vanished).
    expect(merged.map((c) => c.id).sort()).toEqual(["C_1", "C_2", "local-1"]);
  });

  it("a reply posted mid-hydration survives a batch that replaces its parent", () => {
    const s = base();
    s.serverAll = [server("C_1")];
    s.localReplies.set("C_1", [localReply("local-r1")]);
    // A later batch delivers a FRESH C_1 object (no replies) — the reply must
    // re-attach, not disappear.
    s.serverAll = [{ ...server("C_1"), replies: [] }];
    const parent = mergeComments(s).find((c) => c.id === "C_1")!;
    expect(parent.replies.map((r) => r.id)).toEqual(["local-r1"]);
  });

  it("does not duplicate a reply the server batch has now caught up with", () => {
    const s = base();
    s.localReplies.set("C_1", [localReply("R_9")]);
    // The server now returns C_1 already carrying reply R_9.
    s.serverAll = [{ ...server("C_1"), replies: [localReply("R_9")] }];
    const parent = mergeComments(s).find((c) => c.id === "C_1")!;
    expect(parent.replies.filter((r) => r.id === "R_9")).toHaveLength(1);
  });

  it("filters a deleted comment or reply even if a batch still carries it", () => {
    const s = base();
    s.serverAll = [{ ...server("C_1"), replies: [localReply("R_1")] }, server("C_2")];
    s.deleted.add("C_2");
    s.deleted.add("R_1");
    const merged = mergeComments(s);
    expect(merged.map((c) => c.id)).toEqual(["C_1"]);
    expect(merged[0].replies).toEqual([]);
  });
});
