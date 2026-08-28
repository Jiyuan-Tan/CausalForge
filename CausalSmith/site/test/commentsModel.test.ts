// Pure model layer for paper-page comments: placement against the current
// text, grouping/ordering for the rail, the label strings, the hostile-input
// caps, and the GraphQL bodies. No DOM here — the DOM layer is covered in
// test/commentsDom.test.ts.

import { describe, expect, it } from "vitest";
import { makeAnchor, type SentenceRef } from "../src/lib/comments/anchor.js";
import * as model from "../src/scripts/comments/model.js";
import {
  MAX_ANCHOR_COUNT,
  MAX_ANCHORED_COMMENTS,
  MAX_EXACT_CHARS,
  MAX_TEXT_CHARS,
  activeComments,
  archivedNote,
  countLabel,
  driftNote,
  formatWhen,
  groupComments,
  highlightPlan,
  initialsOf,
  isSafeAvatarUrl,
  mergeComments,
  newCommentPayload,
  ownsComment,
  placeComments,
  placeCommentsAsync,
  placeCommentsBudgeted,
  placeReplies,
  replyCountLabel,
  newReplyPayload,
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

function fetched(over: Partial<FetchedComment>): FetchedComment {
  return {
    id: over.id ?? "C_1",
    text: over.text ?? "Body text.",
    createdAt: over.createdAt ?? "2026-08-21T10:00:00Z",
    author:
      "author" in over
        ? over.author!
        : { login: "j-metrics", avatarUrl: "https://avatars.githubusercontent.com/u/1?v=4" },
    tag: over.tag,
    anchor: over.anchor,
    revision: over.revision,
    replies: over.replies,
  };
}

/** The worker's stored fields for a comment anchored to sentences start..end. */
function anchoredFields(start: number, end: number, tag: "none" | "verified" | "problem" = "none") {
  return { tag, anchor: makeAnchor(refs(), start, end), revision: "abc1234", text: "Body text." };
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
    const placed = placeComments([fetched({ ...anchoredFields(1, 3) })], "wp7", refs());
    expect(placed).toHaveLength(1);
    expect(placed[0].kind).toBe("anchored");
    expect(placed[0].sids).toEqual(["b0-s1", "b0-s2"]);
    expect(placed[0].order).toBe(1);
    expect(placed[0].login).toBe("j-metrics");
    expect(placed[0].text).toBe("Body text.");
    expect(placed[0].revision).toBe("abc1234");
  });

  it("marks a reworded passage as drifted", () => {
    const fields = anchoredFields(2, 3, "verified");
    const edited = refs([
      SENTENCES[0],
      SENTENCES[1],
      "The separation constant may be taken as C = 4√2, an absolute constant.",
      SENTENCES[3],
    ]);
    const placed = placeComments([fetched(fields)], "wp7", edited);
    expect(placed[0].kind).toBe("drifted");
    expect(placed[0].sids).toEqual(["b0-s2"]);
  });

  it("archives a quote that no longer exists anywhere", () => {
    const fields = anchoredFields(2, 3, "problem");
    const rewritten = refs([SENTENCES[0], SENTENCES[1], "Nothing like the old sentence at all.", SENTENCES[3]]);
    const placed = placeComments([fetched(fields)], "wp7", rewritten);
    expect(placed[0].kind).toBe("archived");
    expect(placed[0].sids).toEqual([]);
    // The archive still shows what the passage used to say.
    expect(placed[0].quote).toBe(SENTENCES[2]);
  });

  it("renders an unanchored comment at page level", () => {
    const placed = placeComments(
      [fetched({ text: "A page-level comment with no anchor." })],
      "wp7",
      refs(),
    );
    expect(placed[0].kind).toBe("general");
    expect(placed[0].tag).toBe("none");
    expect(placed[0].text).toBe("A page-level comment with no anchor.");
  });

  it("degrades a hostile anchor to a general comment instead of hanging", () => {
    const started = Date.now();
    const placed = placeComments(
      [
        fetched({
          tag: "problem",
          text: "boom",
          anchor: { exact: "x".repeat(50000), prefix: "", suffix: "", count: 100000 },
        }),
      ],
      "wp7",
      refs(),
    );
    expect(placed[0].kind).toBe("general");
    expect(Date.now() - started).toBeLessThan(500);
  });

  it("falls back to initials for an avatar that is not on GitHub's avatar host", () => {
    const placed = placeComments(
      [
        fetched({
          text: "hi",
          author: { login: "evil", avatarUrl: "javascript:alert(1)" },
        }),
      ],
      "wp7",
      refs(),
    );
    expect(placed[0].avatarUrl).toBeNull();
  });

  it("survives a missing author and a text that is not a string", () => {
    const placed = placeComments(
      [{ id: "C_x", text: undefined as unknown as string, createdAt: "", author: null }],
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
        fetched({ id: "c3", ...anchoredFields(3, 4, "problem"), createdAt: "2026-08-20T00:00:00Z" }),
        fetched({ id: "c1", ...anchoredFields(0, 1, "verified"), createdAt: "2026-08-19T00:00:00Z" }),
        fetched({ id: "cg", text: "page level", createdAt: "2026-08-18T00:00:00Z" }),
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
        fetched({ id: "p1", ...anchoredFields(0, 1, "problem") }),
        fetched({ id: "p2", ...anchoredFields(1, 2, "problem") }),
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
    const placed = placeComments([fetched({ ...anchoredFields(0, 1, "verified") })], "wp7", edited);
    expect(placed[0].kind).toBe("drifted");
    expect(countLabel(placed)).toBe("1 total");
  });
});

describe("highlightPlan", () => {
  it("gives each sentence one highlight, strongest tag winning", () => {
    const placed = placeComments(
      [
        fetched({ id: "a", ...anchoredFields(1, 2, "none") }),
        fetched({ id: "b", ...anchoredFields(1, 2, "problem") }),
        fetched({ id: "c", ...anchoredFields(2, 3, "verified") }),
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
        fetched({ id: "drift", ...anchoredFields(1, 2, "none") }),
        fetched({ id: "exact", tag: "none", anchor: makeAnchor(edited, 1, 2), text: "current" }),
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
      [{ ...fetched({ text: "parent" }), replies } as never],
      "wp7",
      refs(),
    )[0];

  it("carries the worker's replies through onto the comment", () => {
    const c = withReplies([
      {
        id: "R_1",
        text: "Agreed — the constant checks out.",
        createdAt: "2026-08-22T09:00:00Z",
        author: { login: "s-reader", avatarUrl: "https://avatars.githubusercontent.com/u/2?v=4" },
      },
    ]);
    expect(c.replies).toHaveLength(1);
    expect(c.replies[0].login).toBe("s-reader");
    expect(c.replies[0].text).toBe("Agreed — the constant checks out.");
    expect(c.replies[0].avatarUrl).toBe("https://avatars.githubusercontent.com/u/2?v=4");
  });

  it("defaults to an empty thread when the worker sends none", () => {
    expect(placeComments([fetched({ text: "hi" })], "wp7", refs())[0].replies).toEqual([]);
    expect(withReplies(undefined).replies).toEqual([]);
    expect(withReplies("not an array").replies).toEqual([]);
  });

  it("gives a reply no tag and no anchor of its own", () => {
    // A reply inherits its parent's placement. Even if the worker ever sent
    // these fields, a reply must not be able to claim a passage.
    const c = withReplies([
      {
        id: "R_2",
        text: "Just a reply, really.",
        tag: "verified",
        anchor: makeAnchor(refs(), 0, 1),
        createdAt: "",
        author: null,
      },
    ]);
    expect(c.replies[0].text).toBe("Just a reply, really.");
    expect(c.replies[0]).not.toHaveProperty("tag");
    expect(c.replies[0]).not.toHaveProperty("anchor");
    expect(c.replies[0].login).toBe("ghost");
  });

  it("keeps a hostile reply body as inert text", () => {
    const c = withReplies([
      {
        id: "R_3",
        text: '<script>alert(1)</script><img src=x onerror=alert(1)>',
        createdAt: "",
        author: { login: "evil", avatarUrl: "javascript:alert(1)" },
      },
    ]);
    expect(c.replies[0].text).toBe('<script>alert(1)</script><img src=x onerror=alert(1)>');
    expect(c.replies[0].avatarUrl).toBeNull();
  });

  it("drops malformed entries instead of rendering junk", () => {
    expect(placeReplies([null, { text: "no id" }, 7])).toEqual([]);
  });

  it("posts a reply as its text plus the parent it answers", () => {
    const payload = newReplyPayload("wp7", "abc123", "  Agreed.  ");
    expect(payload).toEqual({ paper: "wp7", parentId: "abc123", text: "Agreed." });
    expect(newReplyPayload("wp7", "abc123", "x".repeat(20000)).text.length).toBe(MAX_TEXT_CHARS);
  });

  it("labels the collapsed toggle", () => {
    expect(replyCountLabel(1)).toBe("1 reply");
    expect(replyCountLabel(3)).toBe("3 replies");
  });
});

describe("ownsComment", () => {
  const mine = () => placeComments([fetched({ text: "hi" })], "wp7", refs())[0];

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
      [{ id: "g", text: "hi", createdAt: "", author: null }],
      "wp7",
      refs(),
    )[0];
    expect(ownsComment(ghost, { login: "ghost-hunter" })).toBe(false);
  });
});

describe("outgoing wire format", () => {
  it("sends the anchor and revision as structured fields", () => {
    const anchor = makeAnchor(refs(), 0, 2);
    expect(
      newCommentPayload({
        paper: "wp7",
        tag: "verified",
        text: "Checked against the Lean declaration.",
        anchor,
        revision: "d2bf655",
      }),
    ).toEqual({
      paper: "wp7",
      tag: "verified",
      text: "Checked against the Lean declaration.",
      anchor,
      revision: "d2bf655",
    });
  });

  it("omits an absent anchor and revision rather than sending nulls", () => {
    expect(newCommentPayload({ paper: "wp7", tag: "none", text: "hi" })).toEqual({
      paper: "wp7",
      tag: "none",
      text: "hi",
    });
  });

  it("caps the posted text length", () => {
    expect(
      newCommentPayload({ paper: "wp7", tag: "none", text: "x".repeat(20000) }).text,
    ).toHaveLength(10000);
  });

  it("never names an author — the worker resolves that from the token", () => {
    const payload = newCommentPayload({ paper: "wp7", tag: "none", text: "hi" });
    expect(payload).not.toHaveProperty("author");
    expect(payload).not.toHaveProperty("login");
  });

  it("exposes no way for the client to write to GitHub at all", () => {
    // Comments no longer live in a repository, so the browser holds no
    // credential GitHub would accept for anything. A leftover mutation builder
    // would be a live path back to writing as the visitor.
    const m = model as Record<string, unknown>;
    expect(m.createDiscussionMutation).toBeUndefined();
    expect(m.addCommentMutation).toBeUndefined();
    expect(m.addReplyMutation).toBeUndefined();
    expect(m.deleteCommentMutation).toBeUndefined();
  });
});

describe("placement is bounded against a flood of comments", () => {
  // A 400-char anchor whose text matches nothing in the page — the worst case
  // for re-anchoring, and exactly what a DoS attempt would post en masse.
  function junkComment(i: number): FetchedComment {
    const junk = `zzz ${"q".repeat(400)} ${i}`.slice(0, MAX_EXACT_CHARS);
    return fetched({
      id: `C_${i}`,
      tag: "none",
      anchor: { exact: junk, prefix: "", suffix: "", count: MAX_ANCHOR_COUNT },
      text: `comment ${i}`,
    });
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

describe("reanchor with a wire-truncated quote", () => {
  // The worker historically clipped anchor.exact to 400 chars, cutting a long
  // multi-sentence quote mid-formula — full-equality matching then reported
  // "drifted" on the very text the comment was written against (seen live on
  // the loggap paper). The prefix pass must re-anchor such quotes exactly.
  const longSentences: SentenceRef[] = Array.from({ length: 12 }, (_, i) => ({
    id: `s${i}`,
    text:
      `Sentence ${i} states that the estimator envelope E_${i}(n,d,eps) dominates ` +
      `the truncated comparison sup_{P in D_${i}} E_P[(tau-psi(P))^2] for every ` +
      `measurable candidate under the product-law embedding of block ${i}.`,
  }));

  it("re-anchors a clipped 5-sentence quote as anchored, not drifted", async () => {
    const { reanchor } = await import("../src/lib/comments/anchor.js");
    const full = makeAnchor(longSentences, 4, 9);
    expect(full.exact.length).toBeGreaterThan(400); // the clip actually bites
    const clipped = { ...full, exact: full.exact.slice(0, 400) };
    const m = reanchor(clipped, longSentences);
    expect(m).toMatchObject({ state: "anchored", start: 4, end: 9, score: 1 });
  });

  it("a short quote gains no spurious prefix matches", async () => {
    const { reanchor } = await import("../src/lib/comments/anchor.js");
    const short = { exact: "Sentence 4 states", prefix: "", suffix: "", count: 1 };
    const m = reanchor(short, longSentences);
    expect(m.state).not.toBe("anchored"); // below the prefix-pass floor; fuzzy rules apply
  });
});
