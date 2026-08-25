// @vitest-environment happy-dom
//
// Rendering layer. The point of these tests is the security boundary: comment
// bodies, author logins and quotes come from a public GitHub Discussion, so a
// hostile string must land in the page as TEXT and never as markup.

import { beforeEach, describe, expect, it } from "vitest";
import {
  queryUi,
  renderArchived,
  renderHighlights,
  renderRail,
  renderThreadLink,
  type CardHandlers,
  type CommentsUi,
} from "../src/scripts/comments/render.js";
import { collectSidElements } from "../src/scripts/commentsDom.js";
import {
  groupComments,
  type PlacedComment,
  type PlacedReply,
} from "../src/scripts/comments/model.js";

const SHELL = `
<div class="cs-comments" id="cs-comments" hidden>
  <aside class="cs-rail" id="cs-rail">
    <div class="cs-rail-head">
      Reader commentary <span id="cs-rail-count"></span>
      <a id="cs-rail-thread" href="#" hidden>thread</a>
    </div>
    <div id="cs-rail-cards"></div>
    <div id="cs-rail-general"></div>
    <p id="cs-rail-empty"></p>
  </aside>
  <details id="cs-archived" hidden>
    <summary id="cs-archived-summary"></summary>
    <div id="cs-archived-list"></div>
  </details>
  <button id="cs-selbtn" hidden></button>
  <div id="cs-composer" hidden>
    <p><em id="cs-quote"></em> <span id="cs-snap"></span></p>
    <div id="cs-seg"><button data-tag="none"></button></div>
    <p id="cs-tagnote"></p>
    <textarea id="cs-text"></textarea>
    <p id="cs-counter"></p>
    <p id="cs-status"></p>
    <span id="cs-idchip"></span>
    <button id="cs-signin"></button>
    <button id="cs-cancel"></button>
    <button id="cs-post"></button>
  </div>
</div>`;

const NOOP = { onHover: () => {}, onActivate: () => {} };

function comment(over: Partial<PlacedComment>): PlacedComment {
  return {
    id: "c1",
    login: "j-metrics",
    avatarUrl: null,
    createdAt: "2026-08-21T10:00:00Z",
    tag: "none",
    text: "A plain comment.",
    kind: "anchored",
    sids: ["b0-s0"],
    quote: "We study the ATE under weak overlap.",
    revision: null,
    order: 0,
    replies: [],
    ...over,
  };
}

function mount(): { ui: CommentsUi; body: HTMLElement } {
  document.body.innerHTML = `<div id="paper-body"><p><span class="cs-s" data-sid="b0-s0">One.</span> <span class="cs-s" data-sid="b0-s1">Two.</span></p></div>${SHELL}`;
  const ui = queryUi();
  if (!ui) throw new Error("shell not found");
  return { ui, body: document.getElementById("paper-body") as HTMLElement };
}

beforeEach(() => {
  document.body.innerHTML = "";
});

describe("renderRail", () => {
  it("renders a hostile comment body and login as text, never as markup", () => {
    const { ui } = mount();
    const hostile = comment({
      login: '<img src=x onerror="alert(1)">',
      text: '<script>alert("xss")</script><img src=x onerror=alert(1)>',
      quote: "</span><iframe src=evil>",
    });
    renderRail(ui, groupComments([hostile]), NOOP);
    const card = ui.railCards.querySelector(".cs-card") as HTMLElement;
    expect(card.querySelectorAll("script, img, iframe").length).toBe(0);
    expect(card.querySelector(".cs-body")?.textContent).toBe(
      '<script>alert("xss")</script><img src=x onerror=alert(1)>',
    );
    expect(card.querySelector(".cs-name")?.textContent).toBe('<img src=x onerror="alert(1)">');
    expect(card.querySelector(".cs-quote")?.textContent).toContain("</span><iframe src=evil>");
    // The initials fallback stands in for the (absent) avatar.
    expect(card.querySelector(".cs-av")?.tagName).toBe("SPAN");
  });

  it("shows an avatar image only for a GitHub avatar URL", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([comment({ avatarUrl: "https://avatars.githubusercontent.com/u/1?v=4" })]),
      NOOP,
    );
    const av = ui.railCards.querySelector(".cs-av") as HTMLImageElement;
    expect(av.tagName).toBe("IMG");
    expect(av.getAttribute("src")).toBe("https://avatars.githubusercontent.com/u/1?v=4");
    expect(av.getAttribute("referrerpolicy")).toBe("no-referrer");
  });

  it("puts a drifted verification's demotion note on its card", () => {
    const { ui } = mount();
    renderRail(ui, groupComments([comment({ kind: "drifted", tag: "verified" })]), NOOP);
    const note = ui.railCards.querySelector(".cs-drift-note") as HTMLElement;
    expect(note.classList.contains("cs-strong")).toBe(true);
    expect(note.textContent).toContain("may need re-checking");
    expect(ui.railCards.querySelector(".cs-tagb")?.textContent).toBe("✅ Verified");
  });

  it("collects unanchored comments under a General comments heading", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([comment({ kind: "general", id: "g1", quote: "" }), comment({ id: "a1" })]),
      NOOP,
    );
    expect(ui.railCards.querySelectorAll(".cs-card").length).toBe(1);
    expect(ui.railGeneral.querySelector(".cs-group-head")?.textContent).toBe("General comments");
    expect(ui.railGeneral.querySelectorAll(".cs-card").length).toBe(1);
    expect(ui.railEmpty.hidden).toBe(true);
  });

  it("shows the empty note when nothing is placed", () => {
    const { ui } = mount();
    renderRail(ui, groupComments([]), NOOP);
    expect(ui.railEmpty.hidden).toBe(false);
    expect(ui.railCards.childElementCount).toBe(0);
  });

  it("replaces the previous render rather than appending to it", () => {
    const { ui } = mount();
    renderRail(ui, groupComments([comment({})]), NOOP);
    renderRail(ui, groupComments([comment({})]), NOOP);
    expect(ui.railCards.querySelectorAll(".cs-card").length).toBe(1);
  });
});

describe("delete affordance", () => {
  /** Handlers that offer deletion only for comments by `viewer`. */
  const asViewer = (viewer: string | null, onDelete = () => {}) => ({
    ...NOOP,
    canDelete: (c: PlacedComment) =>
      viewer !== null && c.login.toLowerCase() === viewer.toLowerCase(),
    onDelete,
  });

  it("shows a real delete button only on the viewer's own cards", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([
        comment({ id: "mine", login: "j-metrics" }),
        comment({ id: "theirs", login: "someone-else", order: 1, sids: ["b0-s1"] }),
      ]),
      asViewer("J-Metrics"),
    );
    const cards = Array.from(ui.railCards.querySelectorAll(".cs-card"));
    const own = cards.find((c) => c.getAttribute("data-cid") === "mine") as HTMLElement;
    const other = cards.find((c) => c.getAttribute("data-cid") === "theirs") as HTMLElement;
    const btn = own.querySelector(".cs-del") as HTMLButtonElement;
    expect(btn.tagName).toBe("BUTTON");
    expect(btn.getAttribute("type")).toBe("button");
    expect(btn.getAttribute("aria-label")).toBe("Delete your comment");
    expect(other.querySelector(".cs-del-wrap")).toBeNull();
  });

  it("shows nothing at all while no viewer is signed in", () => {
    const { ui } = mount();
    renderRail(ui, groupComments([comment({})]), asViewer(null));
    expect(ui.railCards.querySelector(".cs-del-wrap")).toBeNull();
    // …and nothing when the caller supplies no delete handlers at all. (The
    // reply toggle is always there; it is the delete control that must not be.)
    renderRail(ui, groupComments([comment({})]), NOOP);
    expect(ui.railCards.querySelector(".cs-del-wrap")).toBeNull();
    expect(ui.railCards.querySelector(".cs-del")).toBeNull();
  });

  it("offers deletion on the viewer's general and archived cards too", () => {
    const { ui } = mount();
    const handlers = asViewer("j-metrics");
    renderRail(ui, groupComments([comment({ id: "g", kind: "general", sids: [] })]), handlers);
    expect(ui.railGeneral.querySelector(".cs-del")).not.toBeNull();
    renderArchived(ui, [comment({ id: "a", kind: "archived", sids: [] })], handlers);
    expect(ui.archivedList.querySelector(".cs-del")).not.toBeNull();
    renderArchived(ui, [comment({ id: "a", kind: "archived", login: "other", sids: [] })], handlers);
    expect(ui.archivedList.querySelector(".cs-del")).toBeNull();
  });

  it("confirms inline and only then calls the delete handler", () => {
    const { ui } = mount();
    const deleted: string[] = [];
    renderRail(
      ui,
      groupComments([comment({ id: "mine" })]),
      asViewer("j-metrics", () => deleted.push("mine")),
    );
    const wrap = ui.railCards.querySelector(".cs-del-wrap") as HTMLElement;
    (wrap.querySelector(".cs-del") as HTMLButtonElement).click();
    expect(deleted).toEqual([]);
    expect(wrap.querySelector(".cs-del-ask")?.textContent).toBe("Delete?");
    // "No" puts the plain control back, still without deleting anything.
    (wrap.querySelector(".cs-del-no") as HTMLButtonElement).click();
    expect(deleted).toEqual([]);
    expect(wrap.querySelector(".cs-del")).not.toBeNull();
    // "Yes" is what actually asks the controller to delete.
    (wrap.querySelector(".cs-del") as HTMLButtonElement).click();
    (wrap.querySelector(".cs-del-yes") as HTMLButtonElement).click();
    expect(deleted).toEqual(["mine"]);
    expect((wrap.querySelector(".cs-del-yes") as HTMLButtonElement).disabled).toBe(true);
  });

  it("does not fire the card's jump when the delete control is used", () => {
    const { ui } = mount();
    let jumps = 0;
    renderRail(ui, groupComments([comment({ id: "mine" })]), {
      onHover: () => {},
      onActivate: () => {
        jumps++;
      },
      canDelete: () => true,
      onDelete: () => {},
    });
    (ui.railCards.querySelector(".cs-del") as HTMLButtonElement).click();
    expect(jumps).toBe(0);
    (ui.railCards.querySelector(".cs-card") as HTMLElement).click();
    expect(jumps).toBe(1);
  });
});

describe("reply threads", () => {
  const reply = (over: Partial<PlacedReply> = {}): PlacedReply => ({
    id: "r1",
    login: "s-reader",
    avatarUrl: null,
    createdAt: "2026-08-22T09:00:00Z",
    text: "Agreed — the constant checks out.",
    ...over,
  });

  /** Handlers with a working expansion store, as the controller supplies. */
  const withThread = (extra: Partial<CardHandlers> = {}): CardHandlers => {
    const open = new Set<string>();
    return {
      ...NOOP,
      isExpanded: (c) => open.has(c.id),
      setExpanded: (c, on) => {
        if (on) open.add(c.id);
        else open.delete(c.id);
      },
      isSignedIn: () => true,
      ...extra,
    };
  };

  it("collapses to a count and shows nothing of the thread", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([comment({ replies: [reply(), reply({ id: "r2" })] })]),
      withThread(),
    );
    const toggle = ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement;
    expect(toggle.tagName).toBe("BUTTON");
    expect(toggle.textContent).toBe("2 replies");
    expect(toggle.getAttribute("aria-expanded")).toBe("false");
    expect(ui.railCards.querySelectorAll(".cs-reply").length).toBe(0);
  });

  it("offers a ghost Reply when the comment has no replies yet", () => {
    const { ui } = mount();
    renderRail(ui, groupComments([comment({})]), withThread());
    const toggle = ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement;
    expect(toggle.textContent).toBe("Reply");
    expect(toggle.classList.contains("cs-ghost")).toBe(true);
  });

  it("expands to the replies plus a reply box, and collapses again", () => {
    const { ui } = mount();
    let layouts = 0;
    renderRail(
      ui,
      groupComments([comment({ replies: [reply()] })]),
      withThread({ onLayout: () => layouts++ }),
    );
    const toggle = ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement;
    toggle.click();
    expect(toggle.getAttribute("aria-expanded")).toBe("true");
    expect(layouts).toBe(1); // card grew — the rail must be laid out again
    const item = ui.railCards.querySelector(".cs-reply") as HTMLElement;
    expect(item.querySelector(".cs-name")?.textContent).toBe("s-reader");
    expect(item.querySelector(".cs-reply-body")?.textContent).toBe(
      "Agreed — the constant checks out.",
    );
    expect(ui.railCards.querySelector(".cs-reply-text")).not.toBeNull();
    toggle.click();
    expect(toggle.getAttribute("aria-expanded")).toBe("false");
    expect(ui.railCards.querySelectorAll(".cs-reply").length).toBe(0);
    expect(layouts).toBe(2);
  });

  it("renders a hostile reply body and login as inert text", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([
        comment({
          replies: [
            reply({
              login: '<img src=x onerror="alert(1)">',
              text: '<script>alert("xss")</script><iframe src=evil>',
            }),
          ],
        }),
      ]),
      withThread(),
    );
    (ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement).click();
    const item = ui.railCards.querySelector(".cs-reply") as HTMLElement;
    expect(item.querySelectorAll("script, img, iframe").length).toBe(0);
    expect(item.querySelector(".cs-reply-body")?.textContent).toBe(
      '<script>alert("xss")</script><iframe src=evil>',
    );
    expect(item.querySelector(".cs-name")?.textContent).toBe('<img src=x onerror="alert(1)">');
  });

  it("offers delete only on the viewer's own replies", () => {
    const { ui } = mount();
    renderRail(
      ui,
      groupComments([
        comment({ replies: [reply({ id: "mine", login: "me" }), reply({ id: "theirs" })] }),
      ]),
      withThread({ canDeleteReply: (r) => r.login === "me" }),
    );
    (ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement).click();
    const items = Array.from(ui.railCards.querySelectorAll<HTMLElement>(".cs-reply"));
    const own = items.find((i) => i.getAttribute("data-rid") === "mine") as HTMLElement;
    const other = items.find((i) => i.getAttribute("data-rid") === "theirs") as HTMLElement;
    expect((own.querySelector(".cs-del") as HTMLButtonElement).tagName).toBe("BUTTON");
    expect(own.querySelector(".cs-del")?.getAttribute("aria-label")).toBe("Delete your reply");
    expect(other.querySelector(".cs-del-wrap")).toBeNull();
  });

  it("shows the sign-in button instead of a box when signed out", () => {
    const { ui } = mount();
    let signIns = 0;
    renderRail(
      ui,
      groupComments([comment({})]),
      withThread({ isSignedIn: () => false, onSignIn: () => signIns++ }),
    );
    (ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement).click();
    expect(ui.railCards.querySelector(".cs-reply-text")).toBeNull();
    const signIn = ui.railCards.querySelector(".cs-signin") as HTMLButtonElement;
    expect(signIn.textContent).toBe("Sign in with GitHub");
    signIn.click();
    expect(signIns).toBe(1);
  });

  it("posts through the handler and surfaces its failure in the box", async () => {
    const { ui } = mount();
    const sent: string[] = [];
    renderRail(
      ui,
      groupComments([comment({})]),
      withThread({
        onReply: (_c, text) => {
          sent.push(text);
          return Promise.reject(new Error("Could not post the reply (rate limited)."));
        },
      }),
    );
    (ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement).click();
    const field = ui.railCards.querySelector(".cs-reply-text") as HTMLTextAreaElement;
    field.value = "  a reply  ";
    (ui.railCards.querySelector(".cs-reply-actions .cs-post") as HTMLButtonElement).click();
    expect(sent).toEqual(["a reply"]);
    await Promise.resolve();
    await Promise.resolve();
    expect(ui.railCards.querySelector(".cs-reply-box .cs-status")?.textContent).toBe(
      "Could not post the reply (rate limited).",
    );
  });

  it("never triggers the card's jump while the reply UI is in use", () => {
    const { ui } = mount();
    let jumps = 0;
    renderRail(
      ui,
      groupComments([comment({ replies: [reply()] })]),
      withThread({ onActivate: () => jumps++ }),
    );
    const card = ui.railCards.querySelector(".cs-card") as HTMLElement;
    (ui.railCards.querySelector(".cs-reply-toggle") as HTMLButtonElement).click();
    expect(jumps).toBe(0);
    (ui.railCards.querySelector(".cs-reply-text") as HTMLTextAreaElement).click();
    expect(jumps).toBe(0);
    (ui.railCards.querySelector(".cs-reply-actions .cs-cancel") as HTMLButtonElement).click();
    expect(jumps).toBe(0);
    // The card itself still jumps.
    card.click();
    expect(jumps).toBe(1);
  });

  it("threads replies under archived cards too", () => {
    const { ui } = mount();
    renderArchived(
      ui,
      [comment({ kind: "archived", sids: [], replies: [reply()] })],
      withThread(),
    );
    const toggle = ui.archivedList.querySelector(".cs-reply-toggle") as HTMLButtonElement;
    expect(toggle.textContent).toBe("1 reply");
    toggle.click();
    expect(ui.archivedList.querySelectorAll(".cs-reply").length).toBe(1);
  });
});

describe("renderArchived", () => {
  it("quotes the version the comment was written against, with a per-tag note", () => {
    const { ui } = mount();
    renderArchived(ui, [comment({ kind: "archived", tag: "problem", sids: [] })]);
    expect(ui.archived.hidden).toBe(false);
    expect(ui.archivedSummary.textContent).toBe("Comments on earlier versions (1)");
    const card = ui.archivedList.querySelector(".cs-acard") as HTMLElement;
    expect(card.querySelector(".cs-vlbl")?.textContent).toBe("on the version of 2026-08-21");
    expect(card.querySelector(".cs-oq")?.textContent).toContain("which read:");
    expect(card.querySelector(".cs-anote")?.textContent).toContain("possibly addressed");
  });

  it("stays hidden when nothing is archived", () => {
    const { ui } = mount();
    renderArchived(ui, [comment({ kind: "archived" })]);
    renderArchived(ui, []);
    expect(ui.archived.hidden).toBe(true);
    expect(ui.archivedList.childElementCount).toBe(0);
  });
});

describe("renderHighlights", () => {
  it("paints the plan and clears only what a previous pass painted", () => {
    const { ui, body } = mount();
    const sidmap = collectSidElements(body);
    let lit = renderHighlights(
      sidmap,
      new Map([["b0-s0", { tag: "problem" as const, drift: true }]]),
      new Set(),
    );
    const first = body.querySelector('[data-sid="b0-s0"]') as HTMLElement;
    expect(first.classList.contains("cs-hl-problem")).toBe(true);
    expect(first.classList.contains("cs-hl-drift")).toBe(true);
    expect(lit).toEqual(new Set(["b0-s0"]));
    lit = renderHighlights(
      sidmap,
      new Map([["b0-s1", { tag: "verified" as const, drift: false }]]),
      lit,
    );
    expect(first.className).toBe("cs-s");
    expect(
      (body.querySelector('[data-sid="b0-s1"]') as HTMLElement).classList.contains("cs-hl-verified"),
    ).toBe(true);
    expect(lit).toEqual(new Set(["b0-s1"]));
    expect(ui.root).toBeTruthy();
  });
});

describe("renderThreadLink", () => {
  it("links the discussion only for a well-formed repo and number", () => {
    const { ui } = mount();
    renderThreadLink(ui, "Jiyuan-Tan/CausalSmith", 12);
    expect(ui.railThread.hidden).toBe(false);
    expect(ui.railThread.getAttribute("href")).toBe(
      "https://github.com/Jiyuan-Tan/CausalSmith/discussions/12",
    );
    renderThreadLink(ui, "evil.com/x/../y", 12);
    expect(ui.railThread.hidden).toBe(true);
    renderThreadLink(ui, "owner/repo", null);
    expect(ui.railThread.hidden).toBe(true);
  });
});
