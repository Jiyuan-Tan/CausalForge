// @vitest-environment happy-dom
// Interactive drive of the byline rating widget: full click-to-rate cycles,
// CTA clicks, and a hover storm. Written after a reader reported a browser
// crash while rating — an infinite render/event loop in the click path would
// hang these tests (vitest's per-test timeout turns a hang into a failure),
// so green here rules that class of bug out.
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";
import { initPaperRating } from "../src/scripts/ratings.js";

function mountPage() {
  document.body.innerHTML = `
    <span class="paper-rating" id="paper-rating" hidden></span>
    <script type="application/json" id="paper-data">${JSON.stringify({
      paperId: "exp_demo_v1",
      commentsWorker: "http://localhost:8788",
    })}</script>`;
}

/** Stubbed worker + GitHub: reads serve `rows`, writes mutate them. */
function stubNetwork(rows: { target: string; login: string; avatarUrl: null; stars: number }[]) {
  let writes = 0;
  vi.stubGlobal(
    "fetch",
    vi.fn(async (input: string, init?: RequestInit) => {
      const url = String(input);
      if (url === "https://api.github.com/user") {
        return new Response(JSON.stringify({ login: "you-demo" }), { status: 200 });
      }
      if (url.includes("/api/ratings")) {
        if (init?.method === "POST" || init?.method === "DELETE") {
          writes++;
          const body = JSON.parse(String(init.body)) as { stars?: number };
          const i = rows.findIndex((r) => r.target === "paper" && r.login === "you-demo");
          if (i >= 0) rows.splice(i, 1);
          if (init.method === "POST") {
            rows.push({ target: "paper", login: "you-demo", avatarUrl: null, stars: body.stars! });
          }
          return new Response(JSON.stringify({ ok: true }), { status: 200 });
        }
        return new Response(
          JSON.stringify({ paper: "exp_demo_v1", ratings: rows, truncated: false }),
          { status: 200 },
        );
      }
      return new Response("{}", { status: 404 });
    }),
  );
  return { countWrites: () => writes };
}

const settle = () => new Promise((r) => setTimeout(r, 25));
const host = () => document.getElementById("paper-rating")!;
const stars = () => [...host().querySelectorAll<HTMLButtonElement>(".rate-star")];

beforeEach(() => {
  sessionStorage.setItem("cs-gh-token", "tok-you");
});
afterEach(() => {
  vi.unstubAllGlobals();
  sessionStorage.clear();
});

describe("interactive rating cycle (signed in)", () => {
  it("click rates, re-click withdraws, and the DOM settles each time", async () => {
    mountPage();
    const net = stubNetwork([{ target: "paper", login: "a", avatarUrl: null, stars: 4 }]);
    initPaperRating();
    await settle();

    stars()[3].click(); // rate 4/5
    await settle();
    expect(host().querySelector(".rate-caption")?.textContent).toContain("yours: 4");
    expect(net.countWrites()).toBe(1);

    // The strip after a rating shows the label, not the CTA.
    expect(host().querySelector(".rate-label")).not.toBeNull();
    expect(host().querySelector(".rate-cta")).toBeNull();

    stars()[3].click(); // same star again → withdraw
    await settle();
    expect(host().querySelector(".rate-caption")?.textContent).not.toContain("yours");
    expect(net.countWrites()).toBe(2);
  });

  it("a burst of clicks cannot start concurrent writes (busy gate)", async () => {
    mountPage();
    const net = stubNetwork([]);
    initPaperRating();
    await settle();

    // 25 rapid clicks across the strip while each write is in flight.
    for (let i = 0; i < 25; i++) stars()[i % 5]?.click();
    await settle();
    // The busy flag admits one write per settled cycle, not one per click.
    expect(net.countWrites()).toBeLessThanOrEqual(2);
  });

  it("survives a hover/focus storm without looping", async () => {
    mountPage();
    stubNetwork([{ target: "paper", login: "a", avatarUrl: null, stars: 3 }]);
    initPaperRating();
    await settle();

    const [a, b] = [stars()[0], stars()[4]];
    for (let i = 0; i < 2000; i++) {
      const el = i % 2 ? a : b;
      el.dispatchEvent(new Event("mouseenter"));
      el.dispatchEvent(new Event("focus"));
      el.dispatchEvent(new Event("mouseleave"));
      el.dispatchEvent(new Event("blur"));
    }
    expect(stars()).toHaveLength(5); // still exactly one strip
  });
});

describe("signed out", () => {
  it("popup-blocked sign-in fails cleanly and re-clicks do not loop", async () => {
    sessionStorage.clear();
    mountPage();
    stubNetwork([]);
    vi.stubGlobal("open", vi.fn(() => null)); // popup blocked
    initPaperRating();
    await settle();

    const cta = host().querySelector<HTMLButtonElement>(".rate-cta")!;
    expect(cta.textContent).toContain("Sign in");
    cta.click();
    await settle();
    stars()[2].click();
    await settle();
    expect(host().querySelector(".rate-status")?.textContent).toContain("did not complete");
    expect(stars()).toHaveLength(5);
  });
});
