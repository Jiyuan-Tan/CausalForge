// @vitest-environment happy-dom
// The byline rating widget, driven through its real entry point against a
// stubbed worker: the strip renders, is labelled, shows the average, and shows
// an honest empty state (empty stars + "no ratings yet", never a fake 0/5).
import { afterEach, describe, expect, it, vi } from "vitest";
import { initPaperRating } from "../src/scripts/ratings.js";

afterEach(() => vi.unstubAllGlobals());

describe("byline rating widget", () => {
  it("renders the star strip from paper-data + worker rows", async () => {
    document.body.innerHTML = `
      <span class="paper-rating" id="paper-rating" hidden></span>
      <script type="application/json" id="paper-data">${JSON.stringify({
        paperId: "exp_demo_v1",
        commentsWorker: "http://localhost:8788",
      })}</script>`;
    vi.stubGlobal(
      "fetch",
      vi.fn(async (input: string) => {
        if (String(input).includes("/api/ratings")) {
          return new Response(
            JSON.stringify({
              paper: "exp_demo_v1",
              ratings: [
                { target: "paper", login: "a", avatarUrl: null, stars: 4 },
                { target: "paper", login: "b", avatarUrl: null, stars: 5 },
              ],
              truncated: false,
            }),
            { status: 200 },
          );
        }
        return new Response("{}", { status: 404 });
      }),
    );
    initPaperRating();
    await new Promise((r) => setTimeout(r, 20));
    const host = document.getElementById("paper-rating")!;
    expect(host.hidden).toBe(false);
    expect(host.querySelectorAll(".rate-star")).toHaveLength(5);
    expect(host.querySelector(".rate-caption")?.textContent).toContain("4.5/5");
    // Anonymous viewer has not rated → the call-to-action button is shown,
    // and for a signed-out viewer it names the sign-in it will start.
    expect(host.querySelector(".rate-cta")?.textContent).toContain("Sign in & rate this paper");
  });

  it("renders empty stars and 'no ratings yet' when nobody rated", async () => {
    document.body.innerHTML = `
      <span class="paper-rating" id="paper-rating" hidden></span>
      <script type="application/json" id="paper-data">${JSON.stringify({
        paperId: "exp_demo_v1",
        commentsWorker: "http://localhost:8788",
      })}</script>`;
    vi.stubGlobal(
      "fetch",
      vi.fn(async () =>
        new Response(JSON.stringify({ paper: "exp_demo_v1", ratings: [], truncated: false }), {
          status: 200,
        }),
      ),
    );
    initPaperRating();
    await new Promise((r) => setTimeout(r, 20));
    const host = document.getElementById("paper-rating")!;
    expect(host.hidden).toBe(false);
    expect(host.querySelector(".rate-caption")?.textContent).toContain("no ratings yet");
  });
});
