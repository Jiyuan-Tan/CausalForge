/**
 * Paper-level reader rating — the byline widget's controller.
 *
 * Sits next to the AI reviewer score in the paper byline and answers the other
 * half of the question: what did HUMAN readers think? Five stars, one rating
 * per signed-in GitHub account per paper, withdrawable by clicking the same
 * star again. It shares the page's single sign-in: the token the comments rail
 * or the Proof map obtained is adopted here through `AUTH_EVENT`, and a
 * sign-in started here is broadcast right back to them.
 *
 * No worker configured (the CI/dev default) → the widget never appears and the
 * page is exactly what it was before ratings existed.
 */

import * as auth from "./comments/auth.js";
import {
  clearRating,
  listRatings,
  PAPER_TARGET,
  summarize,
  writeRating,
  type RatingRow,
  type RatingSummary,
} from "./ratings/api.js";
import { renderStars } from "./ratings/stars.js";

interface State {
  host: HTMLElement;
  status: HTMLElement;
  paperId: string;
  worker: string;
  rows: RatingRow[];
  token: string | null;
  viewer: string | null; // login
  busy: boolean;
}

/** Entry point; safe to call on any page. */
export function initPaperRating(): void {
  // .catch, not try/catch: boot is async, so a rejection would otherwise
  // escape the synchronous frame as an unhandled rejection.
  void boot().catch(() => {
    /* the paper must render even if the widget cannot */
  });
}

/** Same acceptance rules the Proof map applies to the worker URL. */
function ratingWorker(raw: string, paperId: string): string {
  if (!raw || !/^[A-Za-z0-9_.-]{1,128}$/.test(paperId)) return "";
  let url: URL;
  try {
    url = new URL(raw);
  } catch {
    return "";
  }
  const localhost = url.hostname === "localhost" || url.hostname === "127.0.0.1";
  if (url.protocol !== "https:" && !localhost) return "";
  return raw.replace(/\/+$/, "");
}

async function boot(): Promise<void> {
  const host = document.getElementById("paper-rating");
  const script = document.getElementById("paper-data");
  if (!host || !script) return;
  let data: Record<string, unknown>;
  try {
    data = JSON.parse(script.textContent ?? "") as Record<string, unknown>;
  } catch {
    return;
  }
  const paperId = typeof data.paperId === "string" ? data.paperId : "";
  const rawWorker = typeof data.commentsWorker === "string" ? data.commentsWorker.trim() : "";
  const worker = ratingWorker(rawWorker, paperId);
  if (!worker) return;

  const status = document.createElement("span");
  status.className = "rate-status";

  const state: State = {
    host,
    status,
    paperId,
    worker,
    rows: [],
    token: auth.readToken(),
    viewer: null,
    busy: false,
  };

  window.addEventListener(auth.AUTH_EVENT, () => {
    const token = auth.readToken();
    if (token === state.token) return;
    state.token = token;
    state.viewer = null;
    if (token) void loadViewer(state).then(() => render(state));
    else render(state);
  });

  host.hidden = false;
  try {
    state.rows = await listRatings(worker, paperId);
  } catch {
    /* a dead endpoint costs only the counts */
  }
  if (state.token) await loadViewer(state);
  render(state);
}

/** Resolve who is signed in, so their own stars can be shown and withdrawn. */
async function loadViewer(state: State): Promise<void> {
  if (!state.token) return;
  try {
    const res = await fetch("https://api.github.com/user", {
      credentials: "omit",
      headers: { Authorization: `Bearer ${state.token}` },
    });
    if (res.status === 401) {
      auth.clearToken();
      state.token = null;
      return;
    }
    if (!res.ok) return;
    const data = (await res.json()) as { login?: unknown };
    if (typeof data.login === "string") state.viewer = data.login;
  } catch {
    /* the widget still works; the reader is just anonymous to it */
  }
}

function mySummary(state: State): RatingSummary | null {
  return summarize(state.rows, state.viewer).get(PAPER_TARGET) ?? null;
}

function render(state: State): void {
  renderStars(state.host, {
    summary: mySummary(state),
    signedIn: !!state.token,
    busy: state.busy,
    noun: "paper",
    onRate: (n) => void onRate(state, n),
    // The CTA starts the sign-in immediately; once it lands, the stars are
    // already focused and one click records the score. Already signed in →
    // no re-render: rebuilding the DOM would kill the pulse and drop the
    // keyboard focus the click just placed on the stars.
    onCta: () => {
      if (!state.busy && !state.token) {
        void ensureSignedIn(state).then((ok) => ok && render(state));
      }
    },
  });
  state.host.appendChild(state.status);
}

/** Sign the viewer in if needed. True when a token is held afterwards. */
async function ensureSignedIn(state: State): Promise<boolean> {
  if (state.token) return true;
  setStatus(state, "Opening GitHub…");
  try {
    const token = await auth.signIn(state.worker);
    state.token = token; // before writeToken: its broadcast must find us in sync
    auth.writeToken(token);
    await loadViewer(state);
    setStatus(state, "Signed in.");
    return true;
  } catch {
    setStatus(state, "Sign-in did not complete.");
    return false;
  }
}

function setStatus(state: State, message: string): void {
  state.status.textContent = message;
}

/** Replace the viewer's own paper-level row locally (null stars removes it). */
function adoptOwnRow(state: State, stars: number | null): void {
  if (!state.viewer) return;
  state.rows = state.rows.filter(
    (r) => !(r.target === PAPER_TARGET && r.login === state.viewer),
  );
  if (stars !== null) {
    state.rows.push({ target: PAPER_TARGET, login: state.viewer, avatarUrl: null, stars });
  }
}

async function onRate(state: State, stars: number): Promise<void> {
  if (state.busy) return;
  // Busy BEFORE the sign-in await: repeated clicks while the popup is open
  // must not start concurrent sign-in/write flows.
  state.busy = true;
  render(state);

  if (!(await ensureSignedIn(state))) {
    state.busy = false;
    render(state);
    return;
  }
  setStatus(state, "");

  const mine = mySummary(state)?.mine ?? null;
  try {
    if (mine === stars) {
      await clearRating(state.worker, state.paperId, null, state.token!);
      adoptOwnRow(state, null);
      setStatus(state, "Rating withdrawn.");
    } else {
      await writeRating(state.worker, state.paperId, null, stars, state.token!);
      adoptOwnRow(state, stars);
      setStatus(state, "");
    }
  } catch (err) {
    const detail = err instanceof Error && err.message ? ` (${err.message.slice(0, 120)})` : "";
    setStatus(state, `Could not save that${detail}.`);
  } finally {
    state.busy = false;
    render(state);
  }
}
