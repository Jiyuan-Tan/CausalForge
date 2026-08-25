/**
 * GitHub sign-in for the paper-page commenter.
 *
 * The visitor's token never touches this repo's servers beyond the one-shot
 * code exchange in the worker: the popup posts it back with `postMessage`, and
 * it is held in `sessionStorage` for the tab's lifetime only. Three things make
 * that safe, and all three are load-bearing:
 *
 *   1. A fresh `crypto.getRandomValues` nonce goes out with the login request
 *      and must come back in the payload, so a message from an unrelated (or
 *      replayed) window is ignored.
 *   2. `event.origin` must equal the worker's origin. Any other frame — the
 *      page itself included — is ignored.
 *   3. The token is never put in a URL, a cookie, or a log line.
 */

const TOKEN_KEY = "cs-gh-token";
const AUTH_TIMEOUT_MS = 180_000;

export interface Viewer {
  login: string;
  avatarUrl: string;
}

/** sessionStorage can throw (private mode, blocked cookies) — never let it. */
export function readToken(): string | null {
  try {
    const t = sessionStorage.getItem(TOKEN_KEY);
    return t && t.length > 0 ? t : null;
  } catch {
    return null;
  }
}

export function writeToken(token: string): void {
  try {
    sessionStorage.setItem(TOKEN_KEY, token);
  } catch {
    /* session-only anyway; sign-in simply won't survive a reload */
  }
}

export function clearToken(): void {
  try {
    sessionStorage.removeItem(TOKEN_KEY);
  } catch {
    /* nothing to do */
  }
}

function makeNonce(): string {
  const bytes = new Uint8Array(16);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
}

/**
 * Open the worker's login popup and resolve with the visitor's token.
 *
 * Rejects on a closed popup, a timeout, or a failed exchange. The caller shows
 * the message; nothing here logs the token.
 */
export function signIn(workerBase: string): Promise<string> {
  const workerOrigin = new URL(workerBase).origin;
  const nonce = makeNonce();
  const url =
    `${workerBase}/login?origin=${encodeURIComponent(location.origin)}` +
    `&nonce=${encodeURIComponent(nonce)}`;
  const popup = window.open(url, "causalsmith-signin", "width=680,height=780");
  if (!popup) return Promise.reject(new Error("popup blocked"));

  return new Promise<string>((resolve, reject) => {
    let settled = false;
    const finish = (fn: () => void) => {
      if (settled) return;
      settled = true;
      window.removeEventListener("message", onMessage);
      clearInterval(closedTimer);
      clearTimeout(timeout);
      fn();
    };

    const onMessage = (event: MessageEvent) => {
      if (event.origin !== workerOrigin) return;
      const data = event.data as { type?: unknown; nonce?: unknown; token?: unknown } | null;
      if (!data || typeof data !== "object") return;
      if (data.type !== "causalsmith-auth") return;
      if (data.nonce !== nonce) return;
      const token = typeof data.token === "string" ? data.token : "";
      finish(() =>
        token ? resolve(token) : reject(new Error("sign-in did not return a token")),
      );
    };

    window.addEventListener("message", onMessage);
    const closedTimer = setInterval(() => {
      if (popup.closed) finish(() => reject(new Error("sign-in window closed")));
    }, 700);
    const timeout = setTimeout(
      () => finish(() => reject(new Error("sign-in timed out"))),
      AUTH_TIMEOUT_MS,
    );
  });
}
