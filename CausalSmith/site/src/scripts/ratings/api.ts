/**
 * Reader ratings — the client's network half.
 *
 * A rating is one signed-in reader giving 1–5 stars to a paper as a whole, or
 * to one statement in it. The wire mirrors the attestation layer it is built
 * beside: the worker serves flat public rows and the page does the arithmetic,
 * so "the average" and "your own rating" both come from one anonymously-cached
 * GET — no authenticated read path exists.
 *
 * Everything here is DOM-free and network-only, so the controllers' logic can
 * be tested against a stubbed `fetch`.
 */

/** The reserved target naming the paper-level rating. */
export const PAPER_TARGET = "paper";

/** One reader's stars on one target ("paper" or an obj id). */
export interface RatingRow {
  target: string;
  login: string;
  avatarUrl: string | null;
  stars: number;
}

/** An aggregated view of one target. */
export interface RatingSummary {
  avg: number;
  count: number;
  /** The viewer's own stars, when a viewer login was supplied and present. */
  mine: number | null;
}

/** How many rows a page will hold, however many the server sends. */
const MAX_ROWS = 5000;

const isStr = (v: unknown): v is string => typeof v === "string" && v.length > 0;
const isStars = (v: unknown): v is number =>
  typeof v === "number" && Number.isInteger(v) && v >= 1 && v <= 5;

function shape(raw: unknown): RatingRow | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  if (!isStr(r.target) || !isStr(r.login) || !isStars(r.stars)) return null;
  return {
    target: r.target,
    login: r.login,
    avatarUrl: isStr(r.avatarUrl) ? r.avatarUrl : null,
    stars: r.stars,
  };
}

export function shapeAll(raw: unknown): RatingRow[] {
  if (!Array.isArray(raw)) return [];
  const out: RatingRow[] = [];
  for (const item of raw.slice(0, MAX_ROWS)) {
    const row = shape(item);
    if (row) out.push(row);
  }
  return out;
}

/** target → {avg, count, mine}. Averages are rounded to one decimal. */
export function summarize(rows: RatingRow[], viewerLogin?: string | null): Map<string, RatingSummary> {
  const sums = new Map<string, { sum: number; count: number; mine: number | null }>();
  for (const r of rows) {
    const s = sums.get(r.target) ?? { sum: 0, count: 0, mine: null };
    s.sum += r.stars;
    s.count += 1;
    if (viewerLogin && r.login === viewerLogin) s.mine = r.stars;
    sums.set(r.target, s);
  }
  const out = new Map<string, RatingSummary>();
  for (const [target, s] of sums) {
    out.set(target, { avg: Math.round((10 * s.sum) / s.count) / 10, count: s.count, mine: s.mine });
  }
  return out;
}

async function readError(res: Response): Promise<string> {
  try {
    const data = (await res.json()) as { error?: unknown };
    if (isStr(data.error)) return data.error;
  } catch {
    /* fall through to the status */
  }
  return `HTTP ${res.status}`;
}

/** Read every rating on a paper. Anonymous — no token involved. */
export async function listRatings(worker: string, paper: string): Promise<RatingRow[]> {
  const res = await fetch(`${worker}/api/ratings?paper=${encodeURIComponent(paper)}`, {
    credentials: "omit",
  });
  if (!res.ok) throw new Error(await readError(res));
  const data = (await res.json()) as { ratings?: unknown };
  return shapeAll(data.ratings);
}

/** The worker refuses a `?papers=` list longer than this; batch to match. */
const MAX_PAPERS_PER_REQUEST = 50;

/** Paper-level averages for many papers (the landing page), batched so a
 *  catalogue past 50 papers degrades to two requests, not to no badges. */
export async function paperAverages(
  worker: string,
  papers: string[],
): Promise<Record<string, { avg: number; count: number }>> {
  const list = papers.filter((p) => /^[A-Za-z0-9][A-Za-z0-9_.-]{0,127}$/.test(p));
  const out: Record<string, { avg: number; count: number }> = {};
  for (let i = 0; i < list.length; i += MAX_PAPERS_PER_REQUEST) {
    const batch = list.slice(i, i + MAX_PAPERS_PER_REQUEST);
    const res = await fetch(
      `${worker}/api/ratings?papers=${encodeURIComponent(batch.join(","))}`,
      { credentials: "omit" },
    );
    if (!res.ok) throw new Error(await readError(res));
    const data = (await res.json()) as { papers?: unknown };
    if (!data.papers || typeof data.papers !== "object") continue;
    for (const [id, v] of Object.entries(data.papers as Record<string, unknown>)) {
      if (!v || typeof v !== "object") continue;
      const { avg, count } = v as Record<string, unknown>;
      if (typeof avg === "number" && typeof count === "number" && count > 0) {
        out[id] = { avg, count };
      }
    }
  }
  return out;
}

async function write(
  method: "POST" | "DELETE",
  worker: string,
  paper: string,
  objId: string | null,
  stars: number | null,
  token: string,
): Promise<void> {
  const body: Record<string, unknown> = { paper };
  if (objId !== null) body.objId = objId;
  if (stars !== null) body.stars = stars;
  const res = await fetch(`${worker}/api/ratings`, {
    method,
    credentials: "omit",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!res.ok) throw new Error(await readError(res));
}

/** Set the signed-in reader's stars on a paper (objId null) or a statement. */
export async function writeRating(
  worker: string,
  paper: string,
  objId: string | null,
  stars: number,
  token: string,
): Promise<void> {
  await write("POST", worker, paper, objId, stars, token);
}

/** Withdraw the signed-in reader's own rating of that target. */
export async function clearRating(
  worker: string,
  paper: string,
  objId: string | null,
  token: string,
): Promise<void> {
  await write("DELETE", worker, paper, objId, null, token);
}
