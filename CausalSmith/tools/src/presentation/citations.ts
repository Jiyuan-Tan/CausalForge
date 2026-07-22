/**
 * Citation pool discipline: the bib is collected before drafting (P0), writers
 * may only cite pool keys, and every entry is verified against an external
 * record (existence + metadata fields — the common hallucination is a real
 * title with wrong fields). Claim-support checking is a separate P3 gate.
 */

export interface BibEntry {
  key: string;
  type: string;
  fields: Record<string, string>;
}

export interface ExternalRecord {
  title: string;
  authorFamily: string;
  /** Canonical BibTeX-style author list when the registry supplies full authors. */
  author?: string;
  year: number;
  /** True when fetched by a DOI/arXiv id (the source is the entry's OWN identifier, so the
   *  record is the right work by construction). A title-query record is never authoritative. */
  authoritative?: boolean;
}

/** Rewrite only identity-confirmed bibliographic fields. The citation key, type, DOI/eprint,
 * and all unrelated fields are preserved. Title-query records are intentionally ineligible. */
export function canonicalizeBibEntry(bib: string, key: string, rec: ExternalRecord): string | null {
  if (!rec.authoritative) return null;
  const startRe = new RegExp(`@([A-Za-z]+)\\s*\\{\\s*${key.replace(/[.*+?^${}()|[\\]\\]/g, "\\$&")}\\s*,`, "i");
  const match = startRe.exec(bib);
  if (!match) return null;
  const start = match.index;
  const brace = bib.indexOf("{", start);
  let depth = 0;
  let end = -1;
  for (let i = brace; i < bib.length; i++) {
    if (bib[i] === "{") depth++;
    else if (bib[i] === "}" && --depth === 0) { end = i + 1; break; }
  }
  if (end < 0) return null;
  let block = bib.slice(start, end);
  const values: Record<string, string | undefined> = {
    title: rec.title || undefined,
    author: rec.author,
    year: rec.year > 0 ? String(rec.year) : undefined,
  };
  for (const [field, value] of Object.entries(values)) {
    if (!value) continue;
    const safe = value
      .replace(/[{}]/g, "")
      // Crossref occasionally returns HTML entities in titles. A literal `&`
      // is an alignment token in TeX, so canonical metadata must remain valid
      // BibTeX after normalization.
      .replace(/&amp;/gi, "&")
      .replace(/(?<!\\)&/g, "\\&");
    const fieldRe = new RegExp(`(\\b${field}\\s*=\\s*)(?:\\{(?:[^{}]|\\{[^{}]*\\})*\\}|\"[^\"]*\"|[^,}]+)`, "i");
    if (fieldRe.test(block)) block = block.replace(fieldRe, `$1{${safe}}`);
    else block = block.replace(/}\s*$/, `,\n  ${field} = {${safe}}\n}`);
  }
  return bib.slice(0, start) + block + bib.slice(end);
}

/**
 * Sentinel: the external registry could not be reached (transient 429/5xx/network
 * failure), as opposed to `null` which means "reached, but no matching record".
 * The distinction matters because an entry that carries a well-formed DOI/arXiv id
 * whose registry is merely unreachable must NOT be laundered into a confident
 * "hallucinated citation" rejection — that would hard-fail an emit on a network blip.
 */
export const UNREACHABLE = Symbol("registry-unreachable");

export type Lookup = (e: BibEntry) => Promise<ExternalRecord | typeof UNREACHABLE | null>;

export interface Verification {
  key: string;
  verdict: "exact" | "minor" | "major";
  detail: string;
}

export function parseBib(bib: string): BibEntry[] {
  const out: BibEntry[] = [];
  for (const entry of scanBibEntries(bib)) {
    const fields: Record<string, string> = {};
    for (const [name, value] of scanBibFields(entry.body)) fields[name.toLowerCase()] = value.trim();
    out.push({ key: entry.key.trim(), type: entry.type.toLowerCase(), fields });
  }
  return out;
}

function scanBibEntries(bib: string): Array<{ type: string; key: string; body: string }> {
  const entries: Array<{ type: string; key: string; body: string }> = [];
  let i = 0;
  while (i < bib.length) {
    const at = bib.indexOf("@", i);
    if (at < 0) break;
    let j = at + 1;
    const type = /^[A-Za-z]+/.exec(bib.slice(j))?.[0];
    if (!type) {
      i = j;
      continue;
    }
    j += type.length;
    while (/\s/.test(bib[j] ?? "")) j++;
    if (bib[j] !== "{") {
      i = j;
      continue;
    }
    // why: balance the ENTIRE `@type{...}` block FIRST (string-aware), so a special entry with no key
    // comma (`@string{JASA = "..."}`) can't scan its "key" past its own `}` into the next real entry.
    const braceStart = j;
    j++;
    let depth = 1;
    let quote = false;
    for (; j < bib.length; j++) {
      const ch = bib[j];
      if (ch === "\\") {
        j++;
      } else if (ch === '"') {
        quote = !quote;
      } else if (!quote && ch === "{") {
        depth++;
      } else if (!quote && ch === "}") {
        depth--;
        if (depth === 0) break;
      }
    }
    if (depth !== 0) break; // unterminated block — nothing safe to parse past here
    const inner = bib.slice(braceStart + 1, j); // between the outer braces
    const t = type.toLowerCase();
    // Skip BibTeX meta forms — they are not keyed reference entries.
    if (t !== "string" && t !== "comment" && t !== "preamble") {
      const comma = inner.indexOf(","); // bib keys contain no comma, so the first comma splits key|body
      if (comma >= 0) entries.push({ type, key: inner.slice(0, comma), body: inner.slice(comma + 1) });
      // else: a keyed entry with no fields — nothing to record
    }
    i = j + 1;
  }
  return entries;
}

function scanBibFields(body: string): Array<[string, string]> {
  const fields: Array<[string, string]> = [];
  let i = 0;
  while (i < body.length) {
    while (i < body.length && /[\s,]/.test(body[i])) i++;
    const name = /^[A-Za-z][A-Za-z0-9_-]*/.exec(body.slice(i))?.[0];
    if (!name) {
      i++;
      continue;
    }
    i += name.length;
    while (/\s/.test(body[i] ?? "")) i++;
    if (body[i] !== "=") continue;
    i++;
    while (/\s/.test(body[i] ?? "")) i++;
    let value = "";
    if (body[i] === "{") {
      const start = ++i;
      let depth = 1;
      for (; i < body.length; i++) {
        if (body[i] === "\\") {
          i++;
        } else if (body[i] === "{") {
          depth++;
        } else if (body[i] === "}") {
          depth--;
          if (depth === 0) break;
        }
      }
      value = body.slice(start, i);
      i++;
    } else if (body[i] === '"') {
      const start = ++i;
      for (; i < body.length; i++) {
        if (body[i] === "\\") i++;
        else if (body[i] === '"') break;
      }
      value = body.slice(start, i);
      i++;
    } else {
      const start = i;
      while (i < body.length && body[i] !== ",") i++;
      value = body.slice(start, i);
    }
    fields.push([name, value]); // why: valid BibTeX allows one-line entries and quoted values, not only newline-closed braced fields.
  }
  return fields;
}

export function citedKeys(tex: string): Set<string> {
  const keys = new Set<string>();
  const re = /\\cite[tp]?\*?(?:\[[^\]]*\])*\{([^}]+)\}/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(tex))) for (const k of m[1].split(",")) keys.add(k.trim());
  return keys;
}

const norm = (s: string) =>
  s
    .toLowerCase()
    .replace(/[^a-z0-9 ]/g, "")
    .replace(/\s+/g, " ")
    .trim();

export async function verifyEntry(e: BibEntry, lookup: Lookup): Promise<Verification> {
  const rec = await lookup(e);
  // Registry unreachable (transient) with an identifier present: non-blocking. The DOI/arXiv id is
  // itself weak evidence the work exists; we simply could not confirm metadata this run. Kept as a
  // caveat (P0 keeps it, P4 does not abort) rather than a false hallucination rejection.
  if (rec === UNREACHABLE) {
    return {
      key: e.key,
      verdict: "minor",
      detail: "external registry unreachable (transient); DOI/arXiv id present but metadata unverified this run",
    };
  }
  if (!rec) return { key: e.key, verdict: "major", detail: "no external record found" };
  const titleOk = norm(rec.title) === norm(e.fields.title ?? "");
  const year = parseInt(e.fields.year ?? "0", 10);
  const yearOk = Math.abs(rec.year - year) <= 1;
  const famOk = rec.authorFamily !== "" && norm(e.fields.author ?? "").includes(norm(rec.authorFamily));
  if (titleOk && yearOk && famOk) return { key: e.key, verdict: "exact", detail: "" };
  if (titleOk) {
    return {
      key: e.key,
      verdict: "minor",
      detail: `field mismatch (year ${year} vs ${rec.year}; author ok=${famOk}) — fix fields from record`,
    };
  }
  // An id-authoritative record (fetched by the entry's own DOI/arXiv id) IS the right work, so a
  // title mismatch is a registry/subtitle discrepancy to fix, NOT a wrong-source rejection — as
  // long as the author corroborates (guards the rare made-up DOI that resolves to some other real
  // paper). Books (Crossref stores only the short title) and arXiv subtitle variants land here.
  if (rec.authoritative && famOk) {
    return {
      key: e.key,
      verdict: "minor",
      detail: `id-confirmed source; entry title differs from registry ("${rec.title}") — fix title/fields from record`,
    };
  }
  return { key: e.key, verdict: "major", detail: "title does not match external record" };
}

const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
let lastFetch = 0;

/**
 * Fetch outcome, distinguishing a definitive "absent" (a non-retryable 4xx — the
 * work is not in this registry) from a transient "unreachable" (429/5xx/network,
 * retries exhausted — we could not reach the registry). Callers must not treat the
 * latter as evidence the citation is wrong.
 */
type Fetched =
  | { ok: true; response: Response }
  | { ok: false; unreachable: boolean };

async function politeFetch(url: string): Promise<Fetched> {
  for (let attempt = 0; attempt < 3; attempt++) {
    const wait = lastFetch + 1000 - Date.now();
    if (wait > 0) await sleep(wait);
    lastFetch = Date.now();
    try {
      const r = await fetch(url, {
        headers: {
          "User-Agent":
            process.env.CAUSALSMITH_CONTACT ??
            "causalean/0.1 (+https://github.com/Jiyuan-Tan/AutoID)",
        },
      });
      if (r.ok) return { ok: true, response: r };
      if (r.status < 500 && r.status !== 429) return { ok: false, unreachable: false }; // definitive 4xx
    } catch {
      // network error — retry
    }
    await sleep(1000 * 2 ** attempt);
  }
  return { ok: false, unreachable: true }; // retries exhausted → transient
}

interface CrossrefItem {
  title?: string[];
  author?: { family?: string; given?: string }[];
  issued?: { "date-parts"?: number[][] };
}

function fromCrossref(it: CrossrefItem | undefined | null): ExternalRecord | null {
  if (!it) return null;
  return {
    title: it.title?.[0] ?? "",
    authorFamily: it.author?.[0]?.family ?? "",
    author: it.author?.map((a) => [a.family, a.given].filter(Boolean).join(", ")).filter(Boolean).join(" and ") || undefined,
    year: it.issued?.["date-parts"]?.[0]?.[0] ?? 0,
  };
}

function fromArxivFeed(xml: string): ExternalRecord | null {
  // first <title> is the feed title; the entry title is the second
  const titles = [...xml.matchAll(/<title>([\s\S]*?)<\/title>/g)].map((m) => m[1].trim());
  const title = titles[1] ?? "";
  const names = [...xml.matchAll(/<name>([^<]+)<\/name>/g)].map((m) => m[1].trim());
  const fam = names[0]?.split(" ").pop() ?? "";
  const year = parseInt(xml.match(/<published>(\d{4})/)?.[1] ?? "0", 10);
  return title ? { title, authorFamily: fam, author: names.join(" and "), year } : null;
}

/** Record fetch result: the parsed record (null if none) plus whether the miss was transient. */
type RecFetch = { rec: ExternalRecord | null; unreachable: boolean };

async function arxivById(eprint: string): Promise<RecFetch> {
  // models emit "arXiv:2305.04116" / "2305.04116v2"; the API wants the bare id
  const id = eprint.replace(/^\s*arxiv:\s*/i, "").trim();
  const r = await politeFetch(`https://export.arxiv.org/api/query?id_list=${encodeURIComponent(id)}`);
  if (!r.ok) return { rec: null, unreachable: r.unreachable };
  return { rec: fromArxivFeed(await r.response.text()), unreachable: false };
}

async function arxivByTitle(title: string): Promise<RecFetch> {
  // arXiv-only preprints are invisible to Crossref; ti:"…" search covers them
  const q = encodeURIComponent(`ti:"${title.replace(/"/g, "")}"`);
  const r = await politeFetch(
    `https://export.arxiv.org/api/query?search_query=${q}&max_results=1`,
  );
  if (!r.ok) return { rec: null, unreachable: r.unreachable };
  return { rec: fromArxivFeed(await r.response.text()), unreachable: false };
}

/**
 * Production lookup: DOI → Crossref; arXiv id → arXiv API; else title query
 * (Crossref, falling back to arXiv title search for arXiv-only preprints).
 * Each candidate record is accepted only if its title matches the entry —
 * a wrong-paper hit from one source must not mask a right-paper hit from the
 * next, and verifyEntry re-checks the returned record anyway.
 */
export async function defaultLookup(e: BibEntry): Promise<ExternalRecord | typeof UNREACHABLE | null> {
  const titleMatches = (rec: ExternalRecord | null) =>
    rec !== null && norm(rec.title) === norm(e.fields.title ?? "");
  const getJson = async (url: string): Promise<{ json: unknown; unreachable: boolean }> => {
    const r = await politeFetch(url);
    if (!r.ok) return { json: null, unreachable: r.unreachable };
    return { json: await r.response.json(), unreachable: false };
  };
  const hasAuthId = Boolean(e.fields.doi || e.fields.eprint);
  let authUnreachable = false; // an authoritative id was present but its registry was unreachable
  try {
    if (e.fields.doi) {
      const { json, unreachable } = await getJson(
        `https://api.crossref.org/works/${encodeURIComponent(e.fields.doi)}`,
      );
      authUnreachable ||= unreachable;
      const rec = fromCrossref((json as { message?: CrossrefItem } | null)?.message);
      if (rec) return { ...rec, authoritative: true }; // DOI is authoritative; mismatch = field error, not wrong source
    }
    if (e.fields.eprint) {
      const { rec, unreachable } = await arxivById(e.fields.eprint);
      authUnreachable ||= unreachable;
      if (rec) return { ...rec, authoritative: true }; // eprint id is authoritative too
    }
    // The entry carries a well-formed DOI/arXiv id but we could not REACH its registry (transient).
    // Do NOT fall back to a title query: its top hit is often a DIFFERENT paper, whose title mismatch
    // would be laundered into a confident "major" rejection that hard-fails the emit. Signal transient
    // instead → non-blocking. (A definitively-absent id — reachable 4xx / empty arXiv feed — leaves
    // authUnreachable false and still falls through to the title fallback, so fabricated ids are caught.)
    if (hasAuthId && authUnreachable) return UNREACHABLE;
    // No identifier (or identifier definitively did not resolve): search by title.
    const candidates: (ExternalRecord | null)[] = [];
    const { json } = await getJson(
      `https://api.crossref.org/works?rows=1&query.title=${encodeURIComponent(e.fields.title ?? "")}`,
    );
    candidates.push(fromCrossref((json as { message?: { items?: CrossrefItem[] } } | null)?.message?.items?.[0]));
    if (!titleMatches(candidates[0]) && e.fields.title) {
      candidates.push((await arxivByTitle(e.fields.title)).rec);
    }
    return candidates.find(titleMatches) ?? candidates[0] ?? null;
  } catch {
    return null;
  }
}
