/**
 * Shared validators + helpers for paper references emitted by codex
 * (literature-lookup at S-1, OQ-resolution mapping at Pass A.2).
 *
 * Lifted out of the old `stageS0_6.ts` (now removed) so both S-1 and Pass
 * A.2 can use the same regexes / mintPaperId / validation. Keeps the
 * "what counts as a real paper ref" decision in one place.
 */

export interface PaperRefInput {
  title?: string;
  authors?: string[];
  year?: number;
  arxiv_id?: string;
  doi?: string;
  rationale?: string;
}

export interface ValidatedPaperRef {
  title: string;
  authors?: string[];
  year?: number;
  arxiv_id?: string;
  doi?: string;
  rationale: string;
}

// arXiv id shape: `NNNN.NNNNN` (canonical 2007+) OR `category/NNNNNNN`
// (pre-2007 archive style). Trailing `vN` version suffix tolerated.
export const ARXIV_ID_RE = /^(?:\d{4}\.\d{4,5}|[a-z\-]+(?:\.[A-Z]{2})?\/\d{7})(?:v\d+)?$/;
// DOI: 10.<registrant>/<suffix>; suffix can contain a wide range of chars.
export const DOI_RE = /^10\.\d{4,9}\/\S+$/i;

/**
 * Validate one resolving paper. Drops entries that lack BOTH arxiv_id and
 * doi, or whose ids are malformed. Returns null on rejection.
 */
export function validatePaperRef(p: PaperRefInput | undefined | null): ValidatedPaperRef | null {
  if (!p || typeof p.title !== "string" || p.title.trim().length === 0) return null;
  const arxivOk = typeof p.arxiv_id === "string" && ARXIV_ID_RE.test(p.arxiv_id);
  const doiOk = typeof p.doi === "string" && DOI_RE.test(p.doi);
  if (!arxivOk && !doiOk) return null;
  return {
    title: p.title.trim(),
    ...(Array.isArray(p.authors) ? { authors: p.authors.map(String) } : {}),
    ...(typeof p.year === "number" ? { year: p.year } : {}),
    ...(arxivOk ? { arxiv_id: p.arxiv_id as string } : {}),
    ...(doiOk ? { doi: p.doi as string } : {}),
    rationale: typeof p.rationale === "string" ? p.rationale : "",
  };
}

/**
 * Mint a deterministic paper_id from a validated paper ref. Preference
 * order: arxiv id > doi-derived > author-year slug. The reading-list
 * dedup is on `paper_id`, so two different OQs returning the same arxiv
 * id will not double-append.
 */
export function mintPaperId(p: ValidatedPaperRef): string {
  if (p.arxiv_id) return p.arxiv_id.replace(/v\d+$/, "");
  if (p.doi) {
    // why: include DOI registrant so 10.1000/ABC and 10.2000/ABC do not collide.
    return p.doi.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, 80) || "doi";
  }
  const author = (p.authors?.[0] ?? "anon").split(/\s+/).pop()!.toLowerCase().replace(/[^a-z0-9]+/g, "");
  const yr = p.year ?? new Date().getFullYear();
  const titleSlug = p.title.toLowerCase().replace(/[^a-z0-9]+/g, "-").slice(0, 40);
  return `${author}-${yr}-${titleSlug}`.replace(/^-+|-+$/g, "");
}
