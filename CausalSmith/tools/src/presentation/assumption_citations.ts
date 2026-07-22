// P2 helper: turn each ASSUMPTION node's citation provenance (`node.standard` =
// {name, cite, citation}, carried from the typed core by `from_core.ts`) into prose
// guidance for the section drafter plus a RESOLVABLE bib key.
//
// Two bibliography namespaces exist: the discovery `core.bibliography` keys that
// `node.standard.cite` points at (e.g. `Tsybakov2004OptimalAggregation`) and the
// paper's own P0-curated `references.bib` keys (e.g. `Audibert2007`). They rarely
// coincide. We RECONCILE each discovery cite to the paper's key by matching first-author
// surname + exact year against `references.bib` (match-or-inject): a confident match
// reuses the paper key (no duplicate reference); no match injects a fresh entry under the
// discovery key (so `\citep` resolves rather than printing `[?]`). Matching requires BOTH
// surname ⊂ author AND equal year, so a wrong-paper citation is very unlikely; the
// fallback only ever ADDS the correct reference, it never mis-cites.
import type { FormalizationGraph, GraphNode } from "../graph/types.js";
import { isCitedNode } from "./graph_view.js";

export interface BibEntry {
  key: string;
  author: string;
  year: string | null;
}

/** Parse `references.bib` into {key, author, year} records (one per `@type{...}` entry).
 *  Tolerant field scan — enough to match author surname + year, not a full BibTeX parse. */
export function indexBib(bibText: string): BibEntry[] {
  const out: BibEntry[] = [];
  // Split on each entry header `@type{key,`; keep the body up to the next `@` or EOF.
  const re = /@\w+\s*\{\s*([^,\s]+)\s*,([\s\S]*?)(?=@\w+\s*\{|$)/g;
  for (let m = re.exec(bibText); m; m = re.exec(bibText)) {
    const key = m[1];
    const body = m[2];
    const author = body.match(/author\s*=\s*[{"]([\s\S]*?)[}"]\s*,?/i)?.[1]?.replace(/\s+/g, " ").trim() ?? "";
    const year = body.match(/year\s*=\s*[{"]?\s*((?:19|20)\d{2})/i)?.[1] ?? null;
    out.push({ key, author, year });
  }
  return out;
}

/** First-author surname from a free-text citation ("Tsybakov, A. B. (2004)…" → "Tsybakov";
 *  "Athey, S., and Wager, S. (2021)…" → "Athey"). The leading capitalized word. */
export function firstAuthorSurname(citation: string): string | null {
  return citation.trim().match(/^([A-Z][A-Za-z'’\-]+)/)?.[1] ?? null;
}

/** First 4-digit year (19xx/20xx) in a citation. */
export function citationYear(citation: string): string | null {
  return citation.match(/\b((?:19|20)\d{2})\b/)?.[1] ?? null;
}

/** Escape TeX-special characters for a BibTeX field value: injected entries carry
 *  free-text citations (journal names with `&`, identifiers with `_`) that natbib
 *  passes straight to TeX. Backslash first, then the single-char specials. */
export function escapeBibText(s: string): string {
  return s
    .replace(/\\/g, "\\textbackslash{}")
    .replace(/([&%#_$])/g, "\\$1")
    .replace(/~/g, "\\textasciitilde{}")
    .replace(/\^/g, "\\textasciicircum{}");
}

/** Build a minimal natbib-citable BibTeX entry from a free-text citation, under `key`.
 *  author + year drive `\citep`'s "(Author, year)"; the full text is kept in `note`. */
export function injectionEntry(key: string, citation: string): string {
  const surname = firstAuthorSurname(citation) ?? key;
  const year = citationYear(citation) ?? "";
  // title ≈ the clause after the "(year)." up to the next period.
  const title = citation.match(/\((?:19|20)\d{2}[a-z]?\)\.?\s*([^.]+)\./)?.[1]?.trim();
  const fields = [
    `  author = {${escapeBibText(surname)}}`,
    year ? `  year = {${year}}` : null,
    title ? `  title = {${escapeBibText(title)}}` : null,
    `  note = {${escapeBibText(citation.replace(/\s+/g, " ").trim())}}`,
  ].filter(Boolean);
  return `@misc{${key},\n${fields.join(",\n")}\n}`;
}

export interface ResolvedCite {
  /** The key to `\citep` — a paper `references.bib` key when matched, else the discovery key. */
  citeKey: string;
  /** A BibTeX entry to APPEND to references.bib (only when no paper match was found). */
  inject: string | null;
}

/** Reconcile a `node.standard` to a resolvable bib key: a confident paper-key match
 *  (surname ⊂ author AND equal year) reuses it; otherwise inject under the discovery key. */
export function reconcileCite(
  std: { name: string; cite: string; citation?: string },
  bibIndex: BibEntry[],
): ResolvedCite {
  // If the discovery key is literally a paper key, use it as-is.
  if (bibIndex.some((b) => b.key === std.cite)) return { citeKey: std.cite, inject: null };
  // Gate sources normally use a kebab-case `cite:` slug while P0 emits a CamelCase
  // BibTeX key.  Match those namespaces before consulting mutable metadata such as
  // the year of the latest arXiv version.  Equality after punctuation/case removal is
  // deliberately strict: it accepts `zeng-...-2024` ↔ `Zeng...2024`, but cannot turn
  // a merely similar author or title into a citation match.
  const normalizedCite = std.cite.replace(/[^A-Za-z0-9]/g, "").toLowerCase();
  const normalizedHit = bibIndex.find(
    (b) => b.key.replace(/[^A-Za-z0-9]/g, "").toLowerCase() === normalizedCite,
  );
  if (normalizedHit) return { citeKey: normalizedHit.key, inject: null };
  const citation = std.citation;
  if (citation) {
    const surname = firstAuthorSurname(citation);
    const year = citationYear(citation);
    if (surname && year) {
      const hit = bibIndex.find((b) => b.year === year && b.author.includes(surname));
      if (hit) return { citeKey: hit.key, inject: null };
    }
    return { citeKey: std.cite, inject: injectionEntry(std.cite, citation) };
  }
  // No citation text: inject a stub so the key resolves (name in note).
  return { citeKey: std.cite, inject: `@misc{${std.cite},\n  note = {${escapeBibText(std.name)}}\n}` };
}

/**
 * Build a `reconcileCite`-shaped record for a CITED gate node from its `gate.source` `cite:` slug —
 * the only attribution causalsmith has (graph-only; the structured bib record lives in plan.json,
 * which causalsmith does not read). The slug convention is `firstauthor[-coauthor...]-year`, so the
 * first segment is the first-author surname and a trailing 4-digit segment is the year; together
 * they let `reconcileCite` match the paper's P0-curated bib entry (surname ⊂ author AND equal year)
 * — e.g. `bonvini-kennedy-2022` → "Bonvini (2022)" → the Bonvini–Kennedy reference. Returns null if
 * the node carries no resolvable source.
 */
export function citedStdFromNode(n: GraphNode): { name: string; cite: string; citation?: string } | null {
  const src = n.gate?.source;
  if (!src) return null;
  const cite = src.replace(/^cite:/, "");
  const segs = cite.split("-").filter(Boolean);
  const year = [...segs].reverse().find((s) => /^(?:19|20)\d{2}$/.test(s)) ?? null;
  const surnameSeg = segs[0] ?? cite;
  const surname = surnameSeg.charAt(0).toUpperCase() + surnameSeg.slice(1);
  const citation = year ? `${surname} (${year})` : undefined;
  return { name: "cited external result", cite, citation };
}

export interface AssumptionCiteContext {
  /** Prose guidance for the drafter, one line per assumption in the section. */
  notes: string;
  /** Reconciled cite keys to ADD to the section's allowed bib keys. */
  extraKeys: string[];
  /** BibTeX entries to append to references.bib, deduped by key (the caller still dedups
   *  ACROSS sections, since the same source can appear in more than one section). */
  injections: string[];
}

/** Build the drafter guidance + resolved keys/injections for the ASSUMPTION objects that
 *  appear in a section. Standard assumptions get a named, citable note; novel ones are
 *  flagged as specific to this work (no citation). Non-assumption objs are ignored. */
export function assumptionCiteContext(
  graph: FormalizationGraph,
  objIds: string[],
  bibText: string,
): AssumptionCiteContext {
  const bibIndex = indexBib(bibText);
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const lines: string[] = [];
  const extraKeys: string[] = [];
  const injections = new Map<string, string>(); // dedup by injected key (one ref per source)
  for (const id of objIds) {
    const n: GraphNode | undefined = byId.get(id);
    if (!n) continue;
    // CITED gate: an imported external result the paper relies on but does not prove. Attribute it
    // with \citep (reconciled from the cite: slug) and tell the drafter never to claim it as the
    // paper's own — the substantive guard against an overclaim built on a borrowed theorem.
    if (isCitedNode(n)) {
      const std = citedStdFromNode(n);
      if (std) {
        const { citeKey, inject } = reconcileCite(std, bibIndex);
        extraKeys.push(citeKey);
        if (inject) injections.set(citeKey, inject);
        lines.push(
          `- Cited result obj_id "${n.obj_id ?? n.id}" (env arg \`${n.id}\`): IMPORTED external result — ` +
            `the paper relies on it but does NOT prove it. When you reference it, attribute it with ` +
            `\\citep{${citeKey}}; never present it as a contribution of this paper.`,
        );
      }
      continue;
    }
    if (n.kind !== "assumption") continue;
    const label = `Assumption obj_id "${n.obj_id ?? n.id}" (env arg \`${n.id}\`)`;
    if (n.standard) {
      const { citeKey, inject } = reconcileCite(n.standard, bibIndex);
      extraKeys.push(citeKey);
      if (inject) injections.set(citeKey, inject);
      lines.push(
        `- ${label}: STANDARD — the ${n.standard.name} condition; cite it with \\citep{${citeKey}} in the explanatory sentence.`,
      );
    } else {
      lines.push(`- ${label}: NOVEL — specific to this analysis; explain it in words, do NOT cite a reference for it.`);
    }
  }
  return { notes: lines.join("\n"), extraKeys: [...new Set(extraKeys)], injections: [...injections.values()] };
}
