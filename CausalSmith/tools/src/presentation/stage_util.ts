/** Small pure helpers shared by the P-stages. */
import { OVERRIDE_ENVS, type OverrideEnv } from "./graph_view.js";

export function extractFenced(text: string, lang: string): string | null {
  const re = new RegExp("```" + lang + "[^\\n]*\\n([\\s\\S]*?)```");
  return text.match(re)?.[1]?.trim() ?? null;
}

/**
 * Models sometimes wrap a requested raw artifact despite the output-format
 * instruction: in a code fence, or in a JSON receipt with the content in a
 * field. Unwrap those envelopes; otherwise return the reply as-is.
 */
export function unwrapArtifact(reply: string, fenceLangs: string[], jsonField: string): string {
  for (const lang of fenceLangs) {
    const fenced = extractFenced(reply, lang);
    if (fenced) return fenced;
  }
  const start = reply.indexOf("{");
  if (start >= 0) {
    try {
      const obj = JSON.parse(reply.slice(start, reply.lastIndexOf("}") + 1)) as Record<
        string,
        unknown
      >;
      if (typeof obj[jsonField] === "string") return obj[jsonField] as string;
    } catch {
      // not a JSON envelope — fall through
    }
  }
  return reply.trim();
}

export interface OutlineSection {
  name: string;
  brief: string;
  objs: string[];
  bib: string[];
}

export interface Outline {
  title: string;
  notation: string;
  sections: OutlineSection[];
  /** Presentation-kind overrides (`env_overrides: P-3=definitionv, …`) — lets the
   *  planner re-kind an object's environment: a constructive "assumption" → `definitionv`,
   *  a proved result tiered as a `propositionv`, or non-result framing → `remarkv`. Only
   *  targets in `OVERRIDE_ENVS` are honored; an unknown target is dropped with a warning. */
  envOverrides: Record<string, OverrideEnv>;
}

/**
 * Parses the P1 outline.md contract:
 *   # Title / # Notation / # Sections with `## section: <name>` blocks each
 *   carrying free brief lines plus `objs:` and `bib:` lines.
 */
export function parseOutline(md: string): Outline {
  // The title line on the row after `# Title` shows up in two LLM-produced
  // shapes; handle both so the real title never collapses to "Untitled":
  //   (a) `**<the full title>.** <optional gloss>`  — the title IS in the bold.
  //   (b) `**Title.** *<the full title>.*`          — the bold is just a LABEL,
  //        and the real title follows it (often italicised).
  // Bug fixed 2026-06-15: the old code always took the bold span, so shape (b)
  // yielded "Title.", which the label-strip then emptied → "Untitled".
  const rawTitle = md.match(/^# Title\s*\n+(.+)$/m)?.[1]?.trim() ?? "Untitled";
  const boldM = rawTitle.match(/^\s*\*\*(.+?)\*\*\s*(.*)$/);
  // shape (b): bold is exactly a "Title"/"Title."/"Title:" label → take what follows.
  const candidate =
    boldM && /^title[.:]?\s*$/i.test(boldM[1]) ? boldM[2] : (boldM?.[1] ?? rawTitle);
  const title =
    candidate
      .replace(/\*+/g, "")
      .replace(/^Title[.:]?\s*/i, "")
      .replace(/\s+/g, " ")
      .replace(/\s*\.\s*$/, "")
      .trim() || "Untitled";
  const notation = md.match(/^# Notation\s*\n([\s\S]*?)(?=^# )/m)?.[1]?.trim() ?? "";
  const envOverrides: Record<string, OverrideEnv> = {};
  const ovLine = md.match(/^env_overrides:\s*(.*)$/m)?.[1] ?? "";
  const valid = new Set<string>(OVERRIDE_ENVS);
  for (const pair of splitList(ovLine)) {
    const m = pair.match(/^([A-Za-z0-9:_-]+)\s*=\s*([A-Za-z]+)$/);
    if (!m) continue;
    // Validate the target against the supported set; never silently drop a target the planner
    // intended (a silent drop hid a real structural fix) — log it so the intent is visible.
    if (valid.has(m[2])) envOverrides[m[1]] = m[2] as OverrideEnv;
    else console.error(`[outline] env_override ${m[1]}=${m[2]} ignored — unsupported env (valid: ${[...valid].join(", ")})`);
  }
  const sections: OutlineSection[] = [];
  let cur: OutlineSection | null = null;
  for (const line of md.split("\n")) {
    const h = line.match(/^## section:\s*(.+)$/);
    if (h) {
      if (cur) sections.push(cur);
      cur = { name: h[1].trim(), brief: "", objs: [], bib: [] };
      continue;
    }
    if (!cur) continue;
    if (/^# /.test(line)) {
      sections.push(cur);
      cur = null;
      continue;
    }
    const objs = line.match(/^objs:\s*(.*)$/);
    const bib = line.match(/^bib:\s*(.*)$/);
    if (objs) cur.objs = splitList(objs[1]);
    else if (bib) cur.bib = splitList(bib[1]);
    else if (line.trim() !== "") cur.brief += (cur.brief ? "\n" : "") + line.trim();
  }
  if (cur) sections.push(cur);
  return { title, notation, sections, envOverrides };
}

// "no items" placeholders the outline model emits for an empty section (intro has
// no envs/citations): `none`, `(none)`, `n/a`, an em dash. These are NOT obj ids /
// bib keys — drop them so validateOutline doesn't reject a literal "(none)".
const EMPTY_LIST_TOKEN = /^(\(?none\)?|n\/?a|[—-])$/i;
const splitList = (s: string) =>
  s
    .split(",")
    .map((x) => x.trim())
    .filter((x) => x !== "" && !EMPTY_LIST_TOKEN.test(x));

/** Re-check P1 notation/xref advisories against the FINAL paper: an advisory naming
 *  `obj:` ids is resolved iff every named id is referenced (`\ref`/`\cref`/`\autoref`
 *  all end in `ref{<id>}`; a bare `\label{<id>}` does not count). Advisories naming
 *  no id are unverifiable here (`resolved: null`). */
export function reconcileXrefAdvisories(
  advisories: { gate: string; detail: string }[],
  paperTex: string,
): { advisory: { gate: string; detail: string }; resolved: boolean | null }[] {
  return advisories.map((advisory) => {
    const ids = [...advisory.detail.matchAll(/obj:[A-Za-z0-9:_'-]+/g)].map((m) => m[0]);
    if (ids.length === 0) return { advisory, resolved: null };
    return { advisory, resolved: ids.every((id) => paperTex.includes(`ref{${id}}`)) };
  });
}

/** Splits raw BibTeX text into per-entry chunks keyed by citation key. */
export function bibChunks(bib: string): Map<string, string> {
  const out = new Map<string, string>();
  for (const chunk of bib.split(/\n(?=@)/)) {
    const key = chunk.match(/@\w+\s*\{\s*([^,\s]+)\s*,/)?.[1];
    if (key) out.set(key.trim(), chunk.trim());
  }
  return out;
}
