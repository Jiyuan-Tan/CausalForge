/**
 * Parser for the P/L/T blocks of a banked NL-formalization note.
 *
 * Two causalsmith F1 note dialects are supported (the smiths drifted; the parser
 * is tolerant of both — see the causalsmith/causalsmith note contract):
 *   - LEGACY structured headers: `### P-1. Title.` / `### L-0a. …` / `### T-2. …`.
 *   - CURRENT causalsmith F1 (stage1_template.txt): bold inline `**P-1 (Title).**`
 *     and `**L-1 (Title).**` for definition/lemma blocks, and `### T-block: t1 — Title`
 *     (local id `tN`, mapped to obj_id `T-N`) for theorem blocks.
 * Fields: `#### Name.` subsections, `- **Name.** text` bullets, and standalone
 * `**Name.** text` field labels. Inside a subsection, `- **H1 (…)**` bullets are
 * content of that field, not new fields.
 */

export interface NoteBlock {
  obj_id: string; // "P-1", "P-1b", "L-0a", "T-2", …
  title: string;
  body: string; // raw markdown of the block (header excluded)
  fields: Record<string, string>;
}

// Legacy `### P-1. Title.` — id MUST start with a digit after the hyphen so this
// never swallows `### T-block: t1 …` (which would match `[PLT]-\w+` as id `T-block`).
const HEADER_LEGACY = /^### (?<id>[PLT]-\d[\w]*)\.?\s*(?<title>.*?)\.?\s*$/;
// Current causalsmith T-block header: `## T-block: t1 — Title` / `### T-block: t1 - Title`.
const HEADER_TBLOCK =
  /^#{2,3}\s+T-block:\s*[tT](?<num>\d+)\b\s*(?:[—–-]+\s*)?(?<title>.*?)\s*$/;
// Current causalsmith bold P/L header: `**P-1 (Title).**` / `**L-0a (Title).**`.
// id must have a digit right after the hyphen (so `**P-block …**`, `**Statement.**`
// do NOT match). The title is captured lazily (`.*?`) so a closing paren INSIDE
// the title — common in math, e.g. `**P-7 (Hölder ball `ℋ^β(L)`).**` — does not
// truncate the match and drop the block; the lazy quantifier stops at the first
// `)` that is actually followed by the closing `.**`.
const HEADER_BOLD_PL = /^\*\*(?<id>[PL]-\d[\w]*)\s*\((?<title>.*?)\)\s*\.?\s*\*\*\s*(?<rest>.*)$/;

interface HeaderMatch {
  obj_id: string;
  title: string;
  rest: string; // any block body text on the same line after the header
}

function matchHeader(line: string): HeaderMatch | null {
  // T-block first: `### T-block: t1 …` must not be read by the legacy rule.
  const t = line.match(HEADER_TBLOCK);
  if (t) return { obj_id: `T-${t.groups!.num}`, title: t.groups!.title ?? "", rest: "" };
  const lg = line.match(HEADER_LEGACY);
  if (lg) return { obj_id: lg.groups!.id, title: lg.groups!.title ?? "", rest: "" };
  const b = line.match(HEADER_BOLD_PL);
  if (b) return { obj_id: b.groups!.id, title: b.groups!.title ?? "", rest: b.groups!.rest ?? "" };
  return null;
}

export function parseNoteBlocks(md: string): NoteBlock[] {
  const blocks: NoteBlock[] = [];
  let cur: NoteBlock | null = null;
  for (const line of md.split("\n")) {
    const h = matchHeader(line);
    if (h) {
      if (cur) blocks.push(finish(cur));
      cur = { obj_id: h.obj_id, title: h.title, body: h.rest ? h.rest + "\n" : "", fields: {} };
      continue;
    }
    if (cur) {
      // A level-2 section header (`## 4. P-block …`) ends the current block.
      // (T-block headers are caught by matchHeader above and never reach here.)
      if (/^## /.test(line)) {
        blocks.push(finish(cur));
        cur = null;
        continue;
      }
      cur.body += line + "\n";
    }
  }
  if (cur) blocks.push(finish(cur));
  return blocks;
}

function finish(b: NoteBlock): NoteBlock {
  let currentField: string | null = null;
  for (const line of b.body.split("\n")) {
    const sub = line.match(/^#### (.+?)\.?\s*$/);
    if (sub) {
      currentField = sub[1];
      b.fields[currentField] ??= "";
      continue;
    }
    // Bulleted field `- **Name.** text` OR standalone field label `**Name.** text`
    // (the current causalsmith T-blocks use standalone `**Statement.** …`,
    // `**Load-bearing hypotheses.**`, `**Conclusion (typed).** …`). Exclude `H\d`
    // hypothesis bullets (content of the current field, not a new field).
    const f = line.match(/^(?:- )?\*\*(.+?)\.?\*\*\s*(.*)$/);
    if (f && !/^H\d/.test(f[1])) {
      currentField = f[1];
      b.fields[currentField] = f[2];
      continue;
    }
    if (currentField && line.trim() !== "") {
      b.fields[currentField] += (b.fields[currentField] ? "\n" : "") + line.trim();
    }
  }
  return b;
}
