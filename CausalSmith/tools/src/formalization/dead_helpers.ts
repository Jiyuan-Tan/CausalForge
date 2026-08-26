import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { isPaperTmpPath } from "../paths.js";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";

/**
 * F4 dead-helper sweep — agent-authored declarations nothing in the run consumes.
 *
 * Every gate before F4 checks that proofs are CORRECT (build green, no sorry, axioms); nothing
 * checks that a declaration is USED. Helper lemmas are authored ahead of a planned proof route,
 * the route changes, and the abandoned helper still compiles — so it survives to F5, gets a
 * docstring, fossilizes into the bank, and P1 renders it into a paper where no proof cites it
 * (observed live: `cellApproxPolynomial_coeff_envelope`, discrete-ATE Lemma 10). The bank graph
 * cannot detect this: its `proof-uses`/`ref_set` edges record what the DISCOVERY-stage derivation
 * planned, not what the final Lean realizes — over- and under-declared in the same run. This
 * sweep therefore reads the ground truth: the Lean sources at the done-point, when usage is final.
 *
 * A finding is a FLAG for the orchestrator, never an auto-delete: a follow-on run may consume an
 * earlier run's helpers (substrate reuse), so "unused by this run" is grounds for adjudication —
 * prune, or keep with a recorded reason.
 *
 * Scope guards against false positives: only public, attribute-free `theorem`/`lemma`/`def`s are
 * candidates (an `@[simp]`-style attribute or `instance` is consumed implicitly, with no textual
 * call site), and declarations realizing a graph node are exempt (results are products — they are
 * ALLOWED to have no consumer). Usage is a whole-identifier textual match over comment/string-
 * masked sources; same-name declarations in different namespaces merge, which can only
 * under-report (the safe direction).
 *
 * Deliberate keeps: a decl whose preceding lines carry a `-- keep: <reason>` comment is exempt —
 * the justification lives in the source next to what it justifies, and the sweep stays quiet on
 * re-entry. An empty reason does not count.
 */

export interface DeadHelperFinding {
  decl: string;
  file: string;
  line: number;
}

interface DeclSite {
  name: string;
  file: string;
  line: number;
  attributed: boolean;
  kept: boolean;
}

/** Char indexes of `-- keep: <reason>` markers in the RAW source (comments are masked everywhere
 *  else). Each marker exempts exactly the NEXT declaration that follows it — binding by adjacency
 *  in char order, so a marker never leaks onto later declarations and an intervening docstring or
 *  attribute block of any length cannot detach it (a fixed lookback window did both — audited
 *  2026-08-25). */
function keepMarkerIndexes(raw: string): number[] {
  return [...raw.matchAll(/^[ \t]*--\s*keep:\s*\S.*$/gm)].map((m) => m.index!);
}

// Name class covers Lean's real shapes: unicode letters (τ, ℓ-names) and dotted declarations.
// Dotted names are captured in full so they are never mistaken for their namespace prefix; they
// are then SKIPPED as candidates (call sites may use any qualified form, so a textual usage count
// is unreliable — under-reporting is the safe direction).
const DECL_RE =
  /^([ \t]*)((?:@\[[^\]]*\][ \t\r\n]*)*)((?:(?:noncomputable|private|protected|scoped|local|partial|unsafe|nonrec)\s+)*)(theorem|lemma|def|instance|abbrev)\s+([\p{L}_][\p{L}\p{N}_?!']*(?:\.[\p{L}_][\p{L}\p{N}_?!']*)*)/gmu;

/** Public candidate + exempt declaration sites in one source. `masked` and `raw` are the same
 *  text with comments/strings blanked in `masked` (the mask is offset-preserving). */
export function scanDeclSites(masked: string, raw: string, file: string): DeclSite[] {
  const keeps = keepMarkerIndexes(raw);
  const out: DeclSite[] = [];
  let m: RegExpExecArray | null;
  let prevEnd = -1;
  while ((m = DECL_RE.exec(masked))) {
    const [, , attrs, mods, kind, name] = m;
    const declIndex = m.index;
    // A marker between the previous declaration and this one binds to this one.
    const kept = keeps.some((k) => k > prevEnd && k < declIndex);
    prevEnd = declIndex;
    if (/\bprivate\b/.test(mods)) continue;
    if (kind === "instance" || kind === "abbrev") continue; // consumed implicitly / inlined
    if (name.includes(".")) continue; // dotted decl: usage-count unreliable, skip (see DECL_RE note)
    const line = masked.slice(0, m.index).split("\n").length;
    out.push({ name, file, line, attributed: attrs.trim().length > 0, kept });
  }
  return out;
}

export async function sweepDeadHelpers(
  leanDir: string,
  graphDeclNames: ReadonlySet<string>,
  opts?: {
    /** Extra root to scan for CONSUMERS (candidates still come only from `leanDir`). Runs share
     *  substrate across sibling run directories (a follow-on run consumes an earlier run's
     *  helpers from its own tree), so counting usage inside `leanDir` alone would flag
     *  cross-run-consumed helpers as dead. Default: `leanDir` only. */
    searchRoot?: string;
  },
): Promise<DeadHelperFinding[]> {
  if (!leanDir) return [];
  const readTree = async (root: string): Promise<{ file: string; src: string; raw: string }[]> => {
    let rels: string[];
    try {
      rels = (await readdir(root, { recursive: true }))
        .map(String)
        .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
        .sort();
    } catch {
      return []; // best-effort, like the sibling F3.5 scanners
    }
    const out: { file: string; src: string; raw: string }[] = [];
    for (const rel of rels) {
      try {
        const raw = await readFile(path.join(root, rel), "utf8");
        out.push({ file: rel.replaceAll(path.sep, "/"), src: maskLeanCommentsAndStrings(raw), raw });
      } catch {
        /* file vanished between readdir and read */
      }
    }
    return out;
  };
  const masked = await readTree(leanDir);
  const searchRoot = opts?.searchRoot ? path.resolve(opts.searchRoot) : null;
  const leanAbs = path.resolve(leanDir);
  const usageCorpus =
    searchRoot === null || searchRoot === leanAbs
      ? masked
      : leanAbs.startsWith(searchRoot + path.sep)
        ? await readTree(searchRoot) // parent root already covers leanDir
        : [...(await readTree(searchRoot)), ...masked];
  // Graph nodes may record fully qualified decl names; call sites use the short name.
  const exempt = new Set<string>();
  for (const d of graphDeclNames) {
    exempt.add(d);
    exempt.add(d.split(".").pop()!);
  }
  const sites: DeclSite[] = [];
  for (const { file, src, raw } of masked) sites.push(...scanDeclSites(src, raw, file));

  const findings: DeadHelperFinding[] = [];
  for (const s of sites) {
    if (s.attributed || s.kept || exempt.has(s.name)) continue;
    const esc = s.name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const wordRe = new RegExp(`(?<![\\p{L}\\p{N}_'])${esc}(?![\\p{L}\\p{N}_?!'])`, "gu");
    // Every definition site of the same short name anywhere in the corpus contributes one match
    // that is not a use (the corpus may span sibling run dirs with their own re-declarations).
    const defRe = new RegExp(
      `(?:theorem|lemma|def|instance|abbrev)\\s+${esc}(?![\\p{L}\\p{N}_?!'])`,
      "gu",
    );
    let uses = 0;
    let defs = 0;
    for (const { src } of usageCorpus) {
      uses += src.match(wordRe)?.length ?? 0;
      defs += src.match(defRe)?.length ?? 0;
    }
    if (uses - Math.max(defs, 1) <= 0) findings.push({ decl: s.name, file: s.file, line: s.line });
  }
  // One finding per name (same-name sites would all report or none).
  const seen = new Set<string>();
  return findings.filter((f) => (seen.has(f.decl) ? false : (seen.add(f.decl), true)));
}
