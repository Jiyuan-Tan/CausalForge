// C3 — API.md ↔ source file-path drift. Both `doc/API.md` (Causalean) and
// `CausalSmith/doc/API.md` document the library under `## N. \`path\` — desc`
// section headers. The path in the FIRST backtick of a section header is the
// file/dir that section describes; when that file is renamed/moved/deleted the
// section silently documents a path that no longer exists. This extracts those
// path tokens and checks them against disk. High-confidence + zero LLM: it only
// checks the section's canonical path, not decl names mentioned in prose
// (resolving prose identifiers is noisy and belongs to the LLM C2 pass).

/** A path token taken from an API.md section header (`## N. \`token\` — …`),
 *  brace-groups already expanded so each `token` is a single concrete path. */
export interface ApiMdPathRef {
  header: string; // the raw header line (for the report)
  token: string; // a single path relative to the file's source root
  line: number; // 1-indexed line of the header
}

export interface ApiMdFinding extends ApiMdPathRef {
  note: string;
}

/** Expand a single `prefix{a, b, c}suffix` brace group into one path per item.
 *  API.md groups co-located files this way (e.g. `SCM/Do/{LocalMarkov,
 *  GlobalMarkov}.lean`). No brace → the token unchanged. Only the first group is
 *  expanded (API.md never nests them). */
function expandBraces(token: string): string[] {
  const m = token.match(/^(.*)\{([^}]+)\}(.*)$/);
  if (!m) return [token];
  const [, prefix, inner, suffix] = m;
  return inner.split(",").map((item) => `${prefix}${item.trim()}${suffix}`);
}

/** A backtick token is a path reference if it names a file or directory: it
 *  contains a `/`, or ends in `.lean`. Plain identifiers (`doMono`) are not. */
function isPathToken(token: string): boolean {
  return token.includes("/") || token.endsWith(".lean");
}

/**
 * Extract path references from an API.md body: for each `## ` section header,
 * take the FIRST backtick-quoted token; if it is path-like, expand any brace
 * group and emit one ref per concrete path. Topic headers with no path-like
 * first backtick (e.g. `## Workspace context`, `## 1. Panel theorems`) yield
 * nothing.
 */
export function extractApiMdPathRefs(apiMdText: string): ApiMdPathRef[] {
  const out: ApiMdPathRef[] = [];
  const lines = apiMdText.split(/\r?\n/);
  for (let i = 0; i < lines.length; i++) {
    const ln = lines[i];
    if (!/^##\s/.test(ln)) continue;
    const tick = ln.match(/`([^`]+)`/);
    if (!tick) continue;
    const token = tick[1].trim();
    if (!isPathToken(token)) continue;
    for (const expanded of expandBraces(token)) {
      out.push({ header: ln.trim(), token: expanded, line: i + 1 });
    }
  }
  return out;
}

/** The concrete path to existence-check for a token. A glob token (`dir/*.lean`,
 *  documenting a whole directory of files) is reduced to its parent directory —
 *  the literal `*` is not a file, so checking the directory is the faithful test.
 *  A non-glob token is checked as-is. */
export function apiMdCheckTarget(token: string): string {
  const star = token.indexOf("*");
  if (star === -1) return token;
  const slash = token.lastIndexOf("/", star);
  return slash === -1 ? "." : token.slice(0, slash + 1);
}

/** Findings for refs whose resolved path is absent. `exists` resolves a check
 *  target (relative to the file's source root) to a boolean — injected so the
 *  pure function stays filesystem-free and testable. Glob tokens are checked at
 *  their parent directory via `apiMdCheckTarget`. */
export function apiMdMissingPaths(
  refs: ApiMdPathRef[],
  exists: (target: string) => boolean,
): ApiMdFinding[] {
  return refs
    .filter((r) => !exists(apiMdCheckTarget(r.token)))
    .map((r) => ({ ...r, note: `documented path \`${r.token}\` does not exist on disk` }));
}
