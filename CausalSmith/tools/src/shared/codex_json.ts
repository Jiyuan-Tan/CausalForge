/**
 * Shared parser + persistence helpers for codex JSON outputs.
 *
 * Why this module exists: every codex call in the study pipeline is followed
 * by `JSON.parse`. Historically each stage had its own local
 * `expectStringJsonOutput` and the raw stdout was discarded on parse failure,
 * making post-mortem diagnostics impossible without scraping
 * `~/.codex/sessions/`. This module:
 *
 *   1. Persists the raw stdout to `<runDir>/codex_raw/<tag>__<ISO>.txt`
 *      BEFORE parsing, so a parse failure leaves a forensic trail in the
 *      run dir itself.
 *   2. Parses with brace-balance repair (a 1-char truncation by the model
 *      is the single most common failure mode observed so far).
 *   3. Throws errors tagged `code: "codex_malformed_output"` so
 *      the retired study-pipeline CLI can route the run via `study_bank.ts`.
 */
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";

/**
 * Unwrap the harness `{ "__unparsedToolInput": { "raw": "<json string>" } }`
 * envelope. When a model emits its structured answer as a tool call whose input
 * the runner could not parse, the runner passes the input through under this key
 * as a raw string — the payload is valid JSON with the intended fields, just
 * double-wrapped. Recursively unwrap so schema validation sees the real object.
 */
function unwrapToolInput(value: unknown, depth = 0): unknown {
  if (depth > 4 || value === null || typeof value !== "object") return value;
  const keys = Object.keys(value as Record<string, unknown>);
  if (keys.length === 1 && keys[0] === "__unparsedToolInput") {
    const inner = (value as { __unparsedToolInput: unknown }).__unparsedToolInput;
    const raw = inner && typeof inner === "object"
      ? (inner as { raw?: unknown }).raw
      : inner;
    if (typeof raw === "string") {
      // Clean case: the inner string is valid JSON.
      try { return unwrapToolInput(JSON.parse(raw), depth + 1); } catch { /* corrupted — repair below */ }
      // Corrupted case (large payloads escape imperfectly / truncate): salvage
      // the largest parseable object, then brace-balance-repair a truncation.
      const scanned = findFirstParseableObject(raw);
      if (scanned !== null) return unwrapToolInput(scanned, depth + 1);
      const repaired = tryBraceBalanceRepair(raw);
      if (repaired !== null) {
        try { return unwrapToolInput(JSON.parse(repaired), depth + 1); } catch { /* give up */ }
      }
      return value;
    }
    return unwrapToolInput(inner, depth + 1);
  }
  return value;
}

export function expectStringJsonOutput(stdout: string): unknown {
  const trimmed = stdout.trim();
  // Fast path: the whole string is the JSON.
  try {
    return unwrapToolInput(JSON.parse(trimmed));
  } catch {
    /* fall through */
  }
  // Strip a single fenced block if present (```json ... ``` or ``` ... ```).
  const fenced = trimmed.match(/```(?:json)?\s*([\s\S]*?)```/i);
  const candidate = fenced?.[1] ?? trimmed;
  const firstBrace = candidate.indexOf("{");
  if (firstBrace < 0) {
    // why: the fenced block may be non-JSON prose (e.g. a ```lean` snippet) with the REAL bare JSON
    // after it — scan the whole raw output before giving up (regression: prose-fence-then-JSON).
    const raw = findFirstParseableObject(trimmed);
    if (raw !== null) return unwrapToolInput(raw);
    throw makeMalformed(`codex output contained no JSON object`);
  }
  // Prefer the FIRST balanced object — handles double-emitted JSON where the
  // model writes a pretty form followed by a compact restatement.
  const balancedEnd = findBalancedObjectEnd(candidate, firstBrace);
  if (balancedEnd !== -1) {
    try {
      return unwrapToolInput(JSON.parse(candidate.slice(firstBrace, balancedEnd + 1)));
    } catch {
      /* fall through to repair */
    }
  }
  // Legacy slice: first `{` to last `}`. Preserves behavior for outputs with
  // prose around a single JSON body and is the input shape the brace-balance
  // repair was designed for.
  const lastBrace = candidate.lastIndexOf("}");
  const sliced = lastBrace > firstBrace ? candidate.slice(firstBrace, lastBrace + 1) : candidate.slice(firstBrace);
  try {
    return unwrapToolInput(JSON.parse(sliced));
  } catch {
    /* try escape repair, then brace-balance repair */
  }
  // LaTeX in a prose field is the most common single cause of an unparseable verdict;
  // try it before brace balance, since an unbalanced-looking body is often just a
  // string that ended early at a bad escape.
  const escaped = repairInvalidStringEscapes(sliced);
  if (escaped !== null) {
    try {
      return unwrapToolInput(JSON.parse(escaped));
    } catch {
      /* not (only) an escape problem — fall through */
    }
  }
  const repaired = tryBraceBalanceRepair(sliced);
  if (repaired !== null) {
    try {
      return unwrapToolInput(JSON.parse(repaired));
    } catch {
      // why: repair failed (e.g. the leading fenced block held non-JSON braces like `{x | P x}`);
      // fall through to the whole-output raw scan rather than throwing over the real later JSON.
    }
  }
  // why: only scan inner balanced objects after outer-slice repair, or a
  // one-char-truncated wrapper like {"insight":{...} loses its top-level key.
  const rawObj = findFirstParseableObject(trimmed);
  if (rawObj !== null) return unwrapToolInput(rawObj);
  throw makeMalformed(`codex output not valid JSON and unrepairable`);
}

/**
 * Scan `text` for the first balanced `{...}` substring that parses as JSON,
 * trying each top-level `{` in turn. Returns the parsed value, or null if no
 * brace yields valid JSON. Robust to prose / fenced code blocks preceding a
 * bare JSON object (a `{` that opens a non-JSON snippet just fails to parse and
 * the scan advances to the next `{`).
 */
function findFirstParseableObject(text: string): unknown | null {
  let from = text.indexOf("{");
  while (from >= 0) {
    const end = findBalancedObjectEnd(text, from);
    if (end !== -1) {
      try {
        return JSON.parse(text.slice(from, end + 1));
      } catch {
        /* not valid JSON at this brace — advance */
      }
    }
    from = text.indexOf("{", from + 1);
  }
  return null;
}

/**
 * Find the position of the `}` that closes the object starting at `start`.
 * Respects string literals and escape sequences. Returns -1 if unbalanced.
 */
function findBalancedObjectEnd(text: string, start: number): number {
  let depth = 0;
  let inString = false;
  let escape = false;
  for (let i = start; i < text.length; i++) {
    const ch = text[i];
    if (inString) {
      if (escape) {
        escape = false;
      } else if (ch === "\\") {
        escape = true;
      } else if (ch === '"') {
        inString = false;
      }
      continue;
    }
    if (ch === '"') {
      inString = true;
      continue;
    }
    if (ch === "{") {
      depth++;
    } else if (ch === "}") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

/**
 * Append `}` / `]` characters when the input is missing a small number of
 * closes (≤ 3 of each). Returns null if no repair is plausible — i.e. the
 * input is over-balanced or missing too many closes to be a likely
 * truncation artefact.
 *
 * Pragmatic guardrails: we do not attempt to repair quotes, commas, or
 * deeper structural issues — those require actually understanding the
 * partial JSON and risk silently mis-parsing valid-looking but wrong
 * outputs.
 */
export function tryBraceBalanceRepair(s: string): string | null {
  const openCurly = countUnquoted(s, "{");
  const closeCurly = countUnquoted(s, "}");
  const openSquare = countUnquoted(s, "[");
  const closeSquare = countUnquoted(s, "]");
  const missingCurly = openCurly - closeCurly;
  const missingSquare = openSquare - closeSquare;
  if (missingCurly < 0 || missingSquare < 0) return null;
  if (missingCurly === 0 && missingSquare === 0) return null;
  if (missingCurly > 3 || missingSquare > 3) return null;
  // Close arrays before objects (innermost first heuristic — works for the
  // common case where the model truncated mid-object inside an array).
  return s + "]".repeat(missingSquare) + "}".repeat(missingCurly);
}

/**
 * Escape backslashes that begin an INVALID escape sequence inside a JSON string,
 * leaving valid ones untouched. Returns null when nothing needed repair.
 *
 * Referees and solvers write LaTeX into JSON prose fields, and JSON's escape grammar
 * admits only `" \ / b f n r t uXXXX`. So `\(q_d(P)=r_n\)` — ordinary inline math —
 * is a hard parse error, and the whole verdict is lost over punctuation. This is not
 * hypothetical: it killed a D0.5.G general review AFTER both referees had already
 * passed, turning a completed judgment into a crash at the finish line.
 *
 * Doubling the offending backslash is content-preserving: `\(` becomes `\\(`, which
 * parses back to the literal `\(` the model meant. Two cases must not be mangled:
 *   • `\\le` is ALREADY valid (an escaped backslash followed by `le`) — the pair is
 *     consumed together, never re-escaped. Models mix both spellings in one string.
 *   • `\u` is a valid PREFIX but only with four hex digits, so `\usepackage` is
 *     invalid and must be repaired, while `é` must not be.
 *
 * Deliberately narrower than a general "fix the JSON" pass: it changes nothing
 * outside string literals and cannot alter structure, so it can cause a parse to
 * succeed but never to succeed DIFFERENTLY.
 */
export function repairInvalidStringEscapes(s: string): string | null {
  const SIMPLE = new Set(['"', "\\", "/", "b", "f", "n", "r", "t"]);
  const isHex4 = (at: number): boolean => /^[0-9a-fA-F]{4}$/.test(s.slice(at, at + 4));
  let out = "";
  let inString = false;
  let changed = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (!inString) {
      if (c === '"') inString = true;
      out += c;
      continue;
    }
    if (c === '"') {
      inString = false;
      out += c;
      continue;
    }
    if (c !== "\\") {
      out += c;
      continue;
    }
    const next = s[i + 1];
    if (next !== undefined && (SIMPLE.has(next) || (next === "u" && isHex4(i + 2)))) {
      out += c + next; // valid escape — consume BOTH so `\\` is never re-escaped
      i += 1;
      continue;
    }
    out += "\\\\"; // invalid escape — make the backslash literal
    changed = true;
  }
  return changed ? out : null;
}

/** Count occurrences of a single-character bracket OUTSIDE of JSON strings. */
function countUnquoted(s: string, ch: string): number {
  let n = 0;
  let inStr = false;
  let escaped = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (escaped) {
      escaped = false;
      continue;
    }
    if (c === "\\") {
      escaped = true;
      continue;
    }
    if (c === '"') {
      inStr = !inStr;
      continue;
    }
    if (!inStr && c === ch) n++;
  }
  return n;
}

function makeMalformed(message: string): Error & { code: string } {
  return Object.assign(new Error(message), { code: "codex_malformed_output" });
}

/**
 * Persist `stdout` to `<runDir>/codex_raw/<safe_tag>__<ISO>.txt`. Best
 * effort: never throws (a parse failure must still surface the underlying
 * issue, not a write race). Returns the path written, or null on failure.
 */
export async function persistCodexRaw(
  runDir: string,
  tag: string,
  stdout: string,
): Promise<string | null> {
  try {
    const dir = path.join(runDir, "codex_raw");
    await mkdir(dir, { recursive: true });
    const safeTag = tag.replace(/[^A-Za-z0-9._-]+/g, "_").slice(0, 80) || "untagged";
    const stamp = new Date().toISOString().replace(/[:.]/g, "-");
    const file = path.join(dir, `${safeTag}__${stamp}.txt`);
    await writeFile(file, stdout, "utf8");
    return file;
  } catch {
    return null;
  }
}

/**
 * Convenience: persist stdout, then parse. Use this at every codex call
 * site so the raw response is on disk before any parse error throws.
 */
export async function parseAndPersist(
  stdout: string,
  runDir: string,
  tag: string,
): Promise<unknown> {
  await persistCodexRaw(runDir, tag, stdout);
  return expectStringJsonOutput(stdout);
}
