import type { Core } from "./schema.js";

/** N-family TeX control words (spelled without the leading `n`) whose under-escaped
 * `\n...` form silently decodes to a newline + remainder. Unlike b/f/r/t, a decoded
 * newline is legitimate content (multi-line TeX must use `\n` escapes in valid JSON),
 * so restoration is dictionary-gated. Multi-char suffixes require a non-letter,
 * non-dot boundary (the dot exclusion keeps a line break before "e.g."/"eg." intact). */
const N_COMMAND_MULTI =
  /^(?:eq|otin|ot|abla|mid|eg|olimits|onumber|atural|earrow|warrow|ewline|cong|leq|geq|gtr|sim|prec|succ|vdash|vDash|Vdash|subseteq|supseteq|triangleleft|triangleright|orm)(?![A-Za-z.])/;
// Deliberately ABSENT from the table: suffixes that are common prose words
// ("exists" for `\nexists`, "less" for `\nless`, "parallel" for `\nparallel`).
// A line break before such a word is far more frequent than an under-escaped
// spelling of the command, so inferring the command there corrupts legitimate
// prose; those three commands must be authored with the doubled backslash.
/** The single-letter suffix `e` (`\ne`) needs the legacy tight boundary: only a
 * delimiter that is natural after the relation but implausible after the letter
 * `e` as ordinary math. Corpus-verified exclusions: `e^`/`e_` (the exponential
 * and subscripted variables, e.g. an mgf bound `\[` + newline + `e^{s\lambda n}`)
 * must stay newlines. `u` (`\nu`) is deliberately NOT inferred at all — accepted
 * papers legitimately open display math with the variable `u` (`u^\alpha`,
 * `u\ge…`), so an under-escaped `\nu` is accepted silent residue instead. */
const N_COMMAND_SHORT = /^e(?=$|[\s\\}\],])/;

/** Normalize raw model-authored JSON bytes BEFORE `JSON.parse`. Post-parse, an
 * under-escaped `\theta` and an intended tab+`heta` are the same characters — the
 * information is destroyed — but in the raw bytes the single backslash is still
 * visible, so repair is exact rather than heuristic. Inside string literals, an
 * odd-count backslash followed by:
 *   - `b`/`f`/`r`/`t` + a letter is an under-escaped TeX control word (`\beta`,
 *     `\frac`, `\rho`, `\theta`, `\to`, …): double the backslash. Intentional
 *     control characters directly before a letter do not occur in this pipeline;
 *     a wrong doubling is visible TeX garbage caught by the render gate, whereas
 *     the alternative was silent data corruption.
 *   - `n` is doubled only for dictionary-listed TeX commands at a word boundary;
 *     every other `\n` stays a genuine line break.
 *   - `u` + 4 hex digits is a genuine `\uXXXX` escape and is preserved; any other
 *     `\u` (`\underline`, …) is doubled.
 *   - any character that is not a valid JSON escape (`\alpha`, `\{`, `\[`, …) is
 *     doubled: JSON.parse would otherwise throw, and the only sane reading of an
 *     isolated invalid escape is a literal TeX backslash.
 * Text outside string literals, even-count backslash runs, `\"`, `\/`, and `\\`
 * are untouched. The transform is idempotent. */
export function normalizeRawModelJson(raw: string): string {
  let out = "";
  let i = 0;
  let inString = false;
  while (i < raw.length) {
    const ch = raw[i];
    if (!inString) {
      if (ch === '"') inString = true;
      out += ch;
      i += 1;
      continue;
    }
    if (ch === '"') {
      inString = false;
      out += ch;
      i += 1;
      continue;
    }
    if (ch !== "\\") {
      out += ch;
      i += 1;
      continue;
    }
    let j = i;
    while (j < raw.length && raw[j] === "\\") j += 1;
    const run = raw.slice(i, j);
    const next = raw[j] ?? "";
    if (run.length % 2 === 0) {
      // Pairs decode to literal backslashes; the following char is plain content.
      out += run;
      i = j;
      continue;
    }
    // Odd run: the final backslash + `next` forms a JSON escape (or an invalid one).
    const keep = () => {
      out += run + next;
      i = j + 1;
    };
    const double = () => {
      out += run + "\\" + next;
      i = j + 1;
    };
    if (next === '"' || next === "\\" || next === "/") keep();
    else if (next === "u") {
      if (/^[0-9a-fA-F]{4}/.test(raw.slice(j + 1))) keep();
      else double();
    } else if (next === "b" || next === "f" || next === "r" || next === "t") {
      if (/^[A-Za-z]/.test(raw.slice(j + 1))) double();
      else keep();
    } else if (next === "n") {
      const rest = raw.slice(j + 1);
      if (N_COMMAND_MULTI.test(rest) || N_COMMAND_SHORT.test(rest)) double();
      else keep();
    } else double();
  }
  return out;
}

/** Recursively apply `repairSerializedLatex` to every string in a parsed model
 * payload (arrays/objects mutated in place). Shared by every model boundary that
 * ingests TeX-bearing JSON without a typed Core shape. */
export function repairLatexStringsDeep(value: unknown): void {
  if (Array.isArray(value)) {
    for (let i = 0; i < value.length; i++) {
      if (typeof value[i] === "string") value[i] = repairSerializedLatex(value[i]);
      else repairLatexStringsDeep(value[i]);
    }
    return;
  }
  if (value === null || typeof value !== "object") return;
  for (const [key, child] of Object.entries(value as Record<string, unknown>)) {
    if (typeof child === "string") (value as Record<string, unknown>)[key] = repairSerializedLatex(child);
    else repairLatexStringsDeep(child);
  }
}

/** Post-parse backstop behind `normalizeRawModelJson`: no decoded string at a model
 * boundary may contain a control character other than newline. After normalization
 * such a character can only arise from an escaping error the normalizer declined to
 * guess about, so fail loudly with the field path instead of letting corrupted data
 * reach schema validation or proposal comparison. */
export function assertNoDecodedControlChars(value: unknown, source: string): void {
  const offenses: string[] = [];
  const visit = (v: unknown, path: string): void => {
    if (typeof v === "string") {
      const m = /[\u0000-\u0009\u000b-\u001f]/.exec(v);
      if (m) {
        const code = m[0].charCodeAt(0).toString(16).toUpperCase().padStart(4, "0");
        const snippet = JSON.stringify(v.slice(Math.max(0, m.index - 20), m.index + 20));
        offenses.push(`${path || "(root)"}: U+${code} at offset ${m.index} near ${snippet}`);
      }
      return;
    }
    if (Array.isArray(v)) {
      v.forEach((child, idx) => visit(child, `${path}[${idx}]`));
      return;
    }
    if (v !== null && typeof v === "object") {
      for (const [key, child] of Object.entries(v)) visit(child, path ? `${path}.${key}` : key);
    }
  };
  visit(value, "");
  if (offenses.length > 0) {
    throw new Error(
      `${source}: decoded JSON control character(s) in model-authored content — almost always an ` +
        `under-escaped TeX backslash (e.g. \`\\theta\` written with one backslash decodes to tab + "heta"). ` +
        `Re-emit with every TeX backslash doubled. Offending field(s):\n` +
        offenses.map((o) => `  - ${o}`).join("\n"),
    );
  }
}

/** Repair recurrent JSON escape ambiguities from model-authored LaTeX. In JSON,
 * an under-escaped `\ne` becomes a newline followed by `e`, and `\notin` becomes
 * a newline followed by `otin`. A row break emitted as three JSON backslashes
 * can likewise decode to one TeX backslash plus a newline. These repairs are
 * deliberately narrow so ordinary prose line breaks remain untouched. */
export function repairSerializedLatex(value: string): string {
  // A model that emits LaTeX inside a JSON string can over-escape every command,
  // leaving two literal backslashes after JSON.parse (for example `\\(` and
  // `\\pi`). Doubled inline-math delimiters are invalid TeX and therefore a
  // reliable signal for this whole-string serialization error. Preserve real
  // `\\` row/line breaks: the collapse only applies before non-space,
  // non-digit characters.
  // Treat this as a WHOLE-STRING over-escape only when the string has no
  // canonical single-backslash LaTeX at all.  In an otherwise valid proof,
  // `\\\\(` can instead be a legitimate row break followed immediately by a
  // parenthesized expression (for example inside `cases`).  Globally
  // de-doubling that mixed string turns the row break into an inline-math
  // opener and makes the deterministic render invalid.
  const hasCanonicalSingleBackslash = /(?<!\\)\\(?!\\)/.test(value);
  // Positive whole-string evidence is required before de-doubling: PAIRED doubled
  // inline-math delimiters (`\\(` and `\\)`). A lone `\\(` is equally consistent
  // with a legitimate row break directly before a parenthesized expression, and
  // de-doubling that silently changes meaning; an unpaired doubled delimiter
  // instead stays invalid TeX and fails loudly at the render gate.
  const hasOverEscapeEvidence = /\\\\\(/.test(value) && /\\\\\)/.test(value);
  const overEscapeRepaired = hasOverEscapeEvidence && !hasCanonicalSingleBackslash
    ? value.replace(/\\\\(?=[^\s\d])/g, "\\")
    : value;
  const repaired = overEscapeRepaired
    // A decoded control character in a/b/f/r/t position followed by a letter is a
    // TeX control word whose backslash was eaten by escape processing — either
    // JSON's own grammar (an under-escaped `\theta` decodes to tab + "heta") or
    // a model/tool boundary that interpreted a C-style escape itself (BEL from
    // `\asymp`'s non-JSON `\a` is a corpus-verified case) and re-serialized
    // the control character as a valid Unicode escape, which pre-parse raw-byte
    // normalization must preserve. The pipeline invariant makes the restore
    // unambiguous: authored control characters are forbidden in formal/prose
    // fields (enforced by `assertNoDecodedControlChars` at every model
    // boundary), while each TeX command family here is broad (`\beta`/`\begin`,
    // `\frac`/`\forall`, `\rho`/`\rightarrow`, `\theta`/`\text`/`\to`). A
    // control character NOT followed by a letter is left alone and fails closed
    // at the backstop. `\v...` (the same rule for vertical tab) follows below.
    .replace(/\x07(?=[A-Za-z])/g, "\\a")
    .replace(/[\b](?=[A-Za-z])/g, "\\b")
    .replace(/\f(?=[A-Za-z])/g, "\\f")
    .replace(/\r(?=[A-Za-z])/g, "\\r")
    .replace(/\t(?=[A-Za-z])/g, "\\t")
    // Some model/tool boundaries permissively interpret the non-JSON `\v`
    // escape and then re-serialize the resulting vertical tab as `\u000b`.
    // At that point raw-byte normalization sees a valid Unicode escape, so the
    // only recoverable signal is the decoded vertical tab. Vertical tabs are
    // forbidden in authored pipeline text, while TeX has a broad `\v...`
    // command family (`\varnothing`, `\varepsilon`, `\vartheta`, ...), hence
    // a vertical tab immediately before a letter is unambiguously that lost
    // TeX backslash.
    .replace(/\v(?=[A-Za-z])/g, "\\v")
    // Models occasionally serialize a visual newline as the two literal
    // characters `\\n`. TeX has no whitespace-followed `\\n` command, so this
    // case is unambiguous; command names such as `\\nu` remain untouched.
    // A literal serialized newline immediately after a display delimiter is
    // unambiguous even when the next formula/prose token starts in lowercase:
    // `\\[\\np_+` and `\\]\\nand hence` cannot be TeX commands.
    .replace(/(\\[\[\]])\\n/g, "$1\n")
    .replace(/\\n(?=\s|\\|[A-Z])/g, "\n")
    .replace(/\n(?=e(?:\\|\s|[}\],]))/g, "\\n")
    .replace(/\n(?=otin(?:\\|\s|[}\],]))/g, "\\n")
    .replace(/(?<!\\)\\\n(?=\s*&)/g, "\\\\\n")
    // Model-authored DOI strings occasionally omit the closing brace of a
    // final `\\mathrm{...}` immediately before the inline-math delimiter,
    // yielding `\\mathrm{token\\)` and an invalid render.  The delimiter is
    // an unambiguous boundary, so restore only that missing brace.
    .replace(/\\mathrm\{([^{}\n]*?)\\\)/g, "\\mathrm{$1}\\)");
  return repaired.replace(
    /\\begin\{aligned\}([\s\S]*?)\\end\{aligned\}/g,
    (_block, body: string) =>
      `\\begin{aligned}${body.replace(/\\+(?=(?:\[[^\]\n]*\])?[ \t]*\n)/g, "\\\\")}\\end{aligned}`,
  );
}

export interface AlignedRowTerminatorViolation {
  block: number;
  line: number;
  count: number;
}

/** Compilation is too permissive here: pdfTeX accepts several malformed
 * backslash counts. Enforce the serialization contract independently. */
export function alignedRowTerminatorViolations(value: string): AlignedRowTerminatorViolation[] {
  const violations: AlignedRowTerminatorViolation[] = [];
  let block = 0;
  for (const match of value.matchAll(/\\begin\{aligned\}([\s\S]*?)\\end\{aligned\}/g)) {
    block += 1;
    match[1].split("\n").forEach((line, index) => {
      const row = /(\\+)(?:\[[^\]\n]*\])?[ \t]*$/.exec(line);
      if (row && row[1].length !== 2) violations.push({ block, line: index + 1, count: row[1].length });
    });
  }
  return violations;
}

export function assertCanonicalAlignedRowTerminators(value: string, source: string): void {
  const violations = alignedRowTerminatorViolations(value);
  if (violations.length === 0) return;
  throw new Error(
    `${source} has noncanonical aligned row terminator(s): ` +
      violations.map((v) => `block ${v.block} line ${v.line} has ${v.count} backslashes`).join("; "),
  );
}

/** Normalize every authored string that can carry LaTeX before core.json is
 * persisted. This keeps the typed core and deterministic TeX render in sync. */
export function repairCoreLatexSerialization(core: Core): void {
  const repair = (value: string | undefined): string | undefined =>
    value === undefined ? undefined : repairSerializedLatex(value);

  core.target_estimand = repairSerializedLatex(core.target_estimand);
  core.estimand_functional = repair(core.estimand_functional);
  core.tldr = repair(core.tldr);
  core.related_work = repair(core.related_work);
  core.interpretation = repair(core.interpretation);
  core.technical_internal_limitation = repair(core.technical_internal_limitation);
  core.honest_scope = repair(core.honest_scope);
  if (core.project_justification) {
    core.project_justification.gap = repairSerializedLatex(core.project_justification.gap);
    core.project_justification.niche = repairSerializedLatex(core.project_justification.niche);
    core.project_justification.fill = repairSerializedLatex(core.project_justification.fill);
  }
  for (const symbol of core.symbols) {
    symbol.type = repairSerializedLatex(symbol.type);
    symbol.space = repair(symbol.space);
    symbol.sig = repair(symbol.sig);
    symbol.def = repair(symbol.def);
    symbol.role = repair(symbol.role);
  }
  for (const assumption of core.assumptions) {
    assumption.condition = repairSerializedLatex(assumption.condition);
    if (assumption.novel) assumption.novel.justification = repairSerializedLatex(assumption.novel.justification);
  }
  for (const definition of core.definitions) {
    definition.name = repairSerializedLatex(definition.name);
    definition.construction = repairSerializedLatex(definition.construction);
  }
  for (const statement of core.statements) {
    statement.statement = repairSerializedLatex(statement.statement);
    statement.proof_tex = repair(statement.proof_tex);
    statement.justification = repair(statement.justification);
    statement.gap = repair(statement.gap);
    statement.consumer = repair(statement.consumer);
  }
  for (const entry of core.bibliography) {
    entry.citation = repair(entry.citation);
  }
}
