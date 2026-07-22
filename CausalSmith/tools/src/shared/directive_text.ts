// Directive-capture sanitizer, shared by every orchestrator directive CLI
// (`bin/{d0,dneg1,f2,f3}_directive.ts`, `bin/d0r_directed_solve.ts`).
//
// WHY THIS EXISTS. A directive is normally captured from a consult agent's output
// and piped into a directive CLI. When that capture is built wrong — the classic
// being `codex exec --json | jq -r '.msg.text'`, which prints a literal `null` for
// every event that has no `.msg.text` — the resulting text is the agent's private
// reasoning stream interleaved with dozens of `null` lines. The CLIs only refused
// an EMPTY directive, so the garbage was written to the escalation log verbatim and
// re-rendered into every solve prompt of the next round.
//
// Observed cost (stat_pn_weak_event_honest_inference, round 36): a 229-line
// directive of which 44 lines (19%) were the literal string `null`, with the actual
// instruction buried after the noise — re-sent to all 3 solve units.
//
// Policy: literal `null`/`undefined` lines are unambiguous capture artifacts and are
// stripped silently. A capture that is WHOLLY a JSON event stream, or that is mostly
// artifact lines, is refused — at that ratio the surviving prose is very likely
// truncated or interleaved too, and a wrong directive costs a full solve round.

/** A directive whose capture is too corrupt to trust. Recovery is re-capturing it,
 *  which is cheap; acting on a mangled directive is not. */
export class DirectiveCaptureError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "DirectiveCaptureError";
  }
}

export interface SanitizedDirective {
  /** The directive with capture artifacts removed. */
  text: string;
  /** Count of literal `null`/`undefined` lines dropped. */
  droppedArtifactLines: number;
  /** Non-blank line count BEFORE stripping. */
  totalLines: number;
}

/** Fraction of artifact lines above which the whole capture is refused rather than
 *  cleaned. Below it, the stray `null`s are noise around good prose; above it, the
 *  pipe itself was wrong and the prose cannot be trusted either. */
const REFUSE_ARTIFACT_RATIO = 0.3;

const ARTIFACT_LINE = /^(?:null|undefined)$/;

/** True when every non-blank line is a JSON object — i.e. a raw `codex exec --json`
 *  event stream was piped in whole, with no text extraction at all. */
function looksLikeRawEventStream(lines: string[]): boolean {
  const nonBlank = lines.filter((l) => l.trim().length > 0);
  if (nonBlank.length < 2) return false;
  return nonBlank.every((l) => {
    const t = l.trim();
    if (!t.startsWith("{") || !t.endsWith("}")) return false;
    try {
      return typeof JSON.parse(t) === "object";
    } catch {
      return false;
    }
  });
}

const RECAPTURE_RECIPE =
  "Re-capture the directive and pipe only the agent's FINAL message text — e.g. " +
  "`codex exec ... | tail -n +1` on plain (non-`--json`) output, or, with `--json`, " +
  "`jq -r 'select(.msg.type == \"agent_message\") | .msg.message'` (the `select` is what " +
  "keeps `jq -r` from emitting a `null` line per non-message event). " +
  "Pass --allow-dirty-capture to write it verbatim anyway.";

/**
 * Strip capture artifacts from a directive, or refuse if the capture is too corrupt.
 *
 * @param raw            the directive text as captured
 * @param allowDirty     bypass every refusal and return `raw` untouched (operator escape)
 * @throws DirectiveCaptureError when the capture is a raw event stream, is mostly
 *         artifact lines, or is empty once cleaned
 */
export function sanitizeDirectiveText(raw: string, allowDirty = false): SanitizedDirective {
  const trimmed = raw.trim();
  const lines = trimmed.split("\n");
  const nonBlank = lines.filter((l) => l.trim().length > 0);
  const droppedArtifactLines = nonBlank.filter((l) => ARTIFACT_LINE.test(l.trim())).length;

  if (allowDirty) {
    return { text: trimmed, droppedArtifactLines, totalLines: nonBlank.length };
  }

  if (trimmed.length === 0) throw new DirectiveCaptureError("Refusing to append an empty directive.");

  if (looksLikeRawEventStream(lines)) {
    throw new DirectiveCaptureError(
      `Refusing a directive that is a raw JSON event stream (${nonBlank.length} lines, every one a JSON object) — ` +
        `the agent's prose was never extracted. ${RECAPTURE_RECIPE}`,
    );
  }

  const ratio = nonBlank.length > 0 ? droppedArtifactLines / nonBlank.length : 0;
  if (ratio > REFUSE_ARTIFACT_RATIO) {
    throw new DirectiveCaptureError(
      `Refusing a directive whose capture is ${Math.round(ratio * 100)}% literal null/undefined lines ` +
        `(${droppedArtifactLines} of ${nonBlank.length}) — at that ratio the surviving prose is likely ` +
        `truncated or interleaved with the agent's reasoning stream. ${RECAPTURE_RECIPE}`,
    );
  }

  // Drop the artifact lines, then collapse the blank runs they leave behind so the
  // directive reads as authored prose rather than a gap-riddled transcript.
  const cleaned = lines
    .filter((l) => !ARTIFACT_LINE.test(l.trim()))
    .join("\n")
    .replace(/\n{3,}/g, "\n\n")
    .trim();

  if (cleaned.length === 0) {
    throw new DirectiveCaptureError(
      `Refusing a directive that is nothing but ${droppedArtifactLines} capture artifact line(s). ${RECAPTURE_RECIPE}`,
    );
  }

  return { text: cleaned, droppedArtifactLines, totalLines: nonBlank.length };
}

/**
 * CLI adapter: sanitize, report to stderr, and exit non-zero on a refused capture.
 * Returns the cleaned text, or `null` when the caller should stop (already reported).
 */
export function sanitizeDirectiveForCli(raw: string, allowDirty: boolean): string | null {
  try {
    const { text, droppedArtifactLines, totalLines } = sanitizeDirectiveText(raw, allowDirty);
    if (droppedArtifactLines > 0) {
      console.error(
        `[directive] stripped ${droppedArtifactLines} capture-artifact line(s) of ${totalLines} — ` +
          `the capture pipeline emitted literal null/undefined lines. ${RECAPTURE_RECIPE}`,
      );
    }
    return text;
  } catch (err) {
    console.error(err instanceof Error ? err.message : String(err));
    return null;
  }
}
