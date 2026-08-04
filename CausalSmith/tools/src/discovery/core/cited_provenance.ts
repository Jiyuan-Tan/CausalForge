/** Provenance resolution for attested `cited` nodes.
 *
 * Content attestation answers "does the source say what we claim it says". It does
 * NOT answer "is the source the one this result is due to" — and those come apart
 * routinely, because papers restate borrowed results in their own appendices.
 *
 * Observed on stat_reversekl_two_coverage (2026-07-25 audit): BOTH attested cited
 * nodes were verbatim-correct against the paper we read, and BOTH credited the wrong
 * authors. The located environments each pointed elsewhere:
 *   - `\begin{lemma}[{\citealt[Lemma~C.1]{zhao2024sharp}}]` — the concentration lemma
 *     belongs to a different paper with a different author set;
 *   - "we refer to \cite[Thm. 18.19]{guide2006infinite} for the proof of this
 *     statement" — a standard textbook theorem restated in a paper's appendix.
 * The verbatim check passed both times because the statements really were identical.
 *
 * So provenance cannot be inferred from a content match; it has to be asked. The
 * attestation CLI therefore requires an explicit decision (`--upstream` or
 * `--upstream-none`), and the marker scan below is only a backstop for the case where
 * the operator pasted enough of the source to make the borrowing visible.
 */

/** Citation markers that indicate the located statement credits an earlier work.
 *
 * HIGH PRECISION IS A HARD REQUIREMENT, not a preference. A marker BLOCKS
 * `--upstream-none`, so a false positive leaves the operator with only two exits:
 * abandon the attestation, or invent an `--upstream` citation to satisfy the check —
 * i.e. write fabricated provenance through the very tool built to prevent it. That is
 * worse than the bug this module addresses. Hence: only patterns that attribute
 * authorship, never patterns that merely appear near a citation. Phrases like
 * "due to", "is known as" and "first proved" were tried and REMOVED — they match
 * ordinary mathematical prose ("is known as the propensity score", "due to
 * boundedness of the second moment") and would fire on well-formed original
 * statements. `acknowledgeMarker` exists as the auditable escape for what remains.
 */
const UPSTREAM_MARKERS: ReadonlyArray<{ readonly label: string; readonly re: RegExp }> = [
  // `[A-Za-z]*\*?` covers the whole natbib family in one shape — `\citep*`,
  // `\citealt*`, `\citeyearpar`, `\citenum`, `\Citet`, … — instead of an
  // enumerated list that missed the starred/`par` variants.
  { label: "LaTeX citation macro", re: /\\[Cc]ite[A-Za-z]*\*?\s*[[{]/ },
  { label: "\"adapted from\"", re: /\badapted from\b/i },
  { label: "\"restated from\"", re: /\brestated (?:from|as)\b/i },
  { label: "\"reproduced from\"", re: /\breproduced (?:from|in)\b/i },
  { label: "\"taken from\"", re: /\btaken from\b/i },
  { label: "\"originally due/proved\"", re: /\boriginally (?:due|proved|proven|shown|established)\b/i },
  // Bounded window rather than "same sentence": the intervening citation routinely
  // contains periods ("we refer to \cite[Thm. 18.19]{…} for the proof"), so a
  // period-excluding window silently never matches the canonical case.
  { label: "\"we refer to … for the proof\"", re: /\bwe refer to\b[\s\S]{0,120}?\bfor the proof\b/i },
];

/** The primary source a restated `cited` statement is actually due to. */
export interface UpstreamSource {
  /** Free-text primary citation, e.g. "H. Zhao, C. Ye, Q. Gu, T. Zhang, arXiv:2411.04625". */
  readonly citation: string;
  /** Locator inside the primary, e.g. "Lemma C.1". */
  readonly locator?: string;
  /** Bibkey, when the primary is itself carried in the core `bibliography`. */
  readonly cite?: string;
}

/** Markers found in `verbatim` suggesting the statement is borrowed. Empty when none. */
export function detectUpstreamMarkers(verbatim: string): string[] {
  return UPSTREAM_MARKERS.filter((marker) => marker.re.test(verbatim)).map((marker) => marker.label);
}

export interface UpstreamDecisionInput {
  /** `--upstream` value: the primary source, when the located statement is borrowed. */
  readonly upstream?: string;
  readonly upstreamLocator?: string;
  readonly upstreamCite?: string;
  /** `--upstream-none`: operator affirms the statement originates in the cited work. */
  readonly upstreamNone: boolean;
  /** `--acknowledge-marker <why>`: the auditable escape when a marker fired on a
   *  statement that is nonetheless original. Recorded in the attestation note so the
   *  judgement is reviewable — never silently discarded. Without this, a false
   *  positive would push the operator into inventing an `--upstream` citation. */
  readonly acknowledgeMarker?: string;
  /** The `--verbatim` source-of-record text, scanned as a backstop. */
  readonly verbatim: string;
  /** Bibkeys available in the core `bibliography`, for `--upstream-cite` resolution. */
  readonly bibkeys: ReadonlySet<string>;
}

/** Guidance appended to every provenance refusal — this is the part that was missing. */
const WHERE_TO_LOOK =
  "Check the source environment's OPTIONAL ARGUMENT (e.g. `\\begin{lemma}[{\\citealt[Lemma C.1]{key}}]`) " +
  "and the sentence introducing it: that is where a paper credits a result it is restating. " +
  "A verbatim match does NOT establish provenance.";

/** Resolve the operator's provenance decision, or throw explaining what is missing.
 * Returns `undefined` when the statement is affirmed original to the cited work. */
export function resolveUpstreamDecision(input: UpstreamDecisionInput): UpstreamSource | undefined {
  const upstream = input.upstream?.trim();
  if (upstream && input.upstreamNone) {
    throw new Error(`--upstream and --upstream-none are contradictory; pass exactly one. ${WHERE_TO_LOOK}`);
  }
  if (!upstream && !input.upstreamNone) {
    throw new Error(
      "refusing attestation: provenance undecided. Pass --upstream <primary citation> if the located " +
        `statement credits an earlier work, or --upstream-none to affirm it originates there. ${WHERE_TO_LOOK}`,
    );
  }
  if (!upstream) {
    // A bibkey/locator only describes a primary; pairing it with "there is no primary"
    // is the same contradiction as --upstream + --upstream-none, and silently dropping
    // it would discard the operator's stated intent (and skip its bibliography check).
    if (input.upstreamCite?.trim() || input.upstreamLocator?.trim()) {
      throw new Error("--upstream-cite/--upstream-locator describe a primary source; they cannot accompany --upstream-none.");
    }
    const markers = detectUpstreamMarkers(input.verbatim);
    if (markers.length > 0 && !input.acknowledgeMarker?.trim()) {
      throw new Error(
        `--upstream-none contradicts the source text, which credits an earlier work (${markers.join(", ")}). ` +
          "Pass --upstream <primary citation> if it is genuinely borrowed. If the marker is a false " +
          "positive, pass --acknowledge-marker <why> to record that judgement — do NOT invent a " +
          `citation to satisfy this check. ${WHERE_TO_LOOK}`,
      );
    }
    return undefined;
  }
  const cite = input.upstreamCite?.trim();
  if (cite && !input.bibkeys.has(cite)) {
    throw new Error(`--upstream-cite ${cite} does not resolve in the core bibliography`);
  }
  const locator = input.upstreamLocator?.trim();
  return { citation: upstream, ...(locator ? { locator } : {}), ...(cite ? { cite } : {}) };
}
