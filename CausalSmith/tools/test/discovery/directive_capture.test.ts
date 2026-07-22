// Directive-capture sanitizer contracts.
//
// A directive is the single highest-leverage string in the D phase: it is re-sent to
// every solve unit of the next round. The round-36 incident on
// stat_pn_weak_event_honest_inference wrote a 229-line directive of which 44 lines
// (19%) were the literal string `null` — the signature of
// `codex exec --json | jq -r '.msg.text'` over events that carry no `.msg.text` —
// with the actual instruction buried after the noise.

import { describe, expect, it } from "vitest";
import { DirectiveCaptureError, sanitizeDirectiveText } from "../../src/shared/directive_text.js";

describe("sanitizeDirectiveText", () => {
  // A handful of stray artifact lines around otherwise-good prose: clean it and keep going.
  const prose = (n: number) => Array.from({ length: n }, (_, i) => `Directive step ${i + 1}.`);

  it("strips the literal null lines a broken jq pipe emits, keeping the prose", () => {
    const raw = ["null", ...prose(9), "null"].join("\n");
    const { text, droppedArtifactLines, totalLines } = sanitizeDirectiveText(raw);
    expect(droppedArtifactLines).toBe(2);
    expect(totalLines).toBe(11);
    expect(text).toBe(prose(9).join("\n"));
  });

  it("collapses the blank runs left behind so the result reads as authored prose", () => {
    const raw = [...prose(5), "null", "null", "null", ...prose(5)].join("\n");
    const text = sanitizeDirectiveText(raw).text;
    expect(text).not.toMatch(/\n{3,}/);
    expect(text).toBe([...prose(5), ...prose(5)].join("\n"));
  });

  it("refuses a capture that is mostly artifact lines", () => {
    // Above the ratio the surviving prose is likely truncated/interleaved too, so
    // cleaning it would hand the solver a confidently-wrong instruction.
    const raw = [...Array(8).fill("null"), "Split the base class.", "Do not require Holder m_1."].join("\n");
    expect(() => sanitizeDirectiveText(raw)).toThrow(DirectiveCaptureError);
    expect(() => sanitizeDirectiveText(raw)).toThrow(/80% literal null/);
  });

  it("names the repair recipe in every refusal", () => {
    const raw = [...Array(8).fill("null"), "prose", "more prose"].join("\n");
    expect(() => sanitizeDirectiveText(raw)).toThrow(/agent_message/);
  });

  it("refuses a raw codex event stream piped in whole", () => {
    const raw = [
      JSON.stringify({ msg: { type: "agent_reasoning", text: "thinking" } }),
      JSON.stringify({ msg: { type: "agent_message", message: "the real directive" } }),
    ].join("\n");
    expect(() => sanitizeDirectiveText(raw)).toThrow(/raw JSON event stream/);
  });

  it("refuses an empty or all-artifact directive", () => {
    expect(() => sanitizeDirectiveText("   ")).toThrow(/empty directive/);
    expect(() => sanitizeDirectiveText("null\nnull\nnull")).toThrow(DirectiveCaptureError);
  });

  it("leaves clean authored prose untouched", () => {
    // Round 36 row 1 was clean; sanitizing must be a no-op on it, including on prose
    // that legitimately contains the word null inside a sentence.
    const raw = "PASS-RETRY\n\nCanonical owner: solve_thm_gaussian_frontier.json.\nThe null hypothesis is unchanged.";
    const { text, droppedArtifactLines } = sanitizeDirectiveText(raw);
    expect(text).toBe(raw);
    expect(droppedArtifactLines).toBe(0);
  });

  it("--allow-dirty-capture writes the text verbatim", () => {
    const raw = [...Array(8).fill("null"), "prose"].join("\n");
    expect(sanitizeDirectiveText(raw, true).text).toBe(raw);
  });
});
