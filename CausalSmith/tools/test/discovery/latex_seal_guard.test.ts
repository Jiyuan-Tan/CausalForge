import { describe, it, expect } from "vitest";
import { assertSealableLatexPayload } from "../../src/discovery/core/latex_serialization.js";

describe("assertSealableLatexPayload", () => {
  it("accepts canonical balanced LaTeX payloads", () => {
    expect(() => assertSealableLatexPayload({
      kind: "definition-replace",
      id: "def:poly-class",
      construction: "The class \\(\\mathcal P_{T,\\beta}(C)=\\{Y:\\|Y\\|\\le B\\}\\).",
      reason: "repair delimiters",
    }, "test payload")).not.toThrow();
  });

  it("accepts a legitimate row break directly before a parenthesis inside proved TeX", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\begin{cases}a\\\\(b+1)&\\text{else}\\end{cases}",
    }, "test payload")).not.toThrow();
  });

  it("rejects a payload with an unclosed inline-math delimiter, naming the field", () => {
    expect(() => assertSealableLatexPayload({
      construction: "for all \\(x\\in\\mathcal X the map is linear.",
    }, "test payload")).toThrow(/construction.*inline-math|inline-math.*construction/s);
  });

  it("rejects a payload with an unclosed display-math delimiter", () => {
    expect(() => assertSealableLatexPayload({
      statement: "We have \\[\\int f\\,d\\mu = 0 and the rest is prose.",
    }, "test payload")).toThrow(/display-math/);
  });

  it("rejects a fully over-escaped payload (doubled delimiters, no canonical single backslash)", () => {
    expect(() => assertSealableLatexPayload({
      construction: "the set \\\\(\\\\{Y: \\\\|Y\\\\|\\\\le B\\\\}\\\\).",
    }, "test payload")).toThrow(/over-escaped/);
  });

  it("rejects a fully over-escaped display-math payload", () => {
    expect(() => assertSealableLatexPayload({
      construction: "the bound \\\\[\\\\|Y\\\\|\\\\le B\\\\] holds.",
    }, "test payload")).toThrow(/over-escaped/);
  });

  it("rejects a close delimiter appearing before any open", () => {
    expect(() => assertSealableLatexPayload({
      construction: "broken \\)x^2\\( tail",
    }, "test payload")).toThrow(/close.*before.*open|before any open/i);
  });

  it("rejects an unmatched math environment", () => {
    expect(() => assertSealableLatexPayload({
      statement: "We have \\begin{equation}\\tau = 0 and then prose continues.",
    }, "test payload")).toThrow(/environment/);
  });

  it("rejects crossed begin/end environments even when per-name counts balance", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\begin{aligned}a\\begin{cases}b\\end{aligned}c\\end{cases}",
    }, "test payload")).toThrow(/environment/);
  });

  it("rejects an end-before-begin environment sequence with balanced counts", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "x\\end{aligned}y\\begin{aligned}z",
    }, "test payload")).toThrow(/environment/);
  });

  it("accepts matched nested environments", () => {
    expect(() => assertSealableLatexPayload({
      proof_tex: "\\[\\begin{aligned}a &= b \\\\\n c &= d\\end{aligned}\\] and \\begin{cases}1\\\\2\\end{cases}",
    }, "test payload")).not.toThrow();
  });

  it("rejects decoded control characters via the shared boundary check", () => {
    expect(() => assertSealableLatexPayload({
      construction: "a\theta-smooth class",
    }, "test payload")).toThrow(/control character/);
  });
});
