import { describe, expect, it } from "vitest";
import { parseLemmaProofBatch, insertLemmaProofs, insertProofPointers } from "../src/presentation/stages/p2_draft.js";

// obj_ids are graph NODE ids and contain ':' (e.g. prop:overlap-envelope) — the marker/env regexes
// must handle the colon, or the whole lemma-proof batch fails to parse (real P2 incident 2026-06-25).
const proofA = "\\begin{proof}[Proof of Lemma~\\ref{obj:lem:witness-membership}]\nStep. % lean: witness_membership\n\\end{proof}";
const proofB = "\\begin{proof}[Proof of Lemma~\\ref{obj:prop:overlap-envelope}]\nOther. % lean: overlap_envelope\n\\end{proof}";

describe("parseLemmaProofBatch", () => {
  it("splits delimited batch output into per-lemma proofs (colon-bearing obj_ids)", () => {
    const stdout = `%% PROOF lem:witness-membership\n${proofA}\n\n%% PROOF prop:overlap-envelope\n${proofB}\n`;
    const m = parseLemmaProofBatch(stdout, ["lem:witness-membership", "prop:overlap-envelope"]);
    expect(m.get("lem:witness-membership")).toBe(proofA);
    expect(m.get("prop:overlap-envelope")).toBe(proofB);
  });

  it("tolerates chatter around markers and keeps UNCLEAR verdicts", () => {
    const stdout = `noise\n%% PROOF lem:witness-membership\n${proofA}\n%% PROOF prop:overlap-envelope\nUNCLEAR: route not visible\n`;
    const m = parseLemmaProofBatch(stdout, ["lem:witness-membership", "prop:overlap-envelope"]);
    expect(m.get("lem:witness-membership")).toBe(proofA);
    expect(m.get("prop:overlap-envelope")).toMatch(/^UNCLEAR:/);
  });

  it("throws when an expected lemma is missing", () => {
    expect(() => parseLemmaProofBatch(`%% PROOF lem:witness-membership\n${proofA}`, ["lem:witness-membership", "lem:two-point-divergence"])).toThrow(/lem:two-point-divergence/);
  });
});

describe("insertLemmaProofs", () => {
  const tex = [
    "intro prose",
    "\\begin{lemmav}{lem:witness-membership}[Title]\nbody\n\\end{lemmav}",
    "remark prose",
    "\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}",
    "tail",
  ].join("\n\n");

  it("inserts each proof directly after its lemma env, leaving others alone", () => {
    const out = insertLemmaProofs(tex, new Map([["lem:witness-membership", proofA]]));
    expect(out).toContain(`\\end{lemmav}\n\n${proofA}\n\nremark prose`);
    expect(out).toContain("\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}\n\ntail");
    expect(out.match(/\\begin\{proof\}/g)?.length).toBe(1);
  });

  it("is a no-op with no proofs", () => {
    expect(insertLemmaProofs(tex, new Map())).toBe(tex);
  });
});

describe("insertProofPointers", () => {
  const tex = [
    "intro prose",
    "\\begin{lemmav}{lem:witness-membership}[Title]\nbody\n\\end{lemmav}",
    "remark prose",
    "\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}",
    "tail",
  ].join("\n\n");

  it("adds a deferral pointer only after the listed (body) lemmas", () => {
    const out = insertProofPointers(tex, new Set(["lem:witness-membership"]), "sec:deferred-proofs");
    // body lemma gets the pointer to the proofs appendix (clickable section ref, not an obj ref).
    // The pointer is a bare \cref: the manuscript's target-typed reference convention has the
    // TARGET supply its own kind, and tex_anchors' xref lint explicitly rejects a manually
    // chosen kind ("Appendix~\ref{…}" / "Appendix~\cref{…}") as duplicating it.
    expect(out).toContain("\\end{lemmav}\n\nThe proof is deferred to \\cref{sec:deferred-proofs}.");
    // the other lemma (appendix-placed; not in the set) is untouched — no pointer, no proof inline
    expect(out).toContain("\\begin{lemmav}{lem:clip-bias}\nbody9\n\\end{lemmav}\n\ntail");
    expect(out.match(/deferred to \\cref/g)?.length).toBe(1);
    // never a manually chosen kind in front of the ref — that is what the lint flags
    expect(out).not.toMatch(/Appendix~?\\c?ref\{/);
    // the pointer uses a section ref (sec:), never an obj ref — so xref lints don't flag it
    expect(out).not.toContain("\\ref{obj:");
  });

  it("is a no-op when no lemma ids are given", () => {
    expect(insertProofPointers(tex, new Set(), "sec:deferred-proofs")).toBe(tex);
  });
});
