import { describe, it, expect, afterAll } from "vitest";
import { readFile, rm, mkdtemp } from "node:fs/promises";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { runPaperPipeline, type PaperDeps } from "../src/presentation/pipeline.js";
import { parseAnchoredEnvs, lintAnchors, type AnchoredEnv } from "../src/presentation/tex_anchors.js";
import { FormalLayerSource } from "../src/presentation/formal_layer.js";
import { parseNotationReviewerOutput } from "../src/presentation/stages/p1_plan.js";
import { acceptedBankEntry, causalSmithRoot } from "./helpers.js";
import { MODELS } from "../src/models.js";

// Run against whatever paper is currently banked (the pipeline reads its graph + Lean; the models
// are stubbed). Tracks bank re-curation instead of a hardcoded qid.
const { qid: QID, spec: SPEC } = acceptedBankEntry();

const BIB = `@article{robins1994,
  title = {Estimation of Regression Coefficients When Some Regressors Are Not Always Observed},
  author = {Robins, James M. and Rotnitzky, Andrea and Zhao, Lue Ping},
  journal = {Journal of the American Statistical Association}, year = {1994},
  doi = {10.1080/01621459.1994.10476818}
}`;

const renderEnv = (e: AnchoredEnv) =>
  `\\begin{${e.env}}{${e.obj_id}}${e.title !== null ? `[${e.title}]` : ""}\n${e.body.trim()}\n\\end{${e.env}}`;

// The P1 outline is now a codex (executor) call; build it from the mechanical
// layer's node-id envs in the prompt.
const stubOutline = (prompt: string): string => {
  const envs = parseAnchoredEnvs(prompt);
  const by = (k: AnchoredEnv["env"][]) =>
    envs.filter((e) => k.includes(e.env)).map((e) => e.obj_id).join(", ");
  return [
    "# Title",
    "Stub Paper Title",
    "# Notation",
    "| `τ` | tau | the ATE |",
    "# Sections",
    "## section: Introduction",
    "intro brief",
    "objs: none",
    "bib: robins1994",
    "## section: Setup and assumptions",
    "setup brief",
    `objs: ${by(["assumptionv", "definitionv"])}`,
    "bib: robins1994",
    "## section: Main results",
    "results brief",
    `objs: ${by(["theoremv"])}`,
    "bib: robins1994",
    "## section: Auxiliary lemmas",
    "lemma brief",
    `objs: ${by(["lemmav"])}`,
    "bib: robins1994",
  ].join("\n");
};

const STUB_BODY = "Touched statement body.";
let outlineAttempts = 0;
let batchOmissionExercised = false;
let omittedBatchId = "";
let singleRecoveryCalls = 0;
let p0Model = "";
let p0Effort = "";

// The P1 loop's cross-reference gate requires each statement to \cref every dependency in its ref_set,
// and the hypothesis-presentation gate requires a theorem/lemma with ≥4 hypotheses to itemize them.
// A real render writes both; the stub must too, or the loop never converges. So the stub emits one
// \item per ref_set dependency (a target-typed \cref) — satisfying both gates uniformly.
const parseRefs = (csv: string): string[] =>
  csv.split(",").map((s) => s.trim()).filter((s) => s && s !== "(none)");
const stubEnv = (id: string, refIds: string[]): string => {
  const items = refIds.length
    ? `\n\\begin{itemize}\n${refIds.map((r) => `\\item \\cref{obj:${r}}`).join("\n")}\n\\end{itemize}`
    : "";
  return `@@@ENV ${id}@@@\nTITLE: Stub Title\n@@@BODY@@@\n${STUB_BODY}${items}\n@@@END@@@`;
};

const deps: PaperDeps = {
  // P0–P2 drive every model call through codex; runClaude (the P3 rubric ensemble) is never reached.
  runClaude: async () => "STUB",
  runCodex: async ({ prompt, model, reasoningEffort }) => {
    // P0 literature pool (now codex via hosted web_search).
    if (prompt.includes("verified citation pool")) {
      p0Model = model ?? "";
      p0Effort = reasoningEffort ?? "";
      return {
        stdout: "```bibtex\n" + BIB + "\n```\n```markdown\nRelated-work brief stub.\n```\n",
        stderr: "",
      };
    }
    // P1 outline (executor / codex).
    if (prompt.includes("outline.md")) {
      outlineAttempts += 1;
      const outline = stubOutline(prompt);
      // Exercise the bounded repair path: the first draft violates the verified-pool
      // contract, while the replacement prompted with validator feedback is clean.
      return {
        stdout: outlineAttempts === 1 ? outline.replace("bib: robins1994", "bib: dropped2006") : outline,
        stderr: "",
      };
    }
    // P1 Lean-aware render: one theorem/lemma statement from its Lean signature (same @@@ENV envelope).
    if (prompt.includes("Render ONE theorem/lemma statement")) {
      const id = prompt.match(/^Object:\s*(\S+)\s+\(kind:/m)?.[1] ?? "unknown";
      const refs = parseRefs(prompt.match(/Dependencies you may[^\n]*\n([^\n]*)/)?.[1] ?? "");
      return { stdout: stubEnv(id, refs), stderr: "" };
    }
    // P1 touch-up render (delimiter format): STUB_BODY + the env's ref_set refs, per ### <id> block.
    if (prompt.includes("Render each formal environment")) {
      const blocks = prompt.split(/^### /m).slice(1);
      let out = blocks.map((blk) => {
        const id = blk.split(/\n/)[0].trim();
        const refs = parseRefs(blk.match(/ref_set:\s*(.+)/)?.[1] ?? "");
        return stubEnv(id, refs);
      });
      if (blocks.length > 1 && !batchOmissionExercised) {
        batchOmissionExercised = true;
        omittedBatchId = blocks[0].split(/\n/)[0].trim();
        out = out.slice(1);
      } else if (blocks.length === 1 && blocks[0].split(/\n/)[0].trim() === omittedBatchId) {
        singleRecoveryCalls += 1;
      }
      return { stdout: out.join("\n\n"), stderr: "" };
    }
    // P1 notation-resolvability review (now codex) → clean.
    if (prompt.includes("NOTATION-RESOLVABILITY")) {
      return { stdout: JSON.stringify({ problems: [] }), stderr: "" };
    }
    // P1 statement equivalence audit (runStatementAudit). Batch: faithful for each `--- <id> ---`.
    if (prompt.includes("statement-faithfulness auditor")) {
      if (prompt.includes("For EACH statement below")) {
        const ids = [...prompt.matchAll(/^--- (\S+) ---$/gm)].map((m) => m[1]);
        return { stdout: JSON.stringify({ results: ids.map((id) => ({ obj_id: id, verdict: "faithful" })) }), stderr: "" };
      }
      return { stdout: JSON.stringify({ verdict: "faithful" }), stderr: "" };
    }
    // P2 proof equivalence audit (runProofAudit) → faithful.
    if (prompt.includes("auditing whether a prose appendix proof faithfully renders")) {
      return { stdout: JSON.stringify({ verdict: "faithful" }), stderr: "" };
    }
    // P2 body section (now codex).
    if (prompt.includes("Write ONE section")) {
      const envs = parseAnchoredEnvs(prompt);
      return {
        stdout: "\\section{Stub Section}\nProse stub.\n\n" + envs.map(renderEnv).join("\n\n"),
        stderr: "",
      };
    }
    // P2 intro + abstract (now codex).
    if (prompt.includes("abstract and introduction")) {
      return {
        stdout:
          "\\begin{abstract}\nStub abstract.\n\\end{abstract}\n\\section{Introduction}\nStub intro \\citep{robins1994}.",
        stderr: "",
      };
    }
    // batched lemma-proof render: one marker + proof per requested obj_id
    const ids = [...prompt.matchAll(/obj_id ([\w:-]+)\n/g)].map((m) => m[1]); // ids may contain ':'
    if (prompt.includes("%% PROOF <obj_id>") && ids.length > 0) {
      return {
        stdout: ids
          .map((id) => `%% PROOF ${id}\n\\begin{proof}[Proof of \\cref{obj:${id}}]\nStep. % lean: stub\n\\end{proof}`)
          .join("\n"),
        stderr: "",
      };
    }
    return {
      stdout: "chatter\n\\begin{proof}[Proof]\nStep 1. % lean: t_thm\n\\end{proof}\nmore chatter",
      stderr: "",
    };
  },
  lookup: async (e) =>
    e.key === "robins1994"
      ? {
          title:
            "Estimation of regression coefficients when some regressors are not always observed",
          authorFamily: "Robins",
          year: 1994,
        }
      : null,
  dryRun: false,
};

describe("stages P0-P2 against the real bank entry (stubbed models)", () => {
  const root = causalSmithRoot();
  // NEVER the real presentationDir: a test run must not clobber live artifacts.
  const dirP = mkdtemp(join(tmpdir(), "causalsmith-p0p2-"));
  afterAll(async () => rm(await dirP, { recursive: true, force: true }));

  it("P0+P1 produce pool, outline, frozen layer; halts at outline checkpoint", async () => {
    const dir = await dirP;
    const r = await runPaperPipeline({ repoRoot: root, qid: QID, spec: SPEC, deps, outDir: dir });
    expect(r.halt).toBe("checkpoint:outline");
    expect(p0Model).toBe(MODELS.codexPresentation);
    expect(p0Effort).toBe("high");
    expect(outlineAttempts).toBe(2);
    expect(batchOmissionExercised).toBe(true);
    expect(singleRecoveryCalls).toBe(1);
    const bib = await readFile(join(dir, "references.bib"), "utf8");
    expect(bib).toContain("robins1994");
    const layer = await readFile(join(dir, "formal_layer.tex"), "utf8");
    const envs = parseAnchoredEnvs(layer);
    expect(envs.length).toBeGreaterThan(20);
    // Every env has a non-empty body. (Loose nodes carry the stub render's "Touched statement body.";
    // nodes the bank locked with a P3-validated `nl.frozen_body` are used verbatim, so the body text
    // varies — assert non-emptiness rather than a fixed string.)
    expect(envs.every((e) => e.body.trim().length > 0)).toBe(true);
    const looseEnvs = envs.filter((e) => e.body.includes("Touched statement body."));
    expect(looseEnvs.length).toBeGreaterThan(0);
    // The freeze lives in the JSON formal layer (each env block's body_hash), not a frozen_hashes.json.
    const layerSrc = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    expect(layerSrc.blocks.filter((b) => b.env).length).toBe(envs.length);
  });

  it("P2 assembles a lint-clean paper.tex and halts at draft checkpoint", async () => {
    const dir = await dirP;
    const r = await runPaperPipeline({
      repoRoot: root,
      qid: QID,
      spec: SPEC,
      deps,
      resume: true,
      outDir: dir,
    });
    expect(r.halt).toBe("checkpoint:draft");
    const paper = await readFile(join(dir, "paper.tex"), "utf8");
    expect(paper).toContain("\\begin{abstract}");
    expect(paper).toContain("\\appendix");
    expect(paper).toContain("\\begin{proof}");
    // Frozen hashes come from the JSON formal layer (per-block body_hash), keyed by env obj_id.
    const layerSrc = FormalLayerSource.parse(JSON.parse(await readFile(join(dir, "formal_layer.json"), "utf8")));
    const frozen = new Map<string, string>(
      layerSrc.blocks.filter((b) => b.env).map((b) => [b.obj_id, b.body_hash]),
    );
    const known = new Set(
      parseAnchoredEnvs(await readFile(join(dir, "formal_layer.tex"), "utf8")).map((e) => e.obj_id),
    );
    expect(lintAnchors(paper, known, frozen)).toEqual([]);
  });
});

describe("parseNotationReviewerOutput (P1 reviewer JSON boundary)", () => {
  it("returns problems array when present", () => {
    expect(parseNotationReviewerOutput('{"problems":[{"symbol":"G_n","case":"undefined"}]}'))
      .toEqual([{ symbol: "G_n", case: "undefined" }]);
  });
  it("accepts an explicit clean verdict without problems", () => {
    expect(parseNotationReviewerOutput('{"clean": true}')).toEqual([]);
    expect(parseNotationReviewerOutput('{"problems": []}')).toEqual([]);
  });
  it("throws on non-JSON output instead of passing as clean", () => {
    expect(() => parseNotationReviewerOutput("I could not review this layer."))
      .toThrow(/notation reviewer/);
  });
  it("throws when neither clean:true nor a problems array is present", () => {
    expect(() => parseNotationReviewerOutput('{"clean": false}')).toThrow(/notation reviewer/);
  });
});
