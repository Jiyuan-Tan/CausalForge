import { describe, expect, it } from "vitest";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { frontMatterFromPaper, stageP3 } from "../src/presentation/stages/p3_gates.js";
import { freshPaperState } from "../src/presentation/state.js";
import { hashEnvBody, parseAnchoredEnvs } from "../src/presentation/tex_anchors.js";

const PAPER = String.raw`\documentclass{article}
\begin{document}
\begin{abstract}
The abstract cites \citep{ghost2020}.
\end{abstract}

\section{Introduction}
The introduction cites \citep{ghost2020}.

\section{Results}
Results.
\end{document}`;

const FROZEN_ENV = String.raw`\begin{theoremv}{thm:foo}
Formal claim.
\end{theoremv}`;

const formalLayer = (withFrozen = false) => JSON.stringify({
  commit: "test",
  blocks: withFrozen ? [{
    obj_id: "thm:foo",
    alias: null,
    kind: "theorem",
    env: "theoremv",
    title: null,
    body: "Formal claim.",
    ref_set: [],
    lean: null,
    status: "matched",
    provenance: "test",
    cited_dependencies: [],
    body_hash: hashEnvBody("Formal claim."),
  }] : [],
});

async function writeFixture(dir: string, paper: string, front: string, withFrozen = false): Promise<void> {
  await Promise.all([
    writeFile(join(dir, "paper.tex"), paper, "utf8"),
    writeFile(join(dir, "front_matter.tex"), front, "utf8"),
    writeFile(join(dir, "outline.md"), "# Notation\n\n# Sections\n", "utf8"),
    writeFile(join(dir, "formal_layer.tex"), withFrozen ? FROZEN_ENV : "", "utf8"),
    writeFile(join(dir, "formal_layer.json"), formalLayer(withFrozen), "utf8"),
    writeFile(join(dir, "related_work_brief.md"), "Literature summary.\n", "utf8"),
    writeFile(join(dir, "references.bib"), "@article{keep2021, title = {Kept}, author = {Author}, year = {2021}}\n", "utf8"),
  ]);
}

const ioFor = (dir: string, runCodex: (arg: { prompt: string }) => Promise<{ stdout: string; stderr: string }>) => ({
  ctx: {
    repoRoot: dir,
    qid: "q_front_sync",
    spec: "v1",
    deps: {
      dryRun: false,
      runClaude: async () => JSON.stringify({ scores: { rigor: 7 } }),
      runCodex,
    },
  },
  state: freshPaperState("q_front_sync", "v1"),
  bank: {} as never,
  outDir: dir,
}) as never;

const cleanCodex = async ({ prompt }: { prompt: string }) => {
  if (prompt.includes("p3_overclaim")) return { stdout: JSON.stringify({ clean: true, flags: [] }), stderr: "" };
  if (prompt.includes("p3_citation_support")) return { stdout: JSON.stringify({ verdict: "supported" }), stderr: "" };
  return { stdout: JSON.stringify({ scores: { rigor: 7 } }), stderr: "" };
};

describe("P3 front-matter cache synchronization", () => {
  it("preserves bytes between the abstract and Introduction in the cache extract", () => {
    const keyworded = PAPER.replace(
      "\u005c\end{abstract}\n\n\u005csection{Introduction}",
      "\u005c\end{abstract}\n\u005cnoindent\u005ctextit{Keywords: minimax, overlap.}\n\n\u005csection{Introduction}",
    );
    const front = frontMatterFromPaper(keyworded);
    expect(front).toContain("\u005cnoindent\u005ctextit{Keywords: minimax, overlap.}");
    expect(front).toContain("\u005csection{Introduction}");
    expect(front).not.toContain("\u005csection{Results}");
  });

  it("refuses to guess when the first post-abstract section is not Introduction", () => {
    const renamed = PAPER.replace("\\section{Introduction}", "\\section{Background}");
    expect(frontMatterFromPaper(renamed)).toBeNull();
    const envFreeFallback = PAPER.replace("\\section{Introduction}", "\\section{Setup}");
    expect(frontMatterFromPaper(envFreeFallback)).toBeNull();
  });

  it("writes revised front matter as a normalized, prose-only cache artifact", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-front-sync-"));
    try {
      await writeFixture(dir, PAPER, "STALE P2 FRONT MATTER\n");
      const io = ioFor(dir, async ({ prompt }) => {
        if (prompt.includes("p3_revision_patch")) {
          return {
            stdout: JSON.stringify({ replacements: [{
              before: "The abstract cites \\citep{ghost2020}.",
              after: "The abstract cites \\citep{keep2021}.",
            }, {
              before: "The introduction cites \\citep{ghost2020}.",
              after: "The introduction cites \\citep{keep2021}.",
            }] }),
            stderr: "",
          };
        }
        return cleanCodex({ prompt });
      });

      await stageP3(io);

      const [paper, front] = await Promise.all([
        readFile(join(dir, "paper.tex"), "utf8"),
        readFile(join(dir, "front_matter.tex"), "utf8"),
      ]);
      expect(paper).toContain("\\citep{keep2021}");
      expect(front).toContain("\\begin{abstract}");
      expect(front).toContain("\\section{Introduction}");
      expect(front).not.toContain("\\section{Results}");
      expect(parseAnchoredEnvs(front)).toEqual([]);
      expect(front).toMatch(/[^\n]\n$/);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("heals a stale cache after a round-zero intro obj-ref repair", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-front-ref-repair-"));
    let revisionCalls = 0;
    let rubricPrompt = "";
    const paper = String.raw`\begin{abstract}
Abstract.
\end{abstract}
\section{Introduction}
See \Cref{obj:foo}.
\section{Results}
${FROZEN_ENV}
\end{document}`;
    try {
      await writeFixture(dir, paper, "STALE FRONT\n", true);
      await stageP3(ioFor(dir, async ({ prompt }) => {
        if (prompt.includes("p3_revision_patch")) revisionCalls += 1;
        if (prompt.includes("p3_rubric")) rubricPrompt = prompt;
        return cleanCodex({ prompt });
      }));
      const [repairedPaper, front] = await Promise.all([
        readFile(join(dir, "paper.tex"), "utf8"),
        readFile(join(dir, "front_matter.tex"), "utf8"),
      ]);
      expect(revisionCalls).toBe(0);
      expect(repairedPaper).toContain("\\Cref{obj:thm:foo}");
      expect(front).toContain("\\Cref{obj:thm:foo}");
      expect(front).not.toContain("\\section{Results}");
      expect(parseAnchoredEnvs(front)).toEqual([]);
      // The repair is on disk before the rubric reads paper.tex; otherwise its
      // prompt would score the stale obj reference while the repaired text ships.
      expect(rubricPrompt).toContain("\\Cref{obj:thm:foo}");
      expect(rubricPrompt).not.toContain("\\Cref{obj:foo}");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("heals an existing stale cache when every hard gate passes in round zero", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-front-round-zero-"));
    let revisionCalls = 0;
    const paper = String.raw`\begin{abstract}
Abstract.
\end{abstract}
\section{Introduction}
Introduction.
\section{Results}
Results.
\end{document}`;
    try {
      await writeFixture(dir, paper, "STALE FRONT\n");
      await stageP3(ioFor(dir, async ({ prompt }) => {
        if (prompt.includes("p3_revision_patch")) revisionCalls += 1;
        return cleanCodex({ prompt });
      }));
      const front = await readFile(join(dir, "front_matter.tex"), "utf8");
      expect(revisionCalls).toBe(0);
      expect(front).toContain("\\section{Introduction}");
      expect(front).not.toContain("STALE FRONT");
      expect(front).not.toContain("\\section{Results}");
      expect(parseAnchoredEnvs(front)).toEqual([]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("syncs a successful revision before a later hard-gate failure can skip round-zero healing", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-front-revision-write-"));
    const paper = String.raw`\begin{abstract}
Abstract cites \citep{ghost2020}.
\end{abstract}
\section{Introduction}
Introduction cites \citep{ghost2020}.
\section{Results}
Results still cite \citep{ghost2020}.
\end{document}`;
    try {
      await writeFixture(dir, paper, "STALE FRONT\n");
      await expect(stageP3(ioFor(dir, async ({ prompt }) => {
        if (prompt.includes("p3_revision_patch")) {
          return {
            stdout: JSON.stringify({ replacements: [{
              before: "Abstract cites \\citep{ghost2020}.",
              after: "Abstract cites \\citep{keep2021}.",
            }, {
              before: "Introduction cites \\citep{ghost2020}.",
              after: "Introduction cites \\citep{keep2021}.",
            }] }),
            stderr: "",
          };
        }
        return cleanCodex({ prompt });
      }))).rejects.toThrow(/patch replacement is missing or non-unique/);
      const front = await readFile(join(dir, "front_matter.tex"), "utf8");
      expect(front).toContain("\\citep{keep2021}");
      expect(front).not.toContain("STALE FRONT");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("persists state before rejecting a revision that removes the Introduction heading", async () => {
    const dir = await mkdtemp(join(tmpdir(), "psmith-p3-front-overcapture-"));
    const paper = String.raw`\begin{abstract}
Abstract cites \citep{ghost2020}.
\end{abstract}
\section{Introduction}
Introduction cites \citep{ghost2020}.
\section{Results}
${FROZEN_ENV}
\end{document}`;
    try {
      await writeFixture(dir, paper, "STALE FRONT\n", true);
      await expect(stageP3(ioFor(dir, async ({ prompt }) => {
        if (prompt.includes("p3_revision_patch")) {
          return {
            stdout: JSON.stringify({ replacements: [{
              before: "Abstract cites \\citep{ghost2020}.",
              after: "Abstract cites \\citep{keep2021}.",
            }, {
              before: "Introduction cites \\citep{ghost2020}.",
              after: "Introduction cites \\citep{keep2021}.",
            }, {
              before: "\\section{Results}\n",
              after: "",
            }] }),
            stderr: "",
          };
        }
        return cleanCodex({ prompt });
      }))).rejects.toThrow(/reviser deleted or renamed the required .*Introduction/);
      expect(await readFile(join(dir, "paper.tex"), "utf8")).toBe(paper);
      expect(await readFile(join(dir, "front_matter.tex"), "utf8")).toBe("STALE FRONT\n");
      const persisted = await readFile(join(dir, "q_front_sync_v1_paper_state.json"), "utf8");
      expect(JSON.parse(persisted).revision_round).toBe(0);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
