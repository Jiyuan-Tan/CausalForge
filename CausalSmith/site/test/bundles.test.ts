import { describe, it, expect, vi } from "vitest";
import { mkdtemp, cp, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { loadBundle, loadBundles, verifiedBadge } from "../src/lib/bundles.js";
import { findBlockInner, blockDigest } from "../src/lib/nlLinks.js";

const FIXTURE = resolve(import.meta.dirname, "..", "fixtures", "demo_paper_v1");

describe("bundle loader", () => {
  it("loads the demo fixture and computes the badge", async () => {
    const b = await loadBundle(FIXTURE, "demo_paper_v1");
    expect(b.meta.title).toContain("Demonstration");
    expect(b.entries).toHaveLength(2);
    expect(b.snippets["T-1"].statement).toContain("theorem t1_thm");
    expect(verifiedBadge(b)).toContain("1 theorem");
    expect(verifiedBadge(b)).toContain("machine-verified");
    expect(b.formalLayer).toBeNull(); // optional artifact absent on the bare fixture
    expect(b.paperGraph).toBeNull(); // ditto: an older bundle simply has no Proof map
  });

  /** A bundle dir with the demo fixture plus a written-in `paper_graph.json`. */
  const withGraph = async (id: string, graph: unknown) => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, id);
    await cp(FIXTURE, dir, { recursive: true });
    await writeFile(
      join(dir, "paper_library_index.json"),
      JSON.stringify({ commit: "demo", modules: {}, entries: [{ name: "t1_thm" }] }),
    );
    await writeFile(
      join(dir, "paper_graph.json"),
      typeof graph === "string" ? graph : JSON.stringify(graph),
    );
    return { root, dir };
  };
  /** The demo fixture plus a written-in `nl_links.json`. */
  const withLinks = async (id: string, artifact: unknown) => {
    const root = await mkdtemp(join(tmpdir(), "site-nllinks-"));
    const dir = join(root, id);
    await cp(FIXTURE, dir, { recursive: true });
    await writeFile(
      join(dir, "nl_links.json"),
      typeof artifact === "string" ? artifact : JSON.stringify(artifact),
    );
    return { root, dir };
  };

  /** Everything a v3 artifact needs to bind to the demo fixture. */
  const BOUND = { commit: "e591f16demo", policy: "nl-links-v3", qid: "demo_paper", spec: "v1" };

  /** T-1's block inner HTML — what the pipeline measures offsets against. */
  const innerOfT1 = async () => {
    const body = await readFile(join(FIXTURE, "paper_body.html"), "utf8");
    const range = findBlockInner(body, "T-1")!;
    return body.slice(range.start, range.end);
  };

  /** Segment offsets into T-1's block, computed the way the pipeline would —
   *  `openPath` included, since pandoc wraps every sentence in a `<p>`. */
  const segAt = async (start: number, end: number, id: string) => {
    const inner = await innerOfT1();
    const stack: string[] = [];
    for (const m of inner.slice(0, start).matchAll(/<(\/?)([a-z][a-z0-9-]*)[^>]*?(\/?)>/gi)) {
      const [, closing, name, selfClose] = m;
      if (selfClose || /^(br|img|hr|input|wbr)$/i.test(name)) continue;
      if (closing) {
        const i = stack.lastIndexOf(name.toLowerCase());
        if (i >= 0) stack.splice(i, 1);
      } else stack.push(name.toLowerCase());
    }
    return { id, kind: "text" as const, start, end, openPath: stack };
  };

  const segIn = async (text: string, id: string) => {
    const inner = await innerOfT1();
    const start = inner.indexOf(text);
    expect(start, `fixture prose: ${text}`).toBeGreaterThanOrEqual(0);
    return segAt(start, start + text.length, id);
  };

  /** Fills the gaps so the named segments TILE T-1's block, as the producer does. */
  const tiled = async (named: Awaited<ReturnType<typeof segIn>>[]) => {
    const inner = await innerOfT1();
    const sorted = [...named].sort((a, b) => a.start - b.start);
    const out: typeof sorted = [];
    let cursor = 0;
    let n = 0;
    const filler = async (start: number, end: number) => {
      if (end > start) out.push(await segAt(start, end, `_f${n++}`));
    };
    for (const seg of sorted) {
      await filler(cursor, seg.start);
      out.push(seg);
      cursor = seg.end;
    }
    await filler(cursor, inner.length);
    return out;
  };

  it("wraps the artifact's segments and tokens the rows they state", async () => {
    const s1 = await segIn("the clipped estimator", "s1");
    const s2 = await segIn("Under Assumption 1", "s2");
    const { root, dir } = await withLinks("links_v3", {
      ...BOUND,
      blocks: {
        "T-1": {
          digest: blockDigest(await innerOfT1()),
          byteLength: (await innerOfT1()).length,
          structured: {
            sharedHyps: [
              { chip: "hyp", code: "(H1 : ObsLaw S)", id: "h1" },
              { chip: "decl", code: "(S : Setup)", id: "h2" },
            ],
            conclusions: [{ hyps: [], code: "risk S estClipped ≤ S.C", id: "c1" }],
          },
          segments: await tiled([s1, s2]),
          assignments: [
            { row: "c1", segments: ["s1"] },
            { row: "h1", segments: ["s2"] },
            { row: "h2", unstated: true },
          ],
          displayLinks: [],
        },
      },
    });
    const b = await loadBundle(dir, "links_v3");
    expect(b.bodyHtml).toContain('<span data-xl="T-1#c1">the clipped estimator</span>');
    expect(b.bodyHtml).toContain('<span data-xl="T-1#h1">Under Assumption 1</span>');
    const s = b.snippets["T-1"].structured!;
    // The artifact's rows, adopted verbatim, each carrying its own token.
    expect(s.conclusions[0].code).toBe("risk S estClipped ≤ S.C");
    expect(s.conclusions[0].xl).toBe("T-1#c1");
    expect(s.sharedHyps[0].xl).toBe("T-1#h1");
    expect(s.sharedHyps[1].unstated).toBe(true);
    expect(s.sharedHyps[1].xl).toBeUndefined();
    await rm(root, { recursive: true, force: true });
  });

  it("leaves the body untouched when the artifact is absent or malformed", async () => {
    const plain = await loadBundle(FIXTURE, "demo_paper_v1");
    expect(plain.bodyHtml).not.toContain("data-xl");
    for (const bad of ["{ not json", JSON.stringify({ ...BOUND, blocks: "nope" })]) {
      const { root, dir } = await withLinks("links_bad", bad);
      const b = await loadBundle(dir, "links_bad");
      expect(b.bodyHtml).toBe(plain.bodyHtml);
      await rm(root, { recursive: true, force: true });
    }
  });

  // The artifact's offsets index one particular rendering of one paper body.
  it("ignores an artifact bound to a different commit, and says why", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const plain = await loadBundle(FIXTURE, "demo_paper_v1");
    const { root, dir } = await withLinks("links_other_commit", {
      ...BOUND,
      commit: "someOtherCommit",
      blocks: { "T-1": { digest: "d", byteLength: 0, rowless: true, structured: null, segments: [], assignments: [], displayLinks: [] } },
    });
    const b = await loadBundle(dir, "links_other_commit");
    expect(b.bodyHtml).toBe(plain.bodyHtml);
    expect(warn.mock.calls.flat().join(" ")).toContain("written against commit");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });

  // v1/v2 predate the closed-world contract: their pairs are phrases to search
  // for, not offsets, and applying them would mean guessing again.
  it("ignores an artifact written to an earlier or unknown policy", async () => {
    for (const policy of ["nl-links-v1", "nl-links-v2", "nl-links-v99"]) {
      const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
      const { root, dir } = await withLinks("links_bad_policy", { ...BOUND, policy, blocks: {} });
      const b = await loadBundle(dir, "links_bad_policy");
      expect(b.bodyHtml).not.toContain("data-xl");
      expect(warn.mock.calls.flat().join(" ")).toContain(`policy is "${policy}"`);
      warn.mockRestore();
      await rm(root, { recursive: true, force: true });
    }
  });

  // Bundles share repo commits, so the commit alone cannot identify one.
  it("ignores an artifact belonging to a different paper", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const { root, dir } = await withLinks("links_other_paper", {
      ...BOUND,
      qid: "some_other_paper",
      blocks: {},
    });
    const b = await loadBundle(dir, "links_other_paper");
    expect(b.bodyHtml).not.toContain("data-xl");
    expect(warn.mock.calls.flat().join(" ")).toContain("belongs to a different paper");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });

  // A body rewritten since the artifact was authored moves every offset. The
  // block is dropped whole and the paper renders as it would without links —
  // never with a span sliced into the middle of a tag.
  it("drops a block with stale offsets, with a warning, instead of failing the build", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const { root, dir } = await withLinks("links_stale", {
      ...BOUND,
      blocks: {
        "T-1": {
          digest: blockDigest(await innerOfT1()),
          byteLength: 999999, // the block is not this long; the pre-check fires
          rowless: true,
          structured: null,
          segments: [{ id: "s1", kind: "text", start: 0, end: 999999, openPath: [] }],
          assignments: [],
          displayLinks: [],
        },
      },
    });
    const b = await loadBundle(dir, "links_stale");
    expect(b.bodyHtml).not.toContain("data-xl"); // degraded, not broken
    expect(warn.mock.calls.flat().join(" ")).toContain("bytes, not the");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });

  // The offsets index bytes that are no longer there.
  it("drops a block whose HTML has changed since the artifact was written", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const s1 = await segIn("the clipped estimator", "s1");
    const { root, dir } = await withLinks("links_moved", {
      ...BOUND,
      blocks: {
        "T-1": {
          digest: blockDigest("a body this paper never had"),
          byteLength: (await innerOfT1()).length,
          rowless: true,
          structured: null,
          segments: await tiled([s1]),
          assignments: [],
          displayLinks: [],
        },
      },
    });
    const b = await loadBundle(dir, "links_moved");
    expect(b.bodyHtml).not.toContain("data-xl");
    expect(warn.mock.calls.flat().join(" ")).toContain("block HTML has changed");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });

  // The prose half and the Lean half are built from the same surviving links,
  // so an unresolvable decl leaves NO token behind on the formula.
  it("emits no prose token for a display formula whose decl does not exist", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const DISPLAY = '<span class="math display">\\[y=1\\]</span>';
    const body = await readFile(join(FIXTURE, "paper_body.html"), "utf8");
    // The demo block carries only inline math, so give it a display to link.
    const range = findBlockInner(body, "T-1")!;
    const withDisplay = body.slice(0, range.end) + DISPLAY + body.slice(range.end);
    const inner = withDisplay.slice(range.start, range.end + DISPLAY.length);
    const dStart = inner.indexOf(DISPLAY);

    const { root, dir } = await withLinks("links_ghost_decl", {
      ...BOUND,
      blocks: {
        "T-1": {
          digest: blockDigest(inner),
          byteLength: inner.length,
          rowless: true,
          structured: null,
          segments: [
            { id: "_f0", kind: "text", start: 0, end: dStart, openPath: [] },
            { id: "d1", kind: "display", start: dStart, end: inner.length, openPath: [] },
          ],
          assignments: [],
          displayLinks: [{ segment: "d1", decl: "NoSuchDeclaration" }],
        },
      },
    });
    await writeFile(join(dir, "paper_body.html"), withDisplay);
    const b = await loadBundle(dir, "links_ghost_decl");
    expect(b.bodyHtml).not.toContain("data-xl");
    expect(warn.mock.calls.flat().join(" ")).toContain("nor an upstream reference of it");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });

  // …and the same block with a decl that DOES resolve gets both halves.
  it("emits both halves for a display formula whose decl exists", async () => {
    const DISPLAY = '<span class="math display">\\[y=1\\]</span>';
    const body = await readFile(join(FIXTURE, "paper_body.html"), "utf8");
    const range = findBlockInner(body, "T-1")!;
    const withDisplay = body.slice(0, range.end) + DISPLAY + body.slice(range.end);
    const inner = withDisplay.slice(range.start, range.end + DISPLAY.length);
    const dStart = inner.indexOf(DISPLAY);

    const { root, dir } = await withLinks("links_good_decl", {
      ...BOUND,
      blocks: {
        "T-1": {
          digest: blockDigest(inner),
          byteLength: inner.length,
          rowless: true,
          structured: null,
          segments: [
            { id: "_f0", kind: "text", start: 0, end: dStart, openPath: [] },
            { id: "d1", kind: "display", start: dStart, end: inner.length, openPath: [] },
          ],
          assignments: [],
          displayLinks: [{ segment: "d1", decl: "t1_thm" }],
        },
      },
    });
    await writeFile(join(dir, "paper_body.html"), withDisplay);
    const b = await loadBundle(dir, "links_good_decl");
    expect(b.bodyHtml).toContain('data-xl="T-1#d1"');
    expect(b.bodyHtml).toContain('data-xl-decl="t1_thm"');
    const view = (b.snippets["T-1"].componentViews ?? []).find((v) => v.decl === "t1_thm")!;
    expect(view.xl).toBe("T-1#d1"); // the same token, both sides
    await rm(root, { recursive: true, force: true });
  });

  it("drops a block the artifact wrote in a shape this does not understand", async () => {
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const { root, dir } = await withLinks("links_bad_block", {
      ...BOUND,
      blocks: {
        "T-1": { digest: "d", byteLength: 0, rowless: true, structured: null, segments: [{ id: "s", kind: "sideways", start: 0, end: 1, openPath: [] }], assignments: [], displayLinks: [] },
      },
    });
    const b = await loadBundle(dir, "links_bad_block");
    expect(b.bodyHtml).not.toContain("data-xl");
    expect(warn.mock.calls.flat().join(" ")).toContain("has an unknown kind");
    warn.mockRestore();
    await rm(root, { recursive: true, force: true });
  });


  // These two are the drawer's WARNINGS — a helper proved only up to `sorry`,
  // and a closure cut off at the depth cap. They were once computed and then
  // dropped on the floor in the loader, so the UI could never render them.
  it("carries the closure warnings through into the emitted snippets", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-sorry-"));
    const dir = join(root, "sorry_v1");
    await cp(FIXTURE, dir, { recursive: true });
    // `t1_thm` pulls in `shaky_helper`, whose own proof is a `sorry`.
    await writeFile(
      join(dir, "paper_library_index.json"),
      JSON.stringify({
        commit: "e591f16demo",
        modules: {},
        entries: [
          {
            name: "t1_thm",
            kind: "theorem",
            file: "Demo.lean",
            line: 1,
            source: "theorem t1_thm : shaky_helper = shaky_helper := by simp",
            refs: ["shaky_helper"],
            proofRefs: [],
            usesSorry: false,
          },
          {
            name: "shaky_helper",
            kind: "theorem",
            file: "Demo.lean",
            line: 9,
            source: "theorem shaky_helper : True := by sorry",
            refs: [],
            proofRefs: [],
            usesSorry: true,
          },
        ],
      }),
    );
    const b = await loadBundle(dir, "sorry_v1");
    const views = b.snippets["T-1"].componentViews ?? [];
    expect(views.map((v) => v.decl)).toContain("shaky_helper");
    expect(b.declSources!["shaky_helper"].usesSorry).toBe(true);
    // The trimmed statement cannot show it, so the flag must come from the index.
    expect(b.declSources!["shaky_helper"].statement).not.toContain("sorry");
    expect(b.snippets["T-1"].closureHasSorry).toBe(true);
    // …and it survives into what paper-data.json.ts serialises.
    expect(JSON.parse(JSON.stringify(b.snippets))["T-1"].closureHasSorry).toBe(true);
    await rm(root, { recursive: true, force: true });
  });

  it("loads paper_graph.json when the bundle carries one", async () => {
    const { root, dir } = await withGraph("graph_v1", {
      commit: "demo",
      nodes: [
        { obj_id: "T-1", env: "theoremv", paper_label: "Theorem 1", title: "Upper bound" },
        { obj_id: "P-2", env: "lemmav", paper_label: "Assumption 1", title: null },
      ],
      edges: [{ from: "T-1", to: "P-2", kind: "proof-cites" }],
    });
    const b = await loadBundle(dir, "graph_v1");
    expect(b.paperGraph?.nodes.map((n) => n.obj_id)).toEqual(["T-1", "P-2"]);
    expect(b.paperGraph?.edges).toEqual([{ from: "T-1", to: "P-2", kind: "proof-cites" }]);
    await rm(root, { recursive: true, force: true });
  });

  // The graph is a separate file from the body the reader sees. Read mid-rewrite
  // they disagree, and the map would label a chip with a number the block it
  // jumps to does not carry. The body wins.
  it("reconciles a stale graph against the crosswalk and the body", async () => {
    const { root, dir } = await withGraph("graph_stale", {
      commit: "stale",
      nodes: [
        { obj_id: "T-1", env: "theoremv", paper_label: "Theorem 9", title: "Old title" },
        { obj_id: "ghost", env: "lemmav", paper_label: "Lemma 4", title: "Cut from the paper" },
      ],
      edges: [{ from: "T-1", to: "ghost", kind: "proof-cites" }],
    });
    const b = await loadBundle(dir, "graph_stale");
    // Renumbered from the crosswalk, and the vanished node (with its edge) dropped.
    expect(b.paperGraph?.nodes).toEqual([
      { obj_id: "T-1", env: "theoremv", paper_label: "Theorem 1", title: "Upper bound" },
    ]);
    expect(b.paperGraph?.edges).toEqual([]);
    await rm(root, { recursive: true, force: true });
  });

  // The Proof map is decoration over the paper: a stale or half-written artifact
  // must cost the panel and nothing else — never the page, never the build.
  it("treats a malformed paper_graph.json as absent, not as a build failure", async () => {
    for (const bad of ['{"nodes": "not a list"}', "{not json at all", "[]"]) {
      const { root, dir } = await withGraph("graph_bad", bad);
      const b = await loadBundle(dir, "graph_bad");
      expect(b.paperGraph).toBeNull();
      expect(b.entries).toHaveLength(2); // the rest of the bundle loads normally
      await rm(root, { recursive: true, force: true });
    }
  });

  it("loads the Formal-layer panel data when formal_layer.json is present", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, "fl_v1");
    await cp(FIXTURE, dir, { recursive: true });
    // The committed fixture omits paper_library_index.json; supply a minimal one so the
    // integrity gate passes and this test isolates the Formal-layer loading.
    await writeFile(
      join(dir, "paper_library_index.json"),
      JSON.stringify({ commit: "demo", modules: {}, entries: [{ name: "t1_thm" }] }),
    );
    await writeFile(
      join(dir, "formal_layer.json"),
      JSON.stringify({
        commit: "demo",
        groups: [
          {
            kind: "theorem",
            items: [
              {
                obj_id: "T-1",
                kind: "theorem",
                label: "Theorem T-1",
                nl: "an upper bound",
                lean: { file: "T1.lean", decl: "t1_thm", decl_kind: "theorem", line: 1 },
                status: "matched",
                sorry_free: true,
              },
            ],
          },
        ],
      }),
    );
    const b = await loadBundle(dir, "fl_v1");
    expect(b.formalLayer?.groups).toHaveLength(1);
    expect(b.formalLayer?.groups[0].items[0]).toMatchObject({ obj_id: "T-1", status: "matched" });
    await rm(root, { recursive: true, force: true });
  });

  it("discovery skips non-bundle dirs and missing roots", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    await cp(FIXTURE, join(root, "demo_paper_v1"), { recursive: true });
    await cp(FIXTURE, join(root, "not_a_bundle"), { recursive: true });
    await rm(join(root, "not_a_bundle", "meta.json"));
    const bundles = await loadBundles([root, "/does/not/exist"]);
    expect(bundles.map((b) => b.id)).toEqual(["demo_paper_v1"]);
    await rm(root, { recursive: true, force: true });
  });

  it("orders papers best-first: score desc, unscored last, OLDEST-first tiebreak (standing flagship keeps the panel)", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const mk = async (id: string, patch: Record<string, unknown>) => {
      const dir = join(root, id);
      await cp(FIXTURE, dir, { recursive: true });
      // The committed fixture omits paper_library_index.json; supply a minimal one so
      // the integrity gate passes and this test isolates the ordering behavior.
      await writeFile(
        join(dir, "paper_library_index.json"),
        JSON.stringify({ commit: "demo", modules: {}, entries: [{ name: "t1_thm" }] }),
      );
      const meta = JSON.parse(await readFile(join(dir, "meta.json"), "utf8"));
      await writeFile(join(dir, "meta.json"), JSON.stringify({ ...meta, ...patch }));
    };
    await mk("mid", { score: 7.2, created: "2026-06-01" });
    await mk("best", { score: 9.1, created: "2026-05-01" }); // lower created but higher score → first
    await mk("unscored_new", { created: "2026-07-01" }); // no score → last despite newest
    await mk("tie_old", { score: 7.2, created: "2026-05-15" }); // ties `mid` on score → OLDER first (a new paper must strictly beat the standing flagship, 2026-08-26)
    const bundles = await loadBundles([root]);
    expect(bundles.map((b) => b.id)).toEqual(["best", "tie_old", "mid", "unscored_new"]);
    await rm(root, { recursive: true, force: true });
  });

  it("integrity gate: an 'auxiliary' entry is exempt from the body-block check (web-only)", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, "aux_v1");
    await cp(FIXTURE, dir, { recursive: true });
    await writeFile(
      join(dir, "paper_library_index.json"),
      JSON.stringify({ commit: "demo", modules: {}, entries: [{ name: "t1_thm" }] }),
    );
    // Add an auxiliary entry with NO data-objid block in the HTML, but WITH a snippet.
    const cwPath = join(dir, "presentation_crosswalk.json");
    const cw = JSON.parse(await readFile(cwPath, "utf8"));
    cw.entries.push({
      obj_id: "helperX",
      env: "auxiliary",
      paper_label: "Lemma helperX",
      title: null,
      lean: { file: "T1.lean", decl: "helperX", decl_kind: "lemma", line: 1 },
      fallback: null,
      uses: [],
      status: "matched",
      sorry_free: true,
    });
    await writeFile(cwPath, JSON.stringify(cw));
    const snPath = join(dir, "lean_snippets.json");
    const sn = JSON.parse(await readFile(snPath, "utf8"));
    sn.snippets["helperX"] = {
      decl: "helperX",
      file: "T1.lean",
      line: 1,
      statement: "lemma helperX : True",
      sorry_free: true,
      axioms: null,
    };
    await writeFile(snPath, JSON.stringify(sn));
    const b = await loadBundle(dir, "aux_v1"); // must NOT throw despite no body block for helperX
    expect(b.entries.some((e) => e.obj_id === "helperX" && e.env === "auxiliary")).toBe(true);
    await rm(root, { recursive: true, force: true });
  });

  it("integrity gate: a cited result is exempt from the body-block check (web-only)", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, "cited_v1");
    await cp(FIXTURE, dir, { recursive: true });
    await writeFile(
      join(dir, "paper_library_index.json"),
      JSON.stringify({ commit: "demo", modules: {}, entries: [{ name: "t1_thm" }] }),
    );
    const cwPath = join(dir, "presentation_crosswalk.json");
    const cw = JSON.parse(await readFile(cwPath, "utf8"));
    cw.entries.push({
      obj_id: "citedX",
      env: "citedv",
      paper_label: "Cited result citedX",
      title: null,
      lean: { file: "T1.lean", decl: "citedX", decl_kind: "def", line: 1 },
      fallback: null,
      uses: [],
      status: "matched",
      sorry_free: true,
    });
    await writeFile(cwPath, JSON.stringify(cw));
    const snPath = join(dir, "lean_snippets.json");
    const sn = JSON.parse(await readFile(snPath, "utf8"));
    sn.snippets.citedX = {
      decl: "citedX",
      file: "T1.lean",
      line: 1,
      statement: "def citedX : Prop := True",
      sorry_free: true,
      axioms: null,
    };
    await writeFile(snPath, JSON.stringify(sn));
    const b = await loadBundle(dir, "cited_v1");
    expect(b.entries.some((e) => e.obj_id === "citedX" && e.env === "citedv")).toBe(true);
    await rm(root, { recursive: true, force: true });
  });

  it("integrity gate: a Lean-backed entry without a snippet fails the build", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, "broken_v1");
    await cp(FIXTURE, dir, { recursive: true });
    const snip = JSON.parse(await readFile(join(dir, "lean_snippets.json"), "utf8"));
    delete snip.snippets["T-1"];
    await writeFile(join(dir, "lean_snippets.json"), JSON.stringify(snip));
    await expect(loadBundle(dir, "broken_v1")).rejects.toThrow(/T-1: Lean-backed entry has no snippet/);
    await rm(root, { recursive: true, force: true });
  });

  it("integrity gate: crosswalk entry without a block in the HTML fails", async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    const dir = join(root, "broken_v2");
    await cp(FIXTURE, dir, { recursive: true });
    const html = await readFile(join(dir, "paper_body.html"), "utf8");
    await writeFile(join(dir, "paper_body.html"), html.replace('data-objid="T-1"', 'data-objid="T-9"'));
    await expect(loadBundle(dir, "broken_v2")).rejects.toThrow(/T-1: no data-objid block/);
    await rm(root, { recursive: true, force: true });
  });

  // A presentation run rewrites its bundle in place over minutes. Mid-write, that
  // bundle fails the gate — and since loadBundles feeds every page's getStaticPaths,
  // it used to take the whole dev site down (landing page and unrelated papers
  // included). Dev isolates the offender; a build must still refuse to ship it.
  const withBrokenBundle = async () => {
    const root = await mkdtemp(join(tmpdir(), "site-bundles-"));
    await cp(FIXTURE, join(root, "good_v1"), { recursive: true });
    const bad = join(root, "torn_v1");
    await cp(FIXTURE, bad, { recursive: true });
    const html = await readFile(join(bad, "paper_body.html"), "utf8");
    await writeFile(join(bad, "paper_body.html"), html.replace('data-objid="T-1"', 'data-objid="T-9"'));
    return root;
  };

  it("dev: a torn bundle is skipped so the rest of the site still loads", async () => {
    vi.stubEnv("DEV", true);
    const errors: unknown[] = [];
    const spy = vi.spyOn(console, "error").mockImplementation((...a) => void errors.push(a[0]));
    const root = await withBrokenBundle();
    const bundles = await loadBundles([root]);
    expect(bundles.map((b) => b.id)).toEqual(["good_v1"]); // torn one dropped, good one served
    expect(String(errors[0])).toMatch(/SKIPPING "torn_v1"/); // and it says so, loudly
    spy.mockRestore();
    vi.unstubAllEnvs();
    await rm(root, { recursive: true, force: true });
  });

  it("build: a torn bundle still fails the whole load (never ships)", async () => {
    vi.stubEnv("DEV", false);
    const root = await withBrokenBundle();
    await expect(loadBundles([root])).rejects.toThrow(/T-1: no data-objid block/);
    vi.unstubAllEnvs();
    await rm(root, { recursive: true, force: true });
  });
});
