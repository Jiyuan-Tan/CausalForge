import { describe, it, expect, vi } from "vitest";
import { mkdtemp, cp, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { loadBundle, loadBundles, verifiedBadge } from "../src/lib/bundles.js";

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

  it("orders papers best-first: score desc, unscored last, created-desc tiebreak", async () => {
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
    await mk("tie_old", { score: 7.2, created: "2026-05-15" }); // ties `mid` on score → older last
    const bundles = await loadBundles([root]);
    expect(bundles.map((b) => b.id)).toEqual(["best", "mid", "tie_old", "unscored_new"]);
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
