/**
 * Proof map panel — the controller.
 *
 * The map is laid out at build time and every chip is a real `#obj-…` link, so
 * with JavaScript off it still draws and still navigates. This file takes the
 * clicks over and applies a file-explorer grammar, which is what keeps a dense
 * rail calm:
 *
 *   • HOVER (and keyboard focus) lights EDGES only: the chip's blue "its proof
 *     invokes" and cardinal "invoked by" arrows, with the rest dimmed. Cheap,
 *     instant, and reversible — on mouse-out the highlight falls back to the
 *     pinned selection, or to neutral when nothing is pinned. It never touches
 *     the preview strip, which is what made brushing past a chip feel like
 *     churn.
 *   • SINGLE CLICK selects and pins: the same edges, plus the preview strip
 *     filled. The page does not move. The selection holds until another chip is
 *     chosen, a click lands outside the map, or ✕ / Escape clears it.
 *   • DOUBLE CLICK jumps: it scrolls the paper to the statement and flashes it.
 *     The first click of the pair has already selected, so there is no
 *     click-delay to disambiguate — select is instant, the jump is additive.
 *   • KEYBOARD mirrors that. Arrow keys walk the map without selecting
 *     anything; Enter or Space selects the focused chip, and Enter or Space
 *     AGAIN on the chip that is already selected jumps. Escape clears.
 *
 * A jump pushes `#obj-…` onto history, so Back returns the reader where they
 * were, and the strip's "Go to this statement ↓" is the discoverable path to
 * the same thing — double-click is a shortcut, never the only way, which is
 * also what makes this work on touch (tap selects, the strip link jumps).
 *
 * The preview strip lives INSIDE the rail, under the map, so it can never
 * overlap the paper column.
 *
 * The rail's width scales with the viewport, so the map is RE-WRAPPED to the
 * width it actually got — a wider rail means fewer wrapped lines, not a
 * stretched picture. The build-time SVG is what a JS-off reader keeps, and the
 * re-wrap only ever touches the fixed rail: on a narrow viewport the panel is
 * in the page's flow, and resizing it there would move the paper column, which
 * readers' scroll positions and the margin-comment anchors depend on.
 *
 * Every reader-supplied string here (a GitHub handle) is written with
 * `textContent`, and avatars go through the comment layer's host check.
 */

import { buildProofGraph, parsePaperGraph, type PaperGraph } from "../lib/proofGraph.js";
import { proofMapMarks } from "../lib/proofMapSvg.js";
import * as auth from "./comments/auth.js";
import { avatar } from "./comments/parts.js";
import {
  createAttestation,
  groupByObj,
  listAttestations,
  withdrawAttestation,
  type Attestation,
} from "./proofmap/attest.js";
import {
  clearRating,
  listRatings,
  summarize,
  writeRating,
  type RatingRow,
} from "./ratings/api.js";
import { renderStars } from "./ratings/stars.js";

interface MapNode {
  id: string;
  label: string;
  title: string | null;
  top: boolean;
  cites: string[];
  citedBy: string[];
}

interface Ui {
  panel: HTMLElement;
  scroll: HTMLElement;
  marks: SVGGElement;
  toggle: HTMLButtonElement;
  body: HTMLElement;
  svg: SVGSVGElement;
  card: HTMLElement;
  cardClose: HTMLButtonElement;
  cardLabel: HTMLElement;
  cardTitle: HTMLElement;
  stmt: HTMLElement;
  goto: HTMLButtonElement;
  cites: HTMLElement;
  citedBy: HTMLElement;
  attest: HTMLElement;
  readers: HTMLElement;
  verify: HTMLButtonElement;
  status: HTMLElement;
  coverage: HTMLElement;
  coverageBar: HTMLElement;
  coverageTxt: HTMLElement;
  /** Star-rating slots. OPTIONAL — an older cached page may lack the markup,
   *  and the map must keep working without it. */
  rate: HTMLElement | null;
  rateStars: HTMLElement | null;
  rateStatus: HTMLElement | null;
}

interface State {
  ui: Ui;
  paperId: string;
  worker: string;
  /** The graph itself, for re-wrapping the map to the rail's real width. */
  graph: PaperGraph | null;
  /** The width the map is currently laid out for. */
  mapWidth: number;
  nodes: Map<string, MapNode>;
  nodeEls: Map<string, SVGAElement>;
  edgeEls: Element[];
  /** The pinned chip: what the strip shows. Only a click changes it. */
  selected: string | null;
  /** Under the cursor or keyboard focus; lights edges, never touches the strip. */
  hovered: string | null;
  /** Chips in reading order, for arrow-key navigation. */
  order: string[];
  /** objId → the readers who attested it. Empty until (and unless) the worker answers. */
  marks: Map<string, Attestation[]>;
  /** Star ratings, one flat row list; summarized per selected statement. */
  ratings: RatingRow[];
  token: string | null;
  viewer: { login: string; avatarUrl: string } | null;
  busy: boolean;
  ratingBusy: boolean;
  /** The verification line under the button, held here so a late-arriving load
   *  cannot repaint over the reader's own result. */
  status: string;
  ratingStatus: string;
}

/** Readers shown by avatar AND named in the verify line; the rest fold into "and N more". */
const MAX_AVATARS = 5;
/** Below this the site hides the contents rail, so the panel collapses instead. */
const RAIL_MIN_PX = 1281;
/** Close to the browser's native smooth-scroll duration, but with a live target. */
const JUMP_DURATION_MS = 480;
/** Cancels an older animation when the reader chooses another statement. */
let jumpGeneration = 0;

/** Entry point; safe to call on any page. */
export function initProofMap(): void {
  try {
    boot();
  } catch {
    /* the paper must render even if the map cannot */
  }
}

function el<T extends HTMLElement>(id: string): T | null {
  return document.getElementById(id) as T | null;
}

function readData(): {
  paperId: string;
  worker: string;
  nodes: MapNode[];
  graph: PaperGraph | null;
  builtWidth: number;
} | null {
  const script = document.getElementById("proof-map-data");
  if (!script) return null;
  let data: Record<string, unknown>;
  try {
    data = JSON.parse(script.textContent ?? "") as Record<string, unknown>;
  } catch {
    return null;
  }
  if (!Array.isArray(data.nodes)) return null;
  // The payload is our own build output, but a stale cached page paired with a
  // new script is a real thing; keep only rows this file can actually drive.
  const nodes = (data.nodes as Record<string, unknown>[])
    .filter((n) => n && typeof n.id === "string")
    .map((n) => ({
      id: n.id as string,
      label: typeof n.label === "string" ? n.label : (n.id as string),
      title: typeof n.title === "string" ? n.title : null,
      top: n.top === true,
      cites: Array.isArray(n.cites) ? (n.cites.filter((x) => typeof x === "string") as string[]) : [],
      citedBy: Array.isArray(n.citedBy)
        ? (n.citedBy.filter((x) => typeof x === "string") as string[])
        : [],
    }));
  if (nodes.length === 0) return null;
  const paperId = typeof data.paperId === "string" ? data.paperId : "";
  const rawWorker = typeof data.worker === "string" ? data.worker.trim() : "";
  const builtWidth = typeof data.builtWidth === "number" ? data.builtWidth : 0;
  // Same defensive parse the build used: a graph we cannot trust simply means
  // no re-wrapping, never a broken map.
  const graph = parsePaperGraph(data.graph);
  return { paperId, worker: attestationWorker(rawWorker, paperId), nodes, graph, builtWidth };
}

/**
 * The worker base URL to talk to, or "" for a read-only map.
 *
 * Same rules the commenting controller applies: a real https origin (or
 * localhost for development), and a paper id that can safely go in a query
 * string. Anything else disables the write path rather than half-enabling it.
 */
function attestationWorker(raw: string, paperId: string): string {
  if (!raw || !/^[A-Za-z0-9_.-]{1,128}$/.test(paperId)) return "";
  let url: URL;
  try {
    url = new URL(raw);
  } catch {
    return "";
  }
  const localhost = url.hostname === "localhost" || url.hostname === "127.0.0.1";
  if (url.protocol !== "https:" && !localhost) return "";
  return raw.replace(/\/+$/, "");
}

function queryUi(): Ui | null {
  const svg = document.getElementById("pm-map") as SVGSVGElement | null;
  const marks = document.getElementById("pm-marks") as SVGGElement | null;
  const parts = {
    panel: el("proof-map"),
    scroll: el("pm-graph-scroll"),
    toggle: el<HTMLButtonElement>("pm-toggle"),
    body: el("pm-body"),
    card: el("pm-card"),
    cardClose: el<HTMLButtonElement>("pm-card-close"),
    cardLabel: el("pm-card-label"),
    cardTitle: el("pm-card-title"),
    stmt: el("pm-stmt"),
    goto: el<HTMLButtonElement>("pm-goto"),
    cites: el("pm-cites"),
    citedBy: el("pm-citedby"),
    attest: el("pm-attest"),
    readers: el("pm-readers"),
    verify: el<HTMLButtonElement>("pm-verify"),
    status: el("pm-attest-status"),
    coverage: el("pm-coverage"),
    coverageBar: el("pm-coverage-bar"),
    coverageTxt: el("pm-coverage-txt"),
  };
  if (!svg || !marks) return null;
  for (const v of Object.values(parts)) if (!v) return null;
  // Rating slots are additive and tolerated absent (stale cached markup).
  const rating = {
    rate: el("pm-rate"),
    rateStars: el("pm-stars"),
    rateStatus: el("pm-rate-status"),
  };
  return { svg, marks, ...(parts as Required<typeof parts>), ...rating } as Ui;
}

function boot(): void {
  const data = readData();
  const ui = queryUi();
  if (!data || !ui) return;

  const state: State = {
    ui,
    paperId: data.paperId,
    worker: data.worker,
    graph: data.graph,
    mapWidth: data.builtWidth || ui.svg.viewBox?.baseVal?.width || 0,
    nodes: new Map(data.nodes.map((n) => [n.id, n])),
    nodeEls: new Map(),
    edgeEls: Array.from(ui.svg.querySelectorAll("path.pm-edge")),
    selected: null,
    hovered: null,
    order: [],
    marks: new Map(),
    ratings: [],
    token: data.worker ? auth.readToken() : null,
    viewer: null,
    busy: false,
    ratingBusy: false,
    status: "",
    ratingStatus: "",
  };

  wireChips(state);

  ui.toggle.addEventListener("click", () => toggleBody(state));
  ui.cardClose.addEventListener("click", () => clearSelection(state));
  ui.goto.addEventListener("click", () => {
    if (state.selected) jumpTo(state, state.selected);
  });
  ui.verify.addEventListener("click", () => void onVerify(state));

  // One session per page: adopt a sign-in or sign-out made through the
  // comments rail (both widgets share the same stored token), so the reader
  // never signs in twice on one paper.
  window.addEventListener(auth.AUTH_EVENT, () => {
    const token = auth.readToken();
    if (token === state.token) return;
    state.token = token;
    state.viewer = null;
    if (token) void loadViewer(state).then(() => refreshMarks(state));
    else refreshMarks(state);
  });

  document.addEventListener("keydown", (e) => {
    if (e.key !== "Escape" || state.selected === null) return;
    clearSelection(state);
  });
  // A click outside the map drops the selection, the way a file explorer
  // deselects when you click the empty pane.
  document.addEventListener("mousedown", (e) => {
    if (state.selected === null) return;
    const t = e.target;
    if (t instanceof Node && ui.panel.contains(t)) return;
    clearSelection(state);
  });

  // Narrow viewports have no rail to dock to, so the panel starts collapsed and
  // costs one line until the reader opens it.
  if (
    typeof window.matchMedia === "function" &&
    !window.matchMedia(`(min-width: ${RAIL_MIN_PX}px)`).matches
  ) {
    setBody(state, false);
  }

  // Fit the map to the width the rail actually got, once the browser has laid
  // the page out.
  if (typeof requestAnimationFrame === "function") requestAnimationFrame(() => fitMap(state));
  else fitMap(state);
  let resizeTimer = 0;
  window.addEventListener("resize", () => {
    window.clearTimeout(resizeTimer);
    resizeTimer = window.setTimeout(() => fitMap(state), 150);
  });

  if (state.worker) void loadMarks(state);
}

/* ── Chips ───────────────────────────────────────────────────────────────── */

/** Bind every chip and rebuild the arrow-key order. Re-run after a re-wrap. */
function wireChips(state: State): void {
  const { ui } = state;
  const chips = Array.from(ui.svg.querySelectorAll<SVGAElement>("a.pm-node")).filter((a) =>
    state.nodes.has(a.getAttribute("data-pm-node") ?? ""),
  );
  state.nodeEls = new Map();
  state.edgeEls = Array.from(ui.svg.querySelectorAll("path.pm-edge"));
  for (const a of chips) {
    const id = a.getAttribute("data-pm-node")!;
    state.nodeEls.set(id, a);
    a.addEventListener("click", (e) => {
      // Single click selects and never navigates; the href stays as the JS-off
      // fallback and as a link a reader can copy.
      e.preventDefault();
      selectNode(state, id);
    });
    a.addEventListener("dblclick", (e) => {
      e.preventDefault();
      jumpTo(state, id);
    });
    // Hover and focus light the edges and nothing else; walking the map never
    // rebuilds the strip, which is what the churn complaint was about.
    a.addEventListener("mouseenter", () => setHover(state, id));
    a.addEventListener("mouseleave", () => clearHover(state, id));
    a.addEventListener("focus", () => {
      setCurrent(state, id);
      setHover(state, id);
    });
    a.addEventListener("blur", () => clearHover(state, id));
    a.addEventListener("keydown", (e) => onChipKey(state, id, e));
  }

  // Reading order for arrow keys: down the lines, left to right within each.
  state.order = chips
    .map((a) => ({ id: a.getAttribute("data-pm-node")!, a }))
    .sort((p, q) => {
      const py = Number(p.a.querySelector("rect")?.getAttribute("y") ?? 0);
      const qy = Number(q.a.querySelector("rect")?.getAttribute("y") ?? 0);
      if (py !== qy) return py - qy;
      return (
        Number(p.a.querySelector("rect")?.getAttribute("x") ?? 0) -
        Number(q.a.querySelector("rect")?.getAttribute("x") ?? 0)
      );
    })
    .map((x) => x.id);
  // Roving tabindex: 23 chips must not be 23 tab stops between the contents and
  // the preview's controls. Applied HERE, not in the markup, so a JS-off page
  // keeps every chip in the tab order.
  state.order.forEach((id, i) =>
    state.nodeEls.get(id)!.setAttribute("tabindex", i === 0 ? "0" : "-1"),
  );
}

/* ── Fitting the map to the rail ─────────────────────────────────────────── */

/** Narrowest and widest the map is ever laid out for. */
const MAP_MIN_PX = 226;
const MAP_MAX_PX = 420;
/** Below this much difference a re-wrap would not change a single line. */
const REFIT_EPSILON_PX = 20;

/**
 * Re-wrap the map for the width the rail actually got.
 *
 * Only ever runs against the FIXED rail: on a narrow viewport the panel sits in
 * the page's flow, where changing its height would move the paper column — and
 * readers' scroll positions and the margin-comment anchors are pinned to that
 * column. A collapsed or unmeasurable panel is left alone for the same reason.
 */
function fitMap(state: State): void {
  const { ui, graph } = state;
  if (!graph) return;
  if (
    typeof window.matchMedia === "function" &&
    !window.matchMedia(`(min-width: ${RAIL_MIN_PX}px)`).matches
  ) {
    return;
  }
  const measured = ui.scroll.clientWidth;
  if (!measured || measured < 80) return; // collapsed, hidden, or not laid out yet
  const target = Math.round(Math.min(MAP_MAX_PX, Math.max(MAP_MIN_PX, measured)));
  if (Math.abs(target - state.mapWidth) < REFIT_EPSILON_PX) return;

  const layout = buildProofGraph(graph, { maxWidth: target });
  ui.svg.setAttribute("viewBox", `0 0 ${layout.width} ${layout.height}`);
  ui.svg.setAttribute("width", String(layout.width));
  ui.svg.setAttribute("height", String(layout.height));
  ui.marks.innerHTML = proofMapMarks(layout);
  state.mapWidth = layout.width;
  // The chips are new elements, so they need their listeners, their arrow-key
  // order, and the state they were showing before the re-wrap.
  wireChips(state);
  refreshMarks(state);
  repaint(state);
}

/* ── Panel disclosure ────────────────────────────────────────────────────── */

function setBody(state: State, open: boolean): void {
  state.ui.body.hidden = !open;
  state.ui.panel.classList.toggle("is-collapsed", !open);
  state.ui.toggle.setAttribute("aria-expanded", open ? "true" : "false");
}

function toggleBody(state: State): void {
  setBody(state, state.ui.body.hidden);
}

/* ── Selection ───────────────────────────────────────────────────────────── */

/** Paint the edges and chips for `id`, or return the map to neutral for null. */
function applyHighlight(state: State, id: string | null): void {
  const node = id ? state.nodes.get(id) : null;
  if (!node) {
    for (const path of state.edgeEls) {
      path.classList.remove("is-cites", "is-citedby", "is-dim");
      path.setAttribute("marker-end", "url(#pm-arr)");
    }
    for (const a of state.nodeEls.values()) a.classList.remove("is-selected", "is-dim");
    return;
  }
  const cites = new Set(node.cites);
  const citedBy = new Set(node.citedBy);
  for (const path of state.edgeEls) {
    const from = path.getAttribute("data-from");
    const to = path.getAttribute("data-to");
    path.classList.remove("is-cites", "is-citedby", "is-dim");
    let marker = "url(#pm-arr)";
    if (from === id) {
      path.classList.add("is-cites");
      marker = "url(#pm-arr-cites)";
    } else if (to === id) {
      path.classList.add("is-citedby");
      marker = "url(#pm-arr-citedby)";
    } else {
      path.classList.add("is-dim");
    }
    path.setAttribute("marker-end", marker);
  }
  for (const [otherId, a] of state.nodeEls) {
    a.classList.toggle("is-selected", otherId === state.selected);
    // The pinned chip is never dimmed, even while a hover lights someone else's
    // neighbourhood: the reader must be able to see what they still have chosen.
    const related = otherId === id || cites.has(otherId) || citedBy.has(otherId);
    a.classList.toggle("is-dim", !related && otherId !== state.selected);
  }
}

/** The highlight the map should show: what the cursor is on, else the pin. */
function repaint(state: State): void {
  applyHighlight(state, state.hovered ?? state.selected);
}

/** Hover or keyboard focus: light this chip's edges. The strip is untouched. */
function setHover(state: State, id: string): void {
  if (!state.nodes.has(id)) return;
  state.hovered = id;
  repaint(state);
}

/** Cursor left (or focus moved on): the pinned selection takes the light back. */
function clearHover(state: State, id: string): void {
  if (state.hovered !== id) return;
  state.hovered = null;
  repaint(state);
}

/** Single click / Enter: light the neighbourhood and fill the strip. No jump. */
function selectNode(state: State, id: string): void {
  const node = state.nodes.get(id);
  if (!node) return;
  const changed = state.selected !== id;
  state.selected = id;
  repaint(state);
  showPreview(state, node, changed);
}

/** ✕, Escape, or a click outside: back to a neutral map and an empty strip. */
function clearSelection(state: State): void {
  state.selected = null;
  repaint(state);
  state.ui.card.hidden = true;
}

/**
 * Double click, the strip's link, or Enter on an already-selected chip: go to
 * the statement.
 *
 * The hash is pushed onto history first, so the reader's Back button returns
 * them to where they were reading — a jump from the map behaves like following
 * a link, because that is what it is.
 */
function jumpTo(state: State, id: string): void {
  selectNode(state, id);
  try {
    if (location.hash !== `#obj-${id}`) history.pushState(null, "", `#obj-${id}`);
  } catch {
    /* history can be unavailable (sandboxed frames); the scroll still works */
  }
  revealInPaper(id);
}

/** Scroll the paper body to a statement and flash it, as a deep link does. */
function revealInPaper(objId: string): void {
  const body = document.getElementById("paper-body");
  const target = body?.querySelector<HTMLElement>(
    `.formal-block[data-objid="${cssEscape(objId)}"]`,
  );
  if (!target) return;
  // Centre the LABEL, not the whole formal block. A theorem can be taller than
  // the viewport; centring that box lands halfway through its body, far below
  // the statement the reader selected in the proof map.
  const label = target.querySelector<HTMLElement>(".env-label") ?? target;
  const generation = ++jumpGeneration;
  const viewportHeight = () => window.innerHeight || document.documentElement.clientHeight;
  const centerError = () => {
    const rect = label.getBoundingClientRect();
    return rect.top + rect.height / 2 - viewportHeight() / 2;
  };
  const center = () => label.scrollIntoView({ block: "center", behavior: "auto" });

  // Activating the destination can itself replace one last intrinsic-size
  // placeholder. Re-check after layout and recenter until two frames agree, so
  // a single double-click settles on the label even in a never-visited paper.
  const settle = () => {
    if (typeof requestAnimationFrame !== "function") return;
    let attempts = 0;
    let stableFrames = 0;
    const frame = () => {
      if (generation !== jumpGeneration || !label.isConnected) return;
      const error = viewportHeight() > 0 ? centerError() : 0;
      if (Math.abs(error) > 1) {
        center();
        stableFrames = 0;
      } else {
        stableFrames++;
      }
      attempts++;
      if (attempts < 8 && stableFrames < 2) requestAnimationFrame(frame);
    };
    requestAnimationFrame(frame);
  };

  const reduce =
    typeof window.matchMedia === "function" &&
    window.matchMedia("(prefers-reduced-motion: reduce)").matches;
  if (
    reduce ||
    typeof requestAnimationFrame !== "function" ||
    typeof window.scrollTo !== "function" ||
    viewportHeight() <= 0
  ) {
    center();
    settle();
  } else {
    // Native smooth scrolling fixes its destination before it starts. That is
    // wrong for this paper: `content-visibility: auto` activates skipped
    // sections along the route, replacing placeholder heights and moving L4
    // (or any later result) while the scroll is under way. Animate manually and
    // recompute the destination every frame, preserving the transition while
    // following the target's live position.
    const startY = window.scrollY;
    let startedAt: number | null = null;
    const animate = (now: number) => {
      if (generation !== jumpGeneration || !label.isConnected) return;
      if (startedAt === null) startedAt = now;
      const progress = Math.min(1, Math.max(0, (now - startedAt) / JUMP_DURATION_MS));
      const eased = 1 - (1 - progress) ** 3;
      const desiredY = window.scrollY + centerError();
      window.scrollTo({ top: startY + (desiredY - startY) * eased, behavior: "auto" });
      if (progress < 1) requestAnimationFrame(animate);
      else settle();
    };
    requestAnimationFrame(animate);
  }
  target.classList.add("flash");
  window.setTimeout(() => target.classList.remove("flash"), 1600);
}

/** Minimal attribute-selector escaping; obj ids are `lem:foo` shaped. */
function cssEscape(value: string): string {
  return value.replace(/["\\]/g, "\\$&");
}

/* ── Keyboard ────────────────────────────────────────────────────────────── */

/** Roving tabindex: only the chip the reader last visited is a tab stop. */
function setCurrent(state: State, id: string): void {
  for (const [otherId, a] of state.nodeEls) {
    a.setAttribute("tabindex", otherId === id ? "0" : "-1");
  }
}

function focusChip(state: State, id: string): void {
  const a = state.nodeEls.get(id);
  if (!a) return;
  setCurrent(state, id);
  (a as unknown as HTMLElement).focus?.();
}

/**
 * Arrow keys walk the map — one tab stop for the whole graph, and walking
 * selects nothing. Enter/Space selects the focused chip; pressing it again on
 * the chip that is already selected jumps, which is the keyboard's spelling of
 * click-then-double-click.
 */
function onChipKey(state: State, id: string, e: KeyboardEvent): void {
  if (e.key === "Enter" || e.key === " " || e.key === "Spacebar") {
    // Anchors activate on Enter by themselves; take it over so the first press
    // selects instead of navigating.
    e.preventDefault();
    if (state.selected === id) jumpTo(state, id);
    else selectNode(state, id);
    return;
  }
  const order = state.order;
  const i = order.indexOf(id);
  if (i < 0) return;
  let next: string | undefined;
  if (e.key === "ArrowRight" || e.key === "ArrowDown") next = order[i + 1];
  else if (e.key === "ArrowLeft" || e.key === "ArrowUp") next = order[i - 1];
  else if (e.key === "Home") next = order[0];
  else if (e.key === "End") next = order[order.length - 1];
  else return;
  e.preventDefault();
  if (next) focusChip(state, next);
}

/* ── Preview strip ───────────────────────────────────────────────────────── */

function clear(node: Element): void {
  while (node.firstChild) node.removeChild(node.firstChild);
}

/**
 * Fill the strip for a node.
 *
 * `rebuild` is false when the same statement is re-selected (a second Enter, a
 * double click): the DOM is left alone so a repaint cannot yank a button out
 * from under the reader's cursor mid-click.
 */
function showPreview(state: State, node: MapNode, rebuild: boolean): void {
  const { ui } = state;
  ui.card.hidden = false;
  if (!rebuild) return;
  ui.cardLabel.textContent = node.label;
  ui.cardTitle.textContent = node.title ?? node.label;

  clear(ui.stmt);
  const block = document
    .getElementById("paper-body")
    ?.querySelector<HTMLElement>(`.formal-block[data-objid="${cssEscape(node.id)}"]`);
  if (block) {
    // A clone of the page's OWN rendered block: same KaTeX, no second source of
    // truth. Its interactive attributes are stripped so the copy cannot open the
    // Lean drawer or take a duplicate id.
    const copy = block.cloneNode(true) as HTMLElement;
    copy.removeAttribute("id");
    copy.removeAttribute("data-objid");
    copy.removeAttribute("tabindex");
    copy.className = "pm-stmt-block";
    for (const inner of Array.from(copy.querySelectorAll("[data-objid], [id]"))) {
      inner.removeAttribute("data-objid");
      inner.removeAttribute("id");
    }
    ui.stmt.appendChild(copy);
  } else {
    const p = document.createElement("p");
    p.textContent = node.title ?? node.label;
    ui.stmt.appendChild(p);
  }

  renderChips(state, ui.cites, node.cites);
  renderChips(state, ui.citedBy, node.citedBy);
  setStatus(state, "");
  setRatingStatus(state, "");
  renderAttest(state, node);
  renderRate(state, node);
}

function renderChips(state: State, host: HTMLElement, ids: string[]): void {
  clear(host);
  if (ids.length === 0) {
    const none = document.createElement("span");
    none.className = "pm-none";
    none.textContent = "nothing in this paper";
    host.appendChild(none);
    return;
  }
  for (const id of ids) {
    const target = state.nodes.get(id);
    if (!target) continue;
    const btn = document.createElement("button");
    btn.type = "button";
    btn.textContent = target.label;
    if (target.title) btn.title = target.title;
    // Following a chip selects it, exactly as clicking it in the map would; it
    // deliberately does NOT move the paper.
    btn.addEventListener("click", () => selectNode(state, id));
    host.appendChild(btn);
  }
}

/* ── Reader verification ─────────────────────────────────────────────────── */

function renderAttest(state: State, node: MapNode): void {
  const { ui } = state;
  // No worker configured → the map is read-only. Never a broken button.
  if (!state.worker) {
    ui.attest.hidden = true;
    return;
  }
  ui.attest.hidden = false;
  ui.status.textContent = state.status;
  const list = state.marks.get(node.id) ?? [];
  const mine = state.viewer ? list.some((a) => a.login === state.viewer!.login) : false;

  clear(ui.readers);
  for (const a of list.slice(0, MAX_AVATARS)) {
    const av = avatar({ login: a.login, avatarUrl: a.avatarUrl }, "pm-av");
    if (state.viewer && a.login === state.viewer.login) av.classList.add("pm-you");
    av.title = `@${a.login}`;
    ui.readers.appendChild(av);
  }
  const count = document.createElement("span");
  count.className = "pm-count";
  if (list.length === 0) {
    count.textContent = "no reader has verified this yet";
  } else {
    const names = list.slice(0, MAX_AVATARS).map((a) => `@${a.login}`);
    const extra = list.length - names.length;
    count.textContent = `verified by ${names.join(", ")}${extra > 0 ? ` and ${extra} more` : ""}`;
  }
  ui.readers.appendChild(count);

  ui.verify.classList.toggle("is-mine", mine);
  ui.verify.classList.toggle("needs-login", !state.token);
  ui.verify.disabled = state.busy;
  ui.verify.textContent = !state.token
    ? "Sign in with GitHub to verify"
    : mine
      ? "✓ You verified this — withdraw"
      : "I verified this statement & proof";
}

async function loadMarks(state: State): Promise<void> {
  const [attRes, ratRes] = await Promise.allSettled([
    listAttestations(state.worker, state.paperId),
    listRatings(state.worker, state.paperId),
  ]);
  // A dead endpoint leaves the map fully usable; only the counts are missing.
  state.marks = attRes.status === "fulfilled" ? groupByObj(attRes.value) : new Map();
  state.ratings = ratRes.status === "fulfilled" ? ratRes.value : [];
  if (state.token) await loadViewer(state);
  refreshMarks(state);
}

/** Resolve who is signed in, so their own mark can be shown and withdrawn. */
async function loadViewer(state: State): Promise<void> {
  if (!state.token) return;
  try {
    const res = await fetch("https://api.github.com/user", {
      credentials: "omit",
      headers: { Authorization: `Bearer ${state.token}` },
    });
    if (res.status === 401) {
      auth.clearToken();
      state.token = null;
      return;
    }
    if (!res.ok) return;
    const data = (await res.json()) as { login?: unknown; avatar_url?: unknown };
    if (typeof data.login === "string") {
      state.viewer = {
        login: data.login,
        avatarUrl: typeof data.avatar_url === "string" ? data.avatar_url : "",
      };
    }
  } catch {
    /* the map still works; the reader is just anonymous to it */
  }
}

/** Repaint the verified marks on the chips, the coverage meter, and the strip. */
function refreshMarks(state: State): void {
  const { ui } = state;
  for (const [id, a] of state.nodeEls) {
    a.classList.toggle("is-attested", (state.marks.get(id) ?? []).length > 0);
  }
  if (!state.worker) return;
  const total = state.nodes.size;
  const covered = [...state.nodes.keys()].filter(
    (id) => (state.marks.get(id) ?? []).length > 0,
  ).length;
  ui.coverage.hidden = false;
  ui.coverageBar.style.width = `${total ? Math.round((100 * covered) / total) : 0}%`;
  ui.coverageTxt.textContent = `${covered}/${total} ✓`;

  const node = state.selected ? state.nodes.get(state.selected) : null;
  if (node && !ui.card.hidden) {
    renderAttest(state, node);
    renderRate(state, node);
  }
}

/** Write the verification line, and remember it: every repaint replays it. */
function setStatus(state: State, message: string): void {
  state.status = message;
  state.ui.status.textContent = message;
}

async function onVerify(state: State): Promise<void> {
  const id = state.selected;
  const node = id ? state.nodes.get(id) : null;
  if (!node || !state.worker || state.busy) return;

  if (!state.token) {
    setStatus(state, "Opening GitHub…");
    try {
      const token = await auth.signIn(state.worker);
      state.token = token; // before writeToken: its broadcast must find us in sync
      auth.writeToken(token);
      await loadViewer(state);
      setStatus(state, "");
    } catch {
      setStatus(state, "Sign-in did not complete.");
    }
    renderAttest(state, node);
    renderRate(state, node); // the star strip shares the token; keep it in step
    return;
  }

  const list = state.marks.get(node.id) ?? [];
  const mine = state.viewer ? list.some((a) => a.login === state.viewer!.login) : false;
  state.busy = true;
  state.ui.verify.disabled = true;
  setStatus(state, mine ? "Withdrawing…" : "Recording…");
  try {
    if (mine) {
      await withdrawAttestation(state.worker, state.paperId, node.id, state.token);
      state.marks.set(
        node.id,
        list.filter((a) => a.login !== state.viewer!.login),
      );
      setStatus(state, "Withdrawn.");
    } else {
      const created = await createAttestation(state.worker, state.paperId, node.id, state.token);
      if (!state.viewer) {
        state.viewer = { login: created.login, avatarUrl: created.avatarUrl ?? "" };
      }
      state.marks.set(node.id, [...list, created]);
      setStatus(state, "Recorded — thank you.");
    }
  } catch (err) {
    const detail = err instanceof Error && err.message ? ` (${err.message.slice(0, 120)})` : "";
    setStatus(state, `Could not save that${detail}.`);
  } finally {
    state.busy = false;
    refreshMarks(state);
    renderAttest(state, node);
  }
}

/* ── Statement star ratings ──────────────────────────────────────────────── */

/** Same holds-across-repaints contract as the verification line. */
function setRatingStatus(state: State, message: string): void {
  state.ratingStatus = message;
  if (state.ui.rateStatus) state.ui.rateStatus.textContent = message;
}

/** Fill (or hide) the star strip for the selected statement. */
function renderRate(state: State, node: MapNode): void {
  const { ui } = state;
  if (!ui.rate || !ui.rateStars) return; // stale markup without the slots
  if (!state.worker) {
    ui.rate.hidden = true;
    return;
  }
  ui.rate.hidden = false;
  if (ui.rateStatus) ui.rateStatus.textContent = state.ratingStatus;
  renderStars(ui.rateStars, {
    summary: summarize(state.ratings, state.viewer?.login ?? null).get(node.id) ?? null,
    signedIn: !!state.token,
    busy: state.ratingBusy,
    noun: "statement",
    onRate: (n) => void onRateStatement(state, n),
    // Already signed in → no re-render: it would kill the pulse and drop the
    // keyboard focus the CTA click just placed on the stars.
    onCta: () => {
      if (state.ratingBusy || state.token) return;
      void ensureRatingSignIn(state).then((ok) => {
        if (ok && state.selected === node.id) {
          renderRate(state, node);
          renderAttest(state, node); // the verify button shares the token
        }
      });
    },
  });
}

/** Sign the viewer in if needed. True when a token is held afterwards. */
async function ensureRatingSignIn(state: State): Promise<boolean> {
  if (state.token) return true;
  setRatingStatus(state, "Opening GitHub…");
  try {
    const token = await auth.signIn(state.worker);
    state.token = token; // before writeToken: its broadcast must find us in sync
    auth.writeToken(token);
    await loadViewer(state);
    setRatingStatus(state, "Signed in.");
    return true;
  } catch {
    setRatingStatus(state, "Sign-in did not complete.");
    return false;
  }
}

/** Replace the viewer's own row for one statement locally (null removes it). */
function adoptOwnRating(state: State, objId: string, stars: number | null): void {
  const login = state.viewer?.login;
  if (!login) return;
  state.ratings = state.ratings.filter((r) => !(r.target === objId && r.login === login));
  if (stars !== null) {
    state.ratings.push({ target: objId, login, avatarUrl: null, stars });
  }
}

async function onRateStatement(state: State, stars: number): Promise<void> {
  const id = state.selected;
  const node = id ? state.nodes.get(id) : null;
  if (!node || !state.worker || state.ratingBusy) return;
  // Busy BEFORE the sign-in await: repeated clicks while the popup is open
  // must not start concurrent sign-in/write flows.
  state.ratingBusy = true;
  renderRate(state, node);

  if (!(await ensureRatingSignIn(state))) {
    state.ratingBusy = false;
    if (state.selected === node.id) renderRate(state, node);
    return;
  }
  setRatingStatus(state, "");
  if (state.selected === node.id) renderAttest(state, node); // verify button shares the token

  const mine =
    summarize(state.ratings, state.viewer?.login ?? null).get(node.id)?.mine ?? null;
  try {
    if (mine === stars) {
      await clearRating(state.worker, state.paperId, node.id, state.token!);
      adoptOwnRating(state, node.id, null);
      setRatingStatus(state, "Rating withdrawn.");
    } else {
      await writeRating(state.worker, state.paperId, node.id, stars, state.token!);
      adoptOwnRating(state, node.id, stars);
      setRatingStatus(state, "");
    }
  } catch (err) {
    const detail = err instanceof Error && err.message ? ` (${err.message.slice(0, 120)})` : "";
    setRatingStatus(state, `Could not save that${detail}.`);
  } finally {
    state.ratingBusy = false;
    // Only repaint if this statement is still the one on the card — the
    // selection may have moved during the awaits, and statement A's stars must
    // not land under statement B's heading. `refreshMarks` on the next load
    // reconciles the counts either way.
    if (state.selected === node.id) renderRate(state, node);
  }
}
