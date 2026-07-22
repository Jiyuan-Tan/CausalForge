import { readFile, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { isUndeliveredNode, type FormalizationGraph, type GraphEdge } from "./types.js";
import { isPaperTmpPath } from "../paths.js";
import { statementHash } from "./hash.js";

// Accept BOTH the legacy obj-id ids (`t1`, `p3b`) and the typed-core node ids the
// plan-driven F2 now emits (`thm:clipped-upper`, `def:weak-overlap-class`) — i.e.
// allow `:`, `.`, and `-` in the id, not only `[A-Za-z0-9_]`.
// The tag id allows `:`, `.`, `-` (typed-core ids like `thm:clipped-upper`) plus the legacy
// obj-ids. A canonical ownership anchor is deliberately COLUMN ZERO. Indented
// `-- @node:` text can occur inside a declaration body when a producer repeats
// metadata; treating it as a new top-level anchor misbinds it to the next lemma.
// Tolerate trailing whitespace/CR; the value is the first run of id chars.
const NODE_TAG_RE = /^--\s*@node:\s*([A-Za-z0-9_:.\-]+)\s*$/;
// A declaration header: optional `@[attr]` attributes, then any order of binder modifiers, then the
// decl keyword + name. Kept permissive so a tagged decl is never missed because of an attribute or
// an extra modifier (the historical source of "@node didn't link" errors).
const DECL_RE =
  /^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+|scoped\s+|local\s+|partial\s+|unsafe\s+|nonrec\s+)*(def|abbrev|structure|theorem|lemma|instance|class|inductive)\s+([A-Za-z0-9_'.]+)/;

export interface ExtractedDecl {
  nodeId: string;
  /** the Lean keyword: def | abbrev | structure | theorem | lemma | instance */
  declKind: string;
  declName: string;
  namespace: string;
  file: string;
  statement: string;
  hasSorry: boolean;
}

/** Identifiers appearing in a statement (alnum/underscore/dot runs), de-duplicated. */
function identifiers(text: string): string[] {
  return Array.from(new Set(text.match(/[A-Za-z_][A-Za-z0-9_'.]*/g) ?? []));
}

/** Index of the TOP-LEVEL `:=` (bracket depth 0 over `()[]{}⟨⟩⦃⦄`) that separates a
 *  declaration's STATEMENT (signature) from its BODY/PROOF, or -1 if there is none.
 *  A theorem/lemma signature can itself contain `:=` — a `let x := …` or a binder
 *  default `(x : T := d)` inside a hypothesis — but that one sits INSIDE a binder's
 *  brackets (depth ≥ 1). Taking the FIRST `:=` regardless (the old `indexOf(":=")`)
 *  truncated the signature there and silently dropped every LATER binder's
 *  statement-uses edges (e.g. `(hvc : PolicyClassVC …)` that follows a `let` in an
 *  earlier hypothesis). A `structure … where` has no top-level `:=` → -1, so its
 *  fields stay part of the statement (the historic behaviour). */
export function topLevelAssignIndex(text: string): number {
  const masked = maskLeanCommentsAndStrings(text);
  const open = "([{⟨⦃";
  const close = ")]}⟩⦄";
  let depth = 0;
  let pendingBinders = 0;
  const wordAt = (i: number, kw: string): boolean => {
    const isWord = (c: string | undefined) => c != null && /[A-Za-z0-9_'.]/.test(c);
    return !isWord(masked[i - 1]) && masked.startsWith(kw, i) && !isWord(masked[i + kw.length]);
  };
  for (let i = 0; i < masked.length; i++) {
    const c = masked[i];
    if (open.includes(c)) depth++;
    else if (close.includes(c)) depth = Math.max(0, depth - 1);
    else if (depth === 0 && (wordAt(i, "let") || wordAt(i, "have"))) pendingBinders++;
    else if (depth === 0 && c === ":" && masked[i + 1] === "=") {
      if (pendingBinders > 0) pendingBinders--;
      else return i;
    }
  }
  return -1;
}

/** Strip Lean comments — `/- … -/` blocks (incl. nested blocks, `/--` docstrings and `/-!`) and
 *  `--` line comments — replacing each with a space. Used so a `sorry` token mentioned in a
 *  docstring or comment is NOT mistaken for an unfinished proof. */
export function stripLeanComments(s: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (depth === 0 && s[i] === "'") {
      // why: a Lean char literal ('c' or '\n') containing a `"` must not be read as a string start
      // (which would swallow later `--`/`/-` and hide a real proof hole). Only consume a GENUINE
      // char literal — a lone `'` (a prime in an identifier like `x'`) falls through to normal output.
      const esc = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (esc || plain) {
        const end = esc ? i + 3 : i + 2;
        out += s.slice(i, end + 1);
        i = end;
        continue;
      }
    }
    if (depth === 0 && s[i] === '"') {
      // why: Lean comment delimiters inside string literals must not hide real proof holes.
      out += s[i];
      for (i++; i < s.length; i++) {
        out += s[i];
        if (s[i] === "\\") {
          if (i + 1 < s.length) out += s[++i];
          continue;
        }
        if (s[i] === '"') break;
      }
      continue;
    }
    if (s[i] === "/" && s[i + 1] === "-") {
      depth++;
      out += " ";
      i++;
      continue;
    }
    if (depth > 0) {
      if (s[i] === "-" && s[i + 1] === "/") {
        depth--;
        out += " ";
        i++;
      } else {
        out += s[i] === "\n" ? "\n" : " ";
      }
      continue;
    }
    if (s[i] === "-" && s[i + 1] === "-") {
      // why: line comments are stripped outside strings by the same string-aware scanner.
      out += " ";
      i += 2;
      while (i < s.length && s[i] !== "\n") i++;
      if (i < s.length) out += "\n";
      continue;
    }
    out += s[i];
  }
  return out;
}

/**
 * Mask Lean comments, strings, and character literals with spaces while preserving byte offsets
 * and newlines. Parser-like consumers can safely scan the result for declaration/delimiter tokens
 * without being fooled by `"/-"`, `"def fake"`, `-- :=`, or brackets in comments.
 */
export function maskLeanCommentsAndStrings(s: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (depth > 0) {
      if (ch === "/" && s[i + 1] === "-") {
        depth++;
        out += "  ";
        i++;
      } else if (ch === "-" && s[i + 1] === "/") {
        depth--;
        out += "  ";
        i++;
      } else out += ch === "\n" ? "\n" : " ";
      continue;
    }
    if (ch === "/" && s[i + 1] === "-") {
      depth = 1;
      out += "  ";
      i++;
      continue;
    }
    if (ch === "-" && s[i + 1] === "-") {
      out += "  ";
      i++;
      while (i + 1 < s.length && s[i + 1] !== "\n") {
        out += " ";
        i++;
      }
      continue;
    }
    if (ch === '"') {
      out += " ";
      for (i++; i < s.length; i++) {
        const q = s[i];
        out += q === "\n" ? "\n" : " ";
        if (q === "\\" && i + 1 < s.length) {
          i++;
          out += s[i] === "\n" ? "\n" : " ";
        } else if (q === '"') break;
      }
      continue;
    }
    if (ch === "'") {
      const escaped = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (escaped || plain) {
        const end = escaped ? i + 3 : i + 2;
        out += " ".repeat(end - i + 1);
        i = end;
        continue;
      }
    }
    out += ch;
  }
  return out;
}

/** Return only genuine Lean comment text, masking code, strings, and character literals while
 * preserving offsets/newlines. Metadata scanners must not treat `"-- @realizes X"` as a tag. */
export function extractLeanCommentText(s: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (depth > 0) {
      if (ch === "/" && s[i + 1] === "-") {
        depth++;
        out += "/-";
        i++;
      } else if (ch === "-" && s[i + 1] === "/") {
        depth--;
        out += "-/";
        i++;
      } else out += ch;
      continue;
    }
    if (ch === "/" && s[i + 1] === "-") {
      depth = 1;
      out += "/-";
      i++;
      continue;
    }
    if (ch === "-" && s[i + 1] === "-") {
      while (i < s.length && s[i] !== "\n") out += s[i++];
      if (i < s.length) out += "\n";
      continue;
    }
    if (ch === '"') {
      out += " ";
      for (i++; i < s.length; i++) {
        const q = s[i];
        out += q === "\n" ? "\n" : " ";
        if (q === "\\" && i + 1 < s.length) {
          i++;
          out += s[i] === "\n" ? "\n" : " ";
        } else if (q === '"') break;
      }
      continue;
    }
    if (ch === "'") {
      const escaped = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (escaped || plain) {
        const end = escaped ? i + 3 : i + 2;
        out += " ".repeat(end - i + 1);
        i = end;
        continue;
      }
    }
    out += ch === "\n" ? "\n" : " ";
  }
  return out;
}

/** True iff `s` contains a real `sorry` proof token (ignoring any `sorry` inside comments). */
export function hasRealSorry(s: string): boolean {
  return /\bsorry\b/.test(stripLeanComments(s));
}

async function leanFiles(dir: string): Promise<string[]> {
  if (!existsSync(dir)) return [];
  return (await readdir(dir, { recursive: true }))
    .map(String)
    // Exclude the paper's disposable agent workspace (`tmp/`): a scratch probe (or a
    // scratch COPY of a real file, with its `-- @node:` tag) must never be extracted
    // into the graph — a duplicate tag there would fail every refresh as "unlinked".
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .sort();
}

function namespaceByLine(raw: string): string[] {
  const codeLines = stripLeanComments(raw).split(/\r?\n/);
  const out: string[] = [];
  const nsStack: string[] = [];
  const blockStack: { kind: "namespace" | "section"; count: number }[] = [];
  for (const ln of codeLines) {
    out.push(nsStack.join("."));
    const ns = ln.match(/^\s*namespace\s+([A-Za-z0-9_'.]+)\s*$/);
    if (ns) {
      const parts = ns[1].split(".").filter(Boolean);
      nsStack.push(...parts);
      blockStack.push({ kind: "namespace", count: parts.length });
      continue;
    }
    if (/^\s*section(?:\s+[A-Za-z0-9_'.]+)?\s*$/.test(ln)) {
      blockStack.push({ kind: "section", count: 0 });
      continue;
    }
    const end = ln.match(/^\s*end(?:\s+([A-Za-z0-9_'.\s]+))?\s*$/);
    if (!end) continue;
    const named = end[1]?.trim().split(/\s+/).flatMap((s) => s.split(".")).filter(Boolean) ?? [];
    const block = blockStack.pop();
    if (block?.kind !== "namespace") continue;
    if (named.length > 0) {
      nsStack.splice(Math.max(0, nsStack.length - named.length), named.length);
      continue;
    }
    nsStack.splice(Math.max(0, nsStack.length - block.count), block.count);
  }
  return out;
}

function fullyQualifiedDeclName(rawName: string, namespace: string): string {
  if (!namespace || rawName.startsWith(`${namespace}.`)) return rawName;
  return `${namespace}.${rawName}`;
}

function shortDeclName(name: string): string {
  const parts = name.split(".");
  return parts[parts.length - 1] ?? name;
}

function namespaceSearchPath(namespace: string): string[] {
  const parts = namespace.split(".").filter(Boolean);
  const out: string[] = [];
  for (let i = parts.length; i > 0; i--) out.push(parts.slice(0, i).join("."));
  out.push("");
  return out;
}

/** Parse every `-- @node: <id>`-annotated declaration in the tree. */
export async function parseAnnotatedDecls(dir: string): Promise<ExtractedDecl[]> {
  const out: ExtractedDecl[] = [];
  for (const rel of await leanFiles(dir)) {
    const raw = await readFile(path.join(dir, rel), "utf8");
    const lines = raw.split(/\r?\n/);
    const namespaces = namespaceByLine(raw);
    for (let i = 0; i < lines.length; i++) {
      const tag = lines[i].match(NODE_TAG_RE);
      if (!tag) continue;
      // Bind this tag to the NEXT declaration header, skipping ANYTHING in between — blank lines,
      // `--` line comments, `/- … -/` (incl. `/--` docstrings, tracked across lines), `@[attr]`
      // attribute lines, and any other stray line. A `-- @node:` tag commonly sits ABOVE the decl's
      // docstring and/or attributes; skipping only blank lines (the old behaviour) silently lost
      // those decls — they never linked, their node stayed `proof.state = "sorry"`, and the loop
      // could never converge. The scan is BOUNDED by the next `@node` tag, so an orphaned tag (a
      // typo'd id with no following decl) gives up instead of mis-binding to a far-away decl.
      let j = i + 1;
      let inBlock = false;
      for (; j < lines.length; j++) {
        const ln = lines[j];
        if (inBlock) { if (ln.includes("-/")) inBlock = false; continue; }
        if (NODE_TAG_RE.test(ln)) { j = lines.length; break; } // next tag first → no decl for this tag
        if (DECL_RE.test(ln)) break;                            // found the decl header
        if (ln.trim().startsWith("/-") && !ln.includes("-/")) inBlock = true; // enter block comment
        // else: blank / line comment / attribute / stray line → keep scanning
      }
      const dm = lines[j]?.match(DECL_RE);
      if (!dm) continue;
      const namespace = namespaces[j] ?? "";
      // Bound this declaration to the NEXT declaration / @node boundary first, so a
      // `structure … where` (which has no `:=`) does not bleed its "statement" into
      // the following declarations — that over-read manufactures spurious
      // statement-uses edges between sibling bundles. Within the bounded text,
      // statement = up to `:=`; body = from `:=` on (a structure has no body).
      let end = j + 1;
      while (end < lines.length && !NODE_TAG_RE.test(lines[end]) && !DECL_RE.test(lines[end])) end++;
      const declText = lines.slice(j, end).join("\n");
      const cut = topLevelAssignIndex(declText);
      const body = cut >= 0 ? declText.slice(cut) : "";
      out.push({
        nodeId: tag[1],
        declKind: dm[1],
        declName: fullyQualifiedDeclName(dm[2], namespace),
        namespace,
        file: rel,
        statement: (cut >= 0 ? declText.slice(0, cut) : declText).trim(),
        hasSorry: hasRealSorry(cut >= 0 ? body : declText),
      });
    }
  }
  return out;
}

export interface ExtractResult {
  graph: FormalizationGraph;
  hashes: Record<string, string>;
  unlinked: { id: string; decl_name: string; file: string }[];
}

/**
 * Refresh the Lean-derived fields of `graph` from the source tree:
 *  - link annotated decls to their nodes (lean.decl_name/file)
 *  - update proof state (sorry detection)
 *  - rebuild ALL `statement-uses` edges (source "extracted"); declared edges untouched
 *  - return a fresh statement hash per linked node (caller decides when to markPassed)
 *  - report annotated decls with no matching node as `unlinked`
 */
export async function extractFromLean(graph: FormalizationGraph, leanDir: string): Promise<ExtractResult> {
  const decls = await parseAnnotatedDecls(leanDir);
  const seenDeclByNode = new Map<string, ExtractedDecl>();
  const duplicateDecls: ExtractedDecl[] = [];
  const duplicateIds = new Set<string>();
  for (const d of decls) {
    const first = seenDeclByNode.get(d.nodeId);
    if (!first) {
      seenDeclByNode.set(d.nodeId, d);
      continue;
    }
    if (!duplicateIds.has(d.nodeId)) {
      duplicateDecls.push(first);
      duplicateIds.add(d.nodeId);
    }
    duplicateDecls.push(d);
  }
  if (duplicateDecls.length > 0) {
    // One graph node has exactly one canonical Lean declaration. Companion declarations are
    // allowed, but must remain untagged; accepting duplicate anchors makes graph coverage and
    // proof state depend silently on source order.
    return {
      graph,
      hashes: {},
      unlinked: duplicateDecls.map((d) => ({
        id: d.nodeId,
        decl_name: d.declName,
        file: d.file,
      })),
    };
  }
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const nodeByDeclName = new Map<string, string | null>();
  const addDeclBinding = (declName: string, nodeId: string): void => {
    const prev = nodeByDeclName.get(declName);
    // why: namespace-qualified duplicates must not silently pick the last node.
    nodeByDeclName.set(declName, prev && prev !== nodeId ? null : nodeId);
  };
  for (const d of decls) if (byId.has(d.nodeId)) addDeclBinding(d.declName, d.nodeId);
  // Also resolve against nodes that already carry a preset lean.decl_name (e.g.
  // library-backed nodes pointing at an external Mathlib/Causalean decl, which
  // therefore carry no `-- @node:` annotation). This lets a statement mentioning
  // that external name draw a statement-uses edge to its node.
  for (const n of graph.nodes) {
    if (n.lean.decl_name) addDeclBinding(n.lean.decl_name, n.id);
  }
  // Uniform-variant aliases. An assumption predicate `Foo` (a per-law condition) commonly has a
  // class-uniform companion `FooUnif` (`∃ uniform constants, ∀ law P, …`) that a downstream lemma
  // takes as an explicit SIGNATURE hypothesis. That binder IS the assumption stated uniformly over
  // the class — exactly how the paper's assumption environment reads — so a statement mentioning
  // `FooUnif` must draw a statement-uses edge to `Foo`'s node (otherwise the rendered lemma silently
  // omits the hypothesis and `\ref`s only the lemmas that consume it). Register the alias for every
  // assumption node; it is inert unless `FooUnif` actually appears as a token, and never shadows a
  // real node already named `FooUnif`.
  for (const [declName, nodeId] of [...nodeByDeclName]) {
    if (nodeId === null) continue;
    if (byId.get(nodeId)?.kind !== "assumption") continue;
    const unif = `${declName}Unif`;
    if (!nodeByDeclName.has(unif)) addDeclBinding(unif, nodeId);
  }
  const shortNameAliases = new Map<string, string | null>();
  for (const [declName, nodeId] of nodeByDeclName) {
    if (nodeId === null) continue;
    const short = shortDeclName(declName);
    const prev = shortNameAliases.get(short);
    // why: unqualified references are kept only when they are not namespace-ambiguous.
    shortNameAliases.set(short, prev && prev !== nodeId ? null : nodeId);
  }
  const resolveDeclRef = (ref: string, namespace: string): string | undefined => {
    const exact = nodeByDeclName.get(ref);
    if (exact) return exact;
    if (ref.includes(".")) {
      for (const ns of namespaceSearchPath(namespace)) {
        if (!ns) continue;
        const scoped = nodeByDeclName.get(`${ns}.${ref}`);
        if (scoped) return scoped;
      }
      return undefined;
    }
    for (const ns of namespaceSearchPath(namespace)) {
      if (!ns) continue;
      const scoped = nodeByDeclName.get(`${ns}.${ref}`);
      if (scoped) return scoped;
    }
    return shortNameAliases.get(ref) ?? undefined;
  };

  const nodes = graph.nodes.map((n) =>
    isUndeliveredNode(n)
      ? {
          ...n,
          lean: { decl_name: null, file: null },
          proof: { state: "sorry" as const, sorry_count: 0 },
          review: { status: "unreviewed" as const, passed_hash: null, note: n.delivery?.reason },
        }
      : { ...n },
  );
  const hashes: Record<string, string> = {};
  const unlinked: ExtractResult["unlinked"] = [];

  for (const d of decls) {
    const target = nodes.find((n) => n.id === d.nodeId);
    if (!target) {
      unlinked.push({ id: d.nodeId, decl_name: d.declName, file: d.file });
      continue;
    }
    if (isUndeliveredNode(target)) {
      unlinked.push({ id: d.nodeId, decl_name: d.declName, file: d.file });
      continue;
    }
    target.lean = { decl_name: d.declName, file: d.file };
    target.proof = { state: d.hasSorry ? "sorry" : "complete", sorry_count: d.hasSorry ? 1 : 0 };
    hashes[d.nodeId] = statementHash(d.statement);
  }

  // Rebuild statement-uses edges: a node's statement references another node's decl_name.
  const declaredEdges = graph.edges.filter((e) => e.source === "declared");
  const stmtEdges: GraphEdge[] = [];
  const seen = new Set<string>();
  for (const d of decls) {
    if (!byId.has(d.nodeId) || isUndeliveredNode(byId.get(d.nodeId)!)) continue;
    for (const id of identifiers(d.statement)) {
      const toNode = resolveDeclRef(id, d.namespace);
      if (toNode && toNode !== d.nodeId) {
        const key = `${d.nodeId}->${toNode}`;
        if (!seen.has(key)) {
          seen.add(key);
          stmtEdges.push({ kind: "statement-uses", from: d.nodeId, to: toNode, source: "extracted" });
        }
      }
    }
  }

  return { graph: { ...graph, nodes, edges: [...declaredEdges, ...stmtEdges] }, hashes, unlinked };
}
