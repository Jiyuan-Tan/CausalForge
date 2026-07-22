// Best-effort resolver for the source text a `gate_class:"cited"` node is matched
// against at F2.5. Policy (user-confirmed): VERBATIM-FIRST — the cite: node's
// `verbatim_statement` is the reliable match target (mode "attested"); when absent
// and an `arxiv` handle is present we best-effort fetch the e-print tex (mode
// "fetched"); if neither yields text the node is "unverifiable" (invalid for new
// runs, flagged-not-blocking for the migration carve-out). The fetch is injectable
// so the unit tests never touch the network.
import { gunzipSync } from "node:zlib";

import type { Citation } from "./plan/schema.js";

/** Minimal source-of-record shape shared by D0.5 core review and F2.5/F4. */
export type ResolvableCitation = Pick<Citation, "id" | "locator"> &
  Partial<Pick<Citation, "verbatim_statement" | "arxiv" | "doi" | "url">>;

export type CitedMatchMode = "attested" | "fetched" | "unverifiable";

export interface CitedMatchTarget {
  /** The exact statement text the Lean `def` must encode (empty when unverifiable). */
  text: string;
  /** Where `text` came from. */
  mode: CitedMatchMode;
  /** Human-readable provenance for logs / the prompt header. */
  detail: string;
}

/** Network seam — defaults to the global fetch; tests inject a stub. */
export type FetchBytes = (url: string) => Promise<Uint8Array | null>;

const defaultFetchBytes: FetchBytes = async (url) => {
  try {
    const res = await fetch(url);
    if (!res.ok) return null;
    return new Uint8Array(await res.arrayBuffer());
  } catch {
    return null;
  }
};

/** True when the bytes are a gzip stream (magic 0x1f 0x8b). */
function isGzip(b: Uint8Array): boolean {
  return b.length > 2 && b[0] === 0x1f && b[1] === 0x8b;
}

/** True when the buffer is a (ustar) tar archive: magic "ustar" at offset 257. */
function isTar(b: Uint8Array): boolean {
  if (b.length < 262) return false;
  return String.fromCharCode(b[257], b[258], b[259], b[260], b[261]) === "ustar";
}

/** Minimal ustar reader: concatenate the contents of every `.tex` member. */
function texFromTar(buf: Uint8Array): string {
  const dec = new TextDecoder("utf-8", { fatal: false });
  let out = "";
  let off = 0;
  while (off + 512 <= buf.length) {
    const header = buf.subarray(off, off + 512);
    // Empty (all-zero) header block → end of archive.
    if (header.every((x) => x === 0)) break;
    const name = dec.decode(header.subarray(0, 100)).replace(/\0.*$/, "").trim();
    const sizeOctal = dec.decode(header.subarray(124, 136)).replace(/\0.*$/, "").trim();
    const size = parseInt(sizeOctal, 8) || 0;
    const dataStart = off + 512;
    if (name.endsWith(".tex")) out += `${dec.decode(buf.subarray(dataStart, dataStart + size))}\n`;
    // Advance past data, rounded up to the next 512-byte boundary.
    off = dataStart + Math.ceil(size / 512) * 512;
  }
  return out;
}

/** Decode an arXiv e-print payload (gzip of either a tar or a single .tex) to tex. */
function decodeEprint(bytes: Uint8Array): string | null {
  let buf = bytes;
  if (isGzip(buf)) {
    try {
      buf = new Uint8Array(gunzipSync(buf));
    } catch {
      return null;
    }
  }
  if (isTar(buf)) {
    const tex = texFromTar(buf);
    return tex.trim() ? tex : null;
  }
  // Single uncompressed source file — accept only if it looks like TeX.
  const text = new TextDecoder("utf-8", { fatal: false }).decode(buf);
  return /\\(begin|documentclass|section|lemma|theorem)/.test(text) ? text : null;
}

/**
 * Resolve the match target for one cited citation. Verbatim-first; arXiv fetch is
 * best-effort and only used when no verbatim statement is supplied.
 */
export async function resolveCitedTarget(
  c: ResolvableCitation,
  fetchBytes: FetchBytes = defaultFetchBytes,
): Promise<CitedMatchTarget> {
  const verbatim = c.verbatim_statement?.trim();
  if (verbatim) {
    return { text: verbatim, mode: "attested", detail: `attested verbatim statement @ ${c.locator}` };
  }
  if (c.arxiv) {
    const bytes = await fetchBytes(`https://arxiv.org/e-print/${c.arxiv}`);
    const tex = bytes ? decodeEprint(bytes) : null;
    if (tex) {
      return { text: tex, mode: "fetched", detail: `arXiv:${c.arxiv} e-print tex @ ${c.locator}` };
    }
  }
  if (!c.arxiv && (c.doi || c.url)) {
    return {
      text: "",
      mode: "unverifiable",
      // why: DOI/URL fetching is intentionally unsupported; require an attested target instead.
      detail: `citation ${c.id} has doi/url but no arXiv fetch; add verbatim_statement for ${c.locator}`,
    };
  }
  return {
    text: "",
    mode: "unverifiable",
    detail: `no verbatim statement and no fetchable source for ${c.id}`,
  };
}
