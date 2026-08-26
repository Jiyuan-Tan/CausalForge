/**
 * Reader attestations — the client half.
 *
 * An attestation is one reader saying, of one statement in one paper: "I read
 * this statement and its proof and certify them correct, taking the results the
 * proof invokes as given." It is deliberately MODULAR — nobody is asked to
 * vouch for the whole paper — and it is public: the GitHub handle is shown on
 * the node.
 *
 * Storage is the comments worker (`/api/attestations`), which is also where the
 * GitHub sign-in already lives, so a reader who can comment can attest with no
 * extra ceremony. Unlike a comment, a write goes THROUGH the worker rather than
 * browser → api.github.com: an attestation is our own record, not a GitHub
 * object, so the worker authenticates the visitor's token, resolves the login
 * itself, and keys the record by that. A reader can therefore only ever create
 * or withdraw their OWN mark.
 *
 * Everything here is DOM-free and network-only, so the controller's logic can
 * be tested against a stubbed `fetch`.
 */

/** One reader's mark on one statement. */
export interface Attestation {
  objId: string;
  login: string;
  avatarUrl: string | null;
  at: string;
}

/** How many marks a page will hold, however many the server sends. */
const MAX_ATTESTATIONS = 2000;

const isStr = (v: unknown): v is string => typeof v === "string" && v.length > 0;

/** Shape one wire row; anything malformed is dropped rather than rendered. */
function shape(raw: unknown): Attestation | null {
  if (!raw || typeof raw !== "object") return null;
  const r = raw as Record<string, unknown>;
  if (!isStr(r.objId) || !isStr(r.login)) return null;
  return {
    objId: r.objId,
    login: r.login,
    avatarUrl: isStr(r.avatarUrl) ? r.avatarUrl : null,
    at: isStr(r.at) ? r.at : "",
  };
}

export function shapeAll(raw: unknown): Attestation[] {
  if (!Array.isArray(raw)) return [];
  const out: Attestation[] = [];
  for (const item of raw.slice(0, MAX_ATTESTATIONS)) {
    const a = shape(item);
    if (a) out.push(a);
  }
  return out;
}

/** objId → the readers who have attested it, in arrival order. */
export function groupByObj(list: Attestation[]): Map<string, Attestation[]> {
  const out = new Map<string, Attestation[]>();
  for (const a of list) {
    const bucket = out.get(a.objId);
    if (bucket) bucket.push(a);
    else out.set(a.objId, [a]);
  }
  return out;
}

async function readError(res: Response): Promise<string> {
  try {
    const data = (await res.json()) as { error?: unknown };
    if (isStr(data.error)) return data.error;
  } catch {
    /* fall through to the status */
  }
  return `HTTP ${res.status}`;
}

/** Read every attestation on a paper. Anonymous — no token involved. */
export async function listAttestations(worker: string, paper: string): Promise<Attestation[]> {
  const res = await fetch(
    `${worker}/api/attestations?paper=${encodeURIComponent(paper)}`,
    { credentials: "omit" },
  );
  if (!res.ok) throw new Error(await readError(res));
  const data = (await res.json()) as { attestations?: unknown };
  return shapeAll(data.attestations);
}

async function write(
  method: "POST" | "DELETE",
  worker: string,
  paper: string,
  objId: string,
  token: string,
): Promise<Record<string, unknown>> {
  const res = await fetch(`${worker}/api/attestations`, {
    method,
    credentials: "omit",
    headers: { Authorization: `Bearer ${token}`, "Content-Type": "application/json" },
    body: JSON.stringify({ paper, objId }),
  });
  if (!res.ok) throw new Error(await readError(res));
  return (await res.json().catch(() => ({}))) as Record<string, unknown>;
}

/** Record the signed-in reader's attestation. Idempotent server-side. */
export async function createAttestation(
  worker: string,
  paper: string,
  objId: string,
  token: string,
): Promise<Attestation> {
  const data = await write("POST", worker, paper, objId, token);
  return (
    shape({ objId, ...data }) ?? { objId, login: "you", avatarUrl: null, at: "" }
  );
}

/** Withdraw the signed-in reader's own attestation. */
export async function withdrawAttestation(
  worker: string,
  paper: string,
  objId: string,
  token: string,
): Promise<void> {
  await write("DELETE", worker, paper, objId, token);
}
