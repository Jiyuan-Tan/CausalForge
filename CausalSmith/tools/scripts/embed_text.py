import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import sys, argparse, socket, json, struct, hashlib, subprocess, time, tempfile
import numpy as np

MODEL = "BAAI/bge-large-en-v1.5"  # default / fallback
QUERY_PREFIX = "Represent this sentence for searching relevant passages: "  # bge query convention
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))

# The warm daemon (scripts/embed_daemon.py) holds the model in memory so repeated queries
# skip the ~30 s load. This client prefers it, spawning it on first use, and falls back to
# an inline model load if the daemon is unavailable — so retrieval never breaks.


def resolve_model():
    """The query encoder MUST match the corpus encoder — read whatever built the embeddings
    (library_embeddings.meta.json `model`), falling back to the default bge name."""
    try:
        meta = json.load(open(os.path.join(ROOT, "doc", "library_embeddings.meta.json")))
        return meta.get("model") or MODEL
    except Exception:  # noqa: BLE001
        return MODEL


def load_st_model(model_id):
    from sentence_transformers import SentenceTransformer, models
    # a repo-relative model dir (as stored in the meta) resolves against ROOT
    resolved = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    if os.path.isdir(resolved) and os.path.exists(os.path.join(resolved, "modules.json")):
        return SentenceTransformer(resolved)  # a saved (fine-tuned) model carries its pooling cfg
    word = models.Transformer(model_id)
    pool = models.Pooling(word.get_word_embedding_dimension(), pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


def sock_path(model_id):
    # Keyed by repo root + model so distinct checkouts / models don't share a daemon.
    h = hashlib.sha1((ROOT + "|" + model_id).encode()).hexdigest()[:12]
    return os.path.join(tempfile.gettempdir(), f"causalean-embed-{h}.sock")


def _recvn(conn, n):
    buf = bytearray()
    while len(buf) < n:
        chunk = conn.recv(min(65536, n - len(buf)))
        if not chunk:
            return None
        buf += chunk
    return bytes(buf)


def try_daemon(texts, path, model_id, spawn_wait=90.0):
    """Return an (n, dim) float32 array via the warm daemon, or None to fall back inline."""
    def connect():
        c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        c.settimeout(180.0)
        c.connect(path)
        return c

    conn = None
    try:
        conn = connect()
    except OSError as e:
        # A stale socket file (the daemon died but left its .sock behind) refuses the
        # connection with ECONNREFUSED. Unlink it so the freshly-spawned daemon binds
        # cleanly, and so no later client blocks on a dead endpoint.
        if isinstance(e, ConnectionRefusedError) and os.path.exists(path):
            try:
                os.unlink(path)
            except OSError:
                pass
        # No daemon yet: spawn it detached (on this exact model), then poll until it has loaded.
        daemon = os.path.join(os.path.dirname(__file__), "embed_daemon.py")
        if not os.path.exists(daemon):
            return None
        try:
            subprocess.Popen([sys.executable, daemon, path, "1800", model_id],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                             start_new_session=True)
        except Exception:  # noqa: BLE001
            return None
        deadline = time.time() + spawn_wait
        while time.time() < deadline:
            time.sleep(1.0)
            try:
                conn = connect()
                break
            except OSError:
                continue
        if conn is None:
            return None

    try:
        conn.sendall((json.dumps({"texts": texts}) + "\n").encode("utf-8"))
        head = _recvn(conn, 8)
        if head is None or len(head) < 8:
            return None
        n, dim = struct.unpack("<ii", head)
        if n < 0 or dim <= 0 or n != len(texts):
            return None
        body = _recvn(conn, n * dim * 4)
        if body is None or len(body) < n * dim * 4:
            return None
        return np.frombuffer(body, dtype=np.float32).reshape(n, dim)
    except OSError:
        return None
    finally:
        try:
            conn.close()
        except OSError:
            pass


def inline(texts, model_id):
    m = load_st_model(model_id)
    return np.asarray(m.encode([QUERY_PREFIX + t for t in texts], normalize_embeddings=True, batch_size=32),
                      dtype=np.float32)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--no-daemon", action="store_true", help="skip the warm daemon; load the model inline")
    ap.add_argument("--model-path", default=None, help="override the encoder (default: read from embeddings meta)")
    args = ap.parse_args()
    lines = [ln.rstrip("\n") for ln in sys.stdin]
    model_id = args.model_path or resolve_model()

    emb = None
    via = "inline"
    if not args.no_daemon and lines:
        emb = try_daemon(lines, sock_path(model_id), model_id)
        if emb is not None:
            via = "daemon"
    if emb is None:
        emb = inline(lines, model_id)

    np.asarray(emb, dtype=np.float32).tofile(args.out)
    print(f"embedded {len(lines)} queries via {via} -> {args.out}", file=sys.stderr)


if __name__ == "__main__":
    main()
