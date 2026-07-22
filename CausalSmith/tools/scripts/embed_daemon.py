# tools/scripts/embed_daemon.py
#
# Warm query-embedding daemon. Holds the bge model in memory and serves query
# vectors over a unix-domain socket, so repeated retrieval queries pay the ~30 s
# sentence-transformers model load ONCE (on first request) instead of per call.
#
# Protocol (one request per connection):
#   client → server : one JSON line  {"texts": ["...", "..."]}\n
#   server → client : 8-byte header  <int32 n><int32 dim>  then n*dim*4 bytes f32
#                     (n = -1 signals a server-side error; client falls back inline)
#
# Vectors are byte-identical to scripts/embed_text.py's inline path: SAME model,
# SAME CLS pooling, SAME query prefix, SAME normalization — the daemon must live in
# the exact vector space as the precomputed decl embeddings (embed_library.py).
#
# The daemon idle-exits after IDLE_TIMEOUT so it never lingers forever, and refuses
# to double-bind (a second daemon detecting a live socket exits immediately).
import os
os.environ.setdefault("HF_HUB_OFFLINE", "1")        # cluster is offline; cached weights only
os.environ.setdefault("TRANSFORMERS_OFFLINE", "1")
import sys, socket, json, struct
import numpy as np

MODEL = "BAAI/bge-large-en-v1.5"  # MUST match embed_library.py / embed_text.py (same vector space)
QUERY_PREFIX = "Represent this sentence for searching relevant passages: "  # bge query convention
IDLE_TIMEOUT = 1800.0  # seconds with no request before the daemon exits (30 min)
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))


def load_model(model_id):
    from sentence_transformers import SentenceTransformer, models
    # a repo-relative model dir (as stored in the meta) resolves against ROOT
    resolved = model_id if os.path.isabs(model_id) else os.path.join(ROOT, model_id)
    if os.path.isdir(resolved) and os.path.exists(os.path.join(resolved, "modules.json")):
        return SentenceTransformer(resolved)  # a saved (fine-tuned) model carries its pooling cfg
    word = models.Transformer(model_id)  # cached bge lacks ST pooling cfg → set CLS explicitly
    pool = models.Pooling(word.get_word_embedding_dimension(),
                          pooling_mode_cls_token=True, pooling_mode_mean_tokens=False)
    return SentenceTransformer(modules=[word, pool])


def recv_line(conn):
    buf = bytearray()
    while b"\n" not in buf:
        chunk = conn.recv(65536)
        if not chunk:
            break
        buf += chunk
    return bytes(buf)


def main():
    if len(sys.argv) < 2:
        print("usage: embed_daemon.py <socket_path> [idle_timeout_s] [model_path]", file=sys.stderr)
        sys.exit(2)
    sock_path = sys.argv[1]
    idle = float(sys.argv[2]) if len(sys.argv) > 2 else IDLE_TIMEOUT
    model_id = sys.argv[3] if len(sys.argv) > 3 else MODEL

    # Already serving? Then this spawn is redundant — exit before the expensive load.
    if os.path.exists(sock_path):
        probe = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        try:
            probe.connect(sock_path)
            probe.close()
            return  # a live daemon owns this socket
        except OSError:
            try:
                os.unlink(sock_path)  # stale socket file from a dead daemon
            except OSError:
                pass
        finally:
            try:
                probe.close()
            except OSError:
                pass

    model = load_model(model_id)  # ~30 s, once
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(sock_path)
    srv.listen(16)
    srv.settimeout(idle)
    print(f"embed_daemon ready on {sock_path}", file=sys.stderr)

    while True:
        try:
            conn, _ = srv.accept()
        except socket.timeout:
            break  # idle → exit
        try:
            raw = recv_line(conn).decode("utf-8").strip()
            if not raw:  # health-check probe (connect + close, no payload) — answer quietly
                conn.sendall(struct.pack("<ii", 0, 0))
                conn.close()
                continue
            req = json.loads(raw)
            texts = req.get("texts", [])
            if texts:
                emb = model.encode([QUERY_PREFIX + t for t in texts],
                                   normalize_embeddings=True, batch_size=32)
                arr = np.asarray(emb, dtype=np.float32)
                n, dim = arr.shape
            else:
                arr = np.zeros((0, 0), dtype=np.float32)
                n, dim = 0, 0
            conn.sendall(struct.pack("<ii", n, dim))
            conn.sendall(arr.tobytes())
        except Exception as e:  # noqa: BLE001 — never crash the daemon on one bad request
            print(f"embed_daemon request error: {e}", file=sys.stderr)
            try:
                conn.sendall(struct.pack("<ii", -1, 0))
            except OSError:
                pass
        finally:
            try:
                conn.close()
            except OSError:
                pass

    try:
        os.unlink(sock_path)
    except OSError:
        pass


if __name__ == "__main__":
    main()
