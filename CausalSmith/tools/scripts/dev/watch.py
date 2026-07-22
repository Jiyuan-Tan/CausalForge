import json, os, time, sys

BASE = "d:/Stat/Causality/Lean Project/AutoID/CausalSmith/doc/research"
RUNS = [
    "pid_emsm_breakdown_frontier",
    "q_lpdid_bjs_frontier",
    "stat_sa_cate_pointwise",
    "pid_gpn_continuous_rho",
    "pid_bunching_friction_breakdown",
]
MAX_SECONDS = 600
POLL = 15

# Words in an event that mean "stop and let the human look"
ALERT_STATUS = {"error", "failed", "aborted", "abort", "blocked"}
ALERT_MSG = ("error", "escalat", "pivot", "abort", "missing_architecture",
             "spawn", "ENOENT", "exception", "traceback")

def jsonl_events(path):
    out = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    out.append(json.loads(line))
                except Exception:
                    pass
    except FileNotFoundError:
        pass
    return out

def state(run):
    p = f"{BASE}/{run}/{run}_v1_state.json"
    try:
        return json.load(open(p, "r", encoding="utf-8", errors="replace"))
    except Exception:
        return {}

def snapshot():
    rows = {}
    for r in RUNS:
        ev = jsonl_events(f"{BASE}/{r}/{r}_v1_pipeline.jsonl")
        st = state(r)
        rows[r] = {
            "n": len(ev),
            "last": ev[-1] if ev else None,
            "stage_completed": st.get("stage_completed"),
            "ckpt_pending": st.get("ckpt_pending"),
            "banked": st.get("banked"),
            "flags": {k: v for k, v in (st.get("flags") or {}).items() if v},
            "events": ev,
        }
    return rows

# Decision boundaries: D-0.5 proposal verdict, D0.5 derivation verdict
DECISION_STAGES = ("-0.5", "D-0.5", "0.5", "D0.5")

def reached_decision(row):
    return str(row["stage_completed"]) in DECISION_STAGES

def reached_d05(row):
    sc = str(row["stage_completed"])
    return sc in ("0.5", "D0.5")

def has_alert(row):
    for e in row["events"]:
        stt = str(e.get("status", "")).lower()
        msg = str(e.get("message", "")).lower()
        if stt in ALERT_STATUS:
            return f"status={stt} :: {str(e.get('message',''))[:140]}"
        if any(w in msg for w in ALERT_MSG):
            return f"msg :: {str(e.get('message',''))[:140]}"
    if row["ckpt_pending"]:
        return f"ckpt_pending={row['ckpt_pending']}"
    if row["flags"]:
        return f"flags={row['flags']}"
    return None

start = time.time()
_init = snapshot()
baseline = {r: _init[r]["n"] for r in RUNS}
# Baseline already-seen state so a restart only wakes on NEW transitions.
alerted = {r: has_alert(_init[r]) is not None for r in RUNS}
last_decision = {r: (str(_init[r]["stage_completed"]) if reached_decision(_init[r]) else None)
                 for r in RUNS}

while True:
    rows = snapshot()
    reasons = []
    for r in RUNS:
        row = rows[r]
        a = has_alert(row)
        if a and not alerted[r]:
            reasons.append(f"[ALERT] {r}: {a}")
            alerted[r] = True
        if reached_decision(row):
            sc = str(row["stage_completed"])
            if last_decision[r] != sc:
                tag = "D0.5" if reached_d05(row) else "D-0.5"
                reasons.append(f"[{tag}] {r}: stage_completed={sc} banked={row['banked']}")
                last_decision[r] = sc

    all_terminal = all(reached_d05(rows[r]) for r in RUNS)
    elapsed = time.time() - start

    if reasons or all_terminal or elapsed > MAX_SECONDS:
        print(f"WATCH EXIT after {elapsed:.0f}s")
        if reasons:
            print("TRIGGERS:")
            for x in reasons:
                print("  " + x)
        if all_terminal:
            print("ALL RUNS REACHED D0.5 OR ALERTED")
        print("\nPROGRESS:")
        for r in RUNS:
            row = rows[r]
            le = row["last"] or {}
            print(f"  {r}: events={row['n']} (was {baseline[r]}) "
                  f"stage_completed={row['stage_completed']} "
                  f"last=[{le.get('stage')}/{le.get('status')}] "
                  f"{str(le.get('message',''))[:70]}")
        sys.exit(0)
    time.sleep(POLL)
