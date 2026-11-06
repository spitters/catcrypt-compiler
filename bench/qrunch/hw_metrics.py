"""Hardware-relevant figures of catq-compile's output against Qiskit transpile(optimization_level=3),
both into the basis {rx, ry, rz, cx, p} as in compare.py:

  (1) routed CX: each circuit is laid out and routed onto a device coupling map by one Qiskit pass
      manager (`generate_preset_pass_manager(optimization_level=0, layout_method="sabre",
      routing_method="sabre")`, seeds 0..SEEDS-1, the seed with fewest CX kept; level 0 runs no
      optimization, so every input meets the same router); CX count and two-qubit depth after
      routing, SWAP counted as three CX;
  (2) expected success probability (ESP) of that routed circuit from the device's published
      calibration (calib/*.json), on a native-gate model scheduled ASAP;
  (5) fault-tolerant cost of the unrouted outputs: non-Clifford rotations, T gates among them,
      rotation depth, and the estimated T-count and T-depth after Clifford+T synthesis.

Variants: `in` the input translated into the basis (Qiskit level 0, no optimization); `ours`
`VerifiedCompiler(level="2r", check=True, permutation="layout")`, the output permutation of swap
elision recorded in the layout and no swap appended; `qk` Qiskit level 3 without a coupling map
(seed 0, as compare.py), which elides swaps into its layout in the same way; `qkr` (routed table
only) Qiskit level 3 given the coupling map, its own layout, routing and post-routing optimization,
best of the same seeds. The layouts of `ours` and `qk` are dropped before routing: the output
permutation relabels the final wires and costs no gate.

Native-gate model for (2). Each maximal run of one-qubit gates on a wire is one unitary U.
IQM (Garnet, Aphrodite: native prx and cz, z rotations virtual): `cx(c,t)` is `h(t) cz h(t)`, the
Hadamards merged into the neighbouring runs; a run with |U00| = 1 is virtual, any other run is one
prx. IBM (Kolkata: native rz virtual, sx, x, cx): |U00| = 1 virtual, |U00| = 0 one x, |U00| =
1/sqrt 2 one sx, otherwise two sx; `cx` is native on both directions of every edge. Operations are
scheduled as soon as their qubits are free; T is the end of the last one.
  ESP = prod_g (1 - eps_g) * prod_{q active} exp(-t_q / T2_q)
IBM: eps_g the published gate_error (randomized benchmarking, which includes relaxation during the
gate), t_q = T - busy_q (idle time). IQM: eps_g = lambda (d - 1) / d, the average infidelity of the
published depolarizing parameter lambda on d = 2^n levels (the fake backend applies thermal
relaxation separately during every gate), t_q = T. Readout is not counted (one measurement per
active qubit on both sides).

FT model for (5): a rotation rx, ry, rz or p by theta is Clifford when theta is a multiple of pi/2,
a T gate (T-count 1) at an odd multiple of pi/4, and otherwise arbitrary, synthesized to precision
EPS by Ross-Selinger at ceil(3 log2(1/EPS)) T gates (the O(1) term taken as 0; 100 at 1e-10).
`rot_depth` is the depth over non-Clifford rotations (cx synchronises its two wires), `t_depth_est`
the same with weight 1 per T gate and T_ARB per arbitrary rotation.

usage: cd bridge && .venv/bin/python -I ../bench/qrunch/hw_metrics.py SUITE [--seeds N]
       SUITE in qsynth, qasmbench, catcrypt, qrisp; writes bench/qrunch/hw-metrics/SUITE-routed.tsv
       and SUITE-ft.tsv
       .venv/bin/python -I ../bench/qrunch/hw_metrics.py import-calib DIR
       rebuilds calib/*.json from the downloaded source files in DIR (see the README)
"""
from __future__ import annotations

import ast
import glob
import json
import math
import os
import sys
import time

import numpy as np
from qiskit import QuantumCircuit, transpile
from qiskit.transpiler import CouplingMap, generate_preset_pass_manager

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "bridge"))
sys.path.insert(0, HERE)
from catq.compiler import VerifiedCompiler  # noqa: E402
from compare import BASIS, deviation, load  # noqa: E402

OUT = os.path.join(HERE, "hw-metrics")
CALIB = os.path.join(OUT, "calib")
SEEDS = 20
EPS = 1e-10
T_ARB = math.ceil(3 * math.log2(1 / EPS))
DEVICES = ("garnet", "aphrodite", "kolkata")
H = np.array([[1, 1], [1, -1]]) / math.sqrt(2)
TOL = 1e-8


# --------------------------------------------------------------------------- calibrations

def _iqm_profile(path: str) -> dict:
    """The keyword arguments of `IQMErrorProfile(...)` and `qubit_connectivity` in a qiskit-iqm
    fake backend source file, read with `ast` (the file is not executed)."""
    tree = ast.parse(open(path).read())
    prof, conn, qubits = {}, None, None
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id == "qubit_connectivity":
                conn = ast.literal_eval(node.value)
            elif node.targets[0].id == "qubits":
                qubits = ast.literal_eval(node.value)
        if isinstance(node, ast.Call) and getattr(node.func, "id", "") == "IQMErrorProfile":
            for kw in node.keywords:
                prof[kw.arg] = ast.literal_eval(kw.value)
    idx = {q: i for i, q in enumerate(qubits)}
    (g1, e1), = prof["single_qubit_gate_depolarizing_error_parameters"].items()
    (g2, e2), = prof["two_qubit_gate_depolarizing_error_parameters"].items()
    return {
        "vendor": "iqm", "num_qubits": len(qubits),
        "edges": [[idx[a], idx[b]] for a, b in conn],
        "t1_ns": [prof["t1s"][q] for q in qubits], "t2_ns": [prof["t2s"][q] for q in qubits],
        "dep1": [e1[q] for q in qubits], "dep2": [e2[tuple(e)] for e in conn],
        "dur1_ns": prof["single_qubit_gate_durations"][g1],
        "dur2_ns": prof["two_qubit_gate_durations"][g2],
        "profile_name": prof.get("name"),
    }


def _ibm_profile(conf: str, props: str) -> dict:
    c, p = json.load(open(conf)), json.load(open(props))
    n = c["n_qubits"]
    q = [{d["name"]: d["value"] * (1000.0 if d["unit"] == "us" else 1.0) for d in qp}
         for qp in p["qubits"]]
    gates: dict[str, dict] = {}
    for g in p["gates"]:
        v = {d["name"]: d["value"] for d in g["parameters"]}
        gates[f"{g['gate']}{','.join(map(str, g['qubits']))}"] = v
    edges = sorted({tuple(sorted(e)) for e in c["coupling_map"]})
    return {
        "vendor": "ibm", "num_qubits": n, "edges": [list(e) for e in edges],
        "t1_ns": [q[i]["T1"] for i in range(n)], "t2_ns": [q[i]["T2"] for i in range(n)],
        "sx": [[gates[f"sx{i}"]["gate_error"], gates[f"sx{i}"]["gate_length"]] for i in range(n)],
        "x": [[gates[f"x{i}"]["gate_error"], gates[f"x{i}"]["gate_length"]] for i in range(n)],
        "cx": {f"{a},{b}": [gates[f"cx{a},{b}"]["gate_error"], gates[f"cx{a},{b}"]["gate_length"]]
               for a, b in c["coupling_map"]},
        "backend": p["backend_name"], "last_update_date": p["last_update_date"],
    }


SOURCES = {
    "garnet": ("https://github.com/iqm-finland/qiskit-on-iqm/blob/"
               "c41a1a9f5c77aa94e2569b359601dd733545c7b4/src/iqm/qiskit_iqm/fake_backends/"
               "fake_garnet.py"),
    "aphrodite": ("https://github.com/iqm-finland/qiskit-on-iqm/blob/"
                  "bbd2e4816bd3b57ce15df73c1dc4d19dcd222c20/src/iqm/qiskit_iqm/fake_backends/"
                  "fake_aphrodite.py"),
    "kolkata": ("https://github.com/Qiskit/qiskit-ibm-runtime/blob/"
                "2a396172c25aa2971e99b434b430177745878a53/qiskit_ibm_runtime/fake_provider/"
                "backends/kolkata/{conf,props}_kolkata.json"),
}


def import_calib(src: str) -> None:
    os.makedirs(CALIB, exist_ok=True)
    profiles = {
        "garnet": _iqm_profile(os.path.join(src, "fake_garnet.py")),
        "aphrodite": _iqm_profile(os.path.join(src, "fake_aphrodite.py")),
        "kolkata": _ibm_profile(os.path.join(src, "kolk_conf.json"),
                                os.path.join(src, "kolk_props.json")),
    }
    for name, prof in profiles.items():
        prof["source"] = SOURCES[name]
        with open(os.path.join(CALIB, name + ".json"), "w") as f:
            json.dump(prof, f, indent=1)
        print(name, prof["num_qubits"], "qubits", len(prof["edges"]), "edges")


class Device:
    def __init__(self, name: str):
        self.name = name
        self.c = json.load(open(os.path.join(CALIB, name + ".json")))
        self.n = self.c["num_qubits"]
        self.iqm = self.c["vendor"] == "iqm"
        self.cmap = CouplingMap([list(e) for e in self.c["edges"]] +
                                [[b, a] for a, b in self.c["edges"]])
        self.t2 = self.c["t2_ns"]
        if self.iqm:
            self.cz = {}
            for (a, b), lam in zip(self.c["edges"], self.c["dep2"]):
                self.cz[(a, b)] = self.cz[(b, a)] = lam * 3 / 4

    def one_q(self, q: int, a: float) -> list[tuple[float, float]]:
        """The native pulses (error, duration ns) of a one-qubit run with |U00| = a."""
        if self.iqm:
            return [(self.c["dep1"][q] / 2, self.c["dur1_ns"])]
        if a < TOL:
            return [tuple(self.c["x"][q])]
        if abs(a - 1 / math.sqrt(2)) < TOL:
            return [tuple(self.c["sx"][q])]
        return [tuple(self.c["sx"][q])] * 2

    def two_q(self, c: int, t: int) -> tuple[float, float]:
        if self.iqm:
            return self.cz[(c, t)], self.c["dur2_ns"]
        return tuple(self.c["cx"][f"{c},{t}"])


# --------------------------------------------------------------------------- metrics

def bare(qc: QuantumCircuit) -> QuantumCircuit:
    """`qc` without its layout (the output permutation relabels final wires, at no gate)."""
    out = qc.copy()
    out._layout = None
    return out


def to_basis(qc: QuantumCircuit) -> QuantumCircuit:
    return transpile(bare(qc), basis_gates=BASIS, optimization_level=0)


def two_q_depth(qc: QuantumCircuit) -> int:
    return qc.depth(lambda ins: ins.operation.num_qubits == 2)


def route(qc: QuantumCircuit, dev: Device, own_level3: bool = False) -> QuantumCircuit:
    """The fewest-CX routed circuit over seeds 0..SEEDS-1 (ties: two-qubit depth)."""
    best = None
    for s in range(SEEDS):
        if own_level3:
            r = transpile(qc, coupling_map=dev.cmap, basis_gates=BASIS, optimization_level=3,
                          seed_transpiler=s)
        else:
            pm = generate_preset_pass_manager(optimization_level=0, coupling_map=dev.cmap,
                                              basis_gates=BASIS, layout_method="sabre",
                                              routing_method="sabre", seed_transpiler=s)
            r = pm.run(qc)
        key = (r.count_ops().get("cx", 0), two_q_depth(r))
        if best is None or key < best[0]:
            best = (key, r)
    return best[1]


def esp(routed: QuantumCircuit, dev: Device) -> tuple[float, float]:
    """(ESP, duration in us) of a routed circuit on the native-gate model of the docstring."""
    pending: dict[int, np.ndarray] = {}
    ops: list[tuple[tuple[int, ...], float, float]] = []

    def push(q: int, m: np.ndarray) -> None:
        pending[q] = m @ pending.get(q, np.eye(2))

    def flush(q: int) -> None:
        u = pending.pop(q, None)
        if u is None:
            return
        a = abs(u[0, 0])
        if a > 1 - TOL:
            return
        ops.extend(((q,), e, d) for e, d in dev.one_q(q, a))

    for ins in routed.data:
        name = ins.operation.name
        qs = [routed.find_bit(b).index for b in ins.qubits]
        if name in ("barrier", "measure"):
            for q in qs:
                flush(q)
            continue
        if len(qs) == 1:
            push(qs[0], ins.operation.to_matrix())
        elif name == "cx":
            c, t = qs
            if dev.iqm:
                push(t, H)
            flush(c)
            flush(t)
            e, d = dev.two_q(c, t)
            ops.append(((c, t), e, d))
            if dev.iqm:
                push(t, H)
        else:
            raise ValueError(f"unexpected gate {name} after routing")
    for q in list(pending):
        flush(q)
    avail: dict[int, float] = {}
    busy: dict[int, float] = {}
    log_p = 0.0
    for qs, e, d in ops:
        s = max(avail.get(q, 0.0) for q in qs)
        for q in qs:
            avail[q] = s + d
            busy[q] = busy.get(q, 0.0) + d
        log_p += math.log1p(-e)
    total = max(avail.values(), default=0.0)
    for q in avail:
        t = total if dev.iqm else total - busy[q]
        log_p -= t / dev.t2[q]
    return math.exp(log_p), total / 1000.0


def angle_class(theta: float) -> str:
    k = theta / (math.pi / 4)
    r = round(k)
    if abs(k - r) > TOL:
        return "arb"
    return "clifford" if r % 2 == 0 else "t"


def ft(qc: QuantumCircuit) -> dict:
    """Non-Clifford rotation figures of a circuit in BASIS."""
    n_t = n_arb = 0
    depth = [0] * qc.num_qubits
    wdepth = [0] * qc.num_qubits
    for ins in qc.data:
        name = ins.operation.name
        qs = [qc.find_bit(b).index for b in ins.qubits]
        if name in ("barrier", "measure"):
            continue
        if name == "cx":
            m, w = max(depth[q] for q in qs), max(wdepth[q] for q in qs)
            for q in qs:
                depth[q], wdepth[q] = m, w
            continue
        if name not in ("rx", "ry", "rz", "p"):
            raise ValueError(f"unexpected gate {name}")
        cls = angle_class(float(ins.operation.params[0]))
        if cls == "clifford":
            continue
        q = qs[0]
        depth[q] += 1
        if cls == "t":
            n_t += 1
            wdepth[q] += 1
        else:
            n_arb += 1
            wdepth[q] += T_ARB
    return {"cx": qc.count_ops().get("cx", 0), "nonclifford": n_t + n_arb, "t": n_t,
            "arb": n_arb, "rot_depth": max(depth, default=0),
            "t_count_est": n_t + T_ARB * n_arb, "t_depth_est": max(wdepth, default=0)}


# --------------------------------------------------------------------------- suites

def suite_inputs(suite: str) -> list[tuple[str, QuantumCircuit]]:
    if suite == "qrisp":
        from qrisp_compare import PROGRAMS
        from catq.qrisp_adapter import to_qiskit
        out = []
        for name, f in PROGRAMS.items():
            if name.endswith("_mcm"):
                continue  # mid-circuit measurements on 153 qubits: larger than every map
            obj, kw = f()
            out.append((name, to_qiskit(obj, kw)))
        return out
    pattern = {"qsynth": "qsynth/*.qasm", "qasmbench": "qasmbench/small/*.qasm",
               "catcrypt": "catcrypt/*.qasm"}[suite]
    paths = sorted(glob.glob(os.path.join(ROOT, "bench", "qasm", pattern)))
    return [(os.path.basename(p)[:-5], load(p)) for p in paths]


VARIANTS = ("in", "ours", "qk")


def run(suite: str) -> None:
    import qiskit
    os.makedirs(OUT, exist_ok=True)
    devices = [Device(d) for d in DEVICES]
    vc = VerifiedCompiler(level="2r", check=True, permutation="layout")
    ft_head = ["circuit", "qubits", "ours_dev"] + [
        f"{v}_{k}" for v in VARIANTS
        for k in ("cx", "nonclifford", "t", "arb", "rot_depth", "t_count_est", "t_depth_est")]
    rt_head = ["circuit", "qubits", "device"] + [
        f"{v}_{k}" for v in VARIANTS + ("qkr",) for k in ("cx", "depth2", "us", "esp")]
    ft_rows, rt_rows = [], []
    print("\t".join(rt_head), flush=True)
    for name, src in suite_inputs(suite):
        ours = vc.compile(src)
        if not vc.last_report.optimized:
            ft_rows.append([name, src.num_qubits, f"refused: {vc.last_report.reason}"])
            continue
        qk = transpile(src, basis_gates=BASIS, optimization_level=3, seed_transpiler=0)
        circs = {"in": to_basis(src), "ours": to_basis(ours), "qk": to_basis(qk)}
        dev = deviation(src, ours)
        row = [name, src.num_qubits, f"{dev:.1e}"]
        for v in VARIANTS:
            row += list(ft(circs[v]).values())
        ft_rows.append(row)
        for d in devices:
            if src.num_qubits > d.n:
                continue
            r = [name, src.num_qubits, d.name]
            for v in VARIANTS + ("qkr",):
                routed = (route(src, d, own_level3=True) if v == "qkr"
                          else route(circs[v], d))
                p, us = esp(routed, d)
                r += [routed.count_ops().get("cx", 0), two_q_depth(routed), f"{us:.3f}",
                      f"{p:.4g}"]
            print("\t".join(map(str, r)), flush=True)
            rt_rows.append(r)
    vc.close()
    stamp = (f"# qiskit {qiskit.__version__}, catq-compile level 2r --check "
             f"(permutation=layout), seeds 0..{SEEDS - 1}, eps {EPS:g} (T_arb {T_ARB}), "
             f"{time.strftime('%Y-%m-%d %H:%M %Z')}\n")
    for fname, head, rows in ((f"{suite}-routed.tsv", rt_head, rt_rows),
                              (f"{suite}-ft.tsv", ft_head, ft_rows)):
        with open(os.path.join(OUT, fname), "w") as f:
            f.write(stamp)
            f.write("\t".join(head) + "\n")
            for r in rows:
                f.write("\t".join(map(str, r)) + "\n")


def _read(fname: str) -> list[dict]:
    with open(os.path.join(OUT, fname)) as f:
        lines = [ln.rstrip("\n").split("\t") for ln in f if not ln.startswith("#")]
    return [dict(zip(lines[0], r)) for r in lines[1:] if len(r) == len(lines[0])]


def summary() -> None:
    """Markdown tables over the written TSVs: per suite and device the summed routed CX and
    two-qubit depth, the median log10 ESP ratio ours/qk with wins-ties-losses (tie: under 0.001
    decades); per suite the summed FT figures."""
    print("| suite | device | n | routed CX in / ours / qk / qkr | depth2 ours / qk "
          "| median log10(ESP ours / ESP qk) | ESP ours better-equal-worse |")
    print("|---|---|---|---|---|---|---|")
    for suite in ("qsynth", "qasmbench", "catcrypt", "qrisp"):
        rows = _read(f"{suite}-routed.tsv")
        for d in DEVICES:
            rs = [r for r in rows if r["device"] == d]
            s = {k: sum(int(r[k]) for r in rs) for k in
                 ("in_cx", "ours_cx", "qk_cx", "qkr_cx", "ours_depth2", "qk_depth2")}
            lr = [math.log10(float(r["ours_esp"])) - math.log10(float(r["qk_esp"])) for r in rs]
            w = sum(x > 1e-3 for x in lr), sum(abs(x) <= 1e-3 for x in lr), sum(x < -1e-3 for x in lr)
            print(f"| {suite} | {d} | {len(rs)} | {s['in_cx']} / {s['ours_cx']} / {s['qk_cx']} / "
                  f"{s['qkr_cx']} | {s['ours_depth2']} / {s['qk_depth2']} | "
                  f"{sorted(lr)[len(lr) // 2]:+.3f} | {w[0]}-{w[1]}-{w[2]} |")
    print()
    print("| suite | n | non-Clifford rot. in / ours / qk | T gates in / ours / qk "
          "| est. T-count in / ours / qk | est. T-depth in / ours / qk |")
    print("|---|---|---|---|---|---|")
    for suite in ("qsynth", "qasmbench", "catcrypt", "qrisp"):
        rs = [r for r in _read(f"{suite}-ft.tsv") if "in_cx" in r]
        cell = []
        for k in ("nonclifford", "t", "t_count_est", "t_depth_est"):
            cell.append(" / ".join(str(sum(int(r[f"{v}_{k}"]) for r in rs)) for v in VARIANTS))
        print(f"| {suite} | {len(rs)} | " + " | ".join(cell) + " |")


if __name__ == "__main__":
    if sys.argv[1:2] == ["import-calib"]:
        import_calib(sys.argv[2])
    elif sys.argv[1:2] == ["summary"]:
        summary()
    else:
        if "--seeds" in sys.argv:
            SEEDS = int(sys.argv[sys.argv.index("--seeds") + 1])
        run(sys.argv[1])
