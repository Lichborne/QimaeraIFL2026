"""Checks the circuits written by Examples/QMESweep.idr (see README).

For every file qme_N_a.py in the given directory (default: the current one), simulates the
11-qubit circuit built by modularN 4 a N on |c, 0, x, 0> for c in {0, 1} and every x < N, and
checks that it gives |c, 0, a x mod N, 0> when c = 1 and |c, 0, x, 0> when c = 0, up to 1e-9.
Registers: c (wire 0), ancilla (wire 1), x (wires 2-5), b (wires 6-10); wire 0 is the most
significant bit of a basis index. Needs NumPy.
"""
import glob, math, os, re, sys
import numpy as np

TOL, S2 = 1e-9, 1 / math.sqrt(2)

def angle(expr):
    if not re.fullmatch(r"[-+*/().0-9 ]*(np\.pi)?[-+*/().0-9 ]*", expr):
        raise ValueError("unexpected angle " + expr)
    return float(eval(expr, {"__builtins__": {}}, {"np": np}))

def parse(path):
    n, gates = None, []
    for line in open(path):
        line = line.strip()
        if m := re.fullmatch(r"qr = QuantumRegister\((\d+)\)", line): n = int(m[1])
        elif m := re.fullmatch(r"qc\.h\(qr\[(\d+)\]\)", line): gates.append(("h", int(m[1])))
        elif m := re.fullmatch(r"qc\.p\((.*), qr\[(\d+)\]\)", line): gates.append(("p", angle(m[1]), int(m[2])))
        elif m := re.fullmatch(r"qc\.cx\(qr\[(\d+)\], qr\[(\d+)\]\)", line): gates.append(("cx", int(m[1]), int(m[2])))
        elif line and not line.startswith(("qc.barrier", "import", "from", "qc = QuantumCircuit", "print(", "qc.draw(")):
            raise ValueError(f"{path}: unexpected line {line!r}")
    return n, gates

def apply(S, n, g):
    T = S.reshape([2] * n + [-1]).copy()
    if g[0] == "h":
        a, b = np.take(T, 0, axis=g[1]), np.take(T, 1, axis=g[1])
        T = np.stack([(a + b) * S2, (a - b) * S2], axis=g[1])
    elif g[0] == "p":
        idx = [slice(None)] * (n + 1); idx[g[2]] = 1
        T[tuple(idx)] *= np.exp(1j * g[1])
    else:
        c, t = g[1], g[2]
        idx = [slice(None)] * (n + 1); idx[c] = 1
        T[tuple(idx)] = np.flip(T[tuple(idx)], axis=t if t < c else t - 1)
    return T.reshape(2 ** n, -1)

def main(d):
    files = sorted(glob.glob(os.path.join(d, "qme_*.py")))
    if not files: sys.exit(f"no qme_*.py files in {d}")
    worst, bad = 0.0, []
    for f in files:
        N, a = map(int, re.fullmatch(r"qme_(\d+)_(\d+)\.py", os.path.basename(f)).groups())
        n, gates = parse(f); assert n == 11, f
        inputs = [(c, x) for c in (0, 1) for x in range(N)]
        S = np.zeros((2 ** n, len(inputs)), dtype=complex)
        E = np.zeros_like(S)
        for j, (c, x) in enumerate(inputs):
            S[c << 10 | x << 5, j] = 1
            E[c << 10 | ((a * x) % N if c else x) << 5, j] = 1
        for g in gates: S = apply(S, n, g)
        dev = np.max(np.abs(S - E)); worst = max(worst, dev)
        if dev >= TOL: bad.append(f"N={N} a={a}")
    print(f"{len(files)} circuits checked, largest amplitude error {worst:.1e}")
    if bad: sys.exit("FAILED: " + ", ".join(bad))
    print("all correct")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
