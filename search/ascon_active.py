#!/usr/bin/env python3
"""Search differential characteristics of the Ascon permutation with few active S-boxes (SAT).

State: 5 rows x 64 columns. One round = S-box layer (5-bit S-box per column) -> linear layer
(Sigma per row). The number of active S-boxes of an R-round characteristic is the number of
columns with a non-zero input difference in S-box layers 0..R-1. Round constants do not affect
differences and are omitted.

Usage:
  ascon_active.py --rounds 3 --search                 minimum for 1..R rounds (sanity check)
  ascon_active.py --rounds 4 --k 42 --bounds 1,4,15   is there a characteristic with <= k?
  ascon_active.py --rounds 4 --k 60 --bounds 1,4,15 --descend
      find one with <= k, then repeatedly ask for one fewer (incremental, under assumptions)
  (--bounds: known lower bounds for 1, 2, ... rounds, used for Matsui-type pruning)
"""
import argparse
import json
import time

from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

W = 64
ROT = [(19, 28), (61, 39), (1, 6), (10, 17), (7, 41)]


def sbox(v):
    """The S-box, computed from the bitsliced description of the specification
    (v = x0 x1 x2 x3 x4 with x0 the most significant bit)."""
    x = [(v >> (4 - i)) & 1 for i in range(5)]
    x[0] ^= x[4]; x[4] ^= x[3]; x[2] ^= x[1]
    t = [(1 - x[i]) & x[(i + 1) % 5] for i in range(5)]
    for i in range(5):
        x[i] ^= t[(i + 1) % 5]
    x[1] ^= x[0]; x[0] ^= x[4]; x[3] ^= x[2]; x[2] ^= 1
    return sum(b << (4 - i) for i, b in enumerate(x))


SBOX = [sbox(v) for v in range(32)]
DDT = [[0] * 32 for _ in range(32)]
for a in range(32):
    for v in range(32):
        DDT[a][SBOX[v] ^ SBOX[v ^ a]] += 1
POSSIBLE = {(a, b) for a in range(32) for b in range(32) if DDT[a][b]}


def sbox_clauses():
    """Clauses over 10 variables (5 input, 5 output) forbidding every impossible
    (input difference, output difference). Each blocking clause is shortened greedily
    as long as it still excludes no possible pair."""
    def bits(a, b):
        return [(a >> (4 - i)) & 1 for i in range(5)] + [(b >> (4 - i)) & 1 for i in range(5)]

    possible_bits = [bits(a, b) for a, b in POSSIBLE]
    clauses = set()
    for a in range(32):
        for b in range(32):
            if (a, b) in POSSIBLE:
                continue
            asg = bits(a, b)
            lits = list(range(10))  # clause = "some variable differs from asg"
            for j in list(lits):
                trial = [t for t in lits if t != j]
                # j can be dropped unless a possible pair agrees with asg on all of trial
                if not any(all(pb[t] == asg[t] for t in trial) for pb in possible_bits):
                    lits = trial
            clauses.add(tuple((t, asg[t]) for t in lits))
    return [list(c) for c in clauses]


SBOX_CNF = sbox_clauses()


class Model:
    def __init__(self, R):
        self.R = R
        self.pool = IDPool()
        self.cnf = CNF()
        v = self.pool.id
        # X[r][row][col]: input difference of the S-box layer of round r; Y: output difference
        self.X = [[[v(f"x{r}_{i}_{j}") for j in range(W)] for i in range(5)] for r in range(R)]
        self.Y = [[[v(f"y{r}_{i}_{j}") for j in range(W)] for i in range(5)] for r in range(R)]
        self.A = [[v(f"a{r}_{j}") for j in range(W)] for r in range(R)]
        for r in range(R):
            for j in range(W):
                ins = [self.X[r][i][j] for i in range(5)]
                outs = [self.Y[r][i][j] for i in range(5)]
                vars10 = ins + outs
                for cl in SBOX_CNF:
                    self.cnf.append([(-vars10[t] if val else vars10[t]) for t, val in cl])
                for x in ins:  # a non-zero input makes the column active
                    self.cnf.append([-x, self.A[r][j]])
            if r + 1 < R:
                self.linear(r)
        # Non-trivial characteristic; to break the rotational symmetry of the columns,
        # require column 0 of the round-0 input difference to be non-zero.
        self.cnf.append([self.X[0][i][0] for i in range(5)])

    def linear(self, r):
        for i, (s1, s2) in enumerate(ROT):
            y = self.Y[r][i]
            for j in range(W):
                # (y >>> s)_j = y_{(j+s) mod 64}
                a, b, c, d = y[j], y[(j + s1) % W], y[(j + s2) % W], self.X[r + 1][i][j]
                for m in range(16):
                    bs = [(m >> t) & 1 for t in range(4)]
                    if sum(bs) % 2 == 1:  # forbid assignments violating a^b^c^d = 0
                        self.cnf.append([(-x if t else x) for x, t in zip((a, b, c, d), bs)])

    def constrain(self, k, bounds):
        """Total number of active S-boxes <= k, plus Matsui-type window constraints.

        One sequential counter over the activity variables in round order, encoded in both
        directions: c[i][j] <=> "at least j of the first i variables are true". The count in the
        window of rounds s..e is c[end_e] - c[end_{s-1}] (Sun-Wang-Wang style).
        bounds[t] = known lower bound for t rounds (bounds[0] = 0).
        """
        R = self.R
        xs = [a for row in self.A for a in row]
        N, K = len(xs), k + 1
        T = self.pool.id("TRUE")
        self.cnf.append([T])
        c = [[None] * (K + 1) for _ in range(N + 1)]
        lit = lambda i, j: T if j <= 0 else (-T if i == 0 or j > i else c[i][j])
        for i in range(1, N + 1):
            xi = xs[i - 1]
            for j in range(1, min(i, K) + 1):
                c[i][j] = self.pool.id(f"c{i}_{j}")
                p, q, z = lit(i - 1, j), lit(i - 1, j - 1), c[i][j]
                # z <=> p or (xi and q)
                self.cnf.extend([[-p, z], [-xi, -q, z], [-z, p, xi], [-z, p, q]])
        self.count = c  # used as assumptions by the descending search
        if N >= K:
            self.cnf.append([-c[N][K]])
        b = [W * t for t in range(R + 1)]
        for s in range(R):
            for e in range(s, R):
                if s == 0 and e == R - 1:
                    continue
                pre, post = s, R - 1 - e
                if pre >= len(bounds) or post >= len(bounds):
                    continue
                m = k - bounds[pre] - bounds[post]
                if m < 0:
                    self.cnf.append([])
                    return
                lo, hi = b[s], b[e + 1]
                # count(hi) - count(lo) <= m  <=>  for all j: count(hi) >= j+m+1 -> count(lo) >= j+1
                for j in range(0, K):
                    t = j + m + 1
                    if t > K or t > hi:
                        break
                    self.cnf.append([-lit(hi, t), lit(lo, j + 1)])

    def decode(self, model):
        pos = set(l for l in model if l > 0)
        word = lambda vec: sum(1 << j for j, x in enumerate(vec) if x in pos)
        return [{"in": [f"{word(self.X[r][i]):016x}" for i in range(5)],
                 "out": [f"{word(self.Y[r][i]):016x}" for i in range(5)]} for r in range(self.R)]


def check_trail(trail):
    """Re-check a characteristic with the DDT and the linear layer, independently of the SAT
    model. Returns (number of active S-boxes, weight = -log2 probability)."""
    from math import log2
    mask = (1 << W) - 1
    rotr = lambda x, s: ((x >> s) | (x << (W - s))) & mask
    active, weight = 0, 0.0
    for r, rd in enumerate(trail):
        xin = [int(h, 16) for h in rd["in"]]
        yout = [int(h, 16) for h in rd["out"]]
        for j in range(W):
            a = sum(((xin[i] >> j) & 1) << (4 - i) for i in range(5))
            b = sum(((yout[i] >> j) & 1) << (4 - i) for i in range(5))
            if DDT[a][b] == 0:
                raise ValueError(f"round {r} col {j}: impossible S-box transition {a:02x}->{b:02x}")
            if a:
                active += 1
                weight += 5 - log2(DDT[a][b])
        if r + 1 < len(trail):
            nxt = [int(h, 16) for h in trail[r + 1]["in"]]
            for i, (s1, s2) in enumerate(ROT):
                if nxt[i] != yout[i] ^ rotr(yout[i], s1) ^ rotr(yout[i], s2):
                    raise ValueError(f"round {r}: linear layer mismatch")
    return active, weight


def solve(R, k, bounds, solver_name):
    t0 = time.time()
    m = Model(R)
    m.constrain(k, bounds)
    with Solver(name=solver_name, bootstrap_with=m.cnf.clauses) as s:
        ok = s.solve()
        dt = time.time() - t0
        if ok:
            trail = m.decode(s.get_model())
            active, weight = check_trail(trail)
            return ok, dt, trail, active, weight
        return ok, dt, None, None, None


def descend(R, k_start, bounds, solver_name, stop):
    """Find a characteristic with <= k_start active S-boxes; each time one is found, solve again
    under the assumption "one fewer". The Matsui-type constraints are built for k_start (they are
    merely weaker, and still sound, for smaller k)."""
    m = Model(R)
    m.constrain(k_start, bounds)
    N = R * W
    t0 = time.time()
    with Solver(name=solver_name, bootstrap_with=m.cnf.clauses) as s:
        assume = []
        while True:
            ok = s.solve(assumptions=assume)
            dt = round(time.time() - t0, 1)
            if not ok:
                print(json.dumps({"R": R, "below": best, "sat": False, "sec": dt}), flush=True)
                return
            trail = m.decode(s.get_model())
            active, weight = check_trail(trail)
            best = active
            print(json.dumps({"R": R, "active": active, "weight": weight, "sec": dt, "trail": trail}), flush=True)
            if active <= stop:
                return
            # next: at most active - 1  <=>  c[N][active] is false
            assume = [-m.count[N][active]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rounds", type=int, required=True)
    ap.add_argument("--k", type=int)
    ap.add_argument("--descend", action="store_true", help="tighten from --k one S-box at a time")
    ap.add_argument("--stop", type=int, default=0, help="stop the descending search at this count")
    ap.add_argument("--bounds", default="", help="known lower bounds for 1, 2, ... rounds (comma-separated)")
    ap.add_argument("--search", action="store_true")
    ap.add_argument("--solver", default="cadical195")
    args = ap.parse_args()
    known = [0] + [int(t) for t in args.bounds.split(",") if t != ""]

    if args.descend:
        descend(args.rounds, args.k, known, args.solver, args.stop)
    elif args.search:
        bounds = [0]
        for R in range(1, args.rounds + 1):
            k = bounds[-1] + 1
            while True:
                ok, dt, trail, active, weight = solve(R, k, bounds, args.solver)
                print(json.dumps({"R": R, "k": k, "sat": ok, "sec": round(dt, 1)}), flush=True)
                if ok:
                    print(json.dumps({"R": R, "min_active": active, "weight": weight, "trail": trail}), flush=True)
                    bounds.append(active)
                    break
                k += 1
        print(json.dumps({"bounds": bounds}), flush=True)
    else:
        ok, dt, trail, active, weight = solve(args.rounds, args.k, known, args.solver)
        print(json.dumps({"R": args.rounds, "k": args.k, "sat": ok, "sec": round(dt, 1),
                          "active": active, "weight": weight, "trail": trail}), flush=True)


if __name__ == "__main__":
    main()
