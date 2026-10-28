"""Generate AsconTrail.lean: definitions (AsconTrail.head.lean), a known answer of the reference
permutation (KAT), the characteristics, one witness state per round, the theorems
(AsconTrail.tail.lean), per-round witness theorems and an axiom audit.

Usage (from the repository root):
  python3 -I lean/gen/gen_lean.py <pyascon ascon.py> lean/AsconTrail.lean \
      trail42=trails/ascon_4r_42active.json trail68=trails/ascon_5r_68active.json
"""
import importlib.util, json, os, random, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "search"))
import ascon_active as AA

spec = importlib.util.spec_from_file_location("ascon_official", sys.argv[1])
A = importlib.util.module_from_spec(spec); spec.loader.exec_module(A)
random.seed(20261028)
M = (1 << 64) - 1
rc = lambda i: 0xf0 - i * 0x10 + i
col = lambda S, j: sum(((S[i] >> j) & 1) << (4 - i) for i in range(5))
st = lambda S: "⟨" + ", ".join(f"0x{w:016x}" for w in S) + "⟩"

def witness(din, dout):
    """S-box layer input (after the constant) whose active columns realise din -> dout."""
    S = [random.getrandbits(64) for _ in range(5)]
    for j in range(64):
        a, b = col(din, j), col(dout, j)
        if a:
            v = random.choice([v for v in range(32) if AA.SBOX[v] ^ AA.SBOX[v ^ a] == b])
            for i in range(5):
                S[i] = (S[i] & ~(1 << j) & M) | (((v >> (4 - i)) & 1) << j)
    return S

kat_in = [0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x8796a5b4c3d2e1f0, 0x0000000000000001]
kat_out = list(kat_in); A.ascon_permutation(kat_out, 12)

parts = []
rounds_thm = []
for arg in sys.argv[3:]:
    name, path = arg.split("=")
    trail = json.load(open(path))["trail"]
    rows = [(([int(h, 16) for h in r["in"]]), [int(h, 16) for h in r["out"]]) for r in trail]
    parts.append(f"def {name} : List Rd := [\n" + ",\n".join(f"  ⟨{st(i)}, {st(o)}⟩" for i, o in rows) + "]\n")
    ws = []
    for r, (din, dout) in enumerate(rows):
        S = witness(din, dout)
        pre = list(S); pre[2] ^= rc(r)  # round r first adds rc r, so store the state before it
        ws.append(st(pre))
    R = len(rows)
    for r in range(R):
        nxt = f"({name}[{r+1}]!).din" if r + 1 < R else f"pL ({name}[{r}]!).dout"
        rounds_thm.append(f"theorem {name}_round{r} :\n    St.xor (round {r} {name}_witness[{r}]!) (round {r} (St.xor {name}_witness[{r}]! ({name}[{r}]!).din))\n      = {nxt} := by decide +kernel\n")
    parts.append(f"/-- Witness states: entry r is fed to `round r` (which first adds rc r), together with its partner s xor din_r. -/\n"
                 f"def {name}_witness : List St := [\n  " + ",\n  ".join(ws) + "]\n")

import re
THMS = re.findall(r"^theorem (\w+)", open(os.path.join(HERE, "AsconTrail.tail.lean")).read(), re.M) + [t.split()[1] for t in rounds_thm]
open(sys.argv[2], "w").write(
    open(os.path.join(HERE, "AsconTrail.head.lean")).read()
    + "\n-- Generated data (gen_lean.py): pyascon KAT, characteristics, witness states\n\n"
    + f"def katIn : St := {st(kat_in)}\n/-- Output of pyascon ascon_permutation(S, 12) on katIn -/\ndef katOut : St := {st(kat_out)}\n\n"
    + "\n".join(parts)
    + "\n" + open(os.path.join(HERE, "AsconTrail.tail.lean")).read()
    + "\n" + "\n".join(rounds_thm)
    + "\n/-! Axiom audit: none of the theorems may depend on `Lean.ofReduceBool` (native_decide). -/\n"
    + "".join(f"#print axioms {n}\n" for n in THMS))
print("ok")
