# Ascon differential characteristics: 42 active S-boxes over 4 rounds, 68 over 5 rounds

Ascon is the cryptographic algorithm that NIST standardised in 2025 (SP 800-232) to protect
data on small devices. This repository contains differential characteristics of the Ascon
permutation with fewer active S-boxes than previously known, the SAT-based search that found
them, and two independent verifications.

| Rounds | proven lower bound | best known characteristic |
|---|---|---|
| 4 | 36 (Erlacher, Mendel, Eichlseder, ToSC 2022) | 44 (designers) → 43 (Makarim, Rohit, ToSC 2022) → **42** |
| 5 | – | 78 (designers) → 72 (Makarim, Rohit, ToSC 2022) → **68** |

The characteristics have probability 2^-138 (4 rounds) and 2^-226 (5 rounds) and do not
threaten the security of Ascon. Details are in the note [`paper/ascon-trails.pdf`](paper/ascon-trails.pdf).

## Contents

| Path | What it is |
|---|---|
| `trails/ascon_4r_42active.json` | 4-round characteristic, 42 active S-boxes (15-11-9-7) |
| `trails/ascon_5r_68active.json` | 5-round characteristic, 68 active S-boxes (15-11-9-7-26); its first 4 rounds have 42 |
| `search/ascon_active.py` | bit-level SAT model and the descending search |
| `verify/verify_trail.py` | round-by-round check against the reference implementation pyascon |
| `verify/extend.py` | forward / backward one-round extension (4 → 5 rounds) |
| `lean/AsconTrail.lean` | Lean 4 proof (kernel-checked, no `native_decide`); see [`lean/README.md`](lean/README.md) |
| `lean/gen/` | generator of the Lean file |
| `paper/` | the note (LaTeX source and PDF) |

Each round of a JSON file gives the S-box layer input (`in`) and output (`out`) differences as
five 64-bit words x0..x4 in hexadecimal (bit 0 = least significant bit; S-box inputs are read
column-wise with x0 as the most significant bit, as in the specification).

## Reproducing

Python 3.9+ and PySAT (`pip install -r requirements.txt`). The reference implementation is
not included; fetch it at the commit we used:

    curl -LO https://raw.githubusercontent.com/meichlseder/pyascon/ed24e54abf9507d26fa49b46a56091570c7e743e/ascon.py

Check the characteristics against the reference implementation (seconds):

    python3 verify/verify_trail.py ascon.py trails/ascon_4r_42active.json
    python3 verify/verify_trail.py ascon.py trails/ascon_5r_68active.json

Check the Lean proof (about 12 s, Lean `v4.33.1`, no Mathlib):

    lean lean/AsconTrail.lean

Sanity check of the SAT model on known minima (1, 4, 15 for 1–3 rounds):

    python3 search/ascon_active.py --rounds 3 --k 15 --bounds 1,4

Run the descending search that found the 4-round characteristic (single core; it reached 42
after 2,821 s of wall-clock time on a shared Apple M1 Max with CaDiCaL 1.9.5; times vary):

    python3 search/ascon_active.py --rounds 4 --k 60 --bounds 1,4,15 --descend

Rebuild the 5-round characteristic from the 4-round one:

    python3 verify/extend.py trails/ascon_4r_42active.json out5.json

## Citation

Nobuo Otoi. Differential Characteristics of the NIST Lightweight Cryptography Standard Ascon:
42 Active S-boxes over 4 Rounds and 68 over 5 Rounds. 2026.

## License

MIT (see `LICENSE`).
