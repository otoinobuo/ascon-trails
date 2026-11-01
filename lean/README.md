# AsconTrail.lean: kernel-checked Ascon differential characteristics

`AsconTrail.lean` proves in Lean 4 (core only, no Mathlib) that two differential
characteristics of the Ascon permutation are valid and have the claimed numbers of
active S-boxes:

- `trail42`: 4 rounds, 42 active S-boxes (profile 15-11-9-7), from `../trails/ascon_4r_42active.json`
- `trail68`: 5 rounds, 68 active S-boxes (profile 15-11-9-7-26), from `../trails/ascon_5r_68active.json`

`pair_follows` and `pair_active` (added in v1.1) show that one single pair of states follows
the first four rounds of `trail68` (a 42-S-box characteristic that differs from `trail42` only in the
last output difference) through rounds 8..11, with 15, 11, 9 and 7 active
S-boxes counted from the two states alone.

Every theorem is proved with `decide +kernel`, so the Lean kernel itself evaluates it.
No theorem uses `native_decide`. The `#print axioms` lines at the end of the file show
only `propext` (or no axioms at all). `Lean.ofReduceBool` does not appear.

## Re-checking

Lean version: `leanprover/lean4:v4.33.1` (no Mathlib, no lakefile needed).

    nice -n 20 ~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean AsconTrail.lean

A successful check prints only the 23 `#print axioms` lines and exits with status 0.
(With elan as default: `lean +leanprover--lean4---v4.33.1 AsconTrail.lean`.)

SHA-256 of the checked file:
`54fe679046f30e4be03d8d188ae30db659b380f9743ae64d1d77cbdfc66ad8da`

## Check time (Apple M1 Max, nice 20; table from 2026-10-28, before the pair was added)

Whole file with the pair: about 11 s. Earlier whole-file measurement: 12.0 s wall, peak RSS 1.46 GB (about the same with `-j 1`).

| theorem | statement | kernel time |
|---|---|---|
| `sbox_table` | S-box derived from `pS` on 1-bit words = spec table | < 0.05 s |
| `perm12_kat` | `perm12 katIn = katOut` (pyascon `ascon_permutation(S,12)`) | < 0.05 s |
| `trail42_valid` | `validTrail trail42 = true` | 5.2 s |
| `trail42_active` | `activeCount trail42 = 42` | < 0.05 s |
| `trail42_profile` | `activeProfile trail42 = [15,11,9,7]` | < 0.05 s |
| `trail42_nontrivial` | first-round input difference is nonzero | < 0.01 s |
| `trail42_realised` | witness pairs realise every round (list form) | < 0.01 s |
| `trail42_round0..3` | per-round witness theorems | < 0.01 s each |
| `trail68_valid` | `validTrail trail68 = true` | 6.6 s |
| `trail68_active` | `activeCount trail68 = 68` | < 0.1 s |
| `trail68_profile` | `activeProfile trail68 = [15,11,9,7,26]` | < 0.1 s |
| `trail68_nontrivial` | first-round input difference is nonzero | < 0.01 s |
| `trail68_realised` | witness pairs realise every round (list form) | < 0.01 s |
| `trail68_round0..4` | per-round witness theorems | < 0.01 s each |

## What is modelled

- `rotr`, `St`, `St.xor`, `pS` (literal transcription of the bitsliced S-box layer,
  in the same order of operations as pyascon `ascon_permutation`, with complement written as `^^^ M`),
  `pL` (rotation pairs (19,28), (61,39), (1,6), (10,17), (7,41)), `rc i = 0xf0 - i*0x10 + i`, `pC`,
  `round i = pL ∘ pS ∘ pC i`, `perm12`. All arithmetic is on `Nat` with mask `M = 2^64-1`,
  so the kernel's GMP-accelerated `Nat` operations apply.
- `sboxCol` (the 5-bit S-box, derived by running `pS` on 1-bit words, with no hand-typed table),
  `col`, `ddt a b` (count over all 32 inputs), `Rd` (S-box layer input/output difference).
- `validRound`: for all 64 columns j, `ddt (col din j) (col dout j) ≠ 0`.
- `validTrail`: every round is valid, every word is < 2^64, and `pL dout_k = din_{k+1}`.
- `activeCount`: number of columns with nonzero `din`, summed over rounds.
- Witness theorems `<trail>_round<r>`: for the generated state s,
  `St.xor (round r s) (round r (St.xor s din_r)) = din_{r+1}` (last round: `pL dout_r`).
  So a concrete pair of 320-bit states follows each round's transition through the full
  round function, including the constant. The rounds are indexed 0..R-1 as in the statement.
  Constants cancel in differences, so the index does not affect validity.

Negative controls (run separately, not part of the file) were also checked with `decide +kernel`:
changing one bit of a `dout` makes `validTrail` false, `ddt 1 1 = 0`, a perturbed witness
makes `realisedFrom` false, and `activeCount trail42 ≠ 41`.

## Regenerating the file

`AsconTrail.lean` = `gen/AsconTrail.head.lean` (definitions) + generated data
(KAT from pyascon, the characteristics, witness states) + `gen/AsconTrail.tail.lean`
(theorems) + generated per-round theorems and the axiom audit. From the repository root:

    python3 -I lean/gen/gen_lean.py <pyascon ascon.py> lean/AsconTrail.lean \
        trail42=trails/ascon_4r_42active.json trail68=trails/ascon_5r_68active.json

Witness states are drawn with the fixed seed 20261028. `AsconTrail.lean` in this repository has the theorems in a slightly different
order from the generator's output (the set of lines is the same), because the pair was added in v1.1 by hand.