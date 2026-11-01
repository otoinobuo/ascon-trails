/-! ### Theorems (all checked by the kernel) -/

/-- The column S-box derived from `pS` is the Ascon S-box of the specification. -/
theorem sbox_table :
    (List.range 32).map sboxCol =
      [0x04, 0x0b, 0x1f, 0x14, 0x1a, 0x15, 0x09, 0x02, 0x1b, 0x05, 0x08, 0x12, 0x1d, 0x03, 0x06, 0x1c,
       0x1e, 0x13, 0x07, 0x0e, 0x00, 0x0d, 0x11, 0x18, 0x10, 0x0c, 0x01, 0x19, 0x16, 0x0a, 0x0f, 0x17] := by
  decide +kernel

/-- The Lean permutation agrees with pyascon's `ascon_permutation(S, 12)` on a known answer. -/
theorem perm12_kat : perm12 katIn = katOut := by decide +kernel

theorem trail42_valid : validTrail trail42 = true := by decide +kernel
theorem trail42_active : activeCount trail42 = 42 := by decide +kernel
theorem trail42_profile : activeProfile trail42 = [15, 11, 9, 7] := by decide +kernel
theorem trail42_nontrivial : nontrivial trail42 = true := by decide +kernel
theorem trail42_realised : realisedFrom 0 trail42 trail42_witness = true := by decide +kernel

theorem trail68_valid : validTrail trail68 = true := by decide +kernel
theorem trail68_active : activeCount trail68 = 68 := by decide +kernel
theorem trail68_profile : activeProfile trail68 = [15, 11, 9, 7, 26] := by decide +kernel
theorem trail68_nontrivial : nontrivial trail68 = true := by decide +kernel
theorem trail68_realised : realisedFrom 0 trail68 trail68_witness = true := by decide +kernel

/-! Per-round form of the witness theorems: for round r with witness state s and
    S-box-layer input difference d_r, the pair (s, s ⊕ d_r) passed through the full
    official round function `round r` has output difference d_{r+1}
    (or pL dout_r for the last round). -/
/-! ### One pair of states that follows all four rounds (added in v1.1)

  `pairP` and `pairP xor dX_0` are run through rounds 8..11, the rounds performed by pyascon's
  `ascon_permutation(S, rounds=4)`. Rounds 0..3 of `trail68` are the characteristic of the table in
  the note. Unlike the per-round witnesses above, one single pair follows every round here. -/

def pairP : St := ⟨0xa69ddcdf1017bede, 0x84a033cdd3354b73, 0x6bcd5a36901c4381, 0x2638430fac79e91d, 0xa480735de75e0dc8⟩

/-- `n` full rounds starting at round `i`. -/
def runFrom (i : Nat) : Nat → St → St
  | 0, s => s
  | n + 1, s => runFrom (i + 1) n (round i s)

/-- The difference of the pair after `k` of the rounds 8..11. -/
def pairDiff (k : Nat) : St :=
  St.xor (runFrom 8 k pairP) (runFrom 8 k (St.xor pairP (trail68[0]!).din))

theorem pair_follows :
    pairDiff 1 = (trail68[1]!).din ∧ pairDiff 2 = (trail68[2]!).din ∧
    pairDiff 3 = (trail68[3]!).din ∧ pairDiff 4 = pL (trail68[3]!).dout := by decide +kernel

/-- Counted from the two states alone: 15, 11, 9 and 7 active S-boxes. -/
theorem pair_active :
    [0, 1, 2, 3].map (fun k => ((List.range 64).filter (fun j => col (pairDiff k) j != 0)).length)
      = [15, 11, 9, 7] := by decide +kernel

