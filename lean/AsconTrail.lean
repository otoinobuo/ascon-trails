/-
  Machine-checked verification of two differential characteristics of the
  Ascon permutation (4 rounds / 42 active S-boxes, 5 rounds / 68 active S-boxes).

  Core Lean 4 only (no Mathlib). All arithmetic is on `Nat`, so the kernel's
  GMP-accelerated `Nat` operations apply; 64-bit words are masked with `M`.

  The model below is a literal transcription of the Ascon permutation as in the
  official reference implementation pyascon (`ascon_permutation`): constant
  addition, bitsliced S-box layer (same order of operations), linear layer.
  Theorem `perm12_kat` ties it to pyascon's own 12-round output.
-/

/-- 64-bit mask. -/
def M : Nat := 0xffffffffffffffff

/-- Rotate a 64-bit word right by `n` (0 < n < 64). -/
def rotr (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (64 - n))) &&& M

/-- The 320-bit Ascon state as five 64-bit words x0..x4. -/
structure St where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
deriving DecidableEq, Repr, Inhabited

def St.xor (a b : St) : St :=
  ⟨a.x0 ^^^ b.x0, a.x1 ^^^ b.x1, a.x2 ^^^ b.x2, a.x3 ^^^ b.x3, a.x4 ^^^ b.x4⟩

def St.zero : St := ⟨0, 0, 0, 0, 0⟩

/-- Every word is a 64-bit value. -/
def St.inRange (s : St) : Bool :=
  s.x0 ≤ M && s.x1 ≤ M && s.x2 ≤ M && s.x3 ≤ M && s.x4 ≤ M

/-- Substitution layer, transcribed literally from the bitsliced specification
    (pyascon lines: S[0]^=S[4]; S[4]^=S[3]; S[2]^=S[1]; T[i]=(~S[i])&S[i+1];
    S[i]^=T[i+1]; S[1]^=S[0]; S[0]^=S[4]; S[3]^=S[2]; S[2]=~S[2]). -/
def pS (s : St) : St :=
  let x0 := s.x0 ^^^ s.x4
  let x4 := s.x4 ^^^ s.x3
  let x2 := s.x2 ^^^ s.x1
  let x1 := s.x1
  let x3 := s.x3
  let t0 := (x0 ^^^ M) &&& x1
  let t1 := (x1 ^^^ M) &&& x2
  let t2 := (x2 ^^^ M) &&& x3
  let t3 := (x3 ^^^ M) &&& x4
  let t4 := (x4 ^^^ M) &&& x0
  let x0 := x0 ^^^ t1
  let x1 := x1 ^^^ t2
  let x2 := x2 ^^^ t3
  let x3 := x3 ^^^ t4
  let x4 := x4 ^^^ t0
  let x1 := x1 ^^^ x0
  let x0 := x0 ^^^ x4
  let x3 := x3 ^^^ x2
  let x2 := x2 ^^^ M
  ⟨x0, x1, x2, x3, x4⟩

/-- Linear diffusion layer. -/
def pL (s : St) : St :=
  ⟨s.x0 ^^^ rotr s.x0 19 ^^^ rotr s.x0 28,
   s.x1 ^^^ rotr s.x1 61 ^^^ rotr s.x1 39,
   s.x2 ^^^ rotr s.x2 1  ^^^ rotr s.x2 6,
   s.x3 ^^^ rotr s.x3 10 ^^^ rotr s.x3 17,
   s.x4 ^^^ rotr s.x4 7  ^^^ rotr s.x4 41⟩

/-- Round constant of round `i` (0..11), as in pyascon: 0xf0 - i*0x10 + i. -/
def rc (i : Nat) : Nat := 0xf0 - i * 0x10 + i

/-- Constant addition (to x2). -/
def pC (i : Nat) (s : St) : St := { s with x2 := s.x2 ^^^ rc i }

/-- One full Ascon round with round index `i`. -/
def round (i : Nat) (s : St) : St := pL (pS (pC i s))

/-- The 12-round Ascon permutation (rounds 0..11). -/
def perm12 (s : St) : St := (List.range 12).foldl (fun s i => round i s) s

/-! ### Column view of the S-box layer -/

/-- Bit `k` of `v`. -/
def bit (v k : Nat) : Nat := (v >>> k) &&& 1

/-- The 5-bit S-box, derived from `pS` itself applied to 1-bit words
    (input/output v = x0 x1 x2 x3 x4 with x0 the most significant bit). -/
def sboxCol (v : Nat) : Nat :=
  let s := pS ⟨bit v 4, bit v 3, bit v 2, bit v 1, bit v 0⟩
  (bit s.x0 0 <<< 4) ||| (bit s.x1 0 <<< 3) ||| (bit s.x2 0 <<< 2) |||
    (bit s.x3 0 <<< 1) ||| bit s.x4 0

/-- Column `j` (0..63) of a state, as a 5-bit value x0 x1 x2 x3 x4 (x0 = MSB). -/
def col (s : St) (j : Nat) : Nat :=
  (bit s.x0 j <<< 4) ||| (bit s.x1 j <<< 3) ||| (bit s.x2 j <<< 2) |||
    (bit s.x3 j <<< 1) ||| bit s.x4 j

/-- Difference distribution table entry: #{v < 32 | S(v) ⊕ S(v ⊕ a) = b}. -/
def ddt (a b : Nat) : Nat :=
  ((List.range 32).filter (fun v => sboxCol v ^^^ sboxCol (v ^^^ a) == b)).length

/-! ### Differential characteristics -/

/-- One round of a characteristic: S-box layer input / output difference. -/
structure Rd where
  din  : St
  dout : St
deriving DecidableEq, Repr, Inhabited

/-- Every column transition din → dout of the S-box layer has nonzero DDT entry. -/
def validRound (r : Rd) : Bool :=
  (List.range 64).all fun j => ddt (col r.din j) (col r.dout j) != 0

/-- Linear-layer links: pL (dout of round k) = din of round k+1. -/
def linksOK : List Rd → Bool
  | [] => true
  | r :: rs =>
    (match rs with
     | [] => true
     | r' :: _ => pL r.dout == r'.din) && linksOK rs

/-- A characteristic is valid if every round is valid, consecutive rounds are linked
    through the linear layer, and all words are 64-bit values. -/
def validTrail (t : List Rd) : Bool :=
  t.all (fun r => validRound r && r.din.inRange && r.dout.inRange) && linksOK t

/-- Number of active S-boxes (columns with nonzero input difference) in one round. -/
def activeIn (r : Rd) : Nat := ((List.range 64).filter (fun j => col r.din j != 0)).length

/-- Number of active S-boxes, summed over rounds. -/
def activeCount (t : List Rd) : Nat := t.foldl (fun acc r => acc + activeIn r) 0

/-- Per-round active S-box counts. -/
def activeProfile (t : List Rd) : List Nat := t.map activeIn

/-- The first round has a nonzero input difference. -/
def nontrivial : List Rd → Bool
  | [] => false
  | r :: _ => r.din != St.zero

/-- The difference expected after round k: din of round k+1, or pL dout for the last round. -/
def nextDiff (r : Rd) : List Rd → St
  | [] => pL r.dout
  | r' :: _ => r'.din

/-- Witness check: for each round k (index i+k), the concrete state s and s ⊕ din_k,
    passed through the full official round function `round (i+k)`, differ by exactly
    the next difference. Also requires one witness per round. -/
def realisedFrom (i : Nat) : List Rd → List St → Bool
  | [], [] => true
  | r :: rs, s :: ss =>
    St.xor (round i s) (round i (St.xor s r.din)) == nextDiff r rs && realisedFrom (i + 1) rs ss
  | _, _ => false

-- Generated data (gen_lean.py): pyascon KAT, characteristics, witness states

def katIn : St := ⟨0x0123456789abcdef, 0xfedcba9876543210, 0x0f1e2d3c4b5a6978, 0x8796a5b4c3d2e1f0, 0x0000000000000001⟩
/-- Output of pyascon ascon_permutation(S, 12) on katIn -/
def katOut : St := ⟨0x10044789cd8279ad, 0xc302948af35aeac3, 0x332069d777f2a307, 0x0d0f95b078c239e1, 0x5c068bbd3247babd⟩

def trail42 : List Rd := [
  ⟨⟨0xb9460e2000000000, 0x0000004080000001, 0x39460c6080000000, 0x0000000000000000, 0x0000000000000001⟩, ⟨0x0000000000000000, 0xa000020080000000, 0x39460c2000000001, 0x0000020000000000, 0x8000024000000000⟩⟩,
  ⟨⟨0x0000000000000000, 0xa100120481400001, 0xa100120080000001, 0x0000020081000000, 0xa100024480400001⟩, ⟨0x0000000000000000, 0xa100024480400001, 0x0000000000000000, 0x0000000000000000, 0x0000104001000000⟩⟩,
  ⟨⟨0x0000000000000000, 0x2000906081020008, 0x0000000000000000, 0x0000000000000000, 0x2000906081020008⟩, ⟨0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x2000906081020008⟩⟩,
  ⟨⟨0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000104044100440⟩, ⟨0x0000104040100440, 0x0000104044100440, 0x0000000000100440, 0x0000000000100000, 0x0000000004000000⟩⟩]

/-- Witness states: entry r is fed to `round r` (which first adds rc r), together with its partner s xor din_r. -/
def trail42_witness : List St := [
  ⟨0xb6384a2678f6c236, 0x802053460ef89de6, 0x3c2f59b2397ceb3f, 0xa2a1618c6ff93249, 0x260181909407f567⟩,
  ⟨0xa9e98bd12e1ccc2d, 0x96f0f886b43fd35c, 0x371422bd77fadf64, 0xf332c3e09d04518d, 0xd68c8f09e55024f6⟩,
  ⟨0x0d0b4f943608d984, 0x3f358a5d4fee2fcc, 0x0bfa45197e3515a5, 0x4aa20f9b3c94a565, 0xa1fecadd63be5b2a⟩,
  ⟨0x6a3b1745c405a657, 0x1dbf12effbf006c4, 0xe5a5dc0651a8b381, 0xe6f7fc777e44c108, 0xf3a5cc6b8044b689⟩]

def trail68 : List Rd := [
  ⟨⟨0xb9460e2000000000, 0x0000004080000001, 0x39460c6080000000, 0x0000000000000000, 0x0000000000000001⟩, ⟨0x0000000000000000, 0xa000020080000000, 0x39460c2000000001, 0x0000020000000000, 0x8000024000000000⟩⟩,
  ⟨⟨0x0000000000000000, 0xa100120481400001, 0xa100120080000001, 0x0000020081000000, 0xa100024480400001⟩, ⟨0x0000000000000000, 0xa100024480400001, 0x0000000000000000, 0x0000000000000000, 0x0000104001000000⟩⟩,
  ⟨⟨0x0000000000000000, 0x2000906081020008, 0x0000000000000000, 0x0000000000000000, 0x2000906081020008⟩, ⟨0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x2000906081020008⟩⟩,
  ⟨⟨0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000000000000000, 0x0000104044100440⟩, ⟨0x0000004000000000, 0x0000104044100440, 0x0000000000000000, 0x0000000000000000, 0x0000100044100440⟩⟩,
  ⟨⟨0x0000004000080400, 0x8088b24ae4902660, 0x0000000000000000, 0x0000000000000000, 0x8022182264982440⟩, ⟨0x0000000000080000, 0x0022082000000000, 0x0088a24880000220, 0x0088a20880000620, 0x8022182264982440⟩⟩]

/-- Witness states: entry r is fed to `round r` (which first adds rc r), together with its partner s xor din_r. -/
def trail68_witness : List St := [
  ⟨0x691565fda2881c38, 0x8238d3844c645041, 0x0d51fae75a4879f1, 0x6638038fc28552d7, 0xe491c25039a04a28⟩,
  ⟨0xaf227261cabee81d, 0x3aeb278e2b348e35, 0x9163717f89e37ea3, 0xb9152960b0084017, 0x2c075122e9ce5079⟩,
  ⟨0xde41288e36417e03, 0xf14aa39d9a9f4a24, 0x510265033858ed11, 0xca07270a1ed57187, 0xfcb2821782a76443⟩,
  ⟨0x34003dc8f6d94ed2, 0x043dae6ba28c9a87, 0xbdbe5663ca5f1b42, 0x8e287dddc7de0eff, 0x00eb6d7dcee389b7⟩,
  ⟨0x226a8ab98a07d2a3, 0xb015075da4cdc641, 0x2e3704e511644539, 0x14afebf99a484bb2, 0x8cb660552f824547⟩]

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

theorem trail42_round0 :
    St.xor (round 0 trail42_witness[0]!) (round 0 (St.xor trail42_witness[0]! (trail42[0]!).din))
      = (trail42[1]!).din := by decide +kernel

theorem trail42_round1 :
    St.xor (round 1 trail42_witness[1]!) (round 1 (St.xor trail42_witness[1]! (trail42[1]!).din))
      = (trail42[2]!).din := by decide +kernel

theorem trail42_round2 :
    St.xor (round 2 trail42_witness[2]!) (round 2 (St.xor trail42_witness[2]! (trail42[2]!).din))
      = (trail42[3]!).din := by decide +kernel

theorem trail42_round3 :
    St.xor (round 3 trail42_witness[3]!) (round 3 (St.xor trail42_witness[3]! (trail42[3]!).din))
      = pL (trail42[3]!).dout := by decide +kernel

theorem trail68_round0 :
    St.xor (round 0 trail68_witness[0]!) (round 0 (St.xor trail68_witness[0]! (trail68[0]!).din))
      = (trail68[1]!).din := by decide +kernel

theorem trail68_round1 :
    St.xor (round 1 trail68_witness[1]!) (round 1 (St.xor trail68_witness[1]! (trail68[1]!).din))
      = (trail68[2]!).din := by decide +kernel

theorem trail68_round2 :
    St.xor (round 2 trail68_witness[2]!) (round 2 (St.xor trail68_witness[2]! (trail68[2]!).din))
      = (trail68[3]!).din := by decide +kernel

theorem trail68_round3 :
    St.xor (round 3 trail68_witness[3]!) (round 3 (St.xor trail68_witness[3]! (trail68[3]!).din))
      = (trail68[4]!).din := by decide +kernel

theorem trail68_round4 :
    St.xor (round 4 trail68_witness[4]!) (round 4 (St.xor trail68_witness[4]! (trail68[4]!).din))
      = pL (trail68[4]!).dout := by decide +kernel

/-! Axiom audit: none of the theorems may depend on `Lean.ofReduceBool` (native_decide). -/
#print axioms sbox_table
#print axioms perm12_kat
#print axioms trail42_valid
#print axioms trail42_active
#print axioms trail42_profile
#print axioms trail42_nontrivial
#print axioms trail42_realised
#print axioms trail68_valid
#print axioms trail68_active
#print axioms trail68_profile
#print axioms trail68_nontrivial
#print axioms trail68_realised
#print axioms trail42_round0
#print axioms trail42_round1
#print axioms trail42_round2
#print axioms trail42_round3
#print axioms trail68_round0
#print axioms trail68_round1
#print axioms trail68_round2
#print axioms trail68_round3
#print axioms trail68_round4
