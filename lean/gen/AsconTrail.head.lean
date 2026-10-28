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
