/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
public import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddCompile

/-!
# Correctness of the shipped `ed25519_point_add` machine code

`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` is the body of the function
`ed25519_point_add(u64 *out, const u64 *inp)` as printed by the owned backend.

## The symbolic executor

The hash-consed value tables of `Ed25519ScReduceShippedProof` are reused. The block uses
the hardware carry and zero flags (`adcx`, `adcxMem`, `bt`, `setc`, `test`, `cmovne`),
which the executor of that module does not model, so this module carries a flag-aware
symbolic state `SSt2` — the register and cell map of `SSt` together with the node of the
carry word and the node whose zero-ness is the zero flag — and its own `symStep2`,
`symRun2`, `partCheck2` with their soundness theorems. Node expressions (`NE`) and their
interning (`internN`) build the compound nodes of the carry-out and of the branchless
select.

## The program

The block is the lowering of `Algebraic.Ed25519PointAdd.pointAddProg` through
`FieldToJasminLimbs25519.loweringL`: nineteen field operations on four-limb elements of
`ZMod (2^255 - 19)` followed by four copies. The word statements of each limb block of
`Algebraic.FieldLimbs.Curve25519` are generated over numbered slots — `feAdcG` for the
carry chain, `feRowG` for a product row, and `feSelG`, `feCsubG`, `feAddG`, `feSubG`,
`feAccG`, `feProdG`, `feRedG`, `feMulG`, `feCopyG` for the blocks built from them — and
each generator's outputs are given their value. `paG` is the whole program from slot `57`
over the thirty-two input slots `25 .. 56`, and `paSpec` its four coordinates on the
natural values of the input limbs.

## Main results

* `partCheck2_sound`: a part check implies the canonical part maps the entry locations and
  flags to the exit ones under the slot values.
* `paG_val`: the sixteen output handles of `paG` hold the four coordinates of `paSpec`.
* `pa_part1` … `pa_part10`: the ten part checks of the block, each by `decide +kernel`.
* `paCanon_correct`: for a name-keyed state whose eight input coordinates are below
  `p25519`, the canonical block stores the four coordinates of `paSpec` at `%rdi`.
* `paShipped_correct_addr`: the same over `runBlockA` on the imported block, when the
  cells of `paCells` occupy pairwise disjoint eight-byte ranges.
* `paSpec_addSpec`: in `ZMod p25519` the four values of `paSpec` are the coordinates of
  `Ed25519PointAddCompile.addSpec` at `ed25519D`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-! ## 1. Node expressions -/

/-- An expression over the nodes of a value table. -/
inductive NE where
  | nd (x : Nat)
  | lit (n : Nat)
  | add (a b : NE)
  | sub (a b : NE)
  | and (a b : NE)
  | xor (a b : NE)
  | mul (a b : NE)
  | mulhi (a b : NE)
  | shr (a : NE) (k : Nat)
  deriving Inhabited, Repr

/-- The word an expression denotes when node `j` denotes `V j`. -/
def NE.den (V : Nat → BitVec 64) : NE → BitVec 64
  | .nd x => V x
  | .lit n => BitVec.ofNat 64 n
  | .add a b => a.den V + b.den V
  | .sub a b => a.den V - b.den V
  | .and a b => a.den V &&& b.den V
  | .xor a b => a.den V ^^^ b.den V
  | .mul a b => a.den V * b.den V
  | .mulhi a b => MultiLimbKernel.mulhi (a.den V) (b.den V)
  | .shr a k => a.den V >>> k

/-- Every node an expression names is below `m`. -/
def NE.Lt (m : Nat) : NE → Prop
  | .nd x => x < m
  | .lit _ => True
  | .add a b => a.Lt m ∧ b.Lt m
  | .sub a b => a.Lt m ∧ b.Lt m
  | .and a b => a.Lt m ∧ b.Lt m
  | .xor a b => a.Lt m ∧ b.Lt m
  | .mul a b => a.Lt m ∧ b.Lt m
  | .mulhi a b => a.Lt m ∧ b.Lt m
  | .shr a _ => a.Lt m

theorem NE.Lt.mono {m m' : Nat} (h : m ≤ m') : ∀ {e : NE}, e.Lt m → e.Lt m'
  | .nd _, he => lt_of_lt_of_le he h
  | .lit _, _ => trivial
  | .add a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .sub a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .and a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .xor a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .mul a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .mulhi a b, he => ⟨NE.Lt.mono h (e := a) he.1, NE.Lt.mono h (e := b) he.2⟩
  | .shr a _, he => NE.Lt.mono h (e := a) he

theorem NE.den_congr {V V' : Nat → BitVec 64} {m : Nat} (hv : ∀ j, j < m → V j = V' j) :
    ∀ {e : NE}, e.Lt m → e.den V = e.den V'
  | .nd x, he => hv x he
  | .lit _, _ => rfl
  | .add a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .sub a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .and a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .xor a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .mul a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .mulhi a b, he => by
      simp only [NE.den, NE.den_congr hv (e := a) he.1, NE.den_congr hv (e := b) he.2]
  | .shr a _, he => by simp only [NE.den, NE.den_congr hv (e := a) he]

/-- The node of a binary operation on the nodes of two interned operands. -/
def binN (op : Nat → Nat → Nd) (r : Tb × Nat) (g : Tb → Tb × Nat) : Tb × Nat :=
  match r with
  | (T₁, x) => match g T₁ with | (T₂, y) => T₂.addN (op x y)

/-- The node of an expression, its subexpressions added to the table. -/
def internN (T : Tb) : NE → Tb × Nat
  | .nd x => (T, x)
  | .lit n => T.addN (.lit n)
  | .add a b => binN .add (internN T a) (fun T₁ => internN T₁ b)
  | .sub a b => binN .sub (internN T a) (fun T₁ => internN T₁ b)
  | .and a b => binN .and (internN T a) (fun T₁ => internN T₁ b)
  | .xor a b => binN .xor (internN T a) (fun T₁ => internN T₁ b)
  | .mul a b => binN .mul (internN T a) (fun T₁ => internN T₁ b)
  | .mulhi a b => binN .mulhi (internN T a) (fun T₁ => internN T₁ b)
  | .shr a k => match internN T a with | (T₁, x) => T₁.addN (.shr x k)

/-- The specification of an interning step: the table grows, the node is in it, and it
    denotes the expression read in the entry table. -/
def InternOK (E : Env) (T : Tb) (e : NE) (r : Tb × Nat) : Prop :=
  Grows T r.1 ∧ r.2 < r.1.size ∧ r.1.V E r.2 = e.den (T.V E)

/-- The interning of a binary node from the internings of its two operands. -/
theorem binN_spec (E : Env) (T T₁ T₂ : Tb) (x y : Nat) (a b : NE) (op : Nat → Nat → Nd)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hop : ∀ (V : Nat → BitVec 64) p q, (op p q).den E V = f (V p) (V q))
    (hargs : ∀ p q m, p < m → q < m → (op p q).ArgsLt m)
    (hT : T.WF) (_ha : a.Lt T.size) (hb : b.Lt T.size)
    (h1 : internN T a = (T₁, x)) (ka : InternOK E T a (internN T a))
    (h2 : internN T₁ b = (T₂, y)) (kb : InternOK E T₁ b (internN T₁ b)) :
    Grows T (T₂.addN (op x y)).1 ∧ (T₂.addN (op x y)).2 < (T₂.addN (op x y)).1.size ∧
      (T₂.addN (op x y)).1.V E (T₂.addN (op x y)).2
        = f (a.den (T.V E)) (b.den (T.V E)) := by
  obtain ⟨g1, l1, v1⟩ := ka
  rw [h1] at g1 l1 v1
  obtain ⟨g2, l2, v2⟩ := kb
  rw [h2] at g2 l2 v2
  have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
  obtain ⟨g3, l3, v3⟩ := Tb.addN_spec E T₂ (op x y) g2.1 (hargs _ _ _ hx2 l2)
  have hbv : b.den (T₁.V E) = b.den (T.V E) :=
    NE.den_congr (fun j hj => g1.V_eq E hT hj) hb
  refine ⟨(g1.trans g2).trans g3, l3, ?_⟩
  rw [v3, hop, g2.V_eq E g1.1 l1, v1, v2, hbv]

theorem internN_spec (E : Env) : ∀ (T : Tb) (e : NE), T.WF → e.Lt T.size →
    InternOK E T e (internN T e)
  | T, .nd x, hT, he => ⟨Grows.refl hT, he, rfl⟩
  | T, .lit n, hT, _ => Tb.addN_spec E T (.lit n) hT trivial
  | T, .shr a k, hT, he => by
      have ka := internN_spec E T a hT he
      rcases h1 : internN T a with ⟨T₁, x⟩
      obtain ⟨g1, l1, v1⟩ := ka
      rw [h1] at g1 l1 v1
      obtain ⟨g2, l2, v2⟩ := Tb.addN_spec E T₁ (.shr x k) g1.1 l1
      refine ⟨?_, ?_, ?_⟩ <;> simp only [internN, h1]
      · exact g1.trans g2
      · exact l2
      · rw [v2]; simp only [Nd.den, NE.den, v1]
  | T, .add a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .add (· + ·) (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this
  | T, .sub a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .sub (· - ·) (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this
  | T, .and a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .and (· &&& ·) (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this
  | T, .xor a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .xor (· ^^^ ·) (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this
  | T, .mul a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .mul (· * ·) (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this
  | T, .mulhi a b, hT, he => by
      have ka := internN_spec E T a hT he.1
      rcases h1 : internN T a with ⟨T₁, x⟩
      have hT₁ : T₁.WF := by have := ka.1; rw [h1] at this; exact this.1
      have hsz : T.size ≤ T₁.size := by have := ka.1; rw [h1] at this; exact this.size_le hT
      have kb := internN_spec E T₁ b hT₁ (NE.Lt.mono hsz he.2)
      rcases h2 : internN T₁ b with ⟨T₂, y⟩
      have := binN_spec E T T₁ T₂ x y a b .mulhi MultiLimbKernel.mulhi (fun _ _ _ => rfl)
        (fun _ _ _ p q => ⟨p, q⟩) hT he.1 he.2 h1 ka h2 kb
      simpa only [InternOK, internN, binN, h1, h2, NE.den] using this

/-! ## 2. The gadgets of the carry and the select -/

/-- The all-ones word as an expression. -/
def onesNE : NE := .lit ones

/-- The carry-out of `s = a + b`: bit 63 of `(a & b) ⊕ ((a ⊕ b) & ¬s)`. -/
def carryNE (s a b : NE) : NE :=
  .shr (.xor (.and a b) (.and (.xor a b) (.xor s onesNE))) 63

/-- Bitwise or, as exclusive-or and and. -/
def orNE (a b : NE) : NE := .xor (.xor a b) (.and a b)

/-- The word `1` when `z` is nonzero and `0` otherwise: bit 63 of `z | -z`. -/
def nzNE (z : NE) : NE := .shr (orNE z (.sub (.lit 0) z)) 63

/-- The all-ones mask when `z` is nonzero and the zero mask otherwise. -/
def maskNE (z : NE) : NE := .sub (.lit 0) (nzNE z)

/-- `a` when `z` is nonzero and `b` otherwise. -/
def selNE (z a b : NE) : NE :=
  .xor (.and a (maskNE z)) (.and b (.xor (maskNE z) onesNE))

theorem ofNat_ones : (BitVec.ofNat 64 ones) = BitVec.allOnes 64 := ofNat_allOnes

/-- The all-ones mask when `z` is nonzero and the zero mask otherwise, as a word
    expression over `z`. -/
def maskB (z : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 0
    - (((z ^^^ (BitVec.ofNat 64 0 - z)) ^^^ (z &&& (BitVec.ofNat 64 0 - z))) >>> 63)

/-- The word a branchless select yields: `a` when `z` is nonzero and `b` otherwise. -/
def selW (z a b : BitVec 64) : BitVec 64 := if z.toNat = 0 then b else a

theorem nzB_eq (w : BitVec 64) :
    ((w ^^^ (BitVec.ofNat 64 0 - w)) ^^^ (w &&& (BitVec.ofNat 64 0 - w))) >>> 63
      = if w.toNat = 0 then 0 else 1 := by
  set nw := BitVec.ofNat 64 0 - w with hnw
  rw [shr63_eq]
  have hbits : ((w ^^^ nw) ^^^ (w &&& nw)).getLsbD 63 = (w.getLsbD 63 || nw.getLsbD 63) := by
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
    cases w.getLsbD 63 <;> cases nw.getLsbD 63 <;> rfl
  have hlt := w.isLt
  have hneg : nw.toNat = (2 ^ 64 - w.toNat) % 2 ^ 64 := by
    rw [hnw, BitVec.toNat_sub]
    simp
  rw [hbits, getLsbD63, getLsbD63, hneg]
  by_cases h0 : w.toNat = 0
  · rw [if_pos h0]
    have h1 : ¬ (2 ^ 63 ≤ w.toNat) := by omega
    have h2 : ¬ (2 ^ 63 ≤ (2 ^ 64 - w.toNat) % 2 ^ 64) := by
      rw [h0]
      norm_num
    simp only [h1, h2, decide_false, Bool.or_self, Bool.false_eq_true, if_false]
  · rw [if_neg h0]
    have : (2 ^ 63 ≤ w.toNat) ∨ (2 ^ 63 ≤ (2 ^ 64 - w.toNat) % 2 ^ 64) := by
      by_cases hh : 2 ^ 63 ≤ w.toNat
      · exact Or.inl hh
      · refine Or.inr ?_
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    rcases this with h | h <;> simp only [h, decide_true, Bool.or_true, Bool.true_or, if_true]

theorem maskB_eq (z : BitVec 64) :
    maskB z = if z.toNat = 0 then 0 else BitVec.allOnes 64 := by
  show BitVec.ofNat 64 0 - _ = _
  rw [nzB_eq]
  split <;> decide +kernel

theorem selB_eq (z a b : BitVec 64) :
    (a &&& maskB z) ^^^ (b &&& (maskB z ^^^ BitVec.ofNat 64 ones)) = selW z a b := by
  rw [maskB_eq, ofNat_ones]
  simp only [selW]
  split
  · simp only [BitVec.ofNat_eq_ofNat, BitVec.and_zero, BitVec.zero_xor, BitVec.and_allOnes]
  · simp only [BitVec.and_allOnes, BitVec.xor_self, BitVec.and_zero,
      BitVec.xor_zero]

theorem selNE_den (V : Nat → BitVec 64) (z a b : NE) :
    (selNE z a b).den V = if (z.den V).toNat = 0 then b.den V else a.den V :=
  selB_eq (z.den V) (a.den V) (b.den V)

/-! ## 3. The flag-aware symbolic state -/

/-- A symbolic state: the register and cell nodes, the node of the carry word, and the
    node whose zero-ness is the zero flag. -/
structure SSt2 where
  /-- The registers and cells. -/
  base : SSt := {}
  /-- The node of the carry word, absent when the carry flag is unknown. -/
  cfw : Option Nat := none
  /-- The node whose zero-ness is the zero flag, absent when it is unknown. -/
  zfn : Option Nat := none

/-- The state `s` agrees with the symbolic state: registers and cells as in `SRel`, the
    carry flag as the value of `cfw`, and the zero flag as the zero-ness of `zfn`. -/
def SRel2 (E : Env) (T : Tb) (S : SSt2) (s : JState 64) : Prop :=
  SRel E T S.base s.regs s.mem ∧
  (∀ x, S.cfw = some x → x < T.size ∧
    T.V E x = (if s.flagB (·.cf) then (1 : BitVec 64) else 0)) ∧
  (∀ x, S.zfn = some x → x < T.size ∧ s.flagB (·.zf) = decide ((T.V E x).toNat = 0))

theorem SRel2.grow {E : Env} {T T' : Tb} {S : SSt2} {s : JState 64}
    (hT : T.WF) (hg : Grows T T') (h : SRel2 E T S s) : SRel2 E T' S s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.grow hT hg, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨l, v⟩ := h2 x hx
    exact ⟨lt_of_lt_of_le l (hg.size_le hT), by rw [hg.V_eq E hT l, v]⟩
  · obtain ⟨l, v⟩ := h3 x hx
    exact ⟨lt_of_lt_of_le l (hg.size_le hT), by rw [hg.V_eq E hT l, v]⟩

/-! ## 4. The symbolic executor -/

/-- One instruction on the flag-aware symbolic state; `none` outside the handled forms. -/
def symStep2 (T : Tb) (S : SSt2) : JInstr 64 → Option (Tb × SSt2)
  | .mov d (.reg r) =>
      match rdR T S.base r with
      | (T₁, x) => some (T₁, { S with base := S.base.setR d x })
  | .mov d (.imm n) =>
      match T.addN (.lit n) with
      | (T₁, x) => some (T₁, { S with base := S.base.setR d x })
  | .loadMem d b o =>
      match rdM T S.base b o with
      | (T₁, x) => some (T₁, { S with base := S.base.setR d x })
  | .storeMem b o (.reg r) =>
      match rdR T S.base r with
      | (T₁, x) => some (T₁, { S with base := S.base.setM (b, o) x })
  | .mulx hd ld (.reg a) (.reg b) =>
      if hd = ld then none else
        match rdR T S.base a with
        | (T₁, x) =>
          match rdR T₁ S.base b with
          | (T₂, y) =>
            match T₂.addN (.mul x y) with
            | (T₃, lo) =>
              match T₃.addN (.mulhi x y) with
              | (T₄, hi) => some (T₄, { S with base := (S.base.setR ld lo).setR hd hi })
  | .imul d (.reg r) =>
      match symBin T S.base d r .mul with
      | (T₁, B) => some (T₁, { base := B, cfw := none, zfn := none })
  | .xor_ d (.reg r) =>
      match symBin T S.base d r .xor with
      | (T₁, B) => some (T₁, { base := B, cfw := none, zfn := none })
  | .or_ d (.reg r) =>
      match rdR T S.base d with
      | (T₁, x) =>
        match rdR T₁ S.base r with
        | (T₂, y) =>
          match internN T₂ (orNE (.nd x) (.nd y)) with
          | (T₃, z) => some (T₃, { base := S.base.setR d z, cfw := none, zfn := none })
  | .bt a (.imm k) =>
      if k = 0 then
        match rdR T S.base a with
        | (T₁, x) =>
          match internN T₁ (.and (.nd x) (.lit 1)) with
          | (T₂, c) => some (T₂, { S with cfw := some c })
      else none
  | .setc d =>
      match S.cfw with
      | none => none
      | some c => some (T, { S with base := S.base.setR d c })
  | .test a (.reg b) =>
      match rdR T S.base a with
      | (T₁, x) =>
        match rdR T₁ S.base b with
        | (T₂, y) =>
          match T₂.addN (.and x y) with
          | (T₃, z) => some (T₃, { base := S.base, cfw := none, zfn := some z })
  | .cmovne d (.reg r) =>
      match S.zfn with
      | none => none
      | some z =>
        match rdR T S.base r with
        | (T₁, x) =>
          match rdR T₁ S.base d with
          | (T₂, y) =>
            match internN T₂ (selNE (.nd z) (.nd x) (.nd y)) with
            | (T₃, w) => some (T₃, { S with base := S.base.setR d w })
  | .adcx d (.reg r) =>
      match S.cfw with
      | none => none
      | some c =>
        match rdR T S.base d with
        | (T₁, x) =>
          match rdR T₁ S.base r with
          | (T₂, y) =>
            match internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with
            | (T₃, z) =>
              match internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
                  (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with
              | (T₄, w) => some (T₄, { base := S.base.setR d z, cfw := some w, zfn := S.zfn })
  | .adcxMem d b o =>
      match S.cfw with
      | none => none
      | some c =>
        match rdR T S.base d with
        | (T₁, x) =>
          match rdM T₁ S.base b o with
          | (T₂, y) =>
            match internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with
            | (T₃, z) =>
              match internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
                  (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with
              | (T₄, w) => some (T₄, { base := S.base.setR d z, cfw := some w, zfn := S.zfn })
  | _ => none

/-- A block on the flag-aware symbolic state. -/
def symRun2 : Tb → SSt2 → List (JInstr 64) → Option (Tb × SSt2)
  | T, S, [] => some (T, S)
  | T, S, i :: is =>
    match symStep2 T S i with
    | some (T₁, S₁) => symRun2 T₁ S₁ is
    | none => none

/-! ## 5. Word identities of the flag instructions -/

theorem and_one_eq (x : BitVec 64) :
    x &&& BitVec.ofNat 64 1 = if x.getLsbD 0 then (1 : BitVec 64) else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, ← BitVec.testBit_toNat]
  have hx := x.toNat.testBit_zero
  have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide +kernel
  rw [h1, Nat.and_one_is_mod, hx]
  have := Nat.mod_two_eq_zero_or_one x.toNat
  rcases this with h | h <;> simp [h]

theorem or_xor_and (a b : BitVec 64) : (a ^^^ b) ^^^ (a &&& b) = a ||| b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem adcx_word (a b : BitVec 64) (c : Bool) :
    (x86_ADCX a b c).2 = a + b + (if c then (1 : BitVec 64) else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [x86_ADCX, waddcarry, BitVec.toNat_add, BitVec.toNat_ofNat]
  cases c <;> simp [Nat.mod_add_mod]

theorem adcx_carry (a b : BitVec 64) (c : Bool) :
    (if ((x86_ADCX a b c).1.getD false) then (1 : BitVec 64) else 0)
      = bSltu (a + b) a
        + bSltu (a + b + (if c then (1 : BitVec 64) else 0)) (a + b) := by
  set cw : BitVec 64 := if c then 1 else 0 with hcw
  have hcwn : cw.toNat = (if c then 1 else 0) := by cases c <;> simp [hcw]
  have hcw1 : cw.toNat ≤ 1 := by cases c <;> simp [hcw]
  have hsum := adc_toNat' a b cw
  have hle := adc_carry_le' a b cw hcw1
  have hlt := (a + b + cw).isLt
  apply BitVec.eq_of_toNat_eq
  have hco : (x86_ADCX a b c).1.getD false
      = decide (2 ^ 64 ≤ a.toNat + b.toNat + (if c then 1 else 0)) := rfl
  rw [hco, ← hcwn]
  by_cases hh : 2 ^ 64 ≤ a.toNat + b.toNat + cw.toNat
  · rw [decide_eq_true hh, if_pos rfl]
    have : (bSltu (a + b) a + bSltu (a + b + cw) (a + b)).toNat = 1 := by omega
    rw [this]
    decide +kernel
  · rw [decide_eq_false hh]
    have : (bSltu (a + b) a + bSltu (a + b + cw) (a + b)).toNat = 0 := by omega
    rw [this]
    simp

/-! ## 6. Soundness of the executor -/

theorem srel2_of_srel {E : Env} {T T' : Tb} {S : SSt2} {s t : JState 64} {B : SSt}
    (hT : T.WF) (hg : Grows T T') (h : SRel2 E T S s) (hb : SRel E T' B t.regs t.mem)
    (hcf : t.flagB (·.cf) = s.flagB (·.cf)) (hzf : t.flagB (·.zf) = s.flagB (·.zf)) :
    SRel2 E T' { base := B, cfw := S.cfw, zfn := S.zfn } t := by
  obtain ⟨-, h2, h3⟩ := h.grow hT hg
  exact ⟨hb, fun x hx => ⟨(h2 x hx).1, by rw [hcf]; exact (h2 x hx).2⟩,
    fun x hx => ⟨(h3 x hx).1, by rw [hzf]; exact (h3 x hx).2⟩⟩

theorem srel2_clob {E : Env} {T' : Tb} {t : JState 64} {B : SSt}
    (hb : SRel E T' B t.regs t.mem) :
    SRel2 E T' { base := B, cfw := none, zfn := none } t := by
  refine ⟨hb, fun x hx => ?_, fun x hx => ?_⟩ <;> simp at hx

theorem adcx_word' (a b : BitVec 64) (c : Bool) :
    BitVec.ofNat 64 (a.toNat + b.toNat + (if c then 1 else 0))
      = a + b + (if c then (1 : BitVec 64) else 0) := adcx_word a b c

theorem maskNE_Lt {m z : Nat} (hz : z < m) : (maskNE (.nd z)).Lt m := by
  simp only [maskNE, nzNE, orNE, NE.Lt]
  exact ⟨trivial, ⟨hz, trivial, hz⟩, hz, trivial, hz⟩

theorem selNE_Lt {m z a b : Nat} (hz : z < m) (ha : a < m) (hb : b < m) :
    (selNE (.nd z) (.nd a) (.nd b)).Lt m := by
  refine ⟨⟨ha, maskNE_Lt hz⟩, hb, maskNE_Lt hz, trivial⟩

theorem carryNE_Lt {m : Nat} {s a b : NE} (hs : s.Lt m) (ha : a.Lt m) (hb : b.Lt m) :
    (carryNE s a b).Lt m := ⟨⟨ha, hb⟩, ⟨ha, hb⟩, hs, trivial⟩

theorem symStep2_sound (E : Env) {T T' : Tb} {S S' : SSt2} (s : JState 64) (i : JInstr 64)
    (h : symStep2 T S i = some (T', S')) (hT : T.WF) (hR : SRel2 E T S s) :
    Grows T T' ∧ SRel2 E T' S' (evalInstr s i) := by
  cases i
  case mov d src =>
    cases src with
    | reg r =>
      rcases hp : rdR T S.base r with ⟨T₁, x⟩
      simp only [symStep2, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := rdR_spec E T S.base s.regs s.mem r hT hR.1
      rw [hp] at g l v
      exact ⟨g, srel2_of_srel hT g hR ((hR.1.grow hT g).setR d x l _ v) rfl rfl⟩
    | imm n =>
      rcases hp : T.addN (.lit n) with ⟨T₁, x⟩
      simp only [symStep2, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit n) hT trivial
      rw [hp] at g l v
      exact ⟨g, srel2_of_srel hT g hR ((hR.1.grow hT g).setR d x l _ v) rfl rfl⟩
  case loadMem d b o =>
    rcases hp : rdM T S.base b o with ⟨T₁, x⟩
    simp only [symStep2, hp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨g, l, v⟩ := rdM_spec E T S.base s.regs s.mem b o hT hR.1
    rw [hp] at g l v
    exact ⟨g, srel2_of_srel hT g hR ((hR.1.grow hT g).setR d x l _ v) rfl rfl⟩
  case storeMem b o src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      rcases hp : rdR T S.base r with ⟨T₁, x⟩
      simp only [symStep2, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := rdR_spec E T S.base s.regs s.mem r hT hR.1
      rw [hp] at g l v
      exact ⟨g, srel2_of_srel hT g hR ((hR.1.grow hT g).setM b o x l _ v) rfl rfl⟩
  case imul d src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      simp only [symStep2, Option.some.injEq] at h
      have hb := symBin_spec E T S.base s.regs s.mem d r Nd.mul (· * ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR.1
      rcases hp : symBin T S.base d r Nd.mul with ⟨T₁, B⟩
      rw [hp] at hb
      simp only [hp, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hb.1, srel2_clob hb.2⟩
  case xor_ d src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      simp only [symStep2, Option.some.injEq] at h
      have hb := symBin_spec E T S.base s.regs s.mem d r Nd.xor (· ^^^ ·) (fun _ _ _ => rfl)
        (fun _ _ _ h1 h2 => ⟨h1, h2⟩) hT hR.1
      rcases hp : symBin T S.base d r Nd.xor with ⟨T₁, B⟩
      rw [hp] at hb
      simp only [hp, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hb.1, srel2_clob hb.2⟩
  case or_ d src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      rcases h1 : rdR T S.base d with ⟨T₁, x⟩
      obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem d hT hR.1
      rw [h1] at g1 l1 v1
      have hR1 := hR.1.grow hT g1
      rcases h2 : rdR T₁ S.base r with ⟨T₂, y⟩
      obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S.base s.regs s.mem r g1.1 hR1
      rw [h2] at g2 l2 v2
      have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
      obtain ⟨g3, l3, v3⟩ := internN_spec E T₂ (orNE (.nd x) (.nd y)) g2.1
        ⟨⟨hx2, l2⟩, hx2, l2⟩
      rcases h3 : internN T₂ (orNE (.nd x) (.nd y)) with ⟨T₃, z⟩
      rw [h3] at g3 l3 v3
      simp only [symStep2, h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(g1.trans g2).trans g3, srel2_clob
        (((hR1.grow g1.1 g2).grow g2.1 g3).setR d z l3 _ ?_)⟩
      rw [v3]
      simp only [orNE, NE.den, g2.V_eq E g1.1 l1, v1, v2]
      exact or_xor_and _ _
  case mulx hd ld a b =>
    cases a with
    | imm _ => simp [symStep2] at h
    | reg a =>
      cases b with
      | imm _ => simp [symStep2] at h
      | reg b =>
        simp only [symStep2] at h
        split_ifs at h with hhl
        rcases h1 : rdR T S.base a with ⟨T₁, x⟩
        obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem a hT hR.1
        rw [h1] at g1 l1 v1
        have hR1 := hR.1.grow hT g1
        rcases h2 : rdR T₁ S.base b with ⟨T₂, y⟩
        obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S.base s.regs s.mem b g1.1 hR1
        rw [h2] at g2 l2 v2
        have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
        rcases h3 : T₂.addN (.mul x y) with ⟨T₃, lo⟩
        obtain ⟨g3, l3, v3⟩ := Tb.addN_spec E T₂ (.mul x y) g2.1 ⟨hx2, l2⟩
        rw [h3] at g3 l3 v3
        have hx3 : x < T₃.size := lt_of_lt_of_le hx2 (g3.size_le g2.1)
        have hy3 : y < T₃.size := lt_of_lt_of_le l2 (g3.size_le g2.1)
        rcases h4 : T₃.addN (.mulhi x y) with ⟨T₄, hi⟩
        obtain ⟨g4, l4, v4⟩ := Tb.addN_spec E T₃ (.mulhi x y) g3.1 ⟨hx3, hy3⟩
        rw [h4] at g4 l4 v4
        simp only [h1, h2, h3, h4, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlo4 : lo < T₄.size := lt_of_lt_of_le l3 (g4.size_le g3.1)
        have hR3 := (hR1.grow g1.1 g2).grow g2.1 g3
        have hxv : T₂.V E x = s.regs a := by rw [g2.V_eq E g1.1 l1, v1]
        have hlo : T₃.V E lo = s.regs a * s.regs b := by
          rw [v3]
          simp only [Nd.den]
          rw [hxv, v2]
        refine ⟨((g1.trans g2).trans g3).trans g4, ?_⟩
        refine srel2_of_srel (B := (S.base.setR ld lo).setR hd hi) hT
          (((g1.trans g2).trans g3).trans g4) hR ?_ rfl rfl
        rw [evalInstr_mulx_regs]
        refine ((hR3.setR ld lo l3 _ hlo).grow g3.1 g4).setR hd hi l4 _ ?_
        rw [v4]
        simp only [Nd.den]
        rw [g3.V_eq E g2.1 hx2, g3.V_eq E g2.1 l2, hxv, v2]
  case bt a src =>
    cases src with
    | reg _ => simp [symStep2] at h
    | imm k =>
      simp only [symStep2] at h
      split_ifs at h with hk
      subst hk
      rcases h1 : rdR T S.base a with ⟨T₁, x⟩
      obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem a hT hR.1
      rw [h1] at g1 l1 v1
      obtain ⟨g2, l2, v2⟩ := internN_spec E T₁ (.and (.nd x) (.lit 1)) g1.1 ⟨l1, trivial⟩
      rcases h2 : internN T₁ (.and (.nd x) (.lit 1)) with ⟨T₂, c⟩
      rw [h2] at g2 l2 v2
      simp only [h1, h2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨g1.trans g2, ?_, fun y hy => ?_, fun y hy => ?_⟩
      · exact (hR.1.grow hT g1).grow g1.1 g2
      · simp only [Option.some.injEq] at hy
        subst hy
        refine ⟨l2, ?_⟩
        rw [v2]
        simp only [NE.den, v1]
        rw [and_one_eq]
        rfl
      · obtain ⟨ly, vy⟩ := hR.2.2 y hy
        exact ⟨lt_of_lt_of_le ly ((g1.trans g2).size_le hT),
          by rw [(g1.trans g2).V_eq E hT ly]; exact vy⟩
  case setc d =>
    rcases hc : S.cfw with _ | c
    · simp only [symStep2, hc] at h
      simp at h
    · simp only [symStep2, hc, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨lc, vc⟩ := hR.2.1 c hc
      refine ⟨Grows.refl hT, hR.1.setR d c lc _ vc, fun y hy => ?_, hR.2.2⟩
      simp only [Option.some.injEq] at hy
      subst hy
      exact ⟨lc, vc⟩
  case test a src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg b =>
      rcases h1 : rdR T S.base a with ⟨T₁, x⟩
      obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem a hT hR.1
      rw [h1] at g1 l1 v1
      have hR1 := hR.1.grow hT g1
      rcases h2 : rdR T₁ S.base b with ⟨T₂, y⟩
      obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S.base s.regs s.mem b g1.1 hR1
      rw [h2] at g2 l2 v2
      have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
      rcases h3 : T₂.addN (.and x y) with ⟨T₃, z⟩
      obtain ⟨g3, l3, v3⟩ := Tb.addN_spec E T₂ (.and x y) g2.1 ⟨hx2, l2⟩
      rw [h3] at g3 l3 v3
      simp only [symStep2, h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(g1.trans g2).trans g3, (hR1.grow g1.1 g2).grow g2.1 g3,
        fun y' hy => ?_, fun y' hy => ?_⟩
      · simp at hy
      · simp only [Option.some.injEq] at hy
        subst hy
        refine ⟨l3, ?_⟩
        rw [v3]
        simp only [Nd.den, g2.V_eq E g1.1 l1, v1, v2]
        rfl
  case cmovne d src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      rcases hz : S.zfn with _ | z
      · simp only [symStep2, hz] at h
        simp at h
      · obtain ⟨lz, vz⟩ := hR.2.2 z hz
        rcases h1 : rdR T S.base r with ⟨T₁, x⟩
        obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem r hT hR.1
        rw [h1] at g1 l1 v1
        have hR1 := hR.1.grow hT g1
        rcases h2 : rdR T₁ S.base d with ⟨T₂, y⟩
        obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S.base s.regs s.mem d g1.1 hR1
        rw [h2] at g2 l2 v2
        have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
        have hz2 : z < T₂.size := lt_of_lt_of_le lz ((g1.trans g2).size_le hT)
        obtain ⟨g3, l3, v3⟩ := internN_spec E T₂ (selNE (.nd z) (.nd x) (.nd y)) g2.1
          (selNE_Lt hz2 hx2 l2)
        rcases h3 : internN T₂ (selNE (.nd z) (.nd x) (.nd y)) with ⟨T₃, w⟩
        rw [h3] at g3 l3 v3
        simp only [symStep2, hz, h1, h2, h3, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hval : T₃.V E w
            = x86_CMOVcc (! s.flagB (·.zf)) (s.regs r) (s.regs d) := by
          rw [v3, selNE_den]
          simp only [NE.den, g2.V_eq E g1.1 l1, v1, v2, (g1.trans g2).V_eq E hT lz]
          rw [vz]
          by_cases hzz : (Tb.V E T z).toNat = 0 <;> simp [hzz, x86_CMOVcc]
        refine ⟨(g1.trans g2).trans g3,
          ((hR1.grow g1.1 g2).grow g2.1 g3).setR d w l3 _ hval, fun y' hy => ?_,
          fun y' hy => ?_⟩
        · obtain ⟨ly, vy⟩ := hR.2.1 y' hy
          exact ⟨lt_of_lt_of_le ly (((g1.trans g2).trans g3).size_le hT),
            by rw [((g1.trans g2).trans g3).V_eq E hT ly]; exact vy⟩
        · simp only [Option.some.injEq] at hy
          subst hy
          exact ⟨lt_of_lt_of_le lz (((g1.trans g2).trans g3).size_le hT),
            by rw [((g1.trans g2).trans g3).V_eq E hT lz]; exact vz⟩
  case adcx d src =>
    cases src with
    | imm _ => simp [symStep2] at h
    | reg r =>
      rcases hc : S.cfw with _ | c
      · simp only [symStep2, hc] at h
        simp at h
      · obtain ⟨lc, vc⟩ := hR.2.1 c hc
        rcases h1 : rdR T S.base d with ⟨T₁, x⟩
        obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem d hT hR.1
        rw [h1] at g1 l1 v1
        have hR1 := hR.1.grow hT g1
        rcases h2 : rdR T₁ S.base r with ⟨T₂, y⟩
        obtain ⟨g2, l2, v2⟩ := rdR_spec E T₁ S.base s.regs s.mem r g1.1 hR1
        rw [h2] at g2 l2 v2
        have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
        have hc2 : c < T₂.size := lt_of_lt_of_le lc ((g1.trans g2).size_le hT)
        obtain ⟨g3, l3, v3⟩ := internN_spec E T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) g2.1
          ⟨⟨hx2, l2⟩, hc2⟩
        rcases h3 : internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with ⟨T₃, z⟩
        rw [h3] at g3 l3 v3
        have hx3 : x < T₃.size := lt_of_lt_of_le hx2 (g3.size_le g2.1)
        have hy3 : y < T₃.size := lt_of_lt_of_le l2 (g3.size_le g2.1)
        have hc3 : c < T₃.size := lt_of_lt_of_le hc2 (g3.size_le g2.1)
        obtain ⟨g4, l4, v4⟩ := internN_spec E T₃
          (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
            (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) g3.1
          ⟨carryNE_Lt ⟨hx3, hy3⟩ hx3 hy3, carryNE_Lt l3 ⟨hx3, hy3⟩ hc3⟩
        rcases h4 : internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
            (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with ⟨T₄, w⟩
        rw [h4] at g4 l4 v4
        simp only [symStep2, hc, h1, h2, h3, h4, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hxv : T₂.V E x = s.regs d := by rw [g2.V_eq E g1.1 l1, v1]
        have hcv : T₂.V E c = (if s.flagB (·.cf) then (1 : BitVec 64) else 0) := by
          rw [(g1.trans g2).V_eq E hT lc]; exact vc
        have hzv : T₃.V E z = s.regs d + s.regs r + (if s.flagB (·.cf) then 1 else 0) := by
          rw [v3]
          simp only [NE.den, hxv, v2, hcv]
        have hwv : T₄.V E w
            = bSltu (s.regs d + s.regs r) (s.regs d)
              + bSltu (s.regs d + s.regs r + (if s.flagB (·.cf) then 1 else 0))
                  (s.regs d + s.regs r) := by
          rw [v4]
          simp only [NE.den, carryNE, onesNE, g3.V_eq E g2.1 hx2, g3.V_eq E g2.1 l2,
            g3.V_eq E g2.1 hc2, hxv, v2, hcv, hzv]
          rw [show (BitVec.ofNat 64 ones) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl,
            carry_bit, carry_bit]
        refine ⟨((g1.trans g2).trans g3).trans g4, ?_, fun y' hy => ?_, fun y' hy => ?_⟩
        · refine (((hR1.grow g1.1 g2).grow g2.1 g3).grow g3.1 g4).setR d z ?_ _ ?_
          · exact lt_of_lt_of_le l3 (g4.size_le g3.1)
          · rw [g4.V_eq E g3.1 l3, hzv, adcx_word']
            simp only [JState.get, JOperand.eval]
        · simp only [Option.some.injEq] at hy
          subst hy
          refine ⟨l4, ?_⟩
          rw [hwv, ← adcx_carry]
          rfl
        · obtain ⟨ly, vy⟩ := hR.2.2 y' hy
          refine ⟨lt_of_lt_of_le ly ((((g1.trans g2).trans g3).trans g4).size_le hT), ?_⟩
          rw [(((g1.trans g2).trans g3).trans g4).V_eq E hT ly]
          exact vy
  case adcxMem d b o =>
    rcases hc : S.cfw with _ | c
    · simp only [symStep2, hc] at h
      simp at h
    · obtain ⟨lc, vc⟩ := hR.2.1 c hc
      rcases h1 : rdR T S.base d with ⟨T₁, x⟩
      obtain ⟨g1, l1, v1⟩ := rdR_spec E T S.base s.regs s.mem d hT hR.1
      rw [h1] at g1 l1 v1
      have hR1 := hR.1.grow hT g1
      rcases h2 : rdM T₁ S.base b o with ⟨T₂, y⟩
      obtain ⟨g2, l2, v2⟩ := rdM_spec E T₁ S.base s.regs s.mem b o g1.1 hR1
      rw [h2] at g2 l2 v2
      have hx2 : x < T₂.size := lt_of_lt_of_le l1 (g2.size_le g1.1)
      have hc2 : c < T₂.size := lt_of_lt_of_le lc ((g1.trans g2).size_le hT)
      obtain ⟨g3, l3, v3⟩ := internN_spec E T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) g2.1
        ⟨⟨hx2, l2⟩, hc2⟩
      rcases h3 : internN T₂ (.add (.add (.nd x) (.nd y)) (.nd c)) with ⟨T₃, z⟩
      rw [h3] at g3 l3 v3
      have hx3 : x < T₃.size := lt_of_lt_of_le hx2 (g3.size_le g2.1)
      have hy3 : y < T₃.size := lt_of_lt_of_le l2 (g3.size_le g2.1)
      have hc3 : c < T₃.size := lt_of_lt_of_le hc2 (g3.size_le g2.1)
      obtain ⟨g4, l4, v4⟩ := internN_spec E T₃
        (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
          (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) g3.1
        ⟨carryNE_Lt ⟨hx3, hy3⟩ hx3 hy3, carryNE_Lt l3 ⟨hx3, hy3⟩ hc3⟩
      rcases h4 : internN T₃ (.add (carryNE (.add (.nd x) (.nd y)) (.nd x) (.nd y))
          (carryNE (.nd z) (.add (.nd x) (.nd y)) (.nd c))) with ⟨T₄, w⟩
      rw [h4] at g4 l4 v4
      simp only [symStep2, hc, h1, h2, h3, h4, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hxv : T₂.V E x = s.regs d := by rw [g2.V_eq E g1.1 l1, v1]
      have hcv : T₂.V E c = (if s.flagB (·.cf) then (1 : BitVec 64) else 0) := by
        rw [(g1.trans g2).V_eq E hT lc]; exact vc
      have hzv : T₃.V E z = s.regs d + s.mem b o + (if s.flagB (·.cf) then 1 else 0) := by
        rw [v3]
        simp only [NE.den, hxv, v2, hcv]
      have hwv : T₄.V E w
          = bSltu (s.regs d + s.mem b o) (s.regs d)
            + bSltu (s.regs d + s.mem b o + (if s.flagB (·.cf) then 1 else 0))
                (s.regs d + s.mem b o) := by
        rw [v4]
        simp only [NE.den, carryNE, onesNE, g3.V_eq E g2.1 hx2, g3.V_eq E g2.1 l2,
          g3.V_eq E g2.1 hc2, hxv, v2, hcv, hzv]
        rw [show (BitVec.ofNat 64 ones) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl,
          carry_bit, carry_bit]
      refine ⟨((g1.trans g2).trans g3).trans g4, ?_, fun y' hy => ?_, fun y' hy => ?_⟩
      · refine (((hR1.grow g1.1 g2).grow g2.1 g3).grow g3.1 g4).setR d z ?_ _ ?_
        · exact lt_of_lt_of_le l3 (g4.size_le g3.1)
        · rw [g4.V_eq E g3.1 l3, hzv, adcx_word']
          simp only [JState.get, JState.load]
      · simp only [Option.some.injEq] at hy
        subst hy
        refine ⟨l4, ?_⟩
        rw [hwv, ← adcx_carry]
        rfl
      · obtain ⟨ly, vy⟩ := hR.2.2 y' hy
        refine ⟨lt_of_lt_of_le ly ((((g1.trans g2).trans g3).trans g4).size_le hT), ?_⟩
        rw [(((g1.trans g2).trans g3).trans g4).V_eq E hT ly]
        exact vy
  all_goals simp [symStep2] at h

theorem symRun2_sound (E : Env) : ∀ (blk : List (JInstr 64)) (T T' : Tb) (S S' : SSt2)
    (s : JState 64), symRun2 T S blk = some (T', S') → T.WF → SRel2 E T S s →
    Grows T T' ∧ SRel2 E T' S' (runBlock s blk)
  | [], T, T', S, S', s, h, hT, hR => by
      simp only [symRun2, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Grows.refl hT, hR⟩
  | i :: is, T, T', S, S', s, h, hT, hR => by
      simp only [symRun2] at h
      split at h
      · rename_i T₁ S₁ hs
        obtain ⟨g1, hR1⟩ := symStep2_sound E s i hs hT hR
        obtain ⟨g2, hR2⟩ := symRun2_sound E is T₁ T' S₁ S' (evalInstr s i) h g1.1 hR1
        exact ⟨g1.trans g2, hR2⟩
      · cases h

/-! ## 7. Part checks -/

/-- Intern an optional expression. -/
def internOpt (a : Nat) (σ : List Nat) (n : Nat) (T : Tb) : Option WE → Option (Tb × Option Nat)
  | none => some (T, none)
  | some e =>
    match internE a σ n T e with
    | some (T₁, x) => some (T₁, some x)
    | none => none

/-- Intern an entry map and the entry expressions of the two flags. -/
def enterF (a : Nat) (T : Tb) (S : SSt) (m : List (Loc × WE)) (ce ze : Option WE) :
    Option (Tb × SSt2) :=
  match enter a T S m with
  | none => none
  | some (T₁, S₁) =>
    match internOpt a [] a T₁ ce with
    | none => none
    | some (T₂, c) =>
      match internOpt a [] a T₂ ze with
      | none => none
      | some (T₃, z) => some (T₃, ⟨S₁, c, z⟩)

/-- The symbolic state lists the node of an exit flag expression. -/
def exitOptOK (a : Nat) (σ : List Nat) (n : Nat) (T : Tb) (x : Option Nat) :
    Option WE → Option Tb
  | none => some T
  | some e =>
    match internE a σ n T e, x with
    | some (T₁, y), some z => if z = y then some T₁ else none
    | _, _ => none

theorem internOpt_sound (E : Env) (a : Nat) (ρ : Nat → BitVec 64) (hW : LeafOK E a ρ)
    (T T' : Tb) (x : Option Nat) (oe : Option WE) (P : BitVec 64 → Prop)
    (h : internOpt a [] a T oe = some (T', x)) (hT : T.WF)
    (hP : ∀ e, oe = some e → P (e.eval ρ)) :
    Grows T T' ∧ ∀ y, x = some y → y < T'.size ∧ P (T'.V E y) := by
  cases oe with
  | none =>
    simp only [internOpt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grows.refl hT, fun y hy => by cases hy⟩
  | some e =>
    simp only [internOpt] at h
    split at h
    · rename_i T₁ z hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := internE_spec E a [] a e T T₁ z hz hT (fun _ hx => by cases hx)
      refine ⟨g, fun y hy => ?_⟩
      simp only [Option.some.injEq] at hy
      subst hy
      refine ⟨l, ?_⟩
      rw [v ρ ⟨hW, fun j y hy => by simp [sget_nil] at hy⟩]
      exact hP e rfl
    · cases h

theorem exitOptOK_sound (E : Env) (a : Nat) (σ : List Nat) (n : Nat) (ρ : Nat → BitVec 64)
    (T T' : Tb) (x : Option Nat) (oe : Option WE) (P : BitVec 64 → Prop)
    (h : exitOptOK a σ n T x oe = some T') (hT : T.WF) (hσ : SigOK T σ)
    (hI : SIdx E T a σ n ρ) (hx : ∀ y, x = some y → y < T.size ∧ P (T.V E y)) :
    Grows T T' ∧ ∀ e, oe = some e → P (e.eval ρ) := by
  cases oe with
  | none =>
    simp only [exitOptOK, Option.some.injEq] at h
    subst h
    exact ⟨Grows.refl hT, fun e he => by cases he⟩
  | some e =>
    simp only [exitOptOK] at h
    rcases hy : internE a σ n T e with _ | ⟨T₁, y⟩
    · rw [hy] at h; cases x <;> cases h
    rcases hxz : x with _ | z
    · rw [hy, hxz] at h; cases h
    rw [hy, hxz] at h
    simp only at h
    split_ifs at h with hzy
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨g, l, v⟩ := internE_spec E a σ n e T T₁ y hy hT hσ
    obtain ⟨lz, pz⟩ := hx z hxz
    refine ⟨g, fun e' he' => ?_⟩
    simp only [Option.some.injEq] at he'
    subst he'
    rw [← v ρ hI, ← hzy, g.V_eq E hT lz]
    exact pz

/-- The carry flag of `s` is the value of `ce`. -/
def CfHolds (ρ : Nat → BitVec 64) (ce : Option WE) (s : JState 64) : Prop :=
  ∀ e, ce = some e → (if s.flagB (·.cf) then (1 : BitVec 64) else 0) = e.eval ρ

/-- The zero flag of `s` is the zero-ness of the value of `ze`. -/
def ZfHolds (ρ : Nat → BitVec 64) (ze : Option WE) (s : JState 64) : Prop :=
  ∀ e, ze = some e → s.flagB (·.zf) = decide ((e.eval ρ).toNat = 0)

theorem enterF_sound (E : Env) (a : Nat) (ρ : Nat → BitVec 64) (hW : LeafOK E a ρ)
    (s : JState 64) (m : List (Loc × WE)) (ce ze : Option WE) (T T' : Tb) (S : SSt)
    (S' : SSt2) (h : enterF a T S m ce ze = some (T', S')) (hT : T.WF)
    (hR : SRel E T S s.regs s.mem) (hm : MapHolds ρ m s) (hc : CfHolds ρ ce s)
    (hz : ZfHolds ρ ze s) : Grows T T' ∧ SRel2 E T' S' s := by
  unfold enterF at h
  rcases hA : enter a T S m with _ | ⟨Ta, Sa⟩
  · simp [hA] at h
  simp only [hA] at h
  rcases hB : internOpt a [] a Ta ce with _ | ⟨Tb₁, cn⟩
  · simp [hB] at h
  simp only [hB] at h
  rcases hC : internOpt a [] a Tb₁ ze with _ | ⟨Tc, zn⟩
  · simp [hC] at h
  simp only [hC, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨ga, hRa⟩ := enter_sound E a ρ hW s m T Ta S Sa hA hT hR hm
  obtain ⟨gb, hcb⟩ := internOpt_sound E a ρ hW Ta Tb₁ cn ce
    (fun v => (if s.flagB (·.cf) then (1 : BitVec 64) else 0) = v) hB ga.1 hc
  obtain ⟨gc, hzc⟩ := internOpt_sound E a ρ hW Tb₁ Tc zn ze
    (fun v => s.flagB (·.zf) = decide (v.toNat = 0)) hC gb.1 hz
  refine ⟨(ga.trans gb).trans gc, (hRa.grow ga.1 gb).grow gb.1 gc, fun y hy => ?_,
    fun y hy => ?_⟩
  · obtain ⟨ly, vy⟩ := hcb y hy
    exact ⟨lt_of_lt_of_le ly (gc.size_le gb.1), by rw [gc.V_eq E gb.1 ly]; exact vy.symm⟩
  · exact hzc y hy

/-- The check of one part: the entry map and entry flags interned over the leaves below
    `a`, the statements `es` of slots `a, a + 1, …`, the symbolic run of `blk`, and the
    exit flags and exit map. -/
def partCheck2 (a : Nat) (es : List WE) (mIn : List (Loc × WE)) (cIn zIn : Option WE)
    (mOut : List (Loc × WE)) (cOut zOut : Option WE) (blk : List (JInstr 64)) : Bool :=
  match enterF a Tb.empty {} mIn cIn zIn with
  | some (T₀, S₀) =>
    match internS a [] a T₀ es with
    | some (T₁, σ) =>
      match symRun2 T₁ S₀ blk with
      | some (T₂, S₂) =>
        match exitOptOK a σ (a + es.length) T₂ S₂.cfw cOut with
        | some T₃ =>
          match exitOptOK a σ (a + es.length) T₃ S₂.zfn zOut with
          | some T₄ => exitOK a σ (a + es.length) S₂.base T₄ mOut
          | none => false
        | none => false
      | none => false
    | none => false
  | none => false

theorem partCheck2_sound (a : Nat) (es : List WE) (mIn : List (Loc × WE))
    (cIn zIn : Option WE) (mOut : List (Loc × WE)) (cOut zOut : Option WE)
    (blk : List (JInstr 64))
    (h : partCheck2 a es mIn cIn zIn mOut cOut zOut blk = true) (ρ : Nat → BitVec 64)
    (hH : Holds ρ a es) (hK : ∀ j c, j < a → cK j = some c → ρ j = BitVec.ofNat 64 c)
    (s : JState 64) (hin : MapHolds ρ mIn s) (hcin : CfHolds ρ cIn s)
    (hzin : ZfHolds ρ zIn s) :
    MapHolds ρ mOut (runBlock s blk) ∧ CfHolds ρ cOut (runBlock s blk) ∧
      ZfHolds ρ zOut (runBlock s blk) := by
  let E : Env := ⟨ρ, s⟩
  have hLeaf : LeafOK E a ρ := ⟨fun _ _ => rfl, hK⟩
  have hR0 : SRel E Tb.empty {} s.regs s.mem :=
    ⟨fun _ => rfl, fun _ _ => rfl, fun _ hp => by simp at hp, fun _ hp => by simp at hp⟩
  unfold partCheck2 at h
  rcases he : enterF a Tb.empty {} mIn cIn zIn with _ | ⟨T₀, S₀⟩
  · simp [he] at h
  simp only [he] at h
  rcases hs : internS a [] a T₀ es with _ | ⟨T₁, σ⟩
  · simp [hs] at h
  simp only [hs] at h
  rcases hr : symRun2 T₁ S₀ blk with _ | ⟨T₂, S₂⟩
  · simp [hr] at h
  simp only [hr] at h
  rcases hc : exitOptOK a σ (a + es.length) T₂ S₂.cfw cOut with _ | T₃
  · simp [hc] at h
  simp only [hc] at h
  rcases hz : exitOptOK a σ (a + es.length) T₃ S₂.zfn zOut with _ | T₄
  · simp [hz] at h
  simp only [hz] at h
  obtain ⟨g0, hR2⟩ := enterF_sound E a ρ hLeaf s mIn cIn zIn Tb.empty T₀ {} S₀ he
    Tb.empty_WF hR0 hin hcin hzin
  obtain ⟨g1, hσ1, hI1⟩ := internS_spec E a ρ es [] a T₀ T₁ σ hs g0.1
    (fun _ hx => by cases hx) hH ⟨hLeaf, fun j y hy => by simp [sget_nil] at hy⟩
  obtain ⟨g2, hRr⟩ := symRun2_sound E blk T₁ T₂ S₀ S₂ s hr g1.1 (hR2.grow g0.1 g1)
  have hσ2 : SigOK T₂ σ := hσ1.grow g1.1 g2
  have hI2 : SIdx E T₂ a σ (a + es.length) ρ := hI1.grow g1.1 g2 hσ1
  obtain ⟨g3, hcout⟩ := exitOptOK_sound E a σ (a + es.length) ρ T₂ T₃
    S₂.cfw cOut (fun v => (if (runBlock s blk).flagB (·.cf) then
      (1 : BitVec 64) else 0) = v) hc g2.1 hσ2 hI2
    (fun y hy => ⟨(hRr.2.1 y hy).1, (hRr.2.1 y hy).2.symm⟩)
  have hσ3 : SigOK T₃ σ := hσ2.grow g2.1 g3
  have hI3 : SIdx E T₃ a σ (a + es.length) ρ := hI2.grow g2.1 g3 hσ2
  obtain ⟨g4, hzout⟩ := exitOptOK_sound E a σ (a + es.length) ρ T₃ T₄
    S₂.zfn zOut (fun v => (runBlock s blk).flagB (·.zf) = decide (v.toNat = 0)) hz
    g3.1 hσ3 hI3
    (fun y hy => ⟨lt_of_lt_of_le (hRr.2.2 y hy).1 (g3.size_le g2.1),
      by rw [g3.V_eq E g2.1 (hRr.2.2 y hy).1]; exact (hRr.2.2 y hy).2⟩)
  exact ⟨exitOK_sound E a σ _ S₂.base ρ _ mOut T₄ h g4.1 (hσ3.grow g3.1 g4)
    (hI3.grow g3.1 g4 hσ3) ((hRr.1.grow g2.1 g3).grow g3.1 g4), hcout, hzout⟩

/-! ## 8. The carry chain and the product row -/

/-- The low bit of a carry word. -/
def aoW (c : BitVec 64) : BitVec 64 := c &&& BitVec.ofNat 64 1

/-- The low bit of a carry expression: the word the `bt` of a carry register reads. -/
def aoWE (c : WE) : WE := .and c (.lit 1)

theorem aoW_le_one (x : BitVec 64) : (aoW x).toNat ≤ 1 := by
  simp only [aoW, BitVec.toNat_and]
  rw [show (BitVec.ofNat 64 1).toNat = 1 from by decide +kernel, Nat.and_one_is_mod]
  omega

theorem aoW_eq_self (x : BitVec 64) (h : x.toNat ≤ 1) : aoW x = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [aoW, BitVec.toNat_and]
  rw [show (BitVec.ofNat 64 1).toNat = 1 from by decide +kernel, Nat.and_one_is_mod]
  omega

theorem aoWE_eval (ρ : Nat → BitVec 64) (c : WE) : (aoWE c).eval ρ = aoW (c.eval ρ) := rfl

/-- The carry chain over two limb lists: three slots per limb, and the handles of the
    sums followed by the handle of the final carry. -/
def feAdcG : List WE → List WE → WE → Nat → List WE × List WE
  | a :: as, b :: bs, c, n =>
      let r := feAdcG as bs (.v (n + 2)) (n + 3)
      ([.add a b, .add (.v n) (aoWE c),
        .add (carryW (.v n) a b) (carryW (.v (n + 1)) (.v n) (aoWE c))] ++ r.1,
       .v (n + 1) :: r.2)
  | [], _, c, _ => ([], [c])
  | _ :: _, [], c, _ => ([], [c])

theorem feAdcG_length : ∀ (as bs : List WE) (c : WE) (n : Nat), as.length = bs.length →
    (feAdcG as bs c n).1.length = 3 * as.length ∧ (feAdcG as bs c n).2.length = as.length + 1
  | [], [], _, _, _ => by simp [feAdcG]
  | a :: as, b :: bs, c, n, hl => by
      have ih := feAdcG_length as bs (.v (n + 2)) (n + 3) (by simpa using hl)
      simp only [feAdcG, List.length_append, List.length_cons, List.length_nil]
      omega
  | [], _ :: _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, hl => by simp at hl

theorem feAdcG_val (ρ : Nat → BitVec 64) :
    ∀ (as bs : List WE) (c : WE) (n : Nat), Holds ρ n (feAdcG as bs c n).1 →
      (c.eval ρ).toNat ≤ 1 →
      (feAdcG as bs c n).2.map (WE.eval ρ)
        = addLimbs (as.map (WE.eval ρ)) (bs.map (WE.eval ρ)) (c.eval ρ)
  | a :: as, b :: bs, c, n, h, hc => by
      simp only [feAdcG] at h ⊢
      rw [holds_append] at h
      obtain ⟨hs, hr⟩ := h
      simp only [List.length_cons, List.length_nil] at hr
      simp only [Holds, WE.eval, Nat.add_assoc, Nat.reduceAdd] at hs
      obtain ⟨h0, h1, h2, -⟩ := hs
      rw [carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h0),
        carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact h1)] at h2
      rw [aoWE_eval, aoW_eq_self _ hc] at h1
      simp only [WE.eval] at h2
      have hc2 : (ρ (n + 2)).toNat ≤ 1 := by
        rw [h2, h1, h0]
        exact adc_carry_le' _ _ _ hc
      have ih := feAdcG_val ρ as bs (.v (n + 2)) (n + 3) hr hc2
      simp only [WE.eval] at ih
      simp only [List.map_cons, WE.eval, addLimbs, ih]
      rw [h2, h1, h0]
  | [], bs, c, n, _, _ => by cases bs <;> simp [feAdcG, addLimbs]
  | a :: as, [], c, n, _, _ => by simp [feAdcG, addLimbs]

/-- The product row `xs · w + h + c`, five slots per limb and one for the top word. -/
def feRowG : List WE → WE → WE → WE → Nat → List WE × List WE
  | [], _, h, c, n => ([.add (.add h (.lit 0)) (aoWE c)], [.v n])
  | x :: xs, w, h, c, n =>
      let r := feRowG xs w (.v (n + 1)) (.v (n + 4)) (n + 5)
      ([.mul x w, .mulhi x w, .add (.v n) h, .add (.v (n + 2)) (aoWE c),
        .add (carryW (.v (n + 2)) (.v n) h)
          (carryW (.v (n + 3)) (.v (n + 2)) (aoWE c))] ++ r.1,
       .v (n + 3) :: r.2)

/-- The word value of a product row. -/
def rowW : List (BitVec 64) → BitVec 64 → BitVec 64 → BitVec 64 → List (BitVec 64)
  | [], _, h, c => [h + BitVec.ofNat 64 0 + c]
  | x :: xs, w, h, c =>
      (x * w + h + c) ::
        rowW xs w (mulhi x w)
          (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h))

theorem feRowG_length : ∀ (xs : List WE) (w h c : WE) (n : Nat),
    (feRowG xs w h c n).1.length = 5 * xs.length + 1 ∧
      (feRowG xs w h c n).2.length = xs.length + 1
  | [], _, _, _, _ => by simp [feRowG]
  | x :: xs, w, h, c, n => by
      have ih := feRowG_length xs w (.v (n + 1)) (.v (n + 4)) (n + 5)
      simp only [feRowG, List.length_append, List.length_cons, List.length_nil]
      omega

theorem rowW_length : ∀ (xs : List (BitVec 64)) (w h c : BitVec 64),
    (rowW xs w h c).length = xs.length + 1
  | [], _, _, _ => by simp [rowW]
  | x :: xs, w, h, c => by
      have ih := rowW_length xs w (mulhi x w)
        (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h))
      simp only [rowW, List.length_cons]
      omega

theorem feRowG_val (ρ : Nat → BitVec 64) :
    ∀ (xs : List WE) (w h c : WE) (n : Nat), Holds ρ n (feRowG xs w h c n).1 →
      (c.eval ρ).toNat ≤ 1 →
      (feRowG xs w h c n).2.map (WE.eval ρ)
        = rowW (xs.map (WE.eval ρ)) (w.eval ρ) (h.eval ρ) (c.eval ρ)
  | [], w, h, c, n, hh, hc => by
      simp only [feRowG, Holds, WE.eval] at hh ⊢
      simp only [List.map_nil, WE.eval, rowW, List.map_cons]
      rw [hh.1, aoWE_eval, aoW_eq_self _ hc]
  | x :: xs, w, h, c, n, hh, hc => by
      simp only [feRowG] at hh ⊢
      rw [holds_append] at hh
      obtain ⟨hs, hr⟩ := hh
      simp only [List.length_cons, List.length_nil] at hr
      simp only [Holds, WE.eval, Nat.add_assoc, Nat.reduceAdd] at hs
      obtain ⟨e0, e1, e2, e3, e4, -⟩ := hs
      rw [carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact e2),
        carryW_eval ρ _ _ _ (by simp only [WE.eval]; exact e3)] at e4
      rw [aoWE_eval, aoW_eq_self _ hc] at e3
      simp only [WE.eval] at e4
      have hc4 : (ρ (n + 4)).toNat ≤ 1 := by
        rw [e4, e3, e2, e0]
        exact adc_carry_le' _ _ _ hc
      have ih := feRowG_val ρ xs w (.v (n + 1)) (.v (n + 4)) (n + 5) hr hc4
      simp only [WE.eval] at ih
      simp only [List.map_cons, WE.eval, rowW, ih]
      rw [e4, e3, e2, e1, e0]

/-! ## 9. The field blocks -/

/-- Bitwise or, as exclusive-or and and. -/
def orWE (a b : WE) : WE := .xor (.xor a b) (.and a b)

/-- The all-ones mask when `z` is nonzero and the zero mask otherwise. -/
def maskWE (z : WE) : WE := .sub (.lit 0) (.shr (orWE z (.sub (.lit 0) z)) 63)

/-- The zero-flag expression of `testq %r, %r`. -/
def tstWE (z : WE) : WE := .and z z

/-- `a` when `z` is nonzero and `b` otherwise, over the zero flag of `testq z, z`. -/
def selWE (z a b : WE) : WE :=
  .xor (.and a (maskWE (tstWE z))) (.and b (.xor (maskWE (tstWE z)) (.lit ones)))

theorem selWE_eval (ρ : Nat → BitVec 64) (z a b : WE) :
    (selWE z a b).eval ρ = selW (z.eval ρ) (a.eval ρ) (b.eval ρ) := by
  show (a.eval ρ &&& maskB ((tstWE z).eval ρ))
      ^^^ (b.eval ρ &&& (maskB ((tstWE z).eval ρ) ^^^ BitVec.ofNat 64 ones)) = _
  rw [selB_eq]
  simp only [tstWE, WE.eval, BitVec.and_self]

/-- The per-limb select of two limb lists on a carry word. -/
def feSelG (z : WE) : List WE → List WE → Nat → List WE × List WE
  | a :: as, b :: bs, n =>
      let r := feSelG z as bs (n + 1)
      (selWE z a b :: r.1, .v n :: r.2)
  | [], _, _ => ([], [])
  | _ :: _, [], _ => ([], [])

/-- The limb list select. -/
def selL (z : BitVec 64) (as bs : List (BitVec 64)) : List (BitVec 64) :=
  if z.toNat = 0 then bs else as

theorem feSelG_val (ρ : Nat → BitVec 64) (z : WE) :
    ∀ (as bs : List WE) (n : Nat), Holds ρ n (feSelG z as bs n).1 → as.length = bs.length →
      (feSelG z as bs n).2.map (WE.eval ρ)
        = selL (z.eval ρ) (as.map (WE.eval ρ)) (bs.map (WE.eval ρ))
  | a :: as, b :: bs, n, h, hl => by
      simp only [feSelG, Holds] at h ⊢
      have ih := feSelG_val ρ z as bs (n + 1) h.2 (by simpa using hl)
      rw [List.map_cons, ih]
      simp only [WE.eval]
      rw [h.1, selWE_eval]
      simp only [selW, selL, List.map_cons]
      split <;> rfl
  | [], bs, n, _, hl => by cases bs <;> simp_all [feSelG, selL]
  | a :: as, [], n, _, hl => by simp at hl

/-- The limbs of `2^256 - p25519`. -/
def kCE : List WE := [.lit 19, .lit 0, .lit 0, .lit (2 ^ 63)]

/-- The limbs of `p25519`. -/
def pWE : List WE := [.lit (2 ^ 64 - 19), .lit (2 ^ 64 - 1), .lit (2 ^ 64 - 1), .lit (2 ^ 63 - 1)]

/-- One conditional subtraction of `p25519`. -/
def feCsubG (xs : List WE) (n : Nat) : List WE × List WE :=
  let d := feAdcG xs kCE (.lit 0) n
  let s := feSelG (d.2.getLastD (.lit 0)) d.2.dropLast xs (n + d.1.length)
  (d.1 ++ s.1, s.2)

/-- Field addition. -/
def feAddG (xs ys : List WE) (n : Nat) : List WE × List WE :=
  let d := feAdcG xs ys (.lit 0) n
  let c := feCsubG d.2.dropLast (n + d.1.length)
  (d.1 ++ c.1, c.2)

/-- Field subtraction. -/
def feSubG (xs ys : List WE) (n : Nat) : List WE × List WE :=
  let d := feAdcG xs (ys.map notW) (.lit 1) n
  let m := n + d.1.length
  let e := feAdcG d.2.dropLast pWE (.lit 0) m
  let s := feSelG (d.2.getLastD (.lit 0)) d.2.dropLast e.2.dropLast (m + e.1.length)
  (d.1 ++ (e.1 ++ s.1), s.2)

/-- One accumulation step of the schoolbook product. -/
def feAccG (i : Nat) (xs : List WE) (y : WE) (acc : List WE) (n : Nat) : List WE × List WE :=
  let r := feRowG xs y (.lit 0) (.lit 0) n
  let s := feAdcG (acc.drop i ++ [.lit 0]) r.2 (.lit 0) (n + r.1.length)
  (r.1 ++ s.1, acc.take i ++ s.2.dropLast)

/-- The schoolbook product of four limbs by four limbs, as eight limbs. -/
def feProdG (xs : List WE) (y0 y1 y2 y3 : WE) (n : Nat) : List WE × List WE :=
  let r0 := feRowG xs y0 (.lit 0) (.lit 0) n
  let r1 := feAccG 1 xs y1 r0.2 (n + r0.1.length)
  let r2 := feAccG 2 xs y2 r1.2 (n + r0.1.length + r1.1.length)
  let r3 := feAccG 3 xs y3 r2.2 (n + r0.1.length + r1.1.length + r2.1.length)
  (r0.1 ++ (r1.1 ++ (r2.1 ++ r3.1)), r3.2)

/-- The fold of the fifth limb with `2^256 ≡ 38`, the carry fold, and the two
    conditional subtractions. -/
def feFoldG (S : List WE) (n : Nat) : List WE × List WE :=
  let m := feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n
  let n3 := n + m.1.length
  let u := feAdcG (S.take 4) (m.2 ++ [.lit 0, .lit 0]) (.lit 0) n3
  let n4 := n3 + u.1.length
  let mm := selWE (u.2.getLastD (.lit 0)) (.lit 38) (.lit 0)
  let v := feAdcG u.2.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4
  let n5 := n4 + v.1.length
  let c1 := feCsubG v.2.dropLast n5
  let c2 := feCsubG c1.2 (n5 + c1.1.length)
  (m.1 ++ (u.1 ++ (v.1 ++ (c1.1 ++ c2.1))), c2.2)

/-- The reduction of eight limbs modulo `p25519`. -/
def feRedG (ps : List WE) (n : Nat) : List WE × List WE :=
  let r := feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n
  let n1 := n + r.1.length
  let s := feAdcG (ps.take 4 ++ [.lit 0]) r.2 (.lit 0) n1
  let f := feFoldG s.2.dropLast (n1 + s.1.length)
  (r.1 ++ (s.1 ++ f.1), f.2)

/-- Field multiplication. -/
def feMulG (xs ys : List WE) (n : Nat) : List WE × List WE :=
  let p := feProdG xs (ys.getD 0 (.lit 0)) (ys.getD 1 (.lit 0)) (ys.getD 2 (.lit 0))
    (ys.getD 3 (.lit 0)) n
  let r := feRedG p.2 (n + p.1.length)
  (p.1 ++ r.1, r.2)

/-- The copy block: one `or` of a limb with itself per limb. -/
def feCopyG (xs : List WE) (n : Nat) : List WE × List WE :=
  (xs.map (fun x => orWE x x), (List.range xs.length).map (fun i => .v (n + i)))

/-! ## 10. The program -/

/-- `2·d` of the Ed25519 curve, as a natural below `p25519`. -/
def twoDNat : Nat :=
  16295367250680780974490674513165176452449235426866156013048779062215315747161

/-- The four limbs of `2·d`. -/
def twoDLimbs : List WE :=
  [.lit (twoDNat % 2 ^ 64), .lit (twoDNat / 2 ^ 64 % 2 ^ 64),
   .lit (twoDNat / 2 ^ 128 % 2 ^ 64), .lit (twoDNat / 2 ^ 192 % 2 ^ 64)]

/-! ## 10. The program -/

/-- The limbs of `Y₁ − X₁`. -/
def paB1 : List WE × List WE := feSubG (slotsFrom 29 4) (slotsFrom 25 4) 57
/-- The slot after the first block. -/
def paN1 : Nat := 57 + paB1.1.length
/-- The limbs of `Y₂ − X₂`. -/
def paB2 : List WE × List WE := feSubG (slotsFrom 45 4) (slotsFrom 41 4) paN1
/-- The slot after the second block. -/
def paN2 : Nat := paN1 + paB2.1.length
/-- The limbs of `A = (Y₁ − X₁)(Y₂ − X₂)`. -/
def paB3 : List WE × List WE := feMulG paB1.2 paB2.2 paN2
/-- The slot after the third block. -/
def paN3 : Nat := paN2 + paB3.1.length
/-- The limbs of `Y₁ + X₁`. -/
def paB4 : List WE × List WE := feAddG (slotsFrom 29 4) (slotsFrom 25 4) paN3
/-- The slot after the fourth block. -/
def paN4 : Nat := paN3 + paB4.1.length
/-- The limbs of `Y₂ + X₂`. -/
def paB5 : List WE × List WE := feAddG (slotsFrom 45 4) (slotsFrom 41 4) paN4
/-- The slot after the fifth block. -/
def paN5 : Nat := paN4 + paB5.1.length
/-- The limbs of `B = (Y₁ + X₁)(Y₂ + X₂)`. -/
def paB6 : List WE × List WE := feMulG paB4.2 paB5.2 paN5
/-- The slot after the sixth block. -/
def paN6 : Nat := paN5 + paB6.1.length
/-- The limbs of `T₁ · 2d`. -/
def paB8 : List WE × List WE := feMulG (slotsFrom 37 4) twoDLimbs paN6
/-- The slot after the seventh block. -/
def paN8 : Nat := paN6 + paB8.1.length
/-- The limbs of `C = T₁ · 2d · T₂`. -/
def paB9 : List WE × List WE := feMulG paB8.2 (slotsFrom 53 4) paN8
/-- The slot after the eighth block. -/
def paN9 : Nat := paN8 + paB9.1.length
/-- The limbs of `2Z₁`. -/
def paB10 : List WE × List WE := feAddG (slotsFrom 33 4) (slotsFrom 33 4) paN9
/-- The slot after the ninth block. -/
def paN10 : Nat := paN9 + paB10.1.length
/-- The limbs of `D = 2Z₁ · Z₂`. -/
def paB11 : List WE × List WE := feMulG paB10.2 (slotsFrom 49 4) paN10
/-- The slot after the tenth block. -/
def paN11 : Nat := paN10 + paB11.1.length
/-- The limbs of `E = B − A`. -/
def paB12 : List WE × List WE := feSubG paB6.2 paB3.2 paN11
/-- The slot after the eleventh block. -/
def paN12 : Nat := paN11 + paB12.1.length
/-- The limbs of `F = D − C`. -/
def paB13 : List WE × List WE := feSubG paB11.2 paB9.2 paN12
/-- The slot after the twelfth block. -/
def paN13 : Nat := paN12 + paB13.1.length
/-- The limbs of `G = D + C`. -/
def paB14 : List WE × List WE := feAddG paB11.2 paB9.2 paN13
/-- The slot after the thirteenth block. -/
def paN14 : Nat := paN13 + paB14.1.length
/-- The limbs of `H = B + A`. -/
def paB15 : List WE × List WE := feAddG paB6.2 paB3.2 paN14
/-- The slot after the fourteenth block. -/
def paN15 : Nat := paN14 + paB15.1.length
/-- The limbs of `X₃ = E · F`. -/
def paB16 : List WE × List WE := feMulG paB12.2 paB13.2 paN15
/-- The slot after the fifteenth block. -/
def paN16 : Nat := paN15 + paB16.1.length
/-- The limbs of `Y₃ = G · H`. -/
def paB17 : List WE × List WE := feMulG paB14.2 paB15.2 paN16
/-- The slot after the sixteenth block. -/
def paN17 : Nat := paN16 + paB17.1.length
/-- The limbs of `T₃ = E · H`. -/
def paB18 : List WE × List WE := feMulG paB12.2 paB15.2 paN17
/-- The slot after the seventeenth block. -/
def paN18 : Nat := paN17 + paB18.1.length
/-- The limbs of `Z₃ = F · G`. -/
def paB19 : List WE × List WE := feMulG paB13.2 paB14.2 paN18
/-- The slot after the eighteenth block. -/
def paN19 : Nat := paN18 + paB19.1.length
/-- The copy of `X₃`. -/
def paC1 : List WE × List WE := feCopyG paB16.2 paN19
/-- The copy of `Y₃`. -/
def paC2 : List WE × List WE := feCopyG paB17.2 (paN19 + paC1.1.length)
/-- The copy of `Z₃`. -/
def paC3 : List WE × List WE := feCopyG paB19.2 (paN19 + paC1.1.length + paC2.1.length)
/-- The copy of `T₃`. -/
def paC4 : List WE × List WE :=
  feCopyG paB18.2 (paN19 + paC1.1.length + paC2.1.length + paC3.1.length)

/-- The statements of the addition over the input slots `25 .. 56`, from slot `57`, and
    the sixteen output handles: the limbs of `X₃`, `Y₃`, `Z₃`, `T₃`. -/
def paG : List WE × List WE :=
  (paB1.1 ++ (paB2.1 ++ (paB3.1 ++ (paB4.1 ++ (paB5.1 ++ (paB6.1 ++ (paB8.1 ++ (paB9.1 ++
    (paB10.1 ++ (paB11.1 ++ (paB12.1 ++ (paB13.1 ++ (paB14.1 ++ (paB15.1 ++ (paB16.1 ++
    (paB17.1 ++ (paB18.1 ++ (paB19.1 ++ (paC1.1 ++ (paC2.1 ++ (paC3.1 ++ paC4.1)))))))))))))))))))),
   paC1.2 ++ (paC2.2 ++ (paC3.2 ++ paC4.2)))



/-- The statements of the addition from slot `57`. -/
def paStmts : List WE := paG.1

/-- The sixteen output handles: the limbs of `X₃`, `Y₃`, `Z₃`, `T₃`. -/
def paOuts : List WE := paG.2

/-- The thirty-two input limbs: cell `(%rsi, 8i)` holds slot `25 + i`. -/
def paIn : List (Loc × WE) :=
  (List.range 32).map (fun i => (Loc.cell "%rsi" ((8 * i : Nat) : Int), WE.v (25 + i)))

/-- The sixteen output limbs: cell `(%rdi, 8j)` holds output handle `j`. -/
def paOut : List (Loc × WE) :=
  (List.range 16).map (fun j => (Loc.cell "%rdi" ((8 * j : Nat) : Int), paOuts.getD j (.lit 0)))


/-- The statements from slot `57`, the argument of the first part. -/
def paR1 : List WE := paStmts
/-- The statements of part 1. -/
def paSl1 : List WE := paR1.take 182
/-- The statements from slot `239`. -/
def paR2 : List WE := paR1.drop 182
/-- The statements of part 2. -/
def paSl2 : List WE := paR2.take 260
/-- The statements from slot `499`. -/
def paR3 : List WE := paR2.drop 260
/-- The statements of part 3. -/
def paSl3 : List WE := paR3.take 263
/-- The statements from slot `762`. -/
def paR4 : List WE := paR3.drop 263
/-- The statements of part 4. -/
def paSl4 : List WE := paR4.take 258
/-- The statements from slot `1020`. -/
def paR5 : List WE := paR4.drop 258
/-- The statements of part 5. -/
def paSl5 : List WE := paR5.take 250
/-- The statements from slot `1270`. -/
def paR6 : List WE := paR5.drop 250
/-- The statements of part 6. -/
def paSl6 : List WE := paR6.take 225
/-- The statements from slot `1495`. -/
def paR7 : List WE := paR6.drop 225
/-- The statements of part 7. -/
def paSl7 : List WE := paR7.take 253
/-- The statements from slot `1748`. -/
def paR8 : List WE := paR7.drop 253
/-- The statements of part 8. -/
def paSl8 : List WE := paR8.take 248
/-- The statements from slot `1996`. -/
def paR9 : List WE := paR8.drop 248
/-- The statements of part 9. -/
def paSl9 : List WE := paR9.take 255
/-- The statements of part 10. -/
def paSl10 : List WE := paR9.drop 255

theorem paStmts_length : paStmts.length = 2311 := by decide +kernel

theorem paR1_len : paR1.length = 2311 := paStmts_length
theorem paSl1_len : paSl1.length = 182 := by
  rw [paSl1, List.length_take, paR1_len]
  omega
theorem paR2_len : paR2.length = 2129 := by rw [paR2, List.length_drop, paR1_len]
theorem paSl2_len : paSl2.length = 260 := by
  rw [paSl2, List.length_take, paR2_len]
  omega
theorem paR3_len : paR3.length = 1869 := by rw [paR3, List.length_drop, paR2_len]
theorem paSl3_len : paSl3.length = 263 := by
  rw [paSl3, List.length_take, paR3_len]
  omega
theorem paR4_len : paR4.length = 1606 := by rw [paR4, List.length_drop, paR3_len]
theorem paSl4_len : paSl4.length = 258 := by
  rw [paSl4, List.length_take, paR4_len]
  omega
theorem paR5_len : paR5.length = 1348 := by rw [paR5, List.length_drop, paR4_len]
theorem paSl5_len : paSl5.length = 250 := by
  rw [paSl5, List.length_take, paR5_len]
  omega
theorem paR6_len : paR6.length = 1098 := by rw [paR6, List.length_drop, paR5_len]
theorem paSl6_len : paSl6.length = 225 := by
  rw [paSl6, List.length_take, paR6_len]
  omega
theorem paR7_len : paR7.length = 873 := by rw [paR7, List.length_drop, paR6_len]
theorem paSl7_len : paSl7.length = 253 := by
  rw [paSl7, List.length_take, paR7_len]
  omega
theorem paR8_len : paR8.length = 620 := by rw [paR8, List.length_drop, paR7_len]
theorem paSl8_len : paSl8.length = 248 := by
  rw [paSl8, List.length_take, paR8_len]
  omega
theorem paR9_len : paR9.length = 372 := by rw [paR9, List.length_drop, paR8_len]
theorem paSl9_len : paSl9.length = 255 := by
  rw [paSl9, List.length_take, paR9_len]
  omega

/-- The locations after part 1. -/
def paMap1 : List (Loc × WE) :=
  [rg "%r9" (.lit 0), rg "%rsi" (.v 237), rg "%rbp" (.v 234), rg "%rcx" (.v 231),
    rg "%r8" (.v 228), rg "%rax" (.v 226), sk 8 (.v 192), sk 0 (.v 156), sk 40 (.v 116),
    sk 144 (.v 25), sk 152 (.v 26), sk 168 (.v 27), sk 184 (.v 28), sk 80 (.v 29),
    sk 88 (.v 30), sk 96 (.v 31), sk 104 (.v 32), sk 232 (.v 33), sk 240 (.v 34),
    sk 248 (.v 35), sk 256 (.v 36), sk 160 (.v 37), sk 176 (.v 38), sk 192 (.v 39),
    sk 200 (.v 40), sk 208 (.v 41), sk 216 (.v 42), sk 224 (.v 43), sk 264 (.v 44),
    sk 112 (.v 45), sk 120 (.v 46), sk 128 (.v 47), sk 136 (.v 48), sk 304 (.v 49),
    sk 312 (.v 50), sk 320 (.v 51), sk 328 (.v 52), sk 272 (.v 53), sk 280 (.v 54),
    sk 288 (.v 55), sk 296 (.v 56)]

/-- The locations after part 2. -/
def paMap2 : List (Loc × WE) :=
  [rg "%r10" (.v 498), rg "%r13" (.v 497), rg "%r8" (.v 495), rg "%r11" (.v 492),
    rg "%rax" (.lit 0), rg "%rbp" (.v 484), rg "%rdi" (.v 481), rg "%rsi" (.v 478),
    sk 224 (.v 487), sk 136 (.v 475), sk 128 (.v 439), sk 264 (.v 399), sk 216 (.v 395),
    sk 184 (.v 367), sk 168 (.v 366), sk 72 (.v 339), sk 64 (.v 338), sk 56 (.v 337),
    sk 48 (.v 336), sk 232 (.v 33), sk 240 (.v 34), sk 248 (.v 35), sk 256 (.v 36),
    sk 160 (.v 37), sk 176 (.v 38), sk 192 (.v 39), sk 200 (.v 40), sk 304 (.v 49),
    sk 312 (.v 50), sk 320 (.v 51), sk 328 (.v 52), sk 272 (.v 53), sk 280 (.v 54),
    sk 288 (.v 55), sk 296 (.v 56)]

/-- The locations after part 3. -/
def paMap3 : List (Loc × WE) :=
  [rg "%rbp" (.v 747), rg "%r13" (.v 761), rg "%rax" (.v 760), rg "%r10" (.v 758),
    rg "%rsi" (.v 755), rg "%rcx" (.lit 0), rg "%rbx" (.lit 38), rg "%r9" (.v 750),
    rg "%rdi" (.v 747), rg "%r8" (.v 738), sk 136 (.v 702), sk 128 (.v 666),
    sk 184 (.v 626), sk 264 (.v 622), sk 224 (.v 621), sk 216 (.v 620), sk 208 (.v 619),
    sk 72 (.v 339), sk 64 (.v 338), sk 56 (.v 337), sk 48 (.v 336), sk 232 (.v 33),
    sk 240 (.v 34), sk 248 (.v 35), sk 256 (.v 36), sk 304 (.v 49), sk 312 (.v 50),
    sk 320 (.v 51), sk 328 (.v 52), sk 272 (.v 53), sk 280 (.v 54), sk 288 (.v 55),
    sk 296 (.v 56)]

/-- The locations after part 4. -/
def paMap4 : List (Loc × WE) :=
  [rg "%r9" (.v 1016), rg "%r13" (.v 1019), rg "%r8" (.v 1018), rg "%rbp" (.lit 0),
    rg "%rdi" (.v 1010), rg "%rcx" (.v 1007), rg "%rsi" (.v 1004), rg "%r11" (.v 1001),
    rg "%rbx" (.lit 0), rg "%rax" (.lit 38), sk 264 (.v 622), sk 224 (.v 621),
    sk 216 (.v 620), sk 208 (.v 619), sk 72 (.v 339), sk 64 (.v 338), sk 56 (.v 337),
    sk 48 (.v 336), sk 232 (.v 33), sk 240 (.v 34), sk 248 (.v 35), sk 256 (.v 36),
    sk 304 (.v 49), sk 312 (.v 50), sk 320 (.v 51), sk 328 (.v 52)]

/-- The locations after part 5. -/
def paMap5 : List (Loc × WE) :=
  [rg "%r8" (.v 1268), rg "%rdi" (.v 1265), rg "%rax" (.v 1262), rg "%rsi" (.v 1259),
    rg "%r11" (.v 1256), rg "%rcx" (.lit 0), rg "%rbx" (.lit 38), sk 296 (.v 1076),
    sk 288 (.v 1075), sk 280 (.v 1074), sk 272 (.v 1073), sk 264 (.v 622),
    sk 224 (.v 621), sk 216 (.v 620), sk 208 (.v 619), sk 72 (.v 339), sk 64 (.v 338),
    sk 56 (.v 337), sk 48 (.v 336)]

/-- The locations after part 6. -/
def paMap6 : List (Loc × WE) :=
  [rg "%r8" (.v 1464), rg "%rax" (.v 1493), rg "%rsi" (.v 1490), rg "%rbx" (.lit 0),
    rg "%rcx" (.v 1485), sk 208 (.v 1487), sk 216 (.v 1483), sk 304 (.v 1447),
    sk 288 (.v 1443), sk 280 (.v 1442), sk 272 (.v 1441), sk 264 (.v 1440),
    sk 328 (.v 1415), sk 320 (.v 1414), sk 312 (.v 1413), sk 296 (.v 1412),
    sk 200 (.v 1387), sk 192 (.v 1386), sk 184 (.v 1385), sk 176 (.v 1384),
    sk 256 (.v 1359), sk 248 (.v 1358), sk 240 (.v 1357), sk 232 (.v 1356)]

/-- The locations after part 7. -/
def paMap7 : List (Loc × WE) :=
  [rg "%rax" (.v 1746), rg "%rsi" (.v 1744), rg "%r12" (.v 1741), rg "%r13" (.v 1736),
    rg "%r11" (.v 1731), rg "%rcx" (.v 1717), rg "%r8" (.v 1723), rg "%rdi" (.v 1720),
    sk (-128) (.lit 0), sk 160 (.v 1726), sk 144 (.v 1714), sk 168 (.v 1674),
    sk 304 (.v 1670), sk 224 (.v 1669), sk 216 (.v 1668), sk 208 (.v 1667),
    sk 288 (.v 1443), sk 280 (.v 1442), sk 272 (.v 1441), sk 264 (.v 1440),
    sk 328 (.v 1415), sk 320 (.v 1414), sk 312 (.v 1413), sk 296 (.v 1412),
    sk 200 (.v 1387), sk 192 (.v 1386), sk 184 (.v 1385), sk 176 (.v 1384),
    sk 256 (.v 1359), sk 248 (.v 1358), sk 240 (.v 1357), sk 232 (.v 1356)]

/-- The locations after part 8. -/
def paMap8 : List (Loc × WE) :=
  [rg "%r14" (.v 1443), rg "%rdx" (.v 1357), rg "%r12" (.v 1995), rg "%r11" (.v 1994),
    rg "%r10" (.v 1992), rg "%rax" (.lit 0), rg "%rcx" (.v 1980), rg "%rsi" (.v 1986),
    rg "%rdi" (.v 1983), sk 280 (.v 1989), sk 264 (.v 1977), sk 128 (.v 1941),
    sk 136 (.v 1901), sk 168 (.v 1897), sk 160 (.v 1896), sk 152 (.v 1895),
    sk 144 (.v 1894), sk 304 (.v 1670), sk 224 (.v 1669), sk 216 (.v 1668),
    sk 208 (.v 1667), sk 288 (.v 1443), sk 328 (.v 1415), sk 320 (.v 1414),
    sk 312 (.v 1413), sk 296 (.v 1412), sk 200 (.v 1387), sk 192 (.v 1386),
    sk 184 (.v 1385), sk 176 (.v 1384), sk 256 (.v 1359), sk 248 (.v 1358)]

/-- The locations after part 9. -/
def paMap9 : List (Loc × WE) :=
  [rg "%r9" (.lit 0), rg "%rsi" (.v 2249), rg "%rdi" (.v 2246), rg "%rcx" (.v 2243),
    rg "%r8" (.v 2240), rg "%rbx" (.v 2238), sk 296 (.v 2204), sk 248 (.v 2168),
    sk 256 (.v 2128), sk 288 (.v 2124), sk 280 (.v 2123), sk 272 (.v 2122),
    sk 264 (.v 2121), sk 168 (.v 1897), sk 160 (.v 1896), sk 152 (.v 1895),
    sk 144 (.v 1894), sk 304 (.v 1670), sk 224 (.v 1669), sk 216 (.v 1668),
    sk 208 (.v 1667)]

theorem pa_part1 :
    partCheck2 57 paSl1 paIn none none paMap1 (some (aoWE (.v 238))) none
      (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true := by
  decide +kernel

theorem pa_part2 :
    partCheck2 239 paSl2 paMap1 (some (aoWE (.v 238))) none paMap2 none none
      (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02) = true := by
  decide +kernel

theorem pa_part3 :
    partCheck2 499 paSl3 paMap2 none none paMap3 (some (.v 761)) none
      (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03) = true := by
  decide +kernel

theorem pa_part4 :
    partCheck2 762 paSl4 paMap3 (some (.v 761)) none paMap4 (some (.v 1019))
      none (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04) = true := by
  decide +kernel

theorem pa_part5 :
    partCheck2 1020 paSl5 paMap4 (some (.v 1019)) none paMap5
      (some (.v 1269)) none
      (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05) = true := by
  decide +kernel

theorem pa_part6 :
    partCheck2 1270 paSl6 paMap5 (some (.v 1269)) none paMap6
      (some (aoWE (.v 1494))) none
      (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06) = true := by
  decide +kernel

theorem pa_part7 :
    partCheck2 1495 paSl7 paMap6 (some (aoWE (.v 1494))) none paMap7
      (some (.v 1747)) none
      (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07) = true := by
  decide +kernel

theorem pa_part8 :
    partCheck2 1748 paSl8 paMap7 (some (.v 1747)) none paMap8 none none
      (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08) = true := by
  decide +kernel

theorem pa_part9 :
    partCheck2 1996 paSl9 paMap8 none none paMap9 (some (aoWE (.v 2250)))
      none (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09) = true := by
  decide +kernel

theorem pa_part10 :
    partCheck2 2251 paSl10 paMap9 (some (aoWE (.v 2250))) none paOut none none
      (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10) = true := by
  decide +kernel


/-! ## 12. The values of the field blocks -/

/-- The limbs of `2^256 - p25519` as words. -/
def kCV : List (BitVec 64) :=
  [BitVec.ofNat 64 19, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 (2 ^ 63)]

/-- The limbs of `p25519` as words. -/
def pV : List (BitVec 64) :=
  [BitVec.ofNat 64 (2 ^ 64 - 19), BitVec.ofNat 64 (2 ^ 64 - 1), BitVec.ofNat 64 (2 ^ 64 - 1),
   BitVec.ofNat 64 (2 ^ 63 - 1)]

theorem kCE_eval (ρ : Nat → BitVec 64) : kCE.map (WE.eval ρ) = kCV := rfl

theorem pWE_eval (ρ : Nat → BitVec 64) : pWE.map (WE.eval ρ) = pV := rfl

theorem bignumVal_kCV : bignumVal kCV = 2 ^ 255 + 19 := by
  simp only [kCV, bignumVal, BitVec.toNat_ofNat]
  norm_num

theorem bignumVal_pV : bignumVal pV = 2 ^ 255 - 19 := by
  simp only [pV, bignumVal, BitVec.toNat_ofNat]
  norm_num

theorem lit0_le_one (ρ : Nat → BitVec 64) : ((WE.lit 0).eval ρ).toNat ≤ 1 := by
  show (BitVec.ofNat 64 0).toNat ≤ 1
  decide +kernel

theorem lit1_le_one (ρ : Nat → BitVec 64) : ((WE.lit 1).eval ρ).toNat ≤ 1 := by
  show (BitVec.ofNat 64 1).toNat ≤ 1
  decide +kernel

/-- The split of a carry-chain result into its low limbs and its top limb. -/
theorem split_top (l : List (BitVec 64)) (k : Nat) (hl : l.length = k + 1) :
    bignumVal l = bignumVal l.dropLast + (2 ^ 64) ^ k * (l.getLastD 0).toNat := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_concat_getLast hne
  have hdl : l.dropLast.length = k := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hl] at hc
    omega
  have hgd : l.getLastD 0 = l.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  have hbs := bignumVal_snoc l.dropLast (l.getLast hne)
  rw [hsplit, hdl] at hbs
  rw [hbs, hgd]
  ring


theorem lit0_eval (ρ : Nat → BitVec 64) : (WE.lit 0).eval ρ = 0 := rfl

theorem feSelG_length (z : WE) : ∀ (as bs : List WE) (n : Nat), as.length = bs.length →
    (feSelG z as bs n).1.length = as.length ∧ (feSelG z as bs n).2.length = as.length
  | [], [], _, _ => by simp [feSelG]
  | a :: as, b :: bs, n, hl => by
      have ih := feSelG_length z as bs (n + 1) (by simpa using hl)
      simp only [feSelG, List.length_cons]
      omega
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem feCsubG_length (xs : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feCsubG xs n).2.length = 4 := by
  have hlen : xs.length = kCE.length := by rw [h4]; rfl
  obtain ⟨-, hdl⟩ := feAdcG_length xs kCE (.lit 0) n hlen
  simp only [feCsubG]
  rw [(feSelG_length _ _ xs _ (by rw [List.length_dropLast, hdl, h4])).2,
    List.length_dropLast, hdl, h4]

theorem feCsubG_val (ρ : Nat → BitVec 64) (xs : List WE) (n : Nat)
    (h : Holds ρ n (feCsubG xs n).1) (h4 : xs.length = 4) :
    bignumVal ((feCsubG xs n).2.map (WE.eval ρ))
      = (if 2 ^ 255 - 19 ≤ bignumVal (xs.map (WE.eval ρ))
         then bignumVal (xs.map (WE.eval ρ)) - (2 ^ 255 - 19)
         else bignumVal (xs.map (WE.eval ρ))) := by
  have hlen : xs.length = kCE.length := by rw [h4]; rfl
  simp only [feCsubG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, hs⟩ := h
  have hdv := feAdcG_val ρ xs kCE (.lit 0) n hd (lit0_le_one ρ)
  rw [kCE_eval, lit0_eval] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs kCE (.lit 0) n hlen
  rw [h4] at hdl
  have hkl : (xs.map (WE.eval ρ)).length = kCV.length := by simp [h4, kCV]
  have hDval : bignumVal (addLimbs (xs.map (WE.eval ρ)) kCV 0)
      = bignumVal (xs.map (WE.eval ρ)) + (2 ^ 255 + 19) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hkl, bignumVal_kCV]
    rfl
  have hDlen : (addLimbs (xs.map (WE.eval ρ)) kCV 0).length = 5 := by
    rw [addLimbs_length _ _ _ hkl]
    simp [h4]
  have hsplit := split_top (addLimbs (xs.map (WE.eval ρ)) kCV 0) 4 hDlen
  have hXlt : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 256 := by
    have := bignumVal_lt (xs.map (WE.eval ρ))
    simp only [List.length_map, h4] at this
    norm_num at this
    exact this
  have hDdl : bignumVal (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast < 2 ^ 256 := by
    have := bignumVal_lt (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast
    rw [List.length_dropLast, hDlen] at this
    norm_num at this
    exact this
  have hpow : ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 := by norm_num
  rw [hpow, hDval] at hsplit
  -- the select
  have hsl := feSelG_val ρ ((feAdcG xs kCE (.lit 0) n).2.getLastD (.lit 0))
    (feAdcG xs kCE (.lit 0) n).2.dropLast xs _ hs
    (by rw [List.length_dropLast, hdl, h4])
  rw [hsl]
  have hz : WE.eval ρ ((feAdcG xs kCE (.lit 0) n).2.getLastD (.lit 0))
      = (addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0 := by
    rw [← hdv, ← lit0_eval ρ, List.getLastD_map]
  have hdrop : ((feAdcG xs kCE (.lit 0) n).2.dropLast).map (WE.eval ρ)
      = (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast := by
    rw [List.map_dropLast, hdv]
  rw [hz, hdrop]
  have htop := ((addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0).isLt
  simp only [selL]
  split
  · rename_i hz0
    rw [if_neg (by omega)]
  · rename_i hz0
    have h1 : ((addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0).toNat = 1 := by omega
    rw [h1] at hsplit
    rw [if_pos (by omega)]
    omega


theorem bnlt4 (l : List (BitVec 64)) (h : l.length = 4) : bignumVal l < 2 ^ 256 := by
  have h2 := bignumVal_lt l
  rw [h, show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at h2
  exact h2

theorem feAddG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) (h4' : ys.length = 4) :
    (feAddG xs ys n).2.length = 4 := by
  obtain ⟨-, hdl⟩ := feAdcG_length xs ys (.lit 0) n (by rw [h4, h4'])
  rw [h4] at hdl
  simp only [feAddG]
  exact feCsubG_length _ _ (by rw [List.length_dropLast, hdl])

theorem feAddG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feAddG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feAddG xs ys n).2.map (WE.eval ρ))
      = (bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ))) % (2 ^ 255 - 19) := by
  simp only [feAddG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, hc⟩ := h
  have hlen : xs.length = ys.length := by rw [h4, h4']
  have hdv := feAdcG_val ρ xs ys (.lit 0) n hd (lit0_le_one ρ)
  rw [lit0_eval] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs ys (.lit 0) n hlen
  rw [h4] at hdl
  have hml : (xs.map (WE.eval ρ)).length = (ys.map (WE.eval ρ)).length := by
    simp [h4, h4']
  have hDval : bignumVal (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0)
      = bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ)) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hml]
    rfl
  have hDlen : (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).length = 5 := by
    rw [addLimbs_length _ _ _ hml]
    simp [h4]
  have hsplit := split_top (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0) 4 hDlen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hDval] at hsplit
  have hddl := bnlt4 (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).dropLast
    (by rw [List.length_dropLast, hDlen])
  have hdrop : ((feAdcG xs ys (.lit 0) n).2.dropLast).map (WE.eval ρ)
      = (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).dropLast := by
    rw [List.map_dropLast, hdv]
  have hlow : bignumVal (((feAdcG xs ys (.lit 0) n).2.dropLast).map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ)) := by
    rw [hdrop]
    omega
  have hcv := feCsubG_val ρ (feAdcG xs ys (.lit 0) n).2.dropLast _ hc
    (by rw [List.length_dropLast, hdl])
  rw [hcv, hlow]
  split <;> omega
theorem feSubG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) (h4' : ys.length = 4) :
    (feSubG xs ys n).2.length = 4 := by
  have hnl : xs.length = (ys.map notW).length := by simp [h4, h4']
  obtain ⟨-, hdl⟩ := feAdcG_length xs (ys.map notW) (.lit 1) n hnl
  rw [h4] at hdl
  have hd4 : (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast.length = 4 := by
    rw [List.length_dropLast, hdl]
  obtain ⟨-, hel⟩ := feAdcG_length (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast pWE (.lit 0)
    (n + (feAdcG xs (ys.map notW) (.lit 1) n).1.length) (by rw [hd4]; rfl)
  rw [hd4] at hel
  simp only [feSubG]
  rw [(feSelG_length _ _ _ _ (by rw [hd4, List.length_dropLast, hel])).2, hd4]

theorem feSubG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feSubG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feSubG xs ys n).2.map (WE.eval ρ))
      = (bignumVal (xs.map (WE.eval ρ)) + (2 ^ 255 - 19 - bignumVal (ys.map (WE.eval ρ))))
        % (2 ^ 255 - 19) := by
  simp only [feSubG] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨hd, he, hs⟩ := h
  have hnl : xs.length = (ys.map notW).length := by simp [h4, h4']
  have hdv := feAdcG_val ρ xs (ys.map notW) (.lit 1) n hd (lit1_le_one ρ)
  rw [notW_map] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs (ys.map notW) (.lit 1) n hnl
  rw [h4] at hdl
  set Dg := (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast with hDg
  have hd4 : Dg.length = 4 := by rw [hDg, List.length_dropLast, hdl]
  set m := n + (feAdcG xs (ys.map notW) (.lit 1) n).1.length with hmdef
  have hml : (xs.map (WE.eval ρ)).length = (notLimbs (ys.map (WE.eval ρ))).length := by
    simp [notLimbs, h4, h4']
  have hnv := notLimbs_val (ys.map (WE.eval ρ))
  simp only [List.length_map, h4'] at hnv
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hnv
  set D := addLimbs (xs.map (WE.eval ρ)) (notLimbs (ys.map (WE.eval ρ))) ((WE.lit 1).eval ρ)
    with hDdef
  have hDval : bignumVal D = bignumVal (xs.map (WE.eval ρ))
      + bignumVal (notLimbs (ys.map (WE.eval ρ))) + 1 := by
    rw [hDdef, addLimbs_val' _ _ _ (lit1_le_one ρ) hml]
    congr 1
  have hDlen : D.length = 5 := by
    rw [hDdef, addLimbs_length _ _ _ hml]
    simp [h4]
  have hsplit := split_top D 4 hDlen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hDval] at hsplit
  have hXlt := bnlt4 (xs.map (WE.eval ρ)) (by simp [h4])
  have hddl := bnlt4 D.dropLast (by rw [List.length_dropLast, hDlen])
  have htop := (D.getLastD 0).isLt
  have hdrop : Dg.map (WE.eval ρ) = D.dropLast := by
    rw [hDg, List.map_dropLast, hdv]
  have hev := feAdcG_val ρ Dg pWE (.lit 0) m he (lit0_le_one ρ)
  rw [pWE_eval, lit0_eval, hdrop] at hev
  obtain ⟨-, hel⟩ := feAdcG_length Dg pWE (.lit 0) m (by rw [hd4]; rfl)
  rw [hd4] at hel
  have hel2 : (D.dropLast).length = pV.length := by
    rw [List.length_dropLast, hDlen]; rfl
  have hEval : bignumVal (addLimbs D.dropLast pV 0)
      = bignumVal D.dropLast + (2 ^ 255 - 19) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hel2, bignumVal_pV]
    rfl
  have hElen : (addLimbs D.dropLast pV 0).length = 5 := by
    rw [addLimbs_length _ _ _ hel2, List.length_dropLast, hDlen]
  have hesplit := split_top (addLimbs D.dropLast pV 0) 4 hElen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hEval] at hesplit
  have hedl := bnlt4 (addLimbs D.dropLast pV 0).dropLast
    (by rw [List.length_dropLast, hElen])
  have hetop := ((addLimbs D.dropLast pV 0).getLastD 0).isLt
  have hsl := feSelG_val ρ ((feAdcG xs (ys.map notW) (.lit 1) n).2.getLastD (.lit 0))
    Dg (feAdcG Dg pWE (.lit 0) m).2.dropLast _ hs
    (by rw [hd4, List.length_dropLast, hel])
  rw [hsl]
  have hz : WE.eval ρ ((feAdcG xs (ys.map notW) (.lit 1) n).2.getLastD (.lit 0))
      = D.getLastD 0 := by
    rw [← hdv, ← lit0_eval ρ, List.getLastD_map]
  have hdrop2 : ((feAdcG Dg pWE (.lit 0) m).2.dropLast).map (WE.eval ρ)
      = (addLimbs D.dropLast pV 0).dropLast := by
    rw [List.map_dropLast, hev]
  rw [hz, hdrop, hdrop2]
  simp only [selL]
  split <;> omega


/-! ## 13. The product row and the schoolbook product -/

theorem bignumVal_append : ∀ (l1 l2 : List (BitVec 64)),
    bignumVal (l1 ++ l2) = bignumVal l1 + (2 ^ 64) ^ l1.length * bignumVal l2
  | [], l2 => by simp [bignumVal]
  | a :: l1, l2 => by
      have ih := bignumVal_append l1 l2
      simp only [List.cons_append, bignumVal, List.length_cons, ih, pow_succ]
      ring

theorem mulhi_le (a b : BitVec 64) : (mulhi a b).toNat ≤ 2 ^ 64 - 2 := by
  have h := mulWide_lo_hi a b
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  norm_num at hab ⊢
  omega

theorem rowW_val : ∀ (xs : List (BitVec 64)) (w h c : BitVec 64), c.toNat ≤ 1 →
    h.toNat + c.toNat < 2 ^ 64 →
    bignumVal (rowW xs w h c) = bignumVal xs * w.toNat + h.toNat + c.toNat
  | [], w, h, c, _, hb => by
      have hz : (h + BitVec.ofNat 64 0 + c).toNat = h.toNat + c.toNat := by
        have h0 : (BitVec.ofNat 64 0).toNat = 0 := by decide +kernel
        rw [BitVec.toNat_add, BitVec.toNat_add, h0, Nat.add_zero,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [rowW, bignumVal, hz]
      omega
  | x :: xs, w, h, c, hc, hb => by
      have hmx := mulWide_lo_hi x w
      have hhi := mulhi_le x w
      have hadc := adc_toNat' (x * w) h c
      have hc' := adc_carry_le' (x * w) h c hc
      have ih := rowW_val xs w (mulhi x w)
        (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)) hc' (by omega)
      simp only [rowW, bignumVal, ih]
      generalize hP : bignumVal xs * w.toNat = P
      have hx : x.toNat * w.toNat = (x * w).toNat + (mulhi x w).toNat * 2 ^ 64 := by omega
      calc (x * w + h + c).toNat
            + 2 ^ 64 * (P + (mulhi x w).toNat
              + (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)).toNat)
          = ((x * w + h + c).toNat
              + (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)).toNat * 2 ^ 64)
            + 2 ^ 64 * P + (mulhi x w).toNat * 2 ^ 64 := by ring
        _ = (x.toNat + 2 ^ 64 * bignumVal xs) * w.toNat + h.toNat + c.toNat := by
            rw [hadc]
            rw [Nat.add_mul, hx]
            rw [show 2 ^ 64 * bignumVal xs * w.toNat = 2 ^ 64 * (bignumVal xs * w.toNat) from by
              ring, hP]
            omega


theorem feAccG_length (i : Nat) (xs : List WE) (y : WE) (acc : List WE) (n : Nat)
    (h4 : xs.length = 4) (hacc : acc.length = i + 4) :
    (feAccG i xs y acc n).2.length = i + 5 := by
  have hdl : (acc.drop i ++ [WE.lit 0]).length = 5 := by
    simp [List.length_drop, hacc]
  have hrl := (feRowG_length xs y (.lit 0) (.lit 0) n).2
  rw [h4] at hrl
  obtain ⟨-, hsl⟩ := feAdcG_length (acc.drop i ++ [.lit 0]) (feRowG xs y (.lit 0) (.lit 0) n).2
    (.lit 0) (n + (feRowG xs y (.lit 0) (.lit 0) n).1.length) (by rw [hdl, hrl])
  rw [hdl] at hsl
  simp only [feAccG, List.length_append, List.length_take, List.length_dropLast, hsl, hacc]
  omega

theorem feAccG_val (ρ : Nat → BitVec 64) (i : Nat) (xs : List WE) (y : WE) (acc : List WE)
    (n : Nat) (h : Holds ρ n (feAccG i xs y acc n).1) (h4 : xs.length = 4)
    (hacc : acc.length = i + 4)
    (hb : bignumVal (acc.map (WE.eval ρ))
        + (2 ^ 64) ^ i * (bignumVal (xs.map (WE.eval ρ)) * (y.eval ρ).toNat)
      < (2 ^ 64) ^ i * 2 ^ 320) :
    bignumVal ((feAccG i xs y acc n).2.map (WE.eval ρ))
      = bignumVal (acc.map (WE.eval ρ))
        + (2 ^ 64) ^ i * (bignumVal (xs.map (WE.eval ρ)) * (y.eval ρ).toNat) := by
  simp only [feAccG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hr, hs⟩ := h
  have hrv := feRowG_val ρ xs y (.lit 0) (.lit 0) n hr (lit0_le_one ρ)
  rw [lit0_eval] at hrv
  have hrl := (feRowG_length xs y (.lit 0) (.lit 0) n).2
  rw [h4] at hrl
  have hdl : (acc.drop i ++ [WE.lit 0]).length = 5 := by simp [List.length_drop, hacc]
  set X := bignumVal (xs.map (WE.eval ρ)) with hX
  set Y := (y.eval ρ).toNat with hY
  set A := (acc.drop i ++ [WE.lit 0]).map (WE.eval ρ) with hA
  set R := rowW (xs.map (WE.eval ρ)) (y.eval ρ) 0 0 with hR
  have hrw : bignumVal R = X * Y := by
    rw [hR, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel)]
    simp [hX, hY]
  have hsv := feAdcG_val ρ (acc.drop i ++ [.lit 0]) (feRowG xs y (.lit 0) (.lit 0) n).2
    (.lit 0) _ hs (lit0_le_one ρ)
  rw [hrv, lit0_eval, ← hA] at hsv
  obtain ⟨-, hsl⟩ := feAdcG_length (acc.drop i ++ [.lit 0])
    (feRowG xs y (.lit 0) (.lit 0) n).2 (.lit 0)
    (n + (feRowG xs y (.lit 0) (.lit 0) n).1.length) (by rw [hdl, hrl])
  rw [hdl] at hsl
  have hAv : bignumVal A = bignumVal ((acc.map (WE.eval ρ)).drop i) := by
    rw [hA, List.map_append, bignumVal_append]
    simp only [List.map_drop, List.map_cons, List.map_nil, bignumVal]
    rw [lit0_eval]
    show bignumVal ((acc.map (WE.eval ρ)).drop i)
      + (2 ^ 64) ^ ((acc.map (WE.eval ρ)).drop i).length * ((0 : BitVec 64).toNat + 2 ^ 64 * 0)
      = bignumVal ((acc.map (WE.eval ρ)).drop i)
    simp
  have hAl : A.length = 5 := by rw [hA, List.length_map, hdl]
  have hRl : R.length = 5 := by rw [hR, rowW_length, List.length_map, h4]
  have hSv : bignumVal (addLimbs A R 0) = bignumVal A + bignumVal R := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) (by rw [hAl, hRl])]
    rfl
  have hSl : (addLimbs A R 0).length = 6 := by
    rw [addLimbs_length _ _ _ (by rw [hAl, hRl]), hAl]
  have hsplit := split_top (addLimbs A R 0) 5 hSl
  have hsplitacc := bignumVal_take_drop i (acc.map (WE.eval ρ))
  rw [show ((2 : Nat) ^ 64) ^ 5 = 2 ^ 320 from by norm_num, hSv, hAv, hrw] at hsplit
  have hcarry : ((addLimbs A R 0).getLastD 0).toNat = 0 := by
    have hmul : (2 ^ 64) ^ i * (bignumVal ((acc.map (WE.eval ρ)).drop i) + X * Y)
        < (2 ^ 64) ^ i * 2 ^ 320 := by
      rw [Nat.mul_add]
      omega
    have hlt := Nat.lt_of_mul_lt_mul_left hmul
    have hb2 := ((addLimbs A R 0).getLastD 0).isLt
    rcases Nat.eq_zero_or_pos ((addLimbs A R 0).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have : 2 ^ 320 * 1 ≤ 2 ^ 320 * ((addLimbs A R 0).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      omega
  rw [List.map_append, bignumVal_append, List.map_take, List.map_dropLast, hsv]
  rw [List.length_take, List.length_map, hacc, show min i (i + 4) = i from by omega]
  have hdl2 : bignumVal (addLimbs A R 0).dropLast
      = bignumVal ((acc.map (WE.eval ρ)).drop i) + X * Y := by
    rw [hcarry] at hsplit
    omega
  rw [hdl2, Nat.mul_add]
  omega


theorem feRowG_out_length (xs : List WE) (w h c : WE) (n : Nat) (h4 : xs.length = 4) :
    (feRowG xs w h c n).2.length = 5 := by
  have := (feRowG_length xs w h c n).2
  rw [h4] at this
  exact this

theorem feProdG_length (xs : List WE) (y0 y1 y2 y3 : WE) (n : Nat) (h4 : xs.length = 4) :
    (feProdG xs y0 y1 y2 y3 n).2.length = 8 := by
  simp only [feProdG]
  rw [feAccG_length 3 xs y3 _ _ h4 (by
    rw [feAccG_length 2 xs y2 _ _ h4 (by
      rw [feAccG_length 1 xs y1 _ _ h4 (by rw [feRowG_out_length _ _ _ _ _ h4])])])]

theorem feProdG_val (ρ : Nat → BitVec 64) (xs : List WE) (y0 y1 y2 y3 : WE) (n : Nat)
    (h : Holds ρ n (feProdG xs y0 y1 y2 y3 n).1) (h4 : xs.length = 4) :
    bignumVal ((feProdG xs y0 y1 y2 y3 n).2.map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ))
        * bignumVal [y0.eval ρ, y1.eval ρ, y2.eval ρ, y3.eval ρ] := by
  simp only [feProdG] at h ⊢
  rw [holds_append, holds_append, holds_append] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  set A0 := (feRowG xs y0 (.lit 0) (.lit 0) n).2 with hA0
  set m0 := n + (feRowG xs y0 (.lit 0) (.lit 0) n).1.length with hm0
  set A1 := (feAccG 1 xs y1 A0 m0).2 with hA1
  set m1 := m0 + (feAccG 1 xs y1 A0 m0).1.length with hm1
  set A2 := (feAccG 2 xs y2 A1 m1).2 with hA2
  set m2 := m1 + (feAccG 2 xs y2 A1 m1).1.length with hm2
  set X := bignumVal (xs.map (WE.eval ρ)) with hX
  have hXlt : X < 2 ^ 256 := bnlt4 _ (by simp [h4])
  have hy0 := (y0.eval ρ).isLt
  have hy1 := (y1.eval ρ).isLt
  have hy2 := (y2.eval ρ).isLt
  have hy3 := (y3.eval ρ).isLt
  have hr0 := feRowG_val ρ xs y0 (.lit 0) (.lit 0) n h0 (lit0_le_one ρ)
  rw [lit0_eval, ← hA0] at hr0
  have hv0 : bignumVal (A0.map (WE.eval ρ)) = X * (y0.eval ρ).toNat := by
    rw [hr0, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel)]
    simp [hX]
  have hl0 : A0.length = 1 + 4 := by rw [hA0, feRowG_out_length _ _ _ _ _ h4]
  have hb1 : bignumVal (A0.map (WE.eval ρ))
      + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat) < (2 ^ 64) ^ 1 * 2 ^ 320 := by
    rw [hv0]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 128 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 1 * 2 ^ 320 := by norm_num
  have hv1 := feAccG_val ρ 1 xs y1 A0 m0 h1 h4 hl0 hb1
  rw [hv0, ← hA1] at hv1
  have hl1 : A1.length = 2 + 4 := by rw [hA1, feAccG_length 1 xs y1 A0 m0 h4 hl0]
  have hb2 : bignumVal (A1.map (WE.eval ρ))
      + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat) < (2 ^ 64) ^ 2 * 2 ^ 320 := by
    rw [hv1]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
          + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat
            + 2 ^ 128 * (y2.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 192 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 2 * 2 ^ 320 := by norm_num
  have hv2 := feAccG_val ρ 2 xs y2 A1 m1 h2 h4 hl1 hb2
  rw [hv1, ← hA2] at hv2
  have hl2 : A2.length = 3 + 4 := by rw [hA2, feAccG_length 2 xs y2 A1 m1 h4 hl1]
  have hb3 : bignumVal (A2.map (WE.eval ρ))
      + (2 ^ 64) ^ 3 * (X * (y3.eval ρ).toNat) < (2 ^ 64) ^ 3 * 2 ^ 320 := by
    rw [hv2]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
          + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat) + (2 ^ 64) ^ 3 * (X * (y3.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat
            + 2 ^ 128 * (y2.eval ρ).toNat + 2 ^ 192 * (y3.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 3 * 2 ^ 320 := by norm_num
  have hv3 := feAccG_val ρ 3 xs y3 A2 m2 h3 h4 hl2 hb3
  rw [hv2] at hv3
  rw [hv3]
  simp only [bignumVal]
  ring


theorem lit38_toNat (ρ : Nat → BitVec 64) : ((WE.lit 38).eval ρ).toNat = 38 := by
  show (BitVec.ofNat 64 38).toNat = 38
  decide +kernel

theorem feFoldG_length (S : List WE) (n : Nat) (h5 : S.length = 5) :
    (feFoldG S n).2.length = 4 := by
  simp only [feFoldG]
  set M := (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hM
  have hMl : M.length = 2 := by
    rw [hM, (feRowG_length _ _ _ _ _).2, List.length_drop, h5]
  set n3 := n + (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn3
  set U := (feAdcG (S.take 4) (M ++ [.lit 0, .lit 0]) (.lit 0) n3).2 with hU
  have hUl : U.length = 5 := by
    rw [hU, (feAdcG_length _ _ _ _ (by
      rw [List.length_take, h5, List.length_append, hMl]; rfl)).2, List.length_take, h5]
    omega
  set n4 := n3 + (feAdcG (S.take 4) (M ++ [.lit 0, .lit 0]) (.lit 0) n3).1.length with hn4
  set mm := selWE (U.getLastD (.lit 0)) (.lit 38) (.lit 0) with hmm
  set V := (feAdcG U.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).2 with hV
  have hVl : V.length = 5 := by
    rw [hV, (feAdcG_length _ _ _ _ (by
      rw [List.length_dropLast, hUl]; rfl)).2, List.length_dropLast, hUl]
  refine feCsubG_length _ _ (feCsubG_length _ _ ?_)
  rw [List.length_dropLast, hVl]

theorem feRedG_length (ps : List WE) (n : Nat) (h8 : ps.length = 8) :
    (feRedG ps n).2.length = 4 := by
  simp only [feRedG]
  have hRl : (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2.length = 5 := by
    rw [(feRowG_length _ _ _ _ _).2, List.length_drop, h8]
  refine feFoldG_length _ _ ?_
  rw [List.length_dropLast, (feAdcG_length _ _ _ _ (by
    rw [List.length_append, List.length_take, h8, hRl]; rfl)).2,
    List.length_append, List.length_take, h8]
  simp


theorem selW_toNat (c : BitVec 64) :
    (selW c (BitVec.ofNat 64 38) (BitVec.ofNat 64 0)).toNat = if c.toNat = 0 then 0 else 38 := by
  simp only [selW]
  split
  · decide +kernel
  · decide +kernel

theorem feFoldG_val (ρ : Nat → BitVec 64) (S : List WE) (n : Nat)
    (h : Holds ρ n (feFoldG S n).1) (h5 : S.length = 5)
    (hs4 : bignumVal ((S.map (WE.eval ρ)).drop 4) < 64) :
    bignumVal ((feFoldG S n).2.map (WE.eval ρ))
      = bignumVal (S.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feFoldG] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨hm, hu, hv, hc1, hc2⟩ := h
  set Slo := bignumVal ((S.map (WE.eval ρ)).take 4) with hSlo
  set S4 := bignumVal ((S.map (WE.eval ρ)).drop 4) with hS4
  have hSsplit : bignumVal (S.map (WE.eval ρ)) = Slo + 2 ^ 256 * S4 := by
    have hts := bignumVal_take_drop 4 (S.map (WE.eval ρ))
    rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hts
    exact hts
  have hSlolt : Slo < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_take, List.length_map, h5])
  set Mg := (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hMg
  set n3 := n + (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn3
  have hMl : Mg.length = 2 := by
    rw [hMg, (feRowG_length _ _ _ _ _).2, List.length_drop, h5]
  have hMv := feRowG_val ρ (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n hm (lit0_le_one ρ)
  rw [lit0_eval, ← hMg, List.map_drop] at hMv
  have hMval : bignumVal (Mg.map (WE.eval ρ)) = S4 * 38 := by
    rw [hMv, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel), lit38_toNat]
    simp [hS4]
  set Ug := (feAdcG (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3).2 with hUg
  set n4 := n3 + (feAdcG (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3).1.length with hn4
  have hUlenIn : (S.take 4).length = (Mg ++ [WE.lit 0, WE.lit 0]).length := by
    rw [List.length_take, h5, List.length_append, hMl]
    rfl
  have hUv := feAdcG_val ρ (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3 hu (lit0_le_one ρ)
  rw [lit0_eval, ← hUg, List.map_take, List.map_append] at hUv
  have hUl : Ug.length = 5 := by
    rw [hUg, (feAdcG_length _ _ _ _ hUlenIn).2, List.length_take, h5]
    omega
  have hMzeros : bignumVal (Mg.map (WE.eval ρ) ++ [WE.lit 0, WE.lit 0].map (WE.eval ρ))
      = S4 * 38 := by
    rw [bignumVal_append, hMval]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp
  have hUval : bignumVal (Ug.map (WE.eval ρ)) = Slo + S4 * 38 := by
    rw [hUv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_take, List.length_map, h5, List.length_append, List.length_map,
        List.length_map, hMl]
      rfl), hMzeros, hSlo]
    simp
  have hUsplit := split_top (Ug.map (WE.eval ρ)) 4 (by rw [List.length_map, hUl])
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hUval] at hUsplit
  set U := bignumVal (Ug.map (WE.eval ρ)).dropLast with hU
  set cu := ((Ug.map (WE.eval ρ)).getLastD 0).toNat with hcu
  have hUlt : U < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_dropLast, List.length_map, hUl])
  have hcu1 : cu ≤ 1 := by
    rcases Nat.lt_or_ge cu 2 with hc | hc
    · omega
    · exfalso
      have : 2 ^ 256 * 2 ≤ 2 ^ 256 * cu := Nat.mul_le_mul_left _ hc
      omega
  set mm := selWE (Ug.getLastD (.lit 0)) (.lit 38) (.lit 0) with hmm
  have hmmv : (mm.eval ρ).toNat = if cu = 0 then 0 else 38 := by
    rw [hmm, selWE_eval]
    show (selW (WE.eval ρ (Ug.getLastD (WE.lit 0))) (BitVec.ofNat 64 38)
      (BitVec.ofNat 64 0)).toNat = _
    rw [selW_toNat, hcu, ← lit0_eval ρ, List.getLastD_map]
  set Vg := (feAdcG Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).2 with hVg
  set n5 := n4 + (feAdcG Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).1.length with hn5
  have hVlenIn : Ug.dropLast.length = [mm, WE.lit 0, WE.lit 0, WE.lit 0].length := by
    rw [List.length_dropLast, hUl]
    rfl
  have hVv := feAdcG_val ρ Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4 hv
    (lit0_le_one ρ)
  rw [lit0_eval, ← hVg, List.map_dropLast] at hVv
  have hVl : Vg.length = 5 := by
    rw [hVg, (feAdcG_length _ _ _ _ hVlenIn).2, List.length_dropLast, hUl]
  have hVval : bignumVal (Vg.map (WE.eval ρ)) = U + (if cu = 0 then 0 else 38) := by
    rw [hVv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_dropLast, List.length_map, hUl]
      rfl), ← hU, ← hmmv]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp
  have hVsplit := split_top (Vg.map (WE.eval ρ)) 4 (by rw [List.length_map, hVl])
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hVval] at hVsplit
  set V := bignumVal (Vg.map (WE.eval ρ)).dropLast with hV
  have hVlt : V < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_dropLast, List.length_map, hVl])
  have hcv : ((Vg.map (WE.eval ρ)).getLastD 0).toNat = 0 := by
    rcases Nat.eq_zero_or_pos ((Vg.map (WE.eval ρ)).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have hge : 2 ^ 256 * 1 ≤ 2 ^ 256 * ((Vg.map (WE.eval ρ)).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      by_cases hcu0 : cu = 0
      · rw [if_pos hcu0] at hVsplit
        rw [hcu0] at hUsplit
        omega
      · rw [if_neg hcu0] at hVsplit
        have hcu1' : cu = 1 := by omega
        rw [hcu1'] at hUsplit
        omega
  have hVfin : V = U + (if cu = 0 then 0 else 38) := by
    rw [hcv] at hVsplit
    omega
  have hVd4 : Vg.dropLast.length = 4 := by rw [List.length_dropLast, hVl]
  have hd1 := feCsubG_val ρ Vg.dropLast n5 hc1 hVd4
  rw [List.map_dropLast, ← hV] at hd1
  set C1 := (feCsubG Vg.dropLast n5).2 with hC1
  have hC1l : C1.length = 4 := by rw [hC1]; exact feCsubG_length _ _ hVd4
  have hd2 := feCsubG_val ρ C1 (n5 + (feCsubG Vg.dropLast n5).1.length) hc2 hC1l
  rw [hd1] at hd2
  rw [hd2]
  have hkey : bignumVal (S.map (WE.eval ρ)) = V + (2 ^ 255 - 19) * (2 * (S4 + cu)) := by
    by_cases hcu0 : cu = 0
    · rw [if_pos hcu0] at hVfin
      rw [hcu0] at hUsplit
      rw [hcu0]
      omega
    · have hcu1' : cu = 1 := by omega
      rw [if_neg hcu0] at hVfin
      rw [hcu1'] at hUsplit
      rw [hcu1']
      omega
  rw [hkey, Nat.add_mul_mod_self_left]
  exact CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519.csub_twice_eq_mod V
    hVlt


theorem feRedG_val (ρ : Nat → BitVec 64) (ps : List WE) (n : Nat)
    (h : Holds ρ n (feRedG ps n).1) (h8 : ps.length = 8)
    (hlt : bignumVal (ps.map (WE.eval ρ)) < 2 ^ 510) :
    bignumVal ((feRedG ps n).2.map (WE.eval ρ))
      = bignumVal (ps.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feRedG] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨hr, hs, hf⟩ := h
  set L := bignumVal ((ps.map (WE.eval ρ)).take 4) with hL
  set H := bignumVal ((ps.map (WE.eval ρ)).drop 4) with hH
  have hPsplit : bignumVal (ps.map (WE.eval ρ)) = L + 2 ^ 256 * H := by
    have hts := bignumVal_take_drop 4 (ps.map (WE.eval ρ))
    rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hts
    exact hts
  have hLlt : L < 2 ^ 256 := bnlt4 _ (by simp [List.length_take, List.length_map, h8])
  have hHlt : H < 2 ^ 254 := by
    rcases Nat.lt_or_ge H (2 ^ 254) with hc | hc
    · exact hc
    · exfalso
      have : 2 ^ 256 * 2 ^ 254 ≤ 2 ^ 256 * H := Nat.mul_le_mul_left _ hc
      norm_num at this
      omega
  set Rg := (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hRg
  set n1 := n + (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn1
  have hRl : Rg.length = 5 := by
    rw [hRg, (feRowG_length _ _ _ _ _).2, List.length_drop, h8]
  have hRv := feRowG_val ρ (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n hr (lit0_le_one ρ)
  rw [lit0_eval, ← hRg, List.map_drop] at hRv
  have hRval : bignumVal (Rg.map (WE.eval ρ)) = H * 38 := by
    rw [hRv, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel), lit38_toNat]
    simp [hH]
  set Sg := (feAdcG (ps.take 4 ++ [.lit 0]) Rg (.lit 0) n1).2 with hSg
  have hSlenIn : (ps.take 4 ++ [WE.lit 0]).length = Rg.length := by
    rw [List.length_append, List.length_take, h8, hRl]
    rfl
  have hSv := feAdcG_val ρ (ps.take 4 ++ [.lit 0]) Rg (.lit 0) n1 hs (lit0_le_one ρ)
  rw [lit0_eval, ← hSg, List.map_append, List.map_take] at hSv
  have hSl : Sg.length = 6 := by
    rw [hSg, (feAdcG_length _ _ _ _ hSlenIn).2, List.length_append, List.length_take, h8]
    simp
  have hAzeros : bignumVal ((ps.map (WE.eval ρ)).take 4 ++ [WE.lit 0].map (WE.eval ρ)) = L := by
    rw [bignumVal_append]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp [hL]
  have hSval : bignumVal (Sg.map (WE.eval ρ)) = L + H * 38 := by
    rw [hSv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_append, List.length_take, List.length_map, h8, List.length_map,
        List.length_map, hRl]
      rfl), hAzeros, hRval]
    simp
  have hSsplit := split_top (Sg.map (WE.eval ρ)) 5 (by rw [List.length_map, hSl])
  rw [show ((2 : Nat) ^ 64) ^ 5 = 2 ^ 320 from by norm_num, hSval] at hSsplit
  have hSdl : bignumVal (Sg.map (WE.eval ρ)).dropLast < 2 ^ 320 := by
    have h2 := bignumVal_lt (Sg.map (WE.eval ρ)).dropLast
    rw [List.length_dropLast, List.length_map, hSl,
      show ((2 : Nat) ^ 64) ^ (6 - 1) = 2 ^ 320 from by norm_num] at h2
    exact h2
  have hcs : ((Sg.map (WE.eval ρ)).getLastD 0).toNat = 0 := by
    rcases Nat.eq_zero_or_pos ((Sg.map (WE.eval ρ)).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have hge : 2 ^ 320 * 1 ≤ 2 ^ 320 * ((Sg.map (WE.eval ρ)).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      omega
  have hSdlval : bignumVal (Sg.dropLast.map (WE.eval ρ)) = L + H * 38 := by
    rw [List.map_dropLast, hcs] at *
    omega
  have hSd5 : Sg.dropLast.length = 5 := by rw [List.length_dropLast, hSl]
  -- the fifth limb of the folded value is small
  have hfsplit := bignumVal_take_drop 4 (Sg.dropLast.map (WE.eval ρ))
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hSdlval] at hfsplit
  have hs4 : bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4) < 64 := by
    rcases Nat.lt_or_ge (bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4)) 64 with hc | hc
    · exact hc
    · exfalso
      have : 2 ^ 256 * 64 ≤ 2 ^ 256 * bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4) :=
        Nat.mul_le_mul_left _ hc
      omega
  have hfold := feFoldG_val ρ Sg.dropLast _ hf hSd5 hs4
  rw [hfold, hSdlval, hPsplit]
  have hmod : L + 2 ^ 256 * H = (L + H * 38) + (2 ^ 255 - 19) * (2 * H) := by ring_nf
  rw [hmod, Nat.add_mul_mod_self_left]


theorem map4 (ρ : Nat → BitVec 64) : ∀ (ys : List WE), ys.length = 4 →
    ys.map (WE.eval ρ) = [(ys.getD 0 (.lit 0)).eval ρ, (ys.getD 1 (.lit 0)).eval ρ,
      (ys.getD 2 (.lit 0)).eval ρ, (ys.getD 3 (.lit 0)).eval ρ]
  | [_, _, _, _], _ => rfl
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem feMulG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feMulG xs ys n).2.length = 4 := by
  simp only [feMulG]
  exact feRedG_length _ _ (feProdG_length xs _ _ _ _ n h4)

theorem feMulG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feMulG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feMulG xs ys n).2.map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ)) * bignumVal (ys.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feMulG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hp, hr⟩ := h
  set Pg := (feProdG xs (ys.getD 0 (.lit 0)) (ys.getD 1 (.lit 0)) (ys.getD 2 (.lit 0))
    (ys.getD 3 (.lit 0)) n).2 with hPg
  have hpv := feProdG_val ρ xs (ys.getD 0 (.lit 0)) (ys.getD 1 (.lit 0)) (ys.getD 2 (.lit 0))
    (ys.getD 3 (.lit 0)) n hp h4
  rw [← hPg, ← map4 ρ ys h4'] at hpv
  have hpl : Pg.length = 8 := by
    rw [hPg]
    exact feProdG_length xs _ _ _ _ n h4
  have hplt : bignumVal (Pg.map (WE.eval ρ)) < 2 ^ 510 := by
    rw [hpv]
    calc bignumVal (xs.map (WE.eval ρ)) * bignumVal (ys.map (WE.eval ρ))
        < 2 ^ 255 * 2 ^ 255 := Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 510 := by norm_num
  rw [feRedG_val ρ Pg _ hr hpl hplt, hpv]

theorem slots_eval (ρ : Nat → BitVec 64) : ∀ (es : List WE) (n : Nat), Holds ρ n es →
    ((List.range es.length).map (fun i => (WE.v (n + i) : WE))).map (WE.eval ρ)
      = es.map (WE.eval ρ)
  | [], _, _ => rfl
  | e :: es, n, h => by
      obtain ⟨h0, hr⟩ := h
      have ih := slots_eval ρ es (n + 1) hr
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons (by simpa only [WE.eval, Nat.add_zero] using h0) ?_
      rw [← ih, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_def, WE.eval]
      congr 1
      omega

theorem feCopyG_val (ρ : Nat → BitVec 64) (xs : List WE) (n : Nat)
    (h : Holds ρ n (feCopyG xs n).1) :
    (feCopyG xs n).2.map (WE.eval ρ) = xs.map (WE.eval ρ) := by
  simp only [feCopyG] at h ⊢
  have hl : (xs.map (fun x => orWE x x)).length = xs.length := by simp
  have := slots_eval ρ (xs.map (fun x => orWE x x)) n h
  rw [hl] at this
  rw [this, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_def, orWE, WE.eval]
  rw [or_xor_and]
  simp

theorem feCopyG_length (xs : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feCopyG xs n).2.length = 4 := by
  simp only [feCopyG, List.length_map, List.length_range, h4]


/-! ## 14. The value of the program -/

/-- The four output coordinates on the natural values of the eight input coordinates,
    each reduced modulo `p25519`. -/
def paSpec (x1 y1 z1 t1 x2 y2 z2 t2 : Nat) : Nat × Nat × Nat × Nat :=
  let p := 2 ^ 255 - 19
  let a := ((y1 + (p - x1)) % p * ((y2 + (p - x2)) % p)) % p
  let b := ((y1 + x1) % p * ((y2 + x2) % p)) % p
  let c := ((t1 * twoDNat) % p * t2) % p
  let dv := ((z1 + z1) % p * z2) % p
  let e := (b + (p - a)) % p
  let f := (dv + (p - c)) % p
  let g := (dv + c) % p
  let hh := (b + a) % p
  ((e * f) % p, (g * hh) % p, (f * g) % p, (e * hh) % p)

theorem twoDLimbs_val (ρ : Nat → BitVec 64) :
    bignumVal (twoDLimbs.map (WE.eval ρ)) = twoDNat := by
  show bignumVal [BitVec.ofNat 64 (twoDNat % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 64 % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 128 % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 192 % 2 ^ 64)] = twoDNat
  simp only [bignumVal, BitVec.toNat_ofNat, twoDNat]
  norm_num

theorem twoDLimbs_length : twoDLimbs.length = 4 := rfl

theorem twoDNat_lt : twoDNat < 2 ^ 255 - 19 := by
  rw [twoDNat]
  norm_num

theorem mod_lt_p (a : Nat) : a % (2 ^ 255 - 19) < 2 ^ 255 - 19 :=
  Nat.mod_lt _ (by norm_num)



theorem slotsFrom_length (b : Nat) : (slotsFrom b 4).length = 4 := by simp [slotsFrom]

theorem paB1_len : paB1.2.length = 4 :=
  feSubG_length _ _ _ (slotsFrom_length 29) (slotsFrom_length 25)
theorem paB2_len : paB2.2.length = 4 :=
  feSubG_length _ _ _ (slotsFrom_length 45) (slotsFrom_length 41)
theorem paB3_len : paB3.2.length = 4 := feMulG_length _ _ _ paB1_len
theorem paB4_len : paB4.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 29) (slotsFrom_length 25)
theorem paB5_len : paB5.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 45) (slotsFrom_length 41)
theorem paB6_len : paB6.2.length = 4 := feMulG_length _ _ _ paB4_len
theorem paB8_len : paB8.2.length = 4 := feMulG_length _ _ _ (slotsFrom_length 37)
theorem paB9_len : paB9.2.length = 4 := feMulG_length _ _ _ paB8_len
theorem paB10_len : paB10.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 33) (slotsFrom_length 33)
theorem paB11_len : paB11.2.length = 4 := feMulG_length _ _ _ paB10_len
theorem paB12_len : paB12.2.length = 4 := feSubG_length _ _ _ paB6_len paB3_len
theorem paB13_len : paB13.2.length = 4 := feSubG_length _ _ _ paB11_len paB9_len
theorem paB14_len : paB14.2.length = 4 := feAddG_length _ _ _ paB11_len paB9_len
theorem paB15_len : paB15.2.length = 4 := feAddG_length _ _ _ paB6_len paB3_len
theorem paB16_len : paB16.2.length = 4 := feMulG_length _ _ _ paB12_len
theorem paB17_len : paB17.2.length = 4 := feMulG_length _ _ _ paB14_len
theorem paB18_len : paB18.2.length = 4 := feMulG_length _ _ _ paB12_len
theorem paB19_len : paB19.2.length = 4 := feMulG_length _ _ _ paB13_len
theorem paC1_len : paC1.2.length = 4 := feCopyG_length _ _ paB16_len
theorem paC2_len : paC2.2.length = 4 := feCopyG_length _ _ paB17_len
theorem paC3_len : paC3.2.length = 4 := feCopyG_length _ _ paB19_len
theorem paC4_len : paC4.2.length = 4 := feCopyG_length _ _ paB18_len

/-- The value of a limb list of the program, as a natural. -/
def bv (ρ : Nat → BitVec 64) (l : List WE) : Nat := bignumVal (l.map (WE.eval ρ))

theorem paG_val (ρ : Nat → BitVec 64) (h : Holds ρ 57 paG.1)
    (hx1 : bv ρ (slotsFrom 25 4) < 2 ^ 255 - 19)
    (hy1 : bv ρ (slotsFrom 29 4) < 2 ^ 255 - 19)
    (hz1 : bv ρ (slotsFrom 33 4) < 2 ^ 255 - 19)
    (ht1 : bv ρ (slotsFrom 37 4) < 2 ^ 255 - 19)
    (hx2 : bv ρ (slotsFrom 41 4) < 2 ^ 255 - 19)
    (hy2 : bv ρ (slotsFrom 45 4) < 2 ^ 255 - 19)
    (hz2 : bv ρ (slotsFrom 49 4) < 2 ^ 255 - 19)
    (ht2 : bv ρ (slotsFrom 53 4) < 2 ^ 255 - 19) :
    bv ρ paC1.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).1
      ∧ bv ρ paC2.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.1
      ∧ bv ρ paC3.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.2.1
      ∧ bv ρ paC4.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.2.2 := by
  simp only [paG] at h
  rw [holds_append] at h
  obtain ⟨g1, h⟩ := h
  rw [show 57 + paB1.1.length = paN1 from rfl, holds_append] at h
  obtain ⟨g2, h⟩ := h
  rw [show paN1 + paB2.1.length = paN2 from rfl, holds_append] at h
  obtain ⟨g3, h⟩ := h
  rw [show paN2 + paB3.1.length = paN3 from rfl, holds_append] at h
  obtain ⟨g4, h⟩ := h
  rw [show paN3 + paB4.1.length = paN4 from rfl, holds_append] at h
  obtain ⟨g5, h⟩ := h
  rw [show paN4 + paB5.1.length = paN5 from rfl, holds_append] at h
  obtain ⟨g6, h⟩ := h
  rw [show paN5 + paB6.1.length = paN6 from rfl, holds_append] at h
  obtain ⟨g8, h⟩ := h
  rw [show paN6 + paB8.1.length = paN8 from rfl, holds_append] at h
  obtain ⟨g9, h⟩ := h
  rw [show paN8 + paB9.1.length = paN9 from rfl, holds_append] at h
  obtain ⟨g10, h⟩ := h
  rw [show paN9 + paB10.1.length = paN10 from rfl, holds_append] at h
  obtain ⟨g11, h⟩ := h
  rw [show paN10 + paB11.1.length = paN11 from rfl, holds_append] at h
  obtain ⟨g12, h⟩ := h
  rw [show paN11 + paB12.1.length = paN12 from rfl, holds_append] at h
  obtain ⟨g13, h⟩ := h
  rw [show paN12 + paB13.1.length = paN13 from rfl, holds_append] at h
  obtain ⟨g14, h⟩ := h
  rw [show paN13 + paB14.1.length = paN14 from rfl, holds_append] at h
  obtain ⟨g15, h⟩ := h
  rw [show paN14 + paB15.1.length = paN15 from rfl, holds_append] at h
  obtain ⟨g16, h⟩ := h
  rw [show paN15 + paB16.1.length = paN16 from rfl, holds_append] at h
  obtain ⟨g17, h⟩ := h
  rw [show paN16 + paB17.1.length = paN17 from rfl, holds_append] at h
  obtain ⟨g18, h⟩ := h
  rw [show paN17 + paB18.1.length = paN18 from rfl, holds_append] at h
  obtain ⟨g19, h⟩ := h
  rw [show paN18 + paB19.1.length = paN19 from rfl, holds_append] at h
  obtain ⟨gc1, h⟩ := h
  rw [holds_append] at h
  obtain ⟨gc2, h⟩ := h
  rw [holds_append] at h
  obtain ⟨gc3, gc4⟩ := h
  simp only [bv] at hx1 hy1 hz1 ht1 hx2 hy2 hz2 ht2 ⊢
  have v1 : bignumVal (paB1.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 29 4).map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal ((slotsFrom 25 4).map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ 57 g1 (slotsFrom_length 29) (slotsFrom_length 25) hy1 hx1
  have v2 : bignumVal (paB2.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 45 4).map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal ((slotsFrom 41 4).map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN1 g2 (slotsFrom_length 45) (slotsFrom_length 41) hy2 hx2
  have v3 : bignumVal (paB3.2.map (WE.eval ρ))
      = bignumVal (paB1.2.map (WE.eval ρ)) * bignumVal (paB2.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN2 g3 paB1_len paB2_len (by rw [v1]; exact mod_lt_p _)
      (by rw [v2]; exact mod_lt_p _)
  have v4 : bignumVal (paB4.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 29 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 25 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN3 g4 (slotsFrom_length 29) (slotsFrom_length 25) hy1 hx1
  have v5 : bignumVal (paB5.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 45 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 41 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN4 g5 (slotsFrom_length 45) (slotsFrom_length 41) hy2 hx2
  have v6 : bignumVal (paB6.2.map (WE.eval ρ))
      = bignumVal (paB4.2.map (WE.eval ρ)) * bignumVal (paB5.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN5 g6 paB4_len paB5_len (by rw [v4]; exact mod_lt_p _)
      (by rw [v5]; exact mod_lt_p _)
  have v8' := feMulG_val ρ (slotsFrom 37 4) twoDLimbs paN6 g8 (slotsFrom_length 37)
    twoDLimbs_length ht1 (by rw [twoDLimbs_val]; exact twoDNat_lt)
  rw [twoDLimbs_val] at v8'
  have v8 : bignumVal (paB8.2.map (WE.eval ρ))
      = bignumVal ((slotsFrom 37 4).map (WE.eval ρ)) * twoDNat % (2 ^ 255 - 19) := v8'
  have v9 : bignumVal (paB9.2.map (WE.eval ρ))
      = bignumVal (paB8.2.map (WE.eval ρ)) * bignumVal ((slotsFrom 53 4).map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN8 g9 paB8_len (slotsFrom_length 53) (by rw [v8]; exact mod_lt_p _) ht2
  have v10 : bignumVal (paB10.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 33 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 33 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN9 g10 (slotsFrom_length 33) (slotsFrom_length 33) hz1 hz1
  have v11 : bignumVal (paB11.2.map (WE.eval ρ))
      = bignumVal (paB10.2.map (WE.eval ρ)) * bignumVal ((slotsFrom 49 4).map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN10 g11 paB10_len (slotsFrom_length 49)
      (by rw [v10]; exact mod_lt_p _) hz2
  have v12 : bignumVal (paB12.2.map (WE.eval ρ))
      = (bignumVal (paB6.2.map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal (paB3.2.map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN11 g12 paB6_len paB3_len (by rw [v6]; exact mod_lt_p _)
      (by rw [v3]; exact mod_lt_p _)
  have v13 : bignumVal (paB13.2.map (WE.eval ρ))
      = (bignumVal (paB11.2.map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal (paB9.2.map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN12 g13 paB11_len paB9_len (by rw [v11]; exact mod_lt_p _)
      (by rw [v9]; exact mod_lt_p _)
  have v14 : bignumVal (paB14.2.map (WE.eval ρ))
      = (bignumVal (paB11.2.map (WE.eval ρ)) + bignumVal (paB9.2.map (WE.eval ρ)))
        % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN13 g14 paB11_len paB9_len (by rw [v11]; exact mod_lt_p _)
      (by rw [v9]; exact mod_lt_p _)
  have v15 : bignumVal (paB15.2.map (WE.eval ρ))
      = (bignumVal (paB6.2.map (WE.eval ρ)) + bignumVal (paB3.2.map (WE.eval ρ)))
        % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN14 g15 paB6_len paB3_len (by rw [v6]; exact mod_lt_p _)
      (by rw [v3]; exact mod_lt_p _)
  have v16 : bignumVal (paB16.2.map (WE.eval ρ))
      = bignumVal (paB12.2.map (WE.eval ρ)) * bignumVal (paB13.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN15 g16 paB12_len paB13_len (by rw [v12]; exact mod_lt_p _)
      (by rw [v13]; exact mod_lt_p _)
  have v17 : bignumVal (paB17.2.map (WE.eval ρ))
      = bignumVal (paB14.2.map (WE.eval ρ)) * bignumVal (paB15.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN16 g17 paB14_len paB15_len (by rw [v14]; exact mod_lt_p _)
      (by rw [v15]; exact mod_lt_p _)
  have v18 : bignumVal (paB18.2.map (WE.eval ρ))
      = bignumVal (paB12.2.map (WE.eval ρ)) * bignumVal (paB15.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN17 g18 paB12_len paB15_len (by rw [v12]; exact mod_lt_p _)
      (by rw [v15]; exact mod_lt_p _)
  have v19 : bignumVal (paB19.2.map (WE.eval ρ))
      = bignumVal (paB13.2.map (WE.eval ρ)) * bignumVal (paB14.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN18 g19 paB13_len paB14_len (by rw [v13]; exact mod_lt_p _)
      (by rw [v14]; exact mod_lt_p _)
  have w1 : bignumVal (paC1.2.map (WE.eval ρ)) = bignumVal (paB16.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB16.2 paN19 gc1)
  have w2 : bignumVal (paC2.2.map (WE.eval ρ)) = bignumVal (paB17.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB17.2 _ gc2)
  have w3 : bignumVal (paC3.2.map (WE.eval ρ)) = bignumVal (paB19.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB19.2 (paN19 + paC1.1.length + paC2.1.length) gc3)
  have w4 : bignumVal (paC4.2.map (WE.eval ρ)) = bignumVal (paB18.2.map (WE.eval ρ)) :=
    congrArg bignumVal
      (feCopyG_val ρ paB18.2 (paN19 + paC1.1.length + paC2.1.length + paC3.1.length) gc4)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [w1, v16, v12, v13, v6, v3, v11, v9, v1, v2, v4, v5, v8, v10, paSpec]
  · simp only [w2, v17, v14, v15, v6, v3, v11, v9, v1, v2, v4, v5, v8, v10, paSpec]
  · simp only [w3, v19, v13, v14, v11, v9, v8, v10, paSpec]
  · simp only [w4, v18, v12, v15, v6, v3, v1, v2, v4, v5, paSpec]


/-! ## 15. The canonical block -/

/-- The canonical block is the concatenation of the canonical parts, each from the abstract
    state after the previous part. -/
theorem canonD_pointAdd :
    canonD shippedBank ed25519PointAddShippedBlock =
      canonFromD shippedBank {} ed25519PointAddShippedPart01 ++
      (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02 ++
      (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03 ++
      (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04 ++
      (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05 ++
      (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06 ++
      (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07 ++
      (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08 ++
      (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09 ++
      canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)))))))) := by
  unfold canonD ed25519PointAddShippedBlock
  simp only [List.append_assoc]
  rw [canonFromD_append, pointAdd_D_part01.2, canonFromD_append, pointAdd_D_part02.2,
    canonFromD_append, pointAdd_D_part03.2, canonFromD_append, pointAdd_D_part04.2,
    canonFromD_append, pointAdd_D_part05.2, canonFromD_append, pointAdd_D_part06.2,
    canonFromD_append, pointAdd_D_part07.2, canonFromD_append, pointAdd_D_part08.2,
    canonFromD_append, pointAdd_D_part09.2]

/-- The cells the canonical block reads or writes: the sixteen output limbs at `%rdi`, the
    thirty-two input limbs at `%rsi`, and the stack cells at `-128` and `0, 8, …, 392`. -/
def paCells : List (String × Int) :=
  (List.range 16).map (fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
  (List.range 32).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
  (("%rsp", -128) :: (List.range 50).map (fun i => ("%rsp", ((8 * i : Nat) : Int))))

theorem pa_foot1 :
    footOK paCells (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true := by
  decide +kernel
theorem pa_foot2 :
    footOK paCells (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02)
      = true := by decide +kernel
theorem pa_foot3 :
    footOK paCells (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03)
      = true := by decide +kernel
theorem pa_foot4 :
    footOK paCells (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04)
      = true := by decide +kernel
theorem pa_foot5 :
    footOK paCells (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05)
      = true := by decide +kernel
theorem pa_foot6 :
    footOK paCells (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06)
      = true := by decide +kernel
theorem pa_foot7 :
    footOK paCells (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07)
      = true := by decide +kernel
theorem pa_foot8 :
    footOK paCells (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08)
      = true := by decide +kernel
theorem pa_foot9 :
    footOK paCells (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09)
      = true := by decide +kernel
theorem pa_foot10 :
    footOK paCells (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)
      = true := by decide +kernel

theorem pa_foot : footOK paCells (canonD shippedBank ed25519PointAddShippedBlock) = true := by
  rw [canonD_pointAdd]
  simp only [footOK_append, pa_foot1, pa_foot2, pa_foot3, pa_foot4, pa_foot5, pa_foot6,
    pa_foot7, pa_foot8, pa_foot9, pa_foot10, Bool.and_self]


/-! ## 16. The canonical block computes the addition -/

/-- The entry slot values: slots `25 .. 56` hold the input cells of `%rsi`, and slots
    `16 .. 24` the literals of `cK`. -/
def rho0 (st : JState 64) (j : Nat) : BitVec 64 :=
  if 25 ≤ j ∧ j < 57 then st.mem "%rsi" ((8 * (j - 25) : Nat) : Int)
  else if 16 ≤ j ∧ j < 25 then BitVec.ofNat 64 (cLits.getD (j - 16) 0)
  else 0

/-- The slot values of the addition on the input cells of `st`. -/
def rhoPA (st : JState 64) : Nat → BitVec 64 := wrun 57 paStmts (rho0 st)

theorem paStmts_wf : wfB 57 paStmts = true := by decide +kernel



theorem paC1_eq : paC1.2 = [.v 2352, .v 2353, .v 2354, .v 2355] := by decide +kernel
theorem paC2_eq : paC2.2 = [.v 2356, .v 2357, .v 2358, .v 2359] := by decide +kernel
theorem paC3_eq : paC3.2 = [.v 2360, .v 2361, .v 2362, .v 2363] := by decide +kernel
theorem paC4_eq : paC4.2 = [.v 2364, .v 2365, .v 2366, .v 2367] := by decide +kernel

theorem paOuts_eq : paOuts = [.v 2352, .v 2353, .v 2354, .v 2355, .v 2356, .v 2357,
    .v 2358, .v 2359, .v 2360, .v 2361, .v 2362, .v 2363, .v 2364, .v 2365, .v 2366,
    .v 2367] := by decide +kernel

theorem holds_rhoPA (st : JState 64) : Holds (rhoPA st) 57 paStmts :=
  holds_wrun _ _ _ paStmts_wf

theorem rhoPA_const (st : JState 64) (j c : Nat) (h : cK j = some c) :
    rhoPA st j = BitVec.ofNat 64 c := by
  unfold cK at h
  split_ifs at h with hj
  have hlt : j - 16 < cLits.length := by
    rcases Nat.lt_or_ge (j - 16) cLits.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h
      cases h
  have hj25 : j < 25 := by
    have : cLits.length = 9 := by decide +kernel
    omega
  have hgd : cLits.getD (j - 16) 0 = c := by
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  rw [rhoPA, wrun_below _ _ _ _ (by omega), rho0]
  rw [if_neg (by omega), if_pos ⟨hj, hj25⟩, hgd]

theorem paIn_holds (st : JState 64) : MapHolds (rhoPA st) paIn st := by
  intro p hp
  simp only [paIn, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [Loc.val, WE.eval, rhoPA]
  rw [wrun_below _ _ _ _ (by omega)]
  simp only [rho0]
  rw [if_pos ⟨by omega, by omega⟩]
  congr 2
  omega


/-- The value of input coordinate `k`: the four limbs at `%rsi + 32k`. -/
def paInVal (st : JState 64) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i => st.mem "%rsi" ((8 * (4 * k + i) : Nat) : Int))

/-- The value of output coordinate `k`: the four limbs at `%rdi + 32k`. -/
def paOutVal (s : JState 64) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i => s.mem "%rdi" ((8 * (4 * k + i) : Nat) : Int))

theorem slots_eq_in (st : JState 64) (k : Nat) (hk : k < 8) :
    (slotsFrom (25 + 4 * k) 4).map (WE.eval (rhoPA st))
      = (List.range 4).map fun i => st.mem "%rsi" ((8 * (4 * k + i) : Nat) : Int) := by
  simp only [slotsFrom, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_def, WE.eval, rhoPA]
  rw [wrun_below _ _ _ _ (by omega), rho0, if_pos ⟨by omega, by omega⟩]
  congr 2
  omega

theorem bv_in (st : JState 64) (k : Nat) (hk : k < 8) :
    bv (rhoPA st) (slotsFrom (25 + 4 * k) 4) = paInVal st k := by
  rw [bv, slots_eq_in st k hk, paInVal]

set_option maxRecDepth 8000 in
/-- **The canonical block computes the addition.** For every name-keyed state whose eight
    input coordinates are below `p25519`, the canonical block stores at `%rdi` the four
    coordinates of `paSpec` on those values, each below `p25519`. -/
theorem paCanon_correct (st : JState 64)
    (b0 : paInVal st 0 < 2 ^ 255 - 19) (b1 : paInVal st 1 < 2 ^ 255 - 19)
    (b2 : paInVal st 2 < 2 ^ 255 - 19) (b3 : paInVal st 3 < 2 ^ 255 - 19)
    (b4 : paInVal st 4 < 2 ^ 255 - 19) (b5 : paInVal st 5 < 2 ^ 255 - 19)
    (b6 : paInVal st 6 < 2 ^ 255 - 19) (b7 : paInVal st 7 < 2 ^ 255 - 19) :
    paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 0
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 1
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 2
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.2.1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 3
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.2.2 := by
  have hH := holds_rhoPA st
  have hK : ∀ (a j c : Nat), j < a → cK j = some c → rhoPA st j = BitVec.ofNat 64 c :=
    fun _ j c _ hc => rhoPA_const st j c hc
  have hsp : ∀ (l l1 l2 : List WE) (m n : Nat), l = l1 ++ l2 → l1.length = m →
      Holds (rhoPA st) n l → Holds (rhoPA st) n l1 ∧ Holds (rhoPA st) (n + m) l2 := by
    intro l l1 l2 m n he hm h
    subst he
    subst hm
    exact (holds_append (rhoPA st) l1 l2 n).1 h
  obtain ⟨k1, r2⟩ := hsp paR1 paSl1 paR2 182 57 (List.take_append_drop 182 paR1).symm
    paSl1_len hH
  obtain ⟨k2, r3⟩ := hsp paR2 paSl2 paR3 260 239 (List.take_append_drop 260 paR2).symm
    paSl2_len r2
  obtain ⟨k3, r4⟩ := hsp paR3 paSl3 paR4 263 499 (List.take_append_drop 263 paR3).symm
    paSl3_len r3
  obtain ⟨k4, r5⟩ := hsp paR4 paSl4 paR5 258 762 (List.take_append_drop 258 paR4).symm
    paSl4_len r4
  obtain ⟨k5, r6⟩ := hsp paR5 paSl5 paR6 250 1020 (List.take_append_drop 250 paR5).symm
    paSl5_len r5
  obtain ⟨k6, r7⟩ := hsp paR6 paSl6 paR7 225 1270 (List.take_append_drop 225 paR6).symm
    paSl6_len r6
  obtain ⟨k7, r8⟩ := hsp paR7 paSl7 paR8 253 1495 (List.take_append_drop 253 paR7).symm
    paSl7_len r7
  obtain ⟨k8, r9⟩ := hsp paR8 paSl8 paR9 248 1748 (List.take_append_drop 248 paR8).symm
    paSl8_len r8
  obtain ⟨k9, k10⟩ := hsp paR9 paSl9 paSl10 255 1996 (List.take_append_drop 255 paR9).symm
    paSl9_len r9
  clear hsp r2 r3 r4 r5 r6 r7 r8 r9
  have znone : ∀ (s : JState 64), ZfHolds (rhoPA st) none s := fun _ e he => by cases he
  have cnone : ∀ (s : JState 64), CfHolds (rhoPA st) none s := fun _ e he => by cases he
  obtain ⟨q1, c1, -⟩ := partCheck2_sound 57 paSl1 paIn none none paMap1
    (some (aoWE (.v 238))) none _ pa_part1 (rhoPA st)
    k1 (hK 57) st (paIn_holds st) (cnone st) (znone st)
  obtain ⟨s1, hs1⟩ : ∃ s,
      runBlock st (canonFromD shippedBank {} ed25519PointAddShippedPart01) = s := ⟨_, rfl⟩
  rw [hs1] at q1 c1
  obtain ⟨q2, c2, -⟩ := partCheck2_sound 239 paSl2 paMap1 (some (aoWE (.v 238)))
    none paMap2 none none _ pa_part2 (rhoPA st)
    k2 (hK 239) s1 q1 c1 (znone _)
  obtain ⟨s2, hs2⟩ : ∃ s,
      runBlock s1 (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02) = s :=
    ⟨_, rfl⟩
  rw [hs2] at q2 c2
  obtain ⟨q3, c3, -⟩ := partCheck2_sound 499 paSl3 paMap2 none none paMap3
    (some (.v 761)) none _ pa_part3 (rhoPA st)
    k3 (hK 499) s2 q2 c2 (znone _)
  obtain ⟨s3, hs3⟩ : ∃ s,
      runBlock s2 (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03) = s :=
    ⟨_, rfl⟩
  rw [hs3] at q3 c3
  obtain ⟨q4, c4, -⟩ := partCheck2_sound 762 paSl4 paMap3 (some (.v 761)) none
    paMap4 (some (.v 1019)) none _ pa_part4 (rhoPA st)
    k4 (hK 762) s3 q3 c3 (znone _)
  obtain ⟨s4, hs4⟩ : ∃ s,
      runBlock s3 (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04) = s :=
    ⟨_, rfl⟩
  rw [hs4] at q4 c4
  obtain ⟨q5, c5, -⟩ := partCheck2_sound 1020 paSl5 paMap4 (some (.v 1019))
    none paMap5 (some (.v 1269)) none _ pa_part5 (rhoPA st)
    k5 (hK 1020) s4 q4 c4 (znone _)
  obtain ⟨s5, hs5⟩ : ∃ s,
      runBlock s4 (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05) = s :=
    ⟨_, rfl⟩
  rw [hs5] at q5 c5
  obtain ⟨q6, c6, -⟩ := partCheck2_sound 1270 paSl6 paMap5 (some (.v 1269))
    none paMap6 (some (aoWE (.v 1494))) none _ pa_part6 (rhoPA st)
    k6 (hK 1270) s5 q5 c5 (znone _)
  obtain ⟨s6, hs6⟩ : ∃ s,
      runBlock s5 (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06) = s :=
    ⟨_, rfl⟩
  rw [hs6] at q6 c6
  obtain ⟨q7, c7, -⟩ := partCheck2_sound 1495 paSl7 paMap6
    (some (aoWE (.v 1494))) none paMap7 (some (.v 1747)) none _ pa_part7 (rhoPA st)
    k7 (hK 1495) s6 q6 c6 (znone _)
  obtain ⟨s7, hs7⟩ : ∃ s,
      runBlock s6 (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07) = s :=
    ⟨_, rfl⟩
  rw [hs7] at q7 c7
  obtain ⟨q8, c8, -⟩ := partCheck2_sound 1748 paSl8 paMap7 (some (.v 1747))
    none paMap8 none none _ pa_part8 (rhoPA st)
    k8 (hK 1748) s7 q7 c7 (znone _)
  obtain ⟨s8, hs8⟩ : ∃ s,
      runBlock s7 (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08) = s :=
    ⟨_, rfl⟩
  rw [hs8] at q8 c8
  obtain ⟨q9, c9, -⟩ := partCheck2_sound 1996 paSl9 paMap8 none none paMap9
    (some (aoWE (.v 2250))) none _ pa_part9 (rhoPA st)
    k9 (hK 1996) s8 q8 c8 (znone _)
  obtain ⟨s9, hs9⟩ : ∃ s,
      runBlock s8 (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09) = s :=
    ⟨_, rfl⟩
  rw [hs9] at q9 c9
  obtain ⟨q10, -, -⟩ := partCheck2_sound 2251 paSl10 paMap9
    (some (aoWE (.v 2250))) none paOut none none _ pa_part10 (rhoPA st)
    k10 (hK 2251) s9 q9 c9 (znone _)
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9 c1 c2 c3 c4 c5 c6 c7 c8 c9
  rw [← hs9, ← hs8, ← hs7, ← hs6, ← hs5, ← hs4, ← hs3, ← hs2, ← hs1] at q10
  simp only [← runBlock_cat, List.append_assoc] at q10
  rw [← canonD_pointAdd] at q10
  generalize runBlock st (canonD shippedBank ed25519PointAddShippedBlock) = out at q10 ⊢
  have hmem : ∀ j, j < 16 → out.mem "%rdi" ((8 * j : Nat) : Int) = rhoPA st (2352 + j) := by
    intro j hj
    have hin : (Loc.cell "%rdi" ((8 * j : Nat) : Int), WE.v (2352 + j)) ∈ paOut := by
      simp only [paOut, List.mem_map, List.mem_range]
      exact ⟨j, hj, by rw [paOuts_eq]; interval_cases j <;> rfl⟩
    have := q10 _ hin
    simpa only [Loc.val, WE.eval] using this
  have hg : ∀ k, k < 4 → paOutVal out k
      = bignumVal ((List.range 4).map fun i => rhoPA st (2352 + (4 * k + i))) := by
    intro k hk
    simp only [paOutVal]
    refine congrArg bignumVal ?_
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    exact hmem (4 * k + i) (by omega)
  have hbv : ∀ k, k < 8 → bv (rhoPA st) (slotsFrom (25 + 4 * k) 4) = paInVal st k :=
    fun k hk => bv_in st k hk
  have hv := paG_val (rhoPA st) hH
    (by rw [show (25 : Nat) = 25 + 4 * 0 from rfl, hbv 0 (by omega)]; exact b0)
    (by rw [show (29 : Nat) = 25 + 4 * 1 from rfl, hbv 1 (by omega)]; exact b1)
    (by rw [show (33 : Nat) = 25 + 4 * 2 from rfl, hbv 2 (by omega)]; exact b2)
    (by rw [show (37 : Nat) = 25 + 4 * 3 from rfl, hbv 3 (by omega)]; exact b3)
    (by rw [show (41 : Nat) = 25 + 4 * 4 from rfl, hbv 4 (by omega)]; exact b4)
    (by rw [show (45 : Nat) = 25 + 4 * 5 from rfl, hbv 5 (by omega)]; exact b5)
    (by rw [show (49 : Nat) = 25 + 4 * 6 from rfl, hbv 6 (by omega)]; exact b6)
    (by rw [show (53 : Nat) = 25 + 4 * 7 from rfl, hbv 7 (by omega)]; exact b7)
  rw [show (25 : Nat) = 25 + 4 * 0 from rfl, show (29 : Nat) = 25 + 4 * 1 from rfl,
    show (33 : Nat) = 25 + 4 * 2 from rfl, show (37 : Nat) = 25 + 4 * 3 from rfl,
    show (41 : Nat) = 25 + 4 * 4 from rfl, show (45 : Nat) = 25 + 4 * 5 from rfl,
    show (49 : Nat) = 25 + 4 * 6 from rfl, show (53 : Nat) = 25 + 4 * 7 from rfl,
    hbv 0 (by omega), hbv 1 (by omega), hbv 2 (by omega), hbv 3 (by omega),
    hbv 4 (by omega), hbv 5 (by omega), hbv 6 (by omega), hbv 7 (by omega)] at hv
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [bv, paC1_eq, paC2_eq, paC3_eq, paC4_eq, List.map_cons, List.map_nil,
    WE.eval] at hv1 hv2 hv3 hv4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg 0 (by omega), ← hv1]; rfl
  · rw [hg 1 (by omega), ← hv2]; rfl
  · rw [hg 2 (by omega), ← hv3]; rfl
  · rw [hg 3 (by omega), ← hv4]; rfl


/-! ## 17. The address machine -/

/-- The value of input coordinate `k` of the address state: the four words at
    `%rsi + 32k`. -/
def paInValA (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

/-- The value of output coordinate `k` after the block: the four words at `%rdi + 32k`. -/
def paOutValA (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 (runBlockA sa ed25519PointAddShippedBlock).mem
      (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

theorem paInValA_eq (sa : AState) (k : Nat) (_hk : k < 8) :
    paInValA sa k = paInVal (jOf shippedBank sa) k := by
  have hsi : shippedBank "%rsi" = some "%rsi" := by simp [shippedBank]
  simp only [paInValA, paInVal, jOf]
  refine congrArg bignumVal (List.map_congr_left ?_)
  intro i _
  rw [absMem_shipped _ _ _ _ hsi]

set_option maxRecDepth 8000 in
/-- **The shipped block computes the addition.** When the cells of `paCells` occupy
    pairwise disjoint eight-byte ranges and the eight input coordinates at `%rsi + 32k`
    are below `p25519`, `runBlockA` of the imported block leaves at `%rdi + 32k` the four
    coordinates of `paSpec` on those values. -/
theorem paShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs paCells)
    (b0 : paInValA sa 0 < 2 ^ 255 - 19) (b1 : paInValA sa 1 < 2 ^ 255 - 19)
    (b2 : paInValA sa 2 < 2 ^ 255 - 19) (b3 : paInValA sa 3 < 2 ^ 255 - 19)
    (b4 : paInValA sa 4 < 2 ^ 255 - 19) (b5 : paInValA sa 5 < 2 ^ 255 - 19)
    (b6 : paInValA sa 6 < 2 ^ 255 - 19) (b7 : paInValA sa 7 < 2 ^ 255 - 19) :
    paOutValA sa 0 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).1
      ∧ paOutValA sa 1 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.1
      ∧ paOutValA sa 2 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.2.1
      ∧ paOutValA sa 3 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.2.2 := by
  obtain ⟨-, -, hKc⟩ := runBlockA_simD_on shippedBank ed25519PointAddShippedBlock paCells
    ed25519PointAdd_disciplinedD
    (readsBeforeWritesFromB_of_reads _ (footOK_reads pa_foot) false)
    (footOK_writes pa_foot) sa hsep
  have hdi : shippedBank "%rdi" = some "%rdi" := by simp [shippedBank]
  have hout : ∀ k, k < 4 → paOutValA sa k
      = paOutVal (runBlock (jOf shippedBank sa)
        (canonD shippedBank ed25519PointAddShippedBlock)) k := by
    intro k hk
    simp only [paOutValA, paOutVal]
    refine congrArg bignumVal (List.map_congr_left ?_)
    intro i hi
    simp only [List.mem_range] at hi
    have hmem : ("%rdi", ((8 * (4 * k + i) : Nat) : Int)) ∈ paCells :=
      List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨4 * k + i, List.mem_range.2 (show 4 * k + i < 16 by omega), rfl⟩))
    rw [← hKc _ hmem, absMem_shipped _ _ _ _ hdi]
  have hin : ∀ k, k < 8 → paInValA sa k = paInVal (jOf shippedBank sa) k :=
    fun k hk => paInValA_eq sa k hk
  rw [hin 0 (by omega)] at b0
  rw [hin 1 (by omega)] at b1
  rw [hin 2 (by omega)] at b2
  rw [hin 3 (by omega)] at b3
  rw [hin 4 (by omega)] at b4
  rw [hin 5 (by omega)] at b5
  rw [hin 6 (by omega)] at b6
  rw [hin 7 (by omega)] at b7
  rw [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hin 3 (by omega),
    hin 4 (by omega), hin 5 (by omega), hin 6 (by omega), hin 7 (by omega)]
  have hc := paCanon_correct (jOf shippedBank sa) b0 b1 b2 b3 b4 b5 b6 b7
  rw [hout 0 (by omega), hout 1 (by omega), hout 2 (by omega), hout 3 (by omega)]
  exact hc


/-! ## 18. The coordinates of the source formula -/

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (p25519)
open CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd (addSpec)
open CatCrypt.Util (ed25519D)

theorem cast_mod_p (a : Nat) :
    ((a % (2 ^ 255 - 19) : Nat) : ZMod p25519) = (a : ZMod p25519) :=
  ZMod.natCast_mod a _

theorem cast_sub_p (x : Nat) (h : x ≤ 2 ^ 255 - 19) :
    (((2 ^ 255 - 19 - x : Nat)) : ZMod p25519) = -(x : ZMod p25519) := by
  rw [Nat.cast_sub h]
  show (p25519 : ZMod p25519) - (x : ZMod p25519) = _
  rw [ZMod.natCast_self]
  ring

theorem cast_twoDNat : ((twoDNat : Nat) : ZMod p25519) = ed25519D + ed25519D := by
  decide +kernel


/-- **The natural-number coordinates are the coordinates of `addSpec`.** In `ZMod p25519`
    the four values of `paSpec` are the four coordinates of the extended-coordinate
    addition of `Ed25519PointAddCompile.addSpec` at the curve constant `ed25519D`. -/
theorem paSpec_addSpec (x1 y1 z1 t1 x2 y2 z2 t2 : Nat)
    (hx1 : x1 ≤ 2 ^ 255 - 19) (hx2 : x2 ≤ 2 ^ 255 - 19) :
    (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.2.1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.2.1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.2.2 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.2.2 := by
  have hle : ∀ a : Nat, a % (2 ^ 255 - 19) ≤ 2 ^ 255 - 19 := fun a => le_of_lt (mod_lt_p a)
  have hsub : ∀ a : Nat, ((2 ^ 255 - 19 - a % (2 ^ 255 - 19) : Nat) : ZMod p25519)
      = -((a % (2 ^ 255 - 19) : Nat) : ZMod p25519) := fun a => cast_sub_p _ (hle a)
  simp only [paSpec, addSpec]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Nat.cast_mul, Nat.cast_add, cast_mod_p, hsub, cast_sub_p x1 hx1,
      cast_sub_p x2 hx2, cast_twoDNat] <;>
    ring

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
