/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
public import CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAddCompile

/-!
# The flag-aware executor and the part checks of the shipped `ed25519_point_add`

`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` is the body of the function
`ed25519_point_add(u64 *out, const u64 *inp)` as printed by the owned backend.
`Ed25519PointAddShippedProof` states its correctness over this module.

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
`paG` is the whole program from slot `57` over the thirty-two input slots `25 .. 56`.

## Main results

* `partCheck2_sound`: a part check implies the canonical part maps the entry locations and
  flags to the exit ones under the slot values.
* `pa_part1` … `pa_part10`: the ten part checks of the block, each by `decide +kernel`.
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
  | .storeMem b o (.imm n) =>
      match T.addN (.lit n) with
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
    | imm n =>
      rcases hp : T.addN (.lit n) with ⟨T₁, x⟩
      simp only [symStep2, hp, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨g, l, v⟩ := Tb.addN_spec E T (.lit n) hT trivial
      rw [hp] at g l v
      exact ⟨g, srel2_of_srel hT g hR ((hR.1.grow hT g).setM b o x l _ v) rfl rfl⟩
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

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
