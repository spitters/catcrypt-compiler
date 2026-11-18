/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Keccak
public import CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect

/-!
# The GF(2^128) multiply as a constant-time `jasminDialect` template

The product in GF(2^128) at the GCM modulus `X^128 + X^7 + X^2 + X + 1`, `Gf2Dialect.mulRed`,
as a straight-line program of `jasminDialect` on 64-bit words generated through the compiler of
`HashTemplate.StraightLine`. A 128-bit operand is the pair of its low and high 64-bit words.

The program computes the 256-bit carry-less product by Karatsuba from three 64 × 64 carry-less
products, and reduces it by two folds of the high part by the constant `0x87`, each fold a
carry-less product by `0x87`; this is the order of operations of `Gf2Dialect.bf128MulSpec`.
Each 64 × 64 carry-less product is bit-serial: step `i` masks the shifts of the second operand
by `i` with the broadcast of bit `i` of the first operand (`0 - ((a >>> i) &&& 1)`) and adds
them into the low and high words. The program has no branch and no memory access at an index
that depends on its inputs.

The program reads the four input words (the low and high words of the two operands) from one
stack array and stores the low and high words of the product by register index into a second
stack array, the output array, which it does not read (the form `compileRegion` accepts,
`HashTemplate/AGENTS.md`).

## Main definitions

* `gf128ClmulStep`, `gf128Clmul`: the bit-serial 64 × 64 carry-less product on words.
* `gf128MulWords`: the product in GF(2^128) on words, Karatsuba and the two folds.
* `gf128ClmulStepLets`, `gf128ClmulLets`, `gf128PrepSt`, `gf128Lets`: the symbolic
  carry-less product and the symbolic multiply with its store list.
* `gf128InCtxt`, `gf128MulBody`: the input context and the program.

## Main results

* `clmul64W_eq_gf128Clmul`: the carry-less product of `jasminDialect` is the bit-serial one.
* `mulRed_eq_gf128MulWords`: `Gf2Dialect.mulRed` is the product on words.
* `gf128MulBody_value`: the program returns the two words of `Gf2Dialect.mulRed` of its
  operands, whatever the contents of the output array.
* `gf128MulBody_events`: the program emits the same events at every two valuations, at
  leakage parameters with no variable-time operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect (mulRed bf128MulSpec gfClmulLoSpec
  gfClmulHiSpec)
open Ctxt (Var Valuation)

/-! ## 1. The reference on words -/

/-- Step `i` of the bit-serial carry-less product of `a` and `b`: the shift of `b` by `i`,
    masked by bit `i` of `a`, added into the low and high words `p`. -/
def gf128ClmulStep (a b : BitVec 64) (p : BitVec 64 × BitVec 64) (i : Nat) :
    BitVec 64 × BitVec 64 :=
  let m := 0 - ((a >>> i) &&& 1)
  (p.1 ^^^ ((b <<< i) &&& m), if i = 0 then p.2 else p.2 ^^^ ((b >>> (64 - i)) &&& m))

/-- The carry-less product of two words, bit-serial: its low and high words. -/
def gf128Clmul (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range 64).foldl (gf128ClmulStep a b) (0, 0)

/-- One step of `clmul64W` on the joined words is one step of `gf128ClmulStep`. -/
theorem clmul64StepW_append (a b : BitVec 64) (p : BitVec 64 × BitVec 64) (i : Nat)
    (hi : i < 64) :
    clmul64StepW a (b.setWidth 128) (p.2 ++ p.1) i =
      (gf128ClmulStep a b p i).2 ++ (gf128ClmulStep a b p i).1 := by
  obtain ⟨lo, hi'⟩ := p
  have hc : (a >>> i) &&& 1 = 0 ∨ (a >>> i) &&& 1 = 1 := by
    generalize a >>> i = x
    bv_decide
  unfold clmul64StepW gf128ClmulStep
  rcases hc with hc | hc
  · simp only [hc]
    split <;> bv_decide
  · simp only [hc]
    rw [show (0#128 : BitVec 128) - BitVec.setWidth 128 (1 : BitVec 64) = BitVec.allOnes 128
      by decide, show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide]
    simp only [BitVec.and_allOnes]
    ext j hj
    grind

/-- The carry-less product of `jasminDialect` is the bit-serial product on words. -/
theorem clmul64W_eq_gf128Clmul (a b : BitVec 64) :
    clmul64W a b = (gf128Clmul a b).2 ++ (gf128Clmul a b).1 := by
  have key : ∀ n, n ≤ 64 →
      Fin.foldl n (fun acc i => clmul64StepW a (b.setWidth 128) acc i.val) 0 =
        ((List.range n).foldl (gf128ClmulStep a b) (0, 0)).2 ++
          ((List.range n).foldl (gf128ClmulStep a b) (0, 0)).1 := by
    intro n
    induction n with
    | zero => intro _; grind
    | succ n ih =>
        intro hn
        rw [Fin.foldl_succ_last, List.range_succ, List.foldl_append]
        simp only [Fin.val_castSucc, Fin.val_last, List.foldl_cons, List.foldl_nil]
        rw [ih (by omega)]
        exact clmul64StepW_append a b _ n (by omega)
  exact key 64 le_rfl

/-- **The product in GF(2^128) on words**: the Karatsuba product of `a1 a0` and `b1 b0` from
    three carry-less products, then the two folds of its high part by `0x87`; the low and high
    words of the result. -/
def gf128MulWords (a0 a1 b0 b1 : BitVec 64) : BitVec 64 × BitVec 64 :=
  let p := gf128Clmul a0 b0
  let q := gf128Clmul a1 b1
  let r := gf128Clmul (a0 ^^^ a1) (b0 ^^^ b1)
  let l1 := p.2 ^^^ (r.1 ^^^ p.1 ^^^ q.1)
  let h0 := q.1 ^^^ (r.2 ^^^ p.2 ^^^ q.2)
  let t := gf128Clmul h0 0x87
  let c := gf128Clmul q.2 0x87
  let u := gf128Clmul c.2 0x87
  (p.1 ^^^ t.1 ^^^ u.1, l1 ^^^ t.2 ^^^ c.1 ^^^ u.2)

/-- The low half of a joined pair of words. -/
@[simp] theorem gf128_setWidth_append (x y : BitVec 64) : (x ++ y).setWidth 64 = y := by
  bv_decide

/-- The high half of a joined pair of words. -/
@[simp] theorem gf128_shr_setWidth_append (x y : BitVec 64) :
    ((x ++ y) >>> 64).setWidth 64 = x := by
  bv_decide

/-- The Karatsuba halves of `Gf2Dialect` on joined words. -/
theorem gfClmulSpec_append (a0 a1 b0 b1 : BitVec 64) :
    gfClmulLoSpec (a1 ++ a0) (b1 ++ b0) =
      ((gf128Clmul a0 b0).2 ^^^ ((gf128Clmul (a0 ^^^ a1) (b0 ^^^ b1)).1 ^^^
        (gf128Clmul a0 b0).1 ^^^ (gf128Clmul a1 b1).1)) ++ (gf128Clmul a0 b0).1 ∧
    gfClmulHiSpec (a1 ++ a0) (b1 ++ b0) =
      (gf128Clmul a1 b1).2 ++ ((gf128Clmul a1 b1).1 ^^^ ((gf128Clmul (a0 ^^^ a1) (b0 ^^^ b1)).2 ^^^
        (gf128Clmul a0 b0).2 ^^^ (gf128Clmul a1 b1).2)) := by
  have ha : ((a1 ++ a0) ^^^ ((a1 ++ a0) >>> (8 * 8))).setWidth 64 = a0 ^^^ a1 := by bv_decide
  have hb : ((b1 ++ b0) ^^^ ((b1 ++ b0) >>> (8 * 8))).setWidth 64 = b0 ^^^ b1 := by bv_decide
  simp only [gfClmulLoSpec, gfClmulHiSpec, clmul128W, clmulHalfW]
  simp (config := {decide := true}) only [ha, hb, gf128_setWidth_append,
    gf128_shr_setWidth_append, ite_true, ite_false, clmul64W_eq_gf128Clmul]
  generalize gf128Clmul a0 b0 = P
  generalize gf128Clmul a1 b1 = Q
  generalize gf128Clmul (a0 ^^^ a1) (b0 ^^^ b1) = R
  obtain ⟨P0, P1⟩ := P
  obtain ⟨Q0, Q1⟩ := Q
  obtain ⟨R0, R1⟩ := R
  constructor <;> bv_decide

/-- `Gf2Dialect.mulRed` on joined words is the product on words. -/
theorem mulRed_eq_gf128MulWords (a0 a1 b0 b1 : BitVec 64) :
    mulRed (a1 ++ a0) (b1 ++ b0) =
      (gf128MulWords a0 a1 b0 b1).2 ++ (gf128MulWords a0 a1 b0 b1).1 := by
  have h87 : (0x87#128 : BitVec 128).setWidth 64 = 0x87#64 := by decide
  obtain ⟨hlo, hhi⟩ := gfClmulSpec_append a0 a1 b0 b1
  simp only [mulRed, bf128MulSpec, gf128MulWords]
  rw [hlo, hhi]
  clear hlo hhi
  generalize gf128Clmul a0 b0 = P
  generalize gf128Clmul a1 b1 = Q
  generalize gf128Clmul (a0 ^^^ a1) (b0 ^^^ b1) = R
  obtain ⟨P0, P1⟩ := P
  obtain ⟨Q0, Q1⟩ := Q
  obtain ⟨R0, R1⟩ := R
  simp (config := {decide := true}) only [clmul128W, clmulHalfW, h87, gf128_setWidth_append,
    gf128_shr_setWidth_append, ite_true, ite_false, clmul64W_eq_gf128Clmul]
  generalize gf128Clmul (Q0 ^^^ (R1 ^^^ P1 ^^^ Q1)) 0x87#64 = T
  generalize gf128Clmul Q1 0x87#64 = C
  obtain ⟨T0, T1⟩ := T
  obtain ⟨C0, C1⟩ := C
  simp only [Nat.reduceMul, gf128_shr_setWidth_append]
  generalize gf128Clmul C1 0x87#64 = U
  obtain ⟨U0, U1⟩ := U
  bv_decide

/-! ## 2. The symbolic multiply -/

/-- Step `i` of the bit-serial carry-less product of the words numbered `a` and `b` into the
    low and high words numbered `q.1`: binds the mask, the new low word and, for `i ≠ 0`, the
    new high word. -/
def gf128ClmulStepLets (a b i : Nat) (q : (Nat × Nat) × LetSt 64) : (Nat × Nat) × LetSt 64 :=
  let m := q.2.push (.bin .sub (.const 0) (.bin .and (.shr i (.var a)) (.const 1)))
  let lo := m.2.push (.bin .xor (.var q.1.1)
    (.bin .and (.bin .shl (.var b) (.const (BitVec.ofNat 64 i))) (.var m.1)))
  if i = 0 then ((lo.1, q.1.2), lo.2) else
  let hi := lo.2.push (.bin .xor (.var q.1.2) (.bin .and (.shr (64 - i) (.var b)) (.var m.1)))
  ((lo.1, hi.1), hi.2)

/-- The symbolic carry-less product of the words numbered `a` and `b`, from the zero word
    numbered `z`: the numbers of its low and high words and the let-list. -/
def gf128ClmulLets (z a b : Nat) (s : LetSt 64) : (Nat × Nat) × LetSt 64 :=
  (List.range 64).foldl (fun q i => gf128ClmulStepLets a b i q) ((z, z), s)

/-- The let-list before the carry-less products, over the input words numbered `0, …, 3`
    (`a0 a1 b0 b1`): the zero word `4`, the constant `0x87` as word `5`, and the Karatsuba
    operands `a0 ⊕ a1`, `b0 ⊕ b1` as words `6` and `7`. -/
def gf128PrepSt : LetSt 64 :=
  ⟨8, [.bin .xor (.var 2) (.var 3), .bin .xor (.var 0) (.var 1), .const 0x87, .const 0]⟩

/-- **The symbolic GF(2^128) multiply**: the store list, the index `0` receiving the low word
    and the index `1` the high word of the product, and the let-list. -/
def gf128Lets : List (Nat × Nat) × LetSt 64 :=
  let p := gf128ClmulLets 4 0 2 gf128PrepSt
  let q := gf128ClmulLets 4 1 3 p.2
  let r := gf128ClmulLets 4 6 7 q.2
  let l1 := r.2.push (.bin .xor (.var p.1.2)
    (.bin .xor (.bin .xor (.var r.1.1) (.var p.1.1)) (.var q.1.1)))
  let h0 := l1.2.push (.bin .xor (.var q.1.1)
    (.bin .xor (.bin .xor (.var r.1.2) (.var p.1.2)) (.var q.1.2)))
  let t := gf128ClmulLets 4 h0.1 5 h0.2
  let c := gf128ClmulLets 4 q.1.2 5 t.2
  let u := gf128ClmulLets 4 c.1.2 5 c.2
  let o0 := u.2.push (.bin .xor (.bin .xor (.var p.1.1) (.var t.1.1)) (.var u.1.1))
  let o1 := o0.2.push (.bin .xor (.bin .xor (.bin .xor (.var l1.1) (.var t.1.2))
    (.var c.1.1)) (.var u.1.2))
  ([(0, o0.1), (1, o1.1)], o1.2)

/-! ## 3. The program -/

/-- The input context of the multiply: the input array of the four words `a0 a1 b0 b1` and
    the output array of the two words of the product. -/
abbrev gf128InCtxt : Ctxt jasminDialect := [.stackArr 64 4, .stackArr 64 2]

/-- **The GF(2^128) multiply as a `jasminDialect` program**: the loads of the four words of the
    input array as the words numbered `0, …, 3`, the compiled symbolic multiply `gf128Lets`
    from the word numbered `4`, and the stores of the two words of the product into the output
    array at register indices. -/
def gf128MulBody : Com jasminDialect gf128InCtxt (.stackArr 64 2) :=
  genLoad Var.here 0 fun ρ0 v0 =>
  genLoads (List.range' 1 3) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLetsR gf128Lets.2.rev.reverse 4 env1 fun ρ2 env2 =>
  genStoresIdx gf128Lets.1 (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2

/-! ## 4. Values -/

/-- The word numbered `v` is bound in the let-list `s` and holds `x`. -/
def Gf128Holds (ρ : Nat → BitVec 64) (s : LetSt 64) (v : Nat) (x : BitVec 64) : Prop :=
  v < s.next ∧ s.val 4 ρ v = x

/-- An extension keeps the bound words and their values. -/
theorem Gf128Holds.ext {ρ : Nat → BitVec 64} {s s' : LetSt 64} {v : Nat} {x : BitVec 64}
    (hs : s.Good 4) (hs' : s'.Good 4) (he : s.Ext s') (h : Gf128Holds ρ s v x) :
    Gf128Holds ρ s' v x :=
  ⟨Nat.lt_of_lt_of_le h.1 (he.next_le hs hs'), (he.val_eq hs ρ v h.1).trans h.2⟩

/-- A binding holds the value of its expression. -/
theorem gf128_push_holds (ρ : Nat → BitVec 64) (e : WExp 64) {s : LetSt 64} (hs : s.Good 4) :
    Gf128Holds ρ (s.push e).2 (s.push e).1 (e.eval (s.val 4 ρ)) := by
  refine ⟨by simp [LetSt.push], ?_⟩
  rw [LetSt.push_val e hs]
  simp [LetSt.push]

/-- One symbolic step of the carry-less product evaluates to `gf128ClmulStep`. -/
theorem gf128ClmulStepLets_spec (ρ : Nat → BitVec 64) (a b i : Nat) (A B : BitVec 64)
    (q : (Nat × Nat) × LetSt 64) (p : BitVec 64 × BitVec 64) (hi : i < 64)
    (hs : q.2.Good 4) (ha : Gf128Holds ρ q.2 a A) (hb : Gf128Holds ρ q.2 b B)
    (hlo : Gf128Holds ρ q.2 q.1.1 p.1) (hhi : Gf128Holds ρ q.2 q.1.2 p.2) :
    (gf128ClmulStepLets a b i q).2.Good 4 ∧ q.2.Ext (gf128ClmulStepLets a b i q).2 ∧
      Gf128Holds ρ (gf128ClmulStepLets a b i q).2 (gf128ClmulStepLets a b i q).1.1
        (gf128ClmulStep A B p i).1 ∧
      Gf128Holds ρ (gf128ClmulStepLets a b i q).2 (gf128ClmulStepLets a b i q).1.2
        (gf128ClmulStep A B p i).2 := by
  obtain ⟨⟨lo0, hi0⟩, s0⟩ := q
  simp only at hs ha hb hlo hhi
  have hsm : shiftMask 64 i = i := by simp [shiftMask, Nat.mod_eq_of_lt hi]
  have hso : shiftMask 64 (BitVec.ofNat 64 i).toNat = i := by
    simp only [shiftMask, BitVec.toNat_ofNat, ite_true]
    omega
  have hsh : shiftMask 64 (64 - i) = 64 - i ∨ i = 0 := by
    simp only [shiftMask, ite_true]
    omega
  let em : WExp 64 := .bin .sub (.const 0) (.bin .and (.shr i (.var a)) (.const 1))
  have g1 := LetSt.push_good em hs
  have x1 := LetSt.Ext.push em s0
  have hm := gf128_push_holds ρ em hs
  have hmv : em.eval (s0.val 4 ρ) = 0 - ((A >>> i) &&& 1) := by
    simp [em, WExp.eval, JasminBinOp.apply, ha.2, hsm]
  rw [hmv] at hm
  have ha1 := ha.ext hs g1 x1
  have hb1 := hb.ext hs g1 x1
  have hlo1 := hlo.ext hs g1 x1
  have hhi1 := hhi.ext hs g1 x1
  let elo : WExp 64 := .bin .xor (.var lo0)
    (.bin .and (.bin .shl (.var b) (.const (BitVec.ofNat 64 i))) (.var (s0.push em).1))
  have g2 := LetSt.push_good elo g1
  have x2 := LetSt.Ext.push elo (s0.push em).2
  have hl := gf128_push_holds ρ elo g1
  have hlv : elo.eval ((s0.push em).2.val 4 ρ) =
      p.1 ^^^ ((B <<< i) &&& (0 - ((A >>> i) &&& 1))) := by
    simp [elo, WExp.eval, JasminBinOp.apply, hlo1.2, hb1.2, hm.2, Nat.mod_eq_of_lt hi]
  rw [hlv] at hl
  have hb2 := hb1.ext g1 g2 x2
  have hhi2 := hhi1.ext g1 g2 x2
  have hm2 := hm.ext g1 g2 x2
  unfold gf128ClmulStepLets gf128ClmulStep
  by_cases h0 : i = 0
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    exact ⟨g2, x1.trans x2, hl, hhi2⟩
  · simp only [h0, ↓reduceIte]
    let ehi : WExp 64 := .bin .xor (.var hi0) (.bin .and (.shr (64 - i) (.var b))
      (.var (s0.push em).1))
    have g3 := LetSt.push_good ehi g2
    have x3 := LetSt.Ext.push ehi ((s0.push em).2.push elo).2
    have hh := gf128_push_holds ρ ehi g2
    have hhv : ehi.eval (((s0.push em).2.push elo).2.val 4 ρ) =
        p.2 ^^^ ((B >>> (64 - i)) &&& (0 - ((A >>> i) &&& 1))) := by
      have hs' : shiftMask 64 (64 - i) = 64 - i := hsh.resolve_right h0
      simp [ehi, WExp.eval, JasminBinOp.apply, hhi2.2, hb2.2, hm2.2, hs']
    rw [hhv] at hh
    exact ⟨g3, (x1.trans x2).trans x3, hl.ext g2 g3 x3, hh⟩

/-- The symbolic carry-less product evaluates to `gf128Clmul`. -/
theorem gf128ClmulLets_spec (ρ : Nat → BitVec 64) (z a b : Nat) (A B : BitVec 64)
    (s : LetSt 64) (hs : s.Good 4) (hz : Gf128Holds ρ s z 0) (ha : Gf128Holds ρ s a A)
    (hb : Gf128Holds ρ s b B) :
    (gf128ClmulLets z a b s).2.Good 4 ∧ s.Ext (gf128ClmulLets z a b s).2 ∧
      Gf128Holds ρ (gf128ClmulLets z a b s).2 (gf128ClmulLets z a b s).1.1
        (gf128Clmul A B).1 ∧
      Gf128Holds ρ (gf128ClmulLets z a b s).2 (gf128ClmulLets z a b s).1.2
        (gf128Clmul A B).2 := by
  have key : ∀ n, n ≤ 64 →
      let q := (List.range n).foldl (fun q i => gf128ClmulStepLets a b i q) ((z, z), s)
      let v := (List.range n).foldl (gf128ClmulStep A B) (0, 0)
      q.2.Good 4 ∧ s.Ext q.2 ∧ Gf128Holds ρ q.2 a A ∧ Gf128Holds ρ q.2 b B ∧
        Gf128Holds ρ q.2 q.1.1 v.1 ∧ Gf128Holds ρ q.2 q.1.2 v.2 := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hs, LetSt.Ext.refl s, ha, hb, hz, hz⟩
    | succ n ih =>
        intro hn
        obtain ⟨hg, he, ha', hb', hlo, hhi⟩ := ih (by omega)
        simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        obtain ⟨hg', he', hlo', hhi'⟩ :=
          gf128ClmulStepLets_spec ρ a b n A B _ _ (by omega) hg ha' hb' hlo hhi
        exact ⟨hg', he.trans he', ha'.ext hg hg' he', hb'.ext hg hg' he', hlo', hhi'⟩
  obtain ⟨hg, he, -, -, hlo, hhi⟩ := key 64 le_rfl
  exact ⟨hg, he, hlo, hhi⟩

/-- The symbolic multiply at input words `a0 a1 b0 b1` numbered `0, …, 3`: the stored words are
    the words of `gf128MulWords`. -/
theorem gf128Lets_spec (ρ : Nat → BitVec 64) :
    gf128Lets.2.val 4 ρ (gf128Lets.1.getD 0 (0, 0)).2 =
        (gf128MulWords (ρ 0) (ρ 1) (ρ 2) (ρ 3)).1 ∧
      gf128Lets.2.val 4 ρ (gf128Lets.1.getD 1 (0, 0)).2 =
        (gf128MulWords (ρ 0) (ρ 1) (ρ 2) (ρ 3)).2 := by
  simp only [gf128Lets, List.getD_cons_zero, List.getD_cons_succ]
  have g0 : gf128PrepSt.Good 4 := rfl
  have hin : ∀ j, j < 4 → Gf128Holds ρ gf128PrepSt j (ρ j) := fun j hj =>
    ⟨by simp only [gf128PrepSt]; omega, evalLets_of_lt _ _ _ _ hj⟩
  have hz : Gf128Holds ρ gf128PrepSt 4 0 := ⟨by decide, by
    simp [gf128PrepSt, LetSt.val, evalLets, WExp.eval]⟩
  have hk : Gf128Holds ρ gf128PrepSt 5 0x87 := ⟨by decide, by
    simp [gf128PrepSt, LetSt.val, evalLets, WExp.eval]⟩
  have hx : Gf128Holds ρ gf128PrepSt 6 (ρ 0 ^^^ ρ 1) := ⟨by decide, by
    simp [gf128PrepSt, LetSt.val, evalLets, WExp.eval, JasminBinOp.apply]⟩
  have hy : Gf128Holds ρ gf128PrepSt 7 (ρ 2 ^^^ ρ 3) := ⟨by decide, by
    simp [gf128PrepSt, LetSt.val, evalLets, WExp.eval, JasminBinOp.apply]⟩
  -- the product `a0 b0`
  obtain ⟨gP, xP, hP1, hP2⟩ :=
    gf128ClmulLets_spec ρ 4 0 2 _ _ gf128PrepSt g0 hz (hin 0 (by omega)) (hin 2 (by omega))
  -- the product `a1 b1`
  obtain ⟨gQ, xQ, hQ1, hQ2⟩ := gf128ClmulLets_spec ρ 4 1 3 _ _ _ gP (hz.ext g0 gP xP)
    ((hin 1 (by omega)).ext g0 gP xP) ((hin 3 (by omega)).ext g0 gP xP)
  have xPQ := xP.trans xQ
  -- the product `(a0 ⊕ a1) (b0 ⊕ b1)`
  obtain ⟨gR, xR, hR1, hR2⟩ := gf128ClmulLets_spec ρ 4 6 7 _ _ _ gQ (hz.ext g0 gQ xPQ)
    (hx.ext g0 gQ xPQ) (hy.ext g0 gQ xPQ)
  have xPQR := xPQ.trans xR
  have hP1R := hP1.ext gP gR (xQ.trans xR)
  have hP2R := hP2.ext gP gR (xQ.trans xR)
  have hQ1R := hQ1.ext gQ gR xR
  have hQ2R := hQ2.ext gQ gR xR
  -- the words `l1` and `h0`
  set p := gf128ClmulLets 4 0 2 gf128PrepSt with hp
  set q := gf128ClmulLets 4 1 3 p.2 with hq
  set r := gf128ClmulLets 4 6 7 q.2 with hr
  let el1 : WExp 64 := .bin .xor (.var p.1.2)
    (.bin .xor (.bin .xor (.var r.1.1) (.var p.1.1)) (.var q.1.1))
  have gL := LetSt.push_good el1 gR
  have xL := LetSt.Ext.push el1 r.2
  have hL := gf128_push_holds ρ el1 gR
  have hLv : el1.eval (r.2.val 4 ρ) = (gf128Clmul (ρ 0) (ρ 2)).2 ^^^
      ((gf128Clmul (ρ 0 ^^^ ρ 1) (ρ 2 ^^^ ρ 3)).1 ^^^ (gf128Clmul (ρ 0) (ρ 2)).1 ^^^
        (gf128Clmul (ρ 1) (ρ 3)).1) := by
    simp [el1, WExp.eval, JasminBinOp.apply, hP1R.2, hP2R.2, hQ1R.2, hR1.2]
  rw [hLv] at hL
  set l1 := r.2.push el1 with hl1
  let eh0 : WExp 64 := .bin .xor (.var q.1.1)
    (.bin .xor (.bin .xor (.var r.1.2) (.var p.1.2)) (.var q.1.2))
  have gH := LetSt.push_good eh0 gL
  have xH := LetSt.Ext.push eh0 l1.2
  have hH := gf128_push_holds ρ eh0 gL
  have hHv : eh0.eval (l1.2.val 4 ρ) = (gf128Clmul (ρ 1) (ρ 3)).1 ^^^
      ((gf128Clmul (ρ 0 ^^^ ρ 1) (ρ 2 ^^^ ρ 3)).2 ^^^ (gf128Clmul (ρ 0) (ρ 2)).2 ^^^
        (gf128Clmul (ρ 1) (ρ 3)).2) := by
    simp [eh0, WExp.eval, JasminBinOp.apply, (hP2R.ext gR gL xL).2, (hQ1R.ext gR gL xL).2,
      (hQ2R.ext gR gL xL).2, (hR2.ext gR gL xL).2]
  rw [hHv] at hH
  set h0 := l1.2.push eh0 with hh0
  have xRH := xL.trans xH
  have xH0 := xPQR.trans xRH
  -- the folds
  obtain ⟨gT, xT, hT1, hT2⟩ := gf128ClmulLets_spec ρ 4 h0.1 5 _ _ h0.2 gH
    (hz.ext g0 gH xH0) hH (hk.ext g0 gH xH0)
  obtain ⟨gC, xC, hC1, hC2⟩ := gf128ClmulLets_spec ρ 4 q.1.2 5 _ _ _ gT
    (hz.ext g0 gT (xH0.trans xT)) ((hQ2R.ext gR gH xRH).ext gH gT xT)
    (hk.ext g0 gT (xH0.trans xT))
  obtain ⟨gU, xU, hU1, hU2⟩ := gf128ClmulLets_spec ρ 4 _ 5 _ _ _ gC
    (hz.ext g0 gC ((xH0.trans xT).trans xC)) hC2 (hk.ext g0 gC ((xH0.trans xT).trans xC))
  set t := gf128ClmulLets 4 h0.1 5 h0.2 with ht
  set c := gf128ClmulLets 4 q.1.2 5 t.2 with hc
  set u := gf128ClmulLets 4 c.1.2 5 c.2 with hu
  have xHU := (xT.trans xC).trans xU
  -- the output words
  let eo0 : WExp 64 := .bin .xor (.bin .xor (.var p.1.1) (.var t.1.1)) (.var u.1.1)
  have gO0 := LetSt.push_good eo0 gU
  have xO0 := LetSt.Ext.push eo0 u.2
  have hO0 := gf128_push_holds ρ eo0 gU
  have hO0v : eo0.eval (u.2.val 4 ρ) = (gf128Clmul (ρ 0) (ρ 2)).1 ^^^
      (gf128Clmul ((gf128Clmul (ρ 1) (ρ 3)).1 ^^^ ((gf128Clmul (ρ 0 ^^^ ρ 1) (ρ 2 ^^^ ρ 3)).2 ^^^
        (gf128Clmul (ρ 0) (ρ 2)).2 ^^^ (gf128Clmul (ρ 1) (ρ 3)).2)) 0x87).1 ^^^
      (gf128Clmul (gf128Clmul (gf128Clmul (ρ 1) (ρ 3)).2 0x87).2 0x87).1 := by
    simp [eo0, WExp.eval, JasminBinOp.apply, (hP1R.ext gR gU (xRH.trans xHU)).2,
      (hT1.ext gT gU (xC.trans xU)).2, hU1.2]
  rw [hO0v] at hO0
  let eo1 : WExp 64 := .bin .xor (.bin .xor (.bin .xor (.var l1.1) (.var t.1.2))
    (.var c.1.1)) (.var u.1.2)
  have gO1 := LetSt.push_good eo1 gO0
  have xO1 := LetSt.Ext.push eo1 (u.2.push eo0).2
  have hO1 := gf128_push_holds ρ eo1 gO0
  have hO1v : eo1.eval ((u.2.push eo0).2.val 4 ρ) =
      (gf128MulWords (ρ 0) (ρ 1) (ρ 2) (ρ 3)).2 := by
    simp [eo1, gf128MulWords, WExp.eval, JasminBinOp.apply,
      (hL.ext gL gO0 (((xH.trans xHU)).trans xO0)).2,
      (hT2.ext gT gO0 ((xC.trans xU).trans xO0)).2, (hC1.ext gC gO0 (xU.trans xO0)).2,
      (hU2.ext gU gO0 xO0).2]
  rw [hO1v] at hO1
  have hO0' := hO0.ext gO0 gO1 xO1
  exact ⟨hO0'.2.trans (by simp only [gf128MulWords]), hO1.2⟩

/-- The two words of a 128-bit value: the low word at index `0`, the high word at index
    `1`. -/
def gf128Words (v : BitVec 128) : Fin 2 → BitVec 64 :=
  fun j => (v >>> (64 * j.val)).setWidth 64

/-- **The value of the GF(2^128) template**: at the input array `S` of the words
    `a0 a1 b0 b1` and any contents `O` of the output array, the program returns the two words
    of the product `Gf2Dialect.mulRed (a1 a0) (b1 b0)` in GF(2^128). -/
theorem gf128MulBody_value (S : Fin 4 → BitVec 64) (O : Fin 2 → BitVec 64) :
    gf128MulBody.denote (.cons S (.cons O .nil)) =
      gf128Words (mulRed (S 1 ++ S 0) (S 3 ++ S 2)) := by
  have hA : ∀ i (h : i < 4), stackGet S (BitVec.ofNat 64 i).toNat = S ⟨i, h⟩ := fun i h => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id S ⟨i, h⟩
  have hL1 : gf128Lets.1 = [(0, (gf128Lets.1.getD 0 (0, 0)).2),
      (1, (gf128Lets.1.getD 1 (0, 0)).2)] := by
    simp only [gf128Lets, List.getD_cons_zero, List.getD_cons_succ]
  have hL : ∀ p ∈ gf128Lets.1, p.1 < 2 ^ 64 := by
    rw [hL1]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> decide
  unfold gf128MulBody
  refine genLoad_denote _ 0 _ _ S rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 S (hρ0 _ _) (fun _ => stackGet S (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLetsR_denote _ 4 env1 _ V1 _ henv1 _ fun ρ2 V2 env2 hρ2 henv2 => ?_
  refine (genStoresIdx_denote gf128Lets.1 (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2 V2 O
    ((hρ2 _ _).trans ((hρ1 _ _).trans (hρ0 _ _))) _ henv2 hL).trans ?_
  have hagree : ∀ i (h : i < 4), loadVals S (fun _ => stackGet S (BitVec.ofNat 64 0).toNat) 1
      (List.range' 1 3) i = S ⟨i, h⟩ := by
    intro i hi
    rw [loadVals_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      exact hA 0 (by omega)
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega]
      exact hA i hi
  obtain ⟨h0, h1⟩ := gf128Lets_spec (loadVals S (fun _ => stackGet S (BitVec.ofNat 64 0).toNat) 1
    (List.range' 1 3))
  simp only [LetSt.val] at h0 h1
  rw [hagree 0 (by omega), hagree 1 (by omega), hagree 2 (by omega), hagree 3 (by omega)] at h0 h1
  rw [hL1, mulRed_eq_gf128MulWords]
  funext j
  fin_cases j
  · simpa [stackSet, gf128Words] using h0
  · simpa [stackSet, gf128Words] using h1

/-! ## 5. Events -/

/-- **The events of the GF(2^128) template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem gf128MulBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) :
    LeakFixed (jLeakModel Pj) gf128MulBody := by
  unfold gf128MulBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

end CatCrypt.Crypto.SecureCompilation.HashTemplate
