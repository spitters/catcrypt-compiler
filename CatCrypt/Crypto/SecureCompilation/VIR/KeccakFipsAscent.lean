/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
public import CatCrypt.Crypto.Primitives.Keccak
public import CatCryptCore.Tactics.WordBound

/-!
# The emitted Keccak-p[1600,24] permutation computes the FIPS 202 permutation

`KeccakEmit.keccakF1600Com` is the Keccak-p[1600,24] permutation as a
straight-line `Com jasminDialect` chain of `regArith` bindings (24 rounds of
θ, ρ∘π, χ, ι over a 57-slot stack file, then the 25-lane output staging). This
module ascends that chain to a pure slot-map computation and identifies its
25-lane view with the FIPS 202 round iteration.

## Main results

* `keccakF1600Com_denote_spec` — for every input state `a : Lanes`, the `Com`
  denotation on the canonical input valuation is lane 24 of
  `fipsRounds 24 0 a`, the 24-fold FIPS 202 round transformation with the
  round-constant stream `RC[0..23]`.
* `keccak_emit_state_fips` — the same identity on all 25 lanes.
* `roundM_lanes` — one emitted round is `KeccakDiffuseExact.keccakFullRound`.

## Architecture

A builder state `bs` together with a valuation `V` is described by the pair
`(slotMap bs V, immMap immV V) : SV × IV` — the 57 stack-slot values and the
immediate words. `Respects k f` says the denotation of a continuation `k`
factors through that pair as `f`. The Jasmin dialect denotation is used exactly
once, in `respects_emitOp`: one `regArith` binding is one `Function.update` of
one slot. Every subsequent step is `BitVec`/`Function.update` algebra.

Each emit helper gets a slot-map model (`thetaCColM`, `thetaDColM`,
`rhoPiLaneM`, `chiLaneM`, `iotaM`) and a `Respects` lifting lemma; the models
compose along the emitter's own recursion (`thetaCM`, `thetaDM`, `rhoPiM`,
`chiM`, `roundM`, `roundsM`). Per-stage read lemmas evaluate the 25 state lanes
and the 25 ρ∘π lanes, and §11 identifies each stage with its
`KeccakDiffuseExact` counterpart, whose bit-level agreement with FIPS 202 is
`KeccakDiffuseExact.keccak_round_bitexact`.

`ImmOK ι` records that each immediate input word carries its literal value;
`keccakVal` is the input valuation supplying the state lanes and the literal
table, and `immOK_keccakVal` discharges the hypothesis for it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakFipsAscent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction

/-! ## 1. The slot-map abstraction -/

/-- The 57 stack-slot values of a Keccak builder state. -/
abbrev SV : Type := Fin numSlots → BitVec 64

/-- The immediate words addressed by their `immList` offset. -/
abbrev IV : Type := Nat → BitVec 64

/-- Slot values of the builder state `bs` under valuation `V`. -/
def slotMap {Γ : Ctxt jasminDialect} (bs : BState Γ) (V : Ctxt.Valuation Γ) : SV :=
  fun i => readSlot bs V i

/-- Immediate words of the resolver `immV` under valuation `V`. -/
def immMap {Γ : Ctxt jasminDialect} (immV : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) : IV :=
  fun n => readImm immV V n

/-- Value of a `Src` operand in a slot map / immediate map. -/
def srcVal (σ : SV) (ι : IV) : Src → BitVec 64
  | .st i  => σ i
  | .imm n => ι (immIdx n)

theorem readSrc_eq_srcVal {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) (s : Src) :
    readSrc bs immV V s = srcVal (slotMap bs V) (immMap immV V) s := by
  cases s <;> rfl

theorem slotMap_bsAfterOp {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) (V : Ctxt.Valuation Γ) (v : BitVec 64) :
    slotMap (bsAfterOp bs dst) (V.extend v) = Function.update (slotMap bs V) dst v := by
  funext i
  by_cases h : i = dst
  · subst h
    simp only [slotMap, Function.update_self, readSlot_bsAfterOp_eq]
  · simp only [slotMap, Function.update_of_ne h, readSlot_bsAfterOp_ne _ _ _ _ _ h]

theorem immMap_immVarAfter {Γ : Ctxt jasminDialect}
    (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) (v : BitVec 64) :
    immMap (immVarAfter immV) (V.extend v) = immMap immV V := by
  funext n
  simp only [immMap, readImm_immVarAfter]

/-- `Respects k f`: the denotation of the polymorphic continuation `k` factors
    through the slot map and the immediate map as `f`. -/
def Respects {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧) : Prop :=
  ∀ (Γ : Ctxt jasminDialect) (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ),
    (k bs immV).denote V = f (slotMap bs V) (immMap immV V)

/-- **The one-binding step.** `emitOp` performs a single functional slot update;
    the immediate map is unchanged. This is the only place the Jasmin dialect
    denotation is used. -/
theorem respects_emitOp {t : JasminTy} (op : JasminBinOp) (dst : Fin numSlots)
    (a b : Src) (k : Cont t) (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitOp bs immV op dst a b k)
      (fun σ ι => f (Function.update σ dst (op.apply (srcVal σ ι a) (srcVal σ ι b))) ι) := by
  intro Γ bs immV V
  show (emitOp bs immV op dst a b k).denote V = _
  rw [emitOp_denote, hk, slotMap_bsAfterOp, immMap_immVarAfter,
    readSrc_eq_srcVal, readSrc_eq_srcVal]

/-- `emitMov` copies one slot (`x ||| x = x`). -/
theorem respects_emitMov {t : JasminTy} (dst src : Fin numSlots)
    (k : Cont t) (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitMov bs immV dst src k)
      (fun σ ι => f (Function.update σ dst (σ src)) ι) := by
  have h := respects_emitOp .or dst (.st src) (.st src) k f hk
  intro Γ bs immV V
  have := h Γ bs immV V
  simpa [emitMov, srcVal, or_self_apply] using this

/-- Transport `Respects` along a pointwise equality of models. -/
theorem Respects.congr {t : JasminTy} {k : Cont t} {f g : SV → IV → ⟦t⟧}
    (h : Respects k f) (hfg : ∀ σ ι, f σ ι = g σ ι) : Respects k g := by
  intro Γ bs immV V; rw [h Γ bs immV V, hfg]

/-- Transport `Respects` along an extensional equality of emitters. -/
theorem Respects.of_eq {t : JasminTy} {k k' : Cont t} {f : SV → IV → ⟦t⟧}
    (h : Respects k' f)
    (he : ∀ (Γ : Ctxt jasminDialect) (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64),
      k (Γ' := Γ) bs immV = k' bs immV) : Respects k f := by
  intro Γ bs immV V
  show (k (Γ' := Γ) bs immV).denote V = _
  rw [he Γ bs immV]
  exact h Γ bs immV V

/-! ## 2. Slot arithmetic

`aSlot` occupies `0..24`, `cSlot` `25..29`, `bSlot` `30..54`, `rotScr = 55`,
`chiScr = 56`. All disequalities below are consequences of these ranges. -/

theorem aSlot_val (x y : Nat) : (aSlot x y).val = x % 5 + 5 * (y % 5) := rfl

theorem cSlot_val (x : Nat) : (cSlot x).val = 25 + x % 5 := rfl

theorem bSlot_val (x y : Nat) : (bSlot x y).val = 30 + (x % 5 + 5 * (y % 5)) := by
  show 30 + x % 5 + 5 * (y % 5) = _
  omega

theorem aSlot_lt (x y : Nat) : (aSlot x y).val < 25 := by
  rw [aSlot_val]; word_bound

theorem bSlot_lt (x y : Nat) : (bSlot x y).val < 55 := by
  rw [bSlot_val]; word_bound

theorem cSlot_lt (x : Nat) : (cSlot x).val < 30 := by
  rw [cSlot_val]; word_bound

@[simp] theorem aSlot_ne_cSlot (x y x' : Nat) : aSlot x y ≠ cSlot x' := by
  intro h; have := congrArg Fin.val h
  rw [cSlot_val] at this; have := aSlot_lt x y; omega

@[simp] theorem aSlot_ne_bSlot (x y x' y' : Nat) : aSlot x y ≠ bSlot x' y' := by
  intro h; have := congrArg Fin.val h
  rw [bSlot_val] at this; have := aSlot_lt x y; omega

@[simp] theorem aSlot_ne_rotScr (x y : Nat) : aSlot x y ≠ rotScr := by
  intro h; have := congrArg Fin.val h
  have := aSlot_lt x y; simp only [rotScr] at *; omega

@[simp] theorem aSlot_ne_chiScr (x y : Nat) : aSlot x y ≠ chiScr := by
  intro h; have := congrArg Fin.val h
  have := aSlot_lt x y; simp only [chiScr] at *; omega

@[simp] theorem cSlot_ne_bSlot (x x' y' : Nat) : cSlot x ≠ bSlot x' y' := by
  intro h; have := congrArg Fin.val h
  rw [cSlot_val, bSlot_val] at this
  omega

@[simp] theorem cSlot_ne_rotScr (x : Nat) : cSlot x ≠ rotScr := by
  intro h; have := congrArg Fin.val h
  have := cSlot_lt x; simp only [rotScr] at *; omega

@[simp] theorem cSlot_ne_chiScr (x : Nat) : cSlot x ≠ chiScr := by
  intro h; have := congrArg Fin.val h
  have := cSlot_lt x; simp only [chiScr] at *; omega

@[simp] theorem bSlot_ne_rotScr (x y : Nat) : bSlot x y ≠ rotScr := by
  intro h; have := congrArg Fin.val h
  have := bSlot_lt x y; simp only [rotScr] at *; omega

@[simp] theorem bSlot_ne_chiScr (x y : Nat) : bSlot x y ≠ chiScr := by
  intro h; have := congrArg Fin.val h
  have := bSlot_lt x y; simp only [chiScr] at *; omega

@[simp] theorem rotScr_ne_chiScr : rotScr ≠ chiScr := by decide

/-- Two `aSlot`s coincide exactly when both coordinates agree mod 5. -/
theorem aSlot_eq_iff (x y x' y' : Nat) :
    aSlot x y = aSlot x' y' ↔ (x % 5 = x' % 5 ∧ y % 5 = y' % 5) := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [aSlot_val, aSlot_val] at hv
    omega
  · rintro ⟨h1, h2⟩
    apply Fin.ext; rw [aSlot_val, aSlot_val, h1, h2]

/-- Two `bSlot`s coincide exactly when both coordinates agree mod 5. -/
theorem bSlot_eq_iff (x y x' y' : Nat) :
    bSlot x y = bSlot x' y' ↔ (x % 5 = x' % 5 ∧ y % 5 = y' % 5) := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [bSlot_val, bSlot_val] at hv
    omega
  · rintro ⟨h1, h2⟩
    apply Fin.ext; rw [bSlot_val, bSlot_val, h1, h2]

/-- `cSlot`s coincide exactly when the column agrees mod 5. -/
theorem cSlot_eq_iff (x x' : Nat) : cSlot x = cSlot x' ↔ x % 5 = x' % 5 := by
  constructor
  · intro h; have hv := congrArg Fin.val h; rw [cSlot_val, cSlot_val] at hv; omega
  · intro h; apply Fin.ext; rw [cSlot_val, cSlot_val, h]

/-! ## 3. `emitRotL` -/

/-- Left rotation by `r` as the emitter realizes it: a shift pair combined with
    `|||`, with both shift amounts read from the immediate map, and the identity
    for `r = 0`. -/
def rotModel (a : BitVec 64) (ι : IV) (r : Nat) : BitVec 64 :=
  if r = 0 then a
  else (a <<< (ι (immIdx r)).toNat) ||| (a >>> (ι (immIdx (64 - r))).toNat)

/-- Slot-map model of `emitRotL dst n`: for `n ≠ 0` the scratch slot receives
    `σ dst >>> (64 - n)` and `dst` receives `rotModel (σ dst) ι n`, with both
    shift amounts read from the immediate map. -/
def rotLM (dst : Fin numSlots) (n : Nat) (σ : SV) (ι : IV) : SV :=
  if n = 0 then σ
  else
    Function.update
      (Function.update σ rotScr ((σ dst) >>> (ι (immIdx (64 - n))).toNat))
      dst (((σ dst) <<< (ι (immIdx n)).toNat) ||| ((σ dst) >>> (ι (immIdx (64 - n))).toNat))

theorem respects_emitRotL {t : JasminTy} (dst : Fin numSlots) (n : Nat)
    (k : Cont t) (f : SV → IV → ⟦t⟧) (hk : Respects k f) (hDst : dst ≠ rotScr) :
    Respects (fun bs immV => emitRotL bs immV dst n k)
      (fun σ ι => f (rotLM dst n σ ι) ι) := by
  by_cases hn : n = 0
  · subst hn
    refine Respects.of_eq (k' := k) (hk.congr ?_) ?_
    · intro σ ι; simp [rotLM]
    · intro Γ bs immV; simp [emitRotL]
  · have hbeq : (n == 0) = false := by simp [hn]
    have h3 := respects_emitOp (t := t) .or dst (.st dst) (.st rotScr) k f hk
    have h2 := respects_emitOp (t := t) .shl dst (.st dst) (.imm n) _ _ h3
    have h1 := respects_emitOp (t := t) .shr rotScr (.st dst) (.imm (64 - n)) _ _ h2
    refine Respects.of_eq (h1.congr ?_) ?_
    · intro σ ι
      congr 1
      simp only [srcVal, JasminBinOp.apply, rotLM, if_neg hn,
        Function.update_of_ne hDst, Function.update_self,
        Function.update_of_ne (Ne.symm hDst), Function.update_idem]
    · intro Γ bs immV
      show emitRotL bs immV dst n k = _
      simp only [emitRotL, hbeq, Bool.false_eq_true, if_false]

/-! ### Reading one slot family through an update of another -/

@[simp] theorem upd_cSlot_at_aSlot (σ : SV) (v : BitVec 64) (x' x y : Nat) :
    Function.update σ (cSlot x') v (aSlot x y) = σ (aSlot x y) :=
  Function.update_of_ne (aSlot_ne_cSlot x y x') _ _

@[simp] theorem upd_bSlot_at_aSlot (σ : SV) (v : BitVec 64) (x' y' x y : Nat) :
    Function.update σ (bSlot x' y') v (aSlot x y) = σ (aSlot x y) :=
  Function.update_of_ne (aSlot_ne_bSlot x y x' y') _ _

@[simp] theorem upd_rotScr_at_aSlot (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ rotScr v (aSlot x y) = σ (aSlot x y) :=
  Function.update_of_ne (aSlot_ne_rotScr x y) _ _

@[simp] theorem upd_chiScr_at_aSlot (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ chiScr v (aSlot x y) = σ (aSlot x y) :=
  Function.update_of_ne (aSlot_ne_chiScr x y) _ _

@[simp] theorem upd_aSlot_at_cSlot (σ : SV) (v : BitVec 64) (x' y' x : Nat) :
    Function.update σ (aSlot x' y') v (cSlot x) = σ (cSlot x) :=
  Function.update_of_ne (Ne.symm (aSlot_ne_cSlot x' y' x)) _ _

@[simp] theorem upd_bSlot_at_cSlot (σ : SV) (v : BitVec 64) (x' y' x : Nat) :
    Function.update σ (bSlot x' y') v (cSlot x) = σ (cSlot x) :=
  Function.update_of_ne (cSlot_ne_bSlot x x' y') _ _

@[simp] theorem upd_rotScr_at_cSlot (σ : SV) (v : BitVec 64) (x : Nat) :
    Function.update σ rotScr v (cSlot x) = σ (cSlot x) :=
  Function.update_of_ne (cSlot_ne_rotScr x) _ _

@[simp] theorem upd_chiScr_at_cSlot (σ : SV) (v : BitVec 64) (x : Nat) :
    Function.update σ chiScr v (cSlot x) = σ (cSlot x) :=
  Function.update_of_ne (cSlot_ne_chiScr x) _ _

@[simp] theorem upd_aSlot_at_bSlot (σ : SV) (v : BitVec 64) (x' y' x y : Nat) :
    Function.update σ (aSlot x' y') v (bSlot x y) = σ (bSlot x y) :=
  Function.update_of_ne (Ne.symm (aSlot_ne_bSlot x' y' x y)) _ _

@[simp] theorem upd_cSlot_at_bSlot (σ : SV) (v : BitVec 64) (x' x y : Nat) :
    Function.update σ (cSlot x') v (bSlot x y) = σ (bSlot x y) :=
  Function.update_of_ne (Ne.symm (cSlot_ne_bSlot x' x y)) _ _

@[simp] theorem upd_rotScr_at_bSlot (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ rotScr v (bSlot x y) = σ (bSlot x y) :=
  Function.update_of_ne (bSlot_ne_rotScr x y) _ _

@[simp] theorem upd_chiScr_at_bSlot (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ chiScr v (bSlot x y) = σ (bSlot x y) :=
  Function.update_of_ne (bSlot_ne_chiScr x y) _ _

@[simp] theorem upd_aSlot_at_rotScr (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ (aSlot x y) v rotScr = σ rotScr :=
  Function.update_of_ne (Ne.symm (aSlot_ne_rotScr x y)) _ _

@[simp] theorem upd_cSlot_at_rotScr (σ : SV) (v : BitVec 64) (x : Nat) :
    Function.update σ (cSlot x) v rotScr = σ rotScr :=
  Function.update_of_ne (Ne.symm (cSlot_ne_rotScr x)) _ _

@[simp] theorem upd_bSlot_at_rotScr (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ (bSlot x y) v rotScr = σ rotScr :=
  Function.update_of_ne (Ne.symm (bSlot_ne_rotScr x y)) _ _

@[simp] theorem upd_chiScr_at_rotScr (σ : SV) (v : BitVec 64) :
    Function.update σ chiScr v rotScr = σ rotScr :=
  Function.update_of_ne rotScr_ne_chiScr _ _

@[simp] theorem upd_aSlot_at_chiScr (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ (aSlot x y) v chiScr = σ chiScr :=
  Function.update_of_ne (Ne.symm (aSlot_ne_chiScr x y)) _ _

@[simp] theorem upd_cSlot_at_chiScr (σ : SV) (v : BitVec 64) (x : Nat) :
    Function.update σ (cSlot x) v chiScr = σ chiScr :=
  Function.update_of_ne (Ne.symm (cSlot_ne_chiScr x)) _ _

@[simp] theorem upd_bSlot_at_chiScr (σ : SV) (v : BitVec 64) (x y : Nat) :
    Function.update σ (bSlot x y) v chiScr = σ chiScr :=
  Function.update_of_ne (Ne.symm (bSlot_ne_chiScr x y)) _ _

@[simp] theorem upd_rotScr_at_chiScr (σ : SV) (v : BitVec 64) :
    Function.update σ rotScr v chiScr = σ chiScr :=
  Function.update_of_ne (Ne.symm rotScr_ne_chiScr) _ _

@[simp] theorem upd_aSlot_at_aSlot (σ : SV) (v : BitVec 64) (x' y' x y : Nat) :
    Function.update σ (aSlot x' y') v (aSlot x y)
      = if x % 5 = x' % 5 ∧ y % 5 = y' % 5 then v else σ (aSlot x y) := by
  rw [Function.update_apply]
  by_cases h : x % 5 = x' % 5 ∧ y % 5 = y' % 5
  · rw [if_pos ((aSlot_eq_iff x y x' y').2 h), if_pos h]
  · rw [if_neg (fun hc => h ((aSlot_eq_iff x y x' y').1 hc)), if_neg h]

@[simp] theorem upd_bSlot_at_bSlot (σ : SV) (v : BitVec 64) (x' y' x y : Nat) :
    Function.update σ (bSlot x' y') v (bSlot x y)
      = if x % 5 = x' % 5 ∧ y % 5 = y' % 5 then v else σ (bSlot x y) := by
  rw [Function.update_apply]
  by_cases h : x % 5 = x' % 5 ∧ y % 5 = y' % 5
  · rw [if_pos ((bSlot_eq_iff x y x' y').2 h), if_pos h]
  · rw [if_neg (fun hc => h ((bSlot_eq_iff x y x' y').1 hc)), if_neg h]

@[simp] theorem upd_cSlot_at_cSlot (σ : SV) (v : BitVec 64) (x' x : Nat) :
    Function.update σ (cSlot x') v (cSlot x)
      = if x % 5 = x' % 5 then v else σ (cSlot x) := by
  rw [Function.update_apply]
  by_cases h : x % 5 = x' % 5
  · rw [if_pos ((cSlot_eq_iff x x').2 h), if_pos h]
  · rw [if_neg (fun hc => h ((cSlot_eq_iff x x').1 hc)), if_neg h]

/-! ## 4. θ: the column parities and the column fold -/

/-- The column parity `C[x] = A[x,0] ⊕ … ⊕ A[x,4]` in the slot map. -/
def parityM (σ : SV) (x : Nat) : BitVec 64 :=
  σ (aSlot x 0) ^^^ σ (aSlot x 1) ^^^ σ (aSlot x 2) ^^^ σ (aSlot x 3) ^^^ σ (aSlot x 4)

/-- Slot-map model of `emitThetaCCol x`: one write of `C[x]` into `cSlot x`. -/
def thetaCColM (x : Nat) (σ : SV) : SV := Function.update σ (cSlot x) (parityM σ x)

theorem respects_emitThetaCCol {t : JasminTy} (x : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitThetaCCol bs immV x k)
      (fun σ ι => f (thetaCColM x σ) ι) := by
  have h4 := respects_emitOp (t := t) .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 4)) k f hk
  have h3 := respects_emitOp (t := t) .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 3)) _ _ h4
  have h2 := respects_emitOp (t := t) .xor (cSlot x) (.st (cSlot x)) (.st (aSlot x 2)) _ _ h3
  have h1 := respects_emitOp (t := t) .xor (cSlot x) (.st (aSlot x 0)) (.st (aSlot x 1)) _ _ h2
  refine Respects.of_eq (h1.congr ?_) (fun Γ bs immV => rfl)
  intro σ ι
  congr 1
  simp only [srcVal, JasminBinOp.apply, thetaCColM, parityM,
    Function.update_self, Function.update_idem, upd_cSlot_at_aSlot]

/-- Slot-map model of `emitTheta_C count start`. -/
def thetaCM : Nat → Nat → SV → SV
  | 0, _, σ => σ
  | (m + 1), s, σ => thetaCM m (s + 1) (thetaCColM s σ)

theorem respects_emitTheta_C {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitTheta_C count start bs immV k)
        (fun σ ι => f (thetaCM count start σ) ι)
  | 0, s => by
      refine Respects.of_eq (hk.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl
  | (m + 1), s => by
      have ih := respects_emitTheta_C k f hk m (s + 1)
      have h := respects_emitThetaCCol (t := t) s _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl

/-! ## 5. θ: the per-column fold `A[x,y] ⊕= D[x]` -/

/-- The θ word `D[x] = rotl(C[x+1], 1) ⊕ C[x-1]` in the slot map, with both
    shift amounts read from the immediate map. -/
def thetaDW (σ : SV) (ι : IV) (x : Nat) : BitVec 64 :=
  rotModel (σ (cSlot (x + 1))) ι 1 ^^^ σ (cSlot (x + 4))

/-- Slot-map model of `emitThetaDCol x`: the rotate scratch and the χ scratch
    receive the two halves of `D[x]`, and the five lanes of column `x` are folded
    with `D[x]`. -/
def thetaDColM (x : Nat) (σ : SV) (ι : IV) : SV :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update
      (Function.update σ rotScr ((σ (cSlot (x + 1))) >>> (ι (immIdx 63)).toNat))
        chiScr (thetaDW σ ι x))
      (aSlot x 0) (σ (aSlot x 0) ^^^ thetaDW σ ι x))
      (aSlot x 1) (σ (aSlot x 1) ^^^ thetaDW σ ι x))
      (aSlot x 2) (σ (aSlot x 2) ^^^ thetaDW σ ι x))
      (aSlot x 3) (σ (aSlot x 3) ^^^ thetaDW σ ι x))
      (aSlot x 4) (σ (aSlot x 4) ^^^ thetaDW σ ι x)

theorem respects_emitThetaDCol {t : JasminTy} (x : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitThetaDCol bs immV x k)
      (fun σ ι => f (thetaDColM x σ ι) ι) := by
  have h8 := respects_emitOp (t := t) .xor (aSlot x 4) (.st (aSlot x 4)) (.st chiScr) k f hk
  have h7 := respects_emitOp (t := t) .xor (aSlot x 3) (.st (aSlot x 3)) (.st chiScr) _ _ h8
  have h6 := respects_emitOp (t := t) .xor (aSlot x 2) (.st (aSlot x 2)) (.st chiScr) _ _ h7
  have h5 := respects_emitOp (t := t) .xor (aSlot x 1) (.st (aSlot x 1)) (.st chiScr) _ _ h6
  have h4 := respects_emitOp (t := t) .xor (aSlot x 0) (.st (aSlot x 0)) (.st chiScr) _ _ h5
  have h3 := respects_emitOp (t := t) .xor chiScr (.st chiScr) (.st (cSlot (x + 4))) _ _ h4
  have h2 := respects_emitRotL (t := t) chiScr 1 _ _ h3 (Ne.symm rotScr_ne_chiScr)
  have h1 := respects_emitMov (t := t) chiScr (cSlot (x + 1)) _ _ h2
  refine Respects.of_eq (h1.congr ?_) (fun Γ bs immV => rfl)
  intro σ ι
  congr 1
  simp [srcVal, JasminBinOp.apply, rotLM, rotModel, thetaDColM, thetaDW,
    Function.update_idem, Function.update_comm (Ne.symm rotScr_ne_chiScr)]

/-- Slot-map model of `emitTheta_D count start`. -/
def thetaDM : Nat → Nat → SV → IV → SV
  | 0, _, σ, _ => σ
  | (m + 1), s, σ, ι => thetaDM m (s + 1) (thetaDColM s σ ι) ι

theorem respects_emitTheta_D {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitTheta_D count start bs immV k)
        (fun σ ι => f (thetaDM count start σ ι) ι)
  | 0, _ => by
      refine Respects.of_eq (hk.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl
  | (m + 1), s => by
      have ih := respects_emitTheta_D k f hk m (s + 1)
      have h := respects_emitThetaDCol (t := t) s _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl

/-! ## 6. ρ ∘ π -/

/-- Slot-map model of `emitRhoPiLane x y`: lane `A[x,y]` is rotated by its ρ
    offset into the π destination `B[y, 2x+3y]`. -/
def rhoPiLaneM (x y : Nat) (σ : SV) (ι : IV) : SV :=
  if rhoOffset (x + 5 * y) = 0 then
    Function.update σ (bSlot y (2 * x + 3 * y))
      (rotModel (σ (aSlot x y)) ι (rhoOffset (x + 5 * y)))
  else
    Function.update
      (Function.update σ rotScr
        ((σ (aSlot x y)) >>> (ι (immIdx (64 - rhoOffset (x + 5 * y)))).toNat))
      (bSlot y (2 * x + 3 * y))
      (rotModel (σ (aSlot x y)) ι (rhoOffset (x + 5 * y)))

theorem respects_emitRhoPiLane {t : JasminTy} (x y : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitRhoPiLane bs immV x y k)
      (fun σ ι => f (rhoPiLaneM x y σ ι) ι) := by
  have h2 := respects_emitRotL (t := t) (bSlot y (2 * x + 3 * y))
    (rhoOffset (x + 5 * y)) k f hk (bSlot_ne_rotScr _ _)
  have h1 := respects_emitMov (t := t) (bSlot y (2 * x + 3 * y)) (aSlot x y) _ _ h2
  refine Respects.of_eq (h1.congr ?_) (fun Γ bs immV => rfl)
  intro σ ι
  congr 1
  by_cases hr : rhoOffset (x + 5 * y) = 0
  · simp [rotLM, rhoPiLaneM, rotModel, hr]
  · simp only [rotLM, rhoPiLaneM, rotModel, if_neg hr, Function.update_self,
      Function.update_comm (bSlot_ne_rotScr y (2 * x + 3 * y)), Function.update_idem]

/-- Slot-map model of `emitRhoPi count start`. -/
def rhoPiM : Nat → Nat → SV → IV → SV
  | 0, _, σ, _ => σ
  | (m + 1), s, σ, ι => rhoPiM m (s + 1) (rhoPiLaneM (s % 5) (s / 5) σ ι) ι

theorem respects_emitRhoPi {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitRhoPi count start bs immV k)
        (fun σ ι => f (rhoPiM count start σ ι) ι)
  | 0, _ => by
      refine Respects.of_eq (hk.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl
  | (m + 1), s => by
      have ih := respects_emitRhoPi k f hk m (s + 1)
      have h := respects_emitRhoPiLane (t := t) (s % 5) (s / 5) _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl

/-! ## 7. χ and ι -/

/-- Slot-map model of `emitChiLane x y`: the χ scratch holds
    `(¬B[x+1,y]) ∧ B[x+2,y]` (with `¬` as XOR against the all-ones immediate) and
    lane `A[x,y]` becomes `B[x,y]` XOR that. -/
def chiLaneM (x y : Nat) (σ : SV) (ι : IV) : SV :=
  Function.update
    (Function.update σ chiScr
      (((σ (bSlot (x + 1) y)) ^^^ ι (immIdx maskImm)) &&& (σ (bSlot (x + 2) y))))
    (aSlot x y)
    ((σ (bSlot x y)) ^^^
      (((σ (bSlot (x + 1) y)) ^^^ ι (immIdx maskImm)) &&& (σ (bSlot (x + 2) y))))

theorem respects_emitChiLane {t : JasminTy} (x y : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitChiLane bs immV x y k)
      (fun σ ι => f (chiLaneM x y σ ι) ι) := by
  have h4 := respects_emitOp (t := t) .xor (aSlot x y) (.st (bSlot x y)) (.st chiScr) k f hk
  have h3 := respects_emitOp (t := t) .and chiScr (.st chiScr) (.st (bSlot (x + 2) y)) _ _ h4
  have h2 := respects_emitOp (t := t) .xor chiScr (.st chiScr) (.imm maskImm) _ _ h3
  have h1 := respects_emitMov (t := t) chiScr (bSlot (x + 1) y) _ _ h2
  refine Respects.of_eq (h1.congr ?_) (fun Γ bs immV => rfl)
  intro σ ι
  congr 1
  simp only [srcVal, JasminBinOp.apply, chiLaneM, Function.update_self,
    Function.update_idem, upd_chiScr_at_bSlot]

/-- Slot-map model of `emitChi count start`. -/
def chiM : Nat → Nat → SV → IV → SV
  | 0, _, σ, _ => σ
  | (m + 1), s, σ, ι => chiM m (s + 1) (chiLaneM (s % 5) (s / 5) σ ι) ι

theorem respects_emitChi {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitChi count start bs immV k)
        (fun σ ι => f (chiM count start σ ι) ι)
  | 0, _ => by
      refine Respects.of_eq (hk.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl
  | (m + 1), s => by
      have ih := respects_emitChi k f hk m (s + 1)
      have h := respects_emitChiLane (t := t) (s % 5) (s / 5) _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl

/-- Slot-map model of `emitIota round`: XOR the round constant into `A[0,0]`. -/
def iotaM (round : Nat) (σ : SV) (ι : IV) : SV :=
  Function.update σ (aSlot 0 0) (σ (aSlot 0 0) ^^^ ι (immIdx (roundConst round)))

theorem respects_emitIota {t : JasminTy} (round : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitIota bs immV round k)
      (fun σ ι => f (iotaM round σ ι) ι) := by
  have h := respects_emitOp (t := t) .xor (aSlot 0 0) (.st (aSlot 0 0))
    (.imm (roundConst round)) k f hk
  exact Respects.of_eq (h.congr (fun σ ι => rfl)) (fun Γ bs immV => rfl)

/-! ## 8. One round, the round loop, and the output staging -/

/-- Slot-map model of `emitRound round`. -/
def roundM (round : Nat) (σ : SV) (ι : IV) : SV :=
  iotaM round (chiM 25 0 (rhoPiM 25 0 (thetaDM 5 0 (thetaCM 5 0 σ) ι) ι) ι) ι

theorem respects_emitRound {t : JasminTy} (round : Nat) (k : Cont t)
    (f : SV → IV → ⟦t⟧) (hk : Respects k f) :
    Respects (fun bs immV => emitRound bs immV round k)
      (fun σ ι => f (roundM round σ ι) ι) := by
  have h5 := respects_emitIota (t := t) round k f hk
  have h4 := respects_emitChi (t := t) _ _ h5 25 0
  have h3 := respects_emitRhoPi (t := t) _ _ h4 25 0
  have h2 := respects_emitTheta_D (t := t) _ _ h3 5 0
  have h1 := respects_emitTheta_C (t := t) _ _ h2 5 0
  exact Respects.of_eq (h1.congr (fun σ ι => rfl)) (fun Γ bs immV => rfl)

/-- Slot-map model of `emitRounds count start`. -/
def roundsM : Nat → Nat → SV → IV → SV
  | 0, _, σ, _ => σ
  | (m + 1), s, σ, ι => roundsM m (s + 1) (roundM s σ ι) ι

theorem respects_emitRounds {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitRounds count start bs immV k)
        (fun σ ι => f (roundsM count start σ ι) ι)
  | 0, _ => by
      refine Respects.of_eq (hk.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl
  | (m + 1), s => by
      have ih := respects_emitRounds k f hk m (s + 1)
      have h := respects_emitRound (t := t) s _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rfl

/-- The output staging is a sequence of idempotent moves, so it leaves the slot
    map unchanged. -/
theorem respects_emitOutStage {t : JasminTy} (k : Cont t) (f : SV → IV → ⟦t⟧)
    (hk : Respects k f) :
    ∀ (count start : Nat),
      Respects (fun bs immV => emitOutStage count start bs immV k) f
  | 0, _ => by exact Respects.of_eq hk (fun Γ bs immV => rfl)
  | (m + 1), s => by
      have ih := respects_emitOutStage k f hk m (s + 1)
      have h := respects_emitMov (t := t)
        ⟨s % numSlots, by word_bound⟩ ⟨s % numSlots, by word_bound⟩ _ _ ih
      refine Respects.of_eq (h.congr ?_) (fun Γ bs immV => rfl)
      intro σ ι; rw [Function.update_eq_self]

/-! ## 9. Immediate words

The emitted program addresses each literal it needs as an input word. `ImmOK ι`
says every such word carries its literal value. -/

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact in
/-- Every immediate slot of `immList` holds its literal value. -/
def ImmOK (ι : IV) : Prop := ∀ n ∈ immList, ι (immIdx n) = BitVec.ofNat 64 n

theorem ImmOK.toNat_of {ι : IV} (h : ImmOK ι) {n : Nat} (hn : n ∈ immList)
    (hlt : n < 64) : (ι (immIdx n)).toNat = n := by
  rw [h n hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem ImmOK.mask {ι : IV} (h : ImmOK ι) :
    ι (immIdx maskImm) = BitVec.allOnes 64 := by
  rw [h maskImm (by decide)]; decide

theorem ImmOK.rc {ι : IV} (h : ImmOK ι) (round : Nat) (hr : round < 24) :
    ι (immIdx (roundConst round)) = BitVec.ofNat 64 (roundConst round) := by
  refine h _ ?_
  interval_cases round <;> decide

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact in
/-- `rotModel` at a ρ offset is the closed-form left rotation `crotl`. -/
theorem rotModel_rho {ι : IV} (h : ImmOK ι) (a : BitVec 64) (s : Nat) (hs : s < 25) :
    rotModel a ι (rhoOffset s) = crotl a (rhoOffset s) := by
  have key : ∀ r : Nat, r < 64 → r ≠ 0 → r ∈ immList → 64 - r ∈ immList →
      rotModel a ι r = crotl a r := by
    intro r hr hr0 hm1 hm2
    rw [rotModel, if_neg hr0, crotl, h.toNat_of hm1 hr,
      h.toNat_of hm2 (by omega)]
  interval_cases s
  · show rotModel a ι 0 = crotl a 0
    rw [rotModel, if_pos rfl, crotl]
    bv_decide
  all_goals (apply key <;> decide)

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact in
/-- The θ rotation by one is the closed-form left rotation. -/
theorem rotModel_one {ι : IV} (h : ImmOK ι) (a : BitVec 64) :
    rotModel a ι 1 = crotl a 1 := rotModel_rho h a 1 (by decide)

/-! ## 10. Reading the stage models -/

theorem thetaCM5 (σ : SV) :
    thetaCM 5 0 σ = thetaCColM 4 (thetaCColM 3 (thetaCColM 2 (thetaCColM 1 (thetaCColM 0 σ)))) :=
  rfl

@[simp] theorem thetaCM5_aSlot (σ : SV) (x y : Nat) :
    thetaCM 5 0 σ (aSlot x y) = σ (aSlot x y) := by
  simp [thetaCM5, thetaCColM]

@[simp] theorem thetaCM5_bSlot (σ : SV) (x y : Nat) :
    thetaCM 5 0 σ (bSlot x y) = σ (bSlot x y) := by
  simp [thetaCM5, thetaCColM]

theorem thetaCM5_cSlot_lt (σ : SV) (z : Nat) (hz : z < 5) :
    thetaCM 5 0 σ (cSlot z) = parityM σ z := by
  interval_cases z <;> simp [thetaCM5, thetaCColM, parityM]

theorem cSlot_mod (x : Nat) : cSlot x = cSlot (x % 5) := by
  apply Fin.ext; rw [cSlot_val, cSlot_val, Nat.mod_mod]

theorem bSlot_mod (x y : Nat) : bSlot x y = bSlot (x % 5) (y % 5) := by
  apply Fin.ext; rw [bSlot_val, bSlot_val, Nat.mod_mod, Nat.mod_mod]

@[simp] theorem thetaCM5_cSlot (σ : SV) (x : Nat) :
    thetaCM 5 0 σ (cSlot x) = parityM σ (x % 5) := by
  rw [cSlot_mod]
  exact thetaCM5_cSlot_lt σ (x % 5) (by word_bound)

theorem thetaDM5 (σ : SV) (ι : IV) :
    thetaDM 5 0 σ ι
      = thetaDColM 4 (thetaDColM 3 (thetaDColM 2 (thetaDColM 1 (thetaDColM 0 σ ι) ι) ι) ι) ι :=
  rfl

theorem thetaDM5_aSlot (σ : SV) (ι : IV) (x y : Nat) (hx : x < 5) (hy : y < 5) :
    thetaDM 5 0 σ ι (aSlot x y) = σ (aSlot x y) ^^^ thetaDW σ ι x := by
  interval_cases x <;> interval_cases y <;>
    (rw [thetaDM5]
     simp only [↓thetaDColM, thetaDW, ↓Function.update_self, ↓upd_aSlot_at_aSlot,
       ↓upd_chiScr_at_aSlot, ↓upd_rotScr_at_aSlot, ↓upd_aSlot_at_cSlot, ↓upd_chiScr_at_cSlot,
       ↓upd_rotScr_at_cSlot, Nat.reduceMod, Nat.reduceAdd, Nat.reduceEqDiff, and_false,
       and_true, ↓reduceIte])

theorem thetaDM5_bSlot (σ : SV) (ι : IV) (x y : Nat) :
    thetaDM 5 0 σ ι (bSlot x y) = σ (bSlot x y) := by
  simp [thetaDM5, thetaDColM]

theorem rhoPiM25 (σ : SV) (ι : IV) :
    rhoPiM 25 0 σ ι
      = rhoPiLaneM 4 4 (rhoPiLaneM 3 4 (rhoPiLaneM 2 4 (rhoPiLaneM 1 4 (rhoPiLaneM 0 4
        (rhoPiLaneM 4 3 (rhoPiLaneM 3 3 (rhoPiLaneM 2 3 (rhoPiLaneM 1 3 (rhoPiLaneM 0 3
        (rhoPiLaneM 4 2 (rhoPiLaneM 3 2 (rhoPiLaneM 2 2 (rhoPiLaneM 1 2 (rhoPiLaneM 0 2
        (rhoPiLaneM 4 1 (rhoPiLaneM 3 1 (rhoPiLaneM 2 1 (rhoPiLaneM 1 1 (rhoPiLaneM 0 1
        (rhoPiLaneM 4 0 (rhoPiLaneM 3 0 (rhoPiLaneM 2 0 (rhoPiLaneM 1 0 (rhoPiLaneM 0 0 σ ι)
          ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι :=
  rfl

/-- Among the 25 lanes, only lane `0` has ρ offset zero. -/
theorem rhoOffset_eq_zero_iff (s : Nat) (hs : s < 25) : rhoOffset s = 0 ↔ s = 0 := by
  interval_cases s <;> decide

theorem rhoPiM25_aSlot (σ : SV) (ι : IV) (x y : Nat) :
    rhoPiM 25 0 σ ι (aSlot x y) = σ (aSlot x y) := by
  simp [rhoPiM25, rhoPiLaneM, rhoOffset_eq_zero_iff]

theorem rhoPiM25_bSlot (σ : SV) (ι : IV) (x y : Nat) (hx : x < 5) (hy : y < 5) :
    rhoPiM 25 0 σ ι (bSlot x y)
      = rotModel (σ (aSlot ((x + 3 * y) % 5) x)) ι
          (rhoOffset ((x + 3 * y) % 5 + 5 * x)) := by
  interval_cases x <;> interval_cases y <;>
    (rw [rhoPiM25]
     simp only [↓rhoPiLaneM, rhoOffset_eq_zero_iff, ↓Function.update_self,
       ↓upd_bSlot_at_bSlot, ↓upd_rotScr_at_bSlot, ↓upd_bSlot_at_aSlot, ↓upd_rotScr_at_aSlot,
       Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceEqDiff, Nat.reduceLT, and_false,
       and_true, ↓reduceIte])

theorem chiM25 (σ : SV) (ι : IV) :
    chiM 25 0 σ ι
      = chiLaneM 4 4 (chiLaneM 3 4 (chiLaneM 2 4 (chiLaneM 1 4 (chiLaneM 0 4
        (chiLaneM 4 3 (chiLaneM 3 3 (chiLaneM 2 3 (chiLaneM 1 3 (chiLaneM 0 3
        (chiLaneM 4 2 (chiLaneM 3 2 (chiLaneM 2 2 (chiLaneM 1 2 (chiLaneM 0 2
        (chiLaneM 4 1 (chiLaneM 3 1 (chiLaneM 2 1 (chiLaneM 1 1 (chiLaneM 0 1
        (chiLaneM 4 0 (chiLaneM 3 0 (chiLaneM 2 0 (chiLaneM 1 0 (chiLaneM 0 0 σ ι)
          ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι) ι :=
  rfl

theorem chiM25_aSlot (σ : SV) (ι : IV) (x y : Nat) (hx : x < 5) (hy : y < 5) :
    chiM 25 0 σ ι (aSlot x y)
      = (σ (bSlot x y)) ^^^
          (((σ (bSlot (x + 1) y)) ^^^ ι (immIdx maskImm)) &&& (σ (bSlot (x + 2) y))) := by
  interval_cases x <;> interval_cases y <;>
    (rw [chiM25]
     simp only [↓chiLaneM, ↓Function.update_self, ↓upd_aSlot_at_aSlot, ↓upd_chiScr_at_aSlot,
       ↓upd_aSlot_at_bSlot, ↓upd_chiScr_at_bSlot, Nat.reduceMod, Nat.reduceAdd,
       Nat.reduceEqDiff, and_false, and_true, ↓reduceIte])

/-! ## 11. The lane view and the FIPS 202 round -/

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact

/-- The 25 state lanes read out of a slot map. -/
def lanesOf (σ : SV) : Lanes := fun i => σ (aSlot (i.val % 5) (i.val / 5))

/-- The 25 ρ∘π lanes read out of a slot map. -/
def bLanesOf (σ : SV) : Lanes := fun i => σ (bSlot (i.val % 5) (i.val / 5))

theorem lanesOf_laneIdx (σ : SV) (x y : Nat) (hx : x < 5) (hy : y < 5) :
    lanesOf σ (laneIdx x y) = σ (aSlot x y) := by
  interval_cases x <;> interval_cases y <;> rfl

theorem bLanesOf_laneIdx (σ : SV) (x y : Nat) (hx : x < 5) (hy : y < 5) :
    bLanesOf σ (laneIdx x y) = σ (bSlot x y) := by
  interval_cases x <;> interval_cases y <;> rfl

theorem laneIdx_val (a b : Nat) (h : a + 5 * b < 25) : (laneIdx a b).val = a + 5 * b := by
  simp [laneIdx, h]

theorem bSlot_mod_left (x y : Nat) : bSlot (x % 5) y = bSlot x y := by
  apply Fin.ext; rw [bSlot_val, bSlot_val, Nat.mod_mod]

theorem parityM_eq (σ : SV) (x : Nat) (hx : x < 5) :
    parityM σ x = cThetaC (lanesOf σ) x := by
  unfold parityM cThetaC
  rw [lanesOf_laneIdx σ x 0 hx (by norm_num), lanesOf_laneIdx σ x 1 hx (by norm_num),
    lanesOf_laneIdx σ x 2 hx (by norm_num), lanesOf_laneIdx σ x 3 hx (by norm_num),
    lanesOf_laneIdx σ x 4 hx (by norm_num)]

theorem thetaDW_eq (σ : SV) (ι : IV) (h : ImmOK ι) (x : Nat) :
    thetaDW (thetaCM 5 0 σ) ι x = cThetaD (lanesOf σ) x := by
  rw [thetaDW, thetaCM5_cSlot, thetaCM5_cSlot, rotModel_one h,
    parityM_eq σ _ (Nat.mod_lt _ (by decide)), parityM_eq σ _ (Nat.mod_lt _ (by decide)),
    cThetaD]
  exact BitVec.xor_comm _ _

theorem lanes_theta (σ : SV) (ι : IV) (h : ImmOK ι) :
    lanesOf (thetaDM 5 0 (thetaCM 5 0 σ) ι) = cThetaClean (lanesOf σ) := by
  funext i
  have hx : i.val % 5 < 5 := by word_bound
  have hy : i.val / 5 < 5 := by word_bound
  show thetaDM 5 0 (thetaCM 5 0 σ) ι (aSlot (i.val % 5) (i.val / 5)) = _
  rw [thetaDM5_aSlot _ _ _ _ hx hy, thetaCM5_aSlot, thetaDW_eq σ ι h]
  rfl

theorem lanes_rhopi (τ : SV) (ι : IV) (h : ImmOK ι) :
    bLanesOf (rhoPiM 25 0 τ ι) = cPi (cRho (lanesOf τ)) := by
  funext i
  have hx : i.val % 5 < 5 := by word_bound
  have hy : i.val / 5 < 5 := by word_bound
  have hm : (i.val % 5 + 3 * (i.val / 5)) % 5 < 5 := by word_bound
  have hlt : (i.val % 5 + 3 * (i.val / 5)) % 5 + 5 * (i.val % 5) < 25 := by omega
  show rhoPiM 25 0 τ ι (bSlot (i.val % 5) (i.val / 5)) = _
  rw [rhoPiM25_bSlot _ _ _ _ hx hy, rotModel_rho h _ _ hlt]
  show _ = cRho (lanesOf τ) (laneIdx ((i.val % 5 + 3 * (i.val / 5)) % 5) (i.val % 5))
  rw [cRho, lanesOf_laneIdx _ _ _ hm hx, rhoAmt, laneIdx_val _ _ hlt]

theorem lanes_chi (β : SV) (ι : IV) (h : ImmOK ι) :
    lanesOf (chiM 25 0 β ι) = cChi (bLanesOf β) := by
  funext i
  have hx : i.val % 5 < 5 := by word_bound
  have hy : i.val / 5 < 5 := by word_bound
  have h1 : (i.val % 5 + 1) % 5 < 5 := by word_bound
  have h2 : (i.val % 5 + 2) % 5 < 5 := by word_bound
  show chiM 25 0 β ι (aSlot (i.val % 5) (i.val / 5)) = _
  rw [chiM25_aSlot _ _ _ _ hx hy, h.mask]
  show _ = cchi (bLanesOf β (laneIdx (i.val % 5) (i.val / 5)))
      (bLanesOf β (laneIdx ((i.val % 5 + 1) % 5) (i.val / 5)))
      (bLanesOf β (laneIdx ((i.val % 5 + 2) % 5) (i.val / 5)))
  rw [bLanesOf_laneIdx _ _ _ hx hy, bLanesOf_laneIdx _ _ _ h1 hy,
    bLanesOf_laneIdx _ _ _ h2 hy, cchi,
    bSlot_mod_left (i.val % 5 + 1) (i.val / 5),
    bSlot_mod_left (i.val % 5 + 2) (i.val / 5)]

theorem lanes_iota (γ : SV) (ι : IV) (h : ImmOK ι) (round : Nat) (hr : round < 24) :
    lanesOf (iotaM round γ ι)
      = iotaApply (lanesOf γ) (BitVec.ofNat 64 (roundConst round)) := by
  funext i
  show iotaM round γ ι (aSlot (i.val % 5) (i.val / 5)) = _
  rw [iotaM, h.rc round hr]
  fin_cases i <;> simp [iotaApply, lanesOf]

/-- **One emitted round denotes the FIPS 202 round.** The slot-map model of
    `emitRound round` acts on the 25 lanes as the FIPS 202 Keccak-p round
    transformation with round constant `RC[round]`. -/
theorem roundM_lanes (σ : SV) (ι : IV) (h : ImmOK ι) (round : Nat) (hr : round < 24) :
    lanesOf (roundM round σ ι)
      = keccakFullRound (lanesOf σ) (BitVec.ofNat 64 (roundConst round)) := by
  rw [roundM, lanes_iota _ _ h round hr, lanes_chi _ _ h, lanes_rhopi _ _ h,
    lanes_theta _ _ h]
  rw [← keccakClosedForm, ← keccakClosedFullRound, keccak_round_bitexact]

/-! ## 12. The 24-round permutation -/

/-- The FIPS 202 round transformation iterated over rounds `start … start+count-1`. -/
def fipsRounds : Nat → Nat → Lanes → Lanes
  | 0, _, s => s
  | (m + 1), r, s => fipsRounds m (r + 1) (keccakFullRound s (BitVec.ofNat 64 (roundConst r)))

theorem roundsM_lanes (ι : IV) (h : ImmOK ι) :
    ∀ (count start : Nat), start + count ≤ 24 → ∀ (σ : SV),
      lanesOf (roundsM count start σ ι) = fipsRounds count start (lanesOf σ)
  | 0, _, _, _ => rfl
  | (m + 1), s, hle, σ => by
      have hs : s < 24 := by omega
      have ih := roundsM_lanes ι h m (s + 1) (by omega) (roundM s σ ι)
      show lanesOf (roundsM m (s + 1) (roundM s σ ι) ι) = _
      rw [ih, roundM_lanes σ ι h s hs]
      rfl

/-! ## 13. The emitted permutation -/

theorem respects_ret (j : Fin numSlots) :
    Respects (t := r64) (fun bs _ => .ret (bs.st j)) (fun σ _ => σ j) := by
  intro Γ bs immV V; rfl

/-- The `Com` denotation of the emitted permutation is the 24-fold slot-map
    model applied to the input slot map, read at lane 24. -/
theorem keccakF1600Com_denote_eq (V : Ctxt.Valuation inCtxt) :
    keccakF1600Com.denote V
      = roundsM 24 0 (slotMap initBState V) (immMap initImmVar V) ⟨24, by decide⟩ := by
  have h0 := respects_ret ⟨24, by decide⟩
  have h1 := respects_emitOutStage _ _ h0 25 0
  have h2 := respects_emitRounds _ _ h1 24 0
  exact h2 inCtxt initBState initImmVar V

/-- **The emitted Keccak-p[1600,24] permutation computes the FIPS 202
    permutation.** On the 25 lanes, the slot-map model of the emitted
    `Com jasminDialect` program is the 24-fold iteration of the FIPS 202 round
    transformation with the round-constant stream `RC[0..23]`. -/
theorem keccak_emit_lanes_fips (V : Ctxt.Valuation inCtxt)
    (h : ImmOK (immMap initImmVar V)) :
    lanesOf (roundsM 24 0 (slotMap initBState V) (immMap initImmVar V))
      = fipsRounds 24 0 (lanesOf (slotMap initBState V)) :=
  roundsM_lanes _ h 24 0 (by norm_num) _

/-- The denoted result word of the emitted permutation is lane 24 of the FIPS 202
    permutation of the input state. -/
theorem keccakF1600Com_denote_fips (V : Ctxt.Valuation inCtxt)
    (h : ImmOK (immMap initImmVar V)) :
    keccakF1600Com.denote V
      = fipsRounds 24 0 (lanesOf (slotMap initBState V)) ⟨24, by decide⟩ := by
  rw [keccakF1600Com_denote_eq]
  have := congrFun (keccak_emit_lanes_fips V h) ⟨24, by decide⟩
  rw [← this]
  rfl

/-! ## 14. The canonical input valuation

The emitted program takes the 25 state lanes and the literal table `immList` as
input words. `keccakVal` is the valuation that supplies exactly those, and
discharges the `ImmOK` precondition. -/

theorem getD_idxOf : ∀ (l : List Nat) (a : Nat), a ∈ l → l.getD (l.idxOf a) 0 = a
  | [], _, h => by simp at h
  | (b :: t), a, h => by
      by_cases hb : b = a
      · subst hb; simp
      · have ht : a ∈ t := by
          rcases List.mem_cons.1 h with h1 | h1
          · exact absurd h1.symm hb
          · exact h1
        have hidx : (b :: t).idxOf a = t.idxOf a + 1 := by
          have hbe : (b == a) = false := by simp [hb]
          rw [List.idxOf_cons, hbe]
          rfl
        rw [hidx, List.getD_cons_succ]
        exact getD_idxOf t a ht

/-- A valuation of a `replicate n r64` context built from a positional word
    function. -/
def mkVal (g : Nat → BitVec 64) :
    (n : Nat) → @Ctxt.Valuation jasminDialect _ (List.replicate n r64)
  | 0 => .nil
  | (n + 1) => .cons (g 0) (mkVal (fun j => g (j + 1)) n)

theorem inputVar_lookup_mkVal (g : Nat → BitVec 64) :
    ∀ (m i : Nat), i ≤ m → (inputVar m i).lookup (mkVal g (m + 1)) = g i
  | _, 0, _ => by unfold inputVar mkVal Ctxt.Var.lookup; rfl
  | 0, (_ + 1), h => by omega
  | (m + 1), (i + 1), h => by
      unfold inputVar mkVal Ctxt.Var.lookup
      exact inputVar_lookup_mkVal (fun j => g (j + 1)) m i (by omega)

/-- Input words for the state `a`: lanes `0..24`, zeroed scratch seeds, then the
    literal table. -/
def keccakWords (a : Lanes) : Nat → BitVec 64 := fun i =>
  if h : i < 25 then a ⟨i, h⟩
  else if i < numSlots then 0
  else BitVec.ofNat 64 (immList.getD (i - firstImm) 0)

/-- The input valuation carrying the state `a` and the literal table. -/
def keccakVal (a : Lanes) : Ctxt.Valuation inCtxt := mkVal (keccakWords a) nInputs

theorem inVar_keccakVal (a : Lanes) (i : Nat) (h : i < nInputs) :
    (inVar i).lookup (keccakVal a) = keccakWords a i :=
  inputVar_lookup_mkVal (keccakWords a) (nInputs - 1) i (by omega)

theorem immOK_keccakVal (a : Lanes) : ImmOK (immMap initImmVar (keccakVal a)) := by
  intro n hn
  have hidx : immList.idxOf n < immList.length := List.idxOf_lt_length_of_mem hn
  have hlt : firstImm + immIdx n < nInputs := by
    show 57 + immList.idxOf n < 57 + immList.length
    omega
  show (inVar (firstImm + immIdx n)).lookup (keccakVal a) = _
  rw [inVar_keccakVal a _ hlt, keccakWords]
  have h1 : ¬ (firstImm + immIdx n < 25) := by
    show ¬ (57 + immList.idxOf n < 25); omega
  have h2 : ¬ (firstImm + immIdx n < numSlots) := by
    show ¬ (57 + immList.idxOf n < 57); omega
  rw [dif_neg h1, if_neg h2, Nat.add_sub_cancel_left]
  rw [show immList.getD (immIdx n) 0 = n from getD_idxOf immList n hn]

theorem lanesOf_keccakVal (a : Lanes) :
    lanesOf (slotMap initBState (keccakVal a)) = a := by
  funext i
  have hi := i.isLt
  have hval : (aSlot (i.val % 5) (i.val / 5)).val = i.val := by
    rw [aSlot_val]; omega
  have hj : (aSlot (i.val % 5) (i.val / 5)).val < 25 := by rw [hval]; exact hi
  show (initBState.st (aSlot (i.val % 5) (i.val / 5))).lookup (keccakVal a) = a i
  rw [show initBState.st (aSlot (i.val % 5) (i.val / 5))
        = inVar (aSlot (i.val % 5) (i.val / 5)).val from by simp only [initBState, if_pos hj]]
  rw [hval, inVar_keccakVal a i.val (by show i.val < 57 + immList.length; omega),
    keccakWords, dif_pos hi]

/-- **The emitted Keccak-p[1600,24] permutation computes FIPS 202.** For every
    input state `a`, the denotation of the emitted `Com jasminDialect` program on
    the canonical input valuation is lane 24 of the 24-fold FIPS 202 round
    iteration of `a`. -/
theorem keccakF1600Com_denote_spec (a : Lanes) :
    keccakF1600Com.denote (keccakVal a) = fipsRounds 24 0 a ⟨24, by decide⟩ := by
  rw [keccakF1600Com_denote_fips _ (immOK_keccakVal a), lanesOf_keccakVal]

/-- The full 25-lane form: the slot-map model of the emitted program, read on the
    state lanes, is the FIPS 202 permutation of the input state. -/
theorem keccak_emit_state_fips (a : Lanes) :
    lanesOf (roundsM 24 0 (slotMap initBState (keccakVal a))
      (immMap initImmVar (keccakVal a))) = fipsRounds 24 0 a := by
  rw [keccak_emit_lanes_fips _ (immOK_keccakVal a), lanesOf_keccakVal]

/-! ## 15. The reference FIPS 202 permutation

`CatCrypt.Crypto.Primitives.Keccak` states FIPS 202 on the 5×5 lane matrix
`KState`. Transporting the 25-lane view along `toKState` identifies the round
iteration of §12 with `Primitives.Keccak.keccakF`. -/

open CatCrypt.Crypto.Primitives.Keccak in
/-- The 5×5 view of the 25 lanes: `toKState l x y = l ⟨x + 5y⟩`. -/
def toKState (l : Lanes) : KState :=
  fun x y => l ⟨x.val + 5 * y.val, by word_bound⟩

open CatCrypt.Crypto.Primitives.Keccak in
/-- The flat ρ offset table agrees with the 5×5 one. -/
theorem rhoOffset_eq_rotOffset (x y : Fin 5) :
    rhoOffset (x.val + 5 * y.val) = rotOffset x y := by
  fin_cases x <;> fin_cases y <;> simp [rhoOffset, rotOffset, rotData]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The emitted round-constant immediates are the FIPS 202 round constants. -/
theorem roundConst_eq (r : Nat) (hr : r < 24) :
    BitVec.ofNat 64 (roundConst r) = roundConstant r := by
  interval_cases r <;> simp [roundConst, roundConstant, rcData]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The θ step of §11 transports to the reference θ. -/
theorem toKState_theta (l : Lanes) :
    toKState (fTheta l) = theta (toKState l) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [toKState, fTheta, fThetaD, fThetaC, frotl, laneIdx,
      Primitives.Keccak.theta]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The ρ step of §11 transports to the reference ρ. -/
theorem toKState_rho (l : Lanes) :
    toKState (fRho l) = rho (toKState l) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [toKState, fRho, frotl, rhoAmt, rhoOffset, Primitives.Keccak.rho,
      rotOffset, rotData]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The π step of §11 transports to the reference π. -/
theorem toKState_pi (l : Lanes) :
    toKState (fPi l) = Primitives.Keccak.pi (toKState l) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [toKState, fPi, cPi, laneIdx, Primitives.Keccak.pi]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The χ step of §11 transports to the reference χ. -/
theorem toKState_chi (l : Lanes) :
    toKState (fChi l) = Primitives.Keccak.chi (toKState l) := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [toKState, fChi, fchi, laneIdx, Primitives.Keccak.chi]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The ι step of §11 transports to the reference ι. -/
theorem toKState_iota (l : Lanes) (rc : BitVec 64) :
    toKState (iotaApply l rc) = Primitives.Keccak.iota (toKState l) rc := by
  funext x y
  fin_cases x <;> fin_cases y <;>
    simp [toKState, iotaApply, Primitives.Keccak.iota]

open CatCrypt.Crypto.Primitives.Keccak in
/-- The round transformation of §11 transports to the reference round. -/
theorem toKState_round (l : Lanes) (rc : BitVec 64) :
    toKState (keccakFullRound l rc) = keccakRound (toKState l) rc := by
  simp only [keccakFullRound, keccakFipsRound, Primitives.Keccak.keccakRound,
    toKState_iota, toKState_chi, toKState_pi, toKState_rho, toKState_theta]

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakFipsAscent
