/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSBreak
public import HaxAscent.Ascent.Encode
public import HaxLean.RuntimeM

/-!
# The `--emit-monadic` text against the `toRustMSB` reading

haxpipeT's `--emit-monadic` prints a function `f` that reaches a Rust panic as a definition in
`RustM` over the guarded operations of `HaxLean/RuntimeM.lean`, beside the `ImpExpr` literal
`f_impExpr` of its body. `ReadsAs m r` relates the printed computation `m` to the reading
`r = toRustMSB appRt f_impExpr ρ`: every outcome the reading returns is a value of `m` whose
encoding is the encoding of the outcome. The reading's values are words of a width and
arrays of words; the printed function computes on `Int` and `Array Int`; the two meet in
`Hax.Value` through `AVal.toValue` and `HaxEnc.enc`.

The tactic `emit_reading` proves `ReadsAs (f args) (toRustMSB appRt f_impExpr ρ)` for a
printed function by running the reading forwards: it unfolds `toRustMSB` construct by construct
on the literal, splits each bind of the reading at the value it returns, and replaces each call
of `appRt` by the guarded operation of the printed text through the lemmas `rd_*`, one per
head. A counted loop is matched by `foldRangeM_go_of_loopBS` against an invariant relating
the printed accumulator to the reading's environment.

## Main definitions

* `ReadsAs`: the relation between a printed computation and the reading.
* `AOp.emitM`: the guarded operation printed for a checked unsigned operation.
* `emit_reading`: the tactic.

## Main results

* `rd_checked`, `rd_index`, `rd_len`, `rd_cmp`: a value of `appRt` at a head is a value of the
  guarded operation the printer writes for that head.
* `foldRangeM_go_of_loopBS`: the loop square between `loopBS` and `Hax.foldRangeM.go`.
-/

@[expose] public section

set_option autoImplicit false

namespace HaxAscent.RustSemantics

open CatCrypt CatCrypt.Hax CatCrypt.Hax.RustSemantics Aeneas.Std
open _root_.Hax.Ascent (HaxEnc)

/-! ## The relation -/

/-- Every outcome `o` and environment `ρ'` the reading `r` returns come with a value `a` of
    the printed computation `m` whose encoding is the encoding of `o`. -/
def ReadsAs {α : Type} [HaxEnc α] (m : RustM α) (r : RustM (BOut × AEnv)) : Prop :=
  ∀ o ρ', r = .ok (o, ρ') → ∃ a, m = .ok a ∧ o.toValue = HaxEnc.enc a

/-- A reading that fails is read as any printed computation. -/
theorem ReadsAs.of_fail {α : Type} [HaxEnc α] (m : RustM α) (e : Error) :
    ReadsAs m (.fail e) := by
  intro o ρ' h
  cases h

/-! ## The heads -/

/-- The guarded operation `--emit-monadic` prints for a checked unsigned operation at width
    `w`. -/
def AOp.emitM (w : Nat) : AOp → Int → Int → RustM Int
  | .add => _root_.Hax.addM_w w
  | .sub => _root_.Hax.subM_w w
  | .mul => _root_.Hax.mulM_w w
  | .div => _root_.Hax.divM_w w
  | .rem => _root_.Hax.remM_w w

section Heads

variable {a b r : AVal} {x y : Int}

/-- Where the checked operation of Rust `u<w>` returns a value, the printed guarded operation
    returns the same value. -/
theorem emitM_of_checkedRt {w : Nat} {o : AOp} {x y : Int} {v : _root_.Hax.Value}
    (h : AOp.checkedRt w o x y = some v) :
    ∃ z : Int, AOp.emitM w o x y = .ok z ∧ v = HaxEnc.enc z := by
  cases o <;> simp only [AOp.checkedRt, _root_.Hax.uintAddOp, _root_.Hax.uintSubOp,
    _root_.Hax.uintMulOp, _root_.Hax.uintDivOp, _root_.Hax.uintRemOp] at h <;>
    split at h <;> (try cases h) <;>
    refine ⟨_, ?_, rfl⟩ <;>
    simp only [AOp.emitM, _root_.Hax.addM_w, _root_.Hax.subM_w, _root_.Hax.mulM_w,
      _root_.Hax.divM_w, _root_.Hax.remM_w] <;>
    rw [ite_eq_left (by
      first | grind | exact ⟨Int.mul_nonneg (by grind) (by grind), by grind⟩)] <;> rfl

/-- A checked width-tagged `Add#w`, `Sub#w` or `Mul#w`: a value of `appRt` is the value of the
    guarded operation `Hax.addM_w`, `Hax.subM_w` or `Hax.mulM_w` at the width of the tag. -/
theorem rd_checked {f : String} {ty : UScalarTy} {o : AOp} (hf : checkedAt? f = some (ty, o))
    (hw : wordOpAt? f = none) (h : appRt f [a, b] = .ok r)
    (ha : a.toValue = HaxEnc.enc x) (hb : b.toValue = HaxEnc.enc y) :
    ∃ z : Int, AOp.emitM ty.numBits o x y = .ok z ∧ r.toValue = HaxEnc.enc z := by
  simp only [appRt, hw, hf] at h
  obtain ⟨x', y', hx, hy, hr⟩ := appChecked_ok hf h
  rw [hx] at ha
  rw [hy] at hb
  cases ha
  cases hb
  obtain ⟨z, hz, hv⟩ := emitM_of_checkedRt hr
  exact ⟨z, hz, hv⟩

/-- A value whose encoding is the integer `x` stands for `x`. -/
theorem AVal.toInt?_of_toValue {v : AVal} (h : v.toValue = HaxEnc.enc x) :
    v.toInt? = some x := by
  cases v <;> simp_all [AVal.toValue, AVal.toInt?]

/-- The unfolding of `AVal.toInt?` at an integer literal. -/
theorem AVal.toInt?_int (n : Int) : (AVal.int n).toInt? = some n := rfl

/-- `appRt` reads a name that is no other two-argument operation by `appBool2`. -/
theorem appRt_two_bool {f : String} (h1 : wordOpAt? f = none) (h2 : checkedAt? f = none)
    (h3 : AOp.ofName f = none) (h4 : (f == "index") = false) (h5 : (f == "repeat") = false)
    (h6 : (f == "array_lit") = false) (h7 : _root_.Hax.FieldTag.fieldTag? f = none) :
    appRt f [a, b] = appBool2 f a b := by
  simp_all [appRt]

/-- A comparison `Lt`, `Le`, `Gt`, `Ge`, `Eq` or `Ne` of two integers: a value of `appRt` is the
    Boolean of the comparison the printer writes. -/
theorem rd_cmp {f : String} {g : Int → Int → Bool} (hc : cmpRt? f = some g)
    (hr : appRt f [a, b] = appBool2 f a b) (h : appRt f [a, b] = .ok r)
    (ha : a.toValue = HaxEnc.enc x) (hb : b.toValue = HaxEnc.enc y) :
    ∃ c : Bool, r = .bool c ∧ g x y = c := by
  rw [hr] at h
  have hx := AVal.toInt?_of_toValue ha
  have hy := AVal.toInt?_of_toValue hb
  unfold appBool2 at h
  split at h
  · simp [AVal.toInt?] at hx
  · simp only [hc, hx, hy] at h
    cases h
    exact ⟨_, rfl, rfl⟩

/-- `len` of an array: a value of `appRt` is `Hax.array_len` of the printed array. -/
theorem rd_len {A : Array Int} (h : appRt "len" [a] = .ok r) (ha : a.toValue = HaxEnc.enc A) :
    r.toValue = HaxEnc.enc (_root_.Hax.array_len A) := by
  simp [appRt, tagTyAt?, uTys, uTag] at h
  cases a <;> simp only [appLen, reduceCtorEq] at h
  cases h
  have hl := congrArg List.length (_root_.Hax.Value.array.inj ha)
  simp only [List.length_map, Array.length_toList] at hl
  simp [AVal.toValue, _root_.Hax.array_len, hl]

/-- `index` of an array: a value of `appRt` is the value of `Hax.indexM` on the printed array
    and index. -/
theorem rd_index {A : Array Int} {I : Int} (h : appRt "index" [a, b] = .ok r)
    (ha : a.toValue = HaxEnc.enc A) (hb : b.toValue = HaxEnc.enc I) :
    ∃ z : Int, _root_.Hax.indexM A I = .ok z ∧ r.toValue = HaxEnc.enc z := by
  simp [appRt, wordOpAt?, checkedAt?, AOp.ofName, tagTyAt?, uTys, WordOp.ofName, uTag] at h
  cases a with
  | arr ty n arr =>
    simp only [appIndex] at h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    cases h
    have hI : I = enc j := by
      rw [AVal.asW_ok hj] at hb
      exact (_root_.Hax.Value.int.inj hb).symm
    have hA : A.toList = arr.val.map (fun x => (x.val : Int)) := by
      have h1 : A.toList.map _root_.Hax.Value.int =
          (arr.val.map (fun x => (x.val : Int))).map _root_.Hax.Value.int := by
        rw [List.map_map]
        exact (_root_.Hax.Value.array.inj ha).symm
      exact (List.map_inj_right (fun _ _ h => _root_.Hax.Value.int.inj h)).mp h1
    unfold Aeneas.Std.Array.index_usize at hx
    rw [Aeneas.Std.Array.getElem?_Usize_eq] at hx
    split at hx
    · cases hx
    · rename_i y hy
      cases hx
      obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hy
      have hsz : A.size = arr.val.length := by
        rw [← Array.length_toList, hA, List.length_map]
      subst hI
      refine ⟨(x.val : Int), ?_, rfl⟩
      have hg : 0 ≤ enc j ∧ enc j < (A.size : Int) := by
        simp only [enc_uscalar, UScalar.val, hsz]
        grind
      rw [_root_.Hax.indexM, ite_eq_left hg]
      have ht : (enc j).toNat = j.val := by grind [enc_uscalar]
      have hlt' : (enc j).toNat < A.size := by omega
      show RustM.ok _ = _
      simp only [_root_.Hax.index, hlt', ↓reduceDIte]
      congr 1
      rw [← Array.getElem_toList]
      simp [hA, hget]
  | _ => simp [appIndex] at h

end Heads

/-! ## Counted loops -/

/-- **The loop square of the printed fold.** If each step of the reading from an environment
    related to the accumulator `s` by `R i` returns no break and comes with a value `s'` of the
    printed body related to the environment it ends in by `R (i + 1)`, then a run of `k` steps
    of `loopBS` returns no break and comes with the value of `k` trips of `Hax.foldRangeM`. -/
theorem foldRangeM_go_of_loopBS {σ : Type} (N : Nat) (R : Nat → σ → AEnv → Prop)
    {step : Nat → AEnv → RustM (Option AVal × AEnv)} {body : Int → σ → RustM σ}
    (hstep : ∀ i s ρ o ρ', i < N → R i s ρ → step i ρ = .ok (o, ρ') →
      o = none ∧ ∃ s', body i s = .ok s' ∧ R (i + 1) s' ρ') :
    ∀ (k i : Nat) (s : σ) (ρ : AEnv) (o : Option AVal) (ρ' : AEnv), i + k ≤ N →
      R i s ρ → loopBS step k i ρ = .ok (o, ρ') →
      o = none ∧ ∃ s', _root_.Hax.foldRangeM.go body k (i : Int) s = .ok s' ∧ R (i + k) s' ρ'
  | 0, i, s, ρ, o, ρ', _, hR, h => by
    cases h
    exact ⟨rfl, s, rfl, hR⟩
  | k + 1, i, s, ρ, o, ρ', hk, hR, h => by
    obtain ⟨⟨o1, ρ1⟩, h1, h2⟩ := rustM_bind_ok h
    obtain ⟨rfl, s1, hb, hR1⟩ := hstep i s ρ o1 ρ1 (by omega) hR h1
    obtain ⟨ho, s2, hg, hR2⟩ :=
      foldRangeM_go_of_loopBS N R hstep k (i + 1) s1 ρ1 o ρ' (by omega) hR1 h2
    refine ⟨ho, s2, ?_, by rwa [show i + (k + 1) = i + 1 + k by omega]⟩
    simp only [_root_.Hax.foldRangeM.go, hb, bind_tc_ok]
    exact_mod_cast hg

/-! ## The tactic -/

/-- `emit_reading [f, f_impExpr]` proves `ReadsAs (f args) (toRustMSB appRt f_impExpr ρ)` for
    a function printed by `--emit-monadic`, where `ρ` binds each parameter `p` to a value
    `v_p` with a hypothesis `v_p.toValue = HaxEnc.enc p`. It unfolds the reading on the literal,
    splits each bind of the reading at the value its call returns, replaces the call by the
    guarded operation of the printed text (`rd_checked`, `rd_index`, `rd_len`, `rd_cmp`), splits
    a conditional at the Boolean of its comparison, and closes each branch at the returned
    value. -/
macro "emit_reading" " [" ids:ident,* "]" : tactic => do
  let ls : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ids.getElems.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
  `(tactic| (
  intro o ρ' h
  simp only [$ls,*, toRustMSB, toRustMSB.argsSB, AEnv.upd] at h ⊢
  simp [AEnv.upd] at h
  repeat (first
    | (cases h; first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl, by assumption⟩)
    | (obtain ⟨ho, -⟩ := h
       subst ho
       first | exact ⟨_, rfl, rfl⟩ | exact ⟨_, rfl, by assumption⟩)
    | (have hb := rustM_bind_ok h
       obtain ⟨r, h1, h⟩ := hb
       first
        | (have hk := rd_checked (by rfl) (by rfl) h1
              (by first | assumption | rfl) (by first | assumption | rfl)
           obtain ⟨z, hz, hr⟩ := hk
           simp only [AOp.emitM, UScalarTy.numBits] at hz
           try simp only [hz, bind_tc_ok])
        | (have hk := rd_index h1
              (by first | assumption | rfl) (by first | assumption | rfl)
           obtain ⟨z, hz, hr⟩ := hk
           try simp only [hz, bind_tc_ok])
        | (have hr := rd_len h1 (by first | assumption | rfl))
        | (have hk := rd_cmp (by rfl)
              (appRt_two_bool (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) h1
              (by first | assumption | rfl) (by first | assumption | rfl)
           obtain ⟨c, hrc, hc⟩ := hk
           subst hrc
           cases c <;> simp only [hc, ↓reduceIte, Bool.false_eq_true] at h ⊢ <;>
             try simp [AEnv.upd] at h)))))

end HaxAscent.RustSemantics
