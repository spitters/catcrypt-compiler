/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOpsSim
public import CatCrypt.Crypto.Hax.HaxRuntimeWordBuiltins
public import HaxAscent.Ascent.Corres
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote

/-!
# The runtime loop of the word-operation front, and `mpn_mul_1`

The hax semantics `denote` gives the post-pipeline constructor `forFold` no
meaning; the control-flow-aware semantics `denote'` runs it as `denoteForLoop'`.
This module lifts the straight-line simulation of `HaxToLowCTWordOpsSim` to
`denote'` and to the runtime loop: `N` trips of a hax body against the `N`-trip
`semRForD` fold of its lowering, the fold `semScalar` gives the bounded loop and
to which the runtime loop `RForRuntime` delegates at the trip count read from
its bound.

It then instantiates the loop at the `mpn_mul_1` body as `fuseMulHiIdiom`,
`aNormalizeTotal`, `haxToLowCT`, `scalarizeWordOps` and `typeWordArrays` leave
it, computes the words one trip writes, and identifies the value the hax
program returns with the denotation of the compiled runtime-trip loop
`mul1RtProgOpt` through the word-model fold `mul1Fold`.

## Main definitions

* `mul1Pre`, `mul1St1`, `mul1St2`, `mul1BodyHax`, `mul1BodyLow`, `mul1ProgHax` —
  the `mpn_mul_1` body and program, hax and lowered.
* `mul1Next`, `mul1Trips` — the hax environment after one and after `n` trips.

## Main results

* `forLoop_sim`, `forFold_sim` — the loop simulation from a per-trip simulation.
* `mul1_front_prog` — the lowered and retyped `mul1ProgHax`.
* `mul1_trip`, `mul1_loop_sim` — one trip and the loop of `mpn_mul_1`.
* `mul1Next_rp`, `mul1Trips_val` — the words the trips write into `rp`.
* `mul1BodyLow_fold` — the `semScalar` fold of the lowered body computes
  `mul1Fold`.
* `mul1_hax_eq_compiled` — the hax `mpn_mul_1` returns the cells and the carry
  of the compiled loop's denotation.
* `mul1_hax_eq_compiled_runtime` — the same at hax-lean's `u64` table
  `Hax.hax64Builtins`.
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section
set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WordOpsSim

open _root_.Hax (ImpExpr ImpLit Value Env Builtins denote' denoteForLoop')
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (SEnvScalar semScalar semRForD isTmpName)

/-! ### The bindings in the control-flow-aware semantics -/

/-- One binding runs in `denote'` to its continuation in `b.next env`. -/
theorem WBind.run' {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat) {env : Env}
    {σ : SEnvScalar} {S : List String} {A : List (String × Nat)} (h : EnvRelW env σ S A)
    (b : WBind) (hok : b.Ok S A env) (k : ImpExpr) :
    denote' bi fuel (b.hax k) env = denote' bi fuel k (b.next env) := by
  cases b with
  | word x f a b =>
    obtain ⟨hf, ha, hb, -, -, -, -, r, hr, hlt⟩ := hok
    obtain ⟨haL, haE, -⟩ := (h.word a ha).natOf_eq
    obtain ⟨hbL, hbE, -⟩ := (h.word b hb).natOf_eq
    simp only [WBind.hax, WBind.next, hr, Option.getD_some]
    exact _root_.Hax.Ascent.denote'_letBind bi fuel
      (_root_.Hax.Ascent.denote'_app bi fuel
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel haE)
          rfl (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
            (_root_.Hax.Ascent.denote'_var bi fuel hbE) rfl
            (_root_.Hax.Ascent.denoteArgs'_nil bi fuel env)))
        (hbi.word f hf _ _ _ haL hbL hr hlt)) rfl
  | lit x n =>
    exact _root_.Hax.Ascent.denote'_letBind bi fuel
      (_root_.Hax.Ascent.denote'_lit bi fuel _ env) rfl
  | load x arr i t ta =>
    obtain ⟨hi, -, -, n, hA, hin⟩ := hok
    obtain ⟨vs, a, he, -, -, hc⟩ := h.arr _ hA
    obtain ⟨-, hiE, -⟩ := (h.word i hi).natOf_eq
    have hcell := hc _ hin
    have harr : arrOf env arr = vs := by simp [arrOf, he]
    simp only [WBind.hax, WBind.next, harr, hcell, Option.getD_some]
    exact _root_.Hax.Ascent.denote'_letBind bi fuel
      (_root_.Hax.Ascent.denote'_app bi fuel
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel he)
          rfl (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
            (_root_.Hax.Ascent.denote'_var bi fuel hiE) rfl
            (_root_.Hax.Ascent.denoteArgs'_nil bi fuel env)))
        (hbi.index vs _ _ hcell)) rfl
  | store arr i v ta tv =>
    obtain ⟨hi, hv, n, hA, -, hin⟩ := hok
    obtain ⟨vs, a, he, -, hl, -⟩ := h.arr _ hA
    obtain ⟨-, hiE, -⟩ := (h.word i hi).natOf_eq
    obtain ⟨-, hvE, -⟩ := (h.word v hv).natOf_eq
    have harr : arrOf env arr = vs := by simp [arrOf, he]
    simp only [WBind.hax, WBind.next, harr]
    exact _root_.Hax.Ascent.denote'_letBind bi fuel
      (_root_.Hax.Ascent.denote'_app bi fuel
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel he)
          rfl (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
            (_root_.Hax.Ascent.denote'_var bi fuel hiE) rfl
            (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
              (_root_.Hax.Ascent.denote'_var bi fuel hvE) rfl
              (_root_.Hax.Ascent.denoteArgs'_nil bi fuel env))))
        (hbi.update vs _ _ (by omega))) rfl

/-- A sequence of bindings whose side conditions hold runs in `denote'` to its
    continuation in `bindsNext bs env`. -/
theorem bindsHax_run' {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat)
    (A : List (String × Nat)) :
    ∀ (bs : List WBind) (S : List String) (env : Env) (σ : SEnvScalar),
      EnvRelW env σ S A → BindsOk A bs S env → ∀ k : ImpExpr,
      denote' bi fuel (bindsHax bs k) env = denote' bi fuel k (bindsNext bs env)
  | [], _, _, _, _, _, _ => rfl
  | b :: bs, S, env, σ, h, hok, k => by
    obtain ⟨-, σ₁, -, h₁⟩ := b.sim hbi 0 h hok.1 (bindsHax bs k) .RSkip
    rw [bindsHax, b.run' hbi fuel h hok.1]
    exact bindsHax_run' hbi fuel A bs _ _ σ₁ h₁ hok.2 k

/-- **Segment in `denote'`.** A sequence of bindings ending in a name bound after
    it to a value that is no control-flow value, followed by `()`, runs to its
    continuation in `bindsNext bs env`. -/
theorem segment_run' {bi : Builtins} (hbi : WordBuiltins' bi) (fuel : Nat)
    {A : List (String × Nat)} {bs : List WBind} {S : List String} {env : Env}
    {σ : SEnvScalar} (h : EnvRelW env σ S A) (hok : BindsOk A bs S env) {y : String}
    {v : Value} (hy : bindsNext bs env y = some v) (hv : v.isControlFlow = false)
    (k : ImpExpr) :
    denote' bi fuel (.seq (.seq (bindsHax bs (.var y)) .unitVal) k) env =
      denote' bi fuel k (bindsNext bs env) := by
  have h1 : denote' bi fuel (bindsHax bs (.var y)) env = (.val v, bindsNext bs env) := by
    rw [bindsHax_run' hbi fuel A bs S env σ h hok]
    exact _root_.Hax.Ascent.denote'_var bi fuel hy
  have h2 : denote' bi fuel (.seq (bindsHax bs (.var y)) .unitVal) env =
      (.val .unit, bindsNext bs env) := by
    rw [_root_.Hax.Ascent.denote'_seq bi fuel h1 hv]
    exact _root_.Hax.Ascent.denote'_unitVal bi fuel _
  exact _root_.Hax.Ascent.denote'_seq bi fuel h2 rfl

/-! ### The runtime loop -/

/-- **Loop simulation.** When every trip `j < N` of the hax body `bh` from an
    environment extended by `x ↦ j` returns `()` in `env'`, and the `semScalar`
    run of `bl` from the scalar environment with `x` bound to the word `j`
    succeeds in `σ'`, preserving the invariant `Inv`, then after `n ≤ N` trips the
    hax loop has run `n` trips of `denoteForLoop'` and the `semRForD` fold of
    `bl` has run `n` trips, and the invariant holds at `n`. -/
theorem forLoop_sim {bi : Builtins} (bh : ImpExpr) (bl : LowCT) (x : String) (N : Nat)
    (Inv : Nat → Env → SEnvScalar → Prop)
    (step : ∀ j, j < N → ∀ env σ, Inv j env σ → ∃ env' σ',
      (∀ fuel, denote' bi fuel bh (env.extend x (.int j)) = (.val .unit, env')) ∧
      semScalar bl (σ.upd x (t := .sword 64) (BitVec.ofNat 64 j)) = some σ' ∧
      Inv (j + 1) env' σ') (env : Env) (σ : SEnvScalar) (h0 : Inv 0 env σ) :
    ∀ n, n ≤ N → ∃ envn σn,
      (∀ fuel, denoteForLoop' bi (fuel + n) x 0 N bh env =
        denoteForLoop' bi fuel x n N bh envn) ∧
      semRForD (semScalar bl) x n σ = some σn ∧ Inv n envn σn
  | 0, _ => ⟨env, σ, fun _ => rfl, rfl, h0⟩
  | n + 1, hn => by
    obtain ⟨envn, σn, hA, hB, hC⟩ := forLoop_sim bh bl x N Inv step env σ h0 n (by omega)
    obtain ⟨env', σ', hbody, hsem, hInv⟩ := step n (by omega) envn σn hC
    refine ⟨env', σ', fun fuel => ?_, ?_, hInv⟩
    · rw [show fuel + (n + 1) = (fuel + 1) + n by omega, hA (fuel + 1),
        _root_.Hax.Ascent.denoteForLoop'_next bi (fuel + 1) x (by omega) (by omega)
          (hbody (fuel + 1)) (by intro w hw; cases hw)]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    · simp only [semRForD, hB]
      exact hsem

/-- **The runtime `forFold` in `denote'` and the `RFor` fold in `semScalar`.**
    Under the per-trip simulation of `forLoop_sim`, with `n` bound to `N` in hax,
    `forFold x 0 n bh` returns `()` at every fuel `≥ N`, the `semRForD` fold of
    `bl` over `N` trips succeeds, and the two final environments satisfy `Inv N`. -/
theorem forFold_sim {bi : Builtins} (bh : ImpExpr) (bl : LowCT) (x n : String) (N : Nat)
    (Inv : Nat → Env → SEnvScalar → Prop)
    (step : ∀ j, j < N → ∀ env σ, Inv j env σ → ∃ env' σ',
      (∀ fuel, denote' bi fuel bh (env.extend x (.int j)) = (.val .unit, env')) ∧
      semScalar bl (σ.upd x (t := .sword 64) (BitVec.ofNat 64 j)) = some σ' ∧
      Inv (j + 1) env' σ') (env : Env) (σ : SEnvScalar) (h0 : Inv 0 env σ)
    (hn : env n = some (.int N)) :
    ∃ envN σN,
      (∀ fuel, N ≤ fuel →
        denote' bi fuel (.forFold x (.lit (.int 0)) (.var n) bh) env = (.val .unit, envN)) ∧
      semRForD (semScalar bl) x N σ = some σN ∧ Inv N envN σN := by
  obtain ⟨envN, σN, hA, hB, hC⟩ := forLoop_sim bh bl x N Inv step env σ h0 N le_rfl
  refine ⟨envN, σN, fun fuel hf => ?_, hB, hC⟩
  obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le' hf
  rw [_root_.Hax.Ascent.denote'_forFold bi (f + N) (_root_.Hax.Ascent.denote'_lit bi _ _ env)
    (_root_.Hax.Ascent.denote'_var bi _ hn)]
  rw [hA f]
  exact _root_.Hax.Ascent.denoteForLoop'_done bi f x bh envN le_rfl

/-! ### The `mpn_mul_1` loop body -/

/-- The straight-line bindings of the `mpn_mul_1` loop body before its two
    stores, as `fuseMulHiIdiom` and `aNormalizeTotal` leave them. -/
def mul1Pre : List WBind :=
  [ .load "cy" "rp" "i" .TFp .TFp
  , .load "t" "up" "i" .TFp .TFp
  , .word "lo" "wrapping_mul#64" "t" "v"
  , .word "hi" "mulhi#64" "t" "v"
  , .word "s" "wrapping_add#64" "lo" "cy"
  , .word "__anorm_0" "BitXor#64" "s" "ONES"
  , .word "cq" "BitAnd#64" "__anorm_0" "lo"
  , .word "__anorm_1" "BitXor#64" "s" "lo"
  , .word "__anorm_2" "BitXor#64" "__anorm_1" "ONES"
  , .word "__anorm_3" "wrapping_sub#64" "s" "lo"
  , .word "cr" "BitAnd#64" "__anorm_2" "__anorm_3"
  , .word "__anorm_4" "BitXor#64" "cq" "cr"
  , .word "__anorm_5" "BitAnd#64" "cq" "cr"
  , .word "__anorm_6" "BitXor#64" "__anorm_4" "__anorm_5"
  , .lit "__anorm_7" 63
  , .word "c" "Shr#64" "__anorm_6" "__anorm_7"
  , .word "cyo" "wrapping_add#64" "hi" "c" ]

/-- The store of the low word `rp[i] = s`, into an output array of `R` words. -/
def mul1St1 (R : Nat) : List WBind := [.store "rp" "i" "s" (.TBytes (8 * R)) (.TBytes 0)]

/-- The store of the carry `rp[i + 1] = cyo`, into an output array of `R` words. -/
def mul1St2 (R : Nat) : List WBind :=
  [ .lit "__anorm_8" 1
  , .word "__anorm_9" "Add" "i" "__anorm_8"
  , .store "rp" "__anorm_9" "cyo" (.TBytes (8 * R)) (.TBytes 0) ]

/-- The hax loop body of `mpn_mul_1` after `fuseMulHiIdiom` and `aNormalizeTotal`. -/
def mul1BodyHax : ImpExpr :=
  bindsHax mul1Pre (.seq (.seq (bindsHax (mul1St1 0) (.var "rp")) .unitVal)
    (.seq (.seq (bindsHax (mul1St2 0) (.var "rp")) .unitVal) .unitVal))

/-- The loop body of `mpn_mul_1` as `haxToLowCT` and `scalarizeWordOps` lower it,
    with its array accesses retyped for an output array of `R` words. -/
def mul1BodyLow (R : Nat) : LowCT :=
  bindsLow mul1Pre (.RSeq (.RSeq (bindsLow (mul1St1 R) .RSkip) .RSkip)
    (.RSeq (.RSeq (bindsLow (mul1St2 R) .RSkip) .RSkip) .RSkip))

/-- The array-length table of `mpn_mul_1`: `rp` of `R` words and `up` of `U`. -/
def mul1Len (R U : Nat) : String → Option Nat :=
  fun a => if a = "rp" then some R else if a = "up" then some U else none

/-- A name whose third character is not `'s'` behind the prefix `"__"` is not a
    fresh temporary `"__sx" ++ toString k`. -/
theorem notTmp_of_thirdNe {s : String} {c : Char} {t : List Char}
    (hs : s.toList = '_' :: '_' :: c :: t) (hc : c ≠ 's') : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hd := congrArg String.toList hk
  rw [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms.tmpName,
    String.toList_append, hs] at hd
  simp only [show "__sx".toList = ['_', '_', 's', 'x'] from rfl, List.cons_append,
    List.nil_append, List.cons.injEq] at hd
  exact hc hd.2.2.1

/-- The two-operand word calls whose value is below `2^64` on every operand. -/
theorem wordOpNat_bounded {f : String}
    (hf : f ∈ ["wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "mulhi#64",
      "BitAnd#64", "BitXor#64"]) (a b : Nat) :
    ∃ r, wordOpNat f a b = some r ∧ r < 2 ^ 64 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, Nat.mod_lt _ (by decide)⟩
  · exact ⟨_, rfl, Nat.mod_lt _ (by decide)⟩
  · exact ⟨_, rfl, Nat.mod_lt _ (by decide)⟩
  · exact ⟨_, rfl, CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU_lt _ _⟩
  · exact ⟨_, rfl, Nat.and_lt_two_pow _ (Nat.mod_lt _ (by decide))⟩
  · exact ⟨_, rfl, Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))⟩

/-- A word binding of a bounded word call on related names satisfies its side
    conditions in every environment. -/
theorem WBind.ok_word {S : List String} {A : List (String × Nat)} {env : Env}
    {x f a b : String}
    (hf : f ∈ ["wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "mulhi#64",
      "BitAnd#64", "BitXor#64"])
    (hS : a ∈ S ∧ b ∈ S ∧ a ≠ x ∧ b ≠ x) (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x) :
    (WBind.word x f a b).Ok S A env := by
  have hf' : f ∈ wordOpNames := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact ⟨hf', hS.1, hS.2.1, hS.2.2.1, hS.2.2.2, hxT, hxA, wordOpNat_bounded hf _ _⟩

/-- The name a binding writes. -/
def WBind.target : WBind → String
  | .word x _ _ _ => x
  | .lit x _ => x
  | .load x _ _ _ _ => x
  | .store arr _ _ _ _ => arr

theorem WBind.next_ne (b : WBind) (env : Env) {y : String} (hy : y ≠ b.target) :
    b.next env y = env y := by
  cases b <;> exact extend_ne _ hy

/-- A sequence of bindings leaves every name it does not write unchanged. -/
theorem bindsNext_ne : ∀ (bs : List WBind) (env : Env) {y : String},
    (∀ b ∈ bs, y ≠ b.target) → bindsNext bs env y = env y
  | [], _, _, _ => rfl
  | b :: bs, env, y, h => by
    rw [bindsNext, bindsNext_ne bs _ (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')),
      b.next_ne env (h b List.mem_cons_self)]

theorem natOf_congr {env env' : Env} {x : String} (h : env' x = env x) :
    natOf env' x = natOf env x := by
  simp only [natOf, h]

theorem natOf_extend_int (env : Env) (x : String) (n : Nat) :
    natOf (env.extend x (.int n)) x = n := by
  simp [natOf]

theorem natOf_lit_next (env : Env) (x : String) (n : Nat) :
    natOf ((WBind.lit x n).next env) x = n :=
  natOf_extend_int env x n

/-- A name other than `rp` and `up` is none of the two arrays of `mpn_mul_1`. -/
theorem mul1A_ne {R U : Nat} {x : String} (h1 : x ≠ "rp") (h2 : x ≠ "up") :
    ∀ p ∈ [("rp", R), ("up", U)], p.1 ≠ x := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact Ne.symm h1
  · exact Ne.symm h2

/-- `EnvRelW` restricted to fewer words. -/
theorem EnvRelW.mono {env : Env} {σ : SEnvScalar} {S S' : List String}
    {A : List (String × Nat)} (h : EnvRelW env σ S' A) (hS : ∀ x ∈ S, x ∈ S') :
    EnvRelW env σ S A where
  word x hx := h.word x (hS x hx)
  arr := h.arr
  wordClean x hx := h.wordClean x (hS x hx)
  arrClean := h.arrClean

theorem nt_short {s : String} (h : s.length < 4) : ¬ isTmpName s :=
  CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar.notTmp_of_len s h

/-- The side conditions of the bindings before the stores hold at every trip
    index `j` inside both arrays. -/
theorem mul1Pre_ok (R U j : Nat) (env : Env) (hR : j < R) (hU : j < U)
    (hi : natOf env "i" = j) :
    BindsOk [("rp", R), ("up", U)] mul1Pre ["i", "v", "ONES", "n"] env := by
  have a0 : ¬ isTmpName "__anorm_0" := notTmp_of_thirdNe (s := "__anorm_0") rfl (by decide)
  have a1 : ¬ isTmpName "__anorm_1" := notTmp_of_thirdNe (s := "__anorm_1") rfl (by decide)
  have a2 : ¬ isTmpName "__anorm_2" := notTmp_of_thirdNe (s := "__anorm_2") rfl (by decide)
  have a3 : ¬ isTmpName "__anorm_3" := notTmp_of_thirdNe (s := "__anorm_3") rfl (by decide)
  have a4 : ¬ isTmpName "__anorm_4" := notTmp_of_thirdNe (s := "__anorm_4") rfl (by decide)
  have a5 : ¬ isTmpName "__anorm_5" := notTmp_of_thirdNe (s := "__anorm_5") rfl (by decide)
  have a6 : ¬ isTmpName "__anorm_6" := notTmp_of_thirdNe (s := "__anorm_6") rfl (by decide)
  have a7 : ¬ isTmpName "__anorm_7" := notTmp_of_thirdNe (s := "__anorm_7") rfl (by decide)
  refine ⟨⟨by decide, nt_short (by decide), mul1A_ne (by decide) (by decide), R, by simp,
    by rw [hi]; exact hR⟩, ?_⟩
  refine ⟨⟨by decide, nt_short (by decide), mul1A_ne (by decide) (by decide), U, by simp,
    by rw [natOf_congr (WBind.next_ne _ env (by decide)), hi]; exact hU⟩, ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a0 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a1 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a2 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a3 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a4 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a5 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨WBind.ok_word (by decide) (by decide) a6 (mul1A_ne (by decide) (by decide)), ?_⟩
  refine ⟨⟨by decide, a7, mul1A_ne (by decide) (by decide)⟩, ?_⟩
  refine ⟨⟨by decide, by decide, by decide, by decide, by decide, nt_short (by decide),
    mul1A_ne (by decide) (by decide), _, by rw [natOf_lit_next]; rfl, ?_⟩, ?_⟩
  · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (Nat.mod_lt _ (by decide))
  exact ⟨WBind.ok_word (by decide) (by decide) (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)), trivial⟩

theorem natOf_word_next (env : Env) (x f a b : String) :
    natOf ((WBind.word x f a b).next env) x = (wordOpNat f (natOf env a) (natOf env b)).getD 0 :=
  natOf_extend_int env x _

/-- The side conditions of the low-word store at a trip index inside `rp`. -/
theorem mul1St1_ok {R U j : Nat} {S : List String} {env : Env} (hiS : "i" ∈ S) (hsS : "s" ∈ S)
    (hi : natOf env "i" = j) (hR : j < R) :
    BindsOk [("rp", R), ("up", U)] (mul1St1 R) S env :=
  ⟨⟨hiS, hsS, R, by simp, encodeTy_TBytes_eight_mul R, by rw [hi]; exact hR⟩, trivial⟩

/-- The side conditions of the carry store at a trip index `j` with `j + 1`
    inside `rp`. -/
theorem mul1St2_ok {R U j : Nat} {S : List String} {env : Env} (hiS : "i" ∈ S)
    (hcS : "cyo" ∈ S) (hi : natOf env "i" = j) (hR : j + 1 < R) (h64 : j + 1 < 2 ^ 64) :
    BindsOk [("rp", R), ("up", U)] (mul1St2 R) S env := by
  have a8 : ¬ isTmpName "__anorm_8" := notTmp_of_thirdNe (s := "__anorm_8") rfl (by decide)
  have a9 : ¬ isTmpName "__anorm_9" := notTmp_of_thirdNe (s := "__anorm_9") rfl (by decide)
  have hi1 : natOf ((WBind.lit "__anorm_8" 1).next env) "i" = j := by
    rw [natOf_congr (WBind.next_ne _ env (by decide)), hi]
  refine ⟨⟨by decide, a8, mul1A_ne (by decide) (by decide)⟩,
    ⟨by decide, by simp [WBind.written, hiS], by simp [WBind.written], by decide, by decide, a9,
      mul1A_ne (by decide) (by decide), j + 1, by rw [hi1, natOf_lit_next]; rfl, h64⟩,
    ⟨by simp [WBind.written], List.mem_append_right _ (List.mem_append_right _ hcS), R, by simp,
      encodeTy_TBytes_eight_mul R, ?_⟩, trivial⟩
  rw [natOf_word_next, hi1, natOf_lit_next]
  exact hR

/-- The hax environment after one trip of the `mpn_mul_1` body. -/
def mul1Next (R : Nat) (env : Env) : Env :=
  bindsNext (mul1St2 R) (bindsNext (mul1St1 R) (bindsNext mul1Pre env))

/-- **One trip of the `mpn_mul_1` body.** At a trip index `j` with `j + 1` inside
    `rp` and `j` inside `up`, from environments related on `v`, `ONES`, `n`, `rp`
    and `up`, the hax body with `i ↦ j` returns `()` in `mul1Next R`, the
    `semScalar` run of the retyped lowered body with `i` bound to the word `j`
    succeeds, and the two results are related on the same names. -/
theorem mul1_trip {bi : Builtins} (hbi : WordBuiltins' bi) {R U j : Nat} (hR : j + 1 < R)
    (hU : j < U) (h64 : j + 1 < 2 ^ 64) {env : Env} {σ : SEnvScalar}
    (h : EnvRelW env σ ["v", "ONES", "n"] [("rp", R), ("up", U)]) :
    ∃ σ', (∀ fuel, denote' bi fuel mul1BodyHax (env.extend "i" (.int j)) =
        (.val .unit, mul1Next R (env.extend "i" (.int j)))) ∧
      semScalar (mul1BodyLow R) (σ.upd "i" (t := .sword 64) (BitVec.ofNat 64 j)) = some σ' ∧
      EnvRelW (mul1Next R (env.extend "i" (.int j))) σ' ["v", "ONES", "n"]
        [("rp", R), ("up", U)] := by
  have hi : EnvRelW (env.extend "i" (.int j)) (σ.upd "i" (t := .sword 64) (BitVec.ofNat 64 j))
      ["i", "v", "ONES", "n"] [("rp", R), ("up", U)] :=
    h.update "i" (nt_short (by decide)) (mul1A_ne (by decide) (by decide))
      (fun y hy => extend_ne _ hy) (fun y hy _ => upd_ne _ hy)
      ⟨j, by omega, extend_self _, upd_self _⟩
  have hiN : natOf (env.extend "i" (.int j)) "i" = j := natOf_extend_int _ _ _
  have ok1 := mul1Pre_ok R U j _ (by omega) hU hiN
  obtain ⟨σ₁, hL1, hR1⟩ := (binds_sim hbi 0 _ mul1Pre _ _ _ hi ok1 .unitVal
    (.RSeq (.RSeq (bindsLow (mul1St1 R) .RSkip) .RSkip)
      (.RSeq (.RSeq (bindsLow (mul1St2 R) .RSkip) .RSkip) .RSkip))).2
  have hiN1 : natOf (bindsNext mul1Pre (env.extend "i" (.int j))) "i" = j := by
    rw [natOf_congr (bindsNext_ne _ _ (by decide)), hiN]
  have ok2 : BindsOk [("rp", R), ("up", U)] (mul1St1 R)
      (bindsScope mul1Pre ["i", "v", "ONES", "n"]) (bindsNext mul1Pre (env.extend "i" (.int j))) :=
    mul1St1_ok (by decide) (by decide) hiN1 (by omega)
  have hy2 : ∀ E : Env, bindsNext (mul1St1 R) E "rp" =
      some (.array ((arrOf E "rp").set (natOf E "i") (.int (natOf E "s")))) := fun E => by
    simp only [mul1St1, bindsNext, WBind.next]
    exact extend_self _
  obtain ⟨-, σ₂, hL2, hR2⟩ := segment_sim hbi 0 hR1 ok2 "rp" ⟨_, hy2 _⟩ .unitVal
    (.RSeq (.RSeq (bindsLow (mul1St2 R) .RSkip) .RSkip) .RSkip)
  have hiN2 : natOf (bindsNext (mul1St1 R) (bindsNext mul1Pre (env.extend "i" (.int j)))) "i" =
      j := by
    rw [natOf_congr (bindsNext_ne _ _ (by simp [mul1St1, WBind.target])), hiN1]
  have ok3 : BindsOk [("rp", R), ("up", U)] (mul1St2 R)
      (bindsScope (mul1St1 R) (bindsScope mul1Pre ["i", "v", "ONES", "n"]))
      (bindsNext (mul1St1 R) (bindsNext mul1Pre (env.extend "i" (.int j)))) :=
    mul1St2_ok (by simp [bindsScope, mul1St1, mul1Pre, WBind.written])
      (by simp [bindsScope, mul1St1, mul1Pre, WBind.written]) hiN2 hR h64
  have hy3 : ∀ E : Env, ∃ v, bindsNext (mul1St2 R) E "rp" = some v ∧ v.isControlFlow = false :=
    fun E => ⟨_, by simp only [mul1St2, bindsNext, WBind.next]; exact extend_self _, rfl⟩
  obtain ⟨v₃, hv₃, hc₃⟩ := hy3 (bindsNext (mul1St1 R) (bindsNext mul1Pre (env.extend "i" (.int j))))
  obtain ⟨-, σ₃, hL3, hR3⟩ := segment_sim hbi 0 hR2 ok3 "rp" ⟨_, hv₃⟩ .unitVal .RSkip
  refine ⟨σ₃, fun fuel => ?_, ?_,
    hR3.mono (by simp [bindsScope, mul1St1, mul1St2, mul1Pre, WBind.written])⟩
  · show denote' bi fuel (bindsHax mul1Pre (.seq (.seq (bindsHax (mul1St1 R) (.var "rp"))
      .unitVal) (.seq (.seq (bindsHax (mul1St2 R) (.var "rp")) .unitVal) .unitVal))) _ = _
    rw [bindsHax_run' hbi fuel _ mul1Pre _ _ _ hi ok1,
      segment_run' hbi fuel hR1 ok2 (hy2 _) rfl,
      segment_run' hbi fuel hR2 ok3 hv₃ hc₃]
    exact _root_.Hax.Ascent.denote'_unitVal bi fuel _
  · rw [mul1BodyLow, hL1, hL2, hL3]
    rfl

/-- The hax environment after `n` trips of the `mpn_mul_1` body, trip `j` run
    with `i ↦ j`. -/
def mul1Trips (R : Nat) (env : Env) : Nat → Env
  | 0 => env
  | n + 1 => mul1Next R ((mul1Trips R env n).extend "i" (.int n))

/-- **The `mpn_mul_1` loop.** From environments related on `v`, `ONES`, `n`, `rp`
    (`R` words) and `up` (`U` words), with `n` holding `N`, `N + 1 ≤ R` and
    `N ≤ U`: the hax loop `forFold i 0 n` over the fused, A-normalised body
    returns `()` in `mul1Trips R env N` at every fuel `≥ N`, the `N`-trip
    `semScalar` fold of the retyped lowered body succeeds, and the two final
    environments are related on the same names. -/
theorem mul1_loop_sim {bi : Builtins} (hbi : WordBuiltins' bi) {R U N : Nat} (hR : N + 1 ≤ R)
    (hU : N ≤ U) (h64 : N + 1 < 2 ^ 64) {env : Env} {σ : SEnvScalar}
    (h : EnvRelW env σ ["v", "ONES", "n"] [("rp", R), ("up", U)]) (hn : natOf env "n" = N) :
    ∃ σN,
      (∀ fuel, N ≤ fuel → denote' bi fuel (.forFold "i" (.lit (.int 0)) (.var "n") mul1BodyHax)
        env = (.val .unit, mul1Trips R env N)) ∧
      semRForD (semScalar (mul1BodyLow R)) "i" N σ = some σN ∧
      EnvRelW (mul1Trips R env N) σN ["v", "ONES", "n"] [("rp", R), ("up", U)] := by
  have hnE : env "n" = some (.int N) := by
    rw [← hn]; exact ((h.word "n" (by simp)).natOf_eq).2.1
  obtain ⟨envN, σN, hA, hB, hC, hD⟩ := forFold_sim (bi := bi) mul1BodyHax (mul1BodyLow R) "i" "n" N
    (fun j e s => e = mul1Trips R env j ∧
      EnvRelW e s ["v", "ONES", "n"] [("rp", R), ("up", U)])
    (fun j hj e s ⟨he, hrel⟩ => by
      obtain ⟨σ', h1, h2, h3⟩ := mul1_trip hbi (j := j) (by omega) (by omega) (by omega) hrel
      subst he
      exact ⟨_, σ', h1, h2, rfl, h3⟩) env σ ⟨rfl, h⟩ hnE
  subst hC
  exact ⟨σN, hA, hB, hD⟩

/-! ### The values the `mpn_mul_1` trip computes -/

section Values

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (mul1Limb ones mul1FoldStep mul1Fold)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (hiU_eq ltu_chain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (mulHiW)

/-- The natural number of an `.int` value, else `0`. -/
def intNat : Value → Nat
  | .int n => n.toNat
  | _ => 0

theorem intNat_natCast (n : Nat) : intNat (.int (n : Int)) = n :=
  Int.toNat_natCast n

theorem arrOf_congr {env env' : Env} {x : String} (h : env' x = env x) :
    arrOf env' x = arrOf env x := by
  simp only [arrOf, h]

theorem natOf_next_ne {b : WBind} {E : Env} {y : String} (h : y ≠ b.target) :
    natOf (b.next E) y = natOf E y :=
  natOf_congr (b.next_ne E h)

theorem arrOf_next_ne {b : WBind} {E : Env} {y : String} (h : y ≠ b.target) :
    arrOf (b.next E) y = arrOf E y :=
  arrOf_congr (b.next_ne E h)

theorem arrOf_store_next (E : Env) (arr i v : String) (ta tv : TowerType) :
    arrOf ((WBind.store arr i v ta tv).next E) arr =
      (arrOf E arr).set (natOf E i) (.int (natOf E v)) := by
  simp [WBind.next, arrOf]

theorem natOf_extend_self (E : Env) (x : String) (v : Value) :
    natOf (E.extend x v) x = intNat v := by
  simp only [natOf, extend_self]
  cases v <;> rfl

theorem natOf_load_next (E : Env) (x arr i : String) (t ta : TowerType) :
    natOf ((WBind.load x arr i t ta).next E) x =
      intNat ((arrOf E arr)[natOf E i]?.getD (.int 0)) :=
  natOf_extend_self E x _

theorem wop_add (x y : BitVec 64) :
    (wordOpNat "wrapping_add#64" x.toNat y.toNat).getD 0 = (x + y).toNat := by
  show (x.toNat + y.toNat) % 2 ^ 64 = _
  exact (BitVec.toNat_add x y).symm

theorem wop_sub (x y : BitVec 64) :
    (wordOpNat "wrapping_sub#64" x.toNat y.toNat).getD 0 = (x - y).toNat := by
  have h : wordOpNat "wrapping_sub#64" x.toNat y.toNat =
      some ((x.toNat % 2 ^ 64 + 2 ^ 64 - y.toNat % 2 ^ 64) % 2 ^ 64) := by
    unfold wordOpNat
    rfl
  rw [h, Option.getD_some, BitVec.toNat_sub, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt,
    Nat.add_comm (2 ^ 64 - _), ← Nat.add_sub_assoc (Nat.le_of_lt y.isLt)]

theorem wop_mul (x y : BitVec 64) :
    (wordOpNat "wrapping_mul#64" x.toNat y.toNat).getD 0 = (x * y).toNat := by
  show (x.toNat * y.toNat) % 2 ^ 64 = _
  exact (BitVec.toNat_mul x y).symm

theorem wop_mulhi (x y : BitVec 64) :
    (wordOpNat "mulhi#64" x.toNat y.toNat).getD 0 = (mulHiW x y).toNat := by
  rw [← hiU_eq, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (CatCrypt.Crypto.Jasmin.LowCT.sexprMulHiU_lt _ _)]
  rfl

theorem wop_and (x y : BitVec 64) :
    (wordOpNat "BitAnd#64" x.toNat y.toNat).getD 0 = (x &&& y).toNat := by
  show (x.toNat % 2 ^ 64) &&& (y.toNat % 2 ^ 64) = _
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  exact (BitVec.toNat_and x y).symm

theorem wop_xor (x y : BitVec 64) :
    (wordOpNat "BitXor#64" x.toNat y.toNat).getD 0 = (x ^^^ y).toNat := by
  show (x.toNat % 2 ^ 64) ^^^ (y.toNat % 2 ^ 64) = _
  rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt]
  exact (BitVec.toNat_xor x y).symm

theorem wop_shr63 (x : BitVec 64) :
    (wordOpNat "Shr#64" x.toNat 63).getD 0 = (x >>> 63).toNat := by
  show (x.toNat % 2 ^ 64) >>> 63 = _
  rw [Nat.mod_eq_of_lt x.isLt]
  exact (BitVec.toNat_ushiftRight x 63).symm

theorem wop_Add (a b : Nat) : (wordOpNat "Add" a b).getD 0 = a + b := rfl

/-- **One trip on values.** From a hax environment holding the trip index `j`,
    the multiplicand limb `T` at `up[j]`, the carry-in `C` at `rp[j]`, the
    multiplier `W` and the all-ones word, one trip of the body writes the low
    word of `mul1Limb T W C` to `rp[j]` and its carry-out to `rp[j + 1]`. -/
theorem mul1Next_rp (R : Nat) (E : Env) (j : Nat) (T W C : BitVec 64)
    (hi : natOf E "i" = j) (hup : (arrOf E "up")[j]? = some (.int T.toNat))
    (hcy : (arrOf E "rp")[j]? = some (.int C.toNat)) (hv : natOf E "v" = W.toNat)
    (hO : natOf E "ONES" = (BitVec.ofNat 64 ones).toNat) :
    arrOf (mul1Next R E) "rp" =
      ((arrOf E "rp").set j (.int (mul1Limb T W C).1.toNat)).set (j + 1)
        (.int (mul1Limb T W C).2.toNat) := by
  simp (disch := first | decide | (simp only [WBind.target]; decide)) only [mul1Next, mul1Pre,
    mul1St1, mul1St2, bindsNext,
    arrOf_store_next, arrOf_next_ne, natOf_next_ne, natOf_word_next, natOf_lit_next,
    natOf_load_next, hi, hup, hcy, hv, hO, Option.getD_some, intNat_natCast, wop_add, wop_sub,
    wop_mul, wop_mulhi, wop_and, wop_xor, wop_shr63, wop_Add]
  rw [ltu_chain]
  rfl

theorem memGetDyn_eq_of_lt {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n) :
    memGetDyn arr k = arr ⟨k, hk⟩ := by
  match n, arr with
  | 0, _ => exact absurd hk (Nat.not_lt_zero k)
  | (p + 1), arr => simp only [memGetDyn]; congr 1; exact Fin.ext (Nat.mod_eq_of_lt hk)

/-- The first `k` cells of a memref as hax `.int` values. -/
def intCells {n : Nat} (a : Fin n → BitVec 64) (k : Nat) : List Value :=
  (List.range k).map fun j => .int (memGetDyn a j).toNat

theorem intCells_getElem? {n : Nat} (a : Fin n → BitVec 64) {k j : Nat} (hj : j < k) :
    (intCells a k)[j]? = some (.int (memGetDyn a j).toNat) := by
  simp [intCells, hj]

/-- Writing the two words of `mul1Limb` at cells `j` and `j + 1` of the first `k`
    cells of `acc` gives the first `k` cells of `mul1FoldStep up b acc j`. -/
theorem intCells_mul1FoldStep {NU NR : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) {k j : Nat} (hk : k ≤ NR) (hj : j + 1 < k) :
    ((intCells acc k).set j (.int (mul1Limb (memGetDyn up j) b (memGetDyn acc j)).1.toNat)).set
        (j + 1) (.int (mul1Limb (memGetDyn up j) b (memGetDyn acc j)).2.toNat) =
      intCells (mul1FoldStep up b acc j) k := by
  apply List.ext_getElem (by simp [intCells])
  intro m h1 h2
  have hm : m < k := by simpa [intCells] using h2
  simp only [List.getElem_set, intCells, List.getElem_map, List.getElem_range, mul1FoldStep]
  rw [memGetDyn_memSetDyn _ (by omega) (by omega), memGetDyn_memSetDyn _ (by omega) (by omega)]
  by_cases hA : j + 1 = m
  · subst hA; simp
  · by_cases hB : j = m
    · subst hB; simp
    · simp [hA, hB, Ne.symm hA, Ne.symm hB]

theorem extend_of_eq {env : Env} {x : String} {v : Value} (h : env x = some v) :
    env.extend x v = env := by
  funext y
  unfold Env.extend
  split
  · rename_i hy
    rw [beq_iff_eq] at hy
    subst hy
    exact h.symm
  · rfl

/-- The last binding of a trip stores into `rp`, so `rp` holds an array after it. -/
theorem mul1Next_rp_eq (R : Nat) (E : Env) :
    mul1Next R E "rp" = some (.array (arrOf (mul1Next R E) "rp")) := by
  obtain ⟨l, hl⟩ : ∃ l, mul1Next R E "rp" = some (.array l) :=
    ⟨_, by simp only [mul1Next, mul1St2, bindsNext, WBind.next]; exact extend_self _⟩
  rw [hl]
  simp [arrOf, hl]

/-- A trip leaves `up`, `v`, `ONES` and `n` unchanged. -/
theorem mul1Next_frame (R : Nat) (E : Env) {y : String}
    (hy : y = "up" ∨ y = "v" ∨ y = "ONES" ∨ y = "n") : mul1Next R E y = E y := by
  unfold mul1Next
  rcases hy with rfl | rfl | rfl | rfl <;>
    (rw [bindsNext_ne _ _ (by simp [mul1St2, WBind.target]),
      bindsNext_ne _ _ (by simp [mul1St1, WBind.target]), bindsNext_ne _ _ (by decide)])

/-- **The values of the hax loop.** From a hax environment holding the first `U`
    cells of `up`, the first `R` cells of `acc` at `rp`, the multiplier `b` and
    the all-ones word, `n` trips with `n + 1 ≤ R` and `n ≤ U` leave the first `R`
    cells of `mul1Fold up b n acc` at `rp`, and `up`, `v`, `ONES`, `n` unchanged. -/
theorem mul1Trips_val (R U : Nat) {NU NR : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (env : Env) (hRN : R ≤ NR) (hUN : U ≤ NU)
    (hup : env "up" = some (.array (intCells up U)))
    (hrp : env "rp" = some (.array (intCells acc R))) (hv : env "v" = some (.int b.toNat))
    (hO : env "ONES" = some (.int ones)) :
    ∀ n, n + 1 ≤ R → n ≤ U →
      mul1Trips R env n "rp" = some (.array (intCells (mul1Fold up b n acc) R)) ∧
      ∀ y, (y = "up" ∨ y = "v" ∨ y = "ONES" ∨ y = "n") → mul1Trips R env n y = env y
  | 0, _, _ => ⟨hrp, fun _ _ => rfl⟩
  | n + 1, hR, hU => by
    obtain ⟨ihr, ihf⟩ := mul1Trips_val R U up b acc env hRN hUN hup hrp hv hO n (by omega)
      (by omega)
    have hext : ∀ y, y ≠ "i" →
        (mul1Trips R env n).extend "i" (.int n) y = mul1Trips R env n y :=
      fun y hy => extend_ne _ hy
    have hupE : (arrOf ((mul1Trips R env n).extend "i" (.int n)) "up")[n]? =
        some (.int (memGetDyn up n).toNat) := by
      rw [arrOf_congr (hext "up" (by decide)), arrOf_congr (ihf "up" (by simp))]
      simp only [arrOf, hup]
      exact intCells_getElem? up (by omega)
    have hrpE : arrOf ((mul1Trips R env n).extend "i" (.int n)) "rp" =
        intCells (mul1Fold up b n acc) R := by
      rw [arrOf_congr (hext "rp" (by decide))]
      simp only [arrOf, ihr]
    have hcyE : (arrOf ((mul1Trips R env n).extend "i" (.int n)) "rp")[n]? =
        some (.int (memGetDyn (mul1Fold up b n acc) n).toNat) := by
      rw [hrpE]
      exact intCells_getElem? _ (by omega)
    have hvE : natOf ((mul1Trips R env n).extend "i" (.int n)) "v" = b.toNat := by
      rw [natOf_congr (hext "v" (by decide)), natOf_congr (ihf "v" (by simp))]
      simp [natOf, hv]
    have hOE : natOf ((mul1Trips R env n).extend "i" (.int n)) "ONES" =
        (BitVec.ofNat 64 ones).toNat := by
      rw [natOf_congr (hext "ONES" (by decide)), natOf_congr (ihf "ONES" (by simp)),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt
          CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote.hones]
      simp [natOf, hO]
    refine ⟨?_, fun y hy => ?_⟩
    · show mul1Next R ((mul1Trips R env n).extend "i" (.int n)) "rp" = _
      rw [mul1Next_rp_eq, mul1Next_rp R _ n (memGetDyn up n) b _ (natOf_extend_int _ _ _) hupE
        hcyE hvE hOE, hrpE, intCells_mul1FoldStep (j := n) up b _ hRN (by omega),
        CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit.mul1Fold_succ]
    · show mul1Next R ((mul1Trips R env n).extend "i" (.int n)) y = _
      rw [mul1Next_frame R _ hy, hext y (by rcases hy with rfl | rfl | rfl | rfl <;> decide),
        ihf y hy]

/-- A word slot holding `w` and a hax `.int` of `w.toNat` are related. -/
theorem WordAt.of_bv {env : Env} {σ : SEnvScalar} {x : String} (w : BitVec 64)
    (he : env x = some (.int w.toNat)) (hs : σ x = some ⟨.sword 64, w⟩) : WordAt env σ x :=
  ⟨w.toNat, w.isLt, he, by rw [hs, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩

/-- The first `k` cells of a memref of `n ≥ k` words, as a memref of `k` words. -/
def prefixMem {n : Nat} (a : Fin n → BitVec 64) (k : Nat) : Fin k → BitVec 64 :=
  fun j => memGetDyn a j.val

theorem ArrAt.of_intCells {env : Env} {σ : SEnvScalar} {x : String} {n : Nat}
    (a : Fin n → BitVec 64) (k : Nat) (he : env x = some (.array (intCells a k)))
    (hs : σ x = some ⟨.memref k, prefixMem a k⟩) : ArrAt env σ x k :=
  ⟨intCells a k, prefixMem a k, he, hs, by simp [intCells], fun j hj => by
    rw [intCells_getElem? a hj, memGetDyn_eq_of_lt _ hj]; rfl⟩

/-- The scalar environment of the `mpn_mul_1` loop entry: the words `v`, `ONES`
    and `n`, and the first `R` cells of `acc` at `rp` and `U` cells of `up`. -/
def mul1Sigma {NU NR : Nat} (R U : Nat) (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (N : Nat) : SEnvScalar :=
  ((((CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote.emptyEnv.upd "v"
    (t := .sword 64) b).upd "ONES" (t := .sword 64)
    (BitVec.ofNat 64 ones)).upd "n" (t := .sword 64) (BitVec.ofNat 64 N)).upd "rp"
    (t := .memref R) (prefixMem acc R)).upd "up" (t := .memref U) (prefixMem up U)

theorem mul1Sigma_rel {NU NR : Nat} (R U : Nat) (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) {N : Nat} (hN : N < 2 ^ 64) {env : Env}
    (hup : env "up" = some (.array (intCells up U)))
    (hrp : env "rp" = some (.array (intCells acc R))) (hv : env "v" = some (.int b.toNat))
    (hO : env "ONES" = some (.int ones)) (hn : env "n" = some (.int N)) :
    EnvRelW env (mul1Sigma R U up b acc N) ["v", "ONES", "n"] [("rp", R), ("up", U)] where
  word x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · refine WordAt.of_bv b hv ?_
      simp only [mul1Sigma]
      rw [upd_ne (y := "v") (x := "up") _ (by decide), upd_ne (y := "v") (x := "rp") _ (by decide),
        upd_ne (y := "v") (x := "n") _ (by decide), upd_ne (y := "v") (x := "ONES") _ (by decide),
        upd_self]
    · refine WordAt.of_bv (BitVec.ofNat 64 ones) ?_ ?_
      · rw [hO, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
          CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote.hones]
      · simp only [mul1Sigma]
        rw [upd_ne (y := "ONES") (x := "up") _ (by decide),
          upd_ne (y := "ONES") (x := "rp") _ (by decide),
          upd_ne (y := "ONES") (x := "n") _ (by decide), upd_self]
    · refine WordAt.of_bv (BitVec.ofNat 64 N) ?_ ?_
      · rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]
      · simp only [mul1Sigma]
        rw [upd_ne (y := "n") (x := "up") _ (by decide),
          upd_ne (y := "n") (x := "rp") _ (by decide), upd_self]
  arr p hp := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ArrAt.of_intCells acc R hrp ?_
      simp only [mul1Sigma]
      rw [upd_ne (y := "rp") (x := "up") _ (by decide), upd_self]
    · exact ArrAt.of_intCells up U hup (upd_self _)
  wordClean x hx := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact nt_short (by decide)
    · exact CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar.notTmp_of_headNe
        (s := "ONES") rfl (by decide)
    · exact nt_short (by decide)
  arrClean p hp := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact nt_short (s := "rp") (by decide)
    · exact nt_short (s := "up") (by decide)

/-- The fused, A-normalised hax `mpn_mul_1`: the argument rebindings, the loop,
    and the return of `rp` with the carry `rp[n]`. -/
def mul1ProgHax : ImpExpr :=
  .letBind "rp" (.var "rp") (.letBind "up" (.var "up") (.letBind "n" (.var "n")
    (.letBind "v" (.var "v") (.letBind "rp" (.var "rp")
      (.seq (.forFold "i" (.lit (.int 0)) (.var "n") mul1BodyHax)
        (.letBind "carry" (.app "index" [.var "rp", .var "n"])
          (.tuple [.var "rp", .var "carry"])))))))

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (mul1RtProgOpt mul1Count mul1Init Gouter NR NU)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (mul1RtProg_fold upVar vVar)
open CatCrypt.Crypto.SecureCompilation.VIR (Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL)

/-- **The hax `mpn_mul_1` and the compiled loop return the same words.** For every
    valuation `V` of the compiled runtime-trip `mpn_mul_1` whose trip count `N`
    satisfies `N + 1 ≤ R ≤ NR` and `N ≤ U ≤ NU`, and every hax environment holding
    the first `U` cells of `up`, the first `R` cells of `rp`, the multiplier `v`,
    the all-ones word at `ONES` and `N` at `n`: the compiled program's denotation
    is some `out`, and at every fuel `≥ N` the fused, A-normalised hax program
    returns the first `R` cells of `out` and the carry cell `out[N]`. -/
theorem mul1_hax_eq_compiled {bi : Builtins} (hbi : WordBuiltins' bi)
    (V : Ctxt.Valuation Gouter) {R U : Nat} (hR9 : R ≤ NR) (hU8 : U ≤ NU)
    (hNR : (mul1Count.lookup V).toNat + 1 ≤ R) (hNU : (mul1Count.lookup V).toNat ≤ U)
    {env : Env} (hup : env "up" = some (.array (intCells (upVar.lookup V) U)))
    (hrp : env "rp" = some (.array (intCells (mul1Init.lookup V) R)))
    (hv : env "v" = some (.int (vVar.lookup V).toNat)) (hO : env "ONES" = some (.int ones))
    (hn : env "n" = some (.int (mul1Count.lookup V).toNat)) :
    ∃ out, (mul1RtProgOpt ()).map (fun c => ComL.denote c V) = some out ∧
      ∀ fuel, (mul1Count.lookup V).toNat ≤ fuel →
        (denote' bi fuel mul1ProgHax env).1 =
          .val (.tuple [.array (intCells out R),
            .int (memGetDyn out (mul1Count.lookup V).toNat).toNat]) := by
  refine ⟨_, mul1RtProg_fold V, fun fuel hf => ?_⟩
  have hR64 : R < 2 ^ 64 := by
    have : NR = 9 := rfl
    omega
  obtain ⟨hvr, hvf⟩ := mul1Trips_val R U (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
    env hR9 hU8 hup hrp hv hO _ hNR hNU
  have hrel := mul1Sigma_rel R U (upVar.lookup V) (vVar.lookup V) (mul1Init.lookup V)
    (N := (mul1Count.lookup V).toNat) (by omega) hup hrp hv hO hn
  obtain ⟨σN, hloop, -, -⟩ := mul1_loop_sim hbi hNR hNU (by omega) hrel (by simp [natOf, hn])
  have hnN : mul1Trips R env (mul1Count.lookup V).toNat "n" =
      some (.int (mul1Count.lookup V).toNat) := by
    rw [hvf "n" (by simp), hn]
  have hcell := intCells_getElem? (mul1Fold (upVar.lookup V) (vVar.lookup V)
    (mul1Count.lookup V).toNat (mul1Init.lookup V)) (k := R) (j := (mul1Count.lookup V).toNat)
    (by omega)
  rw [mul1ProgHax,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hrp) rfl,
    extend_of_eq hrp,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hup) rfl,
    extend_of_eq hup,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hn) rfl,
    extend_of_eq hn,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hv) rfl,
    extend_of_eq hv,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hrp) rfl,
    extend_of_eq hrp,
    _root_.Hax.Ascent.denote'_seq bi fuel (hloop fuel hf) rfl,
    _root_.Hax.Ascent.denote'_letBind bi fuel (_root_.Hax.Ascent.denote'_app bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hvr) rfl
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel (_root_.Hax.Ascent.denote'_var bi fuel hnN) rfl
          (_root_.Hax.Ascent.denoteArgs'_nil bi fuel _)))
      (hbi.index _ _ _ hcell)) rfl,
    _root_.Hax.Ascent.denote'_tuple bi fuel
      (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
        (_root_.Hax.Ascent.denote'_var bi fuel (by rw [extend_ne _ (by decide)]; exact hvr)) rfl
        (_root_.Hax.Ascent.denoteArgs'_cons bi fuel
          (_root_.Hax.Ascent.denote'_var bi fuel (extend_self _)) rfl
          (_root_.Hax.Ascent.denoteArgs'_nil bi fuel _)))]

/-- **The hax `mpn_mul_1` under hax-lean's `u64` table and the compiled loop
    return the same words.** `mul1_hax_eq_compiled` at `bi := Hax.hax64Builtins`. -/
theorem mul1_hax_eq_compiled_runtime (V : Ctxt.Valuation Gouter) {R U : Nat} (hR9 : R ≤ NR)
    (hU8 : U ≤ NU) (hNR : (mul1Count.lookup V).toNat + 1 ≤ R)
    (hNU : (mul1Count.lookup V).toNat ≤ U)
    {env : Env} (hup : env "up" = some (.array (intCells (upVar.lookup V) U)))
    (hrp : env "rp" = some (.array (intCells (mul1Init.lookup V) R)))
    (hv : env "v" = some (.int (vVar.lookup V).toNat)) (hO : env "ONES" = some (.int ones))
    (hn : env "n" = some (.int (mul1Count.lookup V).toNat)) :
    ∃ out, (mul1RtProgOpt ()).map (fun c => ComL.denote c V) = some out ∧
      ∀ fuel, (mul1Count.lookup V).toNat ≤ fuel →
        (denote' _root_.Hax.hax64Builtins fuel mul1ProgHax env).1 =
          .val (.tuple [.array (intCells out R),
            .int (memGetDyn out (mul1Count.lookup V).toNat).toNat]) :=
  mul1_hax_eq_compiled hax64Builtins_wordBuiltins' V hR9 hU8 hNR hNU hup hrp hv hO hn

/-- The hax environment of the `mpn_mul_1` loop entry: the first `U` cells of
    `up`, the first `R` cells of `acc` at `rp`, the multiplier `b`, the all-ones
    word and the trip count `N`. -/
def mul1Env0 {NU NR : Nat} (R U : Nat) (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) (N : Nat) : Env :=
  ((((Env.empty.extend "up" (.array (intCells up U))).extend "rp"
    (.array (intCells acc R))).extend "v" (.int b.toNat)).extend "ONES" (.int ones)).extend
    "n" (.int N)

/-- **The front's `mpn_mul_1` body folds to `mul1Fold`.** The `N`-trip `semScalar`
    fold of the retyped lowered body from the loop-entry scalar environment
    succeeds and leaves at `rp` a memref whose cells below `R` are those of
    `mul1Fold up b N acc`, the fold `mul1RtProg_fold` identifies with the compiled
    loop and whose step `limbBody_run` computes for `limbBodyLowCT`. -/
theorem mul1BodyLow_fold {NU NR : Nat} (up : Fin NU → BitVec 64) (b : BitVec 64)
    (acc : Fin NR → BitVec 64) {R U N : Nat} (hRN : R ≤ NR) (hUN : U ≤ NU) (hNR : N + 1 ≤ R)
    (hNU : N ≤ U) (h64 : R < 2 ^ 64) :
    ∃ σN, semRForD (semScalar (mul1BodyLow R)) "i" N (mul1Sigma R U up b acc N) = some σN ∧
      ∃ a : Fin R → BitVec 64, σN "rp" = some ⟨.memref R, a⟩ ∧
        ∀ k, k < R → memGetDyn a k = memGetDyn (mul1Fold up b N acc) k := by
  have hup : mul1Env0 R U up b acc N "up" = some (.array (intCells up U)) := by
    simp only [mul1Env0]
    rw [extend_ne (x := "n") _ (by decide), extend_ne (x := "ONES") _ (by decide),
      extend_ne (x := "v") _ (by decide), extend_ne (x := "rp") _ (by decide), extend_self]
  have hrp : mul1Env0 R U up b acc N "rp" = some (.array (intCells acc R)) := by
    simp only [mul1Env0]
    rw [extend_ne (x := "n") _ (by decide), extend_ne (x := "ONES") _ (by decide),
      extend_ne (x := "v") _ (by decide), extend_self]
  have hv : mul1Env0 R U up b acc N "v" = some (.int b.toNat) := by
    simp only [mul1Env0]
    rw [extend_ne (x := "n") _ (by decide), extend_ne (x := "ONES") _ (by decide), extend_self]
  have hO : mul1Env0 R U up b acc N "ONES" = some (.int ones) := by
    simp only [mul1Env0]
    rw [extend_ne (x := "n") _ (by decide), extend_self]
  have hn : mul1Env0 R U up b acc N "n" = some (.int N) := by
    simp only [mul1Env0]
    rw [extend_self]
  obtain ⟨σN, -, hsem, hrel⟩ := mul1_loop_sim hax64Builtins_wordBuiltins' hNR hNU (by omega)
    (mul1Sigma_rel R U up b acc (by omega) hup hrp hv hO hn) (by simp [natOf, hn])
  obtain ⟨hvr, -⟩ := mul1Trips_val R U up b acc _ hRN hUN hup hrp hv hO N hNR hNU
  obtain ⟨vs, a, he, hs, -, hc⟩ := hrel.arr ("rp", R) (by simp)
  rw [hvr] at he
  cases he
  refine ⟨σN, hsem, a, hs, fun k hk => ?_⟩
  have := hc k hk
  rw [intCells_getElem? _ hk] at this
  simp only [Option.some.injEq, Value.int.injEq, Nat.cast_inj] at this
  exact BitVec.eq_of_toNat_eq this.symm

end Values

/-- The lowered and retyped `mpn_mul_1`: the runtime loop over the retyped body,
    then the load of the carry `rp[n]`. -/
theorem mul1_front_prog (R U : Nat) :
    (haxToLowCT mul1ProgHax).map
        (fun c => typeWordArrays (mul1Len R U) (scalarizeWordOps c)) =
      some (.RSeq (.RForRuntime "i" (.SVar "n") (mul1BodyLow R))
        (.RLetZero "carry" .TFp
          (.RSeq (.RArrLoad ⟨"carry", .TU64⟩ ⟨"rp", .TFp⟩ "n") .RSkip))) := by
  rfl

end CatCrypt.Crypto.Hax.WordOpsSim
