/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTWordOpsLoop

/-!
# The word-level runtime loop of the front, for every body of bindings and stores

A loop body the front produces for a word-level loop is a sequence of
straight-line bindings `pre` followed by store segments: each segment `(bs, y)`
is the hax statement `bindsHax bs y; ()`, lowered to
`RSeq (RSeq (bindsLow bs RSkip) RSkip)`, and the body ends in `()`, lowered to
`RSkip`. This module proves the loop simulation of `forFold_sim` for every such
body, with the per-trip obligation reduced to the side conditions `BindsOk` of
the body's bindings at each trip index, and instantiates it at `mpn_mul_1` and
`mpn_and_n`.

## Main definitions

* `segsHax`, `segsLow`, `segsBinds` — store segments in hax, lowered, and their
  bindings.
* `loopBinds`, `loopBodyHax`, `loopBodyLow` — a loop body of bindings and store
  segments.
* `loopIter` — the hax environment after `j` trips.
* `SegOk` — the name a segment returns is a related word or array.
* `mul1Segs`, `andNPre`, `andNSegs`, `andNProgHax`, `andNLen` — the `mpn_mul_1`
  and `mpn_and_n` bodies in this form.

## Main results

* `bindsNext_append`, `bindsScope_append`, `bindsOk_append` — bindings over a
  concatenation.
* `segs_sim`, `loopBody_sim` — the store segments, and one trip of the body.
* `forFold_binds_sim` — the runtime loop in `denote'` against the `semRForD`
  fold of the lowered body, for every body of bindings and store segments.
* `mul1_loop_sim'` — the statement of `mul1_loop_sim` through
  `forFold_binds_sim`.
* `andN_front_prog`, `andN_loop_sim` — the lowered `mpn_and_n` and its loop.
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
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)

/-! ### Sequences of bindings -/

theorem bindsNext_append : ∀ (bs cs : List WBind) (env : Env),
    bindsNext (bs ++ cs) env = bindsNext cs (bindsNext bs env)
  | [], _, _ => rfl
  | b :: bs, cs, env => bindsNext_append bs cs (b.next env)

theorem bindsScope_append : ∀ (bs cs : List WBind) (S : List String),
    bindsScope (bs ++ cs) S = bindsScope cs (bindsScope bs S)
  | [], _, _ => rfl
  | b :: bs, cs, S => bindsScope_append bs cs (b.written ++ S)

theorem bindsScope_append_right : ∀ (bs : List WBind) (T S : List String),
    bindsScope bs (T ++ S) = bindsScope bs T ++ S
  | [], _, _ => rfl
  | b :: bs, T, S => by
    rw [bindsScope, bindsScope, ← List.append_assoc]
    exact bindsScope_append_right bs _ S

theorem mem_bindsScope_of_nil {bs : List WBind} {y : String} (S : List String)
    (h : y ∈ bindsScope bs []) : y ∈ bindsScope bs S := by
  have := bindsScope_append_right bs [] S
  rw [List.nil_append] at this
  rw [this]
  exact List.mem_append_left _ h

theorem mem_bindsScope_of_mem {bs : List WBind} {y : String} {S : List String}
    (h : y ∈ S) : y ∈ bindsScope bs S := by
  have := bindsScope_append_right bs [] S
  rw [List.nil_append] at this
  rw [this]
  exact List.mem_append_right _ h

theorem bindsOk_append {A : List (String × Nat)} :
    ∀ (bs cs : List WBind) (S : List String) (env : Env),
      BindsOk A (bs ++ cs) S env ↔
        BindsOk A bs S env ∧ BindsOk A cs (bindsScope bs S) (bindsNext bs env)
  | [], _, _, _ => by simp [BindsOk, bindsScope, bindsNext]
  | b :: bs, cs, S, env => by
    rw [List.cons_append, BindsOk, BindsOk, bindsOk_append bs cs, and_assoc]
    rfl

/-! ### Loop bodies of bindings and store segments -/

/-- Store segments in hax: each segment `(bs, y)` is the statement
    `bindsHax bs y; ()`, and the sequence ends in `()`. -/
def segsHax : List (List WBind × String) → ImpExpr
  | [] => .unitVal
  | s :: rest => .seq (.seq (bindsHax s.1 (.var s.2)) .unitVal) (segsHax rest)

/-- Store segments lowered: each segment is `RSeq (RSeq (bindsLow bs RSkip) RSkip)`,
    and the sequence ends in `RSkip`. -/
def segsLow : List (List WBind × String) → LowCT
  | [] => .RSkip
  | s :: rest => .RSeq (.RSeq (bindsLow s.1 .RSkip) .RSkip) (segsLow rest)

/-- The bindings of a sequence of store segments, in order. -/
def segsBinds : List (List WBind × String) → List WBind
  | [] => []
  | s :: rest => s.1 ++ segsBinds rest

/-- The bindings of a loop body: the leading bindings, then those of the
    segments. -/
def loopBinds (pre : List WBind) (segs : List (List WBind × String)) : List WBind :=
  pre ++ segsBinds segs

/-- A loop body in hax: the leading bindings, then the store segments. -/
def loopBodyHax (pre : List WBind) (segs : List (List WBind × String)) : ImpExpr :=
  bindsHax pre (segsHax segs)

/-- A loop body lowered: the leading bindings, then the store segments. -/
def loopBodyLow (pre : List WBind) (segs : List (List WBind × String)) : LowCT :=
  bindsLow pre (segsLow segs)

/-- The hax environment after `j` trips of a body with bindings `bs`, trip `k`
    run with `x ↦ k`. -/
def loopIter (bs : List WBind) (x : String) (env : Env) : Nat → Env
  | 0 => env
  | j + 1 => bindsNext bs ((loopIter bs x env j).extend x (.int j))

/-- The name a segment returns is a word its bindings write or a related array. -/
def SegOk (A : List (String × Nat)) (s : List WBind × String) : Prop :=
  s.2 ∈ bindsScope s.1 [] ∨ ∃ n, (s.2, n) ∈ A

/-- **Store segments.** A sequence of store segments whose bindings satisfy their
    side conditions returns `()` in `denote'` in `bindsNext (segsBinds segs) env`,
    and its lowering runs in `semScalar` to a related scalar environment. -/
theorem segs_sim {bi : Builtins} (hbi : WordBuiltins' bi) (A : List (String × Nat)) :
    ∀ (segs : List (List WBind × String)) (S : List String) (env : Env) (σ : SEnvScalar),
      EnvRelW env σ S A → BindsOk A (segsBinds segs) S env → (∀ s ∈ segs, SegOk A s) →
      (∀ fuel, denote' bi fuel (segsHax segs) env =
        (.val .unit, bindsNext (segsBinds segs) env)) ∧
      ∃ σ', semScalar (segsLow segs) σ = some σ' ∧
        EnvRelW (bindsNext (segsBinds segs) env) σ' (bindsScope (segsBinds segs) S) A
  | [], _, env, σ, h, _, _ =>
    ⟨fun fuel => _root_.Hax.Ascent.denote'_unitVal bi fuel env, σ, rfl, h⟩
  | s :: rest, S, env, σ, h, hok, hseg => by
    rw [segsBinds, bindsOk_append] at hok
    obtain ⟨-, σ₀, -, h₀⟩ := binds_sim hbi 0 A s.1 S env σ h hok.1 (.var s.2) .RSkip
    obtain ⟨v, hv, hc⟩ : ∃ v, bindsNext s.1 env s.2 = some v ∧ v.isControlFlow = false := by
      rcases hseg s List.mem_cons_self with hy | ⟨n, hy⟩
      · obtain ⟨m, -, he, -⟩ := h₀.word _ (mem_bindsScope_of_nil S hy)
        exact ⟨_, he, rfl⟩
      · obtain ⟨vs, -, he, -⟩ := h₀.arr _ hy
        exact ⟨_, he, rfl⟩
    obtain ⟨-, σ₁, hL, hR⟩ := segment_sim hbi 0 h hok.1 s.2 ⟨v, hv⟩ .unitVal (segsLow rest)
    obtain ⟨i1, σ₂, i2, i3⟩ := segs_sim hbi A rest _ _ σ₁ hR hok.2
      (fun s' hs' => hseg s' (List.mem_cons_of_mem _ hs'))
    refine ⟨fun fuel => ?_, σ₂, hL.trans i2, ?_⟩
    · rw [segsHax, segment_run' hbi fuel h hok.1 hv hc, i1 fuel, segsBinds, bindsNext_append]
    · rw [segsBinds, bindsNext_append, bindsScope_append]
      exact i3

/-- **One trip of a loop body.** From environments related on `S` and `A`, with
    `x` neither a temporary nor an array name and `j < 2^64`, when the body's
    bindings satisfy their side conditions from `x ↦ j`, the hax body returns `()`
    in `bindsNext (loopBinds pre segs)`, the lowered body with `x` bound to the
    word `j` succeeds, and the results are related on `S` and `A`. -/
theorem loopBody_sim {bi : Builtins} (hbi : WordBuiltins' bi) {A : List (String × Nat)}
    {S : List String} {x : String} {env : Env} {σ : SEnvScalar} {j : Nat}
    {pre : List WBind} {segs : List (List WBind × String)} (h : EnvRelW env σ S A)
    (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x) (hj : j < 2 ^ 64)
    (hseg : ∀ s ∈ segs, SegOk A s)
    (hok : BindsOk A (loopBinds pre segs) (x :: S) (env.extend x (.int j))) :
    ∃ σ', (∀ fuel, denote' bi fuel (loopBodyHax pre segs) (env.extend x (.int j)) =
        (.val .unit, bindsNext (loopBinds pre segs) (env.extend x (.int j)))) ∧
      semScalar (loopBodyLow pre segs) (σ.upd x (t := .sword 64) (BitVec.ofNat 64 j)) =
        some σ' ∧
      EnvRelW (bindsNext (loopBinds pre segs) (env.extend x (.int j))) σ' S A := by
  have hi : EnvRelW (env.extend x (.int j)) (σ.upd x (t := .sword 64) (BitVec.ofNat 64 j))
      (x :: S) A :=
    h.update x hxT hxA (fun y hy => extend_ne _ hy) (fun y hy _ => upd_ne _ hy)
      ⟨j, hj, extend_self _, upd_self _⟩
  rw [loopBinds, bindsOk_append] at hok
  obtain ⟨-, σ₁, hL1, hR1⟩ := binds_sim hbi 0 A pre _ _ _ hi hok.1 .unitVal (segsLow segs)
  obtain ⟨s1, σ₂, s2, s3⟩ := segs_sim hbi A segs _ _ σ₁ hR1 hok.2 hseg
  refine ⟨σ₂, fun fuel => ?_, ?_, ?_⟩
  · rw [loopBodyHax, bindsHax_run' hbi fuel A pre _ _ _ hi hok.1, s1 fuel, loopBinds,
      bindsNext_append]
  · rw [loopBodyLow, hL1, s2]
  · rw [loopBinds, bindsNext_append]
    exact s3.mono fun y hy => mem_bindsScope_of_mem (mem_bindsScope_of_mem
      (List.mem_cons_of_mem _ hy))

/-- **The word-level runtime loop.** For a loop body of leading bindings `pre`
    and store segments `segs`, from environments related on `S` and `A`, with `x`
    neither a temporary nor an array name, `n` holding `N < 2^64` and the side
    conditions of the body's bindings holding at every trip `j < N` from the
    `j`-th iterate extended by `x ↦ j`: `forFold x 0 n` over the hax body returns
    `()` in the `N`-th iterate at every fuel `≥ N`, the `N`-trip `semRForD` fold of
    the lowered body succeeds, and the two final environments are related on `S`
    and `A`. -/
theorem forFold_binds_sim {bi : Builtins} (hbi : WordBuiltins' bi) {A : List (String × Nat)}
    {S : List String} {x n : String} {N : Nat} {pre : List WBind}
    {segs : List (List WBind × String)} {env : Env} {σ : SEnvScalar}
    (h : EnvRelW env σ S A) (hxT : ¬ isTmpName x) (hxA : ∀ p ∈ A, p.1 ≠ x)
    (hn : env n = some (.int N)) (hN : N < 2 ^ 64) (hseg : ∀ s ∈ segs, SegOk A s)
    (hok : ∀ j, j < N → BindsOk A (loopBinds pre segs) (x :: S)
      ((loopIter (loopBinds pre segs) x env j).extend x (.int j))) :
    ∃ σN,
      (∀ fuel, N ≤ fuel →
        denote' bi fuel (.forFold x (.lit (.int 0)) (.var n) (loopBodyHax pre segs)) env =
          (.val .unit, loopIter (loopBinds pre segs) x env N)) ∧
      semRForD (semScalar (loopBodyLow pre segs)) x N σ = some σN ∧
      EnvRelW (loopIter (loopBinds pre segs) x env N) σN S A := by
  obtain ⟨envN, σN, hA, hB, hC, hD⟩ := forFold_sim (bi := bi) (loopBodyHax pre segs)
    (loopBodyLow pre segs) x n N
    (fun j e s => e = loopIter (loopBinds pre segs) x env j ∧ EnvRelW e s S A)
    (fun j hj e s ⟨he, hrel⟩ => by
      subst he
      obtain ⟨σ', h1, h2, h3⟩ := loopBody_sim hbi hrel hxT hxA (by omega) hseg (hok j hj)
      exact ⟨_, σ', h1, h2, rfl, h3⟩) env σ ⟨rfl, h⟩ hn
  subst hC
  exact ⟨σN, hA, hB, hD⟩

/-! ### `mpn_mul_1` through the generic rule -/

/-- The store segments of the `mpn_mul_1` body, into an output array of `R`
    words. -/
def mul1Segs (R : Nat) : List (List WBind × String) := [(mul1St1 R, "rp"), (mul1St2 R, "rp")]

theorem mul1Next_eq_loopBinds (R : Nat) (E : Env) :
    mul1Next R E = bindsNext (loopBinds mul1Pre (mul1Segs R)) E := by
  simp only [mul1Next, loopBinds, mul1Segs, segsBinds, bindsNext_append, List.append_nil]

theorem mul1Trips_eq_loopIter (R : Nat) (env : Env) :
    ∀ N, mul1Trips R env N = loopIter (loopBinds mul1Pre (mul1Segs R)) "i" env N
  | 0 => rfl
  | N + 1 => by
    rw [mul1Trips, loopIter, mul1Trips_eq_loopIter R env N, mul1Next_eq_loopBinds]

/-- The side conditions of the `mpn_mul_1` body at a trip index `j` with `j + 1`
    inside `rp` and `j` inside `up`. -/
theorem mul1Binds_ok {R U j : Nat} (hR : j + 1 < R) (hU : j < U) (h64 : j + 1 < 2 ^ 64)
    (E : Env) :
    BindsOk [("rp", R), ("up", U)] (loopBinds mul1Pre (mul1Segs R)) ["i", "v", "ONES", "n"]
      (E.extend "i" (.int j)) := by
  have hiN : natOf (E.extend "i" (.int j)) "i" = j := natOf_extend_int _ _ _
  have hiN1 : natOf (bindsNext mul1Pre (E.extend "i" (.int j))) "i" = j := by
    rw [natOf_congr (bindsNext_ne _ _ (by decide)), hiN]
  have hiN2 : natOf (bindsNext (mul1St1 R) (bindsNext mul1Pre (E.extend "i" (.int j)))) "i" =
      j := by
    rw [natOf_congr (bindsNext_ne _ _ (by simp [mul1St1, WBind.target])), hiN1]
  simp only [loopBinds, mul1Segs, segsBinds, List.append_nil, bindsOk_append]
  exact ⟨mul1Pre_ok R U j _ (by omega) hU hiN,
    mul1St1_ok (by decide) (by decide) hiN1 (by omega),
    mul1St2_ok (by simp [bindsScope, mul1St1, mul1Pre, WBind.written])
      (by simp [bindsScope, mul1St1, mul1Pre, WBind.written]) hiN2 hR h64⟩

/-- **The `mpn_mul_1` loop through `forFold_binds_sim`.** The statement of
    `mul1_loop_sim`. -/
theorem mul1_loop_sim' {bi : Builtins} (hbi : WordBuiltins' bi) {R U N : Nat} (hR : N + 1 ≤ R)
    (hU : N ≤ U) (h64 : N + 1 < 2 ^ 64) {env : Env} {σ : SEnvScalar}
    (h : EnvRelW env σ ["v", "ONES", "n"] [("rp", R), ("up", U)]) (hn : natOf env "n" = N) :
    ∃ σN,
      (∀ fuel, N ≤ fuel → denote' bi fuel (.forFold "i" (.lit (.int 0)) (.var "n") mul1BodyHax)
        env = (.val .unit, mul1Trips R env N)) ∧
      semRForD (semScalar (mul1BodyLow R)) "i" N σ = some σN ∧
      EnvRelW (mul1Trips R env N) σN ["v", "ONES", "n"] [("rp", R), ("up", U)] := by
  have hnE : env "n" = some (.int N) := by
    rw [← hn]; exact ((h.word "n" (by simp)).natOf_eq).2.1
  have hseg : ∀ s ∈ mul1Segs R, SegOk [("rp", R), ("up", U)] s := by
    intro s hs
    simp only [mul1Segs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact Or.inr ⟨R, by simp⟩
  have hbody : mul1BodyHax = loopBodyHax mul1Pre (mul1Segs R) := rfl
  rw [hbody, mul1Trips_eq_loopIter]
  exact forFold_binds_sim (pre := mul1Pre) (segs := mul1Segs R) hbi h (nt_short (by decide))
    (mul1A_ne (by decide) (by decide)) hnE (by omega) hseg
    (fun j hj => mul1Binds_ok (by omega) (by omega) (by omega) _)

/-! ### `mpn_and_n` through the generic rule -/

/-- The loads of the `mpn_and_n` loop body. -/
def andNPre : List WBind := [.load "a" "up" "i" .TFp .TFp, .load "b" "vp" "i" .TFp .TFp]

/-- The store segment `rp[i] = a & b` of the `mpn_and_n` loop body, into an
    output array of `R` words. -/
def andNSegs (R : Nat) : List (List WBind × String) :=
  [([.word "__anorm_0" "BitAnd#64" "a" "b",
      .store "rp" "i" "__anorm_0" (.TBytes (8 * R)) (.TBytes 0)], "rp")]

/-- The A-normalised hax `mpn_and_n`: the argument rebindings, the loop, and the
    return of `rp`. -/
def andNProgHax : ImpExpr :=
  .letBind "rp" (.var "rp") (.letBind "up" (.var "up") (.letBind "vp" (.var "vp")
    (.letBind "n" (.var "n") (.letBind "rp" (.var "rp")
      (.seq (.forFold "i" (.lit (.int 0)) (.var "n") (loopBodyHax andNPre (andNSegs 0)))
        (.var "rp"))))))

/-- The array-length table of `mpn_and_n`: `rp` of `R` words, `up` of `U` and `vp`
    of `V`. -/
def andNLen (R U V : Nat) : String → Option Nat :=
  fun a => if a = "rp" then some R else if a = "up" then some U else if a = "vp" then some V
    else none

/-- The lowered and retyped `mpn_and_n`: the runtime loop over the retyped body,
    then the return of `rp`. -/
theorem andN_front_prog (R U V : Nat) :
    (haxToLowCT andNProgHax).map
        (fun c => typeWordArrays (andNLen R U V) (scalarizeWordOps c)) =
      some (.RSeq (.RForRuntime "i" (.SVar "n") (loopBodyLow andNPre (andNSegs R))) .RSkip) := by
  rfl

/-- The side conditions of the `mpn_and_n` body at a trip index `j` inside the
    three arrays. -/
theorem andNBinds_ok {R U V j : Nat} (hR : j < R) (hU : j < U) (hV : j < V) (E : Env) :
    BindsOk [("rp", R), ("up", U), ("vp", V)] (loopBinds andNPre (andNSegs R)) ["i"]
      (E.extend "i" (.int j)) := by
  have a0 : ¬ isTmpName "__anorm_0" := notTmp_of_thirdNe (s := "__anorm_0") rfl (by decide)
  have hiN : natOf (E.extend "i" (.int j)) "i" = j := natOf_extend_int _ _ _
  have hiN1 : natOf (bindsNext [.load "a" "up" "i" .TFp .TFp] (E.extend "i" (.int j))) "i" = j :=
    by rw [natOf_congr (bindsNext_ne _ _ (by decide)), hiN]
  have hiN2 : natOf (bindsNext andNPre (E.extend "i" (.int j))) "i" = j := by
    rw [natOf_congr (bindsNext_ne _ _ (by decide)), hiN]
  have hiN3 : natOf (bindsNext (andNPre ++ [.word "__anorm_0" "BitAnd#64" "a" "b"])
      (E.extend "i" (.int j))) "i" = j := by
    rw [natOf_congr (bindsNext_ne _ _ (by decide)), hiN]
  exact ⟨⟨by decide, nt_short (by decide), by simp, U, by simp, by rw [hiN]; exact hU⟩,
    ⟨by decide, nt_short (by decide), by simp, V, by simp, hiN1 ▸ hV⟩,
    WBind.ok_word (by decide) (by decide) a0 (by simp),
    ⟨by decide, by decide, R, by simp, encodeTy_TBytes_eight_mul R, hiN3 ▸ hR⟩, trivial⟩

/-- **The `mpn_and_n` loop.** From environments related on the arrays `rp` (`R`
    words), `up` (`U`) and `vp` (`V`), with `n` holding `N ≤ R, U, V` and
    `N < 2^64`: the hax loop over the A-normalised body returns `()` in the `N`-th
    iterate at every fuel `≥ N`, the `N`-trip `semScalar` fold of the retyped
    lowered body succeeds, and the two final environments are related on the
    three arrays. -/
theorem andN_loop_sim {bi : Builtins} (hbi : WordBuiltins' bi) {R U V N : Nat} (hR : N ≤ R)
    (hU : N ≤ U) (hV : N ≤ V) (h64 : N < 2 ^ 64) {env : Env} {σ : SEnvScalar}
    (h : EnvRelW env σ [] [("rp", R), ("up", U), ("vp", V)]) (hn : env "n" = some (.int N)) :
    ∃ σN,
      (∀ fuel, N ≤ fuel → denote' bi fuel
        (.forFold "i" (.lit (.int 0)) (.var "n") (loopBodyHax andNPre (andNSegs 0))) env =
          (.val .unit, loopIter (loopBinds andNPre (andNSegs R)) "i" env N)) ∧
      semRForD (semScalar (loopBodyLow andNPre (andNSegs R))) "i" N σ = some σN ∧
      EnvRelW (loopIter (loopBinds andNPre (andNSegs R)) "i" env N) σN []
        [("rp", R), ("up", U), ("vp", V)] :=
  forFold_binds_sim (pre := andNPre) (segs := andNSegs R) hbi h (nt_short (by decide))
    (by simp) hn h64 (fun s hs => by
      simp only [andNSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      exact Or.inr ⟨R, by simp⟩)
    (fun j hj => andNBinds_ok (by omega) (by omega) (by omega) _)

end CatCrypt.Crypto.Hax.WordOpsSim
