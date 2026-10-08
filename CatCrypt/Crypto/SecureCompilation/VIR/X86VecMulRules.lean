/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X86VecPeephole
public import CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86

/-!
# Fusion of dword multiplies with the even and odd 64-bit products

Rules of the generic acyclic e-graph (`AegraphGeneric.Rule`) on the dialect `jasminVec`,
each reading the definition table of the pass. They relate the dword product
`lw 32 (bin mul)` (`vpmulld`) and the selected unsigned high multiply
`TileSelectX86.mulhuBlk` to the two 64-bit products `vpmuludq a b` (the even product) and
`vpmuludq (vmovshdup a) (vmovshdup b)` (the odd product) of sixteen dwords.

Two relations on 512-bit values carry the proofs: `EvenAgree u v`, the even dwords of `u`
are those of `v`, and `OddIn u v`, the even dwords of `u` are the odd dwords of `v`. A
`vpmuludq` reads the even dwords of its operands only (`mulq_congr`). The resolver
`evenSrc` returns, for a variable bound to a dword product whose even product is bound,
the variable of the even product; `oddSrc` returns the variable of the odd product, and a
dword broadcast constant itself.

* `pairLoRule`: a dword product `lw 32 (bin mul) a b` whose even product `E` and odd
  product `O` are bound gets the form `blend 0xAAAA (dup false O) E`.
* `evenMulRule`: `muludq v z` with `v` bound to `lw 32 (bin mul) x y` gets the form
  `muludq (muludq x' y') z` for `x' = evenSrc x`, `y' = evenSrc y`.
* `oddMulRule`: `muludq v z` with `v` bound to `dup true w` and `w` bound to
  `lw 32 (bin mul) x y` gets the form `muludq (muludq X Y) z` for `oddSrc x = some X`,
  `oddSrc y = some Y`.
* `dupBcstRule`: `dup odd v` with `v` bound to `bcst 32 c` gets the form `bcst 32 c`.

On the Montgomery step `lo = a·b`, `hi = mulhi(a, b)`, `m = lo·μ`, `u = mulhi(m, p)`,
`d = hi - u` after selection, `evenMulRule` and `oddMulRule` offer for the two products of
`u` the forms `muludq (muludq E μ) p` and `muludq (muludq O μ) p'` on the products `E`, `O`
of `hi` (`mont_offers`), six `vpmuludq` in all.

The lemma `montSub_inside` moves the dword subtraction of two merged high halves inside as
two 64-bit subtractions, for a subtrahend `muludq (muludq X c₁) c₂` with `c₁·c₂ = 1` on the
even dwords. Its right-hand side has three bindings, and an alternative (`Alt`) holds at
most two.

The traits `mulFuseTraits` are `vecFusionTraits` with the dword multiply at cost `5` and
the dword broadcast constant-like. The rule set `vecMulFusions` has these traits and the
rules of `vecFusions` followed by those of `mulRules`.

## Main definitions

* `EvenAgree`, `OddIn`: the two relations on the dwords of 512-bit values.
* `lopNode?`, `lopAt?`, `dupNode?`, `bcstNode?`: a node of the definition table read as a
  lane-wise operation, a dword duplication or a broadcast constant.
* `nodeLvl?`, `evenProdVar`, `oddProdVar`: the level of a recorded node satisfying a
  predicate, and the variables of the even and the odd product of two variables.
* `evenSrc`, `oddSrc`: the two resolvers.
* `pairLoRule`, `evenMulRule`, `oddMulRule`, `dupBcstRule`: the rules.
* `mulFuseTraits`, `mulRules`, `vecMulFusions`: the traits and the rule sets.
* `mulFuse`, `mulFuseStep`: the pass `aegraphOptNF mulRules` and its chain step.

## Main results

* `mulq_congr`: a `vpmuludq` depends on the even dwords of its operands only.
* `pair_low`: a value is the blend of the low dwords of its even and its odd product.
* `montSub_inside`: the dword difference of two merged high halves as the merge of two
  64-bit differences.
* `pairLoAt_sound`, `evenMulAt_sound`, `oddMulAt_sound`, `dupBcstAt_sound`: an alternative
  of a rule denotes the expression.
* `mulFuse_denote`: the pass preserves the denotation at every fuel.
* `mulFuseCert`: the certificate of the chain step, with equality as both relations.
* `traverse_events`: for a rule set whose extraction returns one or two bindings with the
  events of the input binding, the traversal has the leakage run of its input.
* `mulFuse_leakRun`, `vecMulFusions_leakRun`: the pass runs to the results and the events
  of its input.
* `pairAlt_cost`, `bcst_key`, `innerMul_cost`: the costs of the fused forms under
  `mulFuseTraits`.
* `mont_offers`: on the Montgomery step the rules offer the forms on the products of the
  high multiply.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X86VecMulRules

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecDialect
open CatCrypt.Crypto.SecureCompilation.VIR.X86VecPeephole
open CatCrypt.Crypto.SecureCompilation.VIR.TileSelectX86 (lane_inj512 isShape_dword
  isShape_qword lookup_here lookup_there)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp wr lane ofLanes lane_ofLanes
  semLW semDup semMerge bcast lane_semLW lane_semDup lane_semMerge lane32_even)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (prod_lanes maskAAAA muludq_lo
  montSub_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel Labels)
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.Optimizer.Rewrite
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric (varLvl getLvl_var varOfLvl? varOfDepth?
  varOfLvl?_lookup argLvls evalKey evalKey_expr DSound Alt Rule RuleSet Defs)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF (aegraphOptNF aegraphOptNF_denote)
open Ctxt (Var Valuation)

/-! ## 1. Even and odd dwords -/

/-- `EvenAgree u v`: the even dwords of `u` are the even dwords of `v`. -/
def EvenAgree (u v : BitVec 512) : Prop :=
  ∀ i, i < 8 → lane 32 u (2 * i) = lane 32 v (2 * i)

/-- `OddIn u v`: the even dwords of `u` are the odd dwords of `v`. -/
def OddIn (u v : BitVec 512) : Prop :=
  ∀ i, i < 8 → lane 32 u (2 * i) = lane 32 v (2 * i + 1)

/-- Dword `2i` of `vmovshdup` is dword `2i+1` of its operand. -/
theorem dup_even (w : BitVec 512) {i : Nat} (hi : i < 8) :
    lane 32 (semDup true w) (2 * i) = lane 32 w (2 * i + 1) := by
  rw [lane_semDup _ _ (by omega), if_pos rfl]
  congr 1
  omega

/-- Dword `2i+1` of `vmovsldup` is dword `2i` of its operand. -/
theorem dupLow_odd (w : BitVec 512) {i : Nat} (hi : i < 8) :
    lane 32 (semDup false w) (2 * i + 1) = lane 32 w (2 * i) := by
  rw [lane_semDup _ _ (by omega), if_neg (by decide)]
  congr 1
  omega

/-- Dword `j` of the dword product. -/
theorem mulw_lane (x y : BitVec 512) {j : Nat} (hj : j < 16) :
    lane 32 (semLW 32 (.bin .mul) x y) j = lane 32 x j * lane 32 y j :=
  (lane_semLW _ _ _ (by omega) (by omega)).trans rfl

/-- Dword `2i` of a `vpmuludq` is the product of the dwords `2i`. -/
theorem mulq_even (x y : BitVec 512) {i : Nat} (hi : i < 8) :
    lane 32 (semLW 64 .muludq x y) (2 * i) = lane 32 x (2 * i) * lane 32 y (2 * i) := by
  have h := muludq_lo (m := .zmm) x y (i := i) (by show 64 * i + 64 ≤ 512; omega)
  simp only [wr] at h
  exact h

/-- Dword `2i+1` of a `vpmuludq` is the high multiply of the dwords `2i`. -/
theorem mulq_odd (x y : BitVec 512) {i : Nat} (hi : i < 8) :
    lane 32 (semLW 64 .muludq x y) (2 * i + 1) =
      mulHiW (lane 32 x (2 * i)) (lane 32 y (2 * i)) := by
  have h := prod_lanes (m := .zmm) x y (semDup true y)
    (fun i' hi' => dup_even y (by have : Mode.zmm.act = 512 := rfl; omega)) i
    (by show 64 * i + 64 ≤ 512; omega)
  simp only [wr] at h
  exact h.2.1

/-- **A `vpmuludq` depends on the even dwords of its operands only.** -/
theorem mulq_congr {x x' y y' : BitVec 512} (hx : EvenAgree x x') (hy : EvenAgree y y') :
    semLW 64 .muludq x y = semLW 64 .muludq x' y' := by
  refine lane_inj512 isShape_qword _ _ fun k hk => ?_
  rw [lane_semLW _ _ _ (by omega) (by omega), lane_semLW _ _ _ (by omega) (by omega)]
  simp only [LOp.apply, ← lane32_even]
  rw [hx k hk, hy k hk]

/-- The even product has the even dwords of the dword product. -/
theorem prod_even (a b : BitVec 512) :
    EvenAgree (semLW 64 .muludq a b) (semLW 32 (.bin .mul) a b) := by
  intro i hi
  have h := prod_lanes (m := .zmm) a b (semDup true b)
    (fun i' hi' => dup_even b (by have : Mode.zmm.act = 512 := rfl; omega)) i
    (by show 64 * i + 64 ≤ 512; omega)
  simp only [wr] at h
  rw [h.1, mulw_lane _ _ (by omega)]

/-- The odd product has, in its even dwords, the odd dwords of the dword product. -/
theorem prod_odd (a b : BitVec 512) :
    OddIn (semLW 64 .muludq (semDup true a) (semDup true b)) (semLW 32 (.bin .mul) a b) := by
  intro i hi
  have h := prod_lanes (m := .zmm) a b (semDup true b)
    (fun i' hi' => dup_even b (by have : Mode.zmm.act = 512 := rfl; omega)) i
    (by show 64 * i + 64 ≤ 512; omega)
  simp only [wr] at h
  rw [h.2.2.1, mulw_lane _ _ (by omega)]

/-- Dword `j` of a dword broadcast. -/
theorem bcast_lane (c : BitVec 32) {j : Nat} (hj : j < 16) : lane 32 (bcast 32 c) j = c := by
  unfold bcast
  exact lane_ofLanes _ (by omega) (by omega)

/-- A dword duplication of a dword broadcast is the broadcast. -/
theorem dup_bcast (odd : Bool) (c : BitVec 32) : semDup odd (bcast 32 c) = bcast 32 c := by
  refine lane_inj512 isShape_dword _ _ fun j hj => ?_
  cases odd
  · rw [lane_semDup _ _ hj, if_neg (by decide), bcast_lane _ (by omega), bcast_lane _ hj]
  · rw [lane_semDup _ _ hj, if_pos rfl, bcast_lane _ (by omega), bcast_lane _ hj]

/-- **A value from its even and its odd product**: the even dwords of `E` and, in the odd
    dwords, the even dwords of `O` moved up by `vmovsldup`. -/
theorem pair_low {E O v : BitVec 512} (hE : EvenAgree E v) (hO : OddIn O v) :
    semMerge 0xAAAA#16 (semDup false O) E = v := by
  refine lane_inj512 isShape_dword _ _ fun j hj => ?_
  rw [lane_semMerge _ _ _ hj]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have hi : i < 8 := by omega
    rw [(maskAAAA i hi).1, if_neg (by decide)]
    exact hE i hi
  · have hi : i < 8 := by omega
    rw [(maskAAAA i hi).2, if_pos rfl, dupLow_odd _ hi]
    exact hO i hi

/-- The inner product of a `vpmuludq` on a dword product, from operands with the even
    dwords of the factors. -/
theorem inner_even {X Y x y : BitVec 512} (hX : EvenAgree X x) (hY : EvenAgree Y y)
    (z : BitVec 512) :
    semLW 64 .muludq (semLW 64 .muludq X Y) z =
      semLW 64 .muludq (semLW 32 (.bin .mul) x y) z :=
  mulq_congr (fun i hi => by
    rw [mulq_even _ _ hi, mulw_lane _ _ (by omega), hX i hi, hY i hi]) (fun _ _ => rfl)

/-- The inner product of a `vpmuludq` on the odd dwords of a dword product, from operands
    with the odd dwords of the factors in their even dwords. -/
theorem inner_odd {X Y x y : BitVec 512} (hX : OddIn X x) (hY : OddIn Y y) (z : BitVec 512) :
    semLW 64 .muludq (semLW 64 .muludq X Y) z =
      semLW 64 .muludq (semDup true (semLW 32 (.bin .mul) x y)) z :=
  mulq_congr (fun i hi => by
    rw [mulq_even _ _ hi, dup_even _ hi, mulw_lane _ _ (by omega), hX i hi, hY i hi])
    (fun _ _ => rfl)

/-- The high dword of the 64-bit difference of a product and its Montgomery multiple is
    the difference of the high dwords, when `c1·c2 = 1` on the even dword. -/
theorem sub_high (a b c1 c2 : BitVec 512) {i : Nat} (hi : i < 8)
    (hinv : lane 32 c1 (2 * i) * lane 32 c2 (2 * i) = 1) :
    lane 32 (semLW 64 (.bin .sub) (semLW 64 .muludq a b)
        (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a b) c1) c2)) (2 * i + 1) =
      lane 32 (semLW 64 .muludq a b) (2 * i + 1) -
        lane 32 (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a b) c1) c2)
          (2 * i + 1) := by
  rw [mulq_odd _ _ hi, mulq_odd _ _ hi, mulq_even _ _ hi, mulq_even _ _ hi]
  have h := montSub_lane (m := .zmm) a b c1 c2 (i := i) (by show 64 * i + 64 ≤ 512; omega) hinv
  simp only [wr] at h
  exact h

/-- **The subtraction of two merged high halves, moved inside.** For the even product
    `E = muludq a b`, the odd product `O = muludq a' b'` and constants with `c1·c2 = 1` on
    the even dwords, the dword difference of the merged high halves of `E`, `O` and of
    their Montgomery multiples is the merge of the high halves of the two 64-bit
    differences. -/
theorem montSub_inside (a b a' b' c1 c2 : BitVec 512)
    (hinv : ∀ i, i < 8 → lane 32 c1 (2 * i) * lane 32 c2 (2 * i) = 1) :
    semLW 32 (.bin .sub)
        (semMerge 0xAAAA#16 (semLW 64 .muludq a' b') (semDup true (semLW 64 .muludq a b)))
        (semMerge 0xAAAA#16
          (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a' b') c1) c2)
          (semDup true (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a b) c1) c2)))
      = semMerge 0xAAAA#16
          (semLW 64 (.bin .sub) (semLW 64 .muludq a' b')
            (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a' b') c1) c2))
          (semDup true (semLW 64 (.bin .sub) (semLW 64 .muludq a b)
            (semLW 64 .muludq (semLW 64 .muludq (semLW 64 .muludq a b) c1) c2))) := by
  refine lane_inj512 isShape_dword _ _ fun j hj => ?_
  rw [lane_semLW _ _ _ (by omega) (by omega), lane_semMerge _ _ _ hj, lane_semMerge _ _ _ hj,
    lane_semMerge _ _ _ hj]
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have hi : i < 8 := by omega
    rw [(maskAAAA i hi).1]
    simp only [Bool.false_eq_true, if_false]
    rw [dup_even _ hi, dup_even _ hi, dup_even _ hi, sub_high a b c1 c2 hi (hinv i hi)]
    rfl
  · have hi : i < 8 := by omega
    rw [(maskAAAA i hi).2]
    simp only [if_true]
    rw [sub_high a' b' c1 c2 hi (hinv i hi)]
    rfl

/-! ## 2. Nodes of the definition table -/

section Nodes

variable {Δ : Ctxt jasminVec}

/-- The de Bruijn index of the variable `varOfDepth?` returns. -/
theorem varDepth_of_depth : ∀ {Δ : Ctxt jasminVec} {s : JasminTy} {k : Nat} {w : Var Δ s},
    varOfDepth? Δ s k = some w → varDepth w = k
  | [], _, _, _, h => by simp [varOfDepth?] at h
  | t :: Δ, s, 0, w, h => by
      unfold varOfDepth? at h
      split at h
      · rename_i hts
        subst hts
        cases h
        rfl
      · cases h
  | t :: Δ, s, k + 1, w, h => by
      unfold varOfDepth? at h
      obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp h
      show varDepth w' + 1 = k + 1
      rw [varDepth_of_depth hw']

/-- The level of the variable `varOfLvl?` returns. -/
theorem varLvl_of_lvl {s : JasminTy} {l : Nat} {w : Var Δ s}
    (h : varOfLvl? Δ s l = some w) : varLvl w = l := by
  unfold varOfLvl? at h
  split at h
  · rename_i hl
    unfold varLvl
    rw [varDepth_of_depth h]
    omega
  · cases h

/-- The value of the variable at the level of a recorded node is the value of the node. -/
theorem lookup_of_lvl {V : Valuation Δ} {D : Defs jasminVec} (hD : DSound V D) {l : Nat}
    {k : jasminVec.Op × List Nat} (h : D[l]? = some k) {t : JasminTy} {w : Var Δ t}
    (hw : varOfLvl? Δ t l = some w) {v : ⟦t⟧} (hk : evalKey V k.1 k.2 = some ⟨t, v⟩) :
    w.lookup V = v := by
  obtain ⟨x, h1, h2⟩ := hD _ _ h
  rw [varOfLvl?_lookup hw V] at h2
  rw [hk] at h1
  rw [← h1] at h2
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Option.some.inj h2)).2

/-- A node read as a lane-wise operation on two 512-bit variables: the lane width, the
    operation and the variables at its argument levels. -/
def lopNode? (Δ : Ctxt jasminVec) :
    jasminVec.Op × List Nat → Option (Nat × LOp × Var Δ VReg × Var Δ VReg)
  | (.inr (.lw .zmm L o), [l1, l2]) =>
      match varOfLvl? Δ VReg l1, varOfLvl? Δ VReg l2 with
      | some a1, some a2 => some (L, o, a1, a2)
      | _, _ => none
  | _ => none

/-- The node `lopNode?` reads evaluates to the lane-wise operation on the variables. -/
theorem lopNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {L : Nat} {o : LOp}
    {a1 a2 : Var Δ VReg} (h : lopNode? Δ k = some (L, o, a1, a2)) :
    evalKey V k.1 k.2 = some ⟨VReg, semLW L o (a1.lookup V) (a2.lookup V)⟩ := by
  unfold lopNode? at h
  split at h
  · rename_i L' o' l1 l2
    split at h
    · rename_i b1 b2 hb1 hb2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      obtain rfl := varLvl_of_lvl hb1
      obtain rfl := varLvl_of_lvl hb2
      have he := evalKey_expr (lwE L' o' b1 b2) V
      rw [lwE_denote] at he
      exact he
    · cases h
  · cases h

/-- A node read as the lane-wise operation `o` at the width `L` on two variables. -/
def lopAt? (Δ : Ctxt jasminVec) (L : Nat) (o : LOp) (k : jasminVec.Op × List Nat) :
    Option (Var Δ VReg × Var Δ VReg) :=
  match lopNode? Δ k with
  | some (L', o', a, b) => if L' = L ∧ o' = o then some (a, b) else none
  | none => none

/-- The node `lopAt?` reads evaluates to the lane-wise operation on the variables. -/
theorem lopAt?_sound (V : Valuation Δ) {L : Nat} {o : LOp} {k : jasminVec.Op × List Nat}
    {a b : Var Δ VReg} (h : lopAt? Δ L o k = some (a, b)) :
    evalKey V k.1 k.2 = some ⟨VReg, semLW L o (a.lookup V) (b.lookup V)⟩ := by
  unfold lopAt? at h
  split at h
  · rename_i L' o' a' b' hn
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact lopNode?_sound V hn
    · cases h
  · cases h

/-- A node read as a dword duplication of a 512-bit variable. -/
def dupNode? (Δ : Ctxt jasminVec) : jasminVec.Op × List Nat → Option (Bool × Var Δ VReg)
  | (.inr (.dup .zmm odd), [l]) => (varOfLvl? Δ VReg l).map fun a => (odd, a)
  | _ => none

/-- The node `dupNode?` reads evaluates to the duplication of the variable. -/
theorem dupNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {odd : Bool}
    {a : Var Δ VReg} (h : dupNode? Δ k = some (odd, a)) :
    evalKey V k.1 k.2 = some ⟨VReg, semDup odd (a.lookup V)⟩ := by
  unfold dupNode? at h
  split at h
  · rename_i odd' l
    obtain ⟨a', ha', h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain rfl := varLvl_of_lvl ha'
    have he := evalKey_expr (dupE odd' a') V
    rw [dupE_denote] at he
    exact he
  · cases h

/-- A node read as a broadcast constant: the lane width and the constant. -/
def bcstNode? : jasminVec.Op × List Nat → Option (Nat × Nat)
  | (.inr (.bcst .zmm L c), []) => some (L, c)
  | _ => none

/-- The node `bcstNode?` reads evaluates to the broadcast. -/
theorem bcstNode?_sound (V : Valuation Δ) {k : jasminVec.Op × List Nat} {L c : Nat}
    (h : bcstNode? k = some (L, c)) :
    evalKey V k.1 k.2 = some ⟨VReg, bcast L (BitVec.ofNat L c)⟩ := by
  unfold bcstNode? at h
  split at h
  · rename_i L' c'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have he := evalKey_expr (bcstE L' c' : Expr jasminVec Δ VReg) V
    rw [bcstE_denote] at he
    exact he
  · cases h

/-- The level of a recorded node that satisfies `p`. -/
def nodeLvl? (D : Defs jasminVec) (p : jasminVec.Op × List Nat → Bool) : Option Nat :=
  (D.toList.find? fun kv => p kv.2).map Prod.fst

/-- The level `nodeLvl?` returns holds a node that satisfies the predicate. -/
theorem nodeLvl?_spec {D : Defs jasminVec} {p : jasminVec.Op × List Nat → Bool} {l : Nat}
    (h : nodeLvl? D p = some l) : ∃ k, D[l]? = some k ∧ p k = true := by
  obtain ⟨⟨l', k⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp : p k = true :=
    List.find?_some (p := fun kv : Nat × jasminVec.Op × List Nat => p kv.2) hf
  exact ⟨k, Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (List.mem_of_find?_eq_some hf), hp⟩

/-- The node of the even product `vpmuludq a b`. -/
def evenKey (a b : Var Δ VReg) : jasminVec.Op × List Nat :=
  (.inr (.lw .zmm 64 .muludq), [varLvl a, varLvl b])

/-- The node of `vmovshdup a`. -/
def dupKey (a : Var Δ VReg) : jasminVec.Op × List Nat :=
  (.inr (.dup .zmm true), [varLvl a])

/-- The variable bound to the even product `vpmuludq a b`. -/
def evenProdVar (D : Defs jasminVec) (a b : Var Δ VReg) : Option (Var Δ VReg) :=
  (nodeLvl? D fun k => decide (k = evenKey a b)).bind (varOfLvl? Δ VReg)

/-- The predicate of the node of the odd product: a `vpmuludq` of two variables bound to
    `vmovshdup a` and `vmovshdup b`. -/
def isOddProd (D : Defs jasminVec) (a b : Var Δ VReg) (k : jasminVec.Op × List Nat) : Bool :=
  match lopAt? Δ 64 .muludq k with
  | some (d1, d2) =>
      decide (D[varLvl d1]? = some (dupKey a)) && decide (D[varLvl d2]? = some (dupKey b))
  | none => false

/-- The variable bound to the odd product `vpmuludq (vmovshdup a) (vmovshdup b)`. -/
def oddProdVar (D : Defs jasminVec) (a b : Var Δ VReg) : Option (Var Δ VReg) :=
  (nodeLvl? D (isOddProd D a b)).bind (varOfLvl? Δ VReg)

variable {D : Defs jasminVec} {V : Valuation Δ}

/-- The variable `evenProdVar` returns holds the even product. -/
theorem evenProdVar_sound (hD : DSound V D) {a b E : Var Δ VReg}
    (h : evenProdVar D a b = some E) :
    E.lookup V = semLW 64 .muludq (a.lookup V) (b.lookup V) := by
  obtain ⟨l, hl, hE⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨k, hk, hp⟩ := nodeLvl?_spec hl
  obtain rfl := of_decide_eq_true hp
  refine lookup_of_lvl hD hk hE ?_
  have he := evalKey_expr (lwE 64 .muludq a b) V
  rw [lwE_denote] at he
  exact he

/-- The variable `oddProdVar` returns holds the odd product. -/
theorem oddProdVar_sound (hD : DSound V D) {a b O : Var Δ VReg}
    (h : oddProdVar D a b = some O) :
    O.lookup V = semLW 64 .muludq (semDup true (a.lookup V)) (semDup true (b.lookup V)) := by
  obtain ⟨l, hl, hO⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨k, hk, hp⟩ := nodeLvl?_spec hl
  unfold isOddProd at hp
  split at hp
  · rename_i d1 d2 hn
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    have hdup : ∀ c : Var Δ VReg, evalKey V (dupKey c).1 (dupKey c).2
        = some ⟨VReg, semDup true (c.lookup V)⟩ := by
      intro c
      have he := evalKey_expr (dupE true c) V
      rw [dupE_denote] at he
      exact he
    rw [← lookup_of_node hD d1 hp.1 (hdup a), ← lookup_of_node hD d2 hp.2 (hdup b)]
    exact lookup_of_lvl hD hk hO (lopAt?_sound V hn)
  · cases hp

/-- A variable with the even dwords of `x`: the variable of the even product of `a`, `b`
    when `x` is bound to their dword product and the even product is bound, else `x`. -/
def evenSrc (D : Defs jasminVec) (x : Var Δ VReg) : Var Δ VReg :=
  match (D[varLvl x]?).bind (lopAt? Δ 32 (.bin .mul)) with
  | some (a, b) => (evenProdVar D a b).getD x
  | none => x

/-- A variable whose even dwords are the odd dwords of `x`: `x` itself when it is bound to
    a dword broadcast, and the variable of the odd product of `a`, `b` when `x` is bound
    to their dword product. -/
def oddSrc (D : Defs jasminVec) (x : Var Δ VReg) : Option (Var Δ VReg) :=
  (D[varLvl x]?).bind fun k =>
    match bcstNode? k with
    | some (L, _) => if L = 32 then some x else none
    | none => (lopAt? Δ 32 (.bin .mul) k).bind fun ab => oddProdVar D ab.1 ab.2

/-- The variable `evenSrc` returns has the even dwords of `x`. -/
theorem evenSrc_sound (hD : DSound V D) (x : Var Δ VReg) :
    EvenAgree ((evenSrc D x).lookup V) (x.lookup V) := by
  unfold evenSrc
  split
  · rename_i a b hx
    obtain ⟨k, hk, hk'⟩ := Option.bind_eq_some_iff.mp hx
    cases hE : evenProdVar D a b with
    | none => exact fun _ _ => rfl
    | some E =>
        show EvenAgree (E.lookup V) (x.lookup V)
        rw [evenProdVar_sound hD hE, lookup_of_node hD x hk (lopAt?_sound V hk')]
        exact prod_even _ _
  · exact fun _ _ => rfl

/-- The variable `oddSrc` returns has, in its even dwords, the odd dwords of `x`. -/
theorem oddSrc_sound (hD : DSound V D) {x X : Var Δ VReg} (h : oddSrc D x = some X) :
    OddIn (X.lookup V) (x.lookup V) := by
  obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i L c hb
    split at h
    · rename_i hL
      subst hL
      cases h
      rw [lookup_of_node hD x hk (bcstNode?_sound V hb)]
      intro i hi
      rw [bcast_lane _ (by omega), bcast_lane _ (by omega)]
    · cases h
  · obtain ⟨⟨a, b⟩, hab, hO⟩ := Option.bind_eq_some_iff.mp h
    rw [oddProdVar_sound hD hO, lookup_of_node hD x hk (lopAt?_sound V hab)]
    exact prod_odd _ _

end Nodes

/-! ## 3. The alternatives of the rules -/

section Alts

variable {Δ : Ctxt jasminVec}

/-- The form `vpmuludq (vpmuludq X Y) z` for the triple `(X, Y, z)`. -/
def innerMul (t : Var Δ VReg × Var Δ VReg × Var Δ VReg) : Alt Δ VReg :=
  .two (lwE 64 .muludq t.1 t.2.1) (lwE 64 .muludq .here (.there t.2.2))

/-- The form `vpblendmd 0xAAAA (vmovsldup O) E` for the pair `(E, O)`. -/
def pairAlt (t : Var Δ VReg × Var Δ VReg) : Alt Δ VReg :=
  .two (dupE false t.2) (blendE 0xAAAA#16 .here (.there t.1))

theorem innerMul_denote (t : Var Δ VReg × Var Δ VReg × Var Δ VReg) (V : Valuation Δ) :
    (innerMul t).denote V =
      semLW 64 .muludq (semLW 64 .muludq (t.1.lookup V) (t.2.1.lookup V)) (t.2.2.lookup V) := by
  simp only [innerMul, Alt.denote, lwE_denote, lookup_here, lookup_there]

theorem pairAlt_denote (t : Var Δ VReg × Var Δ VReg) (V : Valuation Δ) :
    (pairAlt t).denote V = semMerge 0xAAAA#16 (semDup false (t.2.lookup V)) (t.1.lookup V) := by
  simp only [pairAlt, Alt.denote, blendE_denote, dupE_denote, lookup_here, lookup_there]

/-- The paired multiply: for a dword product of `a`, `b` whose even and odd products are
    bound, the variables of the two products. -/
def pairLo? (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) :
    Option (Var Δ VReg × Var Δ VReg) :=
  (lopAt? Δ 32 (.bin .mul) (e.op, argLvls e.args)).bind fun ab =>
    (evenProdVar D ab.1 ab.2).bind fun E => (oddProdVar D ab.1 ab.2).map fun O => (E, O)

/-- The inner even product: for `vpmuludq v z` with `v` bound to the dword product of `x`,
    `y`, the variables with the even dwords of `x` and `y`, and `z`. -/
def evenMul? (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) :
    Option (Var Δ VReg × Var Δ VReg × Var Δ VReg) :=
  (lopAt? Δ 64 .muludq (e.op, argLvls e.args)).bind fun vz =>
    ((D[varLvl vz.1]?).bind (lopAt? Δ 32 (.bin .mul))).map fun xy =>
      (evenSrc D xy.1, evenSrc D xy.2, vz.2)

/-- The inner odd product: for `vpmuludq v z` with `v` bound to `vmovshdup w` and `w` bound
    to the dword product of `x`, `y`, the variables whose even dwords are the odd dwords of
    `x` and `y`, and `z`. -/
def oddMul? (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) :
    Option (Var Δ VReg × Var Δ VReg × Var Δ VReg) :=
  (lopAt? Δ 64 .muludq (e.op, argLvls e.args)).bind fun vz =>
    ((D[varLvl vz.1]?).bind (dupNode? Δ)).bind fun ow =>
      if ow.1 = true then
        ((D[varLvl ow.2]?).bind (lopAt? Δ 32 (.bin .mul))).bind fun xy =>
          (oddSrc D xy.1).bind fun X => (oddSrc D xy.2).map fun Y => (X, Y, vz.2)
      else none

/-- The duplication of a constant: for a dword duplication of a variable bound to the
    dword broadcast of `c`, the constant `c`. -/
def dupBcst? (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : Option Nat :=
  (dupNode? Δ (e.op, argLvls e.args)).bind fun ow =>
    ((D[varLvl ow.2]?).bind bcstNode?).bind fun Lc => if Lc.1 = 32 then some Lc.2 else none

variable {D : Defs jasminVec} {V : Valuation Δ}

theorem pairLo?_spec (hD : DSound V D) (e : Expr jasminVec Δ VReg)
    {t : Var Δ VReg × Var Δ VReg} (h : pairLo? D e = some t) :
    (pairAlt t).denote V = e.denote V := by
  obtain ⟨⟨a, b⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨E, hE, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨O, hO, rfl⟩ := Option.map_eq_some_iff.mp h
  dsimp only at hE hO
  rw [pairAlt_denote, denote_of_node e (lopAt?_sound V hn)]
  dsimp only
  rw [evenProdVar_sound hD hE, oddProdVar_sound hD hO]
  exact pair_low (prod_even _ _) (prod_odd _ _)

theorem evenMul?_spec (hD : DSound V D) (e : Expr jasminVec Δ VReg)
    {t : Var Δ VReg × Var Δ VReg × Var Δ VReg} (h : evenMul? D e = some t) :
    (innerMul t).denote V = e.denote V := by
  obtain ⟨⟨v, z⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨x, y⟩, hv, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨k, hk, hk'⟩ := Option.bind_eq_some_iff.mp hv
  dsimp only at hk
  rw [innerMul_denote, denote_of_node e (lopAt?_sound V hn),
    lookup_of_node hD v hk (lopAt?_sound V hk')]
  exact inner_even (evenSrc_sound hD x) (evenSrc_sound hD y) _

theorem oddMul?_spec (hD : DSound V D) (e : Expr jasminVec Δ VReg)
    {t : Var Δ VReg × Var Δ VReg × Var Δ VReg} (h : oddMul? D e = some t) :
    (innerMul t).denote V = e.denote V := by
  obtain ⟨⟨v, z⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨odd, w⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨kv, hkv, hkv'⟩ := Option.bind_eq_some_iff.mp hv
  dsimp only at hkv h
  split at h
  · rename_i ho
    subst ho
    obtain ⟨⟨x, y⟩, hw, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨kw, hkw, hkw'⟩ := Option.bind_eq_some_iff.mp hw
    obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.mp h
    dsimp only at hX hY
    rw [innerMul_denote, denote_of_node e (lopAt?_sound V hn),
      lookup_of_node hD v hkv (dupNode?_sound V hkv'),
      lookup_of_node hD w hkw (lopAt?_sound V hkw')]
    exact inner_odd (oddSrc_sound hD hX) (oddSrc_sound hD hY) _
  · cases h

theorem dupBcst?_spec (hD : DSound V D) (e : Expr jasminVec Δ VReg) {c : Nat}
    (h : dupBcst? D e = some c) :
    (bcstE 32 c : Expr jasminVec Δ VReg).denote V = e.denote V := by
  obtain ⟨⟨odd, v⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨L, c'⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨k, hk, hk'⟩ := Option.bind_eq_some_iff.mp hv
  dsimp only at hk h
  split at h
  · rename_i hL
    subst hL
    cases h
    rw [bcstE_denote, denote_of_node e (dupNode?_sound V hn),
      lookup_of_node hD v hk (bcstNode?_sound V hk')]
    exact (dup_bcast odd _).symm
  · cases h

/-- The members of the image of an optional value. -/
theorem mem_optMap {α β : Type} {o : Option α} {g : α → β} {b : β}
    (h : b ∈ o.toList.map g) : ∃ a, o = some a ∧ g a = b := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
  exact ⟨a, Option.mem_toList.mp ha, rfl⟩

/-- The alternatives of the paired multiply. -/
def pairLoAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  (pairLo? D e).toList.map pairAlt

/-- The alternatives of the inner even product. -/
def evenMulAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  (evenMul? D e).toList.map innerMul

/-- The alternatives of the inner odd product. -/
def oddMulAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  (oddMul? D e).toList.map innerMul

/-- The alternatives of the duplication of a constant. -/
def dupBcstAt (D : Defs jasminVec) (e : Expr jasminVec Δ VReg) : List (Alt Δ VReg) :=
  (dupBcst? D e).toList.map fun c => Alt.one (bcstE 32 c)

/-- **An alternative of the paired multiply denotes the expression.** -/
theorem pairLoAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ pairLoAt D e, alt.denote V = e.denote V := by
  intro alt h
  obtain ⟨t, ht, rfl⟩ := mem_optMap h
  exact pairLo?_spec hD e ht

/-- **An alternative of the inner even product denotes the expression.** -/
theorem evenMulAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ evenMulAt D e, alt.denote V = e.denote V := by
  intro alt h
  obtain ⟨t, ht, rfl⟩ := mem_optMap h
  exact evenMul?_spec hD e ht

/-- **An alternative of the inner odd product denotes the expression.** -/
theorem oddMulAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ oddMulAt D e, alt.denote V = e.denote V := by
  intro alt h
  obtain ⟨t, ht, rfl⟩ := mem_optMap h
  exact oddMul?_spec hD e ht

/-- **An alternative of the duplication of a constant denotes the expression.** -/
theorem dupBcstAt_sound (hD : DSound V D) (e : Expr jasminVec Δ VReg) :
    ∀ alt ∈ dupBcstAt D e, alt.denote V = e.denote V := by
  intro alt h
  obtain ⟨c, hc, rfl⟩ := mem_optMap h
  exact dupBcst?_spec hD e hc

/-- The alternatives `f` of the expressions on a 512-bit register whose operation is a
    vector operation; none for another expression. -/
def atVec (f : Expr jasminVec Δ VReg → List (Alt Δ VReg)) :
    {s : JasminTy} → Expr jasminVec Δ s → List (Alt Δ s)
  | .reg 512, e =>
      match e.op with
      | .inr _ => f e
      | .inl _ => []
  | _, _ => []

/-- A property of the alternatives `f` of the vector expressions on a 512-bit register
    holds of the alternatives `atVec f`. -/
theorem atVec_cases {f : Expr jasminVec Δ VReg → List (Alt Δ VReg)}
    (P : (s : JasminTy) → Expr jasminVec Δ s → Alt Δ s → Prop)
    (hP : ∀ (e : Expr jasminVec Δ VReg) (alt : Alt Δ VReg) (o : X86VecOp),
      e.op = .inr o → alt ∈ f e → P VReg e alt)
    {s : JasminTy} (e : Expr jasminVec Δ s) {alt : Alt Δ s} (h : alt ∈ atVec f e) :
    P s e alt := by
  unfold atVec at h
  split at h
  · split at h
    · rename_i o ho
      exact hP _ _ o ho h
    · cases h
  · cases h

end Alts

/-! ## 4. The rules, the traits and the pass -/

/-- The rule of the paired multiply. -/
def pairLoRule : Rule jasminVec where
  apply D _ _ e := atVec (pairLoAt D) e
  sound _ _ V hD _ e := fun _ ha =>
    atVec_cases (fun _ e a => a.denote V = e.denote V)
      (fun e a _ _ h => pairLoAt_sound hD e a h) e ha

/-- The rule of the inner even product. -/
def evenMulRule : Rule jasminVec where
  apply D _ _ e := atVec (evenMulAt D) e
  sound _ _ V hD _ e := fun _ ha =>
    atVec_cases (fun _ e a => a.denote V = e.denote V)
      (fun e a _ _ h => evenMulAt_sound hD e a h) e ha

/-- The rule of the inner odd product. -/
def oddMulRule : Rule jasminVec where
  apply D _ _ e := atVec (oddMulAt D) e
  sound _ _ V hD _ e := fun _ ha =>
    atVec_cases (fun _ e a => a.denote V = e.denote V)
      (fun e a _ _ h => oddMulAt_sound hD e a h) e ha

/-- The rule of the duplication of a constant. -/
def dupBcstRule : Rule jasminVec where
  apply D _ _ e := atVec (dupBcstAt D) e
  sound _ _ V hD _ e := fun _ ha =>
    atVec_cases (fun _ e a => a.denote V = e.denote V)
      (fun e a _ _ h => dupBcstAt_sound hD e a h) e ha

/-- The dword multiply `vpmulld`. -/
def isDwordMul : jasminVec.Op → Bool
  | .inr (.lw _ 32 (.bin .mul)) => true
  | _ => false

/-- A dword broadcast or another broadcast constant. -/
def isBcst : jasminVec.Op → Bool
  | .inr (.bcst ..) => true
  | _ => false

/-- The operation traits of the multiply fusions: those of `vecFusionTraits`, with the
    dword multiply at cost `5` and the broadcast constant-like. -/
def mulFuseTraits : OpTraits jasminVec where
  pure _ := false
  speculatable _ := false
  constLike := isBcst
  cost op := if isDwordMul op then 5 else vecFusionTraits.cost op

/-- Off the dword multiply the cost is that of `vecFusionTraits`. -/
theorem mulFuseTraits_cost {op : jasminVec.Op} (h : isDwordMul op = false) :
    mulFuseTraits.cost op = vecFusionTraits.cost op := by
  show (if isDwordMul op then 5 else vecFusionTraits.cost op) = _
  rw [h]
  rfl

/-- The rule set of the multiply fusions. -/
def mulRules : RuleSet jasminVec where
  toOpTraits := mulFuseTraits
  rules := [pairLoRule, evenMulRule, oddMulRule, dupBcstRule]

/-- The rule set of the fusions of `vecFusions` and of the multiply fusions, at the traits
    `mulFuseTraits`. -/
def vecMulFusions : RuleSet jasminVec where
  toOpTraits := mulFuseTraits
  rules := vecFusions.rules ++ mulRules.rules

/-- **The multiply fusion pass** on structured programs of `jasminVec`. -/
def mulFuse {Γ : Ctxt jasminVec} {ts : List JasminTy} (p : NFProg jasminVec Γ ts) :
    NFProg jasminVec Γ ts :=
  aegraphOptNF mulRules p

/-- **The multiply fusion pass preserves the denotation**: the output denotes, at every
    fuel, what the input denotes. -/
theorem mulFuse_denote {Γ : Ctxt jasminVec} {ts : List JasminTy} (p : NFProg jasminVec Γ ts)
    (fuel : Nat) : (mulFuse p).denote fuel = p.denote fuel :=
  aegraphOptNF_denote mulRules p fuel

/-- The pass at the rule set `vecMulFusions` preserves the denotation. -/
theorem vecMulFusions_denote {Γ : Ctxt jasminVec} {ts : List JasminTy}
    (p : NFProg jasminVec Γ ts) (fuel : Nat) :
    (aegraphOptNF vecMulFusions p).denote fuel = p.denote fuel :=
  aegraphOptNF_denote vecMulFusions p fuel

/-- The multiply fusion pass as a chain step. -/
def mulFuseStep (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    Step (NFProg jasminVec Γ ts) (NFProg jasminVec Γ ts) :=
  ⟨"x86vec-mulfuse", fun p => some (mulFuse p)⟩

/-- **The certificate of the multiply fusion step** at every fuel: the output has the
    denotation of the input, so both relations are equality. -/
def mulFuseCert (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    StepCert (mulFuseStep Γ ts).run (vecSem fuel Γ ts) (vecSem fuel Γ ts) :=
  StepCert.ofDenoteEq (vecSem fuel Γ ts) fun p q hf => by
    cases hf
    exact mulFuse_denote p fuel

/-- The input relation of the certificate is equality. -/
theorem mulFuseCert_relIn (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    (mulFuseCert fuel Γ ts).relIn = Eq := rfl

/-- The output relation of the certificate is equality. -/
theorem mulFuseCert_relOut (fuel : Nat) (Γ : Ctxt jasminVec) (ts : List JasminTy) :
    (mulFuseCert fuel Γ ts).relOut = Eq := rfl

/-! ## 5. Equal events -/

section Events

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)

section Traversal

variable {d : Dialect.{0, 0}} [TyDenote d.Ty] [DecidableEq d.Ty] [DialectSignature d]
  [DialectDenote d] [DecidableEq d.Op] [HasWord64 d] [HasBoolBit d]

/-- `SameEvents L e a`: the alternative `a` is one binding with the events of `e`, or two
    bindings whose events, in order, are those of `e`. -/
def SameEvents (L : LeakModel d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s) (a : Alt Δ s) :
    Prop :=
  (∃ e2, a = .one e2 ∧
    ∀ V, ComLevelCheck.Expr.ctLeak L e2 V = ComLevelCheck.Expr.ctLeak L e V) ∨
  (∃ (s1 : d.Ty) (e1 : Expr d Δ s1) (e2 : Expr d (s1 :: Δ) s), a = .two e1 e2 ∧
    ∀ V, ComLevelCheck.Expr.ctLeak L e1 V ++
        ComLevelCheck.Expr.ctLeak L e2 (V.extend (e1.denote V))
      = ComLevelCheck.Expr.ctLeak L e V)

/-- **The leakage run of the traversal.** When extraction at the rule set `R` returns, for
    every expression, one or two bindings with the events of the expression, the traversal
    of a program under a state sound for `V` runs to the results and the events of the
    program at the valuation pulled back along the renaming. -/
theorem traverse_events (R : RuleSet d) (L : LeakModel d)
    (H : ∀ (S : Tbl d × Defs d) {Δ : Ctxt d} {s : d.Ty} (e : Expr d Δ s),
      SameEvents L e (choose R S e))
    (fuel : Nat) : ∀ {Γ Δ : Ctxt d} {ts : List d.Ty} (ρ : Ctxt.Hom Γ Δ) (S : Tbl d × Defs d)
      (p : NFProg d Γ ts) (V : Valuation Δ), StSound V S →
      NFProg.leakRun L fuel (nfGo R ρ S p) V = NFProg.leakRun L fuel p (V.comap ρ)
  | _, _, _, ρ, _, .ret vs, V, _ => by
      simp only [nfGo, NFProg.leakRun, Expr.lookupArgs_renameVars]
  | _, Δ, _, ρ, S, .var (t := s) e k, V, hS => by
      simp only [nfGo]
      rcases H S (e.rename ρ) with ⟨e2, hc, hl⟩ | ⟨s1, e1, e2, hc, hl⟩
      · obtain ⟨hS', hw⟩ := stOne_sound R hS _ hc
        rw [hc]
        simp only [NFProg.leakRun]
        rw [traverse_events R L H fuel _ _ k _ hS', Ctxt.Valuation.extend_comap_lift, hw,
          Expr.denote_rename, hl, Expr.ctLeak_rename]
      · obtain ⟨hS', hw⟩ := stTwo_sound R hS _ hc
        rw [Expr.denote_rename] at hw
        have hl' := hl V
        rw [Expr.ctLeak_rename] at hl'
        rw [hc]
        simp only [NFProg.leakRun]
        rw [traverse_events R L H fuel _ _ k _ hS', comap_consHom, comap_wk2, Option.map_map]
        show Option.map _ (NFProg.leakRun L fuel k
          ((V.comap ρ).extend (e2.denote (V.extend (e1.denote V))))) = _
        rw [hw, ← hl']
        congr 1
        funext r
        simp only [Function.comp, List.append_assoc]
  | _, _, _, ρ, S, .forLoop (cs := cs) count inits body k, V, hS => by
      have hb : ∀ (acc : Valuation cs) (i : Nat),
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs (Ctxt.Hom.lift ρ)) S body)
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) V)) =
            NFProg.leakRun L fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := d) i) (V.comap ρ))) := by
        intro acc i
        refine (traverse_events R L H fuel _ S body _
            (stSound_append acc (stSound_extend (HasWord64.ofNat (d := d) i) hS))).trans ?_
        rw [comap_homLiftApp]
        exact congrArg (fun W => NFProg.leakRun L fuel body (hvAppend acc W))
          (Ctxt.Valuation.extend_comap_lift ρ V _)
      have hk : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            NFProg.leakRun L fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [traverse_events R L H fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hb, hk, Ctxt.Valuation.lookup_comap,
        Expr.lookupArgs_renameVars]
  | _, _, _, ρ, S, .ifThenElse (rs := rs) cond thn els k, V, hS => by
      have hk : ∀ r : Valuation rs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp rs ρ) S k) (hvAppend r V) =
            NFProg.leakRun L fuel k (hvAppend r (V.comap ρ)) := by
        intro r
        rw [traverse_events R L H fuel _ S k _ (stSound_append r hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hk, Ctxt.Valuation.lookup_comap,
        traverse_events R L H fuel ρ S thn V hS, traverse_events R L H fuel ρ S els V hS]
  | _, _, _, ρ, S, .whileLoop (cs := cs) inits body k, V, hS => by
      have hb : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S body) (hvAppend acc V) =
            NFProg.leakRun L fuel body (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [traverse_events R L H fuel _ S body _ (stSound_append acc hS), comap_homLiftApp]
      have hk : ∀ acc : Valuation cs,
          NFProg.leakRun L fuel (nfGo R (homLiftApp cs ρ) S k) (hvAppend acc V) =
            NFProg.leakRun L fuel k (hvAppend acc (V.comap ρ)) := by
        intro acc
        rw [traverse_events R L H fuel _ S k _ (stSound_append acc hS), comap_homLiftApp]
      simp only [nfGo, NFProg.leakRun, hb, hk, Expr.lookupArgs_renameVars]
  | _, _, _, _, _, .call .., _, _ => by
      simp only [nfGo, NFProg.leakRun]

end Traversal

variable (M : LeakModel jasminDialect) {Δ : Ctxt jasminVec}

/-- An alternative of vector operations: one or two bindings, each a vector operation. -/
def vecOnly {s : JasminTy} : Alt Δ s → Prop
  | .var _ => False
  | .one e => ∃ o, e.op = .inr o
  | .two e1 e2 => (∃ o, e1.op = .inr o) ∧ ∃ o, e2.op = .inr o

/-- An alternative of vector operations for a vector expression has its events: none. -/
theorem sameEvents_of_vecOnly {s : JasminTy} (e : Expr jasminVec Δ s) {o : X86VecOp}
    (ho : e.op = .inr o) (a : Alt Δ s) (ha : vecOnly a) : SameEvents (jasminVecLeak M) e a := by
  have he : (jasminVecLeak M).kind e.op = .quiet := by rw [ho]; rfl
  cases a with
  | var w => exact False.elim ha
  | one e2 =>
      obtain ⟨o2, h2⟩ := ha
      exact .inl ⟨e2, rfl, fun V => by
        rw [ctLeak_of_quiet M _ (by rw [h2]; rfl), ctLeak_of_quiet M _ he]⟩
  | two e1 e2 =>
      obtain ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩ := ha
      exact .inr ⟨_, e1, e2, rfl, fun V => by
        rw [ctLeak_of_quiet M _ (by rw [h1]; rfl), ctLeak_of_quiet M _ (by rw [h2]; rfl),
          ctLeak_of_quiet M _ he]
        rfl⟩

/-- An alternative of the multiply fusions has the events of the expression. -/
theorem mulRules_alts (D : Defs jasminVec) {s : JasminTy} (e : Expr jasminVec Δ s) :
    ∀ alt ∈ mulRules.alts D e, SameEvents (jasminVecLeak M) e alt := by
  intro alt halt
  simp only [RuleSet.alts, mulRules, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append] at halt
  rcases halt with h | h | h | h
  · change alt ∈ atVec (pairLoAt D) e at h
    refine atVec_cases (fun _ e a => SameEvents (jasminVecLeak M) e a) ?_ e h
    intro e a o ho ha
    obtain ⟨t, -, rfl⟩ := mem_optMap ha
    exact sameEvents_of_vecOnly M e ho _ (And.intro ⟨_, rfl⟩ ⟨_, rfl⟩)
  · change alt ∈ atVec (evenMulAt D) e at h
    refine atVec_cases (fun _ e a => SameEvents (jasminVecLeak M) e a) ?_ e h
    intro e a o ho ha
    obtain ⟨t, -, rfl⟩ := mem_optMap ha
    exact sameEvents_of_vecOnly M e ho _ (And.intro ⟨_, rfl⟩ ⟨_, rfl⟩)
  · change alt ∈ atVec (oddMulAt D) e at h
    refine atVec_cases (fun _ e a => SameEvents (jasminVecLeak M) e a) ?_ e h
    intro e a o ho ha
    obtain ⟨t, -, rfl⟩ := mem_optMap ha
    exact sameEvents_of_vecOnly M e ho _ (And.intro ⟨_, rfl⟩ ⟨_, rfl⟩)
  · change alt ∈ atVec (dupBcstAt D) e at h
    refine atVec_cases (fun _ e a => SameEvents (jasminVecLeak M) e a) ?_ e h
    intro e a o ho ha
    obtain ⟨c, -, rfl⟩ := mem_optMap ha
    exact sameEvents_of_vecOnly M e ho _ (Exists.intro _ rfl)

/-- Extraction at a rule set with the traits `mulFuseTraits` whose alternatives have the
    events of the expression returns an alternative with the events of the expression. -/
theorem choose_events (rules : List (Rule jasminVec))
    (hA : ∀ (D : Defs jasminVec) {Δ : Ctxt jasminVec} {s : JasminTy} (e : Expr jasminVec Δ s),
      ∀ alt ∈ (RuleSet.mk mulFuseTraits rules).alts D e, SameEvents (jasminVecLeak M) e alt)
    (S : Tbl jasminVec × Defs jasminVec) {s : JasminTy} (e : Expr jasminVec Δ s) :
    SameEvents (jasminVecLeak M) e (choose (RuleSet.mk mulFuseTraits rules) S e) := by
  refine pick_prop (RuleSet.mk mulFuseTraits rules) _
    (fun a => SameEvents (jasminVecLeak M) e a) _ _ (.inl ⟨e, rfl, fun _ => rfl⟩) ?_
  intro a ha _
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  rcases hA S.2 e a' ha' with ⟨e2, rfl, h2⟩ | ⟨s1, e1, e2, rfl, h2⟩
  · exact .inl ⟨e2, rfl, h2⟩
  · exact .inr ⟨s1, e1, e2, rfl, h2⟩

/-- **The multiply fusion pass emits the events of its input**: the output runs, at every
    fuel and valuation, to the results and the events of the input. -/
theorem mulFuse_leakRun (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List JasminTy}
    (p : NFProg jasminVec Γ ts) (V : Valuation Γ) :
    jasminVecLeakRun M fuel (mulFuse p) V = jasminVecLeakRun M fuel p V := by
  show NFProg.leakRun (jasminVecLeak M) fuel (nfGo mulRules (Ctxt.Hom.id Γ) (∅, ∅) p) V = _
  rw [traverse_events mulRules (jasminVecLeak M)
    (fun S _ _ e => choose_events M _ (fun D _ _ e => mulRules_alts M D e) S e) fuel
    _ _ p V (stSound_empty V), Ctxt.Valuation.comap_id]

/-- **The pass at `vecMulFusions` emits the events of its input.** -/
theorem vecMulFusions_leakRun (fuel : Nat) {Γ : Ctxt jasminVec} {ts : List JasminTy}
    (p : NFProg jasminVec Γ ts) (V : Valuation Γ) :
    jasminVecLeakRun M fuel (aegraphOptNF vecMulFusions p) V = jasminVecLeakRun M fuel p V := by
  have hA : ∀ (D : Defs jasminVec) {Δ : Ctxt jasminVec} {s : JasminTy}
      (e : Expr jasminVec Δ s), ∀ alt ∈ vecMulFusions.alts D e,
        SameEvents (jasminVecLeak M) e alt := by
    intro D Δ s e alt halt
    have halt' : alt ∈ vecFusions.alts D e ++ mulRules.alts D e := by
      simpa only [RuleSet.alts, vecMulFusions, List.flatMap_append] using halt
    rcases List.mem_append.mp halt' with h | h
    · obtain ⟨e2, rfl, h2⟩ := vecFusions_alts M D e alt h
      exact .inl ⟨e2, rfl, h2⟩
    · exact mulRules_alts M D e alt h
  show NFProg.leakRun (jasminVecLeak M) fuel
    (nfGo vecMulFusions (Ctxt.Hom.id Γ) (∅, ∅) p) V = _
  rw [traverse_events vecMulFusions (jasminVecLeak M)
    (fun S _ _ e => choose_events M _ hA S e) fuel _ _ p V (stSound_empty V),
    Ctxt.Valuation.comap_id]

end Events

/-! ## 6. Costs -/

section Costs

variable {Δ : Ctxt jasminVec}

/-- The paired form costs less than the dword multiply. -/
theorem pairAlt_cost (t : Var Δ VReg × Var Δ VReg) :
    (pairAlt t).cost mulFuseTraits.cost < mulFuseTraits.cost (.inr (.lw .zmm 32 (.bin .mul))) := by
  show (4 : Nat) < 5
  decide

/-- The extraction weight of a dword broadcast is below that of a dword duplication. -/
theorem bcst_key (c : Nat) (odd : Bool) :
    mulFuseTraits.key (.inr (.bcst .zmm 32 c)) < mulFuseTraits.key (.inr (.dup .zmm odd)) := by
  show (4 : Nat) < 5
  decide

/-- The two `vpmuludq` of the inner form cost less than a dword multiply and a
    `vpmuludq`. -/
theorem innerMul_cost (t : Var Δ VReg × Var Δ VReg × Var Δ VReg) :
    (innerMul t).cost mulFuseTraits.cost <
      mulFuseTraits.cost (.inr (.lw .zmm 32 (.bin .mul))) +
        mulFuseTraits.cost (.inr (.lw .zmm 64 .muludq)) := by
  show (4 : Nat) < 7
  decide

end Costs

/-! ## 7. The Montgomery step -/

section Mont

variable {Δ : Ctxt jasminVec}

theorem lopAt?_key (L : Nat) (o : LOp) (a b : Var Δ VReg) :
    lopAt? Δ L o (.inr (.lw .zmm L o), [varLvl a, varLvl b]) = some (a, b) := by
  simp [lopAt?, lopNode?, varOfLvl?_self]

theorem dupNode?_key (odd : Bool) (a : Var Δ VReg) :
    dupNode? Δ (.inr (.dup .zmm odd), [varLvl a]) = some (odd, a) := by
  simp [dupNode?, varOfLvl?_self]

/-- **The multiply fusions on the Montgomery step.** For `lo` bound to the dword product
    of `a`, `b`, with even product `E` and odd product `O` bound, `m` bound to the dword
    product of `lo` and `μc`, `μc` bound to the dword broadcast of `μ` and `dm` bound to
    `vmovshdup m`: on the even product `vpmuludq m pc` of the high multiply of `m` the
    inner even rule offers `vpmuludq (vpmuludq E μc) pc`, and on its odd product
    `vpmuludq dm dp` the inner odd rule offers `vpmuludq (vpmuludq O μc) dp`. -/
theorem mont_offers (D : Defs jasminVec) (μ : Nat) (a b lo E O μc m pc dm dp : Var Δ VReg)
    (hlo : D[varLvl lo]? = some (.inr (.lw .zmm 32 (.bin .mul)), [varLvl a, varLvl b]))
    (hE : evenProdVar D a b = some E) (hO : oddProdVar D a b = some O)
    (hμ : D[varLvl μc]? = some (.inr (.bcst .zmm 32 μ), []))
    (hm : D[varLvl m]? = some (.inr (.lw .zmm 32 (.bin .mul)), [varLvl lo, varLvl μc]))
    (hdm : D[varLvl dm]? = some (.inr (.dup .zmm true), [varLvl m])) :
    evenMulAt D (lwE 64 .muludq m pc) = [innerMul (E, μc, pc)] ∧
    oddMulAt D (lwE 64 .muludq dm dp) = [innerMul (O, μc, dp)] := by
  have hbm : ∀ (L' : Nat) (o' : LOp),
      lopAt? Δ L' o' ((.inr (.bcst .zmm 32 μ) : jasminVec.Op), []) = none := fun _ _ => rfl
  have h1 : evenSrc D lo = E := by
    unfold evenSrc
    rw [hlo, Option.bind_some, lopAt?_key]
    simp only [hE, Option.getD_some]
  have h2 : evenSrc D μc = μc := by
    unfold evenSrc
    simp only [hμ, Option.bind_some, hbm]
  have h3 : oddSrc D lo = some O := by
    unfold oddSrc
    simp only [hlo, Option.bind_some, bcstNode?]
    rw [lopAt?_key]
    simp only [Option.bind_some, hO]
  have h4 : oddSrc D μc = some μc := by
    unfold oddSrc
    simp only [hμ, Option.bind_some, bcstNode?, if_true]
  have k1 : ∀ x y : Var Δ VReg, ((lwE 64 .muludq x y).op, argLvls (lwE 64 .muludq x y).args)
      = ((.inr (.lw .zmm 64 .muludq) : jasminVec.Op), [varLvl x, varLvl y]) := fun _ _ => rfl
  constructor
  · unfold evenMulAt evenMul?
    rw [k1, lopAt?_key]
    simp only [Option.bind_some, hm]
    rw [lopAt?_key]
    simp only [Option.map_some, h1, h2, Option.toList_some, List.map_cons, List.map_nil]
  · unfold oddMulAt oddMul?
    rw [k1, lopAt?_key]
    simp only [Option.bind_some, hdm]
    rw [dupNode?_key]
    simp only [Option.bind_some, ↓reduceIte, hm]
    rw [lopAt?_key]
    simp only [Option.bind_some, h3, h4, Option.map_some, Option.toList_some, List.map_cons,
      List.map_nil]

end Mont

end CatCrypt.Crypto.SecureCompilation.VIR.X86VecMulRules
