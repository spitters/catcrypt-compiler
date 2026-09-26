/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.GuardsLeaf
public import CatCrypt.Crypto.SecureCompilation.RelationalFrontBls377MillerLoop

/-!
# A counted Miller loop over field leaves, ascended to the `millerLoop` fold

The kernel `millerLoopProg N` is the `LowCT` counted loop

```
for i in 0..N {
  fsq := fp12_square(f); ld := line_dbl(i); f := fp12_mul(fsq, ld);
  b := loop_bit(i);
  if b != 0 { la := line_add(i); f := fp12_mul(f, la) }
}
```

run by `semUL ls fuel` at a leaf oracle `ls`. The `Fp12` slots have tower type
`.TFp12`. The field operations and the per-trip data are leaves: `MillerLeaves` states,
for a representation relation `Rep` between slot values and `Fp12_377`, that the
oracle's `fp12_square` and `fp12_mul` compute the `Fp12_377` square and product at
tower nonresidues `ξ₂, ξ₆`, and that at the counter word of trip `n < N` the oracle's
`line_dbl`, `line_add` and `loop_bit` return the lines and the bit of the entry `es n`.

The abstract state is the counter of the current trip together with the accumulator.
The loop is related to the abstract counted fold `forFold` by `corresUL_for_trips`,
and the fold is identified with `RelationalFront.millerLoop` over the entries
`(List.range N).map es`.

## Main results

* `millerBody_corres` — one trip of the loop body refines `millerStepEntry`
* `millerLoopProg_corres` — the counted loop refines the `N`-fold `forFold`
* `millerFold_snd` — the accumulator of the `forFold` is the fold of `millerStepEntry`
* `millerLoopProg_capstone` — from an accumulator slot representing `1`, the loop ends
  in a slot representing `millerLoop ξ₂ ξ₆ ((List.range N).map es)`
* `millerLoopProg_capstone_8`, `millerLoopProg_capstone_64`,
  `millerLoopProg_capstone_bls377` — the capstone at `N = 8`, `N = 64` and at the
  63 trips of the BLS12-377 ate parameter `0x8508c00000000001`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.MillerLoopBench

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.RelationalFront
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## The kernel -/

/-- The accumulator slot. -/
def fLoc : Located := ⟨"f", .TFp12⟩
/-- The loop counter. -/
def iLoc : Located := ⟨"i", .TU64⟩
/-- The square of the accumulator. -/
def sqLoc : Located := ⟨"fsq", .TFp12⟩
/-- The doubling line of the trip. -/
def ldLoc : Located := ⟨"ld", .TFp12⟩
/-- The addition line of the trip. -/
def laLoc : Located := ⟨"la", .TFp12⟩
/-- The loop-parameter bit of the trip. -/
def bLoc : Located := ⟨"b", .TU64⟩

/-- The encoded type of an `Fp12` slot. -/
abbrev FTy : CryptoTy := encodeTy .TFp12

/-- The `RCall` value at an `Fp12` destination is the leaf oracle (the inline arithmetic
    arm is at `.TFp` only). -/
theorem inlineRCallVal_TFp12 (ls : SemLeafSpec) (f : String) (vals : List ((t : CryptoTy) × ⟦t⟧)) :
    inlineRCallVal ls f .TFp12 vals = ls f (encodeTy .TFp12) vals := rfl

/-- The `RCall` value at a `u64` destination is the leaf oracle. -/
theorem inlineRCallVal_TU64 (ls : SemLeafSpec) (f : String) (vals : List ((t : CryptoTy) × ⟦t⟧)) :
    inlineRCallVal ls f .TU64 vals = ls f (encodeTy .TU64) vals := rfl

/-- The conditional addition step: `la := line_add(i); f := fp12_mul(f, la)`. -/
def millerAddStep : LowCT :=
  .RSeq (.RCall "line_add" laLoc [iLoc]) (.RCall "fp12_mul" fLoc [fLoc, laLoc])

/-- One trip of the Miller loop. -/
def millerBody : LowCT :=
  .RSeq (.RSeq (.RSeq (.RSeq
    (.RCall "fp12_square" sqLoc [fLoc])
    (.RCall "line_dbl" ldLoc [iLoc]))
    (.RCall "fp12_mul" fLoc [sqLoc, ldLoc]))
    (.RCall "loop_bit" bLoc [iLoc]))
    (.RIfNz "b" millerAddStep .RSkip)

/-- The Miller loop over `N` trips, counter `i`. -/
def millerLoopProg (N : Nat) : LowCT := .RFor "i" N millerBody

/-! ## Leaf specifications -/

/-- The product of `Fp12_377` at tower nonresidues `ξ₂, ξ₆`. -/
def mul12 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (x y : Fp12_377) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  x * y

/-- The counter word of trip `n`, as a leaf argument. -/
def ctrArg (n : Nat) : (t : CryptoTy) × ⟦t⟧ := ⟨.sword 64, BitVec.ofNat 64 n⟩

/-- The leaf specifications of the Miller loop at the oracle `ls`: square and product
    of `Fp12_377` under `Rep`, and the lines and bit of entry `es n` at the counter
    word of trip `n < N`. -/
structure MillerLeaves (ls : SemLeafSpec) (Rep : ⟦FTy⟧ → Fp12_377 → Prop)
    (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (N : Nat) (es : Nat → MillerEntry) : Prop where
  sq : ∀ v x, Rep v x → Rep (ls "fp12_square" FTy [⟨FTy, v⟩]) (mul12 ξ₂ ξ₆ x x)
  mul : ∀ v w x y, Rep v x → Rep w y →
    Rep (ls "fp12_mul" FTy [⟨FTy, v⟩, ⟨FTy, w⟩]) (mul12 ξ₂ ξ₆ x y)
  dbl : ∀ n, n < N → Rep (ls "line_dbl" FTy [ctrArg n]) (es n).dbl
  add : ∀ n, n < N → Rep (ls "line_add" FTy [ctrArg n]) (es n).add
  bit : ∀ n, n < N →
    decide ((show BitVec 64 from ls "loop_bit" (.sword 64) [ctrArg n]) ≠ 0) = (es n).bit

/-! ## Abstract state and relation -/

/-- The abstract state: the counter of the current trip, if a trip has started, and
    the accumulator. -/
abbrev MState := Option Nat × Fp12_377

/-- The state relation: a started trip `n` has the counter word of `n` in `i`, and
    the accumulator slot `f` represents the abstract accumulator. -/
def SRm (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (env : SEnvScalar) (a : MState) : Prop :=
  (∀ n, a.1 = some n → env "i" = some (ctrArg n)) ∧
  ∃ v, env "f" = some ⟨FTy, v⟩ ∧ Rep v a.2

/-- The abstract image of the counter set `i := n`. -/
def setM (n : Nat) (a : MState) : MState := (some n, a.2)

/-- The abstract loop body: the Miller step of the entry of the current trip. -/
def stepM (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (es : Nat → MillerEntry) (a : MState) : MState :=
  match a.1 with
  | some n => (some n, millerStepEntry ξ₂ ξ₆ a.2 (es n))
  | none => a

/-- The body precondition: a trip below `N` has started. -/
def preM (N : Nat) (a : MState) : Prop := ∃ n, a.1 = some n ∧ n < N

/-! ## One trip -/

/-- One trip of the loop body refines the Miller step of the current entry. -/
theorem millerBody_corres (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (N : Nat)
    (es : Nat → MillerEntry) (hL : MillerLeaves ls Rep ξ₂ ξ₆ N es) :
    CorresUL ls fuel (SRm Rep) (preM N) (stepM ξ₂ ξ₆ es) millerBody := by
  rintro env ⟨o, x⟩ ⟨hi, v, hv, hrep⟩ ⟨n, rfl, hn⟩
  have hi' : env "i" = some (ctrArg n) := hi n rfl
  have hbit := hL.bit n hn
  simp only [millerBody, millerAddStep, semUL, semScalarL_rCall, sqLoc, ldLoc, fLoc, iLoc, bLoc,
    laLoc, inlineRCallVal_TFp12, inlineRCallVal_TU64, Option.bind_some,
    locNames, argVals, List.map_cons, List.map_nil,
    List.filterMap_cons, List.filterMap_nil, SEnvScalar.upd, hv, hi', semScalarCond, guardNz,
    envReadU64, if_true, if_false, String.reduceEq, encodeTy, Option.getD_some]
  have hsq := hL.sq v x hrep
  have hm := hL.mul _ _ _ _ hsq (hL.dbl n hn)
  cases hb : (es n).bit
  · rw [hb] at hbit
    simp only [hbit, cond_false]
    refine ⟨_, rfl, ?_, _, rfl, ?_⟩
    · rintro m ⟨⟩
      simp only [SEnvScalar.upd, String.reduceEq, if_false, hi']
    · simp only [stepM, millerStepEntry, hb]
      exact hm
  · rw [hb] at hbit
    simp only [hbit, cond_true]
    refine ⟨_, rfl, ?_, _, rfl, ?_⟩
    · rintro m ⟨⟩
      simp only [SEnvScalar.upd, String.reduceEq, if_false, hi']
    · simp only [stepM, millerStepEntry, hb]
      exact hL.mul _ _ _ _ hm (hL.add n hn)

/-! ## The loop -/

/-- The counter set `i := n` preserves the state relation at the abstract image
    `setM n`. -/
theorem srm_setCounter (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (env : SEnvScalar) (a : MState)
    (n : Nat) (h : SRm Rep env a) :
    SRm Rep (env.upd "i" (t := .sword 64) (BitVec.ofNat 64 n)) (setM n a) := by
  obtain ⟨-, v, hv, hrep⟩ := h
  refine ⟨?_, v, ?_, hrep⟩
  · rintro m ⟨⟩
    simp only [SEnvScalar.upd, if_true, ctrArg]
  · simp only [SEnvScalar.upd, String.reduceEq, if_false, hv]

/-- The counted loop refines the `N`-fold abstract `forFold` of the Miller step. -/
theorem millerLoopProg_corres (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (N : Nat)
    (es : Nat → MillerEntry) (hL : MillerLeaves ls Rep ξ₂ ξ₆ N es) :
    CorresUL ls fuel (SRm Rep) (fun _ => True) (forFold setM (stepM ξ₂ ξ₆ es) N)
      (millerLoopProg N) :=
  corresUL_weaken ls (SRm Rep)
    (corresUL_for_trips ls (SRm Rep) setM (srm_setCounter Rep)
      (millerBody_corres ls fuel Rep ξ₂ ξ₆ N es hL) N)
    (fun _ _ n hn => ⟨n, rfl, hn⟩)

/-- The accumulator of the abstract `forFold` is the fold of `millerStepEntry` over the
    entries of trips `0, …, N - 1`. -/
theorem millerFold_snd (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (es : Nat → MillerEntry) :
    ∀ (N : Nat) (a : MState),
      (forFold setM (stepM ξ₂ ξ₆ es) N a).2
        = ((List.range N).map es).foldl (millerStepEntry ξ₂ ξ₆) a.2
  | 0, _ => rfl
  | N + 1, a => by
      rw [List.range_succ, List.map_append, List.foldl_append, ← millerFold_snd ξ₂ ξ₆ es N a]
      rfl

/-- The unit of `Fp12_377` at tower nonresidues `ξ₂, ξ₆`. -/
def one12 (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) : Fp12_377 :=
  letI := Fp12_377.commRing ξ₂ ξ₆
  1

/-- **Capstone.** From an environment whose accumulator slot represents `1`, the
    counted loop at the oracle `ls` ends in an environment whose accumulator slot
    represents `millerLoop ξ₂ ξ₆ ((List.range N).map es)`. -/
theorem millerLoopProg_capstone (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377) (N : Nat)
    (es : Nat → MillerEntry) (hL : MillerLeaves ls Rep ξ₂ ξ₆ N es)
    (env : SEnvScalar) (v : ⟦FTy⟧) (hv : env "f" = some ⟨FTy, v⟩)
    (h1 : Rep v (one12 ξ₂ ξ₆)) :
    ∃ env' w, semUL ls fuel (millerLoopProg N) env = some env' ∧
      env' "f" = some ⟨FTy, w⟩ ∧ Rep w (millerLoop ξ₂ ξ₆ ((List.range N).map es)) := by
  obtain ⟨env', hrun, -, w, hw, hrep⟩ :=
    millerLoopProg_corres ls fuel Rep ξ₂ ξ₆ N es hL env (none, one12 ξ₂ ξ₆)
      (show SRm Rep env (none, one12 ξ₂ ξ₆) from
        ⟨fun _ h => absurd h (by simp), v, hv, h1⟩) trivial
  refine ⟨env', w, hrun, hw, ?_⟩
  rw [millerFold_snd] at hrep
  exact hrep

/-! ## Instances -/

/-- The capstone at `N = 8`. -/
theorem millerLoopProg_capstone_8 (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (es : Nat → MillerEntry) (hL : MillerLeaves ls Rep ξ₂ ξ₆ 8 es)
    (env : SEnvScalar) (v : ⟦FTy⟧) (hv : env "f" = some ⟨FTy, v⟩)
    (h1 : Rep v (one12 ξ₂ ξ₆)) :
    ∃ env' w, semUL ls fuel (millerLoopProg 8) env = some env' ∧
      env' "f" = some ⟨FTy, w⟩ ∧ Rep w (millerLoop ξ₂ ξ₆ ((List.range 8).map es)) :=
  millerLoopProg_capstone ls fuel Rep ξ₂ ξ₆ 8 es hL env v hv h1

/-- The capstone at `N = 64`. -/
theorem millerLoopProg_capstone_64 (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (es : Nat → MillerEntry) (hL : MillerLeaves ls Rep ξ₂ ξ₆ 64 es)
    (env : SEnvScalar) (v : ⟦FTy⟧) (hv : env "f" = some ⟨FTy, v⟩)
    (h1 : Rep v (one12 ξ₂ ξ₆)) :
    ∃ env' w, semUL ls fuel (millerLoopProg 64) env = some env' ∧
      env' "f" = some ⟨FTy, w⟩ ∧ Rep w (millerLoop ξ₂ ξ₆ ((List.range 64).map es)) :=
  millerLoopProg_capstone ls fuel Rep ξ₂ ξ₆ 64 es hL env v hv h1

/-- The bits of the BLS12-377 ate parameter `0x8508c00000000001` below its top bit,
    most significant first. -/
def bls377Bits : List Bool :=
  (List.range 63).map (fun k => Nat.testBit 0x8508c00000000001 (62 - k))

/-- The entry of trip `n` of the BLS12-377 Miller loop, with doubling and addition
    lines `dbl n` and `add n`. -/
def bls377Entry (dbl add : Nat → Fp12_377) (n : Nat) : MillerEntry :=
  ⟨bls377Bits.getD n false, dbl n, add n⟩

/-- The capstone at the 63 trips of the BLS12-377 ate parameter. -/
theorem millerLoopProg_capstone_bls377 (ls : SemLeafSpec) (fuel : Nat)
    (Rep : ⟦FTy⟧ → Fp12_377 → Prop) (ξ₂ : FpBLS377) (ξ₆ : Fp2_377)
    (dbl add : Nat → Fp12_377)
    (hL : MillerLeaves ls Rep ξ₂ ξ₆ 63 (bls377Entry dbl add))
    (env : SEnvScalar) (v : ⟦FTy⟧) (hv : env "f" = some ⟨FTy, v⟩)
    (h1 : Rep v (one12 ξ₂ ξ₆)) :
    ∃ env' w, semUL ls fuel (millerLoopProg 63) env = some env' ∧
      env' "f" = some ⟨FTy, w⟩ ∧
      Rep w (millerLoop ξ₂ ξ₆ ((List.range 63).map (bls377Entry dbl add))) :=
  millerLoopProg_capstone ls fuel Rep ξ₂ ξ₆ 63 _ hL env v hv h1

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.MillerLoopBench
