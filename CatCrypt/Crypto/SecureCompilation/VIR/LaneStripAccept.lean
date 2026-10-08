/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LaneStrip

/-!
# Strip-mining of a scaled addition of arrays

`scaledAddLoop N` is the counted loop `for i < count: out[i] = a[i] + b[i] * c` over arrays
`stackArr 64 N`, with the loop-invariant arrays `a` and `b`, the loop-invariant word `c` and
the carried array `out`. `stripMine 3 64` accepts it for every `N ≥ 8`: the block loop runs 8
iterations at once on tiles of 8 lanes of 64 bits, with the `tileSplat` of `c`.

## Main definitions

* `scaledAddLoop` — the loop, a program of `NFProg jasminDialect`.
* `scaledAddWrite`, `scaledAddOut` — one iteration on the carried array, and the array after
  all iterations.
* `scaledAddStrip` — the strip-mined program.

## Main results

* `scaledAddLoop_stripMine` — `stripMine 3 64` accepts `scaledAddLoop N` for `8 ≤ N`.
* `scaledAddLoop_denote` — the loop returns `scaledAddOut`, at every fuel.
* `scaledAddOut_get`, `scaledAddOut_get_of_ne` — the element of `scaledAddOut` at a position
  whose residue modulo `N` is the residue of an index below the trip count is
  `a[k] + b[k] * c`, and at every other position it is the element of `out`.
* `scaledAddStrip_denote` — the scalar reading of the result of the strip-mined program is
  `scaledAddOut`.
* `scaledAddStrip_events`, `scaledAddStrip_ct` — the events of the strip-mined program are
  `stripEv 8 3` of the events of the loop in `addrModel`, and two runs of the strip-mined
  program have equal events when the two runs of the loop have.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LaneStripAccept

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TileDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.NFTileSum
open CatCrypt.Crypto.SecureCompilation.VIR.TileBridge
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapNF
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStripKernel
open CatCrypt.Crypto.SecureCompilation.VIR.LaneStrip
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

attribute [local instance] jasminTileDenote jasminTileMemDenote

/-! ## 1. The loop -/

/-- The context of `scaledAddLoop`: the trip count, the arrays `a` and `b`, the word `c` and
    the array `out`. -/
abbrev scaledAddCtx (N : Nat) : Ctxt jasminDialect :=
  [.reg 64, .stackArr 64 N, .stackArr 64 N, .reg 64, .stackArr 64 N]

/-- The counted loop `for i < count: out[i] = a[i] + b[i] * c`. The carried tuple is the
    array `out`; the body loads `a[i]` and `b[i]`, multiplies `b[i]` by `c`, adds, and stores
    the sum at `i`. -/
def scaledAddLoop (N : Nat) : NFProg jasminDialect (scaledAddCtx N) [.stackArr 64 N] :=
  NFProg.forLoop (d := jasminDialect) (cs := [.stackArr 64 N]) (Γ := scaledAddCtx N)
    .here (.cons (.there (.there (.there (.there .here)))) .nil)
    (.var ⟨.stackLoad 64 N, rfl,
        .cons (.there (.there (.there .here))) (.cons (.there .here) .nil)⟩
      (.var ⟨.stackLoad 64 N, rfl,
          .cons (.there (.there (.there (.there (.there .here)))))
            (.cons (.there (.there .here)) .nil)⟩
        (.var ⟨.regArith .mul 64, rfl,
            .cons .here
              (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)⟩
          (.var ⟨.regArith .add 64, rfl, .cons (.there (.there .here)) (.cons .here .nil)⟩
            (.var ⟨.stackStore 64 N, rfl,
                .cons (.there (.there (.there (.there .here))))
                  (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))⟩
              (.ret (.cons .here .nil)))))))
    (.ret (.cons .here .nil))

/-- The valuation of `scaledAddCtx` at a trip count, the arrays and the word. -/
abbrev scaledAddIn {N : Nat} (cnt : BitVec 64) (a b : Fin N → BitVec 64) (c : BitVec 64)
    (out : Fin N → BitVec 64) : Valuation (d := jasminDialect) (scaledAddCtx N) :=
  HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.reg 64) cnt
    (HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.stackArr 64 N) a
      (HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.stackArr 64 N) b
        (HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.reg 64) c
          (HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.stackArr 64 N) out .nil))))

/-- The one-array tuple of an array. -/
abbrev arrTuple {N : Nat} (o : Fin N → BitVec 64) :
    Valuation (d := jasminDialect) [JasminTy.stackArr 64 N] :=
  HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.stackArr 64 N) o .nil

/-! ## 2. The result of the loop -/

/-- The carried array after the iteration `i`: the array written at the index `i`, read at 64
    bits, with `a[i] + b[i] * c`. -/
def scaledAddWrite {N : Nat} (a b : Fin N → BitVec 64) (c : BitVec 64)
    (o : Fin N → BitVec 64) (i : Nat) : Fin N → BitVec 64 :=
  stackSet o (BitVec.ofNat 64 i).toNat
    (stackGet a (BitVec.ofNat 64 i).toNat + stackGet b (BitVec.ofNat 64 i).toNat * c)

/-- The array `out` after the iterations below the trip count `cnt`. -/
def scaledAddOut {N : Nat} (cnt : BitVec 64) (a b : Fin N → BitVec 64) (c : BitVec 64)
    (out : Fin N → BitVec 64) : Fin N → BitVec 64 :=
  (List.range cnt.toNat).foldl (scaledAddWrite a b c) out

/-- An iteration at an index below `2 ^ 64` writes at that index. -/
theorem scaledAddWrite_of_lt {N : Nat} (a b : Fin N → BitVec 64) (c : BitVec 64)
    (o : Fin N → BitVec 64) {i : Nat} (hi : i < 2 ^ 64) :
    scaledAddWrite a b c o i = stackSet o i (stackGet a i + stackGet b i * c) := by
  unfold scaledAddWrite
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- Folding over `m` indices a step that maps a one-array tuple by `g` folds `g`. -/
theorem foldlM_range_arr {N : Nat} (g : (Fin N → BitVec 64) → Nat → (Fin N → BitVec 64))
    (f : Valuation (d := jasminDialect) [JasminTy.stackArr 64 N] → Nat →
      Option (Valuation (d := jasminDialect) [JasminTy.stackArr 64 N]))
    (hf : ∀ (o : Fin N → BitVec 64) (i : Nat), f (arrTuple o) i = some (arrTuple (g o i))) :
    (m : Nat) → (o : Fin N → BitVec 64) →
    (List.range m).foldlM f (arrTuple o) = some (arrTuple ((List.range m).foldl g o))
  | 0, _ => rfl
  | m + 1, o => by
      rw [List.range_succ, List.foldlM_append, foldlM_range_arr g f hf m o, List.foldl_append]
      simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, hf,
        List.foldl_cons, List.foldl_nil]
      rfl

/-- **The loop returns `scaledAddOut`**, at every fuel. -/
theorem scaledAddLoop_denote (N fuel : Nat) (cnt : BitVec 64) (a b : Fin N → BitVec 64)
    (c : BitVec 64) (out : Fin N → BitVec 64) :
    (scaledAddLoop N).denote fuel (scaledAddIn cnt a b c out) =
      some (arrTuple (scaledAddOut cnt a b c out)) := by
  rw [scaledAddLoop, NFProg.denote_forLoop]
  erw [foldlM_range_arr (scaledAddWrite a b c) _ (fun o i => rfl)]
  rfl

/-- The elements of the array after `m ≤ 2 ^ 64` iterations: `a[k] + b[k] * c` at a position
    whose residue is the residue of an index below `m`, and the element of `out` at every
    other position. -/
theorem foldl_scaledAddWrite_get {N : Nat} (hN : 0 < N) (a b out : Fin N → BitVec 64)
    (c : BitVec 64) : ∀ m, m ≤ 2 ^ 64 → ∀ k,
      ((∃ i, i < m ∧ i % N = k % N) →
        stackGet ((List.range m).foldl (scaledAddWrite a b c) out) k =
          stackGet a k + stackGet b k * c) ∧
      ((∀ i, i < m → i % N ≠ k % N) →
        stackGet ((List.range m).foldl (scaledAddWrite a b c) out) k = stackGet out k)
  | 0, _, _ => ⟨fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | m + 1, hm, k => by
      have ih := foldl_scaledAddWrite_get hN a b out c m (Nat.le_of_succ_le hm) k
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        scaledAddWrite_of_lt a b c _ hm]
      by_cases hk : m % N = k % N
      · refine ⟨fun _ => ?_, fun h => absurd hk (h m (Nat.lt_succ_self m))⟩
        rw [stackGet_congr_mod _ hk.symm, stackGet_stackSet_self hN,
          stackGet_congr_mod a hk, stackGet_congr_mod b hk]
      · rw [stackGet_stackSet_of_ne _ m k _ (Ne.symm hk)]
        exact ⟨fun ⟨i, hi, he⟩ => ih.1 ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi)
            (fun e => hk (e ▸ he)), he⟩,
          fun h => ih.2 fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

/-- **The written elements.** At a position `k` whose residue modulo `N` is the residue of an
    index below the trip count, `scaledAddOut` holds `a[k] + b[k] * c`. -/
theorem scaledAddOut_get {N : Nat} (hN : 0 < N) (cnt : BitVec 64) (a b : Fin N → BitVec 64)
    (c : BitVec 64) (out : Fin N → BitVec 64) (k : Nat)
    (hk : ∃ i, i < cnt.toNat ∧ i % N = k % N) :
    stackGet (scaledAddOut cnt a b c out) k = stackGet a k + stackGet b k * c :=
  (foldl_scaledAddWrite_get hN a b out c cnt.toNat (Nat.le_of_lt cnt.isLt) k).1 hk

/-- At a position below the trip count, `scaledAddOut` holds `a[k] + b[k] * c`. -/
theorem scaledAddOut_get_of_lt {N : Nat} (hN : 0 < N) (cnt : BitVec 64)
    (a b : Fin N → BitVec 64) (c : BitVec 64) (out : Fin N → BitVec 64) (k : Nat)
    (hk : k < cnt.toNat) :
    stackGet (scaledAddOut cnt a b c out) k = stackGet a k + stackGet b k * c :=
  scaledAddOut_get hN cnt a b c out k ⟨k, hk, rfl⟩

/-- **The other elements.** At a position whose residue modulo `N` is the residue of no index
    below the trip count, `scaledAddOut` holds the element of `out`. -/
theorem scaledAddOut_get_of_ne {N : Nat} (hN : 0 < N) (cnt : BitVec 64)
    (a b : Fin N → BitVec 64) (c : BitVec 64) (out : Fin N → BitVec 64) (k : Nat)
    (hk : ∀ i, i < cnt.toNat → i % N ≠ k % N) :
    stackGet (scaledAddOut cnt a b c out) k = stackGet out k :=
  (foldl_scaledAddWrite_get hN a b out c cnt.toNat (Nat.le_of_lt cnt.isLt) k).2 hk

/-- At a position of the array from the trip count on, `scaledAddOut` holds the element of
    `out`. -/
theorem scaledAddOut_get_of_le {N : Nat} (hN : 0 < N) (cnt : BitVec 64)
    (a b : Fin N → BitVec 64) (c : BitVec 64) (out : Fin N → BitVec 64) (k : Nat)
    (hk : cnt.toNat ≤ k) (hkN : k < N) :
    stackGet (scaledAddOut cnt a b c out) k = stackGet out k :=
  scaledAddOut_get_of_ne hN cnt a b c out k fun i hi he => by
    rw [Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_of_lt_of_le hi hk) hkN),
      Nat.mod_eq_of_lt hkN] at he
    exact absurd (he ▸ hi) (Nat.not_lt_of_le hk)

/-! ## 3. Acceptance -/

/-- **`stripMine` accepts the loop** at 8 lanes of 64 bits, for arrays of at least 8
    elements. -/
theorem scaledAddLoop_stripMine (N : Nat) (h : 8 ≤ N) :
    (stripMine 3 64 (scaledAddLoop N)).isSome = true := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le' h
  rfl

/-- The strip-mined program of `scaledAddLoop N`. -/
def scaledAddStrip (N : Nat) (h : 8 ≤ N) :
    NFProg jasminTileMem ((scaledAddCtx N).map (Sum.inl (β := TileTy)))
      ([JasminTy.stackArr 64 N].map (Sum.inl (β := TileTy))) :=
  (stripMine 3 64 (scaledAddLoop N)).get (scaledAddLoop_stripMine N h)

/-- `stripMine` returns `scaledAddStrip`. -/
theorem stripMine_scaledAddLoop (N : Nat) (h : 8 ≤ N) :
    stripMine 3 64 (scaledAddLoop N) = some (scaledAddStrip N h) :=
  (Option.some_get (scaledAddLoop_stripMine N h)).symm

/-! ## 4. The strip-mined program -/

/-- **The result of the strip-mined program.** On a valuation whose scalar reading is the
    trip count, the arrays and the word, the scalar reading of the result of `scaledAddStrip`
    is `scaledAddOut`, at every fuel. -/
theorem scaledAddStrip_denote (N : Nat) (h : 8 ≤ N) (fuel : Nat) (cnt : BitVec 64)
    (a b : Fin N → BitVec 64) (c : BitVec 64) (out : Fin N → BitVec 64)
    (W : Valuation (d := jasminTileDialect) ((scaledAddCtx N).map (Sum.inl (β := TileTy))))
    (hW : unmapInl (d := jasminDialect) (e := tileDialect) W = scaledAddIn cnt a b c out) :
    (tileMemDenP jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) fuel
        (scaledAddStrip N h) W).map (unmapInl (d := jasminDialect) (e := tileDialect)) =
      some (arrTuple (scaledAddOut cnt a b c out)) := by
  rw [stripMine_denote fuel (scaledAddLoop N) (scaledAddStrip N h)
    (stripMine_scaledAddLoop N h) W, hW]
  exact scaledAddLoop_denote N fuel cnt a b c out

/-- One iteration of `scaledAddLoop` emits three events in `addrModel`: two loads and one
    store. -/
theorem iterEvents_scaledAddLoop (N : Nat) : iterEvents addrModel (scaledAddLoop N) = 3 :=
  rfl

/-- **The events of the strip-mined program** in `addrModel` are `stripEv 8 3` of the events
    of the loop. -/
theorem scaledAddStrip_events (N : Nat) (h : 8 ≤ N) (fuel : Nat)
    (W : Valuation (d := jasminTileDialect) ((scaledAddCtx N).map (Sum.inl (β := TileTy)))) :
    (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) addrModel
        fuel (scaledAddStrip N h) W).map Prod.snd =
      ((NFProg.leakRunM addrModel fuel (scaledAddLoop N)
        (unmapInl (d := jasminDialect) (e := tileDialect) W)).map Prod.snd).map
        (stripEv 8 3) :=
  stripMine_events addrModel (addrModel_laneQuiet 64) addrModel_arrAddr (addrModel_idxQuiet 3)
    fuel (scaledAddLoop N) (scaledAddStrip N h) (stripMine_scaledAddLoop N h) W

/-- **Equal events of the loop give equal events of the strip-mined program.** For two
    valuations on whose scalar readings the loop emits the same events in `addrModel`, the
    strip-mined program emits the same events. -/
theorem scaledAddStrip_ct (N : Nat) (h : 8 ≤ N) (fuel : Nat)
    (W₁ W₂ : Valuation (d := jasminTileDialect)
      ((scaledAddCtx N).map (Sum.inl (β := TileTy))))
    (hev : (NFProg.leakRunM addrModel fuel (scaledAddLoop N)
        (unmapInl (d := jasminDialect) (e := tileDialect) W₁)).map Prod.snd =
      (NFProg.leakRunM addrModel fuel (scaledAddLoop N)
        (unmapInl (d := jasminDialect) (e := tileDialect) W₂)).map Prod.snd) :
    (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) addrModel
        fuel (scaledAddStrip N h) W₁).map Prod.snd =
      (tileMemLeakRun jasminDialect (instDialectDenoteMOptionOfPure jasminDialect) addrModel
        fuel (scaledAddStrip N h) W₂).map Prod.snd := by
  rw [scaledAddStrip_events N h fuel W₁, scaledAddStrip_events N h fuel W₂, hev]

/-- The output relation of the leakage certificate of strip-mining at 8 lanes of 64 bits in
    `addrModel`, over the context of `scaledAddLoop`, implies the constant-time relation. -/
theorem scaledAdd_leakCert_ct (N fuel : Nat) :
    ∀ x y, (stripMineLeakCert (l := 3) (w := 64) addrModel (addrModel_laneQuiet 64)
      addrModel_arrAddr (addrModel_idxQuiet 3) fuel (scaledAddCtx N)
      [JasminTy.stackArr 64 N]).relOut x y → PassChain.ctRel x y :=
  stripMineLeakCert_ct addrModel (addrModel_laneQuiet 64) addrModel_arrAddr
    (addrModel_idxQuiet 3) fuel (scaledAddCtx N) [JasminTy.stackArr 64 N]

end CatCrypt.Crypto.SecureCompilation.VIR.LaneStripAccept
