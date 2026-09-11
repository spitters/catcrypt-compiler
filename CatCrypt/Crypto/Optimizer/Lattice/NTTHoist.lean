/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul

/-!
# Pass 3.2 — Hoist `invntt` out of an NTT multiply-accumulate loop

The per-leaf NTT rewrite (`NTTPolyMul`) turns each coefficient-domain
`poly_mul` into `ntt_poly_mul = invntt ∘ basemul ∘ (ntt × ntt)`.  When
such multiplies feed an accumulation loop (the `polyvec_dot` shape),

```
acc = 0
for i in 0..n {
  prod = ntt_poly_mul(a_i, b_i)      -- = invntt(basemul(ntt a_i, ntt b_i))
  acc  = poly_add(acc, prod)
}
```

the `invntt` is recomputed every iteration.  Because `invntt` is
**additive** (a `Z_q`-linear map), the accumulation can be done in the
NTT domain and the single closing `invntt` pulled out of the loop:

```
acc = 0
for i in 0..n {
  prod = basemul(ntt a_i, ntt b_i)   -- NTT-domain product
  acc  = poly_add(acc, prod)         -- same add, NTT domain
}
acc = invntt(acc)
```

## Soundness

The verified core is `foldl_invntt_fusion`: for an additive map `φ`,

```
foldl (fun acc c => add acc (φ c)) (φ a) cs = φ (foldl (fun acc c => add acc c) a cs)
```

The operational theorem `nttHoist_accLoop_eq` reduces the big-step
execution of both loops to this fold identity (induction on the loop
bound via `RustExec.forZero` / `forSucc`), under explicit leaf-agreement
hypotheses (`add` is the accumulator op, the source mul = `invntt` of the
target mul, `invntt` additive, `invntt 0 = 0`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTHoist

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The verified algebraic core: fold-fusion of an additive map -/

section FoldFusion

variable {V : Type*}

/-- **Fold-fusion.**  If `φ` is additive w.r.t. `add`
    (`add (φ x) (φ y) = φ (add x y)`), then accumulating `φ`-images and
    applying `φ` to a plain accumulation coincide.  This is the linearity
    fact that justifies hoisting `invntt` out of the accumulation loop:
    `Σ invntt(cᵢ) = invntt(Σ cᵢ)`. -/
theorem foldl_invntt_fusion (add : V → V → V) (φ : V → V)
    (hadd : ∀ x y, add (φ x) (φ y) = φ (add x y)) :
    ∀ (a : V) (cs : List V),
      List.foldl (fun acc c => add acc (φ c)) (φ a) cs
        = φ (List.foldl (fun acc c => add acc c) a cs) := by
  intro a cs
  induction cs generalizing a with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons]
      rw [hadd a c, ih (add a c)]

/-- Specialisation starting from a unit `z` fixed by `φ` (`φ z = z`),
    which is the loop's initial zeroed accumulator. -/
theorem foldl_invntt_fusion_zero (add : V → V → V) (φ : V → V) (z : V)
    (hadd : ∀ x y, add (φ x) (φ y) = φ (add x y)) (hz : φ z = z)
    (cs : List V) :
    List.foldl (fun acc c => add acc (φ c)) z cs
      = φ (List.foldl (fun acc c => add acc c) z cs) := by
  have h := foldl_invntt_fusion add φ hadd z cs
  rwa [hz] at h

end FoldFusion

/-! ## §2  The syntactic pass

`nttHoist` recognises the multiply-accumulate loop shape and rewrites the
inner `ntt_poly_mul` leaf to a `basemul` leaf, appending a single
`invntt` after the loop. -/

/-- The NTT-domain `basemul` leaf name for parameters `(q, n)`. -/
@[inline] def nttBasemulName (q n : Nat) : String := s!"ntt_basemul_{q}_{n}"

/-- The `invntt` leaf name for parameters `(q, n)`. -/
@[inline] def nttInvnttName (q n : Nat) : String := s!"ntt_invntt_{q}_{n}"

/-- Recognised accumulator-add leaf names (`poly_add` and the alt
    spelling `polyadd`). -/
def isAddName (f : String) : Bool := f == "poly_add" || f == "polyadd"

/-- Hoist worker threading the set `Z` of accumulator names known to be
    **freshly zero-initialised** in the current scope.  An `RLetZero x`
    adds `x` to `Z` (it sets `x := default`); control-flow joins and
    sequencing conservatively reset `Z` (an earlier statement may have
    written the slot).  The loop-rewrite fires only when the loop's
    accumulator is in `Z` — this is the syntactic witness for the
    `acc = 0` loop-entry precondition of `nttHoist_maccLoop_eq`, so the
    pass never restructures a loop whose accumulator might be non-zero. -/
def nttHoistAux (q n : Nat) : List String → LowCT → LowCT
  | Z, .RFor idx k (.RSeq (.RCall mul prod margs) (.RCall add acc aargs)) =>
      if mul == NTTPolyMul.nttPolyMulName q n
         && isAddName add
         && (aargs.headD prod).locVar == acc.locVar
         && Z.contains acc.locVar then
        .RSeq
          (.RFor idx k (.RSeq (.RCall (nttBasemulName q n) prod margs)
                              (.RCall add acc aargs)))
          (.RCall (nttInvnttName q n) acc [acc])
      else
        .RFor idx k (.RSeq (.RCall mul prod margs) (.RCall add acc aargs))
  | Z, .RSeq c1 c2 => .RSeq (nttHoistAux q n Z c1) (nttHoistAux q n [] c2)
  | Z, .RLetZero x t body => .RLetZero x t (nttHoistAux q n (x :: Z) body)
  | Z, .RLetU64Zero x body => .RLetU64Zero x (nttHoistAux q n Z body)
  | _, .RIfNz cond ct cf =>
      .RIfNz cond (nttHoistAux q n [] ct) (nttHoistAux q n [] cf)
  | _, .RWhileNz cond body => .RWhileNz cond (nttHoistAux q n [] body)
  | _, .RFor idx k body => .RFor idx k (nttHoistAux q n [] body)
  | Z, .RBlock body => .RBlock (nttHoistAux q n Z body)
  | _, .RFnDef name ps rs body cont =>
      .RFnDef name ps rs (nttHoistAux q n [] body) (nttHoistAux q n [] cont)
  | _, c => c

/-- Guarded `invntt` hoist.  Rewrites a multiply-accumulate loop

    `RFor i k (RSeq (RCall mul prod [a,b]) (RCall add acc [acc, prod]))`

    (with `mul = ntt_poly_mul_{q}_{n}`, `add` an accumulator add, and the
    accumulator `acc` freshly `RLetZero`-introduced above the loop) into

    `RSeq (RFor i k (RSeq (RCall basemul prod [a,b]) (RCall add acc [acc, prod])))
          (RCall invntt acc [acc])`.

    The freshly-zeroed-accumulator guard (`acc ∈ Z`) is what makes the
    rewrite sound — see `nttHoist_maccLoop_eq` / `nttHoist_letAccProd_eq`. -/
def nttHoist (q n : Nat) (c : LowCT) : LowCT := nttHoistAux q n [] c

/-! ## §3  Operational correctness

We prove the hoist correct on the canonical multiply-accumulate loop:

```
for idx in 0..k { prod := mul(a, b); acc := add(acc, prod) }
```

where the body leaves are abstract (`mul`, `add`) with semantics fixed
by hypotheses.  The source uses `mul = invntt ∘ basemul`; the target uses
`mul = basemul` and applies one `invntt` after the loop.  The key facts:
`add` is the accumulator op `addF`, the source product is `invF` of the
target product, `invF` is additive, and `invF 0 = 0`. -/

section Operational

variable {N : Nat} {leafSpec : LeafSpec} {T : TowerType}

/-- Effect of one body `prod := mul(a,b); acc := add(acc, prod)` on the
    relevant tower slots, when `mul` evaluates to the constant `P` (on
    inputs `aV`, `bV`) and `add` evaluates to `addF`.  Returns the new
    `acc`, and that `prod`, `a`, `b` hold their expected values. -/
theorem maccBody_effect
    (mul add a b acc prod : String)
    (addF : RustVal T → RustVal T → RustVal T)
    (P accV aV bV : RustVal T)
    (hMul : ∀ o, leafSpec.call mul T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = P)
    (hAdd : ∀ o x y, leafSpec.call add T [T, T] o [⟨T, x⟩, ⟨T, y⟩] = addF x y)
    (hap : acc ≠ prod) (hpa : prod ≠ a) (hpb : prod ≠ b)
    (haa : acc ≠ a) (hab : acc ≠ b)
    {rs rs' : RustState}
    (hAcc : rs.rsTower acc = some ⟨T, accV⟩)
    (hA : rs.rsTower a = some ⟨T, aV⟩)
    (hB : rs.rsTower b = some ⟨T, bV⟩)
    (hProd : ∃ pv, rs.rsTower prod = some ⟨T, pv⟩)
    (h : RustExec N leafSpec
          (.RSeq (.RCall mul ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                 (.RCall add ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩])) rs rs') :
    rs'.rsTower acc = some ⟨T, addF accV P⟩ ∧
    rs'.rsTower prod = some ⟨T, P⟩ ∧
    rs'.rsTower a = some ⟨T, aV⟩ ∧
    rs'.rsTower b = some ⟨T, bV⟩ := by
  obtain ⟨pv, hpv⟩ := hProd
  cases h with
  | seq _ _ _ r1 _ h1 h2 =>
    cases h1 with
    | call _ _ _ _ oldP argL hlk hargL htys =>
      cases h2 with
      | call _ _ _ _ oldA argL2 hlk2 hargL2 htys2 =>
        have hmapAB : List.map (fun x => x.locDst) [(⟨a,T⟩:Located), ⟨b,T⟩] = [T, T] := rfl
        have eArgL : argL = [⟨T, aV⟩, ⟨T, bV⟩] := by rw [hargL]; simp [hA, hB]
        have vP : leafSpec.call mul (⟨prod,T⟩:Located).locDst
              (List.map (fun x => x.locDst) [(⟨a,T⟩:Located), ⟨b,T⟩]) oldP argL = P := by
          rw [eArgL, hmapAB]; exact hMul oldP
        rw [vP]
        -- inner state lookups (after the mul update writes prod := P)
        have hinnerProd : (locatedUpdate rs (⟨prod,T⟩:Located) P).rsTower prod
            = some ⟨T, P⟩ := by
          rw [locatedUpdate]; exact rsSetTower_same rs prod ⟨T, P⟩
        have hinnerAcc : (locatedUpdate rs (⟨prod,T⟩:Located) P).rsTower acc
            = some ⟨T, accV⟩ := by
          rw [locatedUpdate, rsSetTower_other rs prod acc ⟨T, P⟩ hap.symm]; exact hAcc
        have hinnerA : (locatedUpdate rs (⟨prod,T⟩:Located) P).rsTower a
            = some ⟨T, aV⟩ := by
          rw [locatedUpdate, rsSetTower_other rs prod a ⟨T, P⟩ hpa]; exact hA
        have hinnerB : (locatedUpdate rs (⟨prod,T⟩:Located) P).rsTower b
            = some ⟨T, bV⟩ := by
          rw [locatedUpdate, rsSetTower_other rs prod b ⟨T, P⟩ hpb]; exact hB
        have eArgL2 : argL2 = [⟨T, accV⟩, ⟨T, P⟩] := by
          rw [hargL2, vP]; simp [hinnerAcc, hinnerProd]
        have vAdd : leafSpec.call add (⟨acc,T⟩:Located).locDst
              (List.map (fun x => x.locDst) [(⟨acc,T⟩:Located), ⟨prod,T⟩]) oldA argL2
              = addF accV P := by
          rw [eArgL2]; exact hAdd oldA accV P
        rw [vAdd]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [locatedUpdate]; exact rsSetTower_same _ acc ⟨T, addF accV P⟩
        · rw [locatedUpdate, rsSetTower_other _ acc prod ⟨T, addF accV P⟩ hap]
          exact hinnerProd
        · rw [locatedUpdate, rsSetTower_other _ acc a ⟨T, addF accV P⟩ haa]
          exact hinnerA
        · rw [locatedUpdate, rsSetTower_other _ acc b ⟨T, addF accV P⟩ hab]
          exact hinnerB

/-- The multiply-accumulate loop runs `acc := add(acc, mul(a,b))` `k`
    times.  With `mul` constant `= Q` and `add = addF`, the resulting
    accumulator is a left fold of `addF` over `k` copies of `Q`. -/
theorem maccLoop_effect
    (mul add a b acc prod idx : String)
    (addF : RustVal T → RustVal T → RustVal T)
    (Q accV0 aV bV : RustVal T)
    (hMul : ∀ o, leafSpec.call mul T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = Q)
    (hAdd : ∀ o x y, leafSpec.call add T [T, T] o [⟨T, x⟩, ⟨T, y⟩] = addF x y)
    (hap : acc ≠ prod) (hpa : prod ≠ a) (hpb : prod ≠ b)
    (haa : acc ≠ a) (hab : acc ≠ b)
    (k : Nat) :
    ∀ {rs rs' : RustState},
      rs.rsTower acc = some ⟨T, accV0⟩ →
      rs.rsTower a = some ⟨T, aV⟩ →
      rs.rsTower b = some ⟨T, bV⟩ →
      (∃ pv, rs.rsTower prod = some ⟨T, pv⟩) →
      RustExec N leafSpec
        (.RFor idx k (.RSeq (.RCall mul ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                            (.RCall add ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩]))) rs rs' →
      rs'.rsTower acc
          = some ⟨T, List.foldl (fun x c => addF x c) accV0 (List.replicate k Q)⟩ ∧
      rs'.rsTower a = some ⟨T, aV⟩ ∧
      rs'.rsTower b = some ⟨T, bV⟩ ∧
      (∃ pv, rs'.rsTower prod = some ⟨T, pv⟩) := by
  induction k with
  | zero =>
      intro rs rs' hAcc hA hB hPr h
      cases h
      simp_all
  | succ k ih =>
      intro rs rs' hAcc hA hB hPr h
      cases h with
      | forSucc _ _ _ _ r1 _ hloop hbody =>
        obtain ⟨ha1, ha1a, ha1b, ha1p⟩ := ih hAcc hA hB hPr hloop
        -- `rsSetScalar` preserves the tower heap.
        have hsAcc : (rsSetScalar r1 idx k).rsTower acc
            = some ⟨T, List.foldl (fun x c => addF x c) accV0 (List.replicate k Q)⟩ := ha1
        have hsA : (rsSetScalar r1 idx k).rsTower a = some ⟨T, aV⟩ := ha1a
        have hsB : (rsSetScalar r1 idx k).rsTower b = some ⟨T, bV⟩ := ha1b
        have hsP : ∃ pv, (rsSetScalar r1 idx k).rsTower prod = some ⟨T, pv⟩ := ha1p
        obtain ⟨hbAcc, hbProd, hbA, hbB⟩ :=
          maccBody_effect mul add a b acc prod addF Q
            (List.foldl (fun x c => addF x c) accV0 (List.replicate k Q)) aV bV
            hMul hAdd hap hpa hpb haa hab hsAcc hsA hsB hsP hbody
        have hrep : List.replicate (k + 1) Q = List.replicate k Q ++ [Q] :=
          List.replicate_succ'
        refine ⟨?_, hbA, hbB, ⟨_, hbProd⟩⟩
        rw [hrep, List.foldl_append]
        simpa using hbAcc

/-- **Operational correctness of the `invntt` hoist.**

    Source: `for idx in 0..k { prod := mulC(a,b); acc := add(acc, prod) }`
    where `mulC = invF ∘ mulN` (each iteration applies `invntt`).

    Target: `for idx in 0..k { prod := mulN(a,b); acc := add(acc, prod) }`
    in the NTT domain, then a single `acc := invntt(acc)`.

    Under additivity of `invF` (`hLin`) and `invF 0 = 0` (`hZero`), both
    produce the same final accumulator.  The proof reduces both loops to
    `maccLoop_effect` (folds over `replicate k …`) and closes by
    `foldl_invntt_fusion_zero`. -/
theorem nttHoist_maccLoop_eq
    (mulC mulN addName invName a b acc prod idx : String)
    (addF : RustVal T → RustVal T → RustVal T)
    (invF : RustVal T → RustVal T)
    (Pn aV bV : RustVal T)
    (hMulN : ∀ o, leafSpec.call mulN T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = Pn)
    (hMulC : ∀ o, leafSpec.call mulC T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = invF Pn)
    (hAdd : ∀ o x y, leafSpec.call addName T [T, T] o [⟨T, x⟩, ⟨T, y⟩] = addF x y)
    (hInv : ∀ o x, leafSpec.call invName T [T] o [⟨T, x⟩] = invF x)
    (hLin : ∀ x y, addF (invF x) (invF y) = invF (addF x y))
    (hZero : invF (default : RustVal T) = default)
    (hap : acc ≠ prod) (hpa : prod ≠ a) (hpb : prod ≠ b)
    (haa : acc ≠ a) (hab : acc ≠ b)
    (k : Nat)
    {rs rsS rsT : RustState}
    (hAcc : rs.rsTower acc = some ⟨T, (default : RustVal T)⟩)
    (hA : rs.rsTower a = some ⟨T, aV⟩)
    (hB : rs.rsTower b = some ⟨T, bV⟩)
    (hPr : ∃ pv, rs.rsTower prod = some ⟨T, pv⟩)
    (hSrc : RustExec N leafSpec
        (.RFor idx k (.RSeq (.RCall mulC ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                            (.RCall addName ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩]))) rs rsS)
    (hTgt : RustExec N leafSpec
        (.RSeq
          (.RFor idx k (.RSeq (.RCall mulN ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                              (.RCall addName ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩])))
          (.RCall invName ⟨acc, T⟩ [⟨acc, T⟩])) rs rsT) :
    rsS.rsTower acc = rsT.rsTower acc := by
  -- Source loop result.
  obtain ⟨hSacc, _, _, _⟩ :=
    maccLoop_effect mulC addName a b acc prod idx addF (invF Pn) default aV bV
      hMulC hAdd hap hpa hpb haa hab k hAcc hA hB hPr hSrc
  -- Target: loop, then the single `invntt`.
  cases hTgt with
  | seq _ _ _ rL _ hLoop hInvCall =>
    obtain ⟨hLacc, _, _, _⟩ :=
      maccLoop_effect mulN addName a b acc prod idx addF Pn default aV bV
        hMulN hAdd hap hpa hpb haa hab k hAcc hA hB hPr hLoop
    -- Invert the `invntt` call.
    cases hInvCall with
    | call _ _ _ _ oldA argL hlk hargL htys =>
      -- The loop left `acc = B`; the call reads it and writes `invF B`.
      set B := List.foldl (fun x c => addF x c) (default : RustVal T) (List.replicate k Pn)
      have hLlook : locatedLookup rL ⟨acc, T⟩ = some B := by
        simp [locatedLookup, hLacc]
      have eArg : argL = [⟨T, B⟩] := by rw [hargL]; simp [hLacc]
      have hmap : List.map (fun x => x.locDst) [(⟨acc, T⟩ : Located)] = [T] := rfl
      have vInv : leafSpec.call invName (⟨acc, T⟩ : Located).locDst
            (List.map (fun x => x.locDst) [(⟨acc, T⟩ : Located)]) oldA argL = invF B := by
        rw [eArg, hmap]; exact hInv oldA B
      rw [vInv]
      -- Final acc on each side.
      have hTacc : (locatedUpdate rL ⟨acc, T⟩ (invF B)).rsTower acc
          = some ⟨T, invF B⟩ := by
        rw [locatedUpdate]; exact rsSetTower_same _ acc ⟨T, invF B⟩
      rw [hTacc, hSacc]
      -- src fold = invF (tgt fold) by fold-fusion.
      have hfuse : List.foldl (fun x c => addF x c) (default : RustVal T)
            (List.replicate k (invF Pn)) = invF B := by
        have : List.replicate k (invF Pn) = (List.replicate k Pn).map invF :=
          List.map_replicate.symm
        rw [this, List.foldl_map]
        exact foldl_invntt_fusion_zero addF invF default hLin hZero (List.replicate k Pn)
      rw [hfuse]

/-- **Guarded correctness** (the `acc = 0` precondition discharged
    syntactically).  For the freshly-declared accumulator shape
    `RLetZero acc T (RLetZero prod T (loop))` — exactly the shape the
    guarded `nttHoist` fires on (`acc ∈ Z` because of the enclosing
    `RLetZero acc`) — the source loop and the hoisted target agree on the
    accumulator, with **no external zeroed-accumulator hypothesis**: the
    `RLetZero acc` supplies `acc := default` at loop entry. -/
theorem nttHoist_letAccProd_eq
    (mulC mulN addName invName a b acc prod idx : String)
    (addF : RustVal T → RustVal T → RustVal T)
    (invF : RustVal T → RustVal T)
    (Pn aV bV : RustVal T)
    (hMulN : ∀ o, leafSpec.call mulN T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = Pn)
    (hMulC : ∀ o, leafSpec.call mulC T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩] = invF Pn)
    (hAdd : ∀ o x y, leafSpec.call addName T [T, T] o [⟨T, x⟩, ⟨T, y⟩] = addF x y)
    (hInv : ∀ o x, leafSpec.call invName T [T] o [⟨T, x⟩] = invF x)
    (hLin : ∀ x y, addF (invF x) (invF y) = invF (addF x y))
    (hZero : invF (default : RustVal T) = default)
    (hap : acc ≠ prod) (hpa : prod ≠ a) (hpb : prod ≠ b)
    (haa : acc ≠ a) (hab : acc ≠ b)
    (k : Nat)
    {rs rsS rsT : RustState}
    (hA : rs.rsTower a = some ⟨T, aV⟩)
    (hB : rs.rsTower b = some ⟨T, bV⟩)
    (hSrc : RustExec N leafSpec
        (.RLetZero acc T (.RLetZero prod T
          (.RFor idx k (.RSeq (.RCall mulC ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                              (.RCall addName ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩]))))) rs rsS)
    (hTgt : RustExec N leafSpec
        (.RLetZero acc T (.RLetZero prod T
          (.RSeq
            (.RFor idx k (.RSeq (.RCall mulN ⟨prod, T⟩ [⟨a, T⟩, ⟨b, T⟩])
                                (.RCall addName ⟨acc, T⟩ [⟨acc, T⟩, ⟨prod, T⟩])))
            (.RCall invName ⟨acc, T⟩ [⟨acc, T⟩])))) rs rsT) :
    rsS.rsTower acc = rsT.rsTower acc := by
  cases hSrc with
  | letZero _ _ _ _ _ hSrc1 =>
    cases hSrc1 with
    | letZero _ _ _ _ _ hSrc2 =>
      cases hTgt with
      | letZero _ _ _ _ _ hTgt1 =>
        cases hTgt1 with
        | letZero _ _ _ _ _ hTgt2 =>
          -- Loop-entry state: acc and prod freshly zeroed, a/b carried over.
          have hAcc0 : (rsSetTower (rsSetTower rs acc ⟨T, default⟩) prod ⟨T, default⟩).rsTower acc
              = some ⟨T, (default : RustVal T)⟩ := by
            rw [rsSetTower_other _ prod acc ⟨T, default⟩ hap.symm]
            exact rsSetTower_same rs acc ⟨T, default⟩
          have hA0 : (rsSetTower (rsSetTower rs acc ⟨T, default⟩) prod ⟨T, default⟩).rsTower a
              = some ⟨T, aV⟩ := by
            rw [rsSetTower_other _ prod a ⟨T, default⟩ hpa,
                rsSetTower_other _ acc a ⟨T, default⟩ haa]; exact hA
          have hB0 : (rsSetTower (rsSetTower rs acc ⟨T, default⟩) prod ⟨T, default⟩).rsTower b
              = some ⟨T, bV⟩ := by
            rw [rsSetTower_other _ prod b ⟨T, default⟩ hpb,
                rsSetTower_other _ acc b ⟨T, default⟩ hab]; exact hB
          have hProd0 : (rsSetTower (rsSetTower rs acc ⟨T, default⟩) prod ⟨T, default⟩).rsTower prod
              = some ⟨T, (default : RustVal T)⟩ := rsSetTower_same _ prod ⟨T, default⟩
          exact nttHoist_maccLoop_eq mulC mulN addName invName a b acc prod idx
            addF invF Pn aV bV hMulN hMulC hAdd hInv hLin hZero
            hap hpa hpb haa hab k hAcc0 hA0 hB0 ⟨default, hProd0⟩ hSrc2 hTgt2

end Operational

end CatCrypt.Crypto.Optimizer.Lattice.NTTHoist
