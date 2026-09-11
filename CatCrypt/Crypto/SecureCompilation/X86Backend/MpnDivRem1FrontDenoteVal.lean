/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1PreinvAgree

/-!
# `mpn_divrem_1` front-denote value capstone

The runtime-trip `mpn_divrem_1` program denotes the reciprocal-step fold
`preinvFold` (`divRtProg_fold`). Under the normalisation preconditions the
reciprocal step agrees with the exact Euclidean step (`preinvStep_agrees`),
so the fold over `preinvFoldStep` equals the fold over `divFoldStep`. This
module composes those into the value statement: the program's denotation is
`divFold`, whose quotient/remainder invariant is `divFold_val`.

## Main results

* `preinvFold_succ`: the `preinvFold` fold peels its last trip.
* `preinvFoldStep_eq_divFoldStep`: one reciprocal-step trip equals one exact
  Euclidean trip when the running remainder is below the divisor.
* `preinvFold_eq_divFold`: the `k`-fold identification, `k ≤ top + 1`.
* `divRtProg_val`: the compiled program denotes `divFold`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenoteVal

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit
  (NU NR RS Gouter divInit divRem1RtProgOpt divFold divFoldStep divFold_succ divFold_val
   divLimb preinvStep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenote
  (preinvFold preinvFoldStep divRtProg_fold upVar dVar dinvVar nVar)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1PreinvAgree (preinvStep_agrees)

/-- The reciprocal-step fold peels its last trip. -/
theorem preinvFold_succ (up : Fin NU → BitVec 64) (dinv d : BitVec 64)
    (top rs k : Nat) (acc : Fin NR → BitVec 64) :
    preinvFold up dinv d top rs (k + 1) acc
      = preinvFoldStep up dinv d top rs (preinvFold up dinv d top rs k acc) k := by
  simp [preinvFold, List.range_succ, List.foldl_append]

/-- One reciprocal-step trip equals one exact Euclidean trip when the running
    remainder in cell `rs` is below the divisor and the reciprocal is correct. -/
theorem preinvFoldStep_eq_divFoldStep (up : Fin NU → BitVec 64)
    (dinv d : BitVec 64) (top rs : Nat) (acc : Fin NR → BitVec 64) (t : Nat)
    (hd2 : 2 ^ 63 ≤ d.toNat) (hv : dinv.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64)
    (hrem : (memGetDyn acc rs).toNat < d.toNat) :
    preinvFoldStep up dinv d top rs acc t = divFoldStep up d top rs acc t := by
  unfold preinvFoldStep divFoldStep
  rw [preinvStep_agrees dinv d (memGetDyn acc rs) (memGetDyn up (top - t)) hd2 hrem hv]

/-- The `k`-fold reciprocal-step fold equals the exact Euclidean fold, for every
    trip count up to `top + 1`, when cell `rs` starts at zero and the divisor is
    normalised with a correct reciprocal. -/
theorem preinvFold_eq_divFold (up : Fin NU → BitVec 64)
    (dinv d : BitVec 64) (top rs : Nat) (acc : Fin NR → BitVec 64)
    (hrs : rs < NR) (htop : top < rs) (h0 : memGetDyn acc rs = 0)
    (hd2 : 2 ^ 63 ≤ d.toNat) (hv : dinv.toNat = (2 ^ 128 - 1) / d.toNat - 2 ^ 64) :
    ∀ k : Nat, k ≤ top + 1 →
      preinvFold up dinv d top rs k acc = divFold up d top rs k acc := by
  have hdpos : 0 < d.toNat := lt_of_lt_of_le (by norm_num) hd2
  intro k
  induction k with
  | zero => intro _; simp [preinvFold, divFold]
  | succ m ih =>
      intro hm
      rw [preinvFold_succ, divFold_succ, ih (by omega)]
      exact preinvFoldStep_eq_divFoldStep up dinv d top rs (divFold up d top rs m acc) m
        hd2 hv (divFold_val up d top rs acc hrs htop h0 hdpos m (by omega)).1

/-- **The runtime-trip `mpn_divrem_1` program denotes the exact Euclidean fold.**
    Under the normalisation preconditions on the argument registers — divisor
    `d` normalised with bit 63 set, a correct reciprocal `dinv`, the seed cell
    `RS` cleared, at least one trip, and the top limb index below `RS` — the
    compiled program's denotation is `divFold` of the argument registers. -/
theorem divRtProg_val (V : Ctxt.Valuation Gouter)
    (hrs : RS < NR)
    (htop : (nVar.lookup V).toNat - 1 < RS)
    (h0 : memGetDyn (divInit.lookup V) RS = 0)
    (hd2 : 2 ^ 63 ≤ (dVar.lookup V).toNat)
    (hv : (dinvVar.lookup V).toNat
      = (2 ^ 128 - 1) / (dVar.lookup V).toNat - 2 ^ 64)
    (hn : 1 ≤ (nVar.lookup V).toNat) :
    divRem1RtProgOpt.map (fun c => ComL.denote c V)
      = some (divFold (upVar.lookup V) (dVar.lookup V)
          ((nVar.lookup V).toNat - 1) RS (nVar.lookup V).toNat (divInit.lookup V)) := by
  rw [divRtProg_fold V]
  refine congrArg some ?_
  exact preinvFold_eq_divFold (upVar.lookup V) (dinvVar.lookup V) (dVar.lookup V)
    ((nVar.lookup V).toNat - 1) RS (divInit.lookup V) hrs htop h0 hd2 hv
    (nVar.lookup V).toNat (by omega)

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontDenoteVal
