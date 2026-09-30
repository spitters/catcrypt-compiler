/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Constant time of the owned `Lprog` back end

`LprogOptPipeline.ownedLprog` is the basic-block optimizer
`optimizeLprogBasicBlocks`, the constant-index fold `ConstIndexFold.foldIndexedLprog`
and the register re-allocation `LprogGpRealloc.reallocLprog`. This module states
that the three stages preserve constant time from function entry
(`LprogLeak.EntryCT`) in the `CTLeak` model `LprogLeakCT.ctLeak`. The first two
stages are covered by the checker of `LprogLeakTV` on every function body
(`progCheck`), the third by `LprogGpReallocLeak.ReallocOk`.

## Main results

* `progCheck`: the checker `LprogLeakTV.bodyCheck` on every function of a program
  against its image under a body transform.
* `optimizeLprogBasicBlocks_ctLeak`, `foldIndexedLprog_ctLeak`: each of the two
  stages preserves `EntryCT (ctLeak w)` when `progCheck` accepts its input.
* `ownedLprog_constant_time`:
  `EntryCT (ctLeak w) P pub → EntryCT (ctLeak w) (ownedLprog P) pub` under the two
  checks and `ReallocOk` on every function of the folded program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogCT

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeakTV (bodyCheck entryCT_of_mapped)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
  (mapBodies getFundef_mapBodies optimizeBasicBlocks optimizeLprogBasicBlocks ownedLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
  (foldIndexedBody foldIndexedLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (reallocLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
  (ReallocOk reallocLprog_entryCT)

/-- The checker accepts every function body of `P` against its image under `T`. -/
def progCheck (w : Nat) (T : Lcmd → Lcmd) (P : Lprog) : Bool :=
  P.lp_funcs.all fun f =>
    bodyCheck w (f.2.lfd_body.map Linstr.li_i) ((T f.2.lfd_body).map Linstr.li_i)

theorem progCheck_getFundef {w : Nat} {T : Lcmd → Lcmd} {P : Lprog}
    (h : progCheck w T P = true) (fn : String) (fd : Lfundef) (hg : getFundef P fn = some fd) :
    bodyCheck w (fd.lfd_body.map Linstr.li_i) ((T fd.lfd_body).map Linstr.li_i) = true := by
  simp only [getFundef, Option.map_eq_some_iff] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  exact List.all_eq_true.1 h p (List.mem_of_find?_eq_some hp)

theorem foldIndexedLprog_eq (P : Lprog) : foldIndexedLprog P = mapBodies foldIndexedBody P := rfl

/-- **The basic-block optimizer preserves constant time from function entry** when
    the checker accepts every function body against its optimized body. -/
theorem optimizeLprogBasicBlocks_ctLeak {w : Nat} (P : Lprog)
    (pub : LstateP w → LstateP w → Prop) (hchk : progCheck w optimizeBasicBlocks P = true)
    (h : EntryCT (ctLeak w) P pub) : EntryCT (ctLeak w) (optimizeLprogBasicBlocks P) pub :=
  entryCT_of_mapped P _ optimizeBasicBlocks pub (getFundef_mapBodies optimizeBasicBlocks P)
    (progCheck_getFundef hchk) h

/-- **The constant-index fold preserves constant time from function entry** when
    the checker accepts every function body against its folded body. -/
theorem foldIndexedLprog_ctLeak {w : Nat} (P : Lprog) (pub : LstateP w → LstateP w → Prop)
    (hchk : progCheck w foldIndexedBody P = true) (h : EntryCT (ctLeak w) P pub) :
    EntryCT (ctLeak w) (foldIndexedLprog P) pub := by
  rw [foldIndexedLprog_eq]
  exact entryCT_of_mapped P _ foldIndexedBody pub (getFundef_mapBodies foldIndexedBody P)
    (progCheck_getFundef hchk) h

/-- **The owned back end preserves constant time from function entry.** The
    optimizer and the fold are covered by the checker on their inputs, the
    register re-allocation by `ReallocOk` on every function of its input. -/
theorem ownedLprog_constant_time {w : Nat} (P : Lprog) (pub : LstateP w → LstateP w → Prop)
    (hopt : progCheck w optimizeBasicBlocks P = true)
    (hfold : progCheck w foldIndexedBody (optimizeLprogBasicBlocks P) = true)
    (hok : ∀ fn fd, getFundef (foldIndexedLprog (optimizeLprogBasicBlocks P)) fn = some fd →
      ReallocOk w fn fd)
    (h : EntryCT (ctLeak w) P pub) : EntryCT (ctLeak w) (ownedLprog P) pub :=
  reallocLprog_entryCT (ctLeak w) _ pub hok
    (foldIndexedLprog_ctLeak _ pub hfold (optimizeLprogBasicBlocks_ctLeak P pub hopt h))

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogCT
