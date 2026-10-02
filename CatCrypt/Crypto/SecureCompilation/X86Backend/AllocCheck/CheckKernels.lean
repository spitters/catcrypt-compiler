/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.GpInstance
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.YmmInstance
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakYmm4Alloc
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.GpInstance
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.YmmInstance
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFGKernels
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakYmm4Alloc

/-!
# The allocation checker on shipped kernel bodies

The generic checker `Check.allocCheck` against the two checkers it generalises, on the
bodies the owned back end re-allocates and on the four-way Keccak.

General-purpose registers. For each kernel, the body `LprogGpRealloc.reallocLprog`
receives (`preRealloc`: the optimiser and the constant-index fold of `ownedLprog`) is
split into runs with the live-out sets of `reallocBody`. On every run, every candidate of
`runCands` and three decision lists that `goAcc` mostly rejects (every destination in
`RAX`, every destination in `R12`, the first candidate reversed) are checked by `goAcc`
and by `allocCheck gpSig` over the run's one-block graph. The kernels are the five
`mpn_*_loop_owned` loops, the X25519 ladder step and the rolled Keccak-f1600.

Whole bodies. `bodyCheckE` checks the decisions the pass selects over the control-flow
graph of the whole body. On the rolled Keccak-f1600 the decisions selected with the
live-out computation of `reallocBody` pass; with the live-out computation before compiler
commit `81d1d97` (no `labelLiveFrames`) they fail at instruction 58, the reload
`R15 := k.2` after the loop label: the spill store of `k.2` above the back-edge is
dropped as dead, and the merge at the label removes `k.2` from its cell.

Vector registers. On the selected four-way Keccak program (3,218 instructions), the
allocation of `KeccakYmm4Alloc` passes both `ymmAllocValidClosed` and
`allocCheck ymmSig`, and the same decisions with every resident name moved to `%ymm0`
fail both. The evaluation cost of this check is that of computing the allocation.

## Main definitions

* `preRealloc`, `bodyOf`: the body the register re-allocation receives.
* `keccakRolledPre`: the rolled Keccak-f1600 program before `ownedLprog`.
* `gpKernelAgreement`: for the candidates and for the rejected decision lists, the
  number of decision lists checked, the number `goAcc` accepts, and the number on which
  the two checkers disagree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.CheckKernels

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.GpInstance
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.YmmInstance
open CatCrypt.Crypto.Jasmin

/-- The program `LprogGpRealloc.reallocLprog` receives in `LprogOptPipeline.ownedLprog`. -/
def preRealloc (p : Lprog) : Lprog :=
  ConstIndexFold.foldIndexedLprog (LprogOptPipeline.optimizeLprogBasicBlocks p)

/-- The result registers and the body of the first function of `preRealloc p`. -/
def bodyOf (p : Option Lprog) : Option (List String × Lcmd) :=
  p.bind fun p => (preRealloc p).lp_funcs.head?.map fun f => (f.2.lfd_res, f.2.lfd_body)

/-- The rolled Keccak-f1600 program before `ownedLprog`. -/
def keccakRolledPre : Option Lprog :=
  match KeccakJincImport.keccakF1600Rolled with
  | .ok r => JincElab.rolledLprog r.fn r.tables KeccakJincImport.keccakF1600Sym
  | .error _ => none

/-- Three decision lists for a run: every destination in `RAX`, every destination in
    `R12`, and the first candidate reversed. -/
def mutantCands (is : List LprogGpRealloc.FI) (cands : List (List String)) :
    List (List String) :=
  [is.map (fun _ => "RAX"), is.map (fun _ => "R12"), (cands.headD []).reverse]

/-- A count of decision lists checked, accepted by `goAcc`, and judged differently by
    `goAcc` and `allocCheck gpSig`, extended by one decision list. -/
def tally (t : Nat × Nat × Nat) (r : Bool × Bool) : Nat × Nat × Nat :=
  (t.1 + 1, t.2.1 + (if r.1 then 1 else 0), t.2.2 + (if r.1 != r.2 then 1 else 0))

/-- **The agreement of `goAcc` and `allocCheck gpSig` on a kernel**: the tally over every
    candidate of every run, and the tally over the decision lists of `mutantCands`. -/
def gpKernelAgreement (p : Option Lprog) : Option ((Nat × Nat × Nat) × (Nat × Nat × Nat)) :=
  (bodyOf p).map fun (res, b) => Id.run do
    let mut good := (0, 0, 0)
    let mut bad := (0, 0, 0)
    for (is, lend) in runLends true true res b do
      let cands := LprogGpRealloc.runCands lend is
      for cs in cands do
        good := tally good (runVerdicts lend is cs)
      for cs in mutantCands is cands do
        bad := tally bad (runVerdicts lend is cs)
    return (good, bad)

/-! ## General-purpose registers, per run -/

set_option kat.ms 500 in
#kat gpKernelAgreement (MpnLoopFrontEmit.addLprogFront ()) == some ((18, 18, 0), (18, 1, 0))
set_option kat.ms 500 in
#kat gpKernelAgreement (MpnLoopFrontEmit.subLprogFront ()) == some ((18, 18, 0), (18, 1, 0))
set_option kat.ms 500 in
#kat gpKernelAgreement (MpnLoopFrontEmit.andLprog ()) == some ((18, 18, 0), (18, 1, 0))
set_option kat.ms 500 in
#kat gpKernelAgreement (MpnLoopFrontEmit.iorLprog ()) == some ((18, 18, 0), (18, 1, 0))
set_option kat.ms 500 in
#kat gpKernelAgreement (MpnLoopFrontEmit.xorLprog ()) == some ((18, 18, 0), (18, 1, 0))
set_option kat.ms 2500 in
#kat gpKernelAgreement (some Fe25519LfundefBridge.monoStepLprog) ==
  some ((168, 168, 0), (168, 9, 0))
set_option kat.ms 4000 in
#kat gpKernelAgreement keccakRolledPre == some ((18, 18, 0), (18, 2, 0))

/-! ## General-purpose registers, whole bodies -/

set_option kat.ms 1500 in
#kat ((bodyOf (some Fe25519LfundefBridge.monoStepLprog)).bind fun (res, b) =>
  bodyCheckE true true res b) == some (.ok ())
set_option kat.ms 3000 in
#kat ((bodyOf keccakRolledPre).bind fun (res, b) => bodyCheckE true true res b) ==
  some (.ok ())
set_option kat.ms 3000 in
#kat ((bodyOf keccakRolledPre).bind fun (res, b) => bodyCheckE false true res b) ==
  some (.error (.use 58 "k.2" ⟨.frame, "k.2"⟩))

/-! ## Vector registers

The x4 Keccak YMM verdicts (old and new checker agree: both accept the allocation and
both reject it with resident names moved to `%ymm0`) are measured outside Lean: computing
`KeccakYmm4Alloc.allocation` takes about 11 s, above the `#kat` budget. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.CheckKernels
