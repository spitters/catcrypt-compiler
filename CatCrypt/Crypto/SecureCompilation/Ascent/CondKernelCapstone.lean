/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.KeystoneControl
import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubEndToEnd

/-!
# A control-flow kernel capstone: a branch from source to the emit interface

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`._

This is the control-flow analogue of `FeSubEndToEnd.feSub_endToEnd` for a kernel
with a **branch**: a select `r := if c then x else y` — two `RScalarSet` arms on
the same name `r`, merged by `RIfNz` (the (C′) cmov shape). It carries the branch
kernel through the ascent leg (`corres_if`) and the control keystone (`keystone_if`)
so the emitted output word is pinned to the clean branch-select spec
`if c' then wEnc x else wEnc y` in `ZMod 2^64`, with **no free `Corres` hypothesis**.

## Where the branch reaches, and where it stops

Unlike the straight-line `feSub` capstone, the branch kernel does **not** reach
emitted jasmin bytes through the verified `translateDialectControl →
cryptoDialectToJasminCom` (VIR `Com`→jasmin) pipeline. The frontier is exhibited
here as two proved theorems:

* **`condFront_translates`** — the dialect front *accepts* the closed branch kernel:
  `translateDialectControl VarMap.empty` succeeds on
  `RSeq (RScalarSet c gc) (RIfNz c (RScalarSet r x) (RScalarSet r y))`, producing
  the six-op φ-merge `Com` (`bvConst; bvConst; bvConst; bvEq; not; ite`).
* **`condBackend_declines`** — the VIR `Com`→jasmin lowering *declines* that `Com`:
  `cryptoDialectToJasminCom` returns `none`, because the φ-merge is built from the
  `.bvEq` / `.not` / `.ite` ops, all outside the straight-line fragment `toJExprD`
  lowers. This is the precise wall: a genuine conditional select produces a `Com`
  the current owned backend cannot emit (control reaches bytes only through the
  separate `Lprog`/`Lcond` labelled-branch emitter, not this `Com` route).

So the byte instantiation of the keystone is stated as the honest **emit interface**
`condKernel_bytes_of_emit`: for *any* emitted artefact denoting the select word
`ifClosedVal`, its clean `ZMod 2^64` spec is the branch select. The hypothesis
`hEmit` is exactly the fact a backend cmov/select lowering would supply — the one
edge `condBackend_declines` shows the present pipeline does not close.

## Why the closed kernel, not a bare `RIfNz`

The select spec is env-independent only if the guard is written from a literal
before the branch reads it (`ifClosedKernel`, via `ifClosed_hAgree`). A bare
`RIfNz` reads the entry guard, so its output word is entry-dependent (no `hAgree`),
and at the top-level empty varmap its guard is unbound (the front declines it).
The abstraction leg itself is stated on the bare `RIfNz` (`corres_if`, the genuine
φ-merge rule); the closed kernel is what the front consumes.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The branch kernel -/

/-- The bare φ-merge branch kernel `o := if c ≠ 0 then 7 else 9` (two literal
    `RScalarSet` arms on the SAME name `o`, merged by `RIfNz` reading guard `c`).
    This is the (C′) cmov shape — the only conditional shape the front compiles as
    a genuine select. -/
def condBranchKernel : LowCT :=
  .RIfNz "c" (.RScalarSet "o" 7) (.RScalarSet "o" 9)

/-- The **closed** branch kernel: write the guard `c := 0` (a literal) first, then
    the select. Writing the guard from a literal makes the output word
    env-independent (`ifClosed_hAgree`) — the shape the front actually consumes. -/
def condClosedKernel : LowCT := ifClosedKernel "c" "o" 0 7 9

/-! ## The abstraction leg: the genuine φ-merge correspondence -/

/-- **The branch ascent leg.** Over the word state relation `SRword`, the concrete
    `phiSelect` cmov denotes the abstract branch select on the abstract guard's
    zero-test `a "c" = 0` — the terminal φ-merge value leaf `corres_if`, with no
    free hypothesis. The abstract map sets `o` to `9` when the guard is zero and to
    `7` otherwise, leaving every other name untouched. -/
theorem condKernel_ascends :
    Corres SRword (fun _ => True)
      (fun a s => if s = "o" then
          (if a "c" = 0 then (9 : ZMod (2 ^ 64)) else (7 : ZMod (2 ^ 64))) else a s)
      condBranchKernel :=
  corres_if "c" "o" 7 9

/-! ## The keystone at the emit interface -/

/-- **`condKernel_bytes_of_emit` — the branch keystone at the byte interface.**
    For the closed branch kernel, given *any* emitted artefact `jdenote` that
    denotes the select output word (`hEmit : jdenote = ctTransTy (ifClosedVal 0 7 9)`),
    the emitted word's clean `ZMod 2^64` spec is the branch select — here `9`, the
    guard being the literal `0`. The abstraction leg (guard set + `corres_if`) and
    the env-independence adapter `ifClosed_hAgree` are discharged inside `keystone_if`;
    the only premise is `hEmit`, precisely the edge a backend cmov/select lowering
    would supply (the one `condBackend_declines` shows the present VIR `Com`→jasmin
    pipeline does not close). This is the control-flow analogue of `feSub_endToEnd`,
    conditional on that single emit-lowering edge. -/
theorem condKernel_bytes_of_emit (jdenote : ⟦mapTy (.sword 64)⟧)
    (hEmit : jdenote = ctTransTy (t := .sword 64) (ifClosedVal 0 7 9)) :
    jdenote = ctTransTy (t := .sword 64) (ifClosedVal 0 7 9)
      ∧ wEnc (ifClosedVal 0 7 9) = (9 : ZMod (2 ^ 64)) := by
  have h := keystone_if (ctTransTy (t := .sword 64)) "c" "o" 0 7 9 jdenote hEmit
  refine ⟨h.1, ?_⟩
  rw [h.2]; simp

/-! ## The frontier: front accepts, VIR `Com`→jasmin backend declines -/

/-- **`condFront_translates`.** The dialect front `translateDialectControl` accepts
    the closed branch kernel at the top-level empty varmap: the guard-set prefix
    binds `c`, so the `RIfNz` arm reaches the (C′) φ-merge and returns `some`. -/
theorem condFront_translates :
    (translateDialectControl VarMap.empty condClosedKernel).isSome := by rfl

/-- The front output for the closed branch kernel (the φ-merge `DTransOut`). -/
noncomputable def condFrontOut : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty condClosedKernel).get condFront_translates

/-- The tracked output slot `o` in the front output. -/
noncomputable def condRetVar : CVar condFrontOut.Γ' (.sword 64) :=
  ((condFrontOut.vm.lookup "o").get (by rfl)).2

/-- The full φ-merge `Com` (the six-op `bvConst; bvConst; bvConst; bvEq; not; ite`
    prefix applied to the return of the output slot). -/
noncomputable def condFrontCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (condFrontOut.cont (Com.ret (toVIRVar condRetVar))).get (by rfl)

/-- **`condBackend_declines` — the wall, as a theorem.** The VIR `Com`→jasmin
    lowering `cryptoDialectToJasminCom` returns `none` on the φ-merge `Com`: the
    `.bvEq` / `.not` / `.ite` ops the select emits are outside the straight-line
    fragment `toJExprD` lowers, so the owned backend cannot emit the branch through
    this route. This is exactly the `hEmit` edge `condKernel_bytes_of_emit` leaves
    open — a genuine conditional select is the precise point at which the present
    `Com` pipeline stops short of bytes. -/
theorem condBackend_declines : cryptoDialectToJasminCom condFrontCom = none := by rfl

end CatCrypt.Crypto.SecureCompilation.Ascent

#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.condKernel_ascends
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.condKernel_bytes_of_emit
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.condFront_translates
#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.condBackend_declines
