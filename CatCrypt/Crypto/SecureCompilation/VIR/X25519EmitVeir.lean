/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitMLIR
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_CatCryptDialect

/-!
# Path (b): X25519 ladder-step emission through Veir

Mirror of `X25519EmitMLIR` that lowers the same `Com` programs through
the Veir IR (`Com → Veir.IRContext → MLIR text`) instead of CatCrypt's
in-tree printer.

The `Com` definitions (`halfStep`, `fullStep_x2p`, …) are reused
verbatim from `X25519EmitMLIR`; only the printing path differs. Each
program is wrapped in a `func.func` op via `lowerClosedComToFunc`:
inputs become block arguments, the body lowers into the entry block,
and a `func.return` terminator carries the final value.

The lowering emits `func.call` ops (with `callee = @<name>`
symbol-ref attributes) for `extCall`, and a `catcrypt.unknown`
dialect tag for ops with no Veir-side counterpart. `mlir-opt`
accepts the output under `--allow-unregistered-dialect` once the
caller wraps it in a `builtin.module` containing private extern
declarations for each callee. The emitter does *not* generate those
extern declarations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitVeir

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitMLIR
  (Fp25519Ty StepCtx FullCtx halfStep
   fullStep_x2p fullStep_z2p fullStep_x3p fullStep_z3p)

/-! ## End-to-end pipeline -/

/-- Lower a (possibly-open) `Com` over `catCryptDialect` to MLIR text
    via the Veir backend. The context `Γ` becomes block arguments of
    the entry block of a `func.func` op named `funcName`; the
    `Com.ret` is carried by an explicit `func.return` terminator;
    the whole thing is wrapped in a `builtin.module` containing
    private `func.func` decls for each extern callee.

    Output round-trips through `mlir-opt --allow-unregistered-dialect`
    (LLVM 20+) without manual extern wrapping. -/
def emitFuncToVeirText {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (com : Com catCryptDialect Γ t) (funcName : String) : IO String := do
  let externs := dedupExternsByName (Com.catcryptExterns com)
  let (ctx, modOp) :=
    lowerClosedComToModuleWithExterns (d := catCryptDialect) com externs
      (Veir.OpCode.builtin .module) default
      (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
      (Veir.OpCode.func .return) default
      funcName
  VeirPrinterShim.printModuleToString ctx modOp

/-! ## Emit functions -/

def emitHalfStepVeir : IO String :=
  emitFuncToVeirText halfStep "x25519_halfstep"

def emitFullStepX2pVeir : IO String :=
  emitFuncToVeirText fullStep_x2p "x25519_step_x2"
def emitFullStepZ2pVeir : IO String :=
  emitFuncToVeirText fullStep_z2p "x25519_step_z2"
def emitFullStepX3pVeir : IO String :=
  emitFuncToVeirText fullStep_x3p "x25519_step_x3"
def emitFullStepZ3pVeir : IO String :=
  emitFuncToVeirText fullStep_z3p "x25519_step_z3"

/-! ## File writers (optional, env-gated like X25519EmitMLIR) -/

private def benchDir : IO (Option System.FilePath) := do
  let some d ← IO.getEnv "CATCRYPT_BENCH_DIR" | return none
  return some d

def writeHalfStepVeir (path : System.FilePath) : IO Unit := do
  IO.FS.writeFile path (← emitHalfStepVeir)

def writeFullStepVeir (path : System.FilePath) : IO Unit := do
  let nl := "\n\n"
  let x2 ← emitFullStepX2pVeir
  let z2 ← emitFullStepZ2pVeir
  let x3 ← emitFullStepX3pVeir
  let z3 ← emitFullStepZ3pVeir
  IO.FS.writeFile path (x2 ++ nl ++ z2 ++ nl ++ x3 ++ nl ++ z3)

-- #eval do
--   let some d ← benchDir | return ()
--   writeHalfStepVeir (d / "x25519_halfstep.veir.mlir")
--   writeFullStepVeir (d / "x25519_fullstep.veir.mlir")

end CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitVeir
