/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public import CatCrypt.Crypto.SecureCompilation.VIR.ArrAbiOrch
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.Pairing.Bls12381Emit
public import CatCrypt.Crypto.Pairing.Bls12381Emit
public meta import CatCrypt.Crypto.Pairing.Bn254Emit
public import CatCrypt.Crypto.Pairing.Bn254Emit
public meta import CatCrypt.Crypto.Pairing.P256Emit
public import CatCrypt.Crypto.Pairing.P256Emit
public meta import CatCrypt.Crypto.Pairing.Secp256k1Emit
public import CatCrypt.Crypto.Pairing.Secp256k1Emit

/-!
# EC / pairing orchestration through the OWNED x86 backend (no jasminc)

The EC/pairing verifier-equation + MSM-term `Com`s in `Pairing.{Bls12381,Bn254,
P256,Secp256k1}Emit` are straight-line compositions of opaque `.extCall` leaves
over `.stackArr` G1/G2/GT point buffers. Previously they were emitted as jasmin
`.jazz` and a *structural* well-formedness was validated by **jasminc** (the
`gen/*.s: jasminc …` rule, with stub leaves in `*_leaves.jinc`). This driver
emits the SAME orchestrations through the **OWNED** backend instead:

    orchestration `Com`  --Com.toLprogArrAbi (array-ABI gather/scatter)-->  Lprog
                         --renderLprogAtt (LprogAsmPrinter)-->              AT&T `.s`

The array-ABI (`JasminLprogExport.comToLfundefArrAbi`) marshals each `.stackArr`
operand **by pointer** (`leaq` its buffer into the SysV argument register, the
out-buffer into `RDI`), `call`s the opaque leaf, and scatters the result. The
emitted `.s` assembles with `as`/`cc` — NO jasminc. The opaque EC/pairing leaves
(`bls12_pairing`, `g1_add`, `fp12_mul`, `p256_point_add`, …) stay `call`s
resolved at link time against the verified AUCurves / blst tower (the same
primitives `bench/kzg/src/aucurves_backend.rs` rust-cmd-links), exactly the
`EcLeafAgrees` / `PairingLeavesAgree` leaf edge.

## What is owned vs what stays a leaf

The **orchestration** (the verifier equation / MSM-term straight-line gather →
`call` → scatter glue) is owned-emitted. The **leaf** (a G1 point-add, a
scalar-mul, the Miller-loop+final-exp pairing, an `Fp12` product) stays a
`call <leaf>` to the verified AUCurves leaf: the Miller loop + final
exponentiation is opaque and is never owned. The value meaning is
carried by the `*_denote` theorems in the `*Emit` files (e.g.
`Bls12381Emit.groth16VerifyRhsCom_denote`), reducing the orchestration `Com` to
the abstract BLS/EC primitives under the carried leaf agreements; this emit does
not touch the `Com`, so those agreements are untouched.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.EcPairingEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchestrationFront (buildOrchCom)

/-! ## 1. The owned `Lprog`s (one per orchestration), merged per curve -/

/-- BLS12-381 orchestrations: G1 MSM term, BLS/KZG single-pairing verify, and the
    Groth16 RHS pairing-product, all in one `.s`. -/
def bls12381Lprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs :=
      (Com.toLprogArrAbi Bls12381Emit.g1MsmTermCom "bls_g1_msm_step").lp_funcs
      ++ (Com.toLprogArrAbi Bls12381Emit.blsVerifyLhsCom "bls_verify").lp_funcs
      ++ (Com.toLprogArrAbi Bls12381Emit.kzgVerifyLhsCom "kzg_verify").lp_funcs
      ++ (Com.toLprogArrAbi Bls12381Emit.groth16VerifyRhsCom "groth16_verify").lp_funcs }

/-- BN254 orchestrations: G1 MSM term, the single pairing, and the EIP-197 2-pair
    product check. -/
def bn254Lprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs :=
      (Com.toLprogArrAbi Bn254Emit.g1MsmTermCom "bn254_g1_msm_step").lp_funcs
      ++ (Com.toLprogArrAbi Bn254Emit.pairingCom "bn254_pairing_verify").lp_funcs
      ++ (Com.toLprogArrAbi Bn254Emit.eip197VerifyCom "bn254_eip197_verify").lp_funcs }

/-- P-256 orchestrations: the MSM term and the ECDSA `R' = u₁·G + u₂·Q` verify. -/
def p256Lprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs :=
      (Com.toLprogArrAbi P256Emit.msmTermCom "p256_msm_step").lp_funcs
      ++ (Com.toLprogArrAbi P256Emit.ecdsaVerifyCom "p256_ecdsa_verify").lp_funcs }

/-- secp256k1 orchestrations: the MSM term and the ECDSA verify. -/
def secp256k1Lprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs :=
      (Com.toLprogArrAbi Secp256k1Emit.msmTermCom "secp256k1_msm_step").lp_funcs
      ++ (Com.toLprogArrAbi Secp256k1Emit.ecdsaVerifyCom "secp256k1_ecdsa_verify").lp_funcs }

/-! ## 1b. Front provenance (each deployed orchestration is `buildOrchCom`-sourced)

Every `Com` the driver above marshals through `Com.toLprogArrAbi` is its `*Emit`
module's `OrchestrationFront`-generated kernel — the `buildOrchCom <ctxt>
<schedule> <n> <retTy>` output (the phase-scheduled straight-line gather → `call`
→ scatter leaf orchestration). The equalities below name that front lowering
(`buildOrchCom`) for each deployed symbol; each is `rfl` up to the front's
`Option.get` on the `*Com_isSome` witness (proved by `rfl` in the `*Emit`
module). Only the owned array-ABI render tail (`Com.toLprogArrAbi` /
`renderLprogAtt`) is local. -/

theorem bls12381_g1MsmTermCom_front_sourced :
    buildOrchCom [.stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.FPSZ,
      .stackArr 8 Bls12381Emit.G1SZ] Bls12381Emit.g1MsmTermSchedule 4
      (.stackArr 8 Bls12381Emit.G1SZ) = some Bls12381Emit.g1MsmTermCom :=
  (Option.some_get Bls12381Emit.g1MsmTermCom_isSome).symm

theorem bls12381_blsVerifyLhsCom_front_sourced :
    buildOrchCom [.stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.G2SZ]
      Bls12381Emit.singlePairingLhsSchedule 2 (.stackArr 8 Bls12381Emit.GTSZ)
      = some Bls12381Emit.blsVerifyLhsCom :=
  (Option.some_get Bls12381Emit.blsVerifyLhsCom_isSome).symm

theorem bls12381_kzgVerifyLhsCom_front_sourced :
    buildOrchCom [.stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.G2SZ]
      Bls12381Emit.singlePairingLhsSchedule 2 (.stackArr 8 Bls12381Emit.GTSZ)
      = some Bls12381Emit.kzgVerifyLhsCom :=
  (Option.some_get Bls12381Emit.kzgVerifyLhsCom_isSome).symm

theorem bls12381_groth16VerifyRhsCom_front_sourced :
    buildOrchCom
      [.stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.G2SZ,
       .stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.G2SZ,
       .stackArr 8 Bls12381Emit.G1SZ, .stackArr 8 Bls12381Emit.G2SZ]
      Bls12381Emit.groth16VerifyRhsSchedule 10 (.stackArr 8 Bls12381Emit.GTSZ)
      = some Bls12381Emit.groth16VerifyRhsCom :=
  (Option.some_get Bls12381Emit.groth16VerifyRhsCom_isSome).symm

theorem bn254_g1MsmTermCom_front_sourced :
    buildOrchCom Bn254Emit.g1MsmTermCtxt Bn254Emit.g1MsmTermSchedule 4
      Bn254Emit.g1RetTy = some Bn254Emit.g1MsmTermCom :=
  (Option.some_get Bn254Emit.g1MsmTermCom_isSome).symm

theorem bn254_pairingCom_front_sourced :
    buildOrchCom Bn254Emit.pairingCtxt Bn254Emit.pairingSchedule 2
      Bn254Emit.gtRetTy = some Bn254Emit.pairingCom :=
  (Option.some_get Bn254Emit.pairingCom_isSome).symm

theorem bn254_eip197VerifyCom_front_sourced :
    buildOrchCom Bn254Emit.eip197VerifyCtxt Bn254Emit.eip197VerifySchedule 6
      Bn254Emit.gtRetTy = some Bn254Emit.eip197VerifyCom :=
  (Option.some_get Bn254Emit.eip197VerifyCom_isSome).symm

theorem p256_msmTermCom_front_sourced :
    buildOrchCom P256Emit.msmTermCtxt P256Emit.msmTermSchedule 4
      P256Emit.ptRetTy = some P256Emit.msmTermCom :=
  (Option.some_get P256Emit.msmTermCom_isSome).symm

theorem p256_ecdsaVerifyCom_front_sourced :
    buildOrchCom P256Emit.ecdsaVerifyCtxt P256Emit.ecdsaVerifySchedule 6
      P256Emit.ptRetTy = some P256Emit.ecdsaVerifyCom :=
  (Option.some_get P256Emit.ecdsaVerifyCom_isSome).symm

theorem secp256k1_msmTermCom_front_sourced :
    buildOrchCom Secp256k1Emit.msmTermCtxt Secp256k1Emit.msmTermSchedule 4
      Secp256k1Emit.ptRetTy = some Secp256k1Emit.msmTermCom :=
  (Option.some_get Secp256k1Emit.msmTermCom_isSome).symm

theorem secp256k1_ecdsaVerifyCom_front_sourced :
    buildOrchCom Secp256k1Emit.ecdsaVerifyCtxt Secp256k1Emit.ecdsaVerifySchedule 6
      Secp256k1Emit.ptRetTy = some Secp256k1Emit.ecdsaVerifyCom :=
  (Option.some_get Secp256k1Emit.ecdsaVerifyCom_isSome).symm

/-! ## 2. The rendered AT&T `.s` blobs -/

def bls12381Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned bls12381Lprog
def bn254Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned bn254Lprog
def p256Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned p256Lprog
def secp256k1Asm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned secp256k1Lprog

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 4. Emit driver -/

/-- Write the four owned `.s` blobs to `bench/<curve>_compare/gen_com/`. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/bls12381_compare/gen_com"
  IO.FS.createDirAll "bench/bn254_compare/gen_com"
  IO.FS.createDirAll "bench/p256_compare/gen_com"
  IO.FS.createDirAll "bench/secp256k1_compare/gen_com"
  IO.FS.writeFile "bench/bls12381_compare/gen_com/bls12381_orch_owned.s" bls12381Asm
  IO.FS.writeFile "bench/bn254_compare/gen_com/bn254_orch_owned.s" bn254Asm
  IO.FS.writeFile "bench/p256_compare/gen_com/p256_orch_owned.s" p256Asm
  IO.FS.writeFile "bench/secp256k1_compare/gen_com/secp256k1_orch_owned.s" secp256k1Asm
  IO.println "wrote owned EC/pairing orchestration .s (no jasminc):"
  IO.println "  bench/bls12381_compare/gen_com/bls12381_orch_owned.s"
  IO.println "  bench/bn254_compare/gen_com/bn254_orch_owned.s"
  IO.println "  bench/p256_compare/gen_com/p256_orch_owned.s"
  IO.println "  bench/secp256k1_compare/gen_com/secp256k1_orch_owned.s"

/-! ## Artifact generation at elaboration

The four renders are written while this module elaborates, so `lake` produces
them from this file and no separate driver or Makefile rule carries the
dependency. -/

-- #eval emitMain

end CatCrypt.Crypto.Pairing.EcPairingEmit
