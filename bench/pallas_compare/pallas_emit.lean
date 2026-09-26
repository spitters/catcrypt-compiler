/-
Compile the AUCurves verified-CT Bernstein-Yang safegcd inversion leaf
**from a pure-Lean wrapper** through the full verified compiler chain —
the Pallas Fp sibling of `../SSProve-lean/bench/bls12381_safegcd_compare/bls12381_safegcd_emit.lean`:

  safegcdPallasInvertLean    (pure Lean, opaque single-call body)
    --(reflect surface; LowCTReflect)--->  LowCT
    --translateDialectControl------------>  Com[catCryptDialect]
    --cryptoDialectToJasminCom----------->  Com[jasmin]
    --emitAbiOrchRegPtr (typed reg-ptr)--->  .jazz

The emitted `.jazz` is the verified-front denotation of the pure-Lean
`safegcdPallasInvertLean` modulo the named `pallas_invert_divstep_sat`
leaf's opaque semantics (declared in `CatCrypt/Crypto/Vale/Pallas.lean`
as the AUCurves verified-CT Bernstein-Yang divstep modular inversion
for the Pallas base prime `p = 2^254 + 45560315531419706090280762371685220353`).

This is Step 3 of the BY/safegcd wave-2 Pallas leaf adoption (the
Pasta-cycle BY/safegcd surface). The single-`RCall` body is hand-built
(same pattern as `VaesReflect.vaesEnc2WayBody` /
`SafegcdBLS12_381.safegcdBls12_381InvertBody`) because the front-end
`reifyLowCT%` macro reads `knownOps` only; the resulting `LowCT`
is the body the reifier would produce for `safegcdPallasInvertLean`.

ABI shape: 1 × `TBytes 32` (the secret Fp element) → `TBytes 32` (the
modular inverse `x^{-1} mod p_{Pallas}`). At link time the leaf symbol
`pallas_invert_divstep_sat` is the AUCurves Rust staticlib export.

Invoke:  lake env lean bench/pallas_compare/pallas_emit.lean
-/
module

public import CatCrypt.Crypto.Vale.Pallas
public import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom


@[expose] public section
namespace CatCrypt.Crypto.SecureCompilation.VIR.PallasFromLowCT

open CatCrypt.Crypto.Vale.Pallas
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge

/-! ## 1. CryptoSSA encoding

`encodeTy` sends `TBytes 32` → `memref 4` (four `u64` limbs, the
canonical 256-bit packing — here used to carry the 32-byte Pallas Fp
element through the SSA backend). -/

abbrev MFp : CryptoTy := CryptoTy.memref 4

/-! ## 2. Argument context + name resolver

One operand in the order the leaf C signature consumes it:
`x` (secret Fp element). -/

def argCtx : Ctx := [MFp]

def argVM : VarMap argCtx where
  lookup := fun s =>
    if s = "x" then some ⟨MFp, .here⟩
    else none

/-! ## 3. Drive the verified front end to end

The live emit path: `translateDialectControl` (LowCT → `Com catCryptDialect`)
then `cryptoDialectToJasminCom` (`Com catCryptDialect` → `Com jasminDialect`),
closing the `ComCont` prefix with `ret <retVar>`, then the typed-ABI `.jazz`
printer. -/

def emitDialectRegPtr {Γ : Ctx} (vm : VarMap Γ) (body : LowCT) (retName name : String) :
    Option String :=
  match translateDialectControl vm body with
  | none => none
  | some o =>
    match o.vm.lookup retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiOrchRegPtr name c)

def emitDialectStub {Γ : Ctx} (vm : VarMap Γ) (body : LowCT) (retName name : String) :
    Option String :=
  match translateDialectControl vm body with
  | none => none
  | some o =>
    match o.vm.lookup retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiJazz name c)

def emitDialectLink {Γ : Ctx} (vm : VarMap Γ) (body : LowCT) (jinc retName name : String) :
    Option String :=
  match translateDialectControl vm body with
  | none => none
  | some o =>
    match o.vm.lookup retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiJazzWithLeavesRegPtr jinc name c)

def emittedJazz : Option String :=
  emitDialectRegPtr argVM safegcdPallasInvertReified.body safegcdPallasInvertReified.retName
    "pallas_safegcd_invert_rustcmd"
def emittedStubJazz : Option String :=
  emitDialectStub argVM safegcdPallasInvertReified.body safegcdPallasInvertReified.retName
    "pallas_safegcd_invert_rustcmd"
def emittedLinkJazz : Option String :=
  emitDialectLink argVM safegcdPallasInvertReified.body "../include/pallas_safegcd_leaves.jinc"
    safegcdPallasInvertReified.retName "pallas_safegcd_invert_rustcmd"

/-! ## 4. Structural sanity theorems -/

theorem front_fires : emittedJazz.isSome := by native_decide

theorem stub_fires : emittedStubJazz.isSome := by native_decide

theorem link_fires : emittedLinkJazz.isSome := by native_decide

theorem emits_aucurves_leaf :
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "pallas_invert_divstep_sat")) = some true := by
  native_decide

theorem export_abi :
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "export fn pallas_safegcd_invert_rustcmd"
        && JasminPrint.strContains s "u64[4]")) = some true := by
  native_decide

/-! ## 5. The verification claim

**Trust composition.** The verified front discharges the
orchestration (copy-in/leaf-call/copy-out via the typed reg-ptr
ABI). The leaf semantics are the two axioms declared in
`CatCrypt/Crypto/Vale/Pallas.lean`
(`Safegcd_Pallas_invert_denote`, `Safegcd_Pallas_invert_CT`),
which cite the AUCurves Bernstein-Yang divstep correctness proof
(Bernstein-Yang 2019, eprint 2019/266; Pornin 2020 refinement) and
the AUCurves CI valgrind/crabgrind CT verification on the compiled
binary. -/

/-- **Verified compiler chain witness for the AUCurves-leaf Pallas Fp
    inversion path.** -/
theorem safegcd_pallas_chain_correct :
    emittedJazz.isSome ∧
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "pallas_invert_divstep_sat")) = some true :=
  ⟨front_fires, by native_decide⟩

/-! ## 6. Emit driver `main` -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/pallas_compare/gen_com"
  match emittedJazz, emittedStubJazz, emittedLinkJazz with
  | some j, some jStub, some jLink => do
      IO.FS.writeFile
        "bench/pallas_compare/gen_com/pallas_safegcd_invert_from_rustcmd.jazz" j
      IO.FS.writeFile
        "bench/pallas_compare/gen_com/pallas_safegcd_invert_from_rustcmd_stub.jazz" jStub
      IO.FS.writeFile
        "bench/pallas_compare/gen_com/pallas_safegcd_invert_from_rustcmd_link.jazz" jLink
      IO.println
        "wrote gen_com/pallas_safegcd_invert_from_rustcmd{,_stub,_link}.jazz"
      IO.println "----- AUCurves BY/safegcd Pallas Fp invert (orch) -----"
      IO.println j
  | _, _, _ =>
      IO.println "FAILED: front did not fire (check arg names / retName / encoding)"

#eval main

#print axioms safegcd_pallas_chain_correct

end CatCrypt.Crypto.SecureCompilation.VIR.PallasFromLowCT
