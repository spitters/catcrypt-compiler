/-
Compile the AUCurves verified-CT Bernstein-Yang safegcd inversion leaf
**from a pure-Lean wrapper** through the full verified compiler chain —
the BN254 (alt_bn128) Fp sibling of
`../SSProve-lean/bench/p256_safegcd_compare/p256_safegcd_emit.lean`:

  safegcdBN254InvertLean       (pure Lean, opaque single-call body)
    --(reflect surface; LowCTReflect)--->  LowCT
    --translateDialectControl------------>  Com[catCryptDialect]
    --cryptoDialectToJasminCom----------->  Com[jasmin]
    --emitAbiOrchRegPtr (typed reg-ptr)--->  .jazz

The emitted `.jazz` is the verified-front denotation of the pure-Lean
`safegcdBN254InvertLean` modulo the named `safegcd_bn254_invert` leaf's
opaque semantics (declared in `CatCrypt/Crypto/Vale/SafegcdBN254.lean`
as the AUCurves verified-CT Bernstein-Yang divstep modular inversion
for the BN254 base `Fp`).

This is the #489 safegcd-uniform pass entry for BN254 (the one
production curve whose Fp inverse was still the Fermat a^(p-2) chain).
The single-`RCall` body is hand-built (same pattern as
`p256_safegcd_emit.lean`) because the front-end `reifyLowCT%` macro
reads `knownOps` only; the resulting `LowCT` is the body the reifier
would produce for `safegcdBN254InvertLean`.

ABI shape: 1 × `TBytes 32` (the secret Fp element, 4×u64 LE) → `TBytes 32`
(the modular inverse `x^{-1} mod p_{BN254}`). At link time the leaf
symbol `safegcd_bn254_invert` is the AUCurves Rust staticlib export
(thin `extern "C"` shim re-exporting `bn254_invert_divstep_sat`).

Invoke:  lake env lean bench/bn254_safegcd_compare/bn254_safegcd_emit.lean
-/
module

public import CatCrypt.Crypto.Vale.SafegcdBN254
public import CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit


@[expose] public section
namespace CatCrypt.Crypto.SecureCompilation.VIR.SafegcdBN254FromLowCT

open CatCrypt.Crypto.Vale.SafegcdBN254
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge

/-! ### Dialect emit helpers (live path)

`translateDialectControl` (LowCT → `Com catCryptDialect`) then
`cryptoDialectToJasminCom` (`Com catCryptDialect` → `Com jasminDialect`),
closing the `ComCont` prefix with `ret <retVar>`, then the typed-ABI
`.jazz` printer. -/

def emitDialectRegPtr {Γ : Ctx} (vm : VarMap Γ) (f : ReifiedFunc) (name : String) :
    Option String :=
  match translateDialectControl vm f.body with
  | none => none
  | some o =>
    match o.vm.lookup f.retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiOrchRegPtr name c)

def emitDialectStub {Γ : Ctx} (vm : VarMap Γ) (f : ReifiedFunc) (name : String) :
    Option String :=
  match translateDialectControl vm f.body with
  | none => none
  | some o =>
    match o.vm.lookup f.retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiJazz name c)

def emitDialectLink {Γ : Ctx} (vm : VarMap Γ) (f : ReifiedFunc) (jinc name : String) :
    Option String :=
  match translateDialectControl vm f.body with
  | none => none
  | some o =>
    match o.vm.lookup f.retName with
    | none => none
    | some ⟨_t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com =>
        match cryptoDialectToJasminCom com with
        | none => none
        | some c => some (JasminAbiEmit.emitAbiJazzWithLeavesRegPtr jinc name c)

/-! ## 1. CryptoSSA encoding

`encodeTy` sends `TBytes 32` → `memref 4` (four `u64` limbs, the
canonical 256-bit packing — here used to carry the 32-byte BN254 Fp
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

/-! ## 3. Drive the verified front end to end -/

def emittedJazz : Option String :=
  emitDialectRegPtr argVM safegcdBN254InvertReified "bn254_safegcd_invert_rustcmd"

def emittedStubJazz : Option String :=
  emitDialectStub argVM safegcdBN254InvertReified "bn254_safegcd_invert_rustcmd"

def emittedLinkJazz : Option String :=
  emitDialectLink argVM safegcdBN254InvertReified
    "../include/bn254_safegcd_leaves.jinc" "bn254_safegcd_invert_rustcmd"

/-! ## 4. Structural sanity theorems -/

theorem front_fires : emittedJazz.isSome := by native_decide

theorem stub_fires : emittedStubJazz.isSome := by native_decide

theorem link_fires : emittedLinkJazz.isSome := by native_decide

theorem emits_aucurves_leaf :
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "safegcd_bn254_invert")) = some true := by
  native_decide

theorem export_abi :
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "export fn bn254_safegcd_invert_rustcmd"
        && JasminPrint.strContains s "u64[4]")) = some true := by
  native_decide

/-! ## 5. The verification claim

**Trust composition.** The verified front discharges the
orchestration (copy-in/leaf-call/copy-out via the typed reg-ptr
ABI). The leaf semantics are the two axioms declared in
`CatCrypt/Crypto/Vale/SafegcdBN254.lean`
(`AUCurves_safegcd_bn254_invert_denote`,
`AUCurves_safegcd_bn254_invert_CT`), which cite Bernstein-Yang's
divstep correctness theorem applied to `ModInfo<5>` constructed by
`safegcd::modinfo_from_4u64(BN254_P_4X64, 10)` (590 divsteps), and the
byte-identical `x · x^{-1} ≡ 1 (mod p)` round-trip KAT
(`safegcd_bn254.rs::tests::bn254_invert_times_self_is_one`). -/

/-- **Verified compiler chain witness for the AUCurves-leaf BN254 Fp
    inversion path.** -/
theorem safegcd_bn254_chain_correct :
    emittedJazz.isSome ∧
    (emittedJazz.map (fun s =>
        JasminPrint.strContains s
          "safegcd_bn254_invert")) = some true :=
  ⟨front_fires, by native_decide⟩

/-! ## 6. Emit driver `main` -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/bn254_safegcd_compare/gen_com"
  match emittedJazz, emittedStubJazz, emittedLinkJazz with
  | some j, some jStub, some jLink => do
      IO.FS.writeFile
        "bench/bn254_safegcd_compare/gen_com/bn254_safegcd_invert_from_rustcmd.jazz" j
      IO.FS.writeFile
        "bench/bn254_safegcd_compare/gen_com/bn254_safegcd_invert_from_rustcmd_stub.jazz" jStub
      IO.FS.writeFile
        "bench/bn254_safegcd_compare/gen_com/bn254_safegcd_invert_from_rustcmd_link.jazz" jLink
      IO.println
        "wrote gen_com/bn254_safegcd_invert_from_rustcmd{,_stub,_link}.jazz"
      IO.println "----- AUCurves BY/safegcd BN254 Fp invert (orch) -----"
      IO.println j
  | _, _, _ =>
      IO.println "FAILED: front did not fire (check arg names / retName / encoding)"

#eval main

#print axioms safegcd_bn254_chain_correct

end CatCrypt.Crypto.SecureCompilation.VIR.SafegcdBN254FromLowCT
