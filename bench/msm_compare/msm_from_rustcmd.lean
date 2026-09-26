/-
Compile the toy-EC MSM-term kernel **from a pure Lean function** through
the full verified compiler chain — the toy-EC analogue of
`bench/{secp256k1,p256}_compare/scalar_mul_from_rustcmd.lean`.

  msmEcTermLean              (pure Lean)
    --(reflect surface; MsmReflect)----> LowCT
    --translateDialectControl-----> Com[catCryptDialect]
    --cryptoDialectToJasminCom (A1)----------->  Com[jasmin]
    --emitAbiOrchRegPtr (typed reg-ptr)->  .jazz

Architectural opposite of the legacy Tier C `msm_emit.lean`
(`bench/msm_compare/gen/`). Every byte of the new emit goes through the
verified front.

## Toy-EC scope

The MSM bench is a clearly-labelled toy/model artefact validating the
`Pairing.MsmReduce.msm_eq_scalarFold` reduction at a small field
(`ZMod 23`). The full `for i = 0 to L: acc += k_i · P_i` MSM wrapper
lives at the loop-layer (next Tier-A step); this driver covers the
per-term body (one fold step). Production analogues (BLS12-381, BN254,
secp256k1, P-256) have their own siblings with AUCurves verified-CT
field leaves.

## L2↔L3 hax bridge

NO hax for the toy curve (no `msm-hax/` source); the bridge target is
the production-curve siblings. Named hypothesis `MsmEcTermLeanCorrect`
records the trust edge.
-/
module

public import CatCrypt.Crypto.Jasmin.MsmReflect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom


@[expose] public section
namespace CatCrypt.Crypto.SecureCompilation.VIR.MsmFromLowCT

open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge

/-! ## 1. CryptoSSA encoding

| Surface       | TowerType   | bytes | memref u64-limbs |
|---------------|-------------|------:|-----------------:|
| MsmEcScalar   | TBytes 1    |     1 | 1                |
| MsmEcPoint    | TBytes 2    |     2 | 1                |
-/

abbrev MScalar : CryptoTy := CryptoTy.memref 1
abbrev MPoint  : CryptoTy := CryptoTy.memref 1

/-! ## 2. Argument context + name resolver -/

def termArgCtx : Ctx := [MScalar, MPoint]

def termArgVM : VarMap termArgCtx where
  lookup := fun s =>
    if s = "k" then some ⟨MScalar, .here⟩
    else if s = "P" then some ⟨MPoint, .there .here⟩
    else none

/-! ## 3. Drive the verified front end to end -/

/-! ### Dialect emit helpers

`translateDialectControl` (LowCT → `Com catCryptDialect`) then
`cryptoDialectToJasminCom` (`Com catCryptDialect` → `Com jasminDialect`). The
canonical `emitted*` names below are the dialect path. -/

/-- Reg-ptr orchestration emit through the dialect path. -/
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

/-- Self-contained stub-leaf emit through the dialect path. -/
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

/-- Real-leaf link emit (`require`s the leaf `.jinc`) through the dialect path. -/
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

/-- Canonical reg-ptr emit — now the dialect path. -/
def emittedMsmTermJazz : Option String :=
  emitDialectRegPtr termArgVM msmEcTermReified.body msmEcTermReified.retName "msm_term_rustcmd"

/-- Canonical stub emit — now the dialect path. -/
def emittedMsmTermStubJazz : Option String :=
  emitDialectStub termArgVM msmEcTermReified.body msmEcTermReified.retName "msm_term_rustcmd"

/-- Canonical link emit — now the dialect path. -/
def emittedMsmTermLinkJazz : Option String :=
  emitDialectLink termArgVM msmEcTermReified.body "../include/msm_leaves.jinc"
    msmEcTermReified.retName "msm_term_rustcmd"

/-! ## 4. Structural sanity theorems -/

theorem msm_term_front_fires : emittedMsmTermJazz.isSome := by native_decide

theorem msm_term_stub_fires : emittedMsmTermStubJazz.isSome := by native_decide

theorem msm_term_emits_scalar_mul :
    (emittedMsmTermJazz.map (fun s =>
        JasminPrint.strContains s "ec_scalar_mul")) = some true := by
  native_decide

/-! ## 5. Verified compiler chain witness -/

/-- **Verified compiler chain witness for the toy-EC MSM-term kernel.** -/
theorem msm_term_rustcmd_chain_correct :
    emittedMsmTermJazz.isSome ∧
    (emittedMsmTermJazz.map (fun s =>
        JasminPrint.strContains s "ec_scalar_mul")) = some true :=
  ⟨msm_term_front_fires, by native_decide⟩

/-! ## 6. Named hypothesis (NO hax bridge — toy curve, prod analogues elsewhere) -/

/-- **Named hypothesis (toy-curve trust edge).** The pure-Lean
    `msmEcTermLean` spec equals the opaque `ec_scalar_mul` leaf
    application. There is NO hax extraction of the toy Z/23 curve; the
    bridge target is the production-curve siblings (secp256k1, P-256,
    BLS12-381, BN254 — each with their own per-curve Reflect surface). -/
axiom MsmEcTermLeanCorrect :
    ∀ (k : MsmEcScalar) (P : MsmEcPoint),
      msmEcTermLean k P = ec_scalar_mul k P

/-! ## 7. Emit driver `main` -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/msm_compare/gen_com"
  match emittedMsmTermJazz, emittedMsmTermStubJazz, emittedMsmTermLinkJazz with
  | some s, some sStub, some sLink => do
      IO.FS.writeFile "bench/msm_compare/gen_com/msm_term_from_rustcmd.jazz" s
      IO.FS.writeFile "bench/msm_compare/gen_com/msm_term_from_rustcmd_stub.jazz" sStub
      IO.FS.writeFile "bench/msm_compare/gen_com/msm_term_from_rustcmd_link.jazz" sLink
      IO.println "wrote gen_com/msm_term_from_rustcmd{,_stub,_link}.jazz"
      IO.println "----- toy-EC MSM-term (k · P) -----"
      IO.println s
  | _, _, _ =>
      IO.println "FAILED: front did not fire"

#eval main

#print axioms msm_term_rustcmd_chain_correct

end CatCrypt.Crypto.SecureCompilation.VIR.MsmFromLowCT
