/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# FRONT-COMPILED BabyBear field kernels (bucket-C flip: FriFold + Poseidon2 vocab)

Re-sources the hand-CPS `Com jasminDialect` field kernels of `Plonky3FriFoldEmit`
(and the shared BabyBear reduction vocabulary of `Plonky3LdeColumnEmit`,
`Poseidon2Emit`, `Poseidon2WholePermCom`) through the verified front, exactly the
way `KeccakRoundFrontEmit` re-sources a Keccak round: each field op is a single
`RScalarSetExpr` over named scalar slots, the statement list is pushed through
`translateDialectControl` and lowered by `cryptoDialectToJasminCom` to a
`Com jasminDialect`. No de-Bruijn `Com` binding chain is hand-authored.

The field vocabulary is `SAdd`/`SSub`/`SMul`/`SShr`/`SAnd` over `SVar`/`SLit`
(all pre-existing SExpr ops); `SSub` lowers to `regArith .sub` (wrapping), so the
branchless Barrett/csub arithmetic renders correctly even though the abstract
`SSub` denotation saturates. The front inserts a per-`RScalarSetExpr` identity
copy (`shlImm 0`) and a `regConst` per `SLit`, so the front `Com` is ~2.7×
larger than the hand `Com` (a 12-op Barrett `bbMul` → 33 bindings); `emitAbiOrchReg`
is positional, so re-rendering the deployed leaf needs a fresh dst-slot map keyed
to this expanded binding sequence (the orchestrator step, gated on the bench KAT).

Validated end-to-end through `native_decide` (no compositional lemma needed):
* `bbMulFrontCom` — one Barrett multiply (33 bindings);
* `friFoldFrontCom` — the full single-coset fold incl. the 60-mul Fermat inverse
  (2168 bindings) — `isSome` + `allPureArith` both `native_decide`-clean, so the
  translation survives well past the hand code's ~2500-binding *render* wall;
* `reduceFrontCom` — the Poseidon2 `bbReduce` (10 folds + 2 csubs, 138 bindings),
  the fold-reduction vocabulary used by modules 3 & 4.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

set_option autoImplicit false

abbrev r64 : JasminTy := .reg 64

/-- BabyBear prime, Barrett MU. -/
def pLit : Nat := 2013265921
def muLit : Nat := 2290649223

/-! ## Field-op LowCT combinators (each op = one RScalarSetExpr) -/

/-- csub in place on slot `d` (reads `d`, writes scratch `sx`,`sq`, then `d`). -/
def sCsub (d : String) : List LowCT :=
  [ .RScalarSetExpr "sq" (.SSub (.SVar d) (.SLit pLit)),
    .RScalarSetExpr "sx" (.SShr (.SVar "sq") (.SLit 63)),
    .RScalarSetExpr "sx" (.SSub (.SLit 0) (.SVar "sx")),
    .RScalarSetExpr "sx" (.SAnd (.SVar "sx") (.SLit pLit)),
    .RScalarSetExpr d    (.SAdd (.SVar "sq") (.SVar "sx")) ]

/-- Barrett multiply `d = a*b mod p` (a,b are SExpr reads). -/
def sBBMul (d : String) (a b : SExpr) : List LowCT :=
  [ .RScalarSetExpr "sx" (.SMul a b),
    .RScalarSetExpr "sq" (.SShr (.SVar "sx") (.SLit 30)),
    .RScalarSetExpr "sq" (.SMul (.SVar "sq") (.SLit muLit)),
    .RScalarSetExpr "sq" (.SShr (.SVar "sq") (.SLit 32)),
    .RScalarSetExpr "sq" (.SMul (.SVar "sq") (.SLit pLit)),
    .RScalarSetExpr "sx" (.SSub (.SVar "sx") (.SVar "sq")),
    .RScalarSetExpr d    (.SAdd (.SVar "sx") (.SLit 0)) ] ++ sCsub d

/-- `d = a + b mod p`. -/
def sBBAdd (d : String) (a b : SExpr) : List LowCT :=
  .RScalarSetExpr d (.SAdd a b) :: sCsub d

/-- `d = a - b mod p` via `a + p - b`. -/
def sBBSub (d : String) (a b : SExpr) : List LowCT :=
  [ .RScalarSetExpr d (.SAdd a (.SLit pLit)),
    .RScalarSetExpr d (.SSub (.SVar d) b) ] ++ sCsub d

def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## Single-bbMul validation kernel

Inputs: two words `a`,`b`.  Output: `d = a*b mod p`. -/

def bbMulBody : LowCT := seqAll (sBBMul "d" (.SVar "a") (.SVar "b"))

abbrev nIn2 : Nat := 2
def srcCtx2 : Ctx := List.replicate nIn2 (.sword 64)
def srcVM2 : VarMap srcCtx2 := (VarMap.empty.bind "b").bind "a"

def frontComAt (vm : VarMap srcCtx2) (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx2 (.sword 64)) :=
  match translateDialectControl vm body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

def bbMulLoweredOpt :=
  (frontComAt srcVM2 bbMulBody "d").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem bbMulLowered_isSome : bbMulLoweredOpt.isSome := by native_decide

def bbMulFrontCom : Com jasminDialect (List.replicate nIn2 r64) r64 :=
  bbMulLoweredOpt.get bbMulLowered_isSome

/-- Pure-arith binding predicate (regArith / regConst / shlImm / shrImm). -/
def allPureArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body =>
    (match e.op with
     | .regArith _ _ => true
     | .regConst _ _ => true
     | .shlImm _ _ => true
     | .shrImm _ _ => true
     | _ => false) && allPureArith body

theorem bbMulFront_is_purearith : allPureArith bbMulFrontCom = true := by native_decide

def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

def bbMulFront_bindings : Nat := comBindings bbMulFrontCom

#eval bbMulFront_bindings

/-! ## Full friFold front body (tractability test) -/

/-- lsb-first bits of `p-2 = 2013265919`. -/
def pMinus2Bits : List Bool :=
  [true, true, true, true, true, true, true, true, true, true, true, true,
   true, true, true, true, true, true, true, true, true, true, true, true,
   true, true, true, false, true, true, true]

/-- Fermat square-and-multiply: `res^(p-2)` with `res`←1, `base`←seed. -/
def sFermat (res base : String) : List Bool → List LowCT
  | [] => []
  | b :: rest =>
      let mulPart := if b then sBBMul res (.SVar res) (.SVar base) else []
      let sqPart := if rest.isEmpty then [] else sBBMul base (.SVar base) (.SVar base)
      mulPart ++ sqPart ++ sFermat res base rest

/-- The full single-coset friFold arithmetic as a LowCT statement list.
    Inputs: `ep en xx al`.  Output slot: `result`. -/
def foldStmts : List LowCT :=
  sBBAdd "sum" (.SVar "ep") (.SVar "en") ++
  sBBSub "diff" (.SVar "ep") (.SVar "en") ++
  sBBMul "twoX" (.SLit 2) (.SVar "xx") ++
  [ .RScalarSetExpr "invTwoX" (.SLit 1),
    .RScalarSetExpr "curBase" (.SVar "twoX") ] ++
  sFermat "invTwoX" "curBase" pMinus2Bits ++
  sBBMul "pEven" (.SVar "sum") (.SLit 1006632961) ++
  sBBMul "pOdd" (.SVar "diff") (.SVar "invTwoX") ++
  sBBMul "tt" (.SVar "al") (.SVar "pOdd") ++
  sBBAdd "result" (.SVar "pEven") (.SVar "tt")

def foldBody : LowCT := seqAll foldStmts

abbrev nIn4 : Nat := 4
def srcCtx4 : Ctx := List.replicate nIn4 (.sword 64)
def srcVM4 : VarMap srcCtx4 :=
  (((VarMap.empty.bind "al").bind "xx").bind "en").bind "ep"

def frontComAt4 (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx4 (.sword 64)) :=
  match translateDialectControl srcVM4 body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

def foldLoweredOpt :=
  (frontComAt4 foldBody "result").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem foldLowered_isSome : foldLoweredOpt.isSome := by native_decide

def friFoldFrontCom : Com jasminDialect (List.replicate nIn4 r64) r64 :=
  foldLoweredOpt.get foldLowered_isSome

theorem friFoldFront_is_purearith : allPureArith friFoldFrontCom = true := by native_decide

def friFoldFront_bindings : Nat := comBindings friFoldFrontCom

#eval friFoldFront_bindings

/-! ## Poseidon2 BabyBear reduction vocabulary (modules 3 & 4 validation)

`bbFold x = (x>>>31)*C + (x&M)`; `bbReduce` = 10 folds then 2 csubs; the
Poseidon2 `emitReduce`/`emitFold`/`emitCsub` op set (SShr/SMul/SAnd/SAdd/SSub). -/

def cC : Nat := 134217727
def cM : Nat := 2147483647

/-- One fold `d = (src>>>31)*C + (src & M)`. -/
def sFold (d src : String) : List LowCT :=
  [ .RScalarSetExpr "sq" (.SShr (.SVar src) (.SLit 31)),
    .RScalarSetExpr "sq" (.SMul (.SVar "sq") (.SLit cC)),
    .RScalarSetExpr "sx" (.SAnd (.SVar src) (.SLit cM)),
    .RScalarSetExpr d    (.SAdd (.SVar "sq") (.SVar "sx")) ]

/-- Poseidon2-style csub (matches `Poseidon2WholePermCom.emitCsub`). -/
def sCsubP (d src : String) : List LowCT :=
  [ .RScalarSetExpr "sq" (.SSub (.SVar src) (.SLit pLit)),
    .RScalarSetExpr "sx" (.SShr (.SVar "sq") (.SLit 63)),
    .RScalarSetExpr "sx" (.SSub (.SLit 0) (.SVar "sx")),
    .RScalarSetExpr "sx" (.SAnd (.SLit pLit) (.SVar "sx")),
    .RScalarSetExpr d    (.SAdd (.SVar "sq") (.SVar "sx")) ]

/-- `bbReduce d src` = fold into d, 9 more folds in place, 2 csubs in place. -/
def sReduce (d src : String) : List LowCT :=
  sFold d src ++
  (List.range 9).flatMap (fun _ => sFold d d) ++
  sCsubP d d ++ sCsubP d d

def reduceBody : LowCT := seqAll (sReduce "d" "a")

def srcVMR : VarMap srcCtx2 := (VarMap.empty.bind "b").bind "a"

def reduceLoweredOpt :=
  (frontComAt srcVMR reduceBody "d").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem reduceLowered_isSome : reduceLoweredOpt.isSome := by native_decide

def reduceFrontCom : Com jasminDialect (List.replicate nIn2 r64) r64 :=
  reduceLoweredOpt.get reduceLowered_isSome

theorem reduceFront_is_purearith : allPureArith reduceFrontCom = true := by native_decide

#eval comBindings reduceFrontCom

/-! ## Standalone `bb_inv` front body (`a ↦ a^(p-2)`)

Input: one word `a`.  Output: `invTwoX = a^(p-2)`. -/

def bbInvStmts : List LowCT :=
  [ .RScalarSetExpr "invTwoX" (.SLit 1),
    .RScalarSetExpr "curBase" (.SVar "a") ] ++
  sFermat "invTwoX" "curBase" pMinus2Bits

def bbInvBody : LowCT := seqAll bbInvStmts

abbrev nIn1 : Nat := 1
def srcCtx1 : Ctx := List.replicate nIn1 (.sword 64)
def srcVM1 : VarMap srcCtx1 := VarMap.empty.bind "a"

def frontComAt1 (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx1 (.sword 64)) :=
  match translateDialectControl srcVM1 body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

def bbInvLoweredOpt :=
  (frontComAt1 bbInvBody "invTwoX").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem bbInvLowered_isSome : bbInvLoweredOpt.isSome := by native_decide

def bbInvFrontCom : Com jasminDialect (List.replicate nIn1 r64) r64 :=
  bbInvLoweredOpt.get bbInvLowered_isSome

theorem bbInvFront_is_purearith : allPureArith bbInvFrontCom = true := by native_decide

/-! ## Owned-backend emit (`fri_fold_rc`, `bb_inv_rc`) — the DEPLOYED `.s`

Renders the FRONT `Com`s straight to AT&T `.s` via the owned x86 backend
(`Com.toLprogPhysAbi ∘ renderLprogAtt`), the same route as
`Plonky3EmitMain`'s hand-Com leaves and the CROSS / FieldWidenMul flips. No
`emitAbiOrchReg` de-Bruijn dst-map: the owned RA assigns registers. All field
constants are `SLit`-materialized inside the `Com` (rendered as `regConst`/imm),
so BOTH functions take only their runtime words: `fri_fold_rc` reads `inp[0..3]`
(ep,en,x,alpha), `bb_inv_rc` reads `inp[0]` (a) — the exact word offsets the
existing `fri_fold_from_rustcmd_kat.c` harness writes (it zero-fills a 16-word
`inp`; the unused high words are never loaded). One output word each. -/

/-- `out[0..nOut-1]` store map: output word `j` → `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- All `nIn` input words are runtime loads from `[RSI + 8·idx]` (no immediates;
    field constants live inside the `Com` as `regConst`). Argument slot `s`
    corresponds to input word `nIn - 1 - s` (`comToLfundef`'s De Bruijn reversal). -/
def runtimeInLoad (nIn : Nat) : InLoadMap :=
  fun s => if s < nIn then some ("RSI", (nIn - 1 - s) * 8) else none

/-- `fri_fold_rc`: 4 runtime words `inp[0..3]`, 1 output word. -/
def friFoldFrontLprog : Lprog :=
  Com.toLprogPhysAbi friFoldFrontCom
    "fri_fold_rc" (fun _ => none) (fun _ => none) (runtimeInLoad nIn4) (stdOutStore 1)

/-- `bb_inv_rc`: 1 runtime word `inp[0]`, 1 output word. -/
def bbInvFrontLprog : Lprog :=
  Com.toLprogPhysAbi bbInvFrontCom
    "bb_inv_rc" (fun _ => none) (fun _ => none) (runtimeInLoad nIn1) (stdOutStore 1)

/-- Both FRI leaves in one `Lprog` (two `lp_funcs`) → one `.s`. -/
def friFrontLprog : Lprog :=
  { friFoldFrontLprog with
    lp_funcs := friFoldFrontLprog.lp_funcs ++ bbInvFrontLprog.lp_funcs }

/-- The deployed owned `.s` (front-sourced), written to
    `gen_com/fri_fold_from_rustcmd_owned.s`.

    No `# UNHANDLED-OP` can occur: `friFoldFront_is_purearith` /
    `bbInvFront_is_purearith` confine both `Com`s to `regArith`/`regConst`/
    `shlImm`/`shrImm`, and `JasminLprogExport.opToLinstrR` renders exactly those
    four (`regArith`→`Lopn`, `regConst`→`MOV #imm`, `shlImm`→`SHL:n`,
    `shrImm`→`SHR:n`). The byte identity to the `fri_fold`/`bbInv` spec is the
    external `cc` KAT (`fri_fold_from_rustcmd_kat.c`, relinked). -/
def friFrontAsm : String := renderLprogAtt friFrontLprog

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldFrontEmit
