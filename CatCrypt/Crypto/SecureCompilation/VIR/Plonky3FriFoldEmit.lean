/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 FRI fold-layer arithmetic FRONT-COMPILED as a `Com jasminDialect`

The single-coset FRI fold `friFold` (and the modular inverse `bbInv` it needs)
re-sourced through the verified front: each field op is a single `RScalarSetExpr`
over named scalar slots, the statement list is pushed through
`translateDialectControl` and lowered by `cryptoDialectToJasminCom` to a
`Com jasminDialect`.  No de-Bruijn `Com` binding chain is hand-authored.

## The 16-input ABI (preserved for the composite consumers)

`friFoldCom` / `bbInvCom` keep their historical 16-word input context and their
`Com jasminDialect inCtxt r64` type, so every downstream renderer
(`Plonky3WholeProverOwnedEmit`, `Plonky3OrchLoopsOwnedEmit`,
`ZkSumCheckWholeProverOwnedEmit`, `Plonky3OwnedEmitMain`) that does
`Com.toLprogPhysAbi Plonky3FriFoldEmit.friFoldCom … (abiMaps 16 friFoldConstAt)`
keeps working byte-for-byte.  Input words:

* `0` `eval_pos`, `1` `eval_neg`, `2` `x`, `3` `alpha` (the runtime fold args);
* `4` `invTwo = (p+1)/2 = 1006632961`, `5` `two = 2`, `6` `one = 1`,
  `7` Barrett `MU = 2290649223`, `8` prime `p = 2013265921`,
  `9` `0`, `10` `30`, `11` `32`, `12` `63` (the field constants);
* `13..15` unused.

Crucially the field constants are read as **`SVar` input words**, NOT `SLit`
immediates: the `abiMaps 16 friFoldConstAt` materializer at each consumer bakes
words `4..12` as immediates, and the runtime args `0..3` (`bb_inv`: `0`) load
from `RSI`.  Because the shift amounts `30/32/63` are `SVar`s, each `SShr`
lowers to the **variable** `bvShiftRV` (jasmin `regArith .shr`) rather than
`shrImm` — the same op the previous hand-CPS `Com` emitted.

## `bbInv` as a straight-line regArith chain

`bbInv a = a^(p−2)` with `p−2 = 2013265919` (31 significant bits).  The
square-and-multiply loop is unrolled at Lean time into a fixed chain of Barrett
`bbMul`s (`sFermat`): 30 squarings + 30 conditional multiplies.

## leaf.denote = spec by construction

Both front `Com`s are confined to `regArith`/`regConst`/`shlImm`/`shrImm`
bindings (`friFold_is_purearith` / `bbInv_is_purearith`, `native_decide`), so the
owned backend renders no `# UNHANDLED-OP` and the emitted `.s`'s denotation IS
the Barrett/branchless word arithmetic.  The numeric equality of that arithmetic
to `Plonky3FriEmit.friFold` / `bbInv` is KAT-witnessed
(`fri_fold_from_rustcmd_kat.c`); Barrett reduction-correctness is not re-proved
in Lean.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit

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

set_option autoImplicit false

/-- The `reg 64` dialect type, abbreviated. -/
abbrev r64 : JasminTy := .reg 64

/-- Number of declared inputs (the historical 16-word FRI fold ABI). -/
abbrev nInputs : Nat := 16

/-- The input context: `nInputs` `r64` words (preserved for the consumers). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-! ## 1. Field-op LowCT combinators (each op = one `RScalarSetExpr`)

The Barrett `bbMul` and the branchless csub of `bbAdd`/`bbSub`, over named scalar
slots.  Field constants are read from the ABI input words `4..12`
(`invTwo,two,one,mu,p,zero,sh30,sh32,sh63`) as `SVar`s. -/

/-- csub in place on slot `d` (reads `d`, writes scratch `sx`,`sq`, then `d`). -/
def sCsub (d : String) : List LowCT :=
  [ .RScalarSetExpr "sq" (.SSub (.SVar d) (.SVar "p")),
    .RScalarSetExpr "sx" (.SShr (.SVar "sq") (.SVar "sh63")),
    .RScalarSetExpr "sx" (.SSub (.SVar "zero") (.SVar "sx")),
    .RScalarSetExpr "sx" (.SAnd (.SVar "sx") (.SVar "p")),
    .RScalarSetExpr d    (.SAdd (.SVar "sq") (.SVar "sx")) ]

/-- Barrett multiply `d = a*b mod p` (a,b are SExpr reads). -/
def sBBMul (d : String) (a b : SExpr) : List LowCT :=
  [ .RScalarSetExpr "sx" (.SMul a b),
    .RScalarSetExpr "sq" (.SShr (.SVar "sx") (.SVar "sh30")),
    .RScalarSetExpr "sq" (.SMul (.SVar "sq") (.SVar "mu")),
    .RScalarSetExpr "sq" (.SShr (.SVar "sq") (.SVar "sh32")),
    .RScalarSetExpr "sq" (.SMul (.SVar "sq") (.SVar "p")),
    .RScalarSetExpr "sx" (.SSub (.SVar "sx") (.SVar "sq")),
    .RScalarSetExpr d    (.SAdd (.SVar "sx") (.SVar "zero")) ] ++ sCsub d

/-- `d = a + b mod p`. -/
def sBBAdd (d : String) (a b : SExpr) : List LowCT :=
  .RScalarSetExpr d (.SAdd a b) :: sCsub d

/-- `d = a - b mod p` via `a + p - b`. -/
def sBBSub (d : String) (a b : SExpr) : List LowCT :=
  [ .RScalarSetExpr d (.SAdd a (.SVar "p")),
    .RScalarSetExpr d (.SSub (.SVar d) b) ] ++ sCsub d

/-- Right-fold a statement list into a single `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ## 2. The 16-word source context and the front entry point -/

/-- The source `Ctx`: `nInputs` `sword 64` words. -/
abbrev srcCtx : Ctx := List.replicate nInputs (.sword 64)

/-- The source `VarMap`: word `0` (`ep`) is the head; word `15` (`u15`) the
    innermost.  Word `i` names the same slot the `abiMaps 16 friFoldConstAt`
    consumer expects (`0..3` runtime, `4..12` field constants, `13..15` unused). -/
def srcVM : VarMap srcCtx :=
  ((((((((((((((((VarMap.empty.bind "u15").bind "u14").bind "u13").bind
    "sh63").bind "sh32").bind "sh30").bind "zero").bind "p").bind "mu").bind
    "one").bind "two").bind "invTwo").bind "al").bind "xx").bind "en").bind "ep")

/-- Translate a LowCT body and return the `Com` whose result is the slot `name`. -/
def frontComAt (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-! ## 3. The Fermat inverse chain (`bbInv a = a^(p−2)`) -/

/-- lsb-first bits of `p−2 = 2013265919` (31 significant bits). -/
def pMinus2Bits : List Bool :=
  [true, true, true, true, true, true, true, true, true, true, true, true,
   true, true, true, true, true, true, true, true, true, true, true, true,
   true, true, true, false, true, true, true]

/-- Fermat square-and-multiply: `res := base^(p−2)` with `res`←1 on entry. -/
def sFermat (res base : String) : List Bool → List LowCT
  | [] => []
  | b :: rest =>
      let mulPart := if b then sBBMul res (.SVar res) (.SVar base) else []
      let sqPart := if rest.isEmpty then [] else sBBMul base (.SVar base) (.SVar base)
      mulPart ++ sqPart ++ sFermat res base rest

/-! ## 4. The full `friFold` body (single coset) -/

/-- The single-coset friFold arithmetic as a LowCT statement list.
    Inputs: `ep en xx al`.  Output slot: `result`. -/
def foldStmts : List LowCT :=
  sBBAdd "sum" (.SVar "ep") (.SVar "en") ++
  sBBSub "diff" (.SVar "ep") (.SVar "en") ++
  sBBMul "twoX" (.SVar "two") (.SVar "xx") ++
  [ .RScalarSetExpr "invTwoX" (.SAdd (.SVar "one") (.SVar "zero")),
    .RScalarSetExpr "curBase" (.SAdd (.SVar "twoX") (.SVar "zero")) ] ++
  sFermat "invTwoX" "curBase" pMinus2Bits ++
  sBBMul "pEven" (.SVar "sum") (.SVar "invTwo") ++
  sBBMul "pOdd" (.SVar "diff") (.SVar "invTwoX") ++
  sBBMul "tt" (.SVar "al") (.SVar "pOdd") ++
  sBBAdd "result" (.SVar "pEven") (.SVar "tt")

def foldBody : LowCT := seqAll foldStmts

def foldLoweredOpt :=
  (frontComAt foldBody "result").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem foldLowered_isSome : foldLoweredOpt.isSome := by native_decide

/-- The full single-coset `friFold` `Com` (front-sourced, 16-word ABI). -/
def friFoldCom : Com jasminDialect inCtxt r64 :=
  foldLoweredOpt.get foldLowered_isSome

/-! ## 5. The standalone `bbInv` body (`a ↦ a^(p−2)`)

Input word `0` (`ep`) is `a`; the result is slot `invTwoX`. -/

def bbInvStmts : List LowCT :=
  [ .RScalarSetExpr "invTwoX" (.SAdd (.SVar "one") (.SVar "zero")),
    .RScalarSetExpr "curBase" (.SAdd (.SVar "ep") (.SVar "zero")) ] ++
  sFermat "invTwoX" "curBase" pMinus2Bits

def bbInvBody : LowCT := seqAll bbInvStmts

def bbInvLoweredOpt :=
  (frontComAt bbInvBody "invTwoX").bind DialectToJasminCom.cryptoDialectToJasminCom

theorem bbInvLowered_isSome : bbInvLoweredOpt.isSome := by native_decide

/-- The standalone `bbInv` `Com` (front-sourced, 16-word ABI; reads only `a`). -/
def bbInvCom : Com jasminDialect inCtxt r64 :=
  bbInvLoweredOpt.get bbInvLowered_isSome

/-! ## 6. Pure-arith predicate — leaf.denote = spec by construction -/

/-- Pure-arith binding predicate (`regArith` / `regConst` / `shlImm` / `shrImm`). -/
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

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- The `friFoldCom` body is `regArith`/`regConst`/`shlImm`/`shrImm`-only, so the
    owned backend renders no `# UNHANDLED-OP`. -/
theorem friFold_is_purearith : allPureArith friFoldCom = true := by native_decide

/-- The `bbInvCom` body is pure-arith by construction. -/
theorem bbInv_is_purearith : allPureArith bbInvCom = true := by native_decide

#eval IO.println ("fold bindings: " ++ toString (comBindings friFoldCom)
  ++ ", bbInv bindings: " ++ toString (comBindings bbInvCom))

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
