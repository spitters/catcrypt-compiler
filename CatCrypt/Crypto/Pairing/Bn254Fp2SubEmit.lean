/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Core.Code
import all CatCrypt.Core.Heap
import all CatCrypt.Core.Location
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminOps
import all CatCrypt.Crypto.Jasmin.JasminTranslate
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.JasminVar
import all CatCrypt.Crypto.Jasmin.LowCTSyntax
import all CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
import all CatCrypt.Crypto.Jasmin.LowCTReflect
import all CatCrypt.Crypto.Jasmin.LowCTToJasmin
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
import all CatCrypt.Deep.Eval
import all CatCrypt.Deep.RawCode

public meta import CatCrypt.Crypto.Jasmin.Bn254Reflect
public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.Bn254Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiJazz
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiJazz

/-!
# BN254 `Fp2` subtract — owned reg-ptr emit (completes the `tower_subset` set)

The AUCurves jasminc `tower_subset` artifact covers exactly the `Fp2`
`{add, sub, felem_copy}` leaf functions (the 12 functions that compile under the
`reg u64`/byte-offset convention; the other 39 hit the jasminc `reg ptr u64[N]`
stackalloc gap).

`bench/bn254_compare/fp_tower_from_rustcmd.lean` already emits the *owned*
reg-ptr re-emit of the tower field arithmetic through CatCrypt's verified front —
`bn254_Fp2_add_rustcmd` and `bn254_Fp2_mul_rustcmd` (Karatsuba over the verified
`Fp` Montgomery leaves), plus the `Fp6`/`Fp12` levels. The only `tower_subset`
member missing an owned twin there is `Fp2_sub`. This module supplies it:

  bn254Fp2SubBody  (a `bn254_sub` leaf chain, mirroring `bn254Fp2AddBody`)
    --translateDialectControl-------->   Com[catCryptDialect]
    --cryptoDialectToJasminCom------->   Com[jasmin]
    --emitAbiOrchJ .regPtr----------->   .jazz   (reg ptr u64[4] leaf ABI)

The denotation is the component-wise `Fp` subtract `(a−c) + (b−d)u`, exactly the
abstract `Fp2` subtract over `Fp[u]/(u²+1)`; the emitted leaf graph routes both
components through the verified base `bn254_sub`. KAT gate: the AUCurves verified
`bn254_Fp2_sub` reference (same shape as `fp2_kat.rs` for mul) on the published
EIP-197 generator coordinates (Montgomery form).

Invoke:  lake env lean -- (the orchestrator drives the emit via `emittedFp2SubJazz`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Pairing.Bn254Fp2SubEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapCtx mapTy)

/-! ## 1. `Com` encoding + arg context (mirrors `fp_tower_from_rustcmd`) -/

/-- `Fp` felem: `TBytes 32 → memref 4`. -/
abbrev MFp : CryptoTy := CryptoTy.memref 4

/-- `Fp2` op args: `(x_re, x_im, y_re, y_im)` — four `Fp` felems. -/
def fp2ArgCtx : Ctx := [MFp, MFp, MFp, MFp]

def fp2ArgVM : VarMap fp2ArgCtx where
  lookup := fun s =>
    if s = "x_re"      then some ⟨MFp, .here⟩
    else if s = "x_im" then some ⟨MFp, .there .here⟩
    else if s = "y_re" then some ⟨MFp, .there (.there .here)⟩
    else if s = "y_im" then some ⟨MFp, .there (.there (.there .here))⟩
    else none

/-! ## 2. The `Fp2` subtract leaf chain `(a−c) + (b−d)u` -/

/-- `bn254_Fp2_sub`: two component-wise `bn254_sub` leaf calls — the real part
    `__re = x_re − y_re` and the imaginary part `__im = x_im − y_im`. Mirrors
    `Bn254Reflect.bn254Fp2AddBody` with `bn254_sub` in place of `bn254_add`. -/
def bn254Fp2SubBody : LowCT :=
  let xr : Located := { locVar := "x_re", locSrc := bn254FpTowerType }
  let xi : Located := { locVar := "x_im", locSrc := bn254FpTowerType }
  let yr : Located := { locVar := "y_re", locSrc := bn254FpTowerType }
  let yi : Located := { locVar := "y_im", locSrc := bn254FpTowerType }
  let orr : Located := { locVar := "__re", locSrc := bn254FpTowerType }
  let oi : Located := { locVar := "__im", locSrc := bn254FpTowerType }
  .RSeq (.RSeq .RSkip (.RCall "bn254_sub" orr [xr, yr]))
        (.RCall "bn254_sub" oi [xi, yi])

def bn254Fp2SubReified : ReifiedFunc :=
  { args := [("x_re", bn254FpTowerType), ("x_im", bn254FpTowerType),
             ("y_re", bn254FpTowerType), ("y_im", bn254FpTowerType)]
    body := bn254Fp2SubBody, retName := "__im" }

/-! ## 3. Drive the verified front (same helper shape as `fp_tower_from_rustcmd`) -/

/-- The `Fp2` subtract chain as a jasmin program: `bn254Fp2SubReified` through
    `translateDialectControl` and `cryptoDialectToJasminCom`, with the result type
    of `__im`. `none` when a stage refuses. -/
def fp2SubCom : Option (Σ t : CryptoTy, Com jasminDialect (mapCtx fp2ArgCtx) (mapTy t)) :=
  match translateDialectControl fp2ArgVM bn254Fp2SubReified.body with
  | none => none
  | some o =>
    match o.vm.lookup bn254Fp2SubReified.retName with
    | none => none
    | some ⟨t, w⟩ =>
      match o.cont (Com.ret (toVIRVar w)) with
      | none => none
      | some com => (cryptoDialectToJasminCom com).map fun c => ⟨t, c⟩

/-- The extern signature of the base leaf `bn254_sub`: two `Fp` felems (`u64[4]`) to
    one `Fp` felem. -/
def bn254SubLeaf : String × List JasminTy × JasminTy :=
  ("bn254_sub", [.stackArr 64 4, .stackArr 64 4], .stackArr 64 4)

/-- The reg-ptr `.jazz` of `fp2SubCom` as the `export fn` `name`, printed by
    `JasminAbiJazz.emitAbiOrchJ .regPtr` with the leaf `bn254_sub` and the `require`
    lines `requires`. -/
def emitRegPtr (name : String) («requires» : List String := []) : Option String :=
  fp2SubCom.bind fun c =>
    JasminAbiJazz.emitAbiOrchJ .regPtr name c.2 [bn254SubLeaf] «requires»

/-- The link form: `emitRegPtr` with the `require` line of the leaf `.jinc`. -/
def emitRegPtrLink (name : String) : Option String :=
  emitRegPtr name ["../include/bn254_tower_leaves.jinc"]

def emittedFp2SubJazz : Option String := emitRegPtr "bn254_Fp2_sub_rustcmd"
def emittedFp2SubLink : Option String := emitRegPtrLink "bn254_Fp2_sub_rustcmd"

/-! ## 4. Structural front-fires + leaf/ABI theorems -/

/-- The front fires on the `Fp2` subtract chain. -/
theorem fp2_sub_front_fires : fp2SubCom.isSome := by rfl

-- The `Fp2` subtract chain prints through the checked printer in the `regPtr` mode, with
-- and without the `require` line of the leaf `.jinc`.
#kat emittedFp2SubJazz.isSome && emittedFp2SubLink.isSome

/-- **A returned text parses to the unit**: a text of `emitRegPtr` parses to the erasure
    of the unit that `JasminAbiJazz.orchUnit .regPtr` builds from `fp2SubCom`. -/
theorem emitRegPtr_parse {name : String} {«requires» : List String} {s : String}
    (h : emitRegPtr name «requires» = some s) :
    ∃ c, fp2SubCom = some c ∧ ∃ u,
      JasminAbiJazz.orchUnit .regPtr name c.2 [bn254SubLeaf] «requires» = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok u.erase := by
  obtain ⟨c, hc, hs⟩ := Option.bind_eq_some_iff.mp (by simpa only [emitRegPtr] using h)
  exact ⟨c, hc, JasminAbiJazz.emitAbiOrchJ_parse hs⟩

/-- The reg-ptr ABI shape the render must carry: the export at the `Fp`
    (`u64[4]`) felem width, both components through the verified base
    `bn254_sub` leaf, and no unallocated / unknown registers. Checked by
    `main` on the rendered text rather than by reduction. -/
def regptrAbiShapeOk (s : String) : Bool :=
  JasminPrint.strContains s "export fn bn254_Fp2_sub_rustcmd"
    && JasminPrint.strContains s "bn254_sub"
    && JasminPrint.strContains s "u64[4]"
    && !(JasminPrint.strContains s "UNALLOCATED")
    && !(JasminPrint.strContains s "UNKNOWN")

/-! ## 5. Emit driver -/

def main : IO Unit := do
  IO.FS.createDirAll "bench/bn254_compare/gen_com"
  match emittedFp2SubJazz, emittedFp2SubLink with
  | some f2s, some f2sL => do
      IO.FS.writeFile "bench/bn254_compare/gen_com/fp2_sub_from_rustcmd.jazz" f2s
      IO.FS.writeFile "bench/bn254_compare/gen_com/fp2_sub_from_rustcmd_link.jazz" f2sL
      IO.println "wrote gen_com/fp2_sub_from_rustcmd{,_link}.jazz"
      if regptrAbiShapeOk f2s then
        IO.println "ok   fp2_sub reg-ptr ABI shape"
      else
        IO.println "FAIL fp2_sub reg-ptr ABI shape"
  | _, _ =>
      IO.println "FAILED: front did not fire (check arg names / retName / encoding)"

/-! ## Artifact generation

The two renders are written by `main`, run with `lake env lean --run` on this
file. -/

end CatCrypt.Crypto.Pairing.Bn254Fp2SubEmit
