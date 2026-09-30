/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.KatGuard
public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight
public meta import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight

@[expose] public section

set_option autoImplicit false

/-!
# The straight-line check on a front-compiled word kernel

`DecodeGenStraight.lineCheck` is the Boolean condition under which
`DecodeGenStraight.decLine_result` relates the decoded bytes of a straight-line body to the
flag-machine run of its typed chain. This module evaluates it on the front-compiled kernel
`mulAddCom` (`t := a * b; r := t + a` over 64-bit words, lowered by
`ThirToComFront.thirToJasmin`), exported by `Com.toLprogPhysAbi` with the liveness pin
forced and passed through the owned back end `LprogOptPipeline.ownedLprog`, as the
straight-line route of the hax compiler does. The checks are `#kat`s evaluated by the
compiled evaluator: the export certificate `straightCertB`, the decode equation of the
function bytes, and `lineCheck` against the System V layout `mulAddAbi` with the register
map `mulAddPi`.

## Main definitions

* `mulAddThir`, `mulAddCom`, `mulAddBody` — the source, its dialect program and the printed
  function body.
* `mulAddAbi`, `mulAddPi`, `mulAddWit` — the layout, the register map and the witness of the
  check.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraightKat

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (straightOpsMem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (opsD)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight (straightCertB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)

/-- The source `t := a * b; r := t + a` over two word inputs. -/
def mulAddThir : Thir :=
  .let_ "t" (.mul (.inp 0) (.inp 1))
    (.let_ "r" (.add (.lvar "t") (.inp 0))
      (.ret (.lvar "r")))

/-- The front's lowering of `mulAddThir` at width `64`. -/
def mulAddCom : Com jasminDialect (frontCtxt 64 2 []) (rW 64) :=
  (thirToJasmin (w := 64) (nIn := 2) [] (initFState 64 2) mulAddThir).getD (.ret .here)

/-- The printed function body of `mulAddCom`: the physical-ABI export with the liveness
    pin forced, through the owned back end. -/
def mulAddBody : Lcmd :=
  ((LprogOptPipeline.ownedLprog (Com.toLprogPhysAbi mulAddCom "mul_add"
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (forceLivePin := true))).lp_funcs.head?.map
      (·.2.lfd_body)).getD []

/-- The System V layout of `mulAddCom`: two scalar parameters in `%rdi` and `%rsi`, the
    result in `%rax`, and the stack words from `-64` to `-8` below the entry stack
    pointer. -/
def mulAddAbi : AbiLayout where
  args := [⟨"a", "%rdi", .scalar⟩, ⟨"b", "%rsi", .scalar⟩]
  consts := []
  result := .reg "%rax"
  bounds := []
  frameLo := -64
  frameHi := -8

/-- The machine register of each name of the typed chain of `mulAddCom`. -/
def mulAddPi : String → String
  | "a0" => "%rbx"
  | "a1" => "%rcx"
  | "r2" => "%rax"
  | "r3" => "%rbx"
  | "r4" => "%rax"
  | r => r

/-- The witness of the check: the register map, the two arguments live at the start of the
    chain, the decoded block of `mulAddBody` (frame `lea`, eight saves and two argument
    loads; six instructions of the chain; six restores and the closing `lea`). -/
def mulAddWit : LineWit where
  E := ⟨mulAddPi, "%rsp", [], 0⟩
  L0 := ["a0", "a1"]
  js := leaFrame (-(Int.ofNat (Params.ofBody mulAddBody).frame))
    :: opsD (Params.ofBody mulAddBody) (mulAddBody.take 22)
      ++ [leaFrame (Int.ofNat (Params.ofBody mulAddBody).frame)]
  nPre := 11
  nMid := 6

-- the export certificate of the straight-line route
#kat straightCertB mulAddCom

-- the function bytes decode to the witness's layout
#kat decide (decodeLprog (encodeLfundefBytes mulAddBody) = some (lineLayout mulAddWit.js))

-- the straight-line check on the typed chain and its return name
#kat lineCheck mulAddAbi mulAddWit (straightOpsMem 2 mulAddCom 2)
  (comRetReg 2 argName mulAddCom 2)

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraightKat
