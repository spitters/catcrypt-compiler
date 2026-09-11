/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Plonky3 coset-NTT column LDE FRONT-COMPILED as seven `Com jasminDialect` leaves

The seven register-arith leaves of `Plonky3ProveEmit.computeColumnLde colEvals 3
5 31` (`inttLeafCom`, `twistLeafCom`, `nttLeafCom 0..4`) re-sourced through the
verified front: every field op is a single `RScalarSetExpr` over named scalar
slots, each leaf's statement list is pushed through `translateDialectControl` and
lowered by `cryptoDialectToJasminCom` to a `Com jasminDialect`.  No de-Bruijn
`Com` binding chain and no positional `emitAbiOrchReg` dst-map is hand-authored.

## The 139-word ABI (preserved for `Plonky3LdeColumnEmit`)

Each leaf keeps its historical 139-word input context and its
`Com jasminDialect inCtxt r64` type, so `Plonky3LdeColumnEmit`'s
`Com.toLprogPhysAbi <leaf> … (abiMaps 139 ldeConstAt) (stdOutStore 32)` render
(and hence `lde_column_from_rustcmd_owned.s` / the
`plonky3-lde-column-rustcmd-kat` byte KAT) is unchanged.  Input words:

* `0..31`   — the 32-word working buffer values (runtime; leaf-to-leaf pass-through);
* `8..99`   — per-butterfly twiddles (intt at `8..19`, ntt-layer local at `100+j`);
* `100..131`— the 32 coset powers `31^0 .. 31^31`;
* `132`     — the intt scale `8⁻¹`;
* `133..138`— Barrett `MU`, prime `p`, and `0,30,32,63` — the ONLY immediates
  (`ldeConstAt`); every other word is a runtime `RSI` load.

The Barrett/branchless constants are read as **`SVar` input words** (`mu`,`p`,
`zero`,`sh30`,`sh32`,`sh63` = words `133..138`), NOT `SLit`, so the shift
amounts lower to the variable `bvShiftRV` (`regArith .shr`) and the
`abiMaps 139 ldeConstAt` consumer bakes exactly `133..138` as immediates.

## Buffer / finalize discipline

The working buffer is 32 mutable slots `v0..v31`, seeded `v[i] := in[i]`
(the two NTT bit-reversals live in the harness copy-in / the twist swap, exactly
as before).  Each leaf ends with a 32-statement finalize `o[i] := v[i]`; each is
a single identity-copy binding, so the LAST 32 body bindings are `o0..o31` in
order — the slots the `stdOutStore 32` epilogue stores to `out[0..31]`.

## leaf.denote = spec by construction

Every leaf is confined to `regArith`/`regConst`/`shlImm`/`shrImm` bindings
(`*_is_purearith`, `native_decide`), so the owned backend renders no
`# UNHANDLED-OP` and the emitted `.s`'s denotation IS the BabyBear
Barrett/branchless word arithmetic.  Numeric equality to `computeColumnLde` is
KAT-witnessed (`lde_column_from_rustcmd_kat.c`).
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit

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

/-- Number of declared inputs (the historical 139-word LDE ABI). -/
abbrev nInputs : Nat := 139

/-- The input context: `nInputs` `r64` words (preserved for the consumer). -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate nInputs r64

/-! ## 1. Input-word index conventions (unchanged) -/

/-- First input index of the twiddle block. -/
def twBase : Nat := 8
/-- First input index of the coset-power block. -/
def powBase : Nat := 100
/-- Input index of the intt scale `8⁻¹`. -/
def iScale : Nat := 132
/-- Input index of Barrett `MU`. -/
def iMU : Nat := 133
/-- Input index of the prime `p`. -/
def iP : Nat := 134
/-- Input index of the immediate `0`. -/
def iZero : Nat := 135
/-- Input index of the shift amount `30`. -/
def iSh30 : Nat := 136
/-- Input index of the shift amount `32`. -/
def iSh32 : Nat := 137
/-- Input index of the shift amount `63`. -/
def iSh63 : Nat := 138

/-! ## 2. The per-butterfly / twist schedules (twiddle indices in body order) -/

/-- Phase-1 (8-pt intt) butterflies, in body order; 12 butterflies, twiddle
    inputs `8..19`. -/
def inttSchedule : List (Nat × Nat × Nat) :=
  [(0,1,8), (2,3,9), (4,5,10), (6,7,11),
   (0,2,12), (1,3,13), (4,6,14), (5,7,15),
   (0,4,16), (1,5,17), (2,6,18), (3,7,19)]

/-- One NTT layer's butterfly schedule with **leaf-local** twiddle indices:
    butterfly `(blk+j, blk+j+half)` uses twiddle input `powBase + j` (= `100+j`),
    the layer's `wSize^j`. -/
def nttLayerLocal (layer : Nat) : List (Nat × Nat × Nat) := Id.run do
  let size := 2 ^ (layer + 1)
  let half := size / 2
  let mut out : List (Nat × Nat × Nat) := []
  let mut blk := 0
  while blk < 32 do
    for j in List.range half do
      out := out ++ [(blk + j, blk + j + half, powBase + j)]
    blk := blk + size
  return out

/-- The 12 transposition pairs `(i, bitReverse(i,5))` with `i < j`. -/
def brPairs : List (Nat × Nat) :=
  [(1,16),(2,8),(3,24),(5,20),(6,12),(7,28),(9,18),(11,26),(13,22),(15,30),
   (19,25),(23,29)]

/-- The 8 fixed points of `bitReverse(·,5)`. -/
def brFixed : List Nat := [0,4,10,14,17,21,27,31]

/-! ## 3. Field-op LowCT combinators (each op = one `RScalarSetExpr`)

The Barrett `bbMul` and the branchless csub of `bbAdd`/`bbSub`, over named scalar
slots.  Field constants read from the ABI input words `133..138` as `SVar`s. -/

/-- csub in place on slot `d`. -/
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

/-! ## 4. Value-slot / input-word names and the phase generators -/

/-- Working buffer slot `i` (mutable). -/
def vName (i : Nat) : String := "v" ++ toString i
/-- Raw input word `i` (read-only twiddle / coset power / scale / value seed). -/
def inName (i : Nat) : String := "in" ++ toString i
/-- Output slot `i` (the finalize copy). -/
def oName (i : Nat) : String := "o" ++ toString i

/-- One butterfly `wb = bbMul tw v[hi]; v[hi] = bbSub v[lo] wb; v[lo] = bbAdd v[lo] wb`.
    The `bbSub` (o_hi) is emitted first (it reads the old `v[lo]`). -/
def sButterfly (loI hiI twI : Nat) : List LowCT :=
  sBBMul "wb" (.SVar (inName twI)) (.SVar (vName hiI)) ++
  sBBSub (vName hiI) (.SVar (vName loI)) (.SVar "wb") ++
  sBBAdd (vName loI) (.SVar (vName loI)) (.SVar "wb")

/-- Scale `v[i]` by the intt factor `8⁻¹` (input word `iScale`). -/
def sScale (i : Nat) : List LowCT :=
  sBBMul (vName i) (.SVar (inName iScale)) (.SVar (vName i))

/-- Zero slot `v[i]` (`v[i] ← 0` via `0 + 0`). -/
def sZero (i : Nat) : List LowCT :=
  [ .RScalarSetExpr (vName i) (.SAdd (.SVar "zero") (.SVar "zero")) ]

/-- Coset twist of a fixed point: `v[i] ← v[i]·31^i` (power at input `powBase+i`). -/
def sTwistFixed (i : Nat) : List LowCT :=
  sBBMul (vName i) (.SVar (inName (powBase + i))) (.SVar (vName i))

/-- Twist-swap for a pair `(i,j)`, `i < j`: `wb = v[j]·31^j` (reads `v[j]`),
    `v[j] = v[i]·31^i` (reads `v[i]`), `v[i] = wb`. -/
def sTwistSwap (i j : Nat) : List LowCT :=
  sBBMul "wb" (.SVar (inName (powBase + j))) (.SVar (vName j)) ++
  sBBMul (vName j) (.SVar (inName (powBase + i))) (.SVar (vName i)) ++
  [ .RScalarSetExpr (vName i) (.SAdd (.SVar "wb") (.SVar "zero")) ]

/-- Seed the 32 working buffer slots `v[i] := in[i]`. -/
def initBuf : List LowCT :=
  (List.range 32).map (fun i => .RScalarSetExpr (vName i) (.SVar (inName i)))

/-- Finalize: `o[i] := v[i]` for `i = 0..31` (32 identity-copy bindings). -/
def sFinalize : List LowCT :=
  (List.range 32).map (fun i => .RScalarSetExpr (oName i) (.SVar (vName i)))

/-! ## 5. The seven leaf statement lists -/

/-- intt-8 leaf: seed + 12 intt butterflies + 8 scales + finalize. -/
def inttLeafStmts : List LowCT :=
  initBuf ++
  inttSchedule.flatMap (fun t => sButterfly t.1 t.2.1 t.2.2) ++
  (List.range 8).flatMap sScale ++
  sFinalize

/-- coset-twist leaf: seed + zero-pad `v[8..31]` + twist-swap pairs + fixed
    twists + finalize. -/
def twistLeafStmts : List LowCT :=
  initBuf ++
  ((List.range 24).map (· + 8)).flatMap sZero ++
  brPairs.flatMap (fun p => sTwistSwap p.1 p.2) ++
  brFixed.flatMap sTwistFixed ++
  sFinalize

/-- One NTT-layer leaf: seed + 16 butterflies + finalize. -/
def nttLeafStmts (layer : Nat) : List LowCT :=
  initBuf ++
  (nttLayerLocal layer).flatMap (fun t => sButterfly t.1 t.2.1 t.2.2) ++
  sFinalize

/-! ## 6. The 139-word source context and the front entry point -/

/-- The source `Ctx`: `nInputs` `sword 64` words. -/
abbrev srcCtx : Ctx := List.replicate nInputs (.sword 64)

/-- Name of source word `i`: the Barrett/branchless constants at `133..138`,
    every other word is a raw `in<i>`. -/
def wordName (i : Nat) : String :=
  if i = iMU then "mu" else if i = iP then "p" else if i = iZero then "zero"
  else if i = iSh30 then "sh30" else if i = iSh32 then "sh32"
  else if i = iSh63 then "sh63" else inName i

/-- The source `VarMap`: word `0` is the head; word `nInputs-1` the innermost
    (the same De-Bruijn order `abiMaps 139 ldeConstAt` expects). -/
def buildVM : (k : Nat) → VarMap (List.replicate k (.sword 64))
  | 0 => VarMap.empty
  | k+1 => (buildVM k).bind (wordName (nInputs - 1 - k))

def srcVM : VarMap srcCtx := buildVM nInputs

/-- Translate a LowCT body and return the `Com` whose result is the slot `name`. -/
def frontComAt (body : LowCT) (name : String) :
    Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM body with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- Front-lower a leaf's statement list to a `Com jasminDialect` (result `o31`). -/
def frontLeafOpt (stmts : List LowCT) : Option (Com jasminDialect inCtxt r64) :=
  (frontComAt (seqAll stmts) (oName 31)).bind
    DialectToJasminCom.cryptoDialectToJasminCom

/-! ## 7. The seven front-sourced leaf `Com`s -/

def inttLoweredOpt := frontLeafOpt inttLeafStmts
theorem inttLowered_isSome : inttLoweredOpt.isSome := by native_decide
/-- intt-8 leaf (`lde_intt8_rc`): 8-pt inverse NTT + scale `8⁻¹`. -/
def inttLeafCom : Com jasminDialect inCtxt r64 := inttLoweredOpt.get inttLowered_isSome

def twistLoweredOpt := frontLeafOpt twistLeafStmts
theorem twistLowered_isSome : twistLoweredOpt.isSome := by native_decide
/-- coset-twist leaf (`lde_twist_rc`): zero-pad + coset twist + fused fwd-NTT
    bit-reversal. -/
def twistLeafCom : Com jasminDialect inCtxt r64 := twistLoweredOpt.get twistLowered_isSome

def nttLeaf0Opt := frontLeafOpt (nttLeafStmts 0)
theorem nttLeaf0_isSome : nttLeaf0Opt.isSome := by native_decide
def nttLeaf0Com : Com jasminDialect inCtxt r64 := nttLeaf0Opt.get nttLeaf0_isSome

def nttLeaf1Opt := frontLeafOpt (nttLeafStmts 1)
theorem nttLeaf1_isSome : nttLeaf1Opt.isSome := by native_decide
def nttLeaf1Com : Com jasminDialect inCtxt r64 := nttLeaf1Opt.get nttLeaf1_isSome

def nttLeaf2Opt := frontLeafOpt (nttLeafStmts 2)
theorem nttLeaf2_isSome : nttLeaf2Opt.isSome := by native_decide
def nttLeaf2Com : Com jasminDialect inCtxt r64 := nttLeaf2Opt.get nttLeaf2_isSome

def nttLeaf3Opt := frontLeafOpt (nttLeafStmts 3)
theorem nttLeaf3_isSome : nttLeaf3Opt.isSome := by native_decide
def nttLeaf3Com : Com jasminDialect inCtxt r64 := nttLeaf3Opt.get nttLeaf3_isSome

def nttLeaf4Opt := frontLeafOpt (nttLeafStmts 4)
theorem nttLeaf4_isSome : nttLeaf4Opt.isSome := by native_decide
def nttLeaf4Com : Com jasminDialect inCtxt r64 := nttLeaf4Opt.get nttLeaf4_isSome

/-- One forward-NTT layer leaf (`lde_ntt32_l<layer>_rc`), layers `0..4`. -/
def nttLeafCom (layer : Nat) : Com jasminDialect inCtxt r64 :=
  match layer with
  | 0 => nttLeaf0Com
  | 1 => nttLeaf1Com
  | 2 => nttLeaf2Com
  | 3 => nttLeaf3Com
  | 4 => nttLeaf4Com
  | _ => nttLeaf0Com

/-! ## 8. Pure-arith predicate — leaf.denote = spec by construction -/

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

theorem inttLeaf_is_purearith : allPureArith inttLeafCom = true := by native_decide
theorem twistLeaf_is_purearith : allPureArith twistLeafCom = true := by native_decide
theorem nttLeaf0_is_purearith : allPureArith nttLeaf0Com = true := by native_decide
theorem nttLeaf1_is_purearith : allPureArith nttLeaf1Com = true := by native_decide
theorem nttLeaf2_is_purearith : allPureArith nttLeaf2Com = true := by native_decide
theorem nttLeaf3_is_purearith : allPureArith nttLeaf3Com = true := by native_decide
theorem nttLeaf4_is_purearith : allPureArith nttLeaf4Com = true := by native_decide

/-- Binding count of a `Com`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

-- #eval IO.println ("lde leaf bindings — intt8: " ++ toString (comBindings inttLeafCom)
--   ++ ", twist: " ++ toString (comBindings twistLeafCom)
--   ++ ", ntt-l0: " ++ toString (comBindings nttLeaf0Com)
--   ++ ", ntt-l4: " ++ toString (comBindings nttLeaf4Com))

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit


namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-! ## 0. Shared helpers (substring + ABI maps) -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map: output word `j` to `[RDI + 8j]`. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` pair from a per-input-word constant
    oracle `constAt : idx → Option Nat` over an `nIn`-word context. A word with a
    constant becomes an immediate; every other word is loaded from `[RSI+8·idx]`.
    Argument slot `s` corresponds to input word `nIn - 1 - s` (the De Bruijn
    reversal in `comToLfundef`). -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

/-! ## 1. The LDE constant oracle

The 139-word input context (`Plonky3LdeColumnEmit.nInputs = 139`). Words
`133..138` are the six Barrett/branchless immediates (matching `inttInName` /
`bufInName`); every other word (`0..132`: the buffer values, twiddles, coset
powers, intt scale) is a runtime `RSI` load. -/

/-- The Barrett/branchless immediates at LDE input words `133..138`. -/
def ldeConstAt (idx : Nat) : Option Nat :=
  if idx = iMU then some 2290649223        -- 133
  else if idx = iP then some 2013265921    -- 134
  else if idx = iZero then some 0          -- 135
  else if idx = iSh30 then some 30         -- 136
  else if idx = iSh32 then some 32         -- 137
  else if idx = iSh63 then some 63         -- 138
  else none

/-! ## 2. The seven owned leaves

Each leaf takes `(out : RDI ptr u64[32], inp : RSI ptr u64[139])`, writes 32
output words to `[RDI + 8j]`, and reads its runtime words from `[RSI + 8·idx]`.
The seven `Com`s and their `allRegArith` proofs are from `Plonky3LdeColumnEmit`. -/

/-- intt-8 leaf (`lde_intt8_rc`): 8-pt inverse NTT + scale `8⁻¹`. -/
def inttLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi inttLeafCom "lde_intt8_rc" (fun _ => none) imm inl (stdOutStore 32)

/-- coset-twist leaf (`lde_twist_rc`): zero-pad + coset twist + fused fwd-NTT
    bit-reversal. -/
def twistLprog : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi twistLeafCom "lde_twist_rc" (fun _ => none) imm inl (stdOutStore 32)

/-- one forward-NTT layer leaf (`lde_ntt32_l<layer>_rc`). -/
def nttLprog (layer : Nat) : Lprog :=
  let (imm, inl) := abiMaps nInputs ldeConstAt
  Com.toLprogPhysAbi (nttLeafCom layer) ("lde_ntt32_l" ++ toString layer ++ "_rc")
    (fun _ => none) imm inl (stdOutStore 32)

/-- All seven LDE leaves combined into one `.s` (their `lp_funcs` concatenated),
    matching the single composed `lde_column_from_rustcmd.s` unit. -/
def ldeColumnLprog : Lprog :=
  { inttLprog with
    lp_funcs :=
      inttLprog.lp_funcs ++ twistLprog.lp_funcs
        ++ (nttLprog 0).lp_funcs ++ (nttLprog 1).lp_funcs
        ++ (nttLprog 2).lp_funcs ++ (nttLprog 3).lp_funcs
        ++ (nttLprog 4).lp_funcs }

def ldeColumnAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned ldeColumnLprog

/-! ## 2b. Front provenance (per-leaf, small)

Each deployed leaf `Com` this module renders is the sibling front module
`Plonky3LdeColumnEmit`'s front lowering — the `translateDialectControl`-translated
LowCT statement list, lowered to a `Com jasminDialect` by
`cryptoDialectToJasminCom`.  Nothing here hand-authors a `Com`: the leaves are
consumed from the front and only the owned RA-render tail (`toLprogPhysAbi` /
`renderLprogAtt`) is local.  The provenance gate is the front module's SMALL
per-leaf `*_isSome` check (each a `native_decide` over ONE ≈30-binding leaf), not
a whole-block scan; the equalities below are definitional (`Option.some_get`) and
name the front lowering (`cryptoDialectToJasminCom`) that produced each symbol. -/

theorem intt_front_sourced :
    (frontComAt (seqAll inttLeafStmts) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some inttLeafCom :=
  (Option.some_get inttLowered_isSome).symm

theorem twist_front_sourced :
    (frontComAt (seqAll twistLeafStmts) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some twistLeafCom :=
  (Option.some_get twistLowered_isSome).symm

theorem ntt0_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 0)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 0) :=
  (Option.some_get nttLeaf0_isSome).symm

theorem ntt1_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 1)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 1) :=
  (Option.some_get nttLeaf1_isSome).symm

theorem ntt2_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 2)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 2) :=
  (Option.some_get nttLeaf2_isSome).symm

theorem ntt3_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 3)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 3) :=
  (Option.some_get nttLeaf3_isSome).symm

theorem ntt4_front_sourced :
    (frontComAt (seqAll (nttLeafStmts 4)) (oName 31)).bind
      DialectToJasminCom.cryptoDialectToJasminCom = some (nttLeafCom 4) :=
  (Option.some_get nttLeaf4_isSome).symm

/-! ## 3. Structural gates on the lowered program -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-- The combined `.s` carries all seven leaf labels (structural: its `lp_funcs`
    is the concatenation of the seven single-leaf programs). -/
theorem ldeColumn_owned_funcs_len :
    ldeColumnLprog.lp_funcs.length = 7 := by native_decide

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` carrying all seven LDE column leaves into the
    `bench/plonky3_compare/gen_com` harness directory (no jasminc). The `.s`
    relinks into `lde_column_from_rustcmd_kat.c` byte-identically. -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/lde_column_from_rustcmd_owned.s") ldeColumnAsm
  IO.println "WROTE plonky3 owned LDE column .s (intt8 / twist / ntt32 l0..l4)"
  IO.println "  Com[jasmin] regArith -> toLprogPhysAbi -> renderLprogAtt onto the OWNED x86 backend, NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit

/-- Top-level entry point for `lake exe plonky3ldeowned`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeColumnEmit.emitMain
  return 0
