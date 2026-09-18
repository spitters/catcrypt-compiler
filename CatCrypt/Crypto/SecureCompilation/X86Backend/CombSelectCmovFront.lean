/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogCopyCoalesce
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.CombSelectBytes

/-!
# Ed25519 comb select through the front in conditional-move form

The `N`-entry comb select of `CombSelectFront`, stated with the `LowCT`
conditional-select constructor `RSelect` in place of the arithmetic equality
mask: per entry `e` the source binds `q := d ⊕ e`, which is zero exactly when
`d = e`, and for each limb `k` loads table cell `4·e + k` into `l` and writes
`s_k := if q = 0 then l else s_k`.

The `RSelect` arm of `TranslateDialectDirectArms.translateDialectFull` on
64-bit words emits the eight-op mask chain `selectMaskCont`, and
`DialectToJasminCom.toJExprD` maps no `catCryptDialect` op to
`JasminOp.select`; the lowered program of this source therefore contains no
`CMOV`.

## Main results

* `combSelectCmovSrc N`: the `N`-entry scan in `RSelect` form as `LowCT`.
* `combSelectCmovFront`, `combSelectCmovLowered`, `combSelectCmovLprog`: the
  front output, its `Com jasminDialect` lowering and the exported `Lprog`, by
  the composition of `CombSelectFront`.
* `combSelectCmovAsmN`: the owned AT&T rendering after
  `ConstIndexFold.constIndexFold`, the basic-block pipeline and two rounds of
  `LprogCopyCoalesce.coalesceRounds`.
* `combSelectCmovLines`, `combSelectCmovClean`, `combSelectCmovHasCmov`: the
  line count of the rendering, the absence of an `UNHANDLED` sentinel, and the
  presence of a `cmov` mnemonic.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectFront
  (seqL accName setE selInit storeAll selCtx selVM)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located TowerType)

/-! ## 1. The source -/

/-- The selector of entry `e`: `q := d ⊕ e`, zero exactly when `d = e`. -/
def testCmd (e : Nat) : LowCT :=
  setE "q" (.SXor (.SVar "d") (.SLit e))

/-- Load table cell `4·e + k` from `tbl` (a `tw`-byte buffer) into `l` and
    select it into running limb `k` when `q = 0`. -/
def cellSelCmds (tw e : Nat) (k : Fin 4) : List LowCT :=
  [ setE "i" (.SLit (4 * e + k.val))
  , .RArrLoad ⟨"l", .TU64⟩ ⟨"tbl", .TBytes tw⟩ "i"
  , .RSelect ⟨accName k, .TU64⟩ "q" ⟨"l", .TU64⟩ ⟨accName k, .TU64⟩ ]

/-- One entry of the scan: its selector and the four conditional selects. -/
def entrySelCmds (tw e : Nat) : List LowCT :=
  testCmd e :: (cellSelCmds tw e 0 ++ (cellSelCmds tw e 1 ++ (cellSelCmds tw e 2 ++
    cellSelCmds tw e 3)))

/-- The scan over entries `0 … N−1`. -/
def scanSelCmds (tw : Nat) : Nat → List LowCT
  | 0 => []
  | N + 1 => scanSelCmds tw N ++ entrySelCmds tw N

/-- The constant-time `N`-entry comb select in conditional-select form, over the
    arguments `tbl` (`4N` little-endian words), `d` (the secret index) and `out`
    (four words): every entry is read on every call and selected into the
    running limbs under `d ⊕ e = 0`. -/
def combSelectCmovSrc (N : Nat) : LowCT :=
  seqL (selInit ++ (scanSelCmds (32 * N) N ++ storeAll))

/-! ## 2. The front, the lowering and the rendering -/

/-- The front output: `translateDialectControl` on the source, closed by
    returning `out`. -/
def combSelectCmovFront (N : Nat) : Option (Com catCryptDialect (selCtx N) (.memref 4)) :=
  match translateDialectControl (selVM N) (combSelectCmovSrc N) with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front output lowered to `Com jasminDialect`. -/
def combSelectCmovLowered (N : Nat) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match combSelectCmovFront N with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The exported `Lprog` under `f(tbl = RDI, d = RSI, out = RDX)`, with the
    export arguments of `CombSelectFront.combSelectLprog`. -/
def combSelectCmovLprog (name : String) (N : Nat) : Option JasminLprogExport.Lprog :=
  (combSelectCmovLowered N).map (fun s =>
    JasminLprogExport.Com.toLprogPhysAbi s.2.2 name
      (fun _ => none) (fun _ => none) (fun _ => none) []
      (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
      (residence := none) (abiW := 0) (forceLivePin := true))

/-- The exported `Lprog` after `ConstIndexFold.constIndexFold`,
    `ConstIndexFold.spellLprog`, the basic-block pipeline and two rounds of
    `LprogCopyCoalesce.coalesceRounds`, composed as in
    `LprogCopyCoalesce.combSelectCoalescedLprog`. -/
def combSelectCmovCoalescedLprog (name : String) (N : Nat) :
    Option JasminLprogExport.Lprog :=
  (combSelectCmovLprog name N).map (fun lp =>
    LprogCopyCoalesce.coalesceRounds 2 (LprogOptPipeline.optimizeLprogBasicBlocks
      (ConstIndexFold.spellLprog (ConstIndexFold.constIndexFold lp))))

/-- The owned AT&T rendering of `combSelectCmovCoalescedLprog`. -/
def combSelectCmovAsmN (name : String) (N : Nat) : Option String :=
  (combSelectCmovCoalescedLprog name N).map (fun p => LprogAsmPrinter.renderLprogAtt p)

/-! ## 3. Evaluation predicates -/

/-- The line count of the rendered `N`-entry select. -/
def combSelectCmovLines (N : Nat) : Option Nat :=
  (combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N).map
    LprogCopyCoalesce.lineCount

/-- The rendered `N`-entry select exists and has no `UNHANDLED` sentinel. -/
def combSelectCmovClean (N : Nat) : Bool :=
  match combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => !LprogCopyCoalesce.hasUnhandled t
  | none => false

/-- The rendered `N`-entry select contains a `cmov` mnemonic. -/
def combSelectCmovHasCmov (N : Nat) : Bool :=
  match combSelectCmovAsmN "ed25519_comb_select_cmov_x86_from_lean" N with
  | some t => (t.splitOn "cmov").length != 1
  | none => false

end CatCrypt.Crypto.SecureCompilation.X86Backend.CombSelectCmovFront
