/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Core.Heap
import all CatCrypt.Core.Location
import all CatCrypt.Crypto.Jasmin.JasminOps
import all CatCrypt.Crypto.Jasmin.JasminTranslate
import all CatCrypt.Crypto.Jasmin.JasminVar
import all CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
import all CatCrypt.Crypto.Jasmin.LowCTReflect
import all CatCrypt.Crypto.Jasmin.LowCTToJasmin
import all CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import all CatCrypt.Deep.Eval
import all CatCrypt.Deep.RawCode
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCTSyntax
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.EmitCtGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EmitCtGate

/-!
# Constant-time conditional-move / select primitive for the owned backend

The multivariate-signature **sign** path (MAYO / UOV / SNOVA) solves a linear
system over GF(2⁴)/GF(2⁸) by Gaussian elimination. The GE pivot search performs a
**conditional row/element swap**: swap two field elements iff a pivot mask is set.
That mask is derived from *secret* data (the secret oil-space basis), so the swap
must be **branchless** — a secret-dependent `Jcc` would leak the pivot pattern
through the instruction-fetch timing.

This module supplies and exercises the data-oblivious conditional move a
*secret* condition must take, in two interchangeable constant-time shapes:

* **`CMOVcc` select** (`cmovSwapLcmd`) — the GE-solve pivot swap via
  `cmove`/`cmovne`/`cmovb`, the canonical branchless move. The owned printer
  maps the `CMOVE`/`CMOVNE`/`CMOVB`/`CMOVAE`/`CMOVL`/`CMOVGE` body mnemonics to
  `cmov<cc><sz>` (`LprogAsmPrinter.attBase`); the value semantics is pinned by
  `JasminModel.x86_CMOVcc` (`if b then src else dst`) on the matching
  `JInstr.cmove`/`cmovne`/`cmovb` arms.
* **mask select** (`maskSwapAsm`) — the same swap with no CMOV at all: a
  `0 − cond` all-ones/all-zero mask `AND`ed/`XOR`ed, exactly the form the GF(16)
  multiply (`MAYO.VerifyEmit.gf16MulInline`) already uses. It is pure
  `SExpr` arithmetic (`SSub`/`SXor`/`SAnd`), so the deployed kernel is
  FRONT-GENERATED (`translateDialectControl` + `cryptoDialectToJasminCom` +
  `renderLprogAtt`), not hand-authored `Lcmd`.

The CMOV shape is a backend printer primitive (`CMOVcc` has no
`catCryptDialect` front op); the mask shape is the front-expressible CT-select
the GE-solve can always take. In both, the move/select issues unconditionally and
only the written value depends on the condition. The per-shape value semantics is
pinned by small vectors through the full `evalInstr`/`x86_*` chain
(`cmovSwap_value` / `maskSwap_value`, no loop-running `native_decide`).

## The constant-time results

Because the mask is secret, the kernels carry the leakage obligation rather than
a public-data declaration:

* `cmovSwapBody_constant_time`, `maskSwapBody_constant_time` — the two
  `List (JInstr 64)` shapes have the same `MachineConstantTime.blockLeak` trace
  from any two initial machine states, via
  `ConstantTimeCoverage.allDirect_constant_time`.
* `cmovSwapLcmd_lcmdDirect` — the `CMOVcc` backend-primitive body uses only
  base + compile-time-displacement addressing.
* `maskSwapPolicy`, `maskSwapCom_indexFree`, `maskSwapLprog_lprogDirect`,
  `maskSwap_emitChecked`, `maskSwap_gather_constant_time` — the deployed export
  is index-free by construction and passes the `EmitCtGate` gate under a
  `publicData := false` policy, so the gathered `JInstr 64` block of every
  function body has a state-independent leakage trace. `emit` writes the artifact
  through `EmitCtGate.emitCheckedTo`, so a later edit that makes the kernel
  register-indexed stops the emit instead of writing the file.

The leak conclusion is about the gathered `JInstr 64` block; no theorem here
reaches the AT&T text `renderOwned` prints or the bytes an assembler makes of it.

## Scope of the leakage model

`MachineConstantTime.MLeak` has a `branch` constructor and a `mem` constructor.
`JInstr` has no conditional-jump constructor, so no block of type
`List (JInstr 64)` emits `MLeak.branch` and the branch channel is empty for every
such block. The content of the results above is in the address channel: the
sequence of effective memory addresses does not read a register value, hence not
the secret pivot mask. The branchlessness of the two shapes is a property of the
instruction type, not of these theorems.

## The negative control

`condIndexedSelectBody` is the table form of the same select, reading at
`base + 8 · cond`. `condIndexedSelect_leaks_cond` exhibits two machine states
differing only in the condition register whose leakage traces differ, and
`condIndexedSwap_emitChecked_error` has the gate reject its `Lprog` under
`maskSwapPolicy`. The contrast is the one
`MachineConstantTime.nonCT_storeMemIdx_leaks_value` draws for the indexed
scatter, at the condition register of this kernel.

This is the **backend primitive** the MAYO/UOV/SNOVA GE-solve sign emit needs;
the per-protocol GE-solve loop that calls it is outside this module.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopEmit
  (binop64L mov64L memCell)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (occursIn)
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_constant_time)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (blockLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
  (lcmdDirect toLprogPhysAbi_lcmdDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
  (ComJasminCTByConstruction comJasminCT?_eq_true_iff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToLfundefDirect (comToLfundef_lcmdDirect)

/-- A `MOV imm` at the `Lcmd` level (`Lopn [d] MOV:64 [#v]`). -/
def movImm64L (d : String) (v : Nat) : Linstr :=
  ⟨0, .Lopn [.reg d] "MOV:64" [.imm v]⟩

/-! ## 1. The `CMOVcc` swap — value semantics in the `JInstr` model

A constant-time conditional swap of `x` and `y` controlled by the zero flag
(`cc = ne`, i.e. "swap iff the pivot test was non-zero"). The CMOV idiom for a
branchless swap, with `tmp` a scratch register:

```
   mov  tmp, x          -- tmp := x
   cmovne x, y          -- if !ZF then x := y
   cmovne y, tmp        -- if !ZF then y := tmp   (= old x)
```

When `!ZF` (the condition holds) the pair swaps `x`,`y`; when `ZF` both moves are
inert and `x`,`y` are unchanged. Both `cmovne`s issue regardless, so the control
flow is data-independent. The seed sets `zf` to the public/secret pivot bit. -/

/-- A `JInstr 64` `CMOVNE dst, src` (`dst := if !ZF then src else dst`). -/
def cmovneJ (dst src : String) : JInstr 64 := .cmovne dst (.reg src)

/-- The branchless conditional-swap body: swap `x`/`y` iff `!ZF`, via `cmovne`. -/
def cmovSwapBody : List (JInstr 64) :=
  [ .mov "tmp" (.reg "x")
  , cmovneJ "x" "y"
  , cmovneJ "y" "tmp" ]

/-- Seed a state with `x := xv`, `y := yv`, and the zero flag set to `zf`
    (`zf = true` ⇒ condition `!ZF` is false ⇒ no swap; `zf = false` ⇒ swap). -/
def seedSwap (xv yv : BitVec 64) (zf : Bool) : JState 64 :=
  { regs := fun r => if r = "x" then xv else if r = "y" then yv else 0
    flags := { zf := some zf } }

/-- **CMOVcc swap value (vectors).** With `x = 0xAA`, `y = 0xBB`:
    * `zf = false` (condition holds) ⇒ swapped: `x = 0xBB`, `y = 0xAA`;
    * `zf = true` (condition fails) ⇒ unchanged: `x = 0xAA`, `y = 0xBB`.
    Pinned through the full `evalInstr`/`x86_CMOVcc` chain. -/
theorem cmovSwap_value :
    let sSwap := runBlock (seedSwap 0xAA 0xBB false) cmovSwapBody
    let sKeep := runBlock (seedSwap 0xAA 0xBB true) cmovSwapBody
    (sSwap.get "x").toNat = 0xBB ∧ (sSwap.get "y").toNat = 0xAA
      ∧ (sKeep.get "x").toNat = 0xAA ∧ (sKeep.get "y").toNat = 0xBB := by
  native_decide

/-- The `CMOVcc` swap body touches no memory, so every instruction is in the
    direct base + compile-time-displacement class. -/
theorem cmovSwapBody_allDirect : allDirect cmovSwapBody = true := by decide

/-- **`cmovSwapBody` is constant-time.** The block has the same machine leakage
    trace from any two initial states, so the observable control-flow and
    memory-address sequence carries no information about the zero flag the secret
    pivot bit sets. -/
theorem cmovSwapBody_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ cmovSwapBody = blockLeak s₂ cmovSwapBody :=
  allDirect_constant_time cmovSwapBody cmovSwapBody_allDirect s₁ s₂

/-! ## 2. The mask swap — value semantics (no CMOV, pure GP-ALU)

The same swap with a `0 − cond` mask (`cond ∈ {0,1}`), the form the GF kernels
already use. `mask = 0 − cond` is all-ones when `cond = 1`, all-zero when
`cond = 0`; `d := (x ^ y) & mask` is the XOR-difference gated by the mask, and
`x ^= d ; y ^= d` swaps iff `cond` (the constant-time XOR-swap). No flag, no
CMOV — pure `MOV`/`SUB`/`XOR`/`AND`. -/

/-- The branchless XOR-swap body controlled by the register `cond ∈ {0,1}`:
    `mask := 0 − cond ; d := (x ^ y) & mask ; x ^= d ; y ^= d`. -/
def maskSwapBody : List (JInstr 64) :=
  [ .mov "mask" (.imm 0)
  , .sub "mask" (.reg "cond")
  , .mov "d" (.reg "x")
  , .xor_ "d" (.reg "y")
  , .and_ "d" (.reg "mask")
  , .xor_ "x" (.reg "d")
  , .xor_ "y" (.reg "d") ]

/-- Seed for the mask swap: `x`/`y`/`cond` registers, no flag needed. -/
def seedMaskSwap (xv yv : BitVec 64) (cond : Nat) : JState 64 :=
  { regs := fun r => if r = "x" then xv else if r = "y" then yv
                     else if r = "cond" then BitVec.ofNat 64 cond else 0 }

/-- **Mask swap value (vectors).** With `x = 0xAA`, `y = 0xBB`:
    `cond = 1` ⇒ swapped; `cond = 0` ⇒ unchanged. Through the full chain. -/
theorem maskSwap_value :
    let sSwap := runBlock (seedMaskSwap 0xAA 0xBB 1) maskSwapBody
    let sKeep := runBlock (seedMaskSwap 0xAA 0xBB 0) maskSwapBody
    (sSwap.get "x").toNat = 0xBB ∧ (sSwap.get "y").toNat = 0xAA
      ∧ (sKeep.get "x").toNat = 0xAA ∧ (sKeep.get "y").toNat = 0xBB := by
  native_decide

/-- The mask swap body is pure register arithmetic, so every instruction is in
    the direct base + compile-time-displacement class. -/
theorem maskSwapBody_allDirect : allDirect maskSwapBody = true := by decide

/-- **`maskSwapBody` is constant-time.** The block has the same machine leakage
    trace from any two initial states, so the observable sequence carries no
    information about the secret condition register. -/
theorem maskSwapBody_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ maskSwapBody = blockLeak s₂ maskSwapBody :=
  allDirect_constant_time maskSwapBody maskSwapBody_allDirect s₁ s₂

/-- **Denotational tie.** The front-generated mask select and the `CMOVcc`
    select compute the SAME conditional swap: on the shared vectors both swap the
    pair when the condition holds and leave it unchanged otherwise. This is the
    correctness justification for deploying the mask twin as the conditional-swap
    kernel in place of the `CMOVcc` shape (byte-identity is not required). Derived
    from `maskSwap_value` and `cmovSwap_value`, no new reduction. -/
theorem maskSwap_denotes_cmovSwap :
    ((runBlock (seedMaskSwap 0xAA 0xBB 1) maskSwapBody).get "x").toNat
        = ((runBlock (seedSwap 0xAA 0xBB false) cmovSwapBody).get "x").toNat
      ∧ ((runBlock (seedMaskSwap 0xAA 0xBB 1) maskSwapBody).get "y").toNat
        = ((runBlock (seedSwap 0xAA 0xBB false) cmovSwapBody).get "y").toNat
      ∧ ((runBlock (seedMaskSwap 0xAA 0xBB 0) maskSwapBody).get "x").toNat
        = ((runBlock (seedSwap 0xAA 0xBB true) cmovSwapBody).get "x").toNat
      ∧ ((runBlock (seedMaskSwap 0xAA 0xBB 0) maskSwapBody).get "y").toNat
        = ((runBlock (seedSwap 0xAA 0xBB true) cmovSwapBody).get "y").toNat := by
  obtain ⟨ms1, ms2, mk1, mk2⟩ := maskSwap_value
  obtain ⟨cs1, cs2, ck1, ck2⟩ := cmovSwap_value
  exact ⟨ms1.trans cs1.symm, ms2.trans cs2.symm, mk1.trans ck1.symm, mk2.trans ck2.symm⟩

/-! ## 3. The `CMOVcc` backend primitive (the form `renderLfundef` consumes)

The GE-solve CMOV swap at the `LinstrR.Lopn` level. SysV pins
`cmov_cswap_owned(x_ptr, y_ptr, cond)` with `x`→`%rdi`, `y`→`%rsi`,
`cond`→`%rdx`; scratch `%r8 = x`, `%r9 = y`, `%r10 = tmp`. The CMOV shape needs
the flag set first — a `TEST %rdx, %rdx` sets `ZF = (cond == 0)`, so `cmovne`
(move iff `!ZF`, i.e. iff `cond ≠ 0`) performs the swap exactly when the pivot
bit is set. `cmov64L`/`test64L` are the `CMOVcc` printer primitives the
MAYO/UOV/QRUOV/SNOVA GE-solve emits reuse; `CMOVcc` has no `catCryptDialect`
front op, so this shape is a backend primitive, not a front-compiled kernel
(the front-expressible CT-select is the mask swap of §4b). -/

/-- A 64-bit `CMOVcc` at the `Lcmd` level: `Lopn [d] CMOV<cc>:64 [d, s]`
    (`d := cc ? s : d`). The `d` self-source is the two-address implicit
    destination, matching the binop arity the printer renders. -/
def cmov64L (cc d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 ("CMOV" ++ cc)) [.reg d, s]⟩

/-- A 64-bit `TEST d, s` (`Lopn [d] TEST:64 [d, s]`) setting `ZF`. -/
def test64L (d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 "TEST") [.reg d, s]⟩

/-- Memory cell `[base + 0]`. -/
def cell (base : String) : LOperand := memCell base

/-- The owned-RA CMOV conditional-swap body: load `[x_ptr]`→`R8`, `[y_ptr]`→`R9`,
    set `ZF` from `cond` (`RDX`), branchlessly swap `R8`/`R9` iff `cond ≠ 0` via
    two `cmovne`, store back. Scratch `R10 = tmp`. -/
def cmovSwapLcmd : Lcmd :=
  [ mov64L "R8" (cell "RDI")             -- x := [x_ptr]
  , mov64L "R9" (cell "RSI")             -- y := [y_ptr]
  , test64L "RDX" (.reg "RDX")           -- ZF := (cond == 0)
  , mov64L "R10" (.reg "R8")             -- tmp := x
  , cmov64L "NE" "R8" (.reg "R9")        -- if cond≠0: x := y
  , cmov64L "NE" "R9" (.reg "R10")       -- if cond≠0: y := tmp
  , mov64L (memName "RDI" 0) (.reg "R8") -- [x_ptr] := x
  , mov64L (memName "RSI" 0) (.reg "R9") ] -- [y_ptr] := y

/-- Every instruction of the `CMOVcc` conditional-swap body addresses memory by a
    base register and a compile-time displacement, the condition
    `EmitCtGate.lprogDirect` imposes on a secret-input kernel. -/
theorem cmovSwapLcmd_lcmdDirect : lcmdDirect cmovSwapLcmd = true := by decide

/-! ## 4. AT&T emission through the owned printer (no jasminc) -/

/-- Render the CMOV conditional-swap kernel to AT&T `.s` via `renderLfundef`.
    (The `CMOVcc` mnemonic is a backend printer primitive with no
    `catCryptDialect` front op — see `cmov64L`/`test64L`, reused by the
    MAYO/UOV/QRUOV/SNOVA GE-solve emits.) -/
def cmovSwapAsm : String := renderLfundef "ge_solve_cswap_cmov_owned" cmovSwapLcmd

/-! ## 4b. The mask conditional-swap, FRONT-COMPILED (no hand-built `Com`/`Lcmd`)

The `0 − cond` XOR-swap is pure `SExpr` arithmetic (`SSub`/`SXor`/`SAnd`), so the
deployed mask kernel is GENERATED through the verified front — NOT
hand-authored as `Lcmd`:

```
  maskSwapBodyLCT  (RScalarSetExpr 0−cond mask + XOR-swap over x,y,cond)
    --(translateDialectControl)--> Com catCryptDialect maskSrcCtx (.sword 64)
    --(cryptoDialectToJasminCom)-> Com jasminDialect maskInCtxt r64
    --(Com.toLprogPhysAbi)-------> Lprog
    --(renderLprogAtt)-----------> ge_solve_cswap_mask_owned .s
```

Three input words (`x, y, cond`) load from `inp` (RSI): `x = inp[0]`,
`y = inp[8]`, `cond = inp[16]`; the two swapped results store to `out` (RDI):
`x' = out[0]`, `y' = out[8]`. The `0 − cond` subtract renders as a wrapping
`subq` (all-ones iff `cond ≠ 0`), so `d := (x ⊕ y) & mask` gates the XOR-swap —
branch-free, no `cmov`. -/

/-- Sequence a `List LowCT` into an `RSeq` chain. -/
def seqLCT : List LowCT → LowCT
  | [] => .RScalarSetExpr "z0" (.SLit 0)
  | [c] => c
  | c :: cs => .RSeq c (seqLCT cs)

/-- The mask XOR-swap as a straight-line `LowCT` body over `x, y, cond`. The last
    two bindings (`xsw`, `ysw`) are the swapped outputs. -/
def maskSwapBodyLCT : LowCT :=
  seqLCT
    [ .RScalarSetExpr "mask" (.SSub (.SLit 0) (.SVar "cond"))               -- 0 − cond
    , .RScalarSetExpr "d" (.SAnd (.SXor (.SVar "x") (.SVar "y")) (.SVar "mask"))
    , .RScalarSetExpr "xsw" (.SXor (.SVar "x") (.SVar "d"))                 -- x ^ d
    , .RScalarSetExpr "ysw" (.SXor (.SVar "y") (.SVar "d")) ]              -- y ^ d

/-- Bind a name list onto a `replicate`-`sword 64` context, first name = head. -/
def bindAll : (names : List String) → VarMap (List.replicate names.length (.sword 64))
  | [] => VarMap.empty
  | n :: ns => (bindAll ns).bind n

/-- The three input words in word order (`x, y, cond`). -/
def maskWordNames : List String := ["x", "y", "cond"]
/-- Source context: 3 `u64` scalar slots. -/
def maskSrcCtx : Ctx := List.replicate 3 (.sword 64)
/-- Source `VarMap` (word 0 = `x` at the head). -/
def maskSrcVM : VarMap maskSrcCtx := bindAll maskWordNames

/-- Push `maskSwapBodyLCT` through the verified front and cap with
    `ret <name>`. `none` if the front declines. -/
def maskFrontComAt (name : String) : Option (Com catCryptDialect maskSrcCtx (.sword 64)) :=
  match translateDialectControl maskSrcVM maskSwapBodyLCT with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted mask XOR-swap, lowered to the jasmin dialect. -/
def maskLoweredOpt :=
  (maskFrontComAt "ysw").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end (definitional). -/
private theorem maskLowered_isSome : maskLoweredOpt.isSome := rfl

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64
/-- The input context: 3 `r64` words. -/
abbrev maskInCtxt : Ctxt jasminDialect := List.replicate 3 r64

/-- The deployed mask conditional-swap `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
@[no_expose] def maskSwapCom : Com jasminDialect maskInCtxt r64 :=
  maskLoweredOpt.get maskLowered_isSome

/-- **Provenance**: the front pipeline, applied end to end, is DEFINITIONALLY
    the deployed mask `Com`. -/
theorem maskSwapCom_provenance :
    (maskFrontComAt "ysw").bind DialectToJasminCom.cryptoDialectToJasminCom
      = some maskSwapCom :=
  (Option.some_get maskLowered_isSome).symm

/-- Input-load map: `x = inp[0]`, `y = inp[8]`, `cond = inp[16]` (word `2 − slot`
    at byte offset `8·(2 − slot)`, the `u64` stride on `RSI`). -/
def maskInLoadMap : InLoadMap := fun slot =>
  if slot ≤ 2 then some ("RSI", 8 * (2 - slot)) else none

/-- Output-store map: `x' → out[0]`, `y' → out[8]` (the last two bindings). -/
def maskOutStoreMap : OutStoreMap := [("RDI", 0), ("RDI", 8)]

/-- The mask conditional-swap as an owned-RA, two-address `Lprog`, exported under
    the symbol `ge_solve_cswap_mask_owned`. -/
def maskSwapLprog : Lprog :=
  Com.toLprogPhysAbi maskSwapCom "ge_solve_cswap_mask_owned"
    (fun _ => none) (fun _ => none) maskInLoadMap maskOutStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)

/-- Render the mask conditional-swap kernel to AT&T `.s`, straight from the
    front-lowered owned `Lprog` (no jasminc, no hand-built `Lcmd`). -/
def maskSwapAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned maskSwapLprog

/-! ## 4c. The constant-time obligation of the deployed mask kernel

The pivot mask is derived from the secret oil-space basis, so the deployed
conditional-swap kernel is emitted under a secret-input policy and its addressing
must be index-free. The check is discharged structurally rather than by
evaluating the export: `maskSwapCom` binds only register arithmetic, so it is in
the index-free fragment `ComJasminCTByConstruction`, and
`ComToLfundefDirect.comToLfundef_lcmdDirect` with
`AllocCTPreservation.toLprogPhysAbi_lcmdDirect` carry that through the virtual
body and the deployed allocation to the exported program. -/

/-- The policy of the GE-solve conditional swap: its pivot mask is secret, so it
    is emitted only through the directness check. -/
def maskSwapPolicy : EmitCtGate.CtPolicy :=
  EmitCtGate.CtPolicy.secretInputs
    "the pivot mask of the GE-solve conditional swap is derived from the secret oil-space basis"

/-- The front-generated mask conditional-swap `Com` binds only register
    arithmetic, so it is in the index-free fragment of `Com jasminDialect`. -/
theorem maskSwapCom_indexFree : ComJasminCTByConstruction maskSwapCom :=
  (comJasminCT?_eq_true_iff maskSwapCom).mp rfl

/-- No function body of the mask conditional-swap export uses register-indexed
    addressing. -/
theorem maskSwapLprog_lprogDirect : EmitCtGate.lprogDirect maskSwapLprog = true := by
  rw [EmitCtGate.lprogDirect, List.all_eq_true]
  intro f hf
  simpa using
    toLprogPhysAbi_lcmdDirect maskSwapCom "ge_solve_cswap_mask_owned"
      (fun _ => none) (fun _ => none) maskInLoadMap maskOutStoreMap
      ["RDI", "RSI"] [64, 64] none 0 false
      (comToLfundef_lcmdDirect maskSwapCom (fun _ => none) maskSwapCom_indexFree) f hf

/-- The gate admits the mask conditional swap under its secret-input policy. -/
theorem maskSwap_emitChecked :
    EmitCtGate.emitChecked LprogOptPipeline.renderOwned maskSwapPolicy
        "ge_solve_cswap_mask_owned" maskSwapLprog
      = .ok (LprogOptPipeline.renderOwned maskSwapLprog) :=
  EmitCtGate.emitChecked_of_direct _ _ _ maskSwapLprog_lprogDirect

/-- **The deployed kernel's leakage conclusion.** The gathered `JInstr 64` block
    of every function body of the mask conditional-swap export has the same
    machine leakage trace from any two initial states, so the address sequence
    carries no information about the secret pivot mask. The statement is about
    the gathered block, not about the rendered text or the bytes. -/
theorem maskSwap_gather_constant_time {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ maskSwapLprog.lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) (s₁ s₂ : JState 64) :
    blockLeak s₁ g = blockLeak s₂ g :=
  EmitCtGate.emitChecked_gather_constant_time (render := LprogOptPipeline.renderOwned)
    (sym := "ge_solve_cswap_mask_owned") rfl maskSwap_emitChecked hf hg s₁ s₂

/-! ## 4d. The negative control

The constant-time results above constrain the address channel, and the channel
separates programs: a block whose effective addresses read a register value has
a leakage trace that differs between two states disagreeing on that register.
The witness is the table form of the same conditional select, which reads its
result at `base + 8 · cond` instead of masking. -/

/-- A conditional select reading its result at the register-indexed address
    `base + 8 · cond`: the table form of the conditional swap. -/
def condIndexedSelectBody (dst base cond : String) : List (JInstr 64) :=
  [ .loadMemIdx dst base cond 8 ]

/-- The machine state whose registers are all zero. -/
def condZeroState : JState 64 := { regs := fun _ => 0 }

/-- The machine state whose registers are all zero except `"cond"`, which is
    one. -/
def condOneState : JState 64 := { regs := fun r => if r = "cond" then 1 else 0 }

/-- The register-indexed select is outside the direct-addressing class, so the
    hypothesis of `allDirect_constant_time` is unavailable for it. -/
theorem condIndexedSelectBody_not_allDirect :
    allDirect (condIndexedSelectBody "d" "base" "cond") = false := by decide

/-- **The negative control.** Two states differing only in the condition
    register give the register-indexed select two different leakage traces, so
    the conclusion `cmovSwapBody_constant_time` and `maskSwapBody_constant_time`
    draw fails for a block of the same family that indexes on the condition. -/
theorem condIndexedSelect_leaks_cond :
    blockLeak condZeroState (condIndexedSelectBody "d" "base" "cond")
      ≠ blockLeak condOneState (condIndexedSelectBody "d" "base" "cond") := by
  decide

/-- The register-indexed select at the `Lcmd` level: a `MOV` whose source is the
    SIB operand `RSI[RDX*8]`, with `RDX` the condition register. -/
def condIndexedSwapLcmd : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] (withWidthTag 64 "MOV") [.arrIdx "RSI" "RDX" 8]⟩ ]

/-- The register-indexed select as a one-function `Lprog`. -/
def condIndexedSwapLprog : Lprog :=
  { lp_funcs := [("ge_solve_cswap_indexed", { lfd_body := condIndexedSwapLcmd })] }

/-- The register-indexed select fails the whole-program directness check that
    `maskSwapLprog_lprogDirect` establishes for the deployed kernel. -/
theorem condIndexedSwapLprog_not_lprogDirect :
    EmitCtGate.lprogDirect condIndexedSwapLprog = false := by decide

/-- The gate rejects the register-indexed select under the same secret-input
    policy that admits the mask kernel, naming the offending function and
    instruction. -/
theorem condIndexedSwap_emitChecked_error :
    EmitCtGate.emitChecked LprogOptPipeline.renderOwned maskSwapPolicy
        "ge_solve_cswap_indexed" condIndexedSwapLprog
      = .error (EmitCtGate.offenderMessage "ge_solve_cswap_indexed"
          "ge_solve_cswap_indexed"
          ⟨0, .Lopn [.reg "R8"] (withWidthTag 64 "MOV") [.arrIdx "RSI" "RDX" 8]⟩) :=
  rfl

/-! ## 5. Rendered asm -/

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. Emit driver -/

/-- Write the owned-backend CT conditional-swap `.s` kernel into the bench
    directory, through the `EmitCtGate` gate under `maskSwapPolicy`: a program
    with a register-indexed access raises `EmitCtGate.offenderMessage` instead of
    reaching the file. The deployed conditional-swap artifact is the
    FRONT-GENERATED mask twin (via `translateDialectControl` +
    `cryptoDialectToJasminCom`), which denotes the same conditional swap as the
    `CMOVcc` shape (`maskSwap_denotes_cmovSwap`). The `CMOVcc` shape stays as the
    backend-printer-primitive witness (`cmovSwapAsm`), not a deployed artifact. -/
def emit : IO Unit :=
  EmitCtGate.emitCheckedTo LprogOptPipeline.renderOwned maskSwapPolicy
    "ge_solve_cswap_mask_owned" maskSwapLprog
    "bench/mayo_compare/gen_com/ge_solve_cswap_mask_owned.s"

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectEmit in
/-- `lake env lean` entry point: emit the owned-backend CT conditional-swap `.s`. -/
private def main : IO Unit := emit
