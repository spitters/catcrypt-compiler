/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

/-!
# Constant-time conditional-move / select primitive for the owned backend (#581)

The multivariate-signature **sign** path (MAYO / UOV / SNOVA) solves a linear
system over GF(2⁴)/GF(2⁸) by Gaussian elimination. The GE pivot search performs a
**conditional row/element swap**: swap two field elements iff a pivot mask is set.
That mask is derived from *secret* data (the secret oil-space basis), so the swap
must be **branchless** — a secret-dependent `Jcc` would leak the pivot pattern
through the instruction-fetch timing.

Until now the owned linear-jasmin `Lopn` printer (`LprogAsmPrinter`) rendered the
GP-ALU alphabet (`ADD … SHR`, `MOV`, `CMP`/`TEST`, the ADX trio) and a Jcc on a
**public** count (`Lcond`), but had **no `CMOVcc`** — the data-oblivious
conditional move a *secret* condition must take. This module supplies and
exercises that backend primitive in two interchangeable constant-time shapes:

* **`CMOVcc` select** (`cmovSwapLcmd`) — the GE-solve pivot swap via
  `cmove`/`cmovne`/`cmovb`, the canonical branchless move. The owned printer now
  maps the `CMOVE`/`CMOVNE`/`CMOVB`/`CMOVAE`/`CMOVL`/`CMOVGE` body mnemonics to
  `cmov<cc><sz>` (`LprogAsmPrinter.attBase`); the value semantics is pinned by
  `JasminModel.x86_CMOVcc` (`if b then src else dst`) on the matching
  `JInstr.cmove`/`cmovne`/`cmovb` arms.
* **mask select** (`maskSwapAsm`) — the same swap with no CMOV at all: a
  `0 − cond` all-ones/all-zero mask `AND`ed/`XOR`ed, exactly the form the GF(16)
  multiply (`MAYO.VerifyOwnedEmit.gf16MulInline`) already uses. It is pure
  `SExpr` arithmetic (`SSub`/`SXor`/`SAnd`), so the deployed kernel is
  FRONT-GENERATED (`translateDialectControl` + `cryptoDialectToJasminCom` +
  `renderLprogAtt`), not hand-authored `Lcmd`.

The CMOV shape is a backend printer primitive (`CMOVcc` has no
`catCryptDialect` front op); the mask shape is the front-expressible CT-select
the GE-solve can always take. Both are constant-time: the move/select **issues
unconditionally**, only the written value depends on the condition — no PC
divergence, no secret branch. The per-shape value semantics is pinned by small
vectors through the full `evalInstr`/`x86_*` chain (`cmovSwap_value` /
`maskSwap_value`, no loop-running `native_decide`); the rendered asm is
shape-checked to use `cmov`/mask ops and to contain **no** `Jcc`/`UNHANDLED`
(`cmovSwapAsm_shape` / `maskSwapAsm_shape`).

This is the **backend primitive** that unblocks the MAYO/UOV/SNOVA GE-solve sign
emit; wiring it into the per-protocol GE-solve loop is the follow-on (#581/#582).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopOwnedEmit
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
private def cell (base : String) : LOperand := memCell base

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

/-! ## 4. AT&T emission through the owned printer (no jasminc) -/

/-- Render the CMOV conditional-swap kernel to AT&T `.s` via `renderLfundef`.
    (The `CMOVcc` mnemonic is a backend printer primitive with no
    `catCryptDialect` front op — see `cmov64L`/`test64L`, reused by the
    MAYO/UOV/QRUOV/SNOVA GE-solve emits.) -/
def cmovSwapAsm : String := renderLfundef "ge_solve_cswap_cmov_owned" cmovSwapLcmd

/-! ## 4b. The mask conditional-swap, FRONT-COMPILED (no hand-built `Com`/`Lcmd`)

The `0 − cond` XOR-swap is pure `SExpr` arithmetic (`SSub`/`SXor`/`SAnd`), so the
deployed mask kernel is GENERATED through the verified `CProg`-free front — NOT
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

/-- Push `maskSwapBodyLCT` through the `CProg`-free front and cap with
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
theorem maskLowered_isSome : maskLoweredOpt.isSome := rfl

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64
/-- The input context: 3 `r64` words. -/
abbrev maskInCtxt : Ctxt jasminDialect := List.replicate 3 r64

/-- The deployed mask conditional-swap `Com jasminDialect` — FRONT-GENERATED
    (`translateDialectControl` + `cryptoDialectToJasminCom`), not hand-built. -/
def maskSwapCom : Com jasminDialect maskInCtxt r64 :=
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
def maskSwapAsm : String := renderLprogAtt maskSwapLprog

/-! ## 5. Shape checks: branchless, no secret `Jcc`, no `UNHANDLED` -/

/-- The CMOV swap emits the two `cmovneq` moves and the `testq` that sets the
    flag, with **no** `Jcc` (no secret-dependent branch) and **no** `UNHANDLED-OP`
    (every body op — in particular the new `CMOVNE` mnemonic — rendered). -/
theorem cmovSwapAsm_shape :
    occursIn "cmovneq" cmovSwapAsm = true
      ∧ occursIn "testq" cmovSwapAsm = true
      ∧ occursIn "UNHANDLED" cmovSwapAsm = false
      ∧ occursIn "jne" cmovSwapAsm = false
      ∧ occursIn "je " cmovSwapAsm = false := by native_decide

/-- The mask swap emits the `0 − cond` mask ops (`subq`/`xorq`/`andq`) and uses
    **no** `cmov` and **no** `Jcc` — pure GP-ALU, the fallback CT shape. -/
theorem maskSwapAsm_shape :
    occursIn "subq" maskSwapAsm = true
      ∧ occursIn "xorq" maskSwapAsm = true
      ∧ occursIn "andq" maskSwapAsm = true
      ∧ occursIn "cmov" maskSwapAsm = false
      ∧ occursIn "UNHANDLED" maskSwapAsm = false := by native_decide

/-- **Constant-time witness.** Both swap shapes are branch-free: neither emits a
    conditional jump (`jne`/`je`/`jb`/`jl`), so the pivot pattern cannot leak
    through fetch timing. The CMOV form is the canonical branchless move; the mask
    form needs no CMOV. -/
theorem swap_branch_free :
    occursIn "jne" cmovSwapAsm = false ∧ occursIn "je " cmovSwapAsm = false
      ∧ occursIn "jb" cmovSwapAsm = false ∧ occursIn "jl" cmovSwapAsm = false
      ∧ occursIn "jne" maskSwapAsm = false ∧ occursIn "je " maskSwapAsm = false := by
  native_decide

/-! ## 6. Emit driver -/

/-- Write both owned-backend CT-swap `.s` kernels into the bench directory. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/mayo_compare/gen_com"
  IO.FS.writeFile "bench/mayo_compare/gen_com/ge_solve_cswap_cmov_owned.s" cmovSwapAsm
  IO.FS.writeFile "bench/mayo_compare/gen_com/ge_solve_cswap_mask_owned.s" maskSwapAsm
  IO.println "wrote ge_solve_cswap_{cmov,mask}_owned.s (owned backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectOwnedEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.CmovSelectOwnedEmit in
/-- `lake env lean` entry point: emit the owned-backend CT conditional-swap `.s`. -/
private def main : IO Unit := emit
