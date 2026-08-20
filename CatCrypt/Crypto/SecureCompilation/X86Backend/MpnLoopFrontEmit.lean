/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportScalarAcc
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

set_option autoImplicit false

/-!
# FRONT-sourced runtime-N GMP mpn loop kernels (task #20)

The runtime-N looped GMP mpn kernels, front-compiled end-to-end — covered
`LowCT` loop bodies through `TranslateDialectRuntimeLoop.rolledForLoopNRt`
(`translateDialectControl` → `cryptoDialectToJasminCom` → `ComL.forLoopNRt`)
and the committed owned exports. NO hand-authored `Com`/`Lcmd`/`JInstr`.

Two export tiers:

* **No-carry family** (`and/ior/xor/com/copyi/zero`): the output array IS the
  loop accumulator — the committed array-accumulator export
  `ComL.toLprogPhysAbi` (via `rolledForLoopNRtLprog`).
* **Carry family** (`add/sub`): the loop-carried value is the SCALAR
  carry/borrow bit (the half-add-split idiom of
  `MpnAddCarryFrontPrototype`); the output array is a loop INVARIANT written
  via `RArrStore`. Exported through the scalar-accumulator variant
  `ComL.toLprogPhysAbiScalarAcc` (`VIR/JasminLprogExportScalarAcc.lean`),
  which returns the final carry/borrow in `RAX` — GMP's
  `__gmpn_add_n`/`__gmpn_sub_n` return-value ABI.

## ABI (deployed symbols preserved)

SysV, positional (`argName j ↦ abiArgs[j]`), matching
`bench/integration/mpn_loop_owned_kat.c`:

| symbol | signature |
|---|---|
| `mpn_{add,sub,and,ior,xor}_n_loop_owned` | `(rp=RDI, ap=RSI, bp=RDX, n=RCX)` |
| `mpn_{com_n,copyi}_loop_owned` | `(rp=RDI, ap=RSI, n=RDX)` |
| `mpn_zero_loop_owned` | `(rp=RDI, n=RSI)` |
| `mpn_norm_u32len_loop_owned` | `(ap=RDI, n=RSI)`, u32 length in `RAX` |

**Carry-in seed: MOV-0 prologue (no 5th argument).** GMP's `mpn_add_n` has no
carry-in parameter, so the carry seed variable sits at arg slot 4 — beyond the
4-register `abiArgs` — and is immediate-substituted to `0` by `mpnSeedImm`
(`ImmSlotMap`, `4 ↦ 0`): the loop prologue is `MOV acc, #0`, and no 5th SysV
register is read. `add` returns the carry limb, `sub` the borrow limb, in
`RAX` (the C harness may ignore it; asserting it against `__gmpn_*`'s return
is a KAT upgrade).

## The 64-bit borrow idiom (sub)

`MpnAddCarryFrontPrototype` sketches `mpn_sub_n` as "`SSub` with a `+2^64`
bias" (the 32-bit-limb `Secp256k1FeMulFront.genSub` pattern) — but at 64-bit
limb width the bias literal `2^64` does not fit a word, so that exact form is
not HW-faithful. The 64-bit analogue used here is the complement identity

```
  a - b - bw  =  a + ~b + (1 - bw)        (mod 2^64)
  borrow-out  =  1 - carry(a + ~b + (1 - bw))
```

with the SAME two-stage half-add carry split as `add` (`halfCarry`), `~b` as
`SXor b mask64`, and the `{0,1}` flips as `SXor _ 1`. All intermediates stay
`< 2^64`, so the unbounded-`Nat` `SExpr` model and the 64-bit machine agree
(the stage carries are mutually exclusive, as in `add`).

## Regen driver (run from repo root)

```
lake env lean bench/integration/emit_loop_owned.lean
```

runs `MpnLoopEmit.emitMain`, which renders the deployed kernels from this
module's `Lprog` values (the `*AsmFront` strings) and writes them to
`bench/integration/gen_com/*.s`, alongside the hand-tier `*_handtwin.s` perf
twins, `mpn_cmp_loop_owned.s`, and the owned-only `blk4` pair. Byte-KAT:
`make -f Makefile.loop_owned run` in `bench/integration/` (vs libgmp
`__gmpn_*`, 50k trials, sizes 1..256).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype
  (seqAll halfCarry mask64 N AN r64 Γbody addBodyLowCT)

/-! ## 1. No-carry family (array accumulator, committed `toLprogPhysAbi` export)

`out[i] := f(a[i], b[i])` / `f(a[i])` / `const`: the out array is the loop
accumulator (`init = out`), inputs are invariants — the deployed
qruov/sdith-shaped export path, unchanged. -/

/-- Binary no-carry body: `out[i] = op a[i] b[i]`. -/
def binBody (op : SExpr → SExpr → SExpr) : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "r" (op (.SVar "ai") (.SVar "bi"))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyBin : Ctx := [.memref N, .sword 64, .memref N, .memref N]
def vmBin : VarMap ΓbodyBin :=
  ((((VarMap.empty.bind (t := .memref N) "b").bind
      (t := .memref N) "a").bind (t := .sword 64) "idx").bind (t := .memref N) "out")

/-- `Γ` newest-first `[n, b, a, out]`: root slots `a0 = out → RDI`,
    `a1 = a → RSI`, `a2 = b → RDX`, `a3 = n → RCX`. -/
def ΓouterBin : Ctxt jasminDialect := [.reg 64, AN, AN, AN]

def binLprog (name : String) (op : SExpr → SExpr → SExpr) : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterBin) (accCTy := .memref N)
    (invCTys := [.memref N, .memref N])
    vmBin "out" (binBody op)
    (count := .here)
    (init := .there (.there (.there .here)))
    (invs := .cons (.there (.there .here)) (.cons (.there .here) .nil))
    name (argName 0) [argName 1, argName 2]
    ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]

def andLprog : Option Lprog := binLprog "mpn_and_n_loop_owned" .SAnd
/-- `a OR b = (a XOR b) XOR (a AND b)` — the `SExpr` alphabet has no `SOr`. -/
def iorLprog : Option Lprog := binLprog "mpn_ior_n_loop_owned"
  (fun x y => .SXor (.SXor x y) (.SAnd x y))
def xorLprog : Option Lprog := binLprog "mpn_xor_n_loop_owned" .SXor

/-- Unary no-carry body: `out[i] = f a[i]` (`com`: `~a`, `copyi`: `a`). -/
def unBody (f : SExpr → SExpr) : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "r" (f (.SVar "ai"))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyUn : Ctx := [.memref N, .sword 64, .memref N]
def vmUn : VarMap ΓbodyUn :=
  (((VarMap.empty.bind (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind (t := .memref N) "out")

/-- `Γ` newest-first `[n, a, out]`: `a0 = out → RDI`, `a1 = a → RSI`,
    `a2 = n → RDX`. -/
def ΓouterUn : Ctxt jasminDialect := [.reg 64, AN, AN]

def unLprog (name : String) (f : SExpr → SExpr) : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterUn) (accCTy := .memref N)
    (invCTys := [.memref N])
    vmUn "out" (unBody f)
    (count := .here)
    (init := .there (.there .here))
    (invs := .cons (.there .here) .nil)
    name (argName 0) [argName 1]
    ["RDI", "RSI", "RDX"] [64, 64, 64]

def comLprog : Option Lprog := unLprog "mpn_com_n_loop_owned"
  (fun x => .SXor x (.SLit mask64))
def copyLprog : Option Lprog := unLprog "mpn_copyi_loop_owned" (fun x => x)

/-- Nullary body: `out[i] = 0`. -/
def zeroBody : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RScalarSetExpr "r" (.SLit 0)
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"r", .TU64⟩ ]

def ΓbodyZero : Ctx := [.memref N, .sword 64]
def vmZero : VarMap ΓbodyZero :=
  ((VarMap.empty.bind (t := .sword 64) "idx").bind (t := .memref N) "out")

def ΓouterZero : Ctxt jasminDialect := [.reg 64, AN]

def zeroLprog : Option Lprog :=
  rolledForLoopNRtLprog (Γouter := ΓouterZero) (accCTy := .memref N)
    (invCTys := [])
    vmZero "out" zeroBody
    (count := .here)
    (init := .there .here)
    (invs := .nil)
    "mpn_zero_loop_owned" (argName 0) []
    ["RDI", "RSI"] [64, 64]

/-! ## 2. Carry family (scalar accumulator, `toLprogPhysAbiScalarAcc` export)

The loop-carried value is the carry/borrow bit (`.sword 64` accumulator); the
out array is an invariant written via `RArrStore`. `Γouter` is GMP-positional:
newest-first `[cy0seed, n, b, a, out]` = root slots `a0 = out(rp) → RDI`,
`a1 = a(ap) → RSI`, `a2 = b(bp) → RDX`, `a3 = n → RCX`, `a4 = cy0seed`
(imm-substituted `0`, never a register). -/

/-- GMP-positional outer context for `add`/`sub` (newest-first
    `[cy0seed, n, b, a, out]`). -/
def ΓouterCarry : Ctxt jasminDialect := [r64, r64, AN, AN, AN]

/-- The MOV-0 carry-seed map: arg slot 4 (`cy0seed`, beyond the 4-register
    `abiArgs`) is the compile-time constant `0`, so the accumulator seed
    lowers to `MOV acc, #0` and the kernel keeps GMP's 4-argument ABI. -/
def mpnSeedImm : ImmSlotMap := fun j => if j == 4 then some 0 else none

/-- The GMP 4-register SysV signature `(rp, ap, bp, n)`. -/
def gmpAbiArgs : List String := ["RDI", "RSI", "RDX", "RCX"]

/-- `mpn_add_n` front loop: the prototype's carry-threading body
    (`addBodyLowCT`, acc `cy`, two half-add stages) over the GMP-positional
    `ΓouterCarry`. `count = n`, `init = cy0seed` (imm-0), `invs = [a, b, out]`
    (the `Γbody`/`vmBody` binder order). -/
def addRtProgOpt : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N])
    CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddCarryFrontPrototype.vmBody
    "cy" addBodyLowCT
    (count := .there .here)
    (init := .here)
    (invs := .cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil)))

/-- The per-limb `mpn_sub_n` body threading the borrow `bw`:
    `out[i] = a[i] - b[i] - bw` via the complement identity
    `a + ~b + (1 - bw)` with the two-stage half-add carry split;
    `bw' = 1 - (c1 + c2)`. The `{0,1}` flips are `SXor _ 1`. -/
def subBodyLowCT : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes (8 * N)⟩ "ix"
  -- ~b and the complemented borrow-in (1 - bw)
  , .RScalarSetExpr "nb" (.SXor (.SVar "bi") (.SLit mask64))
  , .RScalarSetExpr "cx" (.SXor (.SVar "bw") (.SLit 1))
  -- stage 1: a + ~b
  , .RScalarSetExpr "c1" (halfCarry "ai" "nb")
  , .RScalarSetExpr "s1" (.SAnd (.SAdd (.SVar "ai") (.SVar "nb")) (.SLit mask64))
  -- stage 2: + (1 - bw); store the difference limb
  , .RScalarSetExpr "c2" (halfCarry "s1" "cx")
  , .RScalarSetExpr "df" (.SAnd (.SAdd (.SVar "s1") (.SVar "cx")) (.SLit mask64))
  , .RArrStore ⟨"out", .TBytes (8 * N)⟩ "ix" ⟨"df", .TU64⟩
  -- borrow-out = 1 - total carry (stage carries mutually exclusive)
  , .RScalarSetExpr "bw" (.SXor (.SAdd (.SVar "c1") (.SVar "c2")) (.SLit 1)) ]

/-- The sub-body `VarMap` (same binder order as the add prototype's `vmBody`;
    accumulator name `bw`). -/
def vmBodySub : VarMap Γbody :=
  (((((VarMap.empty.bind (t := .memref N) "out").bind
      (t := .memref N) "b").bind
      (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind
      (t := .sword 64) "bw")

/-- `mpn_sub_n` front loop (borrow accumulator `bw`, seed `0` = no borrow-in). -/
def subRtProgOpt : Option (ComL ΓouterCarry (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := ΓouterCarry) (accCTy := .sword 64)
    (invCTys := [.memref N, .memref N, .memref N])
    vmBodySub "bw" subBodyLowCT
    (count := .there .here)
    (init := .here)
    (invs := .cons (.there (.there (.there .here)))
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there .here)))) .nil)))

/-- `mpn_add_n_loop_owned` through the scalar-accumulator export: carry seeded
    `MOV acc, #0` (`mpnSeedImm`), carry-out returned in `RAX`. -/
def addLprogFront : Option Lprog :=
  addRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_add_n_loop_owned"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64])

/-- `mpn_sub_n_loop_owned` through the scalar-accumulator export: borrow seeded
    `MOV acc, #0`, borrow-out returned in `RAX`. -/
def subLprogFront : Option Lprog :=
  subRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_sub_n_loop_owned"
      (fun _ => none) mpnSeedImm gmpAbiArgs [64, 64, 64, 64])

/-! ## 2b. Normalization scan (scalar accumulator, u32-length result)

`mpn_norm_u32len_loop_owned(ap=RDI, n=RSI) → RAX`: the normalized u32 limb
length of an `n`-u64-limb little-endian array — `1 + i` for the highest
nonzero u32 half-limb index `i`, or `1` for the all-zero array (GMP's minimum
normalized length, via the imm-`1` accumulator seed). The scan is a
branch-free forward full pass — data-independent trip count, no early exit,
no data-dependent branch: each u64 limb splits into its lo/hi u32 halves,
`nz32E` maps a half to its `{0,1}` nonzero flag, and `selE` multiplex-selects
the running length, so a nonzero limb overwrites the accumulator and higher
limbs overwrite lower ones. Consumed by the u32 seam adapter
(`bench/integration_owned/lean_mpn_adapter_u32.c`) to compute `*plngc` after
`vlmpn_add_u32`. -/

/-- `2^32 - 1`, the u32 half-limb mask. -/
def mask32 : Nat := 4294967295

/-- `{0,1}` nonzero flag of a value `< 2^32`: `(x + (2^32-1)) >> 32` is `1`
    iff `x ≥ 1`. The sum stays `< 2^33`, so the unbounded-`Nat` `SExpr` model
    and the 64-bit machine agree (`nz32E_evalBV`). -/
def nz32E (e : SExpr) : SExpr := .SShr (.SAdd e (.SLit mask32)) (.SLit 32)

/-- Multiplex select by a `{0,1}` flag: `c*x + (1-c)*y`, with `1-c` as
    `SXor c 1`. One addend is always `0`, so no wrap occurs
    (`selE_evalBV`). -/
def selE (c x y : SExpr) : SExpr :=
  .SAdd (.SMul c x) (.SMul (.SXor c (.SLit 1)) y)

/-- Per-limb normalization-scan body threading the running u32 length `len`:
    split `a[idx]` into u32 halves, flag each half nonzero, and select
    `2*idx + 1 + nzhi` over the running `len` iff the limb is nonzero
    (`nzw = nzlo OR nzhi`, the or-from-xor/and identity). -/
def normBody : LowCT := seqAll
  [ .RScalarSetExpr "ix" (.SVar "idx")
  , .RArrLoad ⟨"w", .TU64⟩ ⟨"a", .TBytes (8 * N)⟩ "ix"
  , .RScalarSetExpr "lo" (.SAnd (.SVar "w") (.SLit mask32))
  , .RScalarSetExpr "hi" (.SShr (.SVar "w") (.SLit 32))
  , .RScalarSetExpr "nzlo" (nz32E (.SVar "lo"))
  , .RScalarSetExpr "nzhi" (nz32E (.SVar "hi"))
  , .RScalarSetExpr "nzw"
      (.SXor (.SXor (.SVar "nzlo") (.SVar "nzhi"))
             (.SAnd (.SVar "nzlo") (.SVar "nzhi")))
  , .RScalarSetExpr "cand"
      (.SAdd (.SAdd (.SShl (.SVar "ix") (.SLit 1)) (.SLit 1)) (.SVar "nzhi"))
  , .RScalarSetExpr "len" (selE (.SVar "nzw") (.SVar "cand") (.SVar "len")) ]

def ΓbodyNorm : Ctx := [.sword 64, .sword 64, .memref N]
def vmNorm : VarMap ΓbodyNorm :=
  (((VarMap.empty.bind (t := .memref N) "a").bind
      (t := .sword 64) "idx").bind (t := .sword 64) "len")

/-- `Γ` newest-first `[len0seed, n, a]`: root slots `a0 = a → RDI`,
    `a1 = n → RSI`, `a2 = len0seed` (imm-substituted `1`, never a
    register). -/
def ΓouterNorm : Ctxt jasminDialect := [r64, r64, AN]

/-- The MOV-1 length-seed map: arg slot 2 (`len0seed`, beyond the 2-register
    `abiArgs`) is the compile-time constant `1`, the minimum normalized
    length. -/
def normSeedImm : ImmSlotMap := fun j => if j == 2 then some 1 else none

/-- Normalization-scan front loop (running-length accumulator `len`,
    seed `1`). -/
def normRtProgOpt : Option (ComL ΓouterNorm (mapTy (.sword 64))) :=
  rolledForLoopNRt (Γouter := ΓouterNorm) (accCTy := .sword 64)
    (invCTys := [.memref N])
    vmNorm "len" normBody
    (count := .there .here)
    (init := .here)
    (invs := .cons (.there (.there .here)) .nil)

/-- `mpn_norm_u32len_loop_owned` through the scalar-accumulator export: length
    seeded `MOV acc, #1` (`normSeedImm`), normalized u32 length returned in
    `RAX`. -/
def normLprogFront : Option Lprog :=
  normRtProgOpt.map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_norm_u32len_loop_owned"
      (fun _ => none) normSeedImm ["RDI", "RSI"] [64, 64])

/-- `nz32E` computes the `{0,1}` nonzero flag on the wrapping-`u64` evaluator:
    for a value with zero high half, `(x + (2^32-1)) >>> 32` is `0` iff
    `x = 0`. -/
theorem nz32E_evalBV (β : String → BitVec 64) (e : SExpr)
    (h : e.evalBV β >>> 32 = 0) :
    (nz32E e).evalBV β = if e.evalBV β = 0 then 0 else 1 := by
  simp only [nz32E, SExpr.evalBV, mask32]
  split <;> simp_all
  bv_omega

/-- `selE` is the two-way multiplexer on the wrapping-`u64` evaluator: with a
    `{0,1}` selector, `c*x + (c ^^^ 1)*y` is `x` at `c = 1` and `y` at
    `c = 0`. -/
theorem selE_evalBV (β : String → BitVec 64) (c x y : SExpr)
    (h : c.evalBV β = 0 ∨ c.evalBV β = 1) :
    (selE c x y).evalBV β
      = if c.evalBV β = 1 then x.evalBV β else y.evalBV β := by
  rcases h with h | h <;> simp [selE, SExpr.evalBV, h]

/-! ## 3. Front-acceptance gates

Each kernel's front compile returns `some` (the covered lowering accepted the
body and the export produced an `Lprog`). Byte-level conformance is the
external libgmp KAT (`bench/integration/Makefile.loop_owned`), NOT these. -/

theorem andLprog_isSome : andLprog.isSome := by native_decide
theorem iorLprog_isSome : iorLprog.isSome := by native_decide
theorem xorLprog_isSome : xorLprog.isSome := by native_decide
theorem comLprog_isSome : comLprog.isSome := by native_decide
theorem copyLprog_isSome : copyLprog.isSome := by native_decide
theorem zeroLprog_isSome : zeroLprog.isSome := by native_decide
theorem addLprogFront_isSome : addLprogFront.isSome := by native_decide
theorem subLprogFront_isSome : subLprogFront.isSome := by native_decide

/- The normalization-scan front compile returns `some`, and so does its
scalar-accumulator export (elaboration-time checks; no axiom). -/
#guard normRtProgOpt.isSome
#guard normLprogFront.isSome

/-! ## 4. Emit driver -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- Write the 8 front-sourced runtime-N mpn kernels to
    `bench/integration/gen_com/*.s` (run from the repo root). The block-unrolled
    `blk4` pair and `mpn_cmp` remain `MpnLoopEmit.emitMain`'s outputs. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/integration/gen_com"
  let wr (p : String) (o : Option Lprog) : IO Unit := do
    match o with
    | some lp => IO.FS.writeFile p (CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp)
    | none => throw (IO.userError s!"front-compile failed for {p}")
  wr "bench/integration/gen_com/mpn_and_n_loop_owned.s" andLprog
  wr "bench/integration/gen_com/mpn_ior_n_loop_owned.s" iorLprog
  wr "bench/integration/gen_com/mpn_xor_n_loop_owned.s" xorLprog
  wr "bench/integration/gen_com/mpn_com_n_loop_owned.s" comLprog
  wr "bench/integration/gen_com/mpn_copyi_loop_owned.s" copyLprog
  wr "bench/integration/gen_com/mpn_zero_loop_owned.s" zeroLprog
  wr "bench/integration/gen_com/mpn_add_n_loop_owned.s" addLprogFront
  wr "bench/integration/gen_com/mpn_sub_n_loop_owned.s" subLprogFront
  IO.println "wrote 8 front-sourced mpn loop kernels (add/sub via scalar-acc export)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
