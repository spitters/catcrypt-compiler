/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

set_option autoImplicit false

/-!
# Validation: a runtime-count array sum front-compiled to a rolled `ComL.forLoopNRt`

This is the end-to-end witness for the runtime-trip rolled-loop front capability
(`TranslateDialectRuntimeLoop`). It authors the array sum
`out[0] = Σ_{i<n} a[i]` as a **LowCT loop body** (the covered fragment:
`RArrLoad`/`RScalarSetExpr`/`RArrStore`, with the loop counter `idx` as the array
index) and front-compiles it to a genuine `ComL.forLoopNRt` — ONE body copy + a
real back-edge — whose trip count `n` is a **RUNTIME argument** (read from a
register), NOT a compile-time `N`. This is the shape FAEST `ConvertToVole` needs:
its `num`/`depth`/`nblk` trip counts come from a runtime `cfg`.

```
  sumBodyLowCT (RArrLoad a[idx] + RArrLoad out[0] + RScalarSetExpr acc0+ai + RArrStore out[0])
    --(front: translateDialectControl over [out, idx, a])-->  Com catCryptDialect
    --(cryptoDialectToJasminCom)------------------------->  Com jasminDialect (= JLoopBodyN.update)
    --(ComL.forLoopNRt update count out [a] (ret out))--->  ComL  (ONE body copy + back-edge)
    --(ComL.toLprogPhysAbi [RDI,RSI,RDX] / renderLprogAtt)->  sum_front_rt.s (MOV Lctr, <RDX>)
```

Under the export's program-root `resolveVar` convention (newest binder resolves
to the highest arg slot), the outer context `[count, a, out]` (newest-first)
places `count` at `.here` → `a2` → the 3rd SysV integer register `RDX`. The
counter seed is therefore `MOV Lctr, a2` (a **register**), not `MOV Lctr, #N` (an
immediate) — the one instruction that distinguishes a runtime-trip loop.

The validation checks: (i) the front succeeds (`rolledForLoopNRt`); (ii) the
emitted body seeds the counter from the runtime arg register (`MOV Lctr, a2`)
with a REAL back-edge (`Lcond`/`Llabel`) and ONE body copy (bounded
`LOADIDX`/`STOREIDX`, independent of the runtime count); (iii) `ComL.denote =
the independent sum spec` at **two different runtime counts** (the trip is read
from the valuation, not baked in). The deployed C KAT lives at
`bench/rtloop_compare/sum_front_rt_kat.c` (driven by `sum_front_rt_emit.lean`),
which calls the kernel with several runtime `n` values.

Invoke (in-model gate):  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/RuntimeLoopFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RuntimeLoopFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 0. Dimensions -/

/-- The array capacity `N = 8` (the runtime count `n ≤ N`). Small enough that a
    plain 64-bit sum of `[0,255]` residues never overflows `2⁶⁴`. -/
def paramN : Nat := 8

/-! ## 1. The array-sum loop body, authored as covered LowCT

The loop body runs over the catCryptDialect context
`Γbody = [out:.memref 1, idx:.sword 64, a:.memref N]` (accumulator first, loop
index next, the input array as the invariant). `idx` is the loop binder;
`RArrLoad … idx` resolves it as the dynamic index → `memrefGetDyn` → `stackLoad`
SIB `LOADIDX` at the runtime trip counter. -/

/-- Sequence a list of `LowCT` into an `RSeq` chain (avoids manual paren nesting). -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- One trip of the array sum over the loop index `idx`:
    `out[0] := out[0] + a[idx]`. Declares the constant-zero index `z := 0` for the
    `out[0]` access. -/
def sumBodyLowCT : LowCT := seqAll [
  -- z := 0  (constant-zero index for the scalar accumulator slot out[0])
  .RScalarSetExpr "z" (.SLit 0),
  -- ai := a[idx]  (dynamic index at the runtime trip counter)
  .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * paramN)⟩ "idx",
  -- acc0 := out[0]  (running accumulator)
  .RArrLoad ⟨"acc0", .TU64⟩ ⟨"out", .TBytes 8⟩ "z",
  -- s := acc0 + ai
  .RScalarSetExpr "s" (.SAdd (.SVar "acc0") (.SVar "ai")),
  -- out[0] := s
  .RArrStore ⟨"out", .TBytes 8⟩ "z" ⟨"s", .TU64⟩ ]

/-! ## 2. The body context + VarMap

`Γbody = [out, idx, a]` (head-first); `out` is the accumulator (`.here`), `idx`
the loop binder (`.there .here`), `a` the invariant (`.there² .here`). -/

/-- The body context: accumulator `out`, loop index `idx`, invariant `a`. -/
def Γbody : Ctx := [.memref 1, .sword 64, .memref paramN]

/-- The body VarMap: `out ↦ .here`, `idx ↦ .there .here`, `a ↦ .there² .here`. -/
def vmBody : VarMap Γbody :=
  (((VarMap.empty.bind (t := .memref paramN) "a").bind
      (t := .sword 64) "idx").bind (t := .memref 1) "out")

/-! ## 3. The outer program: front body → genuine `ComL.forLoopNRt`

Outer context `[count, a, out]` (newest-first; jasmin types `[.reg 64,
.stackArr 64 N, .stackArr 64 1]`): `count` is the runtime trip-count seed
(`.here` → `a2` → `RDX`), `a` the invariant seed (`.there .here` → `a1` →
`RSI`), `out` the accumulator seed (`.there² .here` → `a0` → `RDI`). ABI
`sum_front_rt(out, a, n)`. -/

/-- The outer (kernel-argument) jasmin context: `[count, a, out]` newest-first. -/
def Γouter : Ctxt jasminDialect := [.reg 64, .stackArr 64 paramN, .stackArr 64 1]

/-- The front-compiled runtime-trip rolled `ComL.forLoopNRt` (one body copy +
    back-edge, counter seeded from the runtime `count` register), or `none` if the
    front declines. -/
def sumComL : Option (ComL Γouter (.stackArr 64 1)) :=
  rolledForLoopNRt (Γouter := Γouter) (accCTy := .memref 1)
    (invCTys := [.memref paramN])
    vmBody "out" sumBodyLowCT
    (count := .here)
    (init := .there (.there .here))
    (invs := .cons (.there .here) .nil)

/-! ## 4. Gate: the front succeeds -/

/-- The array-sum loop body front-compiles to a genuine `ComL.forLoopNRt`. -/
theorem sumComL_isSome : sumComL.isSome := by native_decide

/-! ## 5. denote = independent sum spec (at TWO runtime counts) -/

/-- INDEPENDENT plain-`Nat` array-sum reference: `Σ_{i<cnt} a[i]`. -/
def natSumRt (a : Fin paramN → BitVec 64) (cnt : Nat) : Nat :=
  (List.range cnt).foldl
    (fun acc i => acc + (a ⟨i % paramN, Nat.mod_lt _ (by decide)⟩).toNat) 0

/-- Deterministic sample stream `a[i] = 7i + 3` (small, no 64-bit overflow). -/
def sampleA : Fin paramN → BitVec 64 := fun i => BitVec.ofNat 64 (i.val * 7 + 3)

/-- **denote = sum spec at runtime count 5.** The front-compiled runtime loop
    denotes the independent `Σ_{i<5} a[i]` — the fold runs `(count.lookup V).toNat
    = 5` times, read from the (newest, `.here`) `count` slot of the valuation. -/
theorem sumComL_denote_count5 :
    (sumComL.map (fun c =>
        (ComL.denote c
            (.cons (5 : BitVec 64) (.cons sampleA (.cons (fun _ => (0 : BitVec 64)) .nil)))
          ⟨0, by decide⟩).toNat))
      = some (natSumRt sampleA 5) := by native_decide

/-- **denote = sum spec at runtime count 8 (SAME program, different count).** The
    trip count is genuinely read from the valuation, not baked into the emit — the
    whole point of the runtime-trip capability. -/
theorem sumComL_denote_count8 :
    (sumComL.map (fun c =>
        (ComL.denote c
            (.cons (8 : BitVec 64) (.cons sampleA (.cons (fun _ => (0 : BitVec 64)) .nil)))
          ⟨0, by decide⟩).toNat))
      = some (natSumRt sampleA 8) := by native_decide

/-- **denote = sum spec at runtime count 0 (empty loop).** Zero trips → the seed
    `out[0] = 0`. Confirms the runtime count fully controls the fold length. -/
theorem sumComL_denote_count0 :
    (sumComL.map (fun c =>
        (ComL.denote c
            (.cons (0 : BitVec 64) (.cons sampleA (.cons (fun _ => (0 : BitVec 64)) .nil)))
          ⟨0, by decide⟩).toNat))
      = some 0 := by native_decide

/-! ## 6. The virtual body: runtime counter seed + real back-edge

Top-level (`nArgs = 3`), the loop node sits at depth `3`, so its trip counter is
`Lctr3` and `count` (`.here`) resolves to `a2` (the 3rd program-root argument,
which the SysV projection maps to `RDX`). -/

/-- The lowered (pre-RA) body of the runtime-count sum loop. -/
def sumBody : Option Lcmd :=
  sumComL.map (fun c => comLToBody 3 argName (fun _ => none) c 3)

/-- **Runtime counter seed:** the trip counter `Lctr3` is initialised from a
    **register** (the resolved runtime `count` argument `a2`), i.e. `MOV Lctr3,
    a2` — NOT `MOV Lctr3, #n`. This is the instruction that distinguishes a
    runtime-trip loop from the fixed-trip `forLoopN`, and the whole point of the
    capability (`a2` = 3rd SysV int arg = `RDX` = the `cfg`-driven trip count). -/
theorem sumBody_runtime_counter_seed :
    sumBody.map (fun b =>
      b.any (fun i => match i.li_i with
        | .Lopn dsts mnem srcs =>
            mnem == withWidthTag 64 "MOV" &&
            (dsts.filterMap LOperand.regName?).contains (loopCtr 3) &&
            (srcs.filterMap LOperand.regName?).contains (argName 2)
        | _ => false))
      = some true := by native_decide

/-- **Real back-edge:** the runtime-count loop lowers to a conditional jump
    (`Lcond`, rendered `jne .L<d>`) — a rolled loop, not an unrolled chain. -/
theorem sumBody_has_backedge :
    sumBody.map (fun b =>
      b.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
      = some true := by native_decide

/-! ## 7. Rolled physical lowering: real x86 back-edge, ONE body copy

3-arg ABI `sum_front_rt(out, a, n)` (`RDI = out`, `RSI = a`, `RDX = n`). -/

/-- The 3-arg-ABI physical body of the front-compiled runtime-count loop. -/
def physBody : Option Lcmd :=
  sumComL.map (fun c =>
    (ComL.toLfundefPhysAbi c (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]).lfd_body)

/-- **Real back-edge preserved through RA:** the physical body has both an internal
    `Llabel` and a `Lcond` (`jne .L<d>`) — a genuine counted loop, NOT an unrolled
    chain. -/
theorem physBody_has_backedge :
    physBody.map (fun b =>
      (b.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false))
        && (b.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)))
      = some true := by native_decide

/-- **Bounded depth (ONE body copy):** the indexed loads (`a[idx]`, `out[0]`)
    appear a FIXED number of times, independent of the runtime trip count `n` —
    NOT `n` unrolled copies. (Two `LOADIDX`: `a[idx]`, `out[0]`.) -/
theorem physBody_bounded_indexed_loads :
    physBody.map (fun b =>
      (b.filter (fun i => match i.li_i with
        | .Lopn _ "LOADIDX" _ => true | _ => false)).length)
      = some 2 := by native_decide

/-- **ONE indexed store** (`out[0]`), not `n` unrolled copies. -/
theorem physBody_one_indexed_store :
    physBody.map (fun b =>
      (b.filter (fun i => match i.li_i with
        | .Lopn _ "STOREIDX" _ => true | _ => false)).length)
      = some 1 := by native_decide

/-! ## 8. Emit driver -/

/-- The owned AT&T `.s` text for `sum_front_rt` (front-compiled, runtime-trip
    rolled). -/
def kernelAsm : Option String :=
  sumComL.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (ComL.toLprogPhysAbi c "sum_front_rt" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]))

/-- The emit renders. -/
theorem kernelAsm_isSome : kernelAsm.isSome := by native_decide

/-- Write the front-compiled runtime-trip rolled `.s`. -/
def emit (path : System.FilePath) : IO Unit :=
  match kernelAsm with
  | some asm => IO.FS.writeFile path asm
  | none => throw (IO.userError "front-compile of sum_front_rt runtime-count loop failed")

end CatCrypt.Crypto.SecureCompilation.Dialects.RuntimeLoopFrontValidate
