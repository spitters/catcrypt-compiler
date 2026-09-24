/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth

@[expose] public section

set_option autoImplicit false

/-!
# Validate: a **nested** runtime loop, front-compiled into `ComL.forLoopNRtNested`

`ComL.forLoopNRt`'s per-iteration body is a straight-line `Com`, so it cannot
express the GGM Phase-3 double fold `for jd<D: for idx<num>>(jd+1): …`
(`TranslateDialectPhaseCompose` §4). `ComL.forLoopNRtNested` (JasminLprogExport)
makes the inner loop first-class, and the rolled-loop dispatcher's nested route
(`FrontRoutePlan.compileNested` at the `plain` body front) front-compiles both the
inner-count body and the inner-update body via `frontLoopBodyJ` (no hand-authored
`Com`). This module validates that route with a
`native_decide` check against the proven interpreter semantics.

## The GGM Phase-3 shape

* outer loop `jd ∈ 0..D` (runtime count `D`);
* inner loop `idx ∈ 0..(num >> (jd+1))` — the inner trip **recomputed per outer
  pass** from the outer index and the runtime invariant `num` (the front-compiled
  inner-count body `cnt := num >> (jd+1)`);
* innermost body `acc[0] += 2` (the net effect of GGM's constant inner `outlen = 2`
  loop, front-compiled), so the double fold equals
  `ggmNestedFold D num 2`.

## What is validated (`native_decide`)

* `nestGGM_isSome` — the two bodies front-compile and wrap into ONE `forLoopNRtNested`.
* `nestGGM_is_nested_node` — the spine is the nested node.
* `nestGGM_denote_num8` / `nestGGM_denote_num16` — `ComL.denote = ggmNestedFold 3 num 2`
  (`= 14` at `num=8`, `= 28` at `num=16`), the double fold.
* `nestGGM_denote_matches_ggmProg` — the front-compiled node's denote **equals the
  proven `ggmProg` interpreter execution** (`lsemFuelMemLC ggmProg`, the nested
  `loopLinstrRM` back-edges validated in `JasminLsemMemLoopNestDepth`). This ties
  our front node to the proven nested back-edge semantics, transitively.
* `nestGGM_num_sensitive` — `num=8 ↦ 14`, `num=16 ↦ 28` differ, so the inner trip is
  recomputed per outer pass, not a baked-in schedule.
* `nestGGM_lowering_has_two_backedges` — the `comLToBody` lowering emits exactly two
  `Lcond NZ` back-edges at two distinct labels (outer + inner) — real nested
  back-edges, not a flattened single loop.

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/NestedRuntimeLoopFrontValidate.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.NestedRuntimeLoopFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. The two front bodies (covered LowCT) -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- **Inner-count body** — `cnt := num >> (jd + 1)` (the per-outer-recomputed inner
    trip). `jd` is the outer index (`.here`), `num` the runtime invariant. Lowers
    (via `SShr` on a runtime shift amount) to a real variable right-shift
    `bvShiftRV`. -/
def countBody : LowCT :=
  .RScalarSetExpr "cnt" (.SShr (.SVar "num") (.SAdd (.SVar "jd") (.SLit 1)))

/-- **Inner-update body** — `acc[0] := acc[0] + 2` at the constant index `z = 0`
    (the net effect of GGM's constant inner `outlen = 2` loop). Accumulator `acc`
    is a size-1 memref; `z := 0` is the scalar index. Neither the inner index nor
    the outer index is read (the innermost work is index-free `+2`), but both are in
    scope. -/
def updateBody : LowCT := seqAll [
  .RScalarSetExpr "z" (.SLit 0),
  .RArrLoad ⟨"a0", .TU64⟩ ⟨"acc", .TBytes 8⟩ "z",
  .RScalarSetExpr "s" (.SAdd (.SVar "a0") (.SLit 2)),
  .RArrStore ⟨"acc", .TBytes 8⟩ "z" ⟨"s", .TU64⟩ ]

/-! ## 2. Body contexts + VarMaps -/

/-- Inner-count body context: outer index `jd`, invariant `num` (both scalars). -/
def Γcount : Ctx := [.sword 64, .sword 64]

/-- Inner-count VarMap: `jd ↦ .here`, `num ↦ .there .here`. -/
def vmCount : VarMap Γcount :=
  ((VarMap.empty.bind (t := .sword 64) "num").bind (t := .sword 64) "jd")

/-- Inner-update body context: accumulator `acc`, inner index `inner`, outer index
    `outer`, invariant `num`. -/
def Γupd : Ctx := [.memref 1, .sword 64, .sword 64, .sword 64]

/-- Inner-update VarMap: `acc ↦ .here`, `inner ↦ .there .here`,
    `outer ↦ .there² .here`, `num ↦ .there³ .here`. -/
def vmUpd : VarMap Γupd :=
  ((((VarMap.empty.bind (t := .sword 64) "num").bind
      (t := .sword 64) "outer").bind
      (t := .sword 64) "inner").bind (t := .memref 1) "acc")

/-! ## 3. The nested-runtime-loop spine

Outer context `Γouter = [D, acc, num]` (newest-first): `D ↦ .here`,
`acc ↦ .there .here`, `num ↦ .there² .here`. The accumulator is a size-1 stack
array; `num` is the runtime invariant read by the inner-count body. -/

/-- The outer (kernel-argument) jasmin context: `[D, acc, num]`. -/
def Γouter : Ctxt jasminDialect := [.reg 64, .stackArr 64 1, .reg 64]

/-- The front-compiled nested runtime loop: outer `jd < D`, inner
    `idx < num >> (jd+1)` (recomputed per outer pass), innermost `acc[0] += 2`. ONE
    `ComL.forLoopNRtNested` spine, both bodies front-compiled. -/
def nestGGM : Option (ComL Γouter (.stackArr 64 1)) :=
  FrontRoutePlan.compileNested (Γouter := Γouter) (accCTy := .memref 1)
    (invCTys := [.sword 64]) .plain
    vmCount "cnt" countBody
    vmUpd "acc" updateBody
    (outerCount := .here)                       -- D
    (init := .there .here)                      -- acc
    (invs := .cons (.there (.there .here)) .nil) -- num

/-! ## 4. Gates + denote validates -/

/-- Both bodies front-compile and wrap into ONE `forLoopNRtNested`. -/
theorem nestGGM_isSome : nestGGM.isSome := by native_decide

/-- The spine is the nested runtime-loop node. -/
theorem nestGGM_is_nested_node :
    (nestGGM.map (fun c => match c with
      | .forLoopNRtNested _ _ _ _ _ _ => true
      | _ => false))
      = some true := by native_decide

/-- Outer valuation at outer count `D` and runtime invariant `num`: `D`, `acc = 0`,
    `num`. -/
def valAt (D num : Nat) : Ctxt.Valuation Γouter :=
  .cons (BitVec.ofNat 64 D)
    (.cons (fun _ => (0 : BitVec 64)) (.cons (BitVec.ofNat 64 num) .nil))

/-- **denote = `ggmNestedFold 3 8 2 = 14`.** The double fold with the inner trip
    recomputed per outer pass (`8>>1, 8>>2, 8>>3 = 4,2,1`, each `×2`). -/
theorem nestGGM_denote_num8 :
    (nestGGM.map (fun c => (ComL.denote c (valAt 3 8) ⟨0, by decide⟩).toNat))
      = some (ggmNestedFold 3 8 2) := by native_decide

/-- **denote = `ggmNestedFold 3 16 2 = 28`** (SAME program, `num = 16`). -/
theorem nestGGM_denote_num16 :
    (nestGGM.map (fun c => (ComL.denote c (valAt 3 16) ⟨0, by decide⟩).toNat))
      = some (ggmNestedFold 3 16 2) := by native_decide

/-- **The front node's denote EQUALS the proven `ggmProg` interpreter execution.**
    `ggmProg` is the nested `loopLinstrRM` program (real outer/inner back-edges)
    whose `lsemFuelMemLC` execution `JasminLsemMemLoopNestDepth.ggm_depth3_validate`
    pins to `ggmNestedFold 3 8 2`. Our front-compiled `forLoopNRtNested`'s denote
    equals that same interpreter run — tying the front node to the proven nested
    back-edge semantics, transitively (both `= 14`). -/
theorem nestGGM_denote_matches_ggmProg :
    (nestGGM.map (fun (c : ComL Γouter (.stackArr 64 1)) =>
        some (ComL.denote c (valAt 3 8) ⟨0, by decide⟩)))
      = (lsemFuelMemLC (fun _ => none)
            ggmProg 4000 (ggmStart 8)).map
          (fun t => decodeM t.base "acc" 64) := by native_decide

/-- **The inner trip is recomputed per outer pass:** `num=8 ↦ 14`,
    `num=16 ↦ 28` differ, so the inner bound is read from `num >> (jd+1)` each outer
    pass, not a baked-in `4,2,1` schedule. -/
theorem nestGGM_num_sensitive :
    ggmNestedFold 3 8 2 = 14
      ∧ ggmNestedFold 3 16 2 = 28 := by native_decide

/-! ## 5. The lowering has real nested back-edges

`comLToBody` on the nested node emits an inner runtime loop (top label
`curDepth+1`) inside the outer runtime loop (top label `curDepth`). We count the
`Lcond (.reg "NZ") _` back-edges: exactly two, at two distinct labels — a nested
back-edge, not a flattened single loop. -/

/-- Count `Lcond (.reg "NZ") lbl` back-edges in an `Lcmd`, returning their labels. -/
def nzBackEdges (body : Lcmd) : List LLabel :=
  body.filterMap (fun i =>
    match i.li_i with
    | .Lcond (.reg "NZ") lbl => some lbl
    | _ => none)

/-- The `comLToBody` lowering of the nested node has exactly **two** `Lcond NZ`
    back-edges at two **distinct** labels (outer top `3`, inner top `4` — the
    kernel argument count is `3`, so `curDepth = 3` is the outer loop's depth). Real
    nested back-edges. -/
theorem nestGGM_lowering_has_two_backedges :
    (nestGGM.map (fun c =>
        let edges := nzBackEdges (comLToBody 3 argName (fun _ => none) c 3)
        edges.length == 2 && edges.dedup.length == 2))
      = some true := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.NestedRuntimeLoopFrontValidate
