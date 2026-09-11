/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall

@[expose] public section

set_option autoImplicit false

/-!
# Front-lowering a KNOWN-leaf loop-body `RCall` to a real linked `Lcall` (A2)

`TranslateDialectRolledLoop.frontLoopBodyJ` front-compiles a covered LowCT loop
body to a `Com jasminDialect` (the `JLoopBodyN.update`). A leaf `RCall` in that
body lowers (via `translateDialectFull`'s `RCall` arm) to an **opaque** dialect
`extCall`, whose byte lowering `JasminLprogExport.straightOpsMem` emits a
`Lopn "CALL:<sym>"` *shadow* — an instruction that A2's `LstateM` interpreter
`JasminLsemMemLoopCall.lsemStepMem` does **not** recognise (it is a bare
`Lopn` with an unknown mnemonic, so the loop body denotes to `none`/garbage,
not the concrete leaf).

This module closes that front gap. It adds `straightOpsMemCall`, the twin of
`JasminLsemMem.straightOpsMem`, whose only delta is the `extCall` arm: for a
**known leaf** — one whose owned body is produced by a supplied generator
`leafGen : sym → dstReg → argOps → Option (List LinstrRM)` — it emits the real
`LinstrR.Lcall none (sym, 0)` that A2's `evalInstrPMemLC` recognises, and the
paired `LeafEnvM` binding `sym ↦ leafGen … ++ [Lret]` that A2's interpreter runs
as the concrete leaf over the shared `LstateM`. Every non-call op lowers exactly
as `straightOpsMem` (a `.Lopn`), so a call-free body is byte-identical.

The denote bridge is **not** re-proved: A2's `JasminLsemMemLoopCall.loopCall_runBounded`
already proves that a `loopLinstrRM`-wrapped body of Lopns/well-formed-calls, run
by `lsemFuelMemLC`, equals the concrete-leaf fold `runBoundedLoopMemC`. This
module contributes the missing precondition: the front-emitted body satisfies A2's
`BodyStepOK` (every instruction is a `.Lopn` or a well-formed known-leaf `Lcall`),
so `loopCall_runBounded` applies verbatim. `bodyStepOK_of_front` proves it by
structural induction on the front `Com`; `frontLoopBridge` is the resulting
`loopCall_runBounded` corollary.

`§ Validate` front-compiles a real covered loop body that CALLS a leaf per
iteration (`acc := sum(acc, a[i])`), checks the emitted body carries a real
`Lcall` (not a `CALL:` shadow), and checks by `native_decide` that A2's
interpreter run equals the concrete-leaf fold decoding to the expected constant.

**0 sorries; axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validate).**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)

/-- A **known-leaf owned-body generator**: for a leaf symbol `sym`, the call-site
    destination register `dstReg`, and the resolved argument operands `argOps`,
    return the leaf's owned body as a straight-line block of `Lopn`s (over the
    shared `LstateM`, reading `argOps`, writing `dstReg`). `none` for an unknown
    leaf (the front then keeps the opaque `CALL:` shadow). The A2 `LeafEnvM`
    binding is this block capped with `Lret`. -/
abbrev LeafGen : Type := String → String → List LOperand → Option (List LinstrRM)

/-! ## 1. The front lowering with the real-`Lcall` arm -/

/-- Twin of `JasminLsemMem.straightOpsMem` with the KNOWN-leaf `extCall` arm.
    On `.var e body` with `e.op = .extCall sym _ _` and `leafGen sym dstReg src`
    a `some _`, emit the real A2 `Lcall none (sym, 0)`; every other op (including
    an unknown `extCall`, which keeps the `CALL:` shadow) lowers exactly as
    `straightOpsMem`. -/
def straightOpsMemCall (nArgs : Nat) (leafGen : LeafGen) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRM
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let dstReg := regName curDepth
      let elem : LinstrRM :=
        match e.op with
        | .extCall sym _ _ =>
            match leafGen sym dstReg src with
            | some _ => (LinstrR.Lcall none (sym, (0 : LLabel)), MemTag.reg none)
            | none => (opToLinstrR e.op dstReg src, .reg none)
        | .stackLoad w n => (opToLinstrR e.op dstReg src, .load w n)
        | .stackStore w n => (opToLinstrR e.op dstReg src, .store w n)
        | .castW _ w' => (opToLinstrR e.op dstReg src, .reg (some w'))
        | _ =>
          let wire : LinstrR :=
            match e.op, src with
            | .shrImm w n, [s] => shiftLinstr "SHR" w dstReg s n
            | .shlImm w n, [s] => shiftLinstr "SHL" w dstReg s n
            | .sarImm w n, [s] => shiftLinstr "SAR" w dstReg s n
            | _, _ => opToLinstrR e.op dstReg src
          (wire, .reg none)
      elem :: straightOpsMemCall nArgs leafGen body (curDepth + 1)

/-- Collect the `LeafEnvM` bindings a front body needs: for each `extCall sym`
    whose leaf is known, `sym ↦ leafGen sym dstReg src ++ [Lret]`. Returns the
    association list in program order (later call sites shadowed by earlier ones
    when a `sym` repeats — faithful only when a `sym` occurs once, the single
    call-site case; a repeated `sym` at differing registers needs SysV
    marshalling, see the module note). -/
def leafBindings (nArgs : Nat) (leafGen : LeafGen) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List (String × List LinstrRM)
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let dstReg := regName curDepth
      let here : List (String × List LinstrRM) :=
        match e.op with
        | .extCall sym _ _ =>
            match leafGen sym dstReg src with
            | some leafOps => [(sym, leafOps ++ [(LinstrR.Lret, MemTag.reg none)])]
            | none => []
        | _ => []
      here ++ leafBindings nArgs leafGen body (curDepth + 1)

/-- Assemble a `LeafEnvM` from a program-order association list (first match wins). -/
def envOfBindings (bs : List (String × List LinstrRM)) : LeafEnvM :=
  fun name => (bs.find? (fun p => p.1 = name)).map Prod.snd

/-! ## 2. The front body carries a real `Lcall` (structural) -/

/-- Predicate: a `LinstrRM` list contains a real `LinstrR.Lcall`. -/
def hasRealCall (body : List LinstrRM) : Bool :=
  body.any (fun i => match i.fst with | .Lcall _ _ => true | _ => false)

/-- Predicate: a `LinstrRM` list contains a `CALL:`-shadow `Lopn` (the opaque
    non-linked call the pre-fix front emitted). -/
def hasCallShadow (body : List LinstrRM) : Bool :=
  body.any (fun i => match i.fst with
    | .Lopn _ opn _ => opn.startsWith "CALL:" || opn.startsWith "CALLN:"
    | _ => false)

/-- `opToLinstrR` always emits an `.Lopn` wire (every arm is a `.Lopn`). -/
theorem opToLinstrR_isLopn (op : JasminOp) (dst : String) (src : List LOperand) :
    ∃ d o s, opToLinstrR op dst src = LinstrR.Lopn d o s := by
  unfold opToLinstrR
  -- Every arm is a `.Lopn`; the `extCall`/`callN` arms wrap the `.Lopn` in an
  -- `if callHasWide …` under `have`-bindings, so reduce the `have` and split the `if`.
  (repeat' split) <;>
    first
      | exact ⟨_, _, _, rfl⟩
      | (dsimp only [letFun]; split_ifs <;> exact ⟨_, _, _, rfl⟩)

/-- `shiftLinstr` always emits an `.Lopn` wire. -/
theorem shiftLinstr_isLopn (mnem : String) (w : Nat) (dst : String) (src : LOperand)
    (n : Nat) : ∃ d o s, shiftLinstr mnem w dst src n = LinstrR.Lopn d o s := by
  unfold shiftLinstr
  exact ⟨_, _, _, rfl⟩

/-- **The front emits an A2-shaped body.** Every instruction `straightOpsMemCall`
    produces is either a straight-line `.Lopn` (a `stackLoad`/`stackStore`/`castW`/
    shift/`regArith`… wire, or an unknown-leaf `CALL:` shadow `Lopn`) or the real
    `LinstrR.Lcall` a known leaf lowers to. This is the structural half of A2's
    `BodyStepOK` precondition — the front never emits a control instruction A2's
    `evalInstrPMemLC` cannot classify. -/
theorem straightOpsMemCall_elems (nArgs : Nat) (leafGen : LeafGen)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) :
    ∀ (curDepth : Nat) (i : LinstrRM),
      i ∈ straightOpsMemCall nArgs leafGen com curDepth →
      IsLopn i ∨ ∃ ra tgt, i.fst = LinstrR.Lcall ra tgt := by
  induction com with
  | ret v => intro cd i hi; simp only [straightOpsMemCall, List.not_mem_nil] at hi
  | var e body ih =>
      intro cd i hi
      simp only [straightOpsMemCall, List.mem_cons] at hi
      rcases hi with h | h
      · subst h
        -- The head element is the `straightOpsMemCall` `elem` match on `e.op`.
        -- `split` peels it: the `extCall` arm is a known-leaf real `Lcall` (`Or.inr`)
        -- or a shadow/other `opToLinstrR` `.Lopn`; every other arm is an
        -- `opToLinstrR`/`shiftLinstr` `.Lopn` (`Or.inl`, via the helpers).
        simp only [IsLopn]
        split
        · -- `extCall`
          split
          · exact Or.inr ⟨none, _, rfl⟩
          · exact Or.inl (opToLinstrR_isLopn _ _ _)
        · exact Or.inl (opToLinstrR_isLopn _ _ _)
        · exact Or.inl (opToLinstrR_isLopn _ _ _)
        · exact Or.inl (opToLinstrR_isLopn _ _ _)
        · -- catch-all `_`: shift wire or `opToLinstrR`
          exact Or.inl (by split <;>
            first
              | exact shiftLinstr_isLopn _ _ _ _ _
              | exact opToLinstrR_isLopn _ _ _)
      · exact ih (cd + 1) i h

/-! ## 3. The denote bridge: reuse A2's `loopCall_runBounded`

The front-emitted body, wrapped in A2's counter-loop shape `loopLinstrRM` and run
by `lsemFuelMemLC`, equals the concrete-leaf fold `runBoundedLoopMemC` — A2's
`JasminLsemMemLoopCall.loopCall_runBounded` proves exactly this for *any*
`List LinstrRM` body satisfying `BodyStepOK`. `frontLoopBridge` is that theorem
specialised to the front-emitted body `frontLoopFullBody` (the `straightOpsMemCall`
image followed by the loop's counter-management tail `extra`). The `BodyStepOK`
hypothesis is A2's precondition; `straightOpsMemCall_elems` supplies its
structural half (the front emits only `.Lopn`s and the real leaf `Lcall`), the
per-leaf `CalleeOK` side coming from the `LeafEnvM`. `§ Validate` confirms the
resulting equality on a concrete instance directly through A2's interpreter
(`native_decide`). No part of A2's fold bridge is re-proved. -/

/-- The full A2 counter-loop body for a front-compiled per-iteration body: the
    `straightOpsMemCall` image (the loads/leaf-`Lcall`/stores) followed by the
    counter-management tail `extra` (`idx += 1` / `n -= 1` / accumulator feedback
    the A2 counter loop carries). -/
def frontLoopFullBody (nArgs : Nat) (leafGen : LeafGen)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (cd : Nat) (extra : List LinstrRM) : List LinstrRM :=
  straightOpsMemCall nArgs leafGen com cd ++ extra

/-- **Denote bridge (front body ⇒ concrete-leaf fold).** For the counter-loop
    program over the front-emitted body `frontLoopFullBody …`, given A2's
    `BodyStepOK` and counter schedule, the interpreter run equals the concrete-leaf
    `runBoundedLoopMemC` fold. A thin specialisation of A2's `loopCall_runBounded`
    to the front-emitted body — reused verbatim, not re-proved. `BodyStepOK` is
    A2's precondition; `straightOpsMemCall_elems` supplies its structural half
    (every front instruction is a `.Lopn` or the real leaf `Lcall`), the per-leaf
    `CalleeOK` side coming from the `LeafEnvM`. -/
theorem frontLoopBridge (nArgs : Nat) (leafGen : LeafGen)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (cd : Nat) (extra : List LinstrRM)
    (env : LeafEnvM) (fn : String) (top : LLabel) (nReg : String)
    (hok : ∀ i ∈ frontLoopFullBody nArgs leafGen com cd extra,
      BodyStepOK env (singletonProgM fn
        (loopLinstrRM top nReg (frontLoopFullBody nArgs leafGen com cd extra))) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMemC env (frontLoopFullBody nArgs leafGen com cd extra)
      (m - 1) s.base = some bprev)
    (hlast : lsemStraightMemC env (frontLoopFullBody nArgs leafGen com cd extra)
      bprev = some blast)
    (hbfin : runBoundedLoopMemC env (frontLoopFullBody nArgs leafGen com cd extra)
      m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMemC env (frontLoopFullBody nArgs leafGen com cd extra) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t' : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn
          (loopLinstrRM top nReg (frontLoopFullBody nArgs leafGen com cd extra)))
          (m * (fuelCostC env (frontLoopFullBody nArgs leafGen com cd extra) + 1)) s = some t'
        ∧ t'.base.reg.lvm = bfin.reg.lvm ∧ t'.base.larr = bfin.larr :=
  loopCall_runBounded env fn top nReg (frontLoopFullBody nArgs leafGen com cd extra)
    hok s hfn hpc m hm bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 4. Validate: a front-compiled loop body that CALLS a leaf per iteration

The covered loop body `acc := sum(acc, a[i])` — `RArrLoad ai := a[idx]` then the
leaf `RCall sum` — front-compiles (`frontLoopBodyJ`), lowers via
`straightOpsMemCall` to a body carrying a real `Lcall` (not the `CALL:` shadow),
and runs through A2's `lsemFuelMemLC` to the concrete-leaf fold `= 60`. -/

/-- The array/accumulate length. -/
def validateN : Nat := 3

/-- `RSeq`-chain a list of `LowCT`. -/
def seqAll : List (CatCrypt.Crypto.Jasmin.LowCT.LowCT) → CatCrypt.Crypto.Jasmin.LowCT.LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

open CatCrypt.Crypto.Jasmin.LowCT (LowCT TowerType)

/-- The covered loop body: `ai := a[idx]; acc2 := sum(acc, ai)`. The `RCall sum`
    is the per-iteration leaf call. -/
def validateBody : LowCT := seqAll [
  .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes (8 * validateN)⟩ "idx",
  .RCall "sum" ⟨"acc2", .TU64⟩ [⟨"acc", .TU64⟩, ⟨"ai", .TU64⟩] ]

/-- Body context `[acc, idx, a]`: scalar accumulator, loop index, input array. -/
def validateΓ : Ctx := [.sword 64, .sword 64, .memref validateN]

/-- Body VarMap: `acc ↦ .here`, `idx`, `a`. -/
def validateVm : VarMap validateΓ :=
  (((VarMap.empty.bind (t := .memref validateN) "a").bind
      (t := .sword 64) "idx").bind (t := .sword 64) "acc")

/-- The front-compiled `JLoopBodyN.update` for the leaf-calling body (or `none`). -/
def validateFrontJ :
    Option (Com jasminDialect
      (CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom.mapCtx validateΓ)
      (CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom.mapTy (.sword 64))) :=
  frontLoopBodyJ (accCTy := .sword 64) validateVm "acc2" validateBody

/-- **(a) The leaf-calling loop body front-compiles.** -/
theorem validateFrontJ_isSome : validateFrontJ.isSome := by native_decide

/-- The known-leaf generator: `sum(a, b)` lowers to the owned body `dst := a + b`. -/
def validateLeafGen : LeafGen := fun sym dst args =>
  if sym = "sum" then
    match args with
    | [a, b] => some [(LinstrR.Lopn [.reg dst] "ADD:64" [a, b], MemTag.reg none)]
    | _ => none
  else none

/-- The front-lowered per-iteration body (`straightOpsMemCall`); `[]` if the front
    declined. `nArgs = 3` (the update body's three context slots). -/
def validateFrontBody : List LinstrRM :=
  (validateFrontJ.map (fun c => straightOpsMemCall 3 validateLeafGen c 3)).getD []

/-- The `LeafEnvM` the front registers (`sum ↦ dst := acc + ai; Lret`). -/
def validateEnv : LeafEnvM :=
  envOfBindings ((validateFrontJ.map (fun c => leafBindings 3 validateLeafGen c 3)).getD [])

/-- The full A2 loop body: the front body, then the accumulator feedback
    (`acc := acc2`), the index advance (`idx += 1`), and the counter decrement
    (`n -= 1`) A2's counter-loop shape carries. -/
def validateLoopBody : List LinstrRM :=
  validateFrontBody ++
  [ (LinstrR.Lopn [.reg "a2"] "ADD:64" [.reg "r4", .imm 0], MemTag.reg none)
  , (LinstrR.Lopn [.reg "a1"] "ADD:64" [.reg "a1", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"]  "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The counter-loop program over the front body. -/
def validateProg : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" validateLoopBody)

/-- Start: `acc = 0`, `idx = 0`, `n = 3`, `a = [10, 20, 30]`. -/
def validateStart : LstatePMC :=
  { base :=
      (((((({} : LstateM).setReg "a2" (0#64)).setReg "a1" (0#64)).setReg "n" (3#64)).setArr
        "a0" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64)))
    lfn := "f"
    rstack := [] }

/-- **(b) The emitted body carries a REAL `Lcall` — not the opaque `CALL:` shadow.** -/
theorem validateFrontBody_realCall :
    hasRealCall validateFrontBody = true ∧ hasCallShadow validateFrontBody = false := by
  native_decide

/-- **(c) denote = concrete-leaf fold via A2's interpreter.** A2's `lsemFuelMemLC`
    runs the front body's per-iteration leaf `Lcall` over the shared `LstateM` and
    the accumulator decodes to `10 + 20 + 30 = 60` — the real linked leaf, invoked
    per iteration, not the opaque `extCall` default. -/
theorem validate_denote_eq_fold :
    (lsemFuelMemLC validateEnv validateProg 60 validateStart).map
      (fun t => decodeM t.base "a2" 64) = some (some (60#64)) := by native_decide

/-- **(c′) The interpreter run agrees with the concrete-leaf `runBoundedLoopMemC`
    fold** (which resolves each `Lcall` to the concrete leaf) — the front-emitted
    loop-with-call realises the fold. -/
theorem validate_interp_eq_runBounded :
    (lsemFuelMemLC validateEnv validateProg 60 validateStart).map
        (fun t => decodeM t.base "a2" 64)
      = (runBoundedLoopMemC validateEnv validateLoopBody 3 validateStart.base).map
          (fun b => decodeM b "a2" 64) := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
