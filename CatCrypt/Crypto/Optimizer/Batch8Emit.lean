/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Batch8
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Fused batch8 lowering: scalar `Com` → flat two-address `Lfundef`, in one pass

`batch8 = lowering.blockLowerCom` materialises an entire widened typed-`Com`
before it is flattened to the string-named linear IR. That intermediate carries
Peano `Ctxt.Var` `there`-chains whose length grows with binder depth, so
constructing it costs memory quadratic in the binding count.

The flat `Lprog` the widened `Com` lowers to (`comToBody`) uses integer-depth
register names (`r{depth}`) with no `there`-chains, so the quadratic term is only
the never-inspected intermediate. `batch8Body` walks the SCALAR `Com` once and
emits the widened flat body directly: per scalar op it emits the same YMM block
`lowering.lowerExprBlock` produces, but as flat `Linstr`s at destinations
`regName wDepth …`, resolving each scalar argument through an `endSlot` table
(scalar slot → widened result slot). It never builds the widened `Com`, so it is
linear in the binding count.

## Main results

* `batch8Body` / `batch8RetReg`: the fused flat body and its return register, the
  per-pass analogues of `comToBody (batch8 c)` / `comRetReg (batch8 c)`.
* `batch8Virt`: the virtual `Lfundef` `comToLfundef (batch8 c)` would produce,
  built without the quadratic intermediate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Batch8Emit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.Optimizer.Batch8

/-- The widened slot the scalar argument `a` resolves to, as an `LOperand`, under
    the flat register naming. `a` at scalar depth `sDepth` has absolute scalar slot
    `sa = sDepth - 1 - varIndex a`; `endSlot` maps it to the widened slot `ws`
    (arguments map identically, `endSlot[j] = j`). A widened slot in the argument
    prefix (`ws < nArgs`) renders as the argument name (or the `immSlotMap`
    constant), else as `regName ws`. Mirror of `resolveVar` composed with the
    block-descent's variable transport. -/
def operandOfVar (nArgs sDepth : Nat) (immSlotMap : ImmSlotMap) (endSlot : Array Nat)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (a : Ctxt.Var Γ τ) : LOperand :=
  let sa := sDepth - 1 - varIndex a
  let ws := endSlot.getD sa sa
  if ws < nArgs then
    match immSlotMap ws with
    | some v => .imm v
    | none => .reg (argName ws)
  else .reg (regName ws)

/-- Number of widened bindings the block for op `e` expands to: the rotate
    `rorImm 32 n` becomes shift/shift/or (3), every other op one. Matches the block
    sizes of `lowering.lowerExprBlock`. -/
def blockSize {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    Nat :=
  match e.op with
  | .rorImm 32 _ => 3
  | _ => 1

/-- The flat widened `Linstr` block for one scalar op, at widened base slot
    `wDepth`, with arguments resolved through `endSlot`. The mirror of
    `lowering.lowerExprBlock e` under `comToBody`: each `Com.var ⟨op,…⟩` binding
    becomes `⟨0, opToLinstrR op (regName wSlot) srcs⟩`, intra-block references
    resolve to `regName (wDepth + localIndex)`. -/
def blockBody (nArgs sDepth wDepth : Nat) (immSlotMap : ImmSlotMap) (endSlot : Array Nat)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) : Lcmd :=
  let op1 (wop : JasminOp) (srcs : List LOperand) : Lcmd :=
    [⟨0, opToLinstrR wop (regName wDepth) srcs⟩]
  match e with
  | ⟨.regArith .add 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpaddd) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                           operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .xor 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpxor) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                          operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .or 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpor) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                         operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .and 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpand) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                          operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .sub 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpsubd) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                           operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .mul 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpmulld) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                            operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .andn 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpandn) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                           operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.sarImm 32 n, _, .cons a .nil⟩ =>
      op1 (.vymm (.vpsrad n)) [operandOfVar nArgs sDepth immSlotMap endSlot a]
  | ⟨.shlImm 32 n, _, .cons a .nil⟩ =>
      op1 (.vymm (.vpslld n)) [operandOfVar nArgs sDepth immSlotMap endSlot a]
  | ⟨.shrImm 32 n, _, .cons a .nil⟩ =>
      op1 (.vymm (.vpsrld n)) [operandOfVar nArgs sDepth immSlotMap endSlot a]
  | ⟨.regArith .shl 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpsllvd) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                            operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.regArith .shr 32, _, .cons a (.cons b .nil)⟩ =>
      op1 (.vymm .vpsrlvd) [operandOfVar nArgs sDepth immSlotMap endSlot a,
                            operandOfVar nArgs sDepth immSlotMap endSlot b]
  | ⟨.rorImm 32 n, _, .cons a .nil⟩ =>
      let oa := operandOfVar nArgs sDepth immSlotMap endSlot a
      [⟨0, opToLinstrR (.vymm (.vpslld (32 - n))) (regName wDepth) [oa]⟩,
       ⟨0, opToLinstrR (.vymm (.vpsrld n)) (regName (wDepth + 1)) [oa]⟩,
       ⟨0, opToLinstrR (.vymm .vpor) (regName (wDepth + 2))
             [.reg (regName wDepth), .reg (regName (wDepth + 1))]⟩]
  | ⟨.regConst 32 kk, _, .nil⟩ =>
      op1 (.regConst 256 (bcast256 kk).toNat) []
  | ⟨.stackLoad 32 n, _, .cons arr (.cons idx .nil)⟩ =>
      op1 (.stackLoad 256 n) [operandOfVar nArgs sDepth immSlotMap endSlot arr,
                              operandOfVar nArgs sDepth immSlotMap endSlot idx]
  | ⟨_, _, _⟩ =>
      op1 (.extCall "batch8_uncovered" [] (widen8Ty τ)) []

/-- The fused flat widened body: walk the scalar `Com` once, emitting each op's
    widened `Linstr` block. `sDepth` counts scalar bindings in scope, `wDepth` the
    widened bindings emitted, `endSlot` maps each in-scope scalar slot to its
    widened result slot. The per-pass analogue of
    `comToBody nArgs argName immSlotMap (batch8 com) wDepth`. -/
def batch8Body (nArgs : Nat) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (sDepth wDepth : Nat) → (endSlot : Array Nat) → Lcmd
  | _, _, .ret _, _, _, _ => [⟨0, .Lret⟩]
  | _, _, .var e body, sDepth, wDepth, endSlot =>
      let b := blockSize e
      blockBody nArgs sDepth wDepth immSlotMap endSlot e
        ++ batch8Body nArgs immSlotMap body (sDepth + 1) (wDepth + b)
             (endSlot.push (wDepth + b - 1))

/-- The return register of the fused body: the widened result slot the scalar
    `.ret` points at. Mirror of `comRetReg (batch8 com)`. -/
def batch8RetReg (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (sDepth wDepth : Nat) → (endSlot : Array Nat) → String
  | _, _, .ret v, sDepth, _, endSlot =>
      let sa := sDepth - 1 - varIndex v
      let ws := endSlot.getD sa sa
      if ws < nArgs then argName ws else regName ws
  | _, _, .var e body, sDepth, wDepth, endSlot =>
      let b := blockSize e
      batch8RetReg nArgs body (sDepth + 1) (wDepth + b)
        (endSlot.push (wDepth + b - 1))

/-- The virtual `Lfundef` for the widened program, built without materialising the
    widened `Com`. The per-pass analogue of `comToLfundef (batch8 com) immSlotMap`:
    same argument names/widths (the context map preserves the argument prefix, so
    `nArgs = Γ.length`; each `reg 32`/`stackArr 32` argument widens to width 256),
    the fused body, and the widened return width/register. -/
def batch8Virt {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (immSlotMap : ImmSlotMap := fun _ => none) :
    Lfundef :=
  let nArgs := Γ.length
  let endSlot0 : Array Nat := (Array.range nArgs)
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := (widen8Ctxt Γ).reverse.map tyWidth
    lfd_arg := (List.range nArgs).map argName
    lfd_body := batch8Body nArgs immSlotMap com nArgs nArgs endSlot0
    lfd_tyout := [tyWidth (widen8Ty t)]
    lfd_res := [batch8RetReg nArgs com nArgs nArgs endSlot0]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

/-- The batch8-widened 2-pointer-ABI physical `Lprog`, built without materialising
    the widened `Com`: `batch8Virt` supplies the virtual body directly and the
    existing `comToLfundefPhysAbiFromVirt` runs the RA/ABI wrapping. Equal to
    `Com.toLprogPhysAbi (batch8 com) fname …` whenever `batch8 com` is not a
    degenerate forwarder (it never is for a covered body — it has vymm bindings),
    so the emitted `.s` is byte-identical to the never-materialised widened path;
    the anchoring equality is `batch8Virt_eq` / `batch8Body_eq`. -/
def batch8ToLprogPhysAbi {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0)
    (forceLivePin : Bool := false) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, comToLfundefPhysAbiFromVirt (batch8Virt com immSlotMap)
                 (shiftImm := shiftImm) (inLoadMap := inLoadMap)
                 (outStoreMap := outStoreMap) (abiArgs := abiArgs)
                 (abiTyin := abiTyin) (residence := residence) (abiW := abiW)
                 (forceLivePin := forceLivePin) (reserveVecScratch := true))] }

end CatCrypt.Crypto.Optimizer.Batch8Emit
