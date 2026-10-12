/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripCmp
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

@[expose] public section

set_option autoImplicit false

/-!
# The exported array-accumulator loop against the model loop

The model counter loop runs `loopBodyArrFullMN update nReg`
(`straightOpsMem (nInv+2) update (nInv+2) ++ loopArrWritebackMN update nReg`),
whose names are the trip-context arguments `argName j` and the chain registers
`regName k`. The export `forLoopLcmdNRt`, lifted to the typed program
`forLoopLcmdNRtRM` (`JasminLsemExportLift`), emits the body walk with the
accumulator register, the index `Lidx<d>`, the invariant base registers and the
body temporaries `L<d>_r<k>`. This module states the relation between the two on
the flag machine `lsemFuelMemF`.

## The chain is a renaming

`loopBodyWalkNM_eq_ren`: for an update whose ops lie in the stack-memory fragment
and contain no immediate shift, the typed body walk is the model chain under an
operand renaming `σ` with `σ (argName (nInv+1)) = acc`, `σ (argName nInv) =
Lidx<d>`, `σ (argName j)` the `j`-th invariant base register for `j < nInv`, and
`σ (regName k) = L<d>_r<k>` (`LoopRen`), instruction for instruction and
descriptor for descriptor.

## The two differences

* **Immediate shifts.** The model chain emits a `shrImm`/`shlImm`/`sarImm` binding
  as the structured `Lopn [dst] "SHR[:64]" [src, #k]`; the body walk emits the
  count-in-mnemonic form `Lopn [dst] "SHR:k[:64]" [src]` (`immShift_wire_ne`).
  The two wires step the flag machine to the same state
  (`fstepF_immShiftWire_eq`), so the body walk is the expansion image
  `immShiftExpand` of the renamed model chain (`loopBodyWalkNM_eq_expand`).
  `expProg_immShiftExpand` is the `JasminLsemExportLower.ExpProg` certificate at
  that expansion, and `lsemFuelMemF_immShiftExpand` the resulting run
  correspondence, whose fuel bound is the source fuel because every instruction
  expands to one instruction.
* **The accumulator writeback.** The model writeback copies the return array into
  the accumulator slot with a `LOADIDX`/`STOREIDX` pair. The export writes back
  with the register copy `MOV acc, ret`, which leaves the array carrier unchanged
  (`fstepF_movReg_larr`). No instruction of the exported node stores to the
  accumulator's name, so every halting flag-machine run of the node ends with the
  accumulator's array at its entry value (`forLoopLcmdNRtRM_acc_frozen`,
  `forLoopLcmdNRtRM_regName_acc_frozen`).

## The compare kernel

`cmp_flag_machine_val` runs the model body of the front-compiled `mpn_cmp` limb
inside the export's guarded flag skeleton with the export's trip counter
`Lctr<d>`, and concludes that the output array's cell `0` holds `cmpSign` of the
two operands' `bignumVal`, with no schedule hypothesis. The compare update
contains immediate shifts (`SHL:0:64`, `SHR:63:64`), so the chain equation does
not cover it.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift

/-! ## 1. Operand renaming -/

/-- Rename the register names of an operand (a plain register, and the base and
    index of a SIB element). Immediates and compile-time elements are unchanged. -/
def renOperand (σ : String → String) : LOperand → LOperand
  | .reg r => .reg (σ r)
  | .arrIdx b i s => .arrIdx (σ b) (σ i) s
  | o => o

/-- Rename the operands of an `Lopn`; every other instruction is unchanged. -/
def renLinstrR (σ : String → String) : LinstrR → LinstrR
  | .Lopn d o s => .Lopn (d.map (renOperand σ)) o (s.map (renOperand σ))
  | i => i

/-- Rename a typed instruction's wire, keeping its descriptor. -/
def renRM (σ : String → String) (i : LinstrRM) : LinstrRM := (renLinstrR σ i.1, i.2)

/-- On the fragment's op set, renaming commutes with `opToLinstrR`. -/
theorem renLinstrR_opToLinstrR (σ : String → String) (op : JasminOp) (hop : OpPlain op)
    (dst : String) (srcs : List LOperand) :
    renLinstrR σ (opToLinstrR op dst srcs)
      = opToLinstrR op (σ dst) (srcs.map (renOperand σ)) := by
  cases op <;> simp only [OpPlain] at hop
  all_goals first
    | (simp only [opToLinstrR, renLinstrR, List.map_cons, List.map_nil, renOperand]; done)
    | (simp only [opToLinstrR]
       rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
         (try cases a) <;> (try cases b) <;>
         simp [renLinstrR, renOperand]
       done)
    | (simp only [opToLinstrR]
       split <;>
       rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, rest⟩⟩⟩⟩ <;>
         (try cases a) <;> (try cases b) <;>
         simp [renLinstrR, renOperand])

/-! ## 2. Variable resolution under the renaming -/

/-- The renaming hypotheses tying the model's trip-context names to the export's
    loop-node names, at invariant count `nInv`. -/
structure LoopRen (σ : String → String) (d nInv : Nat) (accReg : String)
    (invRegs : List String) : Prop where
  /-- The accumulator argument renames to the accumulator register. -/
  acc : σ (argName (nInv + 1)) = accReg
  /-- The index argument renames to the loop index register. -/
  idx : σ (argName nInv) = loopIdx d
  /-- Each invariant argument renames to its base register. -/
  inv : ∀ j, j < nInv →
    σ (argName j) = invRegs.getD (nInv - 1 - j) ("Linv" ++ toString d ++ "_" ++ toString j)
  /-- Each chain register renames to the body temporary of the same slot. -/
  reg : ∀ k, σ (regName k) = loopReg d k
  /-- The invariant base registers are one per invariant. -/
  len : invRegs.length = nInv

/-- **Resolution commutes with the renaming.** The body walk resolves a variable
    to the renaming of the model's resolution. -/
theorem loopResolveVarN_eq_ren {σ : String → String} {d nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs) (curDepth : Nat)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    loopResolveVarN d accReg (loopIdx d) invRegs curDepth (fun _ => none) v
      = renOperand σ (resolveVar curDepth (nInv + 2) argName (fun _ => none) v) := by
  unfold loopResolveVarN resolveVar
  dsimp only
  rw [hσ.len]
  generalize curDepth - 1 - varIndex v = slot
  by_cases h1 : slot = nInv + 1
  · simp [h1, renOperand, hσ.acc]
  · by_cases h2 : slot = nInv
    · simp [h2, renOperand, hσ.idx]
    · by_cases h3 : slot < nInv
      · simp [h1, h2, h3, show slot < nInv + 2 by omega, renOperand, hσ.inv slot h3]
      · simp [h1, h2, h3, show ¬ slot < nInv + 2 by omega, renOperand, hσ.reg]

/-- The operand-list walk of the body resolves every variable of a vector to the
    renaming of the model's resolution. -/
theorem loopExprArgsN_go_eq_ren {σ : String → String} {d nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs) (curDepth : Nat)
    {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      loopExprArgsN.go d accReg (loopIdx d) invRegs curDepth (fun _ => none) hv
        = (exprArgs.go curDepth (nInv + 2) argName (fun _ => none) hv).map
            (renOperand σ)
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show loopResolveVarN d accReg (loopIdx d) invRegs curDepth (fun _ => none) v
          :: loopExprArgsN.go d accReg (loopIdx d) invRegs curDepth (fun _ => none) rest
        = (resolveVar curDepth (nInv + 2) argName (fun _ => none) v
          :: exprArgs.go curDepth (nInv + 2) argName (fun _ => none) rest).map (renOperand σ)
      rw [List.map_cons, loopResolveVarN_eq_ren hσ curDepth v,
        loopExprArgsN_go_eq_ren hσ curDepth rest]

/-- The body walk's operand list is the renaming of the model's. -/
theorem loopExprArgsN_eq_ren {σ : String → String} {d nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs) (curDepth : Nat)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    loopExprArgsN d accReg (loopIdx d) invRegs curDepth (fun _ => none) e
      = (exprArgs curDepth (nInv + 2) argName (fun _ => none) e).map (renOperand σ) := by
  unfold loopExprArgsN exprArgs
  exact loopExprArgsN_go_eq_ren hσ curDepth e.args

/-! ## 3. The chain equation -/

/-- An op is not an immediate shift. -/
def NotImmShift : JasminOp → Prop
  | .shrImm _ _ | .shlImm _ _ | .sarImm _ _ => False
  | _ => True

/-- Every binding of a `Com` has an op in the fragment's op set that is not an
    immediate shift. -/
def ComRenOK : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => OpPlain e.op ∧ NotImmShift e.op ∧ ComRenOK body

/-- **The chain equation.** For an update whose ops lie in the fragment's op set
    and contain no immediate shift, the typed body walk of the export is the
    model chain `straightOpsMem` under the loop renaming `σ`: the same
    instructions up to register names, the same descriptors. -/
theorem loopBodyWalkNM_eq_ren {σ : String → String} {d nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hcom : ComRenOK com) (curDepth : Nat) :
    loopBodyWalkNM d accReg (loopIdx d) invRegs (fun _ => none) com curDepth
      = (straightOpsMem (nInv + 2) com curDepth).map (renRM σ) := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      obtain ⟨hop, hns, hbody⟩ := hcom
      simp only [loopBodyWalkNM, straightOpsMem, List.map_cons, ih hbody]
      congr 1
      rw [loopExprArgsN_eq_ren hσ, ← hσ.reg curDepth]
      split
      · next w n h =>
          rw [h] at hop; simp [h, renRM, renLinstrR_opToLinstrR σ _ hop, memTagOfOp]
      · next w n h =>
          rw [h] at hop; simp [h, renRM, renLinstrR_opToLinstrR σ _ hop, memTagOfOp]
      · next w w' h =>
          rw [h] at hop; simp [h, renRM, renLinstrR_opToLinstrR σ _ hop, memTagOfOp]
      · next w n h =>
          rw [h] at hop; simp [h, renRM, renLinstrR_opToLinstrR σ _ hop, memTagOfOp]
      · split
        · next h _ => rw [h] at hns; exact absurd hns id
        · next h _ => rw [h] at hns; exact absurd hns id
        · next h _ => rw [h] at hns; exact absurd hns id
        · simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          congr 1
          unfold memTagOfOp
          split <;> simp_all

/-! ## 4. First difference: the immediate-shift wire -/

/-- The model chain emits an immediate shift as the structured two-source
    instruction `shiftLinstr`; the body walk emits `opToLinstrR`'s one-source
    count-in-mnemonic form. The two wires differ in their source lists. -/
theorem immShift_wire_ne (mnem : String) (w k : Nat) (dst : String) (s : LOperand) :
    JasminLsemShift.shiftLinstr mnem w dst s k
      ≠ LinstrR.Lopn [.reg dst] (withWidthTag w (mnem ++ ":" ++ toString k)) [s] := by
  intro h
  unfold JasminLsemShift.shiftLinstr at h
  injection h with _ _ h3
  simp at h3

/-- A count-in-mnemonic immediate shift strips to neither `NEG` nor `MOV`. -/
theorem stripWidthTag_immShift (m : String) (hm : m = "SHR:" ∨ m = "SHL:" ∨ m = "SAR:")
    (w k : Nat) :
    stripWidthTag (withWidthTag w (m ++ toString k)) ≠ "NEG"
      ∧ stripWidthTag (withWidthTag w (m ++ toString k)) ≠ "MOV" := by
  have hhead : (m ++ toString k).toList.head? = some 'S' := by
    rw [String.toList_append]
    rcases hm with rfl | rfl | rfl <;> rfl
  have hne : (m ++ toString k).toList ≠ [] := by
    intro h; rw [h] at hhead; simp at hhead
  have hw : (withWidthTag w (m ++ toString k)).toList.head? = some 'S' := by
    rw [head?_withWidthTag w _ hne, hhead]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := head?_of_stripWidthTag_eq _ "NEG" (by decide) h
    rw [hw] at this
    exact absurd this (by decide)
  · have := head?_of_stripWidthTag_eq _ "MOV" (by decide) h
    rw [hw] at this
    exact absurd this (by decide)

/-- The count-in-mnemonic wire of an immediate shift, reduced to the base step
    `lsemStepN` over the register half. -/
theorem fstepF_immShiftWire (m : String) (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w k : Nat) (dst a : String) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg dst] (withWidthTag w (m ++ ":" ++ toString k)) [.reg a],
        MemTag.reg none) s zf
      = (lsemStepN (.Lopn [.reg dst] (withWidthTag w (m ++ ":" ++ toString k)) [.reg a])
          s.reg).map (fun r => ({ s with reg := r }, zf)) := by
  obtain ⟨h1, h2⟩ := withWidthTag_plain_of_head w (m ++ ":" ++ toString k) 'S'
    (by rw [String.toList_append, String.toList_append]
        rcases hm with rfl | rfl | rfl <;> rfl) (by decide) (by decide)
  have h3 : copyQ (withWidthTag w (m ++ ":" ++ toString k)) = false := by
    rcases hm with rfl | rfl | rfl <;>
      exact copyQ_withWidthTag w (by rw [String.toList_append, String.toList_append]; rfl)
        (by decide)
  obtain ⟨_, hc, hmv⟩ := lopn_plain [LOperand.reg dst]
    (withWidthTag w (m ++ ":" ++ toString k)) [LOperand.reg a] (.reg none) h1 h2 h3
  unfold fstepF
  rw [hc, hmv]
  simp only []
  rw [stepMemF_of_quiet rfl rfl rfl]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
    lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ rfl]
  simp only [Option.map_map]
  cases lsemStepN (.Lopn [.reg dst] (withWidthTag w (m ++ ":" ++ toString k)) [.reg a]) s.reg <;>
    rfl

/-! ### The expansion carrying the model chain to the body walk -/

/-- Under the trivial immediate-slot map, every operand a variable vector
    resolves to is a register. -/
theorem exprArgs_go_isReg {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys)
      (o : LOperand), o ∈ exprArgs.go curDepth nArgs argName (fun _ => none) hv →
      ∃ r, o = .reg r
  | [], .nil => by
      intro o ho
      rw [show exprArgs.go curDepth nArgs argName (fun _ => none)
          (HVector.nil (f := fun ty => Ctxt.Var Γ ty)) = ([] : List LOperand) from rfl] at ho
      simp at ho
  | _ :: _, .cons v rest => by
      intro o ho
      have hgo : exprArgs.go curDepth nArgs argName (fun _ => none) (HVector.cons v rest)
          = resolveVar curDepth nArgs argName (fun _ => none) v
            :: exprArgs.go curDepth nArgs argName (fun _ => none) rest := rfl
      rw [hgo, List.mem_cons] at ho
      rcases ho with rfl | ho
      · exact ⟨_, resolveVar_isReg v⟩
      · exact exprArgs_go_isReg rest o ho

/-- Under the trivial immediate-slot map, every source operand of a model
    binding is a register. -/
theorem exprArgs_isReg {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) :
    ∀ o ∈ exprArgs curDepth nArgs argName (fun _ => none) e, ∃ r, o = .reg r :=
  fun o ho => exprArgs_go_isReg e.args o ho

/-- The three structured shift bases. -/
def isShiftBase (m : String) : Bool := m == "SHR" || m == "SHL" || m == "SAR"

/-- The count-in-mnemonic rendering of a structured shift mnemonic at count `n`,
    keeping the width tag of the structured form. -/
def shiftCountMnem (opn : String) (n : Nat) : String :=
  if hasSuffix opn ":64" then withWidthTag 64 (stripWidthTag opn ++ ":" ++ toString n)
  else opn ++ ":" ++ toString n

/-- `shiftCountMnem` of a width-tagged shift base is the width-tagged
    count-in-mnemonic rendering of the same base. -/
theorem shiftCountMnem_withWidthTag {m : String}
    (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR") (w n : Nat) :
    shiftCountMnem (withWidthTag w m) n = withWidthTag w (m ++ ":" ++ toString n) := by
  unfold shiftCountMnem
  by_cases hw : w = 64
  · subst hw
    have h64 : withWidthTag 64 m = m ++ ":64" := rfl
    rw [h64, if_pos (JasminImmShiftMnem.hasSuffix_append m ":64"),
      JasminImmShiftMnem.stripWidthTag_append64]
  · have hnt : ∀ s : String, withWidthTag w s = s := by
      intro s; simp only [withWidthTag, if_neg hw]
    rw [hnt, hnt, if_neg (by rcases hm with rfl | rfl | rfl <;> decide)]

/-- `isShiftBase` accepts the stripped width-tagged shift bases. -/
theorem isShiftBase_stripWidthTag {m : String}
    (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR") (w : Nat) :
    isShiftBase (stripWidthTag (withWidthTag w m)) = true := by
  rcases hm with rfl | rfl | rfl
  · rw [stripWidthTag_withWidthTag_SHR]; rfl
  · rw [stripWidthTag_withWidthTag_SHL]; rfl
  · rw [stripWidthTag_withWidthTag_SAR]; rfl

/-- The instruction expansion from the model chain to the body walk: a
    structured immediate shift `Lopn [dst] "SHR" [src, #n]` becomes the
    count-in-mnemonic one-source form `Lopn [dst] "SHR:n" [src]`; every other
    instruction expands to itself. -/
def immShiftExpand (i : LinstrRM) : List LinstrRM :=
  match i with
  | (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none) =>
      if isShiftBase (stripWidthTag opn) then
        [(.Lopn [.reg dst] (shiftCountMnem opn n) [.reg src], MemTag.reg none)]
      else [(.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none)]
  | i => [i]

/-- An `Lopn` all of whose sources are registers expands to itself. -/
theorem immShiftExpand_of_regs (dst opn : String) (srcs : List LOperand) (tag : MemTag)
    (h : ∀ o ∈ srcs, ∃ r, o = LOperand.reg r) :
    immShiftExpand (.Lopn [.reg dst] opn srcs, tag) = [(.Lopn [.reg dst] opn srcs, tag)] := by
  rcases srcs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · rfl
  · cases a <;> rfl
  · obtain ⟨rb, rfl⟩ := h b (by simp)
    cases a <;> cases rest <;> rfl

/-- The expansion of a structured immediate shift is the count-in-mnemonic
    one-source instruction of the same destination, source and count. -/
theorem immShiftExpand_structShift {m : String}
    (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR") (w n : Nat) (dst src : String) :
    immShiftExpand (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n], MemTag.reg none)
      = [(.Lopn [.reg dst] (withWidthTag w (m ++ ":" ++ toString n)) [.reg src],
          MemTag.reg none)] := by
  show (if isShiftBase (stripWidthTag (withWidthTag w m)) then _ else _) = _
  rw [if_pos (isShiftBase_stripWidthTag hm w), shiftCountMnem_withWidthTag hm w n]

/-- A two-source instruction whose mnemonic is not a shift base expands to
    itself. -/
theorem immShiftExpand_of_not_shiftBase (dst opn src : String) (n : Nat)
    (h : isShiftBase (stripWidthTag opn) = false) :
    immShiftExpand (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none)
      = [(.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none)] := by
  show (if isShiftBase (stripWidthTag opn) then _ else _) = _
  rw [if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- An instruction that is not a structured immediate shift expands to
    itself. -/
theorem immShiftExpand_of_not_shift (i : LinstrRM)
    (h : ∀ dst opn src n,
      i ≠ (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none)) :
    immShiftExpand i = [i] := by
  unfold immShiftExpand
  split
  · next dst opn src n => exact absurd rfl (h dst opn src n)
  · rfl

/-- A binding of the fragment's op set whose sources are registers expands to
    itself: only the model chain's structured shift wire, whose count is an
    immediate, is rewritten. -/
theorem immShiftExpand_opToLinstrR {op : JasminOp} (hop : OpPlain op) (dst : String)
    (srcs : List LOperand) (hsrc : ∀ o ∈ srcs, ∃ r, o = LOperand.reg r) :
    immShiftExpand (opToLinstrR op dst srcs, memTagOfOp op)
      = [(opToLinstrR op dst srcs, memTagOfOp op)] := by
  cases op <;> first
    | exact absurd hop id
    | exact immShiftExpand_of_regs _ _ _ _ hsrc
    | rfl
    | exact immShiftExpand_of_not_shift _ (fun _ _ _ _ hcon => by
        simp [memTagOfOp] at hcon)

/-! ### The two wires step the flag machine alike -/

/-- The decoder reads the base mnemonic and the count back from the
    count-in-mnemonic rendering at width `w`: at width `64` from the tagged
    rendering, and at any other width from an untagged rendering that does not
    itself end in `:64`. -/
theorem immShiftMnem?_shiftCount {m : String} (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w n : Nat) (hw : w = 64 ∨ hasSuffix (m ++ ":" ++ toString n) ":64" = false) :
    JasminImmShiftMnem.immShiftMnem? (withWidthTag w (m ++ ":" ++ toString n))
      = some (m, n) := by
  have hm' : m = "SHL" ∨ m = "SHR" ∨ m = "SAR" := by
    rcases hm with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  by_cases h64 : w = 64
  · subst h64
    exact JasminImmShiftMnem.immShiftMnem?_withWidthTag64 hm' n
  · have hnt : withWidthTag w (m ++ ":" ++ toString n) = m ++ ":" ++ toString n := by
      simp only [withWidthTag, if_neg h64]
    rw [hnt]
    exact JasminImmShiftMnem.immShiftMnem?_untagged hm' n (hw.resolve_left h64)

/-- The structured two-source wire of an immediate shift, reduced to the
    shift-aware step `lsemStepSh` over the register half. -/
theorem fstepF_immShiftStruct {m : String} (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w n : Nat) (dst src : String) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n], MemTag.reg none) s zf
      = (lsemStepSh (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n]) s.reg).map
          (fun r => ({ s with reg := r }, zf)) := by
  obtain ⟨h1, h2⟩ := withWidthTag_plain_of_head w m 'S'
    (by rcases hm with rfl | rfl | rfl <;> rfl) (by decide) (by decide)
  have h3 : copyQ (withWidthTag w m) = false := by
    rcases hm with rfl | rfl | rfl <;> (unfold withWidthTag; split <;> decide)
  obtain ⟨_, hc, hmv⟩ := lopn_plain [LOperand.reg dst] (withWidthTag w m)
    [LOperand.reg src, LOperand.imm n] (.reg none) h1 h2 h3
  have ha : aluFlagOp? (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n],
      MemTag.reg none) = none := by
    rcases hm with rfl | rfl | rfl <;> simp only [aluFlagOp?, withWidthTag] <;> split <;> simp
  have hk : carryArgs? (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n],
      MemTag.reg none) = none := by
    rcases hm with rfl | rfl | rfl <;> simp only [carryArgs?, withWidthTag] <;> split <;> simp
  have hw : wideArgs? (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n],
      MemTag.reg none) = none := by
    rcases hm with rfl | rfl | rfl <;> simp only [wideArgs?, withWidthTag] <;> split <;> simp
  unfold fstepF
  rw [hc, hmv]
  simp only []
  rw [stepMemF_of_quiet ha hk hw]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
    lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl]
  simp only [Option.map_map]
  cases lsemStepSh (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n]) s.reg <;> rfl

/-- The register step of the count-in-mnemonic wire is the shift-aware step of
    the structured wire of the same destination, source and count. -/
theorem lsemStepN_immShiftCount {m : String} (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w n : Nat) (dst src : String)
    (hw : w = 64 ∨ hasSuffix (m ++ ":" ++ toString n) ":64" = false) (r : LstateN) :
    lsemStepN (.Lopn [.reg dst] (withWidthTag w (m ++ ":" ++ toString n)) [.reg src]) r
      = lsemStepSh (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n]) r := by
  obtain ⟨hneg, hmov⟩ := stripWidthTag_immShift (m ++ ":")
    (by rcases hm with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)) w n
  have hdec := immShiftMnem?_shiftCount hm w n hw
  show (if _ = "NEG" then _ else if _ = "MOV" then _ else _) = _
  rw [if_neg hneg, if_neg hmov, hdec]
  rcases hm with rfl | rfl | rfl
  · rw [lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne
      (by rw [stripWidthTag_withWidthTag_SHR]; decide))]
    show _ = (match readReg r (.reg src) with
      | some ⟨wa, va⟩ =>
          match evalOperandN r wa (LOperand.imm n) with
          | some vb =>
              match applyOpnN wa (stripWidthTag (withWidthTag w "SHR")) [va, vb] with
              | some v => some ((r.setReg dst v).nextPc)
              | none =>
                  match cmpOfName? (stripWidthTag (withWidthTag w "SHR")) with
                  | some c => some ((r.setReg dst (cmpBit c va vb)).nextPc)
                  | none => none
          | none => none
      | none => none)
    rw [stripWidthTag_withWidthTag_SHR]
    cases readReg r (.reg src) <;> rfl
  · rw [lsemStepSh_of_not_sar _ _ (sarStruct?_of_ne
      (by rw [stripWidthTag_withWidthTag_SHL]; decide))]
    show _ = (match readReg r (.reg src) with
      | some ⟨wa, va⟩ =>
          match evalOperandN r wa (LOperand.imm n) with
          | some vb =>
              match applyOpnN wa (stripWidthTag (withWidthTag w "SHL")) [va, vb] with
              | some v => some ((r.setReg dst v).nextPc)
              | none =>
                  match cmpOfName? (stripWidthTag (withWidthTag w "SHL")) with
                  | some c => some ((r.setReg dst (cmpBit c va vb)).nextPc)
                  | none => none
          | none => none
      | none => none)
    rw [stripWidthTag_withWidthTag_SHL]
    cases readReg r (.reg src) <;> rfl
  · have hsar : sarStruct? (LinstrR.Lopn [LOperand.reg dst] (withWidthTag w "SAR")
        [LOperand.reg src, LOperand.imm n]) = some (dst, src, n) := by
      simp only [sarStruct?, stripWidthTag_withWidthTag_SAR, if_pos]
    simp only [lsemStepSh, hsar]
    cases readReg r (LOperand.reg src) <;> simp [applyImmShiftN]

/-- **The two wires of an immediate shift step the flag machine alike.** The
    count-in-mnemonic one-source wire the body walk emits, run as a straight
    segment, takes the flag machine to the state the model chain's structured
    two-source wire takes it to. -/
theorem fstepF_immShiftWire_eq {m : String} (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w n : Nat) (dst src : String)
    (hw : w = 64 ∨ hasSuffix (m ++ ":" ++ toString n) ":64" = false)
    (s : LstateM) (zf : Bool) :
    runStraightF (immShiftExpand
        (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n], MemTag.reg none)) s zf
      = fstepF (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n],
          MemTag.reg none) s zf := by
  have hsingle : ∀ (j : LinstrRM) (u : LstateM) (b : Bool),
      runStraightF [j] u b = fstepF j u b := by
    intro j u b
    rw [runStraightF_cons]
    cases fstepF j u b <;> rfl
  rw [immShiftExpand_structShift hm, hsingle,
    fstepF_immShiftWire m hm w n dst src, fstepF_immShiftStruct hm w n dst src,
    lsemStepN_immShiftCount hm w n dst src hw]

/-- **The expanded chain equation.** For an update whose ops lie in the
    fragment's op set, the typed body walk of the export is the expansion image
    of the model chain `straightOpsMem` under the loop renaming `σ`. -/
theorem loopBodyWalkNM_eq_expand {σ : String → String} {d nInv : Nat} {accReg : String}
    {invRegs : List String} (hσ : LoopRen σ d nInv accReg invRegs)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (hcom : ComOpsPlain com) (curDepth : Nat) :
    loopBodyWalkNM d accReg (loopIdx d) invRegs (fun _ => none) com curDepth
      = ((straightOpsMem (nInv + 2) com curDepth).map (renRM σ)).flatMap immShiftExpand := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      obtain ⟨hop, hbody⟩ := hcom
      have hreg : ∀ o ∈ (exprArgs curDepth (nInv + 2) argName (fun _ => none) e).map
          (renOperand σ), ∃ r, o = LOperand.reg r := by
        intro o ho
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        obtain ⟨r, rfl⟩ := exprArgs_isReg e o' ho'
        exact ⟨σ r, rfl⟩
      simp only [loopBodyWalkNM, straightOpsMem, List.map_cons, List.flatMap_cons,
        ih hbody]
      rw [loopExprArgsN_eq_ren hσ, ← hσ.reg curDepth, ← List.singleton_append]
      congr 1
      split
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w w' h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · next w n h =>
          rw [h] at hop ⊢
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm
      · split
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inl rfl),
              opToLinstrR, memTagOfOp]
            rfl
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inr (Or.inl rfl)),
              opToLinstrR, memTagOfOp]
            rfl
        · next w n s h hs =>
            obtain ⟨r, rfl⟩ := exprArgs_isReg e s (by rw [hs]; simp)
            rw [hs, h]
            simp only [renRM, renLinstrR, JasminLsemShift.shiftLinstr, List.map_cons,
              List.map_nil, renOperand, immShiftExpand_structShift (Or.inr (Or.inr rfl)),
              opToLinstrR, memTagOfOp]
            rfl
        · have htag : memTagOfOp e.op = MemTag.reg none := by
            unfold memTagOfOp; split <;> simp_all
          simp only [renRM, renLinstrR_opToLinstrR σ _ hop]
          rw [← htag]
          exact (immShiftExpand_opToLinstrR hop _ _ hreg).symm

/-! ### The expansion certificate

`JasminLsemExportLower.ExpProg` is the certificate `lsemFuelMemF_expand`
consumes. At `immShiftExpand` its per-instruction condition holds of a
structured immediate shift by the step agreement above, and of every other
instruction because the expansion is the identity on it. -/

/-- Every instruction expands to one instruction. -/
theorem immShiftExpand_length (i : LinstrRM) : (immShiftExpand i).length = 1 := by
  unfold immShiftExpand
  split
  · split <;> rfl
  · rfl

/-- An `Lopn` whose expansion is a straight segment of `Lopn`s that runs to the
    state of the instruction itself satisfies the per-instruction condition at
    `JasminLsemExportLower.EqPc`. -/
theorem instrOK_of_runStraightF_eq {expand : LinstrRM → List LinstrRM} {i : LinstrRM}
    (hl : IsLopn i) (hex : ∀ j ∈ expand i, IsLopn j)
    (heq : ∀ (s : LstateM) (zf : Bool), runStraightF (expand i) s zf = fstepF i s zf) :
    JasminLsemExportLower.InstrOK JasminLsemExportLower.EqPc expand i :=
  Or.inl ⟨hl, hex, fun s _ _ zf _ hE h =>
    JasminLsemExportLower.runStraightF_eqPc (expand i) hE ((heq s zf).trans h)⟩

/-- A structured immediate shift satisfies the per-instruction condition of the
    immediate-shift expansion. -/
theorem instrOK_immShiftExpand_struct {m : String} (hm : m = "SHR" ∨ m = "SHL" ∨ m = "SAR")
    (w n : Nat) (dst src : String)
    (hw : w = 64 ∨ hasSuffix (m ++ ":" ++ toString n) ":64" = false) :
    JasminLsemExportLower.InstrOK JasminLsemExportLower.EqPc immShiftExpand
      (.Lopn [.reg dst] (withWidthTag w m) [.reg src, .imm n], MemTag.reg none) :=
  instrOK_of_runStraightF_eq ⟨_, _, _, rfl⟩
    (by rw [immShiftExpand_structShift hm]
        intro j hj
        obtain rfl : j = _ := by simpa using hj
        exact ⟨_, _, _, rfl⟩)
    (fun s zf => fstepF_immShiftWire_eq hm w n dst src hw s zf)

/-- An instruction that is not a structured immediate shift satisfies the
    per-instruction condition of the immediate-shift expansion: it expands to
    itself. -/
theorem instrOK_immShiftExpand_of_not_shift (i : LinstrRM)
    (h : ∀ dst opn src n,
      i ≠ (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none))
    (hi : IsLopn i ∨ (∃ kd l, i.1 = LinstrR.Llabel kd l)
      ∨ (∃ c l, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i ≠ none)
      ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)) :
    JasminLsemExportLower.InstrOK JasminLsemExportLower.EqPc immShiftExpand i := by
  rcases hi with hl | hc
  · exact JasminLsemExportLower.instrOK_self hl (immShiftExpand_of_not_shift i h)
  · exact Or.inr ⟨immShiftExpand_of_not_shift i h, hc⟩

/-- An `Lopn` whose mnemonic is not a shift base whenever its operands have the
    structured-shift shape satisfies the per-instruction condition of the
    immediate-shift expansion. -/
theorem instrOK_immShiftExpand_of_isLopn {i : LinstrRM} (hl : IsLopn i)
    (h : ∀ dst opn src n, i = (.Lopn [.reg dst] opn [.reg src, .imm n], MemTag.reg none) →
      isShiftBase (stripWidthTag opn) = false) :
    JasminLsemExportLower.InstrOK JasminLsemExportLower.EqPc immShiftExpand i := by
  refine JasminLsemExportLower.instrOK_self hl ?_
  unfold immShiftExpand
  split
  · next dst opn src n =>
      rw [if_neg (by rw [h dst opn src n rfl]; exact Bool.false_ne_true)]
  · rfl

/-- **The expansion certificate of the immediate-shift expansion.** Two programs
    of the same name whose bodies stand in the `immShiftExpand` relation, with
    every source instruction satisfying the per-instruction condition, form an
    `ExpProg` at `EqPc`. -/
theorem expProg_immShiftExpand {P P' : LprogM} (hfn : P'.lfn = P.lfn)
    (hbody : P'.body = P.body.flatMap immShiftExpand)
    (hinst : ∀ i ∈ P.body,
      JasminLsemExportLower.InstrOK JasminLsemExportLower.EqPc immShiftExpand i) :
    JasminLsemExportLower.ExpProg JasminLsemExportLower.EqPc immShiftExpand P P' where
  lfn := hfn
  body := hbody
  inst := fun _ i hk => hinst i (List.mem_of_getElem? hk)
  pc := fun _ _ p q h => JasminLsemExportLower.EqPc.setLpc h p q

/-- **The flag machine under the immediate-shift expansion.** Every halting run
    of a program whose instructions the expansion carries is matched, from a
    state equal up to the program counter, by a halting run of the expanded
    program of no greater fuel, into a state equal up to the program counter. -/
theorem lsemFuelMemF_immShiftExpand {P P' : LprogM}
    (hP : JasminLsemExportLower.ExpProg JasminLsemExportLower.EqPc immShiftExpand P P')
    (fuel : Nat) {s s' t : LstateMF}
    (hR : JasminLsemExportLower.RelX JasminLsemExportLower.EqPc immShiftExpand P s s')
    (h : lsemFuelMemF P fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF P' fuel' s' = some t'
      ∧ JasminLsemExportLower.RelX JasminLsemExportLower.EqPc immShiftExpand P t t' := by
  obtain ⟨f', t', hf', hrun, hRt⟩ :=
    JasminLsemExportLower.lsemFuelMemF_expand hP
      (m := 1) (fun i _ => le_of_eq (immShiftExpand_length i)) fuel hR h
  exact ⟨f', t', by omega, hrun, hRt⟩

/-! ## 5. Second difference: the accumulator writeback

The flag machine changes an array-carrier cell only through a `STOREIDX` whose
destination names it. The export's feedback `MOV acc, ret` is a register copy,
so no instruction of the exported loop node writes the accumulator's array. -/

/-- A typed instruction does not store to the array named `r`: it is not a
    `STOREIDX` with destination `r`. -/
def NoArrWriteAt (r : String) (i : LinstrRM) : Prop :=
  ∀ dst base idx val, storeStruct? i.1 = some (dst, base, idx, val) → dst ≠ r

/-- An instruction that is not a `STOREIDX` writes no array. -/
theorem noArrWriteAt_of_storeStruct_none (r : String) (i : LinstrRM)
    (h : storeStruct? i.1 = none) : NoArrWriteAt r i := by
  intro dst base idx val h'
  rw [h] at h'
  exact absurd h' (by simp)

/-- An `Lopn` with the single register destination `dst ≠ r` writes no array
    named `r`. -/
theorem noArrWriteAt_of_dst (r dst opn : String) (srcs : List LOperand) (tag : MemTag)
    (h : dst ≠ r) : NoArrWriteAt r (LinstrR.Lopn [.reg dst] opn srcs, tag) := by
  intro dst' base idx val h'
  simp only [storeStruct?] at h'
  split at h'
  · next hmatch =>
      split at h'
      · cases h'
        injection hmatch with h1
        injection h1 with h2
        injection h2 with h3
        rw [← h3]
        exact h
      · exact absurd h' (by simp)
  · exact absurd h' (by simp)

/-- The typed memory step leaves an array cell `r` unchanged unless it stores to
    `r`. -/
theorem lsemStepMem_larr (r : String) (i : LinstrRM) (s s' : LstateM)
    (hi : NoArrWriteAt r i) (h : lsemStepMem i s = some s') : s'.larr r = s.larr r := by
  unfold lsemStepMem at h
  repeat' split at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)
    | (cases h; rfl)
    | (cases h
       simp only [LstateM.nextPc, LstateM.setArr]
       rw [if_neg (Ne.symm (hi _ _ _ _ (by assumption)))])
    | (simp at h)

/-- A jump leaves the array carrier unchanged. -/
theorem evalJumpMem_larr (P : LprogM) (lbl : LLabel) (p p' : LstatePM)
    (h : evalJumpMem P lbl p = some p') : p'.base.larr = p.base.larr := by
  unfold evalJumpMem at h
  split at h
  · cases h; rfl
  · exact absurd h (by simp)

/-- The labelled step leaves an array cell `r` unchanged unless it stores to
    `r`. -/
theorem evalInstrPMemL_larr (r : String) (P : LprogM) (i : LinstrRM) (p p' : LstatePM)
    (hi : NoArrWriteAt r i) (h : evalInstrPMemL P i p = some p') :
    p'.base.larr r = p.base.larr r := by
  unfold evalInstrPMemL at h
  split at h
  · cases h; rfl
  · split at h
    · rw [evalJumpMem_larr P _ p p' h]
    · cases h; rfl
  · split at h
    · rw [evalJumpMem_larr P _ p p' h]
    · exact absurd h (by simp)
  · obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    exact lsemStepMem_larr r i p.base b hi hb

/-- The flag step leaves an array cell `r` unchanged unless it stores to `r`; in
    particular the register-copy `MOV` leaves every array cell unchanged. -/
theorem evalInstrPMemF_larr (r : String) (P : LprogM) (i : LinstrRM) (s s' : LstateMF)
    (hi : NoArrWriteAt r i) (h : evalInstrPMemF P i s = some s') :
    s'.prog.base.larr r = s.prog.base.larr r := by
  unfold evalInstrPMemF at h
  split at h
  · split at h
    · cases h; rfl
    · exact absurd h (by simp)
  · split at h
    · split at h
      · cases h; rfl
      · exact absurd h (by simp)
    · split at h
      · split at h
        · obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [evalJumpMem_larr P _ s.prog p hp]
        · cases h; rfl
      · split at h
        · rename_i p hp
          cases h
          show (withALUFlags i s.prog.base p.base).larr r = _
          rw [withALUFlags_larr]
          exact evalInstrPMemL_larr r P i s.prog p hi hp
        · split at h
          · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
            unfold carryStep at hb
            split at hb
            · split at hb <;> (cases hb; rfl)
            · exact absurd hb (by simp)
          · split at h
            · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
              unfold wideStep at hb
              split at hb
              · split at hb
                · cases hb; rfl
                · exact absurd hb (by simp)
              · split at hb
                · cases hb; rfl
                · exact absurd hb (by simp)
            · cases h

/-- **The register-copy move leaves the array carrier unchanged.** The export's
    feedback `MOV acc, ret` updates the register cell of `acc` and no array
    cell. -/
theorem fstepF_movReg_larr (acc ret : String) (tag : MemTag) (s s' : LstateM) (zf zf' : Bool)
    (h : fstepF (LinstrR.Lopn [.reg acc] (withWidthTag 64 "MOV") [.reg ret], tag) s zf
      = some (s', zf')) : s'.larr = s.larr := by
  unfold fstepF at h
  simp only [cmpArgs?, movRegArgs?] at h
  rw [if_pos (show stripWidthTag (withWidthTag 64 "MOV") = "MOV" by decide)] at h
  simp only [readReg] at h
  cases h
  rfl

/-- **Array frame of the flag machine.** A halting flag-machine run of a program
    none of whose instructions stores to `r` leaves the array cell `r` at its
    entry value. -/
theorem lsemFuelMemF_larr (r : String) (P : LprogM) (hP : ∀ i ∈ P.body, NoArrWriteAt r i) :
    ∀ (fuel : Nat) (s t : LstateMF), lsemFuelMemF P fuel s = some t →
      t.prog.base.larr r = s.prog.base.larr r := by
  intro fuel
  induction fuel with
  | zero =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · cases h; rfl
      · exact absurd h (by simp)
  | succ n ih =>
      intro s t h
      unfold lsemFuelMemF at h
      split at h
      · cases h; rfl
      · next i hf =>
          split at h
          · next s' he =>
              rw [ih s' t h]
              exact evalInstrPMemF_larr r P i s s' (hP i (findInstrMem_mem P s.prog i hf)) he
          · exact absurd h (by simp)

/-- Every `opToLinstrR` image has the single register destination it names. -/
theorem opToLinstrR_dst (op : JasminOp) (dst : String) (srcs : List LOperand) :
    ∃ o s, opToLinstrR op dst srcs = LinstrR.Lopn [.reg dst] o s := by
  unfold opToLinstrR
  split <;> (repeat' (first | exact ⟨_, _, rfl⟩ | split | dsimp only))

/-- The typed loop node split at the body walk. -/
theorem forLoopLcmdNRtRM_split (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    forLoopLcmdNRtRM d accReg initOp countOp update invOps immSlotMap
      = (loopSeedsRM d accReg initOp countOp
          ++ [ (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .imm 0],
                MemTag.reg none)
             , (.Lcond (.reg "Z") (d + 0x40000000), MemTag.reg none)
             , (.Llabel .internal d, MemTag.reg none) ])
        ++ loopBodyWalkNM d accReg (loopIdx d) (invRegsOf invOps) immSlotMap update
            (2 + invTys.length)
        ++ (loopFeedbackRM accReg
              (loopBodyWalkN d accReg (loopIdx d) (invRegsOf invOps) immSlotMap update
                (2 + invTys.length)).2
            ++ loopAdvanceRM d ++ loopTouchRM d (invRegsOf invOps)
            ++ flagBackedge (loopCtr d) d
            ++ [(.Llabel .internal (d + 0x40000000), MemTag.reg none)]) := by
  simp [forLoopLcmdNRtRM, guardedFlagLoopLinstrRM, flagLoopLinstrRM, forLoopBodyNRtRM,
    loopSeedsRM]

/-- No instruction of the exported loop node stores to the accumulator's array,
    when the body temporaries are distinct from the accumulator register. -/
theorem forLoopLcmdNRtRM_noArrWrite (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hacc : ∀ k, loopReg d k ≠ accReg) :
    ∀ i ∈ forLoopLcmdNRtRM d accReg initOp countOp update invOps immSlotMap,
      NoArrWriteAt accReg i := by
  have hwalk : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
      (cd : Nat) (invRegs : List String),
      ∀ i ∈ loopBodyWalkNM d accReg (loopIdx d) invRegs immSlotMap com cd,
        NoArrWriteAt accReg i := by
    intro Γ t com
    induction com with
    | ret v => intro cd invRegs i hi; simp [loopBodyWalkNM] at hi
    | var e body ih =>
        intro cd invRegs i hi
        simp only [loopBodyWalkNM, List.mem_cons] at hi
        rcases hi with rfl | hi
        · obtain ⟨o, s, hos⟩ := opToLinstrR_dst e.op (loopReg d cd)
            (loopExprArgsN d accReg (loopIdx d) invRegs cd immSlotMap e)
          show NoArrWriteAt accReg (opToLinstrR _ _ _, _)
          rw [hos]
          exact noArrWriteAt_of_dst _ _ _ _ _ (hacc cd)
        · exact ih (cd + 1) invRegs i hi
  have hop : ∀ (ds : List LOperand) (opn : String) (ss : List LOperand) (tag : MemTag),
      opn ≠ "STOREIDX" → NoArrWriteAt accReg (LinstrR.Lopn ds opn ss, tag) :=
    fun ds opn ss tag h => noArrWriteAt_of_storeStruct_none _ _ (by
      show storeStruct? (LinstrR.Lopn ds opn ss) = none
      unfold storeStruct?
      split <;> simp_all)
  intro i hi
  rw [forLoopLcmdNRtRM_split, List.mem_append, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · simp only [loopSeedsRM, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hop _ _ _ _ (by decide)
    · exact hop _ _ _ _ (by decide)
    · exact hop _ _ _ _ (by decide)
    · exact hop _ _ _ _ (by decide)
    · exact noArrWriteAt_of_storeStruct_none _ _ rfl
    · exact noArrWriteAt_of_storeStruct_none _ _ rfl
  · exact hwalk _ _ _ i hi
  · simp only [List.mem_append] at hi
    rcases hi with (((hi | hi) | hi) | hi) | hi
    · unfold loopFeedbackRM at hi
      split at hi
      · simp at hi
      · simp only [List.mem_singleton] at hi
        subst hi
        exact hop _ _ _ _ (by decide)
    · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> exact hop _ _ _ _ (by decide)
    · simp only [loopTouchRM, List.mem_map] at hi
      obtain ⟨r, _, rfl⟩ := hi
      exact hop _ _ _ _ (by decide)
    · simp only [flagBackedge, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact hop _ _ _ _ (by decide)
      · exact noArrWriteAt_of_storeStruct_none _ _ rfl
    · simp only [List.mem_singleton] at hi
      subst hi
      exact noArrWriteAt_of_storeStruct_none _ _ rfl

/-- **The exported array-accumulator loop leaves the accumulator's array at its
    entry value.** Every halting flag-machine run of the typed loop node, when the
    body temporaries are distinct from the accumulator register, ends with the
    accumulator's array cell equal to its value at entry: the body's updated
    array is written to a fresh temporary by `STOREIDX`, and the feedback
    `MOV acc, ret` does not copy it into the accumulator's array cell. -/
theorem forLoopLcmdNRtRM_acc_frozen (fn : String) (d : Nat) (accReg : String)
    (initOp countOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap)
    (hacc : ∀ k, loopReg d k ≠ accReg) (fuel : Nat) (s t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn
      (forLoopLcmdNRtRM d accReg initOp countOp update invOps immSlotMap)) fuel s = some t)
    (w n : Nat) :
    decodeArrM t.prog.base accReg w n = decodeArrM s.prog.base accReg w n := by
  have h := lsemFuelMemF_larr accReg _ (forLoopLcmdNRtRM_noArrWrite d accReg initOp countOp
    update invOps immSlotMap hacc) fuel s t hrun
  unfold decodeArrM LstateM.getArr
  rw [h]

/-! ## 6. Register-name hygiene of the export's loop names -/

/-- Appending to a string keeps its first character. -/
theorem head?_append_of (s t : String) (c : Char) (h : s.toList.head? = some c) :
    (s ++ t).toList.head? = some c := by
  rw [String.toList_append]
  cases hs : s.toList with
  | nil => rw [hs] at h; simp at h
  | cons x xs => rw [hs] at h; simpa using h

/-- Two strings with different first characters differ. -/
theorem ne_of_head? (s t : String) (c c' : Char) (hs : s.toList.head? = some c)
    (ht : t.toList.head? = some c') (hc : c ≠ c') : s ≠ t := by
  intro h
  rw [h, ht] at hs
  exact hc (Option.some.inj hs).symm

/-- A body temporary `L<d>_r<k>` starts with `L`. -/
theorem head?_loopReg (d k : Nat) : (loopReg d k).toList.head? = some 'L' :=
  head?_append_of _ _ _ (head?_append_of _ _ _ (head?_append_of _ _ _ rfl))

/-- A trip counter `Lctr<d>` starts with `L`. -/
theorem head?_loopCtr (d : Nat) : (loopCtr d).toList.head? = some 'L' :=
  head?_append_of _ _ _ rfl

/-- An argument register `a<j>` starts with `a`. -/
theorem head?_argName (j : Nat) : (argName j).toList.head? = some 'a' :=
  head?_append_of _ _ _ rfl

/-- A chain register `r<k>` starts with `r`. -/
theorem head?_regName (k : Nat) : (regName k).toList.head? = some 'r' :=
  head?_append_of _ _ _ rfl

/-- The export's body temporaries are distinct from every chain register, in
    particular from the accumulator register `regName d` of a loop node at
    depth `d`. -/
theorem loopReg_ne_regName (d k k' : Nat) : loopReg d k ≠ regName k' :=
  ne_of_head? _ _ _ _ (head?_loopReg d k) (head?_regName k') (by decide)

/-- The export's trip counter is distinct from every argument register. -/
theorem loopCtr_ne_argName (d j : Nat) : loopCtr d ≠ argName j :=
  ne_of_head? _ _ _ _ (head?_loopCtr d) (head?_argName j) (by decide)

/-- The export's trip counter is distinct from every chain register. -/
theorem loopCtr_ne_regName (d k : Nat) : loopCtr d ≠ regName k :=
  ne_of_head? _ _ _ _ (head?_loopCtr d) (head?_regName k) (by decide)

/-- **The exported loop node leaves its accumulator's array at its entry
    value.** The instance of `forLoopLcmdNRtRM_acc_frozen` at the accumulator
    register `regName d` that `comLToBody` assigns a loop node at depth `d`. -/
theorem forLoopLcmdNRtRM_regName_acc_frozen (fn : String) (d : Nat)
    (initOp countOp : LOperand) {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (fuel : Nat) (s t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn
      (forLoopLcmdNRtRM d (regName d) initOp countOp update invOps (fun _ => none)))
        fuel s = some t)
    (w n : Nat) :
    decodeArrM t.prog.base (regName d) w n = decodeArrM s.prog.base (regName d) w n :=
  forLoopLcmdNRtRM_acc_frozen fn d (regName d) initOp countOp update invOps (fun _ => none)
    (fun k => loopReg_ne_regName d k d) fuel s t hrun w n

/-! ## 7. The compare kernel -/

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnDivRem1FrontEmit (segCells)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemArrTripCmp (cmpUpdate_arrMemN)

/-- **The compare kernel on the flag machine under the export's skeleton.** The
    model body of the front-compiled `mpn_cmp` limb (`loopBodyArrFullMN
    cmpUpdate`), placed in the export's zero-trip-guarded flag loop with the
    export's trip counter `Lctr<d>`, run by `lsemFuelMemF` from pc `0` with the
    counter holding the runtime count, halts on an output array whose cell `0`
    holds `cmpSign` of the two operands' `bignumVal`. No schedule hypothesis
    remains. -/
theorem cmp_flag_machine_val (V : Ctxt.Valuation Gouter)
    (hn : 0 < (cmpCount.lookup V).toNat)
    (h0 : memGetDyn (cmpInit.lookup V) 0 = 0)
    (fn : String) (d : Nat)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (([AO, AO, r64] : Ctxt jasminDialect).length + 2)
      (([AO, AO, r64] : Ctxt jasminDialect).length + 2) b0
      (tripValArrMN (Expr.lookupArgs cmpInvs V) 0 (cmpInit.lookup V)))
    (hv0 : b0.reg.getW (loopCtr d) 64 = some (cmpCount.lookup V)) :
    ∃ (k : Nat) (t : LstateMF) (out : Fin NR → BitVec 64),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
            (loopBodyArrTouchMN cmpUpdate (loopCtr d) [])))
          k { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (accRegMN [AO, AO, r64]) 64 NR = some out
        ∧ memGetDyn out 0
            = cmpSign (bignumVal (segCells (apVar.lookup V) 0 (cmpCount.lookup V).toNat))
                (bignumVal (segCells (bpVar.lookup V) 0 (cmpCount.lookup V).toNat)) := by
  obtain ⟨k, t, hrun, hdec, _⟩ := guardedFlagLoopArr_faithful_closed cmpUpdate
    cmpUpdate_arrMemN (Expr.lookupArgs cmpInvs V) fn d (d + 0x40000000) (loopCtr d)
    (show (d : Nat) ≠ d + 0x40000000 by omega) (loopCtr_ne_argName d)
    (loopCtr_ne_regName d) [] (by simp)
    (TouchRestoresFArrMN_nil _ _ _) b0 zf hpc (cmpInit.lookup V) hseed
    (cmpCount.lookup V).toNat (cmpCount.lookup V).isLt
    (by rw [hv0, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  obtain ⟨out, hmap, hval⟩ := cmpRtProg_val V hn h0
  have hd := cmpRtProg_denote (update := cmpUpdate) cmpUpdate_eq V
  rw [hd] at hmap
  obtain rfl := Option.some.inj hmap
  exact ⟨k, t, _, hrun, hdec, hval⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer
