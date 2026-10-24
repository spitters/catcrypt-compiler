/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop

@[expose] public section

set_option autoImplicit false

/-!
# The allocated body of the single-loop export is the certified node

`ExportCertLoop.loopCertB` compares the virtual body `PhysAbiShape.abiBody1` of the
single-loop export with the liveness pin, `ExportCertLoop.certNode` and the return. This
module proves that equation for every single-loop program whose seed and count resolve to
registers, whose invariant operands are registers, and whose update stores only into the
array thread head (`storeOnHeadB` on the model chain).

The export aliases the accumulator register onto the out-array name and then renames each
store result through the store-thread alias map `arrChainAlias`. On a body walk whose stores
all write the thread head, that map sends exactly the body temporaries of the store slots to
the out-array name (`foldl_aliasStepL_walk`), so the two renamings compose to `certRho` over
the store slots of the model chain.

## Main results

* `storeOnHeadB` — every store of a chain reads the current thread head.
* `foldl_aliasStepL_walk` — the store-thread alias map of the aliased body walk.
* `abiBody1_singleLoop_certNode` — the allocated virtual body of the single-loop export is
  the liveness pin, `certNode` and the return, instruction for instruction.
* `loopCertNB`, `loopCertB_of_loopCertNB`, `comLCertNB`, `comLCertB_of_comLCertNB` — the
  check without the body equation, and the body equation as a lemma.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM MemTag straightOpsMem
  storeStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (storeHit? arrUse?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR
  renOperand LoopRen loopExprArgsN_eq_ren head?_loopReg head?_regName ne_of_head?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (renLcmd renLinstr
  aliasRegBody_eq_renLcmd canonicalizeMemrefThread_eq_renLcmd renLcmd_wire)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCanon (renLinstrR_comp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift (forLoopLcmdNRtRM
  forLoopLcmdNRtRM_wire forLoopLcmdNRt_unfold invRegsOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportCert
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (accRegMN)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop

/-! ## 1. Stores on the thread head -/

/-- A runtime-indexed store tag. -/
def isStoreTagB : MemTag → Bool
  | .store _ _ => true
  | _ => false

/-- Every store of a chain reads the current thread head `h`; a store's result becomes the
    head. Every array write of the chain is a runtime-indexed store (`isStoreTagB`): the
    alias walk `aliasStepL` follows `STOREIDX` only, so a constant-index `STOREIMM` is
    refused (C4-34 row E extends the walk). -/
def storeOnHeadB : List LinstrRM → String → Bool
  | [], _ => true
  | i :: is, h =>
      match storeHit? i with
      | none => storeOnHeadB is h
      | some x => arrUse? i == some h && storeOnHeadB is x && isStoreTagB i.2

/-! ## 2. One binding of the walk under the alias map -/

/-- The resolution of a name through an association list, the identity off the list. -/
abbrev lookupD (l : List (String × String)) (n : String) : String := (l.lookup n).getD n

theorem isMemStore_storeidx : isMemStore "STOREIDX" = true := by decide

theorem isMemStore_loadidx : isMemStore "LOADIDX" = false := by decide

/-- An instruction whose first source is no indexed operand leaves the alias list. -/
theorem aliasStepL_of_head (l : List (String × String)) (ii : Nat) (dsts : List LOperand)
    (opn : String) (srcs : List LOperand) (h : ∀ b x s rest, srcs ≠ .arrIdx b x s :: rest) :
    aliasStepL l ⟨ii, .Lopn dsts opn srcs⟩ = l := by
  unfold aliasStepL
  split
  · next heq => simp only [LinstrR.Lopn.injEq] at heq; exact absurd heq.2.2 (h _ _ _ _)
  · rfl

/-- An indexed memory operand. -/
def isArrIdx : LOperand → Bool
  | .arrIdx _ _ _ => true
  | _ => false

/-- The sources of an `Lopn`, empty for every other instruction. -/
def srcsOf : LinstrR → List LOperand
  | .Lopn _ _ s => s
  | _ => []

/-- An instruction with no indexed source, renamed, leaves the alias list. -/
theorem aliasStepL_ren_of_srcs (α : String → String) (l : List (String × String)) (ii : Nat)
    (i : LinstrR) (h : ∀ o ∈ srcsOf i, isArrIdx o = false) :
    aliasStepL l ⟨ii, renLinstrR α i⟩ = l := by
  cases i with
  | Lopn dsts opn srcs =>
      apply aliasStepL_of_head
      intro b x s rest he
      cases srcs with
      | nil => simp at he
      | cons o rest' =>
          have := h o (by simp [srcsOf])
          cases o <;> simp_all [renOperand, isArrIdx]
  | _ => rfl

/-- Outside the array load and store, `opToLinstrR` adds no indexed source. -/
theorem srcsOf_opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand)
    (hs : ∀ w n, op ≠ .stackStore w n) (hl : ∀ w n, op ≠ .stackLoad w n)
    (h : ∀ o ∈ srcs, isArrIdx o = false) :
    ∀ o ∈ srcsOf (opToLinstrR op dst srcs), isArrIdx o = false := by
  cases op <;> simp only [opToLinstrR] <;> (repeat' split) <;>
    simp_all [srcsOf, isArrIdx]
  all_goals
    intro o ho
    rcases ho with ho | rfl
    · exact h o ho
    · rfl

/-- The model-chain instruction `straightOpsMem` emits for a binding of `op` at depth `cd`
    over the resolved operands `src`. -/
def chainElem (op : JasminOp) (cd : Nat) (src : List LOperand) : LinstrRM :=
  match op with
  | .stackLoad w n => (opToLinstrR op (regName cd) src, .load w n)
  | .stackStore w n => (opToLinstrR op (regName cd) src, .store w n)
  | .stackZero w n => (opToLinstrR op (regName cd) src, .zero w n)
  | .stackStoreImm w n _ => (opToLinstrR op (regName cd) src, .storeImm w n)
  | .castW _ w' => (opToLinstrR op (regName cd) src, .reg (some w'))
  | .regConst w _ => (opToLinstrR op (regName cd) src, .reg (VIR.JasminLsemCast.regConstDescr w))
  | _ =>
    let wire : LinstrR :=
      match op, src with
      | .shrImm w n, [s] => shiftLinstr "SHR" w (regName cd) s n
      | .shlImm w n, [s] => shiftLinstr "SHL" w (regName cd) s n
      | .sarImm w n, [s] => shiftLinstr "SAR" w (regName cd) s n
      | _, _ => opToLinstrR op (regName cd) src
    (wire, .reg none)

theorem straightOpsMem_var (nArgs cd : Nat) {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) :
    straightOpsMem nArgs (.var e body) cd
      = chainElem e.op cd (exprArgs cd nArgs argName (fun _ => none) e)
        :: straightOpsMem nArgs body (cd + 1) := rfl

/-- **One binding.** For register operands `src`, the binding either is no store of the
    model chain and leaves the alias list of the renamed walk instruction, or is the store
    of slot `cd` reading `b`, and the walk instruction binds its body temporary to the
    resolution of the renamed `b`, or is an array write that reads no array or is no
    runtime-indexed store. -/
theorem aliasStepL_binding (σ α : String → String) (d cd : Nat) (op : JasminOp)
    (src : List LOperand) (hsrc : ∀ o ∈ src, ∃ r, o = .reg r) (l : List (String × String)) :
    (storeHit? (chainElem op cd src) = none
      ∧ aliasStepL l (renLinstr α ⟨0, opToLinstrR op (loopReg d cd)
          (src.map (renOperand σ))⟩) = l)
    ∨ (∃ b, storeHit? (chainElem op cd src) = some (regName cd)
      ∧ arrUse? (chainElem op cd src) = some b
      ∧ aliasStepL l (renLinstr α ⟨0, opToLinstrR op (loopReg d cd)
          (src.map (renOperand σ))⟩)
        = (α (loopReg d cd), lookupD l (α (σ b))) :: l)
    ∨ ((storeHit? (chainElem op cd src)).isSome ∧ (arrUse? (chainElem op cd src) = none
        ∨ isStoreTagB (chainElem op cd src).2 = false)) := by
  have hreg : ∀ o ∈ src.map (renOperand σ), isArrIdx o = false := by
    intro o ho
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    obtain ⟨r, rfl⟩ := hsrc o' ho'
    rfl
  by_cases hz : ∃ w n, op = .stackZero w n
  · obtain ⟨w, n, rfl⟩ := hz
    right; right
    exact ⟨by simp [chainElem, storeHit?, JasminLsemMem.zeroStruct?_stackZero], Or.inl rfl⟩
  by_cases hsi : ∃ w n k, op = .stackStoreImm w n k
  · obtain ⟨w, n, k, rfl⟩ := hsi
    cases hh : storeHit? (chainElem (.stackStoreImm w n k) cd src) with
    | some x => exact Or.inr (Or.inr ⟨by simp only [hh, Option.isSome_some], Or.inr rfl⟩)
    | none =>
        refine Or.inl ⟨rfl, ?_⟩
        exact aliasStepL_ren_of_srcs α l 0 _ (by
          simp only [opToLinstrR, srcsOf, List.mem_append, List.mem_map, List.mem_singleton]
          rintro o (⟨a, ha, rfl⟩ | rfl)
          · exact hreg _ (List.mem_map_of_mem ha)
          · rfl)
  by_cases hst : ∃ w n, op = .stackStore w n
  · obtain ⟨w, n, rfl⟩ := hst
    rcases src with _ | ⟨o1, _ | ⟨o2, _ | ⟨o3, _ | ⟨o4, rest⟩⟩⟩⟩
    · left; exact ⟨rfl, rfl⟩
    · left; obtain ⟨r1, rfl⟩ := hsrc o1 (by simp); exact ⟨rfl, rfl⟩
    · left
      obtain ⟨r1, rfl⟩ := hsrc o1 (by simp)
      obtain ⟨r2, rfl⟩ := hsrc o2 (by simp)
      exact ⟨rfl, rfl⟩
    · right; left
      obtain ⟨r1, rfl⟩ := hsrc o1 (by simp)
      obtain ⟨r2, rfl⟩ := hsrc o2 (by simp)
      obtain ⟨r3, rfl⟩ := hsrc o3 (by simp)
      refine ⟨r1, rfl, rfl, ?_⟩
      simp [opToLinstrR, renLinstr, renLinstrR, renOperand, aliasStepL, isMemStore_storeidx]
    · left
      obtain ⟨r1, rfl⟩ := hsrc o1 (by simp)
      obtain ⟨r2, rfl⟩ := hsrc o2 (by simp)
      obtain ⟨r3, rfl⟩ := hsrc o3 (by simp)
      exact ⟨rfl, rfl⟩
  · left
    refine ⟨?_, ?_⟩
    · cases op <;> first
        | rfl
        | exact absurd ⟨_, _, rfl⟩ hst
        | exact absurd ⟨_, _, rfl⟩ hz
        | exact absurd ⟨_, _, _, rfl⟩ hsi
    · by_cases hld : ∃ w n, op = .stackLoad w n
      · obtain ⟨w, n, rfl⟩ := hld
        simp only [opToLinstrR]
        split
        · simp [renLinstr, renLinstrR, renOperand, aliasStepL, isMemStore_loadidx]
        · exact aliasStepL_ren_of_srcs α l 0 _ (by simpa [srcsOf] using hreg)
      · exact aliasStepL_ren_of_srcs α l 0 _
          (srcsOf_opToLinstrR op _ _ (fun w n h => hst ⟨w, n, h⟩) (fun w n h => hld ⟨w, n, h⟩)
            hreg)

/-! ## 3. The alias map of the body walk -/

/-- The alias list resolves the body temporaries of the slots `S` to `out` and every other
    name to itself, and is empty exactly when `S` is. -/
def AliasInv (d : Nat) (out : String) (S : List Nat) (l : List (String × String)) : Prop :=
  (∀ n, lookupD l n = if n ∈ S.map (loopReg d) then out else n) ∧ l.isEmpty = S.isEmpty

theorem aliasInv_nil (d : Nat) (out : String) : AliasInv d out [] [] :=
  ⟨fun n => by simp [lookupD], rfl⟩

/-- A store of slot `cd` whose base resolves to `out` extends the invariant by `cd`. -/
theorem AliasInv.store {d : Nat} {out : String} {S : List Nat} {l : List (String × String)}
    (h : AliasInv d out S l) (cd : Nat) :
    AliasInv d out (S ++ [cd]) ((loopReg d cd, out) :: l) := by
  refine ⟨fun n => ?_, by simp⟩
  by_cases hn : n = loopReg d cd
  · subst hn; simp [lookupD]
  · have hb : (n == loopReg d cd) = false := by simpa using hn
    show (List.lookup n ((loopReg d cd, out) :: l)).getD n = _
    rw [List.lookup_cons, hb]
    dsimp only [cond_false]
    rw [show (List.lookup n l).getD n = _ from h.1 n]
    simp [hn]

/-- A body temporary is not the accumulator register. -/
theorem loopReg_ne_regName (d k j : Nat) : loopReg d k ≠ regName j :=
  ne_of_head? _ _ _ _ (head?_loopReg d k) (head?_regName j) (by decide)

theorem aliasRegName_loopReg (d k : Nat) (out : String) :
    aliasRegName (regName d) out (loopReg d k) = loopReg d k := by
  unfold aliasRegName
  rw [ite_eq_right (by simpa using loopReg_ne_regName d k d)]

/-- The model resolves every operand to a register. -/
theorem exprArgs_go_reg (cd nArgs : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go cd nArgs argName (fun _ => none) hv, ∃ r, o = .reg r
  | [], .nil => by simp [exprArgs.go]
  | _ :: _, .cons v rest => by
      intro o ho
      change o ∈ resolveVar cd nArgs argName (fun _ => none) v
        :: exprArgs.go cd nArgs argName (fun _ => none) rest at ho
      rcases List.mem_cons.mp ho with rfl | ho
      · unfold resolveVar
        dsimp only
        split <;> exact ⟨_, rfl⟩
      · exact exprArgs_go_reg cd nArgs rest o ho

/-- **The alias list of the aliased body walk.** From an alias list resolving the store
    slots `S` to `out`, at a thread head that is the accumulator argument or a slot of `S`,
    the walk of a chain whose stores read the head extends the list to the slots `S`
    followed by the store slots of the chain. -/
theorem foldl_aliasStepL_walk {d nInv : Nat} {invRegs : List String} {σ : String → String}
    (hσ : LoopRen σ d nInv (regName d) invRegs) (out : String) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t) (cd : Nat)
      (h : String) (S : List Nat) (l : List (String × String)),
      AliasInv d out S l → (h = argName (nInv + 1) ∨ ∃ k ∈ S, h = regName k) →
      storeOnHeadB (straightOpsMem (nInv + 2) com cd) h = true →
      AliasInv d out (S ++ storeSlots (straightOpsMem (nInv + 2) com cd) cd)
        ((renLcmd (aliasRegName (regName d) out)
          (loopBodyWalkN d (regName d) (loopIdx d) invRegs (fun _ => none) com cd).1).foldl
            aliasStepL l) := by
  intro Γ t com
  induction com with
  | ret v =>
      intro cd h S l hl _ _
      simpa [straightOpsMem, loopBodyWalkN, storeSlots, renLcmd] using hl
  | var e body ih =>
      intro cd h S l hl hh hs
      rw [straightOpsMem_var] at hs ⊢
      have hw : (loopBodyWalkN d (regName d) (loopIdx d) invRegs (fun _ => none)
          (.var e body) cd).1
          = ⟨0, opToLinstrR e.op (loopReg d cd)
              ((exprArgs cd (nInv + 2) argName (fun _ => none) e).map (renOperand σ))⟩
            :: (loopBodyWalkN d (regName d) (loopIdx d) invRegs (fun _ => none) body
              (cd + 1)).1 := by
        rw [← loopExprArgsN_eq_ren hσ]
        rfl
      rw [hw]
      simp only [renLcmd, List.map_cons, List.foldl_cons]
      have hsrc := exprArgs_go_reg cd (nInv + 2) e.args
      rcases aliasStepL_binding σ (aliasRegName (regName d) out) d cd e.op
          (exprArgs cd (nInv + 2) argName (fun _ => none) e) hsrc l with
        ⟨hn, ha⟩ | ⟨b, hn, hb, ha⟩ | ⟨hn, hb⟩
      · rw [ha]
        simp only [storeOnHeadB, hn] at hs
        have := ih (cd + 1) h S l hl hh hs
        simpa [storeSlots, hn, renLcmd] using this
      · rw [ha]
        simp only [storeOnHeadB, hn, hb, Bool.and_eq_true, beq_iff_eq, Option.some.injEq]
          at hs
        obtain ⟨⟨rfl, hs⟩, -⟩ := hs
        have hres : lookupD l (aliasRegName (regName d) out (σ b)) = out := by
          rcases hh with rfl | ⟨k, hk, rfl⟩
          · rw [hσ.acc]
            simp only [aliasRegName, beq_self_eq_true, ite_true]
            rw [hl.1]
            split <;> rfl
          · rw [hσ.reg, aliasRegName_loopReg, hl.1, ite_eq_left (List.mem_map_of_mem hk)]
        rw [hres, aliasRegName_loopReg]
        have := ih (cd + 1) (regName cd) (S ++ [cd]) _ (hl.store cd)
          (Or.inr ⟨cd, by simp, rfl⟩) hs
        simpa [storeSlots, hn, renLcmd, List.append_assoc] using this
      · exfalso
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hn
        rcases hb with hb | hb <;> simp [storeOnHeadB, hx, hb] at hs

/-! ## 4. The loop node -/

/-- No instruction of a list has an indexed source. -/
def NoArrSrc (xs : Lcmd) : Prop := ∀ i ∈ xs, ∀ o ∈ srcsOf i.li_i, isArrIdx o = false

/-- Instructions without indexed sources around a segment leave its alias list. -/
theorem foldl_aliasStepL_sandwich (α : String → String) (A M B : Lcmd) (hA : NoArrSrc A)
    (hB : NoArrSrc B) (l : List (String × String)) :
    ((A ++ (M ++ B)).map (renLinstr α)).foldl aliasStepL l
      = (M.map (renLinstr α)).foldl aliasStepL l := by
  have hX : ∀ (X : Lcmd), NoArrSrc X → ∀ l, (X.map (renLinstr α)).foldl aliasStepL l = l := by
    intro X hX
    induction X with
    | nil => intro l; rfl
    | cons i X ih =>
        intro l
        rw [List.map_cons, List.foldl_cons]
        have hi : aliasStepL l (renLinstr α i) = l :=
          aliasStepL_ren_of_srcs α l i.li_ii i.li_i (hX i (by simp))
        rw [hi]
        exact ih (fun j hj => hX j (by simp [hj])) l
  rw [List.map_append, List.map_append, List.foldl_append, List.foldl_append, hX A hA l,
    hX B hB]

/-- The wire of the certified node is the export's loop node renamed by `certRho`. -/
theorem certNode_wire {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (out c : String) :
    (certNode update invs out c).map Prod.fst
      = ((forLoopLcmdNRt Γ.length (regName Γ.length) (.reg out) (.reg c) update
          (loopInvOps invs) (fun _ => none)).map Linstr.li_i).map
        (renLinstrR (certRho Γ.length (regName Γ.length) out (certSlots update))) := by
  unfold certNode
  rw [← forLoopLcmdNRtRM_wire]
  simp [List.map_map, Function.comp_def, renRM]

/-- **The allocated virtual body of the single-loop export is the certified node.** For the
    program with one runtime-count loop node and nothing after it, whose seed and count
    resolve to registers `out` and `c`, whose invariant operands are one register per
    invariant, and whose update stores only into the array thread head: the body
    `ComL.toLfundefPhysAbi` allocates is the liveness pin, `certNode` and the return,
    instruction for instruction. -/
theorem abiBody1_singleLoop_certNode {Γ : Ctxt jasminDialect} {w n : Nat}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (outArg : String)
    (inArgs abiArgs : List String) {out c : String}
    (hinit : resolveVar Γ.length Γ.length argName (fun _ => none) init = .reg out)
    (hcount : resolveVar Γ.length Γ.length argName (fun _ => none) count = .reg c)
    (hlen : (invRegsOf (loopInvOps invs)).length = invTys.length)
    (hhead : storeOnHeadB (certChain update) (accRegMN invTys) = true) :
    (abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none)
        abiArgs).map (·.li_i)
      = (abiLivePin abiArgs).map (·.li_i) ++ (certNode update invs out c).map Prod.fst
        ++ [.Lret] := by
  have hσ := certSigma_loopRen (d := Γ.length) (acc := regName Γ.length) hlen
  have hder : (abiDerived (singleLoop update count init invs) outArg inArgs
      (fun _ => none)).1 = out := by
    simp [abiDerived, ComL.loopArgBaseNames, loopArgBasesOf, hinit]
  have hnode : loopNode update count init invs (fun _ => none)
      = forLoopLcmdNRt Γ.length (regName Γ.length) (.reg out) (.reg c) update
          (loopInvOps invs) (fun _ => none) := by
    unfold loopNode
    rw [hinit, hcount]
    rfl
  have hb : abiBody1 (singleLoop update count init invs) outArg inArgs (fun _ => none) abiArgs
      = abiLivePin abiArgs ++ canonicalizeMemrefThread (aliasRegBody (regName Γ.length) out
          (loopNode update count init invs (fun _ => none) ++ [⟨0, .Lret⟩])) := by
    have hacc : ComL.loopAccRegs (singleLoop update count init invs) Γ.length = [Γ.length] :=
      rfl
    unfold abiBody1
    rw [toLfundef_singleLoop_body, hacc, List.map_singleton, List.foldl_cons, List.foldl_nil,
      hder]
  set α := aliasRegName (regName Γ.length) out with hα
  set ρ := certRho Γ.length (regName Γ.length) out (certSlots update) with hρ
  set X := loopNode update count init invs (fun _ => none) ++ [⟨0, .Lret⟩] with hX
  have hfold : AliasInv Γ.length out (certSlots update)
      ((renLcmd α X).foldl aliasStepL []) := by
    have hw := foldl_aliasStepL_walk hσ out update (invTys.length + 2) (accRegMN invTys) [] []
      (aliasInv_nil _ _) (Or.inl rfl) hhead
    rw [hX, hnode, forLoopLcmdNRt_unfold]
    dsimp only
    simp only [List.append_assoc, renLcmd]
    rw [foldl_aliasStepL_sandwich]
    · simpa [Nat.add_comm, renLcmd] using hw
    · intro i hi; simp at hi; rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [srcsOf, isArrIdx]
    · intro i hi
      simp at hi
      rcases hi with ⟨-, rfl⟩ | rfl | rfl | ⟨a, -, rfl⟩ | rfl | rfl | rfl | rfl <;>
        simp [srcsOf, isArrIdx]
  have hX1 : (X.map Linstr.li_i).map (renLinstrR ρ)
      = (certNode update invs out c).map Prod.fst ++ [.Lret] := by
    rw [certNode_wire, hX, hnode, List.map_append, List.map_append]
    rfl
  obtain ⟨hget, hemp⟩ := arrChainAlias_spec (renLcmd α X)
  rw [hb, aliasRegBody_eq_renLcmd, canonicalizeMemrefThread_eq_renLcmd, List.map_append,
    List.append_assoc, ← hX1]
  congr 1
  split
  · next he =>
      have hS : certSlots update = [] := by
        rw [hemp, hfold.2] at he
        simpa using he
      have hαρ : α = ρ := by
        funext r
        rw [hα, hρ, hS]
        simp [certRho, aliasRegName]
      rw [renLcmd_wire, ← hα, hαρ]
  · rw [renLcmd_wire, renLcmd_wire, List.map_map]
    refine List.map_congr_left (fun i _ => ?_)
    rw [Function.comp_apply, renLinstrR_comp]
    congr 1
    funext r
    show canonMemrefName (arrChainAlias (renLcmd α X)) (α r) = ρ r
    unfold canonMemrefName
    rw [hget]
    show lookupD _ _ = _
    rw [hfold.1]
    by_cases hr : r = regName Γ.length
    · rw [hr]
      have h1 : α (regName Γ.length) = out := by rw [hα]; simp [aliasRegName]
      rw [h1, hρ, certRho_acc]
      split <;> rfl
    · have hαr : α r = r := by
        rw [hα]
        unfold aliasRegName
        rw [ite_eq_right (by simpa using hr)]
      rw [hαr, hρ]
      unfold certRho
      have hiff : r ∈ (certSlots update).map (loopReg Γ.length)
          ↔ (r == regName Γ.length
              || (certSlots update).any fun k => r == loopReg Γ.length k) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq, hr, false_or, List.any_eq_true,
          List.mem_map]
        constructor <;> rintro ⟨k, hk, h⟩ <;> exact ⟨k, hk, h.symm⟩
      by_cases hm : r ∈ (certSlots update).map (loopReg Γ.length)
      · rw [ite_eq_left hm, ite_eq_left (hiff.mp hm)]
      · rw [ite_eq_right hm, ite_eq_right (mt hiff.mpr hm)]

/-! ## 5. The check without the body equation -/

section Check

variable {Γ : Ctxt jasminDialect} {w n : Nat} {invTys : Ctxt jasminDialect}

/-- **The check of a single-loop export, without the body equation.** The seed and the
    count resolve to registers `out` and `c`, the loop node passes `exportCertB`, and the
    stores of the model chain read the thread head. -/
def loopCertNB (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) : Bool :=
  match resolveVar Γ.length Γ.length argName (fun _ => none) init,
      resolveVar Γ.length Γ.length argName (fun _ => none) count with
  | .reg out, .reg c =>
      exportCertB Γ.length (regName Γ.length) out c update (loopInvOps invs)
      && storeOnHeadB (certChain update) (accRegMN invTys)
  | _, _ => false

/-- **The body equation of `loopCertB` is a lemma.** A program that passes `loopCertNB`
    passes `loopCertB` at every argument naming. -/
theorem loopCertB_of_loopCertNB {update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n)}
    {count : Ctxt.Var Γ (JasminTy.reg 64)} {init : Ctxt.Var Γ (JasminTy.stackArr w n)}
    {invs : HVector (fun ty => Ctxt.Var Γ ty) invTys}
    (h : loopCertNB update count init invs = true) (outArg : String)
    (inArgs abiArgs : List String) :
    loopCertB update count init invs outArg inArgs abiArgs = true := by
  unfold loopCertNB at h
  split at h
  · next out c hi hc =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨hx, hs⟩ := h
      have hlen := (exportCertB_sound hx).loopRen.len
      unfold loopCertB
      simp only [hi, hc, hx, Bool.true_and,
        abiBody1_singleLoop_certNode update count init invs outArg inArgs abiArgs hi hc hlen hs,
        beq_self_eq_true]
  · cases h

end Check

/-- The check without the body equation on a looped program: `loopCertNB` on a runtime-count
    loop node over an array accumulator followed by a return, `false` on every other
    program. -/
def comLCertNB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | _, _, @ComL.forLoopNRt _ (.stackArr _ _) _ _ update count init invs (.ret _) =>
      loopCertNB update count init invs
  | _, _, _ => false

/-- A looped program that passes `comLCertNB` passes `comLCertB` at every argument naming. -/
theorem comLCertB_of_comLCertNB {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (h : comLCertNB c = true) (outArg : String) (inArgs abiArgs : List String) :
    comLCertB c outArg inArgs abiArgs = true := by
  unfold comLCertNB at h
  split at h
  · exact loopCertB_of_loopCertNB h outArg inArgs abiArgs
  · cases h

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoopBody
