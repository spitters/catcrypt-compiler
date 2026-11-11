/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomHiTemplate
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFuseSites
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomCoalesceShape

/-!
# Stage `G10` on the sum and the difference of the field domain

On a member of the field domain whose method is the sum or the difference, the program the
export receives binds no high word `mulhi` of a widening multiplication: the translation binds
one call of the tagged head, the field dialect step replaces it by the lowered body, which binds
no `mulhi` (`fieldBodyD_addSub_hi`), and the later passes bind no new `mulhi`: the select
lowering and the range stage rewrite a binding to itself, a register constant or register
arithmetic, the rules of the e-graph pass emit register constants, register arithmetic and
variables, the widening widens an operation that is not `mulhi` to a block without `mulhi`,
and mask elimination, dead-binding elimination and the carry pairs keep or rename bindings and
insert carry-chain data bindings. The export emits for a binding an instruction whose mnemonic
is that of its operation, and only `mulhi` has the mnemonic `MULXHI`. So the export has no
instruction under `MULXHI` (`ExportHiFree`), and the gate does not refuse at `fuseOKL`.

## Main definitions

* `fieldMethodI`: the method of the tagged head of a field expression.
* `FieldAddSub`: the field expression is a sum or a difference.

## Main results

* `isMulHiMnem_withWidthTag`: a width-tagged mnemonic other than `MULXHI` is no `MULXHI`.
* `hiFree_bindOps`, `hiFree_exportR`: the export of a program of bindings of `opMemB` other
  than `mulhi` has no instruction under `MULXHI`.
* `allOps_lowerSel_hi`, `allOps_carriedGo_hi`, `jasminRules_hi`: the steps after the field
  dialect step bind no new `mulhi`.
* `allOps_narrowPrep_hi`: neither do the narrow-word stages.
* `fieldDom_chain_hi`: the output of the chain on a sum or a difference binds no `mulhi`.
* `exportHiFree_addSub`: `ExportHiFree` on the sum and the difference.
* `fieldDom_fuseOKL_addSub`: the stage `G10` on the sum and the difference.
* `p256Add_fieldAddSub`, `p256Sub_fieldAddSub`: the sum and the difference at the P-256 base
  prime are sums and differences.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi (isMulHiMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open Ctxt (Var)

/-! ## 1. Mnemonics other than `MULXHI` -/

/-- A mnemonic that strips to `MULXHI` begins with `MULXHI`. -/
theorem prefix_of_isMulHiMnem {s : String} (h : isMulHiMnem s = true) :
    "MULXHI".toList <+: s.toList := by
  unfold isMulHiMnem stripWidthTag at h
  simp only [beq_iff_eq] at h
  split_ifs at h with h1 h2
  · have h3 := congrArg String.toList h
    rw [String.toList_ofList] at h3
    rw [← h3]
    exact List.takeWhile_prefix _
  · have h3 := congrArg String.toList h
    rw [String.toList_ofList] at h3
    rw [← h3]
    exact (List.dropLast_prefix _).trans ((List.dropLast_prefix _).trans (List.dropLast_prefix _))
  · rw [h]

/-- A mnemonic that begins with a list incomparable with `MULXHI` is no `MULXHI`. -/
theorem isMulHiMnem_false_of {s : String} (X r : List Char) (hs : s.toList = X ++ r)
    (h1 : ¬ "MULXHI".toList <+: X) (h2 : ¬ X <+: "MULXHI".toList) : isMulHiMnem s = false := by
  cases h : isMulHiMnem s
  · rfl
  · have hp := prefix_of_isMulHiMnem h
    rw [hs] at hp
    rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append X r) with h' | h'
    · exact absurd h' h1
    · exact absurd h' h2

/-- **A width-tagged mnemonic whose base begins with a list incomparable with `MULXHI` is no
    `MULXHI`.** -/
theorem isMulHiMnem_withWidthTag (w : Nat) {Y : String} (X r : List Char)
    (hY : Y.toList = X ++ r) (h1 : ¬ "MULXHI".toList <+: X) (h2 : ¬ X <+: "MULXHI".toList) :
    isMulHiMnem (withWidthTag w Y) = false := by
  unfold withWidthTag
  split
  · exact isMulHiMnem_false_of X (r ++ ":64".toList) (by simp [String.toList_append, hY]) h1 h2
  · exact isMulHiMnem_false_of X (r ++ ("^" ++ toString w).toList)
      (by simp [String.toList_append, hY]) h1 h2

/-- The width-tagged `MUL` is no `MULXHI`. -/
theorem isMulHiMnem_withWidthTag_MUL (w : Nat) :
    isMulHiMnem (withWidthTag w "MUL") = false := by
  unfold withWidthTag
  split
  · decide +kernel
  · exact isMulHiMnem_false_of ['M', 'U', 'L', '^'] (toString w).toList
      (by simp [String.toList_append]) (by decide) (by decide)

/-- An instruction with a mnemonic other than `MULXHI` is `HiFree`. -/
theorem hiFree_lopn {ds ss : List LOperand} {o : String} (h : isMulHiMnem o = false) :
    HiFree (.Lopn ds o ss) := by
  intro ds' o' ss' he
  cases he
  exact h

/-- **The instruction of an operation of `opMemB` other than `mulhi` is `HiFree`.** -/
theorem hiFree_opToLinstrR (op : JasminOp) (h1 : opMemB op = true) (h2 : noMulhiB op = true)
    (dst : String) (srcs : List LOperand) : HiFree (opToLinstrR op dst srcs) := by
  cases op <;> (try simp [opMemB, noMulhiB] at h1 h2)
  case regArith bop w =>
    refine hiFree_lopn ?_
    cases bop
    case mul => exact isMulHiMnem_withWidthTag_MUL w
    all_goals
      refine isMulHiMnem_withWidthTag w _ [] (List.append_nil _).symm ?_ ?_ <;> decide +kernel
  case select w =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['C', 'M', 'O', 'V'] [] (by simp)
      (by decide) (by decide))
  case stackLoad w n =>
    simp only [opToLinstrR]
    split <;> exact hiFree_lopn (by decide +kernel)
  case stackStore w n =>
    simp only [opToLinstrR]
    split <;> exact hiFree_lopn (by decide +kernel)
  case castW w w' =>
    simp only [opToLinstrR, castWMnem]
    split_ifs <;> exact hiFree_lopn (by decide +kernel)
  case regConst w n =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['M', 'O'] ['V'] (by simp) (by decide)
      (by decide))
  case addCarryLo w =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['A'] ['D', 'C', 'X'] (by simp) (by decide)
      (by decide))
  case addCarryHi w =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['A'] ['D', 'C', 'X', 'H', 'I'] (by simp)
      (by decide) (by decide))
  case rorImm w k =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['R'] _ (by simp [String.toList_append]; rfl)
      (by decide) (by decide))
  case shrImm w k =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['S'] _ (by simp [String.toList_append]; rfl)
      (by decide) (by decide))
  case sarImm w k =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['S'] _ (by simp [String.toList_append]; rfl)
      (by decide) (by decide))
  case shlImm w k =>
    exact hiFree_lopn (isMulHiMnem_withWidthTag w ['S'] _ (by simp [String.toList_append]; rfl)
      (by decide) (by decide))
  case cmp c w =>
    refine hiFree_lopn (isMulHiMnem_withWidthTag w ['S'] (cmpName c).toList.tail ?_ (by decide)
      (by decide))
    cases c <;> decide +kernel
  case cmpImm c w n =>
    refine hiFree_lopn (isMulHiMnem_withWidthTag w ['S'] (cmpName c).toList.tail ?_ (by decide)
      (by decide))
    cases c <;> decide +kernel
  case stackZero w n => exact hiFree_lopn (by decide +kernel)
  case stackStoreImm w n i => exact hiFree_lopn (by decide +kernel)

/-- A structured shift instruction is `HiFree`. -/
theorem hiFree_shiftLinstr (mnem : String) (c : Char) (r : List Char) (hm : mnem.toList = c :: r)
    (hc : c ≠ 'M') (w : Nat) (dst : String) (src : LOperand) (n : Nat) :
    HiFree (JasminLsemShift.shiftLinstr mnem w dst src n) := by
  refine hiFree_lopn (isMulHiMnem_withWidthTag (Y := mnem) w [c] r (by simp [hm]) ?_ ?_)
  · intro h
    exact hc (List.cons_prefix_cons.mp h).1.symm
  · intro h
    exact hc (List.cons_prefix_cons.mp h).1

/-- **The instruction the export emits for a binding of `opMemB` other than `mulhi` is
    `HiFree`.** -/
theorem hiFree_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) (h1 : opMemB e.op = true)
    (h2 : noMulhiB e.op = true) : ∀ i ∈ bindOps nArgs e d, HiFree i.1 := by
  intro i hi
  simp only [bindOps, JasminLsemMem.straightOpsMem, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  subst hi
  have hop := hiFree_opToLinstrR e.op h1 h2
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op at hop ⊢
  split
  all_goals first
    | exact hop _ _
    | (dsimp only
       first
       | exact hop _ _
       | split
       all_goals first
         | exact hop _ _
         | exact hiFree_shiftLinstr "SHR" 'S' ['H', 'R'] (by decide +kernel) (by decide) _ _ _ _
         | exact hiFree_shiftLinstr "SHL" 'S' ['H', 'L'] (by decide +kernel) (by decide) _ _ _ _
         | exact hiFree_shiftLinstr "SAR" 'S' ['A', 'R'] (by decide +kernel) (by decide) _ _ _ _)

/-- **The export of a program of bindings of `opMemB` other than `mulhi` has no instruction
    under `MULXHI`.** -/
theorem hiFree_exportR {nArgs : Nat} {fn : String} {I : LprogIsa.IsaData}
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hp : letsOnlyB p = true) (h1 : p.allOps opMemB = true) (h2 : p.allOps noMulhiB = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n I = some r → ∀ i ∈ r.code, HiFree i.1 := by
  induction p with
  | ret vs =>
      intro d n r hr
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      intro i hi
      exact nomatch hi
  | var e k ih =>
      intro d n r hr
      simp only [NFProg.allOps, Bool.and_eq_true] at h1 h2
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk, rfl⟩ := hr
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hiFree_bindOps nArgs e d h1.1 h2.1 i hi
      · exact ih hp h1.2 h2.2 _ _ _ hk i hi
  | forLoop => simp [letsOnlyB] at hp
  | ifThenElse => simp [letsOnlyB] at hp
  | whileLoop => simp [letsOnlyB] at hp
  | call => simp [letsOnlyB] at hp

/-! ## 2. The steps after the field dialect step -/

section Steps

open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.TraitRules
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (RulesOps altOpsB
  altOpsB_of_altConstB constFoldRule_altConst copyRule_altConst cmpOneAlts_altConst pointExpr_op)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (rangeExpr rangeRule ruleOp_op)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop (carriedGo)

/-- **The select lowering of a region-free program binds no new `mulhi`.** -/
theorem allOps_lowerSel_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ), regionFreeB p = true →
      p.allOps noMulhiB = true → (NFProg.lowerSel p ren).allOps noMulhiB = true := by
  induction p with
  | ret => intro _ _ _ _; rfl
  | var e k ih =>
      intro Δ ren hr hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [NFProg.lowerSel, NFProg.allOps, Bool.and_eq_true]
      exact ⟨hp.1, ih _ hr hp.2⟩
  | forLoop => intro _ _ hr; simp [regionFreeB] at hr
  | ifThenElse => intro _ _ hr; simp [regionFreeB] at hr
  | whileLoop => intro _ _ hr; simp [regionFreeB] at hr
  | call f args k ih =>
      intro Δ ren hr hp
      simp only [NFProg.lowerSel, NFProg.allOps] at hp ⊢
      exact ih _ hr hp

/-- **A binding of the range stage binds no new `mulhi`**: a point folds to a register
    constant, and a rule rewrites to register arithmetic. -/
theorem rangeExpr_hi {Γ : Ctxt jasminDialect} (A : _) (len : Nat) {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : noMulhiB e.op = true) :
    noMulhiB (rangeExpr A len e).op = true := by
  rcases e with ⟨op, rfl, args⟩
  unfold rangeExpr
  split
  · exact he
  split
  · rename_i e' h'
    obtain ⟨w, n, hop⟩ := pointExpr_op _ _ e' h'
    rw [hop]
    rfl
  · unfold rangeRule
    split
    · rename_i e' h'
      obtain ⟨bop, w, hop, -⟩ := ruleOp_op _ _ _ h'
      rw [hop]
      rfl
    · exact he

/-- **The traversal of the range stage binds no new `mulhi`.** -/
theorem allOps_carriedGo_hi : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (A : _)
    (len : Nat) (a : CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.CarriedAnn)
    (p : NFProg jasminDialect Γ ts), p.allOps noMulhiB = true →
    (carriedGo A len a p).allOps noMulhiB = true
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, A, len, _, .var e k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carriedGo, NFProg.allOps, Bool.and_eq_true]
      exact ⟨rangeExpr_hi A len e hp.1, allOps_carriedGo_hi _ _ _ k hp.2⟩
  | _, _, _, _, _, .forLoop _ _ body k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carriedGo, NFProg.allOps, allOps_carriedGo_hi _ _ _ body hp.1,
        allOps_carriedGo_hi _ _ _ k hp.2, Bool.and_self]
  | _, _, _, _, _, .ifThenElse _ thn els k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carriedGo, NFProg.allOps, allOps_carriedGo_hi _ _ _ thn hp.1.1,
        allOps_carriedGo_hi _ _ _ els hp.1.2, allOps_carriedGo_hi _ _ _ k hp.2, Bool.and_self]
  | _, _, _, _, _, .whileLoop _ body k, hp => by
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carriedGo, NFProg.allOps, allOps_carriedGo_hi _ _ _ body hp.1,
        allOps_carriedGo_hi _ _ _ k hp.2, Bool.and_self]
  | _, _, _, _, _, .call _ _ k, hp => by
      simp only [carriedGo, NFProg.allOps]
      exact allOps_carriedGo_hi _ _ _ k hp

/-- The alternatives of the arithmetic rules bind register constants and register
    arithmetic. -/
theorem ruleAlts_hi (D : Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : ∀ alt ∈ ruleAlts D e, altOpsB noMulhiB alt = true := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      intro alt halt
      simp only [ruleAlts, HVector.head, HVector.tail] at halt
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp halt
      cases t <;> simp [Term.toAlt, altOpsB, constE, CatCrypt.Crypto.Optimizer.Rewrite.Egraph.binE,
        noMulhiB]
  all_goals intro alt h; simp [ruleAlts] at h

/-- The alternatives of the Mersenne rule bind register arithmetic. -/
theorem mersenneAlts_hi (D : Defs) {Δ : Ctxt jasminDialect} {s : JasminTy}
    (e : Expr jasminDialect Δ s) : ∀ alt ∈ mersenneAlts D e, altOpsB noMulhiB alt = true := by
  intro alt halt
  unfold mersenneAlts at halt
  split at halt
  · rename_i w hop args
    subst hop
    have hm : ∀ (x : Ctxt.Var Δ (.reg w)) (c : BitVec w), ∀ alt ∈ mersenneAlt D x c,
        altOpsB noMulhiB alt = true := by
      intro x c alt ha
      unfold mersenneAlt at ha
      split at ha
      · split at ha
        · split at ha
          · obtain rfl := List.mem_singleton.mp ha
            simp [altOpsB, CatCrypt.Crypto.Optimizer.Rewrite.Egraph.binE, noMulhiB]
          · cases ha
        · cases ha
      · cases ha
    simp only [mersenneTerms, List.mem_append] at halt
    rcases halt with halt | halt
    · split at halt
      · exact hm _ _ alt halt
      · cases halt
    · split at halt
      · exact hm _ _ alt halt
      · cases halt
  · cases halt

/-- **The jasmin rule set binds no new `mulhi`.** -/
theorem jasminRules_hi : RulesOps jasminRules noMulhiB := by
  intro D Δ s e he alt ha
  have hC : ∀ e' : Expr jasminDialect Δ s, jasminConstLike e'.op = true →
      noMulhiB e'.op = true := by
    intro e' hc
    obtain ⟨op, _, _⟩ := e'
    cases op <;> first | rfl | exact absurd hc Bool.false_ne_true
  obtain ⟨r, hr, ha⟩ := List.mem_flatMap.mp ha
  simp only [jasminRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ruleAlts_hi D e alt ha
  · exact altOpsB_of_altConstB hC alt
      (constFoldRule_altConst _ jasminReify _ (fun _ h => h) D e alt ha)
  · exact altOpsB_of_altConstB hC alt (copyRule_altConst _ jasminCastCopy D e alt ha)
  · exact altOpsB_of_altConstB hC alt (cmpOneAlts_altConst _ D e alt ha)
  · exact mersenneAlts_hi D e alt ha

end Steps

/-! ## 3. The narrow-word stages -/

section Narrow

open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (op_rename?)

/-- The Jasmin expressions whose operation is not `mulhi`. -/
local notation "exprHi" => fun e => noMulhiB (Expr.op e) = true

/-- **The widened block of an operation other than `mulhi` binds no `mulhi`.** -/
theorem wideOpBlock?_hi {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    (hop : noMulhiB op = true)
    {blk : Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op))}
    (h : wideOpBlock? op args = some blk) : CoveredCom exprHi blk := by
  cases op <;> simp only [wideOpBlock?, reduceCtorEq] at h <;> (injection h with h; subst h) <;>
    (try simp only [noMulhiB, Bool.false_eq_true] at hop)
  case regArith bop w =>
    unfold arithBlock
    split
    · split <;> simp [withMask, countThen, CoveredCom, noMulhiB]
    · simp [CoveredCom, noMulhiB]
  case castW w w' =>
    unfold castBlock withMask
    split <;> simp [CoveredCom, noMulhiB]
  case addCarryLo w =>
    unfold addLoBlock
    split <;> simp [withMask, CoveredCom, noMulhiB]
  case addCarryHi w =>
    unfold addHiBlock
    split <;> simp [CoveredCom, noMulhiB]
  case rorImm w k =>
    unfold wideRorBlock
    split <;> simp [withMask, CoveredCom, noMulhiB]
  case sarImm w k =>
    unfold sarBlock
    split <;> simp [withMask, CoveredCom, noMulhiB]
  case shlImm w k =>
    unfold wideShlBlock
    split <;> simp [withMask, CoveredCom, noMulhiB]
  all_goals simp [CoveredCom, noMulhiB]

/-- **Mask elimination of a region-free program binds no new `mulhi`.** -/
theorem allOps_maskElimGo_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : Facts Γ) (ren : Ctxt.Hom Γ Δ), regionFreeB p = true →
      p.allOps noMulhiB = true → (maskElimGo p A ren).allOps noMulhiB = true := by
  induction p with
  | ret vs => intro Δ A ren _ _; rfl
  | var e k ih =>
      intro Δ A ren hr hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      obtain ⟨op, hop, args⟩ := e
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _ hr hp.2
        · simp only [NFProg.allOps, Bool.and_eq_true]
          exact ⟨hp.1, ih _ _ hr hp.2⟩
      · simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hp.1, ih _ _ hr hp.2⟩
  | forLoop => intro _ _ _ hr; simp [regionFreeB] at hr
  | ifThenElse => intro _ _ _ hr; simp [regionFreeB] at hr
  | whileLoop => intro _ _ _ hr; simp [regionFreeB] at hr
  | call f args k ih =>
      intro Δ A ren hr hp
      simp only [maskElimGo, NFProg.allOps] at hp ⊢
      exact ih _ _ hr hp

/-- **The carry pairs bind no new `mulhi`**: an inserted binding is a carry-chain data
    binding. -/
theorem allOps_carryPairGo_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ prev : Option (Nat × List Nat), p.allOps noMulhiB = true →
      (carryPairGo prev p).allOps noMulhiB = true := by
  induction p with
  | ret vs => intro prev _; rfl
  | var e k ih =>
      intro prev hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      unfold carryPairGo
      split
      · split
        · simp only [NFProg.allOps, Bool.and_eq_true]
          exact ⟨rfl, ih _ hp.2⟩
        · unfold carryInsert
          split
          · rename_i e' k' he hk
            simp only [NFProg.allOps, Bool.and_eq_true]
            refine ⟨rfl, ?_, ?_⟩
            · rw [op_rename? he]
              rfl
            · rw [FieldInlineOps.allOps_rename? _ _ _ hk]
              exact ih _ hp.2
          · simp only [NFProg.allOps, Bool.and_eq_true]
            exact ⟨rfl, ih _ hp.2⟩
      · simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hp.1, ih _ hp.2⟩
  | forLoop _ _ _ _ ihb ihk =>
      intro prev hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carryPairGo, NFProg.allOps, ihb _ hp.1, ihk _ hp.2, Bool.and_self]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro prev hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carryPairGo, NFProg.allOps, iht _ hp.1.1, ihe _ hp.1.2, ihk _ hp.2,
        Bool.and_self]
  | whileLoop _ _ _ ihb ihk =>
      intro prev hp
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      simp only [carryPairGo, NFProg.allOps, ihb _ hp.1, ihk _ hp.2, Bool.and_self]
  | call fn args k ih =>
      intro prev hp
      simp only [carryPairGo, NFProg.allOps] at hp ⊢
      exact ih _ hp

/-- **The narrow-word stages of a region-free program bind no new `mulhi`.** -/
theorem allOps_narrowPrep_hi {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hr : regionFreeB p = true) (hp : p.allOps noMulhiB = true) (hq : narrowPrep p = some q) :
    q.allOps noMulhiB = true := by
  obtain ⟨q₀, h₀, rfl⟩ := narrowPrep_eq_some.mp hq
  have hw : q₀.allOps noMulhiB = true :=
    JasminImageOps.allOps_map? widenP widenP_regionTypes noMulhiB p
      (NFProg.Covered.mono (fun e he blk hb => by
          obtain ⟨op, rfl, args⟩ := e
          exact wideOpBlock?_hi op args he hb)
        (JasminImageOps.covered_of_allOps noMulhiB p hp)) _ q₀ h₀
  have hw' : regionFreeB q₀ = true := regionFreeB_map? widenP widenP_regionTypes p hr _ h₀
  refine allOps_carryPairGo_hi _ _ ?_
  refine FieldDialectStep.allOps_dce _ _ ?_
  exact allOps_maskElimGo_hi _ _ _ hw' hw

end Narrow

/-! ## 4. The chain on the sum and the difference -/

section Chain

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.Hax.ImpToNF (entryEnv NfEnv)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)
open CatCrypt.Crypto.Hax.NFToCat (quietCall TRd catOp)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat (catRules)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (WideTemplate wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps (callsLoopsAll)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses (lowerSelectsStep aegraphStep)
open CatCrypt.Crypto.Optimizer.Rewrite.RangeAnnSyn (synRangeStep)
open CatCrypt.Crypto.Optimizer.Rewrite.Aegraph (jasminRules)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Hax.NFToCat (catTy nfToCatExt nfToCatExt_calls)

/-- **The translation of a member of the field domain binds the call of its head and returns
    it**, and the head is that of the erased expression. -/
theorem fieldDom_haxToNF_opRet_erase {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true)
    {T : NfTy} {p0 : NFProg nfDialect (CatCrypt.Crypto.Hax.ImpToNF.entryCtx (abiEntry σ)) [T]}
    (hp : haxToNF σ (HaxModule.single e) = some ⟨T, p0⟩) :
    ∃ m p, fieldTag? (fieldHead m p) = some (m, p) ∧ 2 ^ 64 ≤ p ∧
      (FieldWideInline.wideTemplateOf p).isSome = true ∧
      T = NfTy.arr (fieldLimbs p) (.word 64) ∧
      OpRet (NfOp.named "t" (.call (fieldHead m p)
        [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
        (NfTy.arr (fieldLimbs p) (.word 64)))) p0 ∧
      ∃ k, e.erase = fieldLit m p k := by
  unfold fieldDomB at h
  split at h
  · rename_i k n hkn
    obtain ⟨m, p, hm, h64, hok, ht, rfl, he⟩ := fieldDomE_tag hkn
    have hW : (FieldWideInline.wideTemplateOf p).isSome = true := by
      have hok' := hok
      simp only [CatCrypt.Crypto.Hax.ImpToNF.fieldModOk, CatCrypt.Crypto.Hax.ImpToNF.fieldNarrowOk,
        Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true]
        at hok'
      rcases hok' with ⟨⟨-, hodd⟩, hn⟩ | ⟨_, -, ⟨⟨-, hle⟩, -⟩⟩
      · obtain ⟨W, hW⟩ := FieldWideInline.wideTemplateOf_isSome h64 hodd hn
        simp [hW]
      · omega
    simp only [fieldAbiB, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨hargs, hc⟩, -⟩, -⟩, -⟩, -⟩ := h
    have hfr := fieldLit_front m p k
    have hsh : CatCrypt.Crypto.Hax.haxFrontShapeOk e = true := by
      rw [CatCrypt.Crypto.Hax.haxFrontShapeOk, he]
      exact hfr.1
    have hbody : nfBody e = fieldLit m p k := by
      rw [nfBody, he]
      exact hfr.2
    have hbin : m.binary = true := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | h <;>
        first | rfl | cases h
    have hsig := hax64SigOf_fieldHead hbin h64 hok ht
    have hk : k = 2 ∨ k = 1 := by
      simp only [fieldMethods, List.mem_cons, Prod.mk.injEq, List.not_mem_nil] at hm
      grind
    have hI : ∃ o, CatCrypt.Crypto.Hax.ImpToNF.impToNF CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf
        none (entryEnv (abiEntry σ)) (fieldLit m p k) = some o ∧
        OpRet (NfOp.named "t" (.call (fieldHead m p)
          [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
          (NfTy.arr (fieldLimbs p) (.word 64)))) o.prog := by
      rcases hk with rfl | rfl
      · rw [abiEntry_fieldAbi_two hargs]
        exact impToNF_letCall_opRet (entryEnv _) (fieldHead m p) "y" _ Var.here Var.here.there
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
      · rw [abiEntry_fieldAbi_one hargs]
        exact impToNF_letCall_opRet (entryEnv _) (fieldHead m p) "x" _ Var.here Var.here
          (by simp [entryEnv_lookup_cons]) (by simp [entryEnv_lookup_cons])
          (fieldHead_ne_repeat m p) hsig
    obtain ⟨o, ho, hop⟩ := hI
    have hot : o.t = NfTy.arr (fieldLimbs p) (.word 64) := by
      obtain ⟨h1, -, -⟩ := hop
      exact h1.symm
    have hp' : haxToNF σ (HaxModule.single e) = some ⟨o.t, o.prog⟩ := by
      rw [haxToNF_single, hc, bindConsts_nil]
      simp [nfSrcProg, hsh, hbody, ho, hot, entryResOk, outTyB]
    rw [hp] at hp'
    simp only [Option.some.injEq, Sigma.mk.injEq] at hp'
    obtain ⟨rfl, hq⟩ := hp'
    cases hq
    exact ⟨m, p, ht, h64, hW, hot, hop, k, he⟩
  · cases h

/-- One call returned is region-free. -/
theorem regionFreeB_of_callRet {f : String} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : CallRet f p) : regionFreeB p = true := by
  obtain ⟨as, args, rfl⟩ := h
  rfl

/-- **The field dialect step takes one call of a tagged head of the sum or the difference at a
    modulus without a narrow representation and with a wide template, returned, to a program
    that binds no `mulhi`.** -/
theorem fieldDialectStep_addSub_hi {f : String} {m : FieldMethod} {p : Nat}
    {W : WideTemplate p (fieldLimbs p)} (ht : fieldTag? f = some (m, p)) (hm : AddSubM m)
    (hn : narrowFieldOf p = none) (hw : wideTemplateOf p = some W) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p₀ q : NFProg jasminDialect Γ [t]} (hp : CallRet f p₀)
    (hq : (FieldDialectStep.fieldDialectStep Γ [t]).run p₀ = some q) :
    q.allOps noMulhiB = true := by
  obtain ⟨as, args, rfl⟩ := hp
  have hf := _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? ht
  change (if fieldFree (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) then
      some (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil))) else
    (NFProg.inline? FieldDialectStep.fieldLibD
      (NFProg.call (rs := [t]) f args (.ret (.cons .here .nil)))).bind fun q =>
        if fieldFree q then some q else none) = some q at hq
  simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hq
  obtain ⟨q0, hq0, hif⟩ := Option.bind_eq_some_iff.mp hq
  simp only [NFProg.inline?, Option.bind_some] at hq0
  split at hq0
  · rename_i b hb
    have hbl := fieldBodyD_addSub_hi ht hm hn hw hb
    split at hif
    · cases hif
      exact FieldInlineOps.allOps_seq? noMulhiB b _ _ _ hq0 hbl rfl
    · cases hif
  · cases hq0
    simp only [fieldFree, hf, Bool.not_true, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte] at hif
    cases hif

theorem extChain_addSub_hi {Γ : Ctxt nfDialect} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? (fieldHead m p) = some (m, p)) (h64 : 2 ^ 64 ≤ p)
    (hW : (wideTemplateOf p).isSome = true) (hM : AddSubM m)
    {p₀ : NFProg nfDialect Γ [NfTy.arr (fieldLimbs p) (.word 64)]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]}
    (h : (extChain [] Γ (NfTy.arr (fieldLimbs p) (.word 64))).run p₀ = some q)
    (hp : opsNB wideOpB p₀ = true)
    (hs : OpRet (NfOp.named "t" (.call (fieldHead m p)
      [NfTy.arr (fieldLimbs p) (.word 64), NfTy.arr (fieldLimbs p) (.word 64)]
      (NfTy.arr (fieldLimbs p) (.word 64)))) p₀) : q.allOps noMulhiB = true := by
  obtain ⟨W, hw⟩ := Option.isSome_iff_exists.mp hW
  have hn : narrowFieldOf p = none := by
    cases hN : narrowFieldOf p with
    | none => rfl
    | some F =>
        have := (narrowFieldOf_spec hN).2.1
        omega
  have htag : (fieldTag? (fieldHead m p)).isSome = true := by rw [ht]; rfl
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p₀) = some p0 at hp0
  cases hp0
  change flatSame (NFProg.abortElim NfOp.isAbort p₀) = some p1 at hp1
  change (if outTyB (NfTy.arr (fieldLimbs p) (.word 64)) then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor [] p3) p3 TRd.id = some r at hr
  have hp2' : p1 = p2 := by split at hp2 <;> cases hp2; rfl
  subst hp2'
  cases hp3; cases hr1; cases hj1
  have hab : NFProg.abortFree NfOp.isAbort p₀ = true :=
    FrontComplete.abortFree_of_opsNB (fun o ho => by
      simp only [wideOpB, Bool.and_eq_true, Bool.not_eq_true'] at ho
      exact ho.1) p₀ hp
  rw [NFProg.abortElim_of_abortFree _ p₀ hab] at hp1
  -- the montify pass is the identity, as in `extChain_callFree_of_wide`
  have hf : opsNB (fun o => !NFFlattenTuples.opIsTuple o && wideOpB o) p1 = true :=
    FrontComplete.opsNB_flatSame (W := fun _ => false) (fun _ h => h) hp1
      (FrontComplete.opsNB_mono_loop (fun o h => by simp [h]) (fun _ h => h) _ hp)
  have hd : opsNB wideOpB p1.dce = true :=
    FrontComplete.opsNB_dce _ (FrontComplete.opsNB_mono_loop
      (fun o h => by simp only [Bool.and_eq_true] at h; exact h.2) (fun _ h => h) _ hf)
  have hD : ∀ d ∈ fieldDeclsFor [] p1.dce, wideTagB d.name = true := by
    intro d hd'
    simp only [fieldDeclsFor, List.filter_nil, List.nil_append] at hd'
    exact fieldDeclsOf_wide _ hd d hd'
  have h0 : callsLoopsAll (fun f _ _ => wideTagB f) (fun _ => true) r = true :=
    ExportChainOps.callsLoopsAll_of_loops _ _ r (ExportChainOps.callsLoopsAll_true r)
      fun f as rs hc => by
        obtain ⟨d, hd', rfl, -⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
        exact hD d hd'
  have h1 := (ExportChainOps.callsLoopsAll_nfGo (d := CatCryptDialect.catCryptDialect) _ _
    catRules (Ctxt.Hom.id _) (∅, ∅) r).trans h0
  have h2 := ExportChainOps.callsLoopsAll_map? catToJasmin catToJasmin_regionTypes
    (fun f _ _ => wideTagB f) (fun _ => true) _ h1 _ hj
  have hm := montifyPass_of_wideTag (Γ := mapCtx (List.map catTy Γ))
    (ts := [mapTy (catTy (NfTy.arr (fieldLimbs p) (.word 64)))]) j h2
  rw [hm] at hj2
  -- the shape through the steps
  obtain ⟨hh, args, hpe⟩ := hs
  rw [hpe] at hp1
  have g1 := flatSame_callRet hp1
  have g2 := nfToCatExt_callRet _ htag (dce_opRet g1) hr
  have g3 := map?_catToJasmin_callRet (aegraphOptNF_callRet g2) _ hj
  have g4 := fieldDialectStep_addSub_hi ht hM hn hw g3 hj2
  have r4 := fieldDialectStep_regionFreeB (regionFreeB_of_callRet g3) hj2
  cases hj3; cases hj4; cases hj5
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.loopRange
  exact ExportChainOps.allOps_nfGo jasminRules _ jasminRules_hi _ _ _
    (allOps_carriedGo_hi _ _ _ _ (allOps_lowerSel_hi _ _ r4 g4))


end Chain

/-! ## 5. The stage on the sum and the difference -/

section Stage

open CatCrypt.Crypto.Hax (HaxModule)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag?)

/-- **The method of the tagged head of a field expression**: the method of the tag of the head
    of the bound call, `none` on every other expression. -/
def fieldMethodI : _root_.Hax.ImpExpr → Option FieldMethod
  | .letBind _ (.app f _) _ => (fieldTag? f).map Prod.fst
  | _ => none

/-- **The field expression is a sum or a difference**: the method of its tagged head is the
    sum or the difference. -/
def FieldAddSub (e : _root_.Hax.TExpr) : Prop :=
  ∃ m, AddSubM m ∧ fieldMethodI e.erase = some m

/-- The method of the literal of a tagged call is its method. -/
theorem addSubM_of_erase {e : _root_.Hax.TExpr} (hA : FieldAddSub e) {m : FieldMethod}
    {p k : Nat} (ht : fieldTag? (fieldHead m p) = some (m, p)) (he : e.erase = fieldLit m p k) :
    AddSubM m := by
  obtain ⟨m', hm', h'⟩ := hA
  rw [he] at h'
  simp only [fieldLit, fieldMethodI, ht, Option.map_some, Option.some.injEq] at h'
  rw [h']
  exact hm'

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- **The output of the chain on a sum or a difference of the field domain binds no
    `mulhi`.** -/
theorem fieldDom_chain_hi {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hA : FieldAddSub e) (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) :
    q.allOps noMulhiB = true := by
  obtain ⟨T, p0, hp, hops⟩ := fieldDom_haxToNF h
  obtain ⟨m, p, ht, h64, hW, hT, hs, k, he⟩ := fieldDom_haxToNF_opRet_erase h hp
  have hM : AddSubM m := addSubM_of_erase hA ht he
  subst hT
  simp only [NFEntry.chainNF, haxEntry, hp, Option.bind_some, Option.map_eq_some_iff] at hq
  obtain ⟨q', hq', heq⟩ := hq
  cases heq
  rw [linkedDecls_single] at hq'
  exact extChain_addSub_hi ht h64 hW hM hq' hops hs

/-- **`ExportHiFree` on the sum and the difference**: the program the export receives binds
    no `mulhi` and binds operations of `opMemB` only, and is built of bindings only, so its
    export has no instruction under `MULXHI`. -/
theorem exportHiFree_addSub (h : fieldDomB e σ = true) (hA : FieldAddSub e) :
    ExportHiFree e σ fname := by
  intro t0 q q' r0 hq hq' hr0
  have hE0 : regionExportableB q = true := fieldDom_exportable (fieldDom_refusal h) hq
  obtain ⟨q'', hq'', hE1⟩ := NarrowWords.narrowPrep_of_exportable q hE0
  rw [hq'] at hq''
  cases hq''
  have hEx : regionExportableB (legalizeRegion q') = true := fieldDom_legalize hE1
  rw [ExportComplete.regionExportableB_eq] at hEx
  simp only [Bool.and_eq_true] at hEx
  have hHi : q'.allOps noMulhiB = true :=
    allOps_narrowPrep_hi (fieldDom_chain_regionFreeB h hq) (fieldDom_chain_hi h hA hq) hq'
  exact hiFree_exportR (legalizeRegion q') (fieldLetsOnly h t0 q q' hq hq') hEx.1.1 hHi _ _ _ hr0

/-- **Stage `G10` on the sum and the difference of the field domain**: the parts have no
    fusion site, so the gate does not refuse at `fuseOKL`. -/
theorem fieldDom_fuseOKL_addSub (h : fieldDomB e σ = true) (hA : FieldAddSub e)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseOKL" :=
  fieldDom_fuseOKL_of_hiFree h hB (exportHiFree_addSub h hA)

/-- The sum at the P-256 base prime is a sum. -/
theorem p256Add_fieldAddSub : FieldAddSub LeanFrontFields.p256AddTE :=
  ⟨.add, Or.inl rfl, by decide +kernel⟩

/-- The difference at the P-256 base prime is a difference. -/
theorem p256Sub_fieldAddSub : FieldAddSub LeanFrontFields.p256SubTE :=
  ⟨.sub, Or.inr rfl, by decide +kernel⟩

end Stage

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
