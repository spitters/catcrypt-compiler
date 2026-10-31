/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImg

/-!
# The array operands of the allocator input of the region route

`RegionPhysImg.physImgB_regionExport` takes two hypotheses on the allocator input body
`regionAllocBody a Γ.length ts r` of the region route: the indexed accesses are at array
parameters with a save slot (`hacc`), and no compile-time array operand names a `qsave.` slot
(`harr`). This module proves that the allocator input body has no compile-time array operand
at all (`NoCArr`), which gives `harr`.

The export `exportR` builds its operations from `opToLinstrR` over register sources, the frame
moves over register and immediate operands and the array moves over indexed operands; none of
them is a compile-time array element `.arr b k` (`exportR_noCArr`). The steps from the export
to the allocator input, the renaming of the array positions `renArr`, the removal of the
self-moves, the liveness instructions `LIVEPIN`, the result copy and the renaming of the
memref threads `canonicalizeMemrefThread`, introduce no such operand
(`noCArr_regionAllocBody`).

For `hacc`, the accesses of the allocator input body have the form `AccP P` at a predicate `P`
on array names (`accP_regionAllocBody`) when the code given to the renaming has the access
forms `AccCode` and `ImmCode` and its coalescing renaming sends the array names of every
instruction (`RootIn`) into `P`: the renaming of the array positions renames those names
(`accP_renArr`), and the renaming of the memref threads keeps `P`
(`canonMemrefName_arrChainAlias_of`, `accP_canonicalizeMemrefThread`). At the array names of
the parameters with a save slot, `AccP` gives `AccArg` (`accArg_of_accP`).

The conditions on the code given to the renaming hold for the programs of the region
route. The access form holds when every `stackLoad`, `stackStore`, carried array and
branch-result array is of `64`-bit words (`arrW64B`): the only operations exported with the
mnemonic `LOADIDX` or `STOREIDX` are `stackLoad` and `stackStore` (`plainIdx_opToLinstrR`),
and the frames add only the array moves `arrMove`; a `stackZero` exports a `ZEROARR` and a
`stackStoreImm` an `STOREIMM` of the form `ImmCode` (`exportR_immCode_copy`). The array names
(`RootIn`: the indexed bases, the register base of an `STOREIMM` and the destination of a
`ZEROARR`) go to parameters when every zeroing zeroes the result root (`ZeroAtRoot`): along
the export every indexed base is a name of an array variable in scope or the destination of
an earlier store or zeroing (`IdxOk`, `exportR_idxOk`), the array variables of the context of
the direct route are word-array parameters (`arrNamed_nfCtx`), the alias table sends every
array name to a parameter or to the result root (`canonMemrefName_aliasTab_of_idxOk`), and the
alias table with the result alias sends the result root to the result buffer.

## Main results

* `noCArr_opToLinstrR`: an operation over sources that are no compile-time array elements
  has none.
* `exportR_noCArr`: no instruction of the export of a program without `call` has a
  compile-time array operand.
* `noCArr_regionAllocBody`: no instruction of the allocator input body has one.
* `harr_regionAllocBody`: the hypothesis `harr` of `physImgB_regionExport`.
* `accP_regionAllocBody`: the access form of the allocator input body from the access form
  of the code given to the renaming and the bases its renaming yields.
* `physImgB_regionExport_param`: `physImgB_regionExport` with `harr` discharged and `hacc`
  reduced to those two conditions on the code given to the renaming.
* `plainIdx_opToLinstrR`: no operation other than `stackLoad` and `stackStore` exports with
  the mnemonic `LOADIDX` or `STOREIDX` or with an indexed operand.
* `exportR_accCode_copy`: the hypothesis `hC`, under `arrW64B`.
* `exportR_immCode_copy`: the hypothesis `hI`.
* `exportR_untagP_copy`: the hypothesis `hU`, every access mnemonic of the code untagged.
* `exportR_aliasRoots`: the hypothesis `hroot`, under `ZeroAtRoot` and `wordsSlotB`.
* `zeroAtRoot_of_noArrInitB`: a program without `stackZero` and `stackStoreImm` satisfies
  `ZeroAtRoot`.
* `physImgB_regionExport_words`: `physImgB_regionExport_param` with both hypotheses
  discharged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (operandName resolveVar_isReg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data x86Data_loopGuard
  x86Data_zeroTripGuard)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeak (NoCArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renZero renStoreImm renCallW renOpA renOpR)
open RegionAllocMapAlign RegionAllocMapDom

/-! ## 1. Operands and operations -/

/-- An operand that is no compile-time array element. -/
def NoArrOp (o : LOperand) : Prop := ∀ b k, o ≠ .arr b k

theorem noArrOp_reg (x : String) : NoArrOp (.reg x) := fun _ _ e => by cases e

theorem noArrOp_imm (k : Nat) : NoArrOp (.imm k) := fun _ _ e => by cases e

theorem noArrOp_arrIdx (b x : String) (s : Nat) : NoArrOp (.arrIdx b x s) :=
  fun _ _ e => by cases e

theorem noArrOp_of_isReg {o : LOperand} (h : o = .reg (operandName o)) : NoArrOp o := by
  rw [h]; exact noArrOp_reg _

theorem noCArr_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ x ∈ ds ++ ss, NoArrOp x) : NoCArr (.Lopn ds o ss) := h

theorem noCArr_movI (dst : String) {src : LOperand} (h : NoArrOp src) :
    NoCArr (movI dst src).1 := by
  refine noCArr_lopn fun x hx => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact noArrOp_reg _
  · exact h

theorem noCArr_movImmI (dst : String) (k : Nat) : NoCArr (movImmI dst k).1 :=
  noCArr_movI dst (noArrOp_imm k)

theorem noCArr_of_not_lopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : NoCArr w := by
  cases w with
  | Lopn ds o ss => exact absurd rfl (h ds o ss)
  | _ => trivial

/-- **An operation over sources that are no compile-time array elements has none.** -/
theorem noCArr_opToLinstrR (op : JasminOp) (dst : String) {srcs : List LOperand}
    (h : ∀ o ∈ srcs, NoArrOp o) : NoCArr (opToLinstrR op dst srcs) := by
  unfold NoArrOp at h
  cases op <;> simp only [opToLinstrR] <;> (repeat' split) <;>
    refine noCArr_lopn fun x hx b k he => ?_ <;> subst he <;> simp_all <;>
    first | exact h _ hx _ _ rfl | exact h _ _ hx.symm

/-! ## 2. The frames of the export -/

theorem noCArr_labelI (l : LLabel) : NoCArr (labelI l).1 := trivial

theorem noCArr_seedMoves (car : List String) {ops : List LOperand}
    (h : ∀ o ∈ ops, NoArrOp o) : ∀ i ∈ seedMoves car ops, NoCArr i.1 := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact noCArr_movI _ (h _ (List.of_mem_zip hp).2)

theorem noCArr_parMoves (D : Nat) (tgts : List String) {ops : List LOperand}
    (h : ∀ o ∈ ops, NoArrOp o) : ∀ i ∈ parMoves D tgts ops, NoCArr i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  · exact noCArr_movI _ (h _ (List.fst_mem_of_mem_zipIdx hp))
  · exact noCArr_movI _ (noArrOp_reg _)

theorem noCArr_parMoves_reg (D : Nat) (tgts : List String) (xs : List String) :
    ∀ i ∈ parMoves D tgts (xs.map LOperand.reg), NoCArr i.1 :=
  noCArr_parMoves D tgts fun o ho => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ho
    exact noArrOp_reg x

theorem noCArr_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, NoCArr i.1 := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> refine noCArr_lopn fun x hx b k he => ?_ <;> subst he <;>
    simp at hx

theorem noCArr_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, NoCArr i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact noCArr_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact noCArr_movI _ (noArrOp_reg _)

theorem noCArr_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, NoCArr i.1 := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact noCArr_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact noCArr_arrMoves _ _ _ i hi

theorem noCArr_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, NoCArr i.1 := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> refine noCArr_lopn fun x hx b k he => ?_ <;> subst he <;>
    simp at hx

theorem noCArr_flagWord (r z : String) {op : LOperand} (h : NoArrOp op) :
    ∀ i ∈ flagWord x86Data r z op, NoCArr i.1 := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact noCArr_movImmI _ _
    · exact noCArr_movImmI _ _
    · refine noCArr_lopn fun x hx b k he => ?_
      subst he
      simp at hx
  · rw [List.mem_singleton.mp hi]
    exact noCArr_movI _ h

theorem noCArr_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, NoCArr i.1) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, NoCArr i.1 := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine noCArr_lopn fun x hx b k he => ?_
      subst he
      simp at hx
    · trivial
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine noCArr_lopn fun x hx b k he => ?_
      subst he
      simp at hx
    · trivial

theorem noCArr_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, NoCArr i.1 := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact noCArr_movImmI _ _
      · exact noCArr_arrParMoves _ _ _ _ i hi
  · rw [show ((regPairs (ifResPairs rs d ops)).map fun p => LOperand.reg p.2) =
      ((regPairs (ifResPairs rs d ops)).map Prod.snd).map LOperand.reg by simp] at hi
    exact noCArr_parMoves_reg _ _ _ i hi

theorem forArrFrame_noCArr (d n : Nat) (cs : List JasminTy) (initOps : List LOperand)
    {countOp : LOperand} (hc : NoArrOp countOp) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, NoCArr i.1) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, NoCArr i.1 := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact noCArr_movImmI _ _
  · exact noCArr_typedMoves _ _ _ i hi
  · exact noCArr_seedMoves _ (fun o ho => by simp at ho; subst ho; exact hc) i hi
  · exact noCArr_x86Guards.1 _ n _ i hi
  · exact noCArr_labelI _
  · exact hb i hi
  · exact noCArr_movImmI _ _
  · exact noCArr_arrParMoves _ _ _ _ i hi
  · rw [show ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps)).map
        fun p => LOperand.reg p.2) = ((regPairs (carriedPairs cs
        (carriedRegs (d + 1) cs.length) bodyOps)).map Prod.snd).map LOperand.reg by simp] at hi
    exact noCArr_parMoves_reg _ _ _ i hi
  · exact noCArr_advanceOps _ _ i hi
  · exact noCArr_x86Guards.2 _ _ i hi
  · exact noCArr_labelI _
  · exact noCArr_movImmI _ _
  · exact noCArr_typedMoves _ _ _ i hi

theorem whileFrame_noCArr (d n nCar : Nat) {initOps : List LOperand}
    (hi0 : ∀ o ∈ initOps, NoArrOp o) (bodyC : List LinstrRM) {flagOp : LOperand}
    (hf : NoArrOp flagOp) {bodyOps : List LOperand} (hbo : ∀ o ∈ bodyOps, NoArrOp o)
    (bodyD : Nat) (hb : ∀ i ∈ bodyC, NoCArr i.1) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, NoCArr i.1 := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact noCArr_seedMoves _ hi0 i hi
  · exact noCArr_labelI _
  · exact hb i hi
  · exact noCArr_flagWord _ _ hf i hi
  · exact noCArr_parMoves _ _ hbo i hi
  · exact noCArr_x86Guards.2 _ _ i hi

theorem ifFrame_noCArr (fn : String) (d n : Nat) (rs : List JasminTy) {condOp : LOperand}
    (hc : NoArrOp condOp) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (ht : ∀ i ∈ thnC, NoCArr i.1) (he : ∀ i ∈ elsC, NoCArr i.1) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, NoCArr i.1 := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact noCArr_flagWord _ _ hc i hi
  · exact noCArr_x86Guards.1 _ n _ i hi
  · exact noCArr_labelI _
  · exact ht i hi
  · exact noCArr_ifResMoves _ _ _ _ i hi
  · exact noCArr_movImmI _ _
  · exact noCArr_x86Guards.2 _ _ i hi
  · exact noCArr_labelI _
  · exact he i hi
  · exact noCArr_ifResMoves _ _ _ _ i hi
  · exact noCArr_labelI _

theorem noCArr_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, NoCArr i.1 := by
  have hreg := JasminLsemExportTransfer.exprArgs_isReg (curDepth := d) (nArgs := nArgs) e
  have hp : ∀ o ∈ exprArgs d nArgs argName (fun _ => none) e, NoArrOp o := fun o ho => by
    obtain ⟨r, rfl⟩ := hreg o ho
    exact noArrOp_reg r
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  split <;> try exact noCArr_opToLinstrR _ _ hp
  split
  all_goals first
    | exact noCArr_opToLinstrR _ _ hp
    | (rename_i s hs
       refine noCArr_lopn fun x hx b k he => ?_
       subst he
       simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
         or_false] at hx
       rcases hx with hx | hx | hx
       · cases hx
       · exact hp _ (by rw [hs]; simp [hx]) b k rfl
       · cases hx)

/-- **No instruction of the export of a program without `call` has a compile-time array
    operand.** -/
theorem exportR_noCArr (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, NoCArr i.1 := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [NFProg.callFree] at hc
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact noCArr_bindOps nArgs e d i hi
      · exact ih hc _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_noCArr _ _ _ _ (noArrOp_of_isReg (resolveVar_isReg count)) _ _ _
          (ihb hc.1 _ _ _ hb) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_noCArr _ _ _ _ (noArrOp_of_isReg (resolveVar_isReg cond)) _ _ _ _ _ _
          (iht hc.1.1 _ _ _ ht) (ihe hc.1.2 _ _ _ he) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hres := exportR_res_isReg nArgs fn body _ _ b hb
      rcases List.mem_append.mp hi with hi | hi
      · refine whileFrame_noCArr _ _ _
          (fun o ho => noArrOp_of_isReg (exprArgsHV_isReg _ _ inits o ho)) _ ?_ ?_ _
          (ihb hc.1 _ _ _ hb) i hi
        · cases hr : b.res with
          | nil => exact noArrOp_imm 0
          | cons o os => exact noArrOp_of_isReg (hres o (by rw [hr]; simp))
        · intro o ho
          exact noArrOp_of_isReg (hres o (List.mem_of_mem_tail ho))
      · exact ihk hc.2 _ _ _ hk i hi
  | call f args k _ =>
      simp [NFProg.callFree] at hc

/-! ## 3. The steps to the allocator input -/

/-- The renaming of the array positions introduces no compile-time array operand. -/
theorem noCArr_renArr (ρ : String → String) {i : LinstrRM} (h : NoCArr i.1) :
    NoCArr (renArr ρ i).1 := by
  obtain ⟨w, tag⟩ := i
  have hA : ∀ o, NoArrOp o → NoArrOp (renOpA ρ o) := by
    intro o ho b k he
    cases o <;> simp only [renOpA, LOperand.arr.injEq, reduceCtorEq] at he
    exact ho _ _ rfl
  have hR : ∀ o, NoArrOp o → NoArrOp (renOpR ρ o) := by
    intro o ho b k he
    cases o <;> simp only [renOpR, reduceCtorEq] at he
    exact ho _ _ he
  unfold renArr
  split <;> simp only [renLoad, renStore, renZero, renStoreImm, renCallW]
  all_goals
    repeat' split
  all_goals first
    | exact h
    | (rename_i heq
       rw [LprogIsa.eq_callShadow_of_shadowCall? heq] at h
       simp only [LprogIsa.callShadow] at h ⊢
       intro x hx b k he
       subst he
       simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at hx
       rcases hx with hx | ⟨y, hy, hye⟩
       · cases hx
       · exact hR y (h y (by simp [hy])) b k hye)
    | (simp only [NoCArr, NoArrOp] at h hA hR ⊢
       simp_all)

/-- A liveness instruction reads registers only. -/
theorem noCArr_livepin (ns : List String) :
    NoCArr (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)) := by
  refine noCArr_lopn fun x hx b k he => ?_
  subst he
  simp at hx

theorem noCArr_livepin_range (m : Nat) :
    NoCArr (.Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range m).map fun j => (.reg (argName j) : LOperand))) := by
  rw [show ((List.range m).map fun j => (.reg (argName j) : LOperand)) =
    ((List.range m).map argName).map LOperand.reg by simp]
  exact noCArr_livepin _

theorem noCArr_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, NoCArr i.1) :
    ∀ i ∈ backEdgePins C, NoCArr i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, NoCArr i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact noCArr_livepin _
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

theorem noCArr_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, NoCArr i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact noCArr_movImmI _ _
      all_goals
        refine noCArr_lopn fun x hx b k he => ?_
        subst he
        simp at hx
    · cases hi
  · cases hi

/-- **The code given to the allocation has no compile-time array operand** when the code it
    is made of has none. -/
theorem noCArr_regionAllocCode {C : List LinstrRM} {rr : Option (String × String)}
    (h : ∀ i ∈ C, NoCArr i.1) : ∀ i ∈ regionAllocCode C [] rr, NoCArr i.1 := by
  refine noCArr_backEdgePins fun i hi => ?_
  rcases mem_pinSelfMoves hi with hi | ⟨t, a, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact noCArr_renArr _ (h j hj)
  · show NoCArr (.Lopn [.reg t] "LIVEPIN" [.reg a, .reg z])
    refine noCArr_lopn fun x hx => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact noArrOp_reg _
  · show NoCArr (.Lopn [.reg "%livepin"] "LIVEPIN" ([a, z, t].map LOperand.reg))
    exact noCArr_livepin [a, z, t]

theorem noCArr_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, NoCArr i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, NoCArr i.li_i := by
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      have hj' := h j hj
      rw [heq] at hj'
      refine noCArr_lopn fun x hx b k he => ?_
      subst he
      rw [← List.map_append] at hx
      obtain ⟨y, hy, hye⟩ := List.mem_map.mp hx
      cases y <;> simp only [canonMemrefOperand, reduceCtorEq] at hye
      exact hj' _ hy _ _ hye
    · exact h j hj

/-- **No instruction of the allocator input body has a compile-time array operand**, for a
    program without `call` whose export is `r`, at a result other than one register. -/
theorem noCArr_regionAllocBody (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r)
    (hts : ∀ w, ts ≠ [.reg w]) :
    ∀ i ∈ regionAllocBody a Γ.length ts r, NoCArr i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res),
      NoCArr i.1 := by
    refine noCArr_regionAllocCode fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · exact exportR_noCArr _ _ p hc _ _ r hr i hi
    · exact noCArr_regionLprogCopy a ts r.code r.res i hi
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact noCArr_livepin_range _
      · cases hi
    · refine noCArr_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact noCArr_livepin _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]; trivial

/-- **The hypothesis `harr` of `physImgB_regionExport`**: no compile-time array operand of the
    allocator input body names a `qsave.` slot, since it has none. -/
theorem harr_regionAllocBody (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r)
    (hts : ∀ w, ts ≠ [.reg w]) :
    ∀ i ∈ regionAllocBody a Γ.length ts r, ∀ q n,
      LOperand.arr q n ∈ lopnOperands i.li_i → hasPrefix q "qsave." = false := by
  intro i hi q n hq
  have h := noCArr_regionAllocBody a p hc hr hts i hi
  revert h hq
  cases i.li_i with
  | Lopn ds o ss => exact fun hq h => absurd rfl (h _ hq q n)
  | _ => exact fun hq _ => absurd hq (by simp [lopnOperands])

/-! ## 4. The indexed accesses of the allocator input -/

/-- Every base of the instruction has its name in `S`: the base of every indexed source, and
    the first register source of a constant-index store `STOREIMM`. -/
def IdxIn (S : String → Prop) (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss →
    (∀ b y s, LOperand.arrIdx b y s ∈ ss → S b) ∧
      (o = "STOREIMM" → ∀ b rest, ss = .reg b :: rest → S b)

/-- Every array name of the instruction that the image reloads has its name in `S`: the bases
    of `IdxIn` and the destination of a zeroing `ZEROARR`. -/
def RootIn (S : String → Prop) (i : LinstrRM) : Prop :=
  IdxIn S i ∧ ∀ z, X86Backend.ImageStraightRoute.zeroDst? i = some z → S z

/-- The mnemonic of an operation is untagged when its untagged form is one of `LOADIDX`,
    `STOREIDX`, `ZEROARR` and `STOREIMM` (`AccUntagged`). -/
def UntagP (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss → X86Backend.PhysImgEmit.AccUntagged o

theorem untagP_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : X86Backend.PhysImgEmit.AccUntagged o) : UntagP (.Lopn ds o ss) := by
  intro ds' o' ss' he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact h

theorem untagP_of_not_lopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : UntagP w :=
  fun _ _ _ e => absurd e (h _ _ _)

/-- A mnemonic without `^` is untagged. -/
theorem accUntagged_of_caret_free {o : String} (h : '^' ∉ o.toList) :
    X86Backend.PhysImgEmit.AccUntagged o := fun _ =>
  X86Backend.LprogAsmPrinter.untagCaret_of_caret_free h

/-- The width-stripped form of a mnemonic is a prefix of it. -/
theorem toList_stripWidthTag_prefix (o : String) : (stripWidthTag o).toList <+: o.toList := by
  unfold stripWidthTag
  split
  · simpa using List.takeWhile_prefix _
  · split
    · simp only [String.toList_ofList]
      exact ((List.dropLast_prefix _).trans (List.dropLast_prefix _)).trans
        (List.dropLast_prefix _)
    · exact List.prefix_refl _

/-- An array access mnemonic read by `untagCaret` from `o` is a prefix of `o`. -/
theorem untagCaret_acc_prefix {o b : String}
    (hu : X86Backend.LprogAsmPrinter.untagCaret o = b)
    (hb : b = "LOADIDX" ∨ b = "STOREIDX" ∨ b = "ZEROARR" ∨ b = "STOREIMM") :
    b.toList <+: o.toList := by
  unfold X86Backend.LprogAsmPrinter.untagCaret at hu
  split at hu
  · split at hu
    · exfalso
      have := congrArg (fun s => s.toList.getLast?) hu
      rcases hb with rfl | rfl | rfl | rfl <;> simp at this
    · rw [← hu]
      exact toList_stripWidthTag_prefix o
  · rw [← hu]

/-- A mnemonic whose first two characters are none of `LO`, `ST` and `ZE` is untagged. -/
theorem accUntagged_of_take {o : String}
    (h : o.toList.take 2 ≠ ['L', 'O'] ∧ o.toList.take 2 ≠ ['S', 'T'] ∧
      o.toList.take 2 ≠ ['Z', 'E']) : X86Backend.PhysImgEmit.AccUntagged o := by
  intro hb
  exfalso
  have key : ∀ b : String, X86Backend.LprogAsmPrinter.untagCaret o = b →
      (b = "LOADIDX" ∨ b = "STOREIDX" ∨ b = "ZEROARR" ∨ b = "STOREIMM") → False := by
    intro b hu hb'
    have hp := (List.prefix_iff_eq_take.mp (untagCaret_acc_prefix hu hb'))
    have ht := congrArg (List.take 2) hp
    rw [List.take_take] at ht
    rcases hb' with rfl | rfl | rfl | rfl
    · exact h.1 (by simpa using ht.symm)
    · exact h.2.1 (by simpa using ht.symm)
    · exact h.2.2 (by simpa using ht.symm)
    · exact h.2.1 (by simpa using ht.symm)
  exact key _ rfl hb

/-- A mnemonic that begins with two characters other than `LO`, `ST` and `ZE` is untagged
    after any suffix. -/
theorem accUntagged_append {p : String} (s : String)
    (h : 2 ≤ p.toList.length ∧ p.toList.take 2 ≠ ['L', 'O'] ∧ p.toList.take 2 ≠ ['S', 'T'] ∧
      p.toList.take 2 ≠ ['Z', 'E']) : X86Backend.PhysImgEmit.AccUntagged (p ++ s) :=
  accUntagged_of_take (by
    rw [String.toList_append, List.take_append_of_le_length h.1]
    exact h.2)

/-- A width-tagged mnemonic whose body begins with two characters other than `LO`, `ST` and
    `ZE` is untagged. -/
theorem accUntagged_withWidthTag (w : Nat) {m : String}
    (h : 2 ≤ m.toList.length ∧ m.toList.take 2 ≠ ['L', 'O'] ∧ m.toList.take 2 ≠ ['S', 'T'] ∧
      m.toList.take 2 ≠ ['Z', 'E']) : X86Backend.PhysImgEmit.AccUntagged (withWidthTag w m) := by
  unfold withWidthTag
  split
  · exact accUntagged_append _ h
  · rw [String.append_assoc]
    exact accUntagged_append _ h

/-- A width-tagged mnemonic whose body begins with a prefix of two characters other than `LO`,
    `ST` and `ZE` is untagged after any suffix of the body. -/
theorem accUntagged_withWidthTag_append (w : Nat) {p : String} (s : String)
    (h : 2 ≤ p.toList.length ∧ p.toList.take 2 ≠ ['L', 'O'] ∧ p.toList.take 2 ≠ ['S', 'T'] ∧
      p.toList.take 2 ≠ ['Z', 'E']) :
    X86Backend.PhysImgEmit.AccUntagged (withWidthTag w (p ++ s)) := by
  unfold withWidthTag
  split
  · rw [String.append_assoc]
    exact accUntagged_append _ h
  · rw [String.append_assoc, String.append_assoc]
    exact accUntagged_append _ h

/-- `acc_untagged` closes `AccUntagged o` for a literal `o` without `^`, a literal prefix
    other than `LO`, `ST` and `ZE` followed by any suffix, or such a body under a width tag. -/
local macro "acc_untagged" : tactic =>
  `(tactic| first
    | ((with_reducible refine accUntagged_withWidthTag_append _ _ ?_); decide)
    | ((with_reducible refine accUntagged_withWidthTag _ ?_); decide)
    | ((with_reducible refine accUntagged_append _ ?_); decide)
    | exact accUntagged_of_caret_free (by decide)
    | exact accUntagged_of_take (by decide))

/-- **The access form of an instruction at a predicate `P` on array names**: an `LOADIDX` is
    `[.reg d] [.arrIdx b y 8]` and a `STOREIDX` is `[.reg d] [.arrIdx b y 8, .reg v]`, the
    base of every indexed operand satisfies `P`, a `ZEROARR` is `[.reg b] [#n, #w]` and an
    `STOREIMM` is `[.reg d] [.reg b, .reg v, #k]` at a register `b` that satisfies `P`. -/
def AccP (P : String → Prop) (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss →
    (o = "LOADIDX" → ∃ d b y, ds = [.reg d] ∧ ss = [.arrIdx b y 8]) ∧
    (o = "STOREIDX" → ∃ d b y v, ds = [.reg d] ∧ ss = [.arrIdx b y 8, .reg v]) ∧
    (∀ b y s, LOperand.arrIdx b y s ∈ ds ++ ss → P b) ∧
    (o = "ZEROARR" → ∃ b n w, ds = [.reg b] ∧ ss = [.imm n, .imm w] ∧ P b) ∧
    (o = "STOREIMM" → ∃ d b v k, ds = [.reg d] ∧ ss = [.reg b, .reg v, .imm k] ∧ P b) ∧
    X86Backend.PhysImgEmit.AccUntagged o

theorem accP_of_not_lopn {P : String → Prop} {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) :
    AccP P w := fun ds o ss e => absurd e (h ds o ss)

theorem accP_livepin (P : String → Prop) (ns : List String) :
    AccP P (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)) := by
  intro ds o ss e
  simp only [LinstrR.Lopn.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun b y s h => ?_,
    fun h => absurd h (by decide), fun h => absurd h (by decide), by acc_untagged⟩
  simp at h

theorem accP_livepin_range (P : String → Prop) (m : Nat) :
    AccP P (.Lopn [.reg "%livepin"] "LIVEPIN"
      ((List.range m).map fun j => (.reg (argName j) : LOperand))) := by
  rw [show ((List.range m).map fun j => (.reg (argName j) : LOperand)) =
    ((List.range m).map argName).map LOperand.reg by simp]
  exact accP_livepin P _

/-- **The access form of an instruction of the code given to the renaming**: a `LOADIDX` is
    the load-tagged `[.reg d] [.arrIdx b y 8]`, a `STOREIDX` the store-tagged
    `[.reg d] [.arrIdx b y 8, .reg v]`, and no other operation has an indexed operand. -/
def AccCode (i : LinstrRM) : Prop :=
  (∀ ds ss, i.1 = .Lopn ds "LOADIDX" ss →
    ∃ d b y w n, i = (.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n)) ∧
  (∀ ds ss, i.1 = .Lopn ds "STOREIDX" ss →
    ∃ d b y v w n, i = (.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n)) ∧
  ∀ ds o ss, i.1 = .Lopn ds o ss → o ≠ "LOADIDX" → o ≠ "STOREIDX" →
    ∀ b y s, LOperand.arrIdx b y s ∉ ds ++ ss

/-- **The form of the constant-index array writes of the code given to the renaming**: a
    `ZEROARR` is the zero-tagged `[.reg z] [#n, #w]` and an `STOREIMM` the
    constant-store-tagged `[.reg d] [.reg b, .reg v, #k]`. -/
def ImmCode (i : LinstrRM) : Prop :=
  (∀ ds ss, i.1 = .Lopn ds "ZEROARR" ss →
    ∃ z n w w' m, i = (.Lopn [.reg z] "ZEROARR" [.imm n, .imm w], .zero w' m)) ∧
  (∀ ds ss, i.1 = .Lopn ds "STOREIMM" ss →
    ∃ d b v k w m, i = (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k], .storeImm w m))

theorem renOpR_arrIdx {ρ : String → String} {a : LOperand} {b y : String} {s : Nat}
    (h : renOpR ρ a = .arrIdx b y s) : ∃ b0, a = .arrIdx b0 y s := by
  cases a <;> simp only [renOpR, reduceCtorEq] at h
  exact ⟨b, h⟩

theorem renOpA_arrIdx {ρ : String → String} {a : LOperand} {b y : String} {s : Nat}
    (h : renOpA ρ a = .arrIdx b y s) : ∃ b0, a = .arrIdx b0 y s := by
  cases a <;> simp only [renOpA, reduceCtorEq, LOperand.arrIdx.injEq] at h
  exact ⟨_, by rw [h.2.1, h.2.2]⟩

/-- The renaming of the array positions keeps the mnemonic of an operation and renames at
    most the bases of its indexed operands. -/
theorem renArr_lopn (ρ : String → String) {i : LinstrRM} {ds' : List LOperand} {o : String}
    {ss' : List LOperand} (h : (renArr ρ i).1 = .Lopn ds' o ss') :
    ∃ ds ss, i.1 = .Lopn ds o ss ∧ ∀ b y s, LOperand.arrIdx b y s ∈ ds' ++ ss' →
      ∃ b0, LOperand.arrIdx b0 y s ∈ ds ++ ss := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn ds o0 ss =>
      refine ⟨ds, ss, ?_⟩
      cases tag <;> simp only [renArr, renLoad, renStore, renZero, renStoreImm, renCallW] at h
      all_goals
        revert h
        repeat' split
      all_goals first
        | (intro he
           simp only [LinstrR.Lopn.injEq] at he
           obtain ⟨rfl, rfl, rfl⟩ := he
           exact ⟨rfl, fun b y s hm => ⟨b, hm⟩⟩)
        | (rename_i heq
           have hw := LprogIsa.eq_callShadow_of_shadowCall? heq
           intro he
           simp only [LprogIsa.callShadow, LinstrR.Lopn.injEq] at hw he
           obtain ⟨rfl, rfl, rfl⟩ := hw
           obtain ⟨rfl, rfl, rfl⟩ := he
           refine ⟨rfl, fun b y s hm => ?_⟩
           simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
             reduceCtorEq, false_or] at hm
           obtain ⟨a, ha, hae⟩ := hm
           obtain ⟨b0, rfl⟩ := renOpR_arrIdx hae
           exact ⟨b0, by simp [ha]⟩)
        | (rename_i heq _
           intro he
           simp only [LinstrR.Lopn.injEq] at heq he
           obtain ⟨rfl, rfl, rfl⟩ := heq
           obtain ⟨rfl, rfl, rfl⟩ := he
           refine ⟨rfl, fun b y s hm => ?_⟩
           simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map,
             reduceCtorEq, false_or, or_false, List.not_mem_nil, LOperand.arrIdx.injEq] at hm <;>
           first
             | exact ⟨b, List.mem_append_right _ hm⟩
             | (obtain ⟨-, rfl, rfl⟩ := hm
                exact ⟨_, List.mem_append_right _ List.mem_cons_self⟩)
             | (obtain ⟨a, ha, hae⟩ := hm
                obtain ⟨b0, rfl⟩ := renOpA_arrIdx hae
                exact ⟨b0, List.mem_append_right _ ha⟩))
  | _ =>
      exfalso
      cases tag <;> simp [renArr, renLoad, renStore, renZero, renStoreImm, renCallW,
        LprogIsa.shadowCall?] at h

/-- **The renaming of the array positions puts the accesses in the form `AccP P`** when the
    instruction has the access forms `AccCode` and `ImmCode` and the renaming sends its array
    names (`RootIn`) into `P`. -/
theorem accP_renArr (P : String → Prop) (ρ : String → String) {i : LinstrRM}
    (hc : AccCode i) (hm0 : ImmCode i) (hroot : RootIn (fun x => P (ρ x)) i)
    (hu : UntagP i.1) : AccP P (renArr ρ i).1 := by
  intro ds' o ss' he
  obtain ⟨ds, ss, hi, hm⟩ := renArr_lopn ρ he
  by_cases hL : o = "LOADIDX"
  · subst hL
    obtain ⟨d, b, y, w, n, rfl⟩ := hc.1 ds ss hi
    simp only [renArr, renLoad, ite_true, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, rfl⟩ := he
    have hP := (hroot.1 _ _ _ rfl).1 b y 8 (by simp)
    refine ⟨fun _ => ⟨d, ρ b, y, rfl, rfl⟩, fun h => absurd h (by decide), ?_,
      fun h => absurd h (by decide), fun h => absurd h (by decide), by acc_untagged⟩
    intro b' y' s' hb
    simp only [List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq,
      LOperand.arrIdx.injEq, false_or, List.not_mem_nil, or_false] at hb
    rw [hb.1]
    exact hP
  by_cases hS : o = "STOREIDX"
  · subst hS
    obtain ⟨d, b, y, v, w, n, rfl⟩ := hc.2.1 ds ss hi
    simp only [renArr, renStore, ite_true, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, rfl⟩ := he
    have hP := (hroot.1 _ _ _ rfl).1 b y 8 (by simp)
    refine ⟨fun h => absurd h (by decide), fun _ => ⟨ρ d, ρ b, y, v, rfl, rfl⟩, ?_,
      fun h => absurd h (by decide), fun h => absurd h (by decide), by acc_untagged⟩
    intro b' y' s' hb
    simp only [List.cons_append, List.nil_append, List.mem_cons, reduceCtorEq,
      LOperand.arrIdx.injEq, false_or, List.not_mem_nil, or_false] at hb
    rw [hb.1]
    exact hP
  have hidx : ∀ b y s, LOperand.arrIdx b y s ∈ ds' ++ ss' → P b := fun b y s hb => by
    obtain ⟨b0, hb0⟩ := hm b y s hb
    exact absurd hb0 (hc.2.2 ds o ss hi hL hS b0 y s)
  by_cases hZ : o = "ZEROARR"
  · subst hZ
    obtain ⟨z, n, w, w', m, rfl⟩ := hm0.1 ds ss hi
    simp only [renArr, renZero, ite_true, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, rfl⟩ := he
    have hP := hroot.2 z (by simp [X86Backend.ImageStraightRoute.zeroDst?])
    refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), hidx,
      fun _ => ⟨ρ z, n, w, rfl, by simp [renOpA], hP⟩, fun h => absurd h (by decide),
      by acc_untagged⟩
  by_cases hI : o = "STOREIMM"
  · subst hI
    obtain ⟨d, b, v, k, w, m, rfl⟩ := hm0.2 ds ss hi
    simp only [renArr, renStoreImm, ite_true, LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, -, rfl⟩ := he
    have hP := (hroot.1 _ _ _ rfl).2 rfl b _ rfl
    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), hidx,
      fun h => absurd h (by decide), fun _ => ⟨ρ d, ρ b, v, k, rfl, rfl, hP⟩, by acc_untagged⟩
  · exact ⟨fun h => absurd h hL, fun h => absurd h hS, hidx, fun h => absurd h hZ,
      fun h => absurd h hI, hu ds o ss hi⟩

/-- **The renaming of the memref threads keeps a predicate on array names** that holds at the
    base of every indexed operand of the body. -/
theorem canonMemrefName_arrChainAlias_of (P : String → Prop) {body : Lcmd}
    (h : ∀ i ∈ body, AccP P i.li_i) :
    ∀ x, P x → P (canonMemrefName (arrChainAlias body) x) := by
  have key : ∀ (L : Lcmd) (l : List (String × String)), (∀ i ∈ L, AccP P i.li_i) →
      (∀ x, P x → P ((l.lookup x).getD x)) →
        ∀ x, P x → P ((L.foldl X86Backend.PhysAbiShape.aliasStepL l).lookup x |>.getD x) := by
    intro L
    induction L with
    | nil => exact fun _ _ hl => hl
    | cons i L ih =>
      intro l hL hl
      rw [List.foldl_cons]
      refine ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) ?_
      have hn := hL i List.mem_cons_self
      unfold X86Backend.PhysAbiShape.aliasStepL
      split
      · next dst opn base _ _ rest heq =>
        have hb : P base := (hn _ _ _ heq).2.2.1 base _ _
          (List.mem_append_right _ List.mem_cons_self)
        split_ifs
        · intro x hx
          simp only [List.lookup]
          split
          · exact hl base hb
          · exact hl x hx
        · exact hl
      · exact hl
  intro x hx
  unfold canonMemrefName
  rw [(X86Backend.PhysAbiShape.arrChainAlias_spec body).1 x]
  exact key body [] h (fun y hy => by simpa using hy) x hx

/-- **The renaming of the memref threads keeps the access form `AccP P`.** -/
theorem accP_canonicalizeMemrefThread (P : String → Prop) {body : Lcmd}
    (h : ∀ i ∈ body, AccP P i.li_i) : ∀ i ∈ canonicalizeMemrefThread body, AccP P i.li_i := by
  have hc := canonMemrefName_arrChainAlias_of P h
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      have hj' := h j hj ds o ss heq
      intro ds' o' ss' he
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      refine ⟨fun hL => ?_, fun hS => ?_, fun b y s hb => ?_, fun hZ => ?_, fun hI => ?_,
        hj'.2.2.2.2.2⟩
      · obtain ⟨d, b, y, rfl, rfl⟩ := hj'.1 hL
        exact ⟨_, _, _, rfl, rfl⟩
      · obtain ⟨d, b, y, v, rfl, rfl⟩ := hj'.2.1 hS
        exact ⟨_, _, _, _, rfl, rfl⟩
      · rw [← List.map_append] at hb
        obtain ⟨a, ha, hae⟩ := List.mem_map.mp hb
        cases a <;> simp only [canonMemrefOperand, reduceCtorEq, LOperand.arrIdx.injEq] at hae
        rename_i b0 y0 s0
        rw [← hae.1]
        exact hc _ (hj'.2.2.1 b0 y0 s0 ha)
      · obtain ⟨b, n, w, rfl, rfl, hb⟩ := hj'.2.2.2.1 hZ
        exact ⟨_, n, w, rfl, rfl, hc _ hb⟩
      · obtain ⟨d, b, v, k, rfl, rfl, hb⟩ := hj'.2.2.2.2.1 hI
        exact ⟨_, _, _, k, rfl, rfl, hc _ hb⟩
    · exact h j hj

theorem accP_backEdgePins (P : String → Prop) {C : List LinstrRM} (h : ∀ i ∈ C, AccP P i.1) :
    ∀ i ∈ backEdgePins C, AccP P i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, AccP P i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact accP_livepin P _
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

/-- **The accesses of the allocator input body have the form `AccP P`**, at a result other
    than one register, when every instruction of the code `C` given to the renaming (the export
    followed by its result copy) has the access forms `AccCode` and `ImmCode`, and the
    coalescing renaming `canonMemrefName (resAliasTab [] rr C)` at the result alias
    `rr := resAliasOf none (some a.outArg) ts r.res` sends the array names (`RootIn`) of every
    instruction of `C` into `P`. -/
theorem accP_regionAllocBody (P : String → Prop) (a : AbiNames) (nArgs : Nat)
    {ts : List JasminTy} (r : Exported) (hts : ∀ w, ts ≠ [.reg w])
    (hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, AccCode i)
    (hI : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, ImmCode i)
    (hroot : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res,
      RootIn (fun x => P (canonMemrefName (resAliasTab [] (resAliasOf none (some a.outArg) ts
        r.res) (r.code ++ regionLprogCopy a none ts r.code r.res)) x)) i)
    (hU : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, UntagP i.1) :
    ∀ i ∈ regionAllocBody a nArgs ts r, AccP P i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res),
      AccP P i.1 := by
    refine accP_backEdgePins P fun i hi => ?_
    rcases mem_pinSelfMoves hi with hi | ⟨t, b, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact accP_renArr P _ (hC j hj) (hI j hj) (hroot j hj) (hU j hj)
    · show AccP P (.Lopn [.reg t] "LIVEPIN" [.reg b, .reg z])
      intro ds o ss e
      simp only [LinstrR.Lopn.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      refine ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun b y s h => ?_,
        fun h => absurd h (by decide), fun h => absurd h (by decide), by acc_untagged⟩
      simp at h
    · show AccP P (.Lopn [.reg "%livepin"] "LIVEPIN" ([b, z, t].map LOperand.reg))
      exact accP_livepin P [b, z, t]
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact accP_livepin_range P _
      · cases hi
    · refine accP_canonicalizeMemrefThread P (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact accP_livepin P _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]
          exact accP_of_not_lopn fun _ _ _ e => by cases e

/-- The array names of the parameters of `σ` with a save slot. -/
def ArgSlotName (σ : AbiLayout) (x : String) : Prop :=
  ∃ j, x = argName j ∧ RegionPhysImg.ArgSlot σ j

theorem accArg_of_accP {σ : AbiLayout} {w : LinstrR} (h : AccP (ArgSlotName σ) w) :
    RegionPhysImg.AccArg σ w := by
  intro ds o ss he
  have hw := h ds o ss he
  refine ⟨fun hL => ?_, fun hS => ?_, fun hZ => ?_, fun hI => ?_, hw.2.2.2.2.2⟩
  · obtain ⟨d, b, y, rfl, rfl⟩ := hw.1 hL
    obtain ⟨j, rfl, hj⟩ := hw.2.2.1 b y 8 (by simp)
    exact ⟨d, j, y, rfl, rfl, hj⟩
  · obtain ⟨d, b, y, v, rfl, rfl⟩ := hw.2.1 hS
    obtain ⟨j, rfl, hj⟩ := hw.2.2.1 b y 8 (by simp)
    exact ⟨d, j, y, v, rfl, rfl, hj⟩
  · obtain ⟨b, n, w, rfl, rfl, ⟨j, rfl, hj⟩⟩ := hw.2.2.2.1 hZ
    exact ⟨j, n, w, rfl, rfl, hj⟩
  · obtain ⟨d, b, v, k, rfl, rfl, ⟨j, rfl, hj⟩⟩ := hw.2.2.2.2.1 hI
    exact ⟨d, j, v, k, rfl, rfl, hj⟩

/-! ## 5. The access form of the export -/

/-- An operand that is no indexed array operand. -/
def NoIdxOp (o : LOperand) : Prop := ∀ b y s, o ≠ .arrIdx b y s

theorem noIdxOp_reg (x : String) : NoIdxOp (.reg x) := fun _ _ _ e => by cases e

theorem noIdxOp_imm (k : Nat) : NoIdxOp (.imm k) := fun _ _ _ e => by cases e

/-- An instruction without an indexed operand whose mnemonic is none of `LOADIDX`,
    `STOREIDX` and `STOREIMM`. -/
def PlainIdx (i : LinstrRM) : Prop :=
  ∀ ds o ss, i.1 = .Lopn ds o ss →
    o ≠ "LOADIDX" ∧ o ≠ "STOREIDX" ∧ o ≠ "STOREIMM" ∧ ∀ x ∈ ds ++ ss, NoIdxOp x

theorem accCode_of_plainIdx {i : LinstrRM} (h : PlainIdx i) : AccCode i :=
  ⟨fun _ _ he => absurd rfl (h _ _ _ he).1, fun _ _ he => absurd rfl (h _ _ _ he).2.1,
    fun _ _ _ he _ _ b y s hm => (h _ _ _ he).2.2.2 _ hm b y s rfl⟩

/-- An instruction without an indexed operand whose mnemonic is neither `LOADIDX` nor
    `STOREIDX` has the access form. -/
theorem accCode_lopn {ds : List LOperand} {o : String} {ss : List LOperand} {t : MemTag}
    (hL : o ≠ "LOADIDX") (hS : o ≠ "STOREIDX") (h : ∀ x ∈ ds ++ ss, NoIdxOp x) :
    AccCode (.Lopn ds o ss, t) := by
  refine ⟨fun ds' ss' he => ?_, fun ds' ss' he => ?_, fun ds' o' ss' he _ _ b y s hm => ?_⟩
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1 hL
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1 hS
  · simp only [LinstrR.Lopn.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact h _ hm b y s rfl

theorem plainIdx_lopn {ds : List LOperand} {o : String} {ss : List LOperand} {t : MemTag}
    (hL : o ≠ "LOADIDX") (hS : o ≠ "STOREIDX") (hI : o ≠ "STOREIMM")
    (h : ∀ x ∈ ds ++ ss, NoIdxOp x) : PlainIdx (.Lopn ds o ss, t) := by
  intro ds' o' ss' he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨hL, hS, hI, h⟩

theorem plainIdx_of_not_lopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) :
    PlainIdx i := fun _ _ _ e => absurd e (h _ _ _)

theorem accCode_load (d b y : String) (w n : Nat) :
    AccCode (.Lopn [.reg d] "LOADIDX" [.arrIdx b y 8], .load w n) := by
  refine ⟨fun _ _ _ => ⟨d, b, y, w, n, rfl⟩, fun ds ss he => ?_, fun ds o ss he hL _ => ?_⟩
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1 (by decide)
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1.symm hL

theorem accCode_store (d b y v : String) (w n : Nat) :
    AccCode (.Lopn [.reg d] "STOREIDX" [.arrIdx b y 8, .reg v], .store w n) := by
  refine ⟨fun ds ss he => ?_, fun _ _ _ => ⟨d, b, y, v, w, n, rfl⟩, fun ds o ss he _ hS => ?_⟩
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1 (by decide)
  · simp only [LinstrR.Lopn.injEq] at he
    exact absurd he.2.1.symm hS

/-- A string that begins with two characters other than `LO` and `ST` is none of `LOADIDX`,
    `STOREIDX` and `STOREIMM` after any suffix. -/
theorem ne_idxMnem_append {p : String} (s : String)
    (h : 2 ≤ p.toList.length ∧ p.toList.take 2 ≠ ['L', 'O'] ∧ p.toList.take 2 ≠ ['S', 'T']) :
    p ++ s ≠ "LOADIDX" ∧ p ++ s ≠ "STOREIDX" ∧ p ++ s ≠ "STOREIMM" := by
  have ht : (p ++ s).toList.take 2 = p.toList.take 2 := by
    rw [String.toList_append, List.take_append_of_le_length h.1]
  refine ⟨fun e => h.2.1 ?_, fun e => h.2.2 ?_, fun e => h.2.2 ?_⟩ <;> rw [← ht, e] <;> decide

/-- **The mnemonic-distinctness of the export of an operation**: the only operations whose
    instruction has the mnemonic `LOADIDX`, `STOREIDX` or `STOREIMM` are `stackLoad`,
    `stackStore` and `stackStoreImm`; every other operation over operands without an indexed
    operand has none. -/
theorem plainIdx_opToLinstrR (op : JasminOp) (dst : String) {srcs : List LOperand}
    (h : ∀ o ∈ srcs, NoIdxOp o) (hL : ∀ w n, op ≠ .stackLoad w n)
    (hS : ∀ w n, op ≠ .stackStore w n) (hI : ∀ w n k, op ≠ .stackStoreImm w n k)
    (t : MemTag) : PlainIdx (opToLinstrR op dst srcs, t) := by
  have hm : ∀ x ∈ [LOperand.reg dst] ++ srcs, NoIdxOp x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton.mp hx]; exact noIdxOp_reg _
    · exact h x hx
  have hmi : ∀ k, ∀ x ∈ [LOperand.reg dst] ++ (srcs ++ [.imm k]), NoIdxOp x := by
    intro k x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.mem_singleton.mp hx]; exact noIdxOp_reg _
    · rcases List.mem_append.mp hx with hx | hx
      · exact h x hx
      · rw [List.mem_singleton.mp hx]; exact noIdxOp_imm _
  cases op with
  | stackLoad w n => exact absurd rfl (hL w n)
  | stackStore w n => exact absurd rfl (hS w n)
  | stackStoreImm w n k => exact absurd rfl (hI w n k)
  | vsimd op =>
    show PlainIdx (.Lopn [.reg dst] op.mnemonic srcs, t)
    refine plainIdx_lopn ?_ ?_ ?_ hm <;> unfold SimdOp.mnemonic <;> split <;> first
      | decide
      | exact (ne_idxMnem_append _ (by decide)).1
      | exact (ne_idxMnem_append _ (by decide)).2.1
      | exact (ne_idxMnem_append _ (by decide)).2.2
  | vymm op =>
    show PlainIdx (.Lopn [.reg dst] op.jasminMnemonic srcs, t)
    refine plainIdx_lopn ?_ ?_ ?_ hm <;> cases op <;> first
      | decide
      | (rw [YmmDialect.YmmOp.jasminMnemonic]
         first
           | exact (ne_idxMnem_append _ (by decide)).1
           | exact (ne_idxMnem_append _ (by decide)).2.1
           | exact (ne_idxMnem_append _ (by decide)).2.2)
  | _ =>
    simp only [opToLinstrR]
    (repeat' split) <;> refine plainIdx_lopn ?_ ?_ ?_ ?_
    all_goals first
      | exact hm
      | exact hmi _
      | width_tag_ne
      | (intro x hx
         simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
           or_false] at hx
         rcases hx with rfl | rfl | rfl <;> first | exact noIdxOp_reg _ | exact noIdxOp_imm _)
      | decide
      | exact (ne_idxMnem_append _ (by decide)).1
      | exact (ne_idxMnem_append _ (by decide)).2.1
      | exact (ne_idxMnem_append _ (by decide)).2.2
      | (unfold castWMnem; repeat' split
         all_goals decide)
      | (unfold encodeCallW; simp only [String.append_assoc]
         first
           | exact (ne_idxMnem_append _ (by decide)).1
           | exact (ne_idxMnem_append _ (by decide)).2.1
           | exact (ne_idxMnem_append _ (by decide)).2.2)

/-- The width condition of an operation: a `stackLoad` or a `stackStore` is at `64`-bit
    words; every other operation passes. -/
def opW64B : JasminOp → Bool
  | .stackLoad w _ => w == 64
  | .stackStore w _ => w == 64
  | _ => true

/-- The width condition of an array type: an array of `64`-bit words, or no array. -/
def tyW64B : JasminTy → Bool
  | .stackArr w _ => w == 64
  | _ => true

/-- **The width condition of the access form**: every `stackLoad` and `stackStore` of the
    program is at `64`-bit words, and so is every array the program carries through a
    counted loop or returns from a branch. -/
def arrW64B : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => opW64B e.op && arrW64B k
  | _, _, .forLoop (cs := cs) _ _ body k => cs.all tyW64B && arrW64B body && arrW64B k
  | _, _, .ifThenElse (rs := rs) _ thn els k =>
      rs.all tyW64B && arrW64B thn && arrW64B els && arrW64B k
  | _, _, .whileLoop _ body k => arrW64B body && arrW64B k
  | _, _, .call _ _ k => arrW64B k

theorem plainIdx_movI (dst : String) {src : LOperand} (h : NoIdxOp src) :
    PlainIdx (movI dst src) := by
  unfold movI
  refine plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact noIdxOp_reg _
  · exact h

theorem plainIdx_movImmI (dst : String) (k : Nat) : PlainIdx (movImmI dst k) :=
  plainIdx_movI dst (noIdxOp_imm k)

theorem plainIdx_labelI (l : LLabel) : PlainIdx (labelI l) :=
  plainIdx_of_not_lopn fun _ _ _ e => by unfold labelI at e; cases e

theorem plainIdx_seedMoves (car : List String) {ops : List LOperand}
    (h : ∀ o ∈ ops, NoIdxOp o) : ∀ i ∈ seedMoves car ops, PlainIdx i := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact plainIdx_movI _ (h _ (List.of_mem_zip hp).2)

theorem plainIdx_parMoves (D : Nat) (tgts : List String) {ops : List LOperand}
    (h : ∀ o ∈ ops, NoIdxOp o) : ∀ i ∈ parMoves D tgts ops, PlainIdx i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  · exact plainIdx_movI _ (h _ (List.fst_mem_of_mem_zipIdx hp))
  · exact plainIdx_movI _ (noIdxOp_reg _)

theorem plainIdx_parMoves_reg (D : Nat) (tgts : List String) (xs : List String) :
    ∀ i ∈ parMoves D tgts (xs.map LOperand.reg), PlainIdx i :=
  plainIdx_parMoves D tgts fun o ho => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ho
    exact noIdxOp_reg x

theorem plainIdx_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, PlainIdx i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;>
    refine plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => ?_ <;>
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx <;>
    rcases hx with rfl | rfl | rfl <;> first | exact noIdxOp_reg _ | exact noIdxOp_imm _

theorem plainIdx_flagWord (r z : String) {op : LOperand} (h : NoIdxOp op) :
    ∀ i ∈ flagWord x86Data r z op, PlainIdx i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact plainIdx_movImmI _ _
    · exact plainIdx_movImmI _ _
    · refine plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact noIdxOp_reg _
  · rw [List.mem_singleton.mp hi]
    exact plainIdx_movI _ h

theorem plainIdx_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, PlainIdx i) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, PlainIdx i := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl <;> first | exact noIdxOp_reg _ | exact noIdxOp_imm _
    · exact plainIdx_of_not_lopn fun _ _ _ e => by cases e
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · refine plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl <;> first | exact noIdxOp_reg _ | exact noIdxOp_imm _
    · exact plainIdx_of_not_lopn fun _ _ _ e => by cases e

/-- The array moves of a typed pair list come from its pairs of a stack-array type. -/
theorem mem_arrPairs {tp : List (JasminTy × String × String)} {a : ArrMove}
    (h : a ∈ arrPairs tp) : ∃ p ∈ tp, p.1 = .stackArr a.w a.n ∧ p.2.1 = a.dst ∧ p.2.2 = a.src := by
  obtain ⟨p, hp, he⟩ := List.mem_filterMap.mp h
  obtain ⟨t, x, y⟩ := p
  cases t <;> simp only [Option.some.injEq, reduceCtorEq] at he
  subst he
  exact ⟨_, hp, rfl, rfl, rfl⟩

/-- The pairs of the two stages of a parallel assignment of arrays: every commit move reads
    the destination of a stage move of the same width, every stage move reads the source of
    a move of the same width, and every target of the assignment is written by a commit
    move. -/
theorem arrStage_arrCommit (D : Nat) (mv : List ArrMove) :
    (∀ a ∈ arrCommit D mv, ∃ b ∈ arrStage D mv, a.src = b.dst ∧ a.w = b.w) ∧
    (∀ b ∈ arrStage D mv, ∃ c ∈ mv, b.src = c.src ∧ b.w = c.w) ∧
    (∀ c ∈ mv, ∃ a ∈ arrCommit D mv, a.dst = c.dst ∧ a.w = c.w) := by
  induction mv generalizing D with
  | nil => simp [arrCommit, arrStage]
  | cons c mv ih =>
      obtain ⟨h1, h2, h3⟩ := ih (D + 1)
      simp only [arrCommit, arrStage, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
      refine ⟨⟨Or.inl ⟨trivial, trivial⟩, fun a ha => ?_⟩,
        ⟨Or.inl ⟨trivial, trivial⟩, fun b hb => ?_⟩, ⟨Or.inl ⟨trivial, trivial⟩, fun c' hc => ?_⟩⟩
      · obtain ⟨b, hb, e⟩ := h1 a ha
        exact Or.inr ⟨b, hb, e⟩
      · obtain ⟨c', hc, e⟩ := h2 b hb
        exact Or.inr ⟨c', hc, e⟩
      · obtain ⟨a, ha, e⟩ := h3 c' hc
        exact Or.inr ⟨a, ha, e⟩

theorem accCode_arrMoves (z t : String) {mv : List ArrMove} (h : ∀ a ∈ mv, a.w = 64) :
    ∀ i ∈ arrMoves z t mv, AccCode i := by
  intro i hi
  obtain ⟨a, ha, hi⟩ := List.mem_flatMap.mp hi
  have hw : a.w / 8 = 8 := by rw [h a ha]
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false, hw] at hi
  rcases hi with rfl | rfl
  · exact accCode_load _ _ _ _ _
  · exact accCode_store _ _ _ _ _ _

theorem accCode_arrParMoves (z t : String) (D : Nat) {mv : List ArrMove}
    (h : ∀ a ∈ mv, a.w = 64) : ∀ i ∈ arrParMoves z t D mv, AccCode i := by
  obtain ⟨h1, h2, -⟩ := arrStage_arrCommit D mv
  have hs : ∀ b ∈ arrStage D mv, b.w = 64 := fun b hb => by
    obtain ⟨c, hc, -, e⟩ := h2 b hb
    rw [e, h c hc]
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact accCode_arrMoves _ _ h i hi
  · rcases List.mem_append.mp hi with hi | hi
    · exact accCode_arrMoves _ _ hs i hi
    · refine accCode_arrMoves _ _ (fun a ha => ?_) i hi
      obtain ⟨b, hb, -, e⟩ := h1 a ha
      rw [e, hs b hb]

theorem arrPairs_w64 {tp : List (JasminTy × String × String)}
    (h : ∀ p ∈ tp, tyW64B p.1 = true) : ∀ a ∈ arrPairs tp, a.w = 64 := by
  intro a ha
  obtain ⟨p, hp, h1, -, -⟩ := mem_arrPairs ha
  have := h p hp
  rw [h1] at this
  simpa [tyW64B] using this

theorem accCode_typedMoves (z t : String) {tp : List (JasminTy × String × String)}
    (h : ∀ p ∈ tp, tyW64B p.1 = true) : ∀ i ∈ typedMoves z t tp, AccCode i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact accCode_arrMoves _ _ (arrPairs_w64 h) i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact accCode_of_plainIdx (plainIdx_movI _ (noIdxOp_reg _))

theorem carriedPairs_w64 {cs : List JasminTy} (hcs : ∀ t ∈ cs, tyW64B t = true)
    (car : List String) (ops : List LOperand) :
    ∀ p ∈ carriedPairs cs car ops, tyW64B p.1 = true :=
  fun _ hp => hcs _ (List.of_mem_zip hp).1

theorem accCode_ifResMoves {rs : List JasminTy} (hrs : ∀ t ∈ rs, tyW64B t = true)
    (d D : Nat) (ops : List LOperand) : ∀ i ∈ ifResMoves rs d D ops, AccCode i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
      · exact accCode_arrParMoves _ _ _
          (arrPairs_w64 (carriedPairs_w64 hrs _ _)) i hi
  · rw [show ((regPairs (ifResPairs rs d ops)).map fun p => LOperand.reg p.2) =
      ((regPairs (ifResPairs rs d ops)).map Prod.snd).map LOperand.reg by simp] at hi
    exact accCode_of_plainIdx (plainIdx_parMoves_reg _ _ _ i hi)

theorem forArrFrame_accCode (d n : Nat) {cs : List JasminTy}
    (hcs : ∀ t ∈ cs, tyW64B t = true) (initOps : List LOperand)
    {countOp : LOperand} (hc : NoIdxOp countOp) (bodyC : List LinstrRM)
    (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, AccCode i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, AccCode i := by
  have hsh : ∀ p ∈ shiftPairs d cs, tyW64B p.1 = true := fun p hp =>
    hcs _ (List.of_mem_zip (List.mem_reverse.mp hp)).1
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
  · exact accCode_typedMoves _ _ (carriedPairs_w64 hcs _ _) i hi
  · exact accCode_of_plainIdx
      (plainIdx_seedMoves _ (fun o ho => by simp at ho; subst ho; exact hc) i hi)
  · exact accCode_of_plainIdx (plainIdx_x86Guards.1 _ n _ i hi)
  · exact accCode_of_plainIdx (plainIdx_labelI _)
  · exact hb i hi
  · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
  · exact accCode_arrParMoves _ _ _ (arrPairs_w64 (carriedPairs_w64 hcs _ _)) i hi
  · rw [show ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps)).map
        fun p => LOperand.reg p.2) = ((regPairs (carriedPairs cs
        (carriedRegs (d + 1) cs.length) bodyOps)).map Prod.snd).map LOperand.reg by simp] at hi
    exact accCode_of_plainIdx (plainIdx_parMoves_reg _ _ _ i hi)
  · exact accCode_of_plainIdx (plainIdx_advanceOps _ _ i hi)
  · exact accCode_of_plainIdx (plainIdx_x86Guards.2 _ _ i hi)
  · exact accCode_of_plainIdx (plainIdx_labelI _)
  · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
  · exact accCode_typedMoves _ _ hsh i hi

theorem whileFrame_accCode (d n nCar : Nat) {initOps : List LOperand}
    (hi0 : ∀ o ∈ initOps, NoIdxOp o) (bodyC : List LinstrRM) {flagOp : LOperand}
    (hf : NoIdxOp flagOp) {bodyOps : List LOperand} (hbo : ∀ o ∈ bodyOps, NoIdxOp o)
    (bodyD : Nat) (hb : ∀ i ∈ bodyC, AccCode i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, AccCode i := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact accCode_of_plainIdx (plainIdx_seedMoves _ hi0 i hi)
  · exact accCode_of_plainIdx (plainIdx_labelI _)
  · exact hb i hi
  · exact accCode_of_plainIdx (plainIdx_flagWord _ _ hf i hi)
  · exact accCode_of_plainIdx (plainIdx_parMoves _ _ hbo i hi)
  · exact accCode_of_plainIdx (plainIdx_x86Guards.2 _ _ i hi)

theorem ifFrame_accCode (fn : String) (d n : Nat) {rs : List JasminTy}
    (hrs : ∀ t ∈ rs, tyW64B t = true) {condOp : LOperand}
    (hc : NoIdxOp condOp) (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat)
    (elsC : List LinstrRM) (elsOps : List LOperand) (elsD : Nat)
    (ht : ∀ i ∈ thnC, AccCode i) (he : ∀ i ∈ elsC, AccCode i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, AccCode i := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact accCode_of_plainIdx (plainIdx_flagWord _ _ hc i hi)
  · exact accCode_of_plainIdx (plainIdx_x86Guards.1 _ n _ i hi)
  · exact accCode_of_plainIdx (plainIdx_labelI _)
  · exact ht i hi
  · exact accCode_ifResMoves hrs _ _ _ i hi
  · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
  · exact accCode_of_plainIdx (plainIdx_x86Guards.2 _ _ i hi)
  · exact accCode_of_plainIdx (plainIdx_labelI _)
  · exact he i hi
  · exact accCode_ifResMoves hrs _ _ _ i hi
  · exact accCode_of_plainIdx (plainIdx_labelI _)

/-- **The instruction of a binding has the access form `AccCode`** when its operation passes
    the width condition `opW64B`. -/
theorem bindOps_accCode (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hw : opW64B e.op = true) (d : Nat) :
    ∀ i ∈ bindOps nArgs e d, AccCode i := by
  have hreg := JasminLsemExportTransfer.exprArgs_isReg (curDepth := d) (nArgs := nArgs) e
  have hp : ∀ o ∈ exprArgs d nArgs argName (fun _ => none) e, NoIdxOp o := fun o ho => by
    obtain ⟨r, rfl⟩ := hreg o ho
    exact noIdxOp_reg r
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  revert hreg hp hw
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  intro hw hreg hp
  split
  · rename_i w n
    have h8 : w / 8 = 8 := by simp only [opW64B, beq_iff_eq] at hw; rw [hw]
    simp only [opToLinstrR]
    split
    · rw [h8]; exact accCode_load _ _ _ _ _
    · exact accCode_of_plainIdx (plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · rw [List.mem_singleton.mp hx]; exact noIdxOp_reg _
        · exact hp x hx)
  · rename_i w n
    have h8 : w / 8 = 8 := by simp only [opW64B, beq_iff_eq] at hw; rw [hw]
    simp only [opToLinstrR]
    split
    · rename_i base idx val
      obtain ⟨v, rfl⟩ := hreg val (by simp)
      rw [h8]; exact accCode_store _ _ _ _ _ _
    · exact accCode_of_plainIdx (plainIdx_lopn (by decide) (by decide) (by decide) fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · rw [List.mem_singleton.mp hx]; exact noIdxOp_reg _
        · exact hp x hx)
  all_goals first
    | (refine accCode_of_plainIdx (plainIdx_opToLinstrR _ _ hp (fun _ _ e => by cases e)
        (fun _ _ e => by cases e) (fun _ _ _ e => ?_) _)
       cases e
       done)
    | (simp only [opToLinstrR]
       refine accCode_lopn (by decide) (by decide) fun x hx => ?_
       simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append,
         List.not_mem_nil, or_false] at hx
       rcases hx with rfl | hx | rfl
       · exact noIdxOp_reg _
       · exact hp x hx
       · exact noIdxOp_imm _)
    | (split
       all_goals first
         | exact accCode_of_plainIdx (plainIdx_opToLinstrR _ _ hp (fun _ _ e => by simp_all)
             (fun _ _ e => by simp_all) (fun _ _ _ e => by simp_all) _)
         | (unfold JasminLsemShift.shiftLinstr
            refine accCode_of_plainIdx (plainIdx_lopn (by width_tag_ne) (by width_tag_ne)
              (by width_tag_ne)
              fun x hx => ?_)
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at hx
            rcases hx with rfl | rfl | rfl
            · exact noIdxOp_reg _
            · exact hp _ (by simp)
            · exact noIdxOp_imm _))

theorem noIdxOp_of_isReg {o : LOperand} (h : o = .reg (operandName o)) : NoIdxOp o := by
  rw [h]; exact noIdxOp_reg _

/-- **Every instruction of the export has the access form `AccCode`**, for a program without
    `call` that passes the width condition `arrW64B`. -/
theorem exportR_accCode (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true)
    (hw : arrW64B p = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, AccCode i := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [NFProg.callFree] at hc
      simp only [arrW64B, Bool.and_eq_true] at hw
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact bindOps_accCode nArgs e hw.1 d i hi
      · exact ih hc hw.2 _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [arrW64B, Bool.and_eq_true, List.all_eq_true] at hw
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_accCode _ _ hw.1.1 _ (noIdxOp_of_isReg (resolveVar_isReg count)) _ _ _
          (ihb hc.1 hw.1.2 _ _ _ hb) i hi
      · exact ihk hc.2 hw.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [arrW64B, Bool.and_eq_true, List.all_eq_true] at hw
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_accCode _ _ _ hw.1.1.1 (noIdxOp_of_isReg (resolveVar_isReg cond)) _ _ _
          _ _ _ (iht hc.1.1 hw.1.1.2 _ _ _ ht) (ihe hc.1.2 hw.1.2 _ _ _ he) i hi
      · exact ihk hc.2 hw.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [arrW64B, Bool.and_eq_true] at hw
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hres := exportR_res_isReg nArgs fn body _ _ b hb
      rcases List.mem_append.mp hi with hi | hi
      · refine whileFrame_accCode _ _ _
          (fun o ho => noIdxOp_of_isReg (exprArgsHV_isReg _ _ inits o ho)) _ ?_ ?_ _
          (ihb hc.1 hw.1 _ _ _ hb) i hi
        · cases hr : b.res with
          | nil => exact noIdxOp_imm 0
          | cons o os => exact noIdxOp_of_isReg (hres o (by rw [hr]; simp))
        · intro o ho
          exact noIdxOp_of_isReg (hres o (List.mem_of_mem_tail ho))
      · exact ihk hc.2 hw.2 _ _ _ hk i hi
  | call f args k _ =>
      simp [NFProg.callFree] at hc

theorem accCode_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, AccCode i := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact accCode_of_plainIdx (plainIdx_movImmI _ _)
      · exact accCode_load _ _ _ _ _
      · exact accCode_store _ _ _ _ _ _
    · cases hi
  · cases hi

/-- **The code given to the renaming has the access form `AccCode`** (the hypothesis `hC` of
    `physImgB_regionExport_param`), for a program without `call` that passes the width
    condition `arrW64B`. -/
theorem exportR_accCode_copy (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) (hw : arrW64B p = true)
    {r : Exported} (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r) :
    ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, AccCode i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact exportR_accCode _ _ p hc hw _ _ r hr i hi
  · exact accCode_regionLprogCopy a ts r.code r.res i hi

/-! ## 6. The roots of the indexed bases -/

/-- The destination and the base of a store that is no call shadow: the pair whose
    destination the coalescing renaming at no out symbol (`aliasStepO []`) sends to the root
    of the base. The base of an indexed store is its indexed source, the base of a
    constant-index store `STOREIMM` its first register source. -/
def stPair (i : LinstrRM) : Option (String × String) :=
  match LprogIsa.shadowCall? i.1 with
  | some _ => none
  | none =>
      match i.1 with
      | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
          if isMemStore opn then some (dst, base) else none
      | .Lopn [.reg dst] opn (.reg base :: _) =>
          if opn == "STOREIMM" then some (dst, base) else none
      | _ => none

/-- The destination of a store that is no call shadow. -/
def stDst (i : LinstrRM) : Option String := (stPair i).map Prod.fst

/-- One step of the alias table at no out symbol is the insertion of the pair `stPair`. -/
theorem aliasStepO_nil (m : Std.HashMap String String) (i : LinstrRM) :
    X86Backend.ImageStraightRoute.aliasStepO [] m i =
      match stPair i with
      | some p => m.insert p.1 (m.getD p.2 p.2)
      | none => m := by
  unfold X86Backend.ImageStraightRoute.aliasStepO stPair
  cases LprogIsa.shadowCall? i.1 with
  | some v => rfl
  | none =>
      dsimp only
      split
      · rename_i heq
        simp only [heq]
        split <;> rfl
      · rename_i heq
        simp only [heq]
        split <;> rfl
      · split
        · rename_i _ hne hne' _ _ heq
          split at heq
          · rename_i heq2
            exact absurd heq2 (hne _ _ _ _ _ _)
          · rename_i heq2
            exact absurd heq2 (hne' _ _ _ _)
          · cases heq
        · rfl

/-- The base of a store pair is the base of the first source of the store: its indexed
    source, or the first register source of a constant-index store `STOREIMM`. -/
theorem stPair_some {i : LinstrRM} {dst base : String} (h : stPair i = some (dst, base)) :
    (∃ opn y s rest, i.1 = .Lopn [.reg dst] opn (.arrIdx base y s :: rest)) ∨
      ∃ rest, i.1 = .Lopn [.reg dst] "STOREIMM" (.reg base :: rest) := by
  unfold stPair at h
  split at h
  · cases h
  · split at h
    · rename_i dst' opn base' y s rest heq
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨opn, y, s, rest, heq⟩
      · cases h
    · rename_i dst' opn base' rest heq
      split at h
      · rename_i ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [beq_iff_eq] at ho
        subst ho
        exact Or.inr ⟨rest, heq⟩
      · cases h
    · cases h

/-- The names of `S`, the destination of the store `i` and the destination of the zeroing
    `i`. -/
def addDst (S : String → Prop) (i : LinstrRM) : String → Prop :=
  fun x => S x ∨ stDst i = some x ∨ X86Backend.ImageStraightRoute.zeroDst? i = some x

/-- **Indexed bases defined before use**: along the code, every indexed source has its base
    in `S` or among the destinations of the stores and zeroings before it. -/
def IdxOk : (String → Prop) → List LinstrRM → Prop
  | _, [] => True
  | S, i :: c => IdxIn S i ∧ IdxOk (addDst S i) c

/-- The names of `S` and the destinations of the stores of the code `c`. -/
def afterDst (S : String → Prop) (c : List LinstrRM) : String → Prop := c.foldl addDst S

theorem idxIn_mono {S T : String → Prop} (h : ∀ x, S x → T x) {i : LinstrRM}
    (hi : IdxIn S i) : IdxIn T i :=
  fun ds o ss he => ⟨fun b y s hm => h _ ((hi ds o ss he).1 b y s hm),
    fun ho b rest hs => h _ ((hi ds o ss he).2 ho b rest hs)⟩

theorem rootIn_mono {S T : String → Prop} (h : ∀ x, S x → T x) {i : LinstrRM}
    (hi : RootIn S i) : RootIn T i :=
  ⟨idxIn_mono h hi.1, fun z hz => h z (hi.2 z hz)⟩

theorem idxIn_lopn {S : String → Prop} {ds : List LOperand} {o : String} {ss : List LOperand}
    {t : MemTag} (hI : o ≠ "STOREIMM") (h : ∀ b y s, LOperand.arrIdx b y s ∈ ss → S b) :
    IdxIn S (.Lopn ds o ss, t) := by
  intro ds' o' ss' he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨h, fun ho => absurd ho hI⟩

theorem idxIn_of_plainIdx {S : String → Prop} {i : LinstrRM} (h : PlainIdx i) : IdxIn S i :=
  fun ds o ss he =>
    ⟨fun b y s hm => absurd rfl ((h ds o ss he).2.2.2 _ (List.mem_append_right _ hm) b y s),
      fun ho => absurd ho (h ds o ss he).2.2.1⟩

theorem addDst_mono {S T : String → Prop} (h : ∀ x, S x → T x) (i : LinstrRM) :
    ∀ x, addDst S i x → addDst T i x :=
  fun x hx => Or.elim hx (fun hx => Or.inl (h x hx)) Or.inr

theorem idxOk_mono {c : List LinstrRM} : ∀ {S T : String → Prop}, (∀ x, S x → T x) →
    IdxOk S c → IdxOk T c := by
  induction c with
  | nil => exact fun _ _ => trivial
  | cons i c ih => exact fun h hc => ⟨idxIn_mono h hc.1, ih (addDst_mono h i) hc.2⟩

theorem afterDst_cons (S : String → Prop) (i : LinstrRM) (c : List LinstrRM) :
    afterDst S (i :: c) = afterDst (addDst S i) c := rfl

theorem afterDst_append (S : String → Prop) (a b : List LinstrRM) :
    afterDst S (a ++ b) = afterDst (afterDst S a) b := List.foldl_append

theorem afterDst_mono {c : List LinstrRM} : ∀ {S T : String → Prop}, (∀ x, S x → T x) →
    ∀ x, afterDst S c x → afterDst T c x := by
  induction c with
  | nil => exact fun h => h
  | cons i c ih => exact fun h => ih (addDst_mono h i)

theorem le_afterDst {S : String → Prop} {c : List LinstrRM} : ∀ x, S x → afterDst S c x := by
  induction c generalizing S with
  | nil => exact fun _ h => h
  | cons i c ih => exact fun x h => ih x (Or.inl h)

theorem idxOk_append {S T : String → Prop} {a b : List LinstrRM} (ha : IdxOk S a)
    (hT : ∀ x, T x → afterDst S a x) (hb : IdxOk T b) : IdxOk S (a ++ b) := by
  induction a generalizing S with
  | nil => exact idxOk_mono hT hb
  | cons i a ih => exact ⟨ha.1, ih ha.2 hT⟩

theorem afterDst_append_of {S T : String → Prop} {a b : List LinstrRM}
    (hT : ∀ x, T x → afterDst S a x) {x : String} (hx : afterDst T b x) :
    afterDst S (a ++ b) x := by
  rw [afterDst_append]
  exact afterDst_mono hT x hx

theorem afterDst_cons_of {S : String → Prop} {i : LinstrRM} {c : List LinstrRM} {x : String}
    (hx : afterDst S c x) : afterDst S (i :: c) x :=
  afterDst_mono (fun _ h => Or.inl h) x hx

theorem idxOk_of_plainIdx {S : String → Prop} :
    ∀ {c : List LinstrRM}, (∀ i ∈ c, PlainIdx i) → IdxOk S c
  | [], _ => trivial
  | i :: _, h => ⟨idxIn_of_plainIdx (h i List.mem_cons_self),
      idxOk_of_plainIdx fun j hj => h j (List.mem_cons_of_mem _ hj)⟩

theorem idxOk_plain_append {S : String → Prop} {a b : List LinstrRM}
    (ha : ∀ i ∈ a, PlainIdx i) (hb : IdxOk S b) : IdxOk S (a ++ b) :=
  idxOk_append (idxOk_of_plainIdx ha) (fun _ h => le_afterDst _ h) hb

theorem idxOk_cons_plain {S : String → Prop} {i : LinstrRM} {c : List LinstrRM}
    (hi : PlainIdx i) (hc : IdxOk S c) : IdxOk S (i :: c) :=
  ⟨idxIn_of_plainIdx hi, idxOk_mono (fun _ h => Or.inl h) hc⟩

theorem afterDst_plain_append_of {S : String → Prop} {a b : List LinstrRM} {x : String}
    (hx : afterDst S b x) : afterDst S (a ++ b) x :=
  afterDst_append_of (fun _ h => le_afterDst _ h) hx

theorem mnemB_loadIdx : MnemB "LOADIDX" := by unfold MnemB; decide

theorem mnemB_storeIdx : MnemB "STOREIDX" := by unfold MnemB; decide

theorem stDst_load (d b y : String) (s : Nat) (t : MemTag) :
    stDst (.Lopn [.reg d] "LOADIDX" [.arrIdx b y s], t) = none := by
  unfold stDst stPair
  rw [shadowCall?_of_mnemB mnemB_loadIdx]
  simp only [show isMemStore "LOADIDX" = false by decide, Bool.false_eq_true, ite_false,
    Option.map_none]

theorem stDst_store (d b y : String) (s : Nat) (rest : List LOperand) (t : MemTag) :
    stDst (.Lopn [.reg d] "STOREIDX" (.arrIdx b y s :: rest), t) = some d := by
  unfold stDst stPair
  rw [shadowCall?_of_mnemB mnemB_storeIdx]
  simp only [show isMemStore "STOREIDX" = true by decide, ite_true, Option.map_some]

theorem mnemB_storeImm : MnemB "STOREIMM" := by unfold MnemB; decide

theorem stDst_storeImm (d b : String) (rest : List LOperand) (t : MemTag) :
    stDst (.Lopn [.reg d] "STOREIMM" (.reg b :: rest), t) = some d := by
  unfold stDst stPair
  rw [shadowCall?_of_mnemB mnemB_storeImm]
  simp

theorem zeroDst?_zero (z : String) (ss : List LOperand) (t : MemTag) :
    X86Backend.ImageStraightRoute.zeroDst? (.Lopn [.reg z] "ZEROARR" ss, t) = some z := by
  simp [X86Backend.ImageStraightRoute.zeroDst?]

theorem idxOk_arrMove (z t : String) (a : ArrMove) {S : String → Prop} (h : S a.src) :
    IdxOk S (arrMove z t a) ∧ afterDst S (arrMove z t a) a.dst := by
  refine ⟨⟨idxIn_lopn (by decide) fun b y s hm => ?_,
    idxIn_lopn (by decide) fun b y s hm => ?_, trivial⟩, ?_⟩
  · simp only [List.mem_singleton, LOperand.arrIdx.injEq] at hm
    rw [hm.1]; exact h
  · simp only [List.mem_cons, LOperand.arrIdx.injEq, reduceCtorEq, List.not_mem_nil,
      or_false] at hm
    rw [hm.1]; exact Or.inl h
  · exact Or.inr (Or.inl (stDst_store _ _ _ _ _ _))

theorem idxOk_arrMoves (z t : String) {S : String → Prop} :
    ∀ {mv : List ArrMove}, (∀ a ∈ mv, S a.src) →
      IdxOk S (arrMoves z t mv) ∧ ∀ a ∈ mv, afterDst S (arrMoves z t mv) a.dst
  | [], _ => ⟨trivial, fun _ h => by cases h⟩
  | a :: mv, h => by
      obtain ⟨h1, h2⟩ := idxOk_arrMove z t a (h a List.mem_cons_self)
      obtain ⟨h3, h4⟩ := idxOk_arrMoves z t (S := afterDst S (arrMove z t a))
        (mv := mv) fun a' ha => le_afterDst _ (h a' (List.mem_cons_of_mem _ ha))
      have he : arrMoves z t (a :: mv) = arrMove z t a ++ arrMoves z t mv := List.flatMap_cons
      rw [he]
      refine ⟨idxOk_append h1 (fun _ h => h) h3, fun a' ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [afterDst_append]; exact le_afterDst _ h2
      · exact afterDst_append_of (fun _ h => h) (h4 a' ha)

theorem idxOk_arrParMoves (z t : String) (D : Nat) {S : String → Prop} {mv : List ArrMove}
    (h : ∀ a ∈ mv, S a.src) :
    IdxOk S (arrParMoves z t D mv) ∧ ∀ a ∈ mv, afterDst S (arrParMoves z t D mv) a.dst := by
  unfold arrParMoves
  split
  · exact idxOk_arrMoves z t h
  · obtain ⟨c1, c2, c3⟩ := arrStage_arrCommit D mv
    obtain ⟨h1, h2⟩ := idxOk_arrMoves z t (S := S) (mv := arrStage D mv) fun b hb => by
      obtain ⟨c, hc, e, -⟩ := c2 b hb
      rw [e]; exact h c hc
    obtain ⟨h3, h4⟩ := idxOk_arrMoves z t (S := afterDst S (arrMoves z t (arrStage D mv)))
      (mv := arrCommit D mv) fun a ha => by
        obtain ⟨b, hb, e, -⟩ := c1 a ha
        rw [e]; exact h2 b hb
    refine ⟨idxOk_append h1 (fun _ h => h) h3, fun c hc => ?_⟩
    obtain ⟨a, ha, e, -⟩ := c3 c hc
    rw [← e]
    exact afterDst_append_of (fun _ h => h) (h4 a ha)

theorem idxOk_typedMoves (z t : String) {S : String → Prop}
    {tp : List (JasminTy × String × String)} (h : ∀ a ∈ arrPairs tp, S a.src) :
    IdxOk S (typedMoves z t tp) ∧ ∀ a ∈ arrPairs tp, afterDst S (typedMoves z t tp) a.dst := by
  obtain ⟨h1, h2⟩ := idxOk_arrMoves z t h
  have hp : ∀ i ∈ regMoves (regPairs tp), PlainIdx i := fun i hi => by
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact plainIdx_movI _ (noIdxOp_reg _)
  refine ⟨idxOk_append h1 (fun _ h => h) (idxOk_of_plainIdx hp), fun a ha => ?_⟩
  rw [typedMoves, afterDst_append]
  exact le_afterDst _ (h2 a ha)

theorem idxOk_ifResMoves {S : String → Prop} {rs : List JasminTy} {d : Nat} (D : Nat)
    {ops : List LOperand} (h : ∀ a ∈ arrPairs (ifResPairs rs d ops), S a.src) :
    IdxOk S (ifResMoves rs d D ops) ∧
      ∀ a ∈ arrPairs (ifResPairs rs d ops), afterDst S (ifResMoves rs d D ops) a.dst := by
  have hp : ∀ i ∈ parMoves D ((regPairs (ifResPairs rs d ops)).map Prod.fst)
      ((regPairs (ifResPairs rs d ops)).map fun p => .reg p.2), PlainIdx i :=
    plainIdx_parMoves _ _ fun o ho => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
      exact noIdxOp_reg _
  unfold ifResMoves
  split
  · rename_i he
    refine ⟨idxOk_of_plainIdx hp, fun a ha => ?_⟩
    rw [List.isEmpty_iff] at he
    rw [he] at ha
    cases ha
  · obtain ⟨k1, k2⟩ := idxOk_arrParMoves (regName (D + 1)) (regName D) D h
    refine ⟨idxOk_append (idxOk_cons_plain (plainIdx_movImmI _ _) k1) (fun _ h => h)
      (idxOk_of_plainIdx hp), fun a ha => ?_⟩
    rw [afterDst_append]
    exact le_afterDst _ (afterDst_cons_of (k2 a ha))

theorem forArrFrame_idxOk (d n : Nat) {cs : List JasminTy} {initOps : List LOperand}
    {countOp : LOperand} (hcount : NoIdxOp countOp) {bodyC : List LinstrRM}
    {bodyOps : List LOperand} (bodyD : Nat) {S : String → Prop}
    (hinit : ∀ a ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) initOps), S a.src)
    (hshift : ∀ a ∈ arrPairs (shiftPairs d cs),
      ∃ a' ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) initOps), a'.dst = a.src)
    (hbody : ∀ T : String → Prop, (∀ x, S x → T x) →
      (∀ a ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) initOps), T a.dst) →
      IdxOk T bodyC ∧
        ∀ a ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps),
          afterDst T bodyC a.src) :
    IdxOk S (forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data) ∧
      ∀ a ∈ arrPairs (shiftPairs d cs),
        afterDst S (forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data) a.dst := by
  obtain ⟨s1, s2⟩ := idxOk_typedMoves (regName d) (regName (d + 1 + cs.length)) hinit
  obtain ⟨b1, b2⟩ := hbody _ (fun x h => le_afterDst x h) s2
  obtain ⟨k1, k2⟩ := idxOk_arrParMoves (regName (bodyD + 1)) (regName bodyD) bodyD b2
  obtain ⟨h1, h2⟩ := idxOk_typedMoves (regName d) (regName (d + 1 + cs.length))
    (S := afterDst (afterDst (afterDst S (typedMoves (regName d) (regName (d + 1 + cs.length))
      (carriedPairs cs (carriedRegs (d + 1) cs.length) initOps))) bodyC)
      (arrParMoves (regName (bodyD + 1)) (regName bodyD) bodyD
        (arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps))))
    (tp := shiftPairs d cs) fun a ha => by
      obtain ⟨a', ha', e⟩ := hshift a ha
      rw [← e]
      exact le_afterDst _ (le_afterDst _ (s2 a' ha'))
  have hseed : ∀ i ∈ seedMoves [loopCtr n] [countOp], PlainIdx i :=
    plainIdx_seedMoves _ fun o ho => by simp at ho; subst ho; exact hcount
  have hpar : ∀ i ∈ parMoves bodyD
      ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps)).map Prod.fst)
      ((regPairs (carriedPairs cs (carriedRegs (d + 1) cs.length) bodyOps)).map
        fun p => .reg p.2), PlainIdx i :=
    plainIdx_parMoves _ _ fun o ho => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
      exact noIdxOp_reg _
  simp only [forArrFrame]
  refine ⟨idxOk_cons_plain (plainIdx_movImmI _ _) (idxOk_append s1 (fun _ h => h)
    (idxOk_plain_append hseed (idxOk_plain_append (plainIdx_x86Guards.1 _ n _)
      (idxOk_cons_plain (plainIdx_labelI _) (idxOk_append b1 (fun _ h => h)
        (idxOk_cons_plain (plainIdx_movImmI _ _) (idxOk_append k1 (fun _ h => h)
          (idxOk_plain_append hpar (idxOk_plain_append (plainIdx_advanceOps _ _)
            (idxOk_plain_append (plainIdx_x86Guards.2 _ _)
              (idxOk_cons_plain (plainIdx_labelI _)
                (idxOk_cons_plain (plainIdx_movImmI _ _) h1)))))))))))), fun a ha => ?_⟩
  exact afterDst_cons_of (afterDst_append_of (fun _ h => h) (afterDst_plain_append_of
    (afterDst_plain_append_of (afterDst_cons_of (afterDst_append_of (fun _ h => h)
      (afterDst_cons_of (afterDst_append_of (fun _ h => h) (afterDst_plain_append_of
        (afterDst_plain_append_of (afterDst_plain_append_of (afterDst_cons_of
          (afterDst_cons_of (h2 a ha)))))))))))))

theorem whileFrame_idxOk (d n nCar : Nat) {initOps : List LOperand}
    (hi0 : ∀ o ∈ initOps, NoIdxOp o) {bodyC : List LinstrRM} {flagOp : LOperand}
    (hf : NoIdxOp flagOp) {bodyOps : List LOperand} (hbo : ∀ o ∈ bodyOps, NoIdxOp o)
    (bodyD : Nat) {S : String → Prop} (hb : IdxOk S bodyC) :
    IdxOk S (whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data) := by
  have hrest : ∀ i ∈ flagWord x86Data (regName (bodyD + nCar)) (regName (bodyD + nCar + 1))
      flagOp ++ (parMoves bodyD (carriedRegs d nCar) bodyOps
        ++ (x86Data.loopGuard (regName (bodyD + nCar)) n).map guardI), PlainIdx i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact plainIdx_flagWord _ _ hf i hi
    · rcases List.mem_append.mp hi with hi | hi
      · exact plainIdx_parMoves _ _ hbo i hi
      · exact plainIdx_x86Guards.2 _ _ i hi
  simp only [whileFrame]
  exact idxOk_plain_append (plainIdx_seedMoves _ hi0) (idxOk_cons_plain (plainIdx_labelI _)
    (idxOk_append hb (fun _ h => h) (idxOk_of_plainIdx hrest)))

theorem ifFrame_idxOk (fn : String) (d n : Nat) {rs : List JasminTy} {condOp : LOperand}
    (hc : NoIdxOp condOp) {thnC : List LinstrRM} {thnOps : List LOperand} (thnD : Nat)
    {elsC : List LinstrRM} {elsOps : List LOperand} (elsD : Nat) {S : String → Prop}
    (hthn : ∀ T : String → Prop, (∀ x, S x → T x) → IdxOk T thnC ∧
      ∀ a ∈ arrPairs (ifResPairs rs d thnOps), afterDst T thnC a.src)
    (hels : ∀ T : String → Prop, (∀ x, S x → T x) → IdxOk T elsC ∧
      ∀ a ∈ arrPairs (ifResPairs rs d elsOps), afterDst T elsC a.src) :
    IdxOk S (ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data) ∧
      ∀ a ∈ arrPairs (ifResPairs rs d elsOps),
        afterDst S (ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data)
          a.dst := by
  obtain ⟨t1, t2⟩ := hthn S fun _ h => h
  obtain ⟨r1, -⟩ := idxOk_ifResMoves (thnD + rs.length) t2
  obtain ⟨e1, e2⟩ := hels (afterDst (afterDst S thnC)
    (ifResMoves rs d (thnD + rs.length) thnOps)) fun x h => le_afterDst _ (le_afterDst _ h)
  obtain ⟨q1, q2⟩ := idxOk_ifResMoves (elsD + rs.length) e2
  simp only [ifFrame]
  refine ⟨idxOk_plain_append (plainIdx_flagWord _ _ hc)
    (idxOk_plain_append (plainIdx_x86Guards.1 _ n _) (idxOk_cons_plain (plainIdx_labelI _)
      (idxOk_append t1 (fun _ h => h) (idxOk_append r1 (fun _ h => h)
        (idxOk_cons_plain (plainIdx_movImmI _ _) (idxOk_plain_append (plainIdx_x86Guards.2 _ _)
          (idxOk_cons_plain (plainIdx_labelI _) (idxOk_append e1 (fun _ h => h)
            (idxOk_append q1 (fun _ h => h)
              (idxOk_of_plainIdx fun i hi => by
                rw [List.mem_singleton.mp hi]; exact plainIdx_labelI _)))))))))), fun a ha => ?_⟩
  exact afterDst_plain_append_of (afterDst_plain_append_of (afterDst_cons_of
    (afterDst_append_of (fun _ h => h) (afterDst_append_of (fun _ h => h) (afterDst_cons_of
      (afterDst_plain_append_of (afterDst_cons_of (afterDst_append_of (fun _ h => h)
        (afterDst_append_of (fun _ h => h) (le_afterDst _ (q2 a ha)))))))))))

/-- The array moves of the carried pairs are at the positions of an array type. -/
theorem mem_arrPairs_carriedPairs {cs : List JasminTy} {car : List String}
    {ops : List LOperand} {a : ArrMove} (h : a ∈ arrPairs (carriedPairs cs car ops)) :
    ∃ (i : Nat) (o : LOperand), cs[i]? = some (.stackArr a.w a.n) ∧ car[i]? = some a.dst ∧
      ops[i]? = some o ∧
      a.src = operandName o := by
  obtain ⟨p, hp, h1, h2, h3⟩ := mem_arrPairs h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  unfold carriedPairs at hi
  rw [List.getElem?_zip_eq_some, List.getElem?_zip_eq_some, List.getElem?_map] at hi
  obtain ⟨hc, hcar, hop⟩ := hi
  obtain ⟨o, ho, ho'⟩ := Option.map_eq_some_iff.mp hop
  refine ⟨i, o, by rw [hc, h1], by rw [hcar, h2], ho, by rw [← h3, ho']⟩

/-- Every array position of the carried pairs has its array move. -/
theorem dst_mem_arrPairs_carriedPairs {cs : List JasminTy} {car : List String}
    {ops : List LOperand} {i w m : Nat} {x : String} {o : LOperand}
    (hc : cs[i]? = some (.stackArr w m)) (hx : car[i]? = some x) (ho : ops[i]? = some o) :
    ∃ a ∈ arrPairs (carriedPairs cs car ops), a.dst = x :=
  ⟨⟨x, operandName o, w, m⟩, List.mem_filterMap.mpr ⟨(.stackArr w m, x, operandName o),
    List.mem_iff_getElem?.mpr ⟨i, by
      simp [carriedPairs, List.getElem?_zip_eq_some, hc, hx, ho]⟩, rfl⟩, rfl⟩

theorem carriedRegs_getElem? {D n i : Nat} (h : i < n) :
    (carriedRegs D n)[i]? = some (regName (D + (n - 1 - i))) := by
  simp [carriedRegs, h]

/-- The shift of a carried block is the carried pairs of the block one name above, reversed. -/
theorem mem_arrPairs_shiftPairs {d : Nat} {cs : List JasminTy} {a : ArrMove} :
    a ∈ arrPairs (shiftPairs d cs) ↔
      a ∈ arrPairs (carriedPairs cs (carriedRegs d cs.length)
        ((carriedRegs (d + 1) cs.length).map LOperand.reg)) := by
  have he : shiftPairs d cs = (carriedPairs cs (carriedRegs d cs.length)
      ((carriedRegs (d + 1) cs.length).map LOperand.reg)).reverse := by
    simp [shiftPairs, carriedPairs, List.map_map, Function.comp_def, operandName]
  rw [he, arrPairs, arrPairs, List.filterMap_reverse, List.mem_reverse]

/-- The name of the slot `s` of a function of `nArgs` arguments: an argument name below
    `nArgs`, a register name above. -/
def slotName (nArgs s : Nat) : String := if s < nArgs then argName s else regName s

theorem slotName_of_le {nArgs s : Nat} (h : nArgs ≤ s) : slotName nArgs s = regName s := by
  simp [slotName, Nat.not_lt.mpr h]

/-- **The array variables of a context are named in `S`** at the depth `d`: the slot of
    every variable of a stack-array type has its name in `S`. -/
def ArrNamed (S : String → Prop) (nArgs d : Nat) (Γ : Ctxt jasminDialect) : Prop :=
  ∀ i w m : Nat, Γ[i]? = some (JasminTy.stackArr w m) → S (slotName nArgs (d - 1 - i))

/-- **The array results are named in `S`**: the operand of every result of a stack-array
    type has its name in `S`. -/
def ResNamed (S : String → Prop) (ts : List JasminTy) (res : List LOperand) : Prop :=
  ∀ j w m : Nat, ts[j]? = some (JasminTy.stackArr w m) →
    ∃ o, res[j]? = some o ∧ S (operandName o)

theorem operandName_resolveVar (d nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) :
    operandName (resolveVar d nArgs argName (fun _ => none) v) =
      slotName nArgs (d - 1 - varIndex v) := by
  unfold resolveVar slotName
  dsimp only
  split <;> rfl

theorem arrNamed_var {S : String → Prop} {nArgs d : Nat} {Γ : Ctxt jasminDialect}
    (h : ArrNamed S nArgs d Γ) {w m : Nat} (v : Ctxt.Var Γ (.stackArr w m)) :
    S (operandName (resolveVar d nArgs argName (fun _ => none) v)) := by
  rw [operandName_resolveVar]
  exact h _ w m (RegionExportDefInitSort.getElem?_varIndex v)

theorem arrNamed_mono {S T : String → Prop} (hST : ∀ x, S x → T x) {nArgs d : Nat}
    {Γ : Ctxt jasminDialect} (h : ArrNamed S nArgs d Γ) : ArrNamed T nArgs d Γ :=
  fun i w m hi => hST _ (h i w m hi)

theorem arrNamed_append {S : String → Prop} {nArgs d : Nat} {cs Γ : Ctxt jasminDialect}
    (hΓ : ArrNamed S nArgs d Γ)
    (hcs : ∀ i w m, cs[i]? = some (JasminTy.stackArr w m) →
      S (slotName nArgs (d + cs.length - 1 - i))) :
    ArrNamed S nArgs (d + cs.length) (cs ++ Γ) := by
  intro i w m h
  by_cases hi : i < cs.length
  · rw [List.getElem?_append_left hi] at h
    exact hcs i w m h
  · rw [List.getElem?_append_right (by omega)] at h
    rw [show d + cs.length - 1 - i = d - 1 - (i - cs.length) by omega]
    exact hΓ _ w m h

theorem arrNamed_cons {S : String → Prop} {nArgs d : Nat} {t : JasminTy}
    {Γ : Ctxt jasminDialect} (hΓ : ArrNamed S nArgs d Γ)
    (ht : ∀ w m, t = .stackArr w m → S (slotName nArgs d)) :
    ArrNamed S nArgs (d + 1) (t :: Γ) := by
  intro i w m h
  cases i with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      simpa using ht w m h
  | succ i =>
      simp only [List.getElem?_cons_succ] at h
      rw [show d + 1 - 1 - (i + 1) = d - 1 - i by omega]
      exact hΓ i w m h

theorem resNamed_exprArgsHV {S : String → Prop} {nArgs d : Nat} {Γ : Ctxt jasminDialect}
    (h : ArrNamed S nArgs d Γ) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      ResNamed S ts (exprArgsHV d nArgs argName (fun _ => none) vs)
  | [], .nil => fun j w m hj => by simp at hj
  | _ :: _, .cons v rest => by
      intro j w m hj
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          exact ⟨_, rfl, arrNamed_var h v⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          exact resNamed_exprArgsHV h rest j w m hj

theorem srcs_of_resNamed {S : String → Prop} {cs : List JasminTy} {car : List String}
    {ops : List LOperand} (h : ResNamed S cs ops) :
    ∀ a ∈ arrPairs (carriedPairs cs car ops), S a.src := by
  intro a ha
  obtain ⟨i, o, hc, -, ho, he⟩ := mem_arrPairs_carriedPairs ha
  obtain ⟨o', ho', hS⟩ := h i _ _ hc
  rw [ho] at ho'
  cases ho'
  rw [he]
  exact hS

/-- The instruction of a binding whose operation is none of `stackLoad`, `stackStore` and
    `stackStoreImm` has no indexed operand and none of the mnemonics `LOADIDX`, `STOREIDX`
    and `STOREIMM`. -/
theorem bindOps_plainIdx (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hL : ∀ w n, e.op ≠ .stackLoad w n)
    (hS : ∀ w n, e.op ≠ .stackStore w n) (hI : ∀ w n k, e.op ≠ .stackStoreImm w n k)
    (d : Nat) : ∀ i ∈ bindOps nArgs e d, PlainIdx i := by
  have hreg := JasminLsemExportTransfer.exprArgs_isReg (curDepth := d) (nArgs := nArgs) e
  have hp : ∀ o ∈ exprArgs d nArgs argName (fun _ => none) e, NoIdxOp o := fun o ho => by
    obtain ⟨r, rfl⟩ := hreg o ho
    exact noIdxOp_reg r
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  revert hp hL hS hI
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  intro hL hS hI hp
  split
  · exact absurd rfl (hL _ _)
  · exact absurd rfl (hS _ _)
  all_goals first
    | exact plainIdx_opToLinstrR _ _ hp hL hS hI _
    | (split
       all_goals first
         | exact plainIdx_opToLinstrR _ _ hp hL hS hI _
         | (unfold JasminLsemShift.shiftLinstr
            refine plainIdx_lopn (by width_tag_ne) (by width_tag_ne) (by width_tag_ne)
              fun x hx => ?_
            simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false] at hx
            rcases hx with rfl | rfl | rfl
            · exact noIdxOp_reg _
            · exact hp _ (by simp)
            · exact noIdxOp_imm _))

/-- An operation that initialises an array without a source array: `stackZero` and
    `stackStoreImm`. -/
def arrInitB : JasminOp → Bool
  | .stackZero _ _ => true
  | .stackStoreImm _ _ _ => true
  | _ => false

/-- **No binding of the program initialises an array without a source array**: the program
    has no `stackZero` and no `stackStoreImm`. -/
def noArrInitB : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => !arrInitB e.op && noArrInitB k
  | _, _, .forLoop _ _ body k => noArrInitB body && noArrInitB k
  | _, _, .ifThenElse _ thn els k => noArrInitB thn && noArrInitB els && noArrInitB k
  | _, _, .whileLoop _ body k => noArrInitB body && noArrInitB k
  | _, _, .call _ _ k => noArrInitB k

/-- **The instruction of a binding defines its indexed bases before use**, and at an array
    type it stores to or zeroes the destination `regName d`, for an operation of the
    stack-memory fragment, at a context whose arrays are named in `S`. -/
theorem bindOps_idxOk (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : X86Backend.ExportCertFragment.opMemB e.op = true)
    {S : String → Prop} {d : Nat} (hS : ArrNamed S nArgs d Γ) :
    IdxOk S (bindOps nArgs e d) ∧
      ∀ w m, t = .stackArr w m → afterDst S (bindOps nArgs e d) (regName d) := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | stackLoad w n =>
      cases args with
      | cons a rest =>
        cases rest with
        | cons ix rest =>
          cases rest
          simp only [bindOps, straightOpsMem, exprArgs]
          rw [show exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons ix .nil)) =
            [resolveVar d nArgs argName (fun _ => none) a,
              resolveVar d nArgs argName (fun _ => none) ix] from rfl,
            resolveVar_isReg a, resolveVar_isReg ix]
          simp only [opToLinstrR]
          refine ⟨⟨idxIn_lopn (by decide) fun b y s hm => ?_, trivial⟩, fun w' m' ht => ?_⟩
          · simp only [List.mem_singleton, LOperand.arrIdx.injEq] at hm
            rw [hm.1]
            exact arrNamed_var hS a
          · subst ht
            cases heq
  | stackStore w n =>
      cases args with
      | cons a rest =>
        cases rest with
        | cons ix rest =>
          cases rest with
          | cons v rest =>
            cases rest
            simp only [bindOps, straightOpsMem, exprArgs]
            rw [show exprArgs.go d nArgs argName (fun _ => none)
                (.cons a (.cons ix (.cons v .nil))) =
              [resolveVar d nArgs argName (fun _ => none) a,
                resolveVar d nArgs argName (fun _ => none) ix,
                resolveVar d nArgs argName (fun _ => none) v] from rfl,
              resolveVar_isReg a, resolveVar_isReg ix, resolveVar_isReg v]
            simp only [opToLinstrR]
            refine ⟨⟨idxIn_lopn (by decide) fun b y s hm => ?_, trivial⟩, fun w' m' _ =>
              Or.inr (Or.inl (stDst_store _ _ _ _ _ _))⟩
            simp only [List.mem_cons, LOperand.arrIdx.injEq, reduceCtorEq, List.not_mem_nil,
              or_false] at hm
            rw [hm.1]
            exact arrNamed_var hS a
  | stackZero w n =>
      cases args
      simp only [bindOps, straightOpsMem, opToLinstrR]
      refine ⟨⟨idxIn_lopn (by decide) fun b y s hm => by simp at hm, trivial⟩, fun w' m' _ =>
        Or.inr (Or.inr (zeroDst?_zero _ _ _))⟩
  | stackStoreImm w n k =>
      cases args with
      | cons a rest =>
        cases rest with
        | cons v rest =>
          cases rest
          simp only [bindOps, straightOpsMem, exprArgs]
          rw [show exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons v .nil)) =
            [resolveVar d nArgs argName (fun _ => none) a,
              resolveVar d nArgs argName (fun _ => none) v] from rfl,
            resolveVar_isReg a, resolveVar_isReg v]
          simp only [opToLinstrR, List.cons_append, List.nil_append]
          refine ⟨⟨fun ds o ss he => ?_, trivial⟩, fun w' m' _ =>
            Or.inr (Or.inl (stDst_storeImm _ _ _ _))⟩
          simp only [LinstrR.Lopn.injEq] at he
          obtain ⟨rfl, rfl, rfl⟩ := he
          refine ⟨fun b y s hm => by simp at hm, fun _ b rest hs => ?_⟩
          simp only [List.cons.injEq, LOperand.reg.injEq] at hs
          rw [← hs.1]
          exact arrNamed_var hS a
  | _ =>
    first
      | (simp [X86Backend.ExportCertFragment.opMemB] at hop; done)
      | (refine ⟨idxOk_of_plainIdx (bindOps_plainIdx nArgs _ (fun _ _ h => by cases h)
            (fun _ _ h => by cases h) (fun _ _ _ h => by cases h) d), fun w m ht => ?_⟩
         subst ht
         cases heq)

/-- **The indexed bases of the export are defined before use**: for a program of the region
    route without `call`, exported at a depth of at least `nArgs` from names `S` that name its
    array variables, every indexed source of the code has its base in `S` or among the
    destinations of the stores and zeroings before it, and the array results are named after
    the code. -/
theorem exportR_idxOk (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → nArgs ≤ d →
      ∀ S : String → Prop, ArrNamed S nArgs d Γ →
        IdxOk S r.code ∧ ResNamed (afterDst S r.code) ts r.res := by
  induction p with
  | ret vs =>
      intro d n r h hd S hS
      simp only [exportR, Option.some.injEq] at h
      subst h
      exact ⟨trivial, resNamed_exprArgsHV hS vs⟩
  | var e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree] at hc
      intro d n r h hd S hS
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      obtain ⟨b1, b2⟩ := bindOps_idxOk nArgs e hp.1 hS
      have hS' : ArrNamed (afterDst S (bindOps nArgs e d)) nArgs (d + 1) (_ :: _) :=
        arrNamed_cons (arrNamed_mono (fun x h => le_afterDst x h) hS) fun w m ht => by
          rw [slotName_of_le hd]
          exact b2 w m ht
      obtain ⟨k1, k2⟩ := ih hp.2 hc (d + 1) n rk hk (by omega) _ hS'
      refine ⟨idxOk_append b1 (fun _ h => h) k1, ?_⟩
      show ResNamed (afterDst S (bindOps nArgs e d ++ rk.code)) _ rk.res
      rw [afterDst_append]
      exact k2
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h hd S hS
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hRi : ResNamed S cs (exprArgsHV d nArgs argName (fun _ => none) inits) :=
        resNamed_exprArgsHV hS inits
      have hshift : ∀ a ∈ arrPairs (shiftPairs d cs),
          ∃ a' ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length)
            (exprArgsHV d nArgs argName (fun _ => none) inits)), a'.dst = a.src := by
        intro a ha
        obtain ⟨i, o, hci, -, ho, he⟩ := mem_arrPairs_carriedPairs (mem_arrPairs_shiftPairs.mp ha)
        have hi : i < cs.length := (List.getElem?_eq_some_iff.mp hci).1
        rw [List.getElem?_map, carriedRegs_getElem? hi] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        obtain ⟨o', ho', -⟩ := hRi i _ _ hci
        obtain ⟨a', ha', e'⟩ := dst_mem_arrPairs_carriedPairs hci (carriedRegs_getElem? hi) ho'
        exact ⟨a', ha', by rw [e', he]; rfl⟩
      have hbody : ∀ T : String → Prop, (∀ x, S x → T x) →
          (∀ a ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length)
            (exprArgsHV d nArgs argName (fun _ => none) inits)), T a.dst) →
          IdxOk T b.code ∧ ∀ a ∈ arrPairs (carriedPairs cs (carriedRegs (d + 1) cs.length)
            b.res), afterDst T b.code a.src := by
        intro T hST hdst
        have hT : ArrNamed T nArgs (d + 1 + cs.length) (cs ++ HasWord64.word :: Γ) :=
          arrNamed_append (arrNamed_cons (arrNamed_mono hST hS) fun w m h => by cases h)
            fun i w m hi => by
              have hi' : i < cs.length := (List.getElem?_eq_some_iff.mp hi).1
              rw [slotName_of_le (by omega),
                show d + 1 + cs.length - 1 - i = d + 1 + (cs.length - 1 - i) by omega]
              obtain ⟨o', ho', -⟩ := hRi i w m hi
              obtain ⟨a, ha, e⟩ := dst_mem_arrPairs_carriedPairs hi (carriedRegs_getElem? hi') ho'
              rw [← e]
              exact hdst a ha
        obtain ⟨q1, q2⟩ := ihb hp.1 hc.1 _ _ b hb (by omega) T hT
        exact ⟨q1, srcs_of_resNamed q2⟩
      obtain ⟨f1, f2⟩ := forArrFrame_idxOk d n (noIdxOp_of_isReg (resolveVar_isReg count))
        b.depth (srcs_of_resNamed hRi) hshift hbody
      have hk' : ArrNamed (afterDst S (forArrFrame d n cs
          (exprArgsHV d nArgs argName (fun _ => none) inits)
          (resolveVar d nArgs argName (fun _ => none) count) b.code b.res b.depth x86Data))
          nArgs (d + cs.length) (cs ++ Γ) :=
        arrNamed_append (arrNamed_mono (fun x h => le_afterDst x h) hS) fun i w m hi => by
          have hi' : i < cs.length := (List.getElem?_eq_some_iff.mp hi).1
          rw [slotName_of_le (by omega),
            show d + cs.length - 1 - i = d + (cs.length - 1 - i) by omega]
          obtain ⟨a, ha, e⟩ := dst_mem_arrPairs_carriedPairs (o := .reg (regName
            (d + 1 + (cs.length - 1 - i)))) hi (carriedRegs_getElem? hi')
            (by rw [List.getElem?_map, carriedRegs_getElem? hi']; rfl)
          rw [← e]
          exact f2 a (mem_arrPairs_shiftPairs.mpr ha)
      obtain ⟨k1, k2⟩ := ihk hp.2 hc.2 _ _ rk hk (by omega) _ hk'
      refine ⟨idxOk_append f1 (fun _ h => h) k1, ?_⟩
      show ResNamed (afterDst S (_ ++ rk.code)) _ rk.res
      rw [afterDst_append]
      exact k2
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h hd S hS
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      obtain ⟨f1, f2⟩ := ifFrame_idxOk fn d n (rs := rs)
        (noIdxOp_of_isReg (resolveVar_isReg cond)) t.depth e.depth (S := S)
        (fun T hST => by
          obtain ⟨q1, q2⟩ := iht hp.1.1 hc.1.1 d _ t ht hd T (arrNamed_mono hST hS)
          exact ⟨q1, fun a ha => srcs_of_resNamed q2 a ha⟩)
        (fun T hST => by
          obtain ⟨q1, q2⟩ := ihe hp.1.2 hc.1.2 d _ e he hd T (arrNamed_mono hST hS)
          exact ⟨q1, fun a ha => srcs_of_resNamed q2 a ha⟩)
      obtain ⟨-, hRe⟩ := ihe hp.1.2 hc.1.2 d _ e he hd S hS
      have hk' : ArrNamed (afterDst S (ifFrame fn d n rs
          (resolveVar d nArgs argName (fun _ => none) cond) t.code t.res t.depth e.code e.res
          e.depth x86Data)) nArgs (d + rs.length) (rs ++ Γ) :=
        arrNamed_append (arrNamed_mono (fun x h => le_afterDst x h) hS) fun i w m hi => by
          have hi' : i < rs.length := (List.getElem?_eq_some_iff.mp hi).1
          rw [slotName_of_le (by omega),
            show d + rs.length - 1 - i = d + (rs.length - 1 - i) by omega]
          obtain ⟨o', ho', -⟩ := hRe i w m hi
          obtain ⟨a, ha, e⟩ := dst_mem_arrPairs_carriedPairs hi (carriedRegs_getElem? hi') ho'
          rw [← e]
          exact f2 a ha
      obtain ⟨k1, k2⟩ := ihk hp.2 hc.2 _ _ rk hk (by omega) _ hk'
      refine ⟨idxOk_append f1 (fun _ h => h) k1, ?_⟩
      show ResNamed (afterDst S (_ ++ rk.code)) _ rk.res
      rw [afterDst_append]
      exact k2
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true, List.all_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h hd S hS
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      have hcs : ∀ (T : String → Prop) (i w m : Nat), cs[i]? = some (JasminTy.stackArr w m) →
          T (slotName nArgs (d + cs.length - 1 - i)) := fun T i w m hi => by
        have := hp.1.1 _ (List.mem_of_getElem? hi)
        simp [isRegTy] at this
      obtain ⟨q1, -⟩ := ihb hp.1.2 hc.1 _ _ b hb (by omega) S
        (arrNamed_append hS (hcs S))
      have hres := exportR_res_isReg nArgs fn body _ _ b hb
      have f1 := whileFrame_idxOk d n cs.length
        (initOps := exprArgsHV d nArgs argName (fun _ => none) inits)
        (fun o ho => noIdxOp_of_isReg (exprArgsHV_isReg _ _ inits o ho))
        (flagOp := b.res.headD (.imm 0)) (by
          cases hr : b.res with
          | nil => exact noIdxOp_imm 0
          | cons o os => exact noIdxOp_of_isReg (hres o (by rw [hr]; simp)))
        (bodyOps := b.res.tail) (fun o ho => noIdxOp_of_isReg (hres o (List.mem_of_mem_tail ho)))
        b.depth q1
      have hk' : ArrNamed (afterDst S (whileFrame d n cs.length
          (exprArgsHV d nArgs argName (fun _ => none) inits) b.code (b.res.headD (.imm 0))
          b.res.tail b.depth x86Data)) nArgs (d + cs.length) (cs ++ Γ) :=
        arrNamed_append (arrNamed_mono (fun x h => le_afterDst x h) hS) (hcs _)
      obtain ⟨k1, k2⟩ := ihk hp.2 hc.2 _ _ rk hk (by omega) _ hk'
      refine ⟨idxOk_append f1 (fun _ h => h) k1, ?_⟩
      show ResNamed (afterDst S (_ ++ rk.code)) _ rk.res
      rw [afterDst_append]
      exact k2
  | call f args k _ =>
      simp [NFProg.callFree] at hc

theorem idxOk_resCopyCode {S : String → Prop} {src D : String} (m : Nat) (hs : S src)
    (hD : S D) : IdxOk S (resCopyCode src D m) := by
  have key : ∀ k, IdxOk S ((List.range k).flatMap (resCopyStep src D m)) ∧
      afterDst S ((List.range k).flatMap (resCopyStep src D m)) (copyName D k) := by
    intro k
    induction k with
    | zero => exact ⟨trivial, by simpa [copyName, afterDst] using hD⟩
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        refine ⟨idxOk_append ih.1 (fun _ h => h) (idxOk_cons_plain (plainIdx_movImmI _ _)
          ⟨idxIn_lopn (by decide) fun b y s hm => ?_,
            idxIn_lopn (by decide) fun b y s hm => ?_, trivial⟩), ?_⟩
        · simp only [List.mem_singleton, LOperand.arrIdx.injEq] at hm
          rw [hm.1]
          exact le_afterDst _ hs
        · simp only [List.mem_cons, LOperand.arrIdx.injEq, reduceCtorEq, List.not_mem_nil,
            or_false] at hm
          rw [hm.1]
          exact Or.inl ih.2
        · rw [afterDst_append]
          exact Or.inr (Or.inl (stDst_store _ _ _ _ _ _))
  exact (key m).1

/-- **The result copy defines its indexed bases before use** when the array result and the
    result buffer are named in `S`. -/
theorem idxOk_regionLprogCopy {S : String → Prop} (a : AbiNames) (ts : List JasminTy)
    {code : List LinstrRM} {res : List LOperand} (hres : ResNamed S ts res)
    (hD : a.outArg ≠ "" → S a.outArg) : IdxOk S (regionLprogCopy a none ts code res) := by
  unfold regionLprogCopy
  split
  · rename_i t
    split
    · rename_i src D m heq
      unfold resCopyOf at heq
      split at heq
      · rename_i w m' op
        split at heq
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
          obtain ⟨o, ho, hso⟩ := hres 0 w m' rfl
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
          subst ho
          exact idxOk_resCopyCode _ hso (hD hcond.1.1.1.2)
        · cases heq
      · cases heq
    · trivial
  · trivial

/-- The parameters of a word array of `σ` have a save slot: a decision. -/
def wordsSlotB (σ : AbiLayout) : Bool :=
  σ.args.all fun a => match a.kind with
    | .words _ => (abiSaveOfExt (exportReg a.reg)).isSome
    | .scalar => true

theorem argSlot_of_wordsSlotB {σ : AbiLayout} (hσ : wordsSlotB σ = true) {j : Nat}
    {a : AbiArg} {n : Nat} (ha : σ.args[j]? = some a) (hk : a.kind = .words n) :
    RegionPhysImg.ArgSlot σ j := by
  have := List.all_eq_true.mp hσ a (List.mem_of_getElem? ha)
  rw [hk] at this
  exact ⟨a, n, ha, hk, this⟩

/-- The result buffer of the direct route, when it is a name, is a word-array parameter of
    `σ` with a save slot. -/
theorem outArg_argSlotName {σ : AbiLayout} (hσ : wordsSlotB σ = true) (fname : String)
    (h : (nfAbiNames fname σ).outArg ≠ "") : ArgSlotName σ (nfAbiNames fname σ).outArg := by
  simp only [nfAbiNames] at h ⊢
  cases ho : nfOutIdx σ with
  | none => simp [ho] at h
  | some j =>
      simp only [Option.map_some, Option.getD_some]
      refine ⟨j, rfl, ?_⟩
      unfold nfOutIdx at ho
      split at ho
      · rename_i r k _
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp ho
        have hp := List.find?_some hq
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        have hm := List.mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some hq)
        exact argSlot_of_wordsSlotB hσ hm hp.2
      · cases ho

/-- **The array variables of the context of the direct route are word-array parameters with a
    save slot**, at the depth and the argument count of the context. -/
theorem arrNamed_nfCtx {σ : AbiLayout} (hσ : wordsSlotB σ = true) :
    ArrNamed (ArgSlotName σ) (nfCtx σ).length (nfCtx σ).length (nfCtx σ) := by
  intro i w m h
  have hi : i < (nfCtx σ).length := (List.getElem?_eq_some_iff.mp h).1
  rw [slotName, ite_eq_left (by omega)]
  refine ⟨_, rfl, ?_⟩
  simp only [nfCtx, CryptoToJasminCom.mapCtx, Hax.ImpToNF.entryCtx, NFToRoute.abiEntry,
    Hax.NFToCat.abiParamsArr, List.map_reverse, List.map_map, List.length_reverse,
    List.length_map] at h hi ⊢
  rw [List.getElem?_reverse (by simpa using hi), List.getElem?_map, List.length_map] at h
  obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp h
  cases hk : a.kind with
  | scalar =>
      simp only [Function.comp_apply, hk] at he
      cases he
  | words n => exact argSlot_of_wordsSlotB hσ ha hk

/-- **The coalescing renaming sends every array name into `P`** when along the code every
    indexed base is defined before use (`IdxOk`) from names at which `P` holds and `P` holds
    at the destination of every zeroing: the renaming sends the bases of `IdxIn` and the
    destination of every zeroing (`RootIn`) into `P`. -/
theorem canonMemrefName_aliasTab_of_idxOk (P : String → Prop) {C : List LinstrRM}
    {S : String → Prop} (hC : IdxOk S C) (hS : ∀ x, S x → P x)
    (hZ : ∀ i ∈ C, ∀ z, X86Backend.ImageStraightRoute.zeroDst? i = some z → P z) :
    ∀ i ∈ C, RootIn (fun x => P (canonMemrefName (X86Backend.ImageStraightRoute.aliasTab [] C)
      x)) i := by
  let G : Std.HashMap String String → String → Prop := fun m x => P (canonMemrefName m x)
  let Inv : Std.HashMap String String → Prop := fun m => ∀ x, G m x ∨ m.getD x x = x
  have step : ∀ (S : String → Prop) (m : Std.HashMap String String) (i : LinstrRM),
      IdxIn S i → (∀ x, S x → G m x) → Inv m →
      (∀ z, X86Backend.ImageStraightRoute.zeroDst? i = some z → P z) →
      (∀ x, G m x → G (X86Backend.ImageStraightRoute.aliasStepO [] m i) x) ∧
      (∀ x, addDst S i x → G (X86Backend.ImageStraightRoute.aliasStepO [] m i) x) ∧
      Inv (X86Backend.ImageStraightRoute.aliasStepO [] m i) := by
    intro S m i hi hSm hinv hzi
    have hzG : ∀ z, X86Backend.ImageStraightRoute.zeroDst? i = some z → G m z := by
      intro z hz
      rcases hinv z with h | h
      · exact h
      · show P (m.getD z z)
        rw [h]
        exact hzi z hz
    rw [aliasStepO_nil]
    cases hp : stPair i with
    | none =>
        refine ⟨fun x h => h, fun x hx => ?_, hinv⟩
        rcases hx with hx | hx | hx
        · exact hSm x hx
        · simp [stDst, hp] at hx
        · exact hzG x hx
    | some p =>
        obtain ⟨dst, base⟩ := p
        have hb : G m base := by
          rcases stPair_some hp with ⟨opn, y, s, rest, he⟩ | ⟨rest, he⟩
          · exact hSm _ ((hi _ _ _ he).1 base y s List.mem_cons_self)
          · exact hSm _ ((hi _ _ _ he).2 rfl base rest rfl)
        have hins : ∀ x, G m x ∨ x = dst → G (m.insert dst (m.getD base base)) x := by
          intro x hx
          show P ((m.insert dst (m.getD base base)).getD x x)
          rw [Std.HashMap.getD_insert]
          by_cases h : dst = x
          · subst h
            simp only [beq_self_eq_true, ite_true]
            exact hb
          · simp only [beq_iff_eq, h, ite_false]
            rcases hx with hx | rfl
            · exact hx
            · exact absurd rfl h
        refine ⟨fun x h => hins x (Or.inl h), fun x hx => ?_, fun x => ?_⟩
        · rcases hx with hx | hx | hx
          · exact hins x (Or.inl (hSm x hx))
          · simp only [stDst, hp, Option.map_some, Option.some.injEq] at hx
            exact hins x (Or.inr hx.symm)
          · exact hins x (Or.inl (hzG x hx))
        · by_cases h : dst = x
          · exact Or.inl (hins x (Or.inr h.symm))
          · rcases hinv x with hx | hx
            · exact Or.inl (hins x (Or.inl hx))
            · right
              rw [Std.HashMap.getD_insert]
              simp only [beq_iff_eq, h, ite_false]
              exact hx
  have main : ∀ (C : List LinstrRM) (S : String → Prop) (m : Std.HashMap String String),
      IdxOk S C → (∀ x, S x → G m x) → Inv m →
      (∀ i ∈ C, ∀ z, X86Backend.ImageStraightRoute.zeroDst? i = some z → P z) →
      (∀ x, G m x → G (C.foldl (X86Backend.ImageStraightRoute.aliasStepO []) m) x) ∧
      ∀ i ∈ C, RootIn (G (C.foldl (X86Backend.ImageStraightRoute.aliasStepO []) m)) i := by
    intro C
    induction C with
    | nil => exact fun _ _ _ _ _ _ => ⟨fun _ h => h, fun _ h => by cases h⟩
    | cons i C ih =>
        intro S m hok hSm hinv hz
        obtain ⟨s1, s2, s3⟩ := step S m i hok.1 hSm hinv (hz i List.mem_cons_self)
        obtain ⟨i1, i2⟩ := ih (addDst S i) _ hok.2 s2 s3
          fun j hj => hz j (List.mem_cons_of_mem _ hj)
        refine ⟨fun x h => i1 x (s1 x h), fun j hj => ?_⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact ⟨idxIn_mono (fun x h => i1 x (s1 x (hSm x h))) hok.1,
            fun z h => i1 z (s2 z (Or.inr (Or.inr h)))⟩
        · exact i2 j hj
  have hinv0 : Inv {} := fun x => by
    right
    exact Std.HashMap.getD_empty
  exact (main C S {} hC (fun x hx => by
    show P (({} : Std.HashMap String String).getD x x)
    rw [Std.HashMap.getD_empty]
    exact hS x hx) hinv0 hZ).2

/-! ## 6b. No constant-index array write -/

/-- The instruction is no `ZEROARR` and no `STOREIMM`. -/
def NoArrImm (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss → o ≠ "ZEROARR" ∧ o ≠ "STOREIMM"

theorem noArrImm_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") : NoArrImm (.Lopn ds o ss) := by
  intro ds' o' ss' he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact h

theorem noArrImm_of_not_lopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : NoArrImm w :=
  fun _ _ _ e => absurd e (h _ _ _)

/-- An instruction that is no `ZEROARR` is no zeroing. -/
theorem zeroDst?_of_noArrImm {i : LinstrRM} (h : NoArrImm i.1) :
    X86Backend.ImageStraightRoute.zeroDst? i = none := by
  unfold X86Backend.ImageStraightRoute.zeroDst?
  split
  · rename_i d opn ss hw
    rw [ite_eq_right (h _ _ _ hw).1]
  · rfl

theorem isArrImmB_of_noArrImm {w : LinstrR} (h : NoArrImm w) (hu : UntagP w) :
    X86Backend.PhysImgEmit.isArrImmB w = false := by
  cases w with
  | Lopn ds o ss =>
    obtain ⟨h1, h2⟩ := h ds o ss rfl
    have ht := hu ds o ss rfl
    simp [X86Backend.PhysImgEmit.isArrImmB,
      X86Backend.PhysImgEmit.untagCaret_ne_of_accUntagged ht (by simp) h1,
      X86Backend.PhysImgEmit.untagCaret_ne_of_accUntagged ht (by simp) h2]
  | _ => rfl

/-- A string that begins with two characters other than `ZE` and `ST` is neither `ZEROARR`
    nor `STOREIMM` after any suffix. -/
theorem ne_arrImm_append {p : String} (s : String)
    (h : 2 ≤ p.toList.length ∧ p.toList.take 2 ≠ ['Z', 'E'] ∧ p.toList.take 2 ≠ ['S', 'T']) :
    p ++ s ≠ "ZEROARR" ∧ p ++ s ≠ "STOREIMM" := by
  have ht : (p ++ s).toList.take 2 = p.toList.take 2 := by
    rw [String.toList_append, List.take_append_of_le_length h.1]
  refine ⟨fun e => h.2.1 ?_, fun e => h.2.2 ?_⟩ <;> rw [← ht, e] <;> decide

/-- The instruction of an operation other than `stackZero` and `stackStoreImm` is no
    `ZEROARR` and no `STOREIMM`. -/
theorem noArrImm_opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand)
    (hz : arrInitB op = false) : NoArrImm (opToLinstrR op dst srcs) := by
  cases op with
  | stackZero w n => simp [arrInitB] at hz
  | stackStoreImm w n k => simp [arrInitB] at hz
  | vsimd op =>
    show NoArrImm (.Lopn [.reg dst] op.mnemonic srcs)
    refine noArrImm_lopn ⟨?_, ?_⟩ <;> unfold SimdOp.mnemonic <;> split <;> first
      | decide
      | exact (ne_arrImm_append _ (by decide)).1
      | exact (ne_arrImm_append _ (by decide)).2
  | vymm op =>
    show NoArrImm (.Lopn [.reg dst] op.jasminMnemonic srcs)
    refine noArrImm_lopn ⟨?_, ?_⟩ <;> cases op <;> first
      | decide
      | (rw [YmmDialect.YmmOp.jasminMnemonic]
         first
           | exact (ne_arrImm_append _ (by decide)).1
           | exact (ne_arrImm_append _ (by decide)).2)
  | _ =>
    simp only [opToLinstrR]
    (repeat' split) <;> refine noArrImm_lopn ⟨?_, ?_⟩
    all_goals first
      | width_tag_ne
      | decide
      | exact (ne_arrImm_append _ (by decide)).1
      | exact (ne_arrImm_append _ (by decide)).2
      | (unfold castWMnem; repeat' split
         all_goals decide)
      | (unfold encodeCallW; simp only [String.append_assoc]
         first
           | exact (ne_arrImm_append _ (by decide)).1
           | exact (ne_arrImm_append _ (by decide)).2)

/-- The instruction of a binding whose operation is no array initialisation is no `ZEROARR`
    and no `STOREIMM`. -/
theorem bindOps_noArrImm (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hz : arrInitB e.op = false) (d : Nat) :
    ∀ i ∈ bindOps nArgs e d, NoArrImm i.1 := by
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  revert hz
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  intro hz
  split
  all_goals first
    | exact noArrImm_opToLinstrR _ _ _ hz
    | (dsimp only; exact noArrImm_opToLinstrR _ _ _ hz)
    | (split
       all_goals first
         | exact noArrImm_opToLinstrR _ _ _ hz
         | (unfold JasminLsemShift.shiftLinstr
            exact noArrImm_lopn ⟨by width_tag_ne, by width_tag_ne⟩))

theorem noArrImm_movI (dst : String) (src : LOperand) : NoArrImm (movI dst src).1 :=
  noArrImm_lopn (by unfold withWidthTag; decide)

theorem noArrImm_labelI (l : LLabel) : NoArrImm (labelI l).1 :=
  noArrImm_of_not_lopn fun _ _ _ e => by cases e

theorem noArrImm_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, NoArrImm i.1) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, NoArrImm i.1 := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact noArrImm_lopn (by unfold withWidthTag; decide)
    · exact noArrImm_of_not_lopn fun _ _ _ e => by cases e
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact noArrImm_lopn (by unfold withWidthTag; decide)
    · exact noArrImm_of_not_lopn fun _ _ _ e => by cases e

theorem noArrImm_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, NoArrImm i.1 := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact noArrImm_movI _ _

theorem noArrImm_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, NoArrImm i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi <;>
    exact noArrImm_movI _ _

theorem noArrImm_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, NoArrImm i.1 := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact noArrImm_lopn (by decide)

theorem noArrImm_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, NoArrImm i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact noArrImm_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact noArrImm_movI _ _

theorem noArrImm_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, NoArrImm i.1 := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact noArrImm_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact noArrImm_arrMoves _ _ _ i hi

theorem noArrImm_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, NoArrImm i.1 := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact noArrImm_lopn (by unfold withWidthTag; decide)

theorem noArrImm_flagWord (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord x86Data r z op, NoArrImm i.1 := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact noArrImm_movI _ _
    · exact noArrImm_movI _ _
    · exact noArrImm_lopn (by unfold withWidthTag; decide)
  · rw [List.mem_singleton.mp hi]
    exact noArrImm_movI _ _

theorem noArrImm_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, NoArrImm i.1 := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact noArrImm_movI _ _
      · exact noArrImm_arrParMoves _ _ _ _ i hi
  · exact noArrImm_parMoves _ _ _ i hi

/-- **A predicate that holds at every instruction without `ZEROARR` and `STOREIMM` and at
    every instruction of the body holds along the frame of a `for` loop.** -/
theorem forArrFrame_forall (Q : LinstrRM → Prop) (hQ : ∀ i, NoArrImm i.1 → Q i) (d n : Nat)
    (cs : List JasminTy) (initOps : List LOperand)
    (countOp : LOperand) (bodyC : List LinstrRM) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, Q i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, Q i := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact hQ _ (noArrImm_movI _ _)
  · exact hQ _ (noArrImm_typedMoves _ _ _ i hi)
  · exact hQ _ (noArrImm_seedMoves _ _ i hi)
  · exact hQ _ (noArrImm_x86Guards.1 _ n _ i hi)
  · exact hQ _ (noArrImm_labelI _)
  · exact hb i hi
  · exact hQ _ (noArrImm_movI _ _)
  · exact hQ _ (noArrImm_arrParMoves _ _ _ _ i hi)
  · exact hQ _ (noArrImm_parMoves _ _ _ i hi)
  · exact hQ _ (noArrImm_advanceOps _ _ i hi)
  · exact hQ _ (noArrImm_x86Guards.2 _ _ i hi)
  · exact hQ _ (noArrImm_labelI _)
  · exact hQ _ (noArrImm_movI _ _)
  · exact hQ _ (noArrImm_typedMoves _ _ _ i hi)

/-- The frame of a `while` loop keeps a predicate as `forArrFrame_forall` does. -/
theorem whileFrame_forall (Q : LinstrRM → Prop) (hQ : ∀ i, NoArrImm i.1 → Q i)
    (d n nCar : Nat) (initOps : List LOperand) (bodyC : List LinstrRM)
    (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, Q i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, Q i := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact hQ _ (noArrImm_seedMoves _ _ i hi)
  · exact hQ _ (noArrImm_labelI _)
  · exact hb i hi
  · exact hQ _ (noArrImm_flagWord _ _ _ i hi)
  · exact hQ _ (noArrImm_parMoves _ _ _ i hi)
  · exact hQ _ (noArrImm_x86Guards.2 _ _ i hi)

/-- The frame of a conditional keeps a predicate as `forArrFrame_forall` does. -/
theorem ifFrame_forall (Q : LinstrRM → Prop) (hQ : ∀ i, NoArrImm i.1 → Q i) (fn : String)
    (d n : Nat) (rs : List JasminTy) (condOp : LOperand)
    (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat) (elsC : List LinstrRM)
    (elsOps : List LOperand) (elsD : Nat) (ht : ∀ i ∈ thnC, Q i)
    (he : ∀ i ∈ elsC, Q i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, Q i := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact hQ _ (noArrImm_flagWord _ _ _ i hi)
  · exact hQ _ (noArrImm_x86Guards.1 _ n _ i hi)
  · exact hQ _ (noArrImm_labelI _)
  · exact ht i hi
  · exact hQ _ (noArrImm_ifResMoves _ _ _ _ i hi)
  · exact hQ _ (noArrImm_movI _ _)
  · exact hQ _ (noArrImm_x86Guards.2 _ _ i hi)
  · exact hQ _ (noArrImm_labelI _)
  · exact he i hi
  · exact hQ _ (noArrImm_ifResMoves _ _ _ _ i hi)
  · exact hQ _ (noArrImm_labelI _)

/-- **A predicate that holds at every instruction without `ZEROARR` and `STOREIMM` and at
    every instruction of every binding holds along the export** of a program without
    `call`. -/
theorem exportR_forall (Q : LinstrRM → Prop) (hQ : ∀ i, NoArrImm i.1 → Q i) (nArgs : Nat)
    (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (hc : p.callFree = true)
    (hb : ∀ {Γ' : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ' t) (d : Nat),
      ∀ i ∈ bindOps nArgs e d, Q i) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, Q i := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [NFProg.callFree] at hc
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact hb e d i hi
      · exact ih hc _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb', rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_forall Q hQ _ _ _ _ _ _ _ _ (ihb hc.1 _ _ _ hb') i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_forall Q hQ _ _ _ _ _ _ _ _ _ _ _ (iht hc.1.1 _ _ _ ht)
          (ihe hc.1.2 _ _ _ he) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb', rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_forall Q hQ _ _ _ _ _ _ _ _ (ihb hc.1 _ _ _ hb') i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | call f args k ih =>
      simp [NFProg.callFree] at hc

theorem immCode_of_noArrImm {i : LinstrRM} (h : NoArrImm i.1) : ImmCode i :=
  ⟨fun ds ss he => absurd rfl (h ds _ ss he).1, fun ds ss he => absurd rfl (h ds _ ss he).2⟩

/-- **The instruction of a binding has the form `ImmCode`**: a `stackZero` exports the
    zero-tagged `ZEROARR [regName d] [#n, #w]`, a `stackStoreImm` the constant-store-tagged
    `STOREIMM` over its two register sources and its index, and no other operation exports
    either mnemonic. -/
theorem bindOps_immCode (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, ImmCode i := by
  obtain ⟨op, heq, args⟩ := e
  cases op with
  | stackZero w n =>
      cases args
      intro i hi
      simp only [bindOps, straightOpsMem, opToLinstrR, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      subst hi
      exact ⟨fun _ _ _ => ⟨_, n, w, w, n, rfl⟩, fun _ _ he => by
        simp only [LinstrR.Lopn.injEq] at he
        exact absurd he.2.1 (by decide)⟩
  | stackStoreImm w n k =>
      cases args with
      | cons a rest =>
        cases rest with
        | cons v rest =>
          cases rest
          intro i hi
          simp only [bindOps, straightOpsMem, exprArgs, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          subst hi
          rw [show exprArgs.go d nArgs argName (fun _ => none) (.cons a (.cons v .nil)) =
            [resolveVar d nArgs argName (fun _ => none) a,
              resolveVar d nArgs argName (fun _ => none) v] from rfl,
            resolveVar_isReg a, resolveVar_isReg v]
          simp only [opToLinstrR, List.cons_append, List.nil_append]
          exact ⟨fun _ _ he => by
            simp only [LinstrR.Lopn.injEq] at he
            exact absurd he.2.1 (by decide), fun _ _ _ => ⟨_, _, _, k, w, n, rfl⟩⟩
  | _ =>
      exact fun i hi => immCode_of_noArrImm (bindOps_noArrImm nArgs _ (by simp [arrInitB]) d
        i hi)

/-- **The export of a program without array initialisation has no `ZEROARR` and no
    `STOREIMM`**: these come only from `stackZero` and `stackStoreImm`, which `noArrInitB`
    refuses. -/
theorem exportR_noArrImm (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true)
    (hz : noArrInitB p = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, NoArrImm i.1 := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [NFProg.callFree] at hc
      simp only [noArrInitB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hz
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact bindOps_noArrImm nArgs e hz.1 d i hi
      · exact ih hc hz.2 _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [noArrInitB, Bool.and_eq_true] at hz
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_forall _ (fun _ h => h) _ _ _ _ _ _ _ _ (ihb hc.1 hz.1 _ _ _ hb) i hi
      · exact ihk hc.2 hz.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [noArrInitB, Bool.and_eq_true] at hz
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_forall _ (fun _ h => h) _ _ _ _ _ _ _ _ _ _ _ (iht hc.1.1 hz.1.1 _ _ _ ht)
          (ihe hc.1.2 hz.1.2 _ _ _ he) i hi
      · exact ihk hc.2 hz.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      simp only [noArrInitB, Bool.and_eq_true] at hz
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_forall _ (fun _ h => h) _ _ _ _ _ _ _ _ (ihb hc.1 hz.1 _ _ _ hb) i hi
      · exact ihk hc.2 hz.2 _ _ _ hk i hi
  | call f args k ih =>
      simp [NFProg.callFree] at hc

theorem noArrImm_renArr (σ : String → String) {i : LinstrRM} (h : NoArrImm i.1)
    (hs : ShapeB i.1) : NoArrImm (X86Backend.ImageCoalesceCfg.renArr σ i).1 := by
  obtain ⟨w, t⟩ := i
  cases w with
  | Lopn ds o ss =>
      have ho := h ds o ss rfl
      have hm : MnemB o := hs.2 ds o ss rfl
      unfold X86Backend.ImageCoalesceCfg.renArr
      split
      all_goals first
        | (simp only [X86Backend.ImageCoalesceCfg.renCallW, shadowCall?_of_mnemB hm]; exact h)
        | (simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
             X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm]
           repeat' split
           all_goals first
             | exact noArrImm_lopn ho
             | (rename_i heq _
                simp only [LinstrR.Lopn.injEq] at heq
                obtain ⟨-, rfl, -⟩ := heq
                exact noArrImm_lopn ho))
  | _ =>
      unfold X86Backend.ImageCoalesceCfg.renArr
      split <;> exact h

theorem noArrImm_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, NoArrImm i.1) :
    ∀ i ∈ backEdgePins C, NoArrImm i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, NoArrImm i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact noArrImm_lopn (by decide)
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

theorem noArrImm_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, NoArrImm i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, NoArrImm i.li_i := by
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      exact noArrImm_lopn (h j hj ds o ss heq)
    · exact h j hj

/-- **The allocator input body has no `ZEROARR` and no `STOREIMM`**, at a result other than
    one register, when the code given to the renaming (the export followed by its result copy)
    has none and has the shape `ShapeB`. -/
theorem noArrImm_regionAllocBody (a : AbiNames) (nArgs : Nat) {ts : List JasminTy}
    (r : Exported) (hts : ∀ w, ts ≠ [.reg w])
    (hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, NoArrImm i.1 ∧ ShapeB i.1) :
    ∀ i ∈ regionAllocBody a nArgs ts r, NoArrImm i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res),
      NoArrImm i.1 := by
    refine noArrImm_backEdgePins fun i hi => ?_
    rcases mem_pinSelfMoves hi with hi | ⟨t, b, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact noArrImm_renArr _ (hC j hj).1 (hC j hj).2
    · exact noArrImm_lopn (by decide)
    · exact noArrImm_lopn (by decide)
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact noArrImm_lopn (by decide)
      · cases hi
    · refine noArrImm_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact noArrImm_lopn (by decide)
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]
          exact noArrImm_of_not_lopn fun _ _ _ e => by cases e

theorem noArrImm_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, NoArrImm i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact noArrImm_movI _ _
      · exact noArrImm_lopn (by decide)
      · exact noArrImm_lopn (by decide)
    · cases hi
  · cases hi

/-- **The code given to the renaming has the form `ImmCode`**, for a program without
    `call`. -/
theorem exportR_immCode_copy (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r) :
    ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, ImmCode i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact exportR_forall ImmCode (fun _ h => immCode_of_noArrImm h) _ _ p hc
      (fun e d => bindOps_immCode _ e d) _ _ r hr i hi
  · exact immCode_of_noArrImm (noArrImm_regionLprogCopy a ts r.code r.res i hi)

/-! ## The untagged access mnemonics of the export -/

theorem untagP_movI (dst : String) (src : LOperand) : UntagP (movI dst src).1 :=
  untagP_lopn (by acc_untagged)

theorem untagP_labelI (l : LLabel) : UntagP (labelI l).1 :=
  untagP_of_not_lopn fun _ _ _ e => by cases e

theorem untagP_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, UntagP i.1) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, UntagP i.1 := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact untagP_lopn (by acc_untagged)
    · exact untagP_of_not_lopn fun _ _ _ e => by cases e
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact untagP_lopn (by acc_untagged)
    · exact untagP_of_not_lopn fun _ _ _ e => by cases e

theorem untagP_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, UntagP i.1 := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact untagP_movI _ _

theorem untagP_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, UntagP i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi <;>
    exact untagP_movI _ _

theorem untagP_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, UntagP i.1 := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact untagP_lopn (by acc_untagged)

theorem untagP_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, UntagP i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact untagP_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact untagP_movI _ _

theorem untagP_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, UntagP i.1 := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact untagP_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact untagP_arrMoves _ _ _ i hi

theorem untagP_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, UntagP i.1 := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact untagP_lopn (by acc_untagged)

theorem untagP_flagWord (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord x86Data r z op, UntagP i.1 := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact untagP_movI _ _
    · exact untagP_movI _ _
    · exact untagP_lopn (by acc_untagged)
  · rw [List.mem_singleton.mp hi]
    exact untagP_movI _ _

theorem untagP_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, UntagP i.1 := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact untagP_movI _ _
      · exact untagP_arrParMoves _ _ _ _ i hi
  · exact untagP_parMoves _ _ _ i hi

theorem forArrFrame_untagP (d n : Nat) (cs : List JasminTy) (initOps : List LOperand)
    (countOp : LOperand) (bodyC : List LinstrRM) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, UntagP i.1) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, UntagP i.1 := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact untagP_movI _ _
  · exact untagP_typedMoves _ _ _ i hi
  · exact untagP_seedMoves _ _ i hi
  · exact untagP_x86Guards.1 _ n _ i hi
  · exact untagP_labelI _
  · exact hb i hi
  · exact untagP_movI _ _
  · exact untagP_arrParMoves _ _ _ _ i hi
  · exact untagP_parMoves _ _ _ i hi
  · exact untagP_advanceOps _ _ i hi
  · exact untagP_x86Guards.2 _ _ i hi
  · exact untagP_labelI _
  · exact untagP_movI _ _
  · exact untagP_typedMoves _ _ _ i hi

theorem whileFrame_untagP (d n nCar : Nat) (initOps : List LOperand) (bodyC : List LinstrRM)
    (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, UntagP i.1) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, UntagP i.1 := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact untagP_seedMoves _ _ i hi
  · exact untagP_labelI _
  · exact hb i hi
  · exact untagP_flagWord _ _ _ i hi
  · exact untagP_parMoves _ _ _ i hi
  · exact untagP_x86Guards.2 _ _ i hi

theorem ifFrame_untagP (fn : String) (d n : Nat) (rs : List JasminTy) (condOp : LOperand)
    (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat) (elsC : List LinstrRM)
    (elsOps : List LOperand) (elsD : Nat) (ht : ∀ i ∈ thnC, UntagP i.1)
    (he : ∀ i ∈ elsC, UntagP i.1) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, UntagP i.1 := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact untagP_flagWord _ _ _ i hi
  · exact untagP_x86Guards.1 _ n _ i hi
  · exact untagP_labelI _
  · exact ht i hi
  · exact untagP_ifResMoves _ _ _ _ i hi
  · exact untagP_movI _ _
  · exact untagP_x86Guards.2 _ _ i hi
  · exact untagP_labelI _
  · exact he i hi
  · exact untagP_ifResMoves _ _ _ _ i hi
  · exact untagP_labelI _

/-- **The mnemonic of the instruction of an operation is untagged** when its untagged form is
    an array access mnemonic. -/
theorem untagP_opToLinstrR (op : JasminOp) (dst : String) (srcs : List LOperand) :
    UntagP (opToLinstrR op dst srcs) := by
  cases op with
  | vsimd op =>
    show UntagP (.Lopn [.reg dst] op.mnemonic srcs)
    refine untagP_lopn ?_
    unfold SimdOp.mnemonic
    split <;> acc_untagged
  | vymm op =>
    show UntagP (.Lopn [.reg dst] op.jasminMnemonic srcs)
    refine untagP_lopn ?_
    cases op <;> (rw [YmmDialect.YmmOp.jasminMnemonic]; acc_untagged)
  | _ =>
    simp only [opToLinstrR]
    (repeat' split) <;> refine untagP_lopn ?_
    all_goals first
      | acc_untagged
      | ((with_reducible refine accUntagged_withWidthTag _ ?_)
         first
           | (unfold binOpName; split <;> decide)
           | (unfold cmpName; split <;> decide))
      | (unfold castWMnem; repeat' split
         all_goals acc_untagged)
      | (unfold encodeCallW; simp only [String.append_assoc]; acc_untagged)

theorem bindOps_untagP (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ i ∈ bindOps nArgs e d, UntagP i.1 := by
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  split
  all_goals first
    | (dsimp only; exact untagP_opToLinstrR _ _ _)
    | (split
       all_goals first
         | exact untagP_opToLinstrR _ _ _
         | (unfold JasminLsemShift.shiftLinstr
            exact untagP_lopn (by acc_untagged)))

/-- **The mnemonics of the export of a program without `call` are untagged** when their
    untagged form is an array access mnemonic. -/
theorem exportR_untagP (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, UntagP i.1 := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [NFProg.callFree] at hc
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact bindOps_untagP nArgs e d i hi
      · exact ih hc _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_untagP _ _ _ _ _ _ _ _ (ihb hc.1 _ _ _ hb) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_untagP _ _ _ _ _ _ _ _ _ _ _ (iht hc.1.1 _ _ _ ht)
          (ihe hc.1.2 _ _ _ he) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_untagP _ _ _ _ _ _ _ _ (ihb hc.1 _ _ _ hb) i hi
      · exact ihk hc.2 _ _ _ hk i hi
  | call f args k ih =>
      simp [NFProg.callFree] at hc

theorem untagP_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, UntagP i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact untagP_movI _ _
      · exact untagP_lopn (by acc_untagged)
      · exact untagP_lopn (by acc_untagged)
    · cases hi
  · cases hi

/-- **The code given to the renaming has untagged access mnemonics**, for a program without
    `call`. -/
theorem exportR_untagP_copy (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r) :
    ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, UntagP i.1 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact exportR_untagP _ _ p hc _ _ r hr i hi
  · exact untagP_regionLprogCopy a ts r.code r.res i hi

/-- **Every zeroing of the code given to the renaming zeroes the result root**: the export
    names `a`, the result types `ts` and the export `r` have a result alias `(D, src)`, and the
    destination of every `ZEROARR` of the code `C` (the export followed by its result copy) is
    the result root `resRoot? [] D src C`, the root of the returned array that is zeroed before
    any other use and stands for the result buffer `D`. -/
def ZeroAtRoot (a : AbiNames) (ts : List JasminTy) (r : Exported) : Prop :=
  ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, ∀ z,
    X86Backend.ImageStraightRoute.zeroDst? i = some z →
      ∃ D src, resAliasOf none (some a.outArg) ts r.res = some (D, src) ∧
        X86Backend.ImageStraightRoute.resRoot? [] D src
          (r.code ++ regionLprogCopy a none ts r.code r.res) = some z

/-- A program without array initialisation zeroes no array, so every zeroing is at the result
    root. -/
theorem zeroAtRoot_of_noArrInitB (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hc : p.callFree = true) (hz : noArrInitB p = true)
    {r : Exported} (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r) :
    ZeroAtRoot a ts r := by
  intro i hi z h
  have hn : NoArrImm i.1 := by
    rcases List.mem_append.mp hi with hi | hi
    · exact exportR_noArrImm _ a.fname p hc hz _ _ r hr i hi
    · exact noArrImm_regionLprogCopy _ ts r.code r.res i hi
  rw [zeroDst?_of_noArrImm hn] at h
  cases h

/-! ## 7. The export body in the image class -/

/-- **The export body of the region route is in the image class at the slot map of the
    gate**, `physImgB_regionExport` with `harr` discharged (`harr_regionAllocBody`) and `hacc`
    reduced to three conditions on the code `C` of the export followed by its result copy:
    every instruction of `C` has the access forms `AccCode` and `ImmCode`, and the coalescing
    renaming `canonMemrefName (resAliasTab [] rr C)` at the result alias of the allocation
    sends the array names (`RootIn`) of every instruction of `C` to the name `argName j` of a
    word-array parameter `j` of `σ` with a save slot. -/
theorem physImgB_regionExport_param (fname : String) (σ : AbiLayout) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fname p Γ.length 0 x86Data = some r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (hC : ∀ i ∈ r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res,
      AccCode i)
    (hI : ∀ i ∈ r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res,
      ImmCode i)
    (hroot : ∀ i ∈ r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res,
      RootIn (fun x => ArgSlotName σ (canonMemrefName (resAliasTab []
        (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)
        (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res)) x)) i)
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String)) :
    JasminLsemAddrImage.physImgB
      (X86Backend.ImageStraightCells.slotArrC R
        (X86Backend.ImageAddrRoute.slotRen
          (X86Backend.ImageAddrRoute.slotArrOf σ exportReg)
          (JasminLsemRenameLoop.renOf ps)))
      (calleeAllocCert none
        { fd0 with lfd_body :=
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
        (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
        (nfAbiNames fname σ).abiArgs).1.lfd_body = true :=
  RegionPhysImg.physImgB_regionExport fname σ p hp hc hr hts fd0 hnd
    (fun i hi => accArg_of_accP
      (accP_regionAllocBody (ArgSlotName σ) _ _ r hts hC hI hroot
        (exportR_untagP_copy (nfAbiNames fname σ) p hc hr) i hi))
    (harr_regionAllocBody _ p hc hr hts) R ps

/-- The result alias at a result buffer `D0` names `D0`, and `D0` is a name. -/
theorem resAliasOf_some {D0 D src : String} {ts : List JasminTy} {res : List LOperand}
    (h : resAliasOf none (some D0) ts res = some (D, src)) : D = D0 ∧ D0 ≠ "" := by
  unfold resAliasOf at h
  split at h
  · rename_i heq
    simp only [Option.some.injEq] at heq
    split_ifs at h with hD
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := heq
    exact ⟨h.1.symm, hD⟩
  · cases h

/-- **The coalescing renaming sends every array name to a word-array parameter with a save
    slot** (the hypothesis `hroot` of `physImgB_regionExport_param`): for a program of the
    region route over the context of the direct route, without `call`, at a layout whose
    word-array parameters have save slots, whose every zeroing zeroes the result root
    (`ZeroAtRoot`), the array names (`RootIn`) of every instruction of the export followed by
    its result copy are sent by `canonMemrefName (resAliasTab [] rr C)` to the name `argName j`
    of a parameter `j` with `ArgSlot σ j`. Without a zeroing the alias table with the result
    alias is `aliasTab [] C`; with one, the result root is sent to the result buffer, a
    parameter. -/
theorem exportR_aliasRoots (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hσ : wordsSlotB σ = true) {r : Exported}
    (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 x86Data = some r)
    (hzr : ZeroAtRoot (nfAbiNames fname σ) ts r) :
    ∀ i ∈ r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res,
      RootIn (fun x => ArgSlotName σ (canonMemrefName (resAliasTab []
        (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)
        (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res)) x)) i := by
  obtain ⟨k1, k2⟩ := exportR_idxOk _ fname p hp hc _ 0 r hr le_rfl (ArgSlotName σ)
    (arrNamed_nfCtx hσ)
  have hcopy := idxOk_regionLprogCopy (code := r.code) (nfAbiNames fname σ) ts k2
    fun h => le_afterDst _ (outArg_argSlotName hσ fname h)
  have hok := idxOk_append k1 (fun _ h => h) hcopy
  by_cases hnz : ∀ i ∈ r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code r.res,
      X86Backend.ImageStraightRoute.zeroDst? i = none
  · rw [resAliasTab_eq_of_noZero _ _ hnz]
    exact canonMemrefName_aliasTab_of_idxOk (ArgSlotName σ) hok (fun _ h => h)
      fun i hi z hz => by rw [hnz i hi] at hz; cases hz
  · obtain ⟨i0, hi0, hz0⟩ := not_forall₂.mp hnz
    obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp hz0
    obtain ⟨D, src, hrr, hroot0⟩ := hzr i0 hi0 z hz
    obtain ⟨rfl, hD⟩ := resAliasOf_some hrr
    have h := canonMemrefName_aliasTab_of_idxOk (fun x => ArgSlotName σ x ∨ x = z) hok
      (fun x h => Or.inl h) fun i hi z' hz' => by
        obtain ⟨D', src', h1, h2⟩ := hzr i hi z' hz'
        rw [hrr] at h1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
        rw [hroot0] at h2
        exact Or.inr (Option.some.inj h2).symm
    intro i hi
    refine rootIn_mono (fun x hx => ?_) (h i hi)
    rw [hrr]
    show ArgSlotName σ (X86Backend.ImageStraightRoute.chainAliasRes [] _ src _ x)
    rw [X86Backend.ImageStraightRoute.chainAliasRes_apply, hroot0]
    dsimp only
    split_ifs with he
    · exact outArg_argSlotName hσ fname hD
    · rcases hx with hx | hx
      · exact hx
      · exact absurd hx he

/-- **The export body of the region route is in the image class at the slot map of the
    gate** for every program of the region route over the context of the direct route
    without `call`, whose `stackLoad`, `stackStore`, carried and branch-result arrays are of
    `64`-bit words (`arrW64B`) and whose export zeroes only the result root (`ZeroAtRoot`), at
    a layout whose word-array parameters have save slots (`wordsSlotB`), with distinct export
    registers of the parameters and a result other than one register. -/
theorem physImgB_regionExport_words (fname : String) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) (hw : arrW64B p = true)
    (hσ : wordsSlotB σ = true) {r : Exported}
    (hr : exportR (nfCtx σ).length fname p (nfCtx σ).length 0 x86Data = some r)
    (hzr : ZeroAtRoot (nfAbiNames fname σ) ts r)
    (hts : ∀ w, ts ≠ [.reg w]) (fd0 : Lfundef)
    (hnd : (σ.args.map fun a => exportReg a.reg).Nodup)
    (R : X86Backend.ImageCellFold.Slots) (ps : List (String × String)) :
    JasminLsemAddrImage.physImgB
      (X86Backend.ImageStraightCells.slotArrC R
        (X86Backend.ImageAddrRoute.slotRen
          (X86Backend.ImageAddrRoute.slotArrOf σ exportReg)
          (JasminLsemRenameLoop.renOf ps)))
      (calleeAllocCert none
        { fd0 with lfd_body :=
            (arrBasePins (nfAbiNames fname σ)
                (regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy (nfAbiNames fname σ) none ts r.code
                  r.res) []
                  (resAliasOf none (some (nfAbiNames fname σ).outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩])) }
        (nfAbiNames fname σ).outArg (nfAbiNames fname σ).inArgs
        (nfAbiNames fname σ).abiArgs).1.lfd_body = true :=
  physImgB_regionExport_param fname σ p hp hc hr hts fd0 hnd
    (exportR_accCode_copy (nfAbiNames fname σ) p hc hw hr)
    (exportR_immCode_copy (nfAbiNames fname σ) p hc hr)
    (exportR_aliasRoots fname σ p hp hc hσ hr hzr) R ps

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg
