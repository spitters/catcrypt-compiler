/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass

/-!
# The tied flag compares of the allocated function of the region route

Conjunct 7 of the side conditions `physImgSideB` of the printer takes `flagTiedB` on the body
of the allocated function `RegionPhysImgGate.regionAllocFn`: every flag-only compare
`CMP`/`TEST` `d, [x, c]` with a register first source `x` has `x = d`. This module proves it
on the domain of `RegionPhysImgArg.physImgB_regionExport_words`.

The flag-only operations of the region export `exportR` are the loop guards and the
zero-trip guards `CMP:64 c, [c, #0]`: a comparison of the source exports as `SETcc`, and every
other mnemonic of the export has a base other than `CMP` and `TEST`. The predicate `FlagForm`
states this shape of an instruction. The renaming of the array positions `renArr`, the
removal of self moves, the liveness instructions, `canonicalizeMemrefThread` and the return
keep it, and the expansion `physExpand` of an instruction of this shape emits only tied flag
compares: the expansion of a guard is the guard over the allocated register, and every other
expansion emits the mnemonic of its input or a move (`physExpand_mnemOk`).

## Main results

* `exportR_flagForm`: every instruction of the region export has `FlagForm`.
* `flagForm_regionAllocBody`: every instruction of the allocator input body has `FlagForm`.
* `physExpand_mnemOk`: an expansion emits the mnemonic of its input or a move mnemonic.
* `physExpand_tiedI`: the expansion of an instruction of `FlagForm` has tied flag compares.
* `flagTiedB_lfundefPhysAbiOfVirtCert`: `flagTiedB` on the call-free looped physical ABI
  export of an allocator input of `FlagForm`.
* `flagTiedB_regionAllocFn`: `flagTiedB` on the body of `regionAllocFn`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgFlag

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (tieBase_of_colonFree tieBase_append_colon
  tieBase_withWidthTag tieBase_withWidthTag_colon head?_eq_of_tieBase VectorMnem VectorMnem.append binOpName_colonFree
  cmpName_colonFree castWMnem_colonFree simdMnemonic_vector ymmMnemonic_vector)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data tieBase)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renZero renStoreImm renCallW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSideAlloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (flagTiedB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass (TiedI flagTiedB_iff)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov?)
open RegionPhysImgGate
open RegionPhysImgArg (renArr_lopn)
open RegionAllocMapAlign (regionAllocBody)

/-! ## 1. The flag form of an instruction -/

/-- The flag form of an instruction: an operation with a flag-only base is the 64-bit compare
    `CMP:64 c, [c, s]` of a register with itself as destination and first source. -/
def FlagForm (w : LinstrR) : Prop :=
  ∀ ds o ss, w = .Lopn ds o ss → x86Data.flagOnly (tieBase o) = true →
    o = "CMP:64" ∧ ∃ c s, ds = [.reg c] ∧ ss = [.reg c, s]

theorem flagForm_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : x86Data.flagOnly (tieBase o) = false) : FlagForm (.Lopn ds o ss) := by
  intro ds' o' ss' he hf
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  rw [h] at hf
  cases hf

theorem flagForm_nonLopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss) : FlagForm w :=
  fun ds o ss he => absurd he (h ds o ss)

theorem flagForm_cmp (c : String) (s : LOperand) :
    FlagForm (.Lopn [.reg c] "CMP:64" [.reg c, s]) := by
  intro ds o ss he _
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨rfl, c, s, rfl, rfl⟩

theorem noFlag_colonFree {s : String} (h : ':' ∉ s.toList) (h' : '^' ∉ s.toList)
    (hs : x86Data.flagOnly s = false) : x86Data.flagOnly (tieBase s) = false := by
  rw [tieBase_of_colonFree h h']
  exact hs

theorem noFlag_withWidthTag (w : Nat) {s : String} (h : ':' ∉ s.toList) (h' : '^' ∉ s.toList)
    (hs : x86Data.flagOnly s = false) : x86Data.flagOnly (tieBase (withWidthTag w s)) = false := by
  rw [tieBase_withWidthTag w ((tagSepFree_iff s).mpr ⟨h, h'⟩)]
  exact hs

theorem noFlag_colon {s : String} (t : String) (h : ':' ∉ s.toList) (h' : '^' ∉ s.toList)
    (hs : x86Data.flagOnly s = false) : x86Data.flagOnly (tieBase (s ++ ":" ++ t)) = false := by
  rw [tieBase_append_colon _ h h']
  exact hs

theorem noFlag_withWidthTag_colon (w : Nat) {s : String} (t : String) (h : ':' ∉ s.toList)
    (h' : '^' ∉ s.toList) (hs : x86Data.flagOnly s = false) :
    x86Data.flagOnly (tieBase (withWidthTag w (s ++ ":" ++ t))) = false := by
  rw [tieBase_withWidthTag_colon _ _ h h']
  exact hs

theorem noFlag_vector {o : String} (h : VectorMnem o) : x86Data.flagOnly (tieBase o) = false := by
  cases hb : x86Data.flagOnly (tieBase o)
  · rfl
  · exfalso
    have hb' : tieBase o = "CMP" ∨ tieBase o = "TEST" := by
      simpa [x86Data] using hb
    have hne : (tieBase o).toList ≠ [] := by
      rcases hb' with e | e <;> rw [e] <;> decide
    have hh := head?_eq_of_tieBase hne
    unfold VectorMnem at h
    rw [hh] at h
    rcases hb' with e | e <;> rw [e] at h <;> revert h <;> decide

/-! ## 2. The export -/

/-- **The operation `opToLinstrR` has the flag form**: no operation of the dialect exports with
    a flag-only base. -/
theorem opToLinstrR_flagForm (op : JasminOp) (dst : String) (srcs : List LOperand) :
    FlagForm (opToLinstrR op dst srcs) := by
  cases op with
  | regArith bop w =>
    exact flagForm_lopn (noFlag_withWidthTag w (binOpName_colonFree bop) (by cases bop <;> decide)
      (by cases bop <;> decide))
  | select w => exact flagForm_lopn (noFlag_withWidthTag w (by decide) (by decide) (by decide))
  | stackLoad w n =>
    dsimp only [opToLinstrR]; split <;> exact flagForm_lopn (by decide)
  | stackStore w n =>
    dsimp only [opToLinstrR]; split <;> exact flagForm_lopn (by decide)
  | castW w w' =>
    dsimp only [opToLinstrR]; split
    · exact flagForm_lopn (noFlag_colonFree (castWMnem_colonFree w w')
        (by unfold castWMnem; split_ifs <;> decide) (by unfold castWMnem; split_ifs <;> decide))
    · exact flagForm_lopn (by split <;> decide)
  | extCall name argTys retTy =>
    dsimp only [opToLinstrR]; split
    · exact flagForm_lopn (by decide)
    · split
      · refine flagForm_lopn ?_
        simp only [encodeCallW, String.append_assoc]
        rw [show "CALLW:" = "CALLW" ++ ":" from rfl, tieBase_append_colon _ (by decide) (by decide)]
        decide
      · refine flagForm_lopn ?_
        rw [show "CALL:" = "CALL" ++ ":" from rfl, tieBase_append_colon _ (by decide) (by decide)]
        decide
  | regConst w n => exact flagForm_lopn (noFlag_withWidthTag w (by decide) (by decide) (by decide))
  | vpackZMM bop => exact flagForm_lopn (noFlag_vector (VectorMnem.append _ (by
      simp [VectorMnem])))
  | vpackZMMd bop => exact flagForm_lopn (noFlag_vector (VectorMnem.append _ (by
      simp [VectorMnem])))
  | vprordZMM n => exact flagForm_lopn (noFlag_vector (VectorMnem.append _ (by
      simp [VectorMnem])))
  | vpslldq n => exact flagForm_lopn (noFlag_vector (VectorMnem.append _ (by
      simp [VectorMnem])))
  | vpsrldq n => exact flagForm_lopn (noFlag_vector (VectorMnem.append _ (by
      simp [VectorMnem])))
  | vsimd op => exact flagForm_lopn (noFlag_vector (simdMnemonic_vector op))
  | vymm op => exact flagForm_lopn (noFlag_vector (ymmMnemonic_vector op))
  | mulhi w => exact flagForm_lopn (noFlag_withWidthTag w (by decide) (by decide) (by decide))
  | addCarryLo w => exact flagForm_lopn (noFlag_withWidthTag w (by decide) (by decide) (by decide))
  | addCarryHi w => exact flagForm_lopn (noFlag_withWidthTag w (by decide) (by decide) (by decide))
  | rorImm w n =>
    refine flagForm_lopn ?_
    rw [show "ROR:" = "ROR" ++ ":" from rfl]
    exact noFlag_withWidthTag_colon _ _ (by decide) (by decide) (by decide)
  | shrImm w n =>
    refine flagForm_lopn ?_
    rw [show "SHR:" = "SHR" ++ ":" from rfl]
    exact noFlag_withWidthTag_colon _ _ (by decide) (by decide) (by decide)
  | sarImm w n =>
    refine flagForm_lopn ?_
    rw [show "SAR:" = "SAR" ++ ":" from rfl]
    exact noFlag_withWidthTag_colon _ _ (by decide) (by decide) (by decide)
  | shlImm w n =>
    refine flagForm_lopn ?_
    rw [show "SHL:" = "SHL" ++ ":" from rfl]
    exact noFlag_withWidthTag_colon _ _ (by decide) (by decide) (by decide)
  | callN name argTys retTys =>
    dsimp only [opToLinstrR]; split
    · refine flagForm_lopn ?_
      simp only [encodeCallW, String.append_assoc]
      rw [show "CALLNW:" = "CALLNW" ++ ":" from rfl, tieBase_append_colon _ (by decide) (by decide)]
      decide
    · refine flagForm_lopn ?_
      rw [show "CALLN:" = "CALLN" ++ ":" from rfl, tieBase_append_colon _ (by decide) (by decide)]
      decide
  | cmp c w =>
    exact flagForm_lopn (noFlag_withWidthTag w (cmpName_colonFree c) (by cases c <;> decide)
      (by cases c <;> decide))
  | cmpImm c w n =>
    exact flagForm_lopn (noFlag_withWidthTag w (cmpName_colonFree c) (by cases c <;> decide)
      (by cases c <;> decide))
  | stackZero w n => exact flagForm_lopn (by decide)
  | stackStoreImm w n i => exact flagForm_lopn (by decide)

/-- The binding instruction of the export has the flag form. -/
theorem bindOps_flagForm (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (d : Nat) : ∀ x ∈ bindOps nArgs e d, FlagForm x.1 := by
  simp only [bindOps, JasminLsemMem.straightOpsMem, List.mem_cons, List.not_mem_nil, or_false]
  rintro x rfl
  generalize exprArgs d nArgs argName (fun _ => none) e = src
  generalize e.op = op
  have hshift : ∀ (m : String) (w n : Nat) (s : LOperand), ':' ∉ m.toList → '^' ∉ m.toList →
      x86Data.flagOnly m = false →
      FlagForm (JasminLsemShift.shiftLinstr m w (regName d) s n) := fun m w _ s hm hm' hf =>
    flagForm_lopn (noFlag_withWidthTag w hm hm' hf)
  split
  all_goals dsimp only
  all_goals first
    | exact opToLinstrR_flagForm _ _ _
    | (split
       all_goals first
         | exact hshift _ _ _ _ (by decide) (by decide) (by decide)
         | exact opToLinstrR_flagForm _ _ _)

/-- Every instruction of a typed code has the flag form. -/
def AllFlag (L : List LinstrRM) : Prop := ∀ x ∈ L, FlagForm x.1

@[simp] theorem allFlag_nil : AllFlag [] := by simp [AllFlag]

@[simp] theorem allFlag_append (a b : List LinstrRM) :
    AllFlag (a ++ b) ↔ AllFlag a ∧ AllFlag b := by
  simp only [AllFlag, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

@[simp] theorem allFlag_cons (x : LinstrRM) (l : List LinstrRM) :
    AllFlag (x :: l) ↔ FlagForm x.1 ∧ AllFlag l := by
  simp [AllFlag]

@[simp] theorem movI_flag (dst : String) (src : LOperand) : FlagForm (movI dst src).1 :=
  flagForm_lopn (noFlag_withWidthTag 64 (by decide) (by decide) (by decide))

@[simp] theorem movImmI_flag (dst : String) (k : Nat) : FlagForm (movImmI dst k).1 :=
  movI_flag dst _

@[simp] theorem labelI_flag (l : LLabel) : FlagForm (labelI l).1 :=
  flagForm_nonLopn fun _ _ _ e => nomatch e

theorem allFlag_map_movI {α : Type} (l : List α) (f : α → String) (g : α → LOperand) :
    AllFlag (l.map fun p => movI (f p) (g p)) := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx
  exact movI_flag _ _

@[simp] theorem stageMoves_flag (D : Nat) (ops : List LOperand) : AllFlag (stageMoves D ops) :=
  allFlag_map_movI _ _ _

@[simp] theorem commitMoves_flag (D : Nat) (tgts : List String) :
    AllFlag (commitMoves D tgts) := allFlag_map_movI _ _ _

@[simp] theorem parMoves_flag (D : Nat) (tgts : List String) (ops : List LOperand) :
    AllFlag (ExportRegions.parMoves D tgts ops) := by
  simp [ExportRegions.parMoves]

@[simp] theorem seedMoves_flag (car : List String) (ops : List LOperand) :
    AllFlag (seedMoves car ops) := allFlag_map_movI _ _ _

@[simp] theorem shiftMoves_flag (d nCar : Nat) : AllFlag (shiftMoves d nCar) :=
  allFlag_map_movI _ _ _

@[simp] theorem advanceOps_flag (idx ctr : String) : AllFlag (advanceOps idx ctr) := by
  simp only [advanceOps, allFlag_cons, allFlag_nil, and_true]
  exact ⟨flagForm_lopn (noFlag_withWidthTag 64 (by decide) (by decide) (by decide)),
    flagForm_lopn (noFlag_withWidthTag 64 (by decide) (by decide) (by decide))⟩

@[simp] theorem arrMoves_flag (z t : String) (mv : List ArrMove) : AllFlag (arrMoves z t mv) := by
  intro x hx
  obtain ⟨a, -, hx⟩ := List.mem_flatMap.mp hx
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact flagForm_lopn (by decide)

@[simp] theorem typedMoves_flag (z t : String) (tp : List (JasminTy × String × String)) :
    AllFlag (typedMoves z t tp) := by
  simp [typedMoves, regMoves, allFlag_map_movI]

@[simp] theorem arrParMoves_flag (z t : String) (D : Nat) (mv : List ArrMove) :
    AllFlag (arrParMoves z t D mv) := by
  unfold arrParMoves; split <;> simp

@[simp] theorem ifResMoves_flag (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    AllFlag (ifResMoves rs d D ops) := by
  unfold ifResMoves; split <;> simp

@[simp] theorem flagWord_flag (r z : String) (op : LOperand) :
    AllFlag (flagWord x86Data r z op) := by
  unfold flagWord
  split
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl]
    simp only [allFlag_cons, allFlag_nil, movImmI_flag, true_and, and_true]
    exact flagForm_lopn (noFlag_withWidthTag 64 (by decide) (by decide) (by decide))
  · simp

@[simp] theorem guardI_cmp_flag (c : String) (s : LOperand) :
    FlagForm (guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, s])).1 := by
  rw [show withWidthTag 64 "CMP" = "CMP:64" by decide]
  exact flagForm_cmp _ _

@[simp] theorem guardI_cond_flag (c : LOperand) (l : LLabel) :
    FlagForm (guardI (.Lcond c l)).1 :=
  flagForm_nonLopn fun _ _ _ e => nomatch e

@[simp] theorem loopGuard_flag (ctr : String) (top : LLabel) :
    AllFlag ((x86Data.loopGuard ctr top).map guardI) := by
  rw [X86Backend.TwoAddrLegalize.x86Data_loopGuard]
  simp only [List.map_cons, List.map_nil, allFlag_cons, allFlag_nil, and_true]
  refine ⟨?_, flagForm_nonLopn fun _ _ _ e => nomatch e⟩
  rw [show withWidthTag 64 "CMP" = "CMP:64" by decide]
  exact flagForm_cmp _ _

@[simp] theorem zeroTripGuard_flag (ctr : String) (top endL : LLabel) :
    AllFlag ((x86Data.zeroTripGuard ctr top endL).map guardI) := by
  rw [X86Backend.TwoAddrLegalize.x86Data_zeroTripGuard]
  simp only [List.map_cons, List.map_nil, allFlag_cons, allFlag_nil, and_true]
  refine ⟨?_, flagForm_nonLopn fun _ _ _ e => nomatch e⟩
  rw [show withWidthTag 64 "CMP" = "CMP:64" by decide]
  exact flagForm_cmp _ _

@[simp] theorem callI_flag (dst f : String) (srcs : List LOperand) :
    FlagForm (callI dst f srcs).1 := by
  refine flagForm_lopn ?_
  rw [show "CALL:" = "CALL" ++ ":" from rfl]
  exact noFlag_colon _ (by decide) (by decide) (by decide)

/-- **The flag form of the export**: every instruction of the region export on x86 has the
    flag form. -/
theorem exportR_flagForm (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r → AllFlag r.code := by
  induction p with
  | ret vs =>
    intro d n r h
    simp only [exportR, Option.some.injEq] at h
    subst h; exact allFlag_nil
  | var e k ih =>
    intro d n r h
    simp only [exportR, Option.map_eq_some_iff] at h
    obtain ⟨rk, hk, rfl⟩ := h
    simp only [Exported.prepend, allFlag_append]
    exact ⟨bindOps_flagForm nArgs e d, ih _ _ _ hk⟩
  | forLoop count inits body k ihb ihk =>
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rk, hk, rfl⟩ := h
    simp [Exported.prepend, forArrFrame, ihb _ _ _ hb, ihk _ _ _ hk]
  | ifThenElse cond thn els k iht ihe ihk =>
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
    simp [Exported.prepend, ifFrame, iht _ _ _ ht, ihe _ _ _ he, ihk _ _ _ hk]
  | whileLoop inits body k ihb ihk =>
    intro d n r h
    simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rk, hk, rfl⟩ := h
    simp [Exported.prepend, whileFrame, ihb _ _ _ hb, ihk _ _ _ hk]
  | call f args k ih =>
    intro d n r h
    obtain ⟨-, rk, hk, rfl⟩ := exportR_call_eq_some.mp h
    simp [Exported.prepend, ih _ _ _ hk]

/-! ## 3. The allocator input -/

/-- The renaming of the array positions keeps the flag form: it keeps the mnemonic of an
    operation and renames only operations with an array position, none of which has a
    flag-only base. -/
theorem flagForm_renArr (ρ : String → String) {i : LinstrRM} (h : FlagForm i.1) :
    FlagForm (renArr ρ i).1 := by
  intro ds' o ss' he hf
  obtain ⟨ds, ss, hi, -⟩ := renArr_lopn ρ he
  obtain ⟨rfl, c, s, rfl, rfl⟩ := h ds o ss hi hf
  have hfix : (renArr ρ i).1 = i.1 := by
    obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    cases tag <;> simp [renArr, renLoad, renStore, renZero, renStoreImm, renCallW,
      LprogIsa.shadowCall?]
  rw [hfix, hi] at he
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, -, rfl⟩ := he
  exact ⟨rfl, c, s, rfl, rfl⟩

theorem flagForm_livepin (ss : List LOperand) :
    FlagForm (.Lopn [.reg "%livepin"] "LIVEPIN" ss) := flagForm_lopn (by decide)

theorem flagForm_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, FlagForm i.1) :
    ∀ i ∈ backEdgePins C, FlagForm i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, FlagForm i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact flagForm_livepin _
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

theorem flagForm_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, FlagForm i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, FlagForm i.li_i := by
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      intro ds' o' ss' he hf
      simp only [LinstrR.Lopn.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨rfl, c, s, rfl, rfl⟩ := h j hj ds o ss heq hf
      exact ⟨rfl, _, _, rfl, rfl⟩
    · exact h j hj

theorem flagForm_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, FlagForm i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
      simp only [resCopyStep, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with rfl | rfl | rfl
      · exact movImmI_flag _ _
      · exact flagForm_lopn (by decide)
      · exact flagForm_lopn (by decide)
    · cases hi
  · cases hi

/-- **The flag form of the allocator input body**: every instruction of
    `regionAllocBody` has the flag form, for a result other than one register. -/
theorem flagForm_regionAllocBody (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (hts : ∀ w, ts ≠ [.reg w]) :
    ∀ i ∈ regionAllocBody a Γ.length ts r, FlagForm i.li_i := by
  have hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, FlagForm i.1 := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact exportR_flagForm _ _ p _ _ r hr i hi
    · exact flagForm_regionLprogCopy a ts _ _ i hi
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res),
      FlagForm i.1 := by
    refine flagForm_backEdgePins fun i hi => ?_
    rcases mem_pinSelfMoves hi with hi | ⟨t, c, z, _, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact flagForm_renArr _ (hC j hj)
    · show FlagForm (.Lopn [.reg t] "LIVEPIN" [.reg c, .reg z])
      exact flagForm_lopn (by decide)
    · exact flagForm_livepin _
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · exact absurd rfl (hts _)
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact flagForm_livepin _
      · cases hi
    · refine flagForm_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact flagForm_livepin _
      · rcases List.mem_append.mp hj with hj | hj
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
          exact hac l hl
        · rw [List.mem_singleton.mp hj]
          exact flagForm_nonLopn fun _ _ _ e => by cases e

/-! ## 4. The expansion -/

/-- **One expansion emits the mnemonic of its input or a move**: every operation of
    `physExpand` of `i` has the mnemonic of `i` or a mnemonic of `movMnems`. -/
theorem physExpand_mnemOk (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (i : Linstr) :
    MnemOk i.li_i (physExpand shiftImm u64 rm mbr i) := by
  obtain ⟨ii, w⟩ := i
  have harm : ∀ (ins : List LOperand) (opn : String) (L : List LinstrR),
      some opn = opnOf w → (∀ r ∈ L, ArmOut ins opn r) →
      MnemOk w (L.map fun r => (⟨ii, r⟩ : Linstr)) := by
    intro ins opn L ho hL r hr ds o ss he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ds', o', ss', e, ho', -⟩ := hL a ha
    simp only at he
    rw [e] at he
    simp only [LinstrR.Lopn.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    rcases ho' with rfl | h
    · exact Or.inl ho
    · exact Or.inr h
  have hself : ∀ w' : LinstrR, w' = w → MnemOk w [⟨ii, w'⟩] := by
    rintro w' rfl r hr ds o ss he
    rw [List.mem_singleton.mp hr] at he
    simp only at he
    subst he
    exact Or.inl rfl
  have happ : ∀ A B : Lcmd, MnemOk w A → MnemOk w B → MnemOk w (A ++ B) := by
    intro A B hA hB r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hA r hr
    · exact hB r hr
  rw [physExpand_eq]
  simp only
  split
  · rename_i _ d tail opn s0 s1 tail1
    have ho : some opn = opnOf (.Lopn (d :: tail) opn (s0 :: s1 :: tail1)) := rfl
    split
    · split
      · exact harm _ _ _ ho (lowerTwoAddrShiftImm_armOut _ _ _ _ _ (movFor_ok opn))
      · exact harm _ _ _ ho (lowerTwoAddr_armOut _ _ _ _ _ (movFor_ok opn))
    · split
      · rename_i _ d' opn' addr val heq'
        simp only [LinstrR.Lopn.injEq] at heq'
        obtain ⟨-, rfl, -⟩ := heq'
        split
        · exact happ _ _ (harm _ _ _ ho (reloadMemrefBase_armOut mbr _ opn))
            (harm _ _ _ ho (legalizeMemStoreK_armOut _ _ _ _ _ _ (movFor_ok _)))
        · exact harm _ _ _ ho (legalizeSpillDst_armOut _ _ _)
      · rename_i _ dsts opn' srcs _ heq'
        simp only [LinstrR.Lopn.injEq] at heq'
        obtain ⟨-, rfl, -⟩ := heq'
        exact harm _ _ _ ho (legalizeSpillDst_armOut _ _ _)
      · exact hself _ rfl
  · rename_i _ d opn s
    have ho : some opn = opnOf (.Lopn [d] opn [s]) := rfl
    split
    · exact harm _ _ _ ho (lowerNativeShiftRotate_armOut _ _ _ _ (movFor_ok opn))
    · split
      · exact happ _ _ (harm _ _ _ ho (reloadMemrefBase_armOut mbr _ opn))
          (harm _ _ _ ho (legalizeMemLoad_armOut _ _ _ _ (movFor_ok _)))
      · exact harm _ _ _ ho (legalizeOneSrc_armOut _ _ _ _)
  · intro r hr ds o ss he
    rw [List.mem_singleton.mp hr] at he
    simp only [LinstrR.Lopn.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    exact Or.inl (by simp [opnOf])
  · exact hself _ rfl

theorem movMnems_noFlag : ∀ o ∈ movMnems, x86Data.flagOnly (tieBase o) = false := by
  decide

/-- **The expansion of an instruction of the flag form has tied flag compares**, under an
    operand map that sends registers to registers. -/
theorem physExpand_tiedI (shiftImm : ShiftImmOracle) (u64 : Bool) (rm : LOperand → LOperand)
    (mbr : String → Option String) (hreg : ∀ n, ∃ n', rm (.reg n) = .reg n') (i : Linstr)
    (hi : FlagForm i.li_i) : ∀ r ∈ physExpand shiftImm u64 rm mbr i, TiedI r := by
  by_cases hc : ∃ c s, i.li_i = .Lopn [.reg c] "CMP:64" [.reg c, s]
  · obtain ⟨c, s, he⟩ := hc
    obtain ⟨ii, w⟩ := i
    simp only at he
    subst he
    obtain ⟨c', hc'⟩ := hreg c
    have hb : isTwoAddrBinop "CMP:64" = false := by decide
    have hst : isMemStore "CMP:64" = false := by decide
    have hse : isSetccMnem "CMP:64" = false := by decide
    simp only [physExpand_eq, hb, hst, Bool.false_eq_true, ite_false, hc', legalizeSpillDst,
      cmovSpillDst?_of_ne _ _ (by decide +kernel : stripWidthTag "CMP:64" ≠ "CMOV"), setccSpill?_of_ne _ _ hse,
      andnSpill?_of_ne _ _ (by decide : "CMP:64" ≠ "ANDN:64"),
      List.map_cons, List.map_nil, List.mem_singleton]
    rintro r rfl d opn x c0 he _
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq] at he
    obtain ⟨⟨rfl, -⟩, -, ⟨rfl, -⟩, -⟩ := he
    rfl
  · intro r hr d opn x c0 he hf
    exfalso
    rcases physExpand_mnemOk shiftImm u64 rm mbr i r hr _ _ _ he with ho | ho
    · cases hw : i.li_i with
      | Lopn ds o ss =>
        rw [hw] at ho
        simp only [opnOf, Option.some.injEq] at ho
        subst ho
        obtain ⟨rfl, c, s, rfl, rfl⟩ := hi ds opn ss hw hf
        exact hc ⟨c, s, hw⟩
      | _ => rw [hw] at ho; cases ho
    · rw [movMnems_noFlag opn ho] at hf
      cases hf

/-! ## 5. The allocated function -/

theorem tiedI_of_one {j : Linstr} {d o s : String} (h : j.li_i = .Lopn [.reg d] o [.reg s]) :
    TiedI j := by
  intro d' opn x c he _
  rw [h] at he
  simp at he

theorem tiedI_of_slotMov {j : Linstr} (h : (slotMov? j.li_i).isSome = true) : TiedI j := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨o, ho⟩ := slotMov?_eq hp
  exact tiedI_of_one ho

/-- **The tied flag compares of the call-free looped physical ABI export**: when every
    instruction of the allocator input `body1` has the flag form, every flag-only compare of
    the allocated body is tied. The prologue, the argument materialization and the epilogue
    are moves with one source. -/
theorem flagTiedB_lfundefPhysAbiOfVirtCert
    (virt0 : Lfundef) (outArg' : String) (inArgs' accRegs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (posBind : Bool) (body1 : Lcmd)
    (hb1 : body1 = (if abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body))
    (mbr : String → Option String)
    (hmbr : mbr = fun base =>
      (((argBasePairs posBind outArg' inArgs' abiArgs).filterMap (fun p =>
        match abiSlotOfExt p.2 with
        | some saveName => some (physNameForBody body1 (physTableOut body1 []) p.1, saveName)
        | none => none)).find? (fun p => p.1 == base)).map Prod.snd)
    (hcf : bodyHasCall body1 = false) (hflag : ∀ i ∈ body1, FlagForm i.li_i) :
    flagTiedB (lfundefPhysAbiOfVirtCert virt0 outArg' inArgs' accRegs shiftImm abiArgs
      abiTyin x86Abi posBind).1.lfd_body = true := by
  rw [lfundefPhysAbiOfVirtCert_body virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
    posBind body1 hb1 mbr hmbr hcf]
  have hrmE : physRmap body1 [] =
      fun o =>
        remapOperand body1 (straightCallComposeTable body1 (physTableOut body1 [] [])) o := by
    simp only [physRmap, hcf, Bool.false_eq_true, ite_false]
  refine flagTiedB_iff.mpr fun j hj => ?_
  simp only [insertEpilogue, List.mem_append] at hj
  rcases hj with (hj | hj) | hj | (hj | hj) | hj
  · exact tiedI_of_slotMov ((prologue_moves _ _ abiArgs).1 j (List.mem_append_left _ hj))
  · exact tiedI_of_slotMov ((prologue_moves virt0 #[] abiArgs).1 j
      (List.mem_append_right (buildPrologue virt0 #[] (fun _ => none)) hj))
  · unfold buildArgPtrMaterialize at hj
    obtain ⟨⟨abiReg, k⟩, -, hj⟩ := List.mem_flatMap.mp hj
    simp only at hj
    split at hj
    · simp at hj
    · split_ifs at hj <;>
        rcases hs : abiSlotOfExt abiReg with _ | s <;>
        simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hj <;>
        (try rcases hj with rfl | rfl) <;> exact tiedI_of_one rfl
  · rcases mem_reloadArrImmBody (List.dropLast_subset _ hj) with hj | ⟨i', -, l', hl, -, hx⟩
    · obtain ⟨i, hi, hj⟩ := List.mem_flatMap.mp (List.mem_of_mem_filter hj)
      rw [hrmE] at hj
      exact physExpand_tiedI _ _ _ mbr (fun n => ⟨_, rfl⟩) i (hflag i hi) j hj
    · obtain ⟨b, q, -, ⟨n, w, -, rfl⟩ | ⟨d, v, k, -, rfl⟩⟩ := reloadArrImm_eq_some hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx
        all_goals try (rcases ptrLoad_cases q with hp | hp <;> rw [hp] at hx)
        all_goals first
          | exact tiedI_of_one hx
          | (intro d' opn x c he _; rw [hx] at he; simp at he)
      rcases List.mem_cons.mp hx with hx | hx
      · rcases ptrLoad_cases q with hp | hp <;> rw [hp] at hx <;> exact tiedI_of_one hx
      rcases mem_storeImmVia hx with hx | hx | hx
      · exact tiedI_of_one hx
      all_goals (intro d' opn x c he _; rw [hx] at he; simp at he)
  · simp only [calleeSaveRestoreEpilogue, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> exact tiedI_of_one rfl
  · rw [List.mem_singleton.mp hj]
    intro d opn x c he
    cases he

/-- **Conjunct 7 on the allocated function of the region route**: for a program without
    `call` that passes `regionExportableB`, with a result other than one register, every
    flag-only compare of the body of `regionAllocFn` with a register first source is tied. -/
theorem flagTiedB_regionAllocFn (fn : String) (a : AbiNames) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length fn p Γ.length 0 x86Data = some r) (hts : ∀ w, ts ≠ [.reg w])
    (fd0 : Lfundef) : flagTiedB (regionAllocFn a ts r fd0).lfd_body = true := by
  have hB : ∀ i ∈ regionAllocBody a Γ.length ts r, RegionAllocMapDom.ShapeB i.li_i :=
    RegionAllocMapDom.shapeB_regionAllocBody _ _ ts r fun i hi =>
      (RegionAllocMapDom.exportR_mnemDom Γ.length fn p hp hc _ _ r hr i hi).2.2
  have hcf := RegionAllocMapDom.bodyHasCall_of_shapeB hB
  have hb1 : regionAllocBody a Γ.length ts r =
      (if a.abiArgs.length ≥ 4 then
        [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range a.abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (([] : List String).foldl (fun b r => aliasRegBody r a.outArg b)
            (arrBasePins a (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res))
              ++ ((regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
            (resAliasOf none (some a.outArg) ts r.res)).map
                (fun i => (⟨0, i.1⟩ : Linstr)) ++ [⟨0, .Lret⟩]))) := by
    unfold regionAllocBody
    split
    · exact absurd rfl (hts _)
    · rfl
  unfold regionAllocFn calleeAllocCert
  exact flagTiedB_lfundefPhysAbiOfVirtCert _ _ _ [] (fun _ => none) _ _ true _ hb1 _ rfl hcf
    (flagForm_regionAllocBody fn a p hr hts)

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgFlag
