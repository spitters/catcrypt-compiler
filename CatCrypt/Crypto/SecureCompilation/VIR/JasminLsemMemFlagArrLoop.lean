/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond

@[expose] public section

set_option autoImplicit false

/-!
# The array-accumulator counted loop on the flag machine

`JasminLsemMemSourceTieArrUncond.loopMemArr_export_faithful_denote_uncond` runs the
array-accumulator loop body `loopBodyArrFullMN update nReg` under the
counter-register back-edge of `loopLinstrRM` on `lsemFuelMemL`.
`JasminLsemMemFlagInvTouch.guardedFlagLoop_export_faithful_denote_invTouch` runs a
scalar-accumulator body under the emitted flag skeleton (zero-trip guard
`CMP ctr,#0 ; Lcond Z endL`, flag back-edge `CMP ctr,#0 ; Lcond NZ top`) on
`lsemFuelMemF`. This module is the array-accumulator flag version.

The looped segment is `loopBodyArrFullMN update nReg ++ touch`: the emitted
`chain ++ writeback` pass followed by a touch segment in the position the export
places its invariant touches `CMP Lctr, inv` (after the index/counter updates,
before the back-edge compare). The touch is admitted under a per-trip restoration
discipline over the extended straight step `fstepF` (`TouchRestoresFArrMN`), so it
may set the flag.

## Main results

* `loopArrWritebackMN_plain` / `loopBodyArrFullMN_plain` — the array writeback
  contains no flag compare and no register-copy move.
* `straightOpsMem_plain` / `arrMemN_straightOpsMem_plain` — the emitted chain of
  a program over the stack-memory fragment's op set (in particular of every
  `ArrMemN` update) is plain, so the flag route needs no per-instance chain side
  condition.
* `loopBodyArrTouchMN_tripF` / `loopBodyArrTouchMN_invF` — the per-trip pass and
  the trip invariant of the touched array body on the flag fold
  `runBoundedStraightF`.
* `guardedFlagLoopArr_export_faithful_denote` — the full guarded skeleton over the
  touched array body, run by `lsemFuelMemF` from pc `0` at a nonzero runtime
  count, halts on a state whose accumulator array decodes to
  `JLoopBodyN.denote ⟨m, update⟩`.
* `guardedFlagLoopArr_export_faithful_comL` — the same at the front node
  `ComL.forLoopNRt`'s denotation.
* `guardedFlagLoopArr_faithful_closed` — the same with the counter schedule
  discharged: a counter seeded with `m < 2^64` (zero included) suffices.
* `cmpTouchRM_restores` — a list of compares `CMP nReg, r` restores whenever every
  compared register reads at width `64` in every agreeing state; it instantiates
  the discipline at the export's touch shape.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagInvTouch

variable {invTys : Ctxt jasminDialect}

/-! ## 1. The restoration discipline at an array accumulator -/

/-- **The per-trip restoration discipline (flag machine, array accumulator).**
    From any state agreeing with an array trip valuation `tripValArrMN invs t arr`,
    the touch segment runs to completion under `runStraightF`, re-agrees with the
    same trip valuation, and preserves the counter register's read. The exit flag
    is unconstrained. -/
def TouchRestoresFArrMN (invTys : Ctxt jasminDialect) (w n : Nat)
    (touch : List LinstrRM) (nReg : String) : Prop :=
  ∀ (invs : Ctxt.Valuation invTys) (t : Nat) (arr : Fin n → BitVec w) (s : LstateM)
    (zf : Bool),
    StoreAgreesM (invTys.length + 2) (invTys.length + 2) s (tripValArrMN invs t arr) →
    ∃ s' zf', runStraightF touch s zf = some (s', zf')
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) s' (tripValArrMN invs t arr)
      ∧ s'.reg.getW nReg 64 = s.reg.getW nReg 64

/-- The empty touch restores. -/
theorem TouchRestoresFArrMN_nil (w n : Nat) (nReg : String) :
    TouchRestoresFArrMN invTys w n [] nReg :=
  fun _ _ _ s zf h => ⟨s, zf, rfl, h, rfl⟩

/-! ## 2. Plainness of the array writeback -/

/-- The array writeback is plain: `LOADIDX`, `STOREIDX`, `ADD`, `SUB` — no flag
    compare, no register-copy move. -/
theorem loopArrWritebackMN_plain {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) :
    PlainLopnBody (loopArrWritebackMN update nReg) := by
  intro i hi
  simp only [loopArrWritebackMN, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [cmpArgs?, withWidthTag], by simp [movRegArgs?]⟩

/-- The array pass is plain given its chain is. -/
theorem loopBodyArrFullMN_plain {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String)
    (hchain : PlainLopnBody (straightOpsMem (invTys.length + 2) update (invTys.length + 2))) :
    PlainLopnBody (loopBodyArrFullMN update nReg) := by
  intro i hi
  rw [loopBodyArrFullMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hchain i hi
  · exact loopArrWritebackMN_plain update nReg i hi

/-! ### Plainness of the emitted chain

`PlainLopnBody (straightOpsMem …)` holds for every chain whose ops lie in the
stack-memory fragment's op set: none of their mnemonics is the flag compare
`CMP:64`, and the only one whose stripped mnemonic is `MOV` (`regConst`) has an
immediate source, which the register-copy recogniser rejects. -/

/-- The op set of the stack-memory fragment: register arithmetic, constants,
    select, the immediate shifts, the widening multiply and carry pair, the cast
    and the runtime-indexed array load and store. -/
def OpPlain : JasminOp → Prop
  | .regArith _ _ | .regConst _ _ | .select _ | .shrImm _ _ | .shlImm _ _
  | .sarImm _ _ | .mulhi _ | .addCarryLo _ | .addCarryHi _ | .castW _ _
  | .stackLoad _ _ | .stackStore _ _ => True
  | _ => False

/-- Every binding of a `Com` has an op in the stack-memory fragment's op set. -/
def ComOpsPlain : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => OpPlain e.op ∧ ComOpsPlain body

/-- An `Lopn` whose mnemonic is not the flag compare, does not strip to `MOV` and is
    no array-ABI move (`copyQ`) is plain under any descriptor. -/
theorem lopn_plain (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (tag : MemTag) (h1 : opn ≠ withWidthTag 64 "CMP") (h2 : stripWidthTag opn ≠ "MOV")
    (h3 : copyQ opn = false) :
    IsLopn (LinstrR.Lopn dsts opn srcs, tag)
      ∧ cmpArgs? (LinstrR.Lopn dsts opn srcs, tag) = none
      ∧ movRegArgs? (LinstrR.Lopn dsts opn srcs, tag) = none := by
  refine ⟨⟨_, _, _, rfl⟩, ?_, ?_⟩
  · unfold cmpArgs?
    split <;> simp_all
  · unfold movRegArgs?
    split <;> simp_all

/-- The first character of a width-tagged mnemonic is the mnemonic's first
    character. -/
theorem head?_withWidthTag (w : Nat) (m : String) (hm : m.toList ≠ []) :
    (withWidthTag w m).toList.head? = m.toList.head? := by
  unfold withWidthTag
  split
  · rw [String.toList_append]
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hm
    rw [hc]
    rfl
  · rfl

/-- A mnemonic that strips to a nonempty `y` starts with `y`'s first character. -/
theorem head?_of_stripWidthTag_eq (x y : String) (hy : y.toList ≠ [])
    (h : stripWidthTag x = y) : x.toList.head? = y.toList.head? := by
  unfold stripWidthTag at h
  split at h
  · have h' := congrArg String.toList h
    rw [String.toList_ofList] at h'
    have hp : x.toList.dropLast.dropLast.dropLast <+: x.toList :=
      (List.dropLast_prefix _).trans ((List.dropLast_prefix _).trans (List.dropLast_prefix _))
    rw [h'] at hp
    obtain ⟨t, ht⟩ := hp
    rw [← ht]
    obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil hy
    rw [hc]
    rfl
  · rw [h]

/-- A mnemonic that strips to `MOV` starts with `M`. -/
theorem head?_of_stripWidthTag_eq_MOV (x : String) (h : stripWidthTag x = "MOV") :
    x.toList.head? = some 'M' :=
  (head?_of_stripWidthTag_eq x "MOV" (by decide) h).trans (by decide)

/-- The flag compare starts with `C`. -/
theorem head?_cmp64 : (withWidthTag 64 "CMP").toList.head? = some 'C' := by
  decide

/-- A mnemonic whose first character is neither `C` nor `M` is neither the flag
    compare nor a mnemonic stripping to `MOV`. -/
theorem ne_cmp_mov_of_head (x : String) (c : Char) (hx : x.toList.head? = some c)
    (hC : c ≠ 'C') (hM : c ≠ 'M') :
    x ≠ withWidthTag 64 "CMP" ∧ stripWidthTag x ≠ "MOV" := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, head?_cmp64] at hx
    exact hC (Option.some.inj hx).symm
  · rw [head?_of_stripWidthTag_eq_MOV x h] at hx
    exact hM (Option.some.inj hx).symm

/-- A width-tagged mnemonic `m ++ rest` whose head `m` starts with neither `C`
    nor `M` is plain under any descriptor. -/
theorem withWidthTag_plain_of_head (w : Nat) (m : String) (c : Char)
    (hm : m.toList.head? = some c) (hC : c ≠ 'C') (hM : c ≠ 'M') :
    withWidthTag w m ≠ withWidthTag 64 "CMP" ∧ stripWidthTag (withWidthTag w m) ≠ "MOV" := by
  have hne : m.toList ≠ [] := by
    intro h; rw [h] at hm; simp at hm
  exact ne_cmp_mov_of_head _ c (by rw [head?_withWidthTag w m hne, hm]) hC hM

/-- Every `opToLinstrR` image of an op in the fragment's op set is plain. -/
theorem opToLinstrR_plain (op : JasminOp) (hop : OpPlain op) (dst : String)
    (srcs : List LOperand) (tag : MemTag) :
    IsLopn (opToLinstrR op dst srcs, tag)
      ∧ cmpArgs? (opToLinstrR op dst srcs, tag) = none
      ∧ movRegArgs? (opToLinstrR op dst srcs, tag) = none := by
  cases op <;> simp only [OpPlain] at hop
  case regArith bop w =>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> cases bop <;> decide)
      (by unfold withWidthTag; split <;> cases bop <;> decide)
      (by unfold withWidthTag; split <;> cases bop <;> decide)
  case regConst w k =>
    refine ⟨⟨_, _, _, rfl⟩, ?_, ?_⟩ <;> simp [opToLinstrR, cmpArgs?, movRegArgs?]
  case select w =>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> decide)
      (by unfold withWidthTag; split <;> decide) (by unfold withWidthTag; split <;> decide)
  case shrImm w k =>
    obtain ⟨h1, h2⟩ := withWidthTag_plain_of_head w ("SHR:" ++ toString k) 'S'
      (by rw [String.toList_append]; rfl) (by decide) (by decide)
    exact lopn_plain _ _ _ _ h1 h2
      (copyQ_withWidthTag w (by rw [String.toList_append]; rfl) (by decide))
  case shlImm w k =>
    obtain ⟨h1, h2⟩ := withWidthTag_plain_of_head w ("SHL:" ++ toString k) 'S'
      (by rw [String.toList_append]; rfl) (by decide) (by decide)
    exact lopn_plain _ _ _ _ h1 h2
      (copyQ_withWidthTag w (by rw [String.toList_append]; rfl) (by decide))
  case sarImm w k =>
    obtain ⟨h1, h2⟩ := withWidthTag_plain_of_head w ("SAR:" ++ toString k) 'S'
      (by rw [String.toList_append]; rfl) (by decide) (by decide)
    exact lopn_plain _ _ _ _ h1 h2
      (copyQ_withWidthTag w (by rw [String.toList_append]; rfl) (by decide))
  case mulhi w =>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> decide)
      (by unfold withWidthTag; split <;> decide) (by unfold withWidthTag; split <;> decide)
  case addCarryLo w =>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> decide)
      (by unfold withWidthTag; split <;> decide) (by unfold withWidthTag; split <;> decide)
  case addCarryHi w =>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> decide)
      (by unfold withWidthTag; split <;> decide) (by unfold withWidthTag; split <;> decide)
  case castW w w' =>
    simp only [opToLinstrR]
    split
    · unfold castWMnem
      split_ifs <;> exact lopn_plain _ _ _ _ (by decide) (by decide) (by decide)
    · split <;> exact lopn_plain _ _ _ _ (by decide) (by decide) (by decide)
  case stackLoad w k =>
    simp only [opToLinstrR]
    split <;> exact lopn_plain _ _ _ _ (by decide) (by decide) (by decide)
  case stackStore w k =>
    simp only [opToLinstrR]
    split <;> exact lopn_plain _ _ _ _ (by decide) (by decide) (by decide)

/-- The structured shift instruction is plain under any descriptor. -/
theorem shiftLinstr_plain (mnem : String) (hm : mnem = "SHR" ∨ mnem = "SHL" ∨ mnem = "SAR")
    (w : Nat) (dst : String) (s : LOperand) (k : Nat) (tag : MemTag) :
    IsLopn (JasminLsemShift.shiftLinstr mnem w dst s k, tag)
      ∧ cmpArgs? (JasminLsemShift.shiftLinstr mnem w dst s k, tag) = none
      ∧ movRegArgs? (JasminLsemShift.shiftLinstr mnem w dst s k, tag) = none := by
  unfold JasminLsemShift.shiftLinstr
  rcases hm with rfl | rfl | rfl <;>
    exact lopn_plain _ _ _ _ (by unfold withWidthTag; split <;> decide)
      (by unfold withWidthTag; split <;> decide) (by unfold withWidthTag; split <;> decide)

/-- **The emitted chain is plain.** Every instruction `straightOpsMem` emits for a
    `Com` whose ops lie in the stack-memory fragment's op set is an `Lopn` that is
    neither the flag compare nor a register-copy move. -/
theorem straightOpsMem_plain (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (hcom : ComOpsPlain com) (curDepth : Nat) :
    PlainLopnBody (straightOpsMem nArgs com curDepth) := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp [straightOpsMem] at hi
  | var e body ih =>
      obtain ⟨hop, hbody⟩ := hcom
      intro i hi
      simp only [straightOpsMem, List.mem_cons] at hi
      rcases hi with rfl | hi
      · split
        · exact opToLinstrR_plain _ (by simp_all) _ _ _
        · exact opToLinstrR_plain _ (by simp_all) _ _ _
        · exact opToLinstrR_plain _ (by simp_all) _ _ _
        · split
          · exact shiftLinstr_plain _ (Or.inl rfl) _ _ _ _ _
          · exact shiftLinstr_plain _ (Or.inr (Or.inl rfl)) _ _ _ _ _
          · exact shiftLinstr_plain _ (Or.inr (Or.inr rfl)) _ _ _ _ _
          · exact opToLinstrR_plain _ hop _ _ _
      · exact ih hbody (curDepth + 1) i hi

/-- Every op of a `ScalarMemN` program lies in the fragment's op set. -/
theorem scalarMemN_comOpsPlain {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarMemN com) : ComOpsPlain com := by
  induction h <;> trivial

/-- Every op of an `ArrMemN` program lies in the fragment's op set. -/
theorem arrMemN_comOpsPlain {w n : Nat} {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (JasminTy.stackArr w n)} (h : ArrMemN com) :
    ComOpsPlain com := by
  induction h with
  | ret v => trivial
  | reg e he _ ih => exact ⟨(scalarMemN_comOpsPlain he).1, ih⟩
  | store heq args _ ih => exact ⟨trivial, ih⟩

/-- **The chain of an `ArrMemN` update is plain**, so the flag-machine array
    theorems need no per-instance chain side condition. -/
theorem arrMemN_straightOpsMem_plain {w n : Nat} {Γ : Ctxt jasminDialect}
    {com : Com jasminDialect Γ (JasminTy.stackArr w n)} (h : ArrMemN com)
    (nArgs curDepth : Nat) : PlainLopnBody (straightOpsMem nArgs com curDepth) :=
  straightOpsMem_plain nArgs com (arrMemN_comOpsPlain h) curDepth

/-! ## 3. The touched array body -/

/-- **The touched array loop body**: the emitted `chain ++ writeback` pass
    followed by a touch segment. -/
def loopBodyArrTouchMN {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) (touch : List LinstrRM) : List LinstrRM :=
  loopBodyArrFullMN update nReg ++ touch

/-- Every element of the touched array body is an `Lopn`, given the touch is. -/
theorem loopBodyArrTouchMN_isLopn {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (nReg : String) (touch : List LinstrRM) (htouch : ∀ i ∈ touch, IsLopn i) :
    ∀ i ∈ loopBodyArrTouchMN update nReg touch, IsLopn i := by
  intro i hi
  rw [loopBodyArrTouchMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact loopBodyArrFullMN_isLopn update nReg i hi
  · exact htouch i hi

/-- **The per-trip pass on the flag machine.** One `runStraightF` pass of the
    touched array body from any state agreeing with the trip-`t` valuation and
    holding a readable counter: the plain pass computes one `JLoopBodyN.stepC`
    and decrements the counter, then the touch restores. -/
theorem loopBodyArrTouchMN_tripF {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (invs : Ctxt.Valuation invTys) (t : Nat) (arrt : Fin n → BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
      (tripValArrMN invs t arrt))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) (zf : Bool) :
    ∃ bt' zb, runStraightF (loopBodyArrTouchMN update nReg touch) bt zf = some (bt', zb)
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt'
          (tripValArrMN invs (t + 1) (JLoopBodyN.stepC update invs t arrt))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  obtain ⟨s1, hrunB, hAg1, hn1⟩ := loopBodyArrFullMN_trip update hupd nReg hna hnr
    invs t arrt bt hagree vn hn
  obtain ⟨bt', zb, hrunT, hAgT, hpres⟩ := htouch invs (t + 1)
    (JLoopBodyN.stepC update invs t arrt) s1 zf hAg1
  refine ⟨bt', zb, ?_, hAgT, hpres.trans hn1⟩
  rw [loopBodyArrTouchMN, runStraightF_append,
    runStraightF_plain _ (loopBodyArrFullMN_plain update nReg (arrMemN_straightOpsMem_plain hupd _ _)) bt zf, hrunB,
    Option.map_some, Option.bind_some]
  exact hrunT

/-- **The trip invariant on the flag machine.** Every `runBoundedStraightF` trip
    state of the touched array body agrees with its trip valuation at the source
    fold, with a readable counter. -/
theorem loopBodyArrTouchMN_invF {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (invs : Ctxt.Valuation invTys) (q : Nat) (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValArrMN invs 0 arr0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedStraightF (loopBodyArrTouchMN update nReg touch) q t s0 = some bt →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValArrMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs arr0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedStraightF_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedStraightF_succ_right] at hbt
      cases hbk : runBoundedStraightF (loopBodyArrTouchMN update nReg touch) q k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', zb, hbt', hAg', hn'⟩ := loopBodyArrTouchMN_tripF update hupd
            nReg hna hnr touch htouch invs k
            (JLoopBodyN.denote ⟨k, update⟩ invs arr0) bk hAgk vn hvn false
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' q
          · rw [getW_setLpc, hn']
            rfl

/-! ## 4. The flag-machine array export theorems -/

/-- **Flag-machine export faithfulness at an array accumulator.** The full
    guarded skeleton `guardedFlagLoopLinstrRM` (zero-trip guard at pc 0–1,
    `Llabel top` at 2, body at 3, flag back-edge and skip label behind) over the
    touched array body, run by `lsemFuelMemF` from pc `0` at a nonzero runtime
    count: the machine halts, with the flag set, on a state whose accumulator
    array decodes to the source fold `JLoopBodyN.denote ⟨m, update⟩`. The
    schedule (`hbound`/`htaken`/`hzero`) is at the shifted base pc `3`. -/
theorem guardedFlagLoopArr_export_faithful_denote {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top endL : LLabel) (nReg : String) (hne : top ≠ endL)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) b0
      (tripValArrMN invs 0 arr0))
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0)
    (hv0ne : (v0 == 0#64) = false)
    (m : Nat) (hm : 0 < m) (bfin : LstateM)
    (hbound : runBoundedStraightF (loopBodyArrTouchMN update nReg touch) 3 m
      (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedStraightF (loopBodyArrTouchMN update nReg touch) 3 i (b0.setLpc 3)
        = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM top endL nReg (loopBodyArrTouchMN update nReg touch)))
          k { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (accRegMN invTys) w n
            = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0)
        ∧ t.zf = true := by
  have hseed3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (b0.setLpc 3)
      (tripValArrMN invs 0 arr0) := StoreAgreesM.setLpc hseed 3
  have hn03 : ((b0.setLpc 3).reg.getW nReg 64).isSome := by
    rw [getW_setLpc, hv0]
    rfl
  have hinv := loopBodyArrTouchMN_invF update hupd nReg hna hnr touch htouch
    invs 3 (b0.setLpc 3) arr0 hseed3 hn03 m bfin hbound
  have hdec : decodeArrM bfin (accRegMN invTys) w n
      = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0) := tripAgree_getArr_acc hinv.1
  obtain ⟨k, t, hrun, _hlvm, hlarr, hzf⟩ := guardedFlagLoop_runBounded_general fn
    top endL nReg (loopBodyArrTouchMN update nReg touch)
    (loopBodyArrTouchMN_isLopn update nReg touch htLopn) hne b0 zf hpc v0 hv0 hv0ne
    m hm bfin hbound htaken hzero
  refine ⟨k, t, hrun, ?_, hzf⟩
  rw [decodeArrM_congr_larr _ _ hlarr]
  exact hdec

/-- **Flag-machine export faithfulness at `ComL.denote`, array accumulator.** The
    guarded flag loop over the touched array body realises the front node
    `ComL.forLoopNRt` at trip count `(count.lookup V).toNat`. -/
theorem guardedFlagLoopArr_export_faithful_comL {Γ : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top endL : LLabel) (nReg : String) (hne : top ≠ endL)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) b0
      (tripValArrMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (v0 : BitVec 64) (hv0 : b0.reg.getW nReg 64 = some v0)
    (hv0ne : (v0 == 0#64) = false)
    (hm : 0 < (count.lookup V).toNat) (bfin : LstateM)
    (hbound : runBoundedStraightF (loopBodyArrTouchMN update nReg touch) 3
      (count.lookup V).toNat (b0.setLpc 3) = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedStraightF (loopBodyArrTouchMN update nReg touch) 3 i (b0.setLpc 3)
        = some bi →
      condNZ bi (.reg nReg) = true)
    (hzero : bfin.reg.getW nReg 64 = some 0#64) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM top endL nReg (loopBodyArrTouchMN update nReg touch)))
          k { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (accRegMN invTys) w n
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V)
        ∧ t.zf = true := by
  rw [comL_forLoopNRt_ret_denote_acc]
  exact guardedFlagLoopArr_export_faithful_denote update hupd
    (Expr.lookupArgs invsV V) fn top endL nReg hne hna hnr touch htLopn htouch
    b0 zf hpc (initV.lookup V) hseed v0 hv0 hv0ne _ hm bfin hbound htaken hzero

/-! ## 5. The counter schedule, discharged

The schedule hypotheses of §4 follow from the trip pass: each trip decrements the
counter by one, so a counter seeded with `m < 2^64` reads nonzero after the first
`m - 1` trips and zero after the `m`-th. -/

/-- **The run of the touched array body with its counter.** From a seed
    agreement with counter `v0`, every trip count `t` has a trip state, agreeing
    with the source fold at `t`, whose counter reads `v0 - t`. -/
theorem loopBodyArrTouchMN_run {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (invs : Ctxt.Valuation invTys) (q : Nat) (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValArrMN invs 0 arr0))
    (v0 : BitVec 64) (hv0 : s0.reg.getW nReg 64 = some v0) :
    ∀ t, ∃ bt, runBoundedStraightF (loopBodyArrTouchMN update nReg touch) q t s0 = some bt
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValArrMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs arr0))
      ∧ bt.reg.getW nReg 64 = some (v0 - BitVec.ofNat 64 t) := by
  intro t
  induction t with
  | zero =>
      refine ⟨s0, rfl, hseed, ?_⟩
      rw [hv0]
      simp
  | succ k ih =>
      obtain ⟨bk, hbk, hAgk, hnk⟩ := ih
      obtain ⟨bt', zb, hbt', hAg', hn'⟩ := loopBodyArrTouchMN_tripF update hupd
        nReg hna hnr touch htouch invs k
        (JLoopBodyN.denote ⟨k, update⟩ invs arr0) bk hAgk _ hnk false
      refine ⟨bt'.setLpc q, ?_, ?_, ?_⟩
      · rw [runBoundedStraightF_succ_right, hbk, Option.bind_some, hbt', Option.map_some]
      · rw [JLoopBodyN.denote_succ]
        exact StoreAgreesM.setLpc hAg' q
      · rw [getW_setLpc, hn']
        congr 1
        rw [BitVec.sub_sub, BitVec.ofNat_add]

/-- A counter read `v` gives the counter guard `condNZ` its truth value `v ≠ 0`. -/
theorem condNZ_of_getW (b : LstateM) (nReg : String) (v : BitVec 64)
    (h : b.reg.getW nReg 64 = some v) : condNZ b (.reg nReg) = decide (v ≠ 0#64) := by
  unfold condNZ
  rw [show evalOperandN b.reg 64 (.reg nReg) = some v from h]

/-- The counter seeded with `m` reads nonzero after `i < m` trips. -/
theorem ofNat_sub_ofNat_ne_zero (m i : Nat) (hm : m < 2 ^ 64) (hi : i < m) :
    BitVec.ofNat 64 m - BitVec.ofNat 64 i ≠ 0#64 := by
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h'
  have hi' : i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hi'] at h'
  omega

/-- **Flag-machine export faithfulness at an array accumulator, with the counter
    schedule discharged.** The full guarded skeleton over the touched array
    body, started at pc `0` with the counter reading `m < 2^64` (zero included),
    halts on a state whose accumulator array decodes to
    `JLoopBodyN.denote ⟨m, update⟩`, with the flag set. -/
theorem guardedFlagLoopArr_faithful_closed {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (hupd : ArrMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top endL : LLabel) (nReg : String) (hne : top ≠ endL)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (touch : List LinstrRM) (htLopn : ∀ i ∈ touch, IsLopn i)
    (htouch : TouchRestoresFArrMN invTys w n touch nReg)
    (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) b0
      (tripValArrMN invs 0 arr0))
    (m : Nat) (hm64 : m < 2 ^ 64)
    (hv0 : b0.reg.getW nReg 64 = some (BitVec.ofNat 64 m)) :
    ∃ (k : Nat) (t : LstateMF),
      lsemFuelMemF (singletonProgM fn
          (guardedFlagLoopLinstrRM top endL nReg (loopBodyArrTouchMN update nReg touch)))
          k { prog := { base := b0, lfn := fn }, zf := zf } = some t
        ∧ decodeArrM t.prog.base (accRegMN invTys) w n
            = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0)
        ∧ t.zf = true := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨0 + 2, _, guardedFlagLoop_zeroTrip fn top endL nReg _
      (loopBodyArrTouchMN_isLopn update nReg touch htLopn) hne b0 zf hpc
      (by rw [hv0]) 0, tripAgree_getArr_acc hseed, rfl⟩
  · have hseed3 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) (b0.setLpc 3)
        (tripValArrMN invs 0 arr0) := StoreAgreesM.setLpc hseed 3
    have hv03 : (b0.setLpc 3).reg.getW nReg 64 = some (BitVec.ofNat 64 m) := by
      rw [getW_setLpc, hv0]
    have hrun := loopBodyArrTouchMN_run update hupd nReg hna hnr touch htouch invs 3
      (b0.setLpc 3) arr0 hseed3 _ hv03
    obtain ⟨bfin, hbfin, _, hzfin⟩ := hrun m
    refine guardedFlagLoopArr_export_faithful_denote update hupd invs fn top endL nReg
      hne hna hnr touch htLopn htouch b0 zf hpc arr0 hseed (BitVec.ofNat 64 m) hv0 ?_
      m hm bfin hbfin ?_ ?_
    · have := ofNat_sub_ofNat_ne_zero m 0 hm64 hm
      simpa using this
    · intro i hi him bi hbi
      obtain ⟨bi', hbi', _, hni⟩ := hrun i
      rw [hbi] at hbi'
      obtain rfl := Option.some.inj hbi'
      rw [condNZ_of_getW _ _ _ hni]
      exact decide_eq_true (ofNat_sub_ofNat_ne_zero m i hm64 him)
    · rw [hzfin]
      simp

/-! ## 6. The emitted touch shape -/

/-- The emitted invariant touches over a counter `nReg`: one `CMP nReg, r` per
    touched register `r` (the `invTouch` segment of `forLoopLcmdNRt`). -/
def cmpTouchRM (nReg : String) (regs : List String) : List LinstrRM :=
  regs.map (fun r =>
    (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .reg r], MemTag.reg none))

/-- Every emitted touch is an `Lopn`. -/
theorem cmpTouchRM_isLopn (nReg : String) (regs : List String) :
    ∀ i ∈ cmpTouchRM nReg regs, IsLopn i := by
  intro i hi
  simp only [cmpTouchRM, List.mem_map] at hi
  obtain ⟨r, _, rfl⟩ := hi
  exact ⟨_, _, _, rfl⟩

/-- A run of compares `CMP nReg, r` moves only the pc and the flag: from a state
    where `nReg` and every compared register read at width `64`, the run succeeds
    at the same register store and array carrier, the pc advanced by the number
    of compares. -/
theorem runStraightF_cmpTouchRM (nReg : String) :
    ∀ (regs : List String) (s : LstateM) (zf : Bool),
      (s.reg.getW nReg 64).isSome → (∀ r ∈ regs, (s.reg.getW r 64).isSome) →
      ∃ zf', runStraightF (cmpTouchRM nReg regs) s zf
        = some (s.setLpc (s.lpc + regs.length), zf') := by
  intro regs
  induction regs with
  | nil =>
      intro s zf _ _
      refine ⟨zf, ?_⟩
      show some (s, zf) = some (s.setLpc (s.lpc + 0), zf)
      congr 2
  | cons r rs ih =>
      intro s zf hn hr
      obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hn
      obtain ⟨vr, hvr⟩ := Option.isSome_iff_exists.mp (hr r (by simp))
      have hstep : fstepF (.Lopn [.reg nReg] (withWidthTag 64 "CMP") [.reg nReg, .reg r],
          MemTag.reg none) s zf = some (s.nextPc, vn == vr) := by
        unfold fstepF
        simp only [cmpArgs?, if_true]
        rw [show evalOperandN s.reg 64 (.reg nReg) = some vn from hvn,
          show evalOperandN s.reg 64 (.reg r) = some vr from hvr]
      obtain ⟨zf', hrest⟩ := ih s.nextPc (vn == vr)
        (by rw [LstateM.reg_nextPc, LstateN.getW_nextPc]; exact hn)
        (fun r' hr' => by
          rw [LstateM.reg_nextPc, LstateN.getW_nextPc]; exact hr r' (by simp [hr']))
      refine ⟨zf', ?_⟩
      show (fstepF _ s zf).bind _ = _
      rw [hstep, Option.bind_some]
      show runStraightF (cmpTouchRM nReg rs) s.nextPc (vn == vr) = _
      rw [hrest]
      congr 2
      simp only [LstateM.lpc_nextPc, List.length_cons]
      cases s
      simp only [LstateM.setLpc, LstateM.nextPc, LstateN.nextPc, LstateM.lpc]
      congr 2
      omega

/-- **The emitted touches restore.** A list of compares `CMP nReg, r` satisfies
    the array restoration discipline whenever the counter and every compared
    register read at width `64` in every state agreeing with an array trip
    valuation. -/
theorem cmpTouchRM_restores {w n : Nat} (nReg : String) (regs : List String)
    (hread : ∀ (invs : Ctxt.Valuation invTys) (t : Nat) (arr : Fin n → BitVec w)
      (s : LstateM),
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) s (tripValArrMN invs t arr) →
      (s.reg.getW nReg 64).isSome ∧ ∀ r ∈ regs, (s.reg.getW r 64).isSome) :
    TouchRestoresFArrMN invTys w n (cmpTouchRM nReg regs) nReg := by
  intro invs t arr s zf hag
  obtain ⟨hn, hr⟩ := hread invs t arr s hag
  obtain ⟨zf', hrun⟩ := runStraightF_cmpTouchRM nReg regs s zf hn hr
  exact ⟨_, zf', hrun, StoreAgreesM.setLpc hag _, getW_setLpc s _ nReg 64⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
