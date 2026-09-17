/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# Direct addressing through the physical-register export

`ConstantTimeCoverage.allDirect` is the decidable constant-time class on a
`List (JInstr 64)`: every instruction addresses memory through a base register and
a compile-time-constant displacement, never through a register index. The shipped
`Lprog` export `Com.toLprogPhysAbi` (`JasminLprogExport`) works on `Lcmd`, so this
module states the same property one level up and transports it down.

## The `Lcmd`-level class

`isIndexed` marks the register-indexed (SIB) operand `LOperand.arrIdx base idx scale`,
whose effective address is `base + scale · (value of idx)`. `linstrRDirect` holds of
an instruction none of whose operands is `arrIdx`, and `lcmdDirect` of a command all
of whose instructions are `linstrRDirect`.

## The two halves

* `gatherJBlock6_allDirect` — the `JInstr` gather of an `lcmdDirect` body is
  `allDirect`. The gather's only `loadMemIdx`/`storeMemIdx` arms
  (`LoweringExtendedCoverage.lowerLinstrExtCov`) match on an `arrIdx` operand, and
  every other arm of the six-layer lowering emits register, immediate, or
  constant-displacement memory instructions.
* `physBodyWithStores_lcmdDirect` — the deployed linear-scan allocation, spill
  materialization, and two-address legalization pass preserves `lcmdDirect`. Physical
  renaming (`remapOperand` / `remapOperandCalleeSave`) maps `arrIdx` to `arrIdx` and
  everything else to a non-`arrIdx` operand; a spill slot is the register-shaped name
  `k.N` at a fixed frame offset, so the reload/store `MOV`s the legalizers insert
  (`legalizeBinop`, `legalizeMov`, `legalizeMemLoad`, `legalizeMemStore`,
  `lowerTwoAddr`, `lowerTwoAddrShiftImm`, `lowerNativeShiftRotate`) introduce no
  indexed operand.

`comToLfundefPhysAbi_lcmdDirect` and `toLprogPhysAbi_lcmdDirect` compose that core
with the pre-allocation rewrites (`expandCallShadows`, the residence rename,
`materializeShiftCountImms`, `canonicalizeMemrefThread`, the argument-liveness pin)
and the ABI wrapping (`buildPrologue`, `buildArgPtrMaterialize`, the extra input
saves, the return materialization, `calleeSaveRestoreEpilogue`, `insertEpilogue`).
`toLprogPhysAbi_gather_allDirect` and `toLprogPhysAbi_gather_constant_time` land the
result in `MachineConstantTime.blockLeak`.

## Scope

The hypothesis is on the *virtual* body `(comToLfundef com immSlotMap).lfd_body`: a
`Com` that lowers to a `LOADIDX`/`STOREIDX` (the image of `memrefGetDyn` /
`memrefSetDyn`) is outside the class, and the conclusion says nothing about it.

Which shipped kernels that excludes, as of 2026-07-27: the emitted `.s` carrying
a scaled-index memory operand are `FAEST/VoleCommitEmit`'s `vole_commit_owned`
and `FAEST/BavcOpenEmit`'s `bavc_open_owned`. Every other owned kernel — the
GF(251) SDitH, GF(256) UOV and MQOM row-dot families included — addresses memory
only as a base register plus a compile-time displacement, so it is inside the
class. Byte- and halfword-packed kernels reach their cells by a word index and
immediate shifts rather than a scaled index, which is why a narrow ABI width
does not by itself leave the fragment. Re-derive the list with a search for a
`(%base,%index,scale)` operand over the emitted assembly rather than assuming
it; a front change that admits `memrefGetDyn` on a new kernel will extend it.

The conclusion is preservation of the addressing class, not equality of leakage
traces. Allocation is a compile-time decision, so no spill introduces a
value-dependent address; a spilled body nevertheless issues memory accesses the
unspilled body does not, so its `blockLeak` trace is longer. `MLeak.mem base off`
records the base register *name* and the constant displacement, so the model treats
the contents of a base register as public.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (IsDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
  (allDirect allDirect_append)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
  (lowerLinstrExtCov2 lowerSarJ)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms

/-! ## 1. Register-indexed addressing at the `Lprog` level -/

/-- `true` for the register-indexed (SIB) operand `arrIdx base idx scale`, whose
    effective address depends on the value in the index register. -/
def isIndexed : LOperand → Bool
  | .arrIdx _ _ _ => true
  | _ => false

/-- `true` when no operand of the instruction is register-indexed. -/
def linstrRDirect : LinstrR → Bool
  | .Lopn dsts _ srcs => dsts.all (fun o => !isIndexed o) && srcs.all (fun o => !isIndexed o)
  | .Ligoto o => !isIndexed o
  | .Lcond o _ => !isIndexed o
  | _ => true

/-- `true` when no instruction of the command uses register-indexed addressing. -/
def lcmdDirect (c : Lcmd) : Bool := c.all (fun i => linstrRDirect i.li_i)

theorem lcmdDirect_iff (c : Lcmd) :
    lcmdDirect c = true ↔ ∀ i ∈ c, linstrRDirect i.li_i = true := by
  simp [lcmdDirect]

/-! ## 2. The `JInstr` gather of an index-free body -/

/-- `allDirect` from the membership form. -/
theorem allDirect_of_forall {js : List (JInstr 64)} (h : ∀ j ∈ js, IsDirect j) :
    allDirect js = true := by
  rw [allDirect, List.all_eq_true]
  exact fun j hj => decide_eq_true (h j hj)

theorem allDirect_forall {js : List (JInstr 64)} (h : allDirect js = true) :
    ∀ j ∈ js, IsDirect j :=
  ConstantTimeCoverage.allDirect_mem_isDirect js h

theorem lowerAluJ_direct {dst opn : String} {s : JOperand} {j : JInstr 64}
    (h : lowerAluJ dst opn s = some j) : IsDirect j := by
  unfold lowerAluJ at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst_vars <;> simp [IsDirect]

theorem lowerMulHiJ_direct (dst : String) (s0 s1 : JOperand) :
    allDirect (lowerMulHiJ dst s0 s1) = true :=
  allDirect_of_forall (by simp [lowerMulHiJ, IsDirect])

theorem lowerShiftRegJ_direct {dst bare : String} {s0 s1 : JOperand} {js : List (JInstr 64)}
    (h : lowerShiftRegJ dst bare s0 s1 = some js) : allDirect js = true := by
  unfold lowerShiftRegJ at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact allDirect_of_forall (by simp [IsDirect])

theorem lowerAluJ2_direct {dst opn : String} {s0 s1 : JOperand} {js : List (JInstr 64)}
    (h : lowerAluJ2 dst opn s0 s1 = some js) : allDirect js = true := by
  unfold lowerAluJ2 at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · exact lowerShiftRegJ_direct h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact allDirect_of_forall (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · simp [IsDirect]
    · exact lowerAluJ_direct ha)

theorem lowerShiftImmJ_direct {dst opn : String} {src : JOperand} {js : List (JInstr 64)}
    (h : lowerShiftImmJ dst opn src = some js) : allDirect js = true := by
  unfold lowerShiftImmJ at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨p, _, rfl⟩ := h
  exact allDirect_of_forall (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · simp [IsDirect]
    · split <;> simp [IsDirect])

theorem lowerLinstrExt_direct {i : LinstrR} {js : List (JInstr 64)}
    (h : lowerLinstrExt i = some js) : allDirect js = true := by
  unfold lowerLinstrExt at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect, lowerLoad])
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect, lowerStore])
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact allDirect_of_forall (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      subst hj; exact lowerAluJ_direct ha)
  · simp at h

theorem lowerLinstrExt2_direct {i : LinstrR} {js : List (JInstr 64)}
    (h : lowerLinstrExt2 i = some js) : allDirect js = true := by
  unfold lowerLinstrExt2 at h
  split at h
  · exact lowerLinstrExt_direct h
  · exact lowerLinstrExt_direct h
  · simp only [Option.some.injEq] at h
    subst h; exact lowerMulHiJ_direct _ _ _
  · exact lowerAluJ2_direct h
  · split at h
    · exact lowerShiftImmJ_direct h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact allDirect_of_forall (by
          intro j hj
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
          subst hj; rename_i ha; exact lowerAluJ_direct ha)
      · exact lowerLinstrExt_direct h
  · exact lowerLinstrExt_direct h

theorem lowerLinstrExtCov_direct {i : LinstrR} {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerLinstrExtCov i = some js) :
    allDirect js = true := by
  unfold lowerLinstrExtCov at h
  split at h
  · simp [linstrRDirect, isIndexed] at hi
  · simp [linstrRDirect, isIndexed] at hi
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect])
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect])
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect])
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect])
  · exact lowerLinstrExt2_direct h

theorem lowerAluJ2InPlace_direct {dst opn : String} {s0 s1 : JOperand}
    {js : List (JInstr 64)} (h : lowerAluJ2InPlace dst opn s0 s1 = some js) :
    allDirect js = true := by
  unfold lowerAluJ2InPlace at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · exact lowerShiftRegJ_direct h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨a, ha, rfl⟩ := h
  refine allDirect_of_forall ?_
  split
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; exact lowerAluJ_direct ha
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · simp [IsDirect]
    · exact lowerAluJ_direct ha

/-- The select block and the immediate arithmetic right-shift blocks are
    `IsDirect` throughout; every other shape delegates to `lowerLinstrExtCov`. -/
theorem lowerLinstrExtCov2_direct {i : LinstrR} {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerLinstrExtCov2 i = some js) :
    allDirect js = true := by
  unfold lowerLinstrExtCov2 at h
  split at h
  · -- `CMOV:64`: declines when the condition aliases the destination.
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq] at h
      subst h
      exact CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar.lowerLinstrExtCov2_cmov_allDirect _ _ _ _
  · -- the untagged narrow `SAR:31`
    simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp [IsDirect, lowerSarJ])
  · -- the tagged shifts, count read by `sarCountOf`
    split at h
    · simp only [Option.some.injEq] at h
      subst h; exact allDirect_of_forall (by simp [IsDirect, lowerSarJ])
    · exact lowerLinstrExtCov_direct hi h
  · exact lowerLinstrExtCov_direct hi h

theorem lowerLinstrExtCov3_direct {i : LinstrR} {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerLinstrExtCov3 i = some js) :
    allDirect js = true := by
  unfold lowerLinstrExtCov3 at h
  split at h
  · exact lowerLinstrExtCov_direct hi h
  · exact lowerLinstrExtCov_direct hi h
  · exact lowerLinstrExtCov_direct hi h
  · exact lowerAluJ2InPlace_direct h
  · exact lowerLinstrExtCov2_direct hi h

theorem lowerLinstrExtCov4_direct {i : LinstrR} {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerLinstrExtCov4 i = some js) :
    allDirect js = true := by
  unfold lowerLinstrExtCov4 at h
  split at h
  · exact lowerLinstrExtCov3_direct (by simpa [linstrRDirect] using hi) h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine allDirect_of_forall ?_
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        subst hj; split <;> simp [IsDirect]
      · exact lowerLinstrExtCov3_direct hi h
    · exact lowerLinstrExtCov3_direct hi h
  · exact lowerLinstrExtCov3_direct hi h

theorem lowerCov5_direct {frame spillW qsaveB : Nat} {i : LinstrR}
    {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerCov5 frame spillW i qsaveB = some js) :
    allDirect js = true := by
  unfold lowerCov5 at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h; exact allDirect_of_forall (by simp [IsDirect])
    · simp only [Option.some.injEq] at h
      subst h; exact allDirect_of_forall (by simp [IsDirect])
    · exact lowerLinstrExtCov4_direct (by simpa [linstrRDirect] using hi) h
  · exact lowerLinstrExtCov4_direct hi h

theorem lowerCov6_direct {frame spillW qsaveB : Nat} {i : LinstrR}
    {js : List (JInstr 64)}
    (hi : linstrRDirect i = true) (h : lowerCov6 frame spillW i qsaveB = some js) :
    allDirect js = true := by
  unfold lowerCov6 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; exact allDirect_of_forall (by simp)
  · exact lowerCov5_direct hi h

theorem mapM_flatten_direct {f : Linstr → Option (List (JInstr 64))}
    (hf : ∀ i : Linstr, linstrRDirect i.li_i = true →
      ∀ js, f i = some js → allDirect js = true) :
    ∀ l : List Linstr, (∀ i ∈ l, linstrRDirect i.li_i = true) →
      ∀ ls, l.mapM f = some ls → allDirect ls.flatten = true := by
  intro l
  induction l with
  | nil =>
    intro _ ls h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp [allDirect]
  | cons a t ih =>
    intro hall ls h
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp only [hfa] at h; simp at h
    | some b =>
      cases hmt : t.mapM f with
      | none => simp only [hfa, hmt] at h; simp at h
      | some bs =>
        simp only [hfa, hmt] at h
        injection h with h
        subst h
        have h1 : allDirect b = true :=
          hf a (hall a (List.mem_cons_self ..)) b hfa
        have h2 : allDirect bs.flatten = true :=
          ih (fun i hi => hall i (List.mem_cons_of_mem a hi)) bs hmt
        simpa [allDirect_append] using And.intro h1 h2

/-- **The `JInstr` gather of an index-free `Lprog` body is in the constant-time
    class.** When no instruction of `body` uses register-indexed (SIB) addressing,
    every instruction the whole-body gather produces uses direct base +
    compile-time-constant displacement addressing. -/
theorem gatherJBlock6_allDirect {body : Lcmd} {g : List (JInstr 64)}
    (hd : lcmdDirect body = true) (h : gatherJBlock6 body = some g) :
    allDirect g = true := by
  simp only [gatherJBlock6, Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, rfl⟩ := h
  refine mapM_flatten_direct ?_ _ ?_ ls hls
  · intro i hi js hj
    exact lowerCov6_direct hi hj
  · intro i hi
    exact (lcmdDirect_iff body).mp hd i (List.mem_of_mem_filter hi)

/-! ## 3. The legalization helpers preserve index-freeness -/

/-- `true` when no instruction of the untagged command uses register-indexed
    addressing. -/
def lcmdRDirect (l : List LinstrR) : Bool := l.all linstrRDirect

@[simp] theorem lcmdRDirect_nil : lcmdRDirect [] = true := rfl

@[simp] theorem lcmdRDirect_cons (i : LinstrR) (l : List LinstrR) :
    lcmdRDirect (i :: l) = (linstrRDirect i && lcmdRDirect l) := by
  simp [lcmdRDirect]

@[simp] theorem lcmdRDirect_append (a b : List LinstrR) :
    lcmdRDirect (a ++ b) = (lcmdRDirect a && lcmdRDirect b) := by
  simp [lcmdRDirect]

@[simp] theorem isIndexed_reg (n : String) : isIndexed (.reg n) = false := rfl

@[simp] theorem isIndexed_imm (v : Nat) : isIndexed (.imm v) = false := rfl

@[simp] theorem isIndexed_arr (b : String) (i : Nat) : isIndexed (.arr b i) = false := rfl

/-- Physical-register renaming never introduces register-indexed addressing. -/
theorem remapOperand_isIndexed (body : Lcmd) (tbl : Array Nat) (o : LOperand) :
    isIndexed (remapOperand body tbl o) = isIndexed o := by
  cases o <;> rfl

theorem remapOperandCalleeSave_isIndexed (body : Lcmd) (tbl : Array Nat) (o : LOperand) :
    isIndexed (remapOperandCalleeSave body tbl o) = isIndexed o := by
  cases o <;> rfl

/-- The SIB legalizer is the identity on a non-indexed operand. -/
theorem legalizeSibElem_of_direct {o : LOperand} (h : isIndexed o = false) :
    legalizeSibElem o = ([], o) := by
  cases o <;> simp_all [legalizeSibElem, isIndexed]

/-- The memref base reload is the identity on a non-indexed operand. -/
theorem reloadMemrefBase_of_direct (m : String → Option String) {o : LOperand}
    (h : isIndexed o = false) : reloadMemrefBase m o = ([], o) := by
  cases o <;> simp_all [reloadMemrefBase, isIndexed]

theorem materializeWideImm_direct {s1 : LOperand} {mov : String}
    (h : isIndexed s1 = false) :
    lcmdRDirect (materializeWideImm s1 mov).1 = true ∧
      isIndexed (materializeWideImm s1 mov).2 = false := by
  unfold materializeWideImm
  split
  · split <;> simp_all [lcmdRDirect, linstrRDirect]
  · simpa using h

theorem legalizeBinop_direct {dst src : LOperand} {opn mov : String}
    (hd : isIndexed dst = false) (hs : isIndexed src = false) :
    lcmdRDirect (legalizeBinop dst src opn mov) = true := by
  unfold legalizeBinop
  split <;> simp_all [linstrRDirect]

theorem legalizeMov_direct {dst src : LOperand} {mov : String}
    (hd : isIndexed dst = false) (hs : isIndexed src = false) :
    lcmdRDirect (legalizeMov dst src mov) = true := by
  unfold legalizeMov
  split <;> simp_all [linstrRDirect]

theorem legalizeMemLoad_direct {dst src : LOperand} {opn mov : String}
    (hd : isIndexed dst = false) (hs : isIndexed src = false) :
    lcmdRDirect (legalizeMemLoad dst src opn mov) = true := by
  cases src
  case arrIdx => simp [isIndexed] at hs
  all_goals
    (unfold legalizeMemLoad
     simp only [legalizeSibElem, List.nil_append]
     split <;> simp [lcmdRDirect, linstrRDirect, hd])

theorem legalizeMemStore_direct {dArr addr val : LOperand} {opn mov : String}
    (hA : isIndexed dArr = false) (ha : isIndexed addr = false)
    (hv : isIndexed val = false) :
    lcmdRDirect (legalizeMemStore dArr addr val opn mov) = true := by
  cases addr
  case arrIdx => simp [isIndexed] at ha
  all_goals
    (unfold legalizeMemStore
     simp only [legalizeSibElem, List.nil_append]
     split <;>
       first
         | (exfalso; simp_all; done)
         | simp [lcmdRDirect, linstrRDirect, hA, hv])

theorem lowerTwoAddr_direct {dst s0 s1 : LOperand} {opn mov : String}
    (hd : isIndexed dst = false) (h0 : isIndexed s0 = false)
    (h1 : isIndexed s1 = false) :
    lcmdRDirect (lowerTwoAddr dst s0 s1 opn mov) = true := by
  unfold lowerTwoAddr
  have hm := materializeWideImm_direct (s1 := s1) (mov := mov) h1
  rcases hmm : materializeWideImm s1 mov with ⟨pre, s1'⟩
  rw [hmm] at hm
  obtain ⟨hpre, hs1⟩ := hm
  by_cases hds : dst = s0
  · subst hds
    simp [hpre, legalizeBinop_direct hd hs1]
  · simp [hds, hpre, legalizeMov_direct hd h0, legalizeBinop_direct hd hs1]

theorem lowerTwoAddrShiftImm_direct {dst s0 : LOperand} {v : Nat} {opn mov : String}
    (hd : isIndexed dst = false) (h0 : isIndexed s0 = false) :
    lcmdRDirect (lowerTwoAddrShiftImm dst s0 v opn mov) = true := by
  unfold lowerTwoAddrShiftImm
  split
  · simp_all [linstrRDirect]
  · split <;> simp_all [linstrRDirect, legalizeMov_direct hd h0]

theorem lowerNativeShiftRotate_direct {dst s : LOperand} {opn mov : String}
    (hd : isIndexed dst = false) (hs : isIndexed s = false) :
    lcmdRDirect (lowerNativeShiftRotate dst s opn mov) = true := by
  unfold lowerNativeShiftRotate
  split <;> simp_all [linstrRDirect]

/-! ## 4. Structural lemmas for `Lcmd` -/

@[simp] theorem lcmdDirect_nil : lcmdDirect [] = true := rfl

@[simp] theorem lcmdDirect_append (a b : Lcmd) :
    lcmdDirect (a ++ b) = (lcmdDirect a && lcmdDirect b) := by
  simp [lcmdDirect]

theorem lcmdDirect_flatMap {α : Type} (l : List α) (f : α → Lcmd)
    (h : ∀ a ∈ l, lcmdDirect (f a) = true) : lcmdDirect (l.flatMap f) = true := by
  rw [lcmdDirect, List.all_eq_true]
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨a, ha, hia⟩ := hi
  exact (lcmdDirect_iff (f a)).mp (h a ha) i hia

theorem lcmdDirect_map {l : List LinstrR} {g : LinstrR → Linstr}
    (hg : ∀ r, (g r).li_i = r) (h : lcmdRDirect l = true) :
    lcmdDirect (l.map g) = true := by
  rw [lcmdDirect, List.all_eq_true]
  intro i hi
  rw [List.mem_map] at hi
  obtain ⟨r, hr, rfl⟩ := hi
  rw [hg r]
  exact List.all_eq_true.mp h r hr

theorem linstrRDirect_Lopn {dsts srcs : List LOperand} {opn : String}
    (h : linstrRDirect (.Lopn dsts opn srcs) = true) :
    (∀ o ∈ dsts, isIndexed o = false) ∧ (∀ o ∈ srcs, isIndexed o = false) := by
  simp only [linstrRDirect, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  exact ⟨fun o ho => h.1 o ho, fun o ho => h.2 o ho⟩

theorem linstrRDirect_Lopn_mk {dsts srcs : List LOperand} {opn : String}
    (hd : ∀ o ∈ dsts, isIndexed o = false) (hs : ∀ o ∈ srcs, isIndexed o = false) :
    linstrRDirect (.Lopn dsts opn srcs) = true := by
  simp only [linstrRDirect, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  exact ⟨fun o ho => hd o ho, fun o ho => hs o ho⟩

theorem mem_of_mem_zipIdx {α : Type} {l : List α} {p : α × Nat} (h : p ∈ l.zipIdx) :
    p.1 ∈ l := by
  have := List.mem_map_of_mem (f := Prod.fst) h
  rwa [List.zipIdx_map_fst] at this

/-! ## 5. The deployed allocator -/

theorem physBodyWithStores_lcmdDirect
    (shiftImm : ShiftImmOracle) (body : Lcmd) (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String))
    (hd : lcmdDirect body = true) :
    lcmdDirect (physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap
      storeBase abiW memrefBaseReload callArgBaseReload) = true := by
  unfold physBodyWithStores
  simp only []
  generalize hRg : (if bodyHasCall body = true then
      remapOperandCalleeSave body (straightCallComposeTable body (physTableOut body outStoreMap))
    else remapOperand body (straightCallComposeTable body (physTableOut body outStoreMap))) = R
  have hr : ∀ o : LOperand, isIndexed (R o) = isIndexed o := by
    rw [← hRg]
    intro o
    split
    · exact remapOperandCalleeSave_isIndexed _ _ _
    · exact remapOperand_isIndexed _ _ _
  refine lcmdDirect_flatMap _ _ ?_
  rintro ⟨i, virtIdx⟩ hmem
  have hi : linstrRDirect i.li_i = true :=
    (lcmdDirect_iff body).mp hd i (mem_of_mem_zipIdx hmem)
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the inline ABI-prologue loads: register / immediate operands only
    refine lcmdDirect_flatMap _ _ ?_
    intro a _
    split <;> simp [lcmdDirect, linstrRDirect]
  · -- the register-allocated, legalized expansion of the instruction
    have hmapR : ∀ l : List LOperand, (∀ o ∈ l, isIndexed o = false) →
        ∀ o ∈ l.map R, isIndexed o = false := by
      intro l hl o ho
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
      exact (hr o').trans (hl o' ho')
    split
    · -- two or more sources
      rename_i heq
      have h1 := hi
      rw [heq] at h1
      obtain ⟨hD, hS⟩ := linstrRDirect_Lopn h1
      split
      · split
        · exact lcmdDirect_map (fun _ => rfl)
            (lowerTwoAddrShiftImm_direct ((hr _).trans (hD _ (by simp)))
              ((hr _).trans (hS _ (by simp))))
        · exact lcmdDirect_map (fun _ => rfl)
            (lowerTwoAddr_direct ((hr _).trans (hD _ (by simp)))
              ((hr _).trans (hS _ (by simp))) ((hr _).trans (hS _ (by simp))))
      · split
        · rename_i heq2
          have h2 := hi
          rw [heq2] at h2
          obtain ⟨hD2, hS2⟩ := linstrRDirect_Lopn h2
          split
          · rw [reloadMemrefBase_of_direct _ ((hr _).trans (hS2 _ (by simp)))]
            simp only [List.map_nil, List.nil_append]
            exact lcmdDirect_map (fun _ => rfl)
              (legalizeMemStore_direct ((hr _).trans (hD2 _ (by simp)))
                ((hr _).trans (hS2 _ (by simp))) ((hr _).trans (hS2 _ (by simp))))
          · simp only [lcmdDirect, List.all_cons, List.all_nil, Bool.and_true]
            exact linstrRDirect_Lopn_mk
              (by simpa using (hr _).trans (hD2 _ (by simp)))
              (by
                intro o ho
                simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
                rcases ho with rfl | rfl
                · exact (hr _).trans (hS2 _ (by simp))
                · exact (hr _).trans (hS2 _ (by simp)))
        · rename_i heq2
          have h2 := hi
          rw [heq2] at h2
          obtain ⟨hD2, hS2⟩ := linstrRDirect_Lopn h2
          simp only [lcmdDirect, List.all_cons, List.all_nil, Bool.and_true]
          exact linstrRDirect_Lopn_mk (hmapR _ hD2) (hmapR _ hS2)
        · simpa [lcmdDirect] using hi
    · -- exactly one destination and one source
      rename_i heq
      have h1 := hi
      rw [heq] at h1
      obtain ⟨hD, hS⟩ := linstrRDirect_Lopn h1
      split
      · exact lcmdDirect_map (fun _ => rfl)
          (lowerNativeShiftRotate_direct ((hr _).trans (hD _ (by simp)))
            ((hr _).trans (hS _ (by simp))))
      · split
        · rw [reloadMemrefBase_of_direct _ ((hr _).trans (hS _ (by simp)))]
          simp only [List.map_nil, List.nil_append]
          exact lcmdDirect_map (fun _ => rfl)
            (legalizeMemLoad_direct ((hr _).trans (hD _ (by simp)))
              ((hr _).trans (hS _ (by simp))))
        · simp only [lcmdDirect, List.all_cons, List.all_nil, Bool.and_true]
          exact linstrRDirect_Lopn_mk
            (by simpa using (hr _).trans (hD _ (by simp)))
            (by simpa using (hr _).trans (hS _ (by simp)))
    · -- any other `Lopn` shape
      rename_i heq
      have h1 := hi
      rw [heq] at h1
      obtain ⟨hD, hS⟩ := linstrRDirect_Lopn h1
      simp only [lcmdDirect, List.all_cons, List.all_nil, Bool.and_true]
      exact linstrRDirect_Lopn_mk (hmapR _ hD) (hmapR _ hS)
    · -- a non-`Lopn` instruction
      simpa [lcmdDirect] using hi
  · -- the post-call pointer reloads: register operands only
    split
    · rw [lcmdDirect, List.all_eq_true]
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨p, _, rfl⟩ := hz
      simp [linstrRDirect]
    · simp
  · -- the inline output store: register operands and the allocated destination
    split
    · rename_i heq
      rw [heq] at hi
      obtain ⟨hD, _⟩ := linstrRDirect_Lopn hi
      split
      · split
        · split <;> simp [lcmdDirect, linstrRDirect, hr, hD _ (List.mem_cons_self ..)]
        · simp
      · simp
    · simp

/-! ## 6. The ABI wrapper and the pre-allocation rewrites -/

theorem lcmdDirect_of_mem {c : Lcmd} (h : ∀ i ∈ c, linstrRDirect i.li_i = true) :
    lcmdDirect c = true := (lcmdDirect_iff c).mpr h

theorem lcmdDirect_dropLast {c : Lcmd} (h : lcmdDirect c = true) :
    lcmdDirect c.dropLast = true :=
  lcmdDirect_of_mem fun i hi =>
    (lcmdDirect_iff c).mp h i (List.dropLast_subset _ hi)

theorem lcmdDirect_filter {c : Lcmd} {p : Linstr → Bool} (h : lcmdDirect c = true) :
    lcmdDirect (c.filter p) = true :=
  lcmdDirect_of_mem fun i hi =>
    (lcmdDirect_iff c).mp h i (List.mem_of_mem_filter hi)

theorem lcmdDirect_mapOperands {g : LOperand → LOperand}
    (hg : ∀ o, isIndexed (g o) = isIndexed o) {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (body.map (fun i =>
      match i.li_i with
      | .Lopn dsts opn srcs => ⟨i.li_ii, .Lopn (dsts.map g) opn (srcs.map g)⟩
      | _ => i)) = true := by
  refine lcmdDirect_of_mem ?_
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  have h1 := (lcmdDirect_iff body).mp h i hi
  split
  · rename_i heq
    rw [heq] at h1
    obtain ⟨hD, hS⟩ := linstrRDirect_Lopn h1
    exact linstrRDirect_Lopn_mk
      (fun o ho => by obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho; exact (hg o').trans (hD o' ho'))
      (fun o ho => by obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho; exact (hg o').trans (hS o' ho'))
  · exact h1

theorem canonMemrefOperand_isIndexed (m : Std.HashMap String String) (o : LOperand) :
    isIndexed (canonMemrefOperand m o) = isIndexed o := by
  cases o <;> rfl

theorem residenceRenameOperand_isIndexed (nArgs : Nat) (f : Nat → Nat) (o : LOperand) :
    isIndexed (residenceRenameOperand nArgs f o) = isIndexed o := by
  cases o <;> rfl

theorem canonicalizeMemrefThread_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (canonicalizeMemrefThread body) = true := by
  unfold canonicalizeMemrefThread
  simp only []
  split
  · exact h
  · exact lcmdDirect_mapOperands (canonMemrefOperand_isIndexed _) h

theorem residenceRenameBody_lcmdDirect (nArgs : Nat) (f : Nat → Nat) {body : Lcmd}
    (h : lcmdDirect body = true) :
    lcmdDirect (residenceRenameBody nArgs f body) = true :=
  lcmdDirect_mapOperands (residenceRenameOperand_isIndexed nArgs f) h

theorem materializeShiftCountImms_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (materializeShiftCountImms body) = true := by
  unfold materializeShiftCountImms
  refine lcmdDirect_of_mem ?_
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  have h1 := (lcmdDirect_iff body).mp h i hi
  split
  · rename_i heq
    have h2 := h1
    rw [heq] at h2
    obtain ⟨hD, hS⟩ := linstrRDirect_Lopn h2
    split
    · split
      · split
        · refine linstrRDirect_Lopn_mk hD ?_
          intro o ho
          simp only [List.mem_cons] at ho
          rcases ho with rfl | rfl | ho
          · exact hS _ (by simp)
          · rfl
          · exact hS _ (by simp [ho])
        · exact h1
      · exact h1
    · exact h1
  · exact h1

theorem marshalClassedArgs_direct (args : List (LOperand × Bool))
    (hargs : ∀ p ∈ args, isIndexed p.1 = false) (g s : Nat) :
    lcmdDirect (marshalClassedArgs args g s) = true := by
  induction args generalizing g s with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨op, isSse⟩ := a
    have hop : isIndexed op = false := hargs _ (List.mem_cons_self ..)
    have ht : ∀ p ∈ t, isIndexed p.1 = false := fun p hp => hargs p (List.mem_cons_of_mem _ hp)
    unfold marshalClassedArgs
    split
    · split
      · simpa [lcmdDirect, linstrRDirect, hop] using ih ht _ _
      · exact ih ht _ _
    · split
      · simpa [lcmdDirect, linstrRDirect, hop] using ih ht _ _
      · exact ih ht _ _

theorem loopBodyCallLcmd_direct (dst sym : String) (argOps : List LOperand)
    (h : ∀ o ∈ argOps, isIndexed o = false) :
    lcmdDirect (loopBodyCallLcmd dst sym argOps) = true := by
  unfold loopBodyCallLcmd
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with ⟨p, hp, rfl⟩ | rfl | rfl
  · exact linstrRDirect_Lopn_mk (by simp) (by
      intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho
      exact h _ (List.of_mem_zip hp).1)
  · rfl
  · exact linstrRDirect_Lopn_mk (by simp) (by simp)

theorem loopBodyCallLcmdClassed_direct (dst : String) (dstIsVec : Bool) (sym : String)
    (argOps : List (LOperand × Bool)) (h : ∀ p ∈ argOps, isIndexed p.1 = false) :
    lcmdDirect (loopBodyCallLcmdClassed dst dstIsVec sym argOps) = true := by
  unfold loopBodyCallLcmdClassed
  simp only [lcmdDirect_append, Bool.and_eq_true]
  refine ⟨marshalClassedArgs_direct argOps h 0 0, ?_⟩
  refine lcmdDirect_of_mem ?_
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · rfl
  · dsimp only
    split <;> exact linstrRDirect_Lopn_mk (by simp) (by simp)

theorem expandCallShadows_lcmdDirect {body : Lcmd} (h : lcmdDirect body = true) :
    lcmdDirect (expandCallShadows body) = true := by
  unfold expandCallShadows
  refine lcmdDirect_flatMap _ _ ?_
  intro i hi
  have h1 := (lcmdDirect_iff body).mp h i hi
  split
  · rename_i heq
    have h2 := h1
    rw [heq] at h2
    obtain ⟨_, hS⟩ := linstrRDirect_Lopn h2
    split
    · exact loopBodyCallLcmdClassed_direct _ _ _ _ (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact hS _ (List.of_mem_zip hq).1)
    · split
      · exact loopBodyCallLcmd_direct _ _ _ hS
      · split
        · exact loopBodyCallLcmd_direct _ _ _ hS
        · simpa [lcmdDirect] using h1
  · simpa [lcmdDirect] using h1

theorem buildPrologue_lcmdDirect (virt : Lfundef) (tbl : Array Nat) (m : InLoadMap) :
    lcmdDirect (buildPrologue virt tbl m) = true := rfl

theorem calleeSaveRestoreEpilogue_lcmdDirect :
    lcmdDirect calleeSaveRestoreEpilogue = true := rfl

theorem buildArgPtrMaterialize_lcmdDirect (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (m : InLoadMap) :
    lcmdDirect (buildArgPtrMaterialize virt tbl abiArgs m) = true := by
  unfold buildArgPtrMaterialize
  refine lcmdDirect_flatMap _ _ ?_
  rintro ⟨abiReg, j⟩ _
  dsimp only
  repeat' split
  all_goals simp [lcmdDirect, linstrRDirect]

theorem insertEpilogue_lcmdDirect {body epi : Lcmd} (hb : lcmdDirect body = true)
    (he : lcmdDirect epi = true) : lcmdDirect (insertEpilogue body epi) = true := by
  rw [insertEpilogue]
  simp only [lcmdDirect_append, Bool.and_eq_true]
  exact ⟨⟨lcmdDirect_dropLast hb, he⟩, rfl⟩

/-- The ABI wrapping around the register-allocated body keeps every memory
    operand direct, on both the general path and the `forwarderBody?` override
    of the wrapped body. -/
theorem physAbiWrap_lcmdDirect (virt : Lfundef) (tbl : Array Nat)
    (shiftImm : ShiftImmOracle) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (extra retMat : Lcmd) (p : Linstr → Bool) (forwarderBody? : Option Lcmd)
    (hforw : ∀ b ∈ forwarderBody?, lcmdDirect b = true)
    (hextra : lcmdDirect extra = true) (hret : lcmdDirect retMat = true)
    (hv : lcmdDirect virt.lfd_body = true) :
    lcmdDirect (forwarderBody?.getD
      (buildPrologue virt tbl inLoadMap ++ extra
        ++ buildArgPtrMaterialize virt tbl abiArgs inLoadMap
        ++ insertEpilogue ((physBodyWithStores shiftImm virt.lfd_body inLoadMap reloadScratch2
              outStoreMap reloadScratch2 abiW memrefBaseReload).filter p)
            (retMat ++ calleeSaveRestoreEpilogue))) = true := by
  cases forwarderBody? with
  | some b => exact hforw b rfl
  | none =>
  simp only [Option.getD_none, lcmdDirect_append, Bool.and_eq_true]
  refine ⟨⟨⟨buildPrologue_lcmdDirect _ _ _, hextra⟩, buildArgPtrMaterialize_lcmdDirect _ _ _ _⟩, ?_⟩
  refine insertEpilogue_lcmdDirect (lcmdDirect_filter ?_) ?_
  · exact physBodyWithStores_lcmdDirect _ _ _ _ _ _ _ _ _ hv
  · simp only [lcmdDirect_append, Bool.and_eq_true]
    exact ⟨hret, calleeSaveRestoreEpilogue_lcmdDirect⟩

/-- **The deployed physical-register export preserves direct addressing.** When
    the virtual body a `Com` lowers to uses no register-indexed (SIB) operand,
    neither does the body of the ABI-wrapped, register-allocated, spill-legalized
    function the export emits. -/
theorem comToLfundefPhysAbi_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiArgs : List String)
    (abiTyin : List Nat) (residence : Option (Array Nat)) (abiW : Nat)
    (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true) :
    lcmdDirect (comToLfundefPhysAbi com shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lfd_body = true := by
  unfold comToLfundefPhysAbi
  refine physAbiWrap_lcmdDirect _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · rintro b hb
    rw [Option.mem_def, Option.map_eq_some_iff] at hb
    obtain ⟨sym, -, rfl⟩ := hb
    rfl
  · refine lcmdDirect_of_mem ?_
    intro z hz
    rw [List.mem_filterMap] at hz
    obtain ⟨a, _, ha⟩ := hz
    split at ha <;> simp only [Option.some.injEq, reduceCtorEq] at ha
    subst_vars
    simp [linstrRDirect]
  · repeat' split
    all_goals first
      | rfl
      | (simp only []; split <;> rfl)
  · simp only [lcmdDirect_append, Bool.and_eq_true]
    refine ⟨?_, canonicalizeMemrefThread_lcmdDirect ?_⟩
    · refine lcmdDirect_of_mem ?_
      intro z hz
      have key : ∀ (n : Nat) (c : Bool), z ∈ (if c = true then
          [(⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
              ((List.range n).map (fun j => .reg (argName j)))⟩ : Linstr)] else []) →
          linstrRDirect z.li_i = true := by
        intro n c hc
        split at hc
        · rw [List.mem_singleton] at hc
          subst hc
          refine linstrRDirect_Lopn_mk (by simp) ?_
          intro o ho
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp ho
          rfl
        · simp at hc
      split at hz
      · exact key _ _ hz
      · exact key _ _ hz
    · split
      · exact expandCallShadows_lcmdDirect h
      · exact residenceRenameBody_lcmdDirect _ _
          (materializeShiftCountImms_lcmdDirect (expandCallShadows_lcmdDirect h))

/-- **The shipped `Lprog` export preserves direct addressing.** The one function
    of `Com.toLprogPhysAbi com fname …` has a body free of register-indexed (SIB)
    operands whenever the `Com`'s virtual body is. -/
theorem toLprogPhysAbi_lcmdDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true) :
    ∀ f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs,
      lcmdDirect f.2.lfd_body = true := by
  intro f hf
  simp only [Com.toLprogPhysAbi, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  exact comToLfundefPhysAbi_lcmdDirect com shiftImm immSlotMap inLoadMap outStoreMap
    abiArgs abiTyin residence abiW forceLivePin h

/-- **The exported function's `JInstr` gather is in the machine constant-time
    class.** Composing the export's preservation of direct addressing with the
    gather bridge: every instruction of the gathered block uses base +
    compile-time-constant displacement addressing, so
    `ConstantTimeCoverage.allDirect_constant_time` applies to it. -/
theorem toLprogPhysAbi_gather_allDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) :
    allDirect g = true :=
  gatherJBlock6_allDirect
    (toLprogPhysAbi_lcmdDirect com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin h f hf) hg

/-- **The exported function's gathered block is constant-time.** Its machine
    leakage trace is the same from any two initial states. -/
theorem toLprogPhysAbi_gather_constant_time {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (h : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (s₁ s₂ : Jasmin.JState 64) :
    MachineConstantTime.blockLeak s₁ g = MachineConstantTime.blockLeak s₂ g :=
  ConstantTimeCoverage.allDirect_constant_time g
    (toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin h hf hg) s₁ s₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation
