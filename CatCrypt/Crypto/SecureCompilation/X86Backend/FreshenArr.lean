/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfgLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsLeak
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfgTactic

@[expose] public section

set_option autoImplicit false

/-!
# Fresh array roots before coalescing

The coalescing renaming `ImageStraightRoute.chainAliasO` sends the destination of a store to
the root of its base, and the destination of a call of an out symbol to the root of its
operand at the destination position. `ImageCoalesceCfg.coArrStepB` and `ImageCoalesceCfg.callB`
refuse such an instruction when a name live after it other than its destination shares that
root. The pass `freshenArr` places, before each such instruction (a site), a copy of the
array into a fresh array and replaces the array operand by the copy, so that the chain of the
destination starts at the fresh root.

The array copy `resCopyCode src D m` writes the `m` words of `src`, one index at a time,
into the versions `copyName D 1, …, copyName D m` of the array `D`, with the index register
`copyIdx` and the scratch register `copyTmp`.

## Main definitions

* `copyName`, `copyIdx`, `copyTmp`, `resCopyStep`, `resCopyCode`, `resCopyLeak`: the array
  copy and its events.
* `freshName`, `FreshFam`, `KeptF`: the fresh roots, their versions, and the names the pass
  keeps.
* `freshSite`, `retarget`, `freshE`, `freshenArr`: the sites, the replacement of the array
  operand, the expansion of one instruction and the pass.
* `primarySite`: the primary sites, whose array is itself live after the instruction, with
  an arm for the constant-index store `STOREIMM`.
* `SiteRule`, `SiteShape`, `SiteOK`, `freshESel`, `freshenSel`: the pass at a site rule;
  `freshenArr` is `freshenSel freshSite`.
* `FrRel`, `freshRootsSel`, `freshRoots`: the relation of a source base and a freshened base.

## Main results

* `steps_resCopy`, `stepsLeak_resCopy`, `stepsLeak_resCopy_eq`: the copy on the x86 flag
  machine, its events `resCopyLeak` (address events at the constant offsets `8 * j`), equal
  from any two states.
* `runStraightF_resCopy`: the copy on the straight-line fold.
* `lsemFuelMemF_expI_callsPre`: halting runs under an index-dependent expansion whose calls
  are preceded by straight-line code, at an instruction set with local calls.
* `lsemFuelMemF_freshenSel`, `lsemFuelMemF_freshenArr`: a halting run of a body is matched
  by a halting run of the freshened body from a related entry state, into a related state.
* `chainAliasO_freshenSel_carried`, `chainAliasO_freshenArr`: the coalescing renaming of the
  freshened body sends the destination of a site to its fresh root, when every later writer
  of the destination keeps that image.
* `freshenSel_eq_self`: a body with no site is its own freshening.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FreshenArr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (lsemFuelMemF LstateMF)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg

/-! ## 1. The array copy -/

/-- The `j`-th version of the result buffer `D` in the result copy: `D` at `0`, and the name
    `D ++ "#c" ++ toString j` after `j` words. -/
def copyName (D : String) (j : Nat) : String :=
  if j = 0 then D else D ++ "#c" ++ toString j

/-- The index register of the result copy. -/
def copyIdx : String := "rcopy.i"

/-- The scratch register of the result copy. -/
def copyTmp : String := "rcopy.t"

/-- **One word of the result copy** of the `m`-word array `src` into the result buffer `D`,
    at the index `j`: the move of `j` into the index register `copyIdx`, the load of the
    word of `src` at that index into the scratch register `copyTmp`, and the store of that
    word at the same index of the version `copyName D j`, which writes the version
    `copyName D (j + 1)`. -/
def resCopyStep (src D : String) (m j : Nat) : List LinstrRM :=
  [ movImmI copyIdx j
  , (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
  , (.Lopn [.reg (copyName D (j + 1))] "STOREIDX"
      [.arrIdx (copyName D j) copyIdx 8, .reg copyTmp], .store 64 m) ]

/-- **The result copy** of the `m`-word array `src` into the result buffer `D`: the words at
    the indices `0, …, m - 1` in order (`resCopyStep`). After it the version
    `copyName D m` holds the array of `src`. -/
def resCopyCode (src D : String) (m : Nat) : List LinstrRM :=
  (List.range m).flatMap (resCopyStep src D m)

/-- At an index below the length `m < 2 ^ 64`, `stackGet` at the index read back from its
    `64`-bit word is the entry of the array. -/
theorem stackGet_ofNat_lt {m : Nat} (a : Fin m → BitVec 64) {j : Nat} (hj : j < m)
    (hm : m < 2 ^ 64) : stackGet a (BitVec.ofNat 64 j).toNat = a ⟨j, hj⟩ := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  match m, a, hj with
  | k + 1, a, hj => show a ⟨j % (k + 1), _⟩ = _; simp [Nat.mod_eq_of_lt hj]

/-- At an index below the length `m < 2 ^ 64`, `stackSet` at the index read back from its
    `64`-bit word writes the entry at that index and keeps every other entry. -/
theorem stackSet_ofNat_apply {m : Nat} (a : Fin m → BitVec 64) {j : Nat} (hj : j < m)
    (hm : m < 2 ^ 64) (v : BitVec 64) (i : Fin m) :
    stackSet a (BitVec.ofNat 64 j).toNat v i = if i.val = j then v else a i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  match m, a, hj, i with
  | k + 1, a, hj, i =>
      show (if i = ⟨j % (k + 1), _⟩ then v else a i) = _
      simp [Nat.mod_eq_of_lt hj, Fin.ext_iff]

/-- The events of the first `k` words of the result copy of `src` into `D`: at each index
    `j < k`, the address event of the load of `src` and of the store into `copyName D j`,
    both at the offset `8 * j`. -/
def resCopyLeak (src D : String) (k : Nat) : List CT.CTLeak :=
  (List.range k).flatMap fun j =>
    [.addr src (Int.ofNat (8 * j)), .addr (copyName D j) (Int.ofNat (8 * j))]

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak (instrLeakF_of_lopn instrLeakB
  opLeakF idxVal) in
/-- **The first `k` words of the result copy.** Let the body of `P` hold the first `k ≤ m`
    words of the result copy of `src` into `D` behind `pre`, the state `s` be at the end of
    `pre`, `src` hold the array `arr` and `D` an array, both of `m < 2 ^ 64` words, and no
    version `copyName D (j + 1)`, `j < m`, be `src`. Then `3 * k` steps with the events
    `resCopyLeak src D k` lead to a state at the end of those words in which `src` still
    holds `arr` and the version `copyName D k` holds an array whose entries below `k` are
    those of `arr`. -/
theorem steps_resCopy_aux {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre : List LinstrRM) (s : LstateMF) (hat : atPc P pre.length s)
    {arr : Fin m → BitVec 64} (hsrc : s.prog.base.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.prog.base.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∀ k, k ≤ m → ∀ post : List LinstrRM,
      P.body = pre ++ (List.range k).flatMap (resCopyStep src D m) ++ post →
      ∃ u, StepsL P (3 * k) s u (resCopyLeak src D k) ∧ atPc P (pre.length + 3 * k) u
        ∧ u.prog.base.getArr src 64 m = some arr
        ∧ ∃ b : Fin m → BitVec 64, u.prog.base.getArr (copyName D k) 64 m = some b
          ∧ ∀ i (hi : i < m), i < k → b ⟨i, hi⟩ = arr ⟨i, hi⟩ := by
  intro k
  induction k with
  | zero =>
      intro _ _ _
      exact ⟨s, ⟨Steps.refl x86Isa P s, rfl⟩, hat, hsrc, a0, by simpa [copyName] using hD,
        fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ k ih =>
      intro hk post hbody
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton] at hbody
      obtain ⟨u, hs, hatu, hsu, b, hb, hbv⟩ := ih (by omega) (resCopyStep src D m k ++ post)
        (by rw [hbody]; simp only [List.append_assoc])
      have hpos : (pre ++ (List.range k).flatMap (resCopyStep src D m)).length
          = pre.length + 3 * k := by
        simp [List.length_flatMap, resCopyStep]; omega
      have hb' : P.body = (pre ++ (List.range k).flatMap (resCopyStep src D m)) ++
          resCopyStep src D m k ++ post := by rw [hbody]; simp only [List.append_assoc]
      generalize pre ++ (List.range k).flatMap (resCopyStep src D m) = X at hpos hb'
      rw [← hpos] at hatu
      have hk' : k < m := by omega
      have hk64 : k < 2 ^ 64 := by omega
      generalize hL : ((.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 m)
        : LinstrRM) = L at hb'
      generalize hS : ((.Lopn [.reg (copyName D (k + 1))] "STOREIDX"
        [.arrIdx (copyName D k) copyIdx 8, .reg copyTmp], .store 64 m) : LinstrRM) = S at hb'
      have hb1 : P.body = X ++ movImmI copyIdx k :: L :: S :: post := by
        rw [hb', ← hL, ← hS]; simp [resCopyStep]
      have hb2 : P.body = (X ++ [movImmI copyIdx k]) ++ L :: S :: post := by
        rw [hb1]; simp
      have hb3 : P.body = (X ++ [movImmI copyIdx k, L]) ++ S :: post := by
        rw [hb1]; simp
      -- The move of the index.
      obtain ⟨u1, hs1, hat1, hl1, hr1⟩ := steps_movImm (dst := copyIdx) (c := k) hatu
        (fetch_of_body hb1 rfl)
      have hsL1 := stepsL_one hatu (fetch_of_body hb1 rfl) hs1
      rw [instrLeakF_of_lopn ⟨_, _, _, rfl⟩] at hsL1
      have hsrc1 : u1.prog.base.getArr src 64 m = some arr := by
        unfold LstateM.getArr; rw [hl1]; exact hsu
      have hb1' : u1.prog.base.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl1]; exact hb
      have hzl1 : u1.prog.base.reg.lvm copyIdx = ⟨64, BitVec.ofNat 64 k⟩ := by
        rw [hr1, ite_eq_left rfl]
      have hz1 : u1.prog.base.reg.getW copyIdx 64 = some (BitVec.ofNat 64 k) :=
        getW_of_lvm _ _ _ hzl1
      -- The load of the word.
      have h2 := JasminLsemMemSourceTieUncond.lsemStepMem_loadIdx copyTmp src copyIdx 8 arr _
        u1.prog.base hsrc1 hz1
      have hlk2 : instrLeakB u1.prog.base.reg L = [.addr src (Int.ofNat (8 * k))] := by
        rw [← hL]; simp [instrLeakB, opLeakF, idxVal]; rw [hzl1]; simpa using hk64
      rw [hL] at h2
      obtain ⟨hs2, hat2⟩ := x86_steps_mem hat1 (fetch_of_body hb2 (by simp))
        (by rw [← hL]; exact ⟨_, _, _, rfl⟩) (by rw [← hL]; rfl) (by rw [← hL]; rfl) h2
      have hsL2 := stepsL_one hat1 (fetch_of_body hb2 (by simp)) hs2
      rw [instrLeakF_of_lopn (by rw [← hL]; exact ⟨_, _, _, rfl⟩), hlk2] at hsL2
      generalize hu2 : setBase u1 (JasminLsemMemFlagGuard.withALUFlags L u1.prog.base _)
        = u2 at hs2 hat2 hsL2
      have hl2 : u2.prog.base.larr = u1.prog.base.larr := by
        rw [← hu2, setBase_base, JasminLsemMemFlagGuard.withALUFlags_larr]; rfl
      have hr2 : ∀ r, u2.prog.base.reg.lvm r = if r = copyTmp
          then ⟨64, stackGet arr (BitVec.ofNat 64 k).toNat⟩ else u1.prog.base.reg.lvm r := by
        intro r
        rw [← hu2, setBase_base, JasminLsemMemFlagGuard.withALUFlags_reg]
        simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg]
      have hb2' : u2.prog.base.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl2]; exact hb1'
      have hzl2 : u2.prog.base.reg.lvm copyIdx = ⟨64, BitVec.ofNat 64 k⟩ := by
        rw [hr2, ite_eq_right (by decide), hzl1]
      have hz2 : u2.prog.base.reg.getW copyIdx 64 = some (BitVec.ofNat 64 k) :=
        getW_of_lvm _ _ _ hzl2
      have hv2 : u2.prog.base.reg.getW copyTmp 64
          = some (stackGet arr (BitVec.ofNat 64 k).toNat) := by
        apply getW_of_lvm; rw [hr2, ite_eq_left rfl]
      -- The store of the word.
      have h3 := JasminLsemMemSourceTieUncond.lsemStepMem_storeIdx (copyName D (k + 1))
        (copyName D k) copyIdx copyTmp 8 b _ _ u2.prog.base hb2' hz2 hv2
      have hlk3 : instrLeakB u2.prog.base.reg S
          = [.addr (copyName D k) (Int.ofNat (8 * k))] := by
        rw [← hS]; simp [instrLeakB, opLeakF, idxVal]; rw [hzl2]; simpa using hk64
      rw [hS] at h3
      obtain ⟨hs3, hat3⟩ := x86_steps_mem hat2 (fetch_of_body hb3 (by simp))
        (by rw [← hS]; exact ⟨_, _, _, rfl⟩)
        (by rw [← hS]; unfold JasminLsemMemFlagGuard.cmpArgs?; exact ite_eq_right (by decide))
        (by rw [← hS]; rfl) h3
      have hsL3 := stepsL_one hat2 (fetch_of_body hb3 (by simp)) hs3
      rw [instrLeakF_of_lopn (by rw [← hS]; exact ⟨_, _, _, rfl⟩), hlk3] at hsL3
      generalize hnb : stackSet b (BitVec.ofNat 64 k).toNat
        (stackGet arr (BitVec.ofNat 64 k).toNat) = nb at hs3 hat3 hsL3
      generalize hu3 : setBase u2 (JasminLsemMemFlagGuard.withALUFlags S u2.prog.base _)
        = u3 at hs3 hat3 hsL3
      have hl3 : u3.prog.base.larr = (u2.prog.base.setArr (copyName D (k + 1)) nb).larr := by
        rw [← hu3, setBase_base, JasminLsemMemFlagGuard.withALUFlags_larr]; rfl
      have hmv : instrLeakB u.prog.base.reg (movImmI copyIdx k) = [] := by
        simp [instrLeakB, movImmI, ExportRegions.movI, opLeakF]
      rw [hmv] at hsL1
      refine ⟨u3, ?_, ?_, ?_, nb, ?_, fun i hi hik => ?_⟩
      · have := hs.trans (hsL1.trans (hsL2.trans hsL3))
        rw [show 3 * k + (1 + (1 + 1)) = 3 * (k + 1) by omega] at this
        refine this.cast ?_
        simp [resCopyLeak, List.range_succ, List.flatMap_append]
      · rw [hpos] at hat3
        rwa [show pre.length + 3 * k + 1 + 1 + 1 = pre.length + 3 * (k + 1) by omega] at hat3
      · rw [getArr_of_larr_eq (s' := u2.prog.base.setArr (copyName D (k + 1)) nb) (r' := src)
          64 m (by rw [hl3]), LstateM.getArr_setArr_other _ _ _ _ _ _ (hfr k hk')]
        unfold LstateM.getArr; rw [hl2, hl1]; exact hsu
      · rw [getArr_of_larr_eq (s' := u2.prog.base.setArr (copyName D (k + 1)) nb)
          (r' := copyName D (k + 1)) 64 m (by rw [hl3]), LstateM.getArr_setArr_same]
      · rw [← hnb, stackSet_ofNat_apply b hk' hm, stackGet_ofNat_lt arr hk' hm]
        by_cases h : i = k
        · subst h; simp
        · simp only [h, ite_false]; exact hbv i hi (by omega)

/-- **The result copy** of the `m`-word array `src` into `D`, behind `pre` in the body of
    `P`, from a state at the end of `pre` in which `src` holds `arr` and `D` an array of `m`
    words, with `m < 2 ^ 64` and no version `copyName D (j + 1)`, `j < m`, equal to `src`:
    `3 * m` steps with the events `resCopyLeak src D m` lead to a state at the end of the
    copy in which `copyName D m` holds `arr`. -/
theorem steps_resCopy {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ resCopyCode src D m ++ post) (hat : atPc P pre.length s)
    {arr : Fin m → BitVec 64} (hsrc : s.prog.base.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.prog.base.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∃ u, StepsL P (3 * m) s u (resCopyLeak src D m) ∧ atPc P (pre.length + 3 * m) u
      ∧ u.prog.base.getArr (copyName D m) 64 m = some arr := by
  obtain ⟨u, hs, hat', -, b, hb, hbv⟩ :=
    steps_resCopy_aux hm pre s hat hsrc hD hfr m le_rfl post hbody
  refine ⟨u, hs, hat', ?_⟩
  rw [hb]
  congr 1
  funext i
  exact hbv i.1 i.2 i.2

/-- **The events of the array copy.** Under the hypotheses of `steps_resCopy`, the `3 * m`
    steps of the copy emit `resCopyLeak src D m`: the load of `src` and the store into
    `copyName D j` at the constant offset `8 * j` for each `j < m`, whatever the arrays. -/
theorem stepsLeak_resCopy {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre post : List LinstrRM) (s : LstateMF)
    (hbody : P.body = pre ++ resCopyCode src D m ++ post) (hat : atPc P pre.length s)
    {arr : Fin m → BitVec 64} (hsrc : s.prog.base.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.prog.base.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    stepsLeak P (3 * m) s = resCopyLeak src D m := by
  obtain ⟨u, hs, -, -⟩ := steps_resCopy hm pre post s hbody hat hsrc hD hfr
  exact hs.2

/-- **The array copy is constant time.** Two runs of the copy from states that satisfy the
    hypotheses of `steps_resCopy`, with any arrays, emit the same events. -/
theorem stepsLeak_resCopy_eq {P : JasminLsemMemLoop.LprogM} {src D : String} {m : Nat}
    (hm : m < 2 ^ 64) (pre post : List LinstrRM) (s₁ s₂ : LstateMF)
    (hbody : P.body = pre ++ resCopyCode src D m ++ post) (hat₁ : atPc P pre.length s₁)
    (hat₂ : atPc P pre.length s₂) {arr₁ arr₂ a₁ a₂ : Fin m → BitVec 64}
    (hsrc₁ : s₁.prog.base.getArr src 64 m = some arr₁)
    (hsrc₂ : s₂.prog.base.getArr src 64 m = some arr₂)
    (hD₁ : s₁.prog.base.getArr D 64 m = some a₁) (hD₂ : s₂.prog.base.getArr D 64 m = some a₂)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    stepsLeak P (3 * m) s₁ = stepsLeak P (3 * m) s₂ := by
  rw [stepsLeak_resCopy hm pre post s₁ hbody hat₁ hsrc₁ hD₁ hfr,
    stepsLeak_resCopy hm pre post s₂ hbody hat₂ hsrc₂ hD₂ hfr]

/-! ## 2. The array copy on the straight-line fold -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (fstepF runStraightF
  runStraightF_cons runStraightF_nil)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (cmpArgs? movRegArgs?
  stepMemF aluFlagOp? carryArgs? wideArgs? stepMemF_of_quiet)

/-- The step of an indexed load is the memory step, with the zero flag kept. -/
theorem fstepF_loadIdx (d b x : String) (sc w n : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "LOADIDX" [.arrIdx b x sc], .load w n) s zf
      = (lsemStepMem (.Lopn [.reg d] "LOADIDX" [.arrIdx b x sc], .load w n) s).map (·, zf) := by
  simp only [fstepF, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]

/-- The step of an indexed store is the memory step, with the zero flag kept. -/
theorem fstepF_storeIdx (d b x v : String) (sc w n : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v], .store w n) s zf
      = (lsemStepMem (.Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v], .store w n) s).map
          (·, zf) := by
  simp [fstepF, cmpArgs?, movRegArgs?, withWidthTag, stepMemF_of_quiet, aluFlagOp?,
    carryArgs?, wideArgs?]

/-- The step of a constant-index store is the memory step, with the zero flag kept. -/
theorem fstepF_storeImm (d b v : String) (c w n : Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm c], .storeImm w n) s zf
      = (lsemStepMem (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm c], .storeImm w n) s).map
          (·, zf) := by
  simp only [fstepF, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]

/-- The step of the move of an immediate writes its word at width `64`. -/
theorem fstepF_movImmI (d : String) (c : Nat) (s : LstateM) (zf : Bool) :
    fstepF (movImmI d c) s zf = some ((s.setReg d (BitVec.ofNat 64 c)).nextPc, zf) :=
  X86Backend.DecodedLsemStep.fstepF_movII d c s zf

/-- **The first `k` words of the array copy on the straight-line fold.** From a state in
    which `src` holds `arr` and `D` an array, both of `m < 2 ^ 64` words, with no version
    `copyName D (j + 1)`, `j < m`, equal to `src`, the fold over the first `k ≤ m` words of
    the copy keeps the zero flag and ends in a state in which `src` still holds `arr`, the
    version `copyName D k` holds an array whose entries below `k` are those of `arr`, every
    register other than `copyIdx` and `copyTmp` is unchanged, every array other than the
    versions `copyName D (j + 1)`, `j < k`, is unchanged, and the word memory and the carry
    and overflow flags are unchanged. -/
theorem runStraightF_resCopy_aux {src D : String} {m : Nat} (hm : m < 2 ^ 64) (s : LstateM)
    (zf : Bool) {arr : Fin m → BitVec 64} (hsrc : s.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∀ k, k ≤ m → ∃ u, runStraightF ((List.range k).flatMap (resCopyStep src D m)) s zf
        = some (u, zf)
      ∧ u.getArr src 64 m = some arr
      ∧ (∃ b : Fin m → BitVec 64, u.getArr (copyName D k) 64 m = some b
          ∧ ∀ i (hi : i < m), i < k → b ⟨i, hi⟩ = arr ⟨i, hi⟩)
      ∧ (∀ r, r ≠ copyIdx → r ≠ copyTmp → u.reg.lvm r = s.reg.lvm r)
      ∧ (∀ r, (∀ j, j < k → r ≠ copyName D (j + 1)) → u.larr r = s.larr r)
      ∧ u.lmem = s.lmem ∧ u.cf = s.cf ∧ u.of = s.of := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨s, rfl, hsrc, ⟨a0, by simp [copyName, hD],
        fun _ _ h => absurd h (Nat.not_lt_zero _)⟩, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl,
        rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨u, hu, hsu, ⟨b, hb, hbv⟩, hreg, harr, hmem, hcf, hof⟩ := ih (by omega)
      have hk' : k < m := by omega
      -- The move of the index.
      have hz1 : ((u.setReg copyIdx (BitVec.ofNat 64 k)).nextPc).reg.getW copyIdx 64
          = some (BitVec.ofNat 64 k) := getW_of_lvm _ _ _ (by
        simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg,
          ite_true])
      generalize hu1 : (u.setReg copyIdx (BitVec.ofNat 64 k)).nextPc = u1 at hz1
      have hl1 : u1.larr = u.larr := by rw [← hu1]; rfl
      have hsrc1 : u1.getArr src 64 m = some arr := by unfold LstateM.getArr; rw [hl1]; exact hsu
      have hb1 : u1.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl1]; exact hb
      -- The load of the word.
      have h2 := JasminLsemMemSourceTieUncond.lsemStepMem_loadIdx copyTmp src copyIdx 8 arr _
        u1 hsrc1 hz1
      generalize hv : stackGet arr (BitVec.ofNat 64 k).toNat = v at h2
      generalize hu2 : (u1.setReg copyTmp v).nextPc = u2 at h2
      have hl2 : u2.larr = u1.larr := by rw [← hu2]; rfl
      have hz2 : u2.reg.getW copyIdx 64 = some (BitVec.ofNat 64 k) := by
        rw [← hu2]
        simp only [LstateM.nextPc, LstateM.setReg]
        unfold LstateN.getW at hz1 ⊢
        simp only [LstateN.lvm_nextPc, LstateN.lvm_setReg, ite_eq_right (show copyIdx ≠ copyTmp by
          decide)]
        exact hz1
      have hv2 : u2.reg.getW copyTmp 64 = some v := getW_of_lvm _ _ _ (by
        rw [← hu2]
        simp only [LstateM.nextPc, LstateM.setReg, LstateN.lvm_nextPc, LstateN.lvm_setReg,
          ite_true])
      have hb2 : u2.getArr (copyName D k) 64 m = some b := by
        unfold LstateM.getArr; rw [hl2]; exact hb1
      -- The store of the word.
      have h3 := JasminLsemMemSourceTieUncond.lsemStepMem_storeIdx (copyName D (k + 1))
        (copyName D k) copyIdx copyTmp 8 b _ _ u2 hb2 hz2 hv2
      generalize hnb : stackSet b (BitVec.ofNat 64 k).toNat v = nb at h3
      refine ⟨(u2.setArr (copyName D (k + 1)) nb).nextPc, ?_, ?_, ⟨nb, ?_, ?_⟩, ?_, ?_, ?_, ?_,
        ?_⟩
      · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
          JasminLsemAddrMem.runStraightF_append, hu, Option.bind_some]
        simp only [resCopyStep, runStraightF_cons, fstepF_movImmI, Option.bind_some, hu1]
        rw [fstepF_loadIdx, h2, Option.map_some, Option.bind_some, fstepF_storeIdx, h3,
          Option.map_some, Option.bind_some, runStraightF_nil]
      · rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_other _ _ _ _ _ _ (hfr k hk')]
        unfold LstateM.getArr; rw [hl2, hl1]; exact hsu
      · rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_same]
      · intro i hi hik
        rw [← hnb, ← hv, stackSet_ofNat_apply b hk' hm, stackGet_ofNat_lt arr hk' hm]
        by_cases h : i = k
        · subst h; simp
        · simp only [h, ite_false]; exact hbv i hi (by omega)
      · intro r h1 h2'
        rw [← hreg r h1 h2', ← hu2, ← hu1]
        simp only [LstateM.nextPc, LstateM.setArr, LstateM.setReg, LstateN.lvm_nextPc,
          LstateN.lvm_setReg, ite_eq_right h1, ite_eq_right h2']
      · intro r hr
        rw [← harr r (fun j hj => hr j (by omega))]
        simp only [LstateM.larr_nextPc, LstateM.larr_setArr,
          ite_eq_right (hr k (Nat.lt_succ_self k)), hl2, hl1]
      · rw [← hmem, ← hu2, ← hu1]; rfl
      · rw [← hcf, ← hu2, ← hu1]; rfl
      · rw [← hof, ← hu2, ← hu1]; rfl

/-- **The array copy on the straight-line fold.** From a state in which `src` holds `arr`
    and `D` an array, both of `m < 2 ^ 64` words, with no version `copyName D (j + 1)`,
    `j < m`, equal to `src`, the fold over `resCopyCode src D m` keeps the zero flag and ends
    in a state in which `copyName D m` holds `arr`, every register other than `copyIdx` and
    `copyTmp` is unchanged, every array other than the versions `copyName D (j + 1)`,
    `j < m`, is unchanged, and the word memory and the carry and overflow flags are
    unchanged. -/
theorem runStraightF_resCopy {src D : String} {m : Nat} (hm : m < 2 ^ 64) (s : LstateM)
    (zf : Bool) {arr : Fin m → BitVec 64} (hsrc : s.getArr src 64 m = some arr)
    {a0 : Fin m → BitVec 64} (hD : s.getArr D 64 m = some a0)
    (hfr : ∀ j, j < m → src ≠ copyName D (j + 1)) :
    ∃ u, runStraightF (resCopyCode src D m) s zf = some (u, zf)
      ∧ u.getArr (copyName D m) 64 m = some arr
      ∧ (∀ r, r ≠ copyIdx → r ≠ copyTmp → u.reg.lvm r = s.reg.lvm r)
      ∧ (∀ r, (∀ j, j < m → r ≠ copyName D (j + 1)) → u.larr r = s.larr r)
      ∧ u.lmem = s.lmem ∧ u.cf = s.cf ∧ u.of = s.of := by
  obtain ⟨u, hu, -, ⟨b, hb, hbv⟩, hreg, harr, hmem, hcf, hof⟩ :=
    runStraightF_resCopy_aux hm s zf hsrc hD hfr m le_rfl
  refine ⟨u, hu, ?_, hreg, harr, hmem, hcf, hof⟩
  rw [hb]
  congr 1
  funext i
  exact hbv i.1 i.2 i.2

/-! ## 3. Expansions whose calls are preceded by straight-line code -/

section CallPre

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (expI pcI ExpInv RelI
  evalInstrPMemF_expI getElem?_expI_pcI pcI_succ getElem?_expI_pcI_none)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow shadowCall? retRes
  argsRead lpc_retRes lfn_retRes CallRes)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM findInstrMem
  IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (lsemFuelMemF_segF_agree
  runStraightF_lpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (evalInstrPMemF
  findInstrMem_singleton)

variable {Q : LstateM → LstateM → Prop} {G : LstateM → Prop}
  {Inv : Nat → LstateM → Bool → Prop} {e : Nat → LinstrRM → List LinstrRM}

/-- **One step of a shadow instruction of a call expanded behind straight-line code.** At an
    instruction set `I` whose steps beyond `x86Isa` are local calls at the array positions
    `aa`, a step of the call `callShadow dst f srcs` at instruction `i`, whose expansion is a
    straight segment `pre` followed by a call of `f` on the operands `srcs'`, is matched by
    the segment and the call from a related state: the segment runs on the flag fold to a base
    `b` at which the operands `srcs'` have the argument words of `srcs` at the source state,
    and the relation and the invariant are kept by the write of the result. -/
theorem step_expI_callPre {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {s s' u : LstateMF} {i : LinstrRM}
    (hR : RelI Q Inv e body s s') (hfn : s.prog.lfn = fn)
    (hget : body[s.prog.base.lpc]? = some i) (hsh : shadowCall? i.1 ≠ none)
    (hpre : ∀ (dst f : String) (srcs : List LOperand) (x : CallRes),
      i.1 = callShadow dst f srcs →
      I.step (singletonProgM fn body) i s = some (retRes dst x s) →
      ∃ (pre : List LinstrRM) (srcs' : List LOperand) (b : LstateM),
        e s.prog.base.lpc i = pre ++ [(callShadow dst f srcs', i.2)]
        ∧ (∀ j ∈ pre, IsLopn j)
        ∧ (∀ j ∈ pre, ∀ (P : LprogM) (y : LstateMF), I.step P j y = x86Isa.step P j y)
        ∧ srcs'.length = srcs.length
        ∧ runStraightF pre s'.prog.base s'.zf = some (b, s'.zf)
        ∧ argsRead (aa f) b 0 srcs' = argsRead (aa f) s.prog.base 0 srcs
        ∧ Inv (s.prog.base.lpc + 1) (retRes dst x s).prog.base s.zf
        ∧ Q (retRes dst x s).prog.base
            (retRes dst x { prog := { base := b, lfn := s'.prog.lfn }, zf := s'.zf }).prog.base)
    (he : I.step (singletonProgM fn body) i s = some u) :
    ∃ u', (∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0))
        ((e s.prog.base.lpc i).length + f) s'
          = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u')
      ∧ RelI Q Inv e body u u' := by
  rcases hcl _ i s u he with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, -⟩
  · have hx' : evalInstrPMemF (singletonProgM fn body) i s = some u := hx
    rw [evalInstrPMemF_shadowCall _ i s hsh] at hx'
    cases hx'
  · obtain ⟨pre, srcs', b, he', hlop, hag, hlen, hrun, hargs, hinv, hQ⟩ :=
      hpre dst f srcs x hi he
    have hfn' : s'.prog.lfn = fn := hR.lfn.trans hfn
    have hpos : ∀ j, j < (e s.prog.base.lpc i).length →
        (expI e body 0)[s'.prog.base.lpc + j]? = (e s.prog.base.lpc i)[j]? := by
      intro j hj
      rw [hR.pc]
      exact getElem?_expI_pcI e hget hj
    have hlenE : (e s.prog.base.lpc i).length = pre.length + 1 := by rw [he']; simp
    have hseg := fun f' => lsemFuelMemF_segF_agree (I := I) (singletonProgM fn (expI e body 0))
      s'.prog.lfn hfn' pre s'.prog.base s'.zf (f' + 1) hlop hag (fun j hj => by
        show (expI e body 0)[s'.prog.base.lpc + j]? = _
        rw [hpos j (by omega), he', List.getElem?_append_left hj])
    simp only [hrun, Option.bind_some] at hseg
    have hblpc : b.lpc = s'.prog.base.lpc + pre.length :=
      runStraightF_lpc pre _ _ _ _ hrun
    let sb : LstateMF := { prog := { base := b, lfn := s'.prog.lfn }, zf := s'.zf }
    have hfetch : findInstrMem (singletonProgM fn (expI e body 0)) sb.prog
        = some (callShadow dst f srcs', i.2) := by
      rw [findInstrMem_singleton fn _ sb.prog hfn']
      show (expI e body 0)[b.lpc]? = _
      rw [hblpc, hpos pre.length (by omega), he', List.getElem?_append_right (le_refl _),
        Nat.sub_self]
      rfl
    have hstep : I.step (singletonProgM fn (expI e body 0)) (callShadow dst f srcs', i.2) sb
        = some (retRes dst x sb) :=
      hfwd _ i.2 dst srcs' sb hlen hargs
    have hz : ∀ y : LstateMF, (retRes dst x y).zf = y.zf := fun y => by cases x <;> rfl
    refine ⟨retRes dst x sb, fun f' => ?_, ⟨by rw [lfn_retRes, lfn_retRes]; exact hR.lfn,
      by rw [hz, hz]; exact hR.zf, ?_, hQ, ?_⟩⟩
    · rw [hlenE, Nat.add_assoc, Nat.add_comm 1 f']
      exact (hseg f').trans (I.lsemFuelMemF_step _ f' _ sb _ hfetch hstep)
    · rw [lpc_retRes, lpc_retRes, pcI_succ e hget, ← hR.pc, hlenE]
      show b.lpc + 1 = _
      rw [hblpc, Nat.add_assoc]
    · rw [lpc_retRes, hz]
      exact hinv

/-- **An index-dependent expansion with an invariant, whose calls are preceded by
    straight-line code, at an instruction set with local calls.** The statement of
    `JasminLsemFuseMulHi.lsemFuelMemF_expI_calls` for an expansion that sends a shadow
    instruction of a call to a straight segment followed by a call of the same symbol on
    operands with the same argument words after the segment. -/
theorem lsemFuelMemF_expI_callsPre {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body)
    (hag : ∀ k i, body[k]? = some i → shadowCall? i.1 = none →
      ∀ j ∈ e k i, ∀ (P : LprogM) (x : LstateMF), I.step P j x = x86Isa.step P j x)
    (hcall : ∀ k i, body[k]? = some i → shadowCall? i.1 ≠ none →
      ∀ (s s' : LstateMF) (dst f : String) (srcs : List LOperand) (x : CallRes),
        i.1 = callShadow dst f srcs → s.prog.base.lpc = k → s.prog.lfn = fn →
        Inv k s.prog.base s.zf → Q s.prog.base s'.prog.base →
        I.step (singletonProgM fn body) i s = some (retRes dst x s) →
        ∃ (pre : List LinstrRM) (srcs' : List LOperand) (b : LstateM),
          e k i = pre ++ [(callShadow dst f srcs', i.2)]
          ∧ (∀ j ∈ pre, IsLopn j)
          ∧ (∀ j ∈ pre, ∀ (P : LprogM) (y : LstateMF), I.step P j y = x86Isa.step P j y)
          ∧ srcs'.length = srcs.length
          ∧ runStraightF pre s'.prog.base s'.zf = some (b, s'.zf)
          ∧ argsRead (aa f) b 0 srcs' = argsRead (aa f) s.prog.base 0 srcs
          ∧ Inv (k + 1) (retRes dst x s).prog.base s.zf
          ∧ Q (retRes dst x s).prog.base
              (retRes dst x { prog := { base := b, lfn := s'.prog.lfn }, zf := s'.zf }).prog.base)
    {m : Nat} (hm : ∀ k i, body[k]? = some i → (e k i).length ≤ m) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelI Q Inv e body s s' →
      I.lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel * m
        ∧ I.lsemFuelMemF (singletonProgM fn (expI e body 0)) fuel' s' = some t'
        ∧ RelI Q Inv e body t t' := by
  have hhalt : ∀ {s s' : LstateMF}, RelI Q Inv e body s s' →
      findInstrMem (singletonProgM fn body) s.prog = none →
      findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = none := by
    intro s s' hR hf
    unfold findInstrMem at hf ⊢
    rw [hR.lfn]
    split
    · rename_i hfn
      rw [ite_eq_left (show s.prog.lfn = (singletonProgM fn body).lfn from hfn)] at hf
      rw [hR.pc]
      exact getElem?_expI_pcI_none e (body := body) hf
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR hrun
      unfold Isa.lsemFuelMemF at hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          simp only [hf] at hrun
          cases hrun
          exact ⟨0, s', by simp, I.lsemFuelMemF_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i => simp [hf] at hrun
  | succ n ih =>
      intro s s' t hR hrun
      unfold Isa.lsemFuelMemF at hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          simp only [hf] at hrun
          cases hrun
          exact ⟨0, s', by simp, I.lsemFuelMemF_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i =>
          simp only [hf] at hrun
          have hfg : s.prog.lfn = fn ∧ body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact ⟨by assumption, hf⟩
            · simp at hf
          cases he : I.step (singletonProgM fn body) i s with
          | none => simp [he] at hrun
          | some u =>
              simp only [he] at hrun
              have hstep : ∃ u', (∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0))
                  ((e s.prog.base.lpc i).length + f) s'
                    = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u')
                  ∧ RelI Q Inv e body u u' := by
                by_cases hsh : shadowCall? i.1 = none
                · have he' : evalInstrPMemF (singletonProgM fn body) i s = some u := by
                    rw [← he]
                    exact (Isa.CallLocal.step_eq I hle hcl _ hsh s).symm
                  exact evalInstrPMemF_expI h hR hfg.1 hfg.2 (hag _ i hfg.2 hsh) he'
                · exact step_expI_callPre hcl hR hfg.1 hfg.2 hsh
                    (fun dst f srcs x hi hx => hcall _ i hfg.2 hsh s s' dst f srcs x hi rfl
                      hfg.1 hR.inv hR.base hx) he
              obtain ⟨u', hrun1, hRu⟩ := hstep
              obtain ⟨f', t', hf', hrun', hRt⟩ := ih hRu hrun
              have hlen := hm _ i hfg.2
              refine ⟨(e s.prog.base.lpc i).length + f', t', ?_, by rw [hrun1]; exact hrun',
                hRt⟩
              rw [Nat.succ_mul]
              omega

end CallPre

/-! ## 4. The freshening pass -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (callShadow shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (expI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (chainAliasO)

/-- The root of the fresh array of the instruction at position `k`. -/
def freshName (k : Nat) : String := "f#" ++ toString k

/-- A name of the fresh family: a version `copyName (freshName k) j` of a fresh root. -/
def FreshFam (r : String) : Prop := ∃ k j, r = copyName (freshName k) j

/-- A name the pass keeps: neither a register of the array copy nor a name of the fresh
    family. -/
def KeptF (r : String) : Prop := r ≠ copyIdx ∧ r ≠ copyTmp ∧ ¬ FreshFam r

/-- Some name of `after` other than `d` has the image of `d` under `σ`: the condition under
    which `coArrStepB` refuses a store into `d` and `callB` an array call into `d`. -/
def liveShareB (σ : String → String) (after : List String) (d : String) : Bool :=
  after.any fun r => r != d && σ r == σ d

/-- **The site of the instruction `i` at position `k`**, for the coalescing renaming `σ`,
    the liveness certificate `L`, the array positions `aa` and the out symbols `outs` with
    their destination positions: the array to copy and its length, or `none`. A store-tagged
    `STOREIDX` of `64`-bit words into `d` from the base `b` is a site when some name live
    after it other than `d` shares the image of `d` under `σ`; the array is `b`. A shadow
    instruction of a call of an out symbol `f` with the destination position `p`, whose
    operand at `p` is the register `A` of an array of `n` words, is a site under the same
    condition on its destination; the array is `A`. The length is below `2 ^ 64`. -/
def freshSite (σ : String → String) (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (k : Nat) (i : LinstrRM) : Option (String × Nat) :=
  match shadowCall? i.1 with
  | some (dst, f, srcs) =>
      match outs.lookup f with
      | some p =>
          match aa f p, srcs[p]? with
          | some n, some (.reg A) =>
              if liveShareB σ (L (k + 1)) dst && decide (n < 2 ^ 64) then some (A, n)
              else none
          | _, _ => none
      | none => none
  | none =>
      match i.2, storeStruct? i.1 with
      | .store w n, some (d, b, _, _) =>
          if (w == 64) && liveShareB σ (L (k + 1)) d && decide (n < 2 ^ 64) then some (b, n)
          else none
      | _, _ => none

/-- The condition of a primary site with the destination `d` and the array `b` at position
    `k`: some name live after it other than `d` shares the image of `d` under `σ`, and `b`
    is itself live after it. -/
def primaryB (σ : String → String) (L : Nat → List String) (k : Nat) (d b : String) : Bool :=
  liveShareB σ (L (k + 1)) d && (L (k + 1)).contains b

/-- **The primary site of the instruction `i` at position `k`**, for the coalescing renaming
    `σ`, the liveness certificate `L`, the array positions `aa` and the out symbols `outs`:
    the array to copy and its length, or `none`. A store-tagged `STOREIDX` or a
    constant-index `STOREIMM` of `64`-bit words into `d` from the base `b` is a primary site
    when `primaryB σ L k d b` holds; the array is `b`. A shadow instruction of a call of an out
    symbol `f` with the destination position `p`, whose operand at `p` is the register `A` of
    an array of `n` words, is a primary site when `primaryB σ L k dst A` holds for its
    destination `dst`; the array is `A`. The length is below `2 ^ 64`. -/
def primarySite (σ : String → String) (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (k : Nat) (i : LinstrRM) : Option (String × Nat) :=
  match shadowCall? i.1 with
  | some (dst, f, srcs) =>
      match outs.lookup f with
      | some p =>
          match aa f p, srcs[p]? with
          | some n, some (.reg A) =>
              if primaryB σ L k dst A && decide (n < 2 ^ 64) then some (A, n) else none
          | _, _ => none
      | none => none
  | none =>
      match i.2 with
      | .store w n =>
          match storeStruct? i.1 with
          | some (d, b, _, _) =>
              if (w == 64) && primaryB σ L k d b && decide (n < 2 ^ 64) then some (b, n)
              else none
          | none => none
      | .storeImm w n =>
          match storeImmStruct? i.1 with
          | some (d, b, _, _) =>
              if (w == 64) && primaryB σ L k d b && decide (n < 2 ^ 64) then some (b, n)
              else none
          | none => none
      | _ => none

/-- The instruction `i` with its array operand replaced by `F`: the base of a `STOREIDX`, the
    array source of a `STOREIMM`, or the operand at the destination position of a call of an
    out symbol. -/
def retarget (outs : List (String × Nat)) (F : String) (i : LinstrRM) : LinstrRM :=
  match shadowCall? i.1 with
  | some (dst, f, srcs) =>
      match outs.lookup f with
      | some p => (callShadow dst f (srcs.set p (.reg F)), i.2)
      | none => i
  | none =>
      match i.1 with
      | .Lopn [.reg d] opn [.arrIdx _ x sc, .reg v] =>
          (.Lopn [.reg d] opn [.arrIdx F x sc, .reg v], i.2)
      | .Lopn [.reg d] opn [.reg _, .reg v, .imm c] =>
          if opn = "STOREIMM" then (.Lopn [.reg d] opn [.reg F, .reg v, .imm c], i.2) else i
      | _ => i

/-- **The expansion of the instruction `i` at position `k` under the site selector `sel`**:
    at a site with the array `A` of `n` words, the copy `resCopyCode A (freshName k) n`
    followed by `i` retargeted at the last version `copyName (freshName k) n`; elsewhere
    `i`. -/
def freshESel (outs : List (String × Nat)) (sel : Nat → LinstrRM → Option (String × Nat))
    (k : Nat) (i : LinstrRM) : List LinstrRM :=
  match sel k i with
  | some (A, n) =>
      resCopyCode A (freshName k) n ++ [retarget outs (copyName (freshName k) n) i]
  | none => [i]

/-- **The expansion of the instruction `i` at position `k`** at the sites `freshSite`. -/
def freshE (σ : String → String) (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (k : Nat) (i : LinstrRM) : List LinstrRM :=
  freshESel outs (freshSite σ L aa outs) k i

/-- A site rule: for the coalescing renaming, the liveness certificate, the array positions
    and the out symbols, the array to copy at the instruction at a position and its length.
    `freshSite` and `primarySite` are site rules. -/
abbrev SiteRule : Type :=
  (String → String) → (Nat → List String) → (String → Nat → Option Nat) →
    List (String × Nat) → Nat → LinstrRM → Option (String × Nat)

/-- **The freshening pass at the site rule `site`** on a body, for the liveness certificate
    `L` of the body, the array positions `aa` and the out symbols `outs`: each site of `site`
    at the coalescing renaming `chainAliasO outs body` is preceded by a copy of its array into
    a fresh array, and its array operand is replaced by the copy. -/
def freshenSel (site : SiteRule) (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (body : List LinstrRM) : List LinstrRM :=
  expI (freshESel outs (site (chainAliasO outs body) L aa outs)) body 0

/-- **The freshening pass** at the sites `freshSite`. -/
def freshenArr (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (body : List LinstrRM) : List LinstrRM :=
  freshenSel freshSite L aa outs body

/-! ## 5. The names of the pass -/

/-- A version after the first word of the copy into a fresh root is no fresh root. -/
theorem copyName_fresh_ne (k j k' : Nat) : copyName (freshName k) (j + 1) ≠ freshName k' := by
  intro h
  have h' := congrArg String.toList h
  simp only [copyName, freshName, Nat.add_one_ne_zero, ite_false, String.toList_append] at h'
  have h2 : '#' ∈ Nat.toDigits 10 k' := by
    have := List.append_cancel_left (as := ['f', '#']) (by simpa using h')
    rw [← this]
    simp
  simpa using Nat.isDigit_of_mem_toDigits (by decide) (by decide) h2

/-- A fresh root is a name of the fresh family. -/
theorem freshFam_freshName (k : Nat) : FreshFam (freshName k) := ⟨k, 0, by simp [copyName]⟩

/-- A kept name is no version of a fresh root. -/
theorem KeptF.ne_copy {r : String} (h : KeptF r) (k j : Nat) : r ≠ copyName (freshName k) j :=
  fun he => h.2.2 ⟨k, j, he⟩

/-- **The two kinds of site.** A site is a call of an out symbol whose operand at the
    destination position is the register of the copied array, or a store-tagged `STOREIDX`
    of `64`-bit words whose base is the copied array; its length is below `2 ^ 64`. -/
theorem freshSite_some {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i : LinstrRM}
    {A : String} {n : Nat} (h : freshSite σ L aa outs k i = some (A, n)) :
    n < 2 ^ 64 ∧
      ((∃ dst f srcs p, shadowCall? i.1 = some (dst, f, srcs) ∧ outs.lookup f = some p
          ∧ aa f p = some n ∧ srcs[p]? = some (.reg A))
        ∨ (shadowCall? i.1 = none ∧ i.2 = .store 64 n
          ∧ ∃ d x v, storeStruct? i.1 = some (d, A, x, v))) := by
  unfold freshSite at h
  split at h
  · rename_i dst f srcs hsh
    split at h
    · rename_i p hp
      split at h
      · rename_i n' A' hn hA
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨hc.2, Or.inl ⟨dst, f, srcs, p, hsh, hp, hn, hA⟩⟩
        · cases h
      · cases h
    · cases h
  · rename_i hsh
    split at h
    · rename_i w n' d b x v htag hst
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        obtain ⟨⟨rfl, -⟩, hn⟩ := hc
        exact ⟨hn, Or.inr ⟨hsh, htag, d, x, v, hst⟩⟩
      · cases h
    · cases h

/-- **The three kinds of site** of the instruction `i` with the array `A` of `n < 2 ^ 64`
    words: a call of an out symbol whose operand at the destination position is the register
    `A`, a store-tagged `STOREIDX` of `64`-bit words with base `A`, or a `STOREIMM` of
    `64`-bit words with array source `A`. -/
def SiteShape (aa : String → Nat → Option Nat) (outs : List (String × Nat)) (i : LinstrRM)
    (A : String) (n : Nat) : Prop :=
  n < 2 ^ 64 ∧
    ((∃ dst f srcs p, shadowCall? i.1 = some (dst, f, srcs) ∧ outs.lookup f = some p
        ∧ aa f p = some n ∧ srcs[p]? = some (.reg A))
      ∨ (shadowCall? i.1 = none ∧ i.2 = .store 64 n
          ∧ ∃ d x v, storeStruct? i.1 = some (d, A, x, v))
      ∨ (shadowCall? i.1 = none ∧ i.2 = .storeImm 64 n
          ∧ ∃ d v c, storeImmStruct? i.1 = some (d, A, v, c)))

/-- A site selector selects sites of the three kinds only. -/
def SiteOK (aa : String → Nat → Option Nat) (outs : List (String × Nat))
    (sel : Nat → LinstrRM → Option (String × Nat)) : Prop :=
  ∀ k i A n, sel k i = some (A, n) → SiteShape aa outs i A n

/-- The sites `freshSite` are of the three kinds. -/
theorem freshSite_ok (σ : String → String) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) :
    SiteOK aa outs (freshSite σ L aa outs) := fun _ _ _ _ h => by
  obtain ⟨hn, h1 | h2⟩ := freshSite_some h
  exacts [⟨hn, Or.inl h1⟩, ⟨hn, Or.inr (Or.inl h2)⟩]

/-- The primary sites `primarySite` are of the three kinds. -/
theorem primarySite_ok (σ : String → String) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) :
    SiteOK aa outs (primarySite σ L aa outs) := by
  intro k i A n h
  unfold primarySite at h
  split at h
  · rename_i dst f srcs hsh
    split at h
    · rename_i p hp
      split at h
      · rename_i n' A' hn hA
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          exact ⟨hc.2, Or.inl ⟨dst, f, srcs, p, hsh, hp, hn, hA⟩⟩
        · cases h
      · cases h
    · cases h
  · rename_i hsh
    split at h
    · rename_i w n' htag
      split at h
      · rename_i d b x v hst
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          obtain ⟨⟨rfl, -⟩, hn⟩ := hc
          exact ⟨hn, Or.inr (Or.inl ⟨hsh, htag, d, x, v, hst⟩)⟩
        · cases h
      · cases h
    · rename_i w n' htag
      split at h
      · rename_i d b v c hst
        split at h
        · rename_i hc
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
          obtain ⟨⟨rfl, -⟩, hn⟩ := hc
          exact ⟨hn, Or.inr (Or.inr ⟨hsh, htag, d, v, c, hst⟩)⟩
        · cases h
      · cases h
    · cases h

/-! ## 6. The relation of the two runs -/

section Keep

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames RenOn RenProg
  RelF evalInstrPMemF_ren mulxFree CondOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (fstepF_setLpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (emptyP renRM_id)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (evalInstrPMemF)

/-- **A step on bases that agree on a name set.** Let `N` contain the empty name and every
    name of an `Lopn` that is not a `MULX`, and let two bases agree on the registers and the
    arrays of the names of `N`, on the word memory and on the carry and overflow flags. A
    step of the instruction from the first base is matched by a step from the second with
    the same zero flag, into bases that agree in the same way. -/
theorem fstepF_keep {N : String → Prop} (hN : N "") {i : LinstrRM} (hl : IsLopn i)
    (hn : ∀ n ∈ instrNames i.1, N n) (hm : mulxFree i = true) {s s' t : LstateM}
    {zf zt : Bool} (hreg : ∀ r, N r → s'.reg.lvm r = s.reg.lvm r)
    (harr : ∀ r, N r → s'.larr r = s.larr r) (hmem : s'.lmem = s.lmem) (hcf : s'.cf = s.cf)
    (hof : s'.of = s.of) (h : fstepF i s zf = some (t, zt)) :
    ∃ t', fstepF i s' zf = some (t', zt) ∧ (∀ r, N r → t'.reg.lvm r = t.reg.lvm r)
      ∧ (∀ r, N r → t'.larr r = t.larr r) ∧ t'.lmem = t.lmem ∧ t'.cf = t.cf
      ∧ t'.of = t.of := by
  let S : LstateMF := { prog := { base := s, lfn := "" }, zf := zf }
  let S' : LstateMF := { prog := { base := s'.setLpc s.lpc, lfn := "" }, zf := zf }
  have hσ : RenOn id N := ⟨fun _ _ _ _ h => h, hN, rfl⟩
  have hP : RenProg id N 0 emptyP emptyP :=
    ⟨rfl, fun _ => rfl, fun k _ => by simp [emptyP], fun k i _ h => by simp [emptyP] at h,
      fun k i _ h => by simp [emptyP] at h, fun l pc h => by simp⟩
  have hR : RelF id N S S' :=
    ⟨⟨⟨rfl, fun r hr => hreg r hr⟩, fun r hr => harr r hr, hmem⟩, rfl, rfl, hcf, hof⟩
  have hc : CondOK i := ⟨fun c l he => (by
    obtain ⟨d, o, s0, hd⟩ := hl; rw [hd] at he; cases he), hm⟩
  have he : evalInstrPMemF emptyP i S
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ i S hl]
    show (fstepF i s zf).map _ = _
    rw [h]; rfl
  obtain ⟨T', hT', hRT, -⟩ := evalInstrPMemF_ren hσ hP i hn hc hR (Nat.zero_le _) he
  rw [renRM_id, evalInstrPMemF_isLopn _ i S' hl] at hT'
  obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp hT'
  have hb' : fstepF i (s'.setLpc s.lpc) zf = some bz := hb
  rw [fstepF_setLpc] at hb'
  obtain ⟨⟨t'', z''⟩, h'', hbz⟩ := Option.map_eq_some_iff.mp hb'
  subst hbz
  obtain ⟨⟨⟨-, hreg'⟩, harr', hmem'⟩, -, hzf, hcf', hof'⟩ := hRT
  refine ⟨t'', ?_, fun r hr => hreg' r hr, fun r hr => harr' r hr, hmem', hcf', hof'⟩
  rw [h'']
  simp only at hzf
  rw [hzf]

end Keep

/-- **The relation of a source base `s` and a freshened base `s'`**, for the fresh roots
    `Rt` (a root `freshName k` of `n` words at each `Rt k n`): the bases agree on the
    registers and arrays of the kept names, on the word memory and on the carry and overflow
    flags, and each fresh root holds an array of its length in `s'`. -/
structure FrRel (Rt : Nat → Nat → Prop) (s s' : LstateM) : Prop where
  /-- The kept registers agree. -/
  reg : ∀ r, KeptF r → s'.reg.lvm r = s.reg.lvm r
  /-- The kept arrays agree. -/
  arr : ∀ r, KeptF r → s'.larr r = s.larr r
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of
  /-- Each fresh root holds an array of its length. -/
  root : ∀ k n, Rt k n → ∃ a : Fin n → BitVec 64, s'.getArr (freshName k) 64 n = some a

/-- The fresh roots of a body under the site selector `sel`: `freshName k` of `n` words at
    each site of the instruction at position `k` with an array of `n` words. -/
def freshRootsSel (sel : Nat → LinstrRM → Option (String × Nat)) (body : List LinstrRM)
    (k n : Nat) : Prop :=
  ∃ i A, body[k]? = some i ∧ sel k i = some (A, n)

/-- The fresh roots of a body at the sites `freshSite`. -/
def freshRoots (σ : String → String) (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) (body : List LinstrRM) (k n : Nat) : Prop :=
  freshRootsSel (freshSite σ L aa outs) body k n

/-- The empty name is kept. -/
theorem keptF_empty : KeptF "" := by
  refine ⟨by decide, by decide, fun ⟨k, j, h⟩ => ?_⟩
  have h' := congrArg String.toList h
  unfold copyName at h'
  split at h' <;> simp [freshName] at h'

/-- The relation does not read the program counters. -/
theorem FrRel.setLpc {Rt : Nat → Nat → Prop} {s s' : LstateM} (h : FrRel Rt s s') (p q : Nat) :
    FrRel Rt (s.setLpc p) (s'.setLpc q) :=
  ⟨h.reg, h.arr, h.mem, h.cf, h.of, h.root⟩

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames) in
/-- A step of an instruction all of whose names are kept keeps the fresh roots. -/
theorem root_fstepF {Rt : Nat → Nat → Prop} {i : LinstrRM} (hk : ∀ r ∈ instrNames i.1, KeptF r)
    {s t : LstateM} {zf z : Bool} (h : fstepF i s zf = some (t, z))
    (hr : ∀ k n, Rt k n → ∃ a : Fin n → BitVec 64, s.getArr (freshName k) 64 n = some a) :
    ∀ k n, Rt k n → ∃ a : Fin n → BitVec 64, t.getArr (freshName k) 64 n = some a := by
  intro k n hkn
  have hl := (JasminLsemStepFrame.fstepF_frame h
    (fun hm => (hk _ hm).2.2 (freshFam_freshName k))).2
  unfold LstateM.getArr
  rw [hl]
  exact hr k n hkn

/-- The wire of a recognised `STOREIDX`. -/
theorem storeStruct?_eq_some {w : LinstrR} {d b x v : String}
    (h : storeStruct? w = some (d, b, x, v)) :
    ∃ sc, w = .Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v] := by
  unfold storeStruct? at h
  split at h
  · rename_i d' opn b' x' sc v'
    split at h
    · rename_i ho
      cases h
      exact ⟨sc, by rw [ho]⟩
    · cases h
  · cases h

/-- The wire of a recognised `STOREIMM`. -/
theorem storeImmStruct?_eq_some {w : LinstrR} {d b v : String} {c : Nat}
    (h : storeImmStruct? w = some (d, b, v, c)) :
    w = .Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm c] := by
  unfold storeImmStruct? at h
  split at h
  · rename_i d' opn b' v' c'
    split at h
    · rename_i ho
      cases h
      rw [ho]
    · cases h
  · cases h

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames) in
/-- **A freshened store.** At a store site of the instruction `i` at position `k`, a store
    of `64`-bit words into `d` from the base `b` with a fresh root `freshName k` of `n < 2 ^ 64`
    words, a step of `i` from `s` is matched, from a related base, by the copy of `b` into the
    fresh root followed by the store retargeted at the last version of the copy, into a
    related base. -/
theorem freshStore_sim {Rt : Nat → Nat → Prop} (outs : List (String × Nat)) {i : LinstrRM}
    {k n : Nat} {d b x v : String} (hRt : Rt k n) (hn : n < 2 ^ 64)
    (htag : i.2 = .store 64 n) (hst : storeStruct? i.1 = some (d, b, x, v))
    (hkept : ∀ r ∈ instrNames i.1, KeptF r) {s s' t : LstateM} {zf zt : Bool}
    (hQ : FrRel Rt s s') (h : fstepF i s zf = some (t, zt)) :
    ∃ t', runStraightF (resCopyCode b (freshName k) n
        ++ [retarget outs (copyName (freshName k) n) i]) s' zf = some (t', zt)
      ∧ FrRel Rt t t' := by
  obtain ⟨sc, hw⟩ := storeStruct?_eq_some hst
  obtain ⟨w, tag⟩ := i
  simp only at htag hw
  subst htag hw
  have hkb : KeptF b := hkept b (by simp [instrNames, opNames])
  have hkd : KeptF d := hkept d (by simp [instrNames, opNames])
  have hkx : KeptF x := hkept x (by simp [instrNames, opNames])
  have hkv : KeptF v := hkept v (by simp [instrNames, opNames])
  rw [fstepF_storeIdx] at h
  obtain ⟨t0, ht0, hzt⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hzt
  obtain ⟨rfl, rfl⟩ := hzt
  simp only [lsemStepMem, storeStruct?, ite_true] at ht0
  cases ha : s.getArr b 64 n with
  | none => simp [ha] at ht0
  | some arr =>
  cases hi : s.reg.getW x 64 with
  | none => simp [ha, hi] at ht0
  | some vi =>
  cases hv : s.reg.getW v 64 with
  | none => simp [ha, hi, hv] at ht0
  | some vv =>
  simp only [ha, hi, hv, Option.some.injEq] at ht0
  subst ht0
  have ha' : s'.getArr b 64 n = some arr := by
    unfold LstateM.getArr; rw [hQ.arr b hkb]; exact ha
  obtain ⟨a0, ha0⟩ := hQ.root k n hRt
  obtain ⟨u, hu, hcopy, hureg, huarr, humem, hucf, huof⟩ :=
    runStraightF_resCopy hn s' zf ha' (by simpa [copyName] using ha0)
      (fun j _ => hkb.ne_copy k (j + 1))
  have hret : retarget outs (copyName (freshName k) n)
      (.Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v], .store 64 n)
      = (.Lopn [.reg d] "STOREIDX" [.arrIdx (copyName (freshName k) n) x sc, .reg v],
          .store 64 n) := by
    simp [retarget, shadowCall?]
  have hgw : ∀ r, KeptF r → u.reg.getW r 64 = s.reg.getW r 64 := by
    intro r hr
    unfold LstateN.getW
    rw [hureg r hr.1 hr.2.1, hQ.reg r hr]
  have hst' := JasminLsemMemSourceTieUncond.lsemStepMem_storeIdx d (copyName (freshName k) n)
    x v sc arr vi vv u hcopy (by rw [hgw x hkx]; exact hi) (by rw [hgw v hkv]; exact hv)
  refine ⟨(u.setArr d (stackSet arr vi.toNat vv)).nextPc, ?_, ⟨fun r hr => ?_, fun r hr => ?_,
    ?_, ?_, ?_, fun k' n' hk' => ?_⟩⟩
  · rw [JasminLsemAddrMem.runStraightF_append, hu, Option.bind_some, hret, runStraightF_cons,
      fstepF_storeIdx, hst']
    rfl
  · show (u.reg).lvm r = (s.reg).lvm r
    rw [hureg r hr.1 hr.2.1, hQ.reg r hr]
  · simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
    split
    · rfl
    · rw [huarr r (fun j _ => hr.ne_copy k (j + 1)), hQ.arr r hr]
  · show u.lmem = s.lmem
    rw [humem, hQ.mem]
  · show u.cf = s.cf
    rw [hucf, hQ.cf]
  · show u.of = s.of
    rw [huof, hQ.of]
  · have hdk : freshName k' ≠ d := fun he => hkd.ne_copy k' 0 (by simp [copyName, he])
    rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_other _ _ _ _ _ _ hdk]
    unfold LstateM.getArr
    rw [huarr _ (fun j _ => (copyName_fresh_ne k j k').symm)]
    exact hQ.root k' n' hk'

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames) in
/-- **A freshened constant-index store.** At a `STOREIMM` site of the instruction `i` at
    position `k`, a store of `64`-bit words into `d` from the array `b` at the index `c` with
    a fresh root `freshName k` of `n < 2 ^ 64` words, a step of `i` from `s` is matched, from a
    related base, by the copy of `b` into the fresh root followed by the store retargeted at
    the last version of the copy, into a related base. -/
theorem freshStoreImm_sim {Rt : Nat → Nat → Prop} (outs : List (String × Nat)) {i : LinstrRM}
    {k n : Nat} {d b v : String} {c : Nat} (hRt : Rt k n) (hn : n < 2 ^ 64)
    (htag : i.2 = .storeImm 64 n) (hst : storeImmStruct? i.1 = some (d, b, v, c))
    (hkept : ∀ r ∈ instrNames i.1, KeptF r) {s s' t : LstateM} {zf zt : Bool}
    (hQ : FrRel Rt s s') (h : fstepF i s zf = some (t, zt)) :
    ∃ t', runStraightF (resCopyCode b (freshName k) n
        ++ [retarget outs (copyName (freshName k) n) i]) s' zf = some (t', zt)
      ∧ FrRel Rt t t' := by
  have hw := storeImmStruct?_eq_some hst
  obtain ⟨w, tag⟩ := i
  simp only at htag hw
  subst htag hw
  have hkb : KeptF b := hkept b (by simp [instrNames, opNames])
  have hkd : KeptF d := hkept d (by simp [instrNames, opNames])
  have hkv : KeptF v := hkept v (by simp [instrNames, opNames])
  rw [fstepF_storeImm] at h
  obtain ⟨t0, ht0, hzt⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at hzt
  obtain ⟨rfl, rfl⟩ := hzt
  simp only [lsemStepMem, storeImmStruct?, ite_true] at ht0
  cases ha : s.getArr b 64 n with
  | none => simp [ha] at ht0
  | some arr =>
  cases hv : s.reg.getW v 64 with
  | none => simp [ha, hv] at ht0
  | some vv =>
  simp only [ha, hv, Option.some.injEq] at ht0
  subst ht0
  have ha' : s'.getArr b 64 n = some arr := by
    unfold LstateM.getArr; rw [hQ.arr b hkb]; exact ha
  obtain ⟨a0, ha0⟩ := hQ.root k n hRt
  obtain ⟨u, hu, hcopy, hureg, huarr, humem, hucf, huof⟩ :=
    runStraightF_resCopy hn s' zf ha' (by simpa [copyName] using ha0)
      (fun j _ => hkb.ne_copy k (j + 1))
  have hret : retarget outs (copyName (freshName k) n)
      (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm c], .storeImm 64 n)
      = (.Lopn [.reg d] "STOREIMM" [.reg (copyName (freshName k) n), .reg v, .imm c],
          .storeImm 64 n) := by
    simp [retarget, shadowCall?]
  have hgw : ∀ r, KeptF r → u.reg.getW r 64 = s.reg.getW r 64 := by
    intro r hr
    unfold LstateN.getW
    rw [hureg r hr.1 hr.2.1, hQ.reg r hr]
  have hst' := lsemStepMem_storeImmC d (copyName (freshName k) n) v c 64 n u hcopy
    (by rw [hgw v hkv]; exact hv)
  refine ⟨(u.setArr d (stackSet arr c vv)).nextPc, ?_, ⟨fun r hr => ?_, fun r hr => ?_,
    ?_, ?_, ?_, fun k' n' hk' => ?_⟩⟩
  · rw [JasminLsemAddrMem.runStraightF_append, hu, Option.bind_some, hret, runStraightF_cons,
      fstepF_storeImm, hst']
    rfl
  · show (u.reg).lvm r = (s.reg).lvm r
    rw [hureg r hr.1 hr.2.1, hQ.reg r hr]
  · simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
    split
    · rfl
    · rw [huarr r (fun j _ => hr.ne_copy k (j + 1)), hQ.arr r hr]
  · show u.lmem = s.lmem
    rw [humem, hQ.mem]
  · show u.cf = s.cf
    rw [hucf, hQ.cf]
  · show u.of = s.of
    rw [huof, hQ.of]
  · have hdk : freshName k' ≠ d := fun he => hkd.ne_copy k' 0 (by simp [copyName, he])
    rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_other _ _ _ _ _ _ hdk]
    unfold LstateM.getArr
    rw [huarr _ (fun j _ => (copyName_fresh_ne k j k').symm)]
    exact hQ.root k' n' hk'

/-- **The copy into a fresh root keeps the relation.** From a base related to `s` in which
    the kept array `A` holds `arr` of `n < 2 ^ 64` words, the copy of `A` into the fresh root
    `freshName k` of `n` words keeps the zero flag and ends in a base related to `s` in which
    the last version of the copy holds `arr`. -/
theorem frRel_resCopy {Rt : Nat → Nat → Prop} {s s' : LstateM} (hQ : FrRel Rt s s')
    {A : String} (hA : KeptF A) {k n : Nat} (hRt : Rt k n) (hn : n < 2 ^ 64)
    {arr : Fin n → BitVec 64} (ha : s'.getArr A 64 n = some arr) (zf : Bool) :
    ∃ u, runStraightF (resCopyCode A (freshName k) n) s' zf = some (u, zf)
      ∧ u.getArr (copyName (freshName k) n) 64 n = some arr ∧ FrRel Rt s u := by
  obtain ⟨a0, ha0⟩ := hQ.root k n hRt
  obtain ⟨u, hu, hcopy, hureg, huarr, humem, hucf, huof⟩ :=
    runStraightF_resCopy hn s' zf ha (by simpa [copyName] using ha0)
      (fun j _ => hA.ne_copy k (j + 1))
  refine ⟨u, hu, hcopy, ⟨fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_, fun k' n' hk' => ?_⟩⟩
  · rw [hureg r hr.1 hr.2.1, hQ.reg r hr]
  · rw [huarr r (fun j _ => hr.ne_copy k (j + 1)), hQ.arr r hr]
  · rw [humem, hQ.mem]
  · rw [hucf, hQ.cf]
  · rw [huof, hQ.of]
  · unfold LstateM.getArr
    rw [huarr _ (fun j _ => (copyName_fresh_ne k j k').symm)]
    exact hQ.root k' n' hk'

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (retRes CallRes argRead argsRead) in
/-- The write of the result of a call into a kept destination keeps the relation. -/
theorem FrRel.retRes {Rt : Nat → Nat → Prop} {a a' : LstateMF}
    (h : FrRel Rt a.prog.base a'.prog.base) {dst : String} (hd : KeptF dst) (x : CallRes) :
    FrRel Rt (retRes dst x a).prog.base (retRes dst x a').prog.base := by
  have hdk : ∀ k', freshName k' ≠ dst := fun k' he =>
    hd.ne_copy k' 0 (by simp [copyName, he])
  cases x with
  | word r =>
      refine ⟨fun q hq => ?_, fun q hq => h.arr q hq, h.mem, h.cf, h.of, h.root⟩
      simp only [LprogIsa.retRes_word, LprogIsa.retWord, LstateM.nextPc, LstateM.setReg,
        LstateN.lvm_nextPc, LstateN.lvm_setReg]
      split
      · rfl
      · exact h.reg q hq
  | arr v =>
      refine ⟨fun q hq => h.reg q hq, fun q hq => ?_, h.mem, h.cf, h.of, fun k' n' hk' => ?_⟩
      · simp only [LprogIsa.retRes_arr, LprogIsa.retArr, LstateM.larr_nextPc,
          LstateM.larr_setArr]
        split
        · rfl
        · exact h.arr q hq
      · simp only [LprogIsa.retRes_arr, LprogIsa.retArr]
        rw [LstateM.getArr_nextPc, LstateM.getArr_setArr_other _ _ _ _ _ _ (hdk k')]
        exact h.root k' n' hk'

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (argRead argsRead) in
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames) in
/-- The words of an operand all of whose names are kept are read alike from bases that agree
    on the kept registers and arrays. -/
theorem argRead_kept {aa : Nat → Option Nat} {b b' : LstateM}
    (hreg : ∀ r, KeptF r → b'.reg.lvm r = b.reg.lvm r)
    (harr : ∀ r, KeptF r → b'.larr r = b.larr r) (j : Nat) {o : LOperand}
    (ho : ∀ r ∈ opNames o, KeptF r) : argRead aa b' j o = argRead aa b j o := by
  cases o with
  | reg r =>
      have hr := ho r (by simp [opNames])
      simp only [argRead, evalOperandN]
      unfold LstateN.getW LstateM.getArr
      rw [hreg r hr, harr r hr]
  | imm _ => rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (argRead argsRead) in
/-- The argument words of two operand lists of one length whose operands are read alike at
    each position are equal. -/
theorem argsRead_congr {aa : Nat → Option Nat} {b b' : LstateM} :
    ∀ (srcs srcs' : List LOperand) (j0 : Nat), srcs'.length = srcs.length →
      (∀ j o o', srcs[j]? = some o → srcs'[j]? = some o' →
        argRead aa b' (j0 + j) o' = argRead aa b (j0 + j) o) →
      argsRead aa b' j0 srcs' = argsRead aa b j0 srcs
  | [], [], _, _, _ => rfl
  | o :: os, o' :: os', j0, hl, h => by
      simp only [argsRead]
      have h0 := h 0 o o' rfl rfl
      rw [Nat.add_zero] at h0
      rw [h0, argsRead_congr os os' (j0 + 1) (by simpa using hl)
        (fun j p p' hp hp' => by
          rw [show j0 + 1 + j = j0 + (j + 1) by omega]
          exact h (j + 1) p p' hp hp')]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (argRead argsRead) in
/-- Readable argument words read every operand. -/
theorem argRead_isSome_of_argsRead {aa : Nat → Option Nat} {b : LstateM} :
    ∀ (srcs : List LOperand) (j0 : Nat), (argsRead aa b j0 srcs).isSome →
      ∀ j o, srcs[j]? = some o → (argRead aa b (j0 + j) o).isSome
  | [], _, _, j, o, hj => by simp at hj
  | o :: os, j0, h, j, p, hj => by
      simp only [argsRead] at h
      cases ho : argRead aa b j0 o with
      | none => simp [ho] at h
      | some v =>
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
              subst hj
              simp [ho]
          | succ j =>
              simp only [List.getElem?_cons_succ] at hj
              have h' : (argsRead aa b (j0 + 1) os).isSome := by
                simp only [ho, Option.bind_some] at h
                cases hr : argsRead aa b (j0 + 1) os <;> simp_all
              have := argRead_isSome_of_argsRead os (j0 + 1) h' j p hj
              rwa [show j0 + 1 + j = j0 + (j + 1) by omega] at this

/-! ## 7. The shape of the expansion -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (IsLopn)

/-- Every instruction of the array copy is an `Lopn` and no shadow instruction of a call. -/
theorem resCopyCode_mem {A F : String} {n : Nat} {j : LinstrRM} (h : j ∈ resCopyCode A F n) :
    IsLopn j ∧ shadowCall? j.1 = none := by
  simp only [resCopyCode, List.mem_flatMap, resCopyStep, List.mem_cons, List.not_mem_nil,
    or_false] at h
  obtain ⟨_, _, h | h | h⟩ := h <;> subst h
  · exact ⟨⟨_, _, _, rfl⟩, by
      simp [shadowCall?, movImmI, ExportRegions.movI, withWidthTag]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [shadowCall?]⟩
  · exact ⟨⟨_, _, _, rfl⟩, by simp [shadowCall?]⟩

/-- The retargeted `Lopn` is an `Lopn`. -/
theorem isLopn_retarget (outs : List (String × Nat)) (F : String) {i : LinstrRM}
    (hi : IsLopn i) : IsLopn (retarget outs F i) := by
  obtain ⟨d, o, s, hd⟩ := hi
  unfold retarget
  split
  · split
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨d, o, s, hd⟩
  · split
    · exact ⟨_, _, _, rfl⟩
    · split
      · exact ⟨_, _, _, rfl⟩
      · exact ⟨d, o, s, hd⟩
    · exact ⟨d, o, s, hd⟩

/-- The retargeted instruction of an instruction that is no shadow instruction of a call is
    no shadow instruction of a call. -/
theorem shadowCall?_retarget (outs : List (String × Nat)) (F : String) {i : LinstrRM}
    (hi : shadowCall? i.1 = none) : shadowCall? (retarget outs F i).1 = none := by
  unfold retarget
  rw [hi]
  simp only
  split
  · rename_i d opn b x sc v hw
    rw [hw] at hi
    simpa [shadowCall?] using hi
  · rename_i d opn b v c hw
    split
    · rw [hw] at hi
      simpa [shadowCall?] using hi
    · exact hi
  · exact hi

/-- An instruction that is no `Lopn` is no site. -/
theorem freshSite_of_not_lopn {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i : LinstrRM}
    (hi : ¬ IsLopn i) : freshSite σ L aa outs k i = none := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn d o s => exact absurd ⟨d, o, s, rfl⟩ hi
  | _ => simp [freshSite, shadowCall?, storeStruct?]

/-- A site is an `Lopn`. -/
theorem SiteShape.isLopn {aa : String → Nat → Option Nat} {outs : List (String × Nat)}
    {i : LinstrRM} {A : String} {n : Nat} (h : SiteShape aa outs i A n) : IsLopn i := by
  obtain ⟨-, ⟨dst, f, srcs, p, hsh, -⟩ | ⟨-, -, d, x, v, hst⟩ | ⟨-, -, d, v, c, hst⟩⟩ := h
  · obtain ⟨dst', opn, srcs', hw, -⟩ := LprogIsaProcs.shadowCall?_wire
      (by rw [hsh]; exact Option.some_ne_none _)
    exact ⟨_, _, _, hw⟩
  · obtain ⟨sc, hw⟩ := storeStruct?_eq_some hst
    exact ⟨_, _, _, hw⟩
  · exact ⟨_, _, _, storeImmStruct?_eq_some hst⟩

/-- A selector of sites of the three kinds selects no instruction that is no `Lopn`. -/
theorem SiteOK.none_of_not_lopn {aa : String → Nat → Option Nat} {outs : List (String × Nat)}
    {sel : Nat → LinstrRM → Option (String × Nat)} (hsel : SiteOK aa outs sel) {k : Nat}
    {i : LinstrRM} (hi : ¬ IsLopn i) : sel k i = none := by
  cases h : sel k i with
  | none => rfl
  | some An => exact absurd (hsel k i An.1 An.2 h).isLopn hi

/-- Every instruction of the expansion of an `Lopn` under a site selector is an `Lopn`. -/
theorem freshESel_lopn {outs : List (String × Nat)}
    {sel : Nat → LinstrRM → Option (String × Nat)} {k : Nat} {i : LinstrRM}
    (hi : IsLopn i) : ∀ j ∈ freshESel outs sel k i, IsLopn j := by
  intro j hj
  unfold freshESel at hj
  split at hj
  · rcases List.mem_append.mp hj with h | h
    · exact (resCopyCode_mem h).1
    · rw [List.mem_singleton.mp h]
      exact isLopn_retarget outs _ hi
  · rw [List.mem_singleton.mp hj]
    exact hi

/-- No instruction of the expansion under a site selector of an instruction that is no shadow
    instruction of a call is a shadow instruction of a call. -/
theorem freshESel_noCall {outs : List (String × Nat)}
    {sel : Nat → LinstrRM → Option (String × Nat)} {k : Nat} {i : LinstrRM}
    (hi : shadowCall? i.1 = none) : ∀ j ∈ freshESel outs sel k i, shadowCall? j.1 = none := by
  intro j hj
  unfold freshESel at hj
  split at hj
  · rcases List.mem_append.mp hj with h | h
    · exact (resCopyCode_mem h).2
    · rw [List.mem_singleton.mp h]
      exact shadowCall?_retarget outs _ hi
  · rw [List.mem_singleton.mp hj]
    exact hi

/-- Every instruction of the expansion of an `Lopn` is an `Lopn`. -/
theorem freshE_lopn {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i : LinstrRM}
    (hi : IsLopn i) : ∀ j ∈ freshE σ L aa outs k i, IsLopn j :=
  freshESel_lopn hi

/-- No instruction of the expansion of an instruction that is no shadow instruction of a
    call is a shadow instruction of a call. -/
theorem freshE_noCall {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i : LinstrRM}
    (hi : shadowCall? i.1 = none) : ∀ j ∈ freshE σ L aa outs k i, shadowCall? j.1 = none :=
  freshESel_noCall hi

/-! ## 8. The run of the freshened body -/

section Run

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (expI pcI ExpInv RelI CtlI
  expI_split)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow shadowCall? retRes
  argsRead argRead CallRes shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames
  mulxFree)

/-- The flag fold has no step at a shadow instruction of a call. -/
theorem fstepF_shadowCall {i : LinstrRM} (hl : IsLopn i) (hsh : shadowCall? i.1 ≠ none)
    (s : LstateM) (zf : Bool) : fstepF i s zf = none := by
  let S : LstateMF := { prog := { base := s, lfn := "" }, zf := zf }
  have h1 := evalInstrPMemF_shadowCall JasminLsemFuseMulHi.emptyP i S hsh
  rw [evalInstrPMemF_isLopn _ i S hl] at h1
  exact Option.map_eq_none_iff.mp h1

/-- **The expansion conditions of the pass under a site selector.** For a body whose
    instructions are `Lopn`s or control instructions, contain no `MULX` and name kept names
    only, the expansion `freshESel outs sel` at a selector `sel` of sites of the three kinds
    satisfies `ExpInv` for the relation `FrRel` at the fresh roots of the body and the trivial
    invariant. -/
theorem freshESel_expInv (aa : String → Nat → Option Nat) (outs : List (String × Nat))
    {sel : Nat → LinstrRM → Option (String × Nat)} (hsel : SiteOK aa outs sel)
    {body : List LinstrRM}
    (hcls : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → IsLopn i ∨ CtlI i)
    (hmx : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → mulxFree i = true)
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r) :
    ExpInv (FrRel (freshRootsSel sel body)) (fun _ => True) (fun _ _ _ => True)
      (freshESel outs sel) body := by
  refine ⟨fun k i hk => ?_, fun k i hk hl => ⟨freshESel_lopn hl, ?_⟩, fun _ _ _ _ => trivial,
    fun _ _ _ => trivial, fun _ _ _ _ _ _ _ => trivial,
    fun _ _ _ _ h => h.setLpc _ _⟩
  · rcases hcls k i hk with hl | hc
    · exact Or.inl hl
    · refine Or.inr ⟨hc, ?_⟩
      have hnl : ¬ IsLopn i := by
        rintro ⟨d, o, s, hd⟩
        rcases hc with ⟨kd, l, h⟩ | ⟨c, l, h, -⟩ | ⟨tgt, h⟩ <;> rw [h] at hd <;> cases hd
      unfold freshESel
      rw [hsel.none_of_not_lopn hnl]
  · intro s s' t zf zt _ hQ h
    refine ⟨trivial, ?_⟩
    unfold freshESel
    cases hsite : sel k i with
    | none =>
        obtain ⟨t', ht', hreg, harr, hmem, hcf, hof⟩ := fstepF_keep keptF_empty hl
          (hkept k i hk) (hmx k i hk) hQ.reg hQ.arr hQ.mem hQ.cf hQ.of h
        refine ⟨t', ?_, ⟨hreg, harr, hmem, hcf, hof, root_fstepF (hkept k i hk) ht' hQ.root⟩⟩
        simp only [runStraightF_cons, ht', Option.bind_some, runStraightF_nil]
    | some An =>
        obtain ⟨A, n⟩ := An
        obtain ⟨hn, ⟨dst, f, srcs, p, hsh, -⟩ | ⟨-, htag, d, x, v, hst⟩
          | ⟨-, htag, d, v, c, hst⟩⟩ := hsel k i A n hsite
        · rw [fstepF_shadowCall hl (by rw [hsh]; exact Option.some_ne_none _)] at h
          cases h
        · exact freshStore_sim outs ⟨i, A, hk, hsite⟩ hn htag hst (hkept k i hk) hQ h
        · exact freshStoreImm_sim outs ⟨i, A, hk, hsite⟩ hn htag hst (hkept k i hk) hQ h

/-- **The expansion conditions of the pass.** For a body whose instructions are `Lopn`s or
    control instructions, contain no `MULX` and name kept names only, the expansion `freshE`
    with the coalescing renaming `σ` satisfies `ExpInv` for the relation `FrRel` at the fresh
    roots of the body and the trivial invariant. -/
theorem freshE_expInv (σ : String → String) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) {body : List LinstrRM}
    (hcls : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → IsLopn i ∨ CtlI i)
    (hmx : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → mulxFree i = true)
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r) :
    ExpInv (FrRel (freshRoots σ L aa outs body)) (fun _ => True) (fun _ _ _ => True)
      (freshE σ L aa outs) body :=
  freshESel_expInv aa outs (freshSite_ok σ L aa outs) hcls hmx hkept

/-- **A call under the pass.** Let the instruction `i` at position `k` of `body` be the call
    `callShadow dst f srcs` with kept names, and its argument words be readable at `s`. Its
    expansion is a straight segment followed by a call of `f` on as many operands; from a base
    related to `s`, the segment runs to a base at which those operands have the argument words
    of `srcs` at `s`, and the write of every result keeps the relation. At a site the segment
    is the copy of the destination array into its fresh root and the operand at the
    destination position is the last version of the copy; elsewhere the segment is empty. -/
theorem freshESel_call (aa : String → Nat → Option Nat) (outs : List (String × Nat))
    {sel : Nat → LinstrRM → Option (String × Nat)} (hsel : SiteOK aa outs sel)
    {body : List LinstrRM}
    {k : Nat} {i : LinstrRM} (hk : body[k]? = some i)
    (hkept : ∀ r ∈ instrNames i.1, KeptF r) {s s' : LstateMF} {dst f : String}
    {srcs : List LOperand} (x : CallRes) (hi : i.1 = callShadow dst f srcs)
    (harg : (argsRead (aa f) s.prog.base 0 srcs).isSome)
    (hQ : FrRel (freshRootsSel sel body) s.prog.base s'.prog.base) :
    ∃ (pre : List LinstrRM) (srcs' : List LOperand) (b : LstateM),
      freshESel outs sel k i = pre ++ [(callShadow dst f srcs', i.2)]
      ∧ (∀ j ∈ pre, IsLopn j)
      ∧ (∀ j ∈ pre, shadowCall? j.1 = none)
      ∧ srcs'.length = srcs.length
      ∧ runStraightF pre s'.prog.base s'.zf = some (b, s'.zf)
      ∧ argsRead (aa f) b 0 srcs' = argsRead (aa f) s.prog.base 0 srcs
      ∧ FrRel (freshRootsSel sel body) (retRes dst x s).prog.base
          (retRes dst x { prog := { base := b, lfn := s'.prog.lfn }, zf := s'.zf }).prog.base := by
  have hnm : ∀ o ∈ srcs, ∀ r ∈ opNames o, KeptF r := fun o ho r hr =>
    hkept r (by rw [hi]; simp only [callShadow, instrNames, List.flatMap_append,
      List.mem_append]; exact Or.inr (List.mem_flatMap.mpr ⟨o, ho, hr⟩))
  have hd : KeptF dst := hkept dst (by rw [hi]; simp [callShadow, instrNames, opNames])
  have hsh : shadowCall? i.1 = some (dst, f, srcs) := by rw [hi, shadowCall?_callShadow]
  unfold freshESel
  cases hsite : sel k i with
  | none =>
      refine ⟨[], srcs, s'.prog.base, by rw [List.nil_append, ← hi], by simp, by simp, rfl, rfl,
        argsRead_congr srcs srcs 0 rfl (fun j o o' h1 h2 => ?_), hQ.retRes (a' := s') hd x⟩
      rw [h1] at h2
      cases h2
      exact argRead_kept hQ.reg hQ.arr _ (hnm o (List.mem_of_getElem? h1))
  | some An =>
      obtain ⟨A, n⟩ := An
      obtain ⟨hn, ⟨dst', f', srcs0, p, hsh', hp, han, hA⟩ | ⟨hsh', -⟩ | ⟨hsh', -⟩⟩ :=
        hsel k i A n hsite
      · rw [hsh] at hsh'
        obtain ⟨rfl, rfl, rfl⟩ : dst = dst' ∧ f = f' ∧ srcs = srcs0 := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hsh'
          exact hsh'
        have hkA : KeptF A := hnm _ (List.mem_of_getElem? hA) A (by simp [opNames])
        have hrA := argRead_isSome_of_argsRead srcs 0 harg p _ hA
        rw [Nat.zero_add] at hrA
        simp only [argRead, han] at hrA
        obtain ⟨arr, harr⟩ := Option.isSome_iff_exists.mp
          (by simpa using hrA : (s.prog.base.getArr A 64 n).isSome)
        have harr' : s'.prog.base.getArr A 64 n = some arr := by
          unfold LstateM.getArr; rw [hQ.arr A hkA]; exact harr
        obtain ⟨u, hu, hcopy, huQ⟩ := frRel_resCopy hQ hkA ⟨i, A, hk, hsite⟩ hn harr' s'.zf
        have hp' : p < srcs.length := (List.getElem?_eq_some_iff.mp hA).1
        refine ⟨resCopyCode A (freshName k) n, srcs.set p (.reg (copyName (freshName k) n)), u,
          ?_, fun j hj => (resCopyCode_mem hj).1, fun j hj => (resCopyCode_mem hj).2,
          List.length_set, hu, argsRead_congr _ _ 0 List.length_set
            (fun j o o' h1 h2 => ?_), huQ.retRes (a := s) hd x⟩
        · unfold retarget
          rw [hsh]
          simp only [hp]
        · by_cases hjp : j = p
          · subst hjp
            rw [List.getElem?_set_self hp', Option.some.injEq] at h2
            rw [hA, Option.some.injEq] at h1
            subst h1 h2
            simp only [Nat.zero_add, argRead, han, hcopy, harr]
          · rw [List.getElem?_set_ne (Ne.symm hjp), h1] at h2
            cases h2
            exact argRead_kept huQ.reg huQ.arr _ (hnm o (List.mem_of_getElem? h1))
      · rw [hsh] at hsh'
        cases hsh'
      · rw [hsh] at hsh'
        cases hsh'

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (argsRead CallRes retRes) in
/-- **A call under the pass** at the sites `freshSite`: `freshESel_call` at the selector
    `freshSite σ L aa outs`. -/
theorem freshE_call (σ : String → String) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) {body : List LinstrRM}
    {k : Nat} {i : LinstrRM} (hk : body[k]? = some i)
    (hkept : ∀ r ∈ instrNames i.1, KeptF r) {s s' : LstateMF} {dst f : String}
    {srcs : List LOperand} (x : CallRes) (hi : i.1 = callShadow dst f srcs)
    (harg : (argsRead (aa f) s.prog.base 0 srcs).isSome)
    (hQ : FrRel (freshRoots σ L aa outs body) s.prog.base s'.prog.base) :
    ∃ (pre : List LinstrRM) (srcs' : List LOperand) (b : LstateM),
      freshE σ L aa outs k i = pre ++ [(callShadow dst f srcs', i.2)]
      ∧ (∀ j ∈ pre, IsLopn j)
      ∧ (∀ j ∈ pre, shadowCall? j.1 = none)
      ∧ srcs'.length = srcs.length
      ∧ runStraightF pre s'.prog.base s'.zf = some (b, s'.zf)
      ∧ argsRead (aa f) b 0 srcs' = argsRead (aa f) s.prog.base 0 srcs
      ∧ FrRel (freshRoots σ L aa outs body) (retRes dst x s).prog.base
          (retRes dst x { prog := { base := b, lfn := s'.prog.lfn }, zf := s'.zf }).prog.base :=
  freshESel_call aa outs (freshSite_ok σ L aa outs) hk hkept x hi harg hQ

/-- The expansion of one instruction is at most as long as the expanded body. -/
theorem length_e_le_expI (e : Nat → LinstrRM → List LinstrRM) {body : List LinstrRM}
    {k : Nat} {i : LinstrRM} (hk : body[k]? = some i) :
    (e k i).length ≤ (expI e body 0).length := by
  rw [expI_split e hk]
  simp only [List.length_append]
  omega

/-- **The run of the body freshened at a site rule.** Let `I` be an instruction set whose
    steps contain those of `x86Isa` and whose further steps are local calls at the array
    positions `aa`, each from a state at which its argument words are readable. Let the
    instructions of `body` be `Lopn`s or control instructions, contain no `MULX` and name kept
    names only, and let the site rule `site` select, at the coalescing renaming of `body`,
    sites of the three kinds only. Every halting run of `I` on `body` from the entry of the
    function `fn` is matched by a halting run of `I` on `freshenSel site L aa outs body` from
    every entry state with the same function name and zero flag that is related by `FrRel` at
    the fresh roots of the body; the final states are related in the same way and have equal
    zero flags. -/
theorem lsemFuelMemF_freshenSel {I : Isa} {ao : String → Option Nat} (site : SiteRule)
    (aa : String → Nat → Option Nat) (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hrd : ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF), I.step P i s = some t →
      ∀ (dst f : String) (srcs : List LOperand), i.1 = callShadow dst f srcs →
        (argsRead (aa f) s.prog.base 0 srcs).isSome)
    (L : Nat → List String) (outs : List (String × Nat)) {fn : String}
    {body : List LinstrRM} (hsel : SiteOK aa outs (site (chainAliasO outs body) L aa outs))
    (hcls : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → IsLopn i ∨ CtlI i)
    (hmx : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → mulxFree i = true)
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r)
    (fuel : Nat) {s s' t : LstateMF} (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (hpc : s.prog.base.lpc = 0) (hpc' : s'.prog.base.lpc = 0)
    (hQ : FrRel (freshRootsSel (site (chainAliasO outs body) L aa outs) body) s.prog.base
      s'.prog.base)
    (hrun : I.lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn (freshenSel site L aa outs body)) fuel' s'
        = some t'
      ∧ FrRel (freshRootsSel (site (chainAliasO outs body) L aa outs) body) t.prog.base
          t'.prog.base
      ∧ t'.zf = t.zf := by
  set sel := site (chainAliasO outs body) L aa outs
  have h := freshESel_expInv aa outs hsel hcls hmx hkept
  have hR : RelI (FrRel (freshRootsSel sel body)) (fun _ _ _ => True) (freshESel outs sel)
      body s s' := ⟨hfn, hz, by rw [hpc, hpc']; rfl, hQ, trivial⟩
  obtain ⟨fuel', t', -, hrun', hRt⟩ := lsemFuelMemF_expI_callsPre hle hcl h
    (fun k i _ hsh j hj P x => Isa.CallLocal.step_eq I hle hcl P (freshESel_noCall hsh j hj) x)
    (fun k i hk _ s0 s0' dst f srcs x hi _ _ _ hQ0 hx => by
      obtain ⟨pre, srcs', b, he, hlop, hnc, hlen, hrun0, hargs, hQ1⟩ :=
        freshESel_call aa outs hsel hk (hkept k i hk) x hi
          (hrd _ i s0 _ hx dst f srcs hi) hQ0
      exact ⟨pre, srcs', b, he, hlop,
        fun j hj P y => Isa.CallLocal.step_eq I hle hcl P (hnc j hj) y, hlen, hrun0, hargs,
        trivial, hQ1⟩)
    (fun k i hk => length_e_le_expI (freshESel outs sel) hk) fuel hR hrun
  exact ⟨fuel', t', hrun', hRt.base, hRt.zf⟩

/-- **The run of the freshened body.** Let `I` be an instruction set whose steps contain
    those of `x86Isa` and whose further steps are local calls at the array positions `aa`,
    each from a state at which its argument words are readable. Let the instructions of
    `body` be `Lopn`s or control instructions, contain no `MULX` and name kept names only
    (`KeptF`: neither `copyIdx`, `copyTmp` nor a name of the fresh family). Every halting
    run of `I` on `body` from the entry of the function `fn` is matched by a halting run of
    `I` on `freshenArr L aa outs body` from every entry state with the same function name and
    zero flag that is related by `FrRel` at the fresh roots of the body: the two bases agree
    on every kept register and array, on the word memory and on the flags, and each fresh
    root holds an array of its length. The final states are related in the same way and have
    equal zero flags. -/
theorem lsemFuelMemF_freshenArr {I : Isa} {ao : String → Option Nat}
    (aa : String → Nat → Option Nat) (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao)
    (hrd : ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF), I.step P i s = some t →
      ∀ (dst f : String) (srcs : List LOperand), i.1 = callShadow dst f srcs →
        (argsRead (aa f) s.prog.base 0 srcs).isSome)
    (L : Nat → List String) (outs : List (String × Nat)) {fn : String}
    {body : List LinstrRM}
    (hcls : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → IsLopn i ∨ CtlI i)
    (hmx : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → mulxFree i = true)
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r)
    (fuel : Nat) {s s' t : LstateMF} (hfn : s'.prog.lfn = s.prog.lfn) (hz : s'.zf = s.zf)
    (hpc : s.prog.base.lpc = 0) (hpc' : s'.prog.base.lpc = 0)
    (hQ : FrRel (freshRoots (chainAliasO outs body) L aa outs body) s.prog.base s'.prog.base)
    (hrun : I.lsemFuelMemF (singletonProgM fn body) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn (freshenArr L aa outs body)) fuel' s'
        = some t'
      ∧ FrRel (freshRoots (chainAliasO outs body) L aa outs body) t.prog.base t'.prog.base
      ∧ t'.zf = t.zf :=
  lsemFuelMemF_freshenSel freshSite aa hle hcl hrd L outs (freshSite_ok _ L aa outs) hcls hmx
    hkept fuel hfn hz hpc hpc' hQ hrun

end Run

/-! ## 9. The coalescing renaming of the freshened body -/

section Alias

open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (callShadow shadowCall?
  shadowCall?_callShadow)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)

/-- A version after the first word of a copy differs from the copied-into name. -/
theorem copyName_succ_ne (D : String) (j : Nat) : copyName D (j + 1) ≠ D := by
  intro h
  have := congrArg String.length h
  have h2 : ("#c" : String).length = 2 := by decide
  simp only [copyName, Nat.add_one_ne_zero, ite_false, String.length_append, h2] at this
  omega

/-- The destination of a shadow instruction of a call is a name it writes. -/
theorem dst_mem_of_shadowCall {w : LinstrR} {dst f : String} {srcs : List LOperand}
    (h : shadowCall? w = some (dst, f, srcs)) : dst ∈ dstNames w := by
  unfold shadowCall? at h
  split at h
  · split at h
    · cases h; simp [dstNames, JasminLsemExportRewrites.opNames]
    · cases h
  · cases h

/-- An alias step keeps the image of every name the instruction does not write. -/
theorem getD_aliasStepO (outs : List (String × Nat)) (M : Std.HashMap String String)
    {i : LinstrRM} {r : String} (hr : r ∉ dstNames i.1) :
    (aliasStepO outs M i).getD r r = M.getD r r := by
  obtain ⟨w, tag⟩ := i
  unfold aliasStepO
  split
  · rename_i dst f srcs hsh
    have hne : (dst == r) = false := by
      simp only [beq_eq_false_iff_ne]
      rintro rfl
      exact hr (dst_mem_of_shadowCall hsh)
    repeat' split
    all_goals first | rfl | (rw [Std.HashMap.getD_insert, hne]; rfl)
  · split
    · rename_i dst opn base x sc rest hw
      simp only at hw
      subst hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by simp [dstNames, JasminLsemExportRewrites.opNames])
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rename_i dst opn base rest hw
      simp only at hw
      subst hw
      split
      · have hne : (dst == r) = false := by
          simp only [beq_eq_false_iff_ne]
          rintro rfl
          exact hr (by simp [dstNames, JasminLsemExportRewrites.opNames])
        rw [Std.HashMap.getD_insert, hne]
        rfl
      · rfl
    · rfl

/-- The alias step of a store `STOREIDX d, [b]` sends `d` to the image of `b`. -/
theorem aliasStepO_store (outs : List (String × Nat)) (M : Std.HashMap String String)
    (d b x v : String) (sc : Nat) (tag : MemTag) :
    aliasStepO outs M (.Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v], tag)
      = M.insert d (M.getD b b) := by
  simp [aliasStepO, shadowCall?, isMemStore]

/-- **The alias map over the array copy.** After the first `k` words of the copy into `D`,
    every version `copyName D j`, `j ≤ k`, has the image of `D` in the map before the copy. -/
theorem getD_foldl_resCopy (outs : List (String × Nat)) (src D : String) (n : Nat)
    (M : Std.HashMap String String) :
    ∀ k j, j ≤ k →
      (((List.range k).flatMap (resCopyStep src D n)).foldl (aliasStepO outs) M).getD
        (copyName D j) (copyName D j) = M.getD D D := by
  intro k
  induction k with
  | zero =>
      intro j hj
      obtain rfl : j = 0 := by omega
      simp [copyName]
  | succ k ih =>
      intro j hj
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
      generalize hM1 : ((List.range k).flatMap (resCopyStep src D n)).foldl (aliasStepO outs) M
        = M1 at ih
      have hmov : aliasStepO outs M1 (movImmI copyIdx k) = M1 := by
        simp [aliasStepO, movImmI, ExportRegions.movI, shadowCall?, withWidthTag]
      have hld : aliasStepO outs M1
          (.Lopn [.reg copyTmp] "LOADIDX" [.arrIdx src copyIdx 8], .load 64 n) = M1 := by
        simp [aliasStepO, shadowCall?, isMemStore]
      simp only [resCopyStep, List.foldl_cons, List.foldl_nil, hmov, hld, aliasStepO_store,
        Std.HashMap.getD_insert]
      split
      · rename_i heq
        rw [ih k (le_refl k)]
      · exact ih j (by
          rcases Nat.lt_or_ge j (k + 1) with h | h
          · omega
          · exfalso
            rename_i hne
            obtain rfl : j = k + 1 := by omega
            exact hne (by simp))

/-- An alias fold keeps the image of a name no instruction of the list writes. -/
theorem getD_foldl_aliasStepO (outs : List (String × Nat)) {r : String} :
    ∀ (xs : List LinstrRM) (M : Std.HashMap String String), (∀ j ∈ xs, r ∉ dstNames j.1) →
      (xs.foldl (aliasStepO outs) M).getD r r = M.getD r r
  | [], _, _ => rfl
  | j :: xs, M, h => by
      rw [List.foldl_cons, getD_foldl_aliasStepO outs xs _ (fun j' hj' => h j' (by simp [hj'])),
        getD_aliasStepO outs M (h j (by simp))]

/-- The alias step of a store `STOREIMM d, [b]` sends `d` to the image of `b`. -/
theorem aliasStepO_storeImm (outs : List (String × Nat)) (M : Std.HashMap String String)
    (d b v : String) (c : Nat) (tag : MemTag) :
    aliasStepO outs M (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm c], tag)
      = M.insert d (M.getD b b) := by
  simp [aliasStepO, shadowCall?]

/-- **The alias map at a site under a site selector.** Over the expansion of a site of a
    selector of sites of the three kinds with the fresh root `freshName k`, from an alias map
    that fixes the fresh root, the destination of the store or of the call is sent to the
    fresh root. -/
theorem getD_foldl_freshESel {aa : String → Nat → Option Nat} {outs : List (String × Nat)}
    {sel : Nat → LinstrRM → Option (String × Nat)} (hsel : SiteOK aa outs sel) {k : Nat}
    {i : LinstrRM} {A : String} {n : Nat} (hsite : sel k i = some (A, n))
    (M : Std.HashMap String String) (hM : M.getD (freshName k) (freshName k) = freshName k) :
    ∀ d, d ∈ dstNames i.1 →
      ((freshESel outs sel k i).foldl (aliasStepO outs) M).getD d d = freshName k := by
  intro d hd
  have hcopy : ((resCopyCode A (freshName k) n).foldl (aliasStepO outs) M).getD
      (copyName (freshName k) n) (copyName (freshName k) n) = freshName k := by
    rw [resCopyCode, getD_foldl_resCopy outs A (freshName k) n M n n (le_refl n), hM]
  unfold freshESel
  rw [hsite, List.foldl_append]
  generalize ((resCopyCode A (freshName k) n).foldl (aliasStepO outs) M) = M' at hcopy
  obtain ⟨-, ⟨dst, f, srcs, p, hsh, hp, -, hA⟩ | ⟨hsh, -, d', x, v, hst⟩
    | ⟨hsh, -, d', v, c, hst⟩⟩ := hsel k i A n hsite
  · have hdd : d = dst := by
      obtain ⟨dst', opn, srcs', hw, -⟩ := LprogIsaProcs.shadowCall?_wire
        (by rw [hsh]; exact Option.some_ne_none _)
      rw [hw] at hd hsh
      simp only [dstNames, JasminLsemExportRewrites.opNames, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_singleton] at hd
      have := dst_mem_of_shadowCall hsh
      simp only [dstNames, JasminLsemExportRewrites.opNames, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_singleton] at this
      rw [hd, this]
    subst hdd
    have hp' : p < srcs.length := (List.getElem?_eq_some_iff.mp hA).1
    have hret : retarget outs (copyName (freshName k) n) i
        = (callShadow d f (srcs.set p (.reg (copyName (freshName k) n))), i.2) := by
      unfold retarget
      rw [hsh]
      simp only [hp]
    rw [hret]
    simp only [List.foldl_cons, List.foldl_nil, aliasStepO, shadowCall?_callShadow, hp,
      List.getElem?_set_self hp', Std.HashMap.getD_insert, beq_self_eq_true, ite_true, hcopy]
  · obtain ⟨sc, hw⟩ := storeStruct?_eq_some hst
    have hdd : d = d' := by
      rw [hw] at hd
      simpa [dstNames, JasminLsemExportRewrites.opNames] using hd
    subst hdd
    have hret : retarget outs (copyName (freshName k) n) i
        = (.Lopn [.reg d] "STOREIDX" [.arrIdx (copyName (freshName k) n) x sc, .reg v], i.2) := by
      unfold retarget
      rw [hsh]
      simp only [hw]
    rw [hret]
    simp only [List.foldl_cons, List.foldl_nil, aliasStepO_store, Std.HashMap.getD_insert,
      beq_self_eq_true, ite_true, hcopy]
  · have hw := storeImmStruct?_eq_some hst
    have hdd : d = d' := by
      rw [hw] at hd
      simpa [dstNames, JasminLsemExportRewrites.opNames] using hd
    subst hdd
    have hret : retarget outs (copyName (freshName k) n) i
        = (.Lopn [.reg d] "STOREIMM" [.reg (copyName (freshName k) n), .reg v, .imm c], i.2) := by
      unfold retarget
      rw [hsh]
      simp only [hw, ite_true]
    rw [hret]
    simp only [List.foldl_cons, List.foldl_nil, aliasStepO_storeImm, Std.HashMap.getD_insert,
      beq_self_eq_true, ite_true, hcopy]

/-- **The alias map at a site.** Over the expansion of a site with the fresh root
    `freshName k`, from an alias map that fixes the fresh root, the destination of the store or
    of the call is sent to the fresh root. -/
theorem getD_foldl_freshE {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i : LinstrRM}
    {A : String} {n : Nat} (hsite : freshSite σ L aa outs k i = some (A, n))
    (M : Std.HashMap String String) (hM : M.getD (freshName k) (freshName k) = freshName k) :
    ∀ d, d ∈ dstNames i.1 →
      ((freshE σ L aa outs k i).foldl (aliasStepO outs) M).getD d d = freshName k :=
  getD_foldl_freshESel (freshSite_ok σ L aa outs) hsite M hM

/-- An instruction of an expanded body is in the expansion of an instruction of the body. -/
theorem mem_expI (e : Nat → LinstrRM → List LinstrRM) {j : LinstrRM} :
    ∀ (xs : List LinstrRM) (n0 : Nat), j ∈ expI e xs n0 →
      ∃ t i', xs[t]? = some i' ∧ j ∈ e (n0 + t) i'
  | [], _, h => by simp [expI] at h
  | i :: xs, n0, h => by
      rw [expI, List.mem_append] at h
      rcases h with h | h
      · exact ⟨0, i, rfl, by simpa using h⟩
      · obtain ⟨t, i', ht, hj⟩ := mem_expI e xs (n0 + 1) h
        exact ⟨t + 1, i', by simpa using ht, by rwa [show n0 + (t + 1) = n0 + 1 + t by omega]⟩

/-- The names the retargeted instruction writes are those of the instruction. -/
theorem dstNames_retarget (outs : List (String × Nat)) (F : String) (i : LinstrRM) :
    dstNames (retarget outs F i).1 = dstNames i.1 := by
  unfold retarget
  split
  · rename_i dst f srcs hsh
    split
    · obtain ⟨dst', opn, srcs', hw, -⟩ := LprogIsaProcs.shadowCall?_wire
        (by rw [hsh]; exact Option.some_ne_none _)
      have := dst_mem_of_shadowCall hsh
      rw [hw] at this ⊢
      simp only [dstNames, JasminLsemExportRewrites.opNames, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_singleton] at this
      simp [callShadow, dstNames, JasminLsemExportRewrites.opNames, this]
    · rfl
  · split
    · rename_i hw
      simp only at hw ⊢
      rw [hw]
      rfl
    · rename_i hw
      split
      · simp only at hw ⊢
        rw [hw]
        rfl
      · rfl
    · rfl

/-- The names an instruction of the expansion of `i` at `k` under a site selector writes:
    names `i` writes, the registers of the copy, and versions after the first word of the copy
    into `freshName k`. -/
theorem dstNames_freshESel {outs : List (String × Nat)}
    {sel : Nat → LinstrRM → Option (String × Nat)} {k : Nat} {i j : LinstrRM}
    (hj : j ∈ freshESel outs sel k i) {r : String} (hr : r ∈ dstNames j.1) :
    r ∈ dstNames i.1 ∨ r = copyIdx ∨ r = copyTmp ∨ ∃ t, r = copyName (freshName k) (t + 1) := by
  unfold freshESel at hj
  split at hj
  · rename_i A n hsite
    rcases List.mem_append.mp hj with h | h
    · simp only [resCopyCode, List.mem_flatMap, resCopyStep, List.mem_cons, List.not_mem_nil,
        or_false] at h
      obtain ⟨t, _, h | h | h⟩ := h <;> subst h
      · right; left
        simpa [dstNames, JasminLsemExportRewrites.opNames, movImmI, ExportRegions.movI] using hr
      · right; right; left
        simpa [dstNames, JasminLsemExportRewrites.opNames] using hr
      · right; right; right
        exact ⟨t, by simpa [dstNames, JasminLsemExportRewrites.opNames] using hr⟩
    · rw [List.mem_singleton.mp h, dstNames_retarget] at hr
      exact Or.inl hr
  · rw [List.mem_singleton.mp hj] at hr
    exact Or.inl hr

/-- The names an instruction of the expansion of `i` at `k` writes: names `i` writes, the
    registers of the copy, and versions after the first word of the copy into `freshName k`. -/
theorem dstNames_freshE {σ : String → String} {L : Nat → List String}
    {aa : String → Nat → Option Nat} {outs : List (String × Nat)} {k : Nat} {i j : LinstrRM}
    (hj : j ∈ freshE σ L aa outs k i) {r : String} (hr : r ∈ dstNames j.1) :
    r ∈ dstNames i.1 ∨ r = copyIdx ∨ r = copyTmp ∨ ∃ t, r = copyName (freshName k) (t + 1) :=
  dstNames_freshESel hj hr

/-- An alias fold keeps the image `v` of a name `r` when every instruction of the list keeps
    it. -/
theorem getD_foldl_aliasStepO_inv (outs : List (String × Nat)) {r v : String} :
    ∀ (xs : List LinstrRM) (M : Std.HashMap String String),
      (∀ j ∈ xs, ∀ M' : Std.HashMap String String, M'.getD r r = v →
        (aliasStepO outs M' j).getD r r = v) →
      M.getD r r = v → (xs.foldl (aliasStepO outs) M).getD r r = v
  | [], _, _, hM => hM
  | j :: xs, M, h, hM => by
      rw [List.foldl_cons]
      exact getD_foldl_aliasStepO_inv outs xs _ (fun j' hj' => h j' (by simp [hj']))
        (h j (by simp) M hM)

/-- A fresh root is neither register of the copy. -/
theorem freshName_ne_copyRegs (k : Nat) : freshName k ≠ copyIdx ∧ freshName k ≠ copyTmp := by
  constructor <;> intro h <;> have := congrArg (fun s : String => s.toList.head?) h <;>
    simp [freshName, copyIdx, copyTmp] at this

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames) in
/-- **A carried chain of the freshened body has the fresh root.** Let the instruction `i` at
    position `k` of a body with kept names be a site of the site rule `site`, which selects
    sites of the three kinds only, and let `d` be a destination of `i`. Let every later
    instruction that writes `d` be no site and keep the image `freshName k` of `d` in every
    alias map (an in-place store into `d` from `d`, or an instruction outside the alias steps,
    such as a move on a back edge). The coalescing renaming of the freshened body sends `d` to
    the fresh root `freshName k`. -/
theorem chainAliasO_freshenSel_carried (site : SiteRule) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) {body : List LinstrRM}
    {k : Nat} {i : LinstrRM} {A : String} {n : Nat}
    (hsel : SiteOK aa outs (site (chainAliasO outs body) L aa outs))
    (hk : body[k]? = some i)
    (hsite : site (chainAliasO outs body) L aa outs k i = some (A, n))
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r)
    {d : String} (hd : d ∈ dstNames i.1)
    (hcar : ∀ (k' : Nat) (i' : LinstrRM), body[k']? = some i' → k < k' → d ∈ dstNames i'.1 →
      site (chainAliasO outs body) L aa outs k' i' = none
        ∧ ∀ M : Std.HashMap String String, M.getD d d = freshName k →
          (aliasStepO outs M i').getD d d = freshName k) :
    chainAliasO outs (freshenSel site L aa outs body) d = freshName k := by
  set sel := site (chainAliasO outs body) L aa outs
  set e := freshESel outs sel
  have hdk : KeptF d := hkept k i hk d (JasminLsemStepFrame.dstNames_sub hd)
  unfold chainAliasO canonMemrefName freshenSel
  rw [JasminLsemFuseMulHi.expI_split e hk, List.foldl_append, List.foldl_append]
  refine getD_foldl_aliasStepO_inv outs _ _ ?suf ?mid
  case suf =>
    intro j hj M' hM'
    obtain ⟨t, i', ht, hj'⟩ := mem_expI e _ _ hj
    rw [List.getElem?_drop] at ht
    by_cases hdj : d ∈ dstNames j.1
    · rcases dstNames_freshESel hj' hdj with h | h | h | ⟨t', h⟩
      · obtain ⟨hnone, hpres⟩ := hcar _ i' ht (by omega) h
        have hji : j = i' := by
          grind only [freshESel, = List.mem_cons, ← List.not_mem_nil]
        subst hji
        exact hpres M' hM'
      · exact absurd h hdk.1
      · exact absurd h hdk.2.1
      · exact absurd h (hdk.ne_copy _ _)
    · rw [getD_aliasStepO outs M' hdj, hM']
  case mid =>
    refine getD_foldl_freshESel hsel hsite _ ?_ d hd
    rw [getD_foldl_aliasStepO outs _ _ ?pre]
    case pre =>
      intro j hj hdj
      obtain ⟨t, i', ht, hj'⟩ := mem_expI e _ _ hj
      have ht' : body[t]? = some i' := by
        rw [List.getElem?_take] at ht
        split at ht
        · exact ht
        · cases ht
      rcases dstNames_freshESel hj' hdj with h | h | h | ⟨t', h⟩
      · exact (hkept t i' ht' _ (JasminLsemStepFrame.dstNames_sub h)).2.2
          (freshFam_freshName k)
      · exact (freshName_ne_copyRegs k).1 h
      · exact (freshName_ne_copyRegs k).2 h
      · exact copyName_fresh_ne _ t' k h.symm
    simp

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames) in
/-- **The freshened chain has its own root.** Let the instruction `i` at position `k` of a
    body with kept names be a site, and let its destination `d` be written by no other
    instruction of the body. The coalescing renaming of the freshened body sends `d` to the
    fresh root `freshName k`. -/
theorem chainAliasO_freshenArr (L : Nat → List String) (aa : String → Nat → Option Nat)
    (outs : List (String × Nat)) {body : List LinstrRM} {k : Nat} {i : LinstrRM} {A : String}
    {n : Nat} (hk : body[k]? = some i)
    (hsite : freshSite (chainAliasO outs body) L aa outs k i = some (A, n))
    (hkept : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ r ∈ instrNames i.1, KeptF r)
    {d : String} (hd : d ∈ dstNames i.1)
    (honce : ∀ (k' : Nat) (i' : LinstrRM), body[k']? = some i' → k' ≠ k → d ∉ dstNames i'.1) :
    chainAliasO outs (freshenArr L aa outs body) d = freshName k :=
  chainAliasO_freshenSel_carried freshSite L aa outs (freshSite_ok _ L aa outs) hk hsite hkept
    hd (fun k' i' hk' hlt hdi => absurd hdi (honce k' i' hk' (by omega)))

end Alias

/-! ## 10. No site -/

/-- An expansion that leaves every instruction of a list as it is leaves the list as it
    is. -/
theorem expI_eq_self (e : Nat → LinstrRM → List LinstrRM) :
    ∀ (xs : List LinstrRM) (n0 : Nat), (∀ t i, xs[t]? = some i → e (n0 + t) i = [i]) →
      expI e xs n0 = xs
  | [], _, _ => rfl
  | i :: xs, n0, h => by
      have h0 := h 0 i rfl
      rw [Nat.add_zero] at h0
      rw [expI, h0, expI_eq_self e xs (n0 + 1) (fun t j hj => by
        rw [show n0 + 1 + t = n0 + (t + 1) by omega]
        exact h (t + 1) j (by simpa using hj))]
      rfl

/-- **No site, no change.** A body at which the site rule `site` selects no instruction is
    its own freshening. -/
theorem freshenSel_eq_self (site : SiteRule) (L : Nat → List String)
    (aa : String → Nat → Option Nat) (outs : List (String × Nat)) {body : List LinstrRM}
    (h : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i →
      site (chainAliasO outs body) L aa outs k i = none) :
    freshenSel site L aa outs body = body :=
  expI_eq_self _ body 0 (fun t i ht => by
    unfold freshESel
    rw [Nat.zero_add, h t i ht])

end CatCrypt.Crypto.SecureCompilation.X86Backend.FreshenArr
