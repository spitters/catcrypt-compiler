/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.FrameFuelMemF
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaRelocX86
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCall
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg

/-!
# The frame expansion of a body with labels and jumps on the flag machine

The ABI export `JasminLprogExport.lfundefPhysAbiOfVirtCert` places the allocated body between
a prologue of register copies (`buildPrologue`, the saves `extraInputSaves` of the third and
later argument registers, the argument materialisation) and the restore
`calleeSaveRestoreEpilogue` before the final `Lret`. The flag machine `lsemFuelMemF` takes no
step at `Lret`, so a halting run of the framed function is a run of
`pre ++ B ++ calleeSaveRestoreEpilogue`, where `B` is the body without its return.

This module lifts `frame_runStraightF` from straight bodies to bodies with labels,
conditional jumps on the zero flag and gotos: a halting run of `B` from a base agreeing off
the scratches and the save slots with the base after `pre` is matched by a halting run of the
framed body from the entry base. The run of `B` is matched in place by the identity expansion
of `JasminLsemExportLower.lsemFuelMemF_expand` at the relation `FrameQ`, which also carries
the contents of the save slots, and is then relocated behind `pre` and in front of the restore
by `Ascent.IsaCall.x86_steps_relocate`.

## Main definitions

* `extraInputSaves`: the saves of the third and later argument registers.
* `keptFB`, `frameInstrOKB`: the Boolean checks of a kept name and of an instruction the
  frame expansion covers.
* `FrameQ`: agreement on the kept names, with the save slots of the target holding fixed
  values.

## Main results

* `extraInputSaves_copies`, `copyRunL_prologue_qsave`: the further saves are register copies,
  and the prologue with them saves each callee-saved register to its slot.
* `instrOK_frame`, `lsemFuelMemF_frameQ`: an accepted body runs under `FrameQ`.
* `lsemFuelMemF_end_lpc`: a halting run that ends at or before the end of a body ends at its
  end.
* `lsemFuelMemF_of_steps_add`: a segment of steps followed by a run is a run.
* `frame_lsemFuelMemF`: the frame expansion of a body with labels and jumps.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrameFuelMemF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg (Steps goto lsemFuelMemF_stepI)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (shiftPc LabelsFresh labelsFreshB
  labelsFresh_of_labelsFreshB x86_steps_relocate steps_of_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)

/-! ## 1. The saves of the further argument registers -/

/-- The saves of the third and later argument registers that `lfundefPhysAbiOfVirtCert`
    appends to `buildPrologue`: the copy of each register of `extraSaveRegs abiArgs` to its
    save slot `abiSaveOfExt`. -/
def extraInputSaves (abiArgs : List String) : Lcmd :=
  (extraSaveRegs abiArgs).filterMap (fun abiReg =>
    match abiSaveOfExt abiReg with
    | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
    | none => none)

/-- **The further saves are register copies.** -/
theorem extraInputSaves_copies (abiArgs : List String) :
    ∀ i ∈ extraInputSaves abiArgs, IsCopyQ i.li_i := by
  intro i hi
  simp only [extraInputSaves, List.mem_filterMap] at hi
  obtain ⟨r, -, hi⟩ := hi
  unfold IsCopyQ
  grind

/-- A list of register copies followed by a list runs through the base after the copies. -/
theorem copyRunL_append : ∀ (l₁ l₂ : Lcmd), (∀ i ∈ l₁, IsCopyQ i.li_i) → ∀ a,
    copyRunL (l₁ ++ l₂) a = copyRunL l₂ (copyRunL l₁ a) := by
  intro l₁ l₂
  induction l₁ with
  | nil => intro _ a; rfl
  | cons i l ih =>
      intro h a
      obtain ⟨d, s, hds⟩ := h i (List.mem_cons_self ..)
      obtain ⟨ii, w⟩ := i
      simp only at hds
      subst hds
      exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

/-- The save slot of every argument register is one of six names. -/
theorem abiSaveOfExt_mem {r n : String} (h : abiSaveOfExt r = some n) :
    n ∈ ["qsave.RDI", "qsave.RSI", "qsave.RDX", "qsave.RCX", "qsave.R8", "qsave.R9"] := by
  unfold abiSaveOfExt abiSaveOf at h
  grind [abiSaveRdiName, abiSaveRsiName]

/-- The further saves write no slot of a callee-saved register. -/
theorem qsave_not_mem_copyDsts_extraInputSaves (abiArgs : List String) {X : String}
    (hX : X ∈ calleeSaved6) : "qsave." ++ X ∉ copyDsts (extraInputSaves abiArgs) := by
  intro hm
  simp only [copyDsts, List.mem_flatMap, extraInputSaves, List.mem_filterMap] at hm
  obtain ⟨i, ⟨r, -, hi⟩, hd⟩ := hm
  cases hs : abiSaveOfExt r with
  | none => simp [hs] at hi
  | some n =>
      simp only [hs, Option.some.injEq] at hi
      subst hi
      simp only [List.mem_singleton] at hd
      have hn := abiSaveOfExt_mem hs
      rw [← hd] at hn
      simp only [calleeSaved6, List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hn

/-- **The prologue with the further saves saves each callee-saved register to its slot.** -/
theorem copyRunL_prologue_qsave (v : Lfundef) (tbl : Array Nat) (m : InLoadMap)
    (abiArgs : List String) (a : LstateM) {X : String} (hX : X ∈ calleeSaved6) :
    (copyRunL (buildPrologue v tbl m ++ extraInputSaves abiArgs) a).reg.lvm ("qsave." ++ X)
      = a.reg.lvm X := by
  rw [copyRunL_append _ _ (buildPrologue_copies v tbl m),
    copyRunL_lvm_of_not_mem _ _ (qsave_not_mem_copyDsts_extraInputSaves abiArgs hX)]
  exact copyRunL_buildPrologue_qsave v tbl m a hX

/-- The prologue with the further saves is a list of register copies. -/
theorem prologue_copies (v : Lfundef) (tbl : Array Nat) (m : InLoadMap)
    (abiArgs : List String) :
    ∀ i ∈ buildPrologue v tbl m ++ extraInputSaves abiArgs, IsCopyQ i.li_i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact buildPrologue_copies v tbl m i hi
  · exact extraInputSaves_copies abiArgs i hi

/-! ## 2. The accepted bodies -/

/-- The Boolean check of a kept name: neither reload scratch and no save slot `qsave.<R>`. -/
def keptFB (n : String) : Bool :=
  n != reloadScratch && n != reloadScratch2 && !("qsave.".toList.isPrefixOf n.toList)

/-- A name passing `keptFB` is kept. -/
theorem keptF_of_keptFB {n : String} (h : keptFB n = true) : KeptF n := by
  simp only [keptFB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  refine ⟨⟨h.1.1, h.1.2⟩, ?_⟩
  rintro ⟨x, rfl⟩
  have hp : "qsave.".toList.isPrefixOf ("qsave." ++ x).toList = true := by
    rw [String.toList_append, List.isPrefixOf_iff_prefix]
    exact List.prefix_append _ _
  rw [hp] at h
  exact absurd h.2 (by decide)

/-- The instructions the frame expansion covers: an `Lopn` other than `LIVEPIN` and `MULX`
    that names only kept names, a label, a conditional on the zero flag, or a goto. A body
    passing this check contains no `Lret`, no `Lcall`, no `LIVEPIN` and, since `R14` is a
    reload scratch, no reload of an array base into `R14`. -/
def frameInstrOKB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ o _ => o != "LIVEPIN" && mulxFree i && (instrNames i.1).all keptFB
  | .Llabel _ _ => true
  | .Lcond _ _ => (flagCondCC? i).isSome
  | .Lgoto _ => true
  | _ => false

/-- Agreement on the kept names, with the save slots `qsave.X` of the callee-saved registers
    `X` of the second base holding their values in `c`. -/
def FrameQ (c : LstateM) (a b : LstateM) : Prop :=
  AgreeK KeptF a b ∧ ∀ X ∈ calleeSaved6, b.reg.lvm ("qsave." ++ X) = c.reg.lvm ("qsave." ++ X)

/-- **An accepted instruction is simulated by itself under `FrameQ`.** -/
theorem instrOK_frame (c : LstateM) {i : LinstrRM} (h : frameInstrOKB i = true) :
    InstrOK (FrameQ c) (fun j => [j]) i := by
  obtain ⟨w, τ⟩ := i
  cases w with
  | Lopn ds o ss =>
      simp only [frameInstrOKB, Bool.and_eq_true, List.all_eq_true] at h
      have hl : IsLopn (LinstrR.Lopn ds o ss, τ) := ⟨_, _, _, rfl⟩
      have hn : ∀ n ∈ instrNames (LinstrR.Lopn ds o ss, τ).1, KeptF n :=
        fun n hn => keptF_of_keptFB (h.2 n hn)
      refine Or.inl ⟨hl, fun j hj => by rw [List.mem_singleton.mp hj]; exact hl,
        fun s s' t zf zt hQ hst => ?_⟩
      obtain ⟨t', ht', hA⟩ := fstepF_agreeK keptF_empty hl hn h.1.2 hQ.1 hst
      refine ⟨t', by rw [JasminLsemAddrMem.runStraightF_singleton]; exact ht', hA,
        fun X hX => ?_⟩
      rw [(JasminLsemStepFrame.fstepF_frame ht' (fun hm => (hn _ hm).2 ⟨X, rfl⟩)).1]
      exact hQ.2 X hX
  | Llabel kd l => exact Or.inr ⟨rfl, Or.inl ⟨kd, l, rfl⟩⟩
  | Lcond c' l =>
      refine Or.inr ⟨rfl, Or.inr (Or.inl ⟨c', l, rfl, ?_⟩)⟩
      exact Option.isSome_iff_ne_none.mp h
  | Lgoto tgt => exact Or.inr ⟨rfl, Or.inr (Or.inr ⟨tgt, rfl⟩)⟩
  | _ => simp [frameInstrOKB] at h

/-- **An accepted body runs under `FrameQ`.** A halting run of an accepted body from the
    start is matched, with at most the same fuel, by a halting run of the same body from a
    base related by `FrameQ c`, into a related base with the same function name and zero
    flag. -/
theorem lsemFuelMemF_frameQ (c : LstateM) {B : List LinstrRM}
    (hB : B.all frameInstrOKB = true) (fn : String) {fuel : Nat} {s s' t : LstateMF}
    (hQ : FrameQ c s.prog.base s'.prog.base) (hfn : s'.prog.lfn = s.prog.lfn)
    (hz : s'.zf = s.zf) (hpc : s.prog.base.lpc = 0) (hpc' : s'.prog.base.lpc = 0)
    (h : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel ∧ lsemFuelMemF (singletonProgM fn B) fuel' s' = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf ∧ t'.prog.base.lpc ≤ B.length
      ∧ FrameQ c t.prog.base t'.prog.base := by
  have hP : ExpProg (FrameQ c) (fun j => [j]) (singletonProgM fn B) (singletonProgM fn B) :=
    ⟨rfl, by simp [singletonProgM],
      fun k i hk => instrOK_frame c (List.all_eq_true.mp hB i (List.mem_of_getElem? hk)),
      fun _ _ _ _ hab => ⟨⟨hab.1.reg, hab.1.arr, hab.1.mem, hab.1.cf, hab.1.of⟩, hab.2⟩⟩
  have hR : RelX (FrameQ c) (fun j => [j]) (singletonProgM fn B) s s' :=
    ⟨hfn, hz, by rw [hpc, hpc', pcMap_zero], hQ⟩
  obtain ⟨f', t', hle, hrun, hRt⟩ :=
    lsemFuelMemF_expand hP (m := 1) (fun _ _ => le_refl _) fuel hR h
  refine ⟨f', t', by simpa using hle, hrun, hRt.lfn, hRt.zf, ?_, hRt.base⟩
  rw [hRt.pc]
  simp [pcMap, singletonProgM]

/-! ## 3. Runs inside a larger body -/

/-- **A halting run that ends inside a body or at its end ends at its end**, in the function
    of the body. -/
theorem lsemFuelMemF_end_lpc {fn : String} {B : List LinstrRM} {fuel : Nat} {s t : LstateMF}
    (hfn : s.prog.lfn = fn) (hle : t.prog.base.lpc ≤ B.length)
    (h : lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    t.prog.lfn = fn ∧ t.prog.base.lpc = B.length := by
  obtain ⟨hl, hf⟩ := LprogGpReallocCfg.lsemFuelMemF_end fuel h
  refine ⟨hl.trans hfn, ?_⟩
  unfold findInstrMem at hf
  rw [ite_eq_left (show t.prog.lfn = (singletonProgM fn B).lfn from hl.trans hfn)] at hf
  have := List.getElem?_eq_none_iff.mp hf
  simp only [singletonProgM] at this hle
  omega

/-- A run of `n` steps followed by a run with fuel `k` is a run with fuel `n + k`. -/
theorem lsemFuelMemF_of_steps_add (isa : Isa) (P : LprogM) :
    ∀ (n : Nat) {s t : LstateMF}, Steps isa P n s t →
      ∀ k, isa.lsemFuelMemF P (n + k) s = isa.lsemFuelMemF P k t
  | 0, s, t, h, k => by
      have hst : s = t := Option.some.inj h
      subst hst
      simp
  | n + 1, s, t, h, k => by
      simp only [Steps, Ascent.CutPoint.iter, Option.bind_eq_some_iff] at h
      obtain ⟨u, hu, h⟩ := h
      rw [show n + 1 + k = (n + k) + 1 by omega, lsemFuelMemF_stepI isa P _ s u hu]
      exact lsemFuelMemF_of_steps_add isa P n h k

/-- No label of a body is declared in a prefix of `Lopn`s. -/
theorem labelsFresh_of_isLopn {pre B : List LinstrRM} (h : ∀ i ∈ pre, IsLopn i) :
    LabelsFresh pre B := by
  refine labelsFresh_of_labelsFreshB (List.all_eq_true.mpr fun i hi => ?_)
  obtain ⟨d, o, s, hd⟩ := h i hi
  simp [hd]

/-- A typed list of register copies is a list of `Lopn`s. -/
theorem isLopn_of_copies (tg : LinstrR → MemTag) {l : Lcmd} (hl : ∀ i ∈ l, IsCopyQ i.li_i) :
    ∀ i ∈ l.map (fun i => (i.li_i, tg i.li_i)), IsLopn i := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨d, s, hds⟩ := hl j hj
  exact ⟨_, _, _, hds⟩

/-! ## 4. The frame of a body with labels and jumps -/

/-- **The frame expansion of a body with labels and jumps.** Let the body `B` pass
    `frameInstrOKB` at every instruction, and let `pre` (the prologue, the further saves and
    the argument materialisation) be a list of register copies. When `B` halts from a base `s`
    at program counter `0` agreeing off the scratches and the save slots with the base after
    `pre` from the entry base `e` at program counter `0`, the framed body
    `pre ++ B ++ calleeSaveRestoreEpilogue` halts from `e` with the same zero flag, with at
    most the fuel of the run of `B` plus the lengths of `pre` and of the restore, in a state
    with the function name and zero flag of the final state of `B`, whose base agrees with the
    final base of `B` on the kept names other than the callee-saved registers and holds in
    each callee-saved register `X` the slot `qsave.X` of the base after `pre`. -/
theorem frame_lsemFuelMemF (tg : LinstrR → MemTag) (fn : String) {pre : Lcmd}
    {B : List LinstrRM} (hpre : ∀ i ∈ pre, IsCopyQ i.li_i) (hB : B.all frameInstrOKB = true)
    {e s : LstateM} {zf : Bool} {fuel : Nat} {t : LstateMF} (he : e.lpc = 0) (hs : s.lpc = 0)
    (hA : AgreeK KeptF s (copyRunL pre e))
    (h : lsemFuelMemF (singletonProgM fn B) fuel { prog := { base := s, lfn := fn }, zf := zf }
      = some t) :
    ∃ fuel' t', fuel' ≤ pre.length + fuel + calleeSaveRestoreEpilogue.length
      ∧ lsemFuelMemF (singletonProgM fn ((pre.map fun i => (i.li_i, tg i.li_i)) ++ B
          ++ (calleeSaveRestoreEpilogue.map fun i => (i.li_i, tg i.li_i))))
          fuel' { prog := { base := e, lfn := fn }, zf := zf } = some t'
      ∧ t'.prog.lfn = t.prog.lfn ∧ t'.zf = t.zf
      ∧ AgreeK (fun r => KeptF r ∧ r ∉ calleeSaved6) t.prog.base t'.prog.base
      ∧ ∀ X ∈ calleeSaved6,
          t'.prog.base.reg.lvm X = (copyRunL pre e).reg.lvm ("qsave." ++ X) := by
  set c := copyRunL pre e with hc
  set P := pre.map fun i => (i.li_i, tg i.li_i) with hP
  set R := calleeSaveRestoreEpilogue.map fun i => (i.li_i, tg i.li_i) with hR
  have hPl : ∀ i ∈ P, IsLopn i := isLopn_of_copies tg hpre
  have hRl : ∀ i ∈ R, IsLopn i := isLopn_of_copies tg calleeSaveRestoreEpilogue_copies
  -- the body under `FrameQ`, from the base after the prologue
  let s1 : LstateMF := { prog := { base := c.setLpc 0, lfn := fn }, zf := zf }
  obtain ⟨f1, t1, hf1, hrun1, hl1, hz1, hle1, hQ1⟩ :=
    lsemFuelMemF_frameQ c hB fn (s := { prog := { base := s, lfn := fn }, zf := zf }) (s' := s1)
      ⟨⟨hA.reg, hA.arr, hA.mem, hA.cf, hA.of⟩, fun _ _ => rfl⟩ rfl rfl hs rfl h
  obtain ⟨hfn1, hpc1⟩ := lsemFuelMemF_end_lpc (s := s1) rfl hle1 hrun1
  rw [← x86Isa_lsemFuelMemF] at hrun1
  obtain ⟨n, hn, hst, -⟩ := steps_of_lsemFuelMemF x86Isa _ f1 _ _ hrun1
  have hst' := x86_steps_relocate fn (pre := P) R (labelsFresh_of_isLopn hPl) hst
  -- the prologue
  have hcl : c.lpc = P.length := by
    have := runStraightF_lpc P e zf c zf (runStraightF_copies tg pre hpre e zf)
    rw [this, he, Nat.zero_add]
  have hpre_run : ∀ k, lsemFuelMemF (singletonProgM fn (P ++ B ++ R)) (P.length + k)
      { prog := { base := e, lfn := fn }, zf := zf }
      = lsemFuelMemF (singletonProgM fn (P ++ B ++ R)) k (shiftPc P.length s1) := by
    intro k
    have hrunP := runStraightF_copies tg pre hpre e zf
    rw [← hP] at hrunP
    rw [lsemFuelMemF_segF (singletonProgM fn (P ++ B ++ R)) fn rfl P e zf k hPl
      (fun j hj => by
        simp only [singletonProgM, he, Nat.zero_add, List.append_assoc]
        exact List.getElem?_append_left hj), hrunP, Option.bind_some]
    change _ = lsemFuelMemF _ k
      { prog := { base := (c.setLpc 0).setLpc (P.length + 0), lfn := fn }, zf := zf }
    rw [Nat.add_zero, ← hcl]
    rfl
  -- the body, relocated
  have hmid : ∀ k, lsemFuelMemF (singletonProgM fn (P ++ B ++ R)) (n + k) (shiftPc P.length s1)
      = lsemFuelMemF (singletonProgM fn (P ++ B ++ R)) k (shiftPc P.length t1) := by
    intro k
    have := lsemFuelMemF_of_steps_add x86Isa _ n hst' k
    rwa [x86Isa_lsemFuelMemF] at this
  -- the restore
  let b2 : LstateM := t1.prog.base.setLpc (P.length + B.length)
  let u2 : LstateMF :=
    { prog := { base := copyRunL calleeSaveRestoreEpilogue b2, lfn := fn }, zf := t1.zf }
  have hrest : lsemFuelMemF (singletonProgM fn (P ++ B ++ R)) (R.length + 0)
      (shiftPc P.length t1) = some u2 := by
    have ht1 : shiftPc P.length t1 = { prog := { base := b2, lfn := fn }, zf := t1.zf } := by
      have hf : t1.prog.lfn = fn := hfn1
      change ({ t1 with prog := { t1.prog with
        base := t1.prog.base.setLpc (P.length + t1.prog.base.lpc) } } : LstateMF) = _
      rw [hpc1, ← hf]
    have hrunR := runStraightF_copies tg calleeSaveRestoreEpilogue
      calleeSaveRestoreEpilogue_copies b2 t1.zf
    rw [← hR] at hrunR
    have hl2 := runStraightF_lpc R b2 t1.zf _ _ hrunR
    rw [ht1, lsemFuelMemF_segF (singletonProgM fn (P ++ B ++ R)) fn rfl R b2 t1.zf 0 hRl
      (fun j hj => by
        simp only [singletonProgM, b2, LstateM.lpc_setLpc]
        rw [List.getElem?_append_right (by simp only [List.length_append]; omega)]
        congr 1
        simp only [List.length_append]
        omega), hrunR, Option.bind_some]
    refine lsemFuelMemF_halt _ 0 _ ?_
    unfold findInstrMem
    simp only [singletonProgM, ↓reduceIte]
    refine List.getElem?_eq_none ?_
    simp only [List.length_append]
    rw [hl2]
    simp only [b2, LstateM.lpc_setLpc]
    omega
  refine ⟨P.length + (n + (R.length + 0)), u2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hP, hR, List.length_map]
    omega
  · rw [hpre_run, hmid, hrest]
  · exact hfn1.symm.trans hl1
  · exact hz1
  · obtain ⟨hla, hlm, hlc, hlo⟩ := copyRunL_frame calleeSaveRestoreEpilogue b2
    refine ⟨fun r hr => ?_, fun r hr => ?_, hlm.trans hQ1.1.mem, hlc.trans hQ1.1.cf,
      hlo.trans hQ1.1.of⟩
    · rw [copyRunL_lvm_of_not_mem _ _ (by rw [copyDsts_calleeSaveRestore]; exact hr.2)]
      exact hQ1.1.reg r hr.1
    · rw [hla]
      exact hQ1.1.arr r hr.1
  · intro X hX
    rw [copyRunL_calleeSaveRestore b2 hX]
    exact hQ1.2 X hX

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrameFuelMemF
