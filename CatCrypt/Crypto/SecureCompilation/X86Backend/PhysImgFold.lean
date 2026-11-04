/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg

/-!
# The image class under the constant-index fold and the register re-allocation

The image check `physImgB slotArr body` (`JasminLsemAddrImage`) reads each indexed access of a
body through the reload scan `reloadOf`, and each write of an array slot through the entry scan
`entryRegB`. This module proves that the two owned passes `ConstIndexFold.foldIndexedBody` and
`LprogGpRealloc.reallocBody` keep the class.

The reload scan of a body is a forward fold over its instructions: the scan before instruction
`k + 1` is one step `scanStepF` of the scan before instruction `k`, read as a function of the
carried name (`reloadOf_succ_eq`). A pass keeps the class when, along corresponding positions,
the scan of its output resolves to an array slot wherever the scan of its input does
(`DomOn`).

## Main results

* `scanStepF`, `reloadOf_succ_eq`: the reload scan as a forward fold.
* `DomOn`, `domOn_step`: the dominance of one scan by another, kept by a common instruction.
* `physImgB_of_pointwise`: a rewrite that keeps the length of a body and, at every position,
  either keeps the instruction or puts an instruction with no access and no array-slot
  destination whose scan step dominates the step of the input.
* `physImgB_foldIndexedBody`: the constant-index fold, the removal of dead immediate moves and
  the array-ABI spelling keep the class, when no 64-bit copy into a register reads an array slot
  (`copyNoSlotB`) and no indexed access, `ZEROARR` or `STOREIMM` has a cell name as its base
  (`cellBaseFreeB`).
* `goAcc_img`: a run materialized by the check `goAcc` keeps the scans of every name that is no
  location or is live out, and writes an array slot only by a save after moves into other names.
* `physImgB_reallocBody`: the register re-allocation keeps the class, when no result register
  is a frame cell.

Every result assumes that every array slot is a `qsave.` slot, which the region layout gives.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellParts?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The reload scan as a forward fold -/

/-- One step of the reload scan at the instruction `j`: the frame slot whose word the name `b`
    holds after `j`, from the frame slot `f y` whose word each name `y` holds before `j`. -/
def scanStepF (slotArr : String → Option (String × Nat)) (j : Linstr)
    (f : String → Option String) (b : String) : Option String :=
  match slotMov? j.li_i with
  | some (d, q) =>
      if d = b then (if (slotArr q).isNone && gpNameB q then f q else some q)
      else if (slotArr d).isNone then f b else none
  | none =>
      match j.li_i with
      | .Lopn ds _ _ => if ds.any (dstHitB slotArr b) then none else f b
      | _ => none

/-- The reload scan before instruction `k + 1` is one step of the scan before instruction
    `k`. -/
theorem reloadOf_succ_eq (slotArr : String → Option (String × Nat)) {body : Lcmd} {k : Nat}
    {j : Linstr} (hb : body[k]? = some j) (b : String) :
    reloadOf slotArr body (k + 1) b =
      scanStepF slotArr j (fun y => reloadOf slotArr body k y) b := by
  simp only [reloadOf, hb]
  rfl

/-- Past the end of the body the reload scan finds nothing. -/
theorem reloadOf_succ_none (slotArr : String → Option (String × Nat)) {body : Lcmd} {k : Nat}
    (hb : body[k]? = none) (b : String) : reloadOf slotArr body (k + 1) b = none := by
  simp only [reloadOf, hb]

/-- The scan `g` resolves every name of `S` to the array slot the scan `f` resolves it to. -/
def DomOn (slotArr : String → Option (String × Nat)) (S : String → Prop)
    (f g : String → Option String) : Prop :=
  ∀ x, S x → ∀ q, f x = some q → (slotArr q).isSome = true → g x = some q

/-- One step of the scan at a common instruction keeps the dominance, on a set of names that
    holds every general-purpose name. -/
theorem domOn_step {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q)
    {f g : String → Option String} (h : DomOn slotArr S f g) (j : Linstr) :
    DomOn slotArr S (scanStepF slotArr j f) (scanStepF slotArr j g) := by
  intro x hx q hf hq
  unfold scanStepF at hf ⊢
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, s⟩ := p
    rw [hm] at hf
    simp only at hf ⊢
    split_ifs at hf ⊢ with h1 h2 h3
    · exact h s (hS s (by simp only [Bool.and_eq_true] at h2; exact h2.2)) q hf hq
    · exact hf
    · exact h x hx q hf hq
  | none =>
    rw [hm] at hf
    simp only at hf ⊢
    cases hj : j.li_i with
    | Lopn ds o ss =>
      rw [hj] at hf
      simp only at hf ⊢
      split_ifs at hf ⊢
      exact h x hx q hf hq
    | _ => rw [hj] at hf; cases hf

/-- A move of `slotMov?` on an operation with the single destination `d` moves into `d`. -/
theorem slotMov?_single {d : String} {o : String} {ss : List LOperand} {d' s : String}
    (h : slotMov? (.Lopn [.reg d] o ss) = some (d', s)) : d' = d := by
  unfold slotMov? at h
  split at h
  · rename_i heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, -, -⟩ := heq
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  · cases h

/-- The step of the scan at an operation with the single destination `d`, which is no array
    slot, passes every other name. -/
theorem scanStepF_single_ne {d : String} (hd : slotArr d = none) {j : Linstr} {o : String}
    {ss : List LOperand} (hj : j.li_i = .Lopn [.reg d] o ss) {b : String} (hb : b ≠ d)
    (f : String → Option String) : scanStepF slotArr j f b = f b := by
  unfold scanStepF
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d', s⟩ := p
    rw [hj] at hm
    have := slotMov?_single hm
    subst this
    simp [Ne.symm hb, hd]
  | none =>
    simp only [hj, List.any_cons, List.any_nil, Bool.or_false, dstHitB]
    simp [Ne.symm hb, hd]

/-- **Rewriting an operation with a single destination.** Let `i` and `i'` both have the single
    destination `d`, which is no array slot, and let `i` be no move into `d` from an array slot
    or a general-purpose name. Then the step at `i'` dominates the step at `i`. -/
theorem domOn_step_single {S : String → Prop} {d : String} (hd : slotArr d = none)
    {i i' : Linstr} {o o' : String} {ss ss' : List LOperand}
    (hi : i.li_i = .Lopn [.reg d] o ss) (hi' : i'.li_i = .Lopn [.reg d] o' ss')
    (hnr : ∀ x, slotMov? i.li_i = some (d, x) → slotArr x = none ∧ gpNameB x = false)
    {f g : String → Option String} (h : DomOn slotArr S f g) :
    DomOn slotArr S (scanStepF slotArr i f) (scanStepF slotArr i' g) := by
  intro x hx q hf hq
  by_cases hxd : x = d
  · subst hxd
    unfold scanStepF at hf
    cases hm : slotMov? i.li_i with
    | some p =>
      obtain ⟨d', s⟩ := p
      have hd' : d' = x := by rw [hi] at hm; exact slotMov?_single hm
      subst hd'
      obtain ⟨h1, h2⟩ := hnr s hm
      rw [hm] at hf
      simp only [ite_true, h2, Bool.and_false, Bool.false_eq_true, ite_false,
        Option.some.injEq] at hf
      subst hf
      simp [h1] at hq
    | none =>
      rw [hm] at hf
      simp only [hi, List.any_cons, List.any_nil, Bool.or_false, dstHitB] at hf
      simp at hf
  · rw [scanStepF_single_ne hd hi hxd] at hf
    rw [scanStepF_single_ne hd hi' hxd]
    exact h x hx q hf hq

/-- **A non-move operation replaced by an instruction transparent on `S`.** -/
theorem domOn_step_transparent {S : String → Prop} {i i' : Linstr} {ds : List LOperand}
    {o : String} {ss : List LOperand} (hm : slotMov? i.li_i = none)
    (hi : i.li_i = .Lopn ds o ss)
    (hi' : ∀ b, S b → ∀ g : String → Option String, scanStepF slotArr i' g b = g b)
    {f g : String → Option String} (h : DomOn slotArr S f g) :
    DomOn slotArr S (scanStepF slotArr i f) (scanStepF slotArr i' g) := by
  intro x hx q hf hq
  rw [hi' x hx]
  unfold scanStepF at hf
  rw [hm, hi] at hf
  simp only at hf
  split_ifs at hf
  exact h x hx q hf hq

/-! ## 2. A rewrite at fixed positions -/

/-- The scans of two bodies of equal length, related at each position by a dominating step. -/
theorem domOn_reloadOf {S : String → Prop} {b b' : Lcmd} (hlen : b'.length = b.length)
    (hstep : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      ∀ f g, DomOn slotArr S f g → DomOn slotArr S (scanStepF slotArr i f)
        (scanStepF slotArr i' g)) :
    ∀ k, DomOn slotArr S (fun y => reloadOf slotArr b k y) (fun y => reloadOf slotArr b' k y)
  | 0 => fun x _ q hf => by simp [reloadOf] at hf
  | k + 1 => by
    cases hb : b[k]? with
    | none =>
      intro x _ q hf
      simp only at hf
      rw [reloadOf_succ_none slotArr hb] at hf
      cases hf
    | some i =>
      obtain ⟨i', hb'⟩ : ∃ i', b'[k]? = some i' := by
        have hk : k < b.length := (List.getElem?_eq_some_iff.mp hb).1
        exact ⟨b'[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      intro x hx q hf hq
      simp only at hf ⊢
      rw [reloadOf_succ_eq slotArr hb] at hf
      rw [reloadOf_succ_eq slotArr hb']
      exact hstep k i i' hb hb' _ _ (domOn_reloadOf hlen hstep k) x hx q hf hq

/-- **The class under a rewrite at fixed positions.** Let `b'` have the length of `b`, which is
    in the class. At every position let the scan step of `b'` dominate that of `b` on a set `S`
    of names holding the general-purpose names and the bases (`AccBase`) of the instructions of
    `b'`; let the instruction of `b'` be that of `b`, or have no access (`isAccB`, `isArrImmB`)
    and no array-slot destination; and let
    a move of `b` be a move into the same name in `b'`, unless an instruction of `b` in front of
    it is no move. Then `b'` is in the class. -/
theorem physImgB_of_pointwise {S : String → Prop} {b b' : Lcmd}
    (h : physImgB slotArr b = true) (hlen : b'.length = b.length)
    (hstep : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      ∀ f g, DomOn slotArr S f g → DomOn slotArr S (scanStepF slotArr i f)
        (scanStepF slotArr i' g))
    (hpt : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      i' = i ∨ (isAccB i'.li_i = false ∧ isArrImmB i'.li_i = false ∧ DstOk slotArr i'.li_i))
    (hbase : ∀ (k : Nat) (i' : Linstr), b'[k]? = some i' → ∀ x, AccBase x i'.li_i → S x)
    (hent : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      (∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) ∨
        ∃ (p : Nat) (j : Linstr), p < k ∧ b[p]? = some j ∧ slotMov? j.li_i = none) :
    physImgB slotArr b' = true := by
  have hdom := domOn_reloadOf hlen hstep
  have hentry : ∀ k R, entryRegB b k R = true → entryRegB b' k R = true := by
    intro k R he
    unfold entryRegB at he ⊢
    rw [List.all_eq_true] at he ⊢
    intro j' hj'
    obtain ⟨p, hp, hpj⟩ := List.getElem_of_mem hj'
    simp only [List.length_take] at hp
    have hpk : p < k := by omega
    have hpb : p < b.length := by omega
    have hb'p : b'[p]? = some j' := by
      rw [← hpj, List.getElem_take]; exact List.getElem?_eq_getElem _
    have hbp : b[p]? = some b[p] := List.getElem?_eq_getElem hpb
    have hmem : ∀ q (hq : q < k) (hqb : q < b.length), b[q] ∈ b.take k := by
      intro q hq hqb
      exact List.mem_iff_getElem.mpr ⟨q, by simp; omega, by simp⟩
    have hmv := he b[p] (hmem p hpk hpb)
    rcases hent p b[p] j' hbp hb'p with hmv' | ⟨p', j, hp', hj, hjm⟩
    · cases hm : slotMov? b[p].li_i with
      | none => rw [hm] at hmv; cases hmv
      | some ds =>
        obtain ⟨d, s⟩ := ds
        rw [hm] at hmv
        obtain ⟨s', hs'⟩ := hmv' d s hm
        rw [hs']
        exact hmv
    · have hp'b : p' < b.length := by omega
      have := he b[p'] (hmem p' (by omega) hp'b)
      rw [List.getElem?_eq_getElem hp'b, Option.some.injEq] at hj
      rw [hj, hjm] at this
      cases this
  refine physImgB_of_embed h fun k i' hk' => ?_
  have hkb : k < b.length := by
    have := (List.getElem?_eq_some_iff.mp hk').1; omega
  have hk : b[k]? = some b[k] := List.getElem?_eq_getElem hkb
  rcases hpt k b[k] i' hk hk' with heq | ⟨hacc, hai, hdst⟩
  · refine Or.inr ⟨k, by rw [hk, heq], fun x hx ha => ?_, Or.inl (hentry k)⟩
    simp only [accArr, Option.isSome_bind] at ha ⊢
    cases hr : reloadOf slotArr b k x with
    | none => rw [hr] at ha; cases ha
    | some q =>
      rw [hr] at ha
      have ha' : (slotArr q).isSome = true := by simpa using ha
      have := hdom k x (hbase k i' hk' x hx) q hr ha'
      simp only at this
      rw [this]
      exact ha
  · exact Or.inl ⟨hacc, hai, slotWriteB_of_dstOk hdst _ _⟩

/-! ## 3. Names -/

section Names

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave isGpName)

/-- No general-purpose name of the printer is a frame-slot or a cell name. -/
theorem isGpName_prefix {d : String} (h : isGpName d = true) :
    hasPrefix d "qsave." = false ∧ hasPrefix d "mem." = false := by
  have hm : d ∈ ["RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI", "R8", "R9", "R10",
      "R11", "R12", "R13", "R14", "R15"] := by
    unfold isGpName at h
    split at h <;> simp_all
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> decide

/-- No general-purpose name of the image is a cell name. -/
theorem gpNameB_prefix {d : String} (h : gpNameB d = true) :
    hasPrefix d "qsave." = false ∧ hasPrefix d "mem." = false := by
  simp only [gpNameB, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

/-- A frame-slot name is no general-purpose name of the image. -/
theorem gpNameB_of_spill {x : String} (h : isSpillOrQsave x = true) : gpNameB x = false := by
  cases hg : gpNameB x with
  | false => rfl
  | true =>
    exfalso
    simp only [gpNameB, List.contains_iff_mem, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> revert h <;> decide

/-- A cell name `mem.<B>.<off>` starts with `mem.` and not with `qsave.`. -/
theorem memName_prefix (B : String) (off : Nat) :
    hasPrefix (memName B off) "mem." = true ∧ hasPrefix (memName B off) "qsave." = false := by
  simp [hasPrefix, memName, String.toList_append, List.isPrefixOf]

end Names

/-! ## 4. The constant-index fold -/

section Fold

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave isGpName)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)

/-- A move of `slotMov?` is a `MOVQ` or `MOV:64` between two registers. -/
theorem slotMov?_shape {r : LinstrR} {d s : String} (h : slotMov? r = some (d, s)) :
    r = .Lopn [.reg d] "MOVQ" [.reg s] ∨ r = .Lopn [.reg d] "MOV:64" [.reg s] := by
  unfold slotMov? at h
  split at h
  · split_ifs at h with h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases h1 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · cases h

/-- The analysis step from the empty environment records only an immediate move. -/
theorem stepK_nil {j : JInstr 64} (hj : ∀ d k, j ≠ .mov d (.imm k)) : stepK [] j = [] := by
  cases j with
  | mov d s =>
    cases s with
    | imm k => exact absurd rfl (hj d k)
    | reg x => simp [stepK, KEnv.find, KEnv.kill]
  | _ => simp [stepK, KEnv.kill, KEnv.killAll, KEnv.killFrame]

theorem stepKs_nil {js : List (JInstr 64)} (hj : ∀ j ∈ js, ∀ d k, j ≠ .mov d (.imm k)) :
    stepKs [] js = [] := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [stepKs, List.foldl_cons]
    rw [stepK_nil (hj j (by simp))]
    exact ih fun j' hj' => hj j' (by simp [hj'])

/-- A move between registers lowers to no immediate move. -/
theorem lowerPrinted_slotMov (frame spillW qsaveB : Nat) {r : LinstrR} {d s : String}
    (h : slotMov? r = some (d, s)) {js : List (JInstr 64)}
    (hl : lowerPrinted frame spillW qsaveB r = some js) :
    ∀ j ∈ js, ∀ d' k, j ≠ .mov d' (.imm k) := by
  rcases slotMov?_shape h with rfl | rfl
  · have e : lowerPrinted frame spillW qsaveB (.Lopn [.reg d] "MOVQ" [.reg s]) =
        match LprogBytes.spillQsaveOff frame spillW d qsaveB,
          LprogBytes.spillQsaveOff frame spillW s qsaveB with
        | some off, none => some [JInstr.storeMem "RSP" off (.reg s)]
        | none, some off => some [JInstr.loadMem d "RSP" off]
        | _, _ => some [JInstr.mov d (.reg s)] := rfl
    rw [e] at hl
    split at hl <;> simp only [Option.some.injEq] at hl <;> subst hl <;> simp
  · rw [lowerPrinted_movReg] at hl
    simp only [Option.some.injEq] at hl
    subst hl
    simp

/-- After a move from the empty environment the environment is empty. -/
theorem nextEnv_nil_of_move (p : Nat × Nat × Nat) {i : Linstr}
    (h : (slotMov? i.li_i).isSome = true) : nextEnv p [] i = [] := by
  obtain ⟨⟨d, s⟩, hm⟩ := Option.isSome_iff_exists.mp h
  have hx := slotMov?_shape hm
  have hr : isLret i = false := by
    unfold isLret; rcases hx with hx | hx <;> rw [hx]
  unfold nextEnv
  rw [hr]
  simp only [Bool.false_eq_true, ite_false]
  cases hl : lowerPrinted p.1 p.2.1 p.2.2 i.li_i with
  | some js =>
    simp only [stepKs_nil (lowerPrinted_slotMov _ _ _ hm hl)]
    simp [KEnv.killAll]
  | none =>
    simp only
    rcases hx with hx | hx <;> simp [hx, KEnv.killAll]

/-- A move between registers is no dead immediate move. -/
theorem deadImmReg?_of_move (p : Nat × Nat × Nat) {i : Linstr}
    (h : (slotMov? i.li_i).isSome = true) : deadImmReg? p i = none := by
  obtain ⟨⟨d, s⟩, hm⟩ := Option.isSome_iff_exists.mp h
  unfold deadImmReg?
  split
  · rename_i r k hl
    exact absurd rfl (lowerPrinted_slotMov _ _ _ hm hl _ (by simp) r k)
  · rfl

theorem foldCore_length (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (env : KEnv) (b : Lcmd), (foldCore p ex env b).length = b.length
  | _, [] => rfl
  | env, i :: is => by simp [foldCore, foldCore_length p ex _ is]

/-- The instruction at position `k` of the fold is the fold of the instruction at `k` under an
    environment, which is empty when the fold starts empty and every instruction in front of `k`
    is a move. -/
theorem foldCore_getElem? (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (b : Lcmd) (env : KEnv) (k : Nat) (i' : Linstr), (foldCore p ex env b)[k]? = some i' →
      ∃ i e, b[k]? = some i ∧ i' = { i with li_i := foldInstr ex e i.li_i } ∧
        (env = [] → (∀ j ∈ b.take k, (slotMov? j.li_i).isSome = true) → e = [])
  | [], _, _, _, h => by simp [foldCore] at h
  | i :: is, env, 0, i', h => by
    simp only [foldCore, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨i, env, rfl, h.symm, fun he _ => he⟩
  | i :: is, env, k + 1, i', h => by
    simp only [foldCore, List.getElem?_cons_succ] at h
    obtain ⟨i₀, e, h1, h2, h3⟩ := foldCore_getElem? p ex is _ k i' h
    refine ⟨i₀, e, by simpa using h1, h2, fun he hm => h3 ?_ fun j hj => hm j (by simp [hj])⟩
    subst he
    exact nextEnv_nil_of_move p (hm i (by simp))

/-- `foldInstr` either keeps the instruction or rewrites it by `foldTarget?`: an indexed load
    or store to a direct access through the same destination, or a 64-bit copy of a known
    frame-slot name into a general-purpose register to an immediate move. -/
theorem foldInstr_cases (ex : List String) (env : KEnv) (r : LinstrR) :
    foldInstr ex env r = r
    ∨ (∃ d B x sc off, r = .Lopn [.reg d] "LOADIDX" [.arrIdx B x sc]
        ∧ foldInstr ex env r = .Lopn [.reg d] "LOAD" [.arr B off])
    ∨ (∃ d B x sc vn off, r = .Lopn [.reg d] "STOREIDX" [.arrIdx B x sc, .reg vn]
        ∧ foldInstr ex env r = .Lopn [.reg d] "STORE" [.arr B off, .reg vn])
    ∨ (∃ d x n, r = .Lopn [.reg d] "MOV:64" [.reg x]
        ∧ foldInstr ex env r = .Lopn [.reg d] "MOV:64" [.imm n]
        ∧ isGpName d = true ∧ isSpillOrQsave x = true ∧ env ≠ []) := by
  unfold foldInstr
  split
  · exact Or.inl rfl
  · cases ht : foldTarget? env r with
    | none => exact Or.inl rfl
    | some r' =>
      simp only [Option.getD_some]
      unfold foldTarget? at ht
      split at ht
      · split at ht
        · split at ht
          · simp only [Option.some.injEq] at ht
            exact Or.inr (Or.inl ⟨_, _, _, _, _, rfl, ht.symm⟩)
          · cases ht
        · cases ht
      · split at ht
        · split at ht
          · simp only [Option.some.injEq] at ht
            exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl, ht.symm⟩))
          · cases ht
        · cases ht
      · split at ht
        · rename_i v hv
          split at ht
          · rename_i hc
            simp only [Option.some.injEq] at ht
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            refine Or.inr (Or.inr (Or.inr ⟨_, _, _, rfl, ht.symm, hc.1.1, hc.1.2, ?_⟩))
            rintro rfl
            simp [KEnv.find] at hv
          · cases ht
        · cases ht
      · cases ht

end Fold

/-! ## 5. The class under the three stages of the fold -/

/-- An instruction of a body in the class passes both conjuncts of the class. -/
theorem physImgB_getElem {body : Lcmd} (h : physImgB slotArr body = true) {k : Nat}
    {i : Linstr} (hk : body[k]? = some i) :
    accOkB slotArr body k i.li_i = true ∧ slotWriteB slotArr body k i.li_i = true := by
  have hlt : k < body.length := (List.getElem?_eq_some_iff.mp hk).1
  have := List.all_eq_true.mp h k (List.mem_range.mpr hlt)
  rw [hk] at this
  simpa using this

/-- An operation with a single destination that is no move writes no array slot when it
    passes `slotWriteB`. -/
theorem slotArr_of_slotWriteB {body : Lcmd} {k : Nat} {d o : String} {ss : List LOperand}
    (hm : slotMov? (.Lopn [.reg d] o ss) = none)
    (h : slotWriteB slotArr body k (.Lopn [.reg d] o ss) = true) : slotArr d = none := by
  simp only [slotWriteB, List.all_cons, List.all_nil, Bool.and_true, hm, Bool.or_false,
    Option.isNone_iff_eq_none] at h
  exact h

/-- An operation whose single destination is no array slot. -/
theorem dstOk_single {d o : String} {ss : List LOperand} (hd : slotArr d = none) :
    DstOk slotArr (.Lopn [.reg d] o ss) := by
  intro ds o' ss' he x hx
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  simp only [List.mem_singleton] at hx
  subst hx
  unfold OperandOk
  refine ⟨fun q hq => ?_, fun q n hq => ?_, fun q j sc hq => ?_⟩
  · cases hq; exact hd
  · cases hq
  · cases hq

/-- A member of a prefix of a body is at a position in front of the prefix's end. -/
theorem mem_take_getElem? {b : Lcmd} {k : Nat} {j : Linstr} (hj : j ∈ b.take k) :
    ∃ p, p < k ∧ b[p]? = some j := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hj
  simp only [List.length_take] at hp
  exact ⟨p, by omega, by rw [List.getElem_take]; exact List.getElem?_eq_getElem (by omega)⟩

section FoldStages

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave isGpName)

/-- No 64-bit copy into a register reads an array slot. -/
def copyNoSlotB (slotArr : String → Option (String × Nat)) (body : Lcmd) : Bool :=
  body.all fun j =>
    match j.li_i with
    | .Lopn [.reg _] "MOV:64" [.reg x] => (slotArr x).isNone
    | _ => true

/-- No indexed access has a cell name `mem.<B>.<off>` as its base, and no `ZEROARR` or
    `STOREIMM` has a cell name as its base register. -/
def cellBaseFreeB (body : Lcmd) : Bool :=
  body.all fun j =>
    match j.li_i with
    | .Lopn _ _ (.arrIdx x _ _ :: _) => !hasPrefix x "mem."
    | .Lopn ds o (.reg x :: ss) => !isArrImmB (.Lopn ds o (.reg x :: ss)) || !hasPrefix x "mem."
    | _ => true

theorem copyNoSlotB_at {body : Lcmd} (h : copyNoSlotB slotArr body = true) {j : Linstr}
    (hj : j ∈ body) {d x : String} (hx : j.li_i = .Lopn [.reg d] "MOV:64" [.reg x]) :
    slotArr x = none := by
  have := List.all_eq_true.mp h j hj
  rw [hx] at this
  simpa using this

theorem cellBaseFreeB_at {body : Lcmd} (h : cellBaseFreeB body = true) {j : Linstr}
    (hj : j ∈ body) {ds : List LOperand} {o x y : String} {sc : Nat} {ss : List LOperand}
    (hx : j.li_i = .Lopn ds o (.arrIdx x y sc :: ss)) : hasPrefix x "mem." = false := by
  have := List.all_eq_true.mp h j hj
  rw [hx] at this
  simpa using this

theorem cellBaseFreeB_arrImm {body : Lcmd} (h : cellBaseFreeB body = true) {j : Linstr}
    (hj : j ∈ body) {ds : List LOperand} {o x : String} {ss : List LOperand}
    (hx : j.li_i = .Lopn ds o (.reg x :: ss)) (hai : isArrImmB j.li_i = true) :
    hasPrefix x "mem." = false := by
  have := List.all_eq_true.mp h j hj
  rw [hx] at this hai
  simpa [hai] using this

/-- At a position of the fold, the step of the folded instruction dominates the step of the
    input instruction, the folded instruction is the input or has no access and no array-slot
    destination, and a move is kept unless an instruction in front of it is no move. -/
theorem foldCore_pos (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q) {body : Lcmd}
    (h : physImgB slotArr body = true) (hcp : copyNoSlotB slotArr body = true)
    (p : Nat × Nat × Nat) (ex : List String) {k : Nat} {i i' : Linstr}
    (hb : body[k]? = some i) (hb' : (foldCore p ex [] body)[k]? = some i') :
    (∀ f g, DomOn slotArr S f g →
      DomOn slotArr S (scanStepF slotArr i f) (scanStepF slotArr i' g)) ∧
    (i' = i ∨ (isAccB i'.li_i = false ∧ isArrImmB i'.li_i = false ∧ DstOk slotArr i'.li_i)) ∧
    ((∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) ∨
      ∃ (p : Nat) (j : Linstr), p < k ∧ body[p]? = some j ∧ slotMov? j.li_i = none) := by
  obtain ⟨i₀, e, h1, h2, h3⟩ := foldCore_getElem? p ex body [] k i' hb'
  rw [hb, Option.some.injEq] at h1
  subst i₀
  have hw := (physImgB_getElem h hb).2
  rcases foldInstr_cases ex e i.li_i with hf | ⟨d, B, x, sc, off, hi, hf⟩ |
      ⟨d, B, x, sc, vn, off, hi, hf⟩ | ⟨d, x, n, hi, hf, hgd, hsx, he⟩
  · have : i' = i := by rw [h2, hf]
    rw [this]
    exact ⟨fun f g hd => domOn_step hS hd i, Or.inl rfl, Or.inl fun d s hm => ⟨s, hm⟩⟩
  · have hi' : i'.li_i = .Lopn [.reg d] "LOAD" [.arr B off] := by rw [h2]; exact hf
    rw [hi] at hw
    have hd := slotArr_of_slotWriteB (by simp [slotMov?]) hw
    refine ⟨fun f g hdom => domOn_step_single hd hi hi' (by simp [hi, slotMov?]) hdom,
      Or.inr ⟨by simp [hi', isAccB], by simp [hi', isArrImmB], by rw [hi']; exact dstOk_single hd⟩,
      Or.inl fun d s hm => by simp [hi, slotMov?] at hm⟩
  · have hi' : i'.li_i = .Lopn [.reg d] "STORE" [.arr B off, .reg vn] := by rw [h2]; exact hf
    rw [hi] at hw
    have hd := slotArr_of_slotWriteB (by simp [slotMov?]) hw
    refine ⟨fun f g hdom => domOn_step_single hd hi hi' (by simp [hi, slotMov?]) hdom,
      Or.inr ⟨by simp [hi', isAccB], by simp [hi', isArrImmB], by rw [hi']; exact dstOk_single hd⟩,
      Or.inl fun d s hm => by simp [hi, slotMov?] at hm⟩
  · have hi' : i'.li_i = .Lopn [.reg d] "MOV:64" [.imm n] := by rw [h2]; exact hf
    have hd : slotArr d = none := slotArr_none_of_prefix hq (isGpName_prefix hgd).1
    have hx : slotArr x = none :=
      copyNoSlotB_at hcp (List.mem_of_getElem? hb) hi
    refine ⟨fun f g hdom => domOn_step_single hd hi hi' (fun x' hm => ?_) hdom,
      Or.inr ⟨by simp [hi', isAccB], by simp [hi', isArrImmB], by rw [hi']; exact dstOk_single hd⟩, Or.inr ?_⟩
    · rw [hi] at hm
      have : x' = x := by
        unfold slotMov? at hm
        simp only [true_and] at hm
        split_ifs at hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        exact hm.2.symm
      subst this
      exact ⟨hx, gpNameB_of_spill hsx⟩
    · by_contra hc
      apply he
      refine h3 rfl fun j hj => ?_
      obtain ⟨p, hp, hpj⟩ := mem_take_getElem? hj
      cases hm : slotMov? j.li_i with
      | some _ => rfl
      | none => exact absurd ⟨p, j, hp, hpj, hm⟩ hc

/-- **The constant-index fold keeps the class**, when no 64-bit copy into a register reads an
    array slot. -/
theorem physImgB_constIndexFoldBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {body : Lcmd}
    (hcp : copyNoSlotB slotArr body = true) (h : physImgB slotArr body = true) :
    physImgB slotArr (constIndexFoldBody body) = true := by
  unfold constIndexFoldBody
  dsimp only
  split
  · refine physImgB_of_pointwise (S := fun _ => True) h (foldCore_length _ _ _ _)
      (fun k i i' hb hb' => (foldCore_pos hq (fun _ _ => trivial) h hcp _ _ hb hb').1)
      (fun k i i' hb hb' => (foldCore_pos hq (fun _ _ => trivial) h hcp _ _ hb hb').2.1)
      (fun _ _ _ _ _ => trivial)
      (fun k i i' hb hb' => (foldCore_pos hq (fun _ _ => trivial) h hcp _ _ hb hb').2.2)
  · exact h

/-- Every instruction of the fold is an instruction of the body, or has no register-indexed
    first source. -/
theorem mem_constIndexFoldBody {body : Lcmd} {j : Linstr} (hj : j ∈ constIndexFoldBody body) :
    j ∈ body ∨ ∀ ds o x y sc ss, j.li_i ≠ .Lopn ds o (.arrIdx x y sc :: ss) := by
  unfold constIndexFoldBody at hj
  dsimp only at hj
  split at hj
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨i, e, h1, h2, -⟩ := foldCore_getElem? _ _ body [] k _ (List.getElem?_eq_getElem hk)
    rw [h2]
    rcases foldInstr_cases _ e i.li_i with hf | ⟨d, B, x, sc, off, hi, hf⟩ |
        ⟨d, B, x, sc, vn, off, hi, hf⟩ | ⟨d, x, n, hi, hf, -⟩
    · left
      rw [hf]
      exact List.mem_of_getElem? h1
    all_goals
      right
      intro ds o x' y sc' ss hc
      dsimp only at hc
      rw [hf] at hc
      simp at hc
  · exact Or.inl hj

/-- Every instruction of the fold is an instruction of the body, or is no `ZEROARR` or
    `STOREIMM`. -/
theorem mem_constIndexFoldBody_arrImm {body : Lcmd} {j : Linstr}
    (hj : j ∈ constIndexFoldBody body) : j ∈ body ∨ isArrImmB j.li_i = false := by
  unfold constIndexFoldBody at hj
  dsimp only at hj
  split at hj
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨i, e, h1, h2, -⟩ := foldCore_getElem? _ _ body [] k _ (List.getElem?_eq_getElem hk)
    rw [h2]
    rcases foldInstr_cases _ e i.li_i with hf | ⟨d, B, x, sc, off, hi, hf⟩ |
        ⟨d, B, x, sc, vn, off, hi, hf⟩ | ⟨d, x, n, hi, hf, -⟩
    · left
      rw [hf]
      exact List.mem_of_getElem? h1
    all_goals
      right
      dsimp only
      rw [hf]
      simp [isArrImmB]
  · exact Or.inl hj

theorem dropDeadCore_sublist (p : Nat × Nat × Nat) :
    ∀ b : Lcmd, (dropDeadCore p b).Sublist b
  | [] => List.Sublist.slnil
  | i :: is => by
    simp only [dropDeadCore]
    split
    · split
      · exact (dropDeadCore_sublist p is).cons i
      · exact (dropDeadCore_sublist p is).cons_cons i
    · exact (dropDeadCore_sublist p is).cons_cons i

theorem dropDeadCore_filter_move (p : Nat × Nat × Nat) :
    ∀ b : Lcmd, (dropDeadCore p b).filter (fun j => (slotMov? j.li_i).isSome) =
      b.filter (fun j => (slotMov? j.li_i).isSome)
  | [] => rfl
  | i :: is => by
    have ih := dropDeadCore_filter_move p is
    simp only [dropDeadCore]
    split
    · rename_i r hr
      split
      · have hm : (slotMov? i.li_i).isSome = false := by
          cases hc : (slotMov? i.li_i).isSome with
          | false => rfl
          | true => rw [deadImmReg?_of_move p hc] at hr; cases hr
        rw [List.filter_cons_of_neg (by simp [hm]), ih]
      · simp only [List.filter_cons, ih]
    · simp only [List.filter_cons, ih]

/-- **The removal of dead immediate moves keeps the class.** -/
theorem physImgB_dropDeadImmBody {body : Lcmd} (h : physImgB slotArr body = true) :
    physImgB slotArr (dropDeadImmBody body) = true := by
  unfold dropDeadImmBody
  dsimp only
  split
  · exact physImgB_sublist_of (dropDeadCore_sublist _ body) (dropDeadCore_filter_move _ body) h
  · exact h

/-- `spellMemInstr` keeps the instruction, or spells a direct load as a move from the cell
    name into the same destination, or a direct store as a move into the cell name. -/
theorem spellMemInstr_cases (r : LinstrR) :
    spellMemInstr r = r
    ∨ (∃ d B off, r = .Lopn [.reg d] "LOAD" [.arr B off] ∧
        ∃ o, spellMemInstr r = .Lopn [.reg d] o [.reg (memName B off)] ∧
          (o = "LOAD:64" ∨ o = "MOVQ"))
    ∨ (∃ d B off vn, r = .Lopn [.reg d] "STORE" [.arr B off, .reg vn] ∧
        ∃ o, spellMemInstr r = .Lopn [.reg (memName B off)] o [.reg vn] ∧
          (o = "STORE:64" ∨ o = "MOVQ")) := by
  unfold spellMemInstr
  split
  · right; left
    refine ⟨_, _, _, rfl, ?_⟩
    split_ifs
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr rfl⟩
  · right; right
    refine ⟨_, _, _, _, rfl, ?_⟩
    split_ifs
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr rfl⟩
  · exact Or.inl rfl

/-- **The array-ABI spelling keeps the class**, when no base (`AccBase`) of an instruction is
    a cell name. -/
theorem physImgB_spellMemBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {body : Lcmd}
    (hcb : ∀ j ∈ body, ∀ x, AccBase x j.li_i → hasPrefix x "mem." = false)
    (h : physImgB slotArr body = true) :
    physImgB slotArr (spellMemBody body) = true := by
  have hS : ∀ q, gpNameB q = true → (fun x => hasPrefix x "mem." = false) q :=
    fun q hq' => (gpNameB_prefix hq').2
  have hget : ∀ (k : Nat) (i' : Linstr), (spellMemBody body)[k]? = some i' →
      ∃ i : Linstr, body[k]? = some i ∧ i' = { i with li_i := spellMemInstr i.li_i } := by
    intro k i' hk
    simp only [spellMemBody, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    exact ⟨i, hi, rfl⟩
  have hpos : ∀ (k : Nat) (i i' : Linstr), body[k]? = some i →
      (spellMemBody body)[k]? = some i' →
      (∀ f g, DomOn slotArr (fun x => hasPrefix x "mem." = false) f g →
        DomOn slotArr (fun x => hasPrefix x "mem." = false) (scanStepF slotArr i f)
          (scanStepF slotArr i' g)) ∧
      (i' = i ∨ (isAccB i'.li_i = false ∧ isArrImmB i'.li_i = false ∧ DstOk slotArr i'.li_i)) ∧
      (∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) := by
    intro k i i' hb hb'
    obtain ⟨i₀, h1, h2⟩ := hget k i' hb'
    rw [hb, Option.some.injEq] at h1
    subst i₀
    have hw := (physImgB_getElem h hb).2
    rcases spellMemInstr_cases i.li_i with hf | ⟨d, B, off, hi, o, hf, ho⟩ |
        ⟨d, B, off, vn, hi, o, hf, ho⟩
    · have : i' = i := by rw [h2, hf]
      rw [this]
      exact ⟨fun f g hd => domOn_step hS hd i, Or.inl rfl, fun d s hm => ⟨s, hm⟩⟩
    · have hi' : i'.li_i = .Lopn [.reg d] o [.reg (memName B off)] := by rw [h2]; exact hf
      rw [hi] at hw
      have hd := slotArr_of_slotWriteB (by simp [slotMov?]) hw
      refine ⟨fun f g hdom => domOn_step_single hd hi hi' (by simp [hi, slotMov?]) hdom,
        Or.inr ⟨?_, ?_, by rw [hi']; exact dstOk_single hd⟩,
        fun d s hm => by simp [hi, slotMov?] at hm⟩ <;>
      rw [hi'] <;> rcases ho with rfl | rfl <;> simp [isAccB, isArrImmB]
    · have hi' : i'.li_i = .Lopn [.reg (memName B off)] o [.reg vn] := by rw [h2]; exact hf
      have hm := memName_prefix B off
      have hd : slotArr (memName B off) = none := slotArr_none_of_prefix hq hm.2
      refine ⟨fun f g hdom => domOn_step_transparent (by simp [hi, slotMov?]) hi
        (fun b hb g => scanStepF_single_ne hd hi' (fun he => by
          subst he; rw [hm.1] at hb; cases hb) g) hdom,
        Or.inr ⟨?_, ?_, by rw [hi']; exact dstOk_single hd⟩,
        fun d s hm => by simp [hi, slotMov?] at hm⟩ <;>
      rw [hi'] <;> rcases ho with rfl | rfl <;> simp [isAccB, isArrImmB]
  refine physImgB_of_pointwise (S := fun x => hasPrefix x "mem." = false) h
    (by simp [spellMemBody]) (fun k i i' hb hb' => (hpos k i i' hb hb').1)
    (fun k i i' hb hb' => (hpos k i i' hb hb').2.1) ?_
    (fun k i i' hb hb' => Or.inl (hpos k i i' hb hb').2.2)
  intro k i' hk x hx
  obtain ⟨i, hi, rfl⟩ := hget k i' hk
  rcases spellMemInstr_cases i.li_i with hf | ⟨d, B, off, -, o', hf, ho'⟩ |
      ⟨d, B, off, vn, -, o', hf, ho'⟩
  · simp only [hf] at hx
    exact hcb i (List.mem_of_getElem? hi) x hx
  all_goals
    simp only [hf] at hx
    rcases hx with ⟨_, _, _, _, he⟩ | ⟨_, _, _, he, hai⟩
    · simp at he
    · rw [he] at hai
      cases he
      rcases ho' with rfl | rfl <;> simp [isArrImmB] at hai

/-- **The constant-index fold stage keeps the class.** `foldIndexedBody` folds the
    constant-index accesses to direct accesses, removes the dead immediate moves and spells the
    direct accesses as moves of cell names. When every array slot is a `qsave.` slot, no 64-bit
    copy into a register reads an array slot (`copyNoSlotB`), and no indexed access, `ZEROARR`
    or `STOREIMM` has a cell name as its base (`cellBaseFreeB`), a body in the class gives a
    body in the class. -/
theorem physImgB_foldIndexedBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {body : Lcmd}
    (hcp : copyNoSlotB slotArr body = true) (hcb : cellBaseFreeB body = true)
    (h : physImgB slotArr body = true) :
    physImgB slotArr (foldIndexedBody body) = true := by
  unfold foldIndexedBody
  refine physImgB_spellMemBody hq (fun j hj x hx => ?_)
    (physImgB_dropDeadImmBody (physImgB_constIndexFoldBody hq hcp h))
  have hj' : j ∈ constIndexFoldBody body := by
    unfold dropDeadImmBody at hj
    dsimp only at hj
    split at hj
    · exact (dropDeadCore_sublist _ _).subset hj
    · exact hj
  rcases hx with ⟨ds, o, y, ss, hx⟩ | ⟨ds, o, ss, hx, hai⟩
  · rcases mem_constIndexFoldBody hj' with hj'' | hne
    · exact cellBaseFreeB_at hcb hj'' hx
    · exact absurd hx (hne ds o x y 8 ss)
  · rcases mem_constIndexFoldBody_arrImm hj' with hj'' | hne
    · exact cellBaseFreeB_arrImm hcb hj'' hx hai
    · rw [hne] at hai; cases hai

end FoldStages

/-! ## 6. The register re-allocation: one instruction -/

section Realloc

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg (renOf isPrefixOf_list)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs isRecognizedOpn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

theorem isRecognizedOpn_movq : isRecognizedOpn "MOVQ" = true := by
  simp [isRecognizedOpn, LcmdCopyPropagate.implicitReads, LprogAsmPrinter.stripAbiTag]
  rw [isPrefixOf_list]
  decide

theorem isRecognizedOpn_mov64 : isRecognizedOpn "MOV:64" = true := by
  simp [isRecognizedOpn, LcmdCopyPropagate.implicitReads, LprogAsmPrinter.stripAbiTag]
  rw [isPrefixOf_list]
  decide

/-- The general-purpose registers of the re-allocation are the general-purpose names of the
    image. -/
theorem isPhysGP_eq_gpNameB (x : String) : isPhysGP x = gpNameB x := by
  rw [Bool.eq_iff_iff]
  simp only [isPhysGP, physGPs, gpNameB, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false]
  tauto

/-- A location is neither a frame-slot `qsave.` name nor a cell name. -/
theorem isLoc_prefix {x : String} (h : isLoc x = true) :
    hasPrefix x "qsave." = false ∧ hasPrefix x "mem." = false := by
  rw [isLoc_x86, Bool.or_eq_true] at h
  rcases h with h | h
  · rw [isPhysGP_eq_gpNameB] at h
    exact gpNameB_prefix h
  · rw [isPrefixOf_list] at h
    obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp h
    have hx : x.toList = 'k' :: '.' :: t := by rw [← ht]; rfl
    simp only [hasPrefix, hx]
    exact ⟨rfl, rfl⟩

/-- A general-purpose name is a location. -/
theorem isLoc_of_gpNameB {x : String} (h : gpNameB x = true) : isLoc x = true := by
  rw [isLoc_x86, isPhysGP_eq_gpNameB, h, Bool.true_or]

/-- A pool register is a general-purpose name. -/
theorem gpNameB_of_isPool {x : String} (h : isPool x = true) : gpNameB x = true := by
  rw [isPool_x86, Bool.and_eq_true, Bool.and_eq_true] at h
  rw [← isPhysGP_eq_gpNameB]
  exact h.1.1

/-- A location is no cell name. -/
theorem cellParts?_of_loc {x : String} (h : isLoc x = true) : cellParts? x = none := by
  unfold cellParts?
  rw [ite_eq_right (by rw [(isLoc_prefix h).2]; exact Bool.false_ne_true)]

/-- Under the slot hypothesis, a location is no array slot. -/
theorem slotArr_loc (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {x : String} (h : isLoc x = true) : slotArr x = none :=
  slotArr_none_of_prefix hq (isLoc_prefix h).1

/-- Every name is at itself or at a pool register. -/
def PoolMap (m : Cur) : Prop := ∀ n, look m n = n ∨ isPool (look m n) = true

theorem poolMap_empty : PoolMap ({} : Cur) := fun n => Or.inl (look_empty n)

theorem poolMap_insert {m : Cur} (hm : PoolMap m) {d c : String} (hc : okLoc d c = true) :
    PoolMap (m.insert d c) := by
  intro n
  rw [look_insert]
  split_ifs with h
  · subst h
    simp only [okLoc, Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · exact Or.inr hc
    · exact Or.inl hc
  · exact hm n

/-- The renaming keeps a location a location, and a general-purpose name a general-purpose
    name. -/
theorem renOf_loc {m : Cur} (hm : PoolMap m) {s : String} (hs : isLoc s = true) :
    isLoc (renOf m x86Abi s) = true ∧ (gpNameB s = true → gpNameB (renOf m x86Abi s) = true) := by
  simp only [renOf, hs]
  rcases hm s with h | h
  · rw [h]; exact ⟨hs, id⟩
  · have := gpNameB_of_isPool h
    exact ⟨isLoc_of_gpNameB this, fun _ => this⟩

theorem renOf_nonloc (m : Cur) {s : String} (hs : isLoc s = false) : renOf m x86Abi s = s := by
  simp [renOf, hs]

theorem renOp_reg (m : Cur) (s : String) :
    renOp m (.reg s) = .reg (renOf m x86Abi s) := by
  by_cases hs : isLoc s = true <;> simp [renOp, renOf, hs]

theorem renOp_ne_reg {m : Cur} {o : LOperand} (h : ∀ s, o ≠ .reg s) : renOp m o = o := by
  cases o with
  | reg s => exact absurd rfl (h s)
  | _ => rfl

/-- The cell test of a renamed name is that of the name. -/
theorem cellParts?_renOf {m : Cur} (hm : PoolMap m) (s : String) :
    (cellParts? (renOf m x86Abi s)).isSome = (cellParts? s).isSome := by
  by_cases hs : isLoc s = true
  · rw [cellParts?_of_loc (renOf_loc hm hs).1, cellParts?_of_loc hs]
  · rw [renOf_nonloc m (by simpa using hs)]

/-- **The move test of a renamed operation.** -/
theorem slotMov?_ren {m : Cur} (hm : PoolMap m) {d c o : String} {ss : List LOperand}
    (hc : c = d ∨ (isLoc d = true ∧ isLoc c = true)) :
    slotMov? (.Lopn [.reg c] o (ss.map (fun x => renOp m x))) =
      (slotMov? (.Lopn [.reg d] o ss)).map (fun p => (c, renOf m x86Abi p.2)) := by
  have hcd : (cellParts? c).isSome = (cellParts? d).isSome := by
    rcases hc with rfl | ⟨h1, h2⟩
    · rfl
    · rw [cellParts?_of_loc h1, cellParts?_of_loc h2]
  rcases ss with _ | ⟨x, _ | ⟨y, t⟩⟩
  · simp [slotMov?]
  · cases x with
    | reg s =>
      simp only [List.map_cons, List.map_nil, renOp_reg]
      unfold slotMov?
      simp only [hcd, cellParts?_renOf hm s]
      split_ifs <;> simp
    | _ => simp [renOp, slotMov?]
  · simp [slotMov?]

/-- The scan `g` at `y` resolves to the array slot that the scan `f` resolves `x` to. -/
def ResTo (slotArr : String → Option (String × Nat)) (f : String → Option String) (x : String)
    (g : String → Option String) (y : String) : Prop :=
  ∀ q, f x = some q → (slotArr q).isSome = true → g y = some q

/-- **One step of the scan at a renamed instruction.** Let `j` be the instruction `i` written to
    `c` with renamed sources. At the destination, and at a pair of other names related by the
    scans in front, the scan after `j` resolves wherever the scan after `i` does. -/
theorem stepRen (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {m : Cur} (hm : PoolMap m) {i : FI} {c : String}
    (hc : c = i.d ∨ (isLoc i.d = true ∧ isLoc c = true)) (hsl : slotArr c = slotArr i.d)
    {f g : String → Option String}
    (hsrc : ∀ s, i.srcs = [.reg s] → gpNameB s = true →
      ResTo slotArr f s g (renOf m x86Abi s))
    {x y : String} (hxy : (x = i.d ∧ y = c) ∨ (x ≠ i.d ∧ y ≠ c ∧ ResTo slotArr f x g y)) :
    ResTo slotArr (scanStepF slotArr i.toL f) x
      (scanStepF slotArr (FI.toL ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o)⟩) g) y := by
  intro q hf hqs
  have hmv := slotMov?_ren (ss := i.srcs) (o := i.opn) hm hc
  simp only [scanStepF, FI.toL, FI.toR] at hf ⊢
  rw [hmv]
  cases hmi : slotMov? (LinstrR.Lopn [.reg i.d] i.opn i.srcs) with
  | some p =>
    obtain ⟨d', s⟩ := p
    have hd' : d' = i.d := slotMov?_single hmi
    subst hd'
    rw [hmi] at hf
    simp only [Option.map_some]
    rcases hxy with ⟨rfl, rfl⟩ | ⟨hx, hy, hr⟩
    · simp only [ite_true] at hf ⊢
      by_cases hg : ((slotArr s).isNone && gpNameB s) = true
      · rw [ite_eq_left hg] at hf
        have hgs : gpNameB s = true := (Bool.and_eq_true _ _).mp hg |>.2
        have hsrcs : i.srcs = [.reg s] := by
          rcases slotMov?_shape hmi with h | h <;>
            · simp only [LinstrR.Lopn.injEq] at h
              exact h.2.2
        have hloc : isLoc s = true := isLoc_of_gpNameB hgs
        have hgs' := (renOf_loc hm hloc).2 hgs
        have hsl' : slotArr (renOf m x86Abi s) = none := slotArr_loc hq (renOf_loc hm hloc).1
        rw [ite_eq_left (by simp [hsl', hgs'])]
        exact hsrc s hsrcs hgs q hf hqs
      · rw [ite_eq_right hg] at hf
        cases hf
        have hns : isLoc q = false := by
          cases hl : isLoc q with
          | false => rfl
          | true => rw [slotArr_loc hq hl] at hqs; cases hqs
        rw [renOf_nonloc m hns, ite_eq_right hg]
    · simp only at hf
      rw [ite_eq_right (Ne.symm hx)] at hf
      rw [ite_eq_right (Ne.symm hy), hsl]
      split_ifs at hf ⊢
      exact hr q hf hqs
  | none =>
    rw [hmi] at hf
    simp only [Option.map_none]
    simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB] at hf ⊢
    rcases hxy with ⟨rfl, rfl⟩ | ⟨hx, hy, hr⟩
    · simp at hf
    · rw [hsl]
      have e1 : (i.d == x) = false := by simpa using Ne.symm hx
      have e2 : (c == y) = false := by simpa using Ne.symm hy
      rw [e1] at hf
      rw [e2]
      simp only [Bool.false_or] at hf ⊢
      split_ifs at hf ⊢
      exact hr q hf hqs

/-- **One step of the scan at an elided copy.** A 64-bit copy into a location whose renamed
    source is its location `c` resolves its destination as `g` resolves `c`. -/
theorem stepCopy (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {m : Cur} {i : FI} {c : String} (hd : isLoc i.d = true) (hcl : isLoc c = true)
    (hcp : isCopy64 i.opn = true) (hmap : i.srcs.map (fun o => renOp m o) = [.reg c])
    {f g : String → Option String}
    (hsrc : ∀ s, i.srcs = [.reg s] → gpNameB s = true →
      ResTo slotArr f s g (renOf m x86Abi s)) :
    ResTo slotArr (scanStepF slotArr i.toL f) i.d g c := by
  obtain ⟨s, hs, hrs⟩ : ∃ s, i.srcs = [.reg s] ∧ renOf m x86Abi s = c := by
    rcases hsr : i.srcs with _ | ⟨o, _ | ⟨o2, t⟩⟩ <;> rw [hsr] at hmap <;> simp at hmap
    cases o with
    | reg s => rw [renOp_reg] at hmap; cases hmap; exact ⟨s, rfl, rfl⟩
    | _ => simp [renOp] at hmap
  have hsl : isLoc s = true := by
    cases hl : isLoc s with
    | true => rfl
    | false => rw [renOf_nonloc m hl] at hrs; subst hrs; rw [hl] at hcl; cases hcl
  have hmi : slotMov? (LinstrR.Lopn [.reg i.d] i.opn i.srcs) = some (i.d, s) := by
    rw [hs]
    simp only [isCopy64, Bool.or_eq_true, beq_iff_eq] at hcp
    unfold slotMov?
    rcases hcp with h | h <;> rw [h] <;> simp [cellParts?_of_loc hd, cellParts?_of_loc hsl]
  intro q hf hqs
  simp only [scanStepF, FI.toL, FI.toR, hmi, ite_true] at hf
  by_cases hg : ((slotArr s).isNone && gpNameB s) = true
  · rw [ite_eq_left hg] at hf
    rw [← hrs]
    exact hsrc s hs ((Bool.and_eq_true _ _).mp hg).2 q hf hqs
  · rw [ite_eq_right hg] at hf
    cases hf
    rw [slotArr_loc hq hsl] at hqs
    cases hqs

/-- The scan after a run of fragment instructions. -/
def provI (slotArr : String → Option (String × Nat)) (l : List FI) (f : String → Option String) :
    String → Option String :=
  l.foldl (fun f i => scanStepF slotArr i.toL f) f

/-- The scans of the source and the materialized run under the current locations `m`: every
    name that is no location, and every location live in `L` at its location. -/
def RelS (slotArr : String → Option (String × Nat)) (m : Cur) (L : List String)
    (f g : String → Option String) : Prop :=
  PoolMap m ∧ (∀ x, isLoc x = false → ResTo slotArr f x g x) ∧
    ∀ n ∈ L, isLoc n = true → ResTo slotArr f n g (look m n)

/-- The instruction is a move of `slotMov?` into a name other than `R`. -/
def MoveNot (R : String) (j : FI) : Prop :=
  ∃ s, slotMov? j.toR = some (j.d, s) ∧ j.d ≠ R

/-- The entry scan along the materialized run: when every source instruction so far is a move
    into a name other than `R`, the location of `R` is `R`, every materialized instruction is a
    move, and none writes `R` when `R` is live or no location. -/
def EntryInv (done acc : List FI) (m : Cur) (L : List String) : Prop :=
  ∀ R, (∀ j ∈ done, MoveNot R j) →
    (isLoc R = true → look m R = R) ∧ (∀ j ∈ acc, ∃ s, slotMov? j.toR = some (j.d, s)) ∧
      ((isLoc R = true → R ∈ L) → ∀ j ∈ acc, j.d ≠ R)

/-- Every source instruction writing an array slot is a save `MOVQ qsave.R, R` after moves into
    names other than `R` only, and the proposition `P` holds. -/
def SaveCond (slotArr : String → Option (String × Nat)) (full : List FI) (P : Prop) : Prop :=
  ∀ pre i post, full = pre ++ i :: post → (slotArr i.d).isSome = true →
    P ∧ ∃ R, slotMov? i.toR = some (i.d, R) ∧ i.d = slotOfReg R ∧ ∀ j ∈ pre, MoveNot R j

/-- A materialized instruction after the instructions `pre`: no access, and no array-slot
    destination unless it is a save after moves into names other than its register. -/
def OutOk (slotArr : String → Option (String × Nat)) (P : Prop) (pre : List FI) (j : FI) :
    Prop :=
  isAccB j.toR = false ∧ isArrImmB j.toR = false ∧ (slotArr j.d = none ∨
    (P ∧ ∃ R, slotMov? j.toR = some (j.d, R) ∧ j.d = slotOfReg R ∧ ∀ j' ∈ pre, MoveNot R j'))

theorem isAccB_of_wf {i : FI} (h : i.wf = true) (ds : List LOperand) (ss : List LOperand) :
    isAccB (.Lopn ds i.opn ss) = false := by
  simp only [FI.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  simp [isAccB, h.1.2, h.2]

/-- An `Lopn` whose mnemonic reads as no `ZEROARR` or `STOREIMM` after `untagCaret` is no
    constant-index array write. -/
theorem isArrImmB_of_untagCaret_ne {o : String}
    (h : LprogAsmPrinter.untagCaret o ≠ "ZEROARR" ∧ LprogAsmPrinter.untagCaret o ≠ "STOREIMM")
    (ds : List LOperand) (ss : List LOperand) : isArrImmB (.Lopn ds o ss) = false := by
  simp [isArrImmB, h.1, h.2]

/-- An `Lopn` with an `AccUntagged` mnemonic other than `ZEROARR` and `STOREIMM` is no
    constant-index array write. -/
theorem isArrImmB_of_ne {o : String} (h : o ≠ "ZEROARR" ∧ o ≠ "STOREIMM") (ht : AccUntagged o)
    (ds : List LOperand) (ss : List LOperand) : isArrImmB (.Lopn ds o ss) = false :=
  isArrImmB_of_untagCaret_ne ⟨untagCaret_ne_of_accUntagged ht (by simp) h.1,
    untagCaret_ne_of_accUntagged ht (by simp) h.2⟩ ds ss

/-- A mnemonic that reads as `ZEROARR` or `STOREIMM` after `untagCaret` is outside the
    recognized alphabet. -/
theorem isRecognizedOpn_eq_false_of_untagCaret {o b : String}
    (hu : LprogAsmPrinter.untagCaret o = b) (hb : b = "ZEROARR" ∨ b = "STOREIMM") :
    isRecognizedOpn o = false := by
  by_cases hc : '^' ∈ o.toList
  · have hcc : o.toList.contains '^' = true := by simpa using hc
    have hT : o.toList.takeWhile (· != '^') = b.toList := by
      unfold LprogAsmPrinter.untagCaret at hu
      simp only [hcc, ↓reduceIte] at hu
      split at hu
      · exfalso
        have := congrArg (fun s => s.toList.getLast?) hu
        rcases hb with rfl | rfl <;> simp at this
      · unfold stripWidthTag at hu
        simp only [hcc, ↓reduceIte] at hu
        rw [← hu, String.toList_ofList]
    have hP : b.toList <+: (LprogAsmPrinter.stripAbiTag o).toList := by
      have hpre : b.toList <+: o.toList := hT ▸ List.takeWhile_prefix _
      have hcol : ∀ c ∈ b.toList, (c != ':') = true := by
        rcases hb with rfl | rfl <;> decide
      unfold LprogAsmPrinter.stripAbiTag
      split
      · rw [String.toList_ofList]
        obtain ⟨t, ht⟩ := hpre
        rw [← ht, List.takeWhile_append_of_pos hcol]
        exact List.prefix_append _ _
      · unfold stripWidthTag
        simp only [hcc, ↓reduceIte, String.toList_ofList, hT, List.prefix_refl]
    have hS : parseImmShiftMnem o = none := by
      unfold parseImmShiftMnem
      simp only [hcc, ↓reduceIte, hT]
      split
      · rcases hb with rfl | rfl <;> rfl
      · rfl
    unfold isRecognizedOpn
    rw [hS]
    generalize LprogAsmPrinter.stripAbiTag o = s at hP ⊢
    simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_false_iff]
    right
    split <;> first | rfl | (rcases hb with rfl | rfl <;> revert hP <;> decide)
  · have ho : o = b := by
      grind only [WidthTagSimp.untagCaret_lit]
    subst ho
    rcases hb with rfl | rfl <;>
      simp [isRecognizedOpn, LcmdCopyPropagate.implicitReads, LprogAsmPrinter.stripAbiTag,
        isPrefixOf_list] <;> decide

/-- An instruction of the fragment over the default alphabet reads as no `ZEROARR` or
    `STOREIMM` after `untagCaret`. -/
theorem fragOf?_untagCaret_ne {li : Linstr} {i : FI} (h : fragOf? li = some i) :
    LprogAsmPrinter.untagCaret i.opn ≠ "ZEROARR" ∧
      LprogAsmPrinter.untagCaret i.opn ≠ "STOREIMM" := by
  unfold fragOf? at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hr, -⟩ := hc
      dsimp only
      constructor <;> intro h' <;>
        simp [isRecognizedOpn_eq_false_of_untagCaret h' (by simp)] at hr
    · cases h
  · cases h

/-- An instruction of the fragment over the default alphabet is no `ZEROARR` or `STOREIMM`. -/
theorem fragOf?_opn_ne {li : Linstr} {i : FI} (h : fragOf? li = some i) :
    i.opn ≠ "ZEROARR" ∧ i.opn ≠ "STOREIMM" := by
  unfold fragOf? at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hr, -⟩ := hc
      dsimp only
      constructor <;> rintro rfl <;> revert hr <;>
        simp [isRecognizedOpn, LcmdCopyPropagate.implicitReads, LprogAsmPrinter.stripAbiTag,
          isPrefixOf_list] <;> decide
    · cases h
  · cases h

theorem poolMap_loc {m : Cur} (hm : PoolMap m) {n : String} (hn : isLoc n = true) :
    isLoc (look m n) = true := by
  rcases hm n with h | h
  · rw [h]; exact hn
  · exact isLoc_of_gpNameB (gpNameB_of_isPool h)

theorem isLoc_of_okLoc {d c : String} (hd : isLoc d = true) (h : okLoc d c = true) :
    isLoc c = true := by
  simp only [okLoc, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact isLoc_of_isPool h
  · rw [h]; exact hd

/-- The step of an `EntryInv` across a source instruction that adds `new` to the materialized
    run. -/
theorem entryInv_step {done acc new : List FI} {m m' : Cur} {i : FI} {la : List String}
    (hE : EntryInv done acc m (liveBefore i la))
    (hlook : ∀ R, i.d ≠ R → look m' R = look m R)
    (hnew : ∀ s, slotMov? i.toR = some (i.d, s) → ∀ j ∈ new,
      (∃ s', slotMov? j.toR = some (j.d, s')) ∧
        ∀ R, (∀ j ∈ done, MoveNot R j) → i.d ≠ R → (isLoc R = true → R ∈ la) → j.d ≠ R) :
    EntryInv (done ++ [i]) (new ++ acc) m' la := by
  intro R hR
  have hdone : ∀ j ∈ done, MoveNot R j := fun j hj => hR j (by simp [hj])
  obtain ⟨s, hs, hiR⟩ := hR i (by simp)
  obtain ⟨hl, hmv, hlive⟩ := hE R hdone
  refine ⟨fun h => by rw [hlook R hiR]; exact hl h, fun j hj => ?_, fun hL j hj => ?_⟩
  · rcases List.mem_append.mp hj with hj | hj
    · exact (hnew s hs j hj).1
    · exact hmv j hj
  · rcases List.mem_append.mp hj with hj | hj
    · exact (hnew s hs j hj).2 R hdone hiR hL
    · exact hlive (fun h => mem_liveBefore (hL h) (Ne.symm hiR)) j hj

/-- **The materialized run under the scans.** When `goAcc` accepts the decisions for the
    annotated run of `is` from locations `m`, the materialized instructions have no access and
    no array-slot destination other than a save after moves into names other than its
    register, and the scan after them resolves every name that is no location or is live out
    wherever the scan after the source run does. -/
theorem goAcc_img (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (lend : List String) {P : Prop} (full : List FI) (hin : SaveCond slotArr full P) :
    ∀ (is done : List FI) (m : Cur) (cs : List String) (acc out : List FI)
      (f g : String → Option String),
      full = done ++ is → (∀ i ∈ is, i.wf = true) →
      (∀ i ∈ is, LprogAsmPrinter.untagCaret i.opn ≠ "ZEROARR" ∧
        LprogAsmPrinter.untagCaret i.opn ≠ "STOREIMM") →
      goAcc lend m (annotate lend is).1 cs acc = some out →
      RelS slotArr m (annotate lend is).2 f g →
      EntryInv done acc m (annotate lend is).2 →
      ∃ rest, out = acc.reverse ++ rest ∧
        (∀ t j, rest[t]? = some j → OutOk slotArr P (acc.reverse ++ rest.take t) j) ∧
        ∀ x, (isLoc x = false ∨ x ∈ lend) →
          ResTo slotArr (provI slotArr is f) x (provI slotArr rest g) x := by
  intro is
  induction is with
  | nil =>
    intro done m cs acc out f g _ _ _ hgo hR _
    cases cs with
    | cons _ _ => simp [annotate, goAcc] at hgo
    | nil =>
      simp only [annotate, List.foldr_nil, goAcc] at hgo hR
      split at hgo
      · rename_i hall
        simp only [Option.some.injEq] at hgo
        subst hgo
        refine ⟨[], by simp, by simp, fun x hx => ?_⟩
        simp only [provI, List.foldl_nil]
        by_cases hl : isLoc x = true
        · have hxl : x ∈ lend := by
            rcases hx with h | h
            · simp [hl] at h
            · exact h
          have h1 := hR.2.2 x hxl hl
          have h2 : look m x = x := by simpa using List.all_eq_true.1 hall x hxl
          rw [h2] at h1
          exact h1
        · exact hR.2.1 x (by simpa using hl)
      · exact absurd hgo (by simp)
  | cons i is ih =>
    intro done m cs acc out f g hfull hwf himm hgo hR hE
    have hwfi : i.wf = true := hwf i (by simp)
    have hwfs : ∀ j ∈ is, j.wf = true := fun j hj => hwf j (by simp [hj])
    have himmi := himm i (by simp)
    have himms : ∀ j ∈ is, LprogAsmPrinter.untagCaret j.opn ≠ "ZEROARR" ∧
        LprogAsmPrinter.untagCaret j.opn ≠ "STOREIMM" :=
      fun j hj => himm j (by simp [hj])
    rw [annotate_cons] at hgo hR hE
    set la := (annotate lend is).2 with hla
    have hfull' : full = (done ++ [i]) ++ is := by simp [hfull]
    have hli : i.toL.li_i = .Lopn [.reg i.d] i.opn i.srcs := rfl
    have hreads : ∀ n ∈ i.reads, n ∈ liveBefore i la := fun n hn => reads_mem_liveBefore hn
    have hsrc : ∀ s, i.srcs = [.reg s] → gpNameB s = true →
        ResTo slotArr f s g (renOf m x86Abi s) := by
      intro s hs hgs
      have hl := isLoc_of_gpNameB hgs
      have hr : s ∈ i.reads := by simp [FI.reads, hs, opReads, hl]
      have := hR.2.2 s (hreads s hr) hl
      simpa [renOf, hl] using this
    have hpi : provI slotArr (i :: is) f = provI slotArr is (scanStepF slotArr i.toL f) := rfl
    -- the emitted instruction and the facts shared by both emitting branches
    have emit : ∀ (c : String) (m' : Cur) (cs' : List String),
        (c = i.d ∨ (isLoc i.d = true ∧ isLoc c = true)) → slotArr c = slotArr i.d →
        (∀ R, (∀ j ∈ done, MoveNot R j) → i.d ≠ R → (isLoc R = true → R ∈ la) → c ≠ R) →
        (∀ R, i.d ≠ R → look m' R = look m R) →
        RelS slotArr m' la (scanStepF slotArr i.toL f)
          (scanStepF slotArr (FI.toL ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o)⟩) g) →
        (isLoc i.d = true → slotArr c = none) →
        (isLoc i.d = false → c = i.d) →
        goAcc lend m' (annotate lend is).1 cs'
          (⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o)⟩ :: acc) = some out →
        ∃ rest, out = acc.reverse ++ rest ∧
          (∀ t j, rest[t]? = some j → OutOk slotArr P (acc.reverse ++ rest.take t) j) ∧
          ∀ x, (isLoc x = false ∨ x ∈ lend) →
            ResTo slotArr (provI slotArr (i :: is) f) x (provI slotArr rest g) x := by
      intro c m' cs' hc hsl hcR hlook hR' hcl hcn hgo'
      let j : FI := ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o)⟩
      have hE' : EntryInv (done ++ [i]) ([j] ++ acc) m' la := by
        refine entryInv_step hE hlook fun s hs j' hj' => ?_
        simp only [List.mem_singleton] at hj'
        subst hj'
        refine ⟨⟨renOf m x86Abi s, ?_⟩, fun R h0 hR1 hR2 => hcR R h0 hR1 hR2⟩
        have := slotMov?_ren (ss := i.srcs) (o := i.opn) hR.1 hc
        simp only [FI.toR] at hs this ⊢
        rw [this, hs]
        rfl
      obtain ⟨rest, h1, h2, h3⟩ := ih (done ++ [i]) m' cs' (j :: acc) out _ _ hfull' hwfs himms hgo'
        hR' hE'
      refine ⟨j :: rest, by simp [h1], fun t j' ht => ?_, fun x hx => ?_⟩
      · cases t with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
          subst ht
          refine ⟨isAccB_of_wf hwfi _ _, isArrImmB_of_untagCaret_ne himmi _ _, ?_⟩
          by_cases hdl : isLoc i.d = true
          · exact Or.inl (hcl hdl)
          · have hce := hcn (by simpa using hdl)
            cases hs : slotArr c with
            | none => exact Or.inl rfl
            | some _ =>
              right
              have hsi : (slotArr i.d).isSome = true := by rw [← hsl, hs]; rfl
              obtain ⟨hP, R, hmvR, hdR, hpre⟩ := hin done i is hfull hsi
              obtain ⟨hl, hmv, hlive⟩ := hE R hpre
              have hsR : i.srcs = [.reg R] := by
                rcases slotMov?_shape hmvR with h | h <;>
                  · simp only [FI.toR, LinstrR.Lopn.injEq] at h
                    exact h.2.2
              have hRL : isLoc R = true → R ∈ liveBefore i la := fun hRl =>
                hreads R (by simp [FI.reads, hsR, opReads, hRl])
              have hren : renOf m x86Abi R = R := by
                by_cases hRl : isLoc R = true
                · simp [renOf, hRl, hl hRl]
                · exact renOf_nonloc m (by simpa using hRl)
              refine ⟨hP, R, ?_, by simp only [j]; rw [hce]; exact hdR, ?_⟩
              · simp only [j, FI.toR, hsR, List.map_cons, List.map_nil, renOp_reg, hren, hce]
                simpa [FI.toR, hsR] using hmvR
              · intro j' hj'
                simp only [List.take_zero, List.append_nil, List.mem_reverse] at hj'
                obtain ⟨s', hs'⟩ := hmv j' hj'
                exact ⟨s', hs', hlive hRL j' hj'⟩
        | succ t =>
          simp only [List.getElem?_cons_succ] at ht
          have := h2 t j' ht
          simpa using this
      · rw [hpi]
        exact h3 x hx
    cases cs with
    | nil => simp [goAcc] at hgo
    | cons c cs =>
    simp only [goAcc] at hgo
    by_cases hb : basesOk m i = true
    swap
    · rw [ite_eq_right hb] at hgo; exact absurd hgo (by simp)
    rw [ite_eq_left hb] at hgo
    by_cases hd : isLoc i.d = true
    · rw [ite_eq_left hd] at hgo
      have hdsl : slotArr i.d = none := slotArr_loc hq hd
      by_cases hok : (okLoc i.d c && shapeOk m i c) = true
      swap
      · rw [ite_eq_right hok] at hgo; exact absurd hgo (by simp)
      rw [ite_eq_left hok] at hgo
      have hokl : okLoc i.d c = true := ((Bool.and_eq_true _ _).mp hok).1
      have hc : isLoc c = true := isLoc_of_okLoc hd hokl
      have hcsl : slotArr c = none := slotArr_loc hq hc
      have hstay : ∀ x, x ≠ i.d → scanStepF slotArr i.toL f x = f x :=
        fun x hx => scanStepF_single_ne hdsl hli hx f
      by_cases hcp : (isCopy64 i.opn && i.srcs.map (fun o => renOp m o) == [.reg c]) = true
      · -- a self-copy: dropped
        rw [ite_eq_left hcp] at hgo
        simp only [Bool.and_eq_true, beq_iff_eq] at hcp
        obtain ⟨hcopyi, hmap⟩ := hcp
        have hR' : RelS slotArr (m.insert i.d c) la (scanStepF slotArr i.toL f) g := by
          refine ⟨poolMap_insert hR.1 hokl, fun x hx => ?_, fun n hn hnl => ?_⟩
          · have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; cases hx
            intro q hf; rw [hstay x hxd] at hf; exact hR.2.1 x hx q hf
          · rw [look_insert]
            by_cases hnd : i.d = n
            · subst hnd; rw [ite_eq_left rfl]
              exact stepCopy hq hd hc hcopyi hmap hsrc
            · rw [ite_eq_right hnd]
              intro q hf; rw [hstay n (Ne.symm hnd)] at hf
              exact hR.2.2 n (mem_liveBefore hn (Ne.symm hnd)) hnl q hf
        have hE' : EntryInv (done ++ [i]) ([] ++ acc) (m.insert i.d c) la :=
          entryInv_step hE (fun R hR => by rw [look_insert, ite_eq_right hR]) (by simp)
        obtain ⟨rest, h1, h2, h3⟩ := ih (done ++ [i]) _ cs acc out _ _ hfull' hwfs himms hgo hR'
          (by simpa using hE')
        exact ⟨rest, h1, h2, fun x hx => by rw [hpi]; exact h3 x hx⟩
      · rw [ite_eq_right hcp] at hgo
        by_cases hdead : (movClass i.opn && !la.contains i.d) = true
        · -- a dead move: dropped
          rw [ite_eq_left hdead] at hgo
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
            decide_eq_false_iff_not] at hdead
          have hR' : RelS slotArr m la (scanStepF slotArr i.toL f) g := by
            refine ⟨hR.1, fun x hx => ?_, fun n hn hnl => ?_⟩
            · have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; cases hx
              intro q hf; rw [hstay x hxd] at hf; exact hR.2.1 x hx q hf
            · have hnd : n ≠ i.d := fun h => hdead.2 (h ▸ hn)
              intro q hf; rw [hstay n hnd] at hf
              exact hR.2.2 n (mem_liveBefore hn hnd) hnl q hf
          have hE' : EntryInv (done ++ [i]) ([] ++ acc) m la :=
            entryInv_step hE (fun _ _ => rfl) (by simp)
          obtain ⟨rest, h1, h2, h3⟩ := ih (done ++ [i]) _ cs acc out _ _ hfull' hwfs himms hgo hR'
            (by simpa using hE')
          exact ⟨rest, h1, h2, fun x hx => by rw [hpi]; exact h3 x hx⟩
        · rw [ite_eq_right hdead] at hgo
          by_cases hnc : noClobber m la i.d c = true
          swap
          · rw [ite_eq_right hnc] at hgo; exact absurd hgo (by simp)
          rw [ite_eq_left hnc] at hgo
          have hne : ∀ n ∈ la, n ≠ i.d → look m n ≠ c := by
            intro n hn hnd
            have h1 := List.all_eq_true.1 hnc n hn
            simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
            exact h1.resolve_left hnd
          refine emit c (m.insert i.d c) cs (Or.inr ⟨hd, hc⟩) (by rw [hcsl, hdsl])
            (fun R h0 hR1 hR2 => ?_) (fun R hR => by rw [look_insert, ite_eq_right hR])
            ⟨poolMap_insert hR.1 hokl, fun x hx => ?_, fun n hn hnl => ?_⟩
            (fun _ => hcsl) (fun h => by rw [hd] at h; cases h) hgo
          · by_cases hRl : isLoc R = true
            · have := hne R (hR2 hRl) (Ne.symm hR1)
              rw [(hE R h0).1 hRl] at this
              exact fun h => this h.symm
            · intro h; subst h; exact hRl hc
          · have hxd : x ≠ i.d := fun h => by rw [h, hd] at hx; cases hx
            have hxc : x ≠ c := fun h => by rw [h, hc] at hx; cases hx
            exact stepRen hq hR.1 (Or.inr ⟨hd, hc⟩) (by rw [hcsl, hdsl]) hsrc
              (Or.inr ⟨hxd, hxc, hR.2.1 x hx⟩)
          · rw [look_insert]
            by_cases hnd : i.d = n
            · subst hnd; rw [ite_eq_left rfl]
              exact stepRen hq hR.1 (Or.inr ⟨hd, hc⟩) (by rw [hcsl, hdsl]) hsrc
                (Or.inl ⟨rfl, rfl⟩)
            · rw [ite_eq_right hnd]
              exact stepRen hq hR.1 (Or.inr ⟨hd, hc⟩) (by rw [hcsl, hdsl]) hsrc
                (Or.inr ⟨Ne.symm hnd, hne n hn (Ne.symm hnd),
                  hR.2.2 n (mem_liveBefore hn (Ne.symm hnd)) hnl⟩)
    · -- a write to a name that is no location
      rw [ite_eq_right hd] at hgo
      simp only [Bool.not_eq_true] at hd
      by_cases hsh : shapeOk m i i.d = true
      swap
      · rw [ite_eq_right hsh] at hgo; exact absurd hgo (by simp)
      rw [ite_eq_left hsh] at hgo
      refine emit i.d m cs (Or.inl rfl) rfl (fun R _ hR1 _ => hR1) (fun _ _ => rfl)
        ⟨hR.1, fun x hx => ?_, fun n hn hnl => ?_⟩
        (fun h => by rw [hd] at h; cases h) (fun _ => rfl) hgo
      · by_cases hxd : x = i.d
        · subst hxd
          exact stepRen hq hR.1 (Or.inl rfl) rfl hsrc (Or.inl ⟨rfl, rfl⟩)
        · exact stepRen hq hR.1 (Or.inl rfl) rfl hsrc (Or.inr ⟨hxd, hxd, hR.2.1 x hx⟩)
      · have hnd : n ≠ i.d := fun h => by rw [h, hd] at hnl; cases hnl
        have hyd : look m n ≠ i.d := fun h => by
          have := poolMap_loc hR.1 hnl; rw [h, hd] at this; cases this
        exact stepRen hq hR.1 (Or.inl rfl) rfl hsrc
          (Or.inr ⟨hnd, hyd, hR.2.2 n (mem_liveBefore hn hnd) hnl⟩)

/-! ## 7. The register re-allocation: the body -/

/-- The scan after a list of instructions, from the scan `f` in front of them. -/
def provF (slotArr : String → Option (String × Nat)) (l : Lcmd) (f : String → Option String) :
    String → Option String :=
  l.foldl (fun f j => scanStepF slotArr j f) f

theorem provI_eq (l : List FI) (f : String → Option String) :
    provI slotArr l f = provF slotArr (l.map FI.toL) f := by
  simp [provI, provF, List.foldl_map]

theorem provF_append (a c : Lcmd) (f : String → Option String) :
    provF slotArr (a ++ c) f = provF slotArr c (provF slotArr a f) := by
  simp [provF, List.foldl_append]

/-- The reload scan before position `k` is the scan after the first `k` instructions. -/
theorem reloadOf_eq_provF (b : Lcmd) :
    ∀ k, k ≤ b.length →
      (fun y => reloadOf slotArr b k y) = provF slotArr (b.take k) (fun _ => none)
  | 0, _ => by funext y; simp [reloadOf, provF]
  | k + 1, hk => by
    have hkb : k < b.length := by omega
    funext y
    rw [reloadOf_succ_eq slotArr (List.getElem?_eq_getElem hkb), List.take_add_one,
      List.getElem?_eq_getElem hkb, Option.toList_some, provF_append,
      ← reloadOf_eq_provF b k (by omega)]
    rfl

/-- Dominance on `S` is kept along a common list of instructions. -/
theorem domOn_provF {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q) :
    ∀ (l : Lcmd) {f g : String → Option String}, DomOn slotArr S f g →
      DomOn slotArr S (provF slotArr l f) (provF slotArr l g)
  | [], _, _, h => h
  | j :: l, _, _, h => domOn_provF hS l (domOn_step hS h j)

theorem domOn_mono {S S' : String → Prop} (hS : ∀ x, S' x → S x)
    {f g : String → Option String} (h : DomOn slotArr S f g) : DomOn slotArr S' f g :=
  fun x hx => h x (hS x hx)

/-- An instruction of a body that is a move of `slotMov?` is in the fragment. -/
theorem fragOf?_of_slotMov {li : Linstr} {d s : String} (h : slotMov? li.li_i = some (d, s)) :
    fragOf? li ≠ none := by
  obtain ⟨ii, r⟩ := li
  rcases slotMov?_shape h with h' | h' <;> (simp only at h'; subst h') <;>
    simp [fragOf?, FI.wf, regOrImm, isRecognizedOpn_movq, isRecognizedOpn_mov64]

/-- `slotWriteB` at an instruction that is no move reads no position of the body. -/
theorem slotWriteB_noMove {r : LinstrR} (hm : slotMov? r = none) (b b' : Lcmd) (k k' : Nat) :
    slotWriteB slotArr b k r = slotWriteB slotArr b' k' r := by
  cases r with
  | Lopn ds o ss => simp only [slotWriteB, hm]
  | _ => rfl

/-- The return instruction ends every scan. -/
theorem scanStepF_ret {li : Linstr} (h : li.li_i = .Lret) (f : String → Option String) :
    scanStepF slotArr li f = fun _ => none := by
  funext b
  simp [scanStepF, h, slotMov?]

/-- The position of an instruction of a concatenation. -/
theorem flatten_locate : ∀ (segs : List Lcmd) (k : Nat), k < segs.flatten.length →
    ∃ j o, ∃ (hj : j < segs.length), o < segs[j].length ∧ k = bdry segs j + o
  | [], k, h => by simp at h
  | a :: segs, k, h => by
    by_cases hk : k < a.length
    · exact ⟨0, k, by simp, by simpa using hk, by simp⟩
    · obtain ⟨j, o, hj, ho, he⟩ := flatten_locate segs (k - a.length)
        (by simp at h ⊢; omega)
      exact ⟨j + 1, o, by simpa using hj, by simpa using ho,
        by rw [bdry_cons_succ]; omega⟩

theorem flatten_getElem? (segs : List Lcmd) {j o : Nat} (hj : j < segs.length)
    (ho : o < segs[j].length) : segs.flatten[bdry segs j + o]? = some segs[j][o] := by
  rw [flatten_split segs j hj, bdry, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left ho, List.getElem?_eq_getElem ho]

theorem flatten_take (segs : List Lcmd) {j o : Nat} (hj : j < segs.length)
    (ho : o ≤ segs[j].length) :
    segs.flatten.take (bdry segs j + o) = (segs.take j).flatten ++ segs[j].take o := by
  rw [flatten_split segs j hj, bdry, List.take_append, List.take_of_length_le (by omega),
    Nat.add_sub_cancel_left, List.take_append_of_le_length ho]

theorem entryInv_nil (L : List String) : EntryInv [] [] ({} : Cur) L :=
  fun R _ => ⟨fun _ => look_empty R, by simp, by simp⟩

/-- The source run itself: its instructions in the fragment, after the instructions in front of
    them. -/
theorem outOk_self {P : Prop} {is : List FI} (hwf : ∀ i ∈ is, i.wf = true)
    (himm : ∀ i ∈ is, LprogAsmPrinter.untagCaret i.opn ≠ "ZEROARR" ∧
      LprogAsmPrinter.untagCaret i.opn ≠ "STOREIMM")
    (hin : SaveCond slotArr is P) {t : Nat} {j : FI} (ht : is[t]? = some j) :
    OutOk slotArr P (is.take t) j := by
  have htl : t < is.length := (List.getElem?_eq_some_iff.mp ht).1
  have hjt : is[t] = j := (List.getElem?_eq_some_iff.mp ht).2
  have hsplit : is = is.take t ++ j :: is.drop (t + 1) := by
    rw [← hjt, ← List.drop_eq_getElem_cons htl, List.take_append_drop]
  refine ⟨isAccB_of_wf (hwf j (List.mem_of_getElem? ht)) _ _,
    isArrImmB_of_untagCaret_ne (himm j (List.mem_of_getElem? ht)) _ _, ?_⟩
  cases hs : slotArr j.d with
  | none => exact Or.inl rfl
  | some _ => exact Or.inr (hin _ j _ hsplit (by simp [hs]))

/-- **The re-allocation of one run.** At a run of the pieces of a body, the scan after the
    re-allocated run dominates the scan after the run on the names of the next piece, from
    scans that agree on the names of the run, and every re-allocated instruction is in the
    image class after the re-allocated instructions in front of it. -/
theorem run_img (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (res : List String) (hres : ∀ x ∈ res, isFrame x = false) (lf : Std.HashSet String)
    (ps : List Piece) (hadj : noAdjRuns ps = true) (j : Nat) (is : List FI)
    (hj : ps[j]? = some (.run is)) (hwf : ∀ i ∈ is, i.wf = true)
    (himm : ∀ i ∈ is, LprogAsmPrinter.untagCaret i.opn ≠ "ZEROARR" ∧
      LprogAsmPrinter.untagCaret i.opn ≠ "STOREIMM") {P : Prop}
    (hin : SaveCond slotArr is P) {f g : String → Option String}
    (hD : DomOn slotArr (Need ps lf j) f g) :
    (∀ t j', (reallocRun (lendAt res lf ps j) is)[t]? = some j' →
      OutOk slotArr P ((reallocRun (lendAt res lf ps j) is).take t) j') ∧
    DomOn slotArr (Need ps lf (j + 1)) (provI slotArr is f)
      (provI slotArr (reallocRun (lendAt res lf ps j) is) g) := by
  have hrun := not_retAt_run hj
  have hgp : ∀ q, gpNameB q = true → Need ps lf j q := fun q hq' =>
    Or.inr (Or.inl ⟨by rw [isPhysGP_eq_gpNameB]; exact hq', hrun⟩)
  have hmono : ∀ x, Need ps lf (j + 1) x → Need ps lf j x :=
    fun x => Need_mono (Nat.le_succ j) hrun
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    have hR0 : RelS slotArr {} (annotate (lendAt res lf ps j) is).2 f g := by
      refine ⟨poolMap_empty, fun x hx => hD x (Or.inl hx), fun n hn hl => ?_⟩
      rw [look_empty]
      refine hD n ?_
      rcases mem_annotate_snd _ is n hn with hn | ⟨i, hi, hn⟩
      · simp only [lendAt, List.mem_append] at hn
        rcases hn with hn | hn
        · exact Or.inr (Or.inl ⟨regsAfter_gp res hres _ hn hl, hrun⟩)
        · rw [Std.HashSet.mem_toList, mem_foldr_stepF_snd] at hn
          rcases hn with hn | hn
          · exact Or.inr (Or.inr (Or.inl hn))
          · exact Or.inr (Or.inr (Or.inr (mem_flatMap_drop (Nat.le_succ j) hn)))
      · rcases reads_need hn hl with hg | hf
        · exact Or.inr (Or.inl ⟨hg, hrun⟩)
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [drop_eq_cons hj, List.flatMap_cons, List.mem_append]
          left
          simp only [Piece.frames, List.mem_flatMap]
          exact ⟨i, hi, hf⟩
    obtain ⟨rest, h1, h2, h3⟩ := goAcc_img hq _ is hin is [] {} cs [] out f g (by simp) hwf
      himm hcs hR0 (entryInv_nil _)
    simp only [List.reverse_nil, List.nil_append] at h1
    subst h1
    refine ⟨fun t j' ht => by simpa using h2 t j' ht, fun x hx q hfx hqs => ?_⟩
    refine h3 x ?_ q hfx hqs
    rcases hx with hx | ⟨hg, hr⟩ | hx | hx
    · exact Or.inl hx
    · right
      simp only [lendAt, List.mem_append]
      left
      have hregs : regsAfter res (outSegs res lf (ps.drop (j + 1))).flatten = physGPs := by
        cases hp : ps[j + 1]? with
        | none =>
            rw [List.drop_eq_nil_of_le (by
              by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hp; cases hp)]
            rfl
        | some p =>
            have hnr := noAdjRuns_getElem ps hadj j is hj p hp
            cases p with
            | run _ => cases hnr
            | bar li =>
                rw [drop_eq_cons hp]
                simp only [outSegs, outSeg, List.flatten_cons, List.cons_append,
                  List.nil_append]
                obtain ⟨ii, ir⟩ := li
                cases ir with
                | Lret => exact absurd ⟨ii, hp⟩ hr
                | _ => rfl
      rw [hregs]
      exact isPhysGP_mem_physGPs hg
    · right
      simp only [lendAt, List.mem_append, Std.HashSet.mem_toList, mem_foldr_stepF_snd]
      exact Or.inr (Or.inl hx)
    · right
      simp only [lendAt, List.mem_append, Std.HashSet.mem_toList, mem_foldr_stepF_snd]
      exact Or.inr (Or.inr hx)
  · refine ⟨fun t j' ht => outOk_self hwf himm hin ht, ?_⟩
    rw [provI_eq, provI_eq]
    exact domOn_mono hmono (domOn_provF hgp _ hD)

/-- The input segments of the pieces of a body. -/
abbrev inSegs (body : Lcmd) : List Lcmd := (pieces body).map Piece.toLcmd

theorem inSegs_getElem? (body : Lcmd) (j : Nat) :
    (inSegs body)[j]? = (pieces body)[j]?.map Piece.toLcmd := by
  simp [inSegs]

/-- **The saves of a run.** In a body in the class, a run's instruction that writes an array
    slot is a save after moves into names other than its register, and the run is the first
    piece. -/
theorem saveCond_run {body : Lcmd} (h : physImgB slotArr body = true) {j : Nat} {is : List FI}
    (hj : (pieces body)[j]? = some (.run is)) : SaveCond slotArr is (j = 0) := by
  intro pre i post his hsi
  have hjl : j < (inSegs body).length := by
    simpa [inSegs] using (List.getElem?_eq_some_iff.mp hj).1
  have hseg : (inSegs body)[j] = is.map FI.toL := by
    have := inSegs_getElem? body j
    rw [hj, List.getElem?_eq_getElem hjl] at this
    simpa [Piece.toLcmd] using this
  have hbody : body = (inSegs body).flatten := (pieces_flatten body).symm
  have ho : pre.length < (inSegs body)[j].length := by rw [hseg, his]; simp
  have hk : body[bdry (inSegs body) j + pre.length]? = some i.toL := by
    have := flatten_getElem? (inSegs body) hjl ho
    rw [← hbody] at this
    rw [this]
    simp [hseg, his]
  have hw := (physImgB_getElem h hk).2
  simp only [FI.toL, FI.toR, slotWriteB, List.all_cons, List.all_nil, Bool.and_true] at hw
  have hnone : (slotArr i.d).isNone = false := by simpa using hsi
  rw [hnone, Bool.false_or] at hw
  cases hm : slotMov? (LinstrR.Lopn [.reg i.d] i.opn i.srcs) with
  | none => rw [hm] at hw; cases hw
  | some p =>
    obtain ⟨q', R⟩ := p
    have hq' : q' = i.d := slotMov?_single hm
    subst hq'
    rw [hm] at hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨hdR, he⟩ := hw
    have htake : body.take (bdry (inSegs body) j + pre.length) =
        ((inSegs body).take j).flatten ++ pre.map FI.toL := by
      have := flatten_take (inSegs body) hjl ho.le
      rw [← hbody] at this
      rw [this, hseg, his]
      simp
    unfold entryRegB at he
    rw [htake, List.all_eq_true] at he
    refine ⟨?_, R, hm, hdR, fun j' hj' => ?_⟩
    · by_contra hj0
      obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
      have hj₀ : j₀ < (pieces body).length := by simp [inSegs] at hjl; omega
      cases hp : (pieces body)[j₀] with
      | run is₀ =>
        have := noAdjRuns_getElem _ (pieces_noAdjRuns body) j₀ is₀
          (by rw [List.getElem?_eq_getElem hj₀, hp]) _ hj
        cases this
      | bar li₀ =>
        have hgood : fragOf? li₀ = none := by
          have := pieces_good body _ (List.getElem_mem hj₀)
          rw [hp] at this
          exact this
        have hmem : li₀ ∈ ((inSegs body).take (j₀ + 1)).flatten := by
          rw [List.take_add_one, List.getElem?_eq_getElem (by simpa [inSegs] using hj₀)]
          simp [inSegs, hp, Piece.toLcmd]
        have := he li₀ (List.mem_append_left _ hmem)
        cases hm₀ : slotMov? li₀.li_i with
        | none => rw [hm₀] at this; cases this
        | some p₀ =>
          obtain ⟨d₀, s₀⟩ := p₀
          exact fragOf?_of_slotMov hm₀ hgood
    · have := he j'.toL (List.mem_append_right _ (List.mem_map_of_mem hj'))
      cases hm' : slotMov? j'.toR with
      | none => simp only [FI.toL] at this; rw [hm'] at this; cases this
      | some p' =>
        obtain ⟨d', s'⟩ := p'
        have hd' : d' = j'.d := slotMov?_single hm'
        subst hd'
        simp only [FI.toL] at this
        rw [hm'] at this
        exact ⟨s', hm', by simpa using this⟩

/-- **The scans at the boundaries of the pieces.** -/
theorem dom_pieces (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (res : List String) (hres : ∀ x ∈ res, isFrame x = false) {body : Lcmd}
    (h : physImgB slotArr body = true) :
    ∀ j, j ≤ (pieces body).length →
      DomOn slotArr (Need (pieces body) (labelLiveFrames body) j)
        (provF slotArr ((inSegs body).take j).flatten (fun _ => none))
        (provF slotArr ((outSegs res (labelLiveFrames body) (pieces body)).take j).flatten
          (fun _ => none))
  | 0, _ => fun x _ q hf => by simp [provF] at hf
  | j + 1, hj => by
    have hjl : j < (pieces body).length := by omega
    have hD := dom_pieces hq res hres h j (by omega)
    have hin : (inSegs body)[j]? = some (Piece.toLcmd (pieces body)[j]) := by
      rw [inSegs_getElem?, List.getElem?_eq_getElem hjl]; rfl
    have hout := outSegs_getElem? res (labelLiveFrames body) (pieces body) j
    rw [List.getElem?_eq_getElem hjl] at hout
    rw [List.take_add_one, hin, List.take_add_one, hout]
    simp only [Option.toList_some, Option.map_some, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, provF_append]
    cases hp : (pieces body)[j] with
    | bar li =>
      have hpj : (pieces body)[j]? = some (.bar li) := by
        rw [List.getElem?_eq_getElem hjl, hp]
      simp only [Piece.toLcmd, outSeg]
      by_cases hr : li.li_i = .Lret
      · intro x _ q hf
        simp [provF, scanStepF_ret hr] at hf
      · have hnr := not_retAt_bar hpj hr
        have hgp : ∀ q, gpNameB q = true → Need (pieces body) (labelLiveFrames body) j q :=
          fun q hq' => Or.inr (Or.inl ⟨by rw [isPhysGP_eq_gpNameB]; exact hq', hnr⟩)
        exact domOn_mono (fun x => Need_mono (Nat.le_succ j) hnr) (domOn_provF hgp [li] hD)
    | run is =>
      have hpj : (pieces body)[j]? = some (.run is) := by
        rw [List.getElem?_eq_getElem hjl, hp]
      have hgood := pieces_good body _ (List.getElem_mem hjl)
      rw [hp] at hgood
      have hwf : ∀ i ∈ is, i.wf = true := fun i hi => LprogGpReallocCT.fragOf?_wf (hgood.2 i hi)
      simp only [Piece.toLcmd]
      rw [outSeg_run_eq, ← provI_eq, ← provI_eq]
      exact (run_img hq res hres _ _ (pieces_noAdjRuns body) j is hpj hwf
        (fun i hi => fragOf?_untagCaret_ne (hgood.2 i hi)) (saveCond_run h hpj) hD).2

/-- **The register re-allocation keeps the class.** When every array slot is a `qsave.` slot and
    no result register is a frame cell, the re-allocation of a body in the class is in the
    class. -/
theorem physImgB_reallocBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {res : List String} (hres : ∀ x ∈ res, isFrame x = false) {body : Lcmd}
    (h : physImgB slotArr body = true) :
    physImgB slotArr (reallocBody res body) = true := by
  have hbody : body = (inSegs body).flatten := (pieces_flatten body).symm
  rw [reallocBody_eq]
  set outS := outSegs res (labelLiveFrames body) (pieces body) with houtS
  refine physImgB_of_embed h fun k i' hk => ?_
  have hkl : k < outS.flatten.length := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨j, o, hj, ho, rfl⟩ := flatten_locate outS k hkl
  rw [flatten_getElem? outS hj ho, Option.some.injEq] at hk
  subst hk
  have hjp : j < (pieces body).length := by
    simpa [houtS, outSegs_length] using hj
  have hout := outSegs_getElem? res (labelLiveFrames body) (pieces body) j
  rw [List.getElem?_eq_getElem hjp, ← houtS, List.getElem?_eq_getElem hj,
    Option.map_some, Option.some.injEq] at hout
  have hD := dom_pieces hq res hres h j hjp.le
  cases hp : (pieces body)[j] with
  | bar li =>
    have hpj : (pieces body)[j]? = some (.bar li) := by
      rw [List.getElem?_eq_getElem hjp, hp]
    simp only [hp, outSeg] at hout
    have hseg : outS[j] = [li] := hout
    have ho0 : o = 0 := by rw [hseg] at ho; simp at ho; omega
    subst ho0
    have hjl : j < (inSegs body).length := by simpa [inSegs] using hjp
    have hiseg : (inSegs body)[j] = [li] := by simp [inSegs, hp, Piece.toLcmd]
    have hm : body[bdry (inSegs body) j + 0]? = some li := by
      have := flatten_getElem? (inSegs body) hjl (o := 0) (by rw [hiseg]; simp)
      rw [← hbody] at this
      rw [this]; simp [hiseg]
    have hgood := pieces_good body _ (List.getElem_mem hjp)
    rw [hp] at hgood
    have hnm : slotMov? li.li_i = none := by
      cases hm' : slotMov? li.li_i with
      | none => rfl
      | some p => obtain ⟨d, s⟩ := p; exact absurd hgood (fragOf?_of_slotMov hm')
    have hel : outS[j][0] = li := by simp [hseg]
    rw [hel]
    refine Or.inr ⟨_, hm, fun x hx ha => ?_, Or.inr ?_⟩
    · have hNeed : Need (pieces body) (labelLiveFrames body) j x := by
        rcases hx with ⟨ds, o', y, ss, hx'⟩ | ⟨ds, o', ss, hx', -⟩
        all_goals
          cases hl : isLoc x with
          | false => exact Or.inl hl
          | true =>
            by_cases hf : isFrame x = true
            · refine Or.inr (Or.inr (Or.inr ?_))
              rw [drop_eq_cons hpj, List.flatMap_cons, List.mem_append]
              left
              simp [Piece.frames, instrFrames, hx', opFrames, hf]
            · refine Or.inr (Or.inl ⟨isPhysGP_of_loc hl (by simpa using hf), ?_⟩)
              exact not_retAt_bar hpj (by rw [hx']; exact LinstrR.noConfusion)
      have hml : bdry (inSegs body) j + 0 ≤ body.length :=
        (List.getElem?_eq_some_iff.mp hm).1.le
      have hbt : body.take (bdry (inSegs body) j + 0) = ((inSegs body).take j).flatten := by
        have := flatten_take (inSegs body) hjl (o := 0) (by simp)
        rw [← hbody] at this
        simpa using this
      have hot : outS.flatten.take (bdry outS j + 0) = (outS.take j).flatten := by
        simpa using flatten_take outS hj (o := 0) (by simp)
      have hin_eq := congrFun (reloadOf_eq_provF (slotArr := slotArr) body _ hml) x
      have hout_eq := congrFun (reloadOf_eq_provF (slotArr := slotArr) outS.flatten _ hkl.le) x
      rw [hbt] at hin_eq
      rw [hot] at hout_eq
      simp only [accArr] at ha ⊢
      cases hr : reloadOf slotArr body (bdry (inSegs body) j + 0) x with
      | none => rw [hr] at ha; cases ha
      | some q =>
        rw [hr] at ha
        simp only [Option.bind_some] at ha
        have := hD x hNeed q (by rw [← hin_eq]; exact hr) ha
        rw [hout_eq, this]
        exact ha
    · rw [slotWriteB_noMove hnm _ body _ (bdry (inSegs body) j + 0)]
      exact (physImgB_getElem h hm).2
  | run is =>
    have hpj : (pieces body)[j]? = some (.run is) := by
      rw [List.getElem?_eq_getElem hjp, hp]
    have hgood := pieces_good body _ (List.getElem_mem hjp)
    rw [hp] at hgood
    have hwf : ∀ i ∈ is, i.wf = true := fun i hi => LprogGpReallocCT.fragOf?_wf (hgood.2 i hi)
    simp only [hp] at hout
    rw [outSeg_run_eq] at hout
    set out := reallocRun (lendAt res (labelLiveFrames body) (pieces body) j) is with hout_def
    have hseg : outS[j] = out.map FI.toL := hout
    have ho' : o < out.length := by rw [hseg] at ho; simpa using ho
    have hel : outS[j][o] = out[o].toL := by simp only [hseg, List.getElem_map]
    rw [hel]
    have hok := (run_img hq res hres _ _ (pieces_noAdjRuns body) j is hpj hwf
      (fun i hi => fragOf?_untagCaret_ne (hgood.2 i hi)) (saveCond_run h hpj) hD).1 o out[o]
      (List.getElem?_eq_getElem ho')
    obtain ⟨hacc, hai, hsl | ⟨hj0, R, hmv, hdR, hpre⟩⟩ := hok
    · exact Or.inl ⟨hacc, hai, slotWriteB_of_dstOk (dstOk_single hsl) _ _⟩
    · refine Or.inl ⟨hacc, hai, ?_⟩
      have htk : outS.flatten.take (bdry outS j + o) = (out.take o).map FI.toL := by
        rw [flatten_take outS hj (by rw [hseg]; simp; omega), hseg, hj0]
        simp
      have hmv' : slotMov? (LinstrR.Lopn [.reg out[o].d] out[o].opn out[o].srcs) =
          some (out[o].d, R) := hmv
      simp only [FI.toL, FI.toR, slotWriteB, List.all_cons, List.all_nil, Bool.and_true, hmv',
        Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      refine Or.inr ⟨hdR, ?_⟩
      unfold entryRegB
      rw [htk, List.all_eq_true]
      intro j' hj'
      obtain ⟨j'', hj'', rfl⟩ := List.mem_map.mp hj'
      obtain ⟨s, hs, hne⟩ := hpre j'' hj''
      simp only [FI.toL]
      rw [hs]
      simpa using hne

end Realloc

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold
