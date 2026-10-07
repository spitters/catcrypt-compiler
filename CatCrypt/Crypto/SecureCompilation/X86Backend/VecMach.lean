/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextLeakage

@[expose] public section

set_option autoImplicit false

/-!
# The x86 machine with vector registers

`IsaMachine.withOps M S V vexec vleak` is the machine `M` with a second state component `S`
and a second operation class `V`: its state is `M.MState × S`, its operations are
`M.Op ⊕ V`, an operation of `M` runs on the first component and keeps the second, and an
operation of `V` runs as `vexec` and leaks `vleak`. A program of instructions of `M` only
runs on the extended machine as it runs on `M`, with the second component unchanged
(`IsaMachine.withOps_runL_inl`, `IsaMachine.withOps_haltsC_inl`), when the action of `M` at
an index depends on the instruction there only (`IsaMachine.ActLocal`).

`x86VecMach r m` is `x86Mach r` extended by the vector state `VState` (32 registers of 512
bits, 8 mask registers of 16 bits) and the vector instructions `VInstr`: the register forms
of `ZmmTextModel.Instr`, with the semantic functions of that module, and a load and a store
of `m.stride` bytes of the byte memory of `AState` at the address `VAddr.eval` (base, scaled
index, displacement). The register form is the parameter `m`.

`ofText` reads an instruction of the text model in a fixed-base form (input at `%rsi`,
output at `%rdi`, stack frame at `%rsp`) as a vector instruction. Under the separation
`TextSep`, a step of the text model is a step of `vexec` (`vexec_textStep`) and a run is a
block of the extended machine (`runBlock_textRun`), for the relation `TextSim` between the
two states; the leakage of the block is the address trace of the text
(`blockLeak_textRun`).

## Main definitions

* `MAct.map`, `IsaMachine.ActLocal`, `IsaMachine.okLift`, `IsaMachine.withOps`: the
  extension of a machine by an operation class.
* `readBytes`, `writeBytes`, `SepBytes`: a vector of bytes of the byte memory.
* `VState`, `VAddr`, `VInstr`, `vexec`, `vLeak`: the vector state and instructions.
* `x86VecMach`: the x86 machine with vector registers.
* `ofText`, `ofTextL`, `Covers`, `TextSep`, `TextSim`, `accessLeak`: the text model against
  the machine.

## Main results

* `IsaMachine.withOps_runBlock_inl`, `IsaMachine.withOps_blockLeak_inl`,
  `IsaMachine.withOps_blockOk_inl`, `IsaMachine.withOps_act_inl`,
  `IsaMachine.withOps_runL_inl`, `IsaMachine.withOps_haltsC_inl`: the runs of a program of
  the base machine on the extended machine.
* `x86Mach_actLocal`, `x86VecMach_runL_inl`, `x86VecMach_haltsC_inl`: at `x86VecMach`, a
  program of scalar instructions has the runs of `DecodedCT.RunL` and
  `RInstrSemantics.HaltsC aMachine`, the vector state unchanged.
* `readBytes_writeBytes_same`, `readBytes_writeBytes_of_sep`: reading a written vector, and
  reading a separated one.
* `vexec_regs`, `vexec_flags`, `vexec_mem_frame`: a vector instruction keeps the scalar
  registers, the flags and every byte outside a store.
* `vexec_textStep`, `runBlock_textRun`: the text model is the specification of `vexec`.
* `vLeak_ofText`, `blockLeak_textRun`: the address events of the fixed-base forms are
  `ZmmTextLeakage.accesses` at the base registers.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Next)
open CatCrypt.Crypto.SecureCompilation.CT

/-- The action with its operations mapped by `f`. -/
def MAct.map {α β : Type} (f : α → β) : MAct α → MAct β
  | .op i => .op (f i)
  | .block ops => .block (ops.map f)
  | .branch b t => .branch b t
  | .call t => .call t
  | .ret => .ret

namespace IsaMachine

variable (M : IsaMachine)

/-- The action at an index depends on the instruction there only. -/
def ActLocal : Prop :=
  ∀ (prog : List M.Instr) (pc : Nat) (s : M.MState),
    M.act prog pc s = prog[pc]?.bind fun i => M.act [i] 0 s

/-- The side condition of the extended machine: `ok` on an operation of the base machine,
    `okV` on an operation of the second class. -/
def okLift {S V : Type} (ok : M.MState → M.Op → Prop) (okV : M.MState × S → V → Prop) :
    M.MState × S → M.Op ⊕ V → Prop
  | s, .inl i => ok s.1 i
  | s, .inr v => okV s v

/-- **The machine extended by an operation class.** The state is `M.MState × S`, the
    operations and the decoded instructions are those of `M` or of `V`; an operation of `M`
    runs on the first component, an operation of `V` runs as `vexec` and leaks `vleak`, and
    an instruction of `V` is one operation. The decoder is the decoder of `M`. -/
@[reducible] def withOps (S V : Type) (vexec : M.MState × S → V → M.MState × S)
    (vleak : M.MState × S → V → List CTLeak) : IsaMachine where
  Instr := M.Instr ⊕ V
  Op := M.Op ⊕ V
  MState := M.MState × S
  exec := fun s o =>
    match o with
    | .inl i => (M.exec s.1 i, s.2)
    | .inr v => vexec s v
  decode := fun bs => (M.decode bs).map (List.map Sum.inl)
  act := fun prog pc s =>
    match prog[pc]? with
    | none => none
    | some (.inl i) => (M.act [i] 0 s.1).map (MAct.map Sum.inl)
    | some (.inr v) => some (.op (.inr v))
  callOps := fun n => (M.callOps n).map Sum.inl
  retOps := M.retOps.map Sum.inl
  opLeak := fun s o =>
    match o with
    | .inl i => M.opLeak s.1 i
    | .inr v => vleak s v

variable {M}
variable {S V : Type} {vexec : M.MState × S → V → M.MState × S}
  {vleak : M.MState × S → V → List CTLeak}

@[simp] theorem withOps_callOps (n : Nat) :
    (M.withOps S V vexec vleak).callOps n = (M.callOps n).map Sum.inl := rfl

@[simp] theorem withOps_retOps :
    (M.withOps S V vexec vleak).retOps = M.retOps.map Sum.inl := rfl

/-- A block of operations of the base machine runs on the first component. -/
theorem withOps_runBlock_inl (ops : List M.Op) (a : M.MState × S) :
    (M.withOps S V vexec vleak).runBlock a (ops.map Sum.inl) = (M.runBlock a.1 ops, a.2) := by
  obtain ⟨s, v⟩ := a
  induction ops generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (M.exec s i)

/-- The leakage of a block of operations of the base machine is its leakage there. -/
theorem withOps_blockLeak_inl (ops : List M.Op) (a : M.MState × S) :
    (M.withOps S V vexec vleak).blockLeak a (ops.map Sum.inl) = M.blockLeak a.1 ops := by
  obtain ⟨s, v⟩ := a
  induction ops generalizing s with
  | nil => rfl
  | cons i is ih => exact congrArg (M.opLeak s i ++ ·) (ih (M.exec s i))

/-- The side condition of a block of operations of the base machine. -/
theorem withOps_blockOk_inl (ok : M.MState → M.Op → Prop) (okV : M.MState × S → V → Prop)
    (ops : List M.Op) (a : M.MState × S) :
    (M.withOps S V vexec vleak).BlockOk (M.okLift ok okV) a (ops.map Sum.inl) ↔
      M.BlockOk ok a.1 ops := by
  obtain ⟨s, v⟩ := a
  induction ops generalizing s with
  | nil => exact Iff.rfl
  | cons i is ih => exact and_congr Iff.rfl (ih (M.exec s i))

/-- The action of a program of instructions of the base machine. -/
theorem withOps_act_inl (hM : M.ActLocal) (prog : List M.Instr) (pc : Nat)
    (a : M.MState × S) :
    (M.withOps S V vexec vleak).act (prog.map Sum.inl) pc a =
      (M.act prog pc a.1).map (MAct.map Sum.inl) := by
  simp only [withOps, List.getElem?_map]
  rw [hM prog pc a.1]
  cases prog[pc]? <;> rfl

theorem MAct.map_eq_ret {α β : Type} {f : α → β} {a : MAct α} :
    a.map f = .ret ↔ a = .ret := by
  cases a <;> simp [MAct.map]

theorem MAct.map_eq_op {α β : Type} {f : α → β} {a : MAct α} {j : β} :
    a.map f = .op j ↔ ∃ i, a = .op i ∧ f i = j := by
  cases a <;> simp [MAct.map]

theorem MAct.map_eq_block {α β : Type} {f : α → β} {a : MAct α} {l : List β} :
    a.map f = .block l ↔ ∃ ops, a = .block ops ∧ ops.map f = l := by
  cases a <;> simp [MAct.map]

theorem MAct.map_eq_branch {α β : Type} {f : α → β} {a : MAct α} {b : Bool} {t : Nat} :
    a.map f = .branch b t ↔ a = .branch b t := by
  cases a <;> simp [MAct.map]

theorem MAct.map_eq_call {α β : Type} {f : α → β} {a : MAct α} {t : Nat} :
    a.map f = .call t ↔ a = .call t := by
  cases a <;> simp [MAct.map]

/-- The action of the extended machine on a program of instructions of the base machine is
    `x` exactly when the action of the base machine maps to `x`. -/
theorem withOps_act_inl_eq_some (hM : M.ActLocal) {prog : List M.Instr} {pc : Nat}
    {a : M.MState × S} {x : MAct (M.Op ⊕ V)} :
    (M.withOps S V vexec vleak).act (prog.map Sum.inl) pc a = some x ↔
      ∃ y, M.act prog pc a.1 = some y ∧ y.map Sum.inl = x := by
  rw [withOps_act_inl hM, Option.map_eq_some_iff]

/-- **A program of the base machine runs on the extended machine as on the base machine**,
    with the same leakage and the second state component unchanged. -/
theorem withOps_runL_inl (hM : M.ActLocal) {ok : M.MState → M.Op → Prop}
    {okV : M.MState × S → V → Prop} {prog : List M.Instr} {pc : Nat} {s : M.MState} {v : S}
    {t : List CTLeak} {s' : M.MState} {v' : S} :
    (M.withOps S V vexec vleak).RunL (M.okLift ok okV) (prog.map Sum.inl) pc (s, v) t (s', v') ↔
      M.RunL ok prog pc s t s' ∧ v' = v := by
  constructor
  · have key : ∀ {pc : Nat} {a : (M.withOps S V vexec vleak).MState} {t : List CTLeak}
        {b : (M.withOps S V vexec vleak).MState},
        (M.withOps S V vexec vleak).RunL (M.okLift ok okV) (prog.map Sum.inl) pc a t b →
          M.RunL ok prog pc a.1 t b.1 ∧ b.2 = a.2 := by
      intro pc a t b h
      induction h with
      | ret h =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        rw [MAct.map_eq_ret] at he
        subst he
        exact ⟨.ret hy, rfl⟩
      | op h hok _ ih =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        obtain ⟨i, rfl, rfl⟩ := MAct.map_eq_op.mp he
        exact ⟨.op hy hok ih.1, ih.2⟩
      | block h hok _ ih =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        obtain ⟨ops, rfl, rfl⟩ := MAct.map_eq_block.mp he
        rw [withOps_runBlock_inl] at ih
        rw [withOps_blockLeak_inl]
        exact ⟨.block hy ((withOps_blockOk_inl ok okV ops _).mp hok) ih.1, ih.2⟩
      | branch h _ ih =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        rw [MAct.map_eq_branch] at he
        subst he
        exact ⟨.branch hy ih.1, ih.2⟩
      | call h hok _ hokr _ ihc ihr =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        rw [MAct.map_eq_call] at he
        subst he
        rw [withOps_callOps, withOps_runBlock_inl] at ihc
        rw [withOps_retOps, withOps_runBlock_inl] at ihr
        rw [withOps_callOps, withOps_retOps, withOps_blockLeak_inl, withOps_blockLeak_inl]
        rw [withOps_callOps, withOps_blockOk_inl] at hok
        rw [withOps_retOps, withOps_blockOk_inl] at hokr
        exact ⟨.call hy hok ihc.1 hokr ihr.1, ihr.2.trans ihc.2⟩
    exact fun h => key h
  · rintro ⟨h, rfl⟩
    induction h with
    | ret h => exact .ret ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩)
    | @op pc s i t s' h hok _ ih =>
      exact IsaMachine.RunL.op (M := M.withOps S V vexec vleak) (s := (s, v')) (i := Sum.inl i)
        ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩) hok ih
    | @block pc s ops t s' h hok _ ih =>
      have hb := IsaMachine.RunL.block (M := M.withOps S V vexec vleak)
        (ok := M.okLift ok okV) (s := (s, v'))
        ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩)
        ((withOps_blockOk_inl ok okV ops (s, v')).mpr hok)
        (by rw [withOps_runBlock_inl]; exact ih)
      rwa [withOps_blockLeak_inl] at hb
    | branch h _ ih => exact .branch ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩) ih
    | @call pc tgt s sc tc tr s' h hok _ hokr _ ihc ihr =>
      have hb := IsaMachine.RunL.call (M := M.withOps S V vexec vleak)
        (ok := M.okLift ok okV) (s := (s, v')) (sc := (sc, v'))
        ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩)
        (by rw [withOps_callOps, withOps_blockOk_inl]; exact hok)
        (by rw [withOps_callOps, withOps_runBlock_inl]; exact ihc)
        (by rw [withOps_retOps, withOps_blockOk_inl]; exact hokr)
        (by rw [withOps_retOps, withOps_runBlock_inl]; exact ihr)
      rwa [withOps_callOps, withOps_retOps, withOps_blockLeak_inl, withOps_blockLeak_inl] at hb

/-- The step of the extended machine on a program of instructions of the base machine
    continues exactly when the step of the base machine does. -/
theorem withOps_mstep_inl_go (hM : M.ActLocal) {prog : List M.Instr} {pc pc' : Nat}
    {a b : M.MState × S} :
    (M.withOps S V vexec vleak).mstep (prog.map Sum.inl) pc a = some (.go pc' b) ↔
      M.mstep prog pc a.1 = some (.go pc' b.1) ∧ b.2 = a.2 := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  unfold mstep
  rw [withOps_act_inl hM]
  rcases M.act prog pc a1 with _ | (i | ops | ⟨c, t⟩ | t | _)
  · simp
  · simp [MAct.map, and_assoc, eq_comm]
  · have e := withOps_runBlock_inl (vexec := vexec) (vleak := vleak) ops (a1, a2)
    simp [MAct.map, e, and_assoc, eq_comm]
  · simp [MAct.map, and_assoc, eq_comm]
  · simp [MAct.map]
  · simp [MAct.map]

/-- **A program of the base machine halts on the extended machine as on the base machine**,
    the second state component unchanged. -/
theorem withOps_haltsC_inl (hM : M.ActLocal) {prog : List M.Instr} {pc : Nat} {s : M.MState}
    {v : S} {s' : M.MState} {v' : S} :
    (M.withOps S V vexec vleak).HaltsC (prog.map Sum.inl) pc (s, v) (s', v') ↔
      M.HaltsC prog pc s s' ∧ v' = v := by
  constructor
  · have key : ∀ {pc : Nat} {a b : (M.withOps S V vexec vleak).MState},
        (M.withOps S V vexec vleak).HaltsC (prog.map Sum.inl) pc a b →
          M.HaltsC prog pc a.1 b.1 ∧ b.2 = a.2 := by
      intro pc a b h
      induction h with
      | ret h =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        rw [MAct.map_eq_ret] at he
        subst he
        exact ⟨.ret hy, rfl⟩
      | go h _ ih =>
        obtain ⟨h1, h2⟩ := (withOps_mstep_inl_go hM).mp h
        exact ⟨.go h1 ih.1, ih.2.trans h2⟩
      | call h _ _ ihc ihr =>
        obtain ⟨y, hy, he⟩ := (withOps_act_inl_eq_some hM).mp h
        rw [MAct.map_eq_call] at he
        subst he
        rw [withOps_callOps, withOps_runBlock_inl] at ihc
        rw [withOps_retOps, withOps_runBlock_inl] at ihr
        exact ⟨.call hy ihc.1 ihr.1, ihr.2.trans ihc.2⟩
    exact fun h => key h
  · rintro ⟨h, rfl⟩
    induction h with
    | ret h => exact .ret ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩)
    | @go pc s pc' s₁ s₂ h _ ih =>
      exact IsaMachine.HaltsC.go (M := M.withOps S V vexec vleak) (s := (s, v'))
        (s' := (s₁, v')) ((withOps_mstep_inl_go hM).mpr ⟨h, rfl⟩) ih
    | @call pc t s sc s'' h _ _ ihc ihr =>
      exact IsaMachine.HaltsC.call (M := M.withOps S V vexec vleak) (s := (s, v'))
        (sc := (sc, v')) ((withOps_act_inl_eq_some hM).mpr ⟨_, h, rfl⟩)
        (by rw [withOps_callOps, withOps_runBlock_inl]; exact ihc)
        (by rw [withOps_retOps, withOps_runBlock_inl]; exact ihr)

end IsaMachine

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode LOp Opnd MState opVal wr
  getLsbD_wr semLW semShImm semDup semMerge semPerm semRol semTern)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextLeakage (Access accesses addrTrace)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AMem AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Mach x86Act x86Mach_runL_iff
  x86Mach_haltsC_iff)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. Vectors of bytes -/

/-- The little-endian value of the `n` bytes of `mem` from address `a`, zero above them. -/
def readBytes (n : Nat) (mem : AMem) (a : BitVec 64) : BitVec 512 :=
  BitVec.ofFnLE (fun i : Fin 512 =>
    decide (i.val / 8 < n) && (mem (a + BitVec.ofNat 64 (i.val / 8))).getLsbD (i.val % 8))

/-- The memory with the low `n` bytes of `x` stored little-endian from address `a`. -/
def writeBytes (n : Nat) (mem : AMem) (a : BitVec 64) (x : BitVec 512) : AMem := fun p =>
  if (p - a).toNat < n then x.extractLsb' (8 * (p - a).toNat) 8 else mem p

/-- The `n`-byte ranges from `a` and from `b` are disjoint modulo `2^64`. -/
def SepBytes (n : Nat) (a b : BitVec 64) : Prop := n ≤ (b - a).toNat ∧ n ≤ (a - b).toNat

theorem SepBytes.symm {n : Nat} {a b : BitVec 64} (h : SepBytes n a b) : SepBytes n b a :=
  ⟨h.2, h.1⟩

/-- Bit `i` of a vector of bytes. -/
theorem getLsbD_readBytes (n : Nat) (mem : AMem) (a : BitVec 64) (i : Nat) :
    (readBytes n mem a).getLsbD i =
      (decide (i < 512) && (decide (i / 8 < n) &&
        (mem (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8))) := by
  unfold readBytes
  rw [BitVec.getLsbD_ofFnLE]
  by_cases h : i < 512 <;> simp [h]

/-- A byte outside the stored range is unchanged. -/
theorem writeBytes_of_not_lt (n : Nat) (mem : AMem) (a : BitVec 64) (x : BitVec 512)
    (p : BitVec 64) (h : ¬ (p - a).toNat < n) : writeBytes n mem a x p = mem p := by
  simp only [writeBytes, if_neg h]

theorem toNat_add_ofNat_sub (a : BitVec 64) (k : Nat) (hk : k < 64) :
    (a + BitVec.ofNat 64 k - a).toNat = k := by
  have := a.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Reading the vector just stored returns the active bits of the value. -/
theorem readBytes_writeBytes_same (m : Mode) (mem : AMem) (a : BitVec 64) (x : BitVec 512) :
    readBytes m.stride (writeBytes m.stride mem a x) a = wr m x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBytes, getLsbD_wr]
  have hs : (i / 8 < m.stride) ↔ i < m.act := by
    cases m <;> simp only [Mode.stride, Mode.act] <;> omega
  by_cases h : i < m.act
  · have h8 : i / 8 < m.stride := hs.mpr h
    have hk : (a + BitVec.ofNat 64 (i / 8) - a).toNat = i / 8 :=
      toNat_add_ofNat_sub a _ (by omega)
    have hdm : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
    have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
    simp only [writeBytes, hk, hi, h, h8, decide_true, Bool.true_and]
    rw [if_pos trivial, BitVec.getLsbD_extractLsb', hdm]
    simp [hm]
  · have h8 : ¬ i / 8 < m.stride := fun h' => h (hs.mp h')
    simp [h, h8]

/-- A store to a separated range does not change the vector read at `b`. -/
theorem readBytes_writeBytes_of_sep {n : Nat} (hn : n ≤ 64) (mem : AMem) {a b : BitVec 64}
    (x : BitVec 512) (h : SepBytes n a b) :
    readBytes n (writeBytes n mem a x) b = readBytes n mem b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_readBytes, getLsbD_readBytes]
  by_cases h8 : i / 8 < n
  · have hne : ¬ (b + BitVec.ofNat 64 (i / 8) - a).toNat < n := by
      obtain ⟨h1, h2⟩ := h
      have := a.isLt
      have := b.isLt
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
      omega
    rw [writeBytes_of_not_lt _ _ _ _ _ hne]
  · simp [h8]

/-! ## 2. The vector state and instructions -/

/-- The vector state: 32 registers of 512 bits and 8 mask registers of 16 bits. -/
structure VState where
  /-- The vector registers. -/
  zmm : Fin 32 → BitVec 512
  /-- The mask registers. -/
  kr : Fin 8 → BitVec 16

/-- The state with register `d` set to `x`. -/
def VState.setZ (v : VState) (d : Fin 32) (x : BitVec 512) : VState :=
  { v with zmm := fun r => if r = d then x else v.zmm r }

/-- A memory operand: a base register, an optional index register with its scale, and a
    displacement. -/
structure VAddr where
  /-- The base register. -/
  base : String
  /-- The index register and its scale. -/
  idx : Option (String × Nat) := none
  /-- The displacement. -/
  disp : Int := 0
  deriving DecidableEq

/-- The address of a memory operand on a register file. -/
def VAddr.eval (a : VAddr) (regs : String → BitVec 64) : BitVec 64 :=
  regs a.base
    + (match a.idx with
       | none => 0
       | some (x, sc) => BitVec.ofNat 64 (sc * (regs x).toNat))
    + BitVec.ofInt 64 a.disp

/-- The vector instructions: the register forms of `ZmmTextModel.Instr`, and a load and a
    store at a memory operand. -/
inductive VInstr where
  /-- `vmovdqu64 a, dst`. -/
  | ld (a : VAddr) (dst : Fin 32)
  /-- `vmovdqu64 src, a`. -/
  | st (src : Fin 32) (a : VAddr)
  /-- `mnem src2, src1, dst`: `dst := src1 ∘ src2` lane-wise at width `L`. -/
  | op (L : Nat) (o : LOp) (src2 src1 dst : Fin 32)
  /-- `vpsllq/vpsrlq/vpslld/vpsrld $imm, src, dst`. -/
  | shi (L : Nat) (left : Bool) (imm : Nat) (src dst : Fin 32)
  /-- `vmovshdup` (`odd`) or `vmovsldup` `src, dst`, with an optional merge mask. -/
  | dup (odd : Bool) (src dst : Fin 32) (mask : Option (Fin 8))
  /-- `vmovdqa64 src, dst`. -/
  | mova (src dst : Fin 32)
  /-- `vpermd src, idx, dst`. -/
  | perm (src idx dst : Fin 32)
  /-- `vpblendmd a, b, dst{%kN}`. -/
  | blend (k : Fin 8) (a b dst : Fin 32)
  /-- `vprolq` (`L = 64`) or `vprold` (`L = 32`) `$imm, src, dst`. -/
  | rol (L imm : Nat) (src dst : Fin 32)
  /-- `vpternlogq` (`L = 64`) or `vpternlogd` (`L = 32`) `$imm, src3, src2, dst`. -/
  | tern (L : Nat) (imm : BitVec 8) (src3 src2 dst : Fin 32)
  deriving DecidableEq

/-- One vector instruction in register form `m` on the scalar and the vector state: a load
    reads `m.stride` bytes at its address, a store writes the low `m.stride` bytes of its
    source there, and a register form writes the value of `ZmmTextModel.step`. -/
def vexec (m : Mode) (s : AState × VState) : VInstr → AState × VState
  | .ld a d => (s.1, s.2.setZ d (readBytes m.stride s.1.mem (a.eval s.1.regs)))
  | .st r a =>
      ({ s.1 with mem := writeBytes m.stride s.1.mem (a.eval s.1.regs) (s.2.zmm r) }, s.2)
  | .op L o s2 s1 d => (s.1, s.2.setZ d (wr m (semLW L o (s.2.zmm s1) (s.2.zmm s2))))
  | .shi L l i r d => (s.1, s.2.setZ d (wr m (semShImm L l i (s.2.zmm r))))
  | .dup odd r d none => (s.1, s.2.setZ d (wr m (semDup odd (s.2.zmm r))))
  | .dup odd r d (some k) =>
      (s.1, s.2.setZ d (wr m (semMerge (s.2.kr k) (semDup odd (s.2.zmm r)) (s.2.zmm d))))
  | .mova r d => (s.1, s.2.setZ d (wr m (s.2.zmm r)))
  | .perm x i d => (s.1, s.2.setZ d (wr m (semPerm (m.act / 32) (s.2.zmm x) (s.2.zmm i))))
  | .blend k a b d => (s.1, s.2.setZ d (wr m (semMerge (s.2.kr k) (s.2.zmm a) (s.2.zmm b))))
  | .rol L imm r d => (s.1, s.2.setZ d (wr m (semRol L imm (s.2.zmm r))))
  | .tern _ imm s3 s2 d =>
      (s.1, s.2.setZ d (wr m (semTern imm (s.2.zmm d) (s.2.zmm s2) (s.2.zmm s3))))

/-- The address events of a vector instruction: the address of a load or a store. -/
def vLeak (regs : String → BitVec 64) : VInstr → List CTLeak
  | .ld a _ => [.addr "" ((a.eval regs).toNat : Int)]
  | .st _ a => [.addr "" ((a.eval regs).toNat : Int)]
  | _ => []

/-- A vector instruction keeps the scalar registers. -/
theorem vexec_regs (m : Mode) (s : AState × VState) (v : VInstr) :
    (vexec m s v).1.regs = s.1.regs := by
  cases v with
  | dup odd r d mask => cases mask <;> rfl
  | _ => rfl

/-- A vector instruction keeps the flags. -/
theorem vexec_flags (m : Mode) (s : AState × VState) (v : VInstr) :
    (vexec m s v).1.flags = s.1.flags := by
  cases v with
  | dup odd r d mask => cases mask <;> rfl
  | _ => rfl

/-- A vector instruction keeps every byte outside the range of a store. -/
theorem vexec_mem_frame (m : Mode) (s : AState × VState) (v : VInstr) (p : BitVec 64)
    (h : ∀ r a, v = .st r a → ¬ (p - a.eval s.1.regs).toNat < m.stride) :
    (vexec m s v).1.mem p = s.1.mem p := by
  cases v with
  | st r a => exact writeBytes_of_not_lt _ _ _ _ _ (h r a rfl)
  | dup odd r d mask => cases mask <;> rfl
  | _ => rfl

/-- A vector instruction other than a store keeps the scalar state. -/
theorem vexec_fst_of_not_st (m : Mode) (s : AState × VState) (v : VInstr)
    (h : ∀ r a, v ≠ .st r a) : (vexec m s v).1 = s.1 := by
  cases v with
  | st r a => exact absurd rfl (h r a)
  | dup odd r d mask => cases mask <;> rfl
  | _ => rfl

/-- A store keeps the vector state. -/
theorem vexec_st_snd (m : Mode) (s : AState × VState) (r : Fin 32) (a : VAddr) :
    (vexec m s (.st r a)).2 = s.2 := rfl

/-! ## 3. The x86 machine with vector registers -/

/-- The action of `x86Mach` at an index depends on the instruction there only. -/
theorem x86Mach_actLocal (r : DoitRegime) : (x86Mach r).ActLocal := by
  intro prog pc s
  show x86Act prog pc s = prog[pc]?.bind fun i => x86Act [i] 0 s
  unfold x86Act
  cases prog[pc]? with
  | none => rfl
  | some ri => cases ri <;> rfl

/-- **The x86 machine with vector registers** under the timing regime `r`, in register
    form `m`: `x86Mach r` extended by the vector state `VState` and the vector instructions
    `VInstr`, which run as `vexec m` and leak the addresses `vLeak`. -/
@[reducible] def x86VecMach (r : DoitRegime) (m : Mode) : IsaMachine :=
  (x86Mach r).withOps VState VInstr (vexec m) (fun s v => vLeak s.1.regs v)

variable (r : DoitRegime) (m : Mode)

theorem x86VecMach_exec_inl (s : AState × VState) (i : JInstr 64) :
    (x86VecMach r m).exec s (.inl i) = (aMachine.exec s.1 i, s.2) := rfl

theorem x86VecMach_exec_inr (s : AState × VState) (v : VInstr) :
    (x86VecMach r m).exec s (.inr v) = vexec m s v := rfl

theorem x86VecMach_opLeak_inl (s : AState × VState) (i : JInstr 64) :
    (x86VecMach r m).opLeak s (.inl i) = DecodedCT.opLeak r s.1 i := rfl

theorem x86VecMach_opLeak_inr (s : AState × VState) (v : VInstr) :
    (x86VecMach r m).opLeak s (.inr v) = vLeak s.1.regs v := rfl

/-- The decoder of `x86VecMach` is `decodeLprog`: a decoded program has scalar instructions
    only. -/
theorem x86VecMach_decode (bs : List (BitVec 8)) :
    (x86VecMach r m).decode bs =
      (LprogBytesDecode.decodeLprog bs).map (List.map Sum.inl) := rfl

/-- **A program of scalar instructions runs on `x86VecMach` as on the address machine**:
    its runs with leakage are those of `DecodedCT.RunL`, at every vector state, which the
    run does not change. -/
theorem x86VecMach_runL_inl {ok : AState → JInstr 64 → Prop}
    {okV : AState × VState → VInstr → Prop} {prog : List RInstr} {pc : Nat} {sa : AState}
    {v : VState} {t : List CTLeak} {sa' : AState} {v' : VState} :
    (x86VecMach r m).RunL ((x86Mach r).okLift ok okV) (prog.map Sum.inl) pc (sa, v) t
        (sa', v') ↔ DecodedCT.RunL r ok prog pc sa t sa' ∧ v' = v :=
  (IsaMachine.withOps_runL_inl (x86Mach_actLocal r)).trans
    (and_congr (x86Mach_runL_iff r) Iff.rfl)

/-- **A program of scalar instructions halts on `x86VecMach` as on the address machine**,
    at every vector state, which the run does not change. -/
theorem x86VecMach_haltsC_inl {prog : List RInstr} {pc : Nat} {sa : AState} {v : VState}
    {sa' : AState} {v' : VState} :
    (x86VecMach r m).HaltsC (prog.map Sum.inl) pc (sa, v) (sa', v') ↔
      RInstrSemantics.HaltsC aMachine prog pc sa sa' ∧ v' = v :=
  (IsaMachine.withOps_haltsC_inl (x86Mach_actLocal r)).trans
    (and_congr (x86Mach_haltsC_iff r) Iff.rfl)

/-- A block of vector instructions keeps the scalar registers. -/
theorem x86VecMach_runBlock_inr_regs (vs : List VInstr) (s : AState × VState) :
    ((x86VecMach r m).runBlock s (vs.map Sum.inr)).1.regs = s.1.regs := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact (ih (vexec m s v)).trans (vexec_regs m s v)

/-- A block of vector instructions keeps the flags. -/
theorem x86VecMach_runBlock_inr_flags (vs : List VInstr) (s : AState × VState) :
    ((x86VecMach r m).runBlock s (vs.map Sum.inr)).1.flags = s.1.flags := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih => exact (ih (vexec m s v)).trans (vexec_flags m s v)

/-! ## 4. The text model as the specification of `vexec` -/

/-- The address at byte offset `off` from the register `b`. -/
def baseAt (regs : String → BitVec 64) (b : String) (off : Nat) : BitVec 64 :=
  (VAddr.mk b none (off : Int)).eval regs

/-- The vector instruction of a text instruction in a fixed-base form: the input region at
    `%rsi`, the output region at `%rdi` and the stack frame at `%rsp`. The forms that read
    the data table, `%eax` or a mask source, and the moves of `%rsp`, have none. -/
def ofText : VIR.ZmmTextModel.Instr → Option VInstr
  | .ldIn off d => some (.ld ⟨"%rsi", none, off⟩ d)
  | .st r off => some (.st r ⟨"%rdi", none, off⟩)
  | .ldS off d => some (.ld ⟨"%rsp", none, off⟩ d)
  | .stS r off => some (.st r ⟨"%rsp", none, off⟩)
  | .op L o (.reg s2) s1 d => some (.op L o s2 s1 d)
  | .shi L l i r d => some (.shi L l i r d)
  | .dup odd r d k => some (.dup odd r d k)
  | .mova r d => some (.mova r d)
  | .perm x i d => some (.perm x i d)
  | .blend k a b d => some (.blend k a b d)
  | .rol L i r d => some (.rol L i r d)
  | .tern L i s3 s2 d => some (.tern L i s3 s2 d)
  | _ => none

/-- The vector instructions of a text program, `none` when an instruction has none. -/
def ofTextL : List VIR.ZmmTextModel.Instr → Option (List VInstr)
  | [] => some []
  | i :: is => (ofText i).bind fun v => (ofTextL is).map (v :: ·)

/-- The offsets of an instruction lie in the regions: an input offset in `In`, an output
    offset in `Out`, a stack offset in `Stk`. -/
def Covers (In Out Stk : Nat → Prop) : VIR.ZmmTextModel.Instr → Prop
  | .ldIn off _ => In off
  | .st _ off => Out off
  | .ldS off _ => Stk off
  | .stS _ off => Stk off
  | _ => True

/-- **The separation of the three regions** on a register file, for vectors of `m.stride`
    bytes: every output vector is disjoint from every input and every stack vector, every
    stack vector from every input vector, and two output vectors, or two stack vectors, at
    different offsets are disjoint. -/
structure TextSep (m : Mode) (In Out Stk : Nat → Prop) (regs : String → BitVec 64) :
    Prop where
  out_in : ∀ o i, Out o → In i →
    SepBytes m.stride (baseAt regs "%rdi" o) (baseAt regs "%rsi" i)
  out_stk : ∀ o k, Out o → Stk k →
    SepBytes m.stride (baseAt regs "%rdi" o) (baseAt regs "%rsp" k)
  stk_in : ∀ k i, Stk k → In i →
    SepBytes m.stride (baseAt regs "%rsp" k) (baseAt regs "%rsi" i)
  out_out : ∀ o o', Out o → Out o' → o ≠ o' →
    SepBytes m.stride (baseAt regs "%rdi" o) (baseAt regs "%rdi" o')
  stk_stk : ∀ k k', Stk k → Stk k' → k ≠ k' →
    SepBytes m.stride (baseAt regs "%rsp" k) (baseAt regs "%rsp" k')

/-- **The text state against the machine state.** The vector and mask registers agree; the
    memory at each input offset holds the active bits of the input region there; the memory
    at each output offset holds the last value the text stored there; the memory at each
    stack offset holds the active bits of the stack value there. -/
structure TextSim (m : Mode) (input : Nat → BitVec 512) (In Out Stk : Nat → Prop)
    (σ : MState) (s : AState × VState) : Prop where
  zmm : σ.zmm = s.2.zmm
  kr : σ.kr = s.2.kr
  inp : ∀ off, In off →
    readBytes m.stride s.1.mem (baseAt s.1.regs "%rsi" off) = wr m (input off)
  out : ∀ off x, Out off → σ.outAt off = some x →
    readBytes m.stride s.1.mem (baseAt s.1.regs "%rdi" off) = x
  stk : ∀ off, Stk off →
    readBytes m.stride s.1.mem (baseAt s.1.regs "%rsp" off) = wr m (σ.stk (off : Int))

theorem stride_le (m : Mode) : m.stride ≤ 64 := by
  cases m <;> decide

variable {m}

/-- **One step of the text model is one step of `vexec`.** Under the separation of the
    regions, a step of `ZmmTextModel.step` on an instruction in a fixed-base form whose
    offsets lie in the regions preserves the relation `TextSim` to the state after
    `vexec`. -/
theorem vexec_textStep {input : Nat → BitVec 512}
    {ro : Std.HashMap String (Array (BitVec 64))} {In Out Stk : Nat → Prop} {σ σ' : MState}
    {s : AState × VState} {i : VIR.ZmmTextModel.Instr} {v : VInstr}
    (hsep : TextSep m In Out Stk s.1.regs) (hc : Covers In Out Stk i)
    (hv : ofText i = some v) (hsim : TextSim m input In Out Stk σ s)
    (hstep : VIR.ZmmTextModel.step m input ro σ i = some σ') :
    TextSim m input In Out Stk σ' (vexec m s v) := by
  obtain ⟨hz, hk, hin, hout, hstk⟩ := hsim
  cases i with
  | ldIn off d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    funext x
    simp only [MState.setZ, vexec, VState.setZ, hz]
    rw [← hin off hc]
    rfl
  | st x off =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨hz, hk, ?_, ?_, ?_⟩
    · intro j hj
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rdi" off) _)
        (baseAt s.1.regs "%rsi" j) = _
      rw [readBytes_writeBytes_of_sep (stride_le m) _ _ (hsep.out_in off j hc hj)]
      exact hin j hj
    · intro o y ho hy
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rdi" off) _)
        (baseAt s.1.regs "%rdi" o) = _
      by_cases e : o = off
      · subst e
        simp only [MState.outAt, List.find?_cons, beq_self_eq_true, Option.map_some,
          Option.some.injEq] at hy
        rw [readBytes_writeBytes_same, ← hy, hz]
      · have hy' : σ.outAt o = some y := by
          simpa [MState.outAt, List.find?_cons, Ne.symm e] using hy
        rw [readBytes_writeBytes_of_sep (stride_le m) _ _
          (hsep.out_out off o hc ho (Ne.symm e))]
        exact hout o y ho hy'
    · intro k hk'
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rdi" off) _)
        (baseAt s.1.regs "%rsp" k) = _
      rw [readBytes_writeBytes_of_sep (stride_le m) _ _ (hsep.out_stk off k hc hk')]
      exact hstk k hk'
  | ldS off d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    funext x
    simp only [MState.setZ, vexec, VState.setZ, hz]
    rw [← hstk off hc]
    rfl
  | stS x off =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨hz, hk, ?_, ?_, ?_⟩
    · intro j hj
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rsp" off) _)
        (baseAt s.1.regs "%rsi" j) = _
      rw [readBytes_writeBytes_of_sep (stride_le m) _ _ (hsep.stk_in off j hc hj)]
      exact hin j hj
    · intro o y ho hy
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rsp" off) _)
        (baseAt s.1.regs "%rdi" o) = _
      rw [readBytes_writeBytes_of_sep (stride_le m) _ _ (hsep.out_stk o off ho hc).symm]
      exact hout o y ho hy
    · intro k hk'
      show readBytes _ (writeBytes _ s.1.mem (baseAt s.1.regs "%rsp" off) (s.2.zmm x))
        (baseAt s.1.regs "%rsp" k) =
          wr m (if (k : Int) = (off : Int) then σ.zmm x else σ.stk (k : Int))
      by_cases e : k = off
      · subst e
        rw [readBytes_writeBytes_same, if_pos rfl, hz]
      · rw [readBytes_writeBytes_of_sep (stride_le m) _ _
          (hsep.stk_stk off k hc hk' (Ne.symm e)), if_neg (by exact_mod_cast e)]
        exact hstk k hk'
  | op L o s2 s1 d =>
    cases s2 with
    | reg y =>
      simp only [ofText, Option.some.injEq] at hv
      subst hv
      simp only [VIR.ZmmTextModel.step,opVal, Option.map_some, Option.some.injEq] at hstep
      subst hstep
      refine ⟨?_, hk, hin, hout, hstk⟩
      simp only [MState.setZ, vexec, VState.setZ, hz]
    | mem c => simp [ofText] at hv
  | dup odd x d mask =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    cases mask with
    | none =>
      simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
      subst hstep
      refine ⟨?_, hk, hin, hout, hstk⟩
      simp only [MState.setZ, vexec, VState.setZ, hz]
    | some k =>
      simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
      subst hstep
      refine ⟨?_, hk, hin, hout, hstk⟩
      simp only [MState.setZ, vexec, VState.setZ, hz, hk]
  | shi L l n x d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz]
  | mova x d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz]
  | perm x y d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz]
  | blend k a b d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz, hk]
  | rol L n x d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz]
  | tern L n x y d =>
    simp only [ofText, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.step,Option.some.injEq] at hstep
    subst hstep
    refine ⟨?_, hk, hin, hout, hstk⟩
    simp only [MState.setZ, vexec, VState.setZ, hz]
  | ldC c d => simp [ofText] at hv
  | movEax n => simp [ofText] at hv
  | kmov k => simp [ofText] at hv
  | spSub n => simp [ofText] at hv
  | spAdd n => simp [ofText] at hv

variable (m)

/-- **A run of the text model is a block of the machine.** Under the separation of the
    regions at the initial registers, a run of `ZmmTextModel.run` on a program of fixed-base
    forms whose offsets lie in the regions ends in a state related by `TextSim` to the state
    after the block of its vector instructions on `x86VecMach`. -/
theorem runBlock_textRun {input : Nat → BitVec 512}
    {ro : Std.HashMap String (Array (BitVec 64))} {In Out Stk : Nat → Prop} :
    ∀ (prog : List VIR.ZmmTextModel.Instr) (vs : List VInstr) (σ σ' : MState)
      (s : AState × VState),
      TextSep m In Out Stk s.1.regs → (∀ i ∈ prog, Covers In Out Stk i) →
      ofTextL prog = some vs → TextSim m input In Out Stk σ s →
      VIR.ZmmTextModel.run m input ro σ prog = some σ' →
      TextSim m input In Out Stk σ' ((x86VecMach r m).runBlock s (vs.map Sum.inr))
  | [], vs, σ, σ', s, _, _, hv, hsim, hrun => by
    simp only [ofTextL, Option.some.injEq] at hv
    subst hv
    simp only [VIR.ZmmTextModel.run,Option.some.injEq] at hrun
    subst hrun
    exact hsim
  | i :: is, vs, σ, σ', s, hsep, hc, hv, hsim, hrun => by
    simp only [ofTextL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨v, hv1, vs', hv2, rfl⟩ := hv
    simp only [VIR.ZmmTextModel.run,Option.bind_eq_some_iff] at hrun
    obtain ⟨σ₁, h1, h2⟩ := hrun
    exact runBlock_textRun is vs' σ₁ σ' (vexec m s v) (by rw [vexec_regs]; exact hsep)
      (fun j hj => hc j (List.mem_cons_of_mem _ hj)) hv2
      (vexec_textStep hsep (hc i List.mem_cons_self) hv1 hsim h1) h2

/-! ## 5. The address events -/

/-- The address event of a location of the text model at the base registers; a data label
    has none. -/
def accessLeak (regs : String → BitVec 64) : Access → List CTLeak
  | .rdIn off => [.addr "" ((baseAt regs "%rsi" off).toNat : Int)]
  | .rdC _ => []
  | .wrOut off => [.addr "" ((baseAt regs "%rdi" off).toNat : Int)]
  | .rdStk off => [.addr "" ((baseAt regs "%rsp" off).toNat : Int)]
  | .wrStk off => [.addr "" ((baseAt regs "%rsp" off).toNat : Int)]

/-- **The address events of a fixed-base form are its locations** at the base registers. -/
theorem vLeak_ofText {i : VIR.ZmmTextModel.Instr} {v : VInstr} (h : ofText i = some v)
    (regs : String → BitVec 64) :
    vLeak regs v = (accesses i).flatMap (accessLeak regs) := by
  cases i with
  | op L o s2 s1 d =>
    cases s2 with
    | reg y =>
      simp only [ofText, Option.some.injEq] at h
      subst h
      rfl
    | mem c => simp [ofText] at h
  | ldC c d => simp [ofText] at h
  | movEax n => simp [ofText] at h
  | kmov k => simp [ofText] at h
  | spSub n => simp [ofText] at h
  | spAdd n => simp [ofText] at h
  | _ =>
    simp only [ofText, Option.some.injEq] at h
    subst h
    rfl

/-- **The leakage of a block of fixed-base forms is the address trace of the text** at the
    base registers of the initial state. -/
theorem blockLeak_textRun :
    ∀ (prog : List VIR.ZmmTextModel.Instr) (vs : List VInstr) (s : AState × VState),
      ofTextL prog = some vs →
      (x86VecMach r m).blockLeak s (vs.map Sum.inr) =
        (addrTrace prog).flatMap (accessLeak s.1.regs)
  | [], vs, s, hv => by
    simp only [ofTextL, Option.some.injEq] at hv
    subst hv
    rfl
  | i :: is, vs, s, hv => by
    simp only [ofTextL, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hv
    obtain ⟨v, hv1, vs', hv2, rfl⟩ := hv
    show vLeak s.1.regs v ++ (x86VecMach r m).blockLeak (vexec m s v) (vs'.map Sum.inr) = _
    rw [blockLeak_textRun is vs' _ hv2, vexec_regs, vLeak_ofText hv1]
    simp [addrTrace]

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
