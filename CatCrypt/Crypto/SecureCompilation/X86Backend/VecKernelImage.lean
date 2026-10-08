/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec

@[expose] public section

set_option autoImplicit false

/-!
# The byte image of a vector kernel

A kernel block `ops` of `VecKernelSpec.kernelRun` is a list of scalar operations and vector
instructions. `lineItems enc ops` is the block as a program of positions followed by `ret`:
a scalar operation `i` is the position with bytes `enc i` that decodes to `i`, a vector
instruction is itself. `lineBytes A enc ops` is the bytes `VecImage.mixedEncode A` gives the
positions of `ops` followed by `vzeroupper`.

A program of this form has no branch, so the branch condition of the round trip
`VecImage.mixedDecode_mixedEncode` holds for it, and the position of `ret` is well formed
(`LprogBytesDecode.mkRet_ok`). The round trip therefore needs a lawful table with an entry
for each vector instruction of the block and for `vzeroupper` (`BlockEncodable`), and the
well-formedness `LprogBytesDecode.ItemOK` of the position of each scalar operation of the
block. Under these, the machine `VecImage.mixedMach` decodes `lineBytes A enc ops` to
`VecMach.lineProg (ops ++ [.inr .zeroUpper])`, whose runs with leakage are `kernelRun`.

`frameEnc` encodes the three scalar operations `VecMach.opOfText` yields: `movl $imm, %eax`
as `B8 id`, and `subq $n, %rsp`, `addq $n, %rsp` in the sign-extended `imm8` form when `n`
fits and in the `imm32` form otherwise. For a block of a text that passes the frame check
`VecKernelSpec.framedB` with a frame below `2 ^ 31` bytes, every scalar position is well
formed (`frameEnc_ok_of_framed`), so the round trip holds without a hypothesis on positions.

With `VecImage.VecAsm.Faithful`, a processor run on the bytes of a kernel that meets a
callee specification returns in a state that satisfies the postcondition
(`faithful_calleeSpec`); `vectorKernel_image` is the statement for the text
`VectorizeEmit.vectorizeEmit` returns.

## Main definitions

* `scalarItem`, `lineItems`, `lineBytes`: the positions and the bytes of a block followed by
  `ret`.
* `BlockEncodable`: the table has an entry for each vector instruction of a block and for
  `vzeroupper`.
* `frameEnc`: the bytes of the scalar operations of a kernel text.

## Main results

* `mixedExpected_lineItems`, `mixedBranchOK_lineItems`: the positions of a block denote
  `lineProg`, and their branch condition holds.
* `mixedDecode_lineItems`, `lineBytes_decode`: `mixedMach` decodes the bytes of a block to
  its line program.
* `kernelRun_iff_mixedMach`, `kernelImage`: the runs with leakage on `mixedMach` of the
  program decoded from the bytes of a kernel are `kernelRun`.
* `opOfText_inl`, `blockOfText_mem`, `framedB_move_le`: the scalar operations of a text, and
  the bound of a frame move by the frame size.
* `frameEnc_ok_of_text`, `frameEnc_ok_of_framed`: the scalar positions of the block of a
  text are well formed.
* `faithful_kernelRun`, `faithful_kernel_total`: a faithful processor has the runs of
  `kernelRun` on the bytes of the kernel, from every vector state.
* `faithful_calleeSpec`: on the bytes of a kernel that meets a callee specification, a
  faithful processor returns in a state that satisfies the postcondition, the frame and the
  clobber conditions.
* `vectorKernel_image`: the same for the text of `vectorizeEmit`, with `frameEnc`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LaneMapVec
open CatCrypt.Crypto.SecureCompilation.VIR.VectorizeEmit
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (Mode)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (JCtxt)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encMovImmw encAluImmw
  encAluImm8 fitsImm8S)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecMach
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecImage
open CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelSpec
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.CT

/-! ## 1. The positions of a block followed by `ret` -/

/-- The position of the scalar operation `i` with the bytes `enc i`. -/
def scalarItem (enc : JInstr 64 → List (BitVec 8)) (i : JInstr 64) : Item :=
  ⟨enc i, some (.op i), none, none⟩

/-- The positions of a block of operations followed by `ret`: the position `scalarItem` of
    each scalar operation, each vector instruction, and the position of `ret`. -/
def lineItems (enc : JInstr 64 → List (BitVec 8)) (ops : List (JInstr 64 ⊕ VInstr)) :
    List (Item ⊕ VInstr) :=
  ops.map (Sum.map (scalarItem enc) id) ++ [.inl mkRet]

/-- **The bytes of a kernel block**: the bytes of the positions of the block followed by
    `vzeroupper` and `ret`, the vector instructions encoded by the table `A`. -/
def lineBytes (A : VecAsm) (enc : JInstr 64 → List (BitVec 8))
    (ops : List (JInstr 64 ⊕ VInstr)) : List (BitVec 8) :=
  mixedEncode A (lineItems enc (ops ++ [.inr .zeroUpper]))

/-- The positions of a block denote its line program, inside any list of positions. -/
theorem mixedExpected_lineItems (A : VecAsm) (enc : JInstr 64 → List (BitVec 8))
    (all : List MixedItem) :
    ∀ ops, mixedExpected all (mixedItems A (lineItems enc ops)) = some (lineProg ops)
  | [] => rfl
  | o :: ops => by
    have ih := mixedExpected_lineItems A enc all ops
    cases o with
    | inl i =>
      show (mixedExpected all (mixedItems A (lineItems enc ops))).map (Sum.inl (.op i) :: ·) = _
      rw [ih]
      rfl
    | inr v =>
      show (mixedExpected all (mixedItems A (lineItems enc ops))).map (Sum.inr v :: ·) = _
      rw [ih]
      rfl

/-- The positions of a block contain no branch, so their branch condition holds. -/
theorem mixedBranchOK_lineItems (A : VecAsm) (enc : JInstr 64 → List (BitVec 8))
    (all : List MixedItem) :
    ∀ ops off, mixedBranchOK all off (mixedItems A (lineItems enc ops)) = true
  | [], _ => rfl
  | o :: ops, off => by
    cases o with
    | inl i =>
      show (true && mixedBranchOK all _ (mixedItems A (lineItems enc ops))) = true
      rw [mixedBranchOK_lineItems A enc all ops]
      rfl
    | inr v =>
      show (true && mixedBranchOK all _ (mixedItems A (lineItems enc ops))) = true
      rw [mixedBranchOK_lineItems A enc all ops]
      rfl

/-- The scalar positions of a block are well formed when the position of each scalar
    operation is. -/
theorem lineItems_ok {enc : JInstr 64 → List (BitVec 8)} {ops : List (JInstr 64 ⊕ VInstr)}
    (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) :
    ∀ it, Sum.inl it ∈ lineItems enc ops → ItemOK it := by
  intro it hit
  simp only [lineItems, List.mem_append, List.mem_map, List.mem_singleton, Sum.inl.injEq] at hit
  rcases hit with ⟨o, ho, he⟩ | rfl
  · cases o with
    | inl i =>
      simp only [Sum.map_inl, Sum.inl.injEq] at he
      subst he
      exact hok i ho
    | inr v => simp at he
  · exact mkRet_ok

/-- The vector instructions of a block have entries in the table when the block's do. -/
theorem lineItems_encodable {A : VecAsm} {enc : JInstr 64 → List (BitVec 8)}
    {ops : List (JInstr 64 ⊕ VInstr)} (hv : ∀ v, Sum.inr v ∈ ops → A.Encodable v) :
    ∀ v, Sum.inr v ∈ lineItems enc ops → A.Encodable v := by
  intro v hv'
  simp only [lineItems, List.mem_append, List.mem_map, List.mem_singleton, reduceCtorEq,
    or_false] at hv'
  obtain ⟨o, ho, he⟩ := hv'
  cases o with
  | inl i => simp at he
  | inr w =>
    simp only [Sum.map_inr, id_eq, Sum.inr.injEq] at he
    subst he
    exact hv w ho

/-- Every vector instruction of the block `ops` and the closing `vzeroupper` have an entry in
    the table `A`. -/
def BlockEncodable (A : VecAsm) (ops : List (JInstr 64 ⊕ VInstr)) : Prop :=
  ∀ v, Sum.inr v ∈ ops ++ [.inr .zeroUpper] → A.Encodable v

variable {A : VecAsm}

/-- **The bytes of a block followed by `ret` decode to its line program**, for a lawful
    table, encodable vector instructions and well-formed positions of the scalar
    operations. -/
theorem mixedDecode_lineItems (hA : A.Lawful) (enc : JInstr 64 → List (BitVec 8))
    (ops : List (JInstr 64 ⊕ VInstr)) (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i))
    (hv : ∀ v, Sum.inr v ∈ ops → A.Encodable v) :
    mixedDecode A (mixedEncode A (lineItems enc ops)) = some (lineProg ops) :=
  (mixedDecode_mixedEncode hA _ (lineItems_ok hok) (lineItems_encodable hv)
    (mixedBranchOK_lineItems A enc _ ops 0)).trans
    (mixedExpected_lineItems A enc _ ops)

/-! ## 2. The kernel on the machine of mixed images -/

variable (r : DoitRegime) {m : Mode}
  {cpu : List (BitVec 8) → AState × VState → AState × VState → Prop}

/-- **`mixedMach` decodes the bytes of a kernel block** to the line program of the block
    followed by `vzeroupper`. -/
theorem lineBytes_decode (m : Mode) (hA : A.Lawful) (enc : JInstr 64 → List (BitVec 8))
    (ops : List (JInstr 64 ⊕ VInstr)) (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i))
    (hv : BlockEncodable A ops) :
    (mixedMach A r m).decode (lineBytes A enc ops)
      = some (lineProg (ops ++ [.inr .zeroUpper])) :=
  mixedDecode_lineItems hA enc _ (fun i hi => hok i (by simpa using hi)) hv

/-- The runs of `kernelRun` are the runs with leakage of the line program on `mixedMach`. -/
theorem kernelRun_iff_mixedMach (A : VecAsm) (ops : List (JInstr 64 ⊕ VInstr)) (s : AState)
    (t : List CTLeak) (s' : AState) :
    kernelRun r m ops s t s' ↔ ∃ v v' : VState,
      (mixedMach A r m).RunL (fun _ _ => True) (lineProg (ops ++ [.inr .zeroUpper])) 0 (s, v) t
        (s', v') :=
  exists_congr fun _ => exists_congr fun _ => mixedMach_runL.symm

/-- **The kernel contract at the byte level.** For a lawful table that encodes the vector
    instructions of the block and well-formed positions of the scalar operations,
    `mixedMach` decodes the bytes of the kernel block to a program whose runs with leakage,
    from any vector state to any vector state, are `kernelRun`. -/
theorem kernelImage (hA : A.Lawful) (enc : JInstr 64 → List (BitVec 8))
    (ops : List (JInstr 64 ⊕ VInstr)) (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i))
    (hv : BlockEncodable A ops) :
    ∃ prog, (mixedMach A r m).decode (lineBytes A enc ops) = some prog ∧
      ∀ (s : AState) (t : List CTLeak) (s' : AState), kernelRun r m ops s t s' ↔
        ∃ v v' : VState, (mixedMach A r m).RunL (fun _ _ => True) prog 0 (s, v) t (s', v') :=
  ⟨_, lineBytes_decode r m hA enc ops hok hv, kernelRun_iff_mixedMach r A ops⟩

/-! ## 3. The scalar operations of a kernel text -/

/-- **The bytes of the scalar operations of a kernel text**: `movl $v, %eax` as `B8 id`;
    `subq $n, %rsp` and `addq $n, %rsp` as `REX.W 83 /digit ib` when `n` fits a
    sign-extended byte and as `REX.W 81 /digit id` otherwise. Every other operation has no
    bytes. -/
def frameEnc : JInstr 64 → List (BitVec 8)
  | .mov d (.imm v) => if d = "%rax" then encMovImmw 0 0 v else []
  | .sub d (.imm n) =>
      if d = "%rsp" then (if fitsImm8S 1 n then encAluImm8 1 5 4 n else encAluImmw 1 5 4 n)
      else []
  | .add d (.imm n) =>
      if d = "%rsp" then (if fitsImm8S 1 n then encAluImm8 1 0 4 n else encAluImmw 1 0 4 n)
      else []
  | _ => []

/-- The position of `movl $v, %eax` is well formed for `v` below `2 ^ 32`. -/
theorem frameEnc_mov_ok (v : Nat) (hv : v < 2 ^ 32) :
    ItemOK (scalarItem frameEnc (.mov "%rax" (.imm v))) := by
  have e : frameEnc (.mov "%rax" (.imm v)) = encMovImmw 0 0 v := by simp [frameEnc]
  unfold scalarItem
  rw [e]
  exact ItemOK_of_decode fun rest => decodeLinstr_movImm32 0 v rest (by decide) hv

/-- The position of `subq $n, %rsp` is well formed for `n` below `2 ^ 31`. -/
theorem frameEnc_sub_ok (n : Nat) (hn : n < 2 ^ 31) :
    ItemOK (scalarItem frameEnc (.sub "%rsp" (.imm n))) := by
  unfold scalarItem
  by_cases h8 : fitsImm8S 1 n = true
  · have e : frameEnc (.sub "%rsp" (.imm n)) = encAluImm8 1 5 4 n := by simp [frameEnc, h8]
    rw [e]
    exact ItemOK_of_decode fun rest =>
      decodeLinstr_aluImm8 5 JInstr.sub 4 n rest (by decide) (by decide) h8 rfl
  · have e : frameEnc (.sub "%rsp" (.imm n)) = encAluImmw 1 5 4 n := by simp [frameEnc, h8]
    rw [e]
    exact ItemOK_of_decode fun rest =>
      decodeLinstr_aluImm32 5 JInstr.sub 4 n rest (by decide) (by decide) (by omega)
        (by simp only [ScalarEncoder.fitsImm32S, Bool.or_eq_true, decide_eq_true_eq]
            exact Or.inl hn) rfl

/-- The position of `addq $n, %rsp` is well formed for `n` below `2 ^ 31`. -/
theorem frameEnc_add_ok (n : Nat) (hn : n < 2 ^ 31) :
    ItemOK (scalarItem frameEnc (.add "%rsp" (.imm n))) := by
  unfold scalarItem
  by_cases h8 : fitsImm8S 1 n = true
  · have e : frameEnc (.add "%rsp" (.imm n)) = encAluImm8 1 0 4 n := by simp [frameEnc, h8]
    rw [e]
    exact ItemOK_of_decode fun rest =>
      decodeLinstr_aluImm8 0 JInstr.add 4 n rest (by decide) (by decide) h8 rfl
  · have e : frameEnc (.add "%rsp" (.imm n)) = encAluImmw 1 0 4 n := by simp [frameEnc, h8]
    rw [e]
    exact ItemOK_of_decode fun rest =>
      decodeLinstr_aluImm32 0 JInstr.add 4 n rest (by decide) (by decide) (by omega)
        (by simp only [ScalarEncoder.fitsImm32S, Bool.or_eq_true, decide_eq_true_eq]
            exact Or.inl hn) rfl

/-- **The scalar operations of a text instruction**: `movl` to `%eax` and the two moves of
    `%rsp`. -/
theorem opOfText_inl {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))}
    {i : ZmmTextModel.Instr} {j : JInstr 64} (h : opOfText m ro i = some (.inl j)) :
    (∃ imm : BitVec 32, i = .movEax imm ∧ j = .mov "%rax" (.imm imm.toNat))
      ∨ (∃ n, i = .spSub n ∧ j = .sub "%rsp" (.imm n))
      ∨ (∃ n, i = .spAdd n ∧ j = .add "%rsp" (.imm n)) := by
  cases i with
  | op L o src x d => cases src <;> simp [opOfText] at h
  | movEax imm =>
    simp only [opOfText, Option.some.injEq, Sum.inl.injEq] at h
    exact .inl ⟨imm, rfl, h.symm⟩
  | spSub n =>
    simp only [opOfText, Option.some.injEq, Sum.inl.injEq] at h
    exact .inr (.inl ⟨n, rfl, h.symm⟩)
  | spAdd n =>
    simp only [opOfText, Option.some.injEq, Sum.inl.injEq] at h
    exact .inr (.inr ⟨n, rfl, h.symm⟩)
  | _ => simp [opOfText] at h

/-- An operation of the block of a text is the operation of one of its instructions. -/
theorem blockOfText_mem {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))} :
    ∀ (prog : List ZmmTextModel.Instr) (ops : List (JInstr 64 ⊕ VInstr)),
      blockOfText m ro prog = some ops → ∀ o ∈ ops, ∃ i ∈ prog, opOfText m ro i = some o
  | [], ops, h, o, ho => by
    simp only [blockOfText, Option.some.injEq] at h
    subst h
    simp at ho
  | i :: is, ops, h, o, ho => by
    simp only [blockOfText] at h
    cases hi : opOfText m ro i with
    | none => rw [hi] at h; simp at h
    | some a =>
      rw [hi] at h
      cases hr : blockOfText m ro is with
      | none => rw [hr] at h; simp at h
      | some rest =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp ho with rfl | ho
        · exact ⟨i, List.mem_cons_self, hi⟩
        · obtain ⟨i', hi', he⟩ := blockOfText_mem is rest hr o ho
          exact ⟨i', List.mem_cons_of_mem _ hi', he⟩

/-- A move of `%rsp` in a framed text is by at most the frame size. -/
theorem textFramed_move_le {m : Mode} {In Out : Nat → Prop} {F : Nat} :
    ∀ (prog : List ZmmTextModel.Instr) (dp : Nat), TextFramed m In Out F dp prog → dp ≤ F →
      ∀ n, (ZmmTextModel.Instr.spSub n ∈ prog ∨ ZmmTextModel.Instr.spAdd n ∈ prog) → n ≤ F
  | [], _, _, _, n, hn => by simp at hn
  | i :: is, dp, h, hdp, n, hn => by
    obtain ⟨hfit, hrest⟩ := h
    have hdp' : depthStep dp i ≤ F := by
      cases i with
      | spSub k => exact hfit.2
      | spAdd k => exact le_trans (Nat.sub_le _ _) hdp
      | _ => exact hdp
    have ih := textFramed_move_le is _ hrest hdp' n
    rcases hn with hn | hn <;> rcases List.mem_cons.mp hn with rfl | hn
    · exact le_trans (Nat.le_add_left _ _) hfit.2
    · exact ih (.inl hn)
    · exact le_trans hfit.2 hdp
    · exact ih (.inr hn)

/-- **A move of `%rsp` in a text that passes the frame check is by at most the frame
    size.** -/
theorem framedB_move_le {m : Mode} {inLen nOut F : Nat} {prog : List ZmmTextModel.Instr}
    (h : framedB m inLen nOut F 0 prog = true) (n : Nat)
    (hn : ZmmTextModel.Instr.spSub n ∈ prog ∨ ZmmTextModel.Instr.spAdd n ∈ prog) : n ≤ F :=
  textFramed_move_le prog 0 (framedB_sound prog 0 h) (Nat.zero_le _) n hn

/-- The positions `frameEnc` gives the scalar operations of the block of a text are well
    formed, when every move of `%rsp` in the text is by less than `2 ^ 31`. -/
theorem frameEnc_ok_of_text {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))}
    {prog : List ZmmTextModel.Instr} {ops : List (JInstr 64 ⊕ VInstr)}
    (hops : blockOfText m ro prog = some ops)
    (hb : ∀ n, (ZmmTextModel.Instr.spSub n ∈ prog ∨ ZmmTextModel.Instr.spAdd n ∈ prog) →
      n < 2 ^ 31) :
    ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem frameEnc i) := by
  intro j hj
  obtain ⟨i, hi, he⟩ := blockOfText_mem prog ops hops _ hj
  rcases opOfText_inl he with ⟨imm, rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨n, rfl, rfl⟩
  · exact frameEnc_mov_ok _ imm.isLt
  · exact frameEnc_sub_ok n (hb n (.inl hi))
  · exact frameEnc_add_ok n (hb n (.inr hi))

/-- **The scalar positions of the block of a framed text are well formed**, for a frame
    below `2 ^ 31` bytes. -/
theorem frameEnc_ok_of_framed {m : Mode} {ro : Std.HashMap String (Array (BitVec 64))}
    {prog : List ZmmTextModel.Instr} {ops : List (JInstr 64 ⊕ VInstr)} {inLen nOut F : Nat}
    (hops : blockOfText m ro prog = some ops)
    (hfr : framedB m inLen nOut F 0 prog = true) (hF : F < 2 ^ 31) :
    ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem frameEnc i) :=
  frameEnc_ok_of_text hops fun n hn => lt_of_le_of_lt (framedB_move_le hfr n hn) hF

/-! ## 4. The processor on the bytes of a kernel -/

/-- A faithful processor has every run of `kernelRun` on the bytes of the kernel, between
    some vector states. -/
theorem faithful_kernelRun (hF : A.Faithful r m cpu) (hA : A.Lawful)
    {enc : JInstr 64 → List (BitVec 8)} {ops : List (JInstr 64 ⊕ VInstr)}
    (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) (hv : BlockEncodable A ops)
    {s : AState} {t : List CTLeak} {s' : AState} (h : kernelRun r m ops s t s') :
    ∃ v v' : VState, cpu (lineBytes A enc ops) (s, v) (s', v') := by
  obtain ⟨v, v', hX⟩ := h
  exact ⟨v, v', hF _ _ _ _ (lineBytes_decode r m hA enc ops hok hv) hX.haltsC⟩

/-- **A faithful processor returns from the bytes of a kernel, from every vector state**,
    in the return state of a run of `kernelRun`. -/
theorem faithful_kernel_total (hF : A.Faithful r m cpu) (hA : A.Lawful)
    {enc : JInstr 64 → List (BitVec 8)} {ops : List (JInstr 64 ⊕ VInstr)}
    (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) (hv : BlockEncodable A ops)
    (s : AState) (v : VState) :
    ∃ (t : List CTLeak) (s' : AState) (v' : VState),
      kernelRun r m ops s t s' ∧ cpu (lineBytes A enc ops) (s, v) (s', v') := by
  have hX : (x86VecMach r m).RunL (fun _ _ => True) (lineProg (ops ++ [.inr .zeroUpper])) 0
      (s, v) ((x86VecMach r m).blockLeak (s, v) (ops ++ [.inr .zeroUpper]))
      (((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).1,
        ((x86VecMach r m).runBlock (s, v) (ops ++ [.inr .zeroUpper])).2) :=
    (runL_lineProg r m _ _ _ _ _).mpr ⟨IsaMachine.blockOk_true _ _ _, rfl, rfl⟩
  exact ⟨_, _, _, ⟨v, _, hX⟩, hF _ _ _ _ (lineBytes_decode r m hA enc ops hok hv) hX.haltsC⟩

/-- **The processor on the bytes of a kernel that meets a callee specification.** Let
    `kernelRun` of the block meet the signature `sig`, the processor be faithful to a lawful
    table that encodes the vector instructions of the block, and the positions of the
    scalar operations be well formed. Then from every entry
    state that satisfies the precondition, with any vector state, the processor returns
    from the bytes of the kernel in a state that satisfies the postcondition, with `%rsp`
    restored, every register outside the clobber set kept and every byte outside the
    footprint kept. -/
theorem faithful_calleeSpec {sig : CalleeSig} {ops : List (JInstr 64 ⊕ VInstr)}
    (hS : CalleeSpec (kernelRun r m ops) sig) (hF : A.Faithful r m cpu) (hA : A.Lawful)
    {enc : JInstr 64 → List (BitVec 8)}
    (hok : ∀ i, Sum.inl i ∈ ops → ItemOK (scalarItem enc i)) (hv : BlockEncodable A ops)
    (s : AState) (hpre : sig.pre s) (v : VState) :
    ∃ (s' : AState) (v' : VState), cpu (lineBytes A enc ops) (s, v) (s', v')
      ∧ sig.post s s'
      ∧ s'.regs "%rsp" = s.regs "%rsp"
      ∧ (∀ x, sig.clob x = false → s'.regs x = s.regs x)
      ∧ ∀ a, ¬ sig.foot s a → s'.mem a = s.mem a := by
  obtain ⟨t, s', v', hX, hc⟩ := faithful_kernel_total r hF hA hok hv s v
  exact ⟨s', v', hc, hS.post s t s' hpre hX, hS.rsp s t s' hpre hX, hS.keep s t s' hpre hX,
    hS.frame s t s' hpre hX⟩

/-- **The processor on the bytes of a vector kernel given as text.** When `vectorizeEmit V`
    returns `text` for the scalar program `c`, the text parses, and for every block `ops` of
    its parsed program, every input length and every frame size below `2 ^ 31` at which the
    program passes the frame check, every lawful table that encodes the vector instructions
    of the block and every processor faithful to it:
    from an entry state with disjoint regions whose input region holds parameters
    lane-wise, with any vector state, the processor returns from the bytes
    `lineBytes A frameEnc ops` in a state whose output region holds lane-wise the outputs
    of `c`, with `%rsp` restored, every register but `%rax` kept and every byte outside the
    output region and the frame kept. -/
theorem vectorKernel_image (V : VecShape) {Γ : JCtxt} {t : JasminTy} {sym : String}
    {inOffset : Nat → Nat} {nOut : Nat} {c : Com jasminDialect Γ t} {inBound : Option Nat}
    {text : String} (h : vectorizeEmit V sym inOffset nOut c inBound = .ok text) :
    ∃ prog ro, parse V.mode text = .ok (prog, ro) ∧
      ∀ (ops : List (JInstr 64 ⊕ VInstr)) (inLen F : Nat),
        blockOfText V.mode ro prog = some ops → framedB V.mode inLen nOut F 0 prog = true →
        F < 2 ^ 31 →
        ∀ (A : VecAsm) (cpu : List (BitVec 8) → AState × VState → AState × VState → Prop),
          A.Lawful → A.Faithful r V.mode cpu → BlockEncodable A ops →
          ∀ s : AState, (kernelSig V inOffset inBound nOut c inLen F).pre s → ∀ v : VState,
            ∃ (s' : AState) (v' : VState), cpu (lineBytes A frameEnc ops) (s, v) (s', v')
              ∧ (kernelSig V inOffset inBound nOut c inLen F).post s s'
              ∧ s'.regs "%rsp" = s.regs "%rsp"
              ∧ (∀ x, (kernelSig V inOffset inBound nOut c inLen F).clob x = false →
                  s'.regs x = s.regs x)
              ∧ ∀ a, ¬ (kernelSig V inOffset inBound nOut c inLen F).foot s a →
                  s'.mem a = s.mem a := by
  obtain ⟨prog, ro, hp, hk⟩ := vectorKernel_calleeSpec r V h
  exact ⟨prog, ro, hp, fun ops inLen F hops hfr hF A cpu hA hFa hv s hpre v =>
    faithful_calleeSpec r (hk ops inLen F hops hfr) hFa hA
      (frameEnc_ok_of_framed hops hfr hF) hv s hpre v⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.VecKernelImage
