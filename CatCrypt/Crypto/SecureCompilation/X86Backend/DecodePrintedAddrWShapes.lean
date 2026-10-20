/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunASim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

@[expose] public section

set_option autoImplicit false

/-!
# The step relation of the carry-chain simulation and the shapes of its arms

The simulation of a body in `printedAddrWB` by its decoded bytes relates the two machines by
`RelW`: the registers and memories by `ACorrW`, the machine zero flag to the flag of the
address machine at a conditional branch, and the machine carry flag to the carry-out of the
add before a carry-out binding (`CarryReq`). The relation reads the program counter of the
address machine and the instruction at it, so it is the relation `Rel` of
`RunASim.runA_reaches_of_step`.

## Main results

* `RelW.label`, `RelW.cond_taken`, `RelW.cond_fall`: the relation after a label and after a
  taken and a fall-through branch on the zero flag.
* `RelW.next`: the relation after the step of an instruction that is no compare arm and no
  `ADCX:64`, for every flag and every pair of states related by `ACorrW`.
* Per arm family, the tagged instruction the address machine steps (`li_eq`), and the facts
  that the arm is no compare (`not_cmp`) and no `ADCX:64` (`not_adcx`): the carry arms
  `CArm`, the cell arms `MArm`, the slot carry arms `SArm`, the arms `AArm` of
  `DecodePrintedAddr`, and the materialised comparisons (`eInstr`, `eiInstr`), the
  register-count shifts (`xInstr`) and the arithmetic right shifts by an immediate
  (`rInstr`), with the decoded instructions of their shapes (`shape_ops`).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (MemTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

/-! ## 1. The relation -/

/-- **The step relation of the carry-chain simulation** at the program counter of `s`: the
    states are related by `ACorrW`, the machine zero flag is `zf` at a conditional branch, and
    the machine carry flag holds the carry-out of the add before a carry-out binding. -/
structure RelW (rsp : BitVec 64) (body : Lcmd) (sa : AState) (s : LstateA) (zf : Bool) :
    Prop where
  /-- The registers and memories are related. -/
  acorr : ACorrW rsp sa s
  /-- At a conditional branch the machine zero flag is `zf`. -/
  flag : ∀ ii c l, body[s.reg.lpc]? = some ⟨ii, .Lcond c l⟩ → sa.flags.zf.getD false = zf
  /-- At a carry-out binding the machine carry flag holds the carry-out of its add. -/
  carry : CarryReq (frameP (Params.ofBody body) rsp) body s.reg.lpc sa s

/-- The instruction after one that is no compare arm is no conditional branch. -/
theorem next_not_cond {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) {k : Nat}
    {ii : Nat} {li : LinstrR} (hb : body[k]? = some ⟨ii, li⟩)
    (hc : (classifyA li).any cmpArmB = false) (ii' : Nat) (c : LOperand) (l : LLabel) :
    body[k + 1]? ≠ some ⟨ii', .Lcond c l⟩ := by
  intro h
  have hk : k + 1 < body.length := (List.getElem?_eq_some_iff.mp h).1
  have hc2 := hF.cond (k + 1) hk
  unfold condPrevB at hc2
  rw [h] at hc2
  simp [hb, hc] at hc2

/-- The instruction after one that is no `ADCX:64` finds no carry requirement. -/
theorem next_no_carry {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) {k : Nat}
    {ii : Nat} {li : LinstrR} (hb : body[k]? = some ⟨ii, li⟩)
    (hna : ∀ d a s c, li ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
    (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA) :
    CarryReq frame body (k + 1) sa s := by
  intro ii' O A S C h
  have hk : k + 1 < body.length := (List.getElem?_eq_some_iff.mp h).1
  refine no_carryReq hF hk (fun ii₁ d a₁ s₁ c₁ h₁ => ?_) frame sa s ii' O A S C h
  rw [hb] at h₁
  simp only [Option.some.injEq, Linstr.mk.injEq] at h₁
  exact hna d a₁ s₁ c₁ h₁.2

/-- **The relation after an instruction that is no compare arm and no `ADCX:64`**, for every
    flag and every pair of states related by `ACorrW` at the next instruction. -/
theorem RelW.next {rsp : BitVec 64} {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    {s : LstateA} {ii : Nat} {li : LinstrR} (hb : body[s.reg.lpc]? = some ⟨ii, li⟩)
    (hc : (classifyA li).any cmpArmB = false)
    (hna : ∀ d a s c, li ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
    {sa' : AState} {s' : LstateA} (hac : ACorrW rsp sa' s') (hpc : s'.reg.lpc = s.reg.lpc + 1)
    (zf' : Bool) : RelW rsp body sa' s' zf' := by
  refine ⟨hac, ?_, ?_⟩
  · intro ii' c l h
    rw [hpc] at h
    exact absurd h (next_not_cond hF hb hc ii' c l)
  · rw [hpc]
    exact next_no_carry hF hb hna _ _ _

/-- The relation after a label. -/
theorem RelW.label {rsp : BitVec 64} {body : Lcmd} {shs : List DShape}
    (hF : BodyFactsW body shs) {sa : AState} {s : LstateA} {zf : Bool}
    (hR : RelW rsp body sa s zf) {ii : Nat} {kd : LabelKind} {l : LLabel}
    (hb : body[s.reg.lpc]? = some ⟨ii, .Llabel kd l⟩) :
    RelW rsp body sa (s.setLpc (s.reg.lpc + 1)) zf :=
  RelW.next hF hb (by rw [classifyA_label]; rfl) (by intro d a s c h; cases h)
    (acorrW_setLpc hR.acorr _) rfl zf

/-- The relation after a fall-through branch. -/
theorem RelW.cond_fall {rsp : BitVec 64} {body : Lcmd} {shs : List DShape}
    (hF : BodyFactsW body shs) {sa : AState} {s : LstateA} {zf : Bool}
    (hR : RelW rsp body sa s zf) {ii : Nat} {c : LOperand} {l : LLabel}
    (hb : body[s.reg.lpc]? = some ⟨ii, .Lcond c l⟩) :
    RelW rsp body sa (s.setLpc (s.reg.lpc + 1)) zf :=
  RelW.next hF hb (by rw [classifyA_cond]; rfl) (by intro d a s c h; cases h)
    (acorrW_setLpc hR.acorr _) rfl zf

/-- The relation after a taken branch to the label at position `p`. -/
theorem RelW.cond_taken {rsp : BitVec 64} {body : Lcmd} {sa : AState} {s : LstateA}
    {zf : Bool} (hR : RelW rsp body sa s zf) {l : LLabel} {p : Nat}
    (hp : labelAt body l = some p) : RelW rsp body sa (s.setLpc p) zf := by
  obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
  refine ⟨acorrW_setLpc hR.acorr p, ?_, ?_⟩
  · intro ii' c' l' h
    have h' : body[p]? = some ⟨ii', .Lcond c' l'⟩ := h
    rw [List.getElem?_eq_getElem hpl, Option.some.injEq] at h'
    rw [h'] at hlab
    simp [isLabelB] at hlab
  · intro ii' O A S C h
    have h' : body[p]? = some ⟨ii', .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]⟩ := h
    rw [List.getElem?_eq_getElem hpl, Option.some.injEq] at h'
    rw [h'] at hlab
    simp [isLabelB] at hlab

/-! ## 2. The arm families -/

/-- The address machine steps a carry arm as its untagged instruction. -/
@[simp] theorem CArm.li_eq (body : Lcmd) (k : Nat) (c : CArm) :
    (normA c.instr, tagAt body k c.instr) = (c.instr, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases c <;> rfl)]
  cases c <;> simp +decide [CArm.instr, normA, tagA]

/-- A carry arm is no compare arm. -/
@[simp] theorem CArm.not_cmp (c : CArm) : (classifyA c.instr).any cmpArmB = false := by
  cases c <;> exact classifyA_three_not_cmp _ _ _ _ _

/-- The address machine steps a cell arm as its untagged instruction. -/
@[simp] theorem MArm.li_eq (body : Lcmd) (k : Nat) (m : MArm) :
    (normA m.instr, tagAt body k m.instr) = (m.instr, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases m <;> rfl)]
  cases m <;> simp +decide [MArm.instr, normA, tagA]

/-- A cell arm is no `ADCX:64`. -/
@[simp] theorem MArm.not_adcx (m : MArm) (d a s c : String) :
    m.instr ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c] := by
  cases m <;> simp [MArm.instr]

/-- The address machine steps a slot carry arm as its untagged instruction. -/
@[simp] theorem SArm.li_eq (body : Lcmd) (k : Nat) (c : SArm) :
    (normA c.instr, tagAt body k c.instr) = (c.instr, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases c <;> rfl)]
  cases c <;> simp +decide [SArm.instr, normA, tagA]

/-- A slot carry arm is no compare arm. -/
@[simp] theorem SArm.not_cmp (c : SArm) : (classifyA c.instr).any cmpArmB = false := by
  cases c <;> exact classifyA_three_not_cmp _ _ _ _ _

/-- An arm of `DecodePrintedAddr` is no `ADCX:64`. -/
@[simp] theorem AArm.not_adcx (a : AArm) (d x s c : String) :
    a.instr ≠ .Lopn [.reg d] "ADCX:64" [.reg x, .reg s, .reg c] := by
  cases a with
  | reg a => cases a <;> simp [AArm.instr, Arm.instr]
  | _ => simp [AArm.instr]

/-- The address machine steps a materialised comparison as its untagged instruction. -/
@[simp] theorem eInstr_li_eq (body : Lcmd) (k : Nat) (n : Bool) (D A B : String) :
    (normA (eInstr n D A B), tagAt body k (eInstr n D A B))
      = (eInstr n D A B, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases n <;> rfl)]
  cases n <;> simp +decide [eInstr, eMnem, normA, tagA]

/-- A materialised comparison is no compare arm. -/
@[simp] theorem eInstr_not_cmp (n : Bool) (D A B : String) :
    (classifyA (eInstr n D A B)).any cmpArmB = false := by
  cases n <;> simp +decide [eInstr, eMnem, classifyA, classify] <;> split <;> rfl

/-- A materialised comparison is no `ADCX:64`. -/
@[simp] theorem eInstr_not_adcx (n : Bool) (D A B d a s c : String) :
    eInstr n D A B ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c] := by
  simp [eInstr]

/-- The computed shape of a materialised comparison decodes to its machine instructions. -/
theorem eInstr_shape_ops {P : Params} {n : Bool} {D A B : String} (h : eOk D A B = true)
    {sh : DShape} (hs : shapeOf P (eInstr n D A B) = some sh) :
    sh.ops' = (ePieces n D A B).map Prod.snd := by
  obtain ⟨hb, hp⟩ := eBytes P n D A B h
  exact shapeOf_lopn_ops _ hb hp hs

/-- The address machine steps a register-count shift as its untagged instruction. -/
@[simp] theorem xInstr_li_eq (body : Lcmd) (k : Nat) (l : Bool) (D A B : String) :
    (normA (xInstr l D A B), tagAt body k (xInstr l D A B))
      = (xInstr l D A B, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases l <;> rfl)]
  cases l <;> simp +decide [xInstr, xMnem, normA, tagA]

/-- A register-count shift is no compare arm. -/
@[simp] theorem xInstr_not_cmp (l : Bool) (D A B : String) :
    (classifyA (xInstr l D A B)).any cmpArmB = false := by
  cases l <;> simp +decide [xInstr, xMnem, classifyA, classify] <;> split <;> rfl

/-- A register-count shift is no `ADCX:64`. -/
@[simp] theorem xInstr_not_adcx (l : Bool) (D A B d a s c : String) :
    xInstr l D A B ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c] := by
  simp [xInstr]

/-- The computed shape of a register-count shift decodes to its machine instructions. -/
theorem xInstr_shape_ops {P : Params} {l : Bool} {D A B : String} (h : xOk D A B = true)
    {sh : DShape} (hs : shapeOf P (xInstr l D A B) = some sh) :
    sh.ops' = (xPieces l D A B).map Prod.snd := by
  obtain ⟨hb, hp⟩ := xBytes P l D A B h
  exact shapeOf_lopn_ops _ hb hp hs

/-- The address machine steps a materialised comparison with an immediate as its untagged
    instruction. -/
@[simp] theorem eiInstr_li_eq (body : Lcmd) (k : Nat) (n : Bool) (D A : String) (v : Nat) :
    (normA (eiInstr n D A v), tagAt body k (eiInstr n D A v))
      = (eiInstr n D A v, MemTag.reg none) := by
  rw [tagAt_of_ne (by cases n <;> rfl)]
  cases n <;> simp +decide [eiInstr, eMnem, normA, tagA]

/-- A materialised comparison with an immediate is no compare arm. -/
@[simp] theorem eiInstr_not_cmp (n : Bool) (D A : String) (v : Nat) :
    (classifyA (eiInstr n D A v)).any cmpArmB = false := by
  cases n <;> simp +decide [eiInstr, eMnem, classifyA, classify] <;> split <;> rfl

/-- A materialised comparison with an immediate is no `ADCX:64`. -/
@[simp] theorem eiInstr_not_adcx (n : Bool) (D A : String) (v : Nat) (d a s c : String) :
    eiInstr n D A v ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c] := by
  simp [eiInstr]

/-- The computed shape of a materialised comparison with an immediate decodes to its machine
    instructions. -/
theorem eiInstr_shape_ops {P : Params} {n : Bool} {D A : String} {v : Nat}
    (h : eiOk D A v = true) {sh : DShape} (hs : shapeOf P (eiInstr n D A v) = some sh) :
    sh.ops' = (eiPieces n D A v).map Prod.snd := by
  obtain ⟨hb, hp⟩ := eiBytes P n D A v h
  exact shapeOf_lopn_ops _ hb hp hs

/-- The address machine steps an arithmetic right shift by an immediate as its untagged
    instruction. -/
@[simp] theorem rInstr_li_eq (body : Lcmd) (k : Nat) (D : String) (kc : Nat) :
    (normA (rInstr D kc), tagAt body k (rInstr D kc)) = (rInstr D kc, MemTag.reg none) := by
  rw [tagAt_of_ne rfl]
  simp +decide [rInstr, normA, tagA]

/-- An arithmetic right shift by an immediate is no compare arm. -/
@[simp] theorem rInstr_not_cmp (D : String) (kc : Nat) :
    (classifyA (rInstr D kc)).any cmpArmB = false := by
  simp +decide [rInstr, classifyA, classify, cmpArmB]

/-- An arithmetic right shift by an immediate is no `ADCX:64`. -/
@[simp] theorem rInstr_not_adcx (D : String) (kc : Nat) (d a s c : String) :
    rInstr D kc ≠ .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c] := by
  simp [rInstr]

/-- The computed shape of an arithmetic right shift by an immediate decodes to its machine
    instructions. -/
theorem rInstr_shape_ops {P : Params} {D : String} {kc : Nat} (h : rOk D kc = true)
    {sh : DShape} (hs : shapeOf P (rInstr D kc) = some sh) :
    sh.ops' = (rPieces D kc).map Prod.snd := by
  obtain ⟨hb, hp⟩ := rBytes_encode P D kc h
  exact shapeOf_lopn_ops _ hb hp hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
