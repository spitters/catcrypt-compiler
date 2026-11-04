/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells

/-!
# The image simulation at an indexed store through a cell

An indexed store through a cell (`JasminLsemAddrImage.cellIdxStore?`) is a window of a printed
body: the load of the index register `X` from a frame slot or a literal, instructions that write
neither `X` nor the frame slot, the address `LEA:64 D, (B, X, 8)` with `B` the pointer of an
array `A`, the load of the value, and the cell store `MOV:64 mem.D.0, v`. The image of the store
is the name-keyed store into `A` at the index (`JasminLsemAddrImage.cellStoreImg`), and the
address machine writes through the address register `D`. The two machines write the same cell
when `D` holds the address of the word of the index, a fact of the instructions of the window
before the store.

That fact is `CidxInv`, an invariant on the image state beside `ImageAddrSimW.ImgRelW`, keyed
by the program counter. The relation of a wide simulation segment is `ImgRelW` and `CidxInv`.

## Main definitions

* `cidxArmAt`, `cidxArmB`: the arm of the gate at such a store.
* `cidxRegs`: the address register and the index register of a window.
* `idxSrcVal`: the value of the index of a window on an image register file.
* `CidxInv`: the invariant of the window.

## Main results

* `cidxCoversB`, `CidxInv.of_outside`: the positions a window covers, and the invariant at a
  position that no window covers.
* `img_keep`: the image of an instruction that writes no word of a name keeps that word.
* `imgStep_pc`: the program counter after a step of the image at a gated position.
* `cidxInv_step`: a step of the image at a gated position keeps the invariant.
* `rel_cidxStoreW`: the store keeps `ImgRelW`, at a frame-slot index as the indexed store
  `ImageAddrSimW.rel_stxW` and at a literal index as the constant-index store
  `ImageAddrSimW.rel_simmW`.
* `cidxInv_store`: the invariant after the store.
* `img_stepCW`: the step of the image at a store passing `cidxArmB`, into `ImgRelW` and the
  invariant.
* `cidxArmCW`, `gateCW`, `imgGateCW`: the gate of the wide image simulation with indexed stores
  through a cell; `imgGateW_of_imgGateCW`, its positionwise form, and `imgGateCW_of_imgGateBW`,
  `cidxInv_of_imgGateBW`, the gate `imgGateBW` as an instance.
* `safeAt_of_cidxArmCW`: the safety of the address machine at such a store.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel isLabel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet stackGet_id)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimWCond
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (fstepA_mov64_store)

/-! ## 1. The arm of the gate -/

/-- The arm of an indexed store through a cell at position `k`, at the width analyses `W3` at
    `k - 3` and `W` at `k`: the instruction is such a store (`cellIdxStore?`), its cell lies
    outside `W`, its address register and its value have no frame word and lie outside `W`, a
    literal index lies below the array length, and an index read from a frame slot lies
    outside `W3` and `W`. -/
def cidxArmAt (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W3 W : List String) (x : LinstrR) : Bool :=
  match cellIdxStore? slotArr body k x, x with
  | some (_, n, idx, v), .Lopn [.reg c] _ _ =>
      match cellParts? c with
      | some (D, _) =>
          !W.contains c && (frame D).isNone && (frame v).isNone && !W.contains D && !W.contains v
            && (match idx with
              | .inr j => decide (j < n)
              | .inl q => !W3.contains q && !W.contains q)
      | none => false
  | _, _ => false

/-- **The arm of an indexed store through a cell** at the width analysis of the body:
    `cidxArmAt` at `oneBitAt` at `k - 3` and at `k`. -/
def cidxArmB (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  cidxArmAt frame slotArr body k (oneBitAt frame body (k - 3)) (oneBitAt frame body k) x

/-- The conditions of `cidxArmB` at an instruction: it is a store through a cell of the window
    (`cellIdxStore?`), with the conditions of `cidxArmAt` at the analysis of the body. -/
theorem cidxArmB_spec {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {x : LinstrR}
    (h : cidxArmB frame slotArr body k x = true) :
    ∃ A n idx v c D, cellIdxStore? slotArr body k x = some (A, n, idx, v)
      ∧ x = .Lopn [.reg c] "MOV:64" [.reg v] ∧ cellParts? c = some (D, 0)
      ∧ c ∉ oneBitAt frame body k ∧ frame D = none ∧ frame v = none
      ∧ D ∉ oneBitAt frame body k ∧ v ∉ oneBitAt frame body k
      ∧ (∀ j, idx = .inr j → j < n) := by
  unfold cidxArmB cidxArmAt at h
  cases hs : cellIdxStore? slotArr body k x with
  | none => simp [hs] at h
  | some p =>
    obtain ⟨A, n, idx, v⟩ := p
    obtain ⟨c, D, B, X, d1, s, l, r, m, rfl, hc, -⟩ := cellIdxStore?_spec hs
    simp only [hs, hc, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
      List.contains_eq_mem, decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨A, n, idx, v, c, D, rfl, rfl, hc, h1, h2, h3, h4, h5, ?_⟩
    rintro j rfl
    simpa using h6

/-! ## 2. The invariant of the window -/

/-- The address register and the index register of the window of a store at position `k`: the
    destination and the index of the address computation at `k - 2`. -/
def cidxRegs (body : Lcmd) (k : Nat) : Option (String × String) :=
  match body[k - 2]? with
  | some ⟨_, .Lopn [.reg D] _ [.arrIdx _ X _]⟩ => some (D, X)
  | _ => none

/-- The value of the index of a window on an image register file: the value of the frame slot,
    or the word of the literal. -/
def idxSrcVal (r : LstateN) : String ⊕ Nat → Σ w, BitVec w
  | .inl q => r.lvm q
  | .inr j => ⟨64, BitVec.ofNat 64 j⟩

/-- **The invariant of an indexed store through a cell** on the image state `s`, for each
    window at position `k`: after the load of the index register (`cidxStart`) and up to the
    address computation at `k - 2` the index register holds the value of the index; at `k - 1`
    and at `k` the address register holds the address of the word of the index in the array,
    and the index holds that word. -/
structure CidxInv (slotArr : String → Option (String × Nat)) (base : String → BitVec 64)
    (body : Lcmd) (s : LstateMF) : Prop where
  /-- After the load of the index register and up to `k - 2` the index register holds the
      value of the index. -/
  at2 : ∀ k i A n idx v D X, body[k]? = some i →
    cellIdxStore? slotArr body k i.li_i = some (A, n, idx, v) →
    cidxRegs body k = some (D, X) → cidxStart body k < s.prog.base.reg.lpc →
    s.prog.base.reg.lpc + 2 ≤ k →
    s.prog.base.reg.lvm X = idxSrcVal s.prog.base.reg idx
  /-- At `k - 1` and at `k` the address register holds the address of the word of the index. -/
  at1 : ∀ k i A n idx v D X, body[k]? = some i →
    cellIdxStore? slotArr body k i.li_i = some (A, n, idx, v) →
    cidxRegs body k = some (D, X) → (s.prog.base.reg.lpc + 1 = k ∨ s.prog.base.reg.lpc = k) →
    ∃ w : BitVec 64, s.prog.base.reg.lvm D = ⟨64, base A + BitVec.ofNat 64 (8 * w.toNat)⟩
      ∧ idxSrcVal s.prog.base.reg idx = ⟨64, w⟩

/-- The store of a window at `k` covers the position `p`: `p` is `k - 1` or `k`, or lies after
    the load of the index register (`cidxStart`) and at most at the address computation at
    `k - 2`. -/
def cidxCoversB (slotArr : String → Option (String × Nat)) (body : Lcmd) (p k : Nat) : Bool :=
  (body[k]?).any fun i => (cellIdxStore? slotArr body k i.li_i).isSome
    && (p == k || p + 1 == k || (decide (cidxStart body k < p) && decide (p + 2 ≤ k)))

/-- A store of a window covers no position after it. -/
theorem cidxCoversB_of_lt {slotArr : String → Option (String × Nat)} {body : Lcmd} {p k : Nat}
    (h : k < p) : cidxCoversB slotArr body p k = false := by
  unfold cidxCoversB
  cases body[k]? with
  | none => rfl
  | some i =>
    simp only [Option.any_some, Bool.and_eq_false_iff]
    right
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    omega

/-- At a position that no store of a window covers (`cidxCoversB`) the invariant holds. -/
theorem CidxInv.of_outside {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd} {s : LstateMF}
    (h : ∀ k, cidxCoversB slotArr body s.prog.base.reg.lpc k = false) :
    CidxInv slotArr base body s := by
  refine ⟨fun k i A n idx v D X hi hst _ hj hk => ?_, fun k i A n idx v D X hi hst _ hk => ?_⟩
  · have := h k
    simp only [cidxCoversB, hi, hst, Option.any_some, Option.isSome_some, Bool.true_and,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at this
    omega
  · have := h k
    simp only [cidxCoversB, hi, hst, Option.any_some, Option.isSome_some, Bool.true_and,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at this
    omega

/-! ## 3. The steps of the window on the image -/

/-- The window of a store at position `k` read from `cidxRegs`. -/
theorem cidxWindow {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {x : LinstrR} {A v D X : String} {idx : String ⊕ Nat} {n : Nat}
    (h : cellIdxStore? slotArr body k x = some (A, n, idx, v))
    (hr : cidxRegs body k = some (D, X)) :
    ∃ c B d1 src l r m, x = .Lopn [.reg c] "MOV:64" [.reg v] ∧ cellParts? c = some (D, 0)
      ∧ 3 ≤ k ∧ v ≠ D
      ∧ body[k - 2]? = some l ∧ l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8]
      ∧ body[cidxStart body k]? = some r ∧ cellOpMov? r.li_i = some (X, idx)
      ∧ body[k - 1]? = some m ∧ cellOpMov? m.li_i = some (d1, src)
      ∧ d1 ≠ D ∧ cellIdxOkB slotArr D d1 idx = true
      ∧ accArr slotArr body (k - 2) B = some (A, n)
      ∧ cidxStart body k + 3 ≤ k ∧ bitStore? body (cidxStart body k) r.li_i = none
      ∧ ∀ p, cidxStart body k < p → p < k - 2 →
          ∃ x, body[p]? = some x ∧ idxKeepB X idx x.li_i = true := by
  obtain ⟨c, D', B, X', d1, s, l, r, m, hx, hc, h3, hv, hl, hli, hr', hrm, hm, hmm, hd, hok, hac,
    hj3, hbs, hkeep⟩ := cellIdxStore?_spec h
  have e : (D', X') = (D, X) := by
    have : cidxRegs body k = some (D', X') := by
      obtain ⟨ii, li⟩ := l
      simp only at hli
      subst hli
      simp [cidxRegs, hl]
    rw [this] at hr
    exact Option.some.inj hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  exact ⟨c, B, d1, s, l, r, m, hx, hc, h3, hv, hl, hli, hr', hrm, hm, hmm, hd, hok, hac, hj3, hbs,
    hkeep⟩

/-- The instruction of a window with a 64-bit immediate source steps as the write of the word. -/
theorem fstepF_mov64Imm (D : String) (n : Nat) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] "MOV:64" [.imm n], .reg none) m zf
      = some ((m.setReg D (BitVec.ofNat 64 n)).nextPc, zf) := by
  simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, stepMemF, lsemStepMem,
    lsemStepCast, castStruct?, movImmStruct?, withALUFlags, aluFlagOp?,
    JasminLsemMulCarry.lsemStepMC, JasminLsemShift.lsemStepSh, lsemStepN,
    JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
    JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
    JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?, LstateM.setReg, LstateM.nextPc]
  rfl

/-- The address computation of a window on the image: `D` receives the base plus eight times
    the index. -/
theorem fstepF_leaIdx (D B X : String) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] "LEA:64" [.arrIdx B X 8], .reg none) m zf
      = match m.reg.getW B 64, m.reg.getW X 64 with
        | some p, some vi =>
            some ((m.setReg D (p + BitVec.ofNat 64 (8 * vi.toNat))).nextPc, zf)
        | _, _ => none := by
  simp (config := { decide := true }) [fstepF, cmpArgs?, movRegArgs?, carryArgs?, wideArgs?,
    stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?, withALUFlags, aluFlagOp?,
    JasminLsemMulCarry.lsemStepMC, JasminLsemShift.lsemStepSh, lsemStepN,
    JasminLsemMulCarry.mulhiStruct?, JasminLsemMulCarry.adcxStruct?,
    JasminLsemMulCarry.adcxhiStruct?, JasminLsemMulCarry.sbbStruct?,
    JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?, LstateM.setReg, LstateM.nextPc]
  cases m.reg.getW B 64 <;> cases m.reg.getW X 64 <;> rfl

/-- A 64-bit immediate move whose next instruction names the destination other than as a
    carry-in is no stored carry constant. -/
theorem bitStore?_of_lea {body : Lcmd} {k : Nat} {X D B : String} {n : Nat} {l : Linstr}
    (hl : body[k + 1]? = some l) (hli : l.li_i = .Lopn [.reg D] "LEA:64" [.arrIdx B X 8]) :
    bitStore? body k (.Lopn [.reg X] "MOV:64" [.imm n]) = none := by
  cases hb : bitStore? body k (.Lopn [.reg X] "MOV:64" [.imm n]) with
  | none => rfl
  | some p =>
    obtain ⟨d, m⟩ := p
    obtain ⟨hx, -, -, -, hc⟩ := bitStore?_spec hb
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, LOperand.imm.injEq,
      and_true, true_and] at hx
    obtain ⟨rfl, rfl⟩ := hx
    have hlt : k + 1 < body.length := (List.getElem?_eq_some_iff.mp hl).1
    have e : body[k + 1] = l := (List.getElem?_eq_some_iff.mp hl).2
    simp [carryInNext, List.drop_eq_getElem_cons hlt, e, useFirst, hli, carryUseB, namesB,
      opNamesB] at hc

/-- The load of an operand of a window is a move between names or a 64-bit immediate move. -/
theorem cellOpMov?_cases {x : LinstrR} {d : String} {o : String ⊕ Nat}
    (h : cellOpMov? x = some (d, o)) :
    (∃ q, slotMov? x = some (d, q) ∧ o = .inl q)
      ∨ ∃ n, x = .Lopn [.reg d] "MOV:64" [.imm n] ∧ o = .inr n := by
  unfold cellOpMov? at h
  cases hsm : slotMov? x with
  | some p =>
    obtain ⟨d', q⟩ := p
    simp only [hsm, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨q, rfl, rfl⟩
  | none =>
    simp only [hsm] at h
    split at h
    · rename_i d' m n
      split_ifs at h with hm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hm
      exact Or.inr ⟨n, rfl, rfl⟩
    · cases h

/-- A cell store is no load of an operand of a window. -/
theorem cellOpMov?_store {c v : String} {p : String × Nat} (hc : cellParts? c = some p) :
    cellOpMov? (.Lopn [.reg c] "MOV:64" [.reg v]) = none := by
  simp [cellOpMov?, slotMov?, hc]

/-- The image of a load of a window writes only its destination. -/
theorem img_cellOpMov_keep (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (P : LprogM) {x : LinstrR} {d : String} {o : String ⊕ Nat} (hm : cellOpMov? x = some (d, o))
    {s t : LstateMF} (hs : evalInstrPMemFk true P (imgInstr slotArr body k x) s = some t)
    {r : String} (hr : r ≠ d) : t.prog.base.reg.lvm r = s.prog.base.reg.lvm r := by
  rcases cellOpMov?_cases hm with ⟨q, hsm, -⟩ | ⟨n, rfl, -⟩
  · rcases imgInstr_slotMov_cases slotArr body k hsm with hi | hi
    · rw [hi, normA_of_slotMov hsm, evalInstrPMemFk_reg, eval_slotMov P hsm] at hs
      cases hs
      simp [LstateM.setReg, LstateM.nextPc, hr]
    · rw [hi, eval_cast64] at hs
      cases hs
      simp [LstateM.setReg, LstateM.nextPc, hr]
  · cases hbs : bitStore? body k (.Lopn [.reg d] "MOV:64" [.imm n]) with
    | none =>
      rw [imgInstr_reg_of_caret_free slotArr body k (by decide) (by decide) (by decide)
        (bitMovB_of_ne (by simp [movImmStruct?, isMovImmMnem_mov64])) hbs
        (cellIdxStore?_of_ne slotArr (by simp))
        (baseReload?_of_ne slotArr body k (by simp))] at hs
      have hnA : normA (.Lopn [.reg d] "MOV:64" [.imm n])
          = .Lopn [.reg d] "MOV:64" [.imm n] := by
        simp (config := { decide := true }) [normA]
      rw [hnA, evalInstrPMemFk_reg, evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩,
        fstepF_mov64Imm] at hs
      cases hs
      simp [LstateM.setReg, LstateM.nextPc, hr]
    | some p =>
      obtain ⟨d2, n2⟩ := p
      rw [imgInstr_bitStore slotArr hbs] at hs
      obtain ⟨hx, -⟩ := bitStore?_spec hbs
      simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, LOperand.imm.injEq,
        and_true, true_and] at hx
      obtain ⟨rfl, rfl⟩ := hx
      have hs' := evalInstrPMemF_of_k hs
      rw [evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩, fstepF_bitMov] at hs'
      cases hs'
      simp [LstateM.setReg, LstateM.nextPc, hr]

/-- The load of the index register of a window, which is no stored carry constant, writes the
    value of the index to the register. A frame-slot index holds no array pointer, so that the
    load is no reload of a base. -/
theorem img_cellOpMov_idx {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    (P : LprogM) {x : LinstrR} {X : String} {idx : String ⊕ Nat}
    (hm : cellOpMov? x = some (X, idx)) (hok : ∀ q, idx = .inl q → slotArr q = none)
    (hbs : bitStore? body k x = none)
    {s t : LstateMF} (hs : evalInstrPMemFk true P (imgInstr slotArr body k x) s = some t) :
    t.prog.base.reg.lvm X = idxSrcVal t.prog.base.reg idx := by
  rcases cellOpMov?_cases hm with ⟨q, hsm, rfl⟩ | ⟨n, rfl, rfl⟩
  · have hq := hok q rfl
    have hr : baseReload? slotArr body k x = none := by
      rcases slotMov?_cases hsm with rfl | rfl <;> exact baseReload?_of_slot_none _ _ _ hq
    have hi : imgInstr slotArr body k x = (normA x, .reg none) := by
      rcases slotMov?_cases hsm with rfl | rfl <;>
        exact imgInstr_reg_of_caret_free slotArr body k (by decide) (by decide) (by decide)
          (bitMovB_of_slotMov hsm) hbs (cellIdxStore?_of_slotMov hsm) hr
    rw [hi, normA_of_slotMov hsm, evalInstrPMemFk_reg, eval_slotMov P hsm] at hs
    cases hs
    by_cases e : q = X
    · subst e
      simp [idxSrcVal]
    · simp [idxSrcVal, LstateM.setReg, LstateM.nextPc, e]
  · rw [imgInstr_reg_of_caret_free slotArr body k (by decide) (by decide) (by decide)
      (bitMovB_of_ne (by simp [movImmStruct?, isMovImmMnem_mov64])) hbs
        (cellIdxStore?_of_ne slotArr (by simp))
      (baseReload?_of_ne slotArr body k (by simp))] at hs
    have hnA : normA (.Lopn [.reg X] "MOV:64" [.imm n])
        = .Lopn [.reg X] "MOV:64" [.imm n] := by
      simp (config := { decide := true }) [normA]
    rw [hnA, evalInstrPMemFk_reg, evalInstrPMemF_isLopn P _ s ⟨_, _, _, rfl⟩,
      fstepF_mov64Imm] at hs
    cases hs
    simp [idxSrcVal, LstateM.setReg, LstateM.nextPc]

/-- A step of the image of an indexed store through a cell keeps every word of the register
    file: it writes the array. -/
theorem cellStoreImg_lvm (P : LprogM) {A v : String} {idx : String ⊕ Nat} {n : Nat}
    {s t : LstateMF} (hs' : evalInstrPMemF P (cellStoreImg A n idx v) s = some t) :
    t.prog.base.reg.lvm = s.prog.base.reg.lvm := by
  cases idx with
  | inl q =>
    simp only [cellStoreImg] at hs'
    rw [eval_storeIdx] at hs'
    split at hs'
    · cases hs'
      rfl
    · cases hs'
  | inr j =>
    simp only [cellStoreImg] at hs'
    rw [eval_storeImm] at hs'
    split at hs'
    · cases hs'
      rfl
    · cases hs'

/-- A step of an image by `arrImmImg` keeps every word of the register file. -/
theorem arrImmImg_lvm {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    (P : LprogM) {x : LinstrR} {i : LinstrRM} (hi : arrImmImg slotArr body k x = some i)
    {s t : LstateMF} (hs : evalInstrPMemF P i s = some t) :
    t.prog.base.reg.lvm = s.prog.base.reg.lvm := by
  unfold arrImmImg at hi
  repeat' split at hi
  all_goals first
    | (cases hi; done)
    | (cases hi; rw [eval_zeroArr] at hs; cases hs; rfl)
    | (cases hi; rw [eval_storeImm] at hs; split at hs; (cases hs; rfl); cases hs)

/-- An instruction that keeps a name (`keepsB`) is an `Lopn`. -/
theorem lopn_of_keepsB {x : LinstrR} {r : String} (h : keepsB r x = true) :
    ∃ ds op ss, x = .Lopn ds op ss := by
  cases x <;> simp_all [keepsB]

/-- **The image of an instruction that keeps `r` keeps the word of `r`.** An `Lopn` none of
    whose destination operands names `r` (`keepsB`) has an image that writes `r` nowhere: the
    image keeps the destinations of the instruction, or writes an array. -/
theorem img_keep (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (P : LprogM) {x : LinstrR} {r : String} (hk : keepsB r x = true) {s t : LstateMF}
    (hs : evalInstrPMemFk true P (imgInstr slotArr body k x) s = some t) :
    t.prog.base.reg.lvm r = s.prog.base.reg.lvm r := by
  have hs' := evalInstrPMemF_of_k hs
  have hnd : r ∉ dstNames x := by
    obtain ⟨ds, o, ss, rfl⟩ := lopn_of_keepsB hk
    simp only [keepsB, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hk
    simp only [dstNames, List.mem_flatMap, not_exists, not_and]
    intro op hop hr
    have := hk op hop
    cases op <;> simp_all [opNames, opNamesB, @eq_comm _ r]
  have hL : ∀ y : LinstrR, keepsB r y = true → ∀ tg, IsLopn (normA y, tg) := by
    intro y hy tg
    obtain ⟨ds, o, ss, rfl⟩ := lopn_of_keepsB hy
    exact ⟨_, _, _, rfl⟩
  have gen : ∀ i : LinstrRM, IsLopn i → dstNames i.1 = dstNames x →
      evalInstrPMemF P i s = some t → t.prog.base.reg.lvm r = s.prog.base.reg.lvm r :=
    fun i hi he h => evalInstrPMemF_lvm_of_not_dst P hi h (he ▸ hnd)
  unfold imgInstr at hs'
  split at hs'
  · split_ifs at hs'
    · split at hs'
      · exact gen _ ⟨_, _, _, rfl⟩ rfl hs'
      · exact gen _ (hL _ hk _) (by simp only [dstNames_normA]) hs'
    · exact gen _ (hL _ hk _) (by simp only [dstNames_normA]) hs'
  · split_ifs at hs'
    · split at hs'
      · rw [eval_storeIdx] at hs'
        split at hs'
        · cases hs'
          rfl
        · cases hs'
      · exact gen _ (hL _ hk _) (by simp only [dstNames_normA]) hs'
    · exact gen _ (hL _ hk _) (by simp only [dstNames_normA]) hs'
  · split at hs'
    · rename_i d n hb
      obtain ⟨he, -⟩ := bitStore?_spec hb
      exact gen _ ⟨_, _, _, rfl⟩ (by rw [he]; rfl) hs'
    · split at hs'
      · exact congrFun (cellStoreImg_lvm P hs') r
      · split at hs'
        · rename_i ri hri
          exact congrFun (arrImmImg_lvm P hri hs') r
        · split at hs'
          · rename_i b q hbr
            obtain ⟨he, -⟩ := baseReload?_spec hbr
            exact gen _ ⟨_, _, _, rfl⟩ (by rcases he with he | he <;> rw [he] <;> rfl) hs'
          · exact gen _ (hL _ hk _) (by simp only [dstNames_normA]) hs'

/-! ## 4. The program counter and the invariant across a step -/

/-- **The program counter after a step of the image** at a gated position: the next
    instruction, or one past a label. -/
theorem imgStep_pc {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {E : Nat → Prop}
    (hgate : ImgGateW frame slotArr c E) (fn : String) {s t : LstateMF} {k : Nat} {bi : Linstr}
    (hb : c[k]? = some bi) (hlt : k < c.length - 1) (hX : ¬ E k)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c k bi.li_i) s = some t) :
    t.prog.base.reg.lpc = s.prog.base.reg.lpc + 1
      ∨ ∃ p bp ii l, c[p]? = some bp ∧ bp.li_i = .Llabel ii l
          ∧ t.prog.base.reg.lpc = p + 1 := by
  have hg : instrGateBW frame slotArr c k bi.li_i = true := hgate.instr _ _ hb (by omega) hX
  cases hx : bi.li_i with
  | Lopn ds o ss =>
    left
    rw [hx] at hstep
    obtain ⟨ds', o', ss', hi⟩ :
        ∃ ds' o' ss', (imgInstr slotArr c k (.Lopn ds o ss)).1 = .Lopn ds' o' ss' := by
      unfold imgInstr
      repeat' split
      all_goals first
        | exact ⟨_, _, _, rfl⟩
        | exact cellStoreImg_lopn _ _ _ _
        | (apply arrImmImg_lopn; assumption)
    have hs := evalInstrPMemF_of_k hstep
    rw [evalInstrPMemF_isLopn _ _ s ⟨_, _, _, hi⟩] at hs
    obtain ⟨⟨b, z⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hs
    exact fstepF_lpc_succ _ _ _ _ _ hf
  | Llabel ii l =>
    left
    have hi : imgInstr slotArr c k (.Llabel ii l) = (.Llabel ii l, .reg none) := rfl
    rw [hx, hi, evalInstrPMemFk_reg, eval_label] at hstep
    cases hstep
    simp [LstateM.nextPc]
  | Lcond cnd l =>
    obtain ⟨cc, pol, p, rfl, hpol, hp, -⟩ := gateAtW_cond hx hg
    obtain ⟨r, hr, hret⟩ := hgate.last
    have hfl := findLabel_virtImg slotArr c l (fun r' hr' => by
      rw [hr] at hr'
      cases hr'
      rw [hret]; rfl)
    rw [hp] at hfl
    have hi : imgInstr slotArr c k (.Lcond (.reg cc) l) = (.Lcond (.reg cc) l, .reg none) := rfl
    rw [hx, hi, evalInstrPMemFk_reg, eval_cond fn _ cc l _ hpol hfl] at hstep
    split_ifs at hstep
    · right
      cases hstep
      obtain ⟨hpl, hlab, -⟩ := labelAt_spec hp
      have hlabp : ∃ ii', c[p].li_i = .Llabel ii' l := by
        revert hlab
        cases c[p].li_i <;> simp [isLabelB]
      obtain ⟨ii', hli⟩ := hlabp
      exact ⟨p, c[p], ii', l, List.getElem?_eq_getElem hpl, hli, by simp [LstateM.setLpc]⟩
    · left
      cases hstep
      simp [LstateM.nextPc]
  | _ =>
    rw [hx] at hg
    simp [instrGateBW, gateAtW, carryI?, icase, castGateB, DecodePrintedAddrW.classifyK] at hg

/-- The gate of an address computation of a window: its base has no frame word. -/
theorem frame_base_of_lea {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd} {k : Nat} {D B X : String}
    (hg : instrGateBW frame slotArr c k (.Lopn [.reg D] "LEA:64" [.arrIdx B X 8]) = true) :
    frame B = none := by
  simp (config := { decide := true }) [instrGateBW, gateAtW, carryI?, icase, width_tag,
    movImmStruct?, bitStore?, sImmB, sCmovB, regGateBW, regOkB, normA, symStep,
    cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?, wideArgs?, symMem, symCast, castStruct?, symMC,
    symSh, symN, liftR, aluFl, aluFlT, aluFlagOp?, JasminLsemMulCarry.mulhiStruct?,
    JasminLsemMulCarry.adcxStruct?, JasminLsemMulCarry.adcxhiStruct?,
    JasminLsemMulCarry.sbbStruct?, JasminLsemMulCarry.sbbhiStruct?, JasminLsemShift.sarStruct?,
    descReads, SSt.setR, SSt.start, SG.vars, STerm.vars] at hg
  tauto

/-- `idxSrcVal` depends on a frame-slot index only through its value. -/
theorem idxSrcVal_of_keep {r r' : LstateN} {idx : String ⊕ Nat}
    (h : ∀ q, idx = .inl q → r'.lvm q = r.lvm q) : idxSrcVal r' idx = idxSrcVal r idx := by
  cases idx with
  | inl q => exact h q rfl
  | inr j => rfl

/-- The conditions of `cellIdxOkB` at a frame-slot index. -/
theorem cellIdxOkB_inl {slotArr : String → Option (String × Nat)} {D d1 q : String}
    (h : cellIdxOkB slotArr D d1 (.inl q) = true) : d1 ≠ q ∧ D ≠ q ∧ slotArr q = none := by
  simp only [cellIdxOkB, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2⟩

/-- **A step of the image keeps the invariant of the window.** From states related by `ImgRelW`
    at a position outside the exempt set of the gate, the load of the index register
    establishes the value of the index register, the address computation establishes the
    address, with the base read through `ImgGateW.ptr_of_reloadW`, and the load of the value
    writes neither the address register nor the index; an instruction between the load of the
    index register and the address computation keeps the index register and the index
    (`img_keep`). No other instruction reaches a position of a window, since the instructions
    from the load of the index register up to the store are neither a label nor a branch. -/
theorem cidxInv_step {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} {E : Nat → Prop} (hsep : ImgSep frame slotArr base rsp)
    (hgate : ImgGateW frame slotArr c E) (fn : String) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base c s sa zf) (hinv : CidxInv slotArr base c s) {bi : Linstr}
    (hb : c[sa.reg.lpc]? = some bi) (hlt : sa.reg.lpc < c.length - 1) (hX : ¬ E sa.reg.lpc)
    (hstep : evalInstrPMemFk true (singletonProgM fn (virtImg slotArr c))
      (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    CidxInv slotArr base c t := by
  have hp := imgStep_pc hgate fn hb hlt hX hstep
  rw [← hrel.pc] at hp
  refine ⟨fun k i A n idx v D X hi hst hreg hj hk => ?_,
    fun k i A n idx v D X hi hst hreg hk => ?_⟩
  · obtain ⟨-, B, d1, src, l, r, m, -, -, h3, -, hl, hli, hr, hrm, -, -, -, hok, -, hj3, hbs,
      hkeep⟩ := cidxWindow hst hreg
    rcases hp with hp | ⟨p, bp, ii, lb, hbp, hlb, hp⟩
    · rw [hp] at hj hk
      by_cases e : sa.reg.lpc = cidxStart c k
      · have hrb : r = bi := by
          rw [e, hr] at hb
          exact Option.some.inj hb
        subst hrb
        refine img_cellOpMov_idx _ hrm (fun q hq => ?_) (by rw [e]; exact hbs) hstep
        subst hq
        exact (cellIdxOkB_inl hok).2.2
      · obtain ⟨x, hx, hkx⟩ := hkeep sa.reg.lpc (by omega) (by omega)
        rw [hb] at hx
        obtain rfl := Option.some.inj hx
        have h0 := hinv.at2 k i A n idx v D X hi hst hreg (by rw [← hrel.pc]; omega)
          (by rw [← hrel.pc]; omega)
        simp only [idxKeepB, Bool.and_eq_true] at hkx
        rw [img_keep slotArr c _ _ hkx.1 hstep, idxSrcVal_of_keep (r := s.prog.base.reg)
          fun q hq => by
            subst hq
            exact img_keep slotArr c _ _ (by simpa using hkx.2) hstep]
        exact h0
    · rw [hp] at hj hk
      by_cases e : p = cidxStart c k
      · rw [e, hr] at hbp
        obtain rfl := Option.some.inj hbp
        rw [hlb] at hrm
        simp [cellOpMov?, slotMov?] at hrm
      · obtain ⟨x, hx, hkx⟩ := hkeep p (by omega) (by omega)
        rw [hbp] at hx
        obtain rfl := Option.some.inj hx
        rw [hlb] at hkx
        simp [idxKeepB, keepsB] at hkx
  · obtain ⟨-, B, d1, src, l, r, m, -, -, h3, -, hl, hli, -, -, hm, hmm, hd, hok, hac, hj3, -,
      -⟩ := cidxWindow hst hreg
    rcases hp with hp | ⟨p, bp, ii, lb, hbp, hlb, hp⟩
    · rcases hk with hk | hk
      · have e : sa.reg.lpc = k - 2 := by omega
        have hlb : l = bi := by
          rw [e, hl] at hb
          exact Option.some.inj hb
        subst hlb
        have hfB : frame B = none := frame_base_of_lea (hli ▸ hgate.instr _ _ hb (by omega) hX)
        have hi0 : imgInstr slotArr c sa.reg.lpc (.Lopn [.reg D] "LEA:64" [.arrIdx B X 8])
            = (.Lopn [.reg D] "LEA:64" [.arrIdx B X 8], .reg none) := by
          simp [imgInstr, normA, width_tag]
        rw [hli, hi0, evalInstrPMemFk_reg, evalInstrPMemF_isLopn _ _ s ⟨_, _, _, rfl⟩,
          fstepF_leaIdx] at hstep
        have hx2 := hinv.at2 k i A n idx v D X hi hst hreg (by rw [← hrel.pc]; omega)
          (by rw [← hrel.pc]; omega)
        obtain ⟨q', -, hq2⟩ := ImgGateW.ptr_of_reloadW hsep hgate hrel (by rw [e]; exact hac) hfB
        cases hP : s.prog.base.reg.getW B 64 with
        | none => simp [hP] at hstep
        | some p =>
          cases hV : s.prog.base.reg.getW X 64 with
          | none => simp [hP, hV] at hstep
          | some vi =>
            simp only [hP, hV, Option.map_some, Option.some.injEq] at hstep
            have hpb : p = base A := by
              have := (hrel.regs B hfB).getW64 hP
              rw [hq2] at this
              exact (Option.some.inj this).symm
            subst hpb
            obtain rfl := hstep
            refine ⟨vi, by simp [LstateM.setReg, LstateM.nextPc], ?_⟩
            rw [idxSrcVal_of_keep (r := s.prog.base.reg) fun q hq => by
              subst hq
              have := (cellIdxOkB_inl hok).2.1
              simp [LstateM.setReg, LstateM.nextPc, Ne.symm this], ← hx2]
            exact getW_eq_some_iff.1 hV
      · have e : sa.reg.lpc = k - 1 := by omega
        have hmb : m = bi := by
          rw [e, hm] at hb
          exact Option.some.inj hb
        subst hmb
        obtain ⟨w, h1, h2⟩ := hinv.at1 k i A n idx v D X hi hst hreg
          (Or.inl (by rw [← hrel.pc]; omega))
        refine ⟨w, ?_, ?_⟩
        · rw [img_cellOpMov_keep slotArr c _ _ hmm hstep (Ne.symm hd)]
          exact h1
        · rw [idxSrcVal_of_keep (r := s.prog.base.reg) fun q hq => by
            subst hq
            exact img_cellOpMov_keep slotArr c _ _ hmm hstep (Ne.symm (cellIdxOkB_inl hok).1)]
          exact h2
    · rcases hk with hk | hk
      · have e : p = k - 2 := by omega
        rw [e, hl] at hbp
        obtain rfl := Option.some.inj hbp
        rw [hli] at hlb
        cases hlb
      · have e : p = k - 1 := by omega
        rw [e, hm] at hbp
        obtain rfl := Option.some.inj hbp
        rw [hlb] at hmm
        simp [cellOpMov?, slotMov?] at hmm

/-! ## 5. The store -/

/-- Past a cell store, every name of the width analysis other than the cell stays in it. -/
theorem mem_oneBitAt_succ_cellStore {frame : String → Option (BitVec 64)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) {c v : String} {p : String × Nat}
    (hx : bi.li_i = .Lopn [.reg c] "MOV:64" [.reg v]) (hcp : cellParts? c = some p)
    (hcW : c ∉ oneBitAt frame body k) {r : String} (hr : r ∈ oneBitAt frame body k) :
    r ∈ oneBitAt frame body (k + 1) := by
  have hrc : r ≠ c := fun e => hcW (e ▸ hr)
  rw [oneBitAt_succ hb (bitStore?_of_eq hx (by simp)) (seedAt_of_eq hx (by simp)),
    oneBitStep_noCarry (by rw [hx]; rfl), hx]
  simp (config := { decide := true }) [icase, slotMov?, slotCmp?, hcp, normA, width_tag,
    movImmStruct?, regOut, symStep, cmpArgs?, movRegArgs?, SSt.setR, SSt.start, hr, hrc]

/-- **The write of a word of an array keeps `ImgRelW`.** A cell store on the address machine that
    writes the word of index `i < n` of the array `A` at the address of that word, matched by the
    store of the same word on the image, keeps the relation: the frame words and the other cells
    are disjoint from the written word (`ImgSep`). -/
theorem rel_cellWriteW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {c v : String} {p : String × Nat}
    (hx : bi.li_i = .Lopn [.reg c] "MOV:64" [.reg v]) (hcp : cellParts? c = some p)
    (hcW : c ∉ oneBitAt frame body sa.reg.lpc) {q A : String} {n : Nat}
    (hq : slotArr q = some (A, n)) {arr : Fin n → BitVec 64}
    (hcell : ∀ j (hj : j < n), read64 sa.mem (cellAt (base A) j) = arr ⟨j, hj⟩)
    {i : Nat} (hi : i < n) (vv : BitVec 64) :
    ImgRelW frame slotArr base body
      { s with prog := { s.prog with
          base := (s.prog.base.setArr A (stackSet arr i vv)).nextPc } }
      { sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * i)) vv } s.zf := by
  have hz := hrel.zf
  subst hz
  have hnm : slotMov? bi.li_i = none := by rw [hx]; simp [slotMov?, hcp]
  have hsub : ∀ r, r ∈ oneBitAt frame body sa.reg.lpc → r ∈ oneBitAt frame body (sa.reg.lpc + 1) :=
    fun r hr => mem_oneBitAt_succ_cellStore hb hx hcp hcW hr
  have hmem : ∀ q' a, frame q' = some a → faB q' = false →
      read64 (write64 sa.mem (base A + BitVec.ofNat 64 (8 * i)) vv) a = read64 sa.mem a :=
    fun q' a ha hf => read64_write64_of_disjoint _ _ _ _ (hsep.cellFrame q A n i hq hi q' a ha hf)
  obtain ⟨hsv, hrl, hhd⟩ := saved_reload_nextW (sa' := { sa with
      reg := sa.reg.nextPc
      mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * i)) vv })
    hphys hrel hb hnm rfl (fun q' a _ ha hf => hmem q' a ha hf) (fun _ _ _ => rfl)
  refine ⟨by simp [LstateM.setArr, LstateM.nextPc, hrel.pc],
    fun r hr => (hrel.regs r hr).of_eq (by simp [LstateM.setArr, LstateM.nextPc]) (by simp)
      (fun h => by simpa using hsub r h), ?_, rfl,
    hrel.cf, hrel.of, fun r hr hW => ?_, ?_, hsv, hrl, hhd,
    fun r hr hc => by simpa using hrel.bits r hr hc⟩
  · intro q' a ha
    simp only [LstateM.setArr, LstateM.nextPc, LstateN.lvm_nextPc]
    rw [frameVal_congr (hmem q' a ha)]
    exact (hrel.slots q' a ha).of_eq rfl rfl fun h => by simpa using hsub q' h
  · simp only [LstateN.lpc_nextPc] at hW
    simpa using hrel.wid r hr (fun h => hW (hsub r h))
  · intro q' A' n' hq'
    obtain ⟨arr', harr', hcell'⟩ := hrel.cells q' A' n' hq'
    by_cases eA : A' = A
    · subst eA
      have hn := hsep.len q' q A' n' n hq' hq
      subst hn
      refine ⟨stackSet arr i vv, by simp, fun j hj => ?_⟩
      rw [← stackGet_id (stackSet arr i vv) ⟨j, hj⟩]
      by_cases ej : j = i
      · subst ej
        rw [read64_write64_same, stackGet_stackSet_same _ _ _ hi]
      · rw [read64_write64_of_disjoint _ _ _ _
          (hsep.cells q A' n' q A' n' i j hq hq hi hj (Or.inr (Ne.symm ej))),
          stackGet_stackSet_ne _ _ _ _ hi hj ej, hcell j hj, stackGet_id arr ⟨j, hj⟩]
    · refine ⟨arr', by simpa [eA] using harr', fun j hj => ?_⟩
      rw [read64_write64_of_disjoint _ _ _ _
        (hsep.cells q A n q' A' n' i j hq hq' hi hj (Or.inl (Ne.symm eA)))]
      exact hcell' j hj

/-- **An indexed store through a cell keeps `ImgRelW`.** At the store of a window, with the
    invariant at the position, the image stores into the array at the index and the address
    machine writes the same word through the address register. -/
theorem rel_cidxStoreW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp)
    (hphys : physImgB slotArr body = true) (P : LprogM) {s t : LstateMF}
    {sa : LstateA} {zf : Bool} (hrel : ImgRelW frame slotArr base body s sa zf)
    (hinv : CidxInv slotArr base body s) {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    (harm : cidxArmB frame slotArr body sa.reg.lpc bi.li_i = true) {A v : String}
    {idx : String ⊕ Nat} {n : Nat}
    (hst : cellIdxStore? slotArr body sa.reg.lpc bi.li_i = some (A, n, idx, v))
    (hs : evalInstrPMemFk true P (cellStoreImg A n idx v) s = some t) :
    ∃ sa', stepA frame body sa zf = some (sa', t.zf)
      ∧ ImgRelW frame slotArr base body t sa' t.zf := by
  have hz := hrel.zf
  subst hz
  obtain ⟨A', n', idx', v', c, D, hst', hx, hcp, hcW, hfD, hfv, hDW, hvW, hj⟩ :=
    cidxArmB_spec harm
  rw [hst] at hst'
  simp only [Option.some.injEq, Prod.mk.injEq] at hst'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst'
  obtain ⟨c0, D0, B, X, d1, src, l, r, m, hx0, hc0, -, -, hl, hli, -, -, -, -, -, -, hac, -⟩ :=
    cellIdxStore?_spec hst
  have hc0e : c0 = c := by
    rw [hx] at hx0
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at hx0
    exact hx0.symm
  subst hc0e
  have hD0 : D0 = D := by
    rw [hc0] at hcp
    exact (Prod.mk.inj (Option.some.inj hcp)).1
  subst hD0
  have hreg : cidxRegs body sa.reg.lpc = some (D0, X) := by
    obtain ⟨ii, li⟩ := l
    simp only at hli
    subst hli
    simp [cidxRegs, hl]
  obtain ⟨w, hDv, hidxv⟩ := hinv.at1 _ bi A n idx v D0 X hb hst hreg (Or.inr hrel.pc.symm)
  have hDs : sa.reg.getW D0 64 = some (base A + BitVec.ofNat 64 (8 * w.toNat)) := by
    rw [getW_eq_some_iff, ← hrel.regsEq hfD hDW, hDv]
  obtain ⟨q, -, hq, -⟩ := accArr_spec hac
  obtain ⟨arr, harr, hcell⟩ := hrel.cells q A n hq
  have hve := getW_congr (r := s.prog.base.reg) (r' := sa.reg) (hrel.regsEq hfv hvW) 64
  have hs' := evalInstrPMemF_of_k hs
  have hn : normA bi.li_i = .Lopn [.reg c0] "MOV:64" [.reg v] := by
    rw [hx]; simp (config := { decide := true }) [normA]
  have ht : tagAt body sa.reg.lpc bi.li_i = .reg none := by
    rw [hx, tagAt_of_ne (by simp [movImmStruct?])]
    simp (config := { decide := true }) [tagA]
  have hstepA : ∀ vv, sa.reg.getW v 64 = some vv →
      stepA frame body sa s.zf = some ({ sa with
        reg := sa.reg.nextPc
        mem := write64 sa.mem (base A + BitVec.ofNat 64 (8 * w.toNat)) vv }, s.zf) := by
    intro vv hvv
    rw [stepA_lopn frame hb hx, hn, ht, fstepA_mov64_store frame hcp,
      fstepA_stm frame hc0 hDs hvv]
    simp
  cases idx with
  | inl q' =>
    have hq' : s.prog.base.reg.getW q' 64 = some w := getW_eq_some_iff.2 hidxv
    simp only [cellStoreImg] at hs hs'
    have hok := idxOkB_of_checked hs
    have hlt : w.toNat < n := by
      simp only [idxOkB, storeStruct?, ite_true, idxBelowB, hq'] at hok
      simpa using hok
    rw [eval_storeIdx, harr, hq', hve] at hs'
    cases hvv : sa.reg.getW v 64 with
    | none => simp [hvv] at hs'
    | some vv =>
      simp only [hvv, Option.some.injEq] at hs'
      subst hs'
      exact ⟨_, hstepA vv hvv, rel_cellWriteW hsep hphys hrel hb hx hcp hcW hq hcell hlt vv⟩
  | inr j =>
    have hw : w = BitVec.ofNat 64 j := by simpa [idxSrcVal] using hidxv.symm
    subst hw
    have hadr : BitVec.ofNat 64 (8 * (BitVec.ofNat 64 j).toNat) = BitVec.ofNat 64 (8 * j) := by
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mul_mod]
    rw [hadr] at hstepA
    simp only [cellStoreImg] at hs'
    rw [eval_storeImm, harr, hve] at hs'
    cases hvv : sa.reg.getW v 64 with
    | none => simp [hvv] at hs'
    | some vv =>
      simp only [hvv, Option.some.injEq] at hs'
      subst hs'
      exact ⟨_, hstepA vv hvv, rel_cellWriteW hsep hphys hrel hb hx hcp hcW hq hcell (hj j rfl) vv⟩

/-- After the store of a window the invariant holds: the store stands at no position of a
    window before its own address computation other than between the load of an index register
    and its address computation, where it keeps every register (`cellStoreImg_lvm`). -/
theorem cidxInv_store {slotArr : String → Option (String × Nat)} {base : String → BitVec 64}
    {body : Lcmd} (P : LprogM) {s t : LstateMF} {pc : Nat} {bi : Linstr}
    (hb : body[pc]? = some bi) (hpc : s.prog.base.reg.lpc = pc) {A v : String}
    {idx : String ⊕ Nat} {n : Nat}
    (hst : cellIdxStore? slotArr body pc bi.li_i = some (A, n, idx, v))
    (hs : evalInstrPMemFk true P (cellStoreImg A n idx v) s = some t)
    (hinv : CidxInv slotArr base body s) :
    CidxInv slotArr base body t := by
  obtain ⟨c0, D0, -, -, -, -, -, -, -, hx0, hc0, -⟩ := cellIdxStore?_spec hst
  obtain ⟨ds, o, ss, hl0⟩ := cellStoreImg_lopn A n idx v
  have hs' := evalInstrPMemF_of_k hs
  have hlvm := cellStoreImg_lvm P hs'
  rw [evalInstrPMemF_isLopn P _ s ⟨_, _, _, hl0⟩] at hs'
  obtain ⟨⟨b, z⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hs'
  have hpc' : b.reg.lpc = pc + 1 := by
    rw [← hpc]
    exact fstepF_lpc_succ _ _ _ _ _ hf
  refine ⟨fun k i A' n' idx' v' D X hi hst' hreg hj hk => ?_,
    fun k i A' n' idx' v' D X hi hst' hreg hk => ?_⟩
  · obtain ⟨-, B, d1, src, l, r, m, -, -, h3, -, -, -, hr, hrm, -, -, -, -, -, -, -, hkeep⟩ :=
      cidxWindow hst' hreg
    simp only at hj hk hlvm ⊢
    by_cases e : pc = cidxStart body k
    · rw [← e, hb] at hr
      obtain rfl := Option.some.inj hr
      rw [hx0, cellOpMov?_store hc0] at hrm
      cases hrm
    · have h0 := hinv.at2 k i A' n' idx' v' D X hi hst' hreg (by omega) (by omega)
      rw [hlvm, idxSrcVal_of_keep (r := s.prog.base.reg) fun q _ => by rw [hlvm]]
      exact h0
  · obtain ⟨-, B, d1, src, l, r, m, -, -, h3, -, hl, hli, -, -, hm, hmm, -⟩ := cidxWindow hst' hreg
    simp only at hk
    rcases hk with hk | hk
    · have e : pc = k - 2 := by omega
      rw [← e, hb] at hl
      obtain rfl := Option.some.inj hl
      rw [hx0] at hli
      simp at hli
    · have e : pc = k - 1 := by omega
      rw [← e, hb] at hm
      obtain rfl := Option.some.inj hm
      rw [hx0, cellOpMov?_store hc0] at hmm
      cases hmm

/-- **One step of the image at an indexed store through a cell.** From states related by
    `ImgRelW` with the invariant of the window, a checked step of the image at a store passing
    `cidxArmB` is matched by one step of the address machine, which does not halt and reads
    outside the red-zone word, and the result is related by `ImgRelW` with the invariant. -/
theorem img_stepCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr c = true)
    (P : LprogM) {s t : LstateMF} {sa : LstateA}
    (hrel : ImgRelW frame slotArr base c s sa s.zf) (hinv : CidxInv slotArr base c s)
    {bi : Linstr} (hb : c[sa.reg.lpc]? = some bi)
    (harm : cidxArmB frame slotArr c sa.reg.lpc bi.li_i = true)
    (hstep : evalInstrPMemFk true P (imgInstr slotArr c sa.reg.lpc bi.li_i) s = some t) :
    StepOut frame rsp c
      (fun t' sa' z => ImgRelW frame slotArr base c t' sa' z ∧ CidxInv slotArr base c t')
      s.zf sa t := by
  obtain ⟨A, n, idx, v, c0, D, hst, hx, hcp, -⟩ := cidxArmB_spec harm
  rw [imgInstr_cellIdxStore slotArr hst] at hstep
  obtain ⟨sa1, h1, h2⟩ := rel_cidxStoreW hsep hphys P hrel hinv hb harm hst hstep
  exact ⟨haltedA_of hb (by rw [hx]; simp), loadSafe_of hb (by rw [hx]; simp [normA]), sa1, h1,
    Or.inl ⟨h2, cidxInv_store P hb hrel.pc.symm hst hstep hinv⟩⟩

/-! ## 6. The gate with indexed stores through a cell -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (isRetB)

/-- The stored name of an `Lopn` with one register source is no cell name. -/
def srcNoCellB : LinstrR → Bool
  | .Lopn _ _ [.reg v] => (cellParts? v).isNone
  | _ => false

/-- The arm of an indexed store through a cell in the gate: `cidxArmB`, with a stored name that
    is no cell name (`srcNoCellB`), so that the store reads no base besides its address
    register. -/
def cidxArmCW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  cidxArmB frame slotArr body k x && srcNoCellB x

/-- **The gate of an instruction with indexed stores through a cell**: the arm `cidxArmCW` of
    such a store, or the gate `instrGateBW`. -/
def gateCW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (x : LinstrR) : Bool :=
  cidxArmCW frame slotArr body k x || instrGateBW frame slotArr body k x

/-- **The gate of the wide image simulation with indexed stores through a cell**: every
    instruction but the last passes `gateCW`, the last is the return, and every array-pointer
    reload follows a save. -/
def imgGateCW (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) : Bool :=
  (List.range (body.length - 1)).all (fun k =>
      (body[k]?).all fun i => gateCW frame slotArr body k i.li_i)
    && body.getLast?.any (fun r => isRetB r.li_i)
    && reloadSavedB slotArr body

/-- The positions of a body exempt from `instrGateBW` under `imgGateCW`: an indexed store
    through a cell passing `cidxArmCW`. -/
def exemptC (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) : Prop :=
  (body[k]?).any (fun i => cidxArmCW frame slotArr body k i.li_i) = true

/-- A body that passes `imgGateCW` passes the positionwise gate at the exempt positions
    `exemptC`. -/
theorem imgGateW_of_imgGateCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateCW frame slotArr body = true) :
    ImgGateW frame slotArr body (exemptC frame slotArr body) := by
  simp only [imgGateCW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k i hi hk hX => ?_, ?_, h3⟩
  · have := h1 k (by omega)
    rw [hi] at this
    simp only [Option.all_some, gateCW, Bool.or_eq_true] at this
    simp only [exemptC, hi, Option.any_some] at hX
    exact this.resolve_left hX
  · cases hl : body.getLast? with
    | none => rw [hl] at h2; cases h2
    | some r =>
        rw [hl] at h2
        simp only [Option.any_some] at h2
        refine ⟨r, rfl, ?_⟩
        revert h2
        unfold isRetB
        split <;> simp_all

/-- **A body of the gate `imgGateBW` passes `imgGateCW`**: `instrGateBW` is a disjunct of
    `gateCW`. -/
theorem imgGateCW_of_imgGateBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW frame slotArr body = true) : imgGateCW frame slotArr body = true := by
  simp only [imgGateBW, imgGateCW, Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨fun k hk => ?_, h2⟩, h3⟩
  have := h1 k hk
  cases hb : body[k]? with
  | none => rfl
  | some i =>
      rw [hb, Option.all_some] at this
      simp [gateCW, this]

/-- **On a body of the gate `imgGateBW` the invariant of the window holds at every state**: the
    gate refuses every indexed store through a cell (`ImageAddrCells.cellIdxStore?_of_imgGateBW`),
    so that the body has no window. -/
theorem cidxInv_of_imgGateBW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (h : imgGateBW frame slotArr body = true) (base : String → BitVec 64) (s : LstateMF) :
    CidxInv slotArr base body s := by
  refine ⟨fun k i A n idx v D X hi hst _ _ _ => ?_, fun k i A n idx v D X hi hst _ _ => ?_⟩
  · rw [ImageAddrCells.cellIdxStore?_of_imgGateBW h hi] at hst
    cases hst
  · rw [ImageAddrCells.cellIdxStore?_of_imgGateBW h hi] at hst
    cases hst

/-- **The safety of the address machine at an indexed store through a cell.** At the program
    counter of a state related by `ImgRelW` on `c`, where the instruction of `c` passes
    `cidxArmCW`, every body with the same instruction at the program counter reads its
    general-purpose names at width `64` (`WideSafeAt`), and loads no cell (`CellSafeAt`). -/
theorem safeAt_of_cidxArmCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {c : Lcmd} {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base c s sa zf) {bi : Linstr}
    (harm : cidxArmCW frame slotArr c sa.reg.lpc bi.li_i = true) {body : Lcmd}
    (hb : body[sa.reg.lpc]? = some bi) :
    DecodePrintedAddrW.WideSafeAt body sa ∧ DecodePrintedAddrW.CellSafeAt rsp body sa := by
  simp only [cidxArmCW, Bool.and_eq_true] at harm
  obtain ⟨harm, hvc⟩ := harm
  obtain ⟨A, n, idx, v, c0, D, -, hx, hcp, -, -, -, hDW, hvW, -⟩ := cidxArmB_spec harm
  rw [hx] at hvc
  simp only [srcNoCellB, Option.isNone_iff_eq_none] at hvc
  refine ⟨fun ii ds o ss hb' r hr hg _ _ => ?_, fun ii x D' B off p hb' hc _ => ?_⟩
  · rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    simp only at hx
    cases hx
    have hrr : r = v ∨ r = D := by
      rcases hr with rfl | ⟨-, hx⟩ | hr' | hr'
      · exact absurd hg (by decide)
      · simp [JasminLsemAddrCongr.readsRdx, JasminLsemAddrCongr.rdxShape] at hx
      · left; simpa [JasminLsemAddrCongr.srcNames] using hr'
      · right
        simpa [JasminLsemAddrCongr.cellBase, hcp, hvc] using hr'
    rcases hrr with rfl | rfl
    · exact hrel.wid r hg hvW
    · exact hrel.wid r hg hDW
  · rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    simp only at hx
    subst hx
    simp (config := { decide := true }) [cellA?, hcp] at hc

/-- **At an indexed store through a cell, the gate `imgGateCW` is its arm `cidxArmCW`**: the
    gate `instrGateBW` refuses the store (`ImageAddrCells.cellIdxStore?_of_instrGateBW`). -/
theorem cidxArmCW_of_imgGateCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {c : Lcmd}
    (hg : imgGateCW frame slotArr c = true) {k : Nat} {i : Linstr} (hb : c[k]? = some i)
    (hk : k < c.length - 1) (hs : cellIdxStore? slotArr c k i.li_i ≠ none) :
    cidxArmCW frame slotArr c k i.li_i = true := by
  simp only [imgGateCW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
  have := hg.1.1 k hk
  rw [hb, Option.all_some] at this
  simp only [gateCW, Bool.or_eq_true] at this
  exact this.resolve_right fun h => hs (ImageAddrCells.cellIdxStore?_of_instrGateBW h)

/-- **The address of an indexed store through a cell.** At the store of a window passing
    `cidxArmB`, with the invariant of the window at the position, a checked step of the image of
    the store has an index `w` below the array length, and the address register `D` of the cell
    `mem.D.0` holds the address of the word `w` of the array. -/
theorem cidxStore_addr {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    (P : LprogM) {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRelW frame slotArr base body s sa zf) (hinv : CidxInv slotArr base body s)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi)
    (harm : cidxArmB frame slotArr body sa.reg.lpc bi.li_i = true) {A v : String}
    {idx : String ⊕ Nat} {n : Nat}
    (hst : cellIdxStore? slotArr body sa.reg.lpc bi.li_i = some (A, n, idx, v))
    (hs : evalInstrPMemFk true P (cellStoreImg A n idx v) s = some t) :
    ∃ c D w, bi.li_i = .Lopn [.reg c] "MOV:64" [.reg v] ∧ cellParts? c = some (D, 0)
      ∧ w.toNat < n ∧ idxSrcVal s.prog.base.reg idx = ⟨64, w⟩
      ∧ sa.reg.getW D 64 = some (base A + BitVec.ofNat 64 (8 * w.toNat)) := by
  obtain ⟨A', n', idx', v', c, D, hst', hx, hcp, hcW, hfD, hfv, hDW, hvW, hj⟩ :=
    cidxArmB_spec harm
  rw [hst] at hst'
  simp only [Option.some.injEq, Prod.mk.injEq] at hst'
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hst'
  obtain ⟨c0, D0, B, X, d1, src, l, r, m, hx0, hc0, -, -, hl, hli, -, -, -, -, -, -, hac, -⟩ :=
    cellIdxStore?_spec hst
  have hc0e : c0 = c := by
    rw [hx] at hx0
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at hx0
    exact hx0.symm
  subst hc0e
  have hD0 : D0 = D := by
    rw [hc0] at hcp
    exact (Prod.mk.inj (Option.some.inj hcp)).1
  subst hD0
  have hreg : cidxRegs body sa.reg.lpc = some (D0, X) := by
    obtain ⟨ii, li⟩ := l
    simp only at hli
    subst hli
    simp [cidxRegs, hl]
  obtain ⟨w, hDv, hidxv⟩ := hinv.at1 _ bi A n idx v D0 X hb hst hreg (Or.inr hrel.pc.symm)
  have hDs : sa.reg.getW D0 64 = some (base A + BitVec.ofNat 64 (8 * w.toNat)) := by
    rw [getW_eq_some_iff, ← hrel.regsEq hfD hDW, hDv]
  refine ⟨c0, D0, w, hx, hc0, ?_, hidxv, hDs⟩
  cases idx with
  | inl q' =>
    have hq' : s.prog.base.reg.getW q' 64 = some w := getW_eq_some_iff.2 hidxv
    simp only [cellStoreImg] at hs
    have hok := idxOkB_of_checked hs
    simp only [idxOkB, storeStruct?, ite_true, idxBelowB, hq'] at hok
    simpa using hok
  | inr j =>
    have hw : w = BitVec.ofNat 64 j := by simpa [idxSrcVal] using hidxv.symm
    subst hw
    have := hj j rfl
    simp only [BitVec.toNat_ofNat]
    exact lt_of_le_of_lt (Nat.mod_le _ _) this

/-! ## 7. Facts of the gate `imgGateCW` -/

/-- The load of an operand of a window is an `Lopn`. -/
theorem lopn_of_cellOpMov? {x : LinstrR} {d : String} {o : String ⊕ Nat}
    (h : cellOpMov? x = some (d, o)) : ∃ ds op ss, x = .Lopn ds op ss := by
  rcases cellOpMov?_cases h with ⟨q, hsm, -⟩ | ⟨n, rfl, -⟩
  · rcases slotMov?_cases hsm with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩

/-- **One past an instruction that is no `Lopn` no window covers the position**: the
    instructions of a window from the load of the index register up to the store are `Lopn`s. -/
theorem cidxCoversB_succ_of_not_lopn {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {p : Nat} {bi : Linstr} (hb : body[p]? = some bi)
    (hn : ∀ ds op ss, bi.li_i ≠ .Lopn ds op ss) (k : Nat) :
    cidxCoversB slotArr body (p + 1) k = false := by
  unfold cidxCoversB
  cases hk : body[k]? with
  | none => rfl
  | some i =>
    cases hs : cellIdxStore? slotArr body k i.li_i with
    | none => simp [hs]
    | some y =>
      obtain ⟨A, n, q, v⟩ := y
      obtain ⟨c, D, B, X, d1, s, l, r, m, -, -, h3, -, hl, hli, hr, hrm, hm, hmm, -, -, -, hj3, -,
        hkeep⟩ := cellIdxStore?_spec hs
      simp only [Option.any_some, hs, Option.isSome_some, Bool.true_and, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨⟨fun e => ?_, fun e => ?_⟩, ?_⟩
      · rw [show k - 1 = p by omega, hb] at hm
        obtain rfl := Option.some.inj hm
        obtain ⟨ds, op, ss, he⟩ := lopn_of_cellOpMov? hmm
        exact hn ds op ss he
      · rw [show k - 2 = p by omega, hb] at hl
        obtain rfl := Option.some.inj hl
        exact hn _ _ _ hli
      · by_cases hlt : cidxStart body k < p + 1
        · right
          intro hle
          by_cases e : p = cidxStart body k
          · rw [← e, hb] at hr
            obtain rfl := Option.some.inj hr
            obtain ⟨ds, op, ss, he⟩ := lopn_of_cellOpMov? hrm
            exact hn ds op ss he
          · obtain ⟨x, hx, hkx⟩ := hkeep p (by omega) (by omega)
            rw [hb] at hx
            obtain rfl := Option.some.inj hx
            simp only [idxKeepB, Bool.and_eq_true] at hkx
            obtain ⟨ds, op, ss, he⟩ := lopn_of_keepsB hkx.1
            exact hn ds op ss he
        · exact Or.inl hlt

/-- At the position `0` no window covers the position: a window stands at a position of at
    least `3`. -/
theorem cidxCoversB_zero (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat) :
    cidxCoversB slotArr body 0 k = false := by
  unfold cidxCoversB
  cases hb : body[k]? with
  | none => rfl
  | some i =>
    cases hs : cellIdxStore? slotArr body k i.li_i with
    | none => simp [hs]
    | some p =>
      obtain ⟨A, n, q, v⟩ := p
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h3, _⟩ := cellIdxStore?_spec hs
      simp only [Option.any_some, hs, Option.isSome_some, Bool.true_and, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega

/-- At the program counter `0` the invariant of the window holds: a window stands at a
    position of at least `3`. -/
theorem CidxInv.of_lpc_zero {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {body : Lcmd} {s : LstateMF} (h : s.prog.base.reg.lpc = 0) :
    CidxInv slotArr base body s :=
  CidxInv.of_outside fun k => by
    rw [h]
    exact cidxCoversB_zero slotArr body k

/-- `imgGateCW` reads only which names have a frame word. -/
theorem imgGateCW_congr {frame frame' : String → Option (BitVec 64)}
    (h : ∀ q, (frame q).isSome = (frame' q).isSome)
    (slotArr : String → Option (String × Nat)) (body : Lcmd) :
    imgGateCW frame slotArr body = imgGateCW frame' slotArr body := by
  have hn : ∀ q, (frame q).isNone = (frame' q).isNone := fun q => by
    have := h q; cases e : frame q <;> cases e' : frame' q <;> simp_all
  have hi : ∀ k x, instrGateBW frame slotArr body k x = instrGateBW frame' slotArr body k x := by
    intro k x
    have hcg : castGateB frame x = castGateB frame' x := by simp only [castGateB, hn]
    simp only [instrGateBW, gateAtW, carryOkB, oneBitAt_congr h,
      ImageAddrFrame.icase_congr h, gateReadSet_congr h, regGateBW_congr h, sImmB_congr h,
      sCmovB_congr h, hcg, hn, h]
  have hc : ∀ k x, cidxArmCW frame slotArr body k x = cidxArmCW frame' slotArr body k x := by
    intro k x
    simp only [cidxArmCW, cidxArmB, cidxArmAt, oneBitAt_congr h, hn]
  simp only [imgGateCW, gateCW, hi, hc]

/-- Under `imgGateCW` no instruction before the last is the return. -/
theorem not_ret_of_imgGateCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hg : imgGateCW frame slotArr body = true) {k : Nat} {bi : Linstr}
    (hk : k + 1 < body.length) (hb : body[k]? = some bi) : bi.li_i ≠ .Lret := by
  intro hr
  simp only [imgGateCW, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hg
  have := hg.1.1 k (by omega)
  rw [hb] at this
  simp [gateCW, cidxArmCW, cidxArmB, cidxArmAt, srcNoCellB, hr, cellIdxStore?, instrGateBW,
    gateAtW, carryI?, icase, castGateB, DecodePrintedAddrW.classifyK] at this

/-- **At a halt of the address machine on a body of `imgGateCW`, the width analysis is that of
    the last position**: a name outside the analysis at the last position is outside it at
    the program counter. -/
theorem not_mem_oneBitAt_of_haltedCW {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hgate : imgGateCW frame slotArr body = true) {sa : LstateA}
    (hh : haltedA body sa = true) {q : String}
    (hW : q ∉ oneBitAt frame body (body.length - 1)) :
    q ∉ oneBitAt frame body sa.reg.lpc := by
  obtain ⟨r, hr, hret⟩ := (imgGateW_of_imgGateCW hgate).last
  have hlen : 0 < body.length := by
    cases body with
    | nil => cases hr
    | cons _ _ => simp
  have hlast : body[body.length - 1]? = some r := by
    rw [← List.getLast?_eq_getElem?]; exact hr
  have hge : body.length - 1 ≤ sa.reg.lpc := by
    by_contra hlt
    have hk : sa.reg.lpc < body.length := by omega
    obtain ⟨bi, hb⟩ : ∃ bi, body[sa.reg.lpc]? = some bi :=
      ⟨_, List.getElem?_eq_getElem hk⟩
    have hbr : bi.li_i = .Lret := by
      unfold haltedA at hh
      rw [hb] at hh
      obtain ⟨ii, li⟩ := bi
      cases li <;> simp_all
    exact not_ret_of_imgGateCW hgate (by omega) hb hbr
  rcases Nat.lt_or_ge sa.reg.lpc body.length with hk | hk
  · rwa [show sa.reg.lpc = body.length - 1 by omega]
  · have e : oneBitAt frame body sa.reg.lpc = oneBitAt frame body (body.length - 1) := by
      have e1 : oneBitAt frame body sa.reg.lpc = oneBitAt frame body body.length := by
        simp only [oneBitAt, oneBitSt, List.take_of_length_le hk,
          List.take_of_length_le (le_refl _)]
      have e2 : oneBitAt frame body (body.length - 1 + 1)
          = oneBitAt frame body (body.length - 1) := by
        rw [oneBitAt_succ_at hlast, hret]
        simp [oneBitStepAt, oneBitStepAtB, seedB, fwdJoin, bitStore?, oneBitStep, carryI?, icase,
          castOut, DecodePrintedAddrW.classifyK]
      rw [show body.length - 1 + 1 = body.length by omega] at e2
      rw [e1, e2]
    rw [e]
    exact hW

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx
