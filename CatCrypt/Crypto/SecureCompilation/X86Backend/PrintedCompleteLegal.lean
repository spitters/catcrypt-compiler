/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteX86
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowerLegal
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-!
# Completeness of the printed-class gate on covered bodies

`DecodePrintedAddrW.printedAddrWB` gates a printed body by six conjuncts: `decodableLcmd`, a
closing return, `instrOKWB` at every instruction before the return, and the positional
conjuncts `condPrevB`, `carryPrevB` and `castPosB` at every position. This module gives each
conjunct a sufficient condition stated on the instructions of the body, and assembles them.

An instruction is covered (`Covered`) when it is a sub-form `GateOfLegal.GateForm` of the legal
forms of the x86 encoder, a printed shape of `IsaPrintedComplete` over `x86Abi`, or a
stack-array shape `PrintedCompleteX86.ArrShape`; `instrOKWB` accepts every covered instruction.
A body is straight when it has no conditional branch and no width cast (`StraightPrinted`),
and its carry pairs are adjacent when every carry-out binding `ADCXHI:64` directly follows its
add `ADCX:64` on the same sources into a general-purpose destination distinct from them
(`CarryAdjacent`). On such a body the positional conjuncts hold at every position.

The reload of spilled compare operands `CmpSpillReload.cmpReload` is the identity on a body of
covered instructions, since no covered compare has a spill slot as its first operand.

## Main definitions

* `Covered body i`: `i` is a sub-form of `GateForm body`, a printed shape or a stack-array
  shape.
* `UnfusedMulHi i`: `i` is a high-word binding `MULXHI:64` that the fusion did not replace by
  a `MULX`.
* `StraightPrinted body`: no conditional branch and no width cast in `body`.
* `CarryAdjacent body`: every carry-out binding directly follows its add.

## Main results

* `instrOKWB_of_covered`, `instrOKWB_all_of_covered`: `instrOKWB` accepts covered
  instructions, hence the instruction conjunct of `printedAddrWB` holds on a body of them.
* `not_unfusedMulHi_of_covered`: no covered instruction is an unfused high-word binding, so a
  printed body is covered only after the fusion has paired every `MULXHI:64` with its low
  `MUL`.
* `condPrevB_of_straight`, `castPosB_of_straight`: the positional conjuncts on conditional
  branches and casts hold at every position of a straight body.
* `carryPrevB_of_carryAdjacent`: the carry conjunct holds at every position of a body whose
  carry pairs are adjacent.
* `printedAddrWB_of_covered`: a decodable body ending in the return, covered before it, with
  the three positional conjuncts at every position, passes `printedAddrWB`.
* `printedAddrWB_of_straight`: the same for a straight body with adjacent carry pairs.
* `spillCmp?_of_covered`, `cmpReload_of_covered`: `cmpReload` keeps a body of covered
  instructions and returns unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (PrintedShape)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout (decodableLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (condPrevB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteX86
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (GateForm instrOKWB_of_gateForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (spillCmp? cmpReload)

/-! ## 1. The instruction conjunct -/

/-- **A covered instruction** of the body `body`: a sub-form of the legal forms that the gate
    accepts (`GateForm body`), a printed shape over `x86Abi`, or a stack-array shape. -/
def Covered (body : Lcmd) (i : LinstrR) : Prop :=
  GateForm body i ∨ PrintedShape x86Abi i ∨ ArrShape i

/-- `instrOKWB` accepts a covered instruction at the parameters of its body. -/
theorem instrOKWB_of_covered {body : Lcmd} {i : LinstrR} (h : Covered body i) :
    instrOKWB body (Params.ofBody body) i = true := by
  rcases h with h | h | h
  · exact instrOKWB_of_gateForm h
  · exact x86_printedComplete.ok_of_shape _ _ h
  · exact instrOKWB_of_arrShape body _ h

/-- **The instruction conjunct of `printedAddrWB` on covered bodies**: it holds of a body each
    of whose instructions before the last is covered. -/
theorem instrOKWB_all_of_covered {body : Lcmd} (h : ∀ i ∈ body.dropLast, Covered body i.li_i) :
    body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i) = true := by
  grind [List.all_eq_true, instrOKWB_of_covered]

/-- **An unfused high-word binding**: the binding `MULXHI:64 D, [A, S]` of the high word of a
    product that `FuseMulHi.fuseMulHiLprog` did not fuse with its low `MUL` into a `MULX`. The
    encoder emits no bytes for it (`LprogBytes.carriesNoBytes`), and the gate has no arm for
    it. -/
def UnfusedMulHi (i : LinstrR) : Prop :=
  ∃ (ds ss : List LOperand), i = .Lopn ds "MULXHI:64" ss

/-- No covered instruction is an unfused high-word binding. -/
theorem not_unfusedMulHi_of_covered {body : Lcmd} {i : LinstrR} (h : Covered body i) :
    ¬ UnfusedMulHi i := by
  rintro ⟨ds, ss, hi⟩
  rcases h with h | h | h
  · cases h
    case tagShift b k d s hb _ _ _ _ =>
      have hne : GateOfLegal.tagMnem b k ≠ "MULXHI:64" := by tag_ne hb
      simp_all
    all_goals simp_all (config := { decide := true }) [GateOfLegal.castMnems]
  · rcases h with ⟨n, _, _, _, -, -, -, h⟩ | ⟨n, _, _, _, -, -, -, h⟩ |
      ⟨n, _, _, _, -, -, -, h⟩ | ⟨_, -, h⟩ <;> (try cases n) <;> simp_all
  · rcases h with ⟨_, _, -, -, -, h⟩ | ⟨_, _, _, _, -, -, -, -, h⟩ <;> simp_all

/-! ## 2. The positional conjuncts -/

/-- **A straight printed body**: no conditional branch and no width cast (`classifyK`). -/
def StraightPrinted (body : Lcmd) : Prop :=
  ∀ i ∈ body, (∀ c l, i.li_i ≠ .Lcond c l) ∧ classifyK i.li_i = none

/-- **The carry pairs of a body are adjacent**: every carry-out binding
    `ADCXHI:64 O, [A, S, C]` at a position `k` follows, at `k - 1`, the add
    `ADCX:64 D, [A, S, C]` on the same sources into a general-purpose name `D` that is none
    of them. -/
def CarryAdjacent (body : Lcmd) : Prop :=
  ∀ (k ii : Nat) (o a s c : String),
    body[k]? = some ⟨ii, .Lopn [.reg o] "ADCXHI:64" [.reg a, .reg s, .reg c]⟩ →
    ∃ (ii' : Nat) (d : String), 0 < k ∧
      body[k - 1]? = some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩ ∧
      gpOk d = true ∧ d ≠ a ∧ d ≠ s ∧ d ≠ c

/-- On a straight body, `condPrevB` holds at every position. -/
theorem condPrevB_of_straight {body : Lcmd} (h : StraightPrinted body) (k : Nat) :
    condPrevB body k = true := by
  unfold condPrevB
  split
  · next j c l hk =>
    exact absurd rfl ((h _ (List.mem_of_getElem? hk)).1 c l)
  · rfl

/-- On a straight body, `castPosB` holds at every position. -/
theorem castPosB_of_straight {body : Lcmd} (h : StraightPrinted body) (k : Nat) :
    castPosB body k = true := by
  unfold castPosB
  cases hk : body[k]? with
  | none => rfl
  | some j => simp [(h j (List.mem_of_getElem? hk)).2]

/-- A general-purpose name is separated from every name by `slotSepB`. -/
theorem slotSepB_of_gpOk {P : Params} {d x : String} (hd : gpOk d = true) :
    slotSepB P d x = true := by
  simp [slotSepB, GateOfLegal.gpOk_not_slot hd]

/-- On a body whose carry pairs are adjacent, `carryPrevB` holds at every position. -/
theorem carryPrevB_of_carryAdjacent {body : Lcmd} (h : CarryAdjacent body) (k : Nat) :
    carryPrevB body k = true := by
  unfold carryPrevB
  split
  · next j o m a s c hk =>
    split_ifs with hm
    · subst hm
      obtain ⟨ii', d, hk0, hprev, hd, hda, hds, hdc⟩ := h k j o a s c hk
      simp [hprev, hda, hds, hdc, slotSepB_of_gpOk hd, Nat.pos_iff_ne_zero.1 hk0]
    · rfl
  · rfl

/-! ## 3. The assembled gate -/

/-- **`printedAddrWB` from its conjuncts on covered bodies**: a decodable body ending in the
    return, each of whose instructions before the return is covered, and which satisfies
    `condPrevB`, `carryPrevB` and `castPosB` at every position, passes `printedAddrWB`. -/
theorem printedAddrWB_of_covered {body : Lcmd} (hdec : decodableLcmd body = true)
    (hret : body.getLast?.any (fun r => isRetB r.li_i) = true)
    (hcov : ∀ i ∈ body.dropLast, Covered body i.li_i)
    (hcond : ∀ k, condPrevB body k = true) (hcarry : ∀ k, carryPrevB body k = true)
    (hcast : ∀ k, castPosB body k = true) :
    printedAddrWB body = true := by
  simp [printedAddrWB, hdec, hret, instrOKWB_all_of_covered hcov, List.all_eq_true, hcond,
    hcarry, hcast]

/-- **`printedAddrWB` on straight covered bodies**: a decodable straight body ending in the
    return, each of whose instructions before the return is covered and whose carry pairs are
    adjacent, passes `printedAddrWB`. -/
theorem printedAddrWB_of_straight {body : Lcmd} (hdec : decodableLcmd body = true)
    (hret : body.getLast?.any (fun r => isRetB r.li_i) = true)
    (hcov : ∀ i ∈ body.dropLast, Covered body i.li_i) (hs : StraightPrinted body)
    (hc : CarryAdjacent body) :
    printedAddrWB body = true :=
  printedAddrWB_of_covered hdec hret hcov (condPrevB_of_straight hs)
    (carryPrevB_of_carryAdjacent hc) (castPosB_of_straight hs)

/-! ## 4. The reload of spilled compare operands -/

/-- A general-purpose name is no spill slot. -/
theorem isSpill_of_gpOk {d : String} (h : gpOk d = true) : (LOperand.reg d).isSpill = false := by
  rw [EncodeComplete.isSpill_reg]
  cases hk : hasPrefix d "k."
  · rfl
  · have := EncodeComplete.isSpillOrQsave_of_k hk
    rw [GateOfLegal.gpOk_not_slot h] at this
    cases this

/-- An instruction whose destination is no spill slot is no compare on a spilled first
    operand. -/
theorem spillCmp?_of_dst {d opn : String} {ss : List LOperand}
    (h : (LOperand.reg d).isSpill = false) : spillCmp? (.Lopn [.reg d] opn ss) = none := by
  unfold spillCmp?
  split
  · next heq =>
    obtain ⟨rfl, rfl, rfl⟩ := heq
    simp_all
  · rfl

/-- An instruction into a general-purpose name is no compare on a spilled first operand. -/
theorem spillCmp?_of_gpOk {d opn : String} {ss : List LOperand} (h : gpOk d = true) :
    spillCmp? (.Lopn [.reg d] opn ss) = none :=
  spillCmp?_of_dst (isSpill_of_gpOk h)

/-- No covered instruction is a compare on a spilled first operand. -/
theorem spillCmp?_of_covered {body : Lcmd} {i : LinstrR} (h : Covered body i) :
    spillCmp? i = none := by
  rcases h with h | h | h
  · cases h <;> first
      | rfl
      | (apply spillCmp?_of_gpOk; assumption)
  · rcases h with ⟨_, R, _, _, hR, -, -, rfl⟩ | ⟨_, R, _, _, hR, -, -, rfl⟩ |
      ⟨_, R, _, _, hR, -, -, rfl⟩ | ⟨R, hR, rfl⟩ <;>
      exact spillCmp?_of_gpOk ((gpOk_iff_isGp R).2 hR)
  · rcases h with ⟨_, _, -, -, -, rfl⟩ | ⟨D, _, _, _, hD, -, -, -, rfl⟩
    · rfl
    · exact spillCmp?_of_gpOk ((gpOk_iff_isGp D).2 hD)

/-- **`cmpReload` keeps a covered body**: on a body each of whose instructions is covered or
    the return, the reload of spilled compare operands returns the body unchanged. -/
theorem cmpReload_of_covered {body body' : Lcmd}
    (h : ∀ i ∈ body, Covered body' i.li_i ∨ i.li_i = .Lret) :
    cmpReload body = body := by
  apply CmpSpillReload.cmpReload_of_forall
  intro i hi
  rcases h i hi with h | h
  · exact spillCmp?_of_covered h
  · rw [h]; rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal
