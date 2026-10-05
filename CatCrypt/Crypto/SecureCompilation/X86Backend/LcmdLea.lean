/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags

/-!
# `LEA` formation on the owned-RA `Lcmd`

A `Lcmd → Lcmd` pass over the owned-RA linear body that folds an address
computation `d := s; d := d + k` into the single effective-address load
`leaq k(%s), %d`. The shape is the front's index increment: a materialised
constant, a rebind of the index register, and the two-address add.

## The recognised chain

```
Lopn [.reg d] MOV:64/MOVQ [.reg s]          -- d := s
Lopn [.reg d] ADD:64      [.reg d, .imm k]  -- d := d + k
=>
Lopn [.reg d] LEA:64      [.reg (memName s k)]
```

Both registers are bare physical GPs, the displacement is within the signed
`disp32` field, and the width tag is `:64` on both instructions. The output
operand is the `mem.<base>.<off>` form the AT&T printer's `LEA` arm resolves to
an effective address (`LprogAsmPrinter.renderLopn` single-source arm ⇒
`leaq <off>(%<base>), %<d>`).

The immediate source of the `ADD` is what `LcmdCopyPropagate` produces from a
materialised `MOV $k, %r`, so this pass runs AFTER `copyPropagateLprog`; on a
body where the constant is still in a register the chain is three instructions
and is not recognised.

## The flag side condition

`add` writes CF/OF/ZF/SF; `lea` writes no flag. The fold is therefore performed
only where the flags the `add` sets are dead: the pass carries a backward
flags-live bit (all-live at the end of a body, at every barrier, at every
instruction that reads a flag, and at every mnemonic outside the classified
alphabet; cleared by an instruction that rewrites every flag a reader consumes)
and fuses only when that bit is `false` immediately after the `add`. The step is
`LcmdFlags.flagsLiveStep`, over the classification `LcmdFlags.flagEffect` that
the segmenting of `LprogOptPipeline.optimizeBasicBlocks` also uses. `Lstate` carries no flags,
so the machine model below cannot express this condition and the value theorems
do not depend on it; the condition rests on the mnemonic classification alone.

## The byte path

`LprogBytes.encodeLopn` encodes a `LEA` whose source is a `mem.<base>.<off>`
name over a tabulated GP base as `8D /r` with the `[base + disp]`
ModRM/SIB/displacement tail — the bytes of the `leaq <off>(%<base>), %<dst>`
line the AT&T printer emits for the same instruction. §10 checks a fused body
against `LprogBytes.encodableLcmd`, the gate that holds exactly when every
instruction of a body reaches the byte stream.

## The machine model

`JasminLsem.applyOpn` models no `LEA` opcode, so `lsemStep` on the pass's output
is `none`. The results below are stated against `lsemStepLea`, `lsemStep`
extended with one arm: a single-register-source `LEA` writes
`lvm base + disp` for the `(base, disp)` an address decoder `memAddr` assigns
to the operand name. The decoder is a parameter constrained only by
`memAddr (memName b o) = some (b, o)` — the names this pass constructs. §11
gives the concrete decoder, `LprogAsmPrinter.resolveName`'s parse, and checks
that constraint at the base names the pass can construct. Off the `LEA` arm the
extended machine is `lsemStep` (`lsemStepLea_eq_of_not_lea`).

## Main results

* `leaBody` / `leaLprog` — the pass on a body and on a program.
* `leaBody_lsemStraightLea` — running the rewritten body from any state reaches
  a state agreeing with the original on every register and on memory.
* `leaInstr_value_64` — the recognised pair and its `LEA` leave the same word in
  the destination.
* `leaBody_lsemLeakLea_state_indep` — the leak trace is a function of the
  instruction list.
* `lsemStraightLea_eq_of_not_lea` — on a body carrying no `LEA` the extended
  machine agrees with `lsemStraight`.
* `memAddrOfName` — the operand-name address decoder.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdLea

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (mnemWidth)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP instrMnem lsemStep_congr_full)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags (flagsLiveStep)

/-! ## 1. The recognised chain -/

/-- The largest displacement a formed `LEA` may carry: the signed `disp32`
    field of an x86 effective address. -/
def leaDispMax : Nat := 2147483647

/-- The 64-bit register rebind an address chain starts with: `Lopn [.reg d]
    MOV:64/MOVQ [.reg s]` with both names bare physical GPs. Returns `(d, s)`. -/
def moveBase (i : Linstr) : Option (String × String) :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg s] =>
      if (stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ")
          && mnemWidth opn == 64 && isPhysGP d && isPhysGP s then some (d, s)
      else none
  | _ => none

/-- The two-address 64-bit add of an immediate an address chain ends with:
    `Lopn [.reg d] ADD:64 [.reg d, .imm k]` with `d` a bare physical GP and `k`
    within the `disp32` field. Returns `(d, k)`. -/
def addImm (i : Linstr) : Option (String × Nat) :=
  match i.li_i with
  | .Lopn [.reg d] opn [.reg d', .imm k] =>
      if stripWidthTag opn == "ADD" && mnemWidth opn == 64
          && isPhysGP d && d' == d && k ≤ leaDispMax then some (d, k)
      else none
  | _ => none

/-- The instruction a recognised chain is folded into. -/
def leaInstr (ii : Nat) (d s : String) (k : Nat) : Linstr :=
  ⟨ii, .Lopn [LOperand.reg d] "LEA:64" [LOperand.reg (memName s k)]⟩

/-! ## 2. The flag-liveness bit

The bit steps backward by `LcmdFlags.flagsLiveStep`, over the classification
`LcmdFlags.flagEffect`. -/

/-! ## 3. The pass -/

/-- A deferred `add` head: the instruction, its destination register, and its
    displacement. It sits between the fold state's flags bit and its output
    suffix; `leaOut` puts it back when no rebind precedes it. -/
abbrev LeaPending := Linstr × String × Nat

/-- The backward fold state: the flags-live bit at the top of the emitted
    suffix, a deferred `add` head, and the emitted suffix. -/
abbrev LeaState := Bool × Option LeaPending × Lcmd

/-- The fold step for an instruction that heads no fusion: an `add` whose flags
    are dead becomes the deferred head, everything else is emitted. -/
def leaPlain (i : Linstr) (fl : Bool) (acc : Lcmd) : LeaState :=
  match addImm i with
  | some (d, k) => if fl then (false, none, i :: acc) else (false, some (i, d, k), acc)
  | none => (flagsLiveStep i fl, none, i :: acc)

/-- One backward step of the pass: a rebind immediately before a deferred `add`
    on the same register fuses into a `LEA:64`; the fused instruction is
    flag-neutral and the deferred `add`'s flags were dead, so the bit before it
    is `false`. -/
def leaStep (i : Linstr) : LeaState → LeaState
  | (fl, pending, acc) =>
    match pending with
    | some (addI, d, k) =>
        match moveBase i with
        | some (dm, s) =>
            if dm == d then (false, none, leaInstr i.li_ii d s k :: acc)
            else leaPlain i fl (addI :: acc)
        | none => leaPlain i fl (addI :: acc)
    | none => leaPlain i fl acc

theorem leaStep_eq (i : Linstr) (fl : Bool) (pending : Option LeaPending) (acc : Lcmd) :
    leaStep i (fl, pending, acc) =
      (match pending with
       | some (addI, d, k) =>
           (match moveBase i with
            | some (dm, s) =>
                if dm == d then (false, none, leaInstr i.li_ii d s k :: acc)
                else leaPlain i fl (addI :: acc)
            | none => leaPlain i fl (addI :: acc))
       | none => leaPlain i fl acc) := rfl

/-- The instruction list a fold state stands for. -/
def leaOut : LeaState → Lcmd
  | (_, none, acc) => acc
  | (_, some (addI, _, _), acc) => addI :: acc

@[simp] theorem leaOut_none (fl : Bool) (acc : Lcmd) : leaOut (fl, none, acc) = acc := rfl

@[simp] theorem leaOut_some (fl : Bool) (addI : Linstr) (d : String) (k : Nat)
    (acc : Lcmd) : leaOut (fl, some (addI, d, k), acc) = addI :: acc := rfl

/-- `LEA` formation over one owned-RA body. Run it after
    `LcmdCopyPropagate.copyPropagateLprog`, on the AT&T text path only. -/
def leaBody (body : Lcmd) : Lcmd :=
  leaOut (body.foldr leaStep (true, none, []))

/-- The pass on one `Lfundef` (body only; ABI metadata untouched). -/
def leaFundef (f : Lfundef) : Lfundef :=
  { f with lfd_body := leaBody f.lfd_body }

/-- The pass on a whole `Lprog`. -/
def leaLprog (p : Lprog) : Lprog :=
  { p with lp_funcs := p.lp_funcs.map fun (n, f) => (n, leaFundef f) }

/-- Count the `LEA:64` instructions a body carries (the before/after
    measurement hook). -/
def countLea (body : Lcmd) : Nat :=
  (body.filter fun i => instrMnem i == some "LEA:64").length

/-! ## 4. Firing / non-firing demos (`#guard`, evaluated at elaboration) -/

/-- The emitted index-increment slice of `mpn_mul_1`: the materialised `$1`,
    the index rebind, the two-address add, the rebind of the sum, the indexed
    store, and the loop counter bump that overwrites the flags. -/
def demoIndexBump : Lcmd :=
  [ ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.imm 1]⟩,
    ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RDX"]⟩,
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"]⟩,
    ⟨0, .Lopn [.reg "arr"] "STOREIDX:64" [.arrIdx "R14" "RDX" 8, .reg "RBP"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

-- **The chain fires end to end:** constant propagation folds `$1` into the add
-- and kills the materialising move, then the rebind and the add become one
-- `LEA:64`. Four instructions of address arithmetic become one.
#guard leaBody (LcmdCopyPropagate.copyPropagateBody demoIndexBump) =
  [ (⟨0, .Lopn [.reg "R8"] "LEA:64" [.reg "mem.RAX.1"]⟩ : Linstr),
    ⟨0, .Lopn [.reg "RDX"] "MOV:64" [.reg "R8"]⟩,
    ⟨0, .Lopn [.reg "arr"] "STOREIDX:64" [.arrIdx "R14" "RDX" 8, .reg "RBP"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

/-- The same chain with a carry consumer after the add: the flags are live, so
    the fold is declined. -/
def demoFlagsLive : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "R9"] "ADC:64" [.reg "R9", .reg "R10"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoFlagsLive = demoFlagsLive

/-- The chain at the end of a body: the flags are live out, so the fold is
    declined. -/
def demoFlagsLiveOut : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩ ]

#guard leaBody demoFlagsLiveOut = demoFlagsLiveOut

/-- A register-source add is not an address chain. -/
def demoRegAdd : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .reg "RCX"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoRegAdd = demoRegAdd

/-- A rebind of a different register does not head the deferred add. -/
def demoOtherReg : Lcmd :=
  [ ⟨0, .Lopn [.reg "R9"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoOtherReg = demoOtherReg

/-- A spill-slot source is not a bare physical GP, so the rebind is not a
    chain head. -/
def demoSpillSrc : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "k.3"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoSpillSrc = demoSpillSrc

/-- A 32-bit chain is not folded into a 64-bit `LEA`. -/
def demoNarrow : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoNarrow = demoNarrow

-- The operand name a formed `LEA` carries, on the alphabet this pass
-- constructs.
#guard memName "RAX" 1 = "mem.RAX.1"

/-! ## 5. The `LEA`-extended linear machine -/

theorem stripWidthTag_LEA64 : stripWidthTag "LEA:64" = "LEA" := by decide +kernel

/-- Is this a single-register-source `LEA`? Returns `(dst, name)`. -/
def isLeaInstr : LinstrR → Option (String × String)
  | .Lopn [.reg dst] opn [.reg n] =>
      if stripWidthTag opn == "LEA" then some (dst, n) else none
  | _ => none

/-- The effective address a `mem.<base>.<off>` operand name denotes under the
    decoder `memAddr`: the base register's word plus the displacement. -/
def leaAddr {w : Nat} (memAddr : String → Option (String × Nat)) (s : Lstate w)
    (n : String) : Option (BitVec w) :=
  (memAddr n).map fun p => s.lvm p.1 + BitVec.ofNat w p.2

/-- `JasminLsem.lsemStep` extended with the `LEA` arm: a single-register-source
    `LEA` writes the effective address its operand denotes and advances the pc.
    Every other instruction steps exactly as `lsemStep`. -/
def lsemStepLea {w : Nat} (memAddr : String → Option (String × Nat))
    (i : LinstrR) (s : Lstate w) : Option (Lstate w) :=
  match isLeaInstr i with
  | some (dst, n) => (leaAddr memAddr s n).map fun v => (s.setReg dst v).nextPc
  | none => lsemStep i s

/-- Straight-line execution on the `LEA`-extended machine. -/
def lsemStraightLea {w : Nat} (memAddr : String → Option (String × Nat)) :
    List LinstrR → Lstate w → Option (Lstate w)
  | [], s => some s
  | i :: is, s =>
      match lsemStepLea memAddr i s with
      | some s' => lsemStraightLea memAddr is s'
      | none => none

@[simp] theorem lsemStraightLea_nil {w : Nat}
    (memAddr : String → Option (String × Nat)) (s : Lstate w) :
    lsemStraightLea memAddr [] s = some s := rfl

@[simp] theorem lsemStraightLea_cons {w : Nat}
    (memAddr : String → Option (String × Nat)) (i : LinstrR) (is : List LinstrR)
    (s : Lstate w) :
    lsemStraightLea memAddr (i :: is) s =
      (match lsemStepLea memAddr i s with
        | some s' => lsemStraightLea memAddr is s'
        | none => none) := rfl

/-- Off the `LEA` arm the extended machine is `lsemStep`. -/
theorem lsemStepLea_eq_of_not_lea {w : Nat}
    (memAddr : String → Option (String × Nat)) (i : LinstrR) (s : Lstate w)
    (h : isLeaInstr i = none) : lsemStepLea memAddr i s = lsemStep i s := by
  unfold lsemStepLea
  rw [h]

/-- The `LEA` arm's step. -/
theorem lsemStepLea_lea {w : Nat} (memAddr : String → Option (String × Nat))
    {i : LinstrR} {dst n : String} (hi : isLeaInstr i = some (dst, n))
    (s : Lstate w) :
    lsemStepLea memAddr i s
      = (leaAddr memAddr s n).map fun v => (s.setReg dst v).nextPc := by
  unfold lsemStepLea
  rw [hi]

/-- On a `LEA`-free instruction list the extended machine is `lsemStraight`. -/
theorem lsemStraightLea_eq_of_not_lea {w : Nat}
    (memAddr : String → Option (String × Nat)) (is : List LinstrR) (s : Lstate w)
    (h : ∀ i ∈ is, isLeaInstr i = none) :
    lsemStraightLea memAddr is s = lsemStraight is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [lsemStraightLea_cons, lsemStraight_cons,
      lsemStepLea_eq_of_not_lea memAddr i s (h i List.mem_cons_self)]
    cases lsemStep (w := w) i s with
    | none => rfl
    | some s' => exact ih s' (fun j hj => h j (List.mem_cons_of_mem _ hj))

/-! ## 6. The extended machine is a congruence for register/memory agreement -/

/-- On states with equal register map and memory, every instruction steps to
    states with equal register map and memory. -/
theorem lsemStepLea_congr_full {w : Nat} (memAddr : String → Option (String × Nat))
    (i : LinstrR) {s t : Lstate w} (hv : s.lvm = t.lvm) (hm : s.lmem = t.lmem)
    {s₁ : Lstate w} (hst : lsemStepLea memAddr i s = some s₁) :
    ∃ t₁, lsemStepLea memAddr i t = some t₁ ∧ s₁.lvm = t₁.lvm ∧ s₁.lmem = t₁.lmem := by
  cases hi : isLeaInstr i with
  | none =>
    rw [lsemStepLea_eq_of_not_lea memAddr i s hi] at hst
    rw [lsemStepLea_eq_of_not_lea memAddr i t hi]
    exact lsemStep_congr_full i hv hm hst
  | some p =>
    obtain ⟨dst, n⟩ := p
    rw [lsemStepLea_lea memAddr hi s] at hst
    rw [lsemStepLea_lea memAddr hi t]
    cases ha : leaAddr memAddr s n with
    | none => rw [ha] at hst; exact absurd hst (by simp)
    | some v =>
      rw [ha] at hst
      have hat : leaAddr memAddr t n = some v := by
        unfold leaAddr at ha ⊢
        rw [← hv]
        exact ha
      have he : s₁ = (s.setReg dst v).nextPc := by simpa using hst.symm
      rw [hat]
      refine ⟨(t.setReg dst v).nextPc, rfl, ?_, ?_⟩
      · rw [he]; simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, hv]
      · rw [he]; exact hm

/-- Straight-line execution on the extended machine respects register/memory
    agreement. -/
theorem lsemStraightLea_congr_full {w : Nat}
    (memAddr : String → Option (String × Nat)) (is : List LinstrR) :
    ∀ {s t : Lstate w}, s.lvm = t.lvm → s.lmem = t.lmem →
      ∀ {s₂ : Lstate w}, lsemStraightLea memAddr is s = some s₂ →
        ∃ t₂, lsemStraightLea memAddr is t = some t₂
          ∧ s₂.lvm = t₂.lvm ∧ s₂.lmem = t₂.lmem := by
  induction is with
  | nil =>
    intro s t hv hm s₂ h
    refine ⟨t, rfl, ?_, ?_⟩
    · rw [← Option.some.inj h]; exact hv
    · rw [← Option.some.inj h]; exact hm
  | cons i rest ih =>
    intro s t hv hm s₂ h
    rw [lsemStraightLea_cons] at h
    rw [lsemStraightLea_cons]
    cases hst : lsemStepLea memAddr i s with
    | none => rw [hst] at h; exact absurd h (by simp)
    | some s₁ =>
      simp only [hst] at h
      obtain ⟨t₁, ht, hv1, hm1⟩ := lsemStepLea_congr_full memAddr i hv hm hst
      simp only [ht]
      exact ih hv1 hm1 h

/-! ## 7. What the formed `LEA` computes -/

/-- A recognised rebind is an `Lopn` with a copy opcode and two bare-GP
    names. -/
theorem moveBase_inv {i : Linstr} {d s : String} (h : moveBase i = some (d, s)) :
    ∃ opn, i.li_i = .Lopn [LOperand.reg d] opn [LOperand.reg s]
      ∧ (stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ") := by
  unfold moveBase at h
  split at h
  · rename_i d' opn' s' hi
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
      have he := Option.some.inj h
      refine ⟨opn', ?_, ?_⟩
      · rw [hi]; simp_all
      · simp_all
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A recognised add is an `Lopn` with the `ADD` opcode, its destination as
    first source and the displacement as second. -/
theorem addImm_inv {i : Linstr} {d : String} {k : Nat} (h : addImm i = some (d, k)) :
    ∃ opn, i.li_i = .Lopn [LOperand.reg d] opn [LOperand.reg d, LOperand.imm k]
      ∧ stripWidthTag opn = "ADD" := by
  unfold addImm at h
  split at h
  · rename_i d' opn' e' k' hi
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      have he := Option.some.inj h
      refine ⟨opn', ?_, ?_⟩
      · rw [hi]; simp_all
      · simp_all
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A copy opcode is not the `LEA` opcode. -/
theorem isLeaInstr_of_move {d s opn : String}
    (h : stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ") :
    isLeaInstr (.Lopn [LOperand.reg d] opn [LOperand.reg s]) = none := by
  unfold isLeaInstr
  rcases h with h | h <;> simp [h]

/-- The formed instruction is on the `LEA` arm, with its base name as
    operand. -/
theorem isLeaInstr_leaInstr (ii : Nat) (d s : String) (k : Nat) :
    isLeaInstr (leaInstr ii d s k).li_i = some (d, memName s k) := by
  simp [isLeaInstr, leaInstr, stripWidthTag_LEA64]

/-- The step of a recognised rebind: the destination takes the source's word. -/
theorem lsemStepLea_move {w : Nat} (memAddr : String → Option (String × Nat))
    {d s opn : String} (h : stripWidthTag opn = "MOV" ∨ stripWidthTag opn = "MOVQ")
    (st : Lstate w) :
    lsemStepLea memAddr (.Lopn [LOperand.reg d] opn [LOperand.reg s]) st
      = some ((st.setReg d (st.lvm s)).nextPc) := by
  rw [lsemStepLea_eq_of_not_lea memAddr _ st (isLeaInstr_of_move h)]
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand]
  rcases h with h | h <;> rw [h] <;> rfl

/-- The step of a recognised add: the destination takes its old word plus the
    displacement. -/
theorem lsemStepLea_addImm {w : Nat} (memAddr : String → Option (String × Nat))
    {d opn : String} {k : Nat} (h : stripWidthTag opn = "ADD") (st : Lstate w) :
    lsemStepLea memAddr (.Lopn [LOperand.reg d] opn [LOperand.reg d, LOperand.imm k]) st
      = some ((st.setReg d (st.lvm d + BitVec.ofNat w k)).nextPc) := by
  have hl : isLeaInstr (.Lopn [LOperand.reg d] opn [LOperand.reg d, LOperand.imm k])
      = none := rfl
  rw [lsemStepLea_eq_of_not_lea memAddr _ st hl]
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, h]
  rfl

/-- The step of a formed `LEA`: the destination takes the effective address. -/
theorem lsemStepLea_leaInstr {w : Nat} {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (ii : Nat) (d s : String)
    (k : Nat) (st : Lstate w) :
    lsemStepLea memAddr (leaInstr ii d s k).li_i st
      = some ((st.setReg d (st.lvm s + BitVec.ofNat w k)).nextPc) := by
  rw [lsemStepLea_lea memAddr (isLeaInstr_leaInstr ii d s k) st]
  unfold leaAddr
  rw [hmem s k]
  rfl

/-- **The formed `LEA:64` computes the folded chain's word, at 64 bits.** Both
    the two-instruction chain and the single `LEA:64` leave the destination
    holding `base + displacement`. -/
theorem leaInstr_value_64 {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (ii : Nat) (d s : String)
    (k : Nat) {opn1 opn2 : String}
    (h1 : stripWidthTag opn1 = "MOV" ∨ stripWidthTag opn1 = "MOVQ")
    (h2 : stripWidthTag opn2 = "ADD") (st : Lstate 64) :
    ((lsemStraightLea memAddr
        [.Lopn [LOperand.reg d] opn1 [LOperand.reg s],
         .Lopn [LOperand.reg d] opn2 [LOperand.reg d, LOperand.imm k]] st).map
        (fun u => u.lvm d) = some (st.lvm s + BitVec.ofNat 64 k))
      ∧ ((lsemStraightLea memAddr [(leaInstr ii d s k).li_i] st).map (fun u => u.lvm d)
        = some (st.lvm s + BitVec.ofNat 64 k)) := by
  refine ⟨?_, ?_⟩
  · simp only [lsemStraightLea_cons, lsemStepLea_move memAddr h1,
      lsemStepLea_addImm memAddr h2, lsemStraightLea_nil]
    simp [Lstate.setReg, Lstate.nextPc]
  · simp only [lsemStraightLea_cons, lsemStepLea_leaInstr hmem, lsemStraightLea_nil]
    simp [Lstate.setReg, Lstate.nextPc]

/-! ## 8. The pass preserves the machine state -/

/-- The deferred head of a fold state is always an instruction the recogniser
    accepted with the recorded destination and displacement. -/
theorem leaFold_pending_shape (body : Lcmd) :
    ∀ (init : LeaState),
      (∀ addI d k, init.2.1 = some (addI, d, k) → addImm addI = some (d, k)) →
      ∀ addI d k, (body.foldr leaStep init).2.1 = some (addI, d, k) →
        addImm addI = some (d, k) := by
  induction body with
  | nil => intro init h addI d k he; exact h addI d k he
  | cons i rest ih =>
    intro init h addI d k he
    rw [List.foldr_cons] at he
    obtain ⟨fl, pend, acc, hP⟩ : ∃ a b c, rest.foldr leaStep init = (a, b, c) :=
      ⟨_, _, _, rfl⟩
    rw [hP] at he
    have hplain : ∀ (A : Lcmd), (leaPlain i fl A).2.1 = some (addI, d, k) →
        addImm addI = some (d, k) := by
      intro A hA
      unfold leaPlain at hA
      cases hai : addImm i with
      | none => rw [hai] at hA; exact absurd hA (by simp)
      | some q =>
        obtain ⟨d', k'⟩ := q
        rw [hai] at hA
        cases fl with
        | true => exact absurd hA (by simp)
        | false =>
          simp only [Bool.false_eq_true, if_false, Option.some.injEq,
            Prod.mk.injEq] at hA
          obtain ⟨h1, h2, h3⟩ := hA
          rw [← h1, hai, h2, h3]
    rw [leaStep_eq] at he
    cases hpend : pend with
    | none => simp only [hpend] at he; exact hplain acc he
    | some q =>
      obtain ⟨aI, ad, ak⟩ := q
      cases hmb : moveBase i with
      | none => simp only [hpend, hmb] at he; exact hplain (aI :: acc) he
      | some r =>
        obtain ⟨dm, sm⟩ := r
        by_cases hdm : (dm == ad) = true
        · simp only [hpend, hmb, if_pos hdm] at he; exact absurd he (by simp)
        · simp only [hpend, hmb, if_neg hdm] at he; exact hplain (aI :: acc) he

/-- Every non-fusing step emits its instruction at the head. -/
theorem leaOut_leaPlain (i : Linstr) (fl : Bool) (A : Lcmd) :
    leaOut (leaPlain i fl A) = i :: A := by
  unfold leaPlain
  cases hai : addImm i with
  | none => rfl
  | some q =>
    obtain ⟨d, k⟩ := q
    cases fl with
    | true => rfl
    | false => rfl

/-- **The pass preserves the machine state.** On every body and every pair of
    start states agreeing on registers and memory, a run of the input on the
    `LEA`-extended machine is matched by a run of the output ending in a state
    with the same register map and the same memory. The program counter is lower
    by the number of fused pairs. -/
theorem leaFold_sim {w : Nat} {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (body : Lcmd) :
    ∀ (s t : Lstate w), s.lvm = t.lvm → s.lmem = t.lmem →
      ∀ s₂, lsemStraightLea memAddr (body.map Linstr.li_i) s = some s₂ →
        ∃ t₂, lsemStraightLea memAddr
            ((leaOut (body.foldr leaStep (true, none, []))).map Linstr.li_i) t = some t₂
          ∧ s₂.lvm = t₂.lvm ∧ s₂.lmem = t₂.lmem := by
  induction body with
  | nil =>
    intro s t hv hm s₂ h
    refine ⟨t, rfl, ?_, ?_⟩
    · rw [← Option.some.inj h]; exact hv
    · rw [← Option.some.inj h]; exact hm
  | cons i rest ih =>
    intro s t hv hm s₂ hrun
    rw [List.map_cons, lsemStraightLea_cons] at hrun
    obtain ⟨fl, pend, acc, hP⟩ : ∃ a b c, rest.foldr leaStep (true, none, []) = (a, b, c) :=
      ⟨_, _, _, rfl⟩
    have ih' := ih
    rw [hP] at ih'
    have hinv : ∀ addI d k, pend = some (addI, d, k) → addImm addI = some (d, k) := by
      intro addI d k he
      refine leaFold_pending_shape rest (true, none, [])
        (by intro a b c hb; exact absurd hb (by simp)) addI d k ?_
      rw [hP]; exact he
    rw [List.foldr_cons, hP, leaStep_eq]
    cases hst : lsemStepLea memAddr i.li_i s with
    | none => rw [hst] at hrun; exact absurd hrun (by simp)
    | some s₁ =>
      simp only [hst] at hrun
      have plainCase : ∀ (A : Lcmd),
          (∀ (x y : Lstate w), x.lvm = y.lvm → x.lmem = y.lmem → ∀ z,
             lsemStraightLea memAddr (rest.map Linstr.li_i) x = some z →
             ∃ t₂, lsemStraightLea memAddr (A.map Linstr.li_i) y = some t₂
               ∧ z.lvm = t₂.lvm ∧ z.lmem = t₂.lmem) →
          ∃ t₂, lsemStraightLea memAddr ((i :: A).map Linstr.li_i) t = some t₂
            ∧ s₂.lvm = t₂.lvm ∧ s₂.lmem = t₂.lmem := by
        intro A hIH
        obtain ⟨t₁, ht, hv1, hm1⟩ := lsemStepLea_congr_full memAddr i.li_i hv hm hst
        rw [List.map_cons, lsemStraightLea_cons]
        simp only [ht]
        exact hIH s₁ t₁ hv1 hm1 s₂ hrun
      cases hpend : pend with
      | none =>
        simp only [leaOut_leaPlain]
        simp only [hpend, leaOut_none] at ih'
        exact plainCase acc ih'
      | some q =>
        obtain ⟨aI, ad, ak⟩ := q
        simp only [hpend, leaOut_some] at ih'
        cases hmb : moveBase i with
        | none =>
          simp only [leaOut_leaPlain]
          exact plainCase (aI :: acc) ih'
        | some r =>
          obtain ⟨dm, sm⟩ := r
          by_cases hdm : (dm == ad) = true
          · have hdmeq : dm = ad := by simpa using hdm
            subst hdmeq
            simp only [if_pos hdm, leaOut_none]
            obtain ⟨opn1, hi1, hmv⟩ := moveBase_inv hmb
            obtain ⟨opn2, hi2, hadd⟩ := addImm_inv (hinv aI dm ak hpend)
            have hs₁ : s₁ = (s.setReg dm (s.lvm sm)).nextPc := by
              rw [hi1, lsemStepLea_move memAddr hmv s] at hst
              exact (Option.some.inj hst).symm
            have hv1 : s₁.lvm = ((t.setReg dm (t.lvm sm)).nextPc).lvm := by
              rw [hs₁]
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, hv]
            have hm1 : s₁.lmem = ((t.setReg dm (t.lvm sm)).nextPc).lmem := by
              rw [hs₁]; exact hm
            obtain ⟨u₂, hu, hu1, hu2⟩ :=
              ih' s₁ ((t.setReg dm (t.lvm sm)).nextPc) hv1 hm1 s₂ hrun
            simp only [List.map_cons, lsemStraightLea_cons, hi2,
              lsemStepLea_addImm memAddr hadd] at hu
            rw [List.map_cons, lsemStraightLea_cons]
            simp only [lsemStepLea_leaInstr hmem]
            have hveq : (((t.setReg dm (t.lvm sm)).nextPc).setReg dm
                  (((t.setReg dm (t.lvm sm)).nextPc).lvm dm + BitVec.ofNat w ak)).nextPc.lvm
                = ((t.setReg dm (t.lvm sm + BitVec.ofNat w ak)).nextPc).lvm := by
              funext r
              simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg]
              by_cases hr : r = dm <;> simp [hr]
            have hmeq : (((t.setReg dm (t.lvm sm)).nextPc).setReg dm
                  (((t.setReg dm (t.lvm sm)).nextPc).lvm dm + BitVec.ofNat w ak)).nextPc.lmem
                = ((t.setReg dm (t.lvm sm + BitVec.ofNat w ak)).nextPc).lmem := rfl
            obtain ⟨v₂, hv2run, hv2a, hv2b⟩ :=
              lsemStraightLea_congr_full memAddr (acc.map Linstr.li_i) hveq hmeq hu
            exact ⟨v₂, hv2run, hu1.trans hv2a, hu2.trans hv2b⟩
          · simp only [if_neg hdm, leaOut_leaPlain]
            exact plainCase (aI :: acc) ih'

/-- **The pass preserves the machine state on one body.** -/
theorem leaBody_lsemStraightLea {w : Nat} {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (body : Lcmd) (s s₂ : Lstate w)
    (hrun : lsemStraightLea memAddr (body.map Linstr.li_i) s = some s₂) :
    ∃ t₂, lsemStraightLea memAddr ((leaBody body).map Linstr.li_i) s = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem := by
  obtain ⟨t₂, ht, h1, h2⟩ := leaFold_sim hmem body s s rfl rfl s₂ hrun
  exact ⟨t₂, ht, h1.symm, h2.symm⟩

/-- The pass on one `Lfundef` preserves the machine state. -/
theorem leaFundef_lsemStraightLea {w : Nat} {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (f : Lfundef) (s s₂ : Lstate w)
    (hrun : lsemStraightLea memAddr (f.lfd_body.map Linstr.li_i) s = some s₂) :
    ∃ t₂, lsemStraightLea memAddr ((leaFundef f).lfd_body.map Linstr.li_i) s = some t₂
      ∧ t₂.lvm = s₂.lvm ∧ t₂.lmem = s₂.lmem :=
  leaBody_lsemStraightLea hmem f.lfd_body s s₂ hrun

/-! ## 9. Leakage

`JasminLsemRobust.linstrLeak` emits, per instruction, the opcode together with
the operand shapes, and reads no register value, no address and no branch
outcome. The trace of a body that runs to completion is therefore the
concatenation of the per-instruction leaks, a function of the instruction list
alone. Trace *equality* between input and output does not hold — a fused pair
loses two `LLeak.opn` events and gains one — and this model's notion of
constant-timeness, independence of the start state, is satisfied by every
instruction list. -/

/-- The leakage trace on the `LEA`-extended machine. -/
def lsemLeakLea {w : Nat} (memAddr : String → Option (String × Nat)) :
    List LinstrR → Lstate w → List LLeak
  | [], _ => []
  | i :: is, s =>
      linstrLeak i ++
        (match lsemStepLea memAddr i s with
          | some s' => lsemLeakLea memAddr is s'
          | none => [])

@[simp] theorem lsemLeakLea_cons {w : Nat} (memAddr : String → Option (String × Nat))
    (i : LinstrR) (is : List LinstrR) (s : Lstate w) :
    lsemLeakLea memAddr (i :: is) s =
      linstrLeak i ++
        (match lsemStepLea memAddr i s with
          | some s' => lsemLeakLea memAddr is s'
          | none => []) := rfl

/-- On a body that runs to completion the leakage trace is the concatenation of
    the per-instruction leaks, independent of the start state. -/
theorem lsemLeakLea_of_run {w : Nat} (memAddr : String → Option (String × Nat))
    (is : List LinstrR) (s s₂ : Lstate w)
    (h : lsemStraightLea memAddr is s = some s₂) :
    lsemLeakLea memAddr is s = is.flatMap linstrLeak := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [lsemStraightLea_cons] at h
    cases hst : lsemStepLea memAddr i s with
    | none => rw [hst] at h; exact absurd h (by simp)
    | some s' =>
      simp only [hst] at h
      simp only [lsemLeakLea_cons, hst, List.flatMap_cons, ih s' h]

/-- **The pass keeps the constant-time property.** Whenever the input runs from
    two start states, the output leaks the same trace from both. -/
theorem leaBody_lsemLeakLea_state_indep {w : Nat}
    {memAddr : String → Option (String × Nat)}
    (hmem : ∀ b o, memAddr (memName b o) = some (b, o)) (body : Lcmd)
    (s t s₂ t₂ : Lstate w)
    (hs : lsemStraightLea memAddr (body.map Linstr.li_i) s = some s₂)
    (ht : lsemStraightLea memAddr (body.map Linstr.li_i) t = some t₂) :
    lsemLeakLea memAddr ((leaBody body).map Linstr.li_i) s
      = lsemLeakLea memAddr ((leaBody body).map Linstr.li_i) t := by
  obtain ⟨u, hu, _, _⟩ := leaBody_lsemStraightLea hmem body s s₂ hs
  obtain ⟨v, hvv, _, _⟩ := leaBody_lsemStraightLea hmem body t t₂ ht
  rw [lsemLeakLea_of_run memAddr _ s u hu, lsemLeakLea_of_run memAddr _ t v hvv]

/-! ## 10. The byte path

`LprogBytes.encodableLcmd` holds of a body exactly when every one of its
instructions reaches the byte stream, and `LprogBytes.byteCarrying` counts the
instructions that must reach it. A fused body satisfying both, with a byte count
at least its instruction count, carries its `LEA` into the bytes. -/

/-- An address-chain slice with no indexed access, so every instruction of it and
    of its fusion is a form the byte encoder covers. -/
def demoLeaOnly : Lcmd :=
  [ ⟨0, .Lopn [.reg "R8"] "MOV:64" [.reg "RAX"]⟩,
    ⟨0, .Lopn [.reg "R8"] "ADD:64" [.reg "R8", .imm 1]⟩,
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard leaBody demoLeaOnly =
  [ (⟨0, .Lopn [.reg "R8"] "LEA:64" [.reg "mem.RAX.1"]⟩ : Linstr),
    ⟨0, .Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1]⟩ ]

#guard LprogBytes.encodableLcmd demoLeaOnly
#guard LprogBytes.encodableLcmd (leaBody demoLeaOnly)
#guard LprogBytes.byteCarrying (leaBody demoLeaOnly)
  ≤ (LprogBytes.encodeLcmd (leaBody demoLeaOnly)).length

/-! ## 11. The operand-name address decoder

`LprogAsmPrinter.resolveName` resolves a `mem.<base>.<off>` operand by dropping
the `"mem."` prefix, splitting the rest at `"."` and reading the second field as
a numeral. `memAddrOfName` is that parse as an address decoder, the concrete
instance the results of §5–§9 take for their `memAddr` parameter.

Those results carry the hypothesis `memAddr (memName b o) = some (b, o)`, a
round-trip through `String.splitOn` and `String.toNat?`. It is checked below at
the base names `moveBase` accepts and at a spread of displacements; it is not
proved for every `b` and `o`, so the results keep the hypothesis form. -/

/-- The `(base, displacement)` a `mem.<base>.<off>` operand name denotes. -/
def memAddrOfName (n : String) : Option (String × Nat) :=
  if "mem.".isPrefixOf n then
    match ((n.drop 4).toString).splitOn "." with
    | [b, off] => (String.toNat? off).map fun o => (b, o)
    | _ => none
  else none

#guard LcmdCopyPropagate.physGPs.all fun b =>
  [0, 1, 8, 4096, leaDispMax].all fun o => memAddrOfName (memName b o) == some (b, o)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdLea
