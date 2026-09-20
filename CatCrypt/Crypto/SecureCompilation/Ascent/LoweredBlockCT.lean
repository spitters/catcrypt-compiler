/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockSeq
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

/-!
# Machine constant-time for the blocks the ascent lowering emits

`JasminComRunBlockSeq.lowerBlock` compiles a straight-line `ArithBlock` to a
`List (JInstr 64)`. This module computes the machine leakage trace
(`MachineConstantTime.blockLeak`) of that output and shows it is fixed by the
`ArithBlock` alone.

## The statement

`blockAddrs` reads a leakage trace off an `ArithBlock` syntactically, taking
neither a register map, nor a name stream, nor a machine state.
`blockLeak_lowerBlock` states that the machine trace of `lowerBlock ab ρ g` run
from any `JState 64` equals `blockAddrs ab`; `lowerBlock_constant_time` is the
two-state corollary.

## The address channel and the branch channel

`MLeak` has two constructors, `branch` and `mem`. `JInstr` has no conditional
jump, so no instruction of any block emits `MLeak.branch` and the branch channel
is empty for every `List (JInstr 64)`, lowered or not. The content of the
results here is therefore entirely in the address channel: what is proved is
that the sequence of effective memory addresses does not read a register value.

## The displacement

The `load` and `store` arms of `ArithBlock` carry an index `k` and a proof of
`IsDispIndex k`, and lower to `loadMem`/`storeMem` at the constant displacement
`elemDisp k = 8 * k`. `blockLeak_lowerBlock` does not use `IsDispIndex`: the
displacement is an instruction literal whatever its size, so the leak event
`MLeak.mem base (elemDisp k)` is state-independent either way.
`IsDispIndex` is what makes that literal a legal signed 32-bit displacement,
stated as `elemDisp_mem_disp32`. A runtime index would instead be a
`loadMemIdx`/`storeMemIdx`, which is what the negative control below rules out.

## The negative control

`indexedLoadBlock` is a one-instruction block holding a register-indexed load.
`indexedLoadBlock_not_direct` shows it fails the `IsDirect` class,
`indexedLoadBlock_leaks_index` exhibits two machine states whose leakage traces
differ, and `lowerBlock_ne_indexedLoadBlock` shows `lowerBlock` never emits it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.LoweredBlockCT

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. Leakage over a concatenation -/

/-- The leakage trace of a concatenation: the first block's trace from `s`,
    then the second block's trace from the state the first block ends in. -/
theorem blockLeak_append {w : Nat} (s : JState w) (l₁ l₂ : List (JInstr w)) :
    blockLeak s (l₁ ++ l₂) = blockLeak s l₁ ++ blockLeak (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons i is ih =>
    simp only [List.cons_append, blockLeak_cons, runBlock_cons, ih, List.append_assoc]

/-! ## 2. The per-arm leakage of the lowering

The register and constant arms touch no memory, so they leak nothing; the two
memory arms leak their one constant-displacement address. -/

/-- The two-instruction arithmetic lowering is memory-free, so it leaks nothing. -/
theorem blockLeak_lowerArith2 (bop : JasminBinOp) (ra rb dst : String)
    (s : JState 64) : blockLeak s (lowerArith2 bop ra rb dst) = [] := by
  cases bop <;> rfl

/-- The one-input lowering is memory-free, so it leaks nothing. -/
theorem blockLeak_toJInstr (uop : ArithUn) (dst a : String) (s : JState 64) :
    blockLeak s (uop.toJInstr dst a) = [] := by
  cases uop <;> rfl

/-- The constant lowering is memory-free, so it leaks nothing. -/
theorem blockLeak_lowerConst (n : Nat) (dst : String) (s : JState 64) :
    blockLeak s (lowerConst n dst) = [] := rfl

/-- The element-load lowering leaks the single address `base + 8·k`. -/
theorem blockLeak_lowerLoad (dst base : String) (k : Nat) (s : JState 64) :
    blockLeak s (lowerLoad dst base k) = [.mem base (elemDisp k)] := rfl

/-- The element-store lowering leaks the single address `base + 8·k`. -/
theorem blockLeak_lowerStore (base src : String) (k : Nat) (s : JState 64) :
    blockLeak s (lowerStore base src k) = [.mem base (elemDisp k)] := rfl

/-! ## 3. The syntactic trace of a block -/

/-- The leakage trace read off an `ArithBlock`: one `MLeak.mem base (elemDisp k)`
    per element load and per element store, in order, and nothing for the
    register, constant and return arms. It takes no register map, no name stream
    and no machine state. -/
def blockAddrs : {Γ : Ctxt jasminDialect} → ArithBlock Γ → List MLeak
  | _, .ret _ => []
  | _, .op _ _ _ _ rest => blockAddrs rest
  | _, .un _ _ _ rest => blockAddrs rest
  | _, .cnst _ rest => blockAddrs rest
  | _, .load _ k _ base _ _ rest => .mem base (elemDisp k) :: blockAddrs rest
  | _, .store _ k _ base _ _ _ rest => .mem base (elemDisp k) :: blockAddrs rest

/-! ## 4. The main theorem -/

/-- **The machine leakage trace of a lowered block is its syntactic trace.** For
    every straight-line `ArithBlock`, every register map, every name stream and
    every initial machine state, the trace `blockLeak` records of
    `lowerBlock ab ρ g` equals `blockAddrs ab`, which depends on the block alone.

    Proved by structural induction on the block, splitting each arm's lowering
    off the concatenation with `blockLeak_append` and rewriting its leak with
    the per-arm lemmas of section 2. -/
theorem blockLeak_lowerBlock : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    blockLeak s (lowerBlock ab ρ g) = blockAddrs ab
  | _, .ret _, _, _, _ => rfl
  | _, .op bop hbop a b rest, ρ, g, s => by
    rw [lowerBlock, blockLeak_append, blockLeak_lowerArith2, blockAddrs,
      List.nil_append]
    exact blockLeak_lowerBlock rest _ _ _
  | _, .un uop huop a rest, ρ, g, s => by
    rw [lowerBlock, blockLeak_append, blockLeak_toJInstr, blockAddrs,
      List.nil_append]
    exact blockLeak_lowerBlock rest _ _ _
  | _, .cnst n rest, ρ, g, s => by
    rw [lowerBlock, blockLeak_append, blockLeak_lowerConst, blockAddrs,
      List.nil_append]
    exact blockLeak_lowerBlock rest _ _ _
  | _, .load n k hk base arr i rest, ρ, g, s => by
    rw [lowerBlock, blockLeak_append, blockLeak_lowerLoad, blockAddrs,
      List.singleton_append]
    exact congrArg _ (blockLeak_lowerBlock rest _ _ _)
  | _, .store n k hk base arr i src rest, ρ, g, s => by
    rw [lowerBlock, blockLeak_append, blockLeak_lowerStore, blockAddrs,
      List.singleton_append]
    exact congrArg _ (blockLeak_lowerBlock rest _ _ _)

/-- **Every block the ascent lowers is constant-time at the machine level.** The
    machine leakage trace of `lowerBlock ab ρ g` is the same from any two initial
    states `s₁ s₂`, which may differ in every register and every memory cell.
    The observable memory-address sequence therefore carries no register value,
    in particular no secret. -/
theorem lowerBlock_constant_time {Γ : Ctxt jasminDialect} (ab : ArithBlock Γ)
    (ρ : RegMapG Γ) (g : Nat → String) (s₁ s₂ : JState 64) :
    blockLeak s₁ (lowerBlock ab ρ g) = blockLeak s₂ (lowerBlock ab ρ g) := by
  rw [blockLeak_lowerBlock ab ρ g s₁, blockLeak_lowerBlock ab ρ g s₂]

/-- Every instruction a lowered block emits is in the direct-addressing class
    `MachineConstantTime.IsDirect`: none of them is a register-indexed memory
    access. -/
theorem lowerBlock_isDirect : {Γ : Ctxt jasminDialect} → (ab : ArithBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → ∀ i ∈ lowerBlock ab ρ g, IsDirect i
  | _, .ret _, _, _ => by intro i hi; simp [lowerBlock] at hi
  | _, .op bop hbop a b rest, ρ, g => by
    intro i hi
    rw [lowerBlock, List.mem_append] at hi
    rcases hi with hi | hi
    · have h2 : i = .mov (g 0) (.reg (ρ a))
          ∨ i = bopToJInstr bop (g 0) (.reg (ρ b)) := by
        simpa [lowerArith2] using hi
      rcases h2 with rfl | rfl
      · trivial
      · cases bop <;> trivial
    · exact lowerBlock_isDirect rest _ _ i hi
  | _, .un uop huop a rest, ρ, g => by
    intro i hi
    rw [lowerBlock, List.mem_append] at hi
    rcases hi with hi | hi
    · revert hi
      cases uop <;>
        (simp only [ArithUn.toJInstr, List.mem_cons, List.not_mem_nil, or_false]
         intro h2
         rcases h2 with rfl | rfl <;> trivial)
    · exact lowerBlock_isDirect rest _ _ i hi
  | _, .cnst n rest, ρ, g => by
    intro i hi
    rw [lowerBlock, List.mem_append] at hi
    rcases hi with hi | hi
    · simp only [lowerConst, List.mem_singleton] at hi; subst hi; trivial
    · exact lowerBlock_isDirect rest _ _ i hi
  | _, .load n k hk base arr j rest, ρ, g => by
    intro i hi
    rw [lowerBlock, List.mem_append] at hi
    rcases hi with hi | hi
    · simp only [lowerLoad, List.mem_singleton] at hi; subst hi; trivial
    · exact lowerBlock_isDirect rest _ _ i hi
  | _, .store n k hk base arr j src rest, ρ, g => by
    intro i hi
    rw [lowerBlock, List.mem_append] at hi
    rcases hi with hi | hi
    · simp only [lowerStore, List.mem_singleton] at hi; subst hi; trivial
    · exact lowerBlock_isDirect rest _ _ i hi

/-! ## 5. The displacement bound

`IsDispIndex` does not enter the constant-time argument; it bounds the
displacement literal to the signed 32-bit field of the `[base + disp32]`
encoding. -/

/-- The displacement of a covered element index is a non-negative signed 32-bit
    value, the field the `[base + disp32]` encoding holds. -/
theorem elemDisp_mem_disp32 {k : Nat} (hk : IsDispIndex k) :
    0 ≤ elemDisp k ∧ elemDisp k < (2 : Int) ^ 31 := by
  have h : 8 * k < 2 ^ 31 := hk
  have hlt : ((8 * k : Nat) : Int) < ((2 ^ 31 : Nat) : Int) := Int.ofNat_lt.mpr h
  simp only [elemDisp]
  exact ⟨Int.natCast_nonneg _, by simpa using hlt⟩

/-! ## 6. The negative control

The predicate rejects a register-indexed access, and the rejection is witnessed
by two machine states with different leakage traces. -/

/-- A one-instruction block holding a register-indexed load: the effective
    address is `base + 8 · (value in idx)`. -/
def indexedLoadBlock (dst base idx : String) : List (JInstr 64) :=
  [ .loadMemIdx dst base idx 8 ]

/-- `indexedLoadBlock` is outside the direct-addressing class. -/
theorem indexedLoadBlock_not_direct (dst base idx : String) :
    ¬ ∀ i ∈ indexedLoadBlock dst base idx, IsDirect i := by
  intro h
  exact h (.loadMemIdx dst base idx 8) (by simp [indexedLoadBlock])

/-- The machine state whose registers are all zero. -/
def zeroState : JState 64 := { regs := fun _ => 0 }

/-- The machine state whose registers are all zero except `"idx"`, which is one. -/
def oneIdxState : JState 64 := { regs := fun r => if r = "idx" then 1 else 0 }

/-- **The negative control.** The leakage traces of `indexedLoadBlock` from
    `zeroState` and from `oneIdxState` differ: the two states disagree only on
    the index register, and the emitted address follows that disagreement. So
    the block is not constant-time, and the constant-time predicate proved of
    `lowerBlock` in section 4 rejects it. -/
theorem indexedLoadBlock_leaks_index :
    blockLeak zeroState (indexedLoadBlock "d" "base" "idx")
      ≠ blockLeak oneIdxState (indexedLoadBlock "d" "base" "idx") := by
  decide

/-- The lowering never emits a register-indexed access: no `ArithBlock`, register
    map and name stream lower to `indexedLoadBlock`. -/
theorem lowerBlock_ne_indexedLoadBlock {Γ : Ctxt jasminDialect} (ab : ArithBlock Γ)
    (ρ : RegMapG Γ) (g : Nat → String) (dst base idx : String) :
    lowerBlock ab ρ g ≠ indexedLoadBlock dst base idx := by
  intro h
  refine indexedLoadBlock_not_direct dst base idx ?_
  rw [← h]
  exact lowerBlock_isDirect ab ρ g

end CatCrypt.Crypto.SecureCompilation.Ascent.LoweredBlockCT
