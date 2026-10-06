/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfgTactic

/-!
# Three examples of the cut-point rule at the x86 instruction set

Three `Lprog` programs over the instruction-set record `x86Isa`, written on virtual
registers, each with a pure specification. They are examples of the cut-point rule
`IsaCfg.corresIsa_of_cuts` of `Ascent.CorresIsaCfgTactic`, and each proof is the entry
condition followed by one run of `isa_steps` per segment.

* `absProg` computes the absolute value of the register `x`: the sign bit is shifted into
  `t`, a conditional jump on `t` selects the negation. Its cut points are the entry and the
  label of the negation block, and both branches are in the specification.
* `idxAliasProg` writes `u` to `a[i]` and `v` to `a[j]` and reads `a[i]` into `r`, for an
  array `a` of `n` words and in-range indices `i` and `j`. The read value is `v` when
  `i = j` and `u` otherwise. It is one straight-line segment.
* `loopProg` multiplies the register `n` by three with a loop of three blocks (head, body,
  exit) that adds `3` to `r` and decrements `n` until `n` is zero. Its cut points are the
  entry and the loop head, with the invariant `r = 3 * (n₀ - n)` and the measure `n`. The
  fuel is `4 * (M + 2)` for a bound `M` on the entry word of `n`, and `loop_run` takes
  `M` the entry word.

The loop is a simpler relative of the x64 example `P3` of the Kraken verified-assembly
framework. The other two programs are not its examples `Cond` and `Alias`: `Cond` is a
decrement followed by a jump on the zero flag, with a postcondition for one branch, and
`Alias` is two labels at one address.

The machine model restricts what the examples express. The flag compare of the flag
machine records equality only, and a conditional jump on a register tests it for non-zero,
so the examples branch on a register and not on the flags of an arithmetic instruction.
An array is a named register holding a function on indices, so two stores alias through
equal indices of one array and not through two pointers to one address. No stack is
mapped: the programs use registers only.

The side relation of each example pins the program counter to a component of the abstract
state, since `CorresM` has one relation before and after the run. The theorems `abs_run`,
`idxAlias_run` and `loop_run` restate each correspondence on a machine state.

## Main results

* `abs_corresIsa`, `abs_run`: the absolute value.
* `idxAlias_corresIsa`, `idxAlias_run`: two stores through possibly equal indices.
* `loop_corresIsa`, `loop_run`: the multiplication loop, with fuel linear in the entry
  word of `n`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCfgDemo

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## The absolute value by a conditional jump -/

/-- The absolute value of `x`: `t := x >>> 63`; when `t` is non-zero jump to label `1`,
    which negates `x`; otherwise jump to the end, label `2`. -/
def absProg (fn : String) : LprogM := singletonProgM fn
  [ shrI "t" "x" 63,
    (.Lcond (.reg "t") 1, .reg none),
    (.Lgoto (fn, 2), .reg none),
    (.Llabel .internal 1, .reg none),
    negI "x" "x",
    (.Llabel .internal 2, .reg none) ]

/-- The absolute value of a two's-complement word. -/
def absSpec (v : BitVec 64) : BitVec 64 := if v.msb then -v else v

/-- The state is in `fn` at the counter of the abstract pair and holds its word in `x`. -/
def absSR (fn : String) (t : LstateMF) (a : BitVec 64 × Nat) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2 ∧ t.prog.base.reg.lvm "x" = ⟨64, a.1⟩

/-- The invariants of `absProg`: `x` holds the entry word, negative at label `1`. -/
def absInv : Option LLabel → LstateMF → BitVec 64 × Nat → Prop
  | none, m, a => m.prog.base.reg.lvm "x" = ⟨64, a.1⟩
  | some _, m, a => m.prog.base.reg.lvm "x" = ⟨64, a.1⟩ ∧ a.1.msb = true

/-- **The absolute value.** From counter `0`, `absProg` halts at counter `6` with the
    absolute value of the entry word in `x`. -/
theorem abs_corresIsa (fn : String) :
    CorresIsa x86Isa (absProg fn) (absSR fn) (fun a => a.2 = 0)
      (fun a => (absSpec a.1, 6)) (3 * (1 + 1)) := by
  isa_cutpoints absInv, (fun c _ _ => if c = none then 1 else 0), 3, 1 at [1]
  · rintro m ⟨v, k⟩ ⟨hfn, hpc, hx⟩ hk
    exact ⟨⟨hfn, hpc.trans hk⟩, hx, Nat.le_refl _⟩
  · rintro m ⟨v, k⟩ ⟨hfn, hpc⟩ (hx : m.prog.base.reg.lvm "x" = ⟨64, v⟩)
    isa_steps
    · isa_cut 1 <;> simp [absInv, *]
      bv_decide
    · isa_exit
      simp [absSR, absProg, absSpec, *]
      bv_decide
  · rintro m ⟨v, k⟩ ⟨hfn, hpc⟩ ⟨hx, hmsb⟩
    isa_steps
    isa_exit
    simp [absSR, absProg, absSpec, *]

/-- `abs_corresIsa` on a machine state: from counter `0` in `fn` with the word `v` in
    `x`, the run of `absProg fn` returns a state with the absolute value of `v` in `x`. -/
theorem abs_run (fn : String) (s : LstateMF) (v : BitVec 64) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hx : s.prog.base.reg.lvm "x" = ⟨64, v⟩) :
    ∃ t, x86Isa.lsemFuelMemF (absProg fn) 6 s = some t ∧
      t.prog.base.reg.lvm "x" = ⟨64, absSpec v⟩ := by
  obtain ⟨t, hrun, hSR⟩ := abs_corresIsa fn s (v, 0) ⟨hfn, hpc, hx⟩ rfl
  exact ⟨t, hrun, hSR.2.2⟩

/-! ## Two stores through possibly equal indices -/

/-- `a[i] := u; a[j] := v; r := a[i]` on an array `a` of `n` words. -/
def idxAliasProg (fn : String) (n : Nat) : LprogM := singletonProgM fn
  [ storeI n "a" "a" "i" "u", storeI n "a" "a" "j" "v", loadI n "r" "a" "i" ]

/-- The abstract state of `idxAliasProg`: the array, the two indices, the two stored
    words, the word of `r` and the program counter. -/
structure IdxAliasSt (n : Nat) where
  /-- The array `a`. -/
  arr : Fin n → BitVec 64
  /-- The index `i`. -/
  i : BitVec 64
  /-- The index `j`. -/
  j : BitVec 64
  /-- The word `u`. -/
  u : BitVec 64
  /-- The word `v`. -/
  v : BitVec 64
  /-- The word of `r`. -/
  r : BitVec 64
  /-- The program counter. -/
  pc : Nat

/-- The state is in `fn` at the counter of the abstract state and holds its array and its
    five words. -/
def idxAliasSR (fn : String) (n : Nat) (t : LstateMF) (a : IdxAliasSt n) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.pc ∧ t.prog.base.getArr "a" 64 n = some a.arr ∧
    t.prog.base.reg.lvm "i" = ⟨64, a.i⟩ ∧ t.prog.base.reg.lvm "j" = ⟨64, a.j⟩ ∧
    t.prog.base.reg.lvm "u" = ⟨64, a.u⟩ ∧ t.prog.base.reg.lvm "v" = ⟨64, a.v⟩ ∧
    t.prog.base.reg.lvm "r" = ⟨64, a.r⟩

/-- The specification of `idxAliasProg`: both stores applied to the array, and in `r` the
    word `v` when the indices are equal and `u` otherwise. -/
def idxAliasSpec {n : Nat} (a : IdxAliasSt n) : IdxAliasSt n :=
  { a with arr := stackSet (stackSet a.arr a.i.toNat a.u) a.j.toNat a.v,
           r := if a.i = a.j then a.v else a.u, pc := 3 }

/-- The read after the two stores, by the case split on the equality of the indices. -/
theorem stackGet_idxAlias {n : Nat} (arr : Fin n → BitVec 64) (i j u v : BitVec 64)
    (hi : i.toNat < n) (hj : j.toNat < n) :
    stackGet (stackSet (stackSet arr i.toNat u) j.toNat v) i.toNat = if i = j then v else u := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [stackGet, stackSet, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      by_cases h : i = j
      · subst h; simp
      · have hne : i.toNat ≠ j.toNat := fun hc => h (BitVec.eq_of_toNat_eq hc)
        simp [h, Fin.ext_iff, hne]

/-- **Two indexed stores.** From counter `0` with in-range indices, `idxAliasProg` halts
    at counter `3` with both stores applied and, in `r`, `v` when `i = j` and `u`
    otherwise. -/
theorem idxAlias_corresIsa (fn : String) (n : Nat) :
    CorresIsa x86Isa (idxAliasProg fn n) (idxAliasSR fn n)
      (fun a => a.pc = 0 ∧ a.i.toNat < n ∧ a.j.toNat < n) idxAliasSpec (3 * (0 + 1)) := by
  isa_cutpoints (fun _ m a => idxAliasSR fn n m a ∧ a.i.toNat < n ∧ a.j.toNat < n),
    (fun _ _ _ => 0), 3, 0 at []
  · rintro m a hSR ⟨hk, hi, hj⟩
    exact ⟨⟨hSR.1, hSR.2.1.trans hk⟩, ⟨hSR, hi, hj⟩, Nat.le_refl _⟩
  · rintro m a ⟨hfn, hpc⟩ ⟨⟨-, -, harr, hi, hj, hu, hv, hr⟩, hin, hjn⟩
    isa_steps
    isa_exit
    simp [idxAliasSR, idxAliasSpec, idxAliasProg,
      stackGet_idxAlias a.arr a.i a.j a.u a.v hin hjn, *]

/-- `idxAlias_corresIsa` on a machine state: from counter `0` in `fn` with the array `arr`
    in `a`, in-range indices `i` and `j` and the words `u` and `v`, the run of
    `idxAliasProg` returns a state with `v` in `r` when `i = j` and `u` otherwise. -/
theorem idxAlias_run (fn : String) (n : Nat) (s : LstateMF) (arr : Fin n → BitVec 64)
    (i j u v r : BitVec 64) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (harr : s.prog.base.getArr "a" 64 n = some arr)
    (hi : s.prog.base.reg.lvm "i" = ⟨64, i⟩) (hj : s.prog.base.reg.lvm "j" = ⟨64, j⟩)
    (hu : s.prog.base.reg.lvm "u" = ⟨64, u⟩) (hv : s.prog.base.reg.lvm "v" = ⟨64, v⟩)
    (hr : s.prog.base.reg.lvm "r" = ⟨64, r⟩) (hin : i.toNat < n) (hjn : j.toNat < n) :
    ∃ t, x86Isa.lsemFuelMemF (idxAliasProg fn n) 3 s = some t ∧
      t.prog.base.reg.lvm "r" = ⟨64, if i = j then v else u⟩ ∧
      t.prog.base.getArr "a" 64 n = some (stackSet (stackSet arr i.toNat u) j.toNat v) := by
  obtain ⟨t, hrun, hSR⟩ := idxAlias_corresIsa fn n s ⟨arr, i, j, u, v, r, 0⟩
    ⟨hfn, hpc, harr, hi, hj, hu, hv, hr⟩ ⟨rfl, hin, hjn⟩
  exact ⟨t, hrun, hSR.2.2.2.2.2.2.2, hSR.2.2.1⟩

/-! ## A loop of three blocks -/

/-- `r := 0`; at the head, label `1`, jump to the body, label `2`, when `n` is non-zero and
    to the exit, label `3`, otherwise; the body adds `3` to `r`, decrements `n` and jumps
    to the head. -/
def loopProg (fn : String) : LprogM := singletonProgM fn
  [ movI "r" 0,
    (.Llabel .internal 1, .reg none),
    (.Lcond (.reg "n") 2, .reg none),
    (.Lgoto (fn, 3), .reg none),
    (.Llabel .internal 2, .reg none),
    addI "r" "r" 3,
    subI "n" "n" 1,
    (.Lgoto (fn, 1), .reg none),
    (.Llabel .internal 3, .reg none) ]

/-- The state is in `fn` at the counter of the abstract triple and holds its words in `n`
    and `r`. -/
def loopSR (fn : String) (t : LstateMF) (a : BitVec 64 × BitVec 64 × Nat) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2.2 ∧ t.prog.base.reg.lvm "n" = ⟨64, a.1⟩ ∧
    t.prog.base.reg.lvm "r" = ⟨64, a.2.1⟩

/-- The invariants of `loopProg`: at the entry `n` holds the entry word `n₀`; at the head
    `n` holds a word `k` and `r` holds `3 * (n₀ - k)`. -/
def loopInv : Option LLabel → LstateMF → BitVec 64 × BitVec 64 × Nat → Prop
  | none, m, a => m.prog.base.reg.lvm "n" = ⟨64, a.1⟩
  | some _, m, a => ∃ k : BitVec 64, m.prog.base.reg.lvm "n" = ⟨64, k⟩ ∧
      m.prog.base.reg.lvm "r" = ⟨64, 3 * (a.1 - k)⟩

/-- The measure of `loopProg`: the word of `n` at the head, and the successor of the entry
    word at the entry. -/
def loopMeasure : Option LLabel → LstateMF → BitVec 64 × BitVec 64 × Nat → Nat
  | none, _, a => a.1.toNat + 1
  | some _, m, _ => wordNat (m.prog.base.reg.lvm "n")

/-- **The loop.** From counter `0` with the entry word of `n` at most `M`, `loopProg` halts
    at counter `9` within `4 * (M + 2)` steps, with `n` zero and three times the entry
    word of `n` in `r`. At `M = 2 ^ 64 - 1` the bound on the entry word holds of every
    word. -/
theorem loop_corresIsa (fn : String) (M : Nat) :
    CorresIsa x86Isa (loopProg fn) (loopSR fn) (fun a => a.2.2 = 0 ∧ a.1.toNat ≤ M)
      (fun a => (0, 3 * a.1, 9)) (4 * (M + 2)) := by
  isa_cutpoints loopInv, loopMeasure, 4, (M + 1) at [1]
  · rintro m ⟨n0, r0, pc⟩ ⟨hfn, hpc, hn, -⟩ ⟨hk, hM⟩
    exact ⟨⟨hfn, hpc.trans hk⟩, hn, Nat.succ_le_succ hM⟩
  · rintro m ⟨n0, r0, pc⟩ ⟨hfn, hpc⟩ (hn : m.prog.base.reg.lvm "n" = ⟨64, n0⟩)
    isa_steps
    isa_cut 1 <;> simp [loopInv, loopMeasure, *]
  · rintro m ⟨n0, r0, pc⟩ ⟨hfn, hpc⟩ ⟨k, hn, hr⟩
    isa_steps
    · isa_steps
      isa_cut 1 <;> simp [loopInv, loopMeasure, *]
      · bv_decide
      · bv_omega
    · isa_exit
      simp [loopSR, loopProg, *]

/-- `loop_corresIsa` on a machine state: from counter `0` in `fn` with the word `n` in `n`,
    the run of `loopProg fn` with fuel `4 * (n.toNat + 2)` returns a state with `3 * n` in
    `r` and zero in `n`. -/
theorem loop_run (fn : String) (s : LstateMF) (n r : BitVec 64) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hn : s.prog.base.reg.lvm "n" = ⟨64, n⟩)
    (hr : s.prog.base.reg.lvm "r" = ⟨64, r⟩) :
    ∃ t, x86Isa.lsemFuelMemF (loopProg fn) (4 * (n.toNat + 2)) s = some t ∧
      t.prog.base.reg.lvm "r" = ⟨64, 3 * n⟩ ∧ t.prog.base.reg.lvm "n" = ⟨64, 0#64⟩ := by
  obtain ⟨t, hrun, hSR⟩ :=
    loop_corresIsa fn n.toNat s (n, r, 0) ⟨hfn, hpc, hn, hr⟩ ⟨rfl, Nat.le_refl _⟩
  exact ⟨t, hrun, hSR.2.2.2, hSR.2.2.1⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCfgDemo
