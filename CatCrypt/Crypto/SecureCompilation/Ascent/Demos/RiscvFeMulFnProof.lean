/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresRiscvMem
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof

/-!
# The RV64 Curve25519 multiply as a buffer function, at its encoded bytes

`RiscvMulBytesProof.feMulPhys` computes the field product register to register, with `x`
in `a0..a3`, `y` in `a4..a7`, and `s0..s11` as scratch. `feMulFn` wraps it into a buffer
function over the memory layer `RiscvMem64`: `z ← x · y mod p25519` with the pointers
`z` in `a0`, `x` in `a1` and `y` in `a2`. It opens a 112-byte frame below `sp`, saves
`s0..s11` and the output pointer there, loads the two operands, runs `feMulPhys`,
reloads the output pointer into `t0`, stores the four result limbs, restores
`s0..s11` and closes the frame.

## Main results

* `feMulFn_run`: for every machine state whose frame is disjoint from the three buffers,
  the run leaves the product in the `z` buffer (`memLimbs4`), restores `s0..s11` and `sp`,
  and leaves every byte outside the frame and the `z` buffer. `x` and `y` may overlap
  each other and `z`.
* `feMulFnBytes_correct`: the same over the 1073 instructions decoded from the encoded
  bytes (`RiscvMem64.encodeXBlock64`).

## Structure

`pro_run`, `loads_run`, `storeZ_run` and `epilogue_run` state each segment; the stack
slots are read back with `read64_writeSlots_mem` and the buffers across the frame with
`read64_writeSlots_sep`, from the disjointness hypotheses `Sep`.

## Scope

The block ends at the frame close: the return (`jalr zero, 0(ra)`) is control flow, which
the RV64 model does not have, so `ra` is neither used nor written. That the block meets
the rest of the RISC-V psABI (16-byte `sp` alignment at entry, which the frame size
preserves; argument registers beyond `a0..a2`, which it clobbers as the ABI allows) is
read off the code, not stated as a theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvMulBytesProof
open CatCrypt.Crypto.SecureCompilation.Memory64
  (AMem read64 write64 InRange8 Disjoint8 read64_write64_same read64_write64_of_disjoint
    write64_of_not_inRange)

/-! ## Memory ranges -/

/-- The ranges `[a, a + n)` and `[b, b + m)` are disjoint modulo `2^64`. -/
def Sep (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Prop :=
  n ≤ (b - a).toNat ∧ m ≤ (a - b).toNat

theorem out_of_sep {a b x : BitVec 64} {n m : Nat} (h : Sep a n b m) (hx : (x - b).toNat < m) :
    n ≤ (x - a).toNat := by
  obtain ⟨h1, h2⟩ := h
  have := a.isLt; have := b.isLt; have := x.isLt
  simp only [BitVec.toNat_sub] at h1 h2 hx ⊢
  omega

theorem not_inRange_of_out {f x : BitVec 64} {n o : Nat} (hx : n ≤ (x - f).toNat)
    (ho : o + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ InRange8 (f + BitVec.ofNat 64 o) x := by
  have := f.isLt; have := x.isLt
  simp only [InRange8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at hx ⊢
  omega

theorem sep_word {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) (k : Nat) (hk : k + 8 ≤ m)
    (hm : m < 2 ^ 64) : Sep a n (b + BitVec.ofNat 64 k) 8 := by
  obtain ⟨h1, h2⟩ := h
  have := a.isLt; have := b.isLt
  simp only [Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
  omega

/-- Eight-byte words at offsets at least eight apart from one base are disjoint. -/
theorem disjoint8_ofNat (p : BitVec 64) (o o' : Nat) (h : o + 8 ≤ o' ∨ o' + 8 ≤ o)
    (h1 : o < 2 ^ 32) (h2 : o' < 2 ^ 32) :
    Disjoint8 (p + BitVec.ofNat 64 o) (p + BitVec.ofNat 64 o') := by
  have := p.isLt
  simp only [Disjoint8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem read64_congr (m m' : AMem) (a : BitVec 64)
    (h : ∀ j < 8, m' (a + BitVec.ofNat 64 j) = m (a + BitVec.ofNat 64 j)) :
    read64 m' a = read64 m a := by
  have h0 := h 0 (by decide)
  simp only [BitVec.add_zero] at h0
  simp only [read64, h0, h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide)]

/-! ## A run of stores at one base -/

/-- Store each `(o, v)` at `base + o`, in order. -/
def writeSlots (m : AMem) (base : BitVec 64) : List (Nat × BitVec 64) → AMem
  | [] => m
  | (o, v) :: rest => writeSlots (write64 m (base + BitVec.ofNat 64 o) v) base rest

theorem writeSlots_out (m : AMem) (base x : BitVec 64) (l : List (Nat × BitVec 64))
    (h : ∀ p ∈ l, ¬ InRange8 (base + BitVec.ofNat 64 p.1) x) :
    writeSlots m base l x = m x := by
  induction l generalizing m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o, v⟩ := p
    simp only [writeSlots]
    rw [ih _ fun q hq => h q (List.mem_cons_of_mem _ hq),
      write64_of_not_inRange _ _ _ _ (h (o, v) List.mem_cons_self)]

/-- A word outside the range `[base, base + n)` reads the same after the stores. -/
theorem read64_writeSlots_sep (m : AMem) (base a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64)
    (l : List (Nat × BitVec 64)) (hl : ∀ p ∈ l, p.1 + 8 ≤ n) (h : Sep base n a 8) :
    read64 (writeSlots m base l) a = read64 m a := by
  refine read64_congr _ _ _ fun j hj => writeSlots_out _ _ _ _ fun p hp =>
    not_inRange_of_out (out_of_sep h ?_) (hl p hp) hn
  have := a.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A word at a slot offset disjoint from every store reads the same. -/
theorem read64_writeSlots_disj (m : AMem) (base : BitVec 64) (o : Nat) (ho : o < 2 ^ 32)
    (l : List (Nat × BitVec 64)) (hl : ∀ p ∈ l, (p.1 + 8 ≤ o ∨ o + 8 ≤ p.1) ∧ p.1 < 2 ^ 32) :
    read64 (writeSlots m base l) (base + BitVec.ofNat 64 o) = read64 m (base + BitVec.ofNat 64 o) := by
  induction l generalizing m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨o', v⟩ := p
    simp only [writeSlots]
    rw [ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq)]
    obtain ⟨h1, h2⟩ := hl (o', v) List.mem_cons_self
    exact read64_write64_of_disjoint _ _ _ _ (disjoint8_ofNat base o' o (by omega) h2 ho)

/-- **Slot readback.** -/
theorem read64_writeSlots_at (m : AMem) (base : BitVec 64) (l1 l2 : List (Nat × BitVec 64))
    (o : Nat) (v : BitVec 64) (ho : o < 2 ^ 32)
    (hl : ∀ p ∈ l2, (p.1 + 8 ≤ o ∨ o + 8 ≤ p.1) ∧ p.1 < 2 ^ 32) :
    read64 (writeSlots m base (l1 ++ (o, v) :: l2)) (base + BitVec.ofNat 64 o) = v := by
  induction l1 generalizing m with
  | nil =>
    simp only [List.nil_append, writeSlots]
    rw [read64_writeSlots_disj _ _ _ ho _ hl, read64_write64_same]
  | cons p rest ih =>
    obtain ⟨o', v'⟩ := p
    exact ih _

/-- **Slot readback by membership**, for distinct offsets at least eight apart. -/
theorem read64_writeSlots_mem (m : AMem) (base : BitVec 64) (l : List (Nat × BitVec 64))
    (o : Nat) (v : BitVec 64) (hmem : (o, v) ∈ l) (hnd : (l.map Prod.fst).Nodup)
    (hd : ∀ a ∈ l.map Prod.fst, ∀ b ∈ l.map Prod.fst, a ≠ b → a + 8 ≤ b ∨ b + 8 ≤ a)
    (hs : ∀ a ∈ l.map Prod.fst, a < 2 ^ 32) :
    read64 (writeSlots m base l) (base + BitVec.ofNat 64 o) = v := by
  induction l generalizing m with
  | nil => exact absurd hmem List.not_mem_nil
  | cons p rest ih =>
    obtain ⟨o', v'⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, forall_eq_or_imp] at hnd hd hs
    simp only [writeSlots]
    by_cases h : (o, v) ∈ rest
    · exact ih _ h hnd.2 (fun a ha b hb hab => hd.2 a ha |>.2 b hb hab) hs.2
    · obtain ⟨rfl, rfl⟩ : o = o' ∧ v = v' := by
        rcases List.mem_cons.1 hmem with h' | h'
        · exact Prod.mk.inj h'
        · exact absurd h' h
      rw [read64_writeSlots_disj _ _ _ hs.1 _ fun q hq => ⟨?_, hs.2 _ (List.mem_map_of_mem hq)⟩,
        read64_write64_same]
      have hq' := List.mem_map_of_mem (f := Prod.fst) hq
      have hne : q.1 ≠ o := fun he => hnd.1 (he ▸ hq')
      rcases hd.1.2 q.1 hq' (Ne.symm hne) with h1 | h1 <;> omega

/-! ## The function -/

/-- The callee-saved registers the field blocks use. -/
def frameSlots : List (String × Nat) :=
  [("s0", 0), ("s1", 8), ("s2", 16), ("s3", 24), ("s4", 32), ("s5", 40), ("s6", 48), ("s7", 56), ("s8", 64), ("s9", 72), ("s10", 80), ("s11", 88)]

/-- Open a 112-byte frame and save `s0..s11` and the output pointer `a0` in it. -/
def prologue : List XInst64 :=
  [.m (.addi "sp" "sp" (BitVec.ofInt 12 (-112))),
    .sd "s0" "sp" 0,
    .sd "s1" "sp" 8,
    .sd "s2" "sp" 16,
    .sd "s3" "sp" 24,
    .sd "s4" "sp" 32,
    .sd "s5" "sp" 40,
    .sd "s6" "sp" 48,
    .sd "s7" "sp" 56,
    .sd "s8" "sp" 64,
    .sd "s9" "sp" 72,
    .sd "s10" "sp" 80,
    .sd "s11" "sp" 88,
    .sd "a0" "sp" 96]

/-- Load `y` (pointer `a2`) into `a4..a7`, then `x` (pointer `a1`) into `a0..a3`. -/
def loads : List XInst64 :=
  [.ld "a4" "a2" 0, .ld "a5" "a2" 8, .ld "a6" "a2" 16, .ld "a7" "a2" 24,
    .ld "a0" "a1" 0, .ld "a2" "a1" 16, .ld "a3" "a1" 24, .ld "a1" "a1" 8]

/-- Reload the output pointer into `t0` and store `a0..a3` through it. -/
def storeZ : List XInst64 :=
  [.ld "t0" "sp" 96, .sd "a0" "t0" 0, .sd "a1" "t0" 8, .sd "a2" "t0" 16, .sd "a3" "t0" 24]

/-- Restore `s0..s11` and close the frame. -/
def epilogue : List XInst64 :=
  [.ld "s0" "sp" 0,
    .ld "s1" "sp" 8,
    .ld "s2" "sp" 16,
    .ld "s3" "sp" 24,
    .ld "s4" "sp" 32,
    .ld "s5" "sp" 40,
    .ld "s6" "sp" 48,
    .ld "s7" "sp" 56,
    .ld "s8" "sp" 64,
    .ld "s9" "sp" 72,
    .ld "s10" "sp" 80,
    .ld "s11" "sp" 88,
    .m (.addi "sp" "sp" 112)]

/-- **The field multiply as a buffer function**: `z ← x · y mod p25519` with `z` at `a0`,
    `x` at `a1` and `y` at `a2`, preserving `s0..s11` and `sp`. -/
def feMulFn : List XInst64 := prologue ++ loads ++ feMulPhys.map .m ++ storeZ ++ epilogue

/-- The four little-endian doublewords from `p`. -/
def memLimbs4 (m : AMem) (p : BitVec 64) : Nat :=
  (read64 m (p + BitVec.ofNat 64 0)).toNat + 2 ^ 64 * (read64 m (p + BitVec.ofNat 64 8)).toNat
    + 2 ^ 128 * (read64 m (p + BitVec.ofNat 64 16)).toNat
    + 2 ^ 192 * (read64 m (p + BitVec.ofNat 64 24)).toNat

theorem se12 : ∀ k ∈ [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 112],
    (BitVec.ofNat 12 k).signExtend 64 = BitVec.ofNat 64 k := by decide

theorem seNeg : (BitVec.ofInt 12 (-112)).signExtend 64 = BitVec.ofInt 64 (-112) := by decide

/-- The saved values, in slot order. -/
def saved (R : String → BitVec 64) : List (Nat × BitVec 64) :=
  [(0, R "s0"), (8, R "s1"), (16, R "s2"), (24, R "s3"), (32, R "s4"), (40, R "s5"), (48, R "s6"), (56, R "s7"), (64, R "s8"), (72, R "s9"), (80, R "s10"), (88, R "s11"), (96, R "a0")]

theorem pro_run (s : MState64) :
    runX s prologue = ⟨s.regs.set "sp" (s.regs.get "sp" + BitVec.ofInt 64 (-112)),
      writeSlots s.mem (s.regs.get "sp" + BitVec.ofInt 64 (-112)) (saved s.regs.get)⟩ := by
  simp only [prologue, runX_cons, runX_nil, evalX, evalMInst64, addr, seNeg]
  simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
    not_false_eq_true, or_self, saved, writeSlots]
  rfl

theorem loads_run (t : MState64) :
    (runX t loads).mem = t.mem ∧ (runX t loads).regs.get "sp" = t.regs.get "sp" ∧
      limbs4 (runX t loads).regs.get "a0" "a1" "a2" "a3" = memLimbs4 t.mem (t.regs.get "a1") ∧
      limbs4 (runX t loads).regs.get "a4" "a5" "a6" "a7" = memLimbs4 t.mem (t.regs.get "a2") := by
  simp only [loads, runX_cons, runX_nil, evalX, addr, true_and]
  refine ⟨?_, ?_, ?_⟩
  all_goals simp only [limbs4, memLimbs4, RState64.get_set_same, RState64.get_set_other, ne_eq,
    String.reduceEq, not_false_eq_true, or_self]
  all_goals rfl

theorem storeZ_run (t : MState64) :
    (runX t storeZ).mem = writeSlots t.mem (read64 t.mem (t.regs.get "sp" + BitVec.ofNat 64 96))
      [(0, t.regs.get "a0"), (8, t.regs.get "a1"), (16, t.regs.get "a2"), (24, t.regs.get "a3")] ∧
      (runX t storeZ).regs.get "sp" = t.regs.get "sp" := by
  simp only [storeZ, runX_cons, runX_nil, evalX, addr]
  refine ⟨?_, ?_⟩
  all_goals simp only [writeSlots, RState64.get_set_same, RState64.get_set_other, ne_eq,
    String.reduceEq, not_false_eq_true, or_self]
  all_goals rfl

theorem epilogue_run (t : MState64) :
    (runX t epilogue).mem = t.mem ∧
      (runX t epilogue).regs.get "sp" = t.regs.get "sp" + BitVec.ofNat 64 112 ∧
      ∀ q ∈ frameSlots, (runX t epilogue).regs.get q.1
        = read64 t.mem (t.regs.get "sp" + BitVec.ofNat 64 q.2) := by
  simp only [epilogue, runX_cons, runX_nil, evalX, evalMInst64, addr, true_and]
  refine ⟨?_, ?_⟩
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rfl
  · intro q hq
    simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
        not_false_eq_true, or_self]
      rfl

theorem sp_not_written : "sp" ∉ mWrites feMulPhys := by decide +kernel

theorem sep_symm {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) : Sep b m a n := ⟨h.2, h.1⟩

theorem memLimbs4_writeSlots_sep (m : AMem) (base p : BitVec 64) (l : List (Nat × BitVec 64))
    (hl : ∀ q ∈ l, q.1 + 8 ≤ 112) (h : Sep base 112 p 32) :
    memLimbs4 (writeSlots m base l) p = memLimbs4 m p := by
  simp only [memLimbs4]
  rw [read64_writeSlots_sep _ _ _ 112 (by decide) _ hl (sep_word h 0 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 112 (by decide) _ hl (sep_word h 8 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 112 (by decide) _ hl (sep_word h 16 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 112 (by decide) _ hl (sep_word h 24 (by decide) (by decide))]

theorem saved_offsets (R : String → BitVec 64) :
    (saved R).map Prod.fst = [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96] := rfl

/-- **The buffer function computes the field product.** For every machine state whose
    112-byte frame below `sp` is disjoint from the buffers at `a0` (`z`), `a1` (`x`) and
    `a2` (`y`), running `feMulFn` leaves `x · y mod p25519` in the buffer at `a0`, restores
    `s0..s11` and `sp`, and leaves every byte outside the frame and the `z` buffer. `x` and
    `y` may overlap each other and `z`. -/
theorem feMulFn_run (s : MState64)
    (hx : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a1") 32)
    (hy : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a2") 32)
    (hz : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a0") 32) :
    memLimbs4 (runX s feMulFn).mem (s.regs.get "a0")
        = memLimbs4 s.mem (s.regs.get "a1") * memLimbs4 s.mem (s.regs.get "a2") % p25519 ∧
      (∀ q ∈ frameSlots, (runX s feMulFn).regs.get q.1 = s.regs.get q.1) ∧
      (runX s feMulFn).regs.get "sp" = s.regs.get "sp" ∧
      ∀ x, Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 x 1 →
        Sep (s.regs.get "a0") 32 x 1 → (runX s feMulFn).mem x = s.mem x := by
  have e : runX s feMulFn
      = runX (runX (runX (runX (runX s prologue) loads) (feMulPhys.map .m)) storeZ) epilogue := by
    simp only [feMulFn, runX_append]
  rw [e, pro_run, runX_lift]
  generalize hf : s.regs.get "sp" + BitVec.ofInt 64 (-112) = f at hx hy hz ⊢
  generalize hM1 : writeSlots s.mem f (saved s.regs.get) = M1
  obtain ⟨l1, l2, l3, l4⟩ := loads_run ⟨s.regs.set "sp" f, M1⟩
  generalize ht2 : runX ⟨s.regs.set "sp" f, M1⟩ loads = t2 at l1 l2 l3 l4
  have b1 := feMulPhys_correct t2.regs
  have b2 := runM64_frame feMulPhys t2.regs "sp" sp_not_written
  obtain ⟨z1, z2⟩ := storeZ_run ⟨runM64 t2.regs feMulPhys, t2.mem⟩
  generalize ht4 : runX ⟨runM64 t2.regs feMulPhys, t2.mem⟩ storeZ = t4 at z1 z2
  obtain ⟨e1, e2, e3⟩ := epilogue_run t4
  simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
    not_false_eq_true, or_self] at l2 l3 l4
  -- the stack slots of `M1`
  have hslot : ∀ o v, (o, v) ∈ saved s.regs.get → read64 M1 (f + BitVec.ofNat 64 o) = v :=
    fun o v hmem => hM1 ▸ read64_writeSlots_mem _ _ _ o v hmem
      (by rw [saved_offsets]; decide) (by rw [saved_offsets]; decide)
      (by rw [saved_offsets]; decide)
  have hzp : read64 M1 (f + BitVec.ofNat 64 96) = s.regs.get "a0" :=
    hslot 96 _ (by simp [saved])
  simp only [l1, b2, l2, hzp] at z1
  have hsp4 : t4.regs.get "sp" = f := by rw [z2]; exact b2.trans l2
  have hsep : ∀ q ∈ saved s.regs.get, q.1 + 8 ≤ 112 := by
    intro q hq; simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the product
    rw [e1, z1]
    have zl := fun o v (hmem : (o, v) ∈ [(0, (runM64 t2.regs feMulPhys).get "a0"),
        (8, (runM64 t2.regs feMulPhys).get "a1"), (16, (runM64 t2.regs feMulPhys).get "a2"),
        (24, (runM64 t2.regs feMulPhys).get "a3")]) =>
      read64_writeSlots_mem M1 (s.regs.get "a0") _ o v hmem
        (by simp only [List.map_cons, List.map_nil]; decide)
        (by simp only [List.map_cons, List.map_nil]; decide)
        (by simp only [List.map_cons, List.map_nil]; decide)
    unfold memLimbs4
    rw [zl 0 ((runM64 t2.regs feMulPhys).get "a0") (by simp),
      zl 8 ((runM64 t2.regs feMulPhys).get "a1") (by simp),
      zl 16 ((runM64 t2.regs feMulPhys).get "a2") (by simp),
      zl 24 ((runM64 t2.regs feMulPhys).get "a3") (by simp)]
    have := b1
    simp only [limbs4] at this
    rw [this, ← limbs4, ← limbs4, l3, l4, ← hM1,
      memLimbs4_writeSlots_sep _ _ _ _ hsep hx, memLimbs4_writeSlots_sep _ _ _ _ hsep hy]
    rfl
  · -- the saved registers
    intro q hq
    rw [e3 q hq, z1, hsp4,
      read64_writeSlots_sep _ _ _ 32 (by decide) _ (fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> simp)
        (sep_word (sep_symm hz) q.2 ?_ (by decide))]
    · simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hslot _ _ (by simp [saved])
    · simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
  · -- the stack pointer
    rw [e2, hsp4, ← hf, BitVec.add_assoc]
    have : BitVec.ofInt 64 (-112) + BitVec.ofNat 64 112 = 0 := by decide
    rw [this]
    simp
  · -- the memory frame
    intro x hxf hxz
    rw [e1, z1, writeSlots_out _ _ _ _ fun q hq =>
        not_inRange_of_out (out_of_sep hxz (by simp)) ?_ (by decide), ← hM1,
      writeSlots_out _ _ _ _ fun q hq =>
        not_inRange_of_out (out_of_sep hxf (by simp)) (hsep q hq) (by decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp

theorem feMulFn_ok : feMulFn.all XInstOKb = true := by decide +kernel

theorem feMulFn_length : feMulFn.length = 1073 := by decide +kernel

/-- **The encoded field-multiply function.** Its bytes decode as 1073 instructions `c` such
    that, for every machine state whose 112-byte frame below `sp` is disjoint from the
    32-byte buffers at `a0`, `a1` and `a2`, with `sp` 16-byte and the buffers 8-byte
    aligned, running `c` leaves `x · y mod p25519` in the buffer at `a0` (`x` from `a1`,
    `y` from `a2`), restores `s0..s11` and `sp`, and leaves every byte outside the frame and
    the output buffer unchanged. The proof does not use the alignment hypotheses: they are
    the contract under which the function's `ld` and `sd` are aligned on a processor that
    traps misaligned accesses (`RiscvMem64`, "Alignment"). -/
theorem feMulFnBytes_correct :
    ∃ c, decodeXStream64 1073 (encodeXBlock64 feMulFn) = some c ∧
      ∀ s : MState64,
        Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a1") 32 →
        Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a2") 32 →
        Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a0") 32 →
        Aligned 16 (s.regs.get "sp") → Aligned 8 (s.regs.get "a0") →
        Aligned 8 (s.regs.get "a1") → Aligned 8 (s.regs.get "a2") →
        memLimbs4 (runX s c).mem (s.regs.get "a0")
            = memLimbs4 s.mem (s.regs.get "a1") * memLimbs4 s.mem (s.regs.get "a2") % p25519 ∧
          (∀ q ∈ frameSlots, (runX s c).regs.get q.1 = s.regs.get q.1) ∧
          (runX s c).regs.get "sp" = s.regs.get "sp" ∧
          ∀ x, Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 x 1 →
            Sep (s.regs.get "a0") 32 x 1 → (runX s c).mem x = s.mem x :=
  ⟨feMulFn, feMulFn_length ▸ decodeXStream64_encode_b _ feMulFn_ok,
    fun s hx hy hz _ _ _ _ => feMulFn_run s hx hy hz⟩

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof.feMulFnBytes_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms feMulFnBytes_correct

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
