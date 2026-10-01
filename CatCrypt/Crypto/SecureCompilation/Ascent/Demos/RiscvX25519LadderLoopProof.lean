/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof

/-!
# The RV64 Curve25519 ladder as a function

`ladderCode` is the X25519 Montgomery ladder as a function of the program-counter machine
`RiscvPc64`. It opens a 112-byte frame and saves `s0..s11` and `ra`. It loads the scalar from
the first 32 bytes of the state block at `a0` into `s3..s6` and runs a loop of 255
iterations, counted down in `s1`. Each iteration takes bit 254 of `s3..s6`, swaps
`(x2, z2)` with `(x3, z3)` on it (two calls of the swap function), calls the ladder step
function, swaps again, and shifts `s3..s6` left by one bit. The loop is the back-edge
`bne s1, zero`, and the proof is `RiscvPc64.steps_loop_inv` with the invariant `LoopInv`.

The specification is `ladderN 255`, the iterations of `x25519LadderStepVerified` on the
bits 254 down to 0 of the scalar.

## Main results

* `swapCall_run`, `stepCall_run`: a call of the swap and of the step, for any functions
  meeting their `FnSpec`.
* `loop_body`: one iteration keeps `LoopInv` with the counter decremented.
* `fnSpec_ladder`: `ladderCode` placed in any program meets `FnSpec` with `LadderPre` and
  `LadderPost`.

## Scope

The block holds the coordinates as integers below `2^256`, read through `fromNat`, so the
statements are over `Fp25519`. The loop takes bits from a register copy of the scalar.
Whether its timing depends on the scalar is not stated here: the calls and the branch are
the same on every iteration, and the swap is branch-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderFnProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderStepProof (ladderPfx)
open CatCrypt.Crypto.SecureCompilation.Memory64 (AMem read64)
open CatCrypt.Util (P25519 X25519State x25519DoubleAndAdd x25519CSwap x25519LadderStepVerified
  x25519ScalarBit)

/-! ## The specification -/

/-- `n` ladder iterations, on the bits `n - 1` down to `0`. -/
def ladderN : Nat → X25519State → X25519State
  | 0, s => s
  | n + 1, s => ladderN n (x25519LadderStepVerified n s)

/-! ## Bits of the scalar -/

/-- The bit at position 254 of the 256-bit value whose top word is `w`. -/
def topBit (w : BitVec 64) : Nat := w.toNat / 2 ^ 62 % 2

/-- The four scalar registers `s3..s6`, as a 256-bit value. -/
def val4 (R : String → BitVec 64) : Nat :=
  (R "s3").toNat + 2 ^ 64 * (R "s4").toNat + 2 ^ 128 * (R "s5").toNat + 2 ^ 192 * (R "s6").toNat

theorem topBit_val4 (R : String → BitVec 64) : topBit (R "s6") = val4 R / 2 ^ 254 % 2 := by
  have := (R "s3").isLt; have := (R "s4").isLt; have := (R "s5").isLt
  unfold topBit val4
  generalize (R "s3").toNat = a at *
  generalize (R "s4").toNat = b at *
  generalize (R "s5").toNat = c at *
  generalize (R "s6").toNat = d
  omega

theorem bit_shifted (K c : Nat) (hc1 : 1 ≤ c) (hc : c ≤ 255) :
    K * 2 ^ (255 - c) % 2 ^ 256 / 2 ^ 254 % 2 = K / 2 ^ (c - 1) % 2 := by
  have e1 : (2 : Nat) ^ 256 = 2 ^ 254 * 4 := by norm_num
  have e2 : (2 : Nat) ^ 254 = 2 ^ (255 - c) * 2 ^ (c - 1) := by
    rw [← pow_add]; congr 1; omega
  rw [e1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 4), e2,
    Nat.mul_comm K, Nat.mul_div_mul_left _ _ (by positivity)]

theorem shl_add (x y : BitVec 64) :
    (x <<< 1 + y >>> 63).toNat = 2 * x.toNat % 2 ^ 64 + y.toNat / 2 ^ 63 := by
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have := y.isLt
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-! ## A call of the swap -/

/-- Point `a0`, `a1` at the field elements `p`, `q` of the block at `s0`, and put bit 254
    of the scalar registers in `a2`. -/
def swapSet (p q : String) : List XInst64 :=
  [.m (.base (.srli "t0" "s6" 62)), .m (.addi "t1" "zero" 1), .m (.base (.and "a2" "t0" "t1")),
    .m (.addi "a0" "s0" (BitVec.ofNat 12 (off p))), .m (.addi "a1" "s0" (BitVec.ofNat 12 (off q)))]

/-- The swap of `p` and `q` on bit 254, at instruction `j`, calling the function at `cs`. -/
def swapCall (cs j : Nat) (p q : String) : List PInst64 :=
  (swapSet p q).map .x ++ [.jal "ra" (BitVec.ofInt 21 (4 * (cs : Int) - 4 * ((j + 5 : Nat) : Int)))]

theorem get_zero (s : RState64) : s.get "zero" = 0 := by simp [RState64.get]

theorem and_one_toNat (z : BitVec 64) : (z &&& 1#64).toNat = z.toNat % 2 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod]

theorem swapSet_writes (p q : String) :
    ∀ r ∈ "sp" :: "ra" :: frameSlots.map Prod.fst, r ∉ xWrites (swapSet p q) := by
  intro r hr
  simp only [swapSet, xWrites, List.filterMap_cons, List.filterMap_nil, xDst, mDst,
]
  simp only [frameSlots, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem swapSet_run (p q : String) (hp : p ∈ ladderPfx) (hq : q ∈ ladderPfx) (st : MState64) :
    (runX st (swapSet p q)).mem = st.mem ∧
      (runX st (swapSet p q)).regs.get "a0" = st.regs.get "s0" + BitVec.ofNat 64 (off p) ∧
      (runX st (swapSet p q)).regs.get "a1" = st.regs.get "s0" + BitVec.ofNat 64 (off q) ∧
      ((runX st (swapSet p q)).regs.get "a2").toNat = topBit (st.regs.get "s6") := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
    simp only [swapSet, runX_cons, runX_nil, evalX, evalMInst64, evalRInst64, opAnd64]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [off_se _ hp]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [off_se _ hq]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [get_zero, show (0 : BitVec 64) + (1 : BitVec 12).signExtend 64 = 1#64 by decide,
      and_one_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl

theorem sep_offs (P : BitVec 64) (o1 o2 : Nat) (h : o1 + 32 ≤ o2 ∨ o2 + 32 ≤ o1)
    (h1 : o1 < 2 ^ 32) (h2 : o2 < 2 ^ 32) :
    Sep (P + BitVec.ofNat 64 o1) 32 (P + BitVec.ofNat 64 o2) 32 := by
  have := P.isLt
  simp only [RiscvFeMulFnProof.Sep, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **A call of the swap.** -/
theorem swapCall_run (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0) (cs : Nat)
    (hcs : 4 * cs < 2 ^ 20) (hspec : FnSpec prog base (addrOf base cs) CswapPre CswapPost)
    (pre post : List PInst64) (p q : String) (j : Nat) (hj : pre.length = j)
    (hprog : prog = pre ++ swapCall cs j p q ++ post)
    (hlen : 4 * (j + 6) < 2 ^ 20) (hp : p ∈ ladderPfx) (hq : q ∈ ladderPfx)
    (hpq : p ≠ q) (st : MState64) :
    ∃ n st', steps prog base n ⟨addrOf base j, st⟩
        = some ⟨addrOf base (j + 6), st'⟩ ∧
      fe st'.mem (st.regs.get "s0") p = (if topBit (st.regs.get "s6") = 1
        then fe st.mem (st.regs.get "s0") q else fe st.mem (st.regs.get "s0") p) ∧
      fe st'.mem (st.regs.get "s0") q = (if topBit (st.regs.get "s6") = 1
        then fe st.mem (st.regs.get "s0") p else fe st.mem (st.regs.get "s0") q) ∧
      (∀ x, Sep (st.regs.get "s0" + BitVec.ofNat 64 (off p)) 32 x 1 →
        Sep (st.regs.get "s0" + BitVec.ofNat 64 (off q)) 32 x 1 → st'.mem x = st.mem x) ∧
      (∀ r ∈ frameSlots, st'.regs.get r.1 = st.regs.get r.1) ∧
      st'.regs.get "sp" = st.regs.get "sp" := by
  subst hj
  have hprog' : prog = pre ++ (swapSet p q).map .x ++
      (.jal "ra" (BitVec.ofInt 21 (4 * (cs : Int) - 4 * ((pre.length + 5 : Nat) : Int))) :: post) := by
    rw [hprog]; simp [swapCall]
  have h1 := steps_block pre (.jal "ra" (BitVec.ofInt 21 (4 * (cs : Int)
    - 4 * ((pre.length + 5 : Nat) : Int))) :: post) base (swapSet p q) (by simp [swapSet]; omega) st
  rw [← hprog'] at h1
  simp only [show (swapSet p q).length = 5 from rfl] at h1
  obtain ⟨hm, ha0, ha1, ha2⟩ := swapSet_run p q hp hq st
  have hf : prog[pre.length + 5]? =
      some (.jal "ra" (BitVec.ofInt 21 (4 * (cs : Int) - 4 * ((pre.length + 5 : Nat) : Int)))) := by
    rw [hprog, getElem?_mid pre _ _ 5 (by simp [swapCall, swapSet])]; rfl
  have ne := fun (r : String) (h : r ≠ "ra") =>
    RState64.get_set_other (runX st (swapSet p q)).regs "ra" r
      (addrOf base (pre.length + 5 + 1)) h
  obtain ⟨n, st', hrun, hpost⟩ := steps_call_at prog base hb (pre.length + 5) cs (by omega) hcs
    hf hspec (runX st (swapSet p q)) (by
      refine ⟨?_, ?_⟩
      · simp only [ne "a0" (by decide), ne "a1" (by decide), ha0, ha1]
        exact sep_offs _ _ _ (off_sep _ hp _ hq hpq) (by have := off_lt _ hp; omega)
          (by have := off_lt _ hq; omega)
      · simp only [ne "a2" (by decide)]
        rw [ha2]; unfold topBit; omega)
  obtain ⟨c1, c2, c3, c4, c5, -⟩ := hpost
  simp only [ne "a0" (by decide), ne "a1" (by decide), ne "a2" (by decide), ha0, ha1, ha2,
    hm] at c1 c2 c3
  refine ⟨5 + (1 + n), st', ?_, ?_, ?_, c3, ?_, ?_⟩
  · rw [show pre.length + 6 = pre.length + 5 + 1 by omega]; exact steps_trans h1 hrun
  · unfold fe; rw [c1]
  · unfold fe; rw [c2]
  · intro r hr
    rw [c4 r hr, ne _ (frame_ne r hr).2.2.2, runX_frame _ _ _ (swapSet_writes p q r.1 (by
      simp only [List.mem_cons, List.mem_map]; exact Or.inr (Or.inr ⟨r, hr, rfl⟩)))]
  · rw [c5, ne "sp" (by decide), runX_frame _ _ _ (swapSet_writes p q "sp" (by simp))]

/-! ## A call of the step -/

/-- Point `a0` at the block in `s0` and call the step function at `sf`, at instruction `j`. -/
def stepCall (sf j : Nat) : List PInst64 :=
  [.x (.m (.base (.mv "a0" "s0"))), .jal "ra" (BitVec.ofInt 21 (4 * (sf : Int) - 4 * ((j + 1 : Nat) : Int)))]

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFe25519AddSubProof (p25519_pos)
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel (p25519)

/-- **A call of the step.** -/
theorem stepCall_run (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0) (sf : Nat)
    (hsf : 4 * sf < 2 ^ 20) (hspec : FnSpec prog base (addrOf base sf) StepPre StepPost)
    (pre post : List PInst64) (j : Nat) (hj : pre.length = j)
    (hprog : prog = pre ++ stepCall sf j ++ post)
    (hlen : 4 * (j + 2) < 2 ^ 20) (st : MState64)
    (hsep : Sep (st.regs.get "sp" + BitVec.ofInt 64 (-128)) 128 (st.regs.get "s0") 576)
    (hz2 : fe st.mem (st.regs.get "s0") "z2" ≤ 2 * p25519)
    (hz3 : fe st.mem (st.regs.get "s0") "z3" ≤ 2 * p25519)
    (sx : X25519State) (hh : Holds st.mem (st.regs.get "s0") sx) :
    ∃ n st', steps prog base n ⟨addrOf base j, st⟩
        = some ⟨addrOf base (j + 2), st'⟩ ∧
      Holds st'.mem (st.regs.get "s0") (x25519DoubleAndAdd sx) ∧
      fe st'.mem (st.regs.get "s0") "z2" < p25519 ∧ fe st'.mem (st.regs.get "s0") "z3" < p25519 ∧
      (∀ r ∈ frameSlots, st'.regs.get r.1 = st.regs.get r.1) ∧
      st'.regs.get "sp" = st.regs.get "sp" ∧
      ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-128)) 128 x 1 →
        Sep (st.regs.get "s0" + BitVec.ofNat 64 32) 544 x 1 → st'.mem x = st.mem x := by
  subst hj
  have h0 : prog[pre.length]? = some (.x (.m (.base (.mv "a0" "s0")))) := by
    have := getElem?_mid pre (stepCall sf pre.length) post 0 (by simp [stepCall])
    rw [Nat.add_zero] at this; rw [hprog, this]; rfl
  have hf : prog[pre.length + 1]? =
      some (.jal "ra" (BitVec.ofInt 21 (4 * (sf : Int) - 4 * ((pre.length + 1 : Nat) : Int)))) := by
    rw [hprog, getElem?_mid pre _ _ 1 (by simp [stepCall])]; rfl
  have k0 := steps_x prog base pre.length (by omega) _ h0 st
  generalize hst1 : evalX st (.m (.base (.mv "a0" "s0"))) = st1 at k0
  have hm1 : st1.mem = st.mem := by rw [← hst1]; rfl
  have hr1 : ∀ r, r ≠ "a0" → st1.regs.get r = st.regs.get r := by
    intro r hr; rw [← hst1]; exact RState64.get_set_other _ _ _ _ hr
  have ha1 : st1.regs.get "a0" = st.regs.get "s0" := by
    rw [← hst1]
    simp only [evalX, evalMInst64, evalRInst64, RState64.get_set_same, String.reduceEq,
      not_false_eq_true, or_self]
  have ne := fun (r : String) (h : r ≠ "ra") =>
    RState64.get_set_other st1.regs "ra" r (addrOf base (pre.length + 1 + 1)) h
  obtain ⟨n, st', hrun, hpost⟩ := steps_call_at prog base hb (pre.length + 1) sf (by omega) hsf
    hf hspec st1 (by
      refine ⟨?_, ?_, ?_⟩ <;> simp only [ne "a0" (by decide), ne "sp" (by decide)]
      · rw [ha1, hr1 "sp" (by decide)]; exact hsep
      · rw [ha1, hm1]; exact hz2
      · rw [ha1, hm1]; exact hz3)
  have hv := step_value _ _ hpost sx
  simp only [ne "a0" (by decide), ha1, hm1] at hv
  obtain ⟨v1, -, v2, -, v3, -⟩ := hv hh hz2 hz3
  obtain ⟨-, p2, p3, -, p5⟩ := hpost
  simp only [ne "a0" (by decide), ne "sp" (by decide), ha1, hm1, hr1 "sp" (by decide)] at p3 p5
  refine ⟨1 + (1 + n), st', ?_, v1, v2, v3, ?_, p3, p5⟩
  · rw [show pre.length + 2 = pre.length + 1 + 1 by omega]; exact steps_trans k0 hrun
  · intro r hr
    rw [p2 r hr, ne _ (frame_ne r hr).2.2.2, hr1 _ (frame_ne r hr).1]

/-! ## The shift of the scalar -/

/-- Shift the scalar registers `s3..s6` left by one bit (the carried bit lands in the
    cleared bit 0, so `add` is `or`) and decrement the counter `s1`. -/
def shiftDec : List XInst64 :=
  [.m (.base (.srli "t0" "s5" 63)), .m (.base (.slli "s6" "s6" 1)), .m (.base (.add "s6" "s6" "t0")),
    .m (.base (.srli "t0" "s4" 63)), .m (.base (.slli "s5" "s5" 1)), .m (.base (.add "s5" "s5" "t0")),
    .m (.base (.srli "t0" "s3" 63)), .m (.base (.slli "s4" "s4" 1)), .m (.base (.add "s4" "s4" "t0")),
    .m (.base (.slli "s3" "s3" 1)), .m (.addi "s1" "s1" (BitVec.ofInt 12 (-1)))]

theorem shl_toNat (x : BitVec 64) : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega

theorem shiftDec_writes :
    ∀ r ∈ "sp" :: "ra" :: "s0" :: "s2" :: "s7" :: "s8" :: "s9" :: "s10" :: "s11" :: [],
      r ∉ xWrites shiftDec := by decide

theorem shiftDec_run (st : MState64) :
    (runX st shiftDec).mem = st.mem ∧
      val4 (runX st shiftDec).regs.get = 2 * val4 st.regs.get % 2 ^ 256 ∧
      (runX st shiftDec).regs.get "s1" = st.regs.get "s1" + BitVec.ofInt 64 (-1) := by
  refine ⟨rfl, ?_, ?_⟩ <;>
    simp only [shiftDec, runX_cons, runX_nil, evalX, evalMInst64, evalRInst64, opAdd64]
  · unfold val4
    simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [shl_add, shl_add, shl_add, shl_toNat]
    have := (st.regs.get "s3").isLt; have := (st.regs.get "s4").isLt
    have := (st.regs.get "s5").isLt; have := (st.regs.get "s6").isLt
    generalize (st.regs.get "s3").toNat = a at *
    generalize (st.regs.get "s4").toNat = b at *
    generalize (st.regs.get "s5").toNat = c at *
    generalize (st.regs.get "s6").toNat = d at *
    omega
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rfl

/-! ## The swaps at the specification -/

theorem fe_frame (m m' : AMem) (P : BitVec 64) (p q r : String) (hp : p ∈ ladderPfx)
    (hq : q ∈ ladderPfx) (hr : r ∈ ladderPfx) (hrp : r ≠ p) (hrq : r ≠ q)
    (hfr : ∀ x, Sep (P + BitVec.ofNat 64 (off p)) 32 x 1 →
      Sep (P + BitVec.ofNat 64 (off q)) 32 x 1 → m' x = m x) :
    fe m' P r = fe m P r := by
  unfold fe
  refine memLimbs4_congr _ _ _ fun j hj => hfr _ ?_ ?_
  · exact sep_bufs P (off p) (off r) j (off_sep _ hp _ hr (Ne.symm hrp)) hj
      (by have := off_lt _ hp; omega) (by have := off_lt _ hr; omega)
  · exact sep_bufs P (off q) (off r) j (off_sep _ hq _ hr (Ne.symm hrq)) hj
      (by have := off_lt _ hq; omega) (by have := off_lt _ hr; omega)

/-- A byte outside the field region is outside each field element. -/
theorem sep_field (P x : BitVec 64) (p : String) (hp : p ∈ ladderPfx)
    (hx : Sep (P + BitVec.ofNat 64 32) 544 x 1) : Sep (P + BitVec.ofNat 64 (off p)) 32 x 1 := by
  have := sep_into hx (off p - 32) 32 (by decide) (by have := off_lt _ hp; omega) (by decide)
  rwa [add_ofNat_add, show 32 + (off p - 32) = off p by have := off_lt _ hp; omega] at this

theorem holds_swap (m m1 m2 : AMem) (P : BitVec 64) (sx : X25519State) (t : Nat)
    (hh : Holds m P sx)
    (a1 : fe m1 P "x2" = if t = 1 then fe m P "x3" else fe m P "x2")
    (a2 : fe m1 P "x3" = if t = 1 then fe m P "x2" else fe m P "x3")
    (af : ∀ x, Sep (P + BitVec.ofNat 64 (off "x2")) 32 x 1 →
      Sep (P + BitVec.ofNat 64 (off "x3")) 32 x 1 → m1 x = m x)
    (b1 : fe m2 P "z2" = if t = 1 then fe m1 P "z3" else fe m1 P "z2")
    (b2 : fe m2 P "z3" = if t = 1 then fe m1 P "z2" else fe m1 P "z3")
    (bf : ∀ x, Sep (P + BitVec.ofNat 64 (off "z2")) 32 x 1 →
      Sep (P + BitVec.ofNat 64 (off "z3")) 32 x 1 → m2 x = m1 x) :
    Holds m2 P (x25519CSwap (decide (t = 1)) sx) ∧
      fe m2 P "z2" = (if t = 1 then fe m P "z3" else fe m P "z2") ∧
      fe m2 P "z3" = (if t = 1 then fe m P "z2" else fe m P "z3") := by
  have f := fun r hr hrp hrq => fe_frame m m1 P "x2" "x3" r (by decide) (by decide) hr hrp hrq af
  have g := fun r hr hrp hrq => fe_frame m1 m2 P "z2" "z3" r (by decide) (by decide) hr hrp hrq bf
  have ex1 : fe m2 P "x1" = fe m P "x1" :=
    (g "x1" (by decide) (by decide) (by decide)).trans (f "x1" (by decide) (by decide) (by decide))
  have ex2 : fe m2 P "x2" = fe m1 P "x2" := g "x2" (by decide) (by decide) (by decide)
  have ex3 : fe m2 P "x3" = fe m1 P "x3" := g "x3" (by decide) (by decide) (by decide)
  have ez2 : fe m1 P "z2" = fe m P "z2" := f "z2" (by decide) (by decide) (by decide)
  have ez3 : fe m1 P "z3" = fe m P "z3" := f "z3" (by decide) (by decide) (by decide)
  rw [ez2, ez3] at b1 b2
  obtain ⟨h1, h2, h3, h4, h5⟩ := hh
  refine ⟨?_, b1, b2⟩
  by_cases ht : t = 1
  · simp only [ht, ↓reduceIte] at a1 a2 b1 b2
    simp only [ht, decide_true, x25519CSwap, ↓reduceIte]
    exact ⟨ex1 ▸ h1, by rw [ex2, a1]; exact h4, by rw [b1]; exact h5, by rw [ex3, a2]; exact h2,
      by rw [b2]; exact h3⟩
  · simp only [ht, ↓reduceIte] at a1 a2 b1 b2
    simp only [ht, decide_false, x25519CSwap, Bool.false_eq_true, ↓reduceIte]
    exact ⟨ex1 ▸ h1, by rw [ex2, a1]; exact h2, by rw [b1]; exact h3, by rw [ex3, a2]; exact h4,
      by rw [b2]; exact h5⟩

theorem cswap_scalar (b : Bool) (sx : X25519State) : (x25519CSwap b sx).scalar = sx.scalar := by
  cases b <;> rfl

theorem step_eq (i : Nat) (sx : X25519State) :
    x25519LadderStepVerified i sx = x25519CSwap (decide (sx.scalar / 2 ^ i % 2 = 1))
      (x25519DoubleAndAdd (x25519CSwap (decide (sx.scalar / 2 ^ i % 2 = 1)) sx)) := rfl

/-! ## The ladder function -/

/-- Open a 112-byte frame, save `s0..s11` and `ra`, keep the block pointer in `s0`, load the
    scalar into `s3..s6` and set the counter `s1` to 255. -/
def lpro : List XInst64 :=
  prologue ++ [.sd "ra" "sp" 104, .m (.base (.mv "s0" "a0")), .ld "s3" "s0" 0, .ld "s4" "s0" 8,
    .ld "s5" "s0" 16, .ld "s6" "s0" 24, .m (.addi "s1" "zero" 255)]

/-- Restore `ra` and `s0..s11` and close the frame. -/
def lepi : List XInst64 := .ld "ra" "sp" 104 :: epilogue

/-- The shift, the back-edge and the epilogue. -/
def ltail5 : List PInst64 :=
  shiftDec.map .x ++ (.bne "s1" "zero" (BitVec.ofInt 13 (-148)) ::
    (lepi.map .x ++ [.jalr "zero" "ra" 0]))

/-- The code from the second pair of swaps on. -/
def ltail4 (cs k : Nat) : List PInst64 := swapCall cs (k + 41) "z2" "z3" ++ ltail5
def ltail3 (cs k : Nat) : List PInst64 := swapCall cs (k + 35) "x2" "x3" ++ ltail4 cs k
/-- The code from the call of the step on. -/
def ltail2 (cs sf k : Nat) : List PInst64 := stepCall sf (k + 33) ++ ltail3 cs k
def ltail1 (cs sf k : Nat) : List PInst64 := swapCall cs (k + 27) "z2" "z3" ++ ltail2 cs sf k

/-- The ladder function at instruction `k`, calling the swap at `cs` and the step at `sf`:
    255 iterations of swap, step, swap on bit 254 of the shifted scalar. -/
def ladderCode (cs sf k : Nat) : List PInst64 :=
  lpro.map .x ++ (swapCall cs (k + 21) "x2" "x3" ++ ltail1 cs sf k)

theorem lpro_length : lpro.length = 21 := rfl
theorem lepi_length : lepi.length = 14 := rfl
theorem ladderCode_length (cs sf k : Nat) : (ladderCode cs sf k).length = 74 := by
  simp [ladderCode, ltail1, ltail2, ltail3, ltail4, ltail5, lpro_length, lepi_length, swapCall,
    swapSet, stepCall, shiftDec]

/-- The loop invariant at counter `c`: the block pointer and `sp` are fixed, the scalar
    registers hold `K` shifted left by `255 - c`, the block holds a state `sx` with
    `ladderN c sx = T`, and no byte outside the callee frames and the field region has
    changed since `M`. -/
def LoopInv (P SP : BitVec 64) (K : Nat) (T : X25519State) (M : AMem) (c : Nat)
    (st : MState64) : Prop :=
  st.regs.get "s0" = P ∧ st.regs.get "sp" = SP ∧ c ≤ 255 ∧
    val4 st.regs.get = K * 2 ^ (255 - c) % 2 ^ 256 ∧
    fe st.mem P "z2" ≤ 2 * p25519 ∧ fe st.mem P "z3" ≤ 2 * p25519 ∧
    (∃ sx, Holds st.mem P sx ∧ sx.scalar = K ∧ ladderN c sx = T) ∧
    ∀ x, Sep (SP + BitVec.ofInt 64 (-128)) 128 x 1 → Sep (P + BitVec.ofNat 64 32) 544 x 1 →
      st.mem x = M x

theorem frame_s : ∀ r ∈ ["s0", "s1", "s3", "s4", "s5", "s6"], ∃ q ∈ frameSlots, q.1 = r := by
  decide

theorem ofNat_pred (c : Nat) (hc : 1 ≤ c) (hc' : c < 2 ^ 64) :
    BitVec.ofNat 64 c + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (c - 1) := by
  have e : BitVec.ofNat 64 c = BitVec.ofNat 64 (c - 1) + BitVec.ofNat 64 1 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.add_assoc, show BitVec.ofNat 64 1 + BitVec.ofInt 64 (-1) = 0 by decide]
  simp

theorem shift_inv (K c : Nat) (hc : 1 ≤ c) (hc' : c ≤ 255) :
    2 * (K * 2 ^ (255 - c) % 2 ^ 256) % 2 ^ 256 = K * 2 ^ (255 - (c - 1)) % 2 ^ 256 := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, show 255 - (c - 1) = 255 - c + 1 by omega,
    pow_succ]
  ring_nf

theorem val4_congr (R R' : String → BitVec 64) (h3 : R' "s3" = R "s3") (h4 : R' "s4" = R "s4")
    (h5 : R' "s5" = R "s5") (h6 : R' "s6" = R "s6") : val4 R' = val4 R := by
  unfold val4; rw [h3, h4, h5, h6]

theorem le_ite {a b c : Nat} {t : Prop} [Decidable t] (ha : a ≤ c) (hb : b ≤ c) :
    (if t then a else b) ≤ c := by split <;> assumption

theorem lt_ite {a b c : Nat} {t : Prop} [Decidable t] (ha : a < c) (hb : b < c) :
    (if t then a else b) < c := by split <;> assumption

theorem steps_block_of {prog A C : List PInst64} {base : BitVec 64} {b : List XInst64}
    (h : prog = A ++ b.map .x ++ C) (hk : 4 * (A.length + b.length) < 2 ^ 64) (st : MState64) :
    steps prog base b.length ⟨addrOf base A.length, st⟩
      = some ⟨addrOf base (A.length + b.length), runX st b⟩ := by
  rw [h]; exact steps_block A C base b hk st

/-- **One iteration of the loop.** -/
theorem loop_body (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0) (cs sf : Nat)
    (hcs : 4 * cs < 2 ^ 20) (hsf : 4 * sf < 2 ^ 20)
    (hC : FnSpec prog base (addrOf base cs) CswapPre CswapPost)
    (hS : FnSpec prog base (addrOf base sf) StepPre StepPost)
    (pre post : List PInst64) (hprog : prog = pre ++ ladderCode cs sf pre.length ++ post)
    (hlen : 4 * (pre.length + 74) < 2 ^ 20) (P SP : BitVec 64) (K : Nat) (T : X25519State)
    (M : AMem) (hsep : Sep (SP + BitVec.ofInt 64 (-128)) 128 P 576)
    (c : Nat) (st : MState64) (hc : 1 ≤ c) (hI : LoopInv P SP K T M c st)
    (hctr : st.regs.get "s1" = BitVec.ofNat 64 c) :
    ∃ m st', steps prog base m ⟨addrOf base (pre.length + 21), st⟩
        = some ⟨addrOf base (pre.length + 58), st'⟩ ∧
      LoopInv P SP K T M (c - 1) st' ∧ st'.regs.get "s1" = BitVec.ofNat 64 (c - 1) := by
  obtain ⟨hs0, hsp, hc255, hval, hz2, hz3, ⟨sx, hh, hK, hT⟩, hM⟩ := hI
  have hlp := lpro_length
  -- the bit
  have hbit : topBit (st.regs.get "s6") = sx.scalar / 2 ^ (c - 1) % 2 := by
    rw [topBit_val4, hval, hK, bit_shifted K c hc hc255]
  generalize hB : topBit (st.regs.get "s6") = B at hbit
  -- the first swap
  obtain ⟨n1, st1, r1, a1, a2, af, fs1, sp1⟩ := swapCall_run prog base hb cs hcs hC
    (pre ++ lpro.map .x) (ltail1 cs sf pre.length ++ post) "x2" "x3" (pre.length + 21)
    (by simp [hlp]) (by rw [hprog]; simp [ladderCode]) (by omega) (by decide) (by decide)
    (by decide) st
  simp only [hs0, hB] at a1 a2 af
  have e10 : st1.regs.get "s0" = P := (fs1 ("s0", 0) (by decide)).trans hs0
  have e16 : st1.regs.get "s6" = st.regs.get "s6" := fs1 ("s6", 48) (by decide)
  -- the second swap
  obtain ⟨n2, st2, r2, b1, b2, bf, fs2, sp2⟩ := swapCall_run prog base hb cs hcs hC
    (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3")
    (ltail2 cs sf pre.length ++ post) "z2" "z3" (pre.length + 27)
    (by simp [hlp, swapCall, swapSet]) (by rw [hprog]; simp [ladderCode, ltail1])
    (by omega) (by decide) (by decide) (by decide) st1
  simp only [e10, e16, hB] at b1 b2 bf
  have e20 : st2.regs.get "s0" = P := (fs2 ("s0", 0) (by decide)).trans e10
  have e26 : st2.regs.get "s6" = st.regs.get "s6" := (fs2 ("s6", 48) (by decide)).trans e16
  have esp2 : st2.regs.get "sp" = SP := sp2.trans (sp1.trans hsp)
  obtain ⟨H2, z2e, z3e⟩ := holds_swap _ _ _ P sx B hh a1 a2 af b1 b2 bf
  -- the step
  obtain ⟨n3, st3, r3, H3, l2, l3, fs3, sp3, fr3⟩ := stepCall_run prog base hb sf hsf hS
    (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3"
      ++ swapCall cs (pre.length + 27) "z2" "z3")
    (ltail3 cs pre.length ++ post) (pre.length + 33)
    (by simp [hlp, swapCall, swapSet]) (by rw [hprog]; simp [ladderCode, ltail1, ltail2])
    (by omega) st2 (by rw [esp2, e20]; exact hsep)
    (by rw [e20, z2e]; exact le_ite hz3 hz2) (by rw [e20, z3e]; exact le_ite hz2 hz3) _
    (by rw [e20]; exact H2)
  simp only [e20] at H3 l2 l3
  simp only [esp2, e20] at fr3
  have e30 : st3.regs.get "s0" = P := (fs3 ("s0", 0) (by decide)).trans e20
  have e36 : st3.regs.get "s6" = st.regs.get "s6" := (fs3 ("s6", 48) (by decide)).trans e26
  have esp3 : st3.regs.get "sp" = SP := sp3.trans esp2
  -- the second pair of swaps
  obtain ⟨n4, st4, r4, c1, c2, cf, fs4, sp4⟩ := swapCall_run prog base hb cs hcs hC
    (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3"
      ++ swapCall cs (pre.length + 27) "z2" "z3" ++ stepCall sf (pre.length + 33))
    (ltail4 cs pre.length ++ post) "x2" "x3" (pre.length + 35)
    (by simp [hlp, swapCall, swapSet, stepCall])
    (by rw [hprog]; simp [ladderCode, ltail1, ltail2, ltail3]) (by omega) (by decide) (by decide)
    (by decide) st3
  simp only [e30, e36, hB] at c1 c2 cf
  have e40 : st4.regs.get "s0" = P := (fs4 ("s0", 0) (by decide)).trans e30
  have e46 : st4.regs.get "s6" = st.regs.get "s6" := (fs4 ("s6", 48) (by decide)).trans e36
  obtain ⟨n5, st5, r5, d1, d2, df, fs5, sp5⟩ := swapCall_run prog base hb cs hcs hC
    (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3"
      ++ swapCall cs (pre.length + 27) "z2" "z3" ++ stepCall sf (pre.length + 33)
      ++ swapCall cs (pre.length + 35) "x2" "x3")
    (ltail5 ++ post) "z2" "z3" (pre.length + 41)
    (by simp [hlp, swapCall, swapSet, stepCall])
    (by rw [hprog]; simp [ladderCode, ltail1, ltail2, ltail3, ltail4]) (by omega) (by decide)
    (by decide) (by decide) st4
  simp only [e40, e46, hB] at d1 d2 df
  obtain ⟨H5, z2f, z3f⟩ := holds_swap _ _ _ P _ B H3 c1 c2 cf d1 d2 df
  have e50 : st5.regs.get "s0" = P := (fs5 ("s0", 0) (by decide)).trans e40
  have esp5 : st5.regs.get "sp" = SP := sp5.trans (sp4.trans esp3)
  -- the shift
  have hshape : prog = (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3"
      ++ swapCall cs (pre.length + 27) "z2" "z3" ++ stepCall sf (pre.length + 33)
      ++ swapCall cs (pre.length + 35) "x2" "x3" ++ swapCall cs (pre.length + 41) "z2" "z3")
      ++ shiftDec.map .x ++ ((.bne "s1" "zero" (BitVec.ofInt 13 (-148)) ::
        (lepi.map .x ++ [.jalr "zero" "ra" 0])) ++ post) := by
    rw [hprog]; simp [ladderCode, ltail1, ltail2, ltail3, ltail4, ltail5]
  have r6 := steps_block_of (base := base) hshape (by simp [hlp, swapCall, swapSet, stepCall, shiftDec]; omega) st5
  simp only [List.length_append, List.length_map, hlp, swapCall, swapSet, stepCall, shiftDec,
    List.length_cons, List.length_nil] at r6
  obtain ⟨m6, v6, s16⟩ := shiftDec_run st5
  have hfs6 := fun r hr => runX_frame shiftDec st5 r (shiftDec_writes r hr)
  -- the registers kept
  have k5 : ∀ r ∈ frameSlots, st5.regs.get r.1 = st.regs.get r.1 := fun r hr =>
    ((((fs5 r hr).trans (fs4 r hr)).trans (fs3 r hr)).trans (fs2 r hr)).trans (fs1 r hr)
  refine ⟨n1 + n2 + n3 + n4 + n5 + 11, runX st5 shiftDec, ?_, ⟨?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show pre.length + 21 + 6 = pre.length + 27 by omega] at r1
    rw [show pre.length + 27 + 6 = pre.length + 33 by omega] at r2
    rw [show pre.length + 33 + 2 = pre.length + 35 by omega] at r3
    rw [show pre.length + 35 + 6 = pre.length + 41 by omega] at r4
    rw [show pre.length + 41 + 6 = pre.length + 47 by omega] at r5
    rw [show pre.length + 58 = pre.length + 47 + 11 by omega]
    exact steps_trans (steps_trans (steps_trans (steps_trans (steps_trans r1 r2) r3) r4) r5) r6
  · rw [hfs6 "s0" (by simp), e50]
  · rw [hfs6 "sp" (by simp), esp5]
  · rw [v6, val4_congr _ _ (k5 ("s3", 24) (by decide)) (k5 ("s4", 32) (by decide))
      (k5 ("s5", 40) (by decide)) (k5 ("s6", 48) (by decide)), hval]
    exact shift_inv K c hc hc255
  · rw [m6, z2f]; exact (lt_ite l3 l2).le.trans (by omega)
  · rw [m6, z3f]; exact (lt_ite l2 l3).le.trans (by omega)
  · refine ⟨x25519LadderStepVerified (c - 1) sx, ?_, ?_, ?_⟩
    · rw [m6, step_eq, ← hbit]; exact H5
    · rw [step_eq, cswap_scalar]; exact (cswap_scalar _ _).trans hK
    · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      exact hT
  · intro x hx hx'
    rw [m6, df x (sep_field P x "z2" (by decide) hx') (sep_field P x "z3" (by decide) hx'),
      cf x (sep_field P x "x2" (by decide) hx') (sep_field P x "x3" (by decide) hx'),
      fr3 x hx hx',
      bf x (sep_field P x "z2" (by decide) hx') (sep_field P x "z3" (by decide) hx'),
      af x (sep_field P x "x2" (by decide) hx') (sep_field P x "x3" (by decide) hx')]
    exact hM x hx hx'
  · rw [s16, k5 ("s1", 8) (by decide), hctr]
    exact ofNat_pred c hc (by omega)

/-! ## The prologue and the epilogue -/

theorem writeSlots_snoc (m : AMem) (b : BitVec 64) (l : List (Nat × BitVec 64)) (o : Nat)
    (v : BitVec 64) :
    writeSlots m b (l ++ [(o, v)]) = CatCrypt.Crypto.SecureCompilation.Memory64.write64
      (writeSlots m b l) (b + BitVec.ofNat 64 o) v := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih => exact ih _

/-- The saved words of the ladder function: `s0..s11`, `a0` and `ra`. -/
def lsaved (R : String → BitVec 64) : List (Nat × BitVec 64) := saved R ++ [(104, R "ra")]

theorem lpro_run (st : MState64) :
    (runX st lpro).regs.get "sp" = st.regs.get "sp" + BitVec.ofInt 64 (-112) ∧
      (runX st lpro).regs.get "s0" = st.regs.get "a0" ∧
      (runX st lpro).regs.get "s1" = BitVec.ofNat 64 255 ∧
      (runX st lpro).mem = writeSlots st.mem (st.regs.get "sp" + BitVec.ofInt 64 (-112))
        (lsaved st.regs.get) ∧
      val4 (runX st lpro).regs.get = memLimbs4 (runX st lpro).mem (st.regs.get "a0") := by
  rw [lpro, runX_append, pro_run]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [runX_cons, runX_nil, evalX, evalMInst64, evalRInst64, addr]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [get_zero]; rfl
  · simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rw [lsaved, writeSlots_snoc]; rfl
  · unfold val4 memLimbs4
    simp only [RState64.get_set_same, RState64.get_set_other, ne_eq, String.reduceEq,
      not_false_eq_true, or_self]
    rfl

theorem lepi_run (t : MState64) :
    (runX t lepi).mem = t.mem ∧
      (runX t lepi).regs.get "sp" = t.regs.get "sp" + BitVec.ofNat 64 112 ∧
      (runX t lepi).regs.get "ra" = read64 t.mem (t.regs.get "sp" + BitVec.ofNat 64 104) ∧
      ∀ q ∈ frameSlots, (runX t lepi).regs.get q.1
        = read64 t.mem (t.regs.get "sp" + BitVec.ofNat 64 q.2) := by
  rw [lepi, runX_cons]
  obtain ⟨e1, e2, e3⟩ := epilogue_run (evalX t (.ld "ra" "sp" 104))
  have hsp : (evalX t (.ld "ra" "sp" 104)).regs.get "sp" = t.regs.get "sp" := by
    simp only [evalX, RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true]
  have hm : (evalX t (.ld "ra" "sp" 104)).mem = t.mem := rfl
  simp only [hsp, hm] at e2 e3
  rw [hm] at e1
  refine ⟨e1, e2, ?_, e3⟩
  rw [runX_frame _ _ _ (by decide)]
  simp only [evalX, addr, RState64.get_set_same, String.reduceEq, not_false_eq_true, or_self]
  rfl

/-! ## The ladder as a function -/

open CatCrypt.Util.Fp25519 (fromNat)

/-- The ladder state the block at `P` holds: the coordinates at their offsets, the scalar in
    the first 32 bytes. -/
def blockState (m : AMem) (P : BitVec 64) : X25519State :=
  { x2 := fromNat (fe m P "x2"), z2 := fromNat (fe m P "z2"), x3 := fromNat (fe m P "x3"),
    z3 := fromNat (fe m P "z3"), scalar := memLimbs4 m P, baseX := fromNat (fe m P "x1") }

/-- The entry condition of the ladder function: the 240 bytes below `sp` are disjoint from
    the 576-byte state block at `a0`, `z2` and `z3` are at most `2·p25519`, and `sp` and
    `a0` are 16- and 8-byte aligned. The proof does not use the alignment: it is the
    contract under which the function's accesses are aligned (`RiscvMem64`, "Alignment"),
    and the internal calls pass `sp` lowered by multiples of 16 and `a0` plus multiples of
    32. -/
def LadderPre (st : MState64) : Prop :=
  Sep (st.regs.get "sp" + BitVec.ofInt 64 (-240)) 240 (st.regs.get "a0") 576 ∧
    fe st.mem (st.regs.get "a0") "z2" ≤ 2 * p25519 ∧ fe st.mem (st.regs.get "a0") "z3" ≤ 2 * p25519 ∧
    Aligned 16 (st.regs.get "sp") ∧ Aligned 8 (st.regs.get "a0")

/-- The effect of the ladder function: the block holds the 255-step ladder of the state it
    held, `s0..s11`, `sp` and `ra` are restored, and no byte outside the frames below `sp`
    and the field region of the block has changed. -/
def LadderPost (st st' : MState64) : Prop :=
  Holds st'.mem (st.regs.get "a0") (ladderN 255 (blockState st.mem (st.regs.get "a0"))) ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra" ∧
    ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-240)) 240 x 1 →
      Sep (st.regs.get "a0" + BitVec.ofNat 64 32) 544 x 1 → st'.mem x = st.mem x

theorem addr1 (S : BitVec 64) :
    S + BitVec.ofInt 64 (-112) + BitVec.ofInt 64 (-128) = S + BitVec.ofInt 64 (-240) := by
  rw [BitVec.add_assoc,
    show BitVec.ofInt 64 (-112) + BitVec.ofInt 64 (-128) = BitVec.ofInt 64 (-240) by decide]

theorem addr4 (S : BitVec 64) (o : Nat) :
    S + BitVec.ofInt 64 (-112) + BitVec.ofNat 64 o
      = S + BitVec.ofInt 64 (-240) + BitVec.ofNat 64 (128 + o) := by
  rw [show BitVec.ofInt 64 (-112) = BitVec.ofInt 64 (-240) + BitVec.ofNat 64 128 by decide,
    ← BitVec.add_assoc, add_ofNat_add]

theorem addr3 (S : BitVec 64) : S + BitVec.ofInt 64 (-112) + BitVec.ofNat 64 112 = S := by
  rw [BitVec.add_assoc, show BitVec.ofInt 64 (-112) + BitVec.ofNat 64 112 = 0 by decide]
  simp

theorem memLimbs4_lt (m : AMem) (p : BitVec 64) : memLimbs4 m p < 2 ^ 256 := by
  unfold memLimbs4
  have := (read64 m (p + BitVec.ofNat 64 0)).isLt
  have := (read64 m (p + BitVec.ofNat 64 8)).isLt
  have := (read64 m (p + BitVec.ofNat 64 16)).isLt
  have := (read64 m (p + BitVec.ofNat 64 24)).isLt
  omega

theorem sep_head {a b : BitVec 64} {n m : Nat} (h : Sep a n b m) (w : Nat) (hw : w ≤ m) :
    Sep a n b w := ⟨h.1, le_trans hw h.2⟩

theorem lsaved_offs (R : String → BitVec 64) : ∀ q ∈ lsaved R, q.1 + 8 ≤ 112 := by
  intro q hq
  simp only [lsaved, saved, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

theorem lsaved_mem (R : String → BitVec 64) :
    (∀ q ∈ frameSlots, (q.2, R q.1) ∈ lsaved R) ∧ (104, R "ra") ∈ lsaved R := by
  refine ⟨fun q hq => ?_, by simp [lsaved]⟩
  simp only [frameSlots, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [lsaved, saved]

theorem read_lsaved (m : AMem) (b : BitVec 64) (R : String → BitVec 64) (o : Nat)
    (v : BitVec 64) (h : (o, v) ∈ lsaved R) :
    read64 (writeSlots m b (lsaved R)) (b + BitVec.ofNat 64 o) = v :=
  read64_writeSlots_mem _ _ _ o v h (by simp only [lsaved, saved, List.cons_append,
      List.nil_append, List.map_cons, List.map_nil]; decide)
    (by simp only [lsaved, saved, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        decide)
    (by simp only [lsaved, saved, List.cons_append, List.nil_append, List.map_cons, List.map_nil]
        decide)

/-- **The ladder is a function.** `ladderCode` placed in any program, with a swap function
    at `cs` and a step function at `sf`, meets `FnSpec` with `LadderPre` and `LadderPost`. -/
theorem fnSpec_ladder (prog : List PInst64) (base : BitVec 64) (hb : base &&& 3 = 0)
    (cs sf : Nat) (hcs : 4 * cs < 2 ^ 20) (hsf : 4 * sf < 2 ^ 20)
    (hC : FnSpec prog base (addrOf base cs) CswapPre CswapPost)
    (hS : FnSpec prog base (addrOf base sf) StepPre StepPost)
    (pre post : List PInst64) (hprog : prog = pre ++ ladderCode cs sf pre.length ++ post)
    (hlen : 4 * (pre.length + 74) < 2 ^ 20) :
    FnSpec prog base (addrOf base pre.length) LadderPre LadderPost := by
  intro st ⟨hsep, hz2, hz3, _, _⟩
  generalize hS0 : st.regs.get "sp" = S at hsep
  generalize hP : st.regs.get "a0" = P at hsep hz2 hz3
  have hlp := lpro_length
  -- the prologue
  have hshape0 : prog = pre ++ lpro.map .x ++
      ((swapCall cs (pre.length + 21) "x2" "x3" ++ ltail1 cs sf pre.length) ++ post) := by
    rw [hprog]; simp [ladderCode]
  have r0 := steps_block_of (base := base) hshape0 (by simp [hlp]; omega) st
  rw [hlp] at r0
  obtain ⟨q1, q2, q3, q4, q5⟩ := lpro_run st
  rw [hS0] at q1 q4
  rw [hP] at q2 q5
  generalize hst1 : runX st lpro = st1 at r0 q1 q2 q3 q4 q5
  have hsepP : Sep (S + BitVec.ofInt 64 (-112)) 112 P 576 := by
    rw [show S + BitVec.ofInt 64 (-112) = S + BitVec.ofInt 64 (-240) + BitVec.ofNat 64 128 by
      rw [← addr4 S 0]; simp]
    exact sep_shift hsep 128 112 (by decide) (by decide) (by decide)
  have hfe1 : ∀ p ∈ ladderPfx, fe st1.mem P p = fe st.mem P p := by
    intro p hp
    unfold fe
    rw [q4, memLimbs4_writeSlots_sepN _ _ _ _ 112 (by decide) (lsaved_offs _)
      (sep_sub hsepP (off p) 32 (by decide) (off_lt p hp).2 (by decide))]
  have hK1 : memLimbs4 st1.mem P = memLimbs4 st.mem P := by
    rw [q4, memLimbs4_writeSlots_sepN _ _ _ _ 112 (by decide) (lsaved_offs _)
      (sep_head hsepP 32 (by decide))]
  have hsepL : Sep (S + BitVec.ofInt 64 (-112) + BitVec.ofInt 64 (-128)) 128 P 576 := by
    rw [addr1]; exact sep_shrink hsep 128 (by decide)
  have hinit : LoopInv P (S + BitVec.ofInt 64 (-112)) (memLimbs4 st.mem P)
      (ladderN 255 (blockState st.mem P)) st1.mem 255 st1 := by
    refine ⟨q2, q1, le_refl _, ?_, ?_, ?_, ⟨blockState st.mem P, ?_, rfl, rfl⟩, fun _ _ _ => rfl⟩
    · rw [q5, hK1, Nat.sub_self, pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (memLimbs4_lt _ _)]
    · rw [hfe1 _ (by decide)]; exact hz2
    · rw [hfe1 _ (by decide)]; exact hz3
    · exact ⟨by rw [hfe1 _ (by decide)]; rfl, by rw [hfe1 _ (by decide)]; rfl,
        by rw [hfe1 _ (by decide)]; rfl, by rw [hfe1 _ (by decide)]; rfl,
        by rw [hfe1 _ (by decide)]; rfl⟩
  -- the loop
  have hbne : prog[pre.length + 58]? = some (.bne "s1" "zero"
      (BitVec.ofInt 13 (-(4 * (pre.length + 58 - (pre.length + 21) : Nat) : Int)))) := by
    rw [show pre.length + 58 - (pre.length + 21) = 37 by omega, hprog,
      getElem?_mid pre _ _ 58 (by rw [ladderCode_length]; decide)]
    rfl
  obtain ⟨m2, st2, r2, hI0⟩ := steps_loop_inv prog base (pre.length + 21) (pre.length + 58) "s1"
    (by omega) (by omega) (by omega) hbne _
    (fun c st hc hI hctr => loop_body prog base hb cs sf hcs hsf hC hS pre post hprog hlen P _ _ _ _
      hsepL c st hc hI hctr) 255 st1 (by decide) (by decide) hinit q3
  obtain ⟨-, hsp2, -, -, -, -, ⟨sx, hh2, -, hT⟩, hM2⟩ := hI0
  -- the epilogue
  have hshapeE : prog = (pre ++ lpro.map .x ++ swapCall cs (pre.length + 21) "x2" "x3"
      ++ swapCall cs (pre.length + 27) "z2" "z3" ++ stepCall sf (pre.length + 33)
      ++ swapCall cs (pre.length + 35) "x2" "x3" ++ swapCall cs (pre.length + 41) "z2" "z3"
      ++ shiftDec.map .x ++ [.bne "s1" "zero" (BitVec.ofInt 13 (-148))])
      ++ lepi.map .x ++ ([.jalr "zero" "ra" 0] ++ post) := by
    rw [hprog]; simp [ladderCode, ltail1, ltail2, ltail3, ltail4, ltail5]
  have r3 := steps_block_of (base := base) hshapeE
    (by simp [hlp, lepi_length, swapCall, swapSet, stepCall, shiftDec]; omega) st2
  simp only [List.length_append, List.length_map, hlp, lepi_length, swapCall, swapSet, stepCall,
    shiftDec, List.length_cons, List.length_nil] at r3
  obtain ⟨w1, w2, w3, w4⟩ := lepi_run st2
  rw [hsp2] at w2 w3 w4
  generalize hst3 : runX st2 lepi = st3 at r3 w1 w2 w3 w4
  -- the saved words
  have hslot : ∀ o v, (o, v) ∈ lsaved st.regs.get →
      read64 st2.mem (S + BitVec.ofInt 64 (-112) + BitVec.ofNat 64 o) = v := by
    intro o v hov
    have ho := lsaved_offs _ _ hov
    simp only at ho
    rw [← read_lsaved st.mem (S + BitVec.ofInt 64 (-112)) st.regs.get o v hov, ← q4]
    refine read64_congr _ _ _ fun j hj => ?_
    rw [add_ofNat_add]
    refine hM2 _ ?_ ?_
    · rw [addr1, addr4]
      exact sep_after _ 128 (128 + (o + j)) (by omega) (by omega) (by omega)
    · rw [addr4]
      exact sep_symm' (sep_sub (sep_shift hsep (128 + (o + j)) 1 (by decide) (by omega)
        (by decide)) 32 544 (by decide) (by decide) (by decide))
  have hra : st3.regs.get "ra" = st.regs.get "ra" := by
    rw [w3]; exact hslot 104 _ (lsaved_mem _).2
  have q6 : steps prog base 1 ⟨addrOf base (pre.length + 59 + 14), st3⟩
      = some ⟨st.regs.get "ra" &&& ~~~1, st3⟩ := by
    have e : prog[pre.length + 59 + 14]? = some (.jalr "zero" "ra" 0) := by
      rw [hprog, show pre.length + 59 + 14 = pre.length + 73 by omega,
        getElem?_mid pre _ _ 73 (by rw [ladderCode_length]; decide)]
      rfl
    simp only [steps, step, fetch_addrOf prog base (pre.length + 59 + 14) (by omega), e,
      Option.bind_some, hra]
    rw [set_zero _ _ (Or.inl rfl)]
    simp
  refine ⟨21 + m2 + 14 + 1, st3, ?_, ?_, ?_, ?_, hra, ?_⟩
  · have r3' : steps prog base 14 ⟨addrOf base (pre.length + 58 + 1), st2⟩
        = some ⟨addrOf base (pre.length + 59 + 14), st3⟩ := by
      rw [show pre.length + 58 + 1 = pre.length + 59 by omega]
      convert r3 using 3
    exact steps_trans (steps_trans (steps_trans r0 r2) r3') q6
  · rw [hP, w1]
    rw [show ladderN 0 sx = sx from rfl] at hT
    rw [← hT]; exact hh2
  · intro q hq
    rw [w4 q hq]
    exact hslot q.2 _ ((lsaved_mem _).1 q hq)
  · rw [w2, addr3, hS0]
  · intro x hx hx'
    rw [hS0] at hx
    rw [hP] at hx'
    rw [w1, hM2 x (by rw [addr1]; exact sep_shrink hx 128 (by decide)) hx', q4,
      writeSlots_out _ _ _ _ fun q hq => not_inRange_of_out
        (out_of_sep (by
          rw [show S + BitVec.ofInt 64 (-112) = S + BitVec.ofInt 64 (-240) + BitVec.ofNat 64 128 by
            rw [← addr4 S 0]; simp]
          exact sep_shift hx 128 112 (by decide) (by decide) (by decide)) (by simp))
        (lsaved_offs _ q hq) (by decide)]


end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvX25519LadderLoopProof
