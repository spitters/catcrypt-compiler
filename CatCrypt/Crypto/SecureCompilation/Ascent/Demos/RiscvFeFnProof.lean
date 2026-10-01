/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64

/-!
# The RV64 Curve25519 field operations as leaf functions

`RiscvFeMulFnProof.feMulFn` wraps the register kernel `feMulPhys` into a buffer function.
`bufFn k` is the same wrapper over any register kernel `k` with inputs in `a0..a3`,
`a4..a7` and the result in `a0..a3`, and `fnCode k` follows it with the return
`jalr zero, 0(ra)`, so it is a function of the program-counter machine
`RiscvPc64`. `cswapFn` is the conditional swap of two field elements in memory.

## Main results

* `bufFn_run`: from a specification `F` of `k` under a precondition `Pre`, the buffer
  function leaves `F x y` at `a0`, restores `s0..s11` and `sp`, and changes no byte outside
  its frame and the output buffer.
* `fnSpec_buf`: `fnCode k` placed in any program meets `FnSpec` with `BufPre Pre` and
  `BufPost F`.
* `cswapFn_run`, `fnSpec_cswap`: the conditional swap, and its `FnSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof

open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvBytes64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvMem64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvPc64
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvX25519FieldKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.RiscvMacros
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeMulFnProof
open CatCrypt.Crypto.SecureCompilation.Memory64
  (AMem read64 write64 InRange8 Disjoint8 read64_write64_same read64_write64_of_disjoint
    write64_of_not_inRange)

/-- The buffer function of a register kernel `k` with inputs in `a0..a3`, `a4..a7` and the
    result in `a0..a3`. -/
def bufFn (k : List MInst64) : List XInst64 := prologue ++ loads ++ k.map .m ++ storeZ ++ epilogue

theorem feMulFn_eq : feMulFn = bufFn RiscvMulBytesProof.feMulPhys := rfl

theorem bufFn_run (k : List MInst64) (F : Nat → Nat → Nat) (Pre : Nat → Nat → Prop)
    (hk : ∀ r : RState64, Pre (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7") →
      limbs4 (runM64 r k).get "a0" "a1" "a2" "a3"
        = F (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7"))
    (hsp : "sp" ∉ mWrites k) (s : MState64)
    (hx : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a1") 32)
    (hy : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a2") 32)
    (hz : Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (s.regs.get "a0") 32)
    (hpre : Pre (memLimbs4 s.mem (s.regs.get "a1")) (memLimbs4 s.mem (s.regs.get "a2"))) :
    memLimbs4 (runX s (bufFn k)).mem (s.regs.get "a0")
        = F (memLimbs4 s.mem (s.regs.get "a1")) (memLimbs4 s.mem (s.regs.get "a2")) ∧
      (∀ q ∈ frameSlots, (runX s (bufFn k)).regs.get q.1 = s.regs.get q.1) ∧
      (runX s (bufFn k)).regs.get "sp" = s.regs.get "sp" ∧
      ∀ x, Sep (s.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 x 1 →
        Sep (s.regs.get "a0") 32 x 1 → (runX s (bufFn k)).mem x = s.mem x := by
  have e : runX s (bufFn k)
      = runX (runX (runX (runX (runX s prologue) loads) (k.map .m)) storeZ) epilogue := by
    simp only [bufFn, runX_append]
  rw [e, pro_run, runX_lift]
  generalize hf : s.regs.get "sp" + BitVec.ofInt 64 (-112) = f at hx hy hz ⊢
  generalize hM1 : writeSlots s.mem f (saved s.regs.get) = M1
  obtain ⟨l1, l2, l3, l4⟩ := loads_run ⟨s.regs.set "sp" f, M1⟩
  generalize ht2 : runX ⟨s.regs.set "sp" f, M1⟩ loads = t2 at l1 l2 l3 l4
  have b2 := runM64_frame k t2.regs "sp" hsp
  obtain ⟨z1, z2⟩ := storeZ_run ⟨runM64 t2.regs k, t2.mem⟩
  generalize ht4 : runX ⟨runM64 t2.regs k, t2.mem⟩ storeZ = t4 at z1 z2
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
    have zl := fun o v (hmem : (o, v) ∈ [(0, (runM64 t2.regs k).get "a0"),
        (8, (runM64 t2.regs k).get "a1"), (16, (runM64 t2.regs k).get "a2"),
        (24, (runM64 t2.regs k).get "a3")]) =>
      read64_writeSlots_mem M1 (s.regs.get "a0") _ o v hmem
        (by simp only [List.map_cons, List.map_nil]; decide)
        (by simp only [List.map_cons, List.map_nil]; decide)
        (by simp only [List.map_cons, List.map_nil]; decide)
    have hzv : memLimbs4 (writeSlots M1 (s.regs.get "a0")
        [(0, (runM64 t2.regs k).get "a0"), (8, (runM64 t2.regs k).get "a1"),
          (16, (runM64 t2.regs k).get "a2"), (24, (runM64 t2.regs k).get "a3")])
        (s.regs.get "a0") = limbs4 (runM64 t2.regs k).get "a0" "a1" "a2" "a3" := by
      unfold memLimbs4 limbs4
      rw [zl 0 ((runM64 t2.regs k).get "a0") (by simp),
        zl 8 ((runM64 t2.regs k).get "a1") (by simp),
        zl 16 ((runM64 t2.regs k).get "a2") (by simp),
        zl 24 ((runM64 t2.regs k).get "a3") (by simp)]
    have hx' : memLimbs4 M1 (s.regs.get "a1") = memLimbs4 s.mem (s.regs.get "a1") := by
      rw [← hM1, memLimbs4_writeSlots_sep _ _ _ _ hsep hx]
    have hy' : memLimbs4 M1 (s.regs.get "a2") = memLimbs4 s.mem (s.regs.get "a2") := by
      rw [← hM1, memLimbs4_writeSlots_sep _ _ _ _ hsep hy]
    rw [hzv, hk t2.regs (by rw [l3, l4, hx', hy']; exact hpre), l3, l4, hx', hy']
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


/-! ## Leaf functions -/

theorem xWrites_append (a b : List XInst64) : xWrites (a ++ b) = xWrites a ++ xWrites b := by
  simp [xWrites, List.filterMap_append]

theorem xWrites_map_m (k : List MInst64) : xWrites (k.map .m) = mWrites k := by
  induction k with
  | nil => rfl
  | cons i is ih => simp only [List.map_cons, xWrites, List.filterMap_cons, xDst] at ih ⊢; rw [ih]; rfl

theorem bufFn_ra (k : List MInst64) (h : "ra" ∉ mWrites k) : "ra" ∉ xWrites (bufFn k) := by
  simp only [bufFn, xWrites_append, xWrites_map_m, List.mem_append, not_or]
  exact ⟨⟨⟨⟨by decide, by decide⟩, h⟩, by decide⟩, by decide⟩

/-- The code of a leaf function: the buffer function of `k`, then `jalr zero, 0(ra)`. -/
def fnCode (k : List MInst64) : List PInst64 := (bufFn k).map .x ++ [.jalr "zero" "ra" 0]

/-- The entry condition of a buffer function: its frame is disjoint from the three buffers,
    and the operands meet `Pre`. -/
def BufPre (Pre : Nat → Nat → Prop) (st : MState64) : Prop :=
  Sep (st.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (st.regs.get "a1") 32 ∧
    Sep (st.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (st.regs.get "a2") 32 ∧
    Sep (st.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 (st.regs.get "a0") 32 ∧
    Pre (memLimbs4 st.mem (st.regs.get "a1")) (memLimbs4 st.mem (st.regs.get "a2"))

/-- The effect of a buffer function: `F x y` at `a0`; `s0..s11`, `sp` and `ra` restored;
    memory outside the frame and the output buffer unchanged. -/
def BufPost (F : Nat → Nat → Nat) (st st' : MState64) : Prop :=
  memLimbs4 st'.mem (st.regs.get "a0")
      = F (memLimbs4 st.mem (st.regs.get "a1")) (memLimbs4 st.mem (st.regs.get "a2")) ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra" ∧
    ∀ x, Sep (st.regs.get "sp" + BitVec.ofInt 64 (-112)) 112 x 1 →
      Sep (st.regs.get "a0") 32 x 1 → st'.mem x = st.mem x

/-- **A buffer function is a function.** -/
theorem fnSpec_buf (pre post : List PInst64) (base : BitVec 64) (k : List MInst64)
    (F : Nat → Nat → Nat) (Pre : Nat → Nat → Prop)
    (hk : ∀ r : RState64, Pre (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7") →
      limbs4 (runM64 r k).get "a0" "a1" "a2" "a3"
        = F (limbs4 r.get "a0" "a1" "a2" "a3") (limbs4 r.get "a4" "a5" "a6" "a7"))
    (hsp : "sp" ∉ mWrites k) (hra : "ra" ∉ mWrites k)
    (hlen : 4 * (pre.length + (bufFn k).length + 1) < 2 ^ 64) :
    FnSpec (pre ++ fnCode k ++ post) base (addrOf base pre.length) (BufPre Pre) (BufPost F) := by
  have e : pre ++ fnCode k ++ post = pre ++ (bufFn k).map .x ++ (.jalr "zero" "ra" 0 :: post) := by
    simp [fnCode]
  rw [e]
  refine fnSpec_weaken (fnSpec_leaf pre post base (bufFn k) (by simpa using hlen)
    (fun st => runX_frame _ st _ (bufFn_ra k hra))) (fun _ _ => trivial) ?_
  rintro st st' ⟨hx, hy, hz, hpre⟩ rfl
  obtain ⟨r1, r2, r3, r4⟩ := bufFn_run k F Pre hk hsp st hx hy hz hpre
  exact ⟨r1, r2, r3, runX_frame _ st _ (bufFn_ra k hra), r4⟩

/-! ## The conditional swap in memory -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvBytesProof (cswapPhys cswapPhys_correct)

/-- Load `A` (pointer `a0`) into `a0..a3` and `B` (pointer `a1`) into `a4..a7`, keeping the
    pointers in `t5`, `t6` and the swap word (`a2`) in `t0`. -/
def cswapLoads : List XInst64 :=
  [.m (.base (.mv "t5" "a0")), .m (.base (.mv "t6" "a1")), .m (.base (.mv "t0" "a2")),
    .ld "a0" "t5" 0, .ld "a1" "t5" 8, .ld "a2" "t5" 16, .ld "a3" "t5" 24,
    .ld "a4" "t6" 0, .ld "a5" "t6" 8, .ld "a6" "t6" 16, .ld "a7" "t6" 24]

/-- Store `a0..a3` to `A` and `a4..a7` to `B`. -/
def cswapStores : List XInst64 :=
  [.sd "a0" "t5" 0, .sd "a1" "t5" 8, .sd "a2" "t5" 16, .sd "a3" "t5" 24,
    .sd "a4" "t6" 0, .sd "a5" "t6" 8, .sd "a6" "t6" 16, .sd "a7" "t6" 24]

/-- **The conditional swap of two field elements in memory.** -/
def cswapFn : List XInst64 := cswapLoads ++ cswapPhys.map .m ++ cswapStores

theorem cswapLoads_run (t : MState64) :
    (runX t cswapLoads).mem = t.mem ∧
      limbs4 (runX t cswapLoads).regs.get "a0" "a1" "a2" "a3" = memLimbs4 t.mem (t.regs.get "a0") ∧
      limbs4 (runX t cswapLoads).regs.get "a4" "a5" "a6" "a7" = memLimbs4 t.mem (t.regs.get "a1") ∧
      (runX t cswapLoads).regs.get "t0" = t.regs.get "a2" ∧
      (runX t cswapLoads).regs.get "t5" = t.regs.get "a0" ∧
      (runX t cswapLoads).regs.get "t6" = t.regs.get "a1" := by
  simp only [cswapLoads, runX_cons, runX_nil, evalX, evalMInst64, addr, true_and]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [limbs4, memLimbs4, evalRInst64, RState64.get_set_same,
    RState64.get_set_other, ne_eq, String.reduceEq, not_false_eq_true, or_self]
  all_goals rfl

theorem cswapStores_run (t : MState64) :
    (runX t cswapStores).mem = writeSlots (writeSlots t.mem (t.regs.get "t5")
        [(0, t.regs.get "a0"), (8, t.regs.get "a1"), (16, t.regs.get "a2"), (24, t.regs.get "a3")])
        (t.regs.get "t6")
        [(0, t.regs.get "a4"), (8, t.regs.get "a5"), (16, t.regs.get "a6"), (24, t.regs.get "a7")] := by
  simp only [cswapStores, runX_cons, runX_nil, evalX, addr, writeSlots]
  rfl

theorem cswap_t56 : "t5" ∉ mWrites cswapPhys ∧ "t6" ∉ mWrites cswapPhys := by decide +kernel

/-- Reading four limbs at `p` through stores at `p` that write `v0..v3` at offsets
    `0, 8, 16, 24`. -/
theorem memLimbs4_writeSlots_self (m : AMem) (p : BitVec 64) (v0 v1 v2 v3 : BitVec 64) :
    memLimbs4 (writeSlots m p [(0, v0), (8, v1), (16, v2), (24, v3)]) p
      = v0.toNat + 2 ^ 64 * v1.toNat + 2 ^ 128 * v2.toNat + 2 ^ 192 * v3.toNat := by
  have h := fun o v (hmem : (o, v) ∈ [(0, v0), (8, v1), (16, v2), (24, v3)]) =>
    read64_writeSlots_mem m p _ o v hmem
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide)
  unfold memLimbs4
  rw [h 0 v0 (by simp), h 8 v1 (by simp), h 16 v2 (by simp), h 24 v3 (by simp)]

theorem memLimbs4_writeSlots_other (m : AMem) (p q : BitVec 64) (l : List (Nat × BitVec 64))
    (hl : ∀ r ∈ l, r.1 + 8 ≤ 32) (h : Sep q 32 p 32) :
    memLimbs4 (writeSlots m q l) p = memLimbs4 m p := by
  unfold memLimbs4
  rw [read64_writeSlots_sep _ _ _ 32 (by decide) _ hl (sep_word h 0 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 32 (by decide) _ hl (sep_word h 8 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 32 (by decide) _ hl (sep_word h 16 (by decide) (by decide)),
    read64_writeSlots_sep _ _ _ 32 (by decide) _ hl (sep_word h 24 (by decide) (by decide))]

theorem slots4_le (v0 v1 v2 v3 : BitVec 64) :
    ∀ r ∈ [(0, v0), (8, v1), (16, v2), (24, v3)], r.1 + 8 ≤ 32 := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp

/-- **The conditional swap.** With `A` at `a0`, `B` at `a1` disjoint, and a swap word `0` or
    `1` in `a2`, the run exchanges `A` and `B` when the word is `1` and leaves them when it
    is `0`; every other byte is unchanged. -/
theorem cswapFn_run (s : MState64) (hsep : Sep (s.regs.get "a0") 32 (s.regs.get "a1") 32)
    (hw : (s.regs.get "a2").toNat ≤ 1) :
    memLimbs4 (runX s cswapFn).mem (s.regs.get "a0") =
        (if (s.regs.get "a2").toNat = 1 then memLimbs4 s.mem (s.regs.get "a1")
          else memLimbs4 s.mem (s.regs.get "a0")) ∧
      memLimbs4 (runX s cswapFn).mem (s.regs.get "a1") =
        (if (s.regs.get "a2").toNat = 1 then memLimbs4 s.mem (s.regs.get "a0")
          else memLimbs4 s.mem (s.regs.get "a1")) ∧
      ∀ x, Sep (s.regs.get "a0") 32 x 1 → Sep (s.regs.get "a1") 32 x 1 →
        (runX s cswapFn).mem x = s.mem x := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := cswapLoads_run s
  have e : runX s cswapFn = runX (runX (runX s cswapLoads) (cswapPhys.map .m)) cswapStores := by
    simp only [cswapFn, runX_append]
  rw [e, runX_lift]
  generalize ht1 : runX s cswapLoads = t1 at l1 l2 l3 l4 l5 l6
  obtain ⟨c1, c2⟩ := cswapPhys_correct t1.regs (by rw [l4]; exact hw)
  have h5 := runM64_frame cswapPhys t1.regs "t5" cswap_t56.1
  have h6 := runM64_frame cswapPhys t1.regs "t6" cswap_t56.2
  rw [cswapStores_run]
  simp only [h5, h6, l5, l6, l1]
  simp only [limbs4] at c1 c2 l2 l3
  refine ⟨?_, ?_, ?_⟩
  · rw [memLimbs4_writeSlots_other _ _ _ _ (slots4_le _ _ _ _) (sep_symm hsep),
      memLimbs4_writeSlots_self, c1, l2, l3, l4]
  · rw [memLimbs4_writeSlots_self, c2, l2, l3, l4]
  · intro x hxa hxb
    rw [writeSlots_out _ _ _ _ fun q hq =>
        not_inRange_of_out (out_of_sep hxb (by simp)) (slots4_le _ _ _ _ q hq) (by decide),
      writeSlots_out _ _ _ _ fun q hq =>
        not_inRange_of_out (out_of_sep hxa (by simp)) (slots4_le _ _ _ _ q hq) (by decide)]

theorem cswapFn_writes : ∀ r ∈ "sp" :: "ra" :: frameSlots.map Prod.fst, r ∉ xWrites cswapFn := by
  decide +kernel

/-- The entry condition of `cswapFn`: disjoint buffers and a `0`/`1` swap word. -/
def CswapPre (st : MState64) : Prop :=
  Sep (st.regs.get "a0") 32 (st.regs.get "a1") 32 ∧ (st.regs.get "a2").toNat ≤ 1

/-- The effect of `cswapFn`. -/
def CswapPost (st st' : MState64) : Prop :=
  memLimbs4 st'.mem (st.regs.get "a0") =
      (if (st.regs.get "a2").toNat = 1 then memLimbs4 st.mem (st.regs.get "a1")
        else memLimbs4 st.mem (st.regs.get "a0")) ∧
    memLimbs4 st'.mem (st.regs.get "a1") =
      (if (st.regs.get "a2").toNat = 1 then memLimbs4 st.mem (st.regs.get "a0")
        else memLimbs4 st.mem (st.regs.get "a1")) ∧
    (∀ x, Sep (st.regs.get "a0") 32 x 1 → Sep (st.regs.get "a1") 32 x 1 → st'.mem x = st.mem x) ∧
    (∀ q ∈ frameSlots, st'.regs.get q.1 = st.regs.get q.1) ∧
    st'.regs.get "sp" = st.regs.get "sp" ∧ st'.regs.get "ra" = st.regs.get "ra"

/-- The code of the swap function. -/
def cswapCode : List PInst64 := cswapFn.map .x ++ [.jalr "zero" "ra" 0]

/-- **The swap is a function.** -/
theorem fnSpec_cswap (pre post : List PInst64) (base : BitVec 64)
    (hlen : 4 * (pre.length + cswapFn.length + 1) < 2 ^ 64) :
    FnSpec (pre ++ cswapCode ++ post) base (addrOf base pre.length) CswapPre CswapPost := by
  have e : pre ++ cswapCode ++ post = pre ++ cswapFn.map .x ++ (.jalr "zero" "ra" 0 :: post) := by
    simp [cswapCode]
  rw [e]
  refine fnSpec_weaken (fnSpec_leaf pre post base cswapFn hlen
    (fun st => runX_frame _ st _ (cswapFn_writes "ra" (by simp)))) (fun _ _ => trivial) ?_
  rintro st st' ⟨hsep, hw⟩ rfl
  obtain ⟨r1, r2, r3⟩ := cswapFn_run st hsep hw
  refine ⟨r1, r2, r3, fun q hq => runX_frame _ st _ (cswapFn_writes q.1 ?_),
    runX_frame _ st _ (cswapFn_writes "sp" (by simp)),
    runX_frame _ st _ (cswapFn_writes "ra" (by simp))⟩
  simp only [List.mem_cons, List.mem_map]
  exact Or.inr (Or.inr ⟨q, hq, rfl⟩)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.RiscvFeFnProof
