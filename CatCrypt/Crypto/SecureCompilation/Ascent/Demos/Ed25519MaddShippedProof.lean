/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedChecksB
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519

/-!
# Correctness of the shipped `ed25519_madd` machine code

`Imported.Ed25519MaddShipped.ed25519MaddShippedBlock` is the body of the function
`ed25519_madd(u64 *out, const u64 *inp)` as printed by the owned backend: fifteen calls
to `fe25519_add`, `fe25519_sub`, `fe25519_mul` and `ed25519_join16` over stack slots,
followed by a sixteen-word copy to the output pointer.

## The model

The block is a `List CallSeg`, so its run is `segsRunA` over the address machine
`AddrMem.AState` at a call model `C`, with the four callees at the specifications of
`Ed25519MaddShippedParts.MaddCallees`. The address machine is the model in which a
callee's write through its own `%rdi` and the caller's access to the same stack slot
are one memory; the name-keyed memory of `JasminModel` keys them as two cells, so
`runBlock` over `canonD shippedBank` states nothing about a block with calls.

## The source

The source of the kernel is `maddLowCT` in `CatCrypt/Crypto/EdDSA/Ed25519CombEmit.lean`
of the `SSProve-lean` tree, whose formula is `Ed25519CombEmit.maddSpec` over `Fp25519`.
That module is not in this package's import closure; `maddSpecR` is the same formula
over a commutative ring, and `maddSpecN_maddSpecR` relates the natural-number
coordinates to it in `ZMod p25519`.

## Main results

* `maddShipped_correct_cross`: at a call model satisfying `MaddCallees`, for stack words
  disjoint from the input point and from the output words and input coordinates below
  `2 ^ 255 - 19`, the four field elements at the output pointer after the block are the
  four coordinates of `maddSpecN` on the input coordinates; the output may alias the
  input. `maddShipped_correct_addr` is the same result for pairwise separated cells.
  `Ed25519LeafCallees.maddCallees_maddCallModel` discharges `MaddCallees` for the model
  the shipped `fe25519_add`, `fe25519_sub`, `fe25519_mul` and `ed25519_join16` blocks
  induce, and `Ed25519LeafCallees.maddShipped_correct` is the separated result at it.
* `maddOut_of_calls`: the output copy after the fifteen calls, over any call model whose
  run reaches the result block.
* `maddSpecN_maddSpecR`: in `ZMod p25519` those coordinates are the coordinates of the
  source formula.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519MaddShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 15. The output copy -/

theorem maddTailCopy (C : ACallModel) (s : AState) :
    segsRunA C s (maddTail 16)
      = runBlockA (runBlockA s [.loadMem "%r10" "%rsp" 584, .lea "%r9" "%rsp" "%rsp" 0 448])
          (copyBlk outOffs) := by
  rw [segsRunA_tail_plain C s 16 (by omega) rfl, segsRunA_tail_plain C _ 17 (by omega) rfl,
    show maddTail 18 = [] from rfl, segsRunA_nil, ← runBlockA_append, ← runBlockA_append]
  rfl

theorem slot_mem_outOffs (k : Nat) (hk : k < 4) (j : Int) (hj : j ∈ limbOffs) :
    slotOff k + j ∈ outOffs := by
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  have hk4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk4 with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;> decide

/-- The copy leaves the four coordinates of the result block at the output pointer. -/
theorem maddOutVal {SP Q : BitVec 64} (hO : CrossOut SP Q) (s : AState)
    (hsp : s.regs "%rsp" = SP) (hq : read64 s.mem (SP + BitVec.ofInt 64 584) = Q)
    (k : Nat) (hk : k < 4) :
    feO (runBlockA (runBlockA s [.loadMem "%r10" "%rsp" 584, .lea "%r9" "%rsp" "%rsp" 0 448])
        (copyBlk outOffs)).mem Q (slotOff k)
      = feO s.mem SP (448 + slotOff k) := by
  obtain ⟨hm, hsp', h10, h9⟩ := runOutSetup s
  rw [hsp] at hsp' h9
  simp only [outPtr, hsp, hq] at h10
  simp only [feO]
  refine congrArg bignumVal (List.map_congr_left fun j hj => ?_)
  rw [copyOut hO _ h10 h9 (slotOff k + j) (slot_mem_outOffs k hk j hj), hm,
    show (448 : Int) + (slotOff k + j) = 448 + slotOff k + j by omega]

/-! ## 16. The correctness of the block -/

/-- **The output copy after the fifteen calls.** When the run of the block under `C`
    reaches a state after the fifteen calls whose `%rsp` is the entry `%rsp`, whose output
    pointer slot holds the entry `%rdi` and whose result block at `%rsp + 448` holds
    `maddSV sa 10` to `maddSV sa 13`, and the stack words are disjoint from the output words
    (`CrossOut`), the four field elements at the output pointer after the block are the four
    coordinates of `maddSpecN` on the input coordinates. -/
theorem maddOut_of_calls {C : ACallModel} (sa : AState)
    (hO : CrossOut (sa.regs "%rsp") (sa.regs "%rdi"))
    (hcalls : ∃ s : AState,
      segsRunA C sa ed25519MaddShippedBlock = segsRunA C s (maddTail 16)
        ∧ s.regs "%rsp" = sa.regs "%rsp"
        ∧ read64 s.mem (sa.regs "%rsp" + BitVec.ofInt 64 584) = sa.regs "%rdi"
        ∧ feO s.mem (sa.regs "%rsp") 448 = maddSV sa 10
        ∧ feO s.mem (sa.regs "%rsp") 480 = maddSV sa 11
        ∧ feO s.mem (sa.regs "%rsp") 512 = maddSV sa 12
        ∧ feO s.mem (sa.regs "%rsp") 544 = maddSV sa 13) :
    feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 := by
  obtain ⟨s, hrun, hsp, hq, v10, v11, v12, v13⟩ := hcalls
  rw [hrun, maddTailCopy]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [maddOutVal hO s hsp hq 0 (by omega), show (448 : Int) + slotOff 0 = 448 by simp [slotOff]]
    exact v10
  · rw [maddOutVal hO s hsp hq 1 (by omega), show (448 : Int) + slotOff 1 = 480 by simp [slotOff]]
    exact v11
  · rw [maddOutVal hO s hsp hq 2 (by omega), show (448 : Int) + slotOff 2 = 512 by simp [slotOff]]
    exact v12
  · rw [maddOutVal hO s hsp hq 3 (by omega), show (448 : Int) + slotOff 3 = 544 by simp [slotOff]]
    exact v13

/-- **The shipped `ed25519_madd` computes the mixed addition, with an output that may alias
    its input.** For a state whose stack words are disjoint from the input point
    (`CrossIn`) and from the output words (`CrossOut`) and whose seven input coordinates are
    below `2 ^ 255 - 19`, and for a call model whose four callees meet their
    specifications, the four field elements at the output pointer after the block are the
    four coordinates of `maddSpecN` on those inputs. The input and output buffers may
    overlap. -/
theorem maddShipped_correct_cross {C : ACallModel} (hC : MaddCallees C) (sa : AState)
    (hX : CrossIn (sa.regs "%rsp") (sa.regs "%rsi"))
    (hO : CrossOut (sa.regs "%rsp") (sa.regs "%rdi"))
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddOut_of_calls sa hO (maddCallsRun hC sa hX hb)

/-- **The shipped `ed25519_madd` computes the mixed addition, for separated cells.** For a
    state whose input point, output buffer and stack frame occupy pairwise disjoint
    eight-byte cells and whose seven input coordinates are below `2 ^ 255 - 19`, and for a
    call model whose four callees meet their specifications, the four field elements at the
    output pointer after the block are the four coordinates of `maddSpecN` on those inputs.
    This is `maddShipped_correct_cross` with `CrossIn` and `CrossOut` read off the
    separation. -/
theorem maddShipped_correct_addr {C : ACallModel} (hC : MaddCallees C) (sa : AState)
    (hsep : Separated shippedBank sa.regs maddCells)
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA C sa ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddShipped_correct_cross hC sa (fun o o' a b c d e f => djIS hsep o o' a b c d e f)
    (fun o o' a b c d e f => djOS hsep o o' a b c d e f) hb

/-! ## 17. The coordinates of the source formula -/

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (p25519)

/-- The mixed-addition formula over a commutative ring: the accumulator coordinates
    `(x1, y1, z1, t1)` and the three coordinates `(ypx, ymx, t2d)` of the added point. -/
def maddSpecR {R : Type} [CommRing R] (x1 y1 z1 t1 ypx ymx t2d : R) : R × R × R × R :=
  let a := (y1 + x1) * ypx
  let b := (y1 - x1) * ymx
  let c := t1 * t2d
  let d := z1 + z1
  let e := a - b
  let h := a + b
  let g := d + c
  let f := d - c
  (e * f, h * g, g * f, e * h)

theorem mod_lt_pM (a : Nat) : a % pM < pM := Nat.mod_lt _ pM_pos

theorem cast_mod_pM (a : Nat) : ((a % pM : Nat) : ZMod p25519) = (a : ZMod p25519) :=
  ZMod.natCast_mod a _

theorem cast_sub_pM (x : Nat) (h : x ≤ pM) :
    (((pM - x : Nat)) : ZMod p25519) = -(x : ZMod p25519) := by
  rw [Nat.cast_sub h]
  show (p25519 : ZMod p25519) - (x : ZMod p25519) = _
  rw [ZMod.natCast_self]
  ring

/-- **The natural-number coordinates are the coordinates of the source formula.** In
    `ZMod p25519` the four values of `maddSpecN` are the four coordinates of `maddSpecR`
    on the casts of the inputs. -/
theorem maddSpecN_maddSpecR (x1 y1 z1 t1 ypx ymx t2d : Nat) (hx1 : x1 ≤ pM) :
    (((maddSpecN x1 y1 z1 t1 ypx ymx t2d).1 : Nat) : ZMod p25519)
        = (maddSpecR (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (ypx : ZMod p25519) (ymx : ZMod p25519) (t2d : ZMod p25519)).1
      ∧ (((maddSpecN x1 y1 z1 t1 ypx ymx t2d).2.1 : Nat) : ZMod p25519)
        = (maddSpecR (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (ypx : ZMod p25519) (ymx : ZMod p25519) (t2d : ZMod p25519)).2.1
      ∧ (((maddSpecN x1 y1 z1 t1 ypx ymx t2d).2.2.1 : Nat) : ZMod p25519)
        = (maddSpecR (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (ypx : ZMod p25519) (ymx : ZMod p25519) (t2d : ZMod p25519)).2.2.1
      ∧ (((maddSpecN x1 y1 z1 t1 ypx ymx t2d).2.2.2 : Nat) : ZMod p25519)
        = (maddSpecR (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (ypx : ZMod p25519) (ymx : ZMod p25519)
          (t2d : ZMod p25519)).2.2.2 := by
  have hle : ∀ a : Nat, a % pM ≤ pM := fun a => le_of_lt (mod_lt_pM a)
  have hsub : ∀ a : Nat, ((pM - a % pM : Nat) : ZMod p25519)
      = -((a % pM : Nat) : ZMod p25519) := fun a => cast_sub_pM _ (hle a)
  simp only [maddSpecN, maddSlots, maddSpecR]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Nat.cast_mul, Nat.cast_add, cast_mod_pM, hsub, cast_sub_pM x1 hx1] <;>
    ring

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
