/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesJoin
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

/-!
# The call model of the shipped `ed25519_madd`, and the mixed addition at it

`maddCallModel` sends each callee symbol of the shipped mixed addition to the shipped
block of that function, run on the callee's own frame: the field leaves eight bytes below
the caller's `%rsp`, the return address of the call, and the concatenation another 112
bytes below, the stack its body allocates. The `%rsp` the caller sees is restored on
return.

## What the model meets

`fe25519_add` and `fe25519_sub` write only the four words at their `%rdi` and read every
cell before writing it, so their `FieldCallee` statements carry no hypothesis.

`fe25519_mul` writes six words below its own `%rsp` and `ed25519_join16` seventeen words
in its own frame, and both read those words back, so each is stated of a state whose
buffers and whose eighteen words below the caller's `%rsp` are pairwise disjoint:
`FieldCalleeSep` for the multiply, `JoinCallee` for the concatenation. All four frames
are `FrameCS`, over the callee's output together with those eighteen words.

## Main definitions

* `atRsp`, `callBlock`: the state with `%rsp` set to a value, and the state a call leaves.
* `maddCallModel`: the call model.

## Main results

* `maddCallModel_add`, `maddCallModel_sub`, `maddCallModel_mul`, `maddCallModel_join`: the
  four callee specifications at the model.
* `maddCallees_maddCallModel`: the four together.
* `maddShipped_correct`: for pairwise separated cells and input coordinates below
  `2 ^ 255 - 19`, running the shipped mixed-addition block with the shipped callees leaves
  the four coordinates of `maddSpecN` at the output pointer.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-- The state with `%rsp` set to `v`. -/
def atRsp (sa : AState) (v : BitVec 64) : AState :=
  { sa with regs := fun r => if r = "%rsp" then v else sa.regs r }

@[simp] theorem atRsp_mem (sa : AState) (v : BitVec 64) : (atRsp sa v).mem = sa.mem := rfl

theorem atRsp_regs (sa : AState) (v : BitVec 64) (r : String) (hr : r ≠ "%rsp") :
    (atRsp sa v).regs r = sa.regs r := by simp [atRsp, hr]

@[simp] theorem atRsp_rsp (sa : AState) (v : BitVec 64) : (atRsp sa v).regs "%rsp" = v := by
  simp [atRsp]

/-- The state a call leaves: the callee's block run with `%rsp` at the callee's own frame,
    `sa.regs "%rsp" + d`, and `%rsp` restored on return. -/
def callBlock (blk : List (JInstr 64)) (d : Int) (sa : AState) : AState :=
  atRsp (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk) (sa.regs "%rsp")

theorem callBlock_mem (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlock blk d sa).mem
      = (runBlockA (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 d)) blk).mem := rfl

theorem callBlock_rsp (blk : List (JInstr 64)) (d : Int) (sa : AState) :
    (callBlock blk d sa).regs "%rsp" = sa.regs "%rsp" := by simp [callBlock]

/-- The call model of the shipped mixed addition: each callee symbol at the shipped block
    of that function, run on the callee's frame. The field leaves run eight bytes below the
    caller's `%rsp`, the return address of the call; the concatenation runs another 112
    bytes below, the stack its body allocates. -/
def maddCallModel : ACallModel := fun f sa =>
  if f = addSym then callBlock Fe25519AddShipped.fe25519AddShippedBlock (-8) sa
  else if f = subSym then callBlock Fe25519SubShipped.fe25519SubShippedBlock (-8) sa
  else if f = mulSym then callBlock Fe25519MulShipped.fe25519MulShippedBlock (-8) sa
  else if f = join16Sym then
    callBlock Ed25519Join16Shipped.ed25519Join16ShippedBlock (-120) sa
  else sa

theorem maddCallModel_addSym (sa : AState) :
    maddCallModel addSym sa = callBlock Fe25519AddShipped.fe25519AddShippedBlock (-8) sa := by
  simp [maddCallModel]

theorem maddCallModel_subSym (sa : AState) :
    maddCallModel subSym sa = callBlock Fe25519SubShipped.fe25519SubShippedBlock (-8) sa := by
  simp [maddCallModel, addSym, subSym]

theorem maddCallModel_mulSym (sa : AState) :
    maddCallModel mulSym sa = callBlock Fe25519MulShipped.fe25519MulShippedBlock (-8) sa := by
  simp [maddCallModel, addSym, subSym, mulSym]

theorem maddCallModel_joinSym (sa : AState) :
    maddCallModel join16Sym sa
      = callBlock Ed25519Join16Shipped.ed25519Join16ShippedBlock (-120) sa := by
  simp [maddCallModel, addSym, subSym, mulSym, join16Sym]

/-- A range of cells below the caller's `%rsp`, read at a displacement of it. -/
theorem rangeDisj_frame {a sp : BitVec 64} {lo hi : Int} (d : Int) {u v : Int}
    (h : RangeDisj a lo hi sp (-144) (-8))
    (hd : ∀ o : Int, u ≤ o → o ≤ v → o % 8 = 0 →
      (-144 : Int) ≤ d + o ∧ d + o ≤ -8 ∧ (d + o) % 8 = 0) :
    RangeDisj a lo hi (sp + BitVec.ofInt 64 d) u v := by
  intro o o' a1 a2 a3 b1 b2 b3
  rw [addI]
  exact h o (d + o') a1 a2 a3 (hd o' b1 b2 b3).1 (hd o' b1 b2 b3).2.1 (hd o' b1 b2 b3).2.2

/-- **The shipped `fe25519_add` meets the callee specification of the mixed addition.** -/
theorem maddCallModel_add : FieldCallee maddCallModel addSym (fun x y => x + y) := by
  intro sa
  have h := addShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide)] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_addSym, callBlock_mem]; exact hv
  · rw [maddCallModel_addSym, callBlock_mem]; exact frameCS_of_frameC _ hf
  · rw [maddCallModel_addSym]; exact callBlock_rsp _ _ _

/-- **The shipped `fe25519_sub` meets the callee specification of the mixed addition.** -/
theorem maddCallModel_sub : FieldCallee maddCallModel subSym (fun x y => x + (pM - y)) := by
  intro sa
  have h := subShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8)))
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide)] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_subSym, callBlock_mem]; exact hv
  · rw [maddCallModel_subSym, callBlock_mem]; exact frameCS_of_frameC _ hf
  · rw [maddCallModel_subSym]; exact callBlock_rsp _ _ _

/-- **The shipped `fe25519_mul` meets the callee specification of the mixed addition.** -/
theorem maddCallModel_mul : FieldCalleeSep maddCallModel mulSym (fun x y => x * y) := by
  intro sa hsp
  have e_rsi : mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) "%rsi"
      = sa.regs "%rsi" := by simp [mulP, atRsp]
  have e_rdi : mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) "%rdi"
      = sa.regs "%rdi" := by simp [mulP, atRsp]
  have e_rcx : mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) "%rcx"
      = sa.regs "%rdx" := by simp [mulP, atRsp]
  have e_rsp : mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) "%rsp"
      = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by simp [mulP, atRsp]
  have hred : ∀ o : Int, (-48 : Int) ≤ o → o ≤ -8 → o % 8 = 0 →
      (-144 : Int) ≤ -8 + o ∧ -8 + o ≤ -8 ∧ (-8 + o) % 8 = 0 :=
    fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩
  have hsep := separated_mulCells (R := mulP (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))))
    (by rw [e_rsi, e_rcx]; exact hsp.ij)
    (by rw [e_rsi, e_rdi]; exact hsp.oi.symm)
    (by rw [e_rcx, e_rdi]; exact hsp.oj.symm)
    (by rw [e_rsi, e_rsp]; exact rangeDisj_frame (-8) hsp.is hred)
    (by rw [e_rcx, e_rsp]; exact rangeDisj_frame (-8) hsp.js hred)
    (by rw [e_rdi, e_rsp]; exact rangeDisj_frame (-8) hsp.os hred)
  have h := mulShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-8))) hsep
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide), atRsp_rsp] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨fun _ _ => ?_, ?_, ?_⟩
  · rw [maddCallModel_mulSym, callBlock_mem]; exact hv
  · rw [maddCallModel_mulSym, callBlock_mem]
    intro x hx hy
    refine hf x hx fun i hi => ?_
    have h2 := hy (16 - i) (by omega)
    rw [redBase, addI, show (-144 : Int) + ((8 * (16 - i) : Nat) : Int)
      = -8 + (-(8 * (i + 1) : Nat) : Int) from by omega, ← addI] at h2
    exact h2
  · rw [maddCallModel_mulSym]; exact callBlock_rsp _ _ _

/-- **The shipped `ed25519_join16` meets the callee specification of the mixed
    addition.** -/
theorem maddCallModel_join : JoinCallee maddCallModel join16Sym := by
  intro sa hsp
  have er : ∀ r : String, r ≠ "%rsp" →
      (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-120))).regs r = sa.regs r :=
    fun r hr => atRsp_regs _ _ r hr
  have hstk : ∀ o : Int, (-24 : Int) ≤ o → o ≤ 104 → o % 8 = 0 →
      (-144 : Int) ≤ -120 + o ∧ -120 + o ≤ -8 ∧ (-120 + o) % 8 = 0 :=
    fun o a1 a2 a3 => ⟨by omega, by omega, by omega⟩
  have hsep := separated_joinCells
    (R := (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-120))).regs)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o1)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o2)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o3)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.o4)
    (by rw [er _ (by decide), atRsp_rsp]; exact rangeDisj_frame (-120) hsp.os hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a12)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a13)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a14)
    (by rw [er _ (by decide), atRsp_rsp]; exact rangeDisj_frame (-120) hsp.a1s hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a23)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a24)
    (by rw [er _ (by decide), atRsp_rsp]; exact rangeDisj_frame (-120) hsp.a2s hstk)
    (by rw [er _ (by decide), er _ (by decide)]; exact hsp.a34)
    (by rw [er _ (by decide), atRsp_rsp]; exact rangeDisj_frame (-120) hsp.a3s hstk)
    (by rw [er _ (by decide), atRsp_rsp]; exact rangeDisj_frame (-120) hsp.a4s hstk)
  have h := joinShipped_correct_addr (atRsp sa (sa.regs "%rsp" + BitVec.ofInt 64 (-120))) hsep
  rw [atRsp_mem] at h
  rw [atRsp_regs _ _ "%rdi" (by decide), atRsp_regs _ _ "%rsi" (by decide),
    atRsp_regs _ _ "%rdx" (by decide), atRsp_regs _ _ "%rcx" (by decide),
    atRsp_regs _ _ "%r8" (by decide), atRsp_rsp] at h
  obtain ⟨hv, hf, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [maddCallModel_joinSym, callBlock_mem]; exact hv
  · rw [maddCallModel_joinSym, callBlock_mem]
    intro x hx hy
    refine hf x hx fun o ho => ?_
    have key : ∀ (u : Int) (k : Nat), k < 18 →
        (-120 : Int) + u = (-144 : Int) + ((8 * k : Nat) : Int) →
        ¬ InRange8 (sa.regs "%rsp" + BitVec.ofInt 64 (-120) + BitVec.ofInt 64 u) x := by
      intro u k hk he
      rw [addI, he]
      have h2 := hy k hk
      rw [redBase, addI] at h2
      exact h2
    simp only [joinRspOffs, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · exact key _ 16 (by omega) (by omega)
    · exact key _ 15 (by omega) (by omega)
    · exact key _ 14 (by omega) (by omega)
    · exact key _ 13 (by omega) (by omega)
    · exact key _ 12 (by omega) (by omega)
    · exact key _ 11 (by omega) (by omega)
    · exact key _ 10 (by omega) (by omega)
    · exact key _ 9 (by omega) (by omega)
    · exact key _ 2 (by omega) (by omega)
    · exact key _ 1 (by omega) (by omega)
    · exact key _ 0 (by omega) (by omega)
    · exact key _ 8 (by omega) (by omega)
    · exact key _ 7 (by omega) (by omega)
    · exact key _ 6 (by omega) (by omega)
    · exact key _ 5 (by omega) (by omega)
    · exact key _ 4 (by omega) (by omega)
    · exact key _ 3 (by omega) (by omega)
  · rw [maddCallModel_joinSym]; exact callBlock_rsp _ _ _

/-- **The four shipped callees of the mixed addition meet their specifications.** -/
theorem maddCallees_maddCallModel : MaddCallees maddCallModel :=
  ⟨maddCallModel_add, maddCallModel_sub, maddCallModel_mul, maddCallModel_join⟩

/-- **The shipped `ed25519_madd` computes the mixed addition over the shipped callees.**
    For a state whose input point, output buffer and stack frame occupy pairwise disjoint
    eight-byte cells and whose seven input coordinates are below `2 ^ 255 - 19`, the four
    field elements at the output pointer after the block, run with each callee symbol at
    the shipped block of that function, are the four coordinates of `maddSpecN` on those
    inputs. -/
theorem maddShipped_correct (sa : AState)
    (hsep : Separated shippedBank sa.regs maddCells)
    (hb : ∀ j, j < 7 → maddIn sa j < pM) :
    feO (segsRunA maddCallModel sa
          Ed25519MaddShipped.ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 0)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).1
      ∧ feO (segsRunA maddCallModel sa
          Ed25519MaddShipped.ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 1)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.1
      ∧ feO (segsRunA maddCallModel sa
          Ed25519MaddShipped.ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 2)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.1
      ∧ feO (segsRunA maddCallModel sa
          Ed25519MaddShipped.ed25519MaddShippedBlock).mem (sa.regs "%rdi") (slotOff 3)
        = (maddSpecN (maddIn sa 0) (maddIn sa 1) (maddIn sa 2) (maddIn sa 3) (maddIn sa 4)
            (maddIn sa 5) (maddIn sa 6)).2.2.2 :=
  maddShipped_correct_addr maddCallees_maddCallModel sa hsep hb

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
