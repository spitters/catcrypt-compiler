/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignNameKeyed
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesField

/-!
# The shipped `ed25519_pack_sign` on the address machine

`Imported.Ed25519PackSignShipped.ed25519PackSignShippedBlock` is the body of
`ed25519_pack_sign` as printed by the owned backend. This module carries the name-keyed
statement of `Ed25519PackSignNameKeyed.packSign_nameKeyed` to `AddrMem.runBlockA`:
the four words at `%rdi`, the bytes the block leaves alone, and `%rsp`.

## Main definitions

* `packCells`: the eighteen cells the canonical block accesses — the nine stack slots from
  `%rsp - 8` to `%rsp + 56`, the four words at `%rdi`, the four at `%rsi`, and the word at
  `%rdx`.
* `FramePack`: a frame over the four words at the output and the nine stack slots.

## Main results

* `separated_packCells`: the cells are separated when the three buffers and the stack
  slots are pairwise disjoint.
* `packSignShipped_correct_addr`: the block copies the four words at `%rsi` to `%rdi`,
  with the low bit of the word at `%rdx` added into the top bit of the fourth, changes no
  byte outside the output and the stack slots, and keeps `%rsp`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignLeaf

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignNameKeyed

/-! ## The cells of the block -/

/-- The cells the canonical block accesses: the nine stack slots of its frame, the four
    output words at `%rdi`, the four input words at `%rsi`, and the word at `%rdx`. -/
def packCells : List (String × Int) :=
  [("%rsp", -8), ("%rsp", 0), ("%rsp", 8), ("%rsp", 16), ("%rsp", 24), ("%rsp", 32),
   ("%rsp", 40), ("%rsp", 48), ("%rsp", 56),
   ("%rdi", 0), ("%rdi", 8), ("%rdi", 16), ("%rdi", 24),
   ("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24),
   ("%rdx", 0)]

theorem packCells_mem : ∀ k ∈ packCells,
    (k.1 = "%rsp" ∧ -8 ≤ k.2 ∧ k.2 ≤ 56 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rdi" ∧ 0 ≤ k.2 ∧ k.2 ≤ 24 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rsi" ∧ 0 ≤ k.2 ∧ k.2 ≤ 24 ∧ k.2 % 8 = 0)
      ∨ (k.1 = "%rdx" ∧ 0 ≤ k.2 ∧ k.2 ≤ 0 ∧ k.2 % 8 = 0) := by decide

/-- The cells of the block are separated when its output buffer, its two input buffers and
    its stack slots are pairwise disjoint. -/
theorem separated_packCells {R : String → BitVec 64}
    (h1 : RangeDisj (R "%rdi") 0 24 (R "%rsi") 0 24)
    (h2 : RangeDisj (R "%rdi") 0 24 (R "%rdx") 0 0)
    (h3 : RangeDisj (R "%rsi") 0 24 (R "%rdx") 0 0)
    (h4 : RangeDisj (R "%rdi") 0 24 (R "%rsp") (-8) 56)
    (h5 : RangeDisj (R "%rsi") 0 24 (R "%rsp") (-8) 56)
    (h6 : RangeDisj (R "%rdx") 0 0 (R "%rsp") (-8) 56) :
    Separated shippedBank R packCells := by
  intro k hk k' hk' hne
  rcases packCells_mem k hk with ⟨hb, p0, p1, p8⟩ | ⟨hb, p0, p1, p8⟩ | ⟨hb, p0, p1, p8⟩ |
      ⟨hb, p0, p1, p8⟩ <;>
    rcases packCells_mem k' hk' with ⟨hb', q0, q1, q8⟩ | ⟨hb', q0, q1, q8⟩ |
        ⟨hb', q0, q1, q8⟩ | ⟨hb', q0, q1, q8⟩ <;>
    rw [keyAddr_of hb (by bank_self), keyAddr_of hb' (by bank_self)]
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact (h4 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h5 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h6 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact h4 _ _ p0 p1 p8 q0 q1 q8
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact h1 _ _ p0 p1 p8 q0 q1 q8
  · exact h2 _ _ p0 p1 p8 q0 q1 q8
  · exact h5 _ _ p0 p1 p8 q0 q1 q8
  · exact (h1 _ _ q0 q1 q8 p0 p1 p8).symm
  · have hoo : k.2 ≠ k'.2 := fun e => hne (Prod.ext (hb.trans hb'.symm) e)
    exact djSS _ _ _ (by omega) (by omega)
  · exact h3 _ _ p0 p1 p8 q0 q1 q8
  · exact h6 _ _ p0 p1 p8 q0 q1 q8
  · exact (h2 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact (h3 _ _ q0 q1 q8 p0 p1 p8).symm
  · exact absurd (Prod.ext (hb.trans hb'.symm) (by omega)) hne

/-! ## The block over the address machine -/

theorem pack_rbw :
    readsBeforeWritesFromB packCells false
      (canonD shippedBank Ed25519PackSignShipped.ed25519PackSignShippedBlock) = true := by
  decide +kernel

theorem pack_wkList :
    writeKeys (canonD shippedBank Ed25519PackSignShipped.ed25519PackSignShippedBlock)
      = [("%rsp", 56), ("%rsp", 48), ("%rsp", 40), ("%rsp", 32), ("%rsp", 24), ("%rsp", 16),
         ("%rsp", 8), ("%rsp", 0), ("%rsp", -8), ("%rdi", 0), ("%rdi", 8), ("%rdi", 16),
         ("%rdi", 24)] := by
  decide +kernel

theorem pack_wk :
    ∀ k ∈ writeKeys (canonD shippedBank Ed25519PackSignShipped.ed25519PackSignShippedBlock),
      k ∈ packCells := by decide +kernel

/-- `m'` differs from `m` only in the four words at `a` and the nine stack slots from
    `sp - 8`. -/
def FramePack (m m' : AMem) (a : BitVec 64) (sp : BitVec 64) : Prop :=
  ∀ x : BitVec 64,
    (∀ k, k < 4 → ¬ InRange8 (a + BitVec.ofInt 64 (8 * k : Nat)) x) →
    (∀ k, k < 9 → ¬ InRange8 (sp + BitVec.ofInt 64 ((-8 : Int) + (8 * k : Nat))) x) →
    m' x = m x

/-- **The shipped `ed25519_pack_sign` block on the address machine.** When its output
    buffer, its two input buffers and its stack slots occupy pairwise disjoint eight-byte
    ranges, the block copies the four words at `%rsi` to `%rdi`, adds the low bit of the
    word at `%rdx` into the top bit of the fourth word, changes no byte outside the output
    and the stack slots, and keeps `%rsp`. -/
theorem packSignShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs packCells) :
    (∀ j ∈ [(0 : Int), 8, 16],
        read64 (runBlockA sa Ed25519PackSignShipped.ed25519PackSignShippedBlock).mem
            (sa.regs "%rdi" + BitVec.ofInt 64 j)
          = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 j))
      ∧ read64 (runBlockA sa Ed25519PackSignShipped.ed25519PackSignShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 24)
        = read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 24)
          + (read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 0) &&& 1) <<< 63
      ∧ FramePack sa.mem
          (runBlockA sa Ed25519PackSignShipped.ed25519PackSignShippedBlock).mem
          (sa.regs "%rdi") (sa.regs "%rsp")
      ∧ (runBlockA sa Ed25519PackSignShipped.ed25519PackSignShippedBlock).regs "%rsp"
        = sa.regs "%rsp" := by
  obtain ⟨-, -, hK⟩ := runBlockA_simD_on shippedBank
    Ed25519PackSignShipped.ed25519PackSignShippedBlock packCells
    ed25519PackSign_disciplinedD pack_rbw pack_wk sa hsep
  have hout : ∀ o : Int, ("%rdi", o) ∈ packCells →
      read64 (runBlockA sa Ed25519PackSignShipped.ed25519PackSignShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 o)
        = (runBlock (jOf shippedBank sa) (canonD shippedBank
            Ed25519PackSignShipped.ed25519PackSignShippedBlock)).mem "%rdi" o := by
    intro o ho
    have := hK ("%rdi", o) ho
    dsimp only at this
    rw [absMem_shipped _ _ _ _ shippedBank_rdi] at this
    exact this
  obtain ⟨v0, v8, v16, v24⟩ := packSign_nameKeyed (jOf shippedBank sa)
  have hin : ∀ (b : String) (o : Int), shippedBank b = some b →
      (jOf shippedBank sa).mem b o = read64 sa.mem (sa.regs b + BitVec.ofInt 64 o) := by
    intro b o hb
    simp only [jOf, absMem_shipped _ _ _ _ hb]
  rw [hin _ _ shippedBank_rsi] at v0 v8 v16 v24
  rw [hin _ _ shippedBank_rdx] at v24
  refine ⟨?_, ?_, ?_, runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · rw [hout 0 (by simp [packCells])]; exact v0
    · rw [hout 8 (by simp [packCells])]; exact v8
    · rw [hout 16 (by simp [packCells])]; exact v16
  · rw [hout 24 (by simp [packCells])]; exact v24
  · intro x hx hy
    refine runBlockA_mem_frameD shippedBank _ ed25519PackSign_disciplinedD sa x
      (separated_of_subset pack_wk hsep) ?_
    intro k hk
    rw [pack_wkList] at hk
    have hk' : k = ("%rsp", 56) ∨ k = ("%rsp", 48) ∨ k = ("%rsp", 40) ∨ k = ("%rsp", 32) ∨
        k = ("%rsp", 24) ∨ k = ("%rsp", 16) ∨ k = ("%rsp", 8) ∨ k = ("%rsp", 0) ∨
        k = ("%rsp", -8) ∨ k = ("%rdi", 0) ∨ k = ("%rdi", 8) ∨ k = ("%rdi", 16) ∨
        k = ("%rdi", 24) := by simpa using hk
    rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 8 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 7 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 6 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 5 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 4 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 3 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 2 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 1 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy 0 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 0 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 1 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 2 (by omega)
    · simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx 3 (by omega)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PackSignLeaf
