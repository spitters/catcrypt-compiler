/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCalleesField
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-!
# The concatenation callee of the shipped `ed25519_madd` on the address machine

`Ed25519Join16Shipped.ed25519Join16ShippedBlock` is the body of `ed25519_join16` as
printed by the owned backend: sixteen loads from four four-limb inputs and sixteen stores
into one sixteen-word output, through stack slots. This module carries its correctness to
`AddrMem.runBlockA`.

## The route

The canonical block `canonD shippedBank` of the body is a straight-line block of
displacement moves. `Ed25519ScReduceShippedProof.partCheck` symbolically executes it from
the sixteen input cells at the slots `0, …, 15` and checks that the sixteen output cells
carry those same slots; `partCheck_sound` turns the check into the value statement over
`runBlock`, and `AddrMemDerived.runBlockA_simD_on` carries it to the address machine.

## Main definitions

* `joinIn`, `joinOut`: the input and output cells at their slots.
* `jRho`: the slot values of the sixteen input words.
* `joinRspOffs`, `joinCells`: the stack slots the body uses, and every cell it accesses.
* `FrameCJoin`: a frame over the 128-byte output and those stack slots.

## Main results

* `join_check`: the symbolic check of the canonical block.
* `joinCanon_out`: the canonical block leaves each input word at its output cell.
* `joinShipped_correct_addr`: for separated cells, the block leaves the four input field
  elements in the four consecutive field slots at `%rdi`, changes no byte outside those
  128 bytes and its own stack slots, and keeps `%rsp`.
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
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
  (Loc WE MapHolds partCheck partCheck_sound Loc.val cK footOK footOK_reads footOK_writes)

/-- The sixteen input cells of the concatenation: the four limbs at each of `%rsi`, `%rdx`,
    `%rcx` and `%r8`, at the slots `0, …, 15`. -/
def joinIn : List (Loc × WE) :=
  [(.cell "%rsi" 0, .v 0), (.cell "%rsi" 8, .v 1), (.cell "%rsi" 16, .v 2),
   (.cell "%rsi" 24, .v 3),
   (.cell "%rdx" 0, .v 4), (.cell "%rdx" 8, .v 5), (.cell "%rdx" 16, .v 6),
   (.cell "%rdx" 24, .v 7),
   (.cell "%rcx" 0, .v 8), (.cell "%rcx" 8, .v 9), (.cell "%rcx" 16, .v 10),
   (.cell "%rcx" 24, .v 11),
   (.cell "%r8" 0, .v 12), (.cell "%r8" 8, .v 13), (.cell "%r8" 16, .v 14),
   (.cell "%r8" 24, .v 15)]

/-- The sixteen output cells of the concatenation, at the same slots. -/
def joinOut : List (Loc × WE) :=
  [(.cell "%rdi" 0, .v 0), (.cell "%rdi" 8, .v 1), (.cell "%rdi" 16, .v 2),
   (.cell "%rdi" 24, .v 3),
   (.cell "%rdi" 32, .v 4), (.cell "%rdi" 40, .v 5), (.cell "%rdi" 48, .v 6),
   (.cell "%rdi" 56, .v 7),
   (.cell "%rdi" 64, .v 8), (.cell "%rdi" 72, .v 9), (.cell "%rdi" 80, .v 10),
   (.cell "%rdi" 88, .v 11),
   (.cell "%rdi" 96, .v 12), (.cell "%rdi" 104, .v 13), (.cell "%rdi" 112, .v 14),
   (.cell "%rdi" 120, .v 15)]

theorem join_check :
    partCheck 16 [] joinIn joinOut
      (canonD shippedBank Ed25519Join16Shipped.ed25519Join16ShippedBlock) = true := by
  decide +kernel

/-- The slot values of the sixteen input words. -/
def jRho (st : JState 64) (i : Nat) : BitVec 64 :=
  if i < 4 then st.mem "%rsi" ((8 * i : Nat) : Int)
  else if i < 8 then st.mem "%rdx" ((8 * (i - 4) : Nat) : Int)
  else if i < 12 then st.mem "%rcx" ((8 * (i - 8) : Nat) : Int)
  else st.mem "%r8" ((8 * (i - 12) : Nat) : Int)

theorem join_in_holds (st : JState 64) : MapHolds (jRho st) joinIn st := by
  intro p hp
  simp only [joinIn, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> rfl

theorem join_cK (st : JState 64) (j c : Nat) (hj : j < 16) (h : cK j = some c) :
    jRho st j = BitVec.ofNat 64 c := by
  rw [cK, if_neg (by omega)] at h
  exact absurd h (by simp)

/-- The name-keyed canonical concatenation block leaves the four input blocks in the four
    consecutive field slots at `%rdi`. -/
theorem joinCanon_out (st : JState 64) (p : Loc × WE) (hp : p ∈ joinOut) :
    p.1.val (runBlock st
      (canonD shippedBank Ed25519Join16Shipped.ed25519Join16ShippedBlock)) = p.2.eval (jRho st) :=
  partCheck_sound 16 [] joinIn joinOut _ join_check (jRho st) trivial
    (fun j c hj h => join_cK st j c hj h) st (join_in_holds st) p hp

/-- The cells the concatenation block reads or writes: the four limbs at each of `%rsi`,
    `%rdx`, `%rcx` and `%r8`, the sixteen output words at `%rdi`, and the stack slots it
    uses. -/
def joinRspOffs : List Int := [104, 96, 88, 80, 72, 64, 56, 48, -8, -16, -24, 40, 32, 24, 16, 8, 0]

def joinCells : List (String × Int) :=
  (joinRspOffs.map fun o => ("%rsp", o)) ++
  ((List.range 16).map fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
  [("%rsi", 0), ("%rsi", 8), ("%rsi", 16), ("%rsi", 24),
   ("%rdx", 0), ("%rdx", 8), ("%rdx", 16), ("%rdx", 24),
   ("%rcx", 0), ("%rcx", 8), ("%rcx", 16), ("%rcx", 24),
   ("%r8", 0), ("%r8", 8), ("%r8", 16), ("%r8", 24)]

theorem join_foot :
    footOK joinCells (canonD shippedBank Ed25519Join16Shipped.ed25519Join16ShippedBlock)
      = true := by decide +kernel

theorem join_wkList :
    writeKeys (canonD shippedBank Ed25519Join16Shipped.ed25519Join16ShippedBlock)
      = (joinRspOffs.map fun o => ("%rsp", o)) ++
        ((List.range 16).map fun i => ("%rdi", ((8 * i : Nat) : Int))) := by decide +kernel

/-- `m'` differs from `m` only in the 128 bytes at `a` and the stack slots the
    concatenation block uses. -/
def FrameCJoin (m m' : AMem) (a sp : BitVec 64) : Prop :=
  ∀ x : BitVec 64,
    (∀ k, k < 16 → ¬ InRange8 (a + BitVec.ofInt 64 (8 * k : Nat)) x) →
    (∀ o ∈ joinRspOffs, ¬ InRange8 (sp + BitVec.ofInt 64 o) x) →
    m' x = m x

/-- **The shipped `ed25519_join16` block on the address machine.** When the input, output
    and stack cells occupy pairwise disjoint eight-byte ranges, the block leaves the four
    input field elements in the four consecutive field slots at `%rdi`; it changes no byte
    outside those 128 bytes and its own stack slots, and keeps `%rsp`. -/
theorem joinShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs joinCells) :
    (feO (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem (sa.regs "%rdi") 0
        = feO sa.mem (sa.regs "%rsi") 0
      ∧ feO (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem
          (sa.regs "%rdi") 32 = feO sa.mem (sa.regs "%rdx") 0
      ∧ feO (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem
          (sa.regs "%rdi") 64 = feO sa.mem (sa.regs "%rcx") 0
      ∧ feO (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem
          (sa.regs "%rdi") 96 = feO sa.mem (sa.regs "%r8") 0)
      ∧ FrameCJoin sa.mem (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem
          (sa.regs "%rdi") (sa.regs "%rsp")
      ∧ (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).regs "%rsp"
          = sa.regs "%rsp" := by
  obtain ⟨-, -, hK⟩ := runBlockA_simD_on shippedBank
    Ed25519Join16Shipped.ed25519Join16ShippedBlock joinCells ed25519Join16_disciplinedD
    (readsBeforeWritesFromB_of_reads _ (footOK_reads join_foot) false)
    (footOK_writes join_foot) sa hsep
  have hw : ∀ (i : Nat) (o : Int), (Prod.mk (Loc.cell "%rdi" o) (WE.v i)) ∈ joinOut →
      ("%rdi", o) ∈ joinCells →
      read64 (runBlockA sa Ed25519Join16Shipped.ed25519Join16ShippedBlock).mem
          (sa.regs "%rdi" + BitVec.ofInt 64 o)
        = jRho (jOf shippedBank sa) i := by
    intro i o ho hc
    have h1 := hK ("%rdi", o) hc
    rw [absMem_shipped _ _ _ _ shippedBank_rdi] at h1
    have h2 := joinCanon_out (jOf shippedBank sa) (Loc.cell "%rdi" o, WE.v i) ho
    simp only [Loc.val, WE.eval] at h2
    rw [h1, h2]
  have hv : ∀ (b : String) (_ : shippedBank b = some b) (o : Int),
      (jOf shippedBank sa).mem b o = read64 sa.mem (sa.regs b + BitVec.ofInt 64 o) := by
    intro b hb o
    simp only [jOf, absMem_shipped _ _ _ _ hb]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_,
    runBlockA_regs_of_not_dsts _ _ _ (rsp_not_dst_of_all (by decide +kernel))⟩
  · simp only [feO, limbOffs, List.map_cons, List.map_nil, show (0 : Int) + 0 = 0 from rfl,
      show (0 : Int) + 8 = 8 from rfl, show (0 : Int) + 16 = 16 from rfl,
      show (0 : Int) + 24 = 24 from rfl]
    rw [hw 0 0 (by simp [joinOut]) (by decide),
      hw 1 8 (by simp [joinOut]) (by decide),
      hw 2 16 (by simp [joinOut]) (by decide),
      hw 3 24 (by simp [joinOut]) (by decide)]
    simp only [jRho, jOf, absMem_shipped _ _ _ _ shippedBank_rsi]
    norm_num
  · simp only [feO, limbOffs, List.map_cons, List.map_nil, show (32 : Int) + 0 = 32 from rfl,
      show (32 : Int) + 8 = 40 from rfl, show (32 : Int) + 16 = 48 from rfl,
      show (32 : Int) + 24 = 56 from rfl, show (0 : Int) + 0 = 0 from rfl,
      show (0 : Int) + 8 = 8 from rfl, show (0 : Int) + 16 = 16 from rfl,
      show (0 : Int) + 24 = 24 from rfl]
    rw [hw 4 32 (by simp [joinOut]) (by decide),
      hw 5 40 (by simp [joinOut]) (by decide),
      hw 6 48 (by simp [joinOut]) (by decide),
      hw 7 56 (by simp [joinOut]) (by decide)]
    simp only [jRho, jOf, absMem_shipped _ _ _ _ shippedBank_rdx]
    norm_num
  · simp only [feO, limbOffs, List.map_cons, List.map_nil, show (64 : Int) + 0 = 64 from rfl,
      show (64 : Int) + 8 = 72 from rfl, show (64 : Int) + 16 = 80 from rfl,
      show (64 : Int) + 24 = 88 from rfl, show (0 : Int) + 0 = 0 from rfl,
      show (0 : Int) + 8 = 8 from rfl, show (0 : Int) + 16 = 16 from rfl,
      show (0 : Int) + 24 = 24 from rfl]
    rw [hw 8 64 (by simp [joinOut]) (by decide),
      hw 9 72 (by simp [joinOut]) (by decide),
      hw 10 80 (by simp [joinOut]) (by decide),
      hw 11 88 (by simp [joinOut]) (by decide)]
    simp only [jRho, jOf, absMem_shipped _ _ _ _ (by decide : shippedBank "%rcx" = some "%rcx")]
    norm_num
  · simp only [feO, limbOffs, List.map_cons, List.map_nil, show (96 : Int) + 0 = 96 from rfl,
      show (96 : Int) + 8 = 104 from rfl, show (96 : Int) + 16 = 112 from rfl,
      show (96 : Int) + 24 = 120 from rfl, show (0 : Int) + 0 = 0 from rfl,
      show (0 : Int) + 8 = 8 from rfl, show (0 : Int) + 16 = 16 from rfl,
      show (0 : Int) + 24 = 24 from rfl]
    rw [hw 12 96 (by simp [joinOut]) (by decide),
      hw 13 104 (by simp [joinOut]) (by decide),
      hw 14 112 (by simp [joinOut]) (by decide),
      hw 15 120 (by simp [joinOut]) (by decide)]
    simp only [jRho, jOf, absMem_shipped _ _ _ _ (by decide : shippedBank "%r8" = some "%r8")]
    norm_num
  · intro x hx hy
    refine runBlockA_mem_frameD shippedBank _ ed25519Join16_disciplinedD sa x
      (separated_of_subset (fun k hk => ?_) hsep) ?_
    · rw [join_wkList] at hk
      rcases List.mem_append.1 hk with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_left _ (List.mem_append_right _ h)
    · intro k hk
      rw [join_wkList] at hk
      rcases List.mem_append.1 hk with h | h
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h
        simpa [keyAddr_shipped _ _ _ shippedBank_rsp] using hy o ho
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
        simpa [keyAddr_shipped _ _ _ shippedBank_rdi] using hx i (List.mem_range.1 hi)

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
