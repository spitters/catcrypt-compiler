/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressCallModel

/-!
# Correctness of the shipped `ed25519_compress`

`Imported.Ed25519CompressShipped.ed25519CompressShippedBlock` is the body of
`ed25519_compress_x86_from_lean` as printed by the owned backend. Given the output pointer
in `%rdi` and the projective coordinates `X`, `Y`, `Z` at `%rsi`, `%rdx`, `%rcx`, it inverts
`Z` into the slot at `%rsp`, multiplies `X` and `Y` by that inverse into the slots at
`%rsp + 32` and `%rsp + 64`, and packs the second product with the low bit of the first
into the output. Run over `Ed25519MaddShippedProof.segsRunA` with each callee symbol at the
shipped block of that function, it leaves at the output the four-limb value
`y + 2 ^ 255 * (x % 2)`, where `x` and `y` are the affine coordinates.

## Main definitions

* `body1` … `body4`: the instruction runs of the four segments.
* `CompressSep`: the output and coordinate buffers are disjoint from the stack words the
  compression and its callees use.

## Main results

* `feO_mulFrame`, `read64_mulFrame`, `feO_invFrame`, `read64_invFrame`: values across a
  multiply call and the inversion call.
* `limbsNat_packTop`: the four-limb value after the top bit of the fourth limb is set.
* `compressShipped_correct_addr`: the value, over callees at their specifications.
* `compressShipped_correct`: the same over the shipped callees.

Provenance class: `@reimported`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym invertSym packSignSym)
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519LeafCallees
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519InvertShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel (limbsNat)

/-! ## The segments of the block -/

/-- The body of segment 1. -/
def body1 : List (JInstr 64) :=
  [.mov "%rbx" (.reg "%rsi"), .mov "%r12" (.reg "%rdx"), .mov "%r13" (.reg "%rcx"),
   .storeMem "%rsp" 96 (.reg "%rdi"), .lea "%rdi" "%rsp" "%rsp" 0 0, .mov "%rsi" (.reg "%r13")]

/-- The body of segment 2. -/
def body2 : List (JInstr 64) :=
  [.lea "%rdi" "%rsp" "%rsp" 0 32, .mov "%rsi" (.reg "%rbx"), .lea "%rdx" "%rsp" "%rsp" 0 0]

/-- The body of segment 3. -/
def body3 : List (JInstr 64) :=
  [.lea "%rdi" "%rsp" "%rsp" 0 64, .mov "%rsi" (.reg "%r12"), .lea "%rdx" "%rsp" "%rsp" 0 0]

/-- The body of segment 4. -/
def body4 : List (JInstr 64) :=
  [.loadMem "%rdi" "%rsp" 96, .lea "%rsi" "%rsp" "%rsp" 0 64, .lea "%rdx" "%rsp" "%rsp" 0 32]

/-- The block is its four bodies, each followed by its call. -/
theorem segsRunA_compress (C : ACallModel) (sa : AState) :
    segsRunA C sa Ed25519CompressShipped.ed25519CompressShippedBlock
      = C packSignSym (runBlockA (C mulSym (runBlockA (C mulSym (runBlockA
          (C invertSym (runBlockA sa body1)) body2)) body3)) body4) := rfl

theorem runBody1 (sa : AState) :
    let s' := runBlockA sa body1
    s'.mem = write64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 96) (sa.regs "%rdi")
      ∧ s'.regs "%rsp" = sa.regs "%rsp" ∧ s'.regs "%rbx" = sa.regs "%rsi"
      ∧ s'.regs "%r12" = sa.regs "%rdx"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 0
      ∧ s'.regs "%rsi" = sa.regs "%rcx" := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl⟩
  show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 0 = _
  exact leaZero _ _

theorem runBody2 (sa : AState) :
    let s' := runBlockA sa body2
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp" ∧ s'.regs "%r12" = sa.regs "%r12"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 32
      ∧ s'.regs "%rsi" = sa.regs "%rbx"
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 0 := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 32 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 0 = _
    exact leaZero _ _

theorem runBody3 (sa : AState) :
    let s' := runBlockA sa body3
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 64
      ∧ s'.regs "%rsi" = sa.regs "%r12"
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 0 := by
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 64 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 0 = _
    exact leaZero _ _

theorem runBody4 (sa : AState) :
    let s' := runBlockA sa body4
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 96)
      ∧ s'.regs "%rsi" = sa.regs "%rsp" + BitVec.ofInt 64 64
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 32 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 64 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 32 = _
    exact leaZero _ _

/-! ## Values through the frames -/

/-- A four-limb value disjoint from the output and the words below `sp` survives a
    multiply call writing the slot at `sp + a`. -/
theorem feO_mulFrame {m m' : AMem} {sp p : BitVec 64} {a c : Int}
    (hf : FrameCS m m' (sp + BitVec.ofInt 64 a) 4 sp) (ha : a % 8 = 0)
    (hd : ∀ o : Int, (a ≤ o ∧ o ≤ a + 24 ∨ -144 ≤ o ∧ o ≤ -8) → o % 8 = 0 →
      ∀ j ∈ limbOffs, Disjoint8 (sp + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 (c + j))) :
    feO m' p c = feO m p c := by
  refine feO_frameS hf (fun k hk j hj => ?_) (fun k hk j hj => ?_)
  · rw [addI]; exact hd _ (Or.inl ⟨by omega, by omega⟩) (by omega) j hj
  · rw [redBase, addI]; exact hd _ (Or.inr ⟨by omega, by omega⟩) (by omega) j hj

/-- A word disjoint from the output and the words below `sp` survives a multiply call
    writing the slot at `sp + a`. -/
theorem read64_mulFrame {m m' : AMem} {sp b : BitVec 64} {a : Int}
    (hf : FrameCS m m' (sp + BitVec.ofInt 64 a) 4 sp) (ha : a % 8 = 0)
    (hd : ∀ o : Int, (a ≤ o ∧ o ≤ a + 24 ∨ -144 ≤ o ∧ o ≤ -8) → o % 8 = 0 →
      Disjoint8 (sp + BitVec.ofInt 64 o) b) :
    read64 m' b = read64 m b := by
  refine read64_frameCS hf b (fun k hk => ?_) (fun k hk => ?_)
  · rw [addI]; exact hd _ (Or.inl ⟨by omega, by omega⟩) (by omega)
  · rw [redBase, addI]; exact hd _ (Or.inr ⟨by omega, by omega⟩) (by omega)

/-- A word disjoint from the inversion frame 192 bytes below `sp` and from the 32 bytes at
    `sp` survives the inversion call. -/
theorem read64_invFrame {m m' : AMem} {sp b : BitVec 64}
    (hf : InvertFrame m m' (sp + BitVec.ofInt 64 (-192)) (sp + BitVec.ofInt 64 0))
    (hd : ∀ o : Int, (-336 ≤ o ∧ o ≤ -64 ∨ 0 ≤ o ∧ o ≤ 24) → o % 8 = 0 →
      Disjoint8 (sp + BitVec.ofInt 64 o) b) :
    read64 m' b = read64 m b := by
  refine read64_invertFrame hf b (fun k hk => ?_) (fun k hk => ?_)
  · rw [redBase, addI, addI]; exact hd _ (Or.inl ⟨by omega, by omega⟩) (by omega)
  · rw [addI]; exact hd _ (Or.inr ⟨by omega, by omega⟩) (by omega)

/-- A four-limb value disjoint from the inversion frame 192 bytes below `sp` and from the
    32 bytes at `sp` survives the inversion call. -/
theorem feO_invFrame {m m' : AMem} {sp p : BitVec 64} {c : Int}
    (hf : InvertFrame m m' (sp + BitVec.ofInt 64 (-192)) (sp + BitVec.ofInt 64 0))
    (hd : ∀ o : Int, (-336 ≤ o ∧ o ≤ -64 ∨ 0 ≤ o ∧ o ≤ 24) → o % 8 = 0 →
      ∀ j ∈ limbOffs, Disjoint8 (sp + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 (c + j))) :
    feO m' p c = feO m p c := by
  simp only [feO]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  exact read64_invFrame hf fun o ho h8 => hd o ho h8 j hj

/-- The limbs of an input buffer disjoint from the stack words from `sp - 336` to
    `sp + 96`. -/
theorem djBuf {p sp : BitVec 64} (h : RangeDisj p 0 24 sp (-336) 96) :
    ∀ o : Int, -336 ≤ o → o ≤ 96 → o % 8 = 0 →
      ∀ j ∈ limbOffs, Disjoint8 (sp + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 (0 + j)) := by
  intro o h0 h1 h8 j hj
  simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
  exact (h (0 + j) o (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega)
    (by rcases hj with rfl | rfl | rfl | rfl <;> omega) h0 h1 h8).symm

/-- The limbs of a stack slot at `sp + c` disjoint from a stack word at least eight bytes
    away from each of them. -/
theorem djStack (sp : BitVec 64) (c o : Int)
    (h : ∀ j ∈ limbOffs, 8 ≤ (o - (c + j)).natAbs ∧ (o - (c + j)).natAbs ≤ 2 ^ 64 - 8) :
    ∀ j ∈ limbOffs, Disjoint8 (sp + BitVec.ofInt 64 o) (sp + BitVec.ofInt 64 (c + j)) :=
  fun j hj => djSS _ _ _ (h j hj).1 (h j hj).2

/-! ## The value -/

/-- The top bit of the fourth limb set to the low bit of `b`, for a four-limb value below
    `2 ^ 255`. -/
theorem limbsNat_packTop (y0 y1 y2 y3 b : BitVec 64)
    (hy : limbsNat y0 y1 y2 y3 < 2 ^ 255) :
    limbsNat y0 y1 y2 (y3 + (b &&& 1) <<< 63)
      = limbsNat y0 y1 y2 y3 + 2 ^ 255 * (b.toNat % 2) := by
  unfold limbsNat at hy ⊢
  have h3 : y3.toNat < 2 ^ 63 := by omega
  have hb : ((b &&& 1) <<< 63).toNat = b.toNat % 2 * 2 ^ 63 := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_and, Nat.shiftLeft_eq,
      show BitVec.toNat (1 : BitVec 64) = 1 from rfl, Nat.and_one_is_mod]
    omega
  rw [BitVec.toNat_add, hb]
  omega

/-- The buffers of the compression: the output at `%rdi` and the three coordinates at
    `%rsi`, `%rdx` and `%rcx` are each disjoint from the stack words from `%rsp - 336` to
    `%rsp + 96`, which hold the frame of the compression and those of its callees. -/
structure CompressSep (sa : AState) : Prop where
  /-- The first coordinate. -/
  xs : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-336) 96
  /-- The second coordinate. -/
  ys : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-336) 96
  /-- The third coordinate. -/
  zs : RangeDisj (sa.regs "%rcx") 0 24 (sa.regs "%rsp") (-336) 96
  /-- The output. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-336) 96

/-- **The shipped `ed25519_compress` over callees at their specifications.** For a state
    whose output and coordinate buffers are disjoint from the stack words the compression
    and its callees use, and whose third coordinate `Z` is below `2 ^ 255 - 19`, the
    four-limb value at the output pointer after the block is `y + 2 ^ 255 * (x % 2)`, where
    `x` and `y` are the first and second coordinates times `Z ^ (2 ^ 255 - 21)`, reduced
    modulo `2 ^ 255 - 19`. -/
theorem compressShipped_correct_addr {C : ACallModel} (hC : CompressCallees C) (sa : AState)
    (hsep : CompressSep sa) (hz : feO sa.mem (sa.regs "%rcx") 0 < pM) :
    feO (segsRunA C sa Ed25519CompressShipped.ed25519CompressShippedBlock).mem
        (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM
        + 2 ^ 255 * (feO sa.mem (sa.regs "%rsi") 0
            * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM % 2) := by
  rw [segsRunA_compress]
  -- segment 1 and the inversion
  obtain ⟨m1, rsp1, rbx1, r121, rdi1, rsi1⟩ := runBody1 sa
  set b1 := runBlockA sa body1 with hb1
  have wr : ∀ (p : BitVec 64), RangeDisj p 0 24 (sa.regs "%rsp") (-336) 96 →
      feO b1.mem p 0 = feO sa.mem p 0 := fun p hp => by
    rw [m1, feO_write64]
    exact fun j hj => djBuf hp 96 (by omega) (by omega) (by omega) j hj
  have hcs : ChainSep (b1.regs "%rsp" + BitVec.ofInt 64 (-192)) (b1.regs "%rsi") := by
    refine ⟨?_⟩
    rw [rsp1, rsi1]
    exact (rangeDisj_shift (-192) (by decide)
      (rangeDisj_narrow hsep.zs (le_refl _) (le_refl _) (by omega) (by omega))).symm
  obtain ⟨hv1, hf1, k1rsp, k1rbx, k1r12⟩ :=
    hC.inv b1 hcs (by rw [rsi1, wr _ hsep.zs]; exact hz)
  set s1 := C invertSym b1 with hs1
  rw [rsi1, rdi1, wr _ hsep.zs, feO_base] at hv1
  rw [rsp1, rdi1] at hf1
  have inv : ∀ (p : BitVec 64), RangeDisj p 0 24 (sa.regs "%rsp") (-336) 96 →
      feO s1.mem p 0 = feO sa.mem p 0 := fun p hp => by
    rw [feO_invFrame hf1 fun o ho h8 => djBuf hp o (by omega) (by omega) h8, wr p hp]
  -- segment 2 and the first multiply
  obtain ⟨m2, rsp2, r122, rdi2, rsi2, rdx2⟩ := runBody2 s1
  set b2 := runBlockA s1 body2 with hb2
  rw [k1rsp, rsp1] at rsp2 rdi2 rdx2
  rw [k1rbx, rbx1] at rsi2
  have hargs2 : ArgsBelowSep b2 := by
    refine ⟨?_, ?_⟩
    · rw [rsi2, rsp2]
      exact rangeDisj_narrow hsep.xs (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rdx2, rsp2]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 0) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨⟨hv2, hf2, k2rsp, -⟩, k2r12⟩ := hC.mul b2 hargs2
  set s2 := C mulSym b2 with hs2
  rw [rsi2, rdx2, rdi2, m2, inv _ hsep.xs, feO_base, feO_base, hv1] at hv2
  rw [rdi2, rsp2, m2] at hf2
  have stk : ∀ c : Int, c % 8 = 0 → ∀ o : Int, (o ≤ c - 8 ∨ c + 32 ≤ o) →
      o % 8 = 0 → -336 ≤ o → o ≤ 96 → -336 ≤ c → c ≤ 96 →
      ∀ j ∈ limbOffs, Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 o)
        (sa.regs "%rsp" + BitVec.ofInt 64 (c + j)) := by
    intro c hc o ho h8 h0 h1 c0 c1
    refine djStack _ _ _ fun j hj => ?_
    simp only [limbOffs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> omega
  -- segment 3 and the second multiply
  obtain ⟨m3, rsp3, rdi3, rsi3, rdx3⟩ := runBody3 s2
  set b3 := runBlockA s2 body3 with hb3
  rw [k2rsp, rsp2] at rsp3 rdi3 rdx3
  rw [k2r12, r122, k1r12, r121] at rsi3
  have hargs3 : ArgsBelowSep b3 := by
    refine ⟨?_, ?_⟩
    · rw [rsi3, rsp3]
      exact rangeDisj_narrow hsep.ys (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rdx3, rsp3]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 0) (e := 0) 0 24 (-144) (-8) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨⟨hv3, hf3, k3rsp, -⟩, -⟩ := hC.mul b3 hargs3
  set s3 := C mulSym b3 with hs3
  have y2 : feO s2.mem (sa.regs "%rdx") 0 = feO s1.mem (sa.regs "%rdx") 0 :=
    feO_mulFrame hf2 (by decide) fun o ho h8 => djBuf hsep.ys o (by omega) (by omega) h8
  have z2 : feO s2.mem (sa.regs "%rsp") (0 + 0) = feO s1.mem (sa.regs "%rsp") (0 + 0) :=
    feO_mulFrame hf2 (by decide) fun o ho h8 =>
      stk 0 (by decide) o (by omega) h8 (by omega) (by omega) (by omega) (by omega)
  rw [rsi3, rdx3, rdi3, m3, feO_base, feO_base, y2, z2, inv _ hsep.ys, hv1] at hv3
  rw [rdi3, rsp3, m3] at hf3
  -- segment 4 and the pack
  obtain ⟨m4, rsp4, rdi4, rsi4, rdx4⟩ := runBody4 s3
  set b4 := runBlockA s3 body4 with hb4
  rw [k3rsp, rsp3] at rsp4 rdi4 rsi4 rdx4
  have slot : read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 96) = sa.regs "%rdi" := by
    rw [read64_mulFrame hf3 (by decide) fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      read64_mulFrame hf2 (by decide) fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      read64_invFrame hf1 fun o ho h8 => djSS _ _ _ (by omega) (by omega),
      m1, read64_write64_same]
  rw [slot] at rdi4
  have hpack : PackSep b4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rdi4, rsi4]
      exact rangeDisj_shift 64 (by decide)
        (rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega))
    · rw [rdi4, rdx4]
      exact rangeDisj_shift 32 (by decide)
        (rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega))
    · rw [rsi4, rdx4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 32) 0 24 0 0 rfl rfl
        fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdi4, rsp4]
      exact rangeDisj_narrow hsep.os (le_refl _) (le_refl _) (by omega) (by omega)
    · rw [rsi4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 64) (e := 0) 0 24 (-80) (-16) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
    · rw [rdx4, rsp4]
      exact rangeDisj_sameBase (p := sa.regs "%rsp") (d := 32) (e := 0) 0 0 (-80) (-16) rfl
        (eq_add_ofInt_zero _) fun o o' a1 a2 a3 b1 b2 b3 => ⟨by omega, by omega⟩
  obtain ⟨hw, hw24⟩ := hC.pack b4 hpack
  rw [rdi4, rsi4, rdx4, m4] at hw24
  rw [rdi4, rsi4, m4] at hw
  -- the value
  have hY : feO s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64) 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM := by
    rw [feO_base]; exact hv3
  have hX : feO s3.mem (sa.regs "%rsp") (32 + 0)
      = feO sa.mem (sa.regs "%rsi") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM := by
    rw [feO_mulFrame (c := 32 + 0) hf3 (by decide) fun o ho h8 =>
      stk (32 + 0) (by decide) o (by omega) h8 (by omega) (by omega) (by omega) (by omega)]
    exact hv2
  have hpar : (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 32 + BitVec.ofInt 64 0)).toNat
      % 2 = feO sa.mem (sa.regs "%rsi") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM)
        % pM % 2 := by
    rw [← hX, ← feO_base, feO_eq_limbsNat]
    unfold limbsNat
    omega
  have hlt :
      limbsNat (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 0))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 8))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 16))
        (read64 s3.mem (sa.regs "%rsp" + BitVec.ofInt 64 64 + BitVec.ofInt 64 24))
      < 2 ^ 255 := by
    rw [← feO_eq_limbsNat, hY]
    exact Nat.lt_of_lt_of_le (Nat.mod_lt _ pM_pos) (by unfold pM; omega)
  rw [feO_eq_limbsNat, hw 0 (by simp), hw 8 (by simp), hw 16 (by simp), hw24,
    limbsNat_packTop _ _ _ _ _ hlt, ← feO_eq_limbsNat, hY, hpar]

/-- **The shipped `ed25519_compress` over the shipped callees.** For a state whose output
    and coordinate buffers are disjoint from the stack words the compression and its
    callees use, and whose third coordinate `Z` is below `2 ^ 255 - 19`, the four-limb value
    at the output pointer after the block, run with each callee symbol at the shipped block
    of that function, is `y + 2 ^ 255 * (x % 2)`, where `x` and `y` are the first and second
    coordinates times `Z ^ (2 ^ 255 - 21)`, reduced modulo `2 ^ 255 - 19`. -/
theorem compressShipped_correct (sa : AState) (hsep : CompressSep sa)
    (hz : feO sa.mem (sa.regs "%rcx") 0 < pM) :
    feO (segsRunA compressCallModel sa
        Ed25519CompressShipped.ed25519CompressShippedBlock).mem (sa.regs "%rdi") 0
      = feO sa.mem (sa.regs "%rdx") 0 * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM
        + 2 ^ 255 * (feO sa.mem (sa.regs "%rsi") 0
            * (feO sa.mem (sa.regs "%rcx") 0 ^ (pM - 2) % pM) % pM % 2) :=
  compressShipped_correct_addr compressCallees_compressCallModel sa hsep hz

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519CompressShippedProof
