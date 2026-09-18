/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public import CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-!
# The address machine with calls, and the callee interface of the shipped `ed25519_madd`

`Imported.Ed25519MaddShipped.ed25519MaddShippedBlock` is a `List CallSeg`: runs of
`JInstr 64` separated by calls to `fe25519_add`, `fe25519_sub`, `fe25519_mul` and
`ed25519_join16`. This module carries the executor the block's correctness proof runs
on and the specification of its four callees.

## The memory model

The statement is over `AddrMem.AState`, whose memory is addressed by value. The
name-keyed memory of `JasminModel` keys a cell by the name of its base register, so
a scratch slot the caller addresses as `(%rsp, 320)` and the same 32 bytes a callee
writes through its own `%rdi` are two different cells there; the address machine is
the model in which a call's effect and its caller's accesses refer to one memory.

## Main definitions

* `ACallModel`, `segsRunA`: the state a call leaves, and the state after a list of
  segments and their calls.
* `feO m p o`: the four-limb little-endian value in the 32 bytes at `p + o`.
* `FrameC m m' a n`: `m'` and `m` agree outside the `8 * n` bytes at `a`.
* `redBase`, `FrameCS m m' a n sp`: the base of the eighteen words below `sp` that a
  callee's own frame occupies, and a frame over the `8 * n` bytes at `a` together with
  those words.
* `RangeDisj a lo hi b lo' hi'`: the aligned cells in `[lo, hi]` from `a` and in
  `[lo', hi']` from `b` occupy pairwise disjoint eight-byte ranges.
* `FieldSep`, `JoinSep`: the pairwise disjointness of a callee's argument buffers, its
  output and the words below `%rsp`.
* `FieldEffect`, `JoinEffect`: the effect of one call on the four-limb values at its
  argument pointers, on memory outside its output and the words below `%rsp`, and on
  `%rsp`.
* `FieldCallee`, `FieldCalleeSep`, `JoinCallee`, `MaddCallees`: that effect at every
  state, respectively at every state whose buffers are separated.
* `maddCells`: the eight-byte cells the block and its callees access, as
  `(base, offset)` pairs of the entry registers `%rsp`, `%rsi` and `%rdi`; the stack
  cells run from the callee frames at `%rsp - 144` to the pointer slot at `%rsp + 584`.
* `copyBlk`: the load-store pairs of the block's output copy.

## Main results

* `runArgsRR`, `runArgsSR`, `runArgsSS`, `runArgsJoin`, `runEntry`, `runOutSetup`: the
  registers and the memory each segment body leaves.
* `feO_frame`, `feO_frameS`: a four-limb value survives a call whose written cells are
  disjoint from it.
* `copyBlk_val`, `copyBlk_frame`: the copy moves each word and changes nothing else.
* `djSS`, `djIS`, `djOS`: disjointness of two cells at one base and of cells at two
  different bases, the latter from `Separated ... maddCells`.
* `fieldStep`: one field call leaves the reduced result in the stack slot its `%rdi`
  addresses.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel

/-! ## 1. Segments over the address machine -/

/-- The state a call leaves, by callee symbol and state at the call. -/
abbrev ACallModel := String → AState → AState

/-- The state after a list of segments, each body run by `runBlockA` and each call
    resolved by `C`. -/
def segsRunA (C : ACallModel) : AState → List CallSeg → AState
  | sa, [] => sa
  | sa, g :: gs =>
      match g.callee with
      | none => segsRunA C (runBlockA sa g.body) gs
      | some f => segsRunA C (C f (runBlockA sa g.body)) gs

@[simp] theorem segsRunA_nil (C : ACallModel) (sa : AState) : segsRunA C sa [] = sa := rfl

theorem segsRunA_append (C : ACallModel) (sa : AState) (xs ys : List CallSeg) :
    segsRunA C sa (xs ++ ys) = segsRunA C (segsRunA C sa xs) ys := by
  induction xs generalizing sa with
  | nil => rfl
  | cons g gs ih =>
    cases hg : g.callee with
    | none => simp only [List.cons_append, segsRunA, hg]; exact ih _
    | some f => simp only [List.cons_append, segsRunA, hg]; exact ih _

/-! ## 2. Four-limb values and frames -/

/-- The four limb offsets of a field element. -/
def limbOffs : List Int := [0, 8, 16, 24]

/-- The four-limb little-endian value in the 32 bytes at `p + o`. -/
def feO (m : AMem) (p : BitVec 64) (o : Int) : Nat :=
  bignumVal (limbOffs.map fun k => read64 m (p + BitVec.ofInt 64 (o + k)))

theorem addI (p : BitVec 64) (a b : Int) :
    p + BitVec.ofInt 64 a + BitVec.ofInt 64 b = p + BitVec.ofInt 64 (a + b) := by
  have h : BitVec.ofInt 64 a + BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt]
    omega
  rw [BitVec.add_assoc, h]

/-- The value at a base shifted by a displacement is the value at the sum. -/
theorem feO_base (m : AMem) (p : BitVec 64) (d o : Int) :
    feO m (p + BitVec.ofInt 64 d) o = feO m p (d + o) := by
  simp only [feO, limbOffs, List.map_cons, List.map_nil, addI]
  norm_num [Int.add_assoc]

/-- `m'` differs from `m` only in the `8 * n` bytes from `a`. -/
def FrameC (m m' : AMem) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ x : BitVec 64, (∀ k, k < n → ¬ InRange8 (a + BitVec.ofInt 64 (8 * k : Nat)) x) →
    m' x = m x

/-- A word outside the frame reads back unchanged. -/
theorem read64_frameC {m m' : AMem} {a : BitVec 64} {n : Nat} (hf : FrameC m m' a n)
    (b : BitVec 64)
    (hd : ∀ k, k < n → Disjoint8 (a + BitVec.ofInt 64 (8 * k : Nat)) b) :
    read64 m' b = read64 m b := by
  have key : ∀ i : Nat, i < 8 → m' (b + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) :=
    fun i hi => hf _ fun k hk => not_inRange_of_disjoint _ _ i (hd k hk) hi
  have h0 : m' b = m b := by simpa using key 0 (by decide)
  simp only [read64, h0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide)]

/-- A four-limb value whose limbs are disjoint from the frame survives it. -/
theorem feO_frame {m m' : AMem} {a p : BitVec 64} {n : Nat} {o : Int}
    (hf : FrameC m m' a n)
    (hd : ∀ k, k < n → ∀ j ∈ limbOffs,
      Disjoint8 (a + BitVec.ofInt 64 (8 * k : Nat)) (p + BitVec.ofInt 64 (o + j))) :
    feO m' p o = feO m p o := by
  simp only [feO]
  refine congrArg bignumVal (List.map_congr_left fun j hj => ?_)
  exact read64_frameC hf _ fun k hk => hd k hk j hj

/-- The eighteen eight-byte words below `sp`, as the buffer based at `sp - 144`. -/
def redBase (sp : BitVec 64) : BitVec 64 := sp + BitVec.ofInt 64 (-144)

/-- `m'` differs from `m` only in the `8 * n` bytes from `a` and the eighteen words
    below `sp`. -/
def FrameCS (m m' : AMem) (a : BitVec 64) (n : Nat) (sp : BitVec 64) : Prop :=
  ∀ x : BitVec 64, (∀ k, k < n → ¬ InRange8 (a + BitVec.ofInt 64 (8 * k : Nat)) x) →
    (∀ k, k < 18 → ¬ InRange8 (redBase sp + BitVec.ofInt 64 (8 * k : Nat)) x) →
    m' x = m x

/-- A frame over the output alone is a frame over the output together with the eighteen
    words below `sp`. -/
theorem frameCS_of_frameC {m m' : AMem} {a : BitVec 64} {n : Nat} (sp : BitVec 64)
    (hf : FrameC m m' a n) : FrameCS m m' a n sp := fun x hx _ => hf x hx

/-- A word outside the frame reads back unchanged. -/
theorem read64_frameCS {m m' : AMem} {a : BitVec 64} {n : Nat} {sp : BitVec 64}
    (hf : FrameCS m m' a n sp) (b : BitVec 64)
    (hd : ∀ k, k < n → Disjoint8 (a + BitVec.ofInt 64 (8 * k : Nat)) b)
    (hr : ∀ k, k < 18 → Disjoint8 (redBase sp + BitVec.ofInt 64 (8 * k : Nat)) b) :
    read64 m' b = read64 m b := by
  have key : ∀ i : Nat, i < 8 → m' (b + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) :=
    fun i hi => hf _ (fun k hk => not_inRange_of_disjoint _ _ i (hd k hk) hi)
      (fun k hk => not_inRange_of_disjoint _ _ i (hr k hk) hi)
  have h0 : m' b = m b := by simpa using key 0 (by decide)
  simp only [read64, h0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide)]

/-- A four-limb value whose limbs lie outside the frame survives it. -/
theorem feO_frameS {m m' : AMem} {a p sp : BitVec 64} {n : Nat} {o : Int}
    (hf : FrameCS m m' a n sp)
    (hd : ∀ k, k < n → ∀ j ∈ limbOffs,
      Disjoint8 (a + BitVec.ofInt 64 (8 * k : Nat)) (p + BitVec.ofInt 64 (o + j)))
    (hr : ∀ k, k < 18 → ∀ j ∈ limbOffs,
      Disjoint8 (redBase sp + BitVec.ofInt 64 (8 * k : Nat)) (p + BitVec.ofInt 64 (o + j))) :
    feO m' p o = feO m p o := by
  simp only [feO]
  refine congrArg bignumVal (List.map_congr_left fun j hj => ?_)
  exact read64_frameCS hf _ (fun k hk => hd k hk j hj) (fun k hk => hr k hk j hj)

/-- The eight-byte cells at eight-byte-aligned offsets in `[lo, hi]` from `a` and in
    `[lo', hi']` from `b` occupy pairwise disjoint ranges. -/
def RangeDisj (a : BitVec 64) (lo hi : Int) (b : BitVec 64) (lo' hi' : Int) : Prop :=
  ∀ o o' : Int, lo ≤ o → o ≤ hi → o % 8 = 0 → lo' ≤ o' → o' ≤ hi' → o' % 8 = 0 →
    Disjoint8 (a + BitVec.ofInt 64 o) (b + BitVec.ofInt 64 o')

theorem RangeDisj.symm {a b : BitVec 64} {lo hi lo' hi' : Int}
    (h : RangeDisj a lo hi b lo' hi') : RangeDisj b lo' hi' a lo hi :=
  fun o o' h1 h2 h3 h4 h5 h6 => (h o' o h4 h5 h6 h1 h2 h3).symm

/-- A base is its own displacement by zero. -/
theorem eq_add_ofInt_zero (p : BitVec 64) : p = p + BitVec.ofInt 64 0 := by simp

/-- Two ranges at displacements of one base whose absolute offsets stay at least eight
    apart. -/
theorem rangeDisj_sameBase {p a b : BitVec 64} {d e : Int} (lo hi lo' hi' : Int)
    (ha : a = p + BitVec.ofInt 64 d) (hb : b = p + BitVec.ofInt 64 e)
    (h : ∀ o o' : Int, lo ≤ o → o ≤ hi → o % 8 = 0 → lo' ≤ o' → o' ≤ hi' → o' % 8 = 0 →
      8 ≤ ((d + o) - (e + o')).natAbs ∧ ((d + o) - (e + o')).natAbs ≤ 2 ^ 64 - 8) :
    RangeDisj a lo hi b lo' hi' := by
  subst ha; subst hb
  intro o o' a1 a2 a3 b1 b2 b3
  rw [addI, addI]
  exact disjoint8_add_ofInt _ _ _ (h o o' a1 a2 a3 b1 b2 b3).1 (h o o' a1 a2 a3 b1 b2 b3).2

/-- Two ranges at displacements of two bases whose own ranges are disjoint. -/
theorem rangeDisj_twoBase {p q a b : BitVec 64} {lo hi lo' hi' d e : Int}
    (u1 u2 v1 v2 : Int) (hbase : RangeDisj p lo hi q lo' hi')
    (ha : a = p + BitVec.ofInt 64 d) (hb : b = q + BitVec.ofInt 64 e)
    (hu : ∀ o : Int, u1 ≤ o → o ≤ u2 → o % 8 = 0 → lo ≤ d + o ∧ d + o ≤ hi ∧ (d + o) % 8 = 0)
    (hv : ∀ o : Int, v1 ≤ o → o ≤ v2 → o % 8 = 0 →
      lo' ≤ e + o ∧ e + o ≤ hi' ∧ (e + o) % 8 = 0) :
    RangeDisj a u1 u2 b v1 v2 := by
  subst ha; subst hb
  intro o o' a1 a2 a3 b1 b2 b3
  rw [addI, addI]
  exact hbase (d + o) (e + o') (hu o a1 a2 a3).1 (hu o a1 a2 a3).2.1 (hu o a1 a2 a3).2.2
    (hv o' b1 b2 b3).1 (hv o' b1 b2 b3).2.1 (hv o' b1 b2 b3).2.2

/-! ## 3. The callees -/

open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.ShippedCT
  (mulSym addSym subSym join16Sym)

/-- The prime `2 ^ 255 - 19`. -/
def pM : Nat := 2 ^ 255 - 19

theorem pM_pos : 0 < pM := by unfold pM; norm_num

/-- The buffers a field callee touches are pairwise disjoint: the four-limb output at
    `%rdi`, the two four-limb arguments at `%rsi` and `%rdx`, and the eighteen words
    below `%rsp`. -/
structure FieldSep (sa : AState) : Prop where
  /-- The output and the first argument. -/
  oi : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsi") 0 24
  /-- The output and the second argument. -/
  oj : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rdx") 0 24
  /-- The two arguments. -/
  ij : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rdx") 0 24
  /-- The output and the words below `%rsp`. -/
  os : RangeDisj (sa.regs "%rdi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The first argument and the words below `%rsp`. -/
  is : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The second argument and the words below `%rsp`. -/
  js : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-144) (-8)

/-- The buffers the concatenation callee touches are pairwise disjoint: the sixteen-word
    output at `%rdi`, the four four-limb arguments at `%rsi`, `%rdx`, `%rcx` and `%r8`,
    and the eighteen words below `%rsp`. -/
structure JoinSep (sa : AState) : Prop where
  /-- The output and the first argument. -/
  o1 : RangeDisj (sa.regs "%rdi") 0 120 (sa.regs "%rsi") 0 24
  /-- The output and the second argument. -/
  o2 : RangeDisj (sa.regs "%rdi") 0 120 (sa.regs "%rdx") 0 24
  /-- The output and the third argument. -/
  o3 : RangeDisj (sa.regs "%rdi") 0 120 (sa.regs "%rcx") 0 24
  /-- The output and the fourth argument. -/
  o4 : RangeDisj (sa.regs "%rdi") 0 120 (sa.regs "%r8") 0 24
  /-- The output and the words below `%rsp`. -/
  os : RangeDisj (sa.regs "%rdi") 0 120 (sa.regs "%rsp") (-144) (-8)
  /-- The first and second arguments. -/
  a12 : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rdx") 0 24
  /-- The first and third arguments. -/
  a13 : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rcx") 0 24
  /-- The first and fourth arguments. -/
  a14 : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%r8") 0 24
  /-- The first argument and the words below `%rsp`. -/
  a1s : RangeDisj (sa.regs "%rsi") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The second and third arguments. -/
  a23 : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rcx") 0 24
  /-- The second and fourth arguments. -/
  a24 : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%r8") 0 24
  /-- The second argument and the words below `%rsp`. -/
  a2s : RangeDisj (sa.regs "%rdx") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The third and fourth arguments. -/
  a34 : RangeDisj (sa.regs "%rcx") 0 24 (sa.regs "%r8") 0 24
  /-- The third argument and the words below `%rsp`. -/
  a3s : RangeDisj (sa.regs "%rcx") 0 24 (sa.regs "%rsp") (-144) (-8)
  /-- The fourth argument and the words below `%rsp`. -/
  a4s : RangeDisj (sa.regs "%r8") 0 24 (sa.regs "%rsp") (-144) (-8)

/-- The effect of a two-argument field call at one state: with both inputs below `pM` it
    leaves `op` of the four-limb values at `%rsi` and at `%rdx`, reduced modulo `pM`, at
    `%rdi`, changes no memory outside the 32 bytes at `%rdi` and the eighteen words below
    `%rsp`, and keeps `%rsp`. -/
def FieldEffect (C : ACallModel) (f : String) (op : Nat → Nat → Nat) (sa : AState) : Prop :=
  (feO sa.mem (sa.regs "%rsi") 0 < pM → feO sa.mem (sa.regs "%rdx") 0 < pM →
    feO (C f sa).mem (sa.regs "%rdi") 0
      = op (feO sa.mem (sa.regs "%rsi") 0) (feO sa.mem (sa.regs "%rdx") 0) % pM)
  ∧ FrameCS sa.mem (C f sa).mem (sa.regs "%rdi") 4 (sa.regs "%rsp")
  ∧ (C f sa).regs "%rsp" = sa.regs "%rsp"

/-- A field callee with that effect at every state. -/
def FieldCallee (C : ACallModel) (f : String) (op : Nat → Nat → Nat) : Prop :=
  ∀ sa : AState, FieldEffect C f op sa

/-- A field callee with that effect at every state whose buffers are pairwise
    disjoint. -/
def FieldCalleeSep (C : ACallModel) (f : String) (op : Nat → Nat → Nat) : Prop :=
  ∀ sa : AState, FieldSep sa → FieldEffect C f op sa

/-- The effect of the concatenation call at one state: it leaves the four-limb values at
    `%rsi`, `%rdx`, `%rcx` and `%r8` in the four consecutive field slots at `%rdi`,
    changes no memory outside the 128 bytes at `%rdi` and the eighteen words below
    `%rsp`, and keeps `%rsp`. -/
def JoinEffect (C : ACallModel) (f : String) (sa : AState) : Prop :=
  (feO (C f sa).mem (sa.regs "%rdi") 0 = feO sa.mem (sa.regs "%rsi") 0
    ∧ feO (C f sa).mem (sa.regs "%rdi") 32 = feO sa.mem (sa.regs "%rdx") 0
    ∧ feO (C f sa).mem (sa.regs "%rdi") 64 = feO sa.mem (sa.regs "%rcx") 0
    ∧ feO (C f sa).mem (sa.regs "%rdi") 96 = feO sa.mem (sa.regs "%r8") 0)
  ∧ FrameCS sa.mem (C f sa).mem (sa.regs "%rdi") 16 (sa.regs "%rsp")
  ∧ (C f sa).regs "%rsp" = sa.regs "%rsp"

/-- The concatenation callee with that effect at every state whose buffers are pairwise
    disjoint. -/
def JoinCallee (C : ACallModel) (f : String) : Prop :=
  ∀ sa : AState, JoinSep sa → JoinEffect C f sa

/-- The four callees of the mixed addition at their specifications. -/
structure MaddCallees (C : ACallModel) : Prop where
  /-- `fe25519_add` adds modulo `pM`. -/
  add : FieldCallee C addSym fun x y => x + y
  /-- `fe25519_sub` subtracts modulo `pM`. -/
  sub : FieldCallee C subSym fun x y => x + (pM - y)
  /-- `fe25519_mul` multiplies modulo `pM`. -/
  mul : FieldCalleeSep C mulSym fun x y => x * y
  /-- `ed25519_join16` concatenates four field elements. -/
  join : JoinCallee C join16Sym

/-! ## 4. The cells of the block and their disjointness -/

/-- The eight-byte cells the block and its callees access: the 92 stack words from the
    eighteen words of callee frames below `%rsp` up to the two pointer slots at 576 and
    584, the 28 words of the input point at `%rsi + 8i`, and the 16 output words at
    `%rdi + 8i`. -/
def maddCells : List (String × Int) :=
  (List.range 92).map (fun i => ("%rsp", ((8 * i : Nat) : Int) - 144)) ++
  (List.range 28).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
  (List.range 16).map (fun i => ("%rdi", ((8 * i : Nat) : Int)))

theorem memRsp (o : Int) (h0 : -144 ≤ o) (h1 : o ≤ 584) (h8 : o % 8 = 0) :
    ("%rsp", o) ∈ maddCells := by
  refine List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨((o + 144) / 8).toNat, ?_, ?_⟩))
  · exact List.mem_range.2 (by omega)
  · have : ((8 * ((o + 144) / 8).toNat : Nat) : Int) - 144 = o := by omega
    rw [this]

theorem memRsi (o : Int) (h0 : 0 ≤ o) (h1 : o ≤ 216) (h8 : o % 8 = 0) :
    ("%rsi", o) ∈ maddCells := by
  refine List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨(o / 8).toNat, ?_, ?_⟩))
  · exact List.mem_range.2 (by omega)
  · have : ((8 * (o / 8).toNat : Nat) : Int) = o := by omega
    rw [this]

theorem memRdi (o : Int) (h0 : 0 ≤ o) (h1 : o ≤ 120) (h8 : o % 8 = 0) :
    ("%rdi", o) ∈ maddCells := by
  refine List.mem_append_right _
    (List.mem_map.2 ⟨(o / 8).toNat, ?_, ?_⟩)
  · exact List.mem_range.2 (by omega)
  · have : ((8 * (o / 8).toNat : Nat) : Int) = o := by omega
    rw [this]

theorem bankRsp : shippedBank "%rsp" = some "%rsp" := by decide
theorem bankRsi : shippedBank "%rsi" = some "%rsi" := by decide
theorem bankRdi : shippedBank "%rdi" = some "%rdi" := by decide

theorem keyAddr_shipped (P : String → BitVec 64) (b : String) (o : Int)
    (hb : shippedBank b = some b) : keyAddr shippedBank P (b, o) = P b + BitVec.ofInt 64 o := by
  simp only [keyAddr, basePtr, hb]

/-- The address of a cell whose base register is named by an equation. -/
theorem keyAddr_of {P : String → BitVec 64} {k : String × Int} {b : String} (hb : k.1 = b)
    (hbb : shippedBank b = some b) : keyAddr shippedBank P k = P b + BitVec.ofInt 64 k.2 := by
  simp only [keyAddr, basePtr, hb, hbb]

/-- Two cells at one base, at offsets at least eight apart, are disjoint. -/
theorem djSS (p : BitVec 64) (o o' : Int) (h : 8 ≤ (o - o').natAbs)
    (h' : (o - o').natAbs ≤ 2 ^ 64 - 8) :
    Disjoint8 (p + BitVec.ofInt 64 o) (p + BitVec.ofInt 64 o') :=
  disjoint8_add_ofInt p o o' h h'

/-- A stack cell and an input-point cell are disjoint. -/
theorem djIS {R : String → BitVec 64} (hsep : Separated shippedBank R maddCells)
    (o o' : Int) (h0 : -144 ≤ o) (h1 : o ≤ 584) (h8 : o % 8 = 0)
    (g0 : 0 ≤ o') (g1 : o' ≤ 216) (g8 : o' % 8 = 0) :
    Disjoint8 (R "%rsp" + BitVec.ofInt 64 o) (R "%rsi" + BitVec.ofInt 64 o') := by
  have h := hsep ("%rsp", o) (memRsp o h0 h1 h8) ("%rsi", o') (memRsi o' g0 g1 g8)
    (by simp)
  rwa [keyAddr_shipped _ _ _ bankRsp, keyAddr_shipped _ _ _ bankRsi] at h

/-- A stack cell and an output cell are disjoint. -/
theorem djOS {R : String → BitVec 64} (hsep : Separated shippedBank R maddCells)
    (o o' : Int) (h0 : 0 ≤ o) (h1 : o ≤ 584) (h8 : o % 8 = 0)
    (g0 : 0 ≤ o') (g1 : o' ≤ 120) (g8 : o' % 8 = 0) :
    Disjoint8 (R "%rsp" + BitVec.ofInt 64 o) (R "%rdi" + BitVec.ofInt 64 o') := by
  have h := hsep ("%rsp", o) (memRsp o (by omega) h1 h8) ("%rdi", o') (memRdi o' g0 g1 g8)
    (by simp)
  rwa [keyAddr_shipped _ _ _ bankRsp, keyAddr_shipped _ _ _ bankRdi] at h

/-! ## 5. The bodies of the call segments -/

/-- The input pointer: the word in the stack slot at `%rsp + 576`. -/
def inPtr (sa : AState) : BitVec 64 := read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 576)

/-- The output pointer: the word in the stack slot at `%rsp + 584`. -/
def outPtr (sa : AState) : BitVec 64 := read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 584)

theorem leaZero (p : BitVec 64) (o : Int) :
    p + p * BitVec.ofNat 64 0 + BitVec.ofInt 64 o = p + BitVec.ofInt 64 o := by
  simp

/-- The body of a call segment whose two arguments are at the input pointer. -/
theorem runArgsRR (sa : AState) (d o1 o2 : Int) :
    let s' := runBlockA sa
        [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
         .lea "%rsi" "%r10" "%r10" 0 o1, .lea "%rdx" "%r10" "%r10" 0 o2]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 d
      ∧ s'.regs "%rsi" = inPtr sa + BitVec.ofInt 64 o1
      ∧ s'.regs "%rdx" = inPtr sa + BitVec.ofInt 64 o2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 d = _
    exact leaZero _ _
  · show inPtr sa + inPtr sa * BitVec.ofNat 64 0 + BitVec.ofInt 64 o1 = _
    exact leaZero _ _
  · show inPtr sa + inPtr sa * BitVec.ofNat 64 0 + BitVec.ofInt 64 o2 = _
    exact leaZero _ _

/-- The body of a call segment whose first argument is on the stack and whose second
    is at the input pointer. -/
theorem runArgsSR (sa : AState) (d o1 o2 : Int) :
    let s' := runBlockA sa
        [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
         .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%r10" "%r10" 0 o2]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 d
      ∧ s'.regs "%rsi" = sa.regs "%rsp" + BitVec.ofInt 64 o1
      ∧ s'.regs "%rdx" = inPtr sa + BitVec.ofInt 64 o2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 d = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o1 = _
    exact leaZero _ _
  · show inPtr sa + inPtr sa * BitVec.ofNat 64 0 + BitVec.ofInt 64 o2 = _
    exact leaZero _ _

/-- The body of a call segment whose two arguments are on the stack. -/
theorem runArgsSS (sa : AState) (d o1 o2 : Int) :
    let s' := runBlockA sa
        [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
         .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%rsp" "%rsp" 0 o2]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 d
      ∧ s'.regs "%rsi" = sa.regs "%rsp" + BitVec.ofInt 64 o1
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 o2 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 d = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o1 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o2 = _
    exact leaZero _ _

/-- The body of the concatenation segment: four stack arguments and a stack output. -/
theorem runArgsJoin (sa : AState) (d o1 o2 o3 o4 : Int) :
    let s' := runBlockA sa
        [.loadMem "%r10" "%rsp" 576, .lea "%rdi" "%rsp" "%rsp" 0 d,
         .lea "%rsi" "%rsp" "%rsp" 0 o1, .lea "%rdx" "%rsp" "%rsp" 0 o2,
         .lea "%rcx" "%rsp" "%rsp" 0 o3, .lea "%r8" "%rsp" "%rsp" 0 o4]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%rdi" = sa.regs "%rsp" + BitVec.ofInt 64 d
      ∧ s'.regs "%rsi" = sa.regs "%rsp" + BitVec.ofInt 64 o1
      ∧ s'.regs "%rdx" = sa.regs "%rsp" + BitVec.ofInt 64 o2
      ∧ s'.regs "%rcx" = sa.regs "%rsp" + BitVec.ofInt 64 o3
      ∧ s'.regs "%r8" = sa.regs "%rsp" + BitVec.ofInt 64 o4 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 d = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o1 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o2 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o3 = _
    exact leaZero _ _
  · show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 o4 = _
    exact leaZero _ _

/-! ## 6. The entry stores and the output copy -/

/-- The entry segment stores the two pointer arguments in their stack slots. -/
theorem runEntry (sa : AState) :
    let s' := runBlockA sa
      [.storeMem "%rsp" 576 (.reg "%rsi"), .storeMem "%rsp" 584 (.reg "%rdi")]
    s'.regs = sa.regs
      ∧ s'.mem = write64 (write64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 576)
          (sa.regs "%rsi")) (sa.regs "%rsp" + BitVec.ofInt 64 584) (sa.regs "%rdi") :=
  ⟨rfl, rfl⟩

/-- The setup of the output copy: `%r10` at the output pointer, `%r9` at the result
    block on the stack. -/
theorem runOutSetup (sa : AState) :
    let s' := runBlockA sa [.loadMem "%r10" "%rsp" 584, .lea "%r9" "%rsp" "%rsp" 0 448]
    s'.mem = sa.mem ∧ s'.regs "%rsp" = sa.regs "%rsp"
      ∧ s'.regs "%r10" = outPtr sa
      ∧ s'.regs "%r9" = sa.regs "%rsp" + BitVec.ofInt 64 448 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show sa.regs "%rsp" + sa.regs "%rsp" * BitVec.ofNat 64 0 + BitVec.ofInt 64 448 = _
  exact leaZero _ _

/-- The load-store pairs copying the words at the offsets `os` from `%r9` to `%r10`. -/
def copyBlk : List Int → List (JInstr 64)
  | [] => []
  | o :: os => .loadMem "%r11" "%r9" o :: .storeMem "%r10" o (.reg "%r11") :: copyBlk os

theorem copyBlk_cons (sa : AState) (o : Int) (os : List Int) :
    runBlockA sa (copyBlk (o :: os)) =
      runBlockA (runBlockA sa [.loadMem "%r11" "%r9" o, .storeMem "%r10" o (.reg "%r11")])
        (copyBlk os) := rfl

/-- The copy changes no byte outside the words it writes. -/
theorem copyBlk_frame (sa : AState) (os : List Int) (x : BitVec 64)
    (h : ∀ o ∈ os, ¬ InRange8 (sa.regs "%r10" + BitVec.ofInt 64 o) x) :
    (runBlockA sa (copyBlk os)).mem x = sa.mem x := by
  induction os generalizing sa with
  | nil => rfl
  | cons o os ih =>
    rw [copyBlk_cons]
    have hr10 : (runBlockA sa [JInstr.loadMem "%r11" "%r9" o,
        JInstr.storeMem "%r10" o (.reg "%r11")]).regs "%r10" = sa.regs "%r10" := rfl
    rw [ih _ (by rw [hr10]; exact fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
    show write64 sa.mem _ _ x = _
    exact write64_of_not_inRange _ _ _ _ (h o List.mem_cons_self)

/-- A word disjoint from every copied word reads back unchanged. -/
theorem read64_copyBlk_frame (sa : AState) (os : List Int) (b : BitVec 64)
    (h : ∀ o ∈ os, Disjoint8 (sa.regs "%r10" + BitVec.ofInt 64 o) b) :
    read64 (runBlockA sa (copyBlk os)).mem b = read64 sa.mem b := by
  have key : ∀ i : Nat, i < 8 → (runBlockA sa (copyBlk os)).mem (b + BitVec.ofNat 64 i)
      = sa.mem (b + BitVec.ofNat 64 i) :=
    fun i hi => copyBlk_frame sa os _ fun o ho => not_inRange_of_disjoint _ _ i (h o ho) hi
  have h0 : (runBlockA sa (copyBlk os)).mem b = sa.mem b := by simpa using key 0 (by decide)
  simp only [read64, h0, key 1 (by decide), key 2 (by decide), key 3 (by decide),
    key 4 (by decide), key 5 (by decide), key 6 (by decide), key 7 (by decide)]

/-- Each copied word reads back at the output what it read at the source. -/
theorem copyBlk_val (sa : AState) (os : List Int) (hnd : os.Nodup)
    (hdd : ∀ o ∈ os, ∀ o' ∈ os, o ≠ o' →
      Disjoint8 (sa.regs "%r10" + BitVec.ofInt 64 o) (sa.regs "%r10" + BitVec.ofInt 64 o'))
    (hds : ∀ o ∈ os, ∀ o' ∈ os,
      Disjoint8 (sa.regs "%r10" + BitVec.ofInt 64 o) (sa.regs "%r9" + BitVec.ofInt 64 o'))
    (o : Int) (ho : o ∈ os) :
    read64 (runBlockA sa (copyBlk os)).mem (sa.regs "%r10" + BitVec.ofInt 64 o)
      = read64 sa.mem (sa.regs "%r9" + BitVec.ofInt 64 o) := by
  induction os generalizing sa with
  | nil => exact absurd ho List.not_mem_nil
  | cons a os ih =>
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.1 hnd
    have hr10 : (runBlockA sa [JInstr.loadMem "%r11" "%r9" a,
        JInstr.storeMem "%r10" a (.reg "%r11")]).regs "%r10" = sa.regs "%r10" := rfl
    have hr9 : (runBlockA sa [JInstr.loadMem "%r11" "%r9" a,
        JInstr.storeMem "%r10" a (.reg "%r11")]).regs "%r9" = sa.regs "%r9" := rfl
    have hmem : (runBlockA sa [JInstr.loadMem "%r11" "%r9" a,
        JInstr.storeMem "%r10" a (.reg "%r11")]).mem
        = write64 sa.mem (sa.regs "%r10" + BitVec.ofInt 64 a)
          (read64 sa.mem (sa.regs "%r9" + BitVec.ofInt 64 a)) := rfl
    rw [copyBlk_cons]
    rcases List.mem_cons.1 ho with rfl | ho'
    · rw [read64_copyBlk_frame _ os _ (by
        rw [hr10]
        exact fun o' ho' => hdd o' (List.mem_cons_of_mem _ ho') o List.mem_cons_self
          (fun e => hna (e ▸ ho')))]
      rw [hmem, read64_write64_same]
    · have hgoal := ih (runBlockA sa [JInstr.loadMem "%r11" "%r9" a,
          JInstr.storeMem "%r10" a (.reg "%r11")]) hnd'
        (by
          rw [hr10]
          intro x hx y hy hxy
          exact hdd x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)
        (by
          rw [hr10, hr9]
          intro x hx y hy
          exact hds x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        ho'
      rw [hr10, hr9, hmem, read64_write64_of_disjoint _ _ _ _
        (hds a List.mem_cons_self o (List.mem_cons_of_mem _ ho'))] at hgoal
      exact hgoal

/-! ## 7. One field call -/

/-- One field call: the body sets the argument registers, the callee leaves the reduced
    result in the stack slot at `%rsp + d` and changes nothing else. -/
theorem fieldStep {C : ACallModel} {f : String} {op : Nat → Nat → Nat}
    {sa : AState} {body : List (JInstr 64)}
    (hC : FieldEffect C f op (runBlockA sa body))
    (SP a1 a2 : BitVec 64) (d : Int)
    (hm : (runBlockA sa body).mem = sa.mem)
    (hsp : (runBlockA sa body).regs "%rsp" = SP)
    (hdi : (runBlockA sa body).regs "%rdi" = SP + BitVec.ofInt 64 d)
    (hsi : (runBlockA sa body).regs "%rsi" = a1)
    (hdx : (runBlockA sa body).regs "%rdx" = a2)
    (hb1 : feO sa.mem a1 0 < pM) (hb2 : feO sa.mem a2 0 < pM) :
    (C f (runBlockA sa body)).regs "%rsp" = SP
      ∧ feO (C f (runBlockA sa body)).mem SP d
        = op (feO sa.mem a1 0) (feO sa.mem a2 0) % pM
      ∧ FrameCS sa.mem (C f (runBlockA sa body)).mem (SP + BitVec.ofInt 64 d) 4 SP := by
  obtain ⟨hval, hfr, hrsp⟩ := hC
  rw [hsi, hdx, hdi, hm] at hval
  rw [hdi, hm, hsp] at hfr
  refine ⟨by rw [hrsp, hsp], ?_, hfr⟩
  rw [feO_base, show d + (0 : Int) = d by omega] at hval
  exact hval hb1 hb2

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519MaddShippedProof
