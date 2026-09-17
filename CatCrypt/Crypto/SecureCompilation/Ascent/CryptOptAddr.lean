/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import CatCrypt.Crypto.SecureCompilation.Ascent.CarryMulCorrect
public import CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquareCorrect

/-!
# CryptOpt's `carry_mul` and `solinas_square` over address memory

`CarryMul.carryMul_correct` and `SolinasSquare.solinasSquare_correct` are stated over
`runBlock`, whose memory is keyed by the name of the base register. This module states
both kernels over `AddrMem.runBlockA`, whose memory is a byte map from 64-bit addresses,
for pointers into non-overlapping regions.

A block is related to `runBlock` by `AddrMem.runBlockA_sim_on`, whose discipline requires
every memory base to hold, at each access, the entry value of a fixed register. The
`solinas_square` block satisfies it with the banks `%rsi`, `%rdi`, `%rsp`. The `carry_mul`
block writes registers it later uses as bases (`sub rsp`, `xchg rdx, rax`,
`mov r10, [rsp - 0x50]`), so it is related segment by segment, as in the name-keyed proof:
instructions 1–4 (`carryMulPre`, bank `%rdx`), 5–146 (`carryMulMid`, banks `%rsi`, `%rax`,
`%rsp`, entry values taken after instruction 4) and 148–166 (`carryMulTail`, banks `%r10`,
`%rsp`, entry values taken after instruction 147) pass the discipline; instructions 147 and
167 are stepped on the address machine.

## Separation

`RegionsApart a la b lb` states that the `la` bytes from `a` and the `lb` bytes from `b`
are disjoint modulo `2^64`. A layout is a list of regions `(base, lo, len)`;
`layoutOKB L K` checks that every cell of `K` lies in the region of its base and that
cells at one base have offsets at least eight apart, and `separated_of_layout` derives
`AddrMem.Separated` for `K` from `layoutOKB` and the pairwise `RegionsApart` of the
regions at distinct bases.

## Main results

* `RegionsApart`, `limbsAt`, `selfBank`: the separation predicate, the little-endian
  limbs at an address, and the bank map of registers based at their own values.
* `disjoint8_of_regionsApart`, `separated_of_layout`, `cellsSeparated_of_separated`: the
  separation lemmas.
* `carryMulMid_run`, `carryMulTail_run`: the name-keyed facts about the two
  memory-stable segments of `carry_mul`, from `carryMulMid_corres`,
  `absRunMem_carryMulMid_spec`, `carryMulTail_corres` and `absRunMem_carryMulTail_spec`.
* `carryMul_correct_addr`: for input pointers `x`, `y` and output pointer `z`, with the
  input regions apart from each other and from the stack frame, and the output region
  apart from the stack frame, the five words at `z` after `runBlockA` meet `CarryMulSpec`
  against the five words at `x` and at `y` before it. The output may overlap an input.
* `solinasSquare_correct_addr`: for an input pointer `x` and an output pointer `z` with
  the two regions and the spill region pairwise apart, the four words at `z` after
  `runBlockA` meet `SolinasSquareSpec` against the four words at `x` before it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.CryptOptAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem

/-! ## Regions and layouts -/

/-- The `la` bytes from `a` and the `lb` bytes from `b` are disjoint modulo `2^64`. -/
def RegionsApart (a : BitVec 64) (la : Nat) (b : BitVec 64) (lb : Nat) : Prop :=
  la ≤ (b - a).toNat ∧ lb ≤ (a - b).toNat

theorem RegionsApart.symm {a b : BitVec 64} {la lb : Nat} (h : RegionsApart a la b lb) :
    RegionsApart b lb a la :=
  ⟨h.2, h.1⟩

theorem RegionsApart.mono {a b : BitVec 64} {la lb la' lb' : Nat}
    (h : RegionsApart a la b lb) (ha : la' ≤ la) (hb : lb' ≤ lb) : RegionsApart a la' b lb' :=
  ⟨le_trans ha h.1, le_trans hb h.2⟩

/-- Eight-byte ranges inside two regions that are apart are disjoint. -/
theorem disjoint8_of_regionsApart_nat (A B : BitVec 64) (la lb i j : Nat)
    (h : RegionsApart A la B lb) (hi : i + 8 ≤ la) (hj : j + 8 ≤ lb) :
    Disjoint8 (A + BitVec.ofNat 64 i) (B + BitVec.ofNat 64 j) := by
  obtain ⟨h1, h2⟩ := h
  have := A.isLt
  have := B.isLt
  simp only [Disjoint8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2 ⊢
  constructor <;> omega

/-- A displacement at or above `lo` is `lo` plus a natural displacement. -/
theorem add_ofInt_eq (p : BitVec 64) (lo o : Int) (h : lo ≤ o) :
    p + BitVec.ofInt 64 o = (p + BitVec.ofInt 64 lo) + BitVec.ofNat 64 (o - lo).toNat := by
  have e : o = lo + (((o - lo).toNat : Nat) : Int) := by omega
  conv_lhs => rw [e]
  rw [BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.add_assoc]

/-- Cells inside two regions that are apart occupy disjoint eight-byte ranges. -/
theorem disjoint8_of_regionsApart (p q : BitVec 64) (lo lo' o o' : Int) (len len' : Nat)
    (h : RegionsApart (p + BitVec.ofInt 64 lo) len (q + BitVec.ofInt 64 lo') len')
    (ho : lo ≤ o) (ho2 : o + 8 ≤ lo + len) (ho' : lo' ≤ o') (ho2' : o' + 8 ≤ lo' + len') :
    Disjoint8 (p + BitVec.ofInt 64 o) (q + BitVec.ofInt 64 o') := by
  rw [add_ofInt_eq p lo o ho, add_ofInt_eq q lo' o' ho']
  exact disjoint8_of_regionsApart_nat _ _ len len' _ _ h (by omega) (by omega)

/-- The cell `k` lies in the region `g = (base, lo, len)`. -/
def inRegionB (k : String × Int) (g : String × Int × Nat) : Bool :=
  decide (k.1 = g.1) && decide (g.2.1 ≤ k.2) && decide (k.2 + 8 ≤ g.2.1 + (g.2.2 : Int))

/-- Every cell of `K` lies in a region of `L`, and two distinct cells of `K` at one base
    have offsets at least eight and at most `2^64 - 8` apart. -/
def layoutOKB (L : List (String × Int × Nat)) (K : List (String × Int)) : Bool :=
  K.all (fun k => L.any (inRegionB k)) &&
    K.all (fun k => K.all fun k' => !decide (k.1 = k'.1) || decide (k.2 = k'.2) ||
      (decide (8 ≤ (k.2 - k'.2).natAbs) && decide ((k.2 - k'.2).natAbs ≤ 2 ^ 64 - 8)))

/-- The regions of `L` at distinct bases are apart, at the base addresses of `bank` and
    `P`. -/
def LayoutApart (bank : String → Option String) (P : String → BitVec 64)
    (L : List (String × Int × Nat)) : Prop :=
  ∀ g ∈ L, ∀ g' ∈ L, g.1 ≠ g'.1 →
    RegionsApart (basePtr bank P g.1 + BitVec.ofInt 64 g.2.1) g.2.2
      (basePtr bank P g'.1 + BitVec.ofInt 64 g'.2.1) g'.2.2

/-- **Separation from a layout.** -/
theorem separated_of_layout (bank : String → Option String) (P : String → BitVec 64)
    (L : List (String × Int × Nat)) (K : List (String × Int)) (hL : layoutOKB L K = true)
    (h : LayoutApart bank P L) : Separated bank P K := by
  simp only [layoutOKB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hL
  obtain ⟨hreg, hsame⟩ := hL
  intro k hk k' hk' hne
  by_cases hb : k.1 = k'.1
  · have hs := hsame k hk k' hk'
    have ho : k.2 ≠ k'.2 := fun e => hne (Prod.ext hb e)
    rw [decide_eq_true hb, decide_eq_false ho] at hs
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hs
    simp only [keyAddr, hb]
    exact disjoint8_add_ofInt _ _ _ hs.1 hs.2
  · obtain ⟨g, hg, hkg⟩ := hreg k hk
    obtain ⟨g', hg', hkg'⟩ := hreg k' hk'
    simp only [inRegionB, Bool.and_eq_true, decide_eq_true_eq] at hkg hkg'
    obtain ⟨⟨e, l1⟩, l2⟩ := hkg
    obtain ⟨⟨e', l1'⟩, l2'⟩ := hkg'
    have hgg : g.1 ≠ g'.1 := fun x => hb (e.trans (x.trans e'.symm))
    have ha := h g hg g' hg' hgg
    simp only [keyAddr, e, e']
    exact disjoint8_of_regionsApart _ _ _ _ _ _ _ _ ha l1 l2 l1' l2'

theorem ofInt_zero_add (p : BitVec 64) : p + BitVec.ofInt 64 0 = p := by simp

theorem ofInt_neg128 : BitVec.ofInt 64 (-128) = -(128#64) := by decide

theorem add_ofInt_neg128 (r : BitVec 64) : r + BitVec.ofInt 64 (-128) = r - 128#64 := by
  rw [BitVec.sub_eq_add_neg, ofInt_neg128]

/-- The pairs of regions of a three-region layout, from the three `RegionsApart` facts. -/
theorem layoutApart_three (bank : String → Option String) (P : String → BitVec 64)
    (b₁ b₂ b₃ : String) (o₁ o₂ o₃ : Int) (l₁ l₂ l₃ : Nat) (A₁ A₂ A₃ : BitVec 64)
    (e₁ : basePtr bank P b₁ + BitVec.ofInt 64 o₁ = A₁)
    (e₂ : basePtr bank P b₂ + BitVec.ofInt 64 o₂ = A₂)
    (e₃ : basePtr bank P b₃ + BitVec.ofInt 64 o₃ = A₃)
    (h₁₂ : RegionsApart A₁ l₁ A₂ l₂) (h₁₃ : RegionsApart A₁ l₁ A₃ l₃)
    (h₂₃ : RegionsApart A₂ l₂ A₃ l₃) :
    LayoutApart bank P [(b₁, o₁, l₁), (b₂, o₂, l₂), (b₃, o₃, l₃)] := by
  intro g hg g' hg' hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg hg'
  rcases hg with rfl | rfl | rfl <;> rcases hg' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [e₁, e₂, e₃]
       first
       | exact h₁₂ | exact h₁₃ | exact h₂₃
       | exact h₁₂.symm | exact h₁₃.symm | exact h₂₃.symm)

/-- The pair of regions of a two-region layout, from one `RegionsApart` fact. -/
theorem layoutApart_two (bank : String → Option String) (P : String → BitVec 64)
    (b₁ b₂ : String) (o₁ o₂ : Int) (l₁ l₂ : Nat) (A₁ A₂ : BitVec 64)
    (e₁ : basePtr bank P b₁ + BitVec.ofInt 64 o₁ = A₁)
    (e₂ : basePtr bank P b₂ + BitVec.ofInt 64 o₂ = A₂)
    (h₁₂ : RegionsApart A₁ l₁ A₂ l₂) :
    LayoutApart bank P [(b₁, o₁, l₁), (b₂, o₂, l₂)] := by
  intro g hg g' hg' hne
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg hg'
  rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [e₁, e₂]
       first
       | exact h₁₂ | exact h₁₂.symm)

/-! ## Banks based at their own registers -/

/-- The bank map in which each register of `bs` is based at its own value. -/
def selfBank (bs : List String) (b : String) : Option String :=
  if b ∈ bs then some b else none

theorem basePtr_selfBank (bs : List String) (P : String → BitVec 64) (b : String)
    (hb : b ∈ bs) : basePtr (selfBank bs) P b = P b := by
  simp [basePtr, selfBank, hb]

theorem jOf_mem_selfBank (bs : List String) (sa : AState) (b : String) (hb : b ∈ bs)
    (o : Int) :
    (jOf (selfBank bs) sa).mem b o = read64 sa.mem (sa.regs b + BitVec.ofInt 64 o) := by
  simp only [jOf, absMem, keyAddr, basePtr_selfBank bs _ b hb]

theorem absMem_selfBank (bs : List String) (P : String → BitVec 64) (m : AMem) (b : String)
    (hb : b ∈ bs) (o : Int) :
    absMem (selfBank bs) P m b o = read64 m (P b + BitVec.ofInt 64 o) := by
  simp only [absMem, keyAddr, basePtr_selfBank bs _ b hb]

/-- Separated cells at self-based banks have distinct addresses. -/
theorem cellsSeparated_of_separated (bs : List String) (P : String → BitVec 64)
    (K : List (String × Int)) (hK : ∀ k ∈ K, k.1 ∈ bs) (h : Separated (selfBank bs) P K) :
    CellsSeparated K P := by
  intro c hc c' hc' he
  by_contra hne
  have hd := h c hc c' hc' hne
  simp only [keyAddr, basePtr_selfBank bs _ _ (hK c hc), basePtr_selfBank bs _ _ (hK c' hc')]
    at hd
  have he' : P c.1 + BitVec.ofInt 64 c.2 = P c'.1 + BitVec.ofInt 64 c'.2 := he
  rw [he'] at hd
  obtain ⟨h1, -⟩ := hd
  rw [BitVec.sub_self] at h1
  simp at h1

/-- The little-endian words at `p, p + 8, …`. -/
def limbsAt {n : Nat} (m : AMem) (p : BitVec 64) (i : Fin n) : BitVec 64 :=
  read64 m (p + BitVec.ofNat 64 (8 * i.val))

theorem limbsAt_eq {n : Nat} (m : AMem) (p : BitVec 64) (i : Fin n) :
    limbsAt m p i = read64 m (p + BitVec.ofInt 64 ((8 * i.val : Nat) : Int)) := by
  rw [limbsAt, BitVec.ofInt_natCast]

theorem limbsAt_eq' {n : Nat} (m : AMem) (p : BitVec 64) (i : Fin n) (o : Int)
    (ho : ((8 * i.val : Nat) : Int) = o) :
    limbsAt m p i = read64 m (p + BitVec.ofInt 64 o) := by
  rw [limbsAt_eq, ho]

/-! ## `carry_mul`: the name-keyed segment facts -/

section CarryMulSegments

open CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock
open CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul

/-- Instructions 5–146 on a name-keyed state whose tracked cells are separated and hold
    inputs below `2^54`: the facts `MidOut` states hold of an abstract state whose
    registers are those of the run, and the frame slot `[rsp - 0x50]` holds the entry
    `%rdi`. -/
theorem carryMulMid_run (st1 : JState 64) (hsep1 : CellsSeparated carryMulMidCells st1.regs)
    {a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : BitVec 64}
    (hI : MidIn (cellMem carryMulMidCells st1) st1.regs a0 a1 a2 a3 a4 b0 b1 b2 b3 b4)
    (ha0 : a0.toNat < 2 ^ 54) (ha1 : a1.toNat < 2 ^ 54) (ha2 : a2.toNat < 2 ^ 54)
    (ha3 : a3.toNat < 2 ^ 54) (ha4 : a4.toNat < 2 ^ 54)
    (hb0 : b0.toNat < 2 ^ 54) (hb1 : b1.toNat < 2 ^ 54) (hb2 : b2.toNat < 2 ^ 54)
    (hb3 : b3.toNat < 2 ^ 54) (hb4 : b4.toNat < 2 ^ 54)
    (hdx : (st1.regs "%rdx").toNat = b3.toNat * 19 % 2 ^ 64)
    (hr10 : (st1.regs "%r10").toNat = b2.toNat * 19 % 2 ^ 64) :
    ∃ s2 : AMemX, MidOut st1.regs (st1.regs "%rdi") a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 s2 ∧
      (∀ r, (runBlock st1 carryMulMid).regs r = s2.c.regs r) ∧
      (runBlock st1 carryMulMid).mem "%rsp" (-80) = st1.regs "%rdi" := by
  have hSR1 := srmem_cellMem carryMulMidCells st1 hsep1
  rw [← regsOf_ofRegs st1.regs] at hSR1
  obtain ⟨⟨hreg2, -, -⟩, hmem2, -⟩ := carryMulMid_corres st1 _ hSR1 trivial
  have hmo := absRunMem_carryMulMid_spec st1.regs (RegCM.ofRegs st1.regs)
    (st1.flagB (·.cf)) (st1.flagB (·.of)) (cellMem carryMulMidCells st1) hsep1 hI
    ha0 ha1 ha2 ha3 ha4 hb0 hb1 hb2 hb3 hb4 hdx hr10
  simp only [mkS] at hmo
  refine ⟨_, hmo, hreg2, ?_⟩
  rw [hmem2 ("%rsp", -80) (by decide)]
  simp only [cellAddr]
  rw [hmo.2.1]
  exact hmo.2.2.2.2.2.2.1

/-- Instructions 148–166 on a name-keyed state whose tracked cells are separated, with
    `%rdi = 51`, three limb registers below `2^51` and `%rbx` leaving room for a limb:
    the five words stored at `[r10 + 8i]` have as value the weighted sum of the limb
    registers with `%rbx`. -/
theorem carryMulTail_run (st3 : JState 64) (hsep3 : CellsSeparated carryMulTailCells st3.regs)
    (h51 : st3.regs "%rdi" = 51#64) (h13 : (st3.regs "%r13").toNat < 2 ^ 51)
    (h11 : (st3.regs "%r11").toNat < 2 ^ 51) (h12 : (st3.regs "%r12").toNat < 2 ^ 51)
    (hbx : (st3.regs "%rbx").toNat + 2 ^ 51 ≤ 2 ^ 64) :
    val5 ((runBlock st3 carryMulTail).mem "%r10" 0) ((runBlock st3 carryMulTail).mem "%r10" 8)
        ((runBlock st3 carryMulTail).mem "%r10" 16) ((runBlock st3 carryMulTail).mem "%r10" 24)
        ((runBlock st3 carryMulTail).mem "%r10" 32)
      = (st3.regs "%r13").toNat + 2 ^ 51 * (st3.regs "%r11").toNat +
        2 ^ 102 * (st3.regs "%r12").toNat + 2 ^ 153 * (st3.regs "%r14").toNat +
        2 ^ 204 * ((st3.regs "%rbp").toNat % 2 ^ 51) + (st3.regs "%rbx").toNat := by
  have hSR3 := srmem_cellMem carryMulTailCells st3 hsep3
  rw [← regsOf_ofRegs st3.regs] at hSR3
  obtain ⟨-, hmem4, -⟩ := carryMulTail_corres st3 _ hSR3 trivial
  have htl := absRunMem_carryMulTail_spec st3.regs (RegCM.ofRegs st3.regs)
    (st3.flagB (·.cf)) (st3.flagB (·.of)) (cellMem carryMulTailCells st3) h51 h13 h11 h12 hbx
  simp only [mkS] at htl
  obtain ⟨hr10s, hval⟩ := htl
  have hout : ∀ o : Int, ("%r10", o) ∈ carryMulTailCells →
      (runBlock st3 carryMulTail).mem "%r10" o =
        (absRunMem carryMulTail ⟨⟨regsOf (RegCM.ofRegs st3.regs) st3.regs, st3.flagB (·.cf),
          st3.flagB (·.of)⟩, cellMem carryMulTailCells st3⟩).mem
          ((RegCM.ofRegs st3.regs).r10 + BitVec.ofInt 64 o) := by
    intro o ho
    rw [hmem4 _ ho]
    simp only [cellAddr, hr10s]
  rw [hout 0 (by decide), hout 8 (by decide), hout 16 (by decide), hout 24 (by decide),
    hout 32 (by decide)]
  exact hval

end CarryMulSegments

/-! ## `carry_mul`: the address-machine segments -/

section CarryMulAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.CarryMulBlock
open CatCrypt.Crypto.SecureCompilation.Ascent.CarryMul

/-- The bank of instructions 1–4. -/
abbrev preBank : String → Option String := selfBank ["%rdx"]

/-- The banks of instructions 5–146. -/
abbrev midBank : String → Option String := selfBank ["%rsi", "%rax", "%rsp"]

/-- The banks of instructions 148–166. -/
abbrev tailBank : String → Option String := selfBank ["%r10", "%rsp"]

theorem carryMulPre_disciplined : disciplinedB preBank carryMulPre = true := by
  decide +kernel

theorem carryMulPre_writeKeys : writeKeys carryMulPre = [] := by
  decide +kernel

theorem carryMulMid_disciplined : disciplinedB midBank carryMulMid = true := by
  decide +kernel

theorem carryMulMid_reads : readsBeforeWritesFromB carryMulMidCells false carryMulMid = true := by
  decide +kernel

theorem carryMulMid_writes : ∀ k ∈ writeKeys carryMulMid, k ∈ carryMulMidCells := by
  decide +kernel

theorem carryMulTail_disciplined : disciplinedB tailBank carryMulTail = true := by
  decide +kernel

theorem carryMulTail_reads :
    readsBeforeWritesFromB carryMulTailCells false carryMulTail = true := by
  decide +kernel

theorem carryMulTail_writes : ∀ k ∈ writeKeys carryMulTail, k ∈ carryMulTailCells := by
  decide +kernel

/-- The regions of instructions 5–146: the two input arrays and the frame. -/
def carryMulMidLayout : List (String × Int × Nat) :=
  [("%rsi", 0, 40), ("%rax", 0, 40), ("%rsp", -128, 136)]

/-- The regions of instructions 148–166: the output array and the saved registers. -/
def carryMulTailLayout : List (String × Int × Nat) :=
  [("%r10", 0, 40), ("%rsp", -128, 48)]

theorem carryMulMid_layoutOK : layoutOKB carryMulMidLayout carryMulMidCells = true := by
  decide +kernel

theorem carryMulTail_layoutOK : layoutOKB carryMulTailLayout carryMulTailCells = true := by
  decide +kernel

theorem carryMulMid_bases : ∀ k ∈ carryMulMidCells, k.1 ∈ ["%rsi", "%rax", "%rsp"] := by
  decide +kernel

theorem carryMulTail_bases : ∀ k ∈ carryMulTailCells, k.1 ∈ ["%r10", "%rsp"] := by
  decide +kernel

theorem frame_start (r : BitVec 64) : r - 136#64 + BitVec.ofInt 64 (-128) = r - 264#64 := by
  rw [ofInt_neg128, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  congr 1

/-- The effect of instructions 1–4 on the address machine. -/
theorem runBlockA_carryMulPre (sa : AState) :
    (runBlockA sa carryMulPre).mem = sa.mem ∧
    (runBlockA sa carryMulPre).regs "%rax" = sa.regs "%rdx" ∧
    (runBlockA sa carryMulPre).regs "%rsp" = sa.regs "%rsp" - 136#64 ∧
    ((runBlockA sa carryMulPre).regs "%rdx").toNat =
      (read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 24)).toNat * 19 % 2 ^ 64 ∧
    ((runBlockA sa carryMulPre).regs "%r10").toNat =
      (read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 16)).toNat * 19 % 2 ^ 64 ∧
    (runBlockA sa carryMulPre).regs "%rsi" = sa.regs "%rsi" ∧
    (runBlockA sa carryMulPre).regs "%rdi" = sa.regs "%rdi" := by
  obtain ⟨hr, -, -⟩ := runBlockA_sim_on preBank carryMulPre [] carryMulPre_disciplined
    (by decide +kernel) (by rw [carryMulPre_writeKeys]; simp) sa
    (fun k hk => by simp at hk)
  have hmem : (runBlockA sa carryMulPre).mem = sa.mem := funext fun p =>
    runBlockA_mem_frame preBank _ carryMulPre_disciplined sa p
      (by rw [carryMulPre_writeKeys]; simp)
  obtain ⟨-, hax, hsp, hdx, hr10, hsi, hdi⟩ := runBlock_carryMulPre (jOf preBank sa)
  rw [jOf_mem_selfBank ["%rdx"] sa "%rdx" (by simp) 24] at hdx
  rw [jOf_mem_selfBank ["%rdx"] sa "%rdx" (by simp) 16] at hr10
  refine ⟨hmem, (congrFun hr "%rax").trans hax, (congrFun hr "%rsp").trans hsp, ?_, ?_,
    (congrFun hr "%rsi").trans hsi, (congrFun hr "%rdi").trans hdi⟩
  · rw [congrFun hr "%rdx"]; exact hdx
  · rw [congrFun hr "%r10"]; exact hr10

/-- The effect of instruction 147 on the address machine. -/
theorem runBlockA_carryMulLoadOut (sa : AState) :
    (runBlockA sa carryMulLoadOut).mem = sa.mem ∧
    (runBlockA sa carryMulLoadOut).regs "%r10" =
      read64 sa.mem (sa.regs "%rsp" + BitVec.ofInt 64 (-80)) ∧
    ∀ r, r ≠ "%r10" → (runBlockA sa carryMulLoadOut).regs r = sa.regs r := by
  refine ⟨rfl, ?_, fun r hr => ?_⟩
  · simp [carryMulLoadOut, evalInstrA, evalInstr, JState.setReg, JState.load, x86_MOV,
      AState.view]
  · simp [carryMulLoadOut, evalInstrA, evalInstr, JState.setReg, x86_MOV, AState.view, hr]

/-- Instruction 167 leaves the address memory unchanged. -/
theorem runBlockA_carryMulPost_mem (sa : AState) :
    (runBlockA sa carryMulPost).mem = sa.mem := rfl

/-- **Functional correctness of CryptOpt's `fiat_curve25519_carry_mul` over address
    memory.** Let `%rsi`, `%rdx`, `%rdi` hold `x`, `y`, `z`. When the 40 bytes from `x`,
    the 40 bytes from `y` and the 136 bytes of the frame below `%rsp - 128` are pairwise
    apart, the 40 bytes from `z` are apart from the frame, and the input limbs are below
    `2^54`, the five words at `z` after `runBlockA` meet fiat-crypto's `mul_correct`
    congruence against the five words at `x` and at `y` before it. The output region may
    overlap either input region. -/
theorem carryMul_correct_addr (sa : AState) (x y z : BitVec 64)
    (hx : sa.regs "%rsi" = x) (hy : sa.regs "%rdx" = y) (hz : sa.regs "%rdi" = z)
    (hxy : RegionsApart x 40 y 40)
    (hxs : RegionsApart x 40 (sa.regs "%rsp" - 264#64) 136)
    (hys : RegionsApart y 40 (sa.regs "%rsp" - 264#64) 136)
    (hzs : RegionsApart z 40 (sa.regs "%rsp" - 264#64) 136)
    (ha : LimbsBelow54 (limbsAt sa.mem x)) (hb : LimbsBelow54 (limbsAt sa.mem y)) :
    CarryMulSpec (limbsAt sa.mem x) (limbsAt sa.mem y)
      (limbsAt (runBlockA sa carryMulBlock).mem z) := by
  have hblk : runBlockA sa carryMulBlock = runBlockA (runBlockA (runBlockA (runBlockA
      (runBlockA sa carryMulPre) carryMulMid) carryMulLoadOut) carryMulTail) carryMulPost := by
    rw [← carryMulBody_eq_block]
    simp only [runBlockA_append]
  -- instructions 1–4
  obtain ⟨hm1, hax1, hsp1, hdx1, hr101, hsi1, hdi1⟩ := runBlockA_carryMulPre sa
  generalize runBlockA sa carryMulPre = sa1 at hm1 hax1 hsp1 hdx1 hr101 hsi1 hdi1 hblk
  -- instructions 5–146
  have hlay1 : LayoutApart midBank sa1.regs carryMulMidLayout :=
    layoutApart_three _ _ _ _ _ _ _ _ _ _ _ x y (sa.regs "%rsp" - 264#64)
      (by rw [basePtr_selfBank ["%rsi", "%rax", "%rsp"] sa1.regs "%rsi" (by simp),
        ofInt_zero_add, hsi1, hx])
      (by rw [basePtr_selfBank ["%rsi", "%rax", "%rsp"] sa1.regs "%rax" (by simp),
        ofInt_zero_add, hax1, hy])
      (by rw [basePtr_selfBank ["%rsi", "%rax", "%rsp"] sa1.regs "%rsp" (by simp), hsp1,
        frame_start])
      hxy hxs hys
  have hsep1 : Separated midBank sa1.regs carryMulMidCells :=
    separated_of_layout _ _ _ _ carryMulMid_layoutOK hlay1
  obtain ⟨hreg2, -, hK2⟩ := runBlockA_sim_on midBank carryMulMid carryMulMidCells
    carryMulMid_disciplined carryMulMid_reads carryMulMid_writes sa1 hsep1
  have hcs1 : CellsSeparated carryMulMidCells (jOf midBank sa1).regs :=
    cellsSeparated_of_separated _ _ _ carryMulMid_bases hsep1
  have rd : ∀ (b : String) (hb : b ∈ ["%rsi", "%rax", "%rsp"]) (o : Int), (b, o) ∈ carryMulMidCells →
      cellMem carryMulMidCells (jOf midBank sa1) ((jOf midBank sa1).regs b + BitVec.ofInt 64 o) =
        read64 sa.mem (sa1.regs b + BitVec.ofInt 64 o) := by
    intro b hb o ho
    rw [← hm1, ← jOf_mem_selfBank ["%rsi", "%rax", "%rsp"] sa1 b hb o]
    exact cellMem_eq _ _ hcs1 (b, o) ho
  have hI : MidIn (cellMem carryMulMidCells (jOf midBank sa1)) (jOf midBank sa1).regs
      (limbsAt sa.mem x (0 : Fin 5)) (limbsAt sa.mem x (1 : Fin 5)) (limbsAt sa.mem x (2 : Fin 5)) (limbsAt sa.mem x (3 : Fin 5))
      (limbsAt sa.mem x (4 : Fin 5)) (limbsAt sa.mem y (0 : Fin 5)) (limbsAt sa.mem y (1 : Fin 5)) (limbsAt sa.mem y (2 : Fin 5))
      (limbsAt sa.mem y (3 : Fin 5)) (limbsAt sa.mem y (4 : Fin 5)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rd "%rsi" (by simp) 0 (by decide), limbsAt_eq' sa.mem x (0 : Fin 5) 0 rfl, hsi1, hx]
    · rw [rd "%rsi" (by simp) 8 (by decide), limbsAt_eq' sa.mem x (1 : Fin 5) 8 rfl, hsi1, hx]
    · rw [rd "%rsi" (by simp) 16 (by decide), limbsAt_eq' sa.mem x (2 : Fin 5) 16 rfl, hsi1,
        hx]
    · rw [rd "%rsi" (by simp) 24 (by decide), limbsAt_eq' sa.mem x (3 : Fin 5) 24 rfl, hsi1,
        hx]
    · rw [rd "%rsi" (by simp) 32 (by decide), limbsAt_eq' sa.mem x (4 : Fin 5) 32 rfl, hsi1,
        hx]
    · rw [rd "%rax" (by simp) 0 (by decide), limbsAt_eq' sa.mem y (0 : Fin 5) 0 rfl, hax1, hy]
    · rw [rd "%rax" (by simp) 8 (by decide), limbsAt_eq' sa.mem y (1 : Fin 5) 8 rfl, hax1, hy]
    · rw [rd "%rax" (by simp) 16 (by decide), limbsAt_eq' sa.mem y (2 : Fin 5) 16 rfl, hax1,
        hy]
    · rw [rd "%rax" (by simp) 24 (by decide), limbsAt_eq' sa.mem y (3 : Fin 5) 24 rfl, hax1,
        hy]
    · rw [rd "%rax" (by simp) 32 (by decide), limbsAt_eq' sa.mem y (4 : Fin 5) 32 rfl, hax1,
        hy]
  have hy3 : read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 24) = limbsAt sa.mem y (3 : Fin 5) := by
    rw [limbsAt_eq' sa.mem y (3 : Fin 5) 24 rfl, hy]
  have hy2 : read64 sa.mem (sa.regs "%rdx" + BitVec.ofInt 64 16) = limbsAt sa.mem y (2 : Fin 5) := by
    rw [limbsAt_eq' sa.mem y (2 : Fin 5) 16 rfl, hy]
  rw [hy3] at hdx1
  rw [hy2] at hr101
  obtain ⟨s2, hmo, hr2, hslot⟩ := carryMulMid_run (jOf midBank sa1) hcs1 hI
    (ha 0) (ha 1) (ha 2) (ha 3) (ha 4) (hb 0) (hb 1) (hb 2) (hb 3) (hb 4) hdx1 hr101
  obtain ⟨h51, hsp2, h13, h11, h12, hbx, -, hcong⟩ := hmo
  generalize runBlockA sa1 carryMulMid = sa2 at hreg2 hK2 hblk
  have hreg2' : ∀ r, sa2.regs r = s2.c.regs r := fun r => (congrFun hreg2 r).trans (hr2 r)
  have hslot2 : read64 sa2.mem (sa2.regs "%rsp" + BitVec.ofInt 64 (-80)) = z := by
    have e := hK2 ("%rsp", -80) (by decide)
    dsimp only at e
    rw [absMem_selfBank ["%rsi", "%rax", "%rsp"] sa1.regs sa2.mem "%rsp" (by simp)] at e
    rw [hreg2' "%rsp", hsp2]
    exact e.trans (hslot.trans (hdi1.trans hz))
  -- instruction 147
  obtain ⟨hm3, hr103, hreg3⟩ := runBlockA_carryMulLoadOut sa2
  rw [hslot2] at hr103
  generalize runBlockA sa2 carryMulLoadOut = sa3 at hm3 hr103 hreg3 hblk
  have hr3 : ∀ r, r ≠ "%r10" → sa3.regs r = s2.c.regs r := fun r hr =>
    (hreg3 r hr).trans (hreg2' r)
  have hsp3 : sa3.regs "%rsp" = sa.regs "%rsp" - 136#64 := by
    rw [hr3 "%rsp" (by decide), hsp2]; exact hsp1
  -- instructions 148–166
  have hlay3 : LayoutApart tailBank sa3.regs carryMulTailLayout :=
    layoutApart_two _ _ _ _ _ _ _ _ z (sa.regs "%rsp" - 264#64)
      (by rw [basePtr_selfBank ["%r10", "%rsp"] sa3.regs "%r10" (by simp), ofInt_zero_add,
        hr103])
      (by rw [basePtr_selfBank ["%r10", "%rsp"] sa3.regs "%rsp" (by simp), hsp3, frame_start])
      (hzs.mono le_rfl (by decide))
  have hsep3 : Separated tailBank sa3.regs carryMulTailCells :=
    separated_of_layout _ _ _ _ carryMulTail_layoutOK hlay3
  obtain ⟨-, -, hK4⟩ := runBlockA_sim_on tailBank carryMulTail carryMulTailCells
    carryMulTail_disciplined carryMulTail_reads carryMulTail_writes sa3 hsep3
  have hcs3 : CellsSeparated carryMulTailCells (jOf tailBank sa3).regs :=
    cellsSeparated_of_separated _ _ _ carryMulTail_bases hsep3
  have g : ∀ r, r ≠ "%r10" → (jOf tailBank sa3).regs r = s2.c.regs r := hr3
  have hval := carryMulTail_run (jOf tailBank sa3) hcs3
    ((g "%rdi" (by decide)).trans h51)
    (by rw [g "%r13" (by decide)]; exact h13) (by rw [g "%r11" (by decide)]; exact h11)
    (by rw [g "%r12" (by decide)]; exact h12) (by rw [g "%rbx" (by decide)]; exact hbx)
  rw [g "%r13" (by decide), g "%r11" (by decide), g "%r12" (by decide),
    g "%r14" (by decide), g "%rbp" (by decide), g "%rbx" (by decide)] at hval
  rw [← hval] at hcong
  -- instruction 167 and the output words
  have hout : ∀ i : Fin 5, limbsAt (runBlockA sa carryMulBlock).mem z i =
      (runBlock (jOf tailBank sa3) carryMulTail).mem "%r10" ((8 * i.val : Nat) : Int) := by
    intro i
    have hc : ("%r10", ((8 * i.val : Nat) : Int)) ∈ carryMulTailCells := by
      fin_cases i <;> decide
    have e := hK4 _ hc
    dsimp only at e
    rw [absMem_selfBank ["%r10", "%rsp"] sa3.regs _ "%r10" (by simp)] at e
    rw [hblk, runBlockA_carryMulPost_mem, limbsAt_eq, ← hr103]
    exact e
  unfold CarryMulSpec eval5
  rw [hout 0, hout 1, hout 2, hout 3, hout 4]
  exact hcong

end CarryMulAddr

/-! ## `solinas_square` over address memory -/

section SolinasAddr

open CatCrypt.Crypto.SecureCompilation.X86Backend.SolinasSquareBlock
open CatCrypt.Crypto.SecureCompilation.Ascent.SolinasSquare

/-- The banks of `solinas_square`. -/
abbrev solinasBank : String → Option String := selfBank ["%rsi", "%rdi", "%rsp"]

theorem solinasSquareBlock_disciplined : disciplinedB solinasBank solinasSquareBlock = true := by
  decide +kernel

theorem solinasSquareBlock_reads :
    readsBeforeWritesFromB solinasCells false solinasSquareBlock = true := by
  decide +kernel

theorem solinasSquareBlock_writes : ∀ k ∈ writeKeys solinasSquareBlock, k ∈ solinasCells := by
  decide +kernel

/-- The regions of `solinas_square`: the input array, the output array and the spill
    slots. -/
def solinasLayout : List (String × Int × Nat) :=
  [("%rsi", 0, 32), ("%rdi", 0, 32), ("%rsp", -128, 48)]

theorem solinas_layoutOK : layoutOKB solinasLayout solinasCells = true := by
  decide +kernel

theorem solinas_bases : ∀ k ∈ solinasCells, k.1 ∈ ["%rsi", "%rdi", "%rsp"] := by
  decide +kernel

/-- **Functional correctness of CryptOpt's `fiat_curve25519_solinas_square` over address
    memory.** Let `%rsi` and `%rdi` hold `x` and `z`. When the 32 bytes from `x`, the 32
    bytes from `z` and the 48 bytes from `%rsp - 128` are pairwise apart, the four words
    at `z` after `runBlockA` represent a value congruent to the square of the value of
    the four words at `x` before it, modulo `2^255 - 19` (fiat-crypto's `sqr_correct`). -/
theorem solinasSquare_correct_addr (sa : AState) (x z : BitVec 64)
    (hx : sa.regs "%rsi" = x) (hz : sa.regs "%rdi" = z)
    (hxz : RegionsApart x 32 z 32)
    (hxs : RegionsApart x 32 (sa.regs "%rsp" - 128#64) 48)
    (hzs : RegionsApart z 32 (sa.regs "%rsp" - 128#64) 48) :
    SolinasSquareSpec (limbsAt sa.mem x) (limbsAt (runBlockA sa solinasSquareBlock).mem z) := by
  have hlay : LayoutApart solinasBank sa.regs solinasLayout :=
    layoutApart_three _ _ _ _ _ _ _ _ _ _ _ x z (sa.regs "%rsp" - 128#64)
      (by rw [basePtr_selfBank ["%rsi", "%rdi", "%rsp"] sa.regs "%rsi" (by simp),
        ofInt_zero_add, hx])
      (by rw [basePtr_selfBank ["%rsi", "%rdi", "%rsp"] sa.regs "%rdi" (by simp),
        ofInt_zero_add, hz])
      (by rw [basePtr_selfBank ["%rsi", "%rdi", "%rsp"] sa.regs "%rsp" (by simp),
        add_ofInt_neg128])
      hxz hxs hzs
  have hsep : Separated solinasBank sa.regs solinasCells :=
    separated_of_layout _ _ _ _ solinas_layoutOK hlay
  obtain ⟨-, -, hK⟩ := runBlockA_sim_on solinasBank solinasSquareBlock solinasCells
    solinasSquareBlock_disciplined solinasSquareBlock_reads solinasSquareBlock_writes sa hsep
  have hcs : CellsSeparated solinasCells (jOf solinasBank sa).regs :=
    cellsSeparated_of_separated _ _ _ solinas_bases hsep
  have h := solinasSquare_correct (jOf solinasBank sa) hcs
  have hin : ∀ i : Fin 4, (jOf solinasBank sa).mem "%rsi" (8 * (i.val : Int)) =
      limbsAt sa.mem x i := by
    intro i
    rw [jOf_mem_selfBank ["%rsi", "%rdi", "%rsp"] sa "%rsi" (by simp), limbsAt_eq, hx,
      Nat.cast_mul, Nat.cast_ofNat]
  have hout : ∀ i : Fin 4,
      (runBlock (jOf solinasBank sa) solinasSquareBlock).mem "%rdi" (8 * (i.val : Int)) =
        limbsAt (runBlockA sa solinasSquareBlock).mem z i := by
    intro i
    have hc : ("%rdi", 8 * (i.val : Int)) ∈ solinasCells := by
      fin_cases i <;> decide
    have e := hK _ hc
    dsimp only at e
    rw [absMem_selfBank ["%rsi", "%rdi", "%rsp"] sa.regs _ "%rdi" (by simp)] at e
    rw [← e, limbsAt_eq, hz, Nat.cast_mul, Nat.cast_ofNat]
  rw [funext hin, funext hout] at h
  exact h

end SolinasAddr

end CatCrypt.Crypto.SecureCompilation.Ascent.CryptOptAddr
