/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnSubBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesCorrect

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_add_n_loop_owned` and `mpn_sub_n_loop_owned`: sum, difference, carry, borrow

`MpnAddBytesValue.add_halts` and `MpnSubBytesValue.sub_halts` run the decoded linked objects
to their `ret` with the word models `addFold` / `subFold` of the entry words in `rp` and their
carry (borrow) in `%rax`. This module reads the value statements off those words
(`MpnCarryIdiomsHand.addFold_val_hand`, `subFold_val_hand`: `addFold_val`, `subFold_val` without
`bv_decide`), derives the separation from a numeric
address layout, and ties `%rax` to the denotation of the front-compiled programs
`MpnLoopFrontEmit.addRtProgOpt` / `subRtProgOpt`, of which the linked programs
`addLprogFront` / `subLprogFront` are the scalar-accumulator exports (by definition).

## Main results

* `mpn_add_n_bytes_correct`: the linked object is the ELF wrapping of `addText`, which decodes
  to `addDec`, and from every System V entry state with the words separated the machine halts
  with `value(rp[0..n)) + cy · 2^(64n) = value(ap[0..n)) + value(bp[0..n))`, `cy = %rax ≤ 1`,
  `%rsp` and the callee-saved registers restored, and no byte written outside the frame and
  the `n` words of `rp`; for every `n < 2^64`, `rp` disjoint from or equal to (or below) `ap`
  and `bp`.
* `mpn_sub_n_bytes_correct`: the same for the difference:
  `value(rp[0..n)) + value(bp[0..n)) = value(ap[0..n)) + bw · 2^(64n)`, `bw = %rax ≤ 1`.
* `mpn_add_n_correct`, `mpn_sub_n_correct`: the same with the separation given by an address
  layout (`AddLayout`, `SubLayout`).
* `mpn_add_n_denote`, `mpn_sub_n_denote`: `%rax` is the denotation of `addRtProgOpt`
  (`subRtProgOpt`) at every valuation that agrees with the entry state.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubBytesCorrect

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubShipped
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip (at' ix)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue (arr memGetDyn_arr wordsOf calleeSavedL)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesCorrect
  (cells_arr disj_of_toNat toNat_ix toNat_at')
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
  (addFold subFold addFold_val subFold_val addFold_snd subFold_snd addCarryFold subBorrowFold
   addLimbW subLimbW)

theorem cells_words (m : AMem) (p : BitVec 64) (n : Nat) {N : Nat} (o : Fin N → BitVec 64)
    (h : ∀ i, i < n → wordsOf m p i = memGetDyn o i) :
    (List.range n).map (wordsOf m p) = cells o n := by
  simp only [cells]
  refine List.map_congr_left (fun i hi => ?_)
  rw [List.mem_range] at hi
  exact h i hi

/-! ## 1. The value statements -/

/-- **The linked `mpn_add_n_loop_owned` computes the sum and returns the carry.** The linked
    object (`addObj`) is the ELF wrapping of `addText`, whose bytes decode to `addDec`; from
    every entry state with `rp`, `ap`, `bp`, `n` in `%rdi`, `%rsi`, `%rdx`, `%rcx` and the
    words separated (`AddSep`, frame base `%rsp - 64`), the address machine halts on `addDec`
    with `value(rp[0..n)) + %rax · 2^(64n) = value(ap[0..n)) + value(bp[0..n))` (the source
    words read at the entry), `%rax ≤ 1`, `%rsp` and the callee-saved registers as at the
    entry, and every byte outside the `80` frame bytes below the entry `%rsp` and the `n` words
    of `rp` as at the entry (`Keeps`). -/
theorem mpn_add_n_bytes_correct :
    addObj = ElfObject.buildElfObjectMulti [{ name := "mpn_add_n_loop_owned", text := addText }]
    ∧ decodeLprog addText = some addDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      MpnAddBytesValue.AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi")
        (s0.regs "%rdx") n →
      ∃ s', Halts aMachine addDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnAddBytesValue.Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem
            s'.mem := by
  refine ⟨addObj_eq, addText_decode, ?_⟩
  intro s0 n hrcx hS
  obtain ⟨s', hh, hw, hax, hsp, hcs, hk⟩ := MpnAddBytesValue.add_halts s0 n hrcx hS
  obtain ⟨hv, hc⟩ := MpnCarryIdiomsHand.addFold_val_hand (arr n (wordsOf s0.mem (s0.regs "%rsi")))
    (arr n (wordsOf s0.mem (s0.regs "%rdx"))) (arr n (wordsOf s0.mem (s0.regs "%rdi"))) 0#64
    (by decide) n le_rfl
  refine ⟨s', hh, ?_, by rw [hax]; exact hc, hsp, hcs, hk⟩
  rw [cells_words _ _ n _ hw, hax, hv, cells_arr n n _ le_rfl, cells_arr n n _ le_rfl]
  simp

/-- **The linked `mpn_sub_n_loop_owned` computes the difference and returns the borrow.** As
    `mpn_add_n_bytes_correct`, for `subObj` / `subText` / `subDec` (frame base `%rsp - 80`,
    `96` frame bytes): the machine halts with
    `value(rp[0..n)) + value(bp[0..n)) = value(ap[0..n)) + %rax · 2^(64n)` and `%rax ≤ 1`. -/
theorem mpn_sub_n_bytes_correct :
    subObj = ElfObject.buildElfObjectMulti [{ name := "mpn_sub_n_loop_owned", text := subText }]
    ∧ decodeLprog subText = some subDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      MpnSubBytesValue.SubSep (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi")
        (s0.regs "%rdx") n →
      ∃ s', Halts aMachine subDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnSubBytesValue.Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") n s0.mem
            s'.mem := by
  refine ⟨subObj_eq, subText_decode, ?_⟩
  intro s0 n hrcx hS
  obtain ⟨s', hh, hw, hax, hsp, hcs, hk⟩ := MpnSubBytesValue.sub_halts s0 n hrcx hS
  obtain ⟨hv, hc⟩ := MpnCarryIdiomsHand.subFold_val_hand (arr n (wordsOf s0.mem (s0.regs "%rsi")))
    (arr n (wordsOf s0.mem (s0.regs "%rdx"))) (arr n (wordsOf s0.mem (s0.regs "%rdi"))) 0#64
    (by decide) n le_rfl
  refine ⟨s', hh, ?_, by rw [hax]; exact hc, hsp, hcs, hk⟩
  rw [cells_words _ _ n _ hw, hax, ← cells_arr n n (wordsOf s0.mem (s0.regs "%rdx")) le_rfl,
    ← cells_arr n n (wordsOf s0.mem (s0.regs "%rsi")) le_rfl]
  simpa using hv

/-! ## 2. Separation from a numeric layout -/

/-- **A layout of the arguments.** With the entry stack pointer `E` and the frame size `F`
    (`80` for add, `96` for sub): the `n` words of `rp`, `ap` and `bp` and the `F` bytes below
    `E` lie in the address space without wrapping; `rp` starts at or below `ap` (in particular
    `rp = ap`, in place) or lies above `ap`'s words, and likewise for `bp`; the three arrays are
    disjoint from the frame. -/
structure ArgLayout (F : Nat) (E RP AP BP : BitVec 64) (n : Nat) : Prop where
  rpFit : RP.toNat + 8 * n < 2 ^ 64
  apFit : AP.toNat + 8 * n < 2 ^ 64
  bpFit : BP.toNat + 8 * n < 2 ^ 64
  frFit : F ≤ E.toNat
  rpAp : RP.toNat ≤ AP.toNat ∨ AP.toNat + 8 * n ≤ RP.toNat
  rpBp : RP.toNat ≤ BP.toNat ∨ BP.toNat + 8 * n ≤ RP.toNat
  rpFr : RP.toNat + 8 * n ≤ E.toNat - F ∨ E.toNat ≤ RP.toNat
  apFr : AP.toNat + 8 * n ≤ E.toNat - F ∨ E.toNat ≤ AP.toNat
  bpFr : BP.toNat + 8 * n ≤ E.toNat - F ∨ E.toNat ≤ BP.toNat

/-- The address of a frame word, from the entry stack pointer `E`, frame base `E - D`. -/
theorem toNat_slot (E : BitVec 64) (D F : Nat) (hE : F ≤ E.toNat) (o : Int)
    (ho : (D : Int) - F ≤ o ∧ o + 8 ≤ D) (hDF : D ≤ F) :
    ((at' (at' E (-(D : Int))) o).toNat : Int) = E.toNat - D + o := by
  have hE' := E.isLt
  have h1 : ((at' E (-(D : Int))).toNat : Int) = E.toNat + (-(D : Int)) :=
    toNat_at' E (-(D : Int)) (by omega) (by omega)
  rw [toNat_at' _ o (by omega) (by omega), h1]
  omega

/-- A byte of a frame word at offset `o ≥ -16` lies within `L` bytes of `SP - 16` when
    `o + 24 ≤ L`. -/
theorem inFr_of_slot (SP x : BitVec 64) (o : Int) (L : Nat) (ho : -16 ≤ o ∧ o + 24 ≤ L)
    (hL : L < 2 ^ 64) (hx : InRange8 (at' SP o) x) : (x - at' SP (-16)).toNat < L := by
  unfold InRange8 at hx
  have e : x - at' SP (-16) = (x - at' SP o) + BitVec.ofNat 64 (o + 16).toNat := by
    have hc : BitVec.ofInt 64 o = BitVec.ofInt 64 (-16) + BitVec.ofNat 64 (o + 16).toNat := by
      rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
      congr 1
      omega
    simp only [at', hc]
    abel
  rw [e, BitVec.toNat_add]
  generalize (x - at' SP o).toNat = d at hx ⊢
  have h16 : (BitVec.ofNat 64 (o + 16).toNat).toNat = (o + 16).toNat := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  rw [h16, Nat.mod_eq_of_lt (by omega)]
  omega

theorem addOffs_range : ∀ o ∈ MpnAddBytesValue.addOffs, -16 ≤ o ∧ o ≤ 56 := by decide

theorem subOffs_range : ∀ o ∈ MpnSubBytesValue.subOffs, -16 ≤ o ∧ o ≤ 72 := by decide

/-- **`AddSep` from a layout** (frame base `E - 64`, `80` frame bytes). -/
theorem addSep_of_layout {E RP AP BP : BitVec 64} {n : Nat} (h : ArgLayout 80 E RP AP BP n) :
    MpnAddBytesValue.AddSep (at' E (-64)) RP AP BP n := by
  have hr := h.rpFit
  have ha := h.apFit
  have hb := h.bpFit
  have hf := h.frFit
  have hE := E.isLt
  have hra := h.rpAp
  have hrb := h.rpBp
  have hrf := h.rpFr
  have haf := h.apFr
  have hbf := h.bpFr
  have hsl : ∀ o ∈ MpnAddBytesValue.addOffs,
      ((at' (at' E (-64)) o).toNat : Int) = E.toNat - 64 + o ∧ -16 ≤ o ∧ o ≤ 56 := by
    intro o ho
    have := addOffs_range o ho
    exact ⟨toNat_slot E 64 80 hf o (by omega) (by omega), this⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · intro i j hi hj hij
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix RP j (by omega)] <;> omega
  · intro i hi o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix RP i (by omega)]) <;> omega
  · intro i j hij hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix AP j (by omega)] <;> omega
  · intro i j hij hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix BP j (by omega)] <;> omega
  · intro j hj o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix AP j (by omega)]) <;> omega
  · intro j hj o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix BP j (by omega)]) <;> omega
  · intro o ho x hx
    have := addOffs_range o ho
    exact inFr_of_slot _ x o 80 (by omega) (by decide) hx

/-- **`SubSep` from a layout** (frame base `E - 80`, `96` frame bytes). -/
theorem subSep_of_layout {E RP AP BP : BitVec 64} {n : Nat} (h : ArgLayout 96 E RP AP BP n) :
    MpnSubBytesValue.SubSep (at' E (-80)) RP AP BP n := by
  have hr := h.rpFit
  have ha := h.apFit
  have hb := h.bpFit
  have hf := h.frFit
  have hE := E.isLt
  have hra := h.rpAp
  have hrb := h.rpBp
  have hrf := h.rpFr
  have haf := h.apFr
  have hbf := h.bpFr
  have hsl : ∀ o ∈ MpnSubBytesValue.subOffs,
      ((at' (at' E (-80)) o).toNat : Int) = E.toNat - 80 + o ∧ -16 ≤ o ∧ o ≤ 72 := by
    intro o ho
    have := subOffs_range o ho
    exact ⟨toNat_slot E 80 96 hf o (by omega) (by omega), this⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · intro i j hi hj hij
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix RP j (by omega)] <;> omega
  · intro i hi o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix RP i (by omega)]) <;> omega
  · intro i j hij hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix AP j (by omega)] <;> omega
  · intro i j hij hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix BP j (by omega)] <;> omega
  · intro j hj o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix AP j (by omega)]) <;> omega
  · intro j hj o ho
    obtain ⟨h1, h2, h3⟩ := hsl o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix BP j (by omega)]) <;> omega
  · intro o ho x hx
    have := subOffs_range o ho
    exact inFr_of_slot _ x o 96 (by omega) (by decide) hx

/-- **The linked `mpn_add_n_loop_owned`, from a layout.** As `mpn_add_n_bytes_correct`, with
    the separation given by the address layout `ArgLayout 80` of the entry stack pointer and
    the three arrays. -/
theorem mpn_add_n_correct :
    addObj = ElfObject.buildElfObjectMulti [{ name := "mpn_add_n_loop_owned", text := addText }]
    ∧ decodeLprog addText = some addDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      ArgLayout 80 (s0.regs "%rsp") (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
      ∃ s', Halts aMachine addDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnAddBytesValue.Keeps (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") n s0.mem
            s'.mem := by
  obtain ⟨h1, h2, h3⟩ := mpn_add_n_bytes_correct
  exact ⟨h1, h2, fun s0 n hc hL => h3 s0 n hc (addSep_of_layout hL)⟩

/-- **The linked `mpn_sub_n_loop_owned`, from a layout.** As `mpn_sub_n_bytes_correct`, with
    the separation given by `ArgLayout 96`. -/
theorem mpn_sub_n_correct :
    subObj = ElfObject.buildElfObjectMulti [{ name := "mpn_sub_n_loop_owned", text := subText }]
    ∧ decodeLprog subText = some subDec
    ∧ ∀ (s0 : AState) (n : Nat), s0.regs "%rcx" = BitVec.ofNat 64 n →
      ArgLayout 96 (s0.regs "%rsp") (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") n →
      ∃ s', Halts aMachine subDec 0 s0 s'
        ∧ bignumVal ((List.range n).map (wordsOf s'.mem (s0.regs "%rdi")))
            + bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rdx")))
          = bignumVal ((List.range n).map (wordsOf s0.mem (s0.regs "%rsi")))
            + (s'.regs "%rax").toNat * (2 ^ 64) ^ n
        ∧ (s'.regs "%rax").toNat ≤ 1
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ MpnSubBytesValue.Keeps (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") n s0.mem
            s'.mem := by
  obtain ⟨h1, h2, h3⟩ := mpn_sub_n_bytes_correct
  exact ⟨h1, h2, fun s0 n hc hL => h3 s0 n hc (subSep_of_layout hL)⟩

/-! ## 3. The compiled programs' denotations -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL ComL.denote)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLoopFrontEmit
  (ΓouterCarry addRtProgOpt subRtProgOpt addLprogFront subLprogFront)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubFrontDenote
  (seedVar nVar aVar bVar addRtProg_fold subRtProg_fold)

/-- The linked programs are the scalar-accumulator exports of the compiled loops. -/
theorem addLprogFront_eq : addLprogFront () = (addRtProgOpt ()).map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_add_n_loop_owned" (fun _ => none)
      MpnLoopFrontEmit.mpnSeedImm MpnLoopFrontEmit.gmpAbiArgs [64, 64, 64, 64]) := rfl

theorem subLprogFront_eq : subLprogFront () = (subRtProgOpt ()).map (fun c =>
    ComL.toLprogPhysAbiScalarAcc c "mpn_sub_n_loop_owned" (fun _ => none)
      MpnLoopFrontEmit.mpnSeedImm MpnLoopFrontEmit.gmpAbiArgs [64, 64, 64, 64]) := rfl

/-- The carry fold reads only the first `k` cells of the operands. -/
theorem addCarryFold_congr {NA NB NA' NB' : Nat} (ap : Fin NA → BitVec 64) (bp : Fin NB → BitVec 64)
    (ap' : Fin NA' → BitVec 64) (bp' : Fin NB' → BitVec 64) (c₀ : BitVec 64) (k : Nat)
    (ha : ∀ t, t < k → memGetDyn ap t = memGetDyn ap' t)
    (hb : ∀ t, t < k → memGetDyn bp t = memGetDyn bp' t) :
    addCarryFold ap bp k c₀ = addCarryFold ap' bp' k c₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [addCarryFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [addCarryFold] at ih
    rw [ih (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega)), ha k (by omega),
      hb k (by omega)]

/-- The borrow fold reads only the first `k` cells of the operands. -/
theorem subBorrowFold_congr {NA NB NA' NB' : Nat} (ap : Fin NA → BitVec 64)
    (bp : Fin NB → BitVec 64) (ap' : Fin NA' → BitVec 64) (bp' : Fin NB' → BitVec 64)
    (c₀ : BitVec 64) (k : Nat)
    (ha : ∀ t, t < k → memGetDyn ap t = memGetDyn ap' t)
    (hb : ∀ t, t < k → memGetDyn bp t = memGetDyn bp' t) :
    subBorrowFold ap bp k c₀ = subBorrowFold ap' bp' k c₀ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [subBorrowFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [subBorrowFold] at ih
    rw [ih (fun t ht => ha t (by omega)) (fun t ht => hb t (by omega)), ha k (by omega),
      hb k (by omega)]

/-- **The linked add returns the compiled program's denotation.** At every valuation `V` of
    the arguments of `addRtProgOpt` (the compiled loop whose scalar-accumulator export is the
    linked program, `addLprogFront_eq`) with the count `n`, the seed `0` (the export's seed) and
    the operand words the entry words of `ap` and `bp`, the denotation is `some c` and the
    machine halts with `%rax = c`, the output words the word model `addFold`. -/
theorem mpn_add_n_denote (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : MpnAddBytesValue.AddSep (at' (s0.regs "%rsp") (-64)) (s0.regs "%rdi") (s0.regs "%rsi")
      (s0.regs "%rdx") n)
    (V : Ctxt.Valuation ΓouterCarry) (hn : (nVar.lookup V).toNat = n) (hseed : (seedVar.lookup V).toNat = 0)
    (ha : ∀ t, t < n → memGetDyn (aVar.lookup V) t = wordsOf s0.mem (s0.regs "%rsi") t)
    (hb : ∀ t, t < n → memGetDyn (bVar.lookup V) t = wordsOf s0.mem (s0.regs "%rdx") t) :
    ∃ c s', (addRtProgOpt ()).map (fun c => ComL.denote c V) = some c
      ∧ Halts aMachine addDec 0 s0 s'
      ∧ s'.regs "%rax" = c
      ∧ (∀ i, i < n → wordsOf s'.mem (s0.regs "%rdi") i
          = memGetDyn (addFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).1 i)
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R) := by
  obtain ⟨s', hh, hw, hax, hsp, hcs, -⟩ := MpnAddBytesValue.add_halts s0 n hrcx hS
  refine ⟨_, s', addRtProg_fold V, hh, ?_, hw, hsp, hcs⟩
  rw [hax, addFold_snd, hn, BitVec.eq_of_toNat_eq (hseed.trans (BitVec.toNat_zero (w := 64)).symm)]
  refine addCarryFold_congr _ _ _ _ _ n ?_ ?_
  · intro t ht; rw [memGetDyn_arr _ _ t ht, ha t ht]
  · intro t ht; rw [memGetDyn_arr _ _ t ht, hb t ht]

/-- **The linked sub returns the compiled program's denotation** (`subRtProgOpt`, the borrow),
    as `mpn_add_n_denote`. -/
theorem mpn_sub_n_denote (s0 : AState) (n : Nat) (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 n)
    (hS : MpnSubBytesValue.SubSep (at' (s0.regs "%rsp") (-80)) (s0.regs "%rdi") (s0.regs "%rsi")
      (s0.regs "%rdx") n)
    (V : Ctxt.Valuation ΓouterCarry) (hn : (nVar.lookup V).toNat = n) (hseed : (seedVar.lookup V).toNat = 0)
    (ha : ∀ t, t < n → memGetDyn (aVar.lookup V) t = wordsOf s0.mem (s0.regs "%rsi") t)
    (hb : ∀ t, t < n → memGetDyn (bVar.lookup V) t = wordsOf s0.mem (s0.regs "%rdx") t) :
    ∃ c s', (subRtProgOpt ()).map (fun c => ComL.denote c V) = some c
      ∧ Halts aMachine subDec 0 s0 s'
      ∧ s'.regs "%rax" = c
      ∧ (∀ i, i < n → wordsOf s'.mem (s0.regs "%rdi") i
          = memGetDyn (subFold (arr n (wordsOf s0.mem (s0.regs "%rsi")))
              (arr n (wordsOf s0.mem (s0.regs "%rdx"))) n
              (arr n (wordsOf s0.mem (s0.regs "%rdi")), 0#64)).1 i)
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R) := by
  obtain ⟨s', hh, hw, hax, hsp, hcs, -⟩ := MpnSubBytesValue.sub_halts s0 n hrcx hS
  refine ⟨_, s', subRtProg_fold V, hh, ?_, hw, hsp, hcs⟩
  rw [hax, subFold_snd, hn, BitVec.eq_of_toNat_eq (hseed.trans (BitVec.toNat_zero (w := 64)).symm)]
  refine subBorrowFold_congr _ _ _ _ _ n ?_ ?_
  · intro t ht; rw [memGetDyn_arr _ _ t ht, ha t ht]
  · intro t ht; rw [memGetDyn_arr _ _ t ht, hb t ht]

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddSubBytesCorrect
