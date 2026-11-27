/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulFoldHand

@[expose] public section

set_option autoImplicit false

/-!
# The linked `mpn_mul_basecase_rt`: bytes, product, and the compiled program's denotation

`MpnMulBytesValue.mul_halts` runs the decoded linked object to its `ret` with
`MpnMulBasecaseFrontEmit.bcFold` of the entry words in `rp`. This module reads the product off
those words (`bcFold_val`, through its copy `MpnMulFoldHand.bcFold_val_hand` proved without
`bv_decide`) and ties them to the denotation of the front-compiled program
`MpnMulBasecaseFrontEmit.bcProgOpt` (`MpnMulBasecaseFrontDenote.bcRtProg_fold`,
`bcRtProg_val`): the words the machine leaves are the cells of the denotation at the
valuation that agrees with the entry state.

## Main results

* `bcFold_congr`: `bcFold` depends only on the cells it reads, at any array sizes.
* `mpn_mul_basecase_rt_bytes_correct`: the linked object is the ELF wrapping of `mulText`,
  which decodes to `mulDec`, and from every System V entry state with the words separated
  the machine halts with `value(rp[0..un+vn)) = value(up[0..un)) · value(vp[0..vn))` and
  `rp[un+vn] = 0` when the `un + vn + 1` words of `rp` are zero at the entry, `%rsp` and the
  callee-saved registers restored.
* `mulSep_of_layout`, `mpn_mul_basecase_rt_correct`: the separation from a numeric address
  layout (no wrap-around, disjoint intervals), and the end theorem stated with it.
* `mpn_mul_basecase_rt_denote`: at every valuation of the compiled program's arguments
  that agrees with the entry state, the machine's output words are the cells of the
  program's denotation (and `bcRtProg_val`'s product).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesCorrect

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulShipped
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulTrip (at' ix)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesValue
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn memGetDyn_memSetDyn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (bcStep bcLimb bcPartial bcRow bcFold bcPartial_succ bcFold_succ bcFold_val ZeroFrom
   bcProgOpt Gouter)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit (cells)
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel (bignumVal)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (ComL ComL.denote)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontEmit
  (bcFold_val_zero bcOuterCount bcInit NR)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBasecaseFrontDenote
  (upVar vpVar unVar bcRtProg_fold bcRtProg_val)

/-! ## 1. `bcFold` reads only the cells it is about -/

section Congr

variable {NR NU NV NR' NU' NV' : Nat}
  (up : Fin NU → BitVec 64) (up' : Fin NU' → BitVec 64)
  (vp : Fin NV → BitVec 64) (vp' : Fin NV' → BitVec 64) (un nc : Nat)

theorem bcStep_congr (hR : nc < NR) (hR' : nc < NR')
    (hup : ∀ t, t < un → memGetDyn up t = memGetDyn up' t) (jd : Nat)
    (hvp : memGetDyn vp jd = memGetDyn vp' jd) (t : Nat) (ht : jd + t < nc)
    (A : Fin NR → BitVec 64) (A' : Fin NR' → BitVec 64)
    (hA : ∀ i, i ≤ nc → memGetDyn A i = memGetDyn A' i) :
    ∀ i, i ≤ nc → memGetDyn (bcStep up vp un nc jd A t) i
      = memGetDyn (bcStep up' vp' un nc jd A' t) i := by
  intro i hi
  have hl : bcLimb up un t = bcLimb up' un t := by
    unfold bcLimb; split <;> simp_all
  simp only [bcStep, memGetDyn_memSetDyn _ hR (by omega : i < NR),
    memGetDyn_memSetDyn _ hR' (by omega : i < NR'),
    memGetDyn_memSetDyn _ (by omega : jd + t < NR) (by omega : i < NR),
    memGetDyn_memSetDyn _ (by omega : jd + t < NR') (by omega : i < NR'),
    hl, hvp, hA nc (Nat.le_refl _), hA (jd + t) (by omega), hA i hi]

theorem bcPartial_congr (hR : nc < NR) (hR' : nc < NR')
    (hup : ∀ t, t < un → memGetDyn up t = memGetDyn up' t) (jd : Nat)
    (hvp : memGetDyn vp jd = memGetDyn vp' jd) (hjd : jd + un < nc)
    (A : Fin NR → BitVec 64) (A' : Fin NR' → BitVec 64)
    (hA : ∀ i, i ≤ nc → memGetDyn A i = memGetDyn A' i) :
    ∀ T, T ≤ un + 1 → ∀ i, i ≤ nc → memGetDyn (bcPartial up vp un nc jd A T) i
      = memGetDyn (bcPartial up' vp' un nc jd A' T) i := by
  intro T
  induction T with
  | zero => intro _; simpa [bcPartial] using hA
  | succ T ih =>
    intro hT
    rw [bcPartial_succ, bcPartial_succ]
    exact bcStep_congr up up' vp vp' un nc hR hR' hup jd hvp T (by omega) _ _ (ih (by omega))

theorem bcFold_congr (hR : nc < NR) (hR' : nc < NR')
    (hup : ∀ t, t < un → memGetDyn up t = memGetDyn up' t) (n : Nat)
    (hvp : ∀ j, j < n → memGetDyn vp j = memGetDyn vp' j) (hn : n + un ≤ nc)
    (A : Fin NR → BitVec 64) (A' : Fin NR' → BitVec 64)
    (hA : ∀ i, i ≤ nc → memGetDyn A i = memGetDyn A' i) :
    ∀ i, i ≤ nc → memGetDyn (bcFold up vp un nc n A) i
      = memGetDyn (bcFold up' vp' un nc n A') i := by
  induction n with
  | zero => simpa [bcFold] using hA
  | succ n ih =>
    rw [bcFold_succ, bcFold_succ]
    exact bcPartial_congr up up' vp vp' un nc hR hR' hup n (hvp n (by omega)) (by omega) _ _
      (ih (fun j hj => hvp j (by omega)) (by omega)) (un + 1) (Nat.le_refl _)

end Congr

/-! ## 2. The end theorems -/

theorem cells_arr (n k : Nat) (f : Nat → BitVec 64) (hk : k ≤ n) :
    cells (arr n f) k = (List.range k).map f := by
  simp only [cells]
  refine List.map_congr_left (fun i hi => ?_)
  rw [List.mem_range] at hi
  exact memGetDyn_arr n f i (by omega)

/-- **The linked `mpn_mul_basecase_rt` computes the product.** The linked object
    `mpn_mul_basecase_rt_owned.o` (`mulObj`) is the ELF wrapping of `mulText`, whose bytes
    decode to `mulDec`; from every entry state with `rp`, `up`, `vp`, `un`, `vn` in `%rdi`,
    `%rsi`, `%rdx`, `%rcx`, `%r8`, the words separated (`MulSep`, the frame base `%rsp - 128`)
    and the `un + vn + 1` words of `rp` zero, the address machine halts on `mulDec` with
    `value(rp[0..un+vn)) = value(up[0..un)) · value(vp[0..vn))`, the scratch word
    `rp[un+vn]` zero, `%rsp` and the callee-saved registers as at the entry, and every byte
    outside the `152` frame bytes below the entry `%rsp` and the `un + vn + 1` words of `rp`
    as at the entry (`Keeps`). -/
theorem mpn_mul_basecase_rt_bytes_correct :
    mulObj = ElfObject.buildElfObjectMulti [{ name := "mpn_mul_basecase_rt", text := mulText }]
    ∧ decodeLprog mulText = some mulDec
    ∧ ∀ (s0 : AState) (un vn : Nat),
      s0.regs "%rcx" = BitVec.ofNat 64 un → s0.regs "%r8" = BitVec.ofNat 64 vn →
      MulSep (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx")
        un vn →
      (∀ i, i ≤ un + vn → wordsOf s0.mem (s0.regs "%rdi") i = 0) →
      ∃ s', Halts aMachine mulDec 0 s0 s'
        ∧ bignumVal ((List.range (un + vn)).map (wordsOf s'.mem (s0.regs "%rdi")))
            = bignumVal ((List.range un).map (wordsOf s0.mem (s0.regs "%rsi")))
              * bignumVal ((List.range vn).map (wordsOf s0.mem (s0.regs "%rdx")))
        ∧ wordsOf s'.mem (s0.regs "%rdi") (un + vn) = 0
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem s'.mem := by
  refine ⟨mulObj_eq, mulText_decode, ?_⟩
  intro s0 un vn hrcx hr8 hS hz
  obtain ⟨s', hh, hw, hsp, hcs, hk⟩ := mul_halts s0 un vn hrcx hr8 hS
  have hb := hS.bound
  set A := arr (un + vn + 1) (wordsOf s0.mem (s0.regs "%rdi")) with hA
  set U := arr un (wordsOf s0.mem (s0.regs "%rsi"))
  set W := arr vn (wordsOf s0.mem (s0.regs "%rdx"))
  have hzA : ∀ i, i < un + vn + 1 → memGetDyn A i = 0 := fun i hi => by
    rw [hA, memGetDyn_arr _ _ i hi]; exact hz i (by omega)
  have hval := MpnMulFoldHand.bcFold_val_zero_hand U W un vn A (by omega) hzA
  obtain ⟨-, hcy, -⟩ := MpnMulFoldHand.bcFold_val_hand U W un (un + vn) A (by omega) (hzA _ (by omega)) vn
    (by omega) (fun i _ hi => hzA i (by omega))
  refine ⟨s', hh, ?_, by rw [hw _ (Nat.le_refl _), hcy], hsp, hcs, hk⟩
  have hout : (List.range (un + vn)).map (wordsOf s'.mem (s0.regs "%rdi"))
      = cells (bcFold U W un (un + vn) vn A) (un + vn) := by
    simp only [cells]
    refine List.map_congr_left (fun i hi => ?_)
    rw [List.mem_range] at hi
    exact hw i (by omega)
  rw [hout, hval, cells_arr un un _ (Nat.le_refl _), cells_arr vn vn _ (Nat.le_refl _)]

/-- **The linked object computes the compiled program's denotation.** At every valuation `V`
    of the arguments of `MpnMulBasecaseFrontEmit.bcProgOpt` (the front-compiled nested loop
    whose physical-ABI export the encoder turned into the linked object) that agrees with the
    entry state on the counts and on the words the program reads, the machine halts with
    the cells of the denotation `out` in the `un + vn + 1` words of `rp`; `bcRtProg_val`
    gives the product of those cells. -/
theorem mpn_mul_basecase_rt_denote (s0 : AState) (un vn : Nat)
    (hrcx : s0.regs "%rcx" = BitVec.ofNat 64 un) (hr8 : s0.regs "%r8" = BitVec.ofNat 64 vn)
    (hS : MulSep (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (s0.regs "%rsi")
      (s0.regs "%rdx") un vn)
    (V : Ctxt.Valuation Gouter) (hun : (unVar.lookup V).toNat = un)
    (hvn : (bcOuterCount.lookup V).toNat = vn) (hscope : un + vn < NR)
    (hup : ∀ t, t < un → memGetDyn (upVar.lookup V) t = wordsOf s0.mem (s0.regs "%rsi") t)
    (hvp : ∀ j, j < vn → memGetDyn (vpVar.lookup V) j = wordsOf s0.mem (s0.regs "%rdx") j)
    (hrp : ∀ i, i ≤ un + vn → memGetDyn (bcInit.lookup V) i = wordsOf s0.mem (s0.regs "%rdi") i) :
    ∃ out s', bcProgOpt.map (fun c => ComL.denote c V) = some out
      ∧ Halts aMachine mulDec 0 s0 s'
      ∧ (∀ i, i ≤ un + vn → wordsOf s'.mem (s0.regs "%rdi") i = memGetDyn out i)
      ∧ s'.regs "%rsp" = s0.regs "%rsp"
      ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
      ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem s'.mem := by
  have hb := hS.bound
  have hden := bcRtProg_fold V (by rw [hun, hvn]; exact hscope)
  rw [hun, hvn] at hden
  obtain ⟨s', hh, hw, hsp, hcs, hk⟩ := mul_halts s0 un vn hrcx hr8 hS
  refine ⟨_, s', hden, hh, fun i hi => ?_, hsp, hcs, hk⟩
  rw [hw i hi]
  refine bcFold_congr _ _ _ _ un (un + vn) (by omega) hscope
    (fun t ht => by rw [memGetDyn_arr _ _ t ht, hup t ht]) vn
    (fun j hj => by rw [memGetDyn_arr _ _ j hj, hvp j hj]) (by omega) _ _
    (fun i hi => by rw [memGetDyn_arr _ _ i (by omega), hrp i hi]) i hi

/-! ## 3. Separation from a numeric layout -/

/-- Two words whose addresses are eight bytes apart or more, without wrapping, are disjoint. -/
theorem disj_of_toNat (a b : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64) (hb : b.toNat + 8 ≤ 2 ^ 64)
    (h : a.toNat + 8 ≤ b.toNat ∨ b.toNat + 8 ≤ a.toNat) : Disjoint8 a b := by
  simp only [Disjoint8, BitVec.toNat_sub, Nat.reducePow] at ha hb ⊢
  omega

theorem toNat_ix (B : BitVec 64) (i : Nat) (h : B.toNat + 8 * i < 2 ^ 64) :
    (ix B (BitVec.ofNat 64 i)).toNat = B.toNat + 8 * i := by
  have hi : i < 2 ^ 64 := by omega
  simp only [ix, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, BitVec.ofInt_natCast,
    BitVec.toNat_add]
  omega

theorem toNat_at' (p : BitVec 64) (o : Int) (h0 : 0 ≤ (p.toNat : Int) + o)
    (h1 : (p.toNat : Int) + o < 2 ^ 64) :
    ((at' p o).toNat : Int) = p.toNat + o := by
  have hp := p.isLt
  simp only [at', BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- **A layout of the arguments.** With the entry stack pointer `E`: the `un + vn + 1` words
    of `rp`, the `un` words of `up`, the `vn` words of `vp` and the `152` bytes below `E` (the
    frame and the red-zone words the function writes) lie in the address space without
    wrapping, and `rp`'s words are disjoint from the other three regions, `up`'s and `vp`'s
    from the frame. -/
structure MulLayout (E RP UP VP : BitVec 64) (un vn : Nat) : Prop where
  rpFit : RP.toNat + 8 * (un + vn + 1) < 2 ^ 64
  upFit : UP.toNat + 8 * un < 2 ^ 64
  vpFit : VP.toNat + 8 * vn < 2 ^ 64
  frFit : 152 ≤ E.toNat
  rpUp : RP.toNat + 8 * (un + vn + 1) ≤ UP.toNat ∨ UP.toNat + 8 * un ≤ RP.toNat
  rpVp : RP.toNat + 8 * (un + vn + 1) ≤ VP.toNat ∨ VP.toNat + 8 * vn ≤ RP.toNat
  rpFr : RP.toNat + 8 * (un + vn + 1) ≤ E.toNat - 152 ∨ E.toNat ≤ RP.toNat
  upFr : UP.toNat + 8 * un ≤ E.toNat - 152 ∨ E.toNat ≤ UP.toNat
  vpFr : VP.toNat + 8 * vn ≤ E.toNat - 152 ∨ E.toNat ≤ VP.toNat

theorem slotOffs_range : ∀ o ∈ slotOffs, -24 ≤ o ∧ o ≤ 120 := by decide

theorem toNat_slot (E : BitVec 64) (hE : 152 ≤ E.toNat) (o : Int) (ho : -24 ≤ o ∧ o ≤ 120) :
    ((at' (at' E (-128)) o).toNat : Int) = E.toNat - 128 + o := by
  have hE' := E.isLt
  have h1 : ((at' E (-128)).toNat : Int) = E.toNat + (-128) :=
    toNat_at' E (-128) (by omega) (by omega)
  rw [toNat_at' _ o (by omega) (by omega), h1]
  omega

/-- A byte of a frame word lies in the frame bytes. -/
theorem inFrB_of_slot (SP x : BitVec 64) (o : Int) (ho : -24 ≤ o ∧ o ≤ 120)
    (hx : InRange8 (at' SP o) x) : InFrB SP x := by
  unfold InFrB
  unfold InRange8 at hx
  have e : x - at' SP (-24) = (x - at' SP o) + BitVec.ofNat 64 (o + 24).toNat := by
    have hc : BitVec.ofInt 64 o = BitVec.ofInt 64 (-24) + BitVec.ofNat 64 (o + 24).toNat := by
      rw [← BitVec.ofInt_natCast, ← BitVec.ofInt_add]
      congr 1
      omega
    simp only [at', hc]
    abel
  rw [e, BitVec.toNat_add]
  generalize (x - at' SP o).toNat = d at hx ⊢
  have h24 : (BitVec.ofNat 64 (o + 24).toNat).toNat = (o + 24).toNat := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  rw [h24, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **`MulSep` from a layout.** -/
theorem mulSep_of_layout {E RP UP VP : BitVec 64} {un vn : Nat}
    (h : MulLayout E RP UP VP un vn) : MulSep (at' E (-128)) RP UP VP un vn := by
  have hr := h.rpFit
  have hu := h.upFit
  have hv := h.vpFit
  have hf := h.frFit
  have hE := E.isLt
  have hrp := h.rpUp
  have hrv := h.rpVp
  have hrf := h.rpFr
  have huf := h.upFr
  have hvf := h.vpFr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_⟩
  · intro i j hi hj hij
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix RP j (by omega)] <;> omega
  · intro i hi o ho
    have := toNat_slot E hf o (slotOffs_range o ho)
    have := slotOffs_range o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix RP i (by omega)]) <;> omega
  · intro i j hi hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix UP j (by omega)] <;> omega
  · intro i j hi hj
    apply disj_of_toNat <;> simp only [toNat_ix RP i (by omega), toNat_ix VP j (by omega)] <;> omega
  · intro j hj o ho
    have := toNat_slot E hf o (slotOffs_range o ho)
    have := slotOffs_range o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix UP j (by omega)]) <;> omega
  · intro j hj o ho
    have := toNat_slot E hf o (slotOffs_range o ho)
    have := slotOffs_range o ho
    apply disj_of_toNat <;> (try simp only [toNat_ix VP j (by omega)]) <;> omega
  · intro o ho x hx
    exact inFrB_of_slot _ x o (slotOffs_range o ho) hx

/-- **The linked `mpn_mul_basecase_rt`, from a layout.** As
    `mpn_mul_basecase_rt_bytes_correct`, with the separation given by the address layout
    `MulLayout` of the entry stack pointer and the three arrays. -/
theorem mpn_mul_basecase_rt_correct :
    mulObj = ElfObject.buildElfObjectMulti [{ name := "mpn_mul_basecase_rt", text := mulText }]
    ∧ decodeLprog mulText = some mulDec
    ∧ ∀ (s0 : AState) (un vn : Nat),
      s0.regs "%rcx" = BitVec.ofNat 64 un → s0.regs "%r8" = BitVec.ofNat 64 vn →
      MulLayout (s0.regs "%rsp") (s0.regs "%rdi") (s0.regs "%rsi") (s0.regs "%rdx") un vn →
      (∀ i, i ≤ un + vn → wordsOf s0.mem (s0.regs "%rdi") i = 0) →
      ∃ s', Halts aMachine mulDec 0 s0 s'
        ∧ bignumVal ((List.range (un + vn)).map (wordsOf s'.mem (s0.regs "%rdi")))
            = bignumVal ((List.range un).map (wordsOf s0.mem (s0.regs "%rsi")))
              * bignumVal ((List.range vn).map (wordsOf s0.mem (s0.regs "%rdx")))
        ∧ wordsOf s'.mem (s0.regs "%rdi") (un + vn) = 0
        ∧ s'.regs "%rsp" = s0.regs "%rsp"
        ∧ (∀ R ∈ calleeSavedL, s'.regs R = s0.regs R)
        ∧ Keeps (at' (s0.regs "%rsp") (-128)) (s0.regs "%rdi") (un + vn + 1) s0.mem s'.mem := by
  obtain ⟨h1, h2, h3⟩ := mpn_mul_basecase_rt_bytes_correct
  exact ⟨h1, h2, fun s0 un vn hc h8 hL hz => h3 s0 un vn hc h8 (mulSep_of_layout hL) hz⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMulBytesCorrect
