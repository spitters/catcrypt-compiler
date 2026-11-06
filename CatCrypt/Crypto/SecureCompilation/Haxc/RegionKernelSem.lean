/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionArrKeep

/-!
# The specification of a region-compiled callee from the semantics of the back half

`calleeSpec_of_regionBack` derives the specification of a region-compiled callee from the
keep check `keepCheckWB` on the decoded block. This module derives it from
`regionBack_correct` and two decided facts: a linear check `clobOkB` that every register
the block writes, other than the stack register, is in the clobber set, and a check
`layoutFootB` on the layout, the frame size and the store policy that the stack words and
the pointer regions of the layout lie in the footprint `KeepFoot`.

## Main results

* `blockWrites`: the registers a decoded block may write.
* `runL_regs_keep`: a leaky run of a block keeps every register outside `blockWrites` other
  than the stack register.
* `clobOkB`, `not_mem_blockWrites_of_clobOkB`: the check that the clobber set covers the
  written registers, and its soundness.
* `layoutFootB`, `keepFoot_of_frameWords`, `keepFoot_of_regionWords`: the check that the
  layout's stack words and regions lie in `KeepFoot`, and its soundness.
* `calleeSpec_of_regionBack_sem`: the leaky run of the decoded block of a result of
  `regionBack` meets `regionSig`, from `clobOkB` and `layoutFootB`.
* `layoutFootRoB`, `RegionCorrectRO`, `calleeSpec_of_regionCorrectRO`: the footprint check
  on the stack words and the regions of an out result only, the correctness clause of the
  back half with the read-only regions kept, and the specification of the callee from them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
  (decodeLprog RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
  (AState dsts runBlockA evalInstrA evalInstr_regs_of_not_mem_dsts)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (Loc wordsLocs regionWords frameWords)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Labels)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (NFCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)

/-! ## 1. The registers a block writes -/

/-- The registers a decoded instruction may write: the destinations of an operation, and
    the destinations of the straight-line effect of a `push` or `pop`. -/
def instrWrites : RInstr → List String
  | .op i => dsts i
  | ri => (ri.stackOps?.getD []).flatMap dsts

/-- The registers a decoded block may write. -/
def blockWrites (q : List RInstr) : List String := q.flatMap instrWrites

/-- A register an instruction of a block may write is among the registers the block may
    write. -/
theorem mem_blockWrites {q : List RInstr} {pc : Nat} {ri : RInstr} (hq : q[pc]? = some ri)
    {x : String} (hx : x ∈ instrWrites ri) : x ∈ blockWrites q :=
  List.mem_flatMap.2 ⟨ri, List.mem_of_getElem? hq, hx⟩

/-- A block of operations keeps every register outside the destinations of its
    operations. -/
theorem runBlockA_regs_of_not_mem (sa : AState) (blk : List (JInstr 64)) {x : String}
    (h : x ∉ blk.flatMap dsts) : (runBlockA sa blk).regs x = sa.regs x := by
  induction blk generalizing sa with
  | nil => rfl
  | cons i is ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    rw [Ascent.AddrMem.runBlockA_cons, ih _ h.2]
    exact evalInstr_regs_of_not_mem_dsts sa.view i x h.1

/-- **A run keeps the registers its block does not write.** A leaky run of the block `q`
    keeps every register outside `blockWrites q` other than the stack register. -/
theorem runL_regs_keep {r : DoitRegime} {ok : AState → JInstr 64 → Prop} {q : List RInstr}
    {pc : Nat} {s : AState} {t : List CTLeak} {s' : AState} (h : RunL r ok q pc s t s')
    {x : String} (hx : x ∉ blockWrites q) (hsp : x ≠ "%rsp") : s'.regs x = s.regs x := by
  induction h with
  | ret => rfl
  | @op pc sa i _ _ hq _ _ ih =>
    rw [ih]
    exact evalInstr_regs_of_not_mem_dsts sa.view i x fun hm => hx (mem_blockWrites hq hm)
  | jcc _ _ _ ih => exact ih
  | @stack pc sa ri ops _ _ hq hops _ _ ih =>
    rw [ih]
    refine runBlockA_regs_of_not_mem sa ops fun hm => hx (mem_blockWrites hq ?_)
    cases ri <;> simp_all [instrWrites, RInstr.stackOps?]
  | call _ _ _ _ _ ihc ihr =>
    rw [ihr, runBlockA_regs_of_not_mem _ _ (by simp [retOps, dsts, hsp]), ihc,
      runBlockA_regs_of_not_mem _ _ (by simp [callOps, dsts, hsp])]

/-! ## 2. The clobber check -/

/-- **The clobber check**: every register the block writes, other than the stack register,
    is in the clobber set. -/
def clobOkB (q : List RInstr) (clob : String → Bool) : Bool :=
  (blockWrites q).all fun x => x == "%rsp" || clob x

/-- A register outside the clobber set other than the stack register is written by no
    block that passes the clobber check. -/
theorem not_mem_blockWrites_of_clobOkB {q : List RInstr} {clob : String → Bool}
    (h : clobOkB q clob = true) {x : String} (hc : clob x = false) (hsp : x ≠ "%rsp") :
    x ∉ blockWrites q := by
  intro hm
  have := List.all_eq_true.1 h x hm
  simp_all

/-! ## 3. The layout inside the footprint -/

/-- **The footprint check of a layout**: the stack words of `σ` lie in the `F + K.red`
    bytes below the stack register (they are empty, or lie below the return word and above
    `-(F + K.red)`), and each pointer region of `σ` lies in an out window of `K` at its
    register. -/
def layoutFootB (σ : AbiLayout) (F : Nat) (K : StorePol) : Bool :=
  (decide (σ.frameHi < σ.frameLo)
      || (decide (σ.frameHi ≤ -8) && decide (-σ.frameLo ≤ ((F + K.red : Nat) : Int))))
    && σ.regions.all fun p => K.wins.any fun w =>
      w.1 == p.1 && decide (w.2.1 ≤ 0) && decide (8 * (p.2 : Int) ≤ w.2.2)

/-- The distance of a byte `x` of the word at `b + d` from `b + c`, for `c ≤ d`. -/
theorem toNat_sub_le {b x : BitVec 64} {c d : Int} (hcd : c ≤ d)
    (hx : (x - (b + BitVec.ofInt 64 d)).toNat < 8) :
    (x - (b + BitVec.ofInt 64 c)).toNat < (d - c).toNat + 8 := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, d = c + n := ⟨(d - c).toNat, by omega⟩
  subst hn
  have hd : BitVec.ofInt 64 (c + n) = BitVec.ofInt 64 c + BitVec.ofNat 64 n := by
    rw [BitVec.ofInt_add, BitVec.ofInt_natCast]
  rw [hd] at hx
  have e : x - (b + BitVec.ofInt 64 c)
      = (x - (b + (BitVec.ofInt 64 c + BitVec.ofNat 64 n))) + BitVec.ofNat 64 n := by
    grind
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 := Nat.mod_le ((x - (b + (BitVec.ofInt 64 c + BitVec.ofNat 64 n))).toNat
    + n % 2 ^ 64) (2 ^ 64)
  have h2 := Nat.mod_le n (2 ^ 64)
  omega

/-- A byte of a stack word of a layout that passes `layoutFootB` lies in the footprint. -/
theorem keepFoot_of_frameWords {σ : AbiLayout} {F : Nat} {K : StorePol}
    (hB : layoutFootB σ F K = true) {ρ : String → BitVec 64} {x : BitVec 64}
    (hx : Loc.mem x ∈ wordsLocs (frameWords (ρ "%rsp") σ.frameLo σ.frameHi)) :
    KeepFoot K F ρ x := by
  obtain ⟨_, ⟨o, hlo, hhi, rfl⟩, y, hy, he⟩ := Set.mem_iUnion₂.1 hx
  cases he
  change (x - (ρ "%rsp" + BitVec.ofInt 64 o)).toNat < 8 at hy
  simp only [layoutFootB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hB
  rcases hB.1 with hlt | ⟨h8, hG⟩
  · omega
  · left
    have := toNat_sub_le (c := -((F + K.red : Nat) : Int)) (by omega) hy
    unfold InFrame
    omega

/-- A byte of a pointer region of a layout that passes `layoutFootB` lies in the
    footprint. -/
theorem keepFoot_of_regionWords {σ : AbiLayout} {F : Nat} {K : StorePol}
    (hB : layoutFootB σ F K = true) {ρ : String → BitVec 64} {p : String × Nat}
    (hp : p ∈ σ.regions) {x : BitVec 64}
    (hx : Loc.mem x ∈ wordsLocs (regionWords (ρ p.1) p.2)) :
    KeepFoot K F ρ x := by
  obtain ⟨_, ⟨k, hk, rfl⟩, y, hy, he⟩ := Set.mem_iUnion₂.1 hx
  cases he
  simp only [layoutFootB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hB
  obtain ⟨w, hw, ⟨hw1, hlo⟩, hhi⟩ := hB.2 p hp
  right
  refine ⟨w, hw, ?_⟩
  have hofs : BitVec.ofNat 64 (8 * k) = BitVec.ofInt 64 ((8 * k : Nat) : Int) :=
    (BitVec.ofInt_natCast _ _).symm
  change (x - (ρ p.1 + BitVec.ofNat 64 (8 * k))).toNat < 8 at hy
  rw [hofs] at hy
  have := toNat_sub_le (c := w.2.1) (by omega) hy
  unfold InWin
  rw [hw1]
  omega

/-! ## 4. The specification of a region-compiled callee -/

/-- **The specification of a region-compiled callee from the back half.** Let
    `regionBack σ a p` give the bytes `bytes`, decoding to the block `q` that passes the
    clobber check `clobOkB` at `clob`, with the layout, the frame size `F` and the store
    policy `K` passing `layoutFootB`, on a program `p` that is constant time at the source
    events for labels `L` that agree with the public data of `σ`, at every fuel. Then the
    leaky run of `q` under `ctRegime` meets `regionSig σ p args res clob F K`. -/
theorem calleeSpec_of_regionBack_sem {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hc : clobOkB q clob = true)
    (hF : layoutFootB σ F K = true) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) := by
  have hrun : ∀ s, regionPre σ p s → ∃ s', Halts aMachine q 0 s s' ∧ regionPost σ p s s'
      ∧ s'.regs "%rsp" = s.regs "%rsp"
      ∧ ∀ x, ¬ KeepFoot K F s.regs x → s'.mem x = s.mem x := by
    rintro s ⟨hreg, V, fuel, v, hV, hv⟩
    obtain ⟨prog, s', hd, hh, hR, hsp, -, hmem, -⟩ := regionBack_correct h s V hV hreg fuel hv
    rw [hq, Option.some.injEq] at hd
    subst hd
    exact ⟨s', hh, ⟨V, fuel, v, hV, hv, hR⟩, hsp, fun x hx => hmem x
      (fun hm => hx (keepFoot_of_frameWords hF hm))
      (fun p' hp' hm => hx (keepFoot_of_regionWords hF hp' hm))⟩
  have hdet : ∀ s t s', regionPre σ p s → runOf ctRegime q s t s' →
      regionPost σ p s s' ∧ s'.regs "%rsp" = s.regs "%rsp"
        ∧ ∀ x, ¬ KeepFoot K F s.regs x → s'.mem x = s.mem x := by
    intro s t s' hs hX
    obtain ⟨s₀, hh, hp, hsp, hm⟩ := hrun s hs
    obtain ⟨t₀, ht₀⟩ := halts_runL ctRegime hh
    obtain ⟨_, rfl⟩ := runL_det ht₀ hX
    exact ⟨hp, hsp, hm⟩
  exact {
    halts := fun s hs => by
      obtain ⟨s', hh, -⟩ := hrun s hs
      obtain ⟨t, ht⟩ := halts_runL ctRegime hh
      exact ⟨t, s', ht⟩
    rsp := fun s t s' hs hX => (hdet s t s' hs hX).2.1
    keep := fun s t s' hs hX r hr => by
      by_cases hsp : r = "%rsp"
      · subst hsp; exact (hdet s t s' hs hX).2.1
      · exact runL_regs_keep hX (not_mem_blockWrites_of_clobOkB hc hr hsp) hsp
    frame := fun s t s' hs hX x hx => (hdet s t s' hs hX).2.2 x hx
    post := fun s t s' hs hX => (hdet s t s' hs hX).1
    ct := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ =>
      regionPre_bytes_ct h L hsrc hL hq s₁ s₂ t₁ t₂ ⟨hp, h₁, h₂⟩ ⟨s₁', hX₁⟩
        ⟨s₂', hX₂⟩ }

/-! ## 5. The read-only regions outside the footprint -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract (isResRegion)

/-- **The footprint check of a layout on its result regions**: `layoutFootB` with the region
    condition only at the regions of an out result (`isResRegion`); the read-only regions
    need not lie in the footprint. -/
def layoutFootRoB (σ : AbiLayout) (F : Nat) (K : StorePol) : Bool :=
  (decide (σ.frameHi < σ.frameLo)
      || (decide (σ.frameHi ≤ -8) && decide (-σ.frameLo ≤ ((F + K.red : Nat) : Int))))
    && (σ.regions.filter fun p => isResRegion σ p).all fun p => K.wins.any fun w =>
      w.1 == p.1 && decide (w.2.1 ≤ 0) && decide (8 * (p.2 : Int) ≤ w.2.2)

/-- A byte of a stack word of a layout that passes `layoutFootRoB` lies in the footprint. -/
theorem keepFoot_of_frameWords_ro {σ : AbiLayout} {F : Nat} {K : StorePol}
    (hB : layoutFootRoB σ F K = true) {ρ : String → BitVec 64} {x : BitVec 64}
    (hx : Loc.mem x ∈ wordsLocs (frameWords (ρ "%rsp") σ.frameLo σ.frameHi)) :
    KeepFoot K F ρ x := by
  obtain ⟨_, ⟨o, hlo, hhi, rfl⟩, y, hy, he⟩ := Set.mem_iUnion₂.1 hx
  cases he
  change (x - (ρ "%rsp" + BitVec.ofInt 64 o)).toNat < 8 at hy
  simp only [layoutFootRoB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hB
  rcases hB.1 with hlt | ⟨h8, hG⟩
  · omega
  · left
    have := toNat_sub_le (c := -((F + K.red : Nat) : Int)) (by omega) hy
    unfold InFrame
    omega

/-- A byte of a region of an out result of a layout that passes `layoutFootRoB` lies in the
    footprint. -/
theorem keepFoot_of_resRegionWords {σ : AbiLayout} {F : Nat} {K : StorePol}
    (hB : layoutFootRoB σ F K = true) {ρ : String → BitVec 64} {p : String × Nat}
    (hp : p ∈ σ.regions) (hres : isResRegion σ p = true) {x : BitVec 64}
    (hx : Loc.mem x ∈ wordsLocs (regionWords (ρ p.1) p.2)) :
    KeepFoot K F ρ x := by
  obtain ⟨_, ⟨k, hk, rfl⟩, y, hy, he⟩ := Set.mem_iUnion₂.1 hx
  cases he
  simp only [layoutFootRoB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hB
  obtain ⟨w, hw, ⟨hw1, hlo⟩, hhi⟩ := hB.2 p (List.mem_filter.2 ⟨hp, hres⟩)
  right
  refine ⟨w, hw, ?_⟩
  have hofs : BitVec.ofNat 64 (8 * k) = BitVec.ofInt 64 ((8 * k : Nat) : Int) :=
    (BitVec.ofInt_natCast _ _).symm
  change (x - (ρ p.1 + BitVec.ofNat 64 (8 * k))).toNat < 8 at hy
  rw [hofs] at hy
  have := toNat_sub_le (c := w.2.1) (by omega) hy
  unfold InWin
  rw [hw1]
  omega

/-- **The correctness clause of the back half with the read-only regions kept**: from every
    entry state `sa` satisfying `σ.Regions`, at every valuation `V` that `σ` reads off `sa`
    at which `p` denotes `v` at some fuel, the bytes decode to a program that halts from `sa`
    in a state `sa'` from which `σ` reads back the source value of the result, with the stack
    register of `sa`, and whose memory agrees with that of `sa` at every byte outside the
    stack words and outside the regions of an out result. -/
def RegionCorrectRO (σ : AbiLayout) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (bytes : List (BitVec 8)) : Prop :=
  ∀ (sa : AState) (V : Ctxt.Valuation Γ), AbiValOf σ sa V → σ.Regions sa →
    ∀ (fuel : Nat) (v : Ctxt.Valuation (d := jasminDialect) [t]), p.denote fuel V = some v →
      ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
        ∧ σ.ResultOf sa sa' (denVal t
            (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ ∀ x, Loc.mem x ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ q ∈ σ.regions, isResRegion σ q = true →
            Loc.mem x ∉ wordsLocs (regionWords (sa.regs q.1) q.2)) →
          sa'.mem x = sa.mem x

/-- **The specification of a region-compiled callee with read-only regions.**
    `calleeSpec_of_regionBack_sem` with the footprint check `layoutFootRoB` on the stack
    words and the regions of an out result, from the correctness clause `RegionCorrectRO` of
    the bytes in place of the memory clause of `regionBack_correct`. -/
theorem calleeSpec_of_regionCorrectRO {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hc : clobOkB q clob = true)
    (hF : layoutFootRoB σ F K = true) (hcor : RegionCorrectRO σ p bytes) (L : Labels Γ)
    (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p) (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) := by
  have hrun : ∀ s, regionPre σ p s → ∃ s', Halts aMachine q 0 s s' ∧ regionPost σ p s s'
      ∧ s'.regs "%rsp" = s.regs "%rsp"
      ∧ ∀ x, ¬ KeepFoot K F s.regs x → s'.mem x = s.mem x := by
    rintro s ⟨hreg, V, fuel, v, hV, hv⟩
    obtain ⟨prog, s', hd, hh, hR, hsp, hmem⟩ := hcor s V hV hreg fuel v hv
    rw [hq, Option.some.injEq] at hd
    subst hd
    exact ⟨s', hh, ⟨V, fuel, v, hV, hv, hR⟩, hsp, fun x hx => hmem x
      (fun hm => hx (keepFoot_of_frameWords_ro hF hm))
      (fun p' hp' hres hm => hx (keepFoot_of_resRegionWords hF hp' hres hm))⟩
  have hdet : ∀ s t s', regionPre σ p s → runOf ctRegime q s t s' →
      regionPost σ p s s' ∧ s'.regs "%rsp" = s.regs "%rsp"
        ∧ ∀ x, ¬ KeepFoot K F s.regs x → s'.mem x = s.mem x := by
    intro s t s' hs hX
    obtain ⟨s₀, hh, hp, hsp, hm⟩ := hrun s hs
    obtain ⟨t₀, ht₀⟩ := halts_runL ctRegime hh
    obtain ⟨_, rfl⟩ := runL_det ht₀ hX
    exact ⟨hp, hsp, hm⟩
  exact {
    halts := fun s hs => by
      obtain ⟨s', hh, -⟩ := hrun s hs
      obtain ⟨t, ht⟩ := halts_runL ctRegime hh
      exact ⟨t, s', ht⟩
    rsp := fun s t s' hs hX => (hdet s t s' hs hX).2.1
    keep := fun s t s' hs hX r hr => by
      by_cases hsp : r = "%rsp"
      · subst hsp; exact (hdet s t s' hs hX).2.1
      · exact runL_regs_keep hX (not_mem_blockWrites_of_clobOkB hc hr hsp) hsp
    frame := fun s t s' hs hX x hx => (hdet s t s' hs hX).2.2 x hx
    post := fun s t s' hs hX => (hdet s t s' hs hX).1
    ct := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp hX₁ hX₂ =>
      regionPre_bytes_ct h L hsrc hL hq s₁ s₂ t₁ t₂ ⟨hp, h₁, h₂⟩ ⟨s₁', hX₁⟩
        ⟨s₂', hX₂⟩ }

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB_sound)

/-- **The back half keeps the read-only regions**: a result of `regionBack` on a program
    that passes `regionROB` satisfies `RegionCorrectRO`. The virtual run behind the final
    state (`regionCo_bytes_of_regionExp_virt`) writes no read-only array, so the words of those
    regions are their entry words (`RegionArrKeep.keepRO_of_cells`). -/
theorem regionBack_correct_ro {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog} {bytes : List (BitVec 8)}
    (h : regionBack σ a p = some (P, bytes)) (hro : RegionArrKeep.regionROB σ a p = true) :
    RegionCorrectRO σ p bytes := by
  intro sa V hV hreg fuel v hv
  obtain ⟨hB, r0, r, b, cert, hr, rfl, hb, hco, -, -, hro'⟩ :=
    RegionArrKeep.regionBack_spec_ro h hro
  rw [← legalizeRegion_denote] at hv
  obtain ⟨prog, sa', hd, hh, hR, hsp, -, hkeep, ⟨k, s, hrun, hcells⟩, -⟩ :=
    regionCo_bytes_of_regionExp_virt (regionExportableB_sound hB) (regionExp_webs _ hr)
      hco sa V hV hreg fuel hv
  obtain ⟨-, hU⟩ := regionCoB_renImage hco
  have himg := hco
  rw [regionCoB_none] at himg
  simp only [Bool.and_eq_true] at himg
  obtain ⟨-, -, himg⟩ := himg
  exact ⟨prog, sa', by rw [X86Backend.LprogBytes.encodeLfundefBytesChecked_eq hb]; exact hd,
    hh, hR, hsp, RegionArrKeep.keepRO_of_cells himg hU sa hreg hrun hro' hd hh hcells hkeep⟩

/-- **The specification of a region-compiled callee**, from `regionBack`, the clobber check
    `clobOkB`, the read-only check `regionROB` and the footprint check `layoutFootRoB`; no
    syntactic keep check of the decoded block. -/
theorem calleeSpec_of_regionBack_ro {σ : AbiLayout} {a : AbiNames}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : regionBack σ a p = some (P, bytes)) {q : List RInstr}
    (hq : decodeLprog bytes = some q) {args : List String} {res : Option String}
    {clob : String → Bool} {F : Nat} {K : StorePol} (hc : clobOkB q clob = true)
    (hro : RegionArrKeep.regionROB σ a p = true) (hF : layoutFootRoB σ F K = true)
    (L : Labels Γ) (hsrc : ∀ fuel, NFCT (jLeakModel JLeakParams.owned) L fuel p)
    (hL : PubLabelsOK σ L) :
    CalleeSpec (runOf ctRegime q) (regionSig σ p args res clob F K) :=
  calleeSpec_of_regionCorrectRO h hq hc hF (regionBack_correct_ro h hro) L hsrc hL

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionKernelSem
