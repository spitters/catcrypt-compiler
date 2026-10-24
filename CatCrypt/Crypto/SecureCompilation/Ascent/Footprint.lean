/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemWord
public import CatCrypt.Crypto.SecureCompilation.Ascent.CallFrame
public import CatCrypt.Crypto.SecureCompilation.Ascent.Rng
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.MachineMem64

/-!
# Footprints of straight-line blocks over byte memory

A footprint layer for the address machine `AddrMem.runBlockA`: byte ranges, the ranges a
run reads and writes, and the frame rules that follow from them. A kernel has a few
buffers of fixed size and no allocation, so a memory assertion here is a predicate on the
whole byte memory together with the ranges it depends on; there are no resources or
permissions, and an output that aliases an input is stated as an equality of addresses.

## Ranges and assertions

The byte ranges `Rng`, their disjointness `Rng.Disj` and `Rng.Pairwise`, and the lemmas
`Rng.Disj.not_mem`, `Rng.disj_word_iff_memSep` and `Rng.pairwise_pair_word` are defined in
the module `Ascent.Rng`, which this module imports. `Supported S R` states
that the memory predicate `R` depends only on the bytes of the ranges `S`, and
`Sep L` is the conjunction of the predicates of `L` over pairwise disjoint ranges.

The points-to assertion of an `n`-limb little-endian buffer is `MachineMem64.ArrAt`; the
byte memories and the word accesses of `AddrMem` and `MachineMem64` coincide
(`read64_eq`, `write64_eq` in `Ascent/AddrMemWord.lean`), and `ArrAt m base n arr` is supported on the range
`⟨base, 8 * n⟩` (`arrAt_supported`).

## The footprint of a run

`reads blk sa` and `writes blk sa` are the word ranges the run of `blk` from `sa` reads
and writes, with every address evaluated at the registers the run holds at that
instruction. They are defined for every instruction `evalInstrA` interprets, the indexed
forms included. `cellFootprint bank blk` is the same footprint computed without a state:
the cells `(base register, offset)` of the canonical block `AddrMemDerived.canonD`, when
the block passes `disciplinedD`. `footCheckFrom` is the one-pass decision procedure that
checks the discipline and a predicate on every accessed cell.

## Main definitions

* `Supported`, `Sep`: memory predicates with their ranges, and their disjoint conjunction.
* `readAddr`, `reads`, `writes`, `Foot`, `footprint`: the footprint of a run.
* `LocalOn`, `CorresA`: a state predicate that depends only on registers, flags and the
  bytes of given ranges; the correspondence relation over `runBlockA`.
* `cellRng`, `CellFoot`, `cellFootprint`, `footCheckFrom`: the footprint in cells.

## Main results

* `separated_of_pairwise`: pairwise disjoint cell ranges give `AddrMem.Separated`.
* `arrAt_iff`, `arrAt_supported`: the points-to assertion of `MachineMem64` in terms of
  `AddrMem`, and its support.
* `writes_sound`: a byte outside every written range keeps its value.
* `runBlockA_local`: two states with equal registers and flags that agree on the read
  ranges run to equal registers and flags, to memories that agree wherever the entry
  memories agree and on every written range, and to equal footprints.
* `supported_frame`, `arrAt_frame`, `sep_frame`, `corresA_frame`, `frame_rule`: the frame
  rules over `runBlockA`.
* `runBlock_mem_frame`, `corresJ_frame`: the frame rule over the name-keyed `runBlock`.
* `footprint_canonFromD`, `footprint_cells`: the footprint of a run is the list of
  canonical cells at their addresses.
* `footprint_sound`, `footprint_sound_reads`: the frame and the locality of a run from a
  computed `cellFootprint`.
* `footCheckFrom_sound`, `footCheckFrom_append`: the one-pass check gives the discipline
  and the predicate on every cell of the canonical block, and splits at a concatenation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Footprint

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived

/-! ## Cell ranges -/

/-- The word range of the cell `k` at the entry pointers `P`. -/
def cellRng (bank : String → Option String) (P : String → BitVec 64) (k : String × Int) :
    Rng :=
  Rng.word (keyAddr bank P k)

/-- Pairwise disjoint cell ranges give `AddrMem.Separated`. -/
theorem separated_of_pairwise {bank : String → Option String} {P : String → BitVec 64}
    {K : List (String × Int)} (h : Rng.Pairwise (K.map (cellRng bank P))) :
    Separated bank P K :=
  fun _ hk _ hk' hne => h.disj_of_ne hk hk' hne

/-! ## Memory predicates and their ranges -/

/-- The memory predicate `R` depends only on the bytes of the ranges `S`. -/
def Supported (S : List Rng) (R : AMem → Prop) : Prop :=
  ∀ m m' : AMem, (∀ r ∈ S, ∀ x, x ∈ r → m' x = m x) → R m → R m'

/-- The conjunction of the predicates of `L`, over pairwise disjoint ranges. -/
def Sep (L : List (Rng × (AMem → Prop))) (m : AMem) : Prop :=
  Rng.Pairwise (L.map (·.1)) ∧ ∀ p ∈ L, p.2 m

/-- A disjoint conjunction of supported predicates holds in every memory that agrees on
    its ranges. -/
theorem Sep.of_agree {L : List (Rng × (AMem → Prop))} {m m' : AMem}
    (hL : ∀ p ∈ L, Supported [p.1] p.2) (hag : ∀ p ∈ L, ∀ x, x ∈ p.1 → m' x = m x)
    (h : Sep L m) : Sep L m' :=
  ⟨h.1, fun p hp => hL p hp m m'
    (fun r hr x hx => by
      rw [List.mem_singleton] at hr
      subst hr
      exact hag p hp x hx) (h.2 p hp)⟩

/-- A word whose eight bytes agree in two memories reads back equal. -/
theorem read64_congr_word (m m' : AMem) (a : BitVec 64)
    (h : ∀ x, x ∈ Rng.word a → m' x = m x) : read64 m' a = read64 m a :=
  CallFrame.read64_congr m m' a fun i hi => h _ (by
    rw [Rng.mem_word, InRange8, toNat_add_sub_self a i hi]
    exact hi)

/-- `MachineMem64.ArrAt` in terms of the word read of `AddrMem`. -/
theorem arrAt_iff (m : AMem) (base : BitVec 64) (n : Nat) (arr : Fin n → BitVec 64) :
    MachineMem64.ArrAt m base n arr ↔
      ∀ k : Fin n, read64 m (base + BitVec.ofNat 64 (8 * k.val)) = arr k := by
  simp only [MachineMem64.ArrAt, read64_eq]

/-- The points-to assertion of an `n`-limb buffer depends only on its `8 * n` bytes. -/
theorem arrAt_supported (base : BitVec 64) (n : Nat) (arr : Fin n → BitVec 64)
    (hn : 8 * n ≤ 2 ^ 64) :
    Supported [⟨base, 8 * n⟩] (fun m => MachineMem64.ArrAt m base n arr) := by
  intro m m' hag h
  rw [arrAt_iff] at h ⊢
  intro k
  rw [read64_congr_word m m' _ (fun x hx =>
    hag _ (List.mem_singleton.2 rfl) x (Rng.mem_buf_of_mem_limb hn k.isLt hx))]
  exact h k

/-! ## The footprint of a run -/

/-- The address an instruction reads, from the current registers. -/
def readAddr (sa : AState) : JInstr 64 → Option (BitVec 64)
  | .loadMemIdx _ b idx sc =>
      some (sa.regs b + BitVec.ofInt 64 ((sc * (sa.regs idx).toNat : Nat) : Int))
  | i => (readKey i).map fun k => sa.regs k.1 + BitVec.ofInt 64 k.2

/-- The word ranges the run of a block reads, in order. -/
def reads : List (JInstr 64) → AState → List Rng
  | [], _ => []
  | i :: is, sa =>
      match readAddr sa i with
      | some a => Rng.word a :: reads is (evalInstrA sa i)
      | none => reads is (evalInstrA sa i)

/-- The word ranges the run of a block writes, in order. -/
def writes : List (JInstr 64) → AState → List Rng
  | [], _ => []
  | i :: is, sa =>
      match writeAddr sa i with
      | some a => Rng.word a :: writes is (evalInstrA sa i)
      | none => writes is (evalInstrA sa i)

/-- The byte ranges a run reads and writes. -/
structure Foot where
  /-- The ranges read. -/
  reads : List Rng
  /-- The ranges written. -/
  writes : List Rng

/-- The footprint of the run of `blk` from `sa`. -/
def footprint (blk : List (JInstr 64)) (sa : AState) : Foot :=
  ⟨reads blk sa, writes blk sa⟩

theorem mem_reads_cons {r : Rng} {i : JInstr 64} {is : List (JInstr 64)} {sa : AState} :
    r ∈ reads (i :: is) sa ↔
      (∃ a, readAddr sa i = some a ∧ r = Rng.word a) ∨ r ∈ reads is (evalInstrA sa i) := by
  simp only [reads]
  cases readAddr sa i <;> simp

theorem mem_writes_cons {r : Rng} {i : JInstr 64} {is : List (JInstr 64)} {sa : AState} :
    r ∈ writes (i :: is) sa ↔
      (∃ a, writeAddr sa i = some a ∧ r = Rng.word a) ∨ r ∈ writes is (evalInstrA sa i) := by
  simp only [writes]
  cases writeAddr sa i <;> simp

theorem readAddr_eq (sa : AState) (i : JInstr 64) (hf : addrFormB i = true) :
    readAddr sa i = (readKey i).map fun k => sa.regs k.1 + BitVec.ofInt 64 k.2 := by
  cases i <;> simp only [addrFormB, Bool.false_eq_true] at hf <;> rfl

theorem readAddr_congr (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs) :
    readAddr sb i = readAddr sa i := by
  cases i <;> simp only [readAddr, hr]

theorem writeAddr_congr (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs) :
    writeAddr sb i = writeAddr sa i := by
  cases i <;> simp only [writeAddr, hr]

/-- One instruction leaves a byte outside its written range unchanged. -/
theorem evalInstrA_mem_of_not_mem (sa : AState) (i : JInstr 64) (x : BitVec 64)
    (h : ∀ a, writeAddr sa i = some a → x ∉ Rng.word a) :
    (evalInstrA sa i).mem x = sa.mem x := by
  simp only [evalInstrA]
  cases hw : writeAddr sa i with
  | none => rfl
  | some a => exact write64_of_not_inRange _ _ _ _ (h a hw)

/-- **Frame of a run.** A byte outside every range the run writes keeps its value. -/
theorem writes_sound (blk : List (JInstr 64)) :
    ∀ (sa : AState) (x : BitVec 64), (∀ r ∈ writes blk sa, x ∉ r) →
      (runBlockA sa blk).mem x = sa.mem x := by
  induction blk with
  | nil => intro _ _ _; rfl
  | cons i is ih =>
    intro sa x h
    rw [runBlockA_cons, ih (evalInstrA sa i) x (fun r hr => h r (mem_writes_cons.2 (Or.inr hr)))]
    exact evalInstrA_mem_of_not_mem sa i x
      (fun a ha => h _ (mem_writes_cons.2 (Or.inl ⟨a, ha, rfl⟩)))

/-- `evalInstr` on the view reads memory only at `readAddr`: two address states with equal
    registers and flags that agree on that word compute equal registers, flags and stored
    word. -/
theorem evalInstr_view_congr (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ a, readAddr sa i = some a → ∀ x, x ∈ Rng.word a → sb.mem x = sa.mem x) :
    (evalInstr sb.view i).regs = (evalInstr sa.view i).regs ∧
      (evalInstr sb.view i).flags = (evalInstr sa.view i).flags ∧
      writeVal sb.view i = writeVal sa.view i := by
  by_cases hform : addrFormB i = true
  · refine evalInstr_congr sb.view sa.view i hform hr.symm hf.symm (fun k hk => ?_)
    simp only [AState.view, ← hr]
    exact read64_congr_word _ _ _ (hm _ (by rw [readAddr_eq sa i hform, hk]; rfl))
  · obtain ⟨R, F, M⟩ := sa
    obtain ⟨R', F', M'⟩ := sb
    simp only at hr hf
    subst hr hf
    cases i <;> simp only [addrFormB, not_true_eq_false] at hform
    · rename_i d b idx sc
      have e := read64_congr_word M M' _ (hm _ rfl)
      refine ⟨?_, rfl, rfl⟩
      simp only [evalInstr, JState.setReg, JState.loadIdx, JState.load, JState.get,
        AState.view, x86_MOV, ofInt_natCast_mul, e]
    · rename_i b idx sc src
      refine ⟨rfl, rfl, ?_⟩
      cases src <;> rfl
    · exact ⟨rfl, rfl, rfl⟩

/-- One instruction from two states with equal registers and flags that agree on the read
    word: equal registers and flags, memories that agree wherever the entry memories agree,
    and on the written word. -/
theorem evalInstrA_agree (sa sb : AState) (i : JInstr 64) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ a, readAddr sa i = some a → ∀ x, x ∈ Rng.word a → sb.mem x = sa.mem x) :
    (evalInstrA sb i).regs = (evalInstrA sa i).regs ∧
      (evalInstrA sb i).flags = (evalInstrA sa i).flags ∧
      (∀ x, sb.mem x = sa.mem x → (evalInstrA sb i).mem x = (evalInstrA sa i).mem x) ∧
      (∀ a, writeAddr sa i = some a → ∀ x, x ∈ Rng.word a →
        (evalInstrA sb i).mem x = (evalInstrA sa i).mem x) := by
  obtain ⟨h1, h2, h3⟩ := evalInstr_view_congr sa sb i hr hf hm
  refine ⟨h1, h2, ?_, ?_⟩
  · intro x hx
    simp only [evalInstrA, writeAddr_congr sa sb i hr, h3]
    cases writeAddr sa i with
    | none => exact hx
    | some a =>
      simp only [write64]
      split
      · rfl
      · exact hx
  · intro a ha x hx
    simp only [evalInstrA, writeAddr_congr sa sb i hr, h3, ha, write64,
      ite_eq_left (Rng.mem_word.1 hx)]

/-- **Locality of a run.** Two states with equal registers and flags whose memories agree
    on every range the run from the first reads end with equal registers and flags; their
    final memories agree wherever the entry memories agree and on every written range; and
    the two runs have the same footprint. -/
theorem runBlockA_local (blk : List (JInstr 64)) :
    ∀ (sa sb : AState), sa.regs = sb.regs → sa.flags = sb.flags →
      (∀ r ∈ reads blk sa, ∀ x, x ∈ r → sb.mem x = sa.mem x) →
      (runBlockA sb blk).regs = (runBlockA sa blk).regs ∧
        (runBlockA sb blk).flags = (runBlockA sa blk).flags ∧
        (∀ x, sb.mem x = sa.mem x → (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) ∧
        (∀ r ∈ writes blk sa, ∀ x, x ∈ r →
          (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) ∧
        reads blk sb = reads blk sa ∧ writes blk sb = writes blk sa := by
  induction blk with
  | nil => intro _ _ hr hf _; exact ⟨hr.symm, hf.symm, fun _ h => h, by simp [writes], rfl, rfl⟩
  | cons i is ih =>
    intro sa sb hr hf hm
    obtain ⟨h1, h2, h3, h4⟩ := evalInstrA_agree sa sb i hr hf
      (fun a ha x hx => hm _ (mem_reads_cons.2 (Or.inl ⟨a, ha, rfl⟩)) x hx)
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := ih (evalInstrA sa i) (evalInstrA sb i) h1.symm h2.symm
      (fun r hr' x hx => h3 x (hm r (mem_reads_cons.2 (Or.inr hr')) x hx))
    refine ⟨k1, k2, fun x hx => k3 x (h3 x hx), ?_, ?_, ?_⟩
    · intro r hr' x hx
      rcases mem_writes_cons.1 hr' with ⟨a, ha, rfl⟩ | hr'
      · exact k3 x (h4 a ha x hx)
      · exact k4 r hr' x hx
    · simp only [reads, readAddr_congr sa sb i hr, k5]
    · simp only [writes, writeAddr_congr sa sb i hr, k6]

/-! ## Frame rules over `runBlockA` -/

/-- **Frame for a supported predicate.** A memory predicate whose ranges are disjoint from
    every range the run writes holds after the run. -/
theorem supported_frame {S : List Rng} {R : AMem → Prop} (hR : Supported S R)
    (blk : List (JInstr 64)) (sa : AState)
    (hd : ∀ w ∈ writes blk sa, ∀ r ∈ S, w.Disj r) (h : R sa.mem) :
    R (runBlockA sa blk).mem :=
  hR _ _ (fun r hr x hx =>
    writes_sound blk sa x (fun w hw hxw => (hd w hw r hr).not_mem hxw hx)) h

/-- **Frame for a buffer.** An `n`-limb buffer whose bytes are disjoint from every range
    the run writes holds the same limbs after the run. -/
theorem arrAt_frame (blk : List (JInstr 64)) (sa : AState) (base : BitVec 64) (n : Nat)
    (arr : Fin n → BitVec 64) (hn : 8 * n ≤ 2 ^ 64)
    (hd : ∀ w ∈ writes blk sa, w.Disj ⟨base, 8 * n⟩)
    (h : MachineMem64.ArrAt sa.mem base n arr) :
    MachineMem64.ArrAt (runBlockA sa blk).mem base n arr :=
  supported_frame (arrAt_supported base n arr hn) blk sa
    (fun w hw r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact hd w hw) h

/-- **Frame for a disjoint conjunction.** A conjunction of supported predicates whose
    ranges are disjoint from every range the run writes holds after the run. -/
theorem sep_frame {L : List (Rng × (AMem → Prop))} (hL : ∀ p ∈ L, Supported [p.1] p.2)
    (blk : List (JInstr 64)) (sa : AState)
    (hd : ∀ w ∈ writes blk sa, ∀ p ∈ L, w.Disj p.1) (h : Sep L sa.mem) :
    Sep L (runBlockA sa blk).mem :=
  Sep.of_agree hL (fun p hp x hx =>
    writes_sound blk sa x (fun w hw hxw => (hd w hw p hp).not_mem hxw hx)) h

/-- A state predicate that depends only on the registers, the flags and the bytes of the
    ranges `S`. -/
def LocalOn (S : List Rng) (Q : AState → Prop) : Prop :=
  ∀ sa sb : AState, sa.regs = sb.regs → sa.flags = sb.flags →
    (∀ r ∈ S, ∀ x, x ∈ r → sb.mem x = sa.mem x) → Q sa → Q sb

/-- **The frame rule.** Let `Q` hold after the run from `sa` and depend only on registers,
    flags and the ranges `S`. Let `sb` have the registers and flags of `sa` and agree with
    it on every range the run reads and on every byte of `S` the run does not write. Then
    `Q` holds after the run from `sb`, and that run changes no byte outside the written
    ranges. -/
theorem frame_rule (blk : List (JInstr 64)) (sa sb : AState) {S : List Rng}
    {Q : AState → Prop} (hQ : LocalOn S Q) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hreads : ∀ r ∈ reads blk sa, ∀ x, x ∈ r → sb.mem x = sa.mem x)
    (hS : ∀ r ∈ S, ∀ x, x ∈ r → sb.mem x = sa.mem x ∨ ∃ w ∈ writes blk sa, x ∈ w)
    (h : Q (runBlockA sa blk)) :
    Q (runBlockA sb blk) ∧
      ∀ x, (∀ w ∈ writes blk sa, x ∉ w) → (runBlockA sb blk).mem x = sb.mem x := by
  obtain ⟨k1, k2, k3, k4, -, k6⟩ := runBlockA_local blk sa sb hr hf hreads
  refine ⟨hQ _ _ k1.symm k2.symm (fun r hr' x hx => ?_) h, fun x hx => ?_⟩
  · rcases hS r hr' x hx with e | ⟨w, hw, hxw⟩
    · exact k3 x e
    · exact k4 w hw x hxw
  · exact writes_sound blk sb x (k6 ▸ hx)

/-- The correspondence relation over `runBlockA`: the state relation is transported along
    the run of the block and the abstract step. -/
def CorresA {α : Type} (SR : AState → α → Prop) (P : α → Prop) (fa : α → α)
    (c : List (JInstr 64)) : Prop :=
  ∀ sa a, SR sa a → P a → SR (runBlockA sa c) (fa a)

/-- **Frame for a correspondence.** A memory predicate supported on ranges disjoint from
    the written ranges of every related run is carried along the correspondence. -/
theorem corresA_frame {α : Type} {SR : AState → α → Prop} {P : α → Prop} {fa : α → α}
    {c : List (JInstr 64)} (h : CorresA SR P fa c) (S : AState → List Rng)
    (R : AMem → Prop)
    (hS : ∀ sa a, SR sa a → P a →
      Supported (S sa) R ∧ ∀ w ∈ writes c sa, ∀ r ∈ S sa, w.Disj r) :
    CorresA (fun sa a => SR sa a ∧ R sa.mem) P fa c := by
  intro sa a hsr hp
  obtain ⟨hsup, hd⟩ := hS sa a hsr.1 hp
  exact ⟨h sa a hsr.1 hp, supported_frame hsup c sa hd hsr.2⟩

/-! ## The name-keyed machine -/

/-- A cell that no instruction of a displacement block writes keeps its value under
    `runBlock`. -/
theorem runBlock_mem_frame (blk : List (JInstr 64)) :
    ∀ (s : JState 64), (∀ i ∈ blk, addrFormB i = true) → ∀ k : String × Int,
      k ∉ writeKeys blk → (runBlock s blk).mem k.1 k.2 = s.mem k.1 k.2 := by
  induction blk with
  | nil => intro _ _ _ _; rfl
  | cons i is ih =>
    intro s hform k hk
    rw [runBlock_cons, ih _ (fun j hj => hform j (List.mem_cons_of_mem _ hj)) k
      (fun h => hk (mem_writeKeys_cons.2 (Or.inr h))),
      evalInstr_mem s i (hform i List.mem_cons_self)]
    cases hw : writeKey i with
    | none => rfl
    | some c =>
      have hne : ¬ (k.1 = c.1 ∧ k.2 = c.2) := fun ⟨e1, e2⟩ =>
        hk (mem_writeKeys_cons.2 (Or.inl (by rw [hw, Prod.ext e1 e2])))
      simp only [ite_eq_right hne]

/-- **Frame for `CorresJ`.** A predicate on the name-keyed memory that depends only on
    cells a displacement block does not write is carried along the correspondence. -/
theorem corresJ_frame {α : Type} {SR : JState 64 → α → Prop} {P : α → Prop} {fa : α → α}
    {c : List (JInstr 64)} (h : CorresJ SR P fa c) (hform : ∀ i ∈ c, addrFormB i = true)
    (K : List (String × Int)) (hK : ∀ k ∈ K, k ∉ writeKeys c) (R : JMem 64 → Prop)
    (hR : ∀ m m' : JMem 64, (∀ k ∈ K, m' k.1 k.2 = m k.1 k.2) → R m → R m') :
    CorresJ (fun st a => SR st a ∧ R st.mem) P fa c := by
  intro st a hsr hp
  exact ⟨h st a hsr.1 hp,
    hR _ _ (fun k hk => runBlock_mem_frame c st hform k (hK k hk)) hsr.2⟩

/-! ## The footprint in cells -/

/-- Under the check and the register invariant, the addresses an instruction reads and
    writes are the addresses of the cells its canonical form reads and writes. -/
theorem addrs_canonStep (bank : String → Option String) (P : String → BitVec 64)
    (A : DState) (sa : AState) (i : JInstr 64) (hok : accessOKD bank A i = true)
    (hinv : RegInvD bank P A sa.regs) :
    readAddr sa i = (readKey (canonStep bank A i)).map (keyAddr bank P) ∧
      writeAddr sa i = (writeKey (canonStep bank A i)).map (keyAddr bank P) := by
  simp only [accessOKD, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.or_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hok
  obtain ⟨hls, hacc⟩ := hok
  unfold canonStep
  cases hmc : memCell bank A i with
  | none =>
    have ⟨hx, hd⟩ : idxOf i = none ∧ dispKey i = none := by
      rcases hacc with h | ⟨k, hk⟩
      · exact h
      · rw [hmc] at hk; cases hk
    have hf := addrFormB_of i hls hx
    simp only [readAddr_eq sa i hf, writeAddr_eq sa i hf, readKey_eq_none_of_dispKey i hd,
      writeKey_eq_none_of_dispKey i hd, Option.map_none, and_self]
  | some k =>
    simp only
    unfold memCell at hmc
    cases hix : idxOf i with
    | some bxs =>
      obtain ⟨b, x, sc⟩ := bxs
      rw [hix] at hmc
      simp only at hmc
      have ha := addr_of_cellIdx hinv hmc
      cases i <;> simp only [idxOf, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hix
      · obtain ⟨rfl, rfl, rfl⟩ := hix
        refine ⟨?_, rfl⟩
        simp only [readAddr, canonI, readKey, Option.map_some, ha]
      · obtain ⟨rfl, rfl, rfl⟩ := hix
        refine ⟨rfl, ?_⟩
        simp only [writeAddr, canonI, writeKey, Option.map_some, ha]
    | none =>
      rw [hix] at hmc
      simp only at hmc
      cases hdk : dispKey i with
      | none => rw [hdk] at hmc; cases hmc
      | some c =>
        rw [hdk] at hmc
        simp only [Option.bind_some] at hmc
        have ha := addr_of_cell hinv hmc
        have hf := addrFormB_of i hls hix
        rw [readAddr_eq sa i hf, writeAddr_eq sa i hf, readKey_canonI i k hf,
          writeKey_canonI i k hf]
        constructor
        · cases hrk : readKey i with
          | none => rfl
          | some c' =>
            have := dispKey_of_readKey hrk
            rw [hdk] at this
            cases this
            simp only [Option.map_some, ha]
        · cases hwk : writeKey i with
          | none => rfl
          | some c' =>
            have := dispKey_of_writeKey hwk
            rw [hdk] at this
            cases this
            simp only [Option.map_some, ha]

/-- **The footprint of a run is the canonical cells.** Under the check from an abstract
    state whose invariant holds, with the canonical written cells separated from one
    another and from the tracked cells, the run of `blk` reads and writes the word ranges
    of the cells the canonical block reads and writes, in order. -/
theorem footprint_canonFromD (bank : String → Option String) (P : String → BitVec 64) :
    ∀ (blk : List (JInstr 64)) (A : DState) (sa : AState),
      disciplinedFromD bank A blk = true → RegInvD bank P A sa.regs →
      CellInvD bank P A sa.mem →
      (∀ k ∈ writeKeys (canonFromD bank A blk), ∀ c ∈ A.cellKeys ++
        writeKeys (canonFromD bank A blk), c ≠ k →
        Disjoint8 (keyAddr bank P k) (keyAddr bank P c)) →
      reads blk sa = ((canonFromD bank A blk).filterMap readKey).map (cellRng bank P) ∧
        writes blk sa = (writeKeys (canonFromD bank A blk)).map (cellRng bank P) := by
  intro blk
  induction blk with
  | nil => intro _ _ _ _ _ _; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    intro A sa hd hinv hcell hsep
    simp only [disciplinedFromD, Bool.and_eq_true] at hd
    obtain ⟨hok, hd⟩ := hd
    simp only [canonFromD] at hsep
    have hWk : ∀ k, writeKey (canonStep bank A i) = some k →
        k ∈ writeKeys (canonStep bank A i :: canonFromD bank (stepD bank A i) is) :=
      fun k hk => mem_writeKeys_cons.2 (Or.inl hk)
    obtain ⟨hr, hw⟩ := addrs_canonStep bank P A sa i hok hinv
    obtain ⟨ihr, ihw⟩ := ih (stepD bank A i) (evalInstrA sa i) hd
      (regInvD_step bank P A sa i hok hinv hcell)
      (cellInvD_step bank P A sa i hok hinv hcell (fun k hk c hc hck =>
        hsep k (hWk k hk) c (List.mem_append_left _ hc) hck))
      (fun k hk c hc hck => hsep k (mem_writeKeys_cons.2 (Or.inr hk)) c (by
        rcases List.mem_append.1 hc with h | h
        · rcases cellKeys_stepD bank P A sa i hok hinv c h with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (mem_writeKeys_cons.2 (Or.inl h'))
        · exact List.mem_append_right _ (mem_writeKeys_cons.2 (Or.inr h))) hck)
    constructor
    · simp only [reads, hr, ihr, canonFromD, List.filterMap_cons]
      cases readKey (canonStep bank A i) <;> rfl
    · simp only [writes, hw, ihw, canonFromD, writeKeys, List.filterMap_cons]
      cases writeKey (canonStep bank A i) <;> rfl

/-- A footprint in cells: the cells read and the cells written, in order. -/
structure CellFoot where
  /-- The cells read. -/
  reads : List (String × Int)
  /-- The cells written. -/
  writes : List (String × Int)
  deriving DecidableEq

/-- The footprint at the entry pointers `P` of a footprint in cells. -/
def CellFoot.at (bank : String → Option String) (P : String → BitVec 64) (F : CellFoot) :
    Foot :=
  ⟨F.reads.map (cellRng bank P), F.writes.map (cellRng bank P)⟩

/-- The footprint of a block in cells, computed from the block alone: the cells of its
    canonical block, when it passes `disciplinedD`. -/
def cellFootprint (bank : String → Option String) (blk : List (JInstr 64)) :
    Option CellFoot :=
  if disciplinedD bank blk then
    some ⟨(canonD bank blk).filterMap readKey, writeKeys (canonD bank blk)⟩
  else none

theorem cellFootprint_eq_some {bank : String → Option String} {blk : List (JInstr 64)}
    {F : CellFoot} (h : cellFootprint bank blk = some F) :
    disciplinedD bank blk = true ∧ F.reads = (canonD bank blk).filterMap readKey ∧
      F.writes = writeKeys (canonD bank blk) := by
  unfold cellFootprint at h
  split at h
  · rename_i hd
    cases h
    exact ⟨hd, rfl, rfl⟩
  · cases h

/-- **The computed footprint is the footprint of every run.** When the written cells are
    separated at the entry registers, the run from `sa` has the footprint `F` at those
    registers. -/
theorem footprint_cells {bank : String → Option String} {blk : List (JInstr 64)}
    {F : CellFoot} (h : cellFootprint bank blk = some F) (sa : AState)
    (hsep : Separated bank sa.regs F.writes) :
    reads blk sa = (F.at bank sa.regs).reads ∧ writes blk sa = (F.at bank sa.regs).writes := by
  obtain ⟨hd, hr, hw⟩ := cellFootprint_eq_some h
  rw [hw] at hsep
  simp only [CellFoot.at, hr, hw]
  exact footprint_canonFromD bank sa.regs blk {} sa hd (regInvD_entry bank sa.regs)
    (cellInvD_entry bank sa.regs sa.mem)
    (fun k hk c hc hck => hsep k hk c (by simpa [DState.cellKeys, canonD] using hc)
      (Ne.symm hck))

/-- **Soundness of the computed footprint, writes.** When the written cells are separated
    at the entry registers, a byte outside the word range of every written cell keeps its
    value. -/
theorem footprint_sound {bank : String → Option String} {blk : List (JInstr 64)}
    {F : CellFoot} (h : cellFootprint bank blk = some F) (sa : AState)
    (hsep : Separated bank sa.regs F.writes) (x : BitVec 64)
    (hx : ∀ k ∈ F.writes, x ∉ cellRng bank sa.regs k) :
    (runBlockA sa blk).mem x = sa.mem x := by
  refine writes_sound blk sa x (fun r hr => ?_)
  rw [(footprint_cells h sa hsep).2] at hr
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr
  exact hx k hk

/-- **Soundness of the computed footprint, reads.** When the written cells are separated
    at the entry registers, a state with the registers and flags of `sa` that agrees with
    it on the word range of every read cell runs to the same registers and flags, and to a
    memory that agrees with the run from `sa` wherever the entry memories agree and on
    the word range of every written cell. -/
theorem footprint_sound_reads {bank : String → Option String} {blk : List (JInstr 64)}
    {F : CellFoot} (h : cellFootprint bank blk = some F) (sa sb : AState)
    (hsep : Separated bank sa.regs F.writes) (hr : sa.regs = sb.regs)
    (hf : sa.flags = sb.flags)
    (hm : ∀ k ∈ F.reads, ∀ x, x ∈ cellRng bank sa.regs k → sb.mem x = sa.mem x) :
    (runBlockA sb blk).regs = (runBlockA sa blk).regs ∧
      (runBlockA sb blk).flags = (runBlockA sa blk).flags ∧
      (∀ x, sb.mem x = sa.mem x → (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) ∧
      (∀ k ∈ F.writes, ∀ x, x ∈ cellRng bank sa.regs k →
        (runBlockA sb blk).mem x = (runBlockA sa blk).mem x) := by
  obtain ⟨er, ew⟩ := footprint_cells h sa hsep
  obtain ⟨k1, k2, k3, k4, -, -⟩ := runBlockA_local blk sa sb hr hf (fun r hr' x hx => by
    rw [er] at hr'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hr'
    exact hm k hk x hx)
  exact ⟨k1, k2, k3, fun k hk x hx =>
    k4 _ (by rw [ew]; exact List.mem_map.2 ⟨k, hk, rfl⟩) x hx⟩

/-! ## The one-pass check -/

/-- The discipline from the abstract state `A`, and `Pc` at the canonical cell of every
    memory operand, in one pass over the block. -/
def footCheckFrom (bank : String → Option String) (Pc : String × Int → Bool) :
    DState → List (JInstr 64) → Bool
  | _, [] => true
  | A, i :: is =>
      accessOKD bank A i && (memCell bank A i).all Pc &&
        footCheckFrom bank Pc (stepD bank A i) is

theorem footCheckFrom_append (bank : String → Option String) (Pc : String × Int → Bool)
    (A : DState) (xs ys : List (JInstr 64)) :
    footCheckFrom bank Pc A (xs ++ ys) =
      (footCheckFrom bank Pc A xs && footCheckFrom bank Pc (runD bank A xs) ys) := by
  induction xs generalizing A with
  | nil => simp [footCheckFrom, runD]
  | cons i is ih => simp only [List.cons_append, footCheckFrom, runD, ih, Bool.and_assoc]

theorem readKey_canonI_eq {i : JInstr 64} {k c : String × Int}
    (h : readKey (canonI i k) = some c) : c = k ∨ readKey i = some c := by
  cases i <;> simp_all [canonI, readKey]

theorem writeKey_canonI_eq {i : JInstr 64} {k c : String × Int}
    (h : writeKey (canonI i k) = some c) : c = k ∨ writeKey i = some c := by
  cases i <;> simp_all [canonI, writeKey]

/-- A cell the canonical form of an accepted instruction reads or writes is the canonical
    cell of its memory operand. -/
theorem memCell_of_canonStep {bank : String → Option String} {A : DState} {i : JInstr 64}
    (hok : accessOKD bank A i = true) {c : String × Int}
    (h : readKey (canonStep bank A i) = some c ∨ writeKey (canonStep bank A i) = some c) :
    memCell bank A i = some c := by
  simp only [accessOKD, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.or_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hok
  obtain ⟨hls, hacc⟩ := hok
  unfold canonStep at h
  cases hmc : memCell bank A i with
  | none =>
    rw [hmc] at h
    have hd : dispKey i = none := by
      rcases hacc with h' | ⟨k, hk⟩
      · exact h'.2
      · rw [hmc] at hk; cases hk
    simp only [readKey_eq_none_of_dispKey i hd, writeKey_eq_none_of_dispKey i hd,
      reduceCtorEq, or_self] at h
  | some k =>
    rw [hmc] at h
    simp only at h
    cases hix : idxOf i with
    | some bxs =>
      cases i <;> simp only [idxOf, reduceCtorEq] at hix <;>
        simp only [canonI, readKey, writeKey, reduceCtorEq, Option.some.injEq, or_false,
          false_or] at h <;> rw [← h]
    | none =>
      have hf := addrFormB_of i hls hix
      rw [readKey_canonI i k hf, writeKey_canonI i k hf] at h
      rcases h with h | h
      · cases hrk : readKey i with
        | none => rw [hrk] at h; cases h
        | some c' => rw [hrk] at h; cases h; rfl
      · cases hwk : writeKey i with
        | none => rw [hwk] at h; cases h
        | some c' => rw [hwk] at h; cases h; rfl

/-- **Soundness of the one-pass check.** It gives the discipline from `A`, and `Pc` at
    every cell the canonical block reads or writes. -/
theorem footCheckFrom_sound (bank : String → Option String) (Pc : String × Int → Bool) :
    ∀ (blk : List (JInstr 64)) (A : DState), footCheckFrom bank Pc A blk = true →
      disciplinedFromD bank A blk = true ∧
        ∀ k ∈ AddrMem.footprint (canonFromD bank A blk), Pc k = true := by
  intro blk
  induction blk with
  | nil =>
    intro _ _
    exact ⟨rfl, fun k hk => by simp [AddrMem.footprint, canonFromD, writeKeys] at hk⟩
  | cons i is ih =>
    intro A h
    simp only [footCheckFrom, Bool.and_eq_true] at h
    obtain ⟨⟨hok, hP⟩, hrest⟩ := h
    obtain ⟨hd, hK⟩ := ih _ hrest
    refine ⟨by simp only [disciplinedFromD, hok, hd, Bool.and_self], fun k hk => ?_⟩
    simp only [AddrMem.footprint, canonFromD, writeKeys, List.mem_append,
      List.mem_filterMap, List.mem_cons, exists_eq_or_imp] at hk
    have hhead : ∀ c, readKey (canonStep bank A i) = some c ∨
        writeKey (canonStep bank A i) = some c → Pc c = true := by
      intro c hc
      rw [memCell_of_canonStep hok hc] at hP
      exact hP
    rcases hk with (hk | ⟨j, hj, hjk⟩) | hk | ⟨j, hj, hjk⟩
    · exact hhead k (Or.inl hk)
    · exact hK k (List.mem_append_left _ (List.mem_filterMap.2 ⟨j, hj, hjk⟩))
    · exact hhead k (Or.inr hk)
    · exact hK k (List.mem_append_right _ (List.mem_filterMap.2 ⟨j, hj, hjk⟩))

/-- The one-pass check from the entry state gives a computed footprint whose cells all
    satisfy `Pc`. -/
theorem cellFootprint_of_footCheck {bank : String → Option String}
    {Pc : String × Int → Bool} {blk : List (JInstr 64)}
    (h : footCheckFrom bank Pc {} blk = true) :
    ∃ F, cellFootprint bank blk = some F ∧ (∀ k ∈ F.reads, Pc k = true) ∧
      ∀ k ∈ F.writes, Pc k = true := by
  obtain ⟨hd, hK⟩ := footCheckFrom_sound bank Pc blk {} h
  refine ⟨⟨(canonD bank blk).filterMap readKey, writeKeys (canonD bank blk)⟩, ?_, ?_, ?_⟩
  · simp only [cellFootprint, disciplinedD, hd, ite_true]
  · exact fun k hk => hK k (List.mem_append_left _ hk)
  · exact fun k hk => hK k (List.mem_append_right _ hk)

end CatCrypt.Crypto.SecureCompilation.Ascent.Footprint
