/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbCapstone
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul

/-!
# The multi-precision add/sub value capstone over the ascent `CorresJ` runBlock layer

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

`RunBlockCorres.lean` supplies the flag-carrying forward simulation `CorresJ`, the
per-limb carry leaves `corresJ_adc` / `corresJ_sbb`, and the base-`2^64`
recomposition `limbVal`. `EcMultiLimbMul.lean` adds the ADX leaf `corresJ_adcx`
and its chain `corresJ_adcxChain`; `EcMultiLimbCapstone.lean` adds the borrow
chain `corresJ_sbbChain` and the borrow-fold value identity `sbbLimbs_spec`.

This module joins the two legs — the *register* fold a machine chain refines, and
the *value* fold over base-`2^64` limb lists — and states the multi-precision
add/sub result over `runBlock`.

* `carryStep` / `carryAbs` / `carryLimbs` are the shape shared by the
  add-with-carry and subtract-with-borrow abstract transitions: `dst := f dst src
  cf` with carry-out `g dst src cf`, folded over a register-pair list resp. a limb
  list. `adcStep` and `sbbStep` are instances.
* `carryAbs_window` is the register↔value bridge: under name-disjointness, the
  destination register window after the fold reads back as the limb list the value
  fold produces, and the final carry bit is the value fold's carry-out.
* `adcLimbs_spec` is the base-`2^64` carry-chain identity for addition, the
  addition mirror of `sbbLimbs_spec`.
* `mpnAdd_runBlock` / `mpnSub_runBlock` are the chain capstones: running the
  `ADCX` (resp. `SBB`) chain under `runBlock` from a machine state with a cleared
  carry flag, the destination register window recomposes — with the final `CF` as
  the top limb — to `limbVal as + limbVal bs` (resp. the difference), where `as`
  and `bs` are the limb lists read out of the *initial* machine state.
* `mpnAddKernel_runBlock` / `mpnSubKernel_runBlock` are the same statements for
  the three-instruction `MOV / carry op / MOV` limb shape, where the sources and
  the result live in slots distinct from the accumulator.

Every result here is over `List (JInstr 64)` under `runBlock`, parametric in the
register and slot names. The specification side of every capstone mentions only
`limbVal`, the input limb lists, and integer `+`/`−`; no part of it names an
instruction, a flag, or a register.

## Main results

* `carryAbs_window` — the register fold a machine carry chain refines, read as
  the value fold over the limb windows.
* `adcLimbs_spec` — the base-2^64 identity for the addition carry chain.
* `mpnAdd_runBlock` / `mpnSub_runBlock` — an `ADCX` and an `SBB` block over any
  number of limbs against the limb-list sum and difference.
* `mpnAddKernel_runBlock` / `mpnSubKernel_runBlock` — the same over the
  three-instruction kernel limb, under slot disjointness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The shared carry-fold shape

A carry-threading limb transition is determined by two functions: the data word
`f dst src cf` written to the destination, and the carry-out bit `g dst src cf`.
`adcStep` (add-with-carry) and `sbbStep` (subtract-with-borrow) are the two
instances used here. -/

/-- One limb of a carry-threading chain over the abstract carry machine: the
    destination register gets `f dst src cf`, the carry bit gets `g dst src cf`,
    every other register is unchanged. -/
def carryStep (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (dst src : String) (a : ACarry) : ACarry :=
  { regs := fun r => if r = dst then f (a.regs dst) (a.regs src) a.cf else a.regs r
    cf := g (a.regs dst) (a.regs src) a.cf }

/-- The register-level carry fold: `carryStep` per `(dst, src)` pair, the first
    pair applied innermost (limb 0 first). -/
def carryAbs (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    List (String × String) → ACarry → ACarry
  | [], a => a
  | (d, s) :: ps, a => carryAbs f g ps (carryStep f g d s a)

/-- The value-level carry fold over little-endian base-`2^64` limb lists: limb 0
    is least significant, and the carry-out of limb `i` is the carry-in of limb
    `i+1`. Returns the result limbs together with the final carry-out. -/
def carryLimbs (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    List (BitVec 64) → List (BitVec 64) → Bool → List (BitVec 64) × Bool
  | [], _, b => ([], b)
  | _ :: _, [], b => ([], b)
  | x :: xs, y :: ys, b =>
      (f x y b :: (carryLimbs f g xs ys (g x y b)).1, (carryLimbs f g xs ys (g x y b)).2)

/-- A register outside the chain's destination list is unchanged by the fold. -/
theorem carryAbs_regs_of_not_mem (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    ∀ (ps : List (String × String)) (a : ACarry) (r : String),
      r ∉ ps.map Prod.fst → (carryAbs f g ps a).regs r = a.regs r := by
  intro ps
  induction ps with
  | nil => intro a r _; rfl
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    intro a r hr
    simp only [List.map_cons, List.mem_cons, not_or] at hr
    rw [carryAbs, ih _ r hr.2, carryStep]
    exact ite_eq_right hr.1

/-- **The register↔value bridge.** Under two name-disjointness conditions — the
    destination registers are pairwise distinct, and no destination register is a
    source register of any limb — the destination window after the register fold
    reads back as the limb list the value fold produces, and the fold's final
    carry bit is the value fold's carry-out. -/
theorem carryAbs_window (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    ∀ (ps : List (String × String)) (a : ACarry),
      (ps.map Prod.fst).Nodup → (∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2) →
      ps.map (fun p => (carryAbs f g ps a).regs p.1)
          = (carryLimbs f g (ps.map (fun p => a.regs p.1))
              (ps.map (fun p => a.regs p.2)) a.cf).1
        ∧ (carryAbs f g ps a).cf
          = (carryLimbs f g (ps.map (fun p => a.regs p.1))
              (ps.map (fun p => a.regs p.2)) a.cf).2 := by
  intro ps
  induction ps with
  | nil => intro a _ _; exact ⟨rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    intro a hnd hdisj
    rw [List.map_cons, List.nodup_cons] at hnd
    have hdnot : d ∉ ps.map Prod.fst := hnd.1
    have hnd' : (ps.map Prod.fst).Nodup := hnd.2
    have hdisj' : ∀ q ∈ ps, ∀ r ∈ ps, q.1 ≠ r.2 :=
      fun q hq r hr => hdisj q (List.mem_cons_of_mem _ hq) r (List.mem_cons_of_mem _ hr)
    set a1 : ACarry := carryStep f g d s a with ha1
    -- the head destination is not rewritten by the rest of the chain
    have hhead : (carryAbs f g ps a1).regs d = f (a.regs d) (a.regs s) a.cf := by
      rw [carryAbs_regs_of_not_mem f g ps a1 d hdnot, ha1, carryStep]
      exact ite_eq_left rfl
    -- the remaining limbs read the same source words in `a1` as in `a`
    have hsrc : ∀ q ∈ ps, a1.regs q.1 = a.regs q.1 := by
      intro q hq
      have : q.1 ≠ d := by
        intro h; exact hdnot (by rw [← h]; exact List.mem_map_of_mem hq)
      rw [ha1, carryStep]; exact ite_eq_right this
    have hsrc2 : ∀ q ∈ ps, a1.regs q.2 = a.regs q.2 := by
      intro q hq
      have : q.2 ≠ d :=
        Ne.symm (hdisj (d, s) (List.mem_cons_self ..) q (List.mem_cons_of_mem _ hq))
      rw [ha1, carryStep]; exact ite_eq_right this
    have hmap1 : ps.map (fun q => a1.regs q.1) = ps.map (fun q => a.regs q.1) :=
      List.map_congr_left hsrc
    have hmap2 : ps.map (fun q => a1.regs q.2) = ps.map (fun q => a.regs q.2) :=
      List.map_congr_left hsrc2
    have hcf1 : a1.cf = g (a.regs d) (a.regs s) a.cf := rfl
    obtain ⟨ih1, ih2⟩ := ih a1 hnd' hdisj'
    rw [hmap1, hmap2, hcf1] at ih1 ih2
    refine ⟨?_, ?_⟩
    · rw [carryAbs, List.map_cons, hhead, ih1, List.map_cons, List.map_cons, carryLimbs]
    · rw [carryAbs, ih2, List.map_cons, List.map_cons, carryLimbs]

/-! ## 2. The two instances

`adcStep` and `sbbStep` are `carryStep` at the add-with-carry and
subtract-with-borrow word/carry pairs. -/

/-- The add-with-carry data word `x + y + b` at width 64. -/
def addWord (x y : BitVec 64) (b : Bool) : BitVec 64 :=
  add_carry x y (if b then 1 else 0)

/-- The add-with-carry carry-out: the true sum `x + y + b` reached `2^64`. -/
def addCarryOut (x y : BitVec 64) (b : Bool) : Bool :=
  decide (2 ^ 64 ≤ x.toNat + y.toNat + (if b then 1 else 0))

/-- The subtract-with-borrow data word `x − y − b` at width 64. -/
def subWord (x y : BitVec 64) (b : Bool) : BitVec 64 :=
  sub_borrow x y (if b then 1 else 0)

/-- The limbwise add-with-carry over base-`2^64` limb lists, with the final
    carry-out returned alongside the result limbs. The addition mirror of
    `sbbLimbs`. -/
def adcLimbs : List (BitVec 64) → List (BitVec 64) → Bool → List (BitVec 64) × Bool :=
  carryLimbs addWord addCarryOut

/-- `adcStep` is `carryStep` at the add-with-carry word/carry pair. -/
theorem adcStep_eq (dst src : String) (a : ACarry) :
    adcStep dst src a = carryStep addWord addCarryOut dst src a := rfl

/-- `sbbStep` is `carryStep` at the subtract-with-borrow word/borrow pair. -/
theorem sbbStep_eq (dst src : String) (a : ACarry) :
    sbbStep dst src a = carryStep subWord sbbBorrow dst src a := by
  cases h : a.cf <;>
    simp only [sbbStep, carryStep, subWord, sbbBorrow, h, ACarry.mk.injEq, decide_eq_decide] <;>
    norm_num

/-- The `adcx` chain's abstract fold is the shared carry fold at the
    add-with-carry pair. -/
theorem adcxAbs_eq : ∀ (ps : List (String × String)) (a : ACarry),
    adcxAbs ps a = carryAbs addWord addCarryOut ps a := by
  intro ps
  induction ps with
  | nil => intro a; rfl
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    intro a; rw [adcxAbs, carryAbs, adcStep_eq, ih]

/-- The `sbb` chain's abstract fold is the shared carry fold at the
    subtract-with-borrow pair. -/
theorem sbbAbs_eq : ∀ (ps : List (String × String)) (a : ACarry),
    sbbAbs ps a = carryAbs subWord sbbBorrow ps a := by
  intro ps
  induction ps with
  | nil => intro a; rfl
  | cons p ps ih =>
    obtain ⟨d, s⟩ := p
    intro a; rw [sbbAbs, carryAbs, sbbStep_eq, ih]

/-- The borrow-chain value fold is the shared value fold at the
    subtract-with-borrow pair. -/
theorem sbbLimbs_eq : ∀ (xs ys : List (BitVec 64)) (b : Bool),
    sbbLimbs xs ys b = carryLimbs subWord sbbBorrow xs ys b := by
  intro xs
  induction xs with
  | nil => intro ys b; cases ys <;> rfl
  | cons x xs ih =>
    intro ys b
    cases ys with
    | nil => rfl
    | cons y ys =>
      rw [sbbLimbs, carryLimbs, ih ys (sbbBorrow x y b)]
      rfl

/-! ## 3. The base-`2^64` addition identity

The addition mirror of `sbbLimbs_spec`: the recomposed sum limbs, plus the final
carry-out weighted by `2^(64·n)`, equal the true multi-precision sum. -/

/-- **One-limb carry identity.** The output word of a single add-with-carry limb,
    plus its carry-out weighted by `2^64`, equals the true integer sum
    `x + y + b`. -/
theorem addWord_carry_id (x y : BitVec 64) (b : Bool) :
    ((addWord x y b).toNat : Int) + 2 ^ 64 * (if addCarryOut x y b then (1 : Int) else 0)
      = (x.toNat : Int) + y.toNat + (if b then 1 else 0) := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hy : y.toNat < 2 ^ 64 := y.isLt
  cases b <;>
    simp only [addWord, addCarryOut, add_carry, BitVec.toNat_ofNat, ite_true, ite_false,
      Bool.false_eq_true, decide_eq_true_eq] <;>
    split <;> push_cast <;> omega

/-- **The multi-limb add-with-carry specification.** For equal-length limb lists,
    the recomposed sum value plus the final carry-out weighted by `2^(64·n)`
    equals the true multi-precision sum `⟦xs⟧ + ⟦ys⟧ + b`. The addition mirror of
    `sbbLimbs_spec`. -/
theorem adcLimbs_spec : ∀ (xs ys : List (BitVec 64)) (b : Bool), xs.length = ys.length →
    (limbVal (adcLimbs xs ys b).1 : Int)
        + (2 : Int) ^ (64 * xs.length) * (if (adcLimbs xs ys b).2 then (1 : Int) else 0)
      = (limbVal xs : Int) + limbVal ys + (if b then 1 else 0) := by
  intro xs
  induction xs with
  | nil =>
    intro ys b h
    cases ys with
    | nil => cases b <;> simp [adcLimbs, carryLimbs, limbVal]
    | cons y ys' => simp at h
  | cons x xs' ih =>
    intro ys b h
    cases ys with
    | nil => simp at h
    | cons y ys' =>
      have h' : xs'.length = ys'.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using h
      have hih := ih ys' (addCarryOut x y b) h'
      have hstep : adcLimbs (x :: xs') (y :: ys') b
          = (addWord x y b :: (adcLimbs xs' ys' (addCarryOut x y b)).1,
             (adcLimbs xs' ys' (addCarryOut x y b)).2) := rfl
      rw [hstep]
      simp only [limbVal, List.length_cons]
      have hpow : (2 : Int) ^ (64 * (xs'.length + 1))
          = (2 : Int) ^ (64 * xs'.length) * 2 ^ 64 := by
        rw [Nat.mul_succ, pow_add]
      rw [hpow]
      push_cast
      have hid := addWord_carry_id x y b
      linear_combination (2 : Int) ^ 64 * hih + hid

/-! ## 4. The chain capstones over `runBlock`

The specification side names only `limbVal`, the two input limb windows read out
of the initial machine state, and integer `+`/`−`. -/

/-- The abstract carry state a machine state presents: the register file and the
    carry flag. -/
def ofJState (st : JState 64) : ACarry :=
  { regs := st.regs, cf := st.flagB (·.cf) }

/-- A machine state is related to the abstract state it presents. -/
theorem srcarry_ofJState (st : JState 64) : SRcarry st (ofJState st) :=
  ⟨fun _ => rfl, rfl⟩

/-- **The `mpn_add_n` capstone.** From a machine state whose carry flag is clear,
    running the emitted `ADCX` chain `adcxBlock ps` under `runBlock` leaves the
    destination register window holding the limbs of the multi-precision sum: the
    recomposed window, plus the resulting `CF` weighted by `2^(64·n)`, equals
    `⟦as⟧ + ⟦bs⟧`, where `as` and `bs` are the destination and source windows read
    out of the *initial* state. The side conditions are name disjointness — the
    destination registers are pairwise distinct and none of them is a source
    register. -/
theorem mpnAdd_runBlock (ps : List (String × String)) (st : JState 64)
    (hnd : (ps.map Prod.fst).Nodup) (hdisj : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (hcf : st.flagB (·.cf) = false) :
    (limbVal (ps.map (fun p => (runBlock st (adcxBlock ps)).regs p.1)) : Int)
        + (2 : Int) ^ (64 * ps.length)
          * (if (runBlock st (adcxBlock ps)).flagB (·.cf) then (1 : Int) else 0)
      = (limbVal (ps.map (fun p => st.regs p.1)) : Int)
        + limbVal (ps.map (fun p => st.regs p.2)) := by
  obtain ⟨hreg, hflag⟩ :=
    corresJ_adcxChain ps st (ofJState st) (srcarry_ofJState st) trivial
  have hlen : (ps.map (fun p => st.regs p.1)).length = ps.length := by simp
  have hlen2 : (ps.map (fun p => st.regs p.1)).length
      = (ps.map (fun p => st.regs p.2)).length := by simp
  have hcf0 : (ofJState st).cf = false := hcf
  obtain ⟨hw, hc⟩ := carryAbs_window addWord addCarryOut ps (ofJState st) hnd hdisj
  rw [adcxAbs_eq] at hreg hflag
  have hregs : ∀ r, (runBlock st (adcxBlock ps)).regs r
      = (carryAbs addWord addCarryOut ps (ofJState st)).regs r := hreg
  have hspec := adcLimbs_spec (ps.map (fun p => st.regs p.1))
    (ps.map (fun p => st.regs p.2)) (ofJState st).cf hlen2
  rw [hlen] at hspec
  have hwin : ps.map (fun p => (runBlock st (adcxBlock ps)).regs p.1)
      = (adcLimbs (ps.map (fun p => st.regs p.1)) (ps.map (fun p => st.regs p.2))
          (ofJState st).cf).1 := by
    rw [List.map_congr_left (fun p _ => hregs p.1)]
    exact hw
  have hcout : (runBlock st (adcxBlock ps)).flagB (·.cf)
      = (adcLimbs (ps.map (fun p => st.regs p.1)) (ps.map (fun p => st.regs p.2))
          (ofJState st).cf).2 := by
    rw [hflag]; exact hc
  rw [hwin, hcout, hspec, hcf0]
  simp

/-- **The `mpn_sub_n` capstone.** From a machine state whose carry flag is clear,
    running the emitted `SBB` chain `sbbBlock ps` under `runBlock` leaves the
    destination register window holding the limbs of the multi-precision
    difference: the recomposed window, minus the resulting `CF` weighted by
    `2^(64·n)`, equals `⟦as⟧ − ⟦bs⟧`, where `as` and `bs` are the destination and
    source windows read out of the *initial* state. Same name-disjointness side
    conditions as `mpnAdd_runBlock`. -/
theorem mpnSub_runBlock (ps : List (String × String)) (st : JState 64)
    (hnd : (ps.map Prod.fst).Nodup) (hdisj : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2)
    (hcf : st.flagB (·.cf) = false) :
    (limbVal (ps.map (fun p => (runBlock st (sbbBlock ps)).regs p.1)) : Int)
        - (2 : Int) ^ (64 * ps.length)
          * (if (runBlock st (sbbBlock ps)).flagB (·.cf) then (1 : Int) else 0)
      = (limbVal (ps.map (fun p => st.regs p.1)) : Int)
        - limbVal (ps.map (fun p => st.regs p.2)) := by
  obtain ⟨hreg, hflag⟩ :=
    corresJ_sbbChain ps st (ofJState st) (srcarry_ofJState st) trivial
  have hlen : (ps.map (fun p => st.regs p.1)).length = ps.length := by simp
  have hlen2 : (ps.map (fun p => st.regs p.1)).length
      = (ps.map (fun p => st.regs p.2)).length := by simp
  have hcf0 : (ofJState st).cf = false := hcf
  obtain ⟨hw, hc⟩ := carryAbs_window subWord sbbBorrow ps (ofJState st) hnd hdisj
  rw [sbbAbs_eq] at hreg hflag
  have hregs : ∀ r, (runBlock st (sbbBlock ps)).regs r
      = (carryAbs subWord sbbBorrow ps (ofJState st)).regs r := hreg
  have hspec := sbbLimbs_spec (ps.map (fun p => st.regs p.1))
    (ps.map (fun p => st.regs p.2)) (ofJState st).cf hlen2
  rw [hlen] at hspec
  rw [sbbLimbs_eq] at hspec
  have hwin : ps.map (fun p => (runBlock st (sbbBlock ps)).regs p.1)
      = (carryLimbs subWord sbbBorrow (ps.map (fun p => st.regs p.1))
          (ps.map (fun p => st.regs p.2)) (ofJState st).cf).1 := by
    rw [List.map_congr_left (fun p _ => hregs p.1)]
    exact hw
  have hcout : (runBlock st (sbbBlock ps)).flagB (·.cf)
      = (carryLimbs subWord sbbBorrow (ps.map (fun p => st.regs p.1))
          (ps.map (fun p => st.regs p.2)) (ofJState st).cf).2 := by
    rw [hflag]; exact hc
  rw [hwin, hcout, hspec, hcf0]
  simp

/-! ## 5. The kernel limb shape: load, fold through the carry chain, store

A GMP-class `mpn_add_n` / `mpn_sub_n` limb is not a bare two-address arithmetic
instruction: it is `MOV acc, a[i]; <carry op> acc, b[i]; MOV r[i], acc`, so the
sources and the result live in slots distinct from the accumulator. This section
lifts the chain results of §4 to that three-instruction limb shape. -/

/-- The register-move transition: the destination gets the source word, the carry
    bit is unchanged. -/
def movStep (dst src : String) (a : ACarry) : ACarry :=
  { regs := fun r => if r = dst then a.regs src else a.regs r, cf := a.cf }

/-- **The register-move leaf.** `mov dst src` under `runBlock` refines `movStep`
    through `SRcarry`: the destination register gets the source word and no flag
    is written. -/
theorem corresJ_mov (dst src : String) :
    CorresJ SRcarry (fun _ => True) (movStep dst src) [.mov dst (.reg src)] := by
  intro st a hSR _
  obtain ⟨hreg, hcf⟩ := hSR
  refine ⟨?_, ?_⟩
  · intro r
    simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.get,
      JOperand.eval, movStep, hreg]
  · simp only [runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JState.setReg, JState.flagB,
      movStep]
    exact hcf

/-- The register slots one limb of a multi-precision add/sub kernel touches. -/
structure LimbSlots where
  /-- The scratch accumulator the limb computes in. -/
  acc : String
  /-- The slot holding the first operand's limb. -/
  aSlot : String
  /-- The slot holding the second operand's limb. -/
  bSlot : String
  /-- The slot receiving the result limb. -/
  rSlot : String

/-- One kernel limb: load the first operand's limb into the accumulator, fold the
    second operand's limb in through the carry chain, store the result limb. -/
def kernelLimbBlock (op : String → JOperand → JInstr 64) (L : LimbSlots) :
    List (JInstr 64) :=
  [.mov L.acc (.reg L.aSlot), op L.acc (.reg L.bSlot), .mov L.rSlot (.reg L.acc)]

/-- The abstract transition of one kernel limb. -/
def kernelLimbAbs (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (L : LimbSlots) (a : ACarry) : ACarry :=
  movStep L.rSlot L.acc (carryStep f g L.acc L.bSlot (movStep L.acc L.aSlot a))

/-- The kernel block for a whole limb list, limb 0 first. -/
def kernelBlock (op : String → JOperand → JInstr 64) :
    List LimbSlots → List (JInstr 64)
  | [] => []
  | L :: Ls => kernelLimbBlock op L ++ kernelBlock op Ls

/-- The abstract kernel fold for a whole limb list, limb 0 applied innermost. -/
def kernelAbs (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) : List LimbSlots → ACarry → ACarry
  | [], a => a
  | L :: Ls, a => kernelAbs f g Ls (kernelLimbAbs f g L a)

/-- **The kernel-limb refinement.** Given a carry leaf for the fold instruction,
    the three-instruction limb refines the composed abstract limb transition. -/
theorem corresJ_kernelLimb (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (op : String → JOperand → JInstr 64)
    (hleaf : ∀ d s, CorresJ SRcarry (fun _ => True) (carryStep f g d s) [op d (.reg s)])
    (L : LimbSlots) :
    CorresJ SRcarry (fun _ => True) (kernelLimbAbs f g L) (kernelLimbBlock op L) := by
  have h1 := corresJ_append SRcarry (corresJ_mov L.acc L.aSlot) (hleaf L.acc L.bSlot)
    (fun _ _ => trivial)
  have h2 := corresJ_append SRcarry h1 (corresJ_mov L.rSlot L.acc) (fun _ _ => trivial)
  simpa [kernelLimbBlock, kernelLimbAbs] using! h2

/-- **The kernel-chain refinement.** The whole limb chain refines the composed
    abstract kernel fold, assembled from `corresJ_kernelLimb` through
    `corresJ_append`. -/
theorem corresJ_kernel (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (op : String → JOperand → JInstr 64)
    (hleaf : ∀ d s, CorresJ SRcarry (fun _ => True) (carryStep f g d s) [op d (.reg s)]) :
    ∀ Ls : List LimbSlots,
      CorresJ SRcarry (fun _ => True) (kernelAbs f g Ls) (kernelBlock op Ls) := by
  intro Ls
  induction Ls with
  | nil => exact corresJ_weaken SRcarry (corresJ_nil SRcarry) (fun _ _ => trivial)
  | cons L Ls ih =>
    show CorresJ SRcarry (fun _ => True) (fun a => kernelAbs f g Ls (kernelLimbAbs f g L a))
      (kernelLimbBlock op L ++ kernelBlock op Ls)
    exact corresJ_append SRcarry (corresJ_kernelLimb f g op hleaf L) ih (fun _ _ => trivial)

/-- The register a limb neither accumulates in nor stores to is unchanged by that
    limb. -/
theorem kernelLimbAbs_regs_of_untouched (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (L : LimbSlots) (a : ACarry) (r : String)
    (h1 : r ≠ L.rSlot) (h2 : r ≠ L.acc) :
    (kernelLimbAbs f g L a).regs r = a.regs r := by
  simp only [kernelLimbAbs, movStep, carryStep, ite_eq_right h1, ite_eq_right h2]

/-- A register outside every limb's written slots is unchanged by the whole
    chain. -/
theorem kernelAbs_regs_of_untouched (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    ∀ (Ls : List LimbSlots) (a : ACarry) (r : String),
      (∀ M ∈ Ls, r ≠ M.rSlot ∧ r ≠ M.acc) → (kernelAbs f g Ls a).regs r = a.regs r := by
  intro Ls
  induction Ls with
  | nil => intro a r _; rfl
  | cons L Ls ih =>
    intro a r h
    have hL := h L (List.mem_cons_self ..)
    rw [kernelAbs, ih _ r (fun M hM => h M (List.mem_cons_of_mem _ hM)),
      kernelLimbAbs_regs_of_untouched f g L a r hL.1 hL.2]

/-- **The one-limb effect.** When the second source slot is not the accumulator,
    a kernel limb writes the fold word `f a b cf` to both the accumulator and the
    result slot, sets the carry bit to `g a b cf`, and leaves every other register
    alone. -/
theorem kernelLimbAbs_apply (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) (L : LimbSlots) (a : ACarry)
    (hb : L.bSlot ≠ L.acc) :
    (∀ r, (kernelLimbAbs f g L a).regs r
        = if r = L.rSlot then f (a.regs L.aSlot) (a.regs L.bSlot) a.cf
          else if r = L.acc then f (a.regs L.aSlot) (a.regs L.bSlot) a.cf
          else a.regs r)
      ∧ (kernelLimbAbs f g L a).cf = g (a.regs L.aSlot) (a.regs L.bSlot) a.cf := by
  refine ⟨fun r => ?_, ?_⟩
  · by_cases h1 : r = L.rSlot
    · simp only [kernelLimbAbs, movStep, carryStep, ite_eq_left h1, ite_true, ite_eq_right hb]
    · by_cases h2 : r = L.acc
      · simp only [kernelLimbAbs, movStep, carryStep, ite_eq_right h1, ite_eq_left h2, ite_true,
          ite_eq_right hb]
      · simp only [kernelLimbAbs, movStep, carryStep, ite_eq_right h1, ite_eq_right h2]
  · simp only [kernelLimbAbs, movStep, carryStep, ite_true, ite_eq_right hb]

/-! ### Name disjointness for a kernel limb chain -/

/-- The name conditions under which a kernel limb chain computes limbwise: result
    slots are pairwise distinct, no result slot is an accumulator, and no source
    slot is written by any limb. -/
structure SlotsWF (Ls : List LimbSlots) : Prop where
  /-- Result slots are pairwise distinct. -/
  rNodup : (Ls.map LimbSlots.rSlot).Nodup
  /-- No result slot is an accumulator. -/
  rNotAcc : ∀ L ∈ Ls, ∀ M ∈ Ls, L.rSlot ≠ M.acc
  /-- No source slot is written by any limb. -/
  srcNotWritten : ∀ L ∈ Ls, ∀ M ∈ Ls,
    M.aSlot ≠ L.rSlot ∧ M.aSlot ≠ L.acc ∧ M.bSlot ≠ L.rSlot ∧ M.bSlot ≠ L.acc

/-- The conditions restrict to the tail of a chain. -/
theorem SlotsWF.tail {L : LimbSlots} {Ls : List LimbSlots} (h : SlotsWF (L :: Ls)) :
    SlotsWF Ls where
  rNodup := by
    have := h.rNodup
    rw [List.map_cons, List.nodup_cons] at this
    exact this.2
  rNotAcc := fun M hM N hN =>
    h.rNotAcc M (List.mem_cons_of_mem _ hM) N (List.mem_cons_of_mem _ hN)
  srcNotWritten := fun M hM N hN =>
    h.srcNotWritten M (List.mem_cons_of_mem _ hM) N (List.mem_cons_of_mem _ hN)

/-- **The kernel register↔value bridge.** Under `SlotsWF`, the result-slot window
    after the abstract kernel fold reads back as the limb list the value fold
    produces from the two source windows, and the fold's final carry bit is the
    value fold's carry-out. -/
theorem kernelAbs_window (f : BitVec 64 → BitVec 64 → Bool → BitVec 64)
    (g : BitVec 64 → BitVec 64 → Bool → Bool) :
    ∀ (Ls : List LimbSlots) (a : ACarry), SlotsWF Ls →
      Ls.map (fun L => (kernelAbs f g Ls a).regs L.rSlot)
          = (carryLimbs f g (Ls.map (fun L => a.regs L.aSlot))
              (Ls.map (fun L => a.regs L.bSlot)) a.cf).1
        ∧ (kernelAbs f g Ls a).cf
          = (carryLimbs f g (Ls.map (fun L => a.regs L.aSlot))
              (Ls.map (fun L => a.regs L.bSlot)) a.cf).2 := by
  intro Ls
  induction Ls with
  | nil => intro a _; exact ⟨rfl, rfl⟩
  | cons L Ls ih =>
    intro a hwf
    have hmemL : L ∈ L :: Ls := List.mem_cons_self ..
    have hb : L.bSlot ≠ L.acc := (hwf.srcNotWritten L hmemL L hmemL).2.2.2
    obtain ⟨hone, hcfone⟩ := kernelLimbAbs_apply f g L a hb
    set a1 : ACarry := kernelLimbAbs f g L a with ha1
    set w : BitVec 64 := f (a.regs L.aSlot) (a.regs L.bSlot) a.cf with hw
    -- the head result slot survives the rest of the chain
    have hrn : (Ls.map LimbSlots.rSlot).Nodup ∧ L.rSlot ∉ Ls.map LimbSlots.rSlot := by
      have := hwf.rNodup
      rw [List.map_cons, List.nodup_cons] at this
      exact ⟨this.2, this.1⟩
    have huntouched : ∀ M ∈ Ls, L.rSlot ≠ M.rSlot ∧ L.rSlot ≠ M.acc := by
      intro M hM
      refine ⟨?_, hwf.rNotAcc L hmemL M (List.mem_cons_of_mem _ hM)⟩
      intro hEq
      exact hrn.2 (by rw [hEq]; exact List.mem_map_of_mem hM)
    have hhead : (kernelAbs f g Ls a1).regs L.rSlot = w := by
      rw [kernelAbs_regs_of_untouched f g Ls a1 L.rSlot huntouched, ha1, hone L.rSlot]
      exact ite_eq_left rfl
    -- the remaining limbs read the same source words after the head limb
    have hsrcA : ∀ M ∈ Ls, a1.regs M.aSlot = a.regs M.aSlot := by
      intro M hM
      obtain ⟨h1, h2, _, _⟩ := hwf.srcNotWritten L hmemL M (List.mem_cons_of_mem _ hM)
      rw [ha1, hone M.aSlot, ite_eq_right h1, ite_eq_right h2]
    have hsrcB : ∀ M ∈ Ls, a1.regs M.bSlot = a.regs M.bSlot := by
      intro M hM
      obtain ⟨_, _, h3, h4⟩ := hwf.srcNotWritten L hmemL M (List.mem_cons_of_mem _ hM)
      rw [ha1, hone M.bSlot, ite_eq_right h3, ite_eq_right h4]
    have hmapA : Ls.map (fun M => a1.regs M.aSlot) = Ls.map (fun M => a.regs M.aSlot) :=
      List.map_congr_left hsrcA
    have hmapB : Ls.map (fun M => a1.regs M.bSlot) = Ls.map (fun M => a.regs M.bSlot) :=
      List.map_congr_left hsrcB
    obtain ⟨ih1, ih2⟩ := ih a1 hwf.tail
    rw [hmapA, hmapB, hcfone] at ih1 ih2
    refine ⟨?_, ?_⟩
    · rw [kernelAbs, List.map_cons, hhead, ih1, List.map_cons, List.map_cons, carryLimbs]
    · rw [kernelAbs, ih2, List.map_cons, List.map_cons, carryLimbs]

/-! ### The two carry leaves in `carryStep` form -/

/-- `corresJ_adcx` restated at the shared carry-fold shape. -/
theorem corresJ_adcx_carryStep (d s : String) :
    CorresJ SRcarry (fun _ => True) (carryStep addWord addCarryOut d s)
      [.adcx d (.reg s)] := by
  have h := corresJ_adcx d s
  rwa [show adcStep d s = carryStep addWord addCarryOut d s from funext (adcStep_eq d s)] at h

/-- `corresJ_sbb` restated at the shared carry-fold shape. -/
theorem corresJ_sbb_carryStep (d s : String) :
    CorresJ SRcarry (fun _ => True) (carryStep subWord sbbBorrow d s)
      [.sbb d (.reg s)] := by
  have h := corresJ_sbb d s
  rwa [show sbbStep d s = carryStep subWord sbbBorrow d s from funext (sbbStep_eq d s)] at h

/-! ## 6. The kernel capstones over `runBlock` -/

/-- **The `mpn_add_n` kernel capstone.** From a machine state whose carry flag is
    clear, running the `MOV / ADCX / MOV` limb chain `kernelBlock .adcx Ls` under
    `runBlock` leaves the result-slot window holding the limbs of the
    multi-precision sum: the recomposed window, plus the resulting `CF` weighted
    by `2^(64·n)`, equals `⟦as⟧ + ⟦bs⟧`, where `as` and `bs` are the two source
    windows read out of the *initial* state. -/
theorem mpnAddKernel_runBlock (Ls : List LimbSlots) (st : JState 64)
    (hwf : SlotsWF Ls) (hcf : st.flagB (·.cf) = false) :
    (limbVal (Ls.map (fun L => (runBlock st (kernelBlock .adcx Ls)).regs L.rSlot)) : Int)
        + (2 : Int) ^ (64 * Ls.length)
          * (if (runBlock st (kernelBlock .adcx Ls)).flagB (·.cf) then (1 : Int) else 0)
      = (limbVal (Ls.map (fun L => st.regs L.aSlot)) : Int)
        + limbVal (Ls.map (fun L => st.regs L.bSlot)) := by
  obtain ⟨hreg, hflag⟩ :=
    corresJ_kernel addWord addCarryOut _ corresJ_adcx_carryStep Ls st (ofJState st)
      (srcarry_ofJState st) trivial
  obtain ⟨hw, hc⟩ := kernelAbs_window addWord addCarryOut Ls (ofJState st) hwf
  have hlen : (Ls.map (fun L => st.regs L.aSlot)).length = Ls.length := by simp
  have hlen2 : (Ls.map (fun L => st.regs L.aSlot)).length
      = (Ls.map (fun L => st.regs L.bSlot)).length := by simp
  have hspec := adcLimbs_spec (Ls.map (fun L => st.regs L.aSlot))
    (Ls.map (fun L => st.regs L.bSlot)) (ofJState st).cf hlen2
  rw [hlen] at hspec
  have hwin : Ls.map (fun L => (runBlock st (kernelBlock .adcx Ls)).regs L.rSlot)
      = (adcLimbs (Ls.map (fun L => st.regs L.aSlot)) (Ls.map (fun L => st.regs L.bSlot))
          (ofJState st).cf).1 := by
    rw [List.map_congr_left (fun L _ => hreg L.rSlot)]
    exact hw
  have hcout : (runBlock st (kernelBlock .adcx Ls)).flagB (·.cf)
      = (adcLimbs (Ls.map (fun L => st.regs L.aSlot)) (Ls.map (fun L => st.regs L.bSlot))
          (ofJState st).cf).2 := by
    rw [hflag]; exact hc
  have hcf0 : (ofJState st).cf = false := hcf
  rw [hwin, hcout, hspec, hcf0]
  simp

/-- **The `mpn_sub_n` kernel capstone.** From a machine state whose carry flag is
    clear, running the `MOV / SBB / MOV` limb chain `kernelBlock .sbb Ls` under
    `runBlock` leaves the result-slot window holding the limbs of the
    multi-precision difference: the recomposed window, minus the resulting `CF`
    weighted by `2^(64·n)`, equals `⟦as⟧ − ⟦bs⟧`. -/
theorem mpnSubKernel_runBlock (Ls : List LimbSlots) (st : JState 64)
    (hwf : SlotsWF Ls) (hcf : st.flagB (·.cf) = false) :
    (limbVal (Ls.map (fun L => (runBlock st (kernelBlock .sbb Ls)).regs L.rSlot)) : Int)
        - (2 : Int) ^ (64 * Ls.length)
          * (if (runBlock st (kernelBlock .sbb Ls)).flagB (·.cf) then (1 : Int) else 0)
      = (limbVal (Ls.map (fun L => st.regs L.aSlot)) : Int)
        - limbVal (Ls.map (fun L => st.regs L.bSlot)) := by
  obtain ⟨hreg, hflag⟩ :=
    corresJ_kernel subWord sbbBorrow _ corresJ_sbb_carryStep Ls st (ofJState st)
      (srcarry_ofJState st) trivial
  obtain ⟨hw, hc⟩ := kernelAbs_window subWord sbbBorrow Ls (ofJState st) hwf
  have hlen : (Ls.map (fun L => st.regs L.aSlot)).length = Ls.length := by simp
  have hlen2 : (Ls.map (fun L => st.regs L.aSlot)).length
      = (Ls.map (fun L => st.regs L.bSlot)).length := by simp
  have hspec := sbbLimbs_spec (Ls.map (fun L => st.regs L.aSlot))
    (Ls.map (fun L => st.regs L.bSlot)) (ofJState st).cf hlen2
  rw [hlen] at hspec
  rw [sbbLimbs_eq] at hspec
  have hwin : Ls.map (fun L => (runBlock st (kernelBlock .sbb Ls)).regs L.rSlot)
      = (carryLimbs subWord sbbBorrow (Ls.map (fun L => st.regs L.aSlot))
          (Ls.map (fun L => st.regs L.bSlot)) (ofJState st).cf).1 := by
    rw [List.map_congr_left (fun L _ => hreg L.rSlot)]
    exact hw
  have hcout : (runBlock st (kernelBlock .sbb Ls)).flagB (·.cf)
      = (carryLimbs subWord sbbBorrow (Ls.map (fun L => st.regs L.aSlot))
          (Ls.map (fun L => st.regs L.bSlot)) (ofJState st).cf).2 := by
    rw [hflag]; exact hc
  have hcf0 : (ofJState st).cf = false := hcf
  rw [hwin, hcout, hspec, hcf0]
  simp

end CatCrypt.Crypto.SecureCompilation.Ascent
