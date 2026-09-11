/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedc4RunBlockProven
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

/-!
# The Montgomery-reduce carry-fold cascade over one `runBlock` trace

`MontRedc4RunBlockProven.emitMontRedcStep_shifted_window` (the *shift brick*)
proves that running one emitted reduce word-step lands one `montgomeryReduce`
step in the **shifted window** — the accumulator registers with the low limb
dropped, plus the row-carry register `rcy` as the new top word. That value must
then be threaded up into the next word-step's input window: `rcy` is *added*
into the register just above the window (`accNames[i+4]`) and the resulting
carry is propagated through every higher accumulator word into `rtop`. This is
`Curve4MontMulProvenEmit.emitMontRedcStepAt`'s `foldChain`:

```
add accNames[i+4], rcy          -- fold the carry word in (CF-independent)
adc accNames[i+5], 0            -- propagate …
…
adc accNames[7],   0
adc rtop,          0            -- … the whole way up into rtop
```

This module proves the missing **`valLimbs`-level `runBlock` lemma for this
add/adc fold cascade** (residual (1) of
`MontRedc4RunBlockProven.montRedc4RunBlock_gap`). It is the exact analogue, for
"add a single carry word into a higher-word register vector", of
`FieldAddSubTierA.emitAdcChain_runBlock` (the ripple-add of two vectors): the
same `emit_adc_*` per-instruction bridges and `Cios4LimbProven.addLimbs` /
`addLimbs_reconstruct` anchors, but the source is `rcy` in the leading word and
the immediate `0` in every propagated word.

## What is PROVEN here

* **`adcImm0Chain_runBlock`** — the pure `adc dᵢ, 0` propagation chain leaves each
  `dᵢ` holding the `addLimbs u (replicate 0) cin` limb and `CF` the final carry:
  entering with `CF = cin`, it ripples the carry-in through the register vector
  `ds` (all sources `0`). Register-by-register the proven abstract carry chain.

* **`foldCascade_runBlock`** — the whole fold `add d₀, rcy :: adc dᵢ, 0 …` leaves
  the destination registers `D` holding `(addLimbs H (r :: replicate 0) 0).1` and
  `CF` the final carry, where `H = D.map s.get` and `r = (s.get rcy)`. The leading
  `add` (entered with `CF = 0`, so equal to an `adc` with carry-in `0`) folds `rcy`
  into `d₀`; the tail chain propagates.

* **`foldCascade_value`** ⭐ — the composing statement. Running the fold cascade
  from a state with `CF = 0`, the destination register vector `D` reconstructs to
  its old value plus the single carry word `rcy`:

  `valLimbs (D.map post.get) + (2^64)^|D| · (post CF) = valLimbs (D.map s.get) + (s.get rcy).toNat`,

  `post = runBlock s (foldCascade D rcy)`. Value-exact: the carry word is added in,
  the final `CF` weighted at the top. This is the piece that turns the shift
  brick's value into the next word-step's input-window value (see the module note
  `carryFold_composition_note`).

## How it composes with the shift brick (see `carryFold_composition_note`)

Writing `Higher = valLimbs (accNames[i+4..7]) + (2^64)^(4-i)·rtop`, one has, at the
full running value `W_i = valLimbs (accNames[i..7]) + weight·rtop`,

`montgomeryReduce N (2^64) n' W_i
   = montgomeryReduce N (2^64) n' (valLimbs win) + (2^64)^3 · Higher`,

because `m = W_i mod 2^64` depends only on the low window word and `m·N` (5 words)
never reaches `accNames[i+4]`. The shift brick supplies the first summand as
`valLimbs (win.drop 1) + (2^64)^3·rcy`; `foldCascade_value` supplies exactly
`(2^64)^3·(rcy + Higher)` redistributed across `accNames[i+4..7]` and `rtop`. So
the shift brick and this cascade lemma together give the register realisation of
one `montgomeryReduce` step **on the full running value** — the content of one
`hstep_i` of `MontReduceRunBlock.emitMontRedc4_value`. What this module does NOT
close is stated honestly in `carryFold_composition_note`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (addCarryWord carryOutBit)

/-! ## 1. The `adc dst, 0` per-instruction bridges

Immediate-`0` analogues of `FieldAddSubTierA.emit_adc_word` / `emit_adc_cf` /
`emit_adc_other`: the propagated words of the fold add the constant `0` (plus the
carry-in), not a source register. -/

/-- One emitted `adc dst, 0` writes `addCarryWord dst 0 (CF-bit)` into `dst`. -/
theorem emit_adc_imm0_word (s : JState 64) (dst : String) :
    (evalInstr s (.adc dst (.imm 0))).get dst
      = addCarryWord (s.get dst) 0
          (BitVec.ofNat 1 (if s.flagB (·.cf) then 1 else 0)) := by
  simp only [evalInstr, JState.get, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry,
    addCarryWord, JOperand.eval]
  rcases h : s.flagB (·.cf) with _ | _ <;>
    simp only [if_true, if_false, Bool.false_eq_true] <;>
    (apply BitVec.eq_of_toNat_eq) <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- One emitted `adc dst, 0` sets `CF` to the carry-out of `dst + 0 + CF-in`. -/
theorem emit_adc_imm0_cf (s : JState 64) (dst : String) :
    (evalInstr s (.adc dst (.imm 0))).flagB (·.cf)
      = decide (2 ^ 64 ≤ (s.get dst).toNat + 0
          + (if s.flagB (·.cf) then 1 else 0)) := by
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry,
    JOperand.eval, wunsigned, Option.getD_some, BitVec.toNat_ofNat]
  have hx := (s.get dst).isLt
  simp only [JState.get] at hx
  refine wrap_iff _ ?_
  split <;> omega

/-- One emitted `adc dst, 0` writes only `dst`: any other register is preserved. -/
theorem emit_adc_imm0_other (s : JState 64) (dst r : String) (hr : r ≠ dst) :
    (evalInstr s (.adc dst (.imm 0))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-! ## 2. The `adc dᵢ, 0` propagation chain = `addLimbs u (replicate 0) cin`

`adcImm0Chain ds` is `[adc d₀, 0; adc d₁, 0; …]`: entered with `CF` the carry-in
bit, it ripples that carry through the register vector `ds` (all sources `0`),
leaving each `dᵢ` the `addLimbs u (replicate 0) cin` sum limb and `CF` the final
carry. The immediate-`0` sibling of `FieldAddSubTierA.emitAdcChain_runBlock`. -/

/-- The emitted `adc dᵢ, 0` propagation chain. -/
def adcImm0Chain : List String → List (JInstr 64)
  | [] => []
  | d :: ds => JInstr.adc d (.imm 0) :: adcImm0Chain ds

/-- The chain writes only the destination registers `ds`: a register distinct from
    every `dᵢ` is preserved across the whole chain. -/
theorem adcImm0Chain_preserves :
    ∀ (ds : List String) (r : String) (s : JState 64),
      (∀ q ∈ ds, r ≠ q) → (runBlock s (adcImm0Chain ds)).get r = s.get r := by
  intro ds
  induction ds with
  | nil => intro r s _; simp [adcImm0Chain]
  | cons d ds ih =>
      intro r s hr
      rw [adcImm0Chain, runBlock_cons]
      rw [ih r _ (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
      exact emit_adc_imm0_other s d r (hr d List.mem_cons_self)

/-- **The `adc dᵢ, 0` chain over `runBlock` = the abstract `addLimbs` carry-ripple
    with an all-zero source.** With destination registers `ds` holding `u`, `ds`
    pairwise distinct (`Nodup`), and `CF` the carry-in bit `cin`, running
    `adcImm0Chain` leaves each `dᵢ` holding the `addLimbs u (replicate |u| 0) cin`
    limb and `CF` the final carry — register-by-register the proven carry chain. -/
theorem adcImm0Chain_runBlock :
    ∀ (ds : List String) (u : List (BitVec 64)) (cin : BitVec 1) (s : JState 64),
      ds.length = u.length → ds.Nodup →
      ds.map s.get = u → s.flagB (·.cf) = (cin = 1) →
      ds.map (runBlock s (adcImm0Chain ds)).get
          = (addLimbs u (List.replicate u.length 0) cin).1
        ∧ (runBlock s (adcImm0Chain ds)).flagB (·.cf)
          = ((addLimbs u (List.replicate u.length 0) cin).2 = 1) := by
  intro ds
  induction ds with
  | nil =>
      intro u cin s hdu _ hdmap hcf
      have hu : u = [] := by cases u with | nil => rfl | cons => simp at hdu
      subst hu
      simp only [adcImm0Chain, runBlock_nil, List.map_nil, addLimbs, hcf, and_self]
  | cons d ds ih =>
      intro u cin s hdu hnd hdmap hcf
      cases u with
      | nil => simp at hdu
      | cons u0 us =>
        simp only [List.map_cons, List.cons.injEq] at hdmap
        obtain ⟨hdhd, hdtl⟩ := hdmap
        rw [adcImm0Chain, runBlock_cons]
        set s1 := evalInstr s (.adc d (.imm 0)) with hs1
        -- head value: d := addCarryWord u0 0 cin
        have hs1d : s1.get d = addCarryWord u0 0 cin := by
          rw [hs1, emit_adc_imm0_word, hdhd]
          congr 1
          exact cin_bridge cin _ hcf
        -- head carry-out flag = carryOutBit u0 0 cin
        have hs1cf : (s1.flagB (·.cf) = true) = (carryOutBit u0 0 cin = 1) := by
          rw [hs1, emit_adc_imm0_cf, hdhd]
          rw [show (if (s.flagB fun x ↦ x.cf) then (1 : Nat) else 0)
                = (if cin = 1 then 1 else 0) by
            rcases hb : (s.flagB fun x ↦ x.cf) with _ | _ <;> simp_all]
          have := cf_carryOut u0 0 cin
          simp only [show ((0 : BitVec 64).toNat) = 0 from rfl, Nat.add_zero] at this ⊢
          simp only [decide_eq_true_eq] at this ⊢
          rw [this]
        -- ds-registers preserved (distinct from d by Nodup): hold us
        have hdsmap : ds.map s1.get = us := by
          rw [← hdtl]; apply List.map_congr_left; intro r hr
          rw [hs1]; exact emit_adc_imm0_other s d r
            (fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hr)
        -- apply IH with cin := carryOutBit u0 0 cin
        obtain ⟨ihmap, ihcf⟩ := ih us (carryOutBit u0 0 cin) s1
          (by simpa using hdu) (List.nodup_cons.mp hnd).2 hdsmap hs1cf
        simp only [List.length_cons, List.replicate_succ, addLimbs, List.headD_cons,
          List.tail_cons, List.map_cons]
        -- head limb d preserved through the tail block
        have hdfinal : (runBlock s1 (adcImm0Chain ds)).get d = addCarryWord u0 0 cin := by
          rw [adcImm0Chain_preserves ds d s1
            (fun q hq => fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hq), hs1d]
        refine ⟨?_, ihcf⟩
        rw [hdfinal, ihmap]

/-! ## 3. The full fold cascade `add d₀, rcy :: adc dᵢ, 0 …`

`foldCascade D rcy` is exactly `Curve4MontMulProvenEmit.emitMontRedcStepAt`'s
`[add nextCarryWord, rcy] ++ foldChain` with `D = nextCarryWord :: (higher words
++ [rtop])`. The leading `add` folds the carry word `rcy` into the low destination
`d₀`; the `adcImm0Chain` tail propagates the resulting carry the whole way up. -/

/-- The fold cascade: fold `rcy` into `D.head`, propagate the carry up `D.tail`. -/
def foldCascade (D : List String) (rcy : String) : List (JInstr 64) :=
  match D with
  | [] => []
  | d0 :: tl => JInstr.add d0 (.reg rcy) :: adcImm0Chain tl

/-- **The fold cascade over `runBlock` = `addLimbs (r :: replicate 0)`.** With
    destination registers `D` holding `H`, `D` pairwise distinct and disjoint from
    the carry register `rcy`, and `CF = 0` on entry, running `foldCascade` leaves the
    registers `D` holding the `addLimbs H (r :: replicate 0) 0` limbs and `CF` the
    final carry, where `r = s.get rcy`. -/
theorem foldCascade_runBlock (D : List String) (rcy : String) (H : List (BitVec 64))
    (s : JState 64)
    (hlen : D.length = H.length) (hnd : D.Nodup) (hrcy : ∀ d ∈ D, rcy ≠ d)
    (hmap : D.map s.get = H) (hcf0 : s.flagB (·.cf) = false) :
    D.map (runBlock s (foldCascade D rcy)).get
        = (addLimbs H ((s.get rcy) :: List.replicate (H.length - 1) 0) 0).1
      ∧ (runBlock s (foldCascade D rcy)).flagB (·.cf)
        = ((addLimbs H ((s.get rcy) :: List.replicate (H.length - 1) 0) 0).2 = 1) := by
  cases D with
  | nil =>
      have hH : H = [] := by cases H with | nil => rfl | cons => simp at hlen
      subst hH
      refine ⟨by simp [foldCascade, addLimbs], ?_⟩
      simp only [foldCascade, runBlock_nil, addLimbs]
      rw [hcf0]; simp
  | cons d0 tl =>
      cases H with
      | nil => simp at hlen
      | cons h0 hs =>
        simp only [List.map_cons, List.cons.injEq] at hmap
        obtain ⟨hd0, htl⟩ := hmap
        set r := s.get rcy with hr
        rw [foldCascade, runBlock_cons]
        set s1 := evalInstr s (.add d0 (.reg rcy)) with hs1
        -- head value: d0 := addCarryWord h0 r 0
        have hs1d : s1.get d0 = addCarryWord h0 r 0 := by
          rw [hs1, emit_add_word, hd0, hr]
        -- head carry-out flag = carryOutBit h0 r 0
        have hs1cf : s1.flagB (·.cf) = (carryOutBit h0 r 0 = 1) := by
          rw [hs1, emit_add_cf, hd0, ← hr]
          have := cf_carryOut h0 r 0
          simp only [if_neg (by decide : ¬ ((0 : BitVec 1) = 1)),
            Nat.add_zero] at this
          simp only [decide_eq_true_eq] at this ⊢
          rw [this]
        -- tail regs preserved (distinct from d0 by Nodup): hold hs
        have htlmap : tl.map s1.get = hs := by
          rw [← htl]; apply List.map_congr_left; intro q hq
          rw [hs1]; exact emit_add_other s d0 rcy q
            (fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hq)
        -- carry-fold on the tail via the imm-0 chain
        obtain ⟨ihmap, ihcf⟩ := adcImm0Chain_runBlock tl hs (carryOutBit h0 r 0) s1
          (by simpa using hlen) (List.nodup_cons.mp hnd).2 htlmap hs1cf
        simp only [List.length_cons, Nat.add_sub_cancel, addLimbs,
          List.headD_cons, List.tail_cons, List.map_cons]
        -- head limb d0 preserved through the tail block
        have hd0final : (runBlock s1 (adcImm0Chain tl)).get d0 = addCarryWord h0 r 0 := by
          rw [adcImm0Chain_preserves tl d0 s1
            (fun q hq => fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hq), hs1d]
        refine ⟨?_, ihcf⟩
        rw [hd0final, ihmap]

/-- **The fold cascade's `runBlock` value: the carry word `rcy` folded into the
    destination vector.** ⭐ For destination registers `D` holding `H`, disjoint from
    the carry register `rcy`, entered with `CF = 0`, the fold cascade leaves the
    registers `D` reconstructing to their old value plus the single carry word,
    with the final `CF` weighted at the top:

    `valLimbs (D.map post.get) + (2^64)^|D| · (post CF) = valLimbs H + (s.get rcy).toNat`.

    This is the `valLimbs`-level `runBlock` lemma for the `add`/`adc` fold cascade
    (residual (1) of `MontRedc4RunBlockProven.montRedc4RunBlock_gap`), built from
    `foldCascade_runBlock` + the proven `Cios4LimbProven.addLimbs_reconstruct`. -/
theorem foldCascade_value (D : List String) (rcy : String) (H : List (BitVec 64))
    (s : JState 64)
    (hlen : D.length = H.length) (hnd : D.Nodup) (hrcy : ∀ d ∈ D, rcy ≠ d)
    (hmap : D.map s.get = H) (hcf0 : s.flagB (·.cf) = false) (hH : 0 < H.length) :
    valLimbs (D.map (runBlock s (foldCascade D rcy)).get)
        + (2 ^ 64) ^ D.length
            * (if (runBlock s (foldCascade D rcy)).flagB (·.cf) then 1 else 0)
      = valLimbs H + (s.get rcy).toNat := by
  obtain ⟨hregs, hcf⟩ := foldCascade_runBlock D rcy H s hlen hnd hrcy hmap hcf0
  set r := s.get rcy with hr
  set v := r :: List.replicate (H.length - 1) (0 : BitVec 64) with hv
  rw [hregs, hlen]
  -- the recombination of `addLimbs H v 0`
  have hrec := addLimbs_reconstruct H v 0
  -- v.take |H| = v (|v| = |H|), and valLimbs v = r.toNat
  have hvlen : v.length = H.length := by
    rw [hv, List.length_cons, List.length_replicate]; omega
  have htake : v.take H.length = v := by apply List.take_of_length_le; omega
  have hvval : valLimbs v = r.toNat := by
    rw [hv, valLimbs_cons, valLimbs_replicate_zero, Nat.mul_zero, Nat.add_zero]
  rw [htake, hvval, show ((0 : BitVec 1).toNat) = 0 from rfl, Nat.add_zero] at hrec
  -- rewrite the CF bit to the addLimbs final carry's toNat
  have hcfbit : (if (runBlock s (foldCascade D rcy)).flagB (·.cf) then (1 : Nat) else 0)
      = (addLimbs H v 0).2.toNat := by
    rw [bit_toNat (addLimbs H v 0).2]
    by_cases hb : (runBlock s (foldCascade D rcy)).flagB (·.cf) = true
    · rw [if_pos hb, if_pos (by rw [← hcf]; exact hb)]
    · rw [if_neg hb, if_neg (by rw [← hcf]; simpa using hb)]
  rw [hcfbit]
  exact hrec

/-! ## 4. How this composes with the shift brick, and what remains (honest)

`carryFold_composition_note` records, as documentation, exactly how
`foldCascade_value` (this module) plus
`MontRedc4RunBlockProven.emitMontRedcStep_shifted_window` (the shift brick) fit
together toward the four `hstep_i` of `MontReduceRunBlock.emitMontRedc4_value`,
and precisely what is NOT yet a theorem. -/

/-- **The carry-fold ↔ shift-brick composition, and the residual (documentation).**

    Fix step `i` of the fused reduce. Let the running full value be
    `W_i = valLimbs (accNames[i..7]) + (2^64)^(8-i)·(post rtop)` (`W_0 = T`, the
    512-bit product; rtop starts at `0`), and split off the higher words
    `Higher = valLimbs (accNames[i+4..7]) + (2^64)^(4-i)·rtop`, so
    `W_i = valLimbs win + (2^64)^4·Higher` with `win = accNames[i..i+3]`.

    **Arithmetic bridge (a `Nat` identity, provable from `montgomeryReduce`):**
    because `m = W_i mod 2^64 = (accNames[i]·n') mod 2^64` reads only the low
    window word and `m·N` (five words) never reaches `accNames[i+4]`,

    `montgomeryReduce N (2^64) n' W_i
       = montgomeryReduce N (2^64) n' (valLimbs win) + (2^64)^3·Higher`.

    * The shift brick (`emitMontRedcStep_shifted_window`) discharges the first
      summand: after the reduce word-step, `accNames[i+1..i+3]` and `rcy` hold
      `montgomeryReduce N (2^64) n' (valLimbs win) = valLimbs (win.drop 1) + (2^64)^3·rcy`.
    * `foldCascade_value` (this module), with `D = accNames[i+4] :: accNames[i+5..7]
      ++ [rtop]` and carry word `rcy`, discharges `(2^64)^3·(rcy + Higher)`: the fold
      leaves `valLimbs (accNames[i+4..7]) + weight·rtop = Higher + rcy.toNat`
      redistributed, carry absorbed into `rtop`.

    Summing, `valLimbs (accNames[i+1..7]) + weight·rtop = montgomeryReduce N (2^64)
    n' W_i = W_{i+1}` — the register realisation of ONE `hstep_i` on the full
    running value.

    **What is NOT closed here (the exact open obligations).** Turning the four
    `hstep_i` into theorems from the instructions still needs, beyond the two value
    bricks above:

    1. *The `Nat` arithmetic bridge* boxed above — `montgomeryReduce` on the split
       value `valLimbs win + (2^64)^4·Higher` equals the windowed reduce plus
       `(2^64)^3·Higher`. This is a pure `Number.montgomeryReduce` divisibility fact
       (`m` reads only the low word; `2^256·Higher` is `2^64`-divisible), NOT yet
       stated. It is the "the higher product words ride through untouched" lemma.

    2. *The four-fold state threading* — that step `i`'s output `JState` (registers
       `accNames[i+1..7]`, `rtop`; scratch `m/dcy/rcy/hi/lo` dirty; `CF` set by the
       final `adc rtop, 0`) re-establishes step `i+1`'s `emitMontRedcStep_shifted_window`
       preconditions after its three leading `xor` clears (`m=dcy=rcy=0`, `CF=OF=0`),
       and that the window/freshness hypotheses (`RowFresh`, disjointness) hold at
       every offset `i ∈ {0,1,2,3}`. This is register-routing bookkeeping over the
       concrete `accNames`/`pNames` layout, `runBlock`-splitting
       `emitMontRedc4Block = emitMontRedcStepAt 0 ++ … ++ emitMontRedcStepAt 3`.

    With (1) and (2), `emitMontRedcStep_shifted_window` + `foldCascade_value`
    discharge the four `hstep_i`, reducing `MontRedc4RunBlockProven.montRedc4RunBlockGoal`
    to ONLY residual (2) of `montRedc4RunBlock_gap` — the `emitCondSubP`
    canonicalisation anomaly. The `add`/`adc` fold half of residual (1), which
    `montRedc4RunBlock_gap` flagged as "no `valLimbs`-level `add`/`adc` lemma in
    tree", is `foldCascade_value`, proved here. -/
theorem carryFold_composition_note : True := trivial

end CatCrypt.Crypto.SecureCompilation.X86Backend.MontRedcCarryFold
