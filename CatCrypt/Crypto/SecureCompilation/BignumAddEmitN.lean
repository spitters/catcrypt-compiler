/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp
public import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# An emitted N-limb `adcx` add proven against the multi-limb proof stack

> **`@kat-target`.** Hand-authored leaf block + direct `runBlock` proof — a KAT oracle /
> prototype for the bridge technique, NOT the canonical artifact. New field ops go via the
> golden path (`FieldEmitGoldenPath`); do not extend by hand.

The N-limb generalization of `BignumAddEmit.add2adcx_value`. Where that file
proves a fixed two-limb `adcx` chain

```
adcx a0, b0    -- a0 := a0 + b0 + CF,  CF := carry
adcx a1, b1    -- a1 := a1 + b1 + CF,  CF := carry
```

equals the verified two-limb add, this file does the same for an arbitrary
length: `adcxChain` takes a list of `(dst, src)` register-name pairs and emits
one `.adcx dst (.reg src)` per pair, and `adcxChain_value` proves — by induction
on the pair list, for all inputs, over the differentially-validated x86 machine —
that with `CF` cleared on entry the recombined destination limbs plus the final
carry equal `valLimbs (dst-values) + valLimbs (src-values)`. `adcxChain_bignumVal`
reads that through `valLimbs_eq_bignumVal` as the `MultiLimbKernel.bignumVal`
sum. The non-aliasing side condition (`AdcxFresh`: the destinations are pairwise
distinct and disjoint from the sources) is what lets a later step's write not
clobber an earlier step's source.

The abstract reference is the carry fold over `waddcarry` (`adcxFold`), the exact
`(carry-out, low-word)` semantics that `get_adcx` / `cf_adcx` give each `.adcx`
step — so the proof never leaves the machine's own ALU model. This is the
`valLimbs(runBlock) = bignumVal(kernel)` bridge a multi-limb Barrett-reduce
emission needs, now at the full N-limb width the curves (P256 = 4 limbs,
P384/BLS12-381 = 6 limbs) require.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.BignumAddEmitN

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-! ## 1. The emitted `adcx` chain and its abstract carry fold -/

/-- The emitted N-limb add-with-carry block: one `.adcx dst (.reg src)` per
    register pair `(dst, src)`, in order from least- to most-significant limb. -/
def adcxChain : List (String × String) → List (JInstr 64)
  | [] => []
  | (d, s) :: ps => .adcx d (.reg s) :: adcxChain ps

@[simp] theorem adcxChain_nil : adcxChain [] = [] := rfl

@[simp] theorem adcxChain_cons (d s : String) (ps : List (String × String)) :
    adcxChain ((d, s) :: ps) = .adcx d (.reg s) :: adcxChain ps := rfl

/-- The abstract carry fold the `adcx` chain realizes, over the machine's own
    `waddcarry` word primitive. Given the destination/source *values* `u`/`v`
    (limb lists) and a `Bool` carry-in, it produces the output limb list and the
    final carry-out — exactly the `(low-word, carry-out)` chain `get_adcx` /
    `cf_adcx` give each step. -/
def adcxFold : List (BitVec 64) → List (BitVec 64) → Bool →
    (List (BitVec 64) × Bool)
  | [], _, c => ([], c)
  | u₀ :: us, v, c =>
      let v₀ := v.headD 0
      let lo := (waddcarry u₀ v₀ c).2
      let cout := (waddcarry u₀ v₀ c).1
      let (rest, fc) := adcxFold us v.tail cout
      (lo :: rest, fc)

theorem adcxFold_length (u v : List (BitVec 64)) (c : Bool) :
    (adcxFold u v c).1.length = u.length := by
  induction u generalizing v c with
  | nil => rfl
  | cons u₀ us ih => simp only [adcxFold, List.length_cons]; rw [ih]

/-! ## 2. The carry fold reconstructs the sum -/

/-- **The carry fold recombines to the exact sum.** For `v` at least as long as
    `u`, the recombined output limbs plus the final carry (weighted at
    `2^(64·|u|)`) equal `valLimbs u + valLimbs (v.take |u|) + (carry-in)`. The
    `waddcarry`-fold analogue of `addLimbs_reconstruct`, proven by induction over
    `u` via the per-word `waddcarry_decompose`. -/
theorem adcxFold_reconstruct (u : List (BitVec 64)) :
    ∀ (v : List (BitVec 64)) (c : Bool),
      valLimbs (adcxFold u v c).1
          + (2 ^ 64) ^ u.length * (if (adcxFold u v c).2 then 1 else 0)
        = valLimbs u + valLimbs (v.take u.length) + (if c then 1 else 0) := by
  induction u with
  | nil => intro v c; simp [adcxFold]; rfl
  | cons u₀ us ih =>
      intro v c
      have h1 : (adcxFold (u₀ :: us) v c).1
          = (waddcarry u₀ (v.headD 0) c).2
              :: (adcxFold us v.tail (waddcarry u₀ (v.headD 0) c).1).1 := rfl
      have h2 : (adcxFold (u₀ :: us) v c).2
          = (adcxFold us v.tail (waddcarry u₀ (v.headD 0) c).1).2 := rfl
      rw [h1, h2, List.length_cons]
      set v₀ := v.headD 0 with hv₀
      set cout := (waddcarry u₀ v₀ c).1 with hcout
      have hword := waddcarry_decompose u₀ v₀ c
      have hrec := ih v.tail cout
      have hvsplit : valLimbs (v.take (us.length + 1))
          = v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length) := by
        cases v with
        | nil => simp [hv₀]
        | cons w ws => simp [hv₀, List.take]
      have hpow : (2 ^ 64) ^ (us.length + 1) = 2 ^ 64 * (2 ^ 64) ^ us.length := by
        rw [pow_succ]; ring
      simp only [valLimbs_cons]
      rw [hvsplit, hpow]
      have key : ((waddcarry u₀ v₀ c).2).toNat
          + 2 ^ 64 * (valLimbs (adcxFold us v.tail cout).1
              + (2 ^ 64) ^ us.length * (if (adcxFold us v.tail cout).2 then 1 else 0))
          = u₀.toNat + (v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length))
            + 2 ^ 64 * valLimbs us + (if c then 1 else 0) := by
        rw [hrec]
        nlinarith [hword]
      linarith [key]

/-! ## 3. The emitted chain over `runBlock` realizes the carry fold -/

/-- Register-layout freshness for the `adcx` chain: the destination registers are
    pairwise distinct (`Nodup`) and disjoint from the source registers — a later
    `.adcx` must not have an earlier step's write clobber its source. -/
structure AdcxFresh (ps : List (String × String)) : Prop where
  ds_nodup : (ps.map Prod.fst).Nodup
  ds_ss : ∀ p ∈ ps, ∀ q ∈ ps, p.1 ≠ q.2

/-- One `.adcx` step writes only `dst`: any other register is preserved. -/
theorem adcx_other (s : JState 64) (dst src r : String) (hr : r ≠ dst) :
    (evalInstr s (.adcx dst (.reg src))).get r = s.get r := by
  simp only [get_adcx, if_neg hr]

/-- The chain writes only the destination registers: a register distinct from
    every `dst` is preserved across the whole chain. -/
theorem adcxChain_preserves :
    ∀ (ps : List (String × String)) (r : String) (s : JState 64),
      (∀ q ∈ ps.map Prod.fst, r ≠ q) →
      (runBlock s (adcxChain ps)).get r = s.get r := by
  intro ps
  induction ps with
  | nil => intro r s _; simp [adcxChain]
  | cons p ps ih =>
      intro r s hr
      obtain ⟨d, sr⟩ := p
      simp only [List.map_cons, List.mem_cons] at hr
      rw [adcxChain_cons, runBlock_cons]
      rw [ih r _ (fun q hq => hr q (Or.inr hq))]
      exact adcx_other s d sr r (hr d (Or.inl rfl))

/-- **The emitted `adcx` chain over `runBlock` realizes the abstract carry fold.**
    With destination registers holding the limbs `u`, source registers holding
    `v` (matching lengths), the `AdcxFresh` register layout, and `CF` the carry-in
    `c`, running `adcxChain` leaves each destination register holding the
    `adcxFold u v c` output limb and `CF` the final carry — register-by-register
    the machine's `waddcarry` chain. -/
theorem adcxChain_runBlock :
    ∀ (ps : List (String × String)) (u v : List (BitVec 64)) (c : Bool) (s : JState 64),
      ps.length = u.length → ps.length = v.length →
      AdcxFresh ps →
      (ps.map Prod.fst).map s.get = u → (ps.map Prod.snd).map s.get = v →
      s.flagB (·.cf) = c →
      (ps.map Prod.fst).map (runBlock s (adcxChain ps)).get = (adcxFold u v c).1
        ∧ (runBlock s (adcxChain ps)).flagB (·.cf) = (adcxFold u v c).2 := by
  intro ps
  induction ps with
  | nil =>
      intro u v c s hpu hpv _ hdmap _ hcf
      have hu : u = [] := by cases u with | nil => rfl | cons => simp at hpu
      have hv : v = [] := by cases v with | nil => rfl | cons => simp at hpv
      subst hu; subst hv
      simp only [adcxChain, runBlock_nil, List.map_nil, adcxFold, hcf, and_self]
  | cons p ps ih =>
      intro u v c s hpu hpv hfresh hdmap hsmap hcf
      obtain ⟨d, sr⟩ := p
      cases u with
      | nil => simp at hpu
      | cons u0 us =>
        cases v with
        | nil => simp at hpv
        | cons v0 vs =>
          simp only [List.map_cons, List.cons.injEq] at hdmap hsmap
          obtain ⟨hdhd, hdtl⟩ := hdmap
          obtain ⟨hshd, hstl⟩ := hsmap
          rw [adcxChain_cons, runBlock_cons]
          set s1 := evalInstr s (.adcx d (.reg sr)) with hs1
          -- head value: d := (waddcarry u0 v0 c).2
          have hs1d : s1.get d = (waddcarry u0 v0 c).2 := by
            rw [hs1, get_adcx]
            simp only [JOperand.eval, hdhd, hshd, hcf, if_true]
          -- head carry-out flag = (waddcarry u0 v0 c).1
          have hs1cf : s1.flagB (·.cf) = (waddcarry u0 v0 c).1 := by
            rw [hs1, JState.flagB, cf_adcx]
            simp only [JOperand.eval, hdhd, hshd, hcf, Option.getD_some]
          -- Nodup / disjointness facts
          have hnd := hfresh.ds_nodup
          simp only [List.map_cons, List.nodup_cons] at hnd
          -- dst-registers preserved (distinct from d by Nodup): hold us
          have hdsmap : (ps.map Prod.fst).map s1.get = us := by
            rw [← hdtl]; apply List.map_congr_left; intro r hr
            rw [hs1]; exact adcx_other s d sr r (fun he => by subst he; exact hnd.1 hr)
          -- src-registers preserved (disjoint from d): hold vs
          have hssmap : (ps.map Prod.snd).map s1.get = vs := by
            rw [← hstl]; apply List.map_congr_left; intro r hr
            rw [hs1]
            refine adcx_other s d sr r (Ne.symm ?_)
            obtain ⟨q, hq, hqr⟩ := List.mem_map.1 hr
            subst hqr
            exact hfresh.ds_ss (d, sr) List.mem_cons_self q (List.mem_cons_of_mem _ hq)
          -- the tail AdcxFresh
          have hfresh' : AdcxFresh ps :=
            { ds_nodup := hnd.2
              ds_ss := fun a ha b hb => hfresh.ds_ss a (List.mem_cons_of_mem _ ha) b
                (List.mem_cons_of_mem _ hb) }
          obtain ⟨ihmap, ihcf⟩ := ih us vs (waddcarry u0 v0 c).1 s1
            (by simpa using hpu) (by simpa using hpv) hfresh' hdsmap hssmap hs1cf
          simp only [adcxFold, List.map_cons, List.headD_cons, List.tail_cons]
          -- head limb d preserved through the tail block
          have hdfinal : (runBlock s1 (adcxChain ps)).get d = (waddcarry u0 v0 c).2 := by
            rw [adcxChain_preserves ps d s1
              (fun q hq => fun he => by subst he; exact hnd.1 hq), hs1d]
          refine ⟨?_, ihcf⟩
          rw [hdfinal, ihmap]

/-! ## 4. The emitted chain's `runBlock` value = the verified sum -/

/-- **Symbolic value-correctness of the emitted `adcx` chain.** With `CF` cleared
    on entry, the recombined destination limbs plus the carry-out equal the sum of
    the destination and source limb values — for all inputs, over the
    differentially-validated x86 machine. The N-limb generalization of
    `add2adcx_value`. -/
theorem adcxChain_value (ps : List (String × String)) (u v : List (BitVec 64))
    (s : JState 64)
    (hpu : ps.length = u.length) (hpv : ps.length = v.length)
    (hfresh : AdcxFresh ps)
    (hdmap : (ps.map Prod.fst).map s.get = u) (hsmap : (ps.map Prod.snd).map s.get = v)
    (hcf : s.flagB (·.cf) = false) :
    valLimbs ((ps.map Prod.fst).map (runBlock s (adcxChain ps)).get)
        + (2 ^ 64) ^ ps.length
            * (if (runBlock s (adcxChain ps)).flagB (·.cf) then 1 else 0)
      = valLimbs u + valLimbs v := by
  obtain ⟨hmap, hcfout⟩ :=
    adcxChain_runBlock ps u v false s hpu hpv hfresh hdmap hsmap hcf
  rw [hmap, hcfout, hpu]
  have hrec := adcxFold_reconstruct u v false
  have htake : v.take u.length = v := by
    apply List.take_of_length_le; omega
  rw [htake] at hrec
  simpa using hrec

/-- **The emitted `adcx` chain computes the verified multi-limb sum.** Reading the
    value identity through `valLimbs_eq_bignumVal`, the emitted recombined output
    plus carry equals `bignumVal u + bignumVal v` — the kernel-proven full sum, at
    arbitrary limb count. -/
theorem adcxChain_bignumVal (ps : List (String × String)) (u v : List (BitVec 64))
    (s : JState 64)
    (hpu : ps.length = u.length) (hpv : ps.length = v.length)
    (hfresh : AdcxFresh ps)
    (hdmap : (ps.map Prod.fst).map s.get = u) (hsmap : (ps.map Prod.snd).map s.get = v)
    (hcf : s.flagB (·.cf) = false) :
    bignumVal ((ps.map Prod.fst).map (runBlock s (adcxChain ps)).get)
        + (2 ^ 64) ^ ps.length
            * (if (runBlock s (adcxChain ps)).flagB (·.cf) then 1 else 0)
      = bignumVal u + bignumVal v := by
  rw [← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal, ← valLimbs_eq_bignumVal]
  exact adcxChain_value ps u v s hpu hpv hfresh hdmap hsmap hcf

end CatCrypt.Crypto.SecureCompilation.BignumAddEmitN
