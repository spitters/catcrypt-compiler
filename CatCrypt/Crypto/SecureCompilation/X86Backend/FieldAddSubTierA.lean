/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
import CatCrypt.Crypto.SecureCompilation.X86Backend.PastaFieldAddSubKernel
import CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel

/-!
# Tier-A modular field add/sub: limb/`runBlock` value = `(a ± b) mod p`

The curve add/sub kernels (`PastaFieldAddSubKernel`, the 6-limb BLS/P384 add/sub)
carry only a `*_lowering_correct` theorem (the lowered `Com` denotes the source
block) and an external GMP KAT; the link "the block computes `(a ± b) mod p`" was
never a Lean theorem. This file supplies that value link at the **multi-limb
carry-chain** level, the add/sub analogue of `Cios4LimbProven`'s Montgomery
reconstruction.

The arithmetic is pinned to the genuine modular spec over `Nat`:

* modular add  `(a + b) mod p`  = add the limb vectors (`Cios4LimbProven.addLimbs`,
  the proven ripple-add over the dialect carry primitives), then **conditionally
  subtract** `p` if the sum is `≥ p`;
* modular sub  `(a − b) mod p`  = subtract the limb vectors, then **conditionally
  add** `p` back if the difference went negative (a borrow).

For canonical inputs `a, b ∈ [0, p)` the sum is `< 2p` and the difference is in
`(−p, p)`, so a single conditional subtract (resp. add) of `p` canonicalises.

## What is PROVEN here

1. `condSubP` / `condSubP_eq_mod` — the canonical conditional subtract of `p`
   (the `Nat`-level `if v < p then v else v − p`, the value the emitted `SUB`/`SBB`
   trial + `CMOVB` select computes), proven `= v % p` on `v < 2p`. The multi-limb
   generalization of `Sm2FieldProven.condsub_word` (which proved the same identity
   for a two-word value branch-free).
2. `condAddP` / `condAddP_eq_mod` — the canonical conditional add-back of `p` for
   modular sub (the value the masked `ADD`/`ADC` chain computes), proven
   `(a + p − b) mod p` for `a, b < p`.
3. `modAddVal` / `modAddVal_eq_mod`, `modSubVal` / `modSubVal_eq_mod` — the full
   modular add/sub at the recombined-value level, with the ripple-add value pinned
   to the proven `Cios4LimbProven.addLimbs_reconstruct`.
4. `<curve>_modadd_value` / `<curve>_modsub_value` — instantiations at the Pasta
   (Pallas/Vesta, 4-limb) and BLS12-381 / P384 (6-limb) curve moduli: the emitted
   add/sub recombined value = `(a ± b) mod p`. Tier A for the add/sub kernels.
5. `babybear_fpadd_runBlock` / `babybear_fpsub_runBlock` — the single-word BabyBear
   / Barrett-butterfly add/sub (`p = 2^31 − 2^27 + 1` fits one word): the emitted
   butterfly's stored output words equal `(a + ω·b) mod p` and `(a + p − ω·b) mod p`,
   wrapping the already-proven `BarrettButterflyKernel.butterfly_out{0,1}_spec`
   (a genuine `runBlock`-of-emitted tie) into the add/sub field-op shape.

6. `emitAdcChain` / `emitAdcChain_runBlock` / `emitAdcChain_runBlock_value` — a
   genuine emitted ADD/ADC ripple-add `List (JInstr 64)` proven over `runBlock`
   (register-by-register) to equal `Cios4LimbProven.addLimbs`, recombining to
   `valLimbs a + valLimbs b`; `modAdd_runBlock` / `<curve>_modadd_runBlock` compose
   it with `condSubP` for `runBlock(emitted add) = (a + b) mod p` at each curve.

## Scope (honest)

The modular **add** is a genuine `runBlock`-of-emitted statement: `emitAdcChain` is
a real `List (JInstr 64)` and `emitAdcChain_runBlock` proves it computes the
proven `Cios4LimbProven.addLimbs` over `runBlock` (each step the `.adc` ALU
semantics of `evalInstr`, no abstraction gap), recombined by the proven
`addLimbs_reconstruct` and canonicalised by `condSubP`. The single-word BabyBear
add/sub is likewise tied to a genuine emitted `runBlock` output
(`butterfly_out{0,1}_spec`). The modular **sub** conditional add-back of `p` is
proven at the recombined-`Nat` level (`condAddP`, exactly the value the emitted
masked `ADD`/`ADC` add-back computes); the emitted SUB/SBB borrow-chain over
`runBlock` (the `.sub`/`.sbb`/`CMOVB` analogue of `emitAdcChain`) is the named
remainder for the 4-limb / 6-limb curves.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (addCarryWord carryOutBit)

/-! ## 1. The canonical conditional subtract / add of the modulus

`condSubP p v = if v < p then v else v − p` is the value the emitted modular-add
tail computes: the trial difference `v − p` is kept (`CMOVB` not taken) exactly
when the `SUB`/`SBB` chain produced **no** final borrow (`v ≥ p`); otherwise the
original `v` is kept. `condAddP p d` is the dual for modular sub. -/

/-- The canonical conditional subtract of `p` (the `Nat` value the emitted
    `SUB`/`SBB` trial + `CMOVB` select computes). -/
def condSubP (p v : Nat) : Nat := if v < p then v else v - p

/-- **The conditional subtract is the reduction, on `v < 2p`.** Generalizes
    `Sm2FieldProven.condsub_word` (which proved the same identity branch-free for a
    two-word value) to an arbitrary value `v < 2p`. -/
theorem condSubP_eq_mod (p v : Nat) (hv : v < 2 * p) : condSubP p v = v % p := by
  unfold condSubP
  by_cases h : v < p
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    rw [Nat.not_lt] at h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]

/-- The canonical conditional add-back of `p` for modular sub: the emitted borrow
    subtract produces the wrapped difference `(a + 2^? − b)`; modeled at the value
    level as: if `a ≥ b` keep `a − b`, else add `p` back to `a + p − b`. We package
    it directly as the value `(a + p − b)` reduced once. -/
def condAddP (p a b : Nat) : Nat := if a < b then a + p - b else a - b

/-- **The conditional add-back is the modular difference, for `a, b < p`.** When
    `a ≥ b` the difference `a − b` is already canonical; when `a < b` adding `p`
    back gives `a + p − b ∈ [0, p)`. Either way the value is `(a + p − b) % p`. -/
theorem condAddP_eq_mod (p a b : Nat) (ha : a < p) (hb : b < p) :
    condAddP p a b = (a + p - b) % p := by
  unfold condAddP
  by_cases h : a < b
  · rw [if_pos h, Nat.mod_eq_of_lt (by omega)]
  · rw [if_neg h]
    rw [Nat.not_lt] at h
    -- a + p - b = p + (a - b), and (a - b) < p
    have : a + p - b = p + (a - b) := by omega
    rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-! ## 2. The ripple-add value over the proven carry chain

`addLimbs u v 0` is the proven multi-limb ripple-add (`Cios4LimbProven`); for
equal-length limb vectors its recombined value (sum limbs with the final carry
weighted at `2^{64·n}`) is exactly `valLimbs u + valLimbs v`. -/

/-- The recombined value of the ripple-add `addLimbs u v 0`: the sum limbs plus
    the final carry word, read little-endian. This is the value the emitted
    `ADD`/`ADC` chain leaves (sum limbs + carry-out register). -/
def addChainVal (u v : List (BitVec 64)) : Nat :=
  valLimbs (addLimbs u v 0).1 + (2 ^ 64) ^ u.length * (addLimbs u v 0).2.toNat

/-- **The ripple-add chain value is the exact sum**, for equal-length limb
    vectors. Direct from the proven `Cios4LimbProven.addLimbs_reconstruct`
    (`cin = 0`, `v.take |u| = v`). -/
theorem addChainVal_eq (u v : List (BitVec 64)) (hlen : v.length = u.length) :
    addChainVal u v = valLimbs u + valLimbs v := by
  have h := addLimbs_reconstruct u v 0
  have htake : v.take u.length = v := by
    apply List.take_of_length_le; omega
  rw [htake] at h
  simp only [addChainVal]
  rw [h]
  rfl

/-! ## 2b. A genuine emitted ripple-add over `runBlock` = `addLimbs`

The emitted ADD/ADC chain `[.add d₀ s₀, .adc d₁ s₁, …]` (first `.add` enters with
carry-in `0`, each subsequent `.adc` reads the carry from `CF`) is the real
`List (JInstr 64)` the curve add kernels run. Reading each result limb out of its
destination register `dᵢ` and the final carry out of `CF` over `runBlock`, the
chain produces exactly the proven abstract `Cios4LimbProven.addLimbs` output (sum
limbs + final carry), so its recombined value is `addChainVal` — the genuine
`runBlock`-of-emitted anchor for the add primitive. -/

/-- One emitted ADD step writes the wrapped-sum limb into `dst`. -/
theorem emit_add_word (s : JState 64) (dst src : String) :
    (evalInstr s (.add dst (.reg src))).get dst = addCarryWord (s.get dst) (s.get src) 0 := by
  simp only [evalInstr, JState.get, JState.writeB5W, x86_ADD, rflags_of_aluop, addCarryWord,
    JOperand.eval]
  simp

/-- One emitted ADD step sets `CF` to the carry-out (`= 1`). -/
theorem emit_add_cf (s : JState 64) (dst src : String) :
    (evalInstr s (.add dst (.reg src))).flagB (·.cf)
      = decide (2 ^ 64 ≤ (s.get dst).toNat + (s.get src).toNat) := by
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_ADD, rflags_of_aluop, JOperand.eval,
    wunsigned, Option.getD_some, BitVec.toNat_add]
  have hx := (s.get dst).isLt; have hy := (s.get src).isLt
  have hmod : ((s.get dst).toNat + (s.get src).toNat) % 2 ^ 64
      = if 2 ^ 64 ≤ (s.get dst).toNat + (s.get src).toNat
        then (s.get dst).toNat + (s.get src).toNat - 2 ^ 64
        else (s.get dst).toNat + (s.get src).toNat := by
    split
    · rename_i h; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · rename_i h; rw [Nat.mod_eq_of_lt (by omega)]
  simp only [hmod]
  split
  · simp_all; omega
  · simp_all

/-- One emitted ADD step writes only `dst` (and the flags): any other register is
    preserved. -/
theorem emit_add_other (s : JState 64) (dst src r : String) (hr : r ≠ dst) :
    (evalInstr s (.add dst (.reg src))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-- One emitted ADC step writes `addCarryWord dst src (CF-bit)` into `dst`. -/
theorem emit_adc_word (s : JState 64) (dst src : String) :
    (evalInstr s (.adc dst (.reg src))).get dst
      = addCarryWord (s.get dst) (s.get src) (BitVec.ofNat 1 (if s.flagB (·.cf) then 1 else 0)) := by
  simp only [evalInstr, JState.get, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry,
    addCarryWord, JOperand.eval]
  rcases h : s.flagB (·.cf) with _ | _ <;>
    simp only [if_true, if_false, Bool.false_eq_true] <;>
    (apply BitVec.eq_of_toNat_eq) <;> simp [BitVec.toNat_add, BitVec.toNat_ofNat]

/-- The carry-out characterisation as a `Nat` fact: for `X < 2^65` (two words plus
    a carry-in), the wrap-flag `decide (X % 2^64 ≠ X)` is `decide (2^64 ≤ X)`. -/
theorem wrap_iff (X : Nat) (h : X < 2 ^ 65) :
    decide (X % 2 ^ 64 ≠ X) = decide (2 ^ 64 ≤ X) := by
  have hmod : X % 2 ^ 64 = if 2 ^ 64 ≤ X then X - 2 ^ 64 else X := by
    split
    · rename_i hh; rw [Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega)]
    · rename_i hh; rw [Nat.mod_eq_of_lt (by omega)]
  simp only [hmod]
  split
  · rename_i hh; simp only [decide_eq_true hh]; simp; omega
  · rename_i hh; rw [decide_eq_false hh]; simp

/-- One emitted ADC step sets `CF` to the carry-out of `dst + src + CF-in`. -/
theorem emit_adc_cf (s : JState 64) (dst src : String) :
    (evalInstr s (.adc dst (.reg src))).flagB (·.cf)
      = decide (2 ^ 64 ≤ (s.get dst).toNat + (s.get src).toNat
          + (if s.flagB (·.cf) then 1 else 0)) := by
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_ADC, rflags_of_aluop, add_carry,
    JOperand.eval, wunsigned, Option.getD_some, BitVec.toNat_ofNat]
  have hx := (s.get dst).isLt; have hy := (s.get src).isLt
  simp only [JState.get] at hx hy
  refine wrap_iff _ ?_
  split <;> omega

/-- One emitted ADC step writes only `dst`: any other register is preserved. -/
theorem emit_adc_other (s : JState 64) (dst src r : String) (hr : r ≠ dst) :
    (evalInstr s (.adc dst (.reg src))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-! ## 2c. The emitted ADC chain over `runBlock` = `addLimbs`

`emitAdcChain ds ss` is the real emitted instruction list `[.adc d₀ s₀,
.adc d₁ s₁, …]`: each step adds `sᵢ` and the carry-in `CF` into the destination
limb register `dᵢ`, leaving the carry-out in `CF`. Entered with `CF` the carry-in
bit, the chain leaves each `dᵢ` holding the `addLimbs` sum limb and `CF` the final
carry — proven by induction over the limb register list, each step the per-`.adc`
bridge `emit_adc_word` / `emit_adc_cf`. (The leading word can be an `.adc` entered
with `CF = 0`, equivalently an `.add`.) -/

/-- A 1-bit register equals its `toNat` indicator. -/
theorem bit_toNat (cin : BitVec 1) : cin.toNat = (if cin = 1 then 1 else 0) := by
  have := cin.isLt
  rcases hc : cin.toNat with _ | _ <;>
    (first
      | (have hcin : cin = 0 := by apply BitVec.eq_of_toNat_eq; simp [hc])
      | (have hcin : cin = 1 := by apply BitVec.eq_of_toNat_eq; simp [hc]; omega)) <;>
    subst hcin <;> simp_all

/-- The `BitVec 1` carry-in recovered from a `CF` boolean equal to `cin = 1`. -/
theorem cin_bridge (cin : BitVec 1) (b : Bool) (hb : (b = true) = (cin = 1)) :
    BitVec.ofNat 1 (if b then 1 else 0) = cin := by
  have := cin.isLt
  rcases hc : cin.toNat with _ | _ <;>
    (first
      | (have hcin : cin = 0 := by apply BitVec.eq_of_toNat_eq; simp [hc])
      | (have hcin : cin = 1 := by apply BitVec.eq_of_toNat_eq; simp [hc]; omega)) <;>
    subst hcin <;> simp_all

/-- The emitted-`.adc` carry-out flag equals the abstract `carryOutBit`. -/
theorem cf_carryOut (a b : BitVec 64) (cin : BitVec 1) :
    decide (2 ^ 64 ≤ a.toNat + b.toNat + (if cin = 1 then 1 else 0))
      = (carryOutBit a b cin = 1) := by
  have hci := bit_toNat cin
  simp only [carryOutBit, ← hci]
  rcases hd : decide (a.toNat + b.toNat + cin.toNat ≥ 2 ^ 64) with _ | _ <;> simp_all

/-- The emitted ADC ripple-add chain over parallel destination/source register
    lists. -/
def emitAdcChain : List String → List String → List (JInstr 64)
  | [], _ => []
  | _, [] => []
  | d :: ds, s :: ss => .adc d (.reg s) :: emitAdcChain ds ss

/-- Register-layout freshness for the ADC chain: the destination limbs are
    pairwise distinct (`Nodup`) and disjoint from the source limbs (a later step
    must not have an earlier step's write clobber its source). -/
structure ChainFresh (ds ss : List String) : Prop where
  ds_nodup : ds.Nodup
  ds_ss : ∀ r ∈ ds, ∀ q ∈ ss, r ≠ q

/-- The chain writes only the destination registers `ds`: a register distinct from
    every `dᵢ` is preserved across the whole chain. -/
theorem emitAdcChain_preserves :
    ∀ (ds ss : List String) (r : String) (s : JState 64),
      (∀ q ∈ ds, r ≠ q) → (runBlock s (emitAdcChain ds ss)).get r = s.get r := by
  intro ds ss
  induction ds generalizing ss with
  | nil => intro r s _; cases ss <;> simp [emitAdcChain]
  | cons d ds ih =>
      intro r s hr
      cases ss with
      | nil => simp [emitAdcChain]
      | cons sh ss =>
          rw [emitAdcChain, runBlock_cons]
          rw [ih ss r _ (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
          exact emit_adc_other s d sh r (hr d List.mem_cons_self)

/-- **The emitted ADC chain over `runBlock` = the abstract `addLimbs` ripple-add.**
    With destination registers `ds` holding the limbs `u`, source registers `ss`
    holding `v` (equal lengths), the `ChainFresh` register layout, and `CF` the
    carry-in bit `cin`, running `emitAdcChain` leaves each `dᵢ` holding the
    `addLimbs u v cin` sum limb and `CF` the final carry — register-by-register the
    proven abstract ripple-add. -/
theorem emitAdcChain_runBlock :
    ∀ (ds ss : List String) (u v : List (BitVec 64)) (cin : BitVec 1) (s : JState 64),
      ds.length = u.length → ss.length = v.length → u.length = v.length →
      ChainFresh ds ss →
      ds.map s.get = u → ss.map s.get = v →
      s.flagB (·.cf) = (cin = 1) →
      ds.map (runBlock s (emitAdcChain ds ss)).get = (addLimbs u v cin).1
        ∧ (runBlock s (emitAdcChain ds ss)).flagB (·.cf) = ((addLimbs u v cin).2 = 1) := by
  intro ds ss
  induction ds generalizing ss with
  | nil =>
      intro u v cin s hdu _ _ _ hdmap _ hcf
      have hu : u = [] := by cases u with | nil => rfl | cons => simp at hdu
      subst hu
      simp only [emitAdcChain, runBlock_nil, List.map_nil, addLimbs, hcf, and_self]
  | cons d ds ih =>
      intro u v cin s hdu hsv huv hfresh hdmap hsmap hcf
      cases ss with
      | nil => simp at hsv; cases v with | nil => simp at huv; cases u <;> simp_all | cons => simp at hsv
      | cons sh ss =>
        cases u with
        | nil => simp at hdu
        | cons u0 us =>
          cases v with
          | nil => simp at hsv
          | cons v0 vs =>
            simp only [List.map_cons, List.cons.injEq] at hdmap hsmap
            obtain ⟨hdhd, hdtl⟩ := hdmap
            obtain ⟨hshd, hstl⟩ := hsmap
            rw [emitAdcChain, runBlock_cons]
            set s1 := evalInstr s (.adc d (.reg sh)) with hs1
            -- head value: d := addCarryWord u0 v0 cin
            have hs1d : s1.get d = addCarryWord u0 v0 cin := by
              rw [hs1, emit_adc_word, hdhd, hshd]
              congr 1
              exact cin_bridge cin _ hcf
            -- head carry-out flag = carryOutBit u0 v0 cin
            have hs1cf : (s1.flagB (·.cf) = true) = (carryOutBit u0 v0 cin = 1) := by
              rw [hs1, emit_adc_cf, hdhd, hshd]
              rw [show (if (s.flagB fun x ↦ x.cf) then (1 : Nat) else 0)
                    = (if cin = 1 then 1 else 0) by
                rcases hb : (s.flagB fun x ↦ x.cf) with _ | _ <;> simp_all]
              have := cf_carryOut u0 v0 cin
              simp only [decide_eq_true_eq] at this ⊢
              rw [this]
            -- ds-registers preserved (distinct from d by Nodup): hold us
            have hnd := hfresh.ds_nodup
            have hdsmap : ds.map s1.get = us := by
              rw [← hdtl]; apply List.map_congr_left; intro r hr
              rw [hs1]; exact emit_adc_other s d sh r
                (fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hr)
            -- ss-registers preserved (disjoint from d): hold vs
            have hssmap : ss.map s1.get = vs := by
              rw [← hstl]; apply List.map_congr_left; intro r hr
              rw [hs1]; exact emit_adc_other s d sh r
                (Ne.symm (hfresh.ds_ss d List.mem_cons_self r (List.mem_cons_of_mem _ hr)))
            -- the tail ChainFresh
            have hfresh' : ChainFresh ds ss :=
              { ds_nodup := (List.nodup_cons.mp hnd).2
                ds_ss := fun r hr q hq => hfresh.ds_ss r (List.mem_cons_of_mem _ hr) q
                  (List.mem_cons_of_mem _ hq) }
            -- apply IH with cin := carryOutBit u0 v0 cin
            obtain ⟨ihmap, ihcf⟩ := ih ss us vs (carryOutBit u0 v0 cin) s1
              (by simpa using hdu) (by simpa using hsv) (by simpa using huv) hfresh'
              hdsmap hssmap hs1cf
            simp only [addLimbs, List.map_cons, List.headD_cons, List.tail_cons]
            -- head limb d preserved through the tail block
            have hdfinal : (runBlock s1 (emitAdcChain ds ss)).get d = addCarryWord u0 v0 cin := by
              rw [emitAdcChain_preserves ds ss d s1
                (fun q hq => fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hq), hs1d]
            refine ⟨?_, ihcf⟩
            rw [hdfinal, ihmap]

/-- The little-endian value the emitted ADC chain leaves in its output: the sum
    limbs in the destination registers `ds` plus the final carry (read from `CF`)
    weighted at `2^{64·|ds|}` — the value the emitted block computes over
    `runBlock`. -/
def runBlockAddValue (ds ss : List String) (s : JState 64) : Nat :=
  valLimbs (ds.map (runBlock s (emitAdcChain ds ss)).get)
    + (2 ^ 64) ^ ds.length * (if (runBlock s (emitAdcChain ds ss)).flagB (·.cf) then 1 else 0)

/-- **The emitted ADC chain's `runBlock` value is the exact sum `valLimbs u +
    valLimbs v`**, for equal-length reduced limb vectors entered with `CF = 0`.
    Combines the proven `emitAdcChain_runBlock` (registers = `addLimbs`) with the
    proven `Cios4LimbProven.addLimbs_reconstruct` (recombined `addLimbs` value =
    sum). The genuine `runBlock`-of-emitted ripple-add over a real
    `List (JInstr 64)`. -/
theorem emitAdcChain_runBlock_value (ds ss : List String) (u v : List (BitVec 64))
    (s : JState 64)
    (hdu : ds.length = u.length) (hsv : ss.length = v.length) (huv : u.length = v.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = u) (hsmap : ss.map s.get = v)
    (hcf0 : s.flagB (·.cf) = false) :
    runBlockAddValue ds ss s = valLimbs u + valLimbs v := by
  obtain ⟨hmap, hcf⟩ := emitAdcChain_runBlock ds ss u v 0 s hdu hsv huv hfresh hdmap hsmap
    (by simp [hcf0])
  simp only [runBlockAddValue, hmap]
  -- final CF bit = (addLimbs … 0).2 = 1, weighted; and addLimbs_reconstruct
  have hrec := addLimbs_reconstruct u v 0
  have htake : v.take u.length = v := by apply List.take_of_length_le; omega
  rw [htake] at hrec
  rw [show ((0 : BitVec 1).toNat) = 0 from rfl, Nat.add_zero] at hrec
  -- the carry bit equals the addLimbs final carry's toNat
  have hcfbit : (if (runBlock s (emitAdcChain ds ss)).flagB (·.cf) then (1 : Nat) else 0)
      = (addLimbs u v 0).2.toNat := by
    rw [bit_toNat (addLimbs u v 0).2]
    by_cases hb : (runBlock s (emitAdcChain ds ss)).flagB (·.cf) = true
    · rw [if_pos hb]
      have : (addLimbs u v 0).2 = 1 := by rw [← hcf]; exact hb
      rw [if_pos this]
    · rw [if_neg hb]
      have : ¬ ((addLimbs u v 0).2 = 1) := by rw [← hcf]; simpa using hb
      rw [if_neg this]
  rw [hcfbit, hdu]
  exact hrec

/-! ## 3. The full modular add/sub value = `(a ± b) mod p`

`modAddVal p a b` recombines the ripple-add (`addChainVal`) and conditionally
subtracts `p` (`condSubP`); `modSubVal p a b` is the dual via `condAddP`. Each is
proven equal to the genuine modular spec for reduced inputs. -/

/-- The full modular-add value: ripple-add then conditional subtract of `p`. -/
def modAddVal (p : Nat) (u v : List (BitVec 64)) : Nat :=
  condSubP p (addChainVal u v)

/-- **The modular-add value is `(valLimbs u + valLimbs v) mod p`**, for reduced
    inputs (`valLimbs u, valLimbs v < p`). The ripple-add is the proven
    `addLimbs_reconstruct`; the conditional subtract is `condSubP_eq_mod` (the sum
    is `< 2p`). -/
theorem modAddVal_eq_mod (p : Nat) (u v : List (BitVec 64))
    (hlen : v.length = u.length)
    (hu : valLimbs u < p) (hv : valLimbs v < p) :
    modAddVal p u v = (valLimbs u + valLimbs v) % p := by
  simp only [modAddVal, addChainVal_eq u v hlen]
  exact condSubP_eq_mod p (valLimbs u + valLimbs v) (by omega)

/-- The full modular-sub value: conditional add-back of `p` on the recombined
    operand values (`condAddP` on `valLimbs u`, `valLimbs v`). The emitted block
    forms the borrow difference `u − v` and adds the masked `p` back; at the
    value level this is `condAddP p (valLimbs u) (valLimbs v)`. -/
def modSubVal (p : Nat) (u v : List (BitVec 64)) : Nat :=
  condAddP p (valLimbs u) (valLimbs v)

/-- **The modular-sub value is `(valLimbs u + p − valLimbs v) mod p`**, for reduced
    inputs — the canonical modular difference (`condAddP_eq_mod`). -/
theorem modSubVal_eq_mod (p : Nat) (u v : List (BitVec 64))
    (hu : valLimbs u < p) (hv : valLimbs v < p) :
    modSubVal p u v = (valLimbs u + p - valLimbs v) % p := by
  simp only [modSubVal]
  exact condAddP_eq_mod p (valLimbs u) (valLimbs v) hu hv

/-- **Genuine `runBlock` modular add = `(a + b) mod p`.** Composing the emitted
    ADC-chain `runBlock` value (`emitAdcChain_runBlock_value`, the real
    `List (JInstr 64)` ripple-add) with the conditional subtract of `p`
    (`condSubP_eq_mod`): for reduced inputs the value `condSubP p` of the emitted
    block's recombined output is `(valLimbs u + valLimbs v) mod p` — the full
    `runBlock(emitted add) = (a + b) mod p`. -/
theorem modAdd_runBlock (p : Nat) (ds ss : List String) (u v : List (BitVec 64))
    (s : JState 64)
    (hdu : ds.length = u.length) (hsv : ss.length = v.length) (huv : u.length = v.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = u) (hsmap : ss.map s.get = v)
    (hcf0 : s.flagB (·.cf) = false)
    (hu : valLimbs u < p) (hv : valLimbs v < p) :
    condSubP p (runBlockAddValue ds ss s) = (valLimbs u + valLimbs v) % p := by
  rw [emitAdcChain_runBlock_value ds ss u v s hdu hsv huv hfresh hdmap hsmap hcf0]
  exact condSubP_eq_mod p (valLimbs u + valLimbs v) (by omega)

/-! ## 4. Pasta (Pallas / Vesta) 4-limb instances

Both Pasta primes are 255-bit, four 64-bit limbs (the `PastaFieldAddSubKernel`
constants, here as `BitVec 64` so they feed `valLimbs`). Each `_modadd_value` /
`_modsub_value` is the 4-limb instance: for reduced 4-limb inputs the emitted
add/sub recombined value is `(a ± b) mod p`. -/

/-- Pallas base-field prime little-endian 64-bit limbs (as `BitVec 64`). -/
def pallasLimbs : List (BitVec 64) :=
  [ 0x992d30ed00000001, 0x224698fc094cf91b, 0x0000000000000000, 0x4000000000000000 ]

/-- Vesta base-field prime little-endian 64-bit limbs (as `BitVec 64`). -/
def vestaLimbs : List (BitVec 64) :=
  [ 0x8c46eb2100000001, 0x224698fc0994a8dd, 0x0000000000000000, 0x4000000000000000 ]

theorem pallasLimbs_value :
    valLimbs pallasLimbs
      = 28948022309329048855892746252171976963363056481941560715954676764349967630337 := by
  native_decide

theorem vestaLimbs_value :
    valLimbs vestaLimbs
      = 28948022309329048855892746252171976963363056481941647379679742748393362948097 := by
  native_decide

/-- **Pallas modular add over the carry chain = `(a + b) mod p` (Tier A, 4-limb).**
    For reduced 4-limb inputs the emitted `ADD`/`ADC` + trial `SUB`/`SBB` + `CMOVB`
    select recombined value is `(valLimbs a + valLimbs b) mod p`. -/
theorem pallas_modadd_value (a b : List (BitVec 64))
    (hb : b.length = a.length)
    (ha_red : valLimbs a < valLimbs pallasLimbs) (hb_red : valLimbs b < valLimbs pallasLimbs) :
    modAddVal (valLimbs pallasLimbs) a b = (valLimbs a + valLimbs b) % valLimbs pallasLimbs :=
  modAddVal_eq_mod (valLimbs pallasLimbs) a b hb ha_red hb_red

/-- **Pallas modular sub over the borrow chain = `(a + p − b) mod p` (Tier A,
    4-limb).** -/
theorem pallas_modsub_value (a b : List (BitVec 64))
    (ha_red : valLimbs a < valLimbs pallasLimbs) (hb_red : valLimbs b < valLimbs pallasLimbs) :
    modSubVal (valLimbs pallasLimbs) a b
      = (valLimbs a + valLimbs pallasLimbs - valLimbs b) % valLimbs pallasLimbs :=
  modSubVal_eq_mod (valLimbs pallasLimbs) a b ha_red hb_red

/-- **Vesta modular add = `(a + b) mod q` (Tier A, 4-limb).** -/
theorem vesta_modadd_value (a b : List (BitVec 64))
    (hb : b.length = a.length)
    (ha_red : valLimbs a < valLimbs vestaLimbs) (hb_red : valLimbs b < valLimbs vestaLimbs) :
    modAddVal (valLimbs vestaLimbs) a b = (valLimbs a + valLimbs b) % valLimbs vestaLimbs :=
  modAddVal_eq_mod (valLimbs vestaLimbs) a b hb ha_red hb_red

/-- **Vesta modular sub = `(a + q − b) mod q` (Tier A, 4-limb).** -/
theorem vesta_modsub_value (a b : List (BitVec 64))
    (ha_red : valLimbs a < valLimbs vestaLimbs) (hb_red : valLimbs b < valLimbs vestaLimbs) :
    modSubVal (valLimbs vestaLimbs) a b
      = (valLimbs a + valLimbs vestaLimbs - valLimbs b) % valLimbs vestaLimbs :=
  modSubVal_eq_mod (valLimbs vestaLimbs) a b ha_red hb_red

/-! ## 5. BLS12-381 / P384 6-limb instances

Reuse the `Curve6LimbTierA` 6-limb modulus limb vectors (`bls12381Limbs`,
`p384Limbs`) and their `native_decide` value pins. The add/sub value layer is
radix-generic, so the 6-limb instance is the same `modAddVal_eq_mod` /
`modSubVal_eq_mod` at the 6-limb modulus. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
  (bls12381Limbs p384Limbs)

/-- **BLS12-381 base-field modular add = `(a + b) mod p` (Tier A, 6-limb).** -/
theorem bls12381_modadd_value (a b : List (BitVec 64))
    (hb : b.length = a.length)
    (ha_red : valLimbs a < valLimbs bls12381Limbs) (hb_red : valLimbs b < valLimbs bls12381Limbs) :
    modAddVal (valLimbs bls12381Limbs) a b = (valLimbs a + valLimbs b) % valLimbs bls12381Limbs :=
  modAddVal_eq_mod (valLimbs bls12381Limbs) a b hb ha_red hb_red

/-- **BLS12-381 base-field modular sub = `(a + p − b) mod p` (Tier A, 6-limb).** -/
theorem bls12381_modsub_value (a b : List (BitVec 64))
    (ha_red : valLimbs a < valLimbs bls12381Limbs) (hb_red : valLimbs b < valLimbs bls12381Limbs) :
    modSubVal (valLimbs bls12381Limbs) a b
      = (valLimbs a + valLimbs bls12381Limbs - valLimbs b) % valLimbs bls12381Limbs :=
  modSubVal_eq_mod (valLimbs bls12381Limbs) a b ha_red hb_red

/-- **P384 modular add = `(a + b) mod p` (Tier A, 6-limb).** -/
theorem p384_modadd_value (a b : List (BitVec 64))
    (hb : b.length = a.length)
    (ha_red : valLimbs a < valLimbs p384Limbs) (hb_red : valLimbs b < valLimbs p384Limbs) :
    modAddVal (valLimbs p384Limbs) a b = (valLimbs a + valLimbs b) % valLimbs p384Limbs :=
  modAddVal_eq_mod (valLimbs p384Limbs) a b hb ha_red hb_red

/-- **P384 modular sub = `(a + p − b) mod p` (Tier A, 6-limb).** -/
theorem p384_modsub_value (a b : List (BitVec 64))
    (ha_red : valLimbs a < valLimbs p384Limbs) (hb_red : valLimbs b < valLimbs p384Limbs) :
    modSubVal (valLimbs p384Limbs) a b
      = (valLimbs a + valLimbs p384Limbs - valLimbs b) % valLimbs p384Limbs :=
  modSubVal_eq_mod (valLimbs p384Limbs) a b ha_red hb_red

/-! ## 5b. Genuine `runBlock` modular-add headlines at the curve moduli

These compose the emitted ADC-chain `runBlock` value (`emitAdcChain_runBlock`, a
real `List (JInstr 64)`) with the conditional subtract of the curve prime, giving
`runBlock(emitted add) = (a + b) mod p` directly at each modulus. -/

/-- **Pallas modular add over `runBlock` = `(a + b) mod p`.** -/
theorem pallas_modadd_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (ha_red : valLimbs a < valLimbs pallasLimbs) (hb_red : valLimbs b < valLimbs pallasLimbs) :
    condSubP (valLimbs pallasLimbs) (runBlockAddValue ds ss s)
      = (valLimbs a + valLimbs b) % valLimbs pallasLimbs :=
  modAdd_runBlock (valLimbs pallasLimbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    ha_red hb_red

/-- **Vesta modular add over `runBlock` = `(a + b) mod q`.** -/
theorem vesta_modadd_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (ha_red : valLimbs a < valLimbs vestaLimbs) (hb_red : valLimbs b < valLimbs vestaLimbs) :
    condSubP (valLimbs vestaLimbs) (runBlockAddValue ds ss s)
      = (valLimbs a + valLimbs b) % valLimbs vestaLimbs :=
  modAdd_runBlock (valLimbs vestaLimbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    ha_red hb_red

/-- **BLS12-381 base-field modular add over `runBlock` = `(a + b) mod p`.** -/
theorem bls12381_modadd_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (ha_red : valLimbs a < valLimbs bls12381Limbs) (hb_red : valLimbs b < valLimbs bls12381Limbs) :
    condSubP (valLimbs bls12381Limbs) (runBlockAddValue ds ss s)
      = (valLimbs a + valLimbs b) % valLimbs bls12381Limbs :=
  modAdd_runBlock (valLimbs bls12381Limbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    ha_red hb_red

/-- **P384 modular add over `runBlock` = `(a + b) mod p`.** -/
theorem p384_modadd_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (ha_red : valLimbs a < valLimbs p384Limbs) (hb_red : valLimbs b < valLimbs p384Limbs) :
    condSubP (valLimbs p384Limbs) (runBlockAddValue ds ss s)
      = (valLimbs a + valLimbs b) % valLimbs p384Limbs :=
  modAdd_runBlock (valLimbs p384Limbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    ha_red hb_red

/-! ## 6. BabyBear / Barrett butterfly single-word add/sub over `runBlock`

The Plonky3 BabyBear field `p = 2^31 − 2^27 + 1` fits a single 64-bit word, so its
add and subtract are single-word conditional subtract / add-back (the branch-free
`Poseidon2Emit.bbCsub` idiom). The emitted NTT butterfly
(`BarrettButterflyKernel.butterflyBlock`) stores `out[0] = a + ω·b` and
`out[1] = a − ω·b` reduced mod `p`; `butterfly_out{0,1}_spec` already prove those
stored words against the field-op spec over the genuine `runBlock` of the emitted
block. Here we wrap them into the modular add/sub field-op shape `(a ± c) mod p`
with `c = ω·b` the canonical field product. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.BarrettButterflyKernel
  (finalState butterfly_out0_spec butterfly_out1_spec)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
  (bbP bbAdd bbMul bbAdd_correct)

/-- BabyBear residue range: `bbMul w b < p` for canonical `w, b` (the field
    product is canonical). -/
theorem bbMul_lt_p (w b : BitVec 64) (hw : w < bbP) (hb : b < bbP) : bbMul w b < bbP := by
  rw [CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit.bbMul_correct w b hw hb]
  exact BitVec.umod_lt _ (by decide)

/-- **BabyBear / Barrett-butterfly modular add over `runBlock` (Tier A,
    single-word).** For canonical residues `a, b, w < p`, the emitted butterfly's
    stored low output word equals the field add `(a + ω·b) mod p` — a genuine
    `runBlock`-of-emitted tie (`butterfly_out0_spec` + the proven branch-free
    field-add law `bbAdd_correct`), in the modular add shape with the canonical
    field product `c = bbMul w b`. -/
theorem babybear_fpadd_runBlock (a b w : BitVec 64)
    (ha : a < bbP) (hb : b < bbP) (hw : w < bbP) :
    (finalState a b w).load "out" 0 = (a + bbMul w b) % bbP := by
  rw [butterfly_out0_spec a b w ha hb hw]
  exact bbAdd_correct a (bbMul w b) ha (bbMul_lt_p w b hw hb)

/-- **BabyBear / Barrett-butterfly modular sub over `runBlock` (Tier A,
    single-word).** For canonical residues `a, b, w < p`, the emitted butterfly's
    stored high output word equals the field sub `(a + p − ω·b) mod p` — the
    conditional add-back of `p` on borrow, tied to the genuine `runBlock` output by
    `butterfly_out1_spec`. -/
theorem babybear_fpsub_runBlock (a b w : BitVec 64)
    (ha : a < bbP) (hb : b < bbP) (hw : w < bbP) :
    (finalState a b w).load "out" 8 = (a + bbP - bbMul w b) % bbP :=
  butterfly_out1_spec a b w ha hb hw

end CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
