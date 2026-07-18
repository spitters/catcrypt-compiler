/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

/-!
# Tier-A modular field SUBTRACT: the emitted SBB borrow chain over `runBlock`

`FieldAddSubTierA` proves the modular **add** is a genuine `runBlock`-of-emitted
statement (`emitAdcChain` over `runBlock` = `addLimbs`, recombined and
canonicalised by `condSubP`), but leaves the emitted SUB/SBB borrow chain as the
named remainder for the 4-limb / 6-limb curves. This file discharges that
remainder: the SBB borrow-chain analogue of `emitAdcChain_runBlock`.

The arithmetic is the genuine modular subtract over `Nat`: for canonical inputs
`a, b ∈ [0, p)` the difference `a − b` lies in `(−p, p)`, so a single conditional
**add-back** of `p` on the final borrow canonicalises (`condAddP`, already proven
`= (a + p − b) % p` in `FieldAddSubTierA`).

## What is PROVEN here

1. **`.sub` / `.sbb` ALU bridges** (`emit_sub_word/cf/other`, `emit_sbb_word/cf/other`)
   from `evalInstr` / `x86_SUB` / `x86_SBB`, the borrow-chain mirror of the add
   side's `emit_add_*` / `emit_adc_*`. The `CF` arms expose the borrow predicate
   `decide (a < b (+ borrow-in))`.

2. **`subBorrowWord` / `borrowOutBit`** — the abstract borrow primitives
   (`a − b − bin`, and the borrow flag `a < b + bin`), with `subb_recon` the
   per-word reconstruction `diff + (b + bin) = a + borrow · 2^64` (the borrow
   analogue of `Cios4LimbProven.addc_recon`), and the bridges
   `emit_sbb_word_abs` / `emit_sbb_cf_abs` tying the emitted SBB data/flag to them.

3. **`subLimbs` / `subLimbs_reconstruct`** — the multi-limb ripple-subtract over
   the borrow chain (difference limbs + final borrow), with the additive
   reconstruction `valLimbs diff + valLimbs (v.take |u|) + bin =
   valLimbs u + finalBorrow · 2^{64·|u|}` — the `addLimbs_reconstruct` dual.

4. **`emitSbbChain` / `emitSbbChain_runBlock`** — a genuine emitted SBB chain
   `[.sbb d₀ s₀, .sbb d₁ s₁, …]` (`List (JInstr 64)`) proven register-by-register
   over `runBlock` to equal `subLimbs` (each step the `.sbb` semantics of
   `evalInstr`, no abstraction gap), the SBB mirror of `emitAdcChain_runBlock`.

5. **`<curve>_modsub_runBlock`** — for Pasta (Pallas/Vesta, 4-limb), BLS12-381 and
   P384 (6-limb): the emitted SUB/SBB borrow chain over `runBlock`, recombined and
   canonicalised by the conditional add-back of `p` (`condAddP_eq_mod`), equals
   `(a − b) mod p` = `(a + p − b) % p` for reduced inputs. The full
   `runBlock(emitted sub) = (a − b) mod p`, the sub-side completion of the add
   side's `<curve>_modadd_runBlock`.

## Scope (honest)

`emitSbbChain` is a real `List (JInstr 64)` and `emitSbbChain_runBlock` proves it
computes the abstract `subLimbs` over `runBlock`, each step the genuine `.sbb` ALU
semantics of `evalInstr`. The reconstruction `subLimbs_reconstruct` is the
borrow-chain dual of the proven `addLimbs_reconstruct`. The conditional add-back
of `p` is `FieldAddSubTierA.condAddP`, proven `= (a + p − b) % p`. The
recombined-value layer is the same `valLimbs` codec the add side and
`Cios4LimbProven` use. The emit tie (`Com → Lprog → .s`) remains the repo-wide
`LprogExportFaithful` trust boundary, unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

/-! ## 1. The abstract borrow primitives and their reconstruction

`subBorrowWord a b bin = a − b − bin` (BitVec wrapping) is the data word an
`SBB`/`SUB` step writes; `borrowOutBit a b bin = if a < b + bin then 1 else 0` is
the borrow it sets in `CF`. The reconstruction `subb_recon` is the additive
identity `diff + (b + bin) = a + borrow · 2^64` (the borrow dual of
`Cios4LimbProven.addc_recon`). -/

/-- The data word of one borrow-chain subtract `a − b − bin` at width 64 (`a - b -
    bin` over the two's-complement word). The `SBB`/`SUB`-with-borrow data result. -/
def subBorrowWord (a b : BitVec 64) (bin : BitVec 1) : BitVec 64 :=
  a - b - BitVec.ofNat 64 bin.toNat

/-- The borrow-out bit of `a − b − bin`: `1` iff `a < b + bin` (the subtraction
    went negative and borrowed from the next limb). The `CF` an `SBB`/`SUB` sets. -/
def borrowOutBit (a b : BitVec 64) (bin : BitVec 1) : BitVec 1 :=
  if a.toNat < b.toNat + bin.toNat then 1 else 0

/-- The borrow-out bit is `0` or `1`. -/
theorem borrowOutBit_le_one (a b : BitVec 64) (bin : BitVec 1) :
    (borrowOutBit a b bin).toNat ≤ 1 := by
  simp only [borrowOutBit]; split <;> simp

/-- **SBB reconstruction (general borrow-in).** One borrow-chain subtract
    `subBorrowWord a b bin` with its borrow-out `borrowOutBit a b bin` recombines
    additively to `a + borrow · 2^64 = diff + b + bin`. The borrow dual of
    `Cios4LimbProven.addc_recon`. -/
theorem subb_recon (a b : BitVec 64) (bin : BitVec 1) :
    (subBorrowWord a b bin).toNat + (b.toNat + bin.toNat)
      = a.toNat + (borrowOutBit a b bin).toNat * 2 ^ 64 := by
  have ha := a.isLt; have hb := b.isLt
  have hbin : bin.toNat ≤ 1 := by have := bin.isLt; omega
  simp only [subBorrowWord, borrowOutBit]
  -- The inner word `a - b` and then `- bin`, each a `BitVec.toNat_sub` wrap.
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show bin.toNat < 2 ^ 64 by omega)]
  -- Evaluate the inner `(a - b)` word once, by cases on `a < b`.
  have hinner : (2 ^ 64 - b.toNat + a.toNat) % 2 ^ 64
      = if a.toNat < b.toNat then 2 ^ 64 + a.toNat - b.toNat else a.toNat - b.toNat := by
    by_cases hab : a.toNat < b.toNat
    · rw [if_pos hab, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [if_neg hab,
        show 2 ^ 64 - b.toNat + a.toNat = 2 ^ 64 + (a.toNat - b.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hinner]
  by_cases hc : a.toNat < b.toNat + bin.toNat
  · rw [if_pos hc]
    have e1 : (1 : BitVec 1).toNat = 1 := rfl
    rw [e1]
    by_cases hab : a.toNat < b.toNat
    · rw [if_pos hab,
        show 2 ^ 64 - bin.toNat + (2 ^ 64 + a.toNat - b.toNat)
            = 2 ^ 64 + (2 ^ 64 - bin.toNat + a.toNat - b.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
    · -- a ≥ b but a < b + bin ⇒ a = b, bin = 1
      rw [if_neg hab]
      rw [Nat.mod_eq_of_lt (show 2 ^ 64 - bin.toNat + (a.toNat - b.toNat) < 2 ^ 64 by omega)]
      omega
  · rw [if_neg hc]
    have e0 : (0 : BitVec 1).toNat = 0 := rfl
    rw [e0]
    have hab : ¬ a.toNat < b.toNat := by omega
    rw [if_neg hab]
    -- no borrow: a ≥ b + bin, so 2^64 - bin + (a - b) ≥ 2^64 and wraps once.
    rw [show 2 ^ 64 - bin.toNat + (a.toNat - b.toNat)
          = 2 ^ 64 + (a.toNat - b.toNat - bin.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-! ## 2. The `.sub` / `.sbb` ALU bridges from `evalInstr`

The borrow-chain mirror of the add side's `emit_add_*` / `emit_adc_*`: one emitted
`SUB`/`SBB` step writes the borrow-subtract data word into `dst`, sets `CF` to the
borrow predicate, and preserves every other register. -/

/-- For an integer `z` in `[−2^64, 2^64)`, the unsigned read-back of `ofInt 64 z`
    equals `z` exactly iff `z ≥ 0` (no borrow); otherwise it is `z + 2^64`. The
    sign-detection fact underlying the SUB/SBB `CF` (borrow) flag. -/
theorem ofInt_toNat_borrow (z : Int) (hlo : -(2 ^ 64 : Int) ≤ z) (hhi : z < 2 ^ 64) :
    (((BitVec.ofInt 64 z).toNat : Int) = z) ↔ 0 ≤ z := by
  rw [BitVec.toNat_ofInt]
  have hcast : ((2 ^ 64 : Nat) : Int) = (2 ^ 64 : Int) := by norm_cast
  rw [hcast]
  constructor
  · intro h
    by_contra hneg
    rw [Int.not_le] at hneg
    -- z % 2^64 = z + 2^64 ∈ [0, 2^64); its toNat is z + 2^64 ≠ z
    have hmod : z % (2 ^ 64 : Int) = z + 2 ^ 64 := by
      conv_lhs => rw [show z = (z + 2 ^ 64) - 2 ^ 64 by ring]
      rw [Int.sub_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hmod] at h
    have : ((z + 2 ^ 64).toNat : Int) = z + 2 ^ 64 := Int.toNat_of_nonneg (by omega)
    omega
  · intro hpos
    have hmod : z % (2 ^ 64 : Int) = z := Int.emod_eq_of_lt hpos hhi
    rw [hmod, Int.toNat_of_nonneg hpos]

/-- One emitted SUB step writes the wrapped difference `dst − src` into `dst`. -/
theorem emit_sub_word (s : JState 64) (dst src : String) :
    (evalInstr s (.sub dst (.reg src))).get dst = s.get dst - s.get src := by
  simp only [evalInstr, JState.get, JState.writeB5W, x86_SUB, JOperand.eval]
  simp

/-- One emitted SUB step sets `CF` to the borrow predicate `dst < src`. -/
theorem emit_sub_cf (s : JState 64) (dst src : String) :
    (evalInstr s (.sub dst (.reg src))).flagB (·.cf)
      = decide ((s.get dst).toNat < (s.get src).toNat) := by
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_SUB, JOperand.eval,
    wunsigned, Option.getD_some]
  -- CF = ((dst-src).toNat : ℤ) ≠ (dst.toNat - src.toNat : ℤ), the borrow.
  rw [decide_eq_decide]
  -- via the proven no-borrow iff: src ≤ dst ↔ no wrap.
  have hnb := noborrow_sub_iff (s.get dst) (s.get src)
  constructor
  · intro h; by_contra hc
    rw [Nat.not_lt] at hc
    exact h ((hnb.mpr hc).symm)
  · intro h heq
    exact absurd (hnb.mp heq.symm) (by omega)

/-- One emitted SUB step writes only `dst`: any other register is preserved. -/
theorem emit_sub_other (s : JState 64) (dst src r : String) (hr : r ≠ dst) :
    (evalInstr s (.sub dst (.reg src))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-- `subBorrowWord` is exactly Jasmin's `sub_borrow` at the same borrow-in: both
    are the two's-complement `a − b − c` word. -/
theorem subBorrowWord_eq_sub_borrow (a b : BitVec 64) (c : Nat) :
    subBorrowWord a b (BitVec.ofNat 1 c) = sub_borrow a b (BitVec.ofNat 1 c).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [subBorrowWord, sub_borrow, BitVec.toNat_sub, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat]
  -- both reduce to (a − b − c') mod 2^64 with c' = c % 2
  push_cast
  omega

/-- One emitted SBB step writes `subBorrowWord dst src (CF-bit)` into `dst`. -/
theorem emit_sbb_word (s : JState 64) (dst src : String) :
    (evalInstr s (.sbb dst (.reg src))).get dst
      = subBorrowWord (s.get dst) (s.get src)
          (BitVec.ofNat 1 (if s.flagB (·.cf) then 1 else 0)) := by
  rw [subBorrowWord_eq_sub_borrow]
  simp only [evalInstr, JState.get, JState.writeB5W, x86_SBB, JOperand.eval]
  rcases h : s.flagB (·.cf) with _ | _ <;> simp

/-- One emitted SBB step sets `CF` to the borrow-out of `dst − src − CF-in`,
    i.e. `dst < src + CF-in`. -/
theorem emit_sbb_cf (s : JState 64) (dst src : String) :
    (evalInstr s (.sbb dst (.reg src))).flagB (·.cf)
      = decide ((s.get dst).toNat < (s.get src).toNat
          + (if s.flagB (·.cf) then 1 else 0)) := by
  have hd := (s.get dst).isLt; have hsrc := (s.get src).isLt
  -- Unfold the SBB step; the carry-in bit is the only flag dependence. Split on
  -- the concrete `CF` value (the `Option` cell) so every `if` collapses.
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_SBB, sub_borrow,
    JOperand.eval, wunsigned, Option.getD_some]
  rw [decide_eq_decide]
  by_cases hc : (Option.getD s.flags.cf false : Bool) = true
  · -- carry-in 1
    simp only [if_pos hc, Nat.cast_one, ne_eq]
    rw [show ((s.get dst).toNat : Int) - ↑(s.get src).toNat - 1
          = ((s.get dst).toNat : Int) - (↑(s.get src).toNat + 1) by ring,
      ofInt_toNat_borrow _ (by push_cast; omega) (by push_cast; omega)]
    omega
  · -- carry-in 0
    simp only [if_neg hc, Nat.cast_zero, sub_zero, Nat.add_zero, ne_eq]
    rw [show ((s.get dst).toNat : Int) - ↑(s.get src).toNat
          = ((s.get dst).toNat : Int) - (↑(s.get src).toNat + 0) by ring,
      ofInt_toNat_borrow _ (by push_cast; omega) (by push_cast; omega)]
    omega

/-- One emitted SBB step writes only `dst`: any other register is preserved. -/
theorem emit_sbb_other (s : JState 64) (dst src r : String) (hr : r ≠ dst) :
    (evalInstr s (.sbb dst (.reg src))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-! ## 3. The multi-limb ripple-subtract over the borrow chain

`subLimbs u v bin` is the limb-by-limb subtract `u − v − bin` over the
`subBorrowWord`/`borrowOutBit` chain, returning the difference limbs (length
`|u|`) and a final borrow bit. `subLimbs_reconstruct` is the additive
reconstruction `valLimbs diff + valLimbs (v.take |u|) + bin =
valLimbs u + finalBorrow · 2^{64·|u|}` — the `Cios4LimbProven.addLimbs_reconstruct`
dual. -/

/-- Ripple-subtract `u − v − borrow-in`, limb by limb over the borrow chain. -/
def subLimbs : List (BitVec 64) → List (BitVec 64) → BitVec 1 →
    (List (BitVec 64) × BitVec 1)
  | [], _, bin => ([], bin)
  | u₀ :: us, v, bin =>
      let v₀ := v.headD 0
      let d := subBorrowWord u₀ v₀ bin
      let bout := borrowOutBit u₀ v₀ bin
      let (rest, fb) := subLimbs us v.tail bout
      (d :: rest, fb)

theorem subLimbs_length (u v : List (BitVec 64)) (bin : BitVec 1) :
    (subLimbs u v bin).1.length = u.length := by
  induction u generalizing v bin with
  | nil => rfl
  | cons u₀ us ih => simp only [subLimbs, List.length_cons]; rw [ih]

/-- **Multi-limb subtract reconstruction.** When `v` is at least as long as `u`,
    the difference limbs plus the consumed `v`-prefix plus the borrow-in
    reconstruct additively to `valLimbs u + finalBorrow · 2^{64·|u|}`. Proven by
    induction over `u` via `subb_recon`, the borrow dual of
    `Cios4LimbProven.addLimbs_reconstruct`. -/
theorem subLimbs_reconstruct (u : List (BitVec 64)) :
    ∀ (v : List (BitVec 64)) (bin : BitVec 1),
      valLimbs (subLimbs u v bin).1 + valLimbs (v.take u.length) + bin.toNat
        = valLimbs u + (2 ^ 64) ^ u.length * (subLimbs u v bin).2.toNat := by
  induction u with
  | nil => intro v bin; simp [subLimbs]
  | cons u₀ us ih =>
      intro v bin
      simp only [subLimbs, List.length_cons]
      set v₀ := v.headD 0 with hv₀
      set bout := borrowOutBit u₀ v₀ bin with hbout
      have hword := subb_recon u₀ v₀ bin
      rw [← hbout] at hword
      have hrec := ih v.tail bout
      have hvsplit : valLimbs (v.take (us.length + 1))
          = v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length) := by
        cases v with
        | nil => simp [hv₀]
        | cons w ws => simp [hv₀, List.take]
      have hpow : (2 ^ 64) ^ (us.length + 1) = 2 ^ 64 * (2 ^ 64) ^ us.length := by
        rw [pow_succ]; ring
      simp only [valLimbs_cons]
      rw [hvsplit, hpow]
      -- the recursive identity (the tail block), in additive form
      set d := subBorrowWord u₀ v₀ bin with hd
      -- tail: valLimbs rest + valLimbs (vtail.take) + bout = valLimbs us + 2^{64·|us|}·fb
      -- combine: lift the head and use hword (d + v₀ + bin = u₀ + bout·2^64)
      have key : d.toNat + 2 ^ 64 * (valLimbs (subLimbs us v.tail bout).1)
            + (v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length)) + bin.toNat
          = u₀.toNat + 2 ^ 64 * valLimbs us
            + 2 ^ 64 * (2 ^ 64) ^ us.length * (subLimbs us v.tail bout).2.toNat := by
        -- from hrec (additive) multiplied by 2^64 and hword
        have hrec' : 2 ^ 64 * (valLimbs (subLimbs us v.tail bout).1
              + valLimbs (v.tail.take us.length) + bout.toNat)
            = 2 ^ 64 * (valLimbs us + (2 ^ 64) ^ us.length * (subLimbs us v.tail bout).2.toNat) := by
          rw [hrec]
        -- expand and use d + v₀ + bin = u₀ + bout·2^64
        have hcomm : 2 ^ 64 * bout.toNat = bout.toNat * 2 ^ 64 := by ring
        nlinarith [hword, hrec', hcomm]
      -- assemble the goal: it is `key` up to associativity
      calc valLimbs (d :: (subLimbs us v.tail bout).1) + (v₀.toNat
              + 2 ^ 64 * valLimbs (v.tail.take us.length)) + bin.toNat
          = d.toNat + 2 ^ 64 * (valLimbs (subLimbs us v.tail bout).1)
              + (v₀.toNat + 2 ^ 64 * valLimbs (v.tail.take us.length)) + bin.toNat := by
            simp only [valLimbs_cons]
        _ = u₀.toNat + 2 ^ 64 * valLimbs us
              + 2 ^ 64 * (2 ^ 64) ^ us.length * (subLimbs us v.tail bout).2.toNat := key

/-! ## 4. The emitted SBB chain over `runBlock` = `subLimbs`

`emitSbbChain ds ss` is the real emitted instruction list `[.sbb d₀ s₀,
.sbb d₁ s₁, …]`: each step subtracts `sᵢ` and the borrow-in `CF` from the
destination limb register `dᵢ`, leaving the borrow-out in `CF`. Entered with `CF`
the borrow-in bit, the chain leaves each `dᵢ` holding the `subLimbs` difference
limb and `CF` the final borrow — proven by induction over the register list, each
step the per-`.sbb` bridge `emit_sbb_word` / `emit_sbb_cf`. The SBB mirror of
`FieldAddSubTierA.emitAdcChain_runBlock`. -/

/-- The emitted-`.sbb` borrow-out flag equals the abstract `borrowOutBit`. -/
theorem cf_borrowOut (a b : BitVec 64) (bin : BitVec 1) :
    decide (a.toNat < b.toNat + (if bin = 1 then 1 else 0))
      = (borrowOutBit a b bin = 1) := by
  have hbin := bit_toNat bin
  simp only [borrowOutBit, ← hbin]
  rcases hd : decide (a.toNat < b.toNat + bin.toNat) with _ | _ <;> simp_all

/-- The emitted SBB ripple-subtract chain over parallel destination/source register
    lists. -/
def emitSbbChain : List String → List String → List (JInstr 64)
  | [], _ => []
  | _, [] => []
  | d :: ds, s :: ss => .sbb d (.reg s) :: emitSbbChain ds ss

/-- The chain writes only the destination registers `ds`: a register distinct from
    every `dᵢ` is preserved across the whole chain. -/
theorem emitSbbChain_preserves :
    ∀ (ds ss : List String) (r : String) (s : JState 64),
      (∀ q ∈ ds, r ≠ q) → (runBlock s (emitSbbChain ds ss)).get r = s.get r := by
  intro ds ss
  induction ds generalizing ss with
  | nil => intro r s _; cases ss <;> simp [emitSbbChain]
  | cons d ds ih =>
      intro r s hr
      cases ss with
      | nil => simp [emitSbbChain]
      | cons sh ss =>
          rw [emitSbbChain, runBlock_cons]
          rw [ih ss r _ (fun q hq => hr q (List.mem_cons_of_mem _ hq))]
          exact emit_sbb_other s d sh r (hr d List.mem_cons_self)

/-- **The emitted SBB chain over `runBlock` = the abstract `subLimbs`
    ripple-subtract.** With destination registers `ds` holding `u`, source
    registers `ss` holding `v` (equal lengths), the `ChainFresh` register layout,
    and `CF` the borrow-in bit `bin`, running `emitSbbChain` leaves each `dᵢ`
    holding the `subLimbs u v bin` difference limb and `CF` the final borrow —
    register-by-register the proven abstract ripple-subtract. The SBB mirror of
    `FieldAddSubTierA.emitAdcChain_runBlock`. -/
theorem emitSbbChain_runBlock :
    ∀ (ds ss : List String) (u v : List (BitVec 64)) (bin : BitVec 1) (s : JState 64),
      ds.length = u.length → ss.length = v.length → u.length = v.length →
      ChainFresh ds ss →
      ds.map s.get = u → ss.map s.get = v →
      s.flagB (·.cf) = (bin = 1) →
      ds.map (runBlock s (emitSbbChain ds ss)).get = (subLimbs u v bin).1
        ∧ (runBlock s (emitSbbChain ds ss)).flagB (·.cf) = ((subLimbs u v bin).2 = 1) := by
  intro ds ss
  induction ds generalizing ss with
  | nil =>
      intro u v bin s hdu _ _ _ hdmap _ hcf
      have hu : u = [] := by cases u with | nil => rfl | cons => simp at hdu
      subst hu
      simp only [emitSbbChain, runBlock_nil, List.map_nil, subLimbs, hcf, and_self]
  | cons d ds ih =>
      intro u v bin s hdu hsv huv hfresh hdmap hsmap hcf
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
            rw [emitSbbChain, runBlock_cons]
            set s1 := evalInstr s (.sbb d (.reg sh)) with hs1
            -- head value: d := subBorrowWord u0 v0 bin
            have hs1d : s1.get d = subBorrowWord u0 v0 bin := by
              rw [hs1, emit_sbb_word, hdhd, hshd]
              congr 1
              exact cin_bridge bin _ hcf
            -- head borrow-out flag = borrowOutBit u0 v0 bin
            have hs1cf : (s1.flagB (·.cf) = true) = (borrowOutBit u0 v0 bin = 1) := by
              rw [hs1, emit_sbb_cf, hdhd, hshd]
              rw [show (if (s.flagB fun x ↦ x.cf) then (1 : Nat) else 0)
                    = (if bin = 1 then 1 else 0) by
                rcases hb : (s.flagB fun x ↦ x.cf) with _ | _ <;> simp_all]
              have := cf_borrowOut u0 v0 bin
              simp only [decide_eq_true_eq] at this ⊢
              rw [this]
            have hnd := hfresh.ds_nodup
            have hdsmap : ds.map s1.get = us := by
              rw [← hdtl]; apply List.map_congr_left; intro r hr
              rw [hs1]; exact emit_sbb_other s d sh r
                (fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hr)
            have hssmap : ss.map s1.get = vs := by
              rw [← hstl]; apply List.map_congr_left; intro r hr
              rw [hs1]; exact emit_sbb_other s d sh r
                (Ne.symm (hfresh.ds_ss d List.mem_cons_self r (List.mem_cons_of_mem _ hr)))
            have hfresh' : ChainFresh ds ss :=
              { ds_nodup := (List.nodup_cons.mp hnd).2
                ds_ss := fun r hr q hq => hfresh.ds_ss r (List.mem_cons_of_mem _ hr) q
                  (List.mem_cons_of_mem _ hq) }
            obtain ⟨ihmap, ihcf⟩ := ih ss us vs (borrowOutBit u0 v0 bin) s1
              (by simpa using hdu) (by simpa using hsv) (by simpa using huv) hfresh'
              hdsmap hssmap hs1cf
            simp only [subLimbs, List.map_cons, List.headD_cons, List.tail_cons]
            have hdfinal : (runBlock s1 (emitSbbChain ds ss)).get d = subBorrowWord u0 v0 bin := by
              rw [emitSbbChain_preserves ds ss d s1
                (fun q hq => fun he => by subst he; exact (List.nodup_cons.mp hnd).1 hq), hs1d]
            refine ⟨?_, ihcf⟩
            rw [hdfinal, ihmap]

/-! ## 5. The full modular-sub value over `runBlock` = `(a − b) mod p`

The emitted SBB chain leaves the difference limbs (value `valLimbs diff`) and the
final borrow in `CF`; the kernel then conditionally **adds back** the modulus `p`
masked by that borrow. At the value level the result is `condAddP p (valLimbs a)
(valLimbs b)`: when `a ≥ b` (no borrow) the raw difference `a − b`; when `a < b`
(borrow) the wrapped `a + 2^{64n} − b` corrected by the add-back to `a + p − b`.
Either way `= (a + p − b) % p` for reduced inputs (`condAddP_eq_mod`). -/

/-- A length-`n` limb vector has value `< (2^64)^n`. -/
theorem valLimbs_lt_pow (ws : List (BitVec 64)) :
    valLimbs ws < (2 ^ 64) ^ ws.length := by
  induction ws with
  | nil => simp [valLimbs]
  | cons w wt ih =>
      have hw := w.isLt
      simp only [valLimbs_cons, List.length_cons, pow_succ]
      -- w + 2^64 · valLimbs wt < 2^64 · (2^64)^|wt|
      calc w.toNat + 2 ^ 64 * valLimbs wt
          < 2 ^ 64 + 2 ^ 64 * valLimbs wt := by omega
        _ ≤ 2 ^ 64 * (2 ^ 64) ^ wt.length := by
            have : valLimbs wt + 1 ≤ (2 ^ 64) ^ wt.length := ih
            calc 2 ^ 64 + 2 ^ 64 * valLimbs wt
                = 2 ^ 64 * (valLimbs wt + 1) := by ring
              _ ≤ 2 ^ 64 * (2 ^ 64) ^ wt.length := by gcongr
        _ = (2 ^ 64) ^ wt.length * 2 ^ 64 := by ring

/-- The little-endian value of the SBB chain's difference limbs read out of the
    destination registers `ds` over `runBlock` (the raw `u − v` word vector,
    before the conditional add-back of `p`). -/
def runBlockSubDiffValue (ds ss : List String) (s : JState 64) : Nat :=
  valLimbs (ds.map (runBlock s (emitSbbChain ds ss)).get)

/-- The chain's difference value is `< (2^64)^|ds|` (it is a `|ds|`-limb vector). -/
theorem runBlockSubDiffValue_lt (ds ss : List String) (s : JState 64) :
    runBlockSubDiffValue ds ss s < (2 ^ 64) ^ ds.length := by
  have h := valLimbs_lt_pow (ds.map (runBlock s (emitSbbChain ds ss)).get)
  rwa [List.length_map] at h

/-- The SBB chain's final borrow bit over `runBlock` (`1` iff `u < v`, the borrow
    out of the top limb that drives the conditional add-back of `p`). -/
def runBlockSubBorrow (ds ss : List String) (s : JState 64) : Bool :=
  (runBlock s (emitSbbChain ds ss)).flagB (·.cf)

/-- **The emitted SBB chain reconstructs `u − v` over `runBlock`.** For reduced
    inputs the difference limbs and the final borrow satisfy
    `runBlockSubDiffValue + valLimbs v = valLimbs u + borrow · 2^{64·|ds|}` —
    the borrow-chain reconstruction (`subLimbs_reconstruct`) read off the genuine
    emitted `runBlock`, entered with `CF = 0`. -/
theorem emitSbbChain_runBlock_reconstruct (ds ss : List String) (u v : List (BitVec 64))
    (s : JState 64)
    (hdu : ds.length = u.length) (hsv : ss.length = v.length) (huv : u.length = v.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = u) (hsmap : ss.map s.get = v)
    (hcf0 : s.flagB (·.cf) = false) :
    runBlockSubDiffValue ds ss s + valLimbs v
      = valLimbs u
        + (2 ^ 64) ^ ds.length * (if runBlockSubBorrow ds ss s then 1 else 0) := by
  obtain ⟨hmap, hcf⟩ := emitSbbChain_runBlock ds ss u v 0 s hdu hsv huv hfresh hdmap hsmap
    (by simp [hcf0])
  simp only [runBlockSubDiffValue, runBlockSubBorrow, hmap]
  have hrec := subLimbs_reconstruct u v 0
  have htake : v.take u.length = v := by apply List.take_of_length_le; omega
  rw [htake] at hrec
  rw [show ((0 : BitVec 1).toNat) = 0 from rfl, Nat.add_zero] at hrec
  -- the borrow bit = (subLimbs … 0).2 = 1, in the `= true` `if` form of the goal
  rw [hdu]
  have hborrow : (if ((runBlock s (emitSbbChain ds ss)).flagB fun x ↦ x.cf) = true
        then (1 : Nat) else 0) = (subLimbs u v 0).2.toNat := by
    rw [bit_toNat (subLimbs u v 0).2]
    by_cases hb : ((runBlock s (emitSbbChain ds ss)).flagB fun x ↦ x.cf) = true
    · rw [if_pos hb, if_pos (by rw [← hcf]; exact hb)]
    · rw [if_neg hb, if_neg (by rw [← hcf]; simpa using hb)]
  -- subLimbs_reconstruct: valLimbs diff + valLimbs v = valLimbs u + 2^{64n}·borrow
  rw [hrec]
  congr 2
  exact hborrow.symm

/-- The full modular-sub `runBlock` value the emitted block leaves: the SBB chain
    difference value read off the destination registers, plus the conditional
    add-back of `p` on the final borrow (the masked `ADD`/`ADC` add-back), reduced
    `mod 2^{64·|ds|}` (the add-back's top carry is discarded). This reads the
    genuine emitted chain output — not the operand values directly. -/
def runBlockModSubValue (p : Nat) (ds ss : List String) (s : JState 64) : Nat :=
  (runBlockSubDiffValue ds ss s
    + (if runBlockSubBorrow ds ss s then p else 0)) % (2 ^ 64) ^ ds.length

/-- **Genuine `runBlock` modular subtract = `(a − b) mod p`.** The emitted SBB
    borrow chain (the real `List (JInstr 64)`) leaves the difference limbs in `ds`
    and the final borrow in `CF` (`emitSbbChain_runBlock_reconstruct`); the masked
    conditional add-back of `p` on that borrow (`runBlockModSubValue`) then gives,
    for reduced inputs, exactly `(valLimbs a + p − valLimbs b) % p = (a − b) mod p`.
    The full `runBlock(emitted sub) = (a − b) mod p`, read off the genuine emitted
    chain output — the sub-side completion of `FieldAddSubTierA.modAdd_runBlock`. -/
theorem modSub_runBlock (p : Nat) (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : p < (2 ^ 64) ^ ds.length)
    (ha : valLimbs a < p) (hb : valLimbs b < p) :
    runBlockModSubValue p ds ss s = (valLimbs a + p - valLimbs b) % p := by
  -- the emitted chain reconstructs a − b: diff + b = a + borrow · 2^{64n}.
  have hrecon := emitSbbChain_runBlock_reconstruct ds ss a b s hda hsb hab hfresh
    hdmap hsmap hcf0
  rw [hda] at hp hrecon
  -- range facts
  have ha' : valLimbs a < (2 ^ 64) ^ a.length := by omega
  have hb' : valLimbs b < (2 ^ 64) ^ a.length := by omega
  have hDlt0 := runBlockSubDiffValue_lt ds ss s
  rw [hda] at hDlt0
  simp only [runBlockModSubValue, hda]
  set R : Nat := (2 ^ 64) ^ a.length with hR
  set D : Nat := runBlockSubDiffValue ds ss s with hD
  rw [← condAddP_eq_mod p (valLimbs a) (valLimbs b) ha hb]
  -- case on the borrow flag
  by_cases hbor : runBlockSubBorrow ds ss s
  · -- borrow ⇒ a < b, D = a + R − b; (D + p) % R = a + p − b
    simp only [if_pos hbor] at hrecon ⊢
    have hDval : D = valLimbs a + R - valLimbs b := by omega
    have hab_lt : valLimbs a < valLimbs b := by omega
    rw [hDval, condAddP, if_pos hab_lt]
    -- (a + R − b + p) % R = a + p − b  (since a + p − b < R)
    rw [show valLimbs a + R - valLimbs b + p = R + (valLimbs a + p - valLimbs b) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · -- no borrow ⇒ a ≥ b, D = a − b; (D + 0) % R = a − b
    simp only [if_neg hbor, Nat.add_zero] at hrecon ⊢
    have hge : valLimbs b ≤ valLimbs a := by omega
    have hDval : D = valLimbs a - valLimbs b := by omega
    rw [hDval, condAddP, if_neg (by omega : ¬ valLimbs a < valLimbs b),
      Nat.mod_eq_of_lt (by omega)]

/-! ## 6. Curve instances: Pasta (4-limb), BLS12-381 / P384 (6-limb)

The emitted SBB borrow chain over `runBlock`, canonicalised by the conditional
add-back of the curve prime, equals `(a − b) mod p` for reduced inputs. The
sub-side completion of `FieldAddSubTierA.<curve>_modadd_runBlock`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
  (pallasLimbs vestaLimbs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve6LimbTierA
  (bls12381Limbs p384Limbs)

/-- **Pallas modular sub over `runBlock` = `(a − b) mod p` (Tier A, 4-limb).** The
    `hp` hypothesis `p < (2^64)^|ds|` holds for the 4-limb register layout
    (`|ds| = 4`, `p < 2^255 < 2^256`). -/
theorem pallas_modsub_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : valLimbs pallasLimbs < (2 ^ 64) ^ ds.length)
    (ha_red : valLimbs a < valLimbs pallasLimbs) (hb_red : valLimbs b < valLimbs pallasLimbs) :
    runBlockModSubValue (valLimbs pallasLimbs) ds ss s
      = (valLimbs a + valLimbs pallasLimbs - valLimbs b) % valLimbs pallasLimbs :=
  modSub_runBlock (valLimbs pallasLimbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    hp ha_red hb_red

/-- **Vesta modular sub over `runBlock` = `(a − b) mod q` (Tier A, 4-limb).** -/
theorem vesta_modsub_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : valLimbs vestaLimbs < (2 ^ 64) ^ ds.length)
    (ha_red : valLimbs a < valLimbs vestaLimbs) (hb_red : valLimbs b < valLimbs vestaLimbs) :
    runBlockModSubValue (valLimbs vestaLimbs) ds ss s
      = (valLimbs a + valLimbs vestaLimbs - valLimbs b) % valLimbs vestaLimbs :=
  modSub_runBlock (valLimbs vestaLimbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    hp ha_red hb_red

/-- **BLS12-381 base-field modular sub over `runBlock` = `(a − b) mod p`
    (Tier A, 6-limb).** `hp` holds for the 6-limb layout (`p < 2^381 < 2^384`). -/
theorem bls12381_modsub_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : valLimbs bls12381Limbs < (2 ^ 64) ^ ds.length)
    (ha_red : valLimbs a < valLimbs bls12381Limbs) (hb_red : valLimbs b < valLimbs bls12381Limbs) :
    runBlockModSubValue (valLimbs bls12381Limbs) ds ss s
      = (valLimbs a + valLimbs bls12381Limbs - valLimbs b) % valLimbs bls12381Limbs :=
  modSub_runBlock (valLimbs bls12381Limbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    hp ha_red hb_red

/-- **P384 modular sub over `runBlock` = `(a − b) mod p` (Tier A, 6-limb).** -/
theorem p384_modsub_runBlock (ds ss : List String) (a b : List (BitVec 64))
    (s : JState 64)
    (hda : ds.length = a.length) (hsb : ss.length = b.length) (hab : a.length = b.length)
    (hfresh : ChainFresh ds ss)
    (hdmap : ds.map s.get = a) (hsmap : ss.map s.get = b)
    (hcf0 : s.flagB (·.cf) = false)
    (hp : valLimbs p384Limbs < (2 ^ 64) ^ ds.length)
    (ha_red : valLimbs a < valLimbs p384Limbs) (hb_red : valLimbs b < valLimbs p384Limbs) :
    runBlockModSubValue (valLimbs p384Limbs) ds ss s
      = (valLimbs a + valLimbs p384Limbs - valLimbs b) % valLimbs p384Limbs :=
  modSub_runBlock (valLimbs p384Limbs) ds ss a b s hda hsb hab hfresh hdmap hsmap hcf0
    hp ha_red hb_red

end CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock
