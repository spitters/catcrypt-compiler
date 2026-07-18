/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
import CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
import CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
import CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

/-!
# Concrete realizer for the Barrett modular-reduction kernel — KAT-free

`BarrettReduceEmitValue.lean` reduces the Barrett-reduce emit obligation to a
*leaf-realization* predicate — "the emitted reduce leaf's bytes decode to
`barrettCondsub q k (decode x)` (= `x mod q` under the Barrett bounds)".  Its
non-vacuity witness (`barrettKernelRealizes_canonical`) exhibits a realizing
`LeafSpec`, but only **parametrically** over an abstract `encode`/`decode` pair
with a *hypothesised* section (`hsection : ∀ n, decode (encode n) = n`).

This module makes that section **concrete and proved**, mirroring
`ConcreteSymFieldRealizer.lean` (the field-op concrete realizer).  The Barrett
reduction (`BarrettReduceGeneric`) is proved over `ℕ`, so the field realizer's
base-256 `ℕ`→bytes codec applies directly — here returning a raw `ℕ` (not a
`ZMod q`), which is exactly the carrier the reduce leaf consumes.

We exhibit:

* a genuine `RustVal .TFp` (= `JArray 48`, the `.TBytes 48` byte carrier)
  base-256 codec `encodeB`/`decodeB` — `encodeB` lays a natural number's `width`
  little-endian base-256 digits into the first `width` carrier bytes, zero in the
  tail; `decodeB` reads them back base-256.  No constructor-wrapping of a
  function, no `axiom`;
* a **proved** round-trip `decodeB_encodeB : decodeB width (encodeB width x) = x`
  for **all** in-range inputs `x < 256 ^ width` — the byte-level fact a KAT would
  merely *assert*, here a theorem (it is `base256_digit_sum` reused, the same
  engine as the field codec);
* a spec-computing realizer `LeafSpec` (`barrettLeafSpec q k width leaf`) whose
  `.call` value at the leaf decodes to `barrettCondsub q k (decode x)` — and,
  under the Barrett side-conditions, to `(decode x) % q` by the proven
  `barrettCondsub_eq_mod`;
* the **unconditional** realization `barrett_realizes_concrete`
  (`KernelRealizes decodeB (fun x => barrettCondsub q k x) leaf …`) — no KAT, no
  abstract section — proved from `decodeB_encodeB`; and its mod-reduction form
  `barrett_realizes_mod` (`KernelRealizes decodeB (· % q) …`), which threads the
  Barrett bounds.

## What this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there is a *concrete*,
  round-trip-verified base-256 byte codec and a *concrete*, spec-computing
  realizer `LeafSpec` under which the Barrett-reduce leaf realization holds for
  **all** inputs — strictly stronger than *assuming* a KAT, because the
  byte-level decode-equals-`barrettCondsub` fact is a theorem here, not a test
  vector.  The Barrett-reduce *encoding* KAT (the `decode ∘ encode = id`
  assumption of `barrettKernelRealizes_canonical`) is now discharged.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine
  bytes* of the real Barrett-reduce kernel equal this realizer.  That equality —
  emitted assembly ≡ the realizer `LeafSpec` — is the owned-machine-code route
  and is a separate follow-up.  This file removes the *encoding* KAT for the
  modular-reduction family; it does **not** remove the *machine-code* obligation.

This covers the **modular-reduction** primitive used across lattice/field crypto
(ML-KEM/ML-DSA coefficient reduction, prime-field arithmetic).

## Honesty: side-conditions are NOT kernel hypotheses

Only the codec-fit + Barrett-bound *side-conditions* remain — `width ≤ 48`,
`x < 256 ^ width` (codec fit), and `0 < q`, `q ≤ 2 ^ k`, `decode x < 2 ^ k`
(Barrett bound).  They are threaded as side hypotheses of the theorems (exactly
as the field codec threads `q < 2 ^ (8 · width)`), **not** as hypotheses on the
realizer/kernel — `barrett_realizes_concrete` (the `barrettCondsub` form) is
fully unconditional.

## References
* P. Barrett, "Implementing the Rivest Shamir and Adleman public key encryption
  algorithm on a standard digital signal processor", CRYPTO 1986.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.BarrettReduceEmitValue
open CatCrypt.Crypto.Optimizer.Rewrite.BarrettReduceGeneric

/-! ## §1  A concrete base-256 `ℕ`↔bytes codec over `RustVal .TFp`

`RustVal .TFp = JArray 48 = Fin 48 → BitVec 8` is the `.TBytes 48` byte carrier.
A natural number `x` (in range `x < 256 ^ width`) is laid out `width` bytes
little-endian into the first `width` of the 48 carrier bytes, zero in the tail.
`decodeB` reads the `width` bytes back base-256.  This is the field codec's
`encodeF`/`decodeF` with the `ZMod q`-reduction stripped — the carrier the
reduce leaf consumes is a raw `ℕ`, not a field element. -/

/-- Encode a natural number into the first `width` carrier bytes, little-endian
    base-256 of `x`; zero in the tail.  (`width` must satisfy `width ≤ 48` and
    `x < 256 ^ width` for the round-trip and fit.)  The carrier `RustVal .TFp`
    is the `.TBytes 48` byte array. -/
def encodeB (width : ℕ) (x : ℕ) : RustVal .TFp :=
  fun b =>
    if _h : b.val < width then BitVec.ofNat 8 ((x / 256 ^ b.val) % 256) else 0

/-- Decode the first `width` carrier bytes as a base-256 little-endian natural
    number. -/
def decodeB (width : ℕ) (a : RustVal .TFp) : ℕ :=
  (Finset.range width).sum
    (fun j => 256 ^ j * (a ⟨j % 48, Nat.mod_lt _ (by decide)⟩).toNat)

/-- **The verified Barrett-codec round-trip (the crux).**  For `width ≤ 48` and
    `x < 256 ^ width`, decoding the concrete base-256 byte encoding of a natural
    number returns it unchanged — for **all** in-range inputs.  The byte-level
    fact a KAT would merely *assert*; here a theorem, with engine
    `base256_digit_sum` (the same base-256 digit reconstruction as the field
    codec). -/
theorem decodeB_encodeB (width : ℕ) (hw : width ≤ 48) (x : ℕ)
    (hx : x < 256 ^ width) :
    decodeB width (encodeB width x) = x := by
  simp only [decodeB, encodeB]
  -- Each byte slot `j < width` reads back `(x / 256^j) % 256`.
  have hbytes : ∀ j ∈ Finset.range width,
      256 ^ j *
        ((if _h : (⟨j % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48).val < width then
          BitVec.ofNat 8 ((x / 256 ^ (⟨j % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48).val) % 256)
          else 0)).toNat
      = 256 ^ j * ((x / 256 ^ j) % 256) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j % 48 = j := Nat.mod_eq_of_lt (lt_of_lt_of_le hj hw)
    simp only [hjm]
    rw [dif_pos hj, BitVec.toNat_ofNat]
    have hlt : (x / 256 ^ j) % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt hlt]
  rw [Finset.sum_congr rfl hbytes]
  -- The base-256 digit sum reconstructs `x` since `x < 256^width`.
  rw [ConcreteSymFieldRealizer.base256_digit_sum x width, Nat.mod_eq_of_lt hx]

/-! ## §2  The concrete Barrett realizer `LeafSpec`

The realizer's `CallSpec`: at the Barrett leaf it decodes the sole `.TFp`
argument, applies `barrettCondsub q k`, and re-encodes via `encodeB`; off-leaf
it returns `oldDest`.  The unary analogue of `ConcreteSymFieldRealizer.aesCallSpec`,
specialized to the reduce primitive. -/

/-- The concrete Barrett realizer's `CallSpec`. -/
def barrettCallSpec (q k width : ℕ) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ℕ := fun a =>
        if ht : a.1 = TowerType.TFp then decodeB width (ht ▸ a.2) else 0
      match args with
      | a :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encodeB width (barrettCondsub q k (pick a))
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete Barrett realizer `LeafSpec`. -/
def barrettLeafSpec (q k width : ℕ) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  { call := barrettCallSpec q k width leaf, limbStore := limbStore }

/-! ## §3  The unconditional realization (no KAT, no abstract section) -/

/-- **Unconditional Barrett-kernel realization (no KAT, no abstract section).**
    For `width ≤ 48`, the concrete realizer `barrettLeafSpec q k width …` decodes
    its leaf-call value to `barrettCondsub q k` of its decoded input for **every**
    input — proved by the round-trip `decodeB_encodeB`, not assumed via a test
    vector.

    `width ≤ 48` is the *codec-fit* side-condition (so the `width` digits lie
    inside the 48-byte carrier); it is **not** a kernel hypothesis — the realizer
    `barrettCondsub q k` is unconditional. -/
theorem barrett_realizes_concrete (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeB width) (fun x => barrettCondsub q k x) leaf
      (barrettLeafSpec q k width leaf limbStore) := by
  intro xVal oldDest
  -- The decoded argument is in range for the round-trip: it is decoded from the
  -- `width`-byte window, hence `< 256 ^ width`.
  have hxlt : decodeB width xVal < 256 ^ width := by
    have hbound : ∀ j, (xVal ⟨j % 48, Nat.mod_lt _ (by decide)⟩).toNat ≤ 255 := by
      intro j
      have := (xVal ⟨j % 48, Nat.mod_lt _ (by decide)⟩).isLt
      omega
    calc decodeB width xVal
        = (Finset.range width).sum
            (fun j => 256 ^ j * (xVal ⟨j % 48, Nat.mod_lt _ (by decide)⟩).toNat) := rfl
      _ ≤ (Finset.range width).sum (fun j => 256 ^ j * 255) :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (hbound j))
      _ < 256 ^ width := by
            induction width with
            | zero => simp
            | succ w ih =>
                rw [Finset.sum_range_succ, pow_succ]
                have : (Finset.range w).sum (fun j => 256 ^ j * 255) < 256 ^ w :=
                  ih (le_trans (Nat.le_succ w) hw)
                nlinarith [pow_pos (show 0 < 256 by decide) w]
  show decodeB width (barrettCallSpec q k width leaf leaf .TFp [.TFp] oldDest
      [⟨.TFp, xVal⟩])
    = barrettCondsub q k (decodeB width xVal)
  simp only [barrettCallSpec, ite_true, dite_true]
  rw [decodeB_encodeB width hw _ (by
    -- `barrettCondsub q k (decodeB width xVal) ≤ decodeB width xVal < 256 ^ width`.
    have : barrettCondsub q k (decodeB width xVal) ≤ decodeB width xVal := by
      simp only [barrettCondsub, barrett]
      split <;> omega
    omega)]

/-- **Unconditional Barrett-kernel realization as a `BarrettKernelRealizes`
    seam.**  `barrett_realizes_concrete` *is* the localized
    `BarrettReduceEmitValue.BarrettKernelRealizes` predicate — by definitional
    unfolding — with its abstract `encode`/`decode` section now a *theorem*
    (`decodeB_encodeB`) rather than the assumed `hsection`. -/
theorem barrett_kernel_realizes_concrete (q k width : ℕ) (hw : width ≤ 48)
    (leaf : String) (limbStore : LimbStoreSpec) :
    BarrettKernelRealizes q k (decodeB width) leaf
      (barrettLeafSpec q k width leaf limbStore) :=
  barrett_realizes_concrete q k width hw leaf limbStore

/-! ## §4  The mod-reduction form via the proven Barrett bound

Threading the Barrett side-conditions (`0 < q`, `q ≤ 2 ^ k`,
`decodeB width x < 2 ^ k`) through the proven `barrettCondsub_eq_mod`
(`barrettCondsub q k x = x % q`) gives the full modular-reduction realization
`KernelRealizes decodeB (· % q) …`.  These bounds are *side-conditions*, not
kernel hypotheses. -/

/-- **Unconditional modular-reduction realization (codec round-trip a theorem).**
    Under the Barrett side-conditions (`0 < q`, `q ≤ 2 ^ k`, in-range inputs
    `decodeB width x < 2 ^ k`) and the codec-fit `width ≤ 48`, the concrete
    realizer decodes its leaf-call value to `(decode x) % q` — the modular
    residue the reduce primitive computes — for **every** input.  The
    "Barrett reduce = mod" content is the proven `barrettCondsub_eq_mod`; the
    byte-level decode-equals-spec content is the proven `decodeB_encodeB`. -/
theorem barrett_realizes_mod (q k width : ℕ) (hw : width ≤ 48)
    (hq : 0 < q) (hk : q ≤ 2 ^ k)
    (hbound : ∀ xVal : RustVal .TFp, decodeB width xVal < 2 ^ k)
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes (decodeB width) (· % q) leaf
      (barrettLeafSpec q k width leaf limbStore) := by
  intro xVal oldDest
  show decodeB width (barrettLeafSpec q k width leaf limbStore |>.call leaf .TFp [.TFp]
      oldDest [⟨.TFp, xVal⟩]) = decodeB width xVal % q
  rw [show (decodeB width (barrettLeafSpec q k width leaf limbStore |>.call leaf .TFp [.TFp]
      oldDest [⟨.TFp, xVal⟩])) = barrettCondsub q k (decodeB width xVal) from
        barrett_realizes_concrete q k width hw leaf limbStore xVal oldDest,
    barrettCondsub_eq_mod q k hq hk (decodeB width xVal) (hbound xVal)]

/-- The mod-reduction realization as the `BarrettReduceEmitValue.BarrettEmitRealizes`
    seam (definitionally `KernelRealizes _ (· % q) _ _` via `barrett_iff_kernel`),
    now with the encoding section a *theorem*. -/
theorem barrett_emit_realizes_concrete (q k width : ℕ) (hw : width ≤ 48)
    (hq : 0 < q) (hk : q ≤ 2 ^ k)
    (hbound : ∀ xVal : RustVal .TFp, decodeB width xVal < 2 ^ k)
    (leaf : String) (limbStore : LimbStoreSpec) :
    BarrettEmitRealizes q k (decodeB width) leaf
      (barrettLeafSpec q k width leaf limbStore) :=
  barrett_realizes_mod q k width hw hq hk hbound leaf limbStore

end CatCrypt.Crypto.SecureCompilation.ConcreteBarrettRealizer
