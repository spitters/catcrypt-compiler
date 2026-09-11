/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
public import CatCrypt.Crypto.SecureCompilation.HashKernelRegistryEntry
public import CatCrypt.Crypto.SecureCompilation.Sha256KernelRegistryEntry

/-!
# CONCRETE hash realizers: round-trip-verified codecs, KAT-free realization

The hash registry rows (`HashKernelRegistryEntry`, `Sha256KernelRegistryEntry`)
register Keccak-f[1600] and SHA-256 compression as rows of the generic
`KernelRealizes` predicate, but each row's realization fact is taken as a
**hypothesis** — the localized "this leaf's bytes decode to the hash spec"
residual a leaf-bytes KAT would discharge.  This module turns that hypothesis into
a **theorem** for a concrete, spec-computing realizer with a verified byte codec —
the "better than a KAT" deeper-axis work, mirroring `ConcreteNttRealizer` for the
NTT row.

We exhibit, for each hash:

* a genuine `RustVal`-byte codec (a real `JArray` byte array, not a constructor
  wrapping the function): a little-endian `encode`/`decode` pair over the carrier
  `RustVal (.TBytes n)` (`n = 200` bytes = 1600 bits for Keccak, `n = 32` bytes =
  256 bits for SHA-256), and
* a **proved** round-trip (`decodeKbytes_encodeKbytes`, `decodeSbytes_encodeSbytes`):
  for **every** input, decoding the byte encoding returns the input.  This is the
  byte-level fact a KAT would merely *assert*; here it is a theorem (Keccak via a
  per-bit `getLsbD` argument over the 200-byte layout; SHA-256 via a per-word
  32-bit `bv_decide`).

From the round-trip, the concrete realizer `specLeafSpecT` provably computes the
hash spec (`keccak_f steps` / `fun s => compress s block`) for **all** inputs:
`keccak_realizes_concrete` and `sha256_realizes_concrete` are `KernelRealizesT`
theorems with **no** KAT hypothesis and **no** abstract `decode ∘ encode = id`
assumption.

## The carrier: `.TBytes n` vs the `.TFp` registry row

The registry rows hardcode the `.TFp` carrier (`RustVal .TFp = JArray 48`, 384
bits).  No round-trip `decode ∘ encode = id` can exist there for `KeccakState =
BitVec 1600`: a faithful injection needs ≥ 1600 bits, far above 384 (pigeonhole) —
the same carrier-size point `ConcreteNttRealizer` makes for the ML-KEM vector type.
We therefore re-state the unary realization predicate over an arbitrary carrier
TowerType `T` (`KernelRealizesT`), instantiated at `.TBytes 200` / `.TBytes 32`,
which have enough room; `kernelRealizesT_TFp_iff` records that at `.TFp` this is
*exactly* the registry predicate, so it is the same mechanism, carrier-generalized.

## HONEST scope — what this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there is a *concrete* leaf realizer and
  a *concrete*, round-trip-verified byte codec under which the Keccak-f[1600] /
  SHA-256 compression realization holds for **all** inputs — strictly stronger than
  *assuming* the per-kernel KAT, because the byte-level decode-equals-hash-spec fact
  is a theorem here.  This discharges the per-kernel KAT for the hash families *for
  the spec-computing realizer*.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine bytes*
  of the real Keccak-f / SHA-256 kernels equal this realizer (actual emitted
  assembly ≡ `specLeafSpecT`).  That is the owned-machine-code route, a separate
  follow-up.  This file removes the *encoding* KAT (the `decode ∘ encode = id`
  assumption); it does **not** remove the *machine-code* obligation.

## References
* NIST FIPS 202 (Keccak / SHA-3), FIPS 180-4 (SHA-256)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Primitives.SHA256

/-! ## §1  Keccak: a round-trip-verified 200-byte little-endian codec -/

/-- Encode a 1600-bit state as 200 little-endian bytes. -/
def encodeKbytes (s : KeccakState) : Fin 200 → BitVec 8 :=
  fun i => BitVec.setWidth 8 (s >>> (8 * i.val))

/-- Decode 200 bytes into a 1600-bit state via an OR-fold of shifted bytes. -/
def decodeKbytes (a : Fin 200 → BitVec 8) : KeccakState :=
  (List.finRange 200).foldl
    (fun acc i => acc ||| (BitVec.setWidth 1600 (a i) <<< (8 * i.val))) 0

/-- getLsbD of an OR-fold distributes: the bit is set iff the init has it or some
    folded contribution has it. -/
theorem getLsbD_foldl_or {w : ℕ} {α : Type*} (f : α → BitVec w) (k : ℕ) :
    ∀ (l : List α) (init : BitVec w),
      (l.foldl (fun acc i => acc ||| f i) init).getLsbD k
        = (init.getLsbD k || (l.map (fun i => (f i).getLsbD k)).foldr (· || ·) false) := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons x xs ih =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.foldr_cons]
      rw [ih (init ||| f x)]
      simp only [BitVec.getLsbD_or]
      rw [Bool.or_assoc]

/-- A foldr-OR of (predicate AND constant) factors the constant out. -/
theorem foldr_or_and_const {α : Type*} (P : α → Bool) (b : Bool) (l : List α) :
    (l.map (fun i => P i && b)).foldr (· || ·) false
      = ((l.map P).foldr (· || ·) false && b) := by
  induction l with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      rw [List.map_cons, List.map_cons, List.foldr_cons, List.foldr_cons]
      cases b <;> cases hpx : P x <;> simp_all

/-- A foldr-OR is `true` whenever some element of the list is `true`. -/
theorem foldr_or_true_of_mem {l : List Bool} (h : true ∈ l) :
    l.foldr (· || ·) false = true := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp h with hx | hx
      · subst hx; simp
      · rw [ih hx]; simp

/-- The byte-selector predicate is satisfied by some byte index in `finRange 200`
    for every bit position `< 1600`. -/
theorem byteSelector_finRange (k : ℕ) (hk : k < 1600) :
    ((List.finRange 200).map
        (fun i : Fin 200 => decide (k < 1600) && !decide (k < 8 * i.val)
          && (decide (k - 8 * i.val < 1600) && decide (k - 8 * i.val < 8)))).foldr
      (· || ·) false = true := by
  apply foldr_or_true_of_mem
  rw [List.mem_map]
  refine ⟨⟨k / 8, by omega⟩, List.mem_finRange _, ?_⟩
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_eq_eq_not]
  simp only [Bool.not_true, decide_eq_false_iff_not]
  omega

theorem decodeKbytes_encodeKbytes (s : KeccakState) :
    decodeKbytes (encodeKbytes s) = s := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  unfold decodeKbytes encodeKbytes
  rw [getLsbD_foldl_or]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  -- Pointwise: each contribution = (byte-selector i) && s.getLsbD k.
  have hpt : ∀ i : Fin 200,
      (decide (k < 1600) && !decide (k < 8 * i.val) &&
        (decide (k - 8 * i.val < 1600) && (decide (k - 8 * i.val < 8) &&
          BitVec.getLsbD s (8 * i.val + (k - 8 * i.val)))))
        = ((decide (k < 1600) && !decide (k < 8 * i.val) &&
            (decide (k - 8 * i.val < 1600) && decide (k - 8 * i.val < 8))) && BitVec.getLsbD s k) := by
    intro i
    by_cases hki : k < 8 * i.val
    · simp [hki]
    · by_cases hk8 : k - 8 * i.val < 8
      · have : 8 * i.val + (k - 8 * i.val) = k := by omega
        rw [this]; cases BitVec.getLsbD s k <;> simp_all
      · simp [hk8]
  rw [List.map_congr_left (fun i _ => hpt i), foldr_or_and_const]
  rw [byteSelector_finRange k hk, Bool.true_and]
  simp [BitVec.getLsbD_zero]

/-! ## §2  SHA-256: a round-trip-verified 32-byte little-endian codec -/

/-- Encode a SHA-256 state (8 words) as 32 little-endian bytes: byte `b` is byte
    `b % 4` of word `b / 4`. -/
def encodeSbytes (s : State256) : Fin 32 → BitVec 8 :=
  fun b => BitVec.setWidth 8 ((s ⟨b.val / 4, by have := b.isLt; omega⟩).toBitVec >>> (8 * (b.val % 4)))

/-- Reassemble one 32-bit word from its 4 little-endian bytes. -/
def wordOfBytes (b0 b1 b2 b3 : BitVec 8) : BitVec 32 :=
  BitVec.setWidth 32 b0 ||| (BitVec.setWidth 32 b1 <<< 8)
    ||| (BitVec.setWidth 32 b2 <<< 16) ||| (BitVec.setWidth 32 b3 <<< 24)

/-- Decode 32 bytes back into a SHA-256 state, four bytes per word, little-endian. -/
def decodeSbytes (a : Fin 32 → BitVec 8) : State256 :=
  fun i => UInt32.ofBitVec
    (wordOfBytes (a ⟨4 * i.val, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 1, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 2, by have := i.isLt; omega⟩)
      (a ⟨4 * i.val + 3, by have := i.isLt; omega⟩))

/-- The per-word round-trip: reassembling the four little-endian bytes of a 32-bit
    word returns the word. A 32-bit `bv_decide` fact. -/
theorem wordOfBytes_split (w : BitVec 32) :
    wordOfBytes (BitVec.setWidth 8 w) (BitVec.setWidth 8 (w >>> 8))
      (BitVec.setWidth 8 (w >>> 16)) (BitVec.setWidth 8 (w >>> 24)) = w := by
  unfold wordOfBytes
  bv_decide

theorem decodeSbytes_encodeSbytes (s : State256) :
    decodeSbytes (encodeSbytes s) = s := by
  funext i
  unfold decodeSbytes encodeSbytes
  have e0 : (4 * i.val) / 4 = i.val := by omega
  have e1 : (4 * i.val + 1) / 4 = i.val := by omega
  have e2 : (4 * i.val + 2) / 4 = i.val := by omega
  have e3 : (4 * i.val + 3) / 4 = i.val := by omega
  have m0 : (4 * i.val) % 4 = 0 := by omega
  have m1 : (4 * i.val + 1) % 4 = 1 := by omega
  have m2 : (4 * i.val + 2) % 4 = 2 := by omega
  have m3 : (4 * i.val + 3) % 4 = 3 := by omega
  simp only [e0, e1, e2, e3, m0, m1, m2, m3, Fin.eta]
  norm_num
  rw [wordOfBytes_split]

/-! ## §3  A carrier-parametric kernel-realization predicate + concrete realizer

The registry predicate `ProtocolEmitRealizes.KernelRealizes` hardcodes the `.TFp`
carrier (`RustVal .TFp = JArray 48`, 384 bits).  No round-trip `decode ∘ encode = id`
can exist there for `KeccakState = BitVec 1600` (a faithful injection needs ≥ 1600
bits, far above 384 — pigeonhole), exactly as the NTT carrier note explains.  We
re-state the unary predicate over an arbitrary carrier TowerType `T` whose
`RustVal T = JArray T.storageBytes` is genuinely large enough — `.TBytes 200`
(1600 bits) for Keccak, `.TBytes 32` (256 bits) for SHA-256 — and build a concrete,
round-trip-verified realizer over it. -/

/-- **Carrier-parametric unary kernel-realization** — `KernelRealizes` over an
    arbitrary carrier TowerType `T` instead of the fixed `.TFp`. -/
def KernelRealizesT {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (spec : C → C) (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (xVal oldDest : RustVal T),
    decode (leafSpec.call leaf T [T] oldDest [⟨T, xVal⟩]) = spec (decode xVal)

/-- `KernelRealizesT` at the `.TFp` carrier *is* the registry's
    `ProtocolEmitRealizes.KernelRealizes` — by `Iff.rfl`.  So `KernelRealizesT` is
    not a fresh mechanism: it is the one generic unary predicate, generalized over
    the carrier TowerType so a faithful round-trip codec can exist (which it cannot
    on the 384-bit `.TFp` carrier for a 1600-bit Keccak state). -/
theorem kernelRealizesT_TFp_iff {C : Type*} (decode : RustVal .TFp → C)
    (spec : C → C) (leaf : String) (leafSpec : LeafSpec) :
    KernelRealizesT .TFp decode spec leaf leafSpec
      ↔ ProtocolEmitRealizes.KernelRealizes decode spec leaf leafSpec := Iff.rfl

/-- The concrete, spec-computing `CallSpec` over carrier `T`: at `leaf`, decode the
    sole argument, apply `spec`, and re-encode; off-leaf return `oldDest`. -/
def specCallSpecT {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (encode : C → RustVal T) (spec : C → C) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      match args with
      | a :: _ =>
          if ht : a.1 = T then
            if hd : _dt = T then hd ▸ encode (spec (decode (ht ▸ a.2))) else oldDest
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete realizer `LeafSpec` over carrier `T`. -/
def specLeafSpecT {C : Type*} (T : TowerType) (decode : RustVal T → C)
    (encode : C → RustVal T) (spec : C → C) (leaf : String)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := specCallSpecT T decode encode spec leaf, limbStore := limbStore }

/-- **Unconditional realization for the concrete realizer.**  When `decode ∘ encode
    = id` is a *theorem* (`hsec`), the concrete realizer `specLeafSpecT` realizes
    `spec` for **every** input — no KAT hypothesis. -/
theorem kernelRealizesT_concrete {C : Type*} (T : TowerType)
    (decode : RustVal T → C) (encode : C → RustVal T) (spec : C → C)
    (hsec : ∀ x, decode (encode x) = x) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizesT T decode spec leaf
      (specLeafSpecT T decode encode spec leaf limbStore) := by
  intro xVal oldDest
  show decode (specCallSpecT T decode encode spec leaf leaf T [T] oldDest
      [⟨T, xVal⟩]) = spec (decode xVal)
  simp only [specCallSpecT, ite_true, dite_true]
  rw [hsec]

/-! ## §4  The unconditional Keccak realization -/

/-- **Keccak-f[1600] realization — UNCONDITIONAL.**  For the concrete realizer
    `specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps) …` and
    the round-trip-verified 200-byte little-endian codec, the kernel realization
    `KernelRealizesT (.TBytes 200) decodeKbytes (keccak_f steps) …` holds for every
    input.  No KAT hypothesis and no abstract `decode ∘ encode = id` assumption: the
    section is the theorem `decodeKbytes_encodeKbytes`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    Keccak-f kernel equal this realizer (the owned-machine-code route — a separate
    follow-up). -/
theorem keccak_realizes_concrete (steps : KeccakStepMappings) (limbStore : LimbStoreSpec) :
    KernelRealizesT (.TBytes 200) decodeKbytes (keccak_f steps)
      "keccak_f1600"
      (specLeafSpecT (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
        "keccak_f1600" limbStore) :=
  kernelRealizesT_concrete (.TBytes 200) decodeKbytes encodeKbytes (keccak_f steps)
    decodeKbytes_encodeKbytes "keccak_f1600" limbStore

/-! ## §5  The unconditional SHA-256 realization -/

/-- **SHA-256 compression realization — UNCONDITIONAL.**  For the concrete realizer
    `specLeafSpecT (.TBytes 32) decodeSbytes encodeSbytes (fun s => compress s block)
    …` and the round-trip-verified 32-byte little-endian codec, the kernel
    realization holds for every input.  No KAT hypothesis and no abstract section
    assumption: the section is the theorem `decodeSbytes_encodeSbytes`.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    SHA-256 compression kernel equal this realizer (the owned-machine-code route —
    a separate follow-up). -/
theorem sha256_realizes_concrete (block : Fin 64 → UInt8) (limbStore : LimbStoreSpec) :
    KernelRealizesT (.TBytes 32) decodeSbytes (fun s => compress s block)
      "sha256_compress"
      (specLeafSpecT (.TBytes 32) decodeSbytes encodeSbytes (fun s => compress s block)
        "sha256_compress" limbStore) :=
  kernelRealizesT_concrete (.TBytes 32) decodeSbytes encodeSbytes
    (fun s => compress s block) decodeSbytes_encodeSbytes "sha256_compress" limbStore

end CatCrypt.Crypto.SecureCompilation.ConcreteHashRealizer
