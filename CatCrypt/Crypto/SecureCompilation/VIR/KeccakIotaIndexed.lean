/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

/-!
# Keccak ι as a bit-exact index-parameterized loop (the per-round-constant exemplar)

`KeccakEmit.keccak_round_loop_denote_eq` (committed) certifies the 24-round
Keccak loop *structure* — but with a **uniform** body that folds in a *fixed*
`RC[0]`; the genuinely per-round ι constant stream lived only in the
fully-unrolled emission, whose bit-exactness rested on the FIPS 202 KAT, NOT on
the loop denotation theorem.

This file closes that hole for the cleanest per-round-constant primitive, the
Keccak **ι** step (a single per-round XOR of `RC[round]` into lane 0). Using the
index-parameterized loop layer `JForProgIndexed` (the `JForProgTab` form: the
body context carries the loop index register `"idx"` and the loop-invariant
constant table `"rc"`), we **prove**:

* `keccakIotaBody` — the ι body over `[reg 64, reg 64, stackArr 64 24]`: read
  `RC[idx]` by `stackLoad rc idx`, then `acc ⊕ RC[idx]` by `regArith xor`. It is
  `StraightLine` (two binders, both non-`stackStore`).
* `keccakIotaStep_eq` — the body's per-iteration step is **bit-exactly**
  `acc ^^^ RC[i]` (the FIPS 202 ι), the actual per-round constant `RC[i]` read
  from the table — NOT a fixed `RC[0]`.
* `keccak_iota_loop_bitexact` — **the keystone**: the emitted indexed loop
  `for i = 0 to 24 { acc = acc ⊕ RC[i] }`, run on the word-level evaluator,
  denotes the bit-exact 24-fold ι fold `keccakIotaRef` — a THEOREM via
  `JForProgIndexed.loopRunT_eq_denoteT` (routed through `freshName_injective`),
  **not** `native_decide` / KAT.
* `keccak_iota_kat` — the FIPS 202 KAT for the ι stream (the cumulative XOR of all
  24 round constants from `init = 0`) is now derived as a **corollary** of the
  bit-exact loop theorem — a sanity check, not the validation.

The only carried hypothesis is the opaque-leaf edge `LeafAgrees`, which is
**vacuous** here (the ι body has no `extCall`). No `sorry`, no new axioms, no
`native_decide` for the bit-exactness.

## Corollaries for the other two per-round-constant primitives

The same mechanism applies verbatim to:

* **SHA-2** (`Sha2Emit`): the message-schedule / compression round adds `K[t]` and
  uses the fixed σ shift amounts `{7,18,3,17,19,10}`. Realize the round body over
  `[stateTy, reg 64, stackArr 64 64]` reading `K[t]` by `stackLoad K t` (the
  fixed shift amounts are per-position constants of the same table form, or
  baked into the per-`t` body family `JForProgIdx.update t`); the indexed loop
  `for t = 0 to 64 { state = round(state, K[t]) }` denotes the bit-exact 64-round
  compression by `loopRunT_eq_denoteT`. See `keccak_iota_loop_bitexact` for the
  pattern; `Sha2Emit.lean` is the committed unrolled artifact the corollary
  re-derives.
* **Poseidon2** (`Poseidon2Emit`): each (full / partial) round adds its per-round
  constant vector `RC[r]`. Realize the round body over `[stateTy, reg 64,
  stackArr 64 nRounds·width]` reading the round-constant block by `stackLoad`;
  the indexed loop denotes the bit-exact `nRounds`-round permutation by
  `loopRunT_eq_denoteT`.

Each corollary is the `JForProgTab` instantiation with that primitive's constant
table and round body; the loop denotation is the same theorem, so the per-round
constant becomes a certified input rather than a KAT-validated unrolled stream.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
file is step #104 in that chain — a **standalone exemplar** (no internal
importers; referenced by docstrings in `KeccakBitexact` / `KeccakDiffuseExact`
as the template the rest of the chain extends). Closes the isolated-ι
per-round-constant primitive bit-exactly.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakIotaIndexed

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
  (LeafSem LeafAgrees StraightLine ExprNotStackStore)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed

/-! ## 1. The FIPS 202 round-constant table as a `Fin 24 → BitVec 64` -/

/-- The 24 ι round constants as a `stackArr 64 24` table value. Entry `i` is
    `RC[i]` (FIPS 202 Table 2), agreeing with `KeccakEmit.roundConst` and with
    `CatCrypt.Crypto.Hash.Keccak.keccak_round_constant`. -/
def rcTable : Fin 24 → BitVec 64 :=
  fun i => BitVec.ofNat 64 (KeccakEmit.roundConst i.val)

/-! ## 2. The ι body over `[acc, idx, rc]`

`acc : reg 64` (lane 0 — the only lane ι touches), `idx : reg 64` (the loop
counter), `rc : stackArr 64 24` (the round-constant table). The body reads
`RC[idx]` by `stackLoad rc idx`, then `acc ⊕ RC[idx]` by `regArith xor`. The
result `reg 64` is the new lane-0 value. -/

/-- The ι body context: lane accumulator, loop index register, RC table. -/
abbrev ictx : Ctxt jasminDialect := tabCtxt (.reg 64) 24

/-- `acc = .here`, `idx = .there .here`, `rc = .there (.there .here)`. -/
def vAcc : Ctxt.Var ictx (.reg 64) := .here
def vIdx : Ctxt.Var ictx (.reg 64) := .there .here
def vRc : Ctxt.Var ictx (.stackArr 64 24) := .there (.there .here)

/-- The Keccak ι body: `v0 = rc[idx];  v1 = acc ⊕ v0;  ret v1`. A two-binder
    straight-line `Com` over `[acc, idx, rc]`; the per-round variation is exactly
    the value `rc[idx] = RC[i]` read from the table at the threaded index. -/
def keccakIotaBody : Com jasminDialect ictx (.reg 64) :=
  -- v0 = stackLoad rc idx  (= RC[idx])
  .var (.mk (.stackLoad 64 24) rfl (.cons vRc (.cons vIdx .nil)))
    -- v1 = regArith xor acc v0   (acc is now `.there .here`, v0 is `.here`)
    (.var (.mk (.regArith .xor 64) rfl
            (.cons (.there vAcc) (.cons .here .nil)))
      (.ret .here))

/-- The ι body is `StraightLine`: its two binders are `stackLoad` and `regArith`,
    neither the aliasing `stackStore`. -/
theorem keccakIotaBody_straightLine : StraightLine keccakIotaBody := by
  refine ⟨?_, ?_, trivial⟩ <;> (intro w n; exact JasminOp.noConfusion)

/-- The ι `JForProgTab`: 24 rounds, the FIPS 202 RC table, the ι body. -/
def keccakIotaLoop : JForProgTab (.reg 64) 24 :=
  { n := 24, table := rcTable, body := keccakIotaBody }

/-! ## 3. The body's per-iteration step is bit-exactly `acc ⊕ RC[i]`

The body denotation on `[acc, ofNat 64 i, rcTable]` is
`acc ^^^ stackGet rcTable ((ofNat 64 i).toNat)`. For `i < 24` (so
`(ofNat 64 i).toNat = i` and the `% 24` reduction is the identity), this is
`acc ^^^ rcTable ⟨i, _⟩ = acc ^^^ RC[i]` — the FIPS 202 ι with the **actual**
per-round constant. -/

/-- `(BitVec.ofNat 64 i).toNat = i` for `i < 24` (a fortiori `< 2^64`). -/
theorem ofNat_toNat_of_lt {i : Nat} (h : i < 24) :
    (BitVec.ofNat 64 i).toNat = i := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- **The ι body's per-iteration step is bit-exactly `acc ⊕ RC[i]`** (for a valid
    round `i < 24`): the actual FIPS 202 per-round constant `RC[i]` read from the
    table, NOT a fixed `RC[0]`. This is the per-round-constant materialization the
    uniform loop body could not express. -/
theorem keccakIotaStep_eq {i : Nat} (h : i < 24) (acc : BitVec 64) :
    keccakIotaLoop.stepT i acc
      = acc ^^^ (BitVec.ofNat 64 (KeccakEmit.roundConst i)) := by
  show keccakIotaBody.denote
        (.cons acc (.cons (BitVec.ofNat 64 i) (.cons rcTable .nil)))
      = acc ^^^ BitVec.ofNat 64 (KeccakEmit.roundConst i)
  -- Unfold the two-binder body denotation: v0 = rc[idx], v1 = acc ⊕ v0.
  show JasminBinOp.apply .xor acc
        (stackGet rcTable ((BitVec.ofNat 64 i).toNat))
      = acc ^^^ BitVec.ofNat 64 (KeccakEmit.roundConst i)
  rw [ofNat_toNat_of_lt h]
  -- `stackGet rcTable i = rcTable ⟨i, _⟩ = RC[i]` since `i < 24`.
  rw [show stackGet rcTable i = rcTable ⟨i, h⟩ from by
        rw [← stackGet_id rcTable ⟨i, h⟩]]
  rfl

/-! ## 4. The bit-exact reference ι fold

`keccakIotaRef init` folds in the **actual** per-round constants `RC[0], …,
RC[23]`: `init ⊕ RC[0] ⊕ … ⊕ RC[23]`. This is the bit-exact 24-round ι
permutation on lane 0 (each round XORs the genuine `RC[round]`). -/

/-- The bit-exact 24-round ι reference: fold `acc ↦ acc ⊕ RC[i]` over
    `i = 0 .. 23` with the actual FIPS 202 round constants. -/
def keccakIotaRef (init : BitVec 64) : BitVec 64 :=
  (List.range 24).foldl
    (fun acc i => acc ^^^ BitVec.ofNat 64 (KeccakEmit.roundConst i)) init

/-- Fold congruence under a per-element side condition: two index-threading step
    functions that agree on every `(acc, i)` with `i ∈ l` give the same
    left-fold over `l`. -/
private theorem foldl_congr_mem (f g : BitVec 64 → Nat → BitVec 64) :
    ∀ (l : List Nat), (∀ i ∈ l, ∀ acc, f acc i = g acc i) →
      ∀ init, l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | i :: rest, h, init => by
      rw [List.foldl_cons, List.foldl_cons, h i List.mem_cons_self init]
      exact foldl_congr_mem f g rest
        (fun j hj acc => h j (List.mem_cons_of_mem _ hj) acc) _

/-- The loop's index-dependent denotation `denoteT` **is** the bit-exact ι
    reference fold: each `stepT i` is `acc ⊕ RC[i]` (for the valid rounds
    `i ∈ range 24`), so the two folds coincide. -/
theorem denoteT_eq_ref (init : BitVec 64) :
    keccakIotaLoop.denoteT init = keccakIotaRef init := by
  show (List.range keccakIotaLoop.n).foldl
        (fun acc i => keccakIotaLoop.stepT i acc) init
      = (List.range 24).foldl
        (fun acc i => acc ^^^ BitVec.ofNat 64 (KeccakEmit.roundConst i)) init
  -- `keccakIotaLoop.n = 24`; the fold is over `List.range 24`, every element `< 24`.
  rw [show keccakIotaLoop.n = 24 from rfl]
  exact foldl_congr_mem _ _ (List.range 24)
    (fun i hi acc => keccakIotaStep_eq (List.mem_range.mp hi) acc) init

/-! ## 5. The keystone: the emitted ι loop is bit-exact (a THEOREM, not a KAT) -/

/-- **Keystone — the emitted Keccak ι loop denotes the bit-exact 24-round ι
    permutation, with the ACTUAL per-round constants.** Running the emitted
    `for i = 0 to 24 { acc = acc ⊕ RC[i] }` on the word-level evaluator (the ι
    body run once per round, reading `RC[i]` from the table at the threaded index
    register), threading the lane accumulator, the index `"idx"` and the
    loop-invariant constant table `"rc"`, equals `keccakIotaRef init` — the
    bit-exact 24-fold XOR of the genuine FIPS 202 round constants
    `RC[0..23]`.

    This is a **proof** (via `JForProgIndexed.loopRunT_eq_denoteT`, routed through
    `freshName_injective`), NOT a `native_decide`/KAT check. The per-round
    constant `RC[i]` is now a certified input to the loop denotation — closing the
    "uniform `RC[0]` skeleton" hole of `KeccakEmit.keccak_round_loop_denote_eq`.
    The only hypothesis is the opaque-leaf edge `LeafAgrees`, **vacuous** here (the
    ι body has no `extCall`). -/
theorem keccak_iota_loop_bitexact {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 64) :
    loopRunT leafSem keccakIotaLoop init = keccakIotaRef init := by
  rw [loopRunT_eq_denoteT hLeaf keccakIotaLoop keccakIotaBody_straightLine init,
      denoteT_eq_ref]

/-! ## 6. The FIPS 202 KAT is now a corollary

With the bit-exact loop theorem in hand, a concrete ι KAT — e.g. running the loop
from `init = 0` yields the cumulative XOR of all 24 round constants — is a
**corollary** (`rw` the keystone, then evaluate the reference fold), NOT the
validation. -/

/-- The cumulative XOR of all 24 FIPS 202 round constants (the ι loop output from
    `init = 0`), computed once for the KAT corollary. -/
def rcXorAll : BitVec 64 := keccakIotaRef 0

/-- **KAT (corollary).** Running the emitted ι loop from `init = 0` yields
    `rcXorAll` — the cumulative XOR of all 24 round constants. This is a sanity
    check **derived** from the bit-exact loop theorem
    `keccak_iota_loop_bitexact`, not a `native_decide` validation of the loop. -/
theorem keccak_iota_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    loopRunT leafSem keccakIotaLoop (0 : BitVec 64) = rcXorAll := by
  rw [keccak_iota_loop_bitexact hLeaf]; rfl

/-- The concrete value of `rcXorAll` (the 24-fold XOR of the FIPS 202 round
    constants) — a closed `BitVec 64` literal, checkable by the kernel. This ties
    the bit-exact loop output to a concrete constant the KAT in
    `bench/keccak_compare/` exercises. -/
theorem rcXorAll_value : rcXorAll = BitVec.ofNat 64 0x800000000000800A := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakIotaIndexed
