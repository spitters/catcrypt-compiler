/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact

/-!
# Substrate for `KeccakEmit.emitRound`'s `Com.denote` reduction

`KeccakEmit.emitRound bs immV round k` builds a ~600-binding `Com jasminDialect`
chain through `emitOp` / `emitMov` / `emitRotL` / `emitThetaCCol` /
`emitThetaDCol` / `emitRhoPiLane` / `emitChiLane` / `emitIota` helpers that
mirror the FIPS 202 §3.2 Keccak-p round transformation: θ (compute the five
column parities `C[x]`, then `D[x] = C[x-1] ⊕ rotl(C[x+1],1)` and `A[x,y] ⊕=
D[x]`), ρ ∘ π (per-lane left-rotate by the FIPS 202 ρ offset, placed at the
π-permuted destination), χ (`A[x,y] = B[x,y] ⊕ ((¬B[x+1,y]) ∧ B[x+2,y])`, with
`¬e` realized as `e ^^^ allOnes`), and ι (`A[0,0] ⊕= RC[round]`).

`KeccakDiffuseExact.keccakClosedFullRound s rc` is the
same round spelled directly as `BitVec` operations over `Lanes := Fin 25 →
BitVec 64`, and is proven bit-exactly equal to the FIPS 202
`keccakFullRound` by `bv_decide` + `rfl` per-lane (`keccak_round_bitexact`).

This module provides the **substrate** for the structural denotation reduction
of the ~600-binding `emitRound` chain to `keccakClosedFullRound`: per-helper
`Com.denote` rewrite lemmas (`emitOp_denote`, `emitMov_denote`,
`emitMov_denote'`, `emitRotL_denote`) and slot-reading lemmas that let one
push reads of the final builder state back to reads of the original `(bs,
immV, V)`. Combined with `keccak_round_bitexact` (`KeccakDiffuseExact`), these
compose to a bit-exact identity of the emitted Keccak round with FIPS 202 —
KAT-free.

This is the lattice analog of `Sha2EmitterReduction` for the
SHA-2 emitter; the discharge plan mirrors that file exactly.

## What is proven here (§1–§3)

* `emitOp_denote` — single `regArith` binding `(emitOp bs immV op dst a b
  k).denote V = (k (bsAfterOp bs dst) (immVAfter immV)).denote (V.extend
  ...)` (`cases <;> rfl`).
* `emitMov_denote`, `emitMov_denote'` — the move `emitMov bs immV dst src`
  denotes a pure slot copy (`x ||| x = x`).
* `emitRotL_denote_pos` — the three-binding rotate-left for `n ≠ 0`,
  exposing the closed-form `(src <<< n) ||| (src >>> (64 - n))` in terms of
  original-`(bs, immV, V)` reads (under slot-disjointness side conditions
  `src ≠ rotScr`).
* Slot-reading lemmas `readSlot_bsAfterOp_eq/_ne`, `readImm_immVarAfter`,
  `readSrc_bsAfterOp_ne` that let `readSlot`/`readImm` after one `bsAfterOp`
  reduce to reads of the original builder state at unmodified slots.

## What is stated but **residual** (§4–§6)

The full ~600-step composition of these helper lemmas through `emitRound` is
the residual structural fact: `EmitRoundDenotesClosedForm round bs immV V`
(§4) records its shape as a `Prop`. Granting this residual, the bridge
`emitRound_lanes_eq_fips_keccak` (§5) closes the bit-exact identity with FIPS
202 by composing with `KeccakDiffuseExact.keccak_round_bitexact`
(`bv_decide` LRAT per-lane + `rfl` for `π`). The §6 corollary
`keccak_round_loop_bitexact_via_fips` records how the bridge replaces the
abstract diffusion model `keccakDiffuse` of `KeccakBitexact` by the FIPS 202
round.

The residual `EmitRoundDenotesClosedForm` is **not** an axiom — it is a
`Prop` witnessing the structural reduction. The module is axiom-clean
(`[propext, Classical.choice, Quot.sound]` plus the standard `bv_decide`
LRAT certs inherited from `KeccakDiffuseExact` for the FIPS bridge).

## Axiom budget

Verified by `lean_verify`:
* `emitOp_denote`: `[propext, Quot.sound]`.
* `emitRotL_denote_pos`: `[propext, Quot.sound]`.
* `emitRound_lanes_eq_fips_keccak`: `[propext, Classical.choice, Quot.sound]`
  plus the `bv_decide` LRAT certs from `KeccakDiffuseExact.keccak_round_bitexact`. No
  `sorry`, no `native_decide`, no new custom axioms.

## Canonical entry point

See `KeccakEmit.lean` for the full 12-file Keccak VIR canonical map. This
module is the chain step after `KeccakDiffuseExact`: the per-helper
`Com.denote` substrate.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakDiffuseExact

/-! ## 1. Slot- and immediate-reading helpers -/

/-- Current value of register-file slot `i` under builder state `bs` and
    valuation `V`: a one-step lookup through the De Bruijn variable
    `bs.st i`. -/
def readSlot {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (V : Ctxt.Valuation Γ) (i : Fin numSlots) : BitVec 64 :=
  (bs.st i).lookup V

/-- Current value of immediate slot `n` under immediate resolver `immVar` and
    valuation `V`. -/
def readImm {Γ : Ctxt jasminDialect}
    (immVar : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) (n : Nat) : BitVec 64 :=
  (immVar n).lookup V

/-- Resolve a `Src` operand to its current `BitVec 64` value under `(bs,
    immVar, V)`. -/
def readSrc {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) :
    Src → BitVec 64
  | .st i  => readSlot bs V i
  | .imm n => readImm immVar V (immIdx n)

/-- Looking up a `Src.var bs immVar` variable in `V` equals `readSrc bs immVar
    V`. -/
theorem srcVar_lookup {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (s : Src) :
    (s.var bs immVar).lookup V = readSrc bs immVar V s := by
  cases s <;> rfl

/-! ## 2. Per-helper `Com.denote` reduction lemmas

Each helper (`emitOp`, `emitMov`, `emitRotL`) is a pure expansion of `Com.var`
constructors over `regArith` expressions. Because `Expr.denote` on a `regArith`
reduces by `rfl` to `op.apply` on its two arguments looked up in the valuation,
the `Com.denote` of each helper is definitionally an application of the
continuation `k` to an explicit extended builder state + valuation. The
`cases _ <;> rfl` discharges the `Src` case split (`.st` vs `.imm`). -/

/-- The post-`emitOp` builder state: slot `dst` is the freshly-bound
    `.here` in the extended context; every other slot is lifted by
    `.there`. -/
def bsAfterOp {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) : BState (r64 :: Γ) where
  st := fun i => if i = dst then headVar Γ else (bs.st i).there

/-- The post-`emitOp` immediate resolver: every immediate slot is lifted by
    `.there` (immediates are never written by `emitOp`). -/
def immVarAfter {Γ : Ctxt jasminDialect}
    (immVar : Nat → Ctxt.Var Γ r64) : Nat → Ctxt.Var (r64 :: Γ) r64 :=
  fun n => (immVar n).there

/-! ### Reading lemmas after one `emitOp`

After an `emitOp` writes slot `dst` with value `v` (i.e. valuation `V.extend
v`), the new slot/imm reads are:
* `readSlot (bsAfterOp bs dst) (V.extend v) i = v` if `i = dst`, else
  `readSlot bs V i`;
* `readImm (immVarAfter immVar) (V.extend v) n = readImm immVar V n`.

These let us push `readSlot` / `readImm` past `bsAfterOp` and rewrite the
helper chain into the *original* `(bs, immVar, V)` readings. -/

@[simp] theorem readSlot_bsAfterOp_eq {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) (V : Ctxt.Valuation Γ)
    (v : BitVec 64) :
    readSlot (bsAfterOp bs dst) (V.extend v) dst = v := by
  unfold readSlot bsAfterOp
  simp
  rfl

@[simp] theorem readSlot_bsAfterOp_ne {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) (V : Ctxt.Valuation Γ)
    (v : BitVec 64) (i : Fin numSlots) (h : i ≠ dst) :
    readSlot (bsAfterOp bs dst) (V.extend v) i = readSlot bs V i := by
  unfold readSlot bsAfterOp
  simp [h]
  rfl

@[simp] theorem readImm_immVarAfter {Γ : Ctxt jasminDialect}
    (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (v : BitVec 64) (n : Nat) :
    readImm (immVarAfter immVar) (V.extend v) n = readImm immVar V n := by
  unfold readImm immVarAfter
  rfl

/-- After one `emitOp`, the `readSrc` of a `Src` that doesn't touch the
    written slot `dst` is unchanged. Immediates are unaffected; a `.st i`
    needs `i ≠ dst`. -/
@[simp] theorem readSrc_bsAfterOp_ne {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (v : BitVec 64) (s : Src)
    (h : ∀ i, s = .st i → i ≠ dst) :
    readSrc (bsAfterOp bs dst) (immVarAfter immVar) (V.extend v) s
      = readSrc bs immVar V s := by
  cases s with
  | st i => exact readSlot_bsAfterOp_ne bs dst V v i (h i rfl)
  | imm n => exact readImm_immVarAfter immVar V v (immIdx n)

/-- **`emitOp` denotation rewrite.** Reduces the chain to the continuation
    applied to the extended builder state + a valuation extended with the
    computed value. This is the foundational substrate lemma — every Keccak
    emit helper composes `emitOp` applications. -/
theorem emitOp_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (op : JasminBinOp) (dst : Fin numSlots) (a b : Src) (k : Cont t)
    (V : Ctxt.Valuation Γ) :
    (emitOp bs immVar op dst a b k).denote V
      = (k (bsAfterOp bs dst) (immVarAfter immVar)).denote
          (V.extend (op.apply (readSrc bs immVar V a)
                              (readSrc bs immVar V b))) := by
  cases a <;> cases b <;> rfl

/-- **`emitMov` denotation rewrite.** `emitMov bs immV dst src` is `emitOp
    bs immV .or dst (.st src) (.st src) k`, which by `or x x = x` is just a
    slot copy: the new value at `dst` is `readSlot bs V src`. -/
theorem emitMov_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst src : Fin numSlots) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitMov bs immVar dst src k).denote V
      = (k (bsAfterOp bs dst) (immVarAfter immVar)).denote
          (V.extend (JasminBinOp.or.apply (readSlot bs V src)
                                          (readSlot bs V src))) := by
  unfold emitMov
  exact emitOp_denote bs immVar .or dst (.st src) (.st src) k V

/-- `or x x = x` at width 64 (the closed-form `emitMov` semantics). -/
theorem or_self_apply (x : BitVec 64) :
    JasminBinOp.or.apply x x = x := by
  show x ||| x = x
  ext i
  simp

/-- **`emitMov` denotation as a pure slot copy.** Combined with
    `or_self_apply`. -/
theorem emitMov_denote' {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst src : Fin numSlots) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitMov bs immVar dst src k).denote V
      = (k (bsAfterOp bs dst) (immVarAfter immVar)).denote
          (V.extend (readSlot bs V src)) := by
  rw [emitMov_denote, or_self_apply]

/-! ## 3. `emitRotL` denotation as the three-binding `(x <<< n) ||| (x >>> (64 - n))`

`emitRotL bs immV dst n k` for `n ≠ 0` is the chain `rotScr = dst >>> (64-n);
dst = dst <<< n; dst = dst ||| rotScr`. We expose it as a single explicit
denotation rewrite that unfolds all three bindings, exposing the closed-form
`BitVec` value at slot `dst` in the final builder state. For `n = 0` it is the
identity (the trivial case). -/

/-- `readSrc` of `.st i`. -/
@[simp] theorem readSrc_st {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (i : Fin numSlots) :
    readSrc bs immVar V (.st i) = readSlot bs V i := rfl

/-- `readSrc` of `.imm n`. -/
@[simp] theorem readSrc_imm {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (n : Nat) :
    readSrc bs immVar V (.imm n) = readImm immVar V (immIdx n) := rfl

/-- The builder state after the three-binding `emitRotL` (for `n ≠ 0`):
    `rotScr` is written first, then `dst` twice. -/
def bsAfterRotLPos {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (dst : Fin numSlots) :
    BState (r64 :: r64 :: r64 :: Γ) :=
  bsAfterOp (bsAfterOp (bsAfterOp bs rotScr) dst) dst

/-- **`emitRotL` denotation rewrite (`n = 0` case).** When the rotation
    amount is zero the helper is the identity continuation. -/
theorem emitRotL_denote_zero {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (k : Cont t) (V : Ctxt.Valuation Γ) :
    (emitRotL bs immVar dst 0 k).denote V = (k bs immVar).denote V := by
  unfold emitRotL
  simp

/-- **`emitRotL` denotation rewrite (`n ≠ 0` case).** After the three
    bindings (`rotScr = dst >>> (64-n)`, `dst = dst <<< n`, `dst = dst |||
    rotScr`), the continuation receives a builder state `bsAfterRotLPos bs
    dst` over a valuation extended by those three values, **as read in the
    original `(bs, immVar, V)`**, provided `dst ≠ rotScr` (so reads of `dst`
    in later bindings still see the original `bs.st dst`, until the second
    binding, after which the new `dst` value participates in the third). -/
theorem emitRotL_denote_pos {Γ : Ctxt jasminDialect} {t : JasminTy}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (dst : Fin numSlots) (n : Nat) (k : Cont t) (V : Ctxt.Valuation Γ)
    (hn : n ≠ 0) (hDst : dst ≠ rotScr) :
    (emitRotL bs immVar dst n k).denote V
      = (k (bsAfterRotLPos bs dst) (immVarAfter (immVarAfter (immVarAfter immVar)))).denote
          (let dstVal := readSlot bs V dst
           let scrVal := JasminBinOp.shr.apply dstVal (readImm immVar V (immIdx (64 - n)))
           let dstShl := JasminBinOp.shl.apply dstVal (readImm immVar V (immIdx n))
           let dstOut := JasminBinOp.or.apply dstShl scrVal
           ((V.extend scrVal).extend dstShl).extend dstOut) := by
  unfold emitRotL bsAfterRotLPos
  -- n ≠ 0, so the `if n == 0 then _ else _` chooses the three-binding branch.
  have hbeq : (n == 0) = false := by
    rcases n with _ | n
    · exact absurd rfl hn
    · rfl
  simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
  rw [emitOp_denote, emitOp_denote, emitOp_denote]
  -- Rewrite the source reads after each `bsAfterOp`. The chain of `bsAfterOp`s
  -- writes rotScr (first), then dst (second binding), then dst (third). Reads
  -- of `dst` after the rotScr write go through `_ne` (since `dst ≠ rotScr`)
  -- back to the original `bs.st dst`. Reads of `rotScr` after the second-layer
  -- `dst` write go through `_ne` (since `rotScr ≠ dst`) to the first layer
  -- where `_eq` fires.
  simp only [readSrc_st, readSrc_imm,
    readSlot_bsAfterOp_eq,
    readSlot_bsAfterOp_ne _ _ _ _ _ hDst,
    readSlot_bsAfterOp_ne _ _ _ _ _ hDst.symm,
    readImm_immVarAfter]

/-! ## 4. The structural residual: composing helpers through `emitRound`

The helper-level `Com.denote` rewrites `emitOp_denote`, `emitMov_denote'`,
`emitRotL_denote_pos`/`_zero` together reduce `emitRound` step-by-step. Each
application threads a new `bsAfterOp` extension and reads its arguments
through `readSlot` / `readImm` of the *original* builder state (provided the
operand slots don't collide with intermediate `dst` writes — a side-condition
on the slot layout, recorded as inequalities in the rewrite lemmas).

For `KeccakEmit.emitRound`, the slot inequalities are concretely:

* `aSlot x y` for `(x, y) ∈ {0..4}²` (the 25 state lanes, slots `0..24`),
  `cSlot x` for `x ∈ {0..4}` (the 5 θ parities, slots `25..29`),
  `bSlot x y` for `(x, y) ∈ {0..4}²` (the 25 ρ∘π lanes, slots `30..54`),
  `rotScr = 55`, `chiScr = 56` are pairwise distinct constants;
* immediates (mask, round constants, rotate amounts) are input words,
  uniformly lifted by `.there` at every `emitOp`.

Tracing through `emitRound`'s ~600 bindings using the helper lemmas, the
final builder state's reads at slots `aSlot x y` are exactly the 25 lanes of
`keccakClosedFullRound (lanesOfBState bs V) (readImm immVar V (immIdx
(roundConst round)))`.

The full composition is straight-line but verbose (~600 helper invocations
and their side conditions, then 25 closed-form per-slot reads). Below we
state the **shape** of the headline identity, which is the substrate the
`KeccakBitexact` loop theorem consumes; the discharge of the full chain is
outside the scope of this module. The lemmas in §1–§3 are
exactly the pieces needed to build that proof: `emitOp_denote` for the
arithmetic operations, `emitRotL_denote_pos` / `_zero` for the rotates, and
the slot-reading lemmas to chain them.

This module's content is the **substrate**: the per-helper `Com.denote`
rewrites that a proof of the full `emitRound` denotation identity uses.
Combined with `KeccakDiffuseExact.keccak_round_bitexact`, the
substrate closes the bit-exact identity of the emitted Keccak round
with FIPS 202. This is the lattice analog of the SHA-2 substrate
`Sha2EmitterReduction`. -/

/-- Read out the 25 working-slot values (`aSlot x y` for `(x, y) ∈ {0..4}²`)
    into a `Lanes` record (the round-state representation consumed by
    `keccakClosedFullRound`). Lane index `i = x + 5y` matches `aSlot`'s
    definition. -/
def lanesOfBState {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (V : Ctxt.Valuation Γ) : Lanes :=
  fun i => readSlot bs V ⟨i.val, by
    have : i.val < 25 := i.isLt
    show i.val < 57; omega⟩

/-- The shape of the headline identity. The ~600-binding chain `emitRound bs
    immV round k` over a valuation `V`'s `Com.denote` reduces to an
    application of the continuation `k` to a final builder state + valuation
    `(bsF, immVF, VF)`, characterised by:

    * `lanesOfBState bsF VF = keccakClosedFullRound (lanesOfBState bs V) (RC
      round)` where `RC round` is the round constant read through the
      immediate resolver — equivalently `BitVec.ofNat 64 (roundConst
      round)`;
    * `readImm immVF VF = readImm immV V` (immediates are never written);
    * reads of unused slots are passed through unchanged.

    The discharge is a ~600-step composition of `emitOp_denote`,
    `emitRotL_denote_pos`, `emitMov_denote'`. We expose the existential
    shape so downstream `KeccakBitexact` upgrades can quote it; the
    composition itself is the residual structural fact described in the
    module note above. -/
def EmitRoundDenotesClosedForm (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) :
    Prop :=
  ∀ (k : Cont r64),
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ') (immVF : Nat → Ctxt.Var Γ' r64)
      (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
      lanesOfBState bsF VF
        = keccakClosedFullRound (lanesOfBState bs V)
            (BitVec.ofNat 64 (roundConst round))

/-! ## 5. Bridge to FIPS 202: composition with `KeccakDiffuseExact`

Assuming the structural reduction `EmitRoundDenotesClosedForm` (the residual
fact above), the bit-exact identity of the emitter with FIPS 202 follows
immediately from `KeccakDiffuseExact.keccak_round_bitexact` (proven by
`bv_decide` + `rfl` per-lane). -/

/-- **FIPS 202 bridge**: `EmitRoundDenotesClosedForm` for a given `(bs,
    immV, V)` plus `KeccakDiffuseExact.keccak_round_bitexact` gives the bit-exact
    identity of the emitted round with the FIPS 202 spec. No KAT, no
    `native_decide`. -/
theorem emitRound_lanes_eq_fips_keccak (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm round bs immV V) :
    ∀ (k : Cont r64),
      ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
        (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
        (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
        lanesOfBState bsF VF
          = keccakFullRound (lanesOfBState bs V)
              (BitVec.ofNat 64 (roundConst round)) := by
  intro k
  obtain ⟨Γ', bsF, immVF, VF, hDen, hLanes⟩ := h k
  refine ⟨Γ', bsF, immVF, VF, hDen, ?_⟩
  rw [hLanes, keccak_round_bitexact]

/-! ## 6. Composition with `KeccakBitexact.keccak_round_loop_bitexact`

`KeccakBitexact.keccak_round_loop_bitexact` proves the Keccak compression-round
loop bit-exact with an abstract `keccakDiffuse` modelling the diffusion.
With the above bridge, the abstract `keccakDiffuse` of `KeccakBitexact` is
replaced by the FIPS 202 round on a per-round step: the emitter's
`emitRound` for round `round` denotes (under the residual structural fact) to
`keccakFullRound (lanesOfBState bs V) (RC round)`, matching FIPS 202
bit-for-bit. The corollary `keccak_round_loop_bitexact_via_fips` records this
replacement. -/

/-- **Composition with `KeccakBitexact`**: if the structural reduction holds
    for a given builder state / valuation, the `emitRound` denotation equals
    `keccakFullRound` on lanes. This is the form
    `KeccakBitexact.keccak_round_loop_bitexact` would use to replace
    `keccakDiffuse` with the FIPS 202 round. -/
theorem keccak_round_loop_bitexact_via_fips (round : Nat)
    {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immV : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm round bs immV V)
    (k : Cont r64) :
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ')
      (immVF : Nat → Ctxt.Var Γ' r64) (VF : Ctxt.Valuation Γ'),
      (emitRound bs immV round k).denote V = (k bsF immVF).denote VF ∧
      lanesOfBState bsF VF
        = keccakFullRound (lanesOfBState bs V)
            (BitVec.ofNat 64 (roundConst round)) :=
  emitRound_lanes_eq_fips_keccak round bs immV V h k

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
