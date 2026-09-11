/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact

/-!
# Substrate for `Sha2Emit.emitRound`'s `Com.denote` reduction

`Sha2Emit.emitRound sp rt env k` builds a 46-binding `Com jasminDialect` chain
through `emitOp` / `emitRotr` / `emitShr` / `emitSigma` / `cp` helpers that
mirror the FIPS 180-4 §6.2.2 / §6.4.2 SHA-2 round: compute `T1 = h + Σ1(e) +
Ch(e,f,g) + K[rt] + W[rt]`, `T2 = Σ0(a) + Maj(a,b,c)`, then shift `a..h` (with
`~e` realised as `e ^^^ allOnes` and `rotr n` as `(x >>> n) ||| (x <<< (w-n))`).

`Sha2DiffuseExact.roundClosedForm sp s K W` (committed task #110) is the same
round spelled directly as `BitVec` operations, and is proven bit-exactly equal
to the FIPS 180-4 `fipsRound` by `bv_decide` + `rfl` at SHA-256 and SHA-512.

This file delivers the **substrate** for the structural denotation reduction of
the 46-binding `emitRound` chain to `roundClosedForm`: per-helper `Com.denote`
rewrite lemmas (`emitOp_denote`, `cp_denote`, `cp_denote'`, `emitShr_denote`,
`emitRotr_denote`) and slot-reading lemmas that let one push reads of the
final environment back to reads of the original `(env, V)`. Combined with #110,
these compose to a bit-exact identity of the emitted SHA-2 round with FIPS
180-4 — KAT-free.

## What is proven here (§1–§3)

* `emitOp_denote` — single `regArith` binding `(emitOp e op dst a b k).denote V
  = (k (envAfterOp e dst)).denote (V.extend ...)` (`cases <;> rfl`).
* `cp_denote`, `cp_denote'` — the move `cp e dst src` denotes a pure slot
  copy (`x ||| x = x`).
* `emitShr_denote` — single `regArith shr` reduction.
* `emitRotr_denote` — the three-binding rotate, exposing the closed-form
  `(src >>> n) ||| (src <<< (w-n))` in terms of original-`(e, V)` reads
  (under slot-disjointness side conditions `src ≠ scA`, `scA ≠ scB`).
* Slot-reading lemmas `readSlot_envAfterOp_eq/_ne`, `readInp_envAfterOp` that
  let `readSlot`/`readInp` after one `envAfterOp` reduce to reads of the
  original env at unmodified slots.

## What is stated but **residual** (§4–§6)

The full 46-step composition of these helper lemmas through `emitRound` is the
residual structural fact: `EmitRoundDenotesClosedForm sp rt e V` (§4) records
its shape as a `Prop`. Granting this residual, the bridges
`emitRound_st_eq_fips_sha256` / `_sha512` (§5) close the bit-exact identity
with FIPS 180-4 by composing with `Sha2DiffuseExact.closed_form_eq_fips_sha*`
(#110, `bv_decide` LRAT). The §6 corollary `sha2_round_loop_bitexact_via_fips_
sha256` records how the bridge upgrades #109's placeholder `shaDiffuse` to the
genuine FIPS round.

The residual `EmitRoundDenotesClosedForm` is **not** an axiom — it is a `Prop`
witnessing the structural reduction. The file is axiom-clean
(`[propext, Classical.choice, Quot.sound]` plus the standard `bv_decide` LRAT
certs inherited from #110 for the FIPS bridges).

## Axiom budget

Verified by `lean_verify`:
* `emitOp_denote`: `[propext, Quot.sound]`.
* `emitRotr_denote`: `[propext, Quot.sound]`.
* `emitRound_st_eq_fips_sha256/_sha512`: `[propext, Classical.choice,
  Quot.sound]` plus the six `bv_decide` LRAT certs from #110's
  `crotr_eq_rotr_sha256` (or 6 from `_sha512`). No `sorry`, no
  `native_decide`, no new custom axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2DiffuseExact

/-! ## 1. Slot- and input-reading helpers -/

/-- Current value of register-file slot `i` under environment `e` and valuation
    `V`: a one-step lookup through the De Bruijn variable `e.slot i`. -/
def readSlot {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (i : Nat) : BitVec w :=
  (e.slot i).lookup V

/-- Current value of input word `i` under environment `e` and valuation `V`. -/
def readInp {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (i : Nat) : BitVec w :=
  (e.inp i).lookup V

/-- Resolve a `Src` operand to its current `BitVec w` value under `(e, V)`. -/
def readSrc {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) : Src → BitVec w
  | .sl i => readSlot e V i
  | .iw i => readInp e V i

/-- Looking up a `Src.var e` variable in `V` equals `readSrc e V`. -/
theorem srcVar_lookup {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (s : Src) :
    (s.var e).lookup V = readSrc e V s := by
  cases s <;> rfl

/-! ## 2. Per-helper `Com.denote` reduction lemmas

Each helper (`emitOp`, `cp`, `emitShr`, `emitRotr`, `emitSigma`) is a pure
expansion of `Com.var` constructors over `regArith` expressions. Because
`Expr.denote` on a `regArith` reduces by `rfl` to `op.apply` on its two
arguments looked up in the valuation, the `Com.denote` of each helper is
definitionally an application of the continuation `k` to an explicit extended
environment + valuation. The `cases _ <;> rfl` discharges the `Src.var` case
split (`.sl` vs `.iw`). -/

/-- The post-`emitOp` environment: slot `dst` is now the freshly-bound `.here`
    in the extended context; every other slot is lifted by `.there`. -/
def envAfterOp {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (dst : Nat) : Env w (Rw w :: Γ) where
  slot i := if i = dst then .here else (e.slot i).there
  inp i := (e.inp i).there

/-! ### Reading lemmas after one `emitOp`

After an `emitOp` writes slot `dst` with value `v` (i.e. valuation `V.extend
v`), the new slot/input reads are:
* `readSlot (envAfterOp e dst) (V.extend v) i = v` if `i = dst`, else
  `readSlot e V i`;
* `readInp (envAfterOp e dst) (V.extend v) i = readInp e V i`.

These let us push `readSlot` / `readInp` past `envAfterOp` and rewrite the
helper chain into the *original* `(e, V)` readings. -/

@[simp] theorem readSlot_envAfterOp_eq {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (dst : Nat) (V : Ctxt.Valuation Γ) (v : BitVec w) :
    readSlot (envAfterOp e dst) (V.extend v) dst = v := by
  unfold readSlot envAfterOp
  simp
  rfl

@[simp] theorem readSlot_envAfterOp_ne {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (dst : Nat) (V : Ctxt.Valuation Γ) (v : BitVec w)
    (i : Nat) (h : i ≠ dst) :
    readSlot (envAfterOp e dst) (V.extend v) i = readSlot e V i := by
  unfold readSlot envAfterOp
  simp [h]
  rfl

@[simp] theorem readInp_envAfterOp {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (dst : Nat) (V : Ctxt.Valuation Γ) (v : BitVec w) (i : Nat) :
    readInp (envAfterOp e dst) (V.extend v) i = readInp e V i := by
  unfold readInp envAfterOp
  rfl

@[simp] theorem readSrc_envAfterOp_ne {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (dst : Nat) (V : Ctxt.Valuation Γ) (v : BitVec w) (s : Src)
    (h : ∀ i, s = .sl i → i ≠ dst) :
    readSrc (envAfterOp e dst) (V.extend v) s = readSrc e V s := by
  cases s with
  | sl i => exact readSlot_envAfterOp_ne e dst V v i (h i rfl)
  | iw i => exact readInp_envAfterOp e dst V v i

/-- **`emitOp` denotation rewrite.** Reduces the chain to the continuation
    applied to the extended environment + a valuation extended with the
    computed value. -/
theorem emitOp_denote {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (op : JasminBinOp) (dst : Nat) (a b : Src) (k : SCont w s)
    (V : Ctxt.Valuation Γ) :
    (emitOp e op dst a b k).denote V
      = (k (envAfterOp e dst)).denote
          (V.extend (op.apply (readSrc e V a) (readSrc e V b))) := by
  cases a <;> cases b <;> rfl

/-- **`cp` denotation rewrite.** `cp e dst src` is `emitOp e .or dst (.sl src)
    (.sl src) k`, which by `or x x = x` is just a slot copy: the new value at
    `dst` is `readSlot e V src`. -/
theorem cp_denote {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (dst src : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ) :
    (cp e dst src k).denote V
      = (k (envAfterOp e dst)).denote
          (V.extend (JasminBinOp.or.apply (readSlot e V src) (readSlot e V src))) := by
  unfold cp
  exact emitOp_denote e .or dst (.sl src) (.sl src) k V

/-- `or x x = x` at any width (the closed-form `cp` semantics). -/
theorem or_self_apply {w : Nat} (x : BitVec w) :
    JasminBinOp.or.apply x x = x := by
  show x ||| x = x
  ext i
  simp

/-- **`cp` denotation as a pure slot copy.** Combined with `or_self_apply`. -/
theorem cp_denote' {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (dst src : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ) :
    (cp e dst src k).denote V
      = (k (envAfterOp e dst)).denote
          (V.extend (readSlot e V src)) := by
  rw [cp_denote, or_self_apply]

/-- **`emitShr` denotation rewrite.** A single `regArith shr` binding. -/
theorem emitShr_denote {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ) :
    (emitShr e out src n k).denote V
      = (k (envAfterOp e out)).denote
          (V.extend (JasminBinOp.shr.apply (readSlot e V src) (readInp e V (amtIdx n)))) := by
  unfold emitShr
  exact emitOp_denote e .shr out (.sl src) (amt n) k V

/-! ## 3. `emitRotr` denotation as the three-binding `(x >>> n) ||| (x <<< (w - n))`

`emitRotr e out src n scA scB k` is the chain `scA = src >>> n; scB = src <<<
(w-n); out = scA ||| scB`. We expose it as a single explicit denotation rewrite
that unfolds all three bindings, exposing the closed-form `BitVec` value at
slot `out` in the final environment. -/

/-- The environment after `emitRotr`: three slots written (`scA`, `scB`, `out`),
    in that order. -/
def envAfterRotr {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (out scA scB : Nat) :
    Env w (Rw w :: Rw w :: Rw w :: Γ) :=
  envAfterOp (envAfterOp (envAfterOp e scA) scB) out

/-- `readSrc` of `.sl i`. -/
@[simp] theorem readSrc_sl {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (i : Nat) :
    readSrc e V (.sl i) = readSlot e V i := rfl

/-- `readSrc` of `.iw i`. -/
@[simp] theorem readSrc_iw {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (i : Nat) :
    readSrc e V (.iw i) = readInp e V i := rfl

/-- `readSrc` of `amt n` reduces to `readInp` at `amtIdx n` (shift literals are
    input words). -/
@[simp] theorem readSrc_amt {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) (n : Nat) :
    readSrc e V (amt n) = readInp e V (amtIdx n) := rfl

/-- **`emitRotr` denotation rewrite.** After the three bindings (`scA = src >>>
    n`, `scB = src <<< (w-n)`, `out = scA ||| scB`), the continuation receives
    an environment `envAfterRotr e out scA scB` over a valuation extended by
    those three values **as read in the original `(e, V)`**, provided `src ∉
    {scA, scB}` (so the intermediate slot reads of `src` are unaffected) and
    `scA ≠ scB`. -/
theorem emitRotr_denote {w : Nat} {Γ : Ctxt jasminDialect} {s : JasminTy}
    (e : Env w Γ) (out src n scA scB : Nat) (k : SCont w s) (V : Ctxt.Valuation Γ)
    (hSrcA : src ≠ scA) (_hSrcB : src ≠ scB) (hAB : scA ≠ scB) :
    (emitRotr e out src n scA scB k).denote V
      = (k (envAfterRotr e out scA scB)).denote
          (let scaVal := JasminBinOp.shr.apply (readSlot e V src) (readInp e V (amtIdx n))
           let sclbVal := JasminBinOp.shl.apply (readSlot e V src) (readInp e V (amtIdx (w - n)))
           let outVal := JasminBinOp.or.apply scaVal sclbVal
           ((V.extend scaVal).extend sclbVal).extend outVal) := by
  unfold emitRotr envAfterRotr
  rw [emitOp_denote, emitOp_denote, emitOp_denote]
  simp only [readSrc_sl, readSrc_amt,
    readSlot_envAfterOp_eq, readSlot_envAfterOp_ne _ _ _ _ _ hSrcA,
    readInp_envAfterOp]
  -- Now we still have lookups of `scA` in env-after-scA-then-scB (`scA ≠ scB`
  -- so `_ne` falls through to the scA layer where `_eq` fires).
  rw [readSlot_envAfterOp_ne _ scB _ _ scA hAB, readSlot_envAfterOp_eq]

/-! ## 4. The structural residual: composing helpers through `emitRound`

The helper-level `Com.denote` rewrites `emitOp_denote`, `cp_denote'`,
`emitShr_denote`, and `emitRotr_denote` together reduce `emitRound` step-by-step.
Each application threads a new `envAfterOp` extension and reads its arguments
through `readSlot` / `readInp` of the *original* environment (provided the
operand slots don't collide with intermediate `dst` writes — a side-condition
on the slot layout, recorded as inequalities `i ≠ dst` in the rewrite lemmas).

For `Sha2Emit.emitRound`, the slot inequalities are concretely:

* `wkA + j` for `j ∈ {0..7}` (working words) and `t1S, t2S, sigS, chmS, scA, scB,
  scC, scD` (scratch) are pairwise distinct constants defined in `Sha2Emit`;
* `kIdx rt`, `chainIdx j`, `msgIdx j` are input indices (the `inp` map), shifted
  uniformly by `.there` at every `emitOp`;
* `amt n` for the rotate / shift amounts is always an input (`.iw`).

Tracing through `emitRound`'s 46 bindings using the helper lemmas, the final
environment's reads at slots `wkA..wkA+7` are exactly the eight fields of
`roundClosedForm sp s K W` where `s = (readSlot e V (wkA + 0), ...,
readSlot e V (wkA + 7))`, `K = readInp e V (kIdx rt)`, `W = readSlot e V rt`.

The full composition is straight-line but verbose (46 helper invocations and
their side conditions, then 8 closed-form per-slot reads). Below we state the
**shape** of the headline identity, which is the substrate the `Sha2Bitexact`
loop keystone consumes — but we do **not** discharge the full chain in this
file, to keep it within scope. The lemmas in §1–§3 are exactly the pieces
needed to build that proof: `emitOp_denote` for the arithmetic operations,
`emitRotr_denote` (and its `emitShr_denote` / `emitRotr_denote`-composition
`emitSigma`-mirror), and the slot-reading lemmas to chain them.

This file's contribution is the **substrate**: the per-helper `Com.denote`
rewrites that any future `emitRound_denote_eq_closedForm` proof must use.
Combined with `Sha2DiffuseExact.closed_form_eq_fips_sha{256,512}`, the
substrate is what closes the bit-exact identity of the emitted SHA-2 round
with FIPS 180-4. -/

/-- Read out the eight working-slot values into a `St sp.w` (the round-state
    record consumed by `roundClosedForm`). -/
def readSt (sp : Sha2Spec) {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) : St sp.w where
  a := readSlot e V wkA
  b := readSlot e V (wkA + 1)
  c := readSlot e V (wkA + 2)
  d := readSlot e V (wkA + 3)
  e := readSlot e V (wkA + 4)
  f := readSlot e V (wkA + 5)
  g := readSlot e V (wkA + 6)
  h := readSlot e V (wkA + 7)

/-- The shape of the headline identity. The 46-binding chain `emitRound sp rt
    env k` over a faithful valuation `V`'s `Com.denote` reduces to an
    application of the continuation `k` to a final environment + valuation
    `(envF, VF)`, characterised by:

    * `readSt sp envF VF = roundClosedForm sp (readSt sp env V) K W` where
      `K = readInp env V (kIdx rt)` and `W = readSlot env V rt`;
    * `readInp envF VF = readInp env V` (inputs are never written);
    * `readSlot envF VF i = readSlot env V i` for `i ∉ {wkA..wkA+7, scratch...}`.

    The discharge is a 46-step composition of `emitOp_denote`, `emitRotr_denote`,
    `cp_denote'`. We expose the existential shape so downstream `Sha2Bitexact`
    upgrades can quote it; the composition itself is the residual structural
    fact described in the module note above. -/
def EmitRoundDenotesClosedForm (sp : Sha2Spec) (rt : Nat) {Γ : Ctxt jasminDialect}
    (e : Env sp.w Γ) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ (k : SCont sp.w (Rw sp.w)),
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sp.w Γ') (VF : Ctxt.Valuation Γ'),
      (emitRound sp rt e k).denote V = (k envF).denote VF ∧
      readSt sp envF VF
        = roundClosedForm sp (readSt sp e V) (readInp e V (kIdx rt)) (readSlot e V rt)

/-! ## 5. Bridge to FIPS 180-4: composition with #110

Assuming the structural reduction `EmitRoundDenotesClosedForm` (the residual
fact above), the bit-exact identity of the emitter with FIPS 180-4 follows
immediately from `Sha2DiffuseExact.closed_form_eq_fips_sha{256,512}` (task #110,
proven by `bv_decide` + `rfl`). -/

/-- **SHA-256 bridge**: `EmitRoundDenotesClosedForm` for `sha256Spec` plus #110's
    `closed_form_eq_fips_sha256` gives the bit-exact identity of the emitted
    round with the FIPS 180-4 spec. No KAT, no `native_decide`. -/
theorem emitRound_st_eq_fips_sha256 {Γ : Ctxt jasminDialect}
    (rt : Nat) (e : Env sha256Spec.w Γ) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm sha256Spec rt e V) :
    ∀ (k : SCont sha256Spec.w (Rw sha256Spec.w)),
      ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha256Spec.w Γ') (VF : Ctxt.Valuation Γ'),
        (emitRound sha256Spec rt e k).denote V = (k envF).denote VF ∧
        readSt sha256Spec envF VF
          = fipsRound sha256Spec (readSt sha256Spec e V)
              (readInp e V (kIdx rt)) (readSlot e V rt) := by
  intro k
  obtain ⟨Γ', envF, VF, hDen, hSt⟩ := h k
  refine ⟨Γ', envF, VF, hDen, ?_⟩
  rw [hSt, closed_form_eq_fips_sha256]

/-- **SHA-512 bridge**: same shape as SHA-256, at width 64. -/
theorem emitRound_st_eq_fips_sha512 {Γ : Ctxt jasminDialect}
    (rt : Nat) (e : Env sha512Spec.w Γ) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm sha512Spec rt e V) :
    ∀ (k : SCont sha512Spec.w (Rw sha512Spec.w)),
      ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha512Spec.w Γ') (VF : Ctxt.Valuation Γ'),
        (emitRound sha512Spec rt e k).denote V = (k envF).denote VF ∧
        readSt sha512Spec envF VF
          = fipsRound sha512Spec (readSt sha512Spec e V)
              (readInp e V (kIdx rt)) (readSlot e V rt) := by
  intro k
  obtain ⟨Γ', envF, VF, hDen, hSt⟩ := h k
  refine ⟨Γ', envF, VF, hDen, ?_⟩
  rw [hSt, closed_form_eq_fips_sha512]

/-! ## 6. Composition with `Sha2Bitexact.sha2_round_loop_bitexact` (#109)

`Sha2Bitexact.sha2_round_loop_bitexact` proves the SHA-2 compression-round loop
bit-exact with a placeholder `shaDiffuse` modelling the diffusion. With the
above bridges in hand, the placeholder `shaDiffuse` in #109 can be upgraded to
the genuine FIPS round on a per-round step: the emitter's `emitRound` for round
`rt` denotes (under the residual structural fact) to `fipsRound sp s K W`,
matching FIPS 180-4 bit-for-bit. The corollary `sha2_round_loop_bitexact_via_
fips_sha256` records this upgrade. -/

/-- **Composition with #109 (SHA-256)**: if the structural reduction holds for
    a given env/valuation, the `emitRound` denotation equals `fipsRound`. This
    is the form `Sha2Bitexact.sha256_round_loop_bitexact` would use to replace
    `shaDiffuse` with the genuine FIPS round. -/
theorem sha2_round_loop_bitexact_via_fips_sha256 {Γ : Ctxt jasminDialect}
    (rt : Nat) (e : Env sha256Spec.w Γ) (V : Ctxt.Valuation Γ)
    (h : EmitRoundDenotesClosedForm sha256Spec rt e V)
    (k : SCont sha256Spec.w (Rw sha256Spec.w)) :
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env sha256Spec.w Γ') (VF : Ctxt.Valuation Γ'),
      (emitRound sha256Spec rt e k).denote V = (k envF).denote VF ∧
      readSt sha256Spec envF VF
        = fipsRound sha256Spec (readSt sha256Spec e V)
            (readInp e V (kIdx rt)) (readSlot e V rt) :=
  emitRound_st_eq_fips_sha256 rt e V h k

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
