/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

/-!
# Scalable loop artifact: `RFor` realizes a fold (no unrolling)

The compile-from-hax compression proofs in `CompileFromHaxCompressRound.lean`
discharge value-correctness by *unrolling* a bounded loop into a flat
let-chain (`compUnroll`/`stIter`).  That gives a genuine theorem, but the proof
term grows with the trip count `N`: a concrete `N = 64` instantiation
materialises a ~1700-binder term (OOM / kernel timeout on a small box).

This file demonstrates the *scalable* alternative at the operational-semantics
layer.  A `LowCT.RFor` loop is emitted by `JasminPrint` as a real
`for i = 0 to n` loop (never unrolled), and its `RustExec` big-step semantics
(`forZero` / `forSucc`) is a structural fold over the trip count.  We prove that
the loop's final state equals an explicit fold by induction on `n` — an `O(1)`
proof term, independent of `N`.

The witness body here is a running accumulator `acc := acc + i` (counter `i`),
the simplest non-trivial fold.  The SHA-256 compression body (σ/Ch/Maj over the
8-word working state, stored in scalar slots) is realised by the *same*
`forZero`/`forSucc` induction with a heavier per-step characterisation; the
scalability argument — proof term size constant in `N` — is exactly the one
established below.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCT

/-- The state-fold a `RFor x n body` loop computes, given a per-iteration
    transformer `f k` (the effect of `body` run with counter `x := k`):
    `rforFold f rs n = f (n-1) (… (f 0 rs))`. -/
def rforFold (f : Nat → RustState → RustState) (rs : RustState) : Nat → RustState
  | 0     => rs
  | n + 1 => f n (rforFold f rs n)

/-- **`RFor` realizes a fold — general, body-agnostic (scalable loop core).**

    If every single iteration of `body` (run with the counter bound to `k`) is a
    `RustExec` step from `rs` to `f k rs`, then the whole `RFor x n body` loop is
    a `RustExec` step to the `n`-fold `rforFold f rs n`.  Proved by induction on
    the trip count via `forZero`/`forSucc` — an `O(1)` proof term, *independent
    of `n` and of the body*.  This is the reusable scalability lemma: any loop
    whose body is a deterministic state transformer is realised by its fold
    without unrolling.  Instantiate `f` per body (see `rfor_realizes_accFold`). -/
theorem rfor_realizes_fold {N : Nat} {leafSpec : LeafSpec}
    (x : String) (body : LowCT) (f : Nat → RustState → RustState)
    (hstep : ∀ k rs, RustExec N leafSpec body (rsSetScalar rs x k) (f k rs))
    (rs : RustState) (n : Nat) :
    RustExec N leafSpec (.RFor x n body) rs (rforFold f rs n) := by
  induction n with
  | zero => exact RustExec.forZero x body rs
  | succ n ih =>
      exact RustExec.forSucc x n body rs (rforFold f rs n) (rforFold f rs (n + 1))
        ih (hstep n (rforFold f rs n))

/-- The fold a single-accumulator `RFor i n (acc := acc + i)` loop computes:
    after `n` iterations starting from `a0`, the accumulator holds
    `a0 + Σ_{k<n} k`. -/
def accFold (a0 : Nat) : Nat → Nat
  | 0     => a0
  | n + 1 => accFold a0 n + n

/-- The accumulator loop body: `acc := acc + i` where `i` is the loop counter.
    `RScalarSetExpr` stores a runtime-evaluated scalar expression, and the
    `RFor` rule binds the counter into scalar slot `"i"` on each iteration. -/
abbrev accBody : LowCT :=
  .RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "i"))

/-- **`RFor` realizes a fold (scalable loop artifact).**

    For *every* trip count `n`, the accumulator loop's `RustExec` final state
    has `acc = accFold a0 n` — proved by induction on `n` via `forZero`/`forSucc`.
    The proof term is `O(1)` in `n`: the loop is never unrolled.  Contrast
    `compUnroll_denote`, whose concrete-`N` instantiation explodes.  -/
theorem rfor_realizes_accFold {N : Nat} (leafSpec : LeafSpec)
    (rs : RustState) (n : Nat) :
    ∃ rs', RustExec N leafSpec (.RFor "i" n accBody) rs rs'
      ∧ rs'.rsScalar "acc" = accFold (rs.rsScalar "acc") n := by
  induction n with
  | zero =>
      exact ⟨rs, RustExec.forZero "i" accBody rs, rfl⟩
  | succ n ih =>
      obtain ⟨r1, hr1, hacc1⟩ := ih
      -- One more iteration: run the body on the state with counter `i := n`.
      refine ⟨_, RustExec.forSucc "i" n accBody rs r1 _ hr1
                (RustExec.scalarSetExpr "acc"
                  (SExpr.SAdd (SExpr.SVar "acc") (SExpr.SVar "i"))
                  (rsSetScalar r1 "i" n)),
              ?_⟩
      -- Compute the new accumulator and match it against `accFold _ (n+1)`.
      simp only [SExpr.eval, rsSetScalar, accFold]
      rw [hacc1]; simp

/-! ### Multi-scalar, counter-injecting body (SHA-256 round shape)

The SHA-256 compression round is an 8-word shift register `(a,…,h)` whose
updates read the *old* values (executed in an order that respects that) and
inject a per-round constant `K[r]`/message word `W[r]` indexed by the counter.
The 3-register witness below has exactly that shape — a sequence of
`RScalarSetExpr` updates reading old slots, with the counter `i` injected — and
is realised by its fold through the *same* general `rfor_realizes_fold`, with the
per-iteration `RustExec` discharged by `RustExec.seq`.  This shows the scalable
loop core composes for real round-shaped bodies, not just a lone accumulator. -/

/-- A 3-register shift-register round body: `c := b ; b := a ; a := a + i`
    (updates ordered so each reads the pre-update value), counter `i` injected
    into `a`.  Same structural shape as the SHA-256 `a..h` round. -/
def shiftBody : LowCT :=
  .RSeq (.RScalarSetExpr "c" (.SVar "b"))
    (.RSeq (.RScalarSetExpr "b" (.SVar "a"))
      (.RScalarSetExpr "a" (.SAdd (.SVar "a") (.SVar "i"))))

/-- The per-iteration state transformer realised by `shiftBody` started from a
    state whose counter slot already holds `k` (matching `rfor_realizes_fold`). -/
def shiftStep (k : Nat) (rs : RustState) : RustState :=
  let s0 := rsSetScalar rs "i" k
  let s1 := rsSetScalar s0 "c" (s0.rsScalar "b")
  let s2 := rsSetScalar s1 "b" (s1.rsScalar "a")
  rsSetScalar s2 "a" (s2.rsScalar "a" + s2.rsScalar "i")

/-- **`RFor` realizes the round-shaped fold.**  The 3-register shift-register
    loop is realised by `rforFold shiftStep` — a fold, no unrolling — via the
    general `rfor_realizes_fold` with the per-iteration step discharged by
    `RustExec.seq`.  `O(1)` proof term in the trip count. -/
theorem rfor_realizes_shiftFold {N : Nat} {leafSpec : LeafSpec}
    (rs : RustState) (n : Nat) :
    RustExec N leafSpec (.RFor "i" n shiftBody) rs (rforFold shiftStep rs n) := by
  apply rfor_realizes_fold
  intro k rs'
  exact RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
    (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
      (RustExec.scalarSetExpr _ _ _))

/-! ### Value bridge: the loop's fold realizes FIPS 180-4 `compFold`

`rfor_realizes_fold` makes the loop a fold over an arbitrary `RustState`
transformer.  This section ties that fold to the *proven* SHA-256 compression
spec `compFold` (from `CompileFromHaxCompress`, the FIPS 180-4 round folded
over the trip count).

The eight working words `a..h` live in scalar slots `"a".."h"`, each a
`BitVec 32` encoded by `.toNat` (`encodeSt`) and read back by `BitVec.ofNat`
(`decodeSt`); `decode_encode` is the round-trip.  `roundStepBV` is the round
leaf's effect on the encoded state — decode, apply the verified `roundFn`,
re-encode — and `rforFold_realizes_compFold` proves the `n`-fold loop equals
`compFold` by induction on the trip count: an `O(1)` proof term, no unrolling.

This bridges the loop's *fold structure* to FIPS.  Faithfulness of the
*compiled scalar σ/Ch/Maj ops* to `roundFn` (the rotate/mask layer) is
`roundBody_denote` on the unroll side; the two axes together give the SHA-256
compression as a scalable verified loop. -/

section ValueBridge
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

/-- Read the eight `BitVec 32` working words back out of scalar slots `"a".."h"`. -/
def decodeSt (rs : RustState) : St where
  a := BitVec.ofNat 32 (rs.rsScalar "a")
  b := BitVec.ofNat 32 (rs.rsScalar "b")
  c := BitVec.ofNat 32 (rs.rsScalar "c")
  d := BitVec.ofNat 32 (rs.rsScalar "d")
  e := BitVec.ofNat 32 (rs.rsScalar "e")
  f := BitVec.ofNat 32 (rs.rsScalar "f")
  g := BitVec.ofNat 32 (rs.rsScalar "g")
  h := BitVec.ofNat 32 (rs.rsScalar "h")

/-- Store the eight working words into scalar slots `"a".."h"` as `.toNat`. -/
def encodeSt (rs : RustState) (s : St) : RustState :=
  rsSetScalar (rsSetScalar (rsSetScalar (rsSetScalar (rsSetScalar
    (rsSetScalar (rsSetScalar (rsSetScalar rs
      "a" s.a.toNat) "b" s.b.toNat) "c" s.c.toNat) "d" s.d.toNat)
      "e" s.e.toNat) "f" s.f.toNat) "g" s.g.toNat) "h" s.h.toNat

/-- Encoding round-trips: reading the slots back recovers the working words. -/
theorem decode_encode (rs : RustState) (s : St) : decodeSt (encodeSt rs s) = s := by
  cases s
  simp [decodeSt, encodeSt, rsSetScalar]

/-- The round leaf's effect on the encoded state: decode, apply the verified
    FIPS round `roundFn` at constant `K k` / schedule word `W k`, re-encode. -/
def roundStepBV (K W : Nat → BitVec 32) (k : Nat) (rs : RustState) : RustState :=
  encodeSt rs (roundFn (decodeSt rs) (K k) (W k))

/-- **Value bridge: the `RFor` loop's fold realizes `compFold`.**  The
    `n`-fold of the round step over the encoded initial state decodes to the
    FIPS 180-4 compression `compFold init K W n`.  Proved by induction on the
    trip count — `O(1)` proof term, no unrolling. -/
theorem rforFold_realizes_compFold (K W : Nat → BitVec 32) (rs0 : RustState)
    (init : St) (n : Nat) :
    decodeSt (rforFold (roundStepBV K W) (encodeSt rs0 init) n)
      = compFold init K W n := by
  induction n with
  | zero => simpa using! decode_encode rs0 init
  | succ n ih =>
      simp only [rforFold, roundStepBV, compFold]
      rw [decode_encode, ih]

/-- **End-to-end: a `for`-loop calling the round body realizes FIPS `compFold`.**

    Composes the two axes.  Given a round body whose *single* `RustExec`
    iteration (counter `"r" := k`) realizes the verified round step
    `roundStepBV` — the op-faithfulness hypothesis, the loop-side analogue of
    `roundBody_denote`, dischargeable by the compiled σ/Ch/Maj scalar ops — the
    whole `RFor "r" n body` loop's final state decodes to `compFold init K W n`.
    Scalability comes from `rfor_realizes_fold` (no unrolling, `O(1)` term);
    value comes from `rforFold_realizes_compFold`. -/
theorem rfor_loop_realizes_compFold {N : Nat} {leafSpec : LeafSpec}
    (body : LowCT) (K W : Nat → BitVec 32) (rs0 : RustState) (init : St) (n : Nat)
    (hbody : ∀ k rs, RustExec N leafSpec body (rsSetScalar rs "r" k)
              (roundStepBV K W k rs)) :
    ∃ rs', RustExec N leafSpec (.RFor "r" n body) (encodeSt rs0 init) rs'
      ∧ decodeSt rs' = compFold init K W n :=
  ⟨rforFold (roundStepBV K W) (encodeSt rs0 init) n,
   rfor_realizes_fold "r" body (roundStepBV K W) hbody (encodeSt rs0 init) n,
   rforFold_realizes_compFold K W rs0 init n⟩

/-! ### Discharging the round-body obligation concretely

The capstone's `hbody` is the loop-side op-faithfulness obligation: a concrete
`LowCT` round body whose single `RustExec` iteration computes `roundFn` under
the `encodeSt`/`decodeSt` encoding.  We discharge it here for the round
arithmetic (σ/Ch/Maj/T1/T2 + the 8-word shift), with the round constant `K[r]`
and message word `W[r]` supplied in scalar slots `"kk"`/`"ww"` (the per-round
constant/schedule lookup is separate plumbing).

The working words are kept as `BitVec 32` via `.toNat`.  `redE` masks a read to
32 bits (needed before a shift); `ofNat 32` absorbs the mask and is a
homomorphism for `+`/`^^^`/`&&&`, and `rotateRight` is the `xor` of the two
masked shifts (all proven by `bv_decide`).  Hence each output word decodes to
the corresponding `roundFn` field. -/

/-- Mask a slot read to its low 32 bits (so a subsequent shift sees the exact
    32-bit value `decodeSt` reads via `ofNat`). -/
def redE (x : String) : SExpr := .SAnd (.SVar x) (.SLit 4294967295)

/-- `rotateRight x n` as the `xor` of the two masked shifts. -/
def rorE (x : String) (n : Nat) : SExpr :=
  .SXor (.SShr (redE x) (.SLit n)) (.SShl (redE x) (.SLit (32 - n)))

/-- `Σ₀(a) = ror2 ⊕ ror13 ⊕ ror22`. -/
def sig0E : SExpr := .SXor (rorE "a" 2) (.SXor (rorE "a" 13) (rorE "a" 22))
/-- `Σ₁(e) = ror6 ⊕ ror11 ⊕ ror25`. -/
def sig1E : SExpr := .SXor (rorE "e" 6) (.SXor (rorE "e" 11) (rorE "e" 25))
/-- `Ch(e,f,g) = (e∧f) ⊕ (¬e∧g)`, complement as `e ⊕ 0xFFFFFFFF`. -/
def chE : SExpr :=
  .SXor (.SAnd (redE "e") (redE "f"))
    (.SAnd (.SXor (redE "e") (.SLit 4294967295)) (redE "g"))
/-- `Maj(a,b,c) = (a∧b) ⊕ (a∧c) ⊕ (b∧c)`. -/
def majE : SExpr :=
  .SXor (.SAnd (redE "a") (redE "b"))
    (.SXor (.SAnd (redE "a") (redE "c")) (.SAnd (redE "b") (redE "c")))

/-- `T₁ = h + Σ₁(e) + Ch(e,f,g) + K[r] + W[r]` (constant/word in slots `kk`/`ww`). -/
def t1E : SExpr :=
  .SAdd (.SAdd (.SAdd (.SAdd (.SVar "h") sig1E) chE) (.SVar "kk")) (.SVar "ww")
/-- `T₂ = Σ₀(a) + Maj(a,b,c)`. -/
def t2E : SExpr := .SAdd sig0E majE

/-- The concrete round body: compute `T₁`,`T₂` into temps, then the 8-word
    shift `(a',…,h') = (T₁+T₂, a, b, c, d+T₁, e, f, g)` — updates ordered
    high→low so each read sees the pre-update value. -/
def roundBody : LowCT :=
  .RSeq (.RScalarSetExpr "t1" t1E)
   (.RSeq (.RScalarSetExpr "t2" t2E)
    (.RSeq (.RScalarSetExpr "h" (.SVar "g"))
     (.RSeq (.RScalarSetExpr "g" (.SVar "f"))
      (.RSeq (.RScalarSetExpr "f" (.SVar "e"))
       (.RSeq (.RScalarSetExpr "e" (.SAdd (.SVar "d") (.SVar "t1")))
        (.RSeq (.RScalarSetExpr "d" (.SVar "c"))
         (.RSeq (.RScalarSetExpr "c" (.SVar "b"))
          (.RSeq (.RScalarSetExpr "b" (.SVar "a"))
           (.RScalarSetExpr "a" (.SAdd (.SVar "t1") (.SVar "t2")))))))))))

/-- Decode a `BitVec 32` round input (constant/message word) from a scalar slot. -/
def decodeWord (rs : RustState) (s : String) : BitVec 32 :=
  BitVec.ofNat 32 (rs.rsScalar s)

/-! The op-correspondence kit: `ofNat 32` pushes through the Nat-masked ops to
    the matching `BitVec 32` ops, so a Nat expression over masked reads decodes
    to the `BitVec` expression over the decoded atoms.  (`+`/`^^^`/`&&&` are the
    library lemmas `BitVec.ofNat_{add,xor,and}`; shifts and the mask need these.) -/

/-- `ofNat` of a masked right-shift is the `BitVec` right-shift of the decode. -/
theorem ofNat_mask_shr (a n : Nat) :
    BitVec.ofNat 32 ((a &&& 4294967295) >>> n) = (BitVec.ofNat 32 a) >>> n := by
  apply BitVec.eq_of_toNat_eq
  have hmask : a &&& 4294967295 = a % 2 ^ 32 := by
    have h : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [h, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, hmask, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by norm_num)))

/-- `ofNat` of a masked left-shift is the `BitVec` left-shift of the decode. -/
theorem ofNat_mask_shl (a n : Nat) :
    BitVec.ofNat 32 ((a &&& 4294967295) <<< n) = (BitVec.ofNat 32 a) <<< n := by
  apply BitVec.eq_of_toNat_eq
  have hmask : a &&& 4294967295 = a % 2 ^ 32 := by
    have h : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [h, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hmask, Nat.shiftLeft_eq]

/-- The 32-bit mask is absorbed by `ofNat 32`. -/
theorem ofNat_mask (a : Nat) :
    BitVec.ofNat 32 (a &&& 4294967295) = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq
  have hmask : a &&& 4294967295 = a % 2 ^ 32 := by
    have h : (4294967295 : Nat) = 2 ^ 32 - 1 := by norm_num
    rw [h, Nat.and_two_pow_sub_one_eq_mod]
  simp only [BitVec.toNat_ofNat, hmask, Nat.mod_mod]

/-- A single scalar update, matching `RustExec.scalarSetExpr`'s effect. -/
def setE (rs : RustState) (x : String) (e : SExpr) : RustState :=
  rsSetScalar rs x (e.eval rs.rsScalar)

/-- The explicit per-iteration state transformer realised by `roundBody`
    (direct `setE` nesting; `"t1"` applied first, `"a"` last). -/
def roundExec (rs : RustState) : RustState :=
  setE (setE (setE (setE (setE (setE (setE (setE (setE (setE rs
    "t1" t1E) "t2" t2E) "h" (.SVar "g")) "g" (.SVar "f")) "f" (.SVar "e"))
    "e" (.SAdd (.SVar "d") (.SVar "t1"))) "d" (.SVar "c")) "c" (.SVar "b"))
    "b" (.SVar "a")) "a" (.SAdd (.SVar "t1") (.SVar "t2"))

/-- `roundBody`'s `RustExec` realises `roundExec` (the explicit transformer). -/
theorem roundBody_exec {N : Nat} {leafSpec : LeafSpec} (rs : RustState) :
    RustExec N leafSpec roundBody rs (roundExec rs) := by
  unfold roundBody roundExec setE
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  apply RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _)
  exact RustExec.scalarSetExpr _ _ _

set_option maxHeartbeats 4000000 in
/-- **The concrete round body computes `roundFn` under the encoding.**  Discharges
    the loop-side op-faithfulness obligation: `roundExec` (what `roundBody`
    executes to, by `roundBody_exec`) decodes to the FIPS round applied to the
    decoded input, with `K[r]`/`W[r]` read from slots `kk`/`ww`. -/
theorem roundExec_decode (rs : RustState) :
    decodeSt (roundExec rs)
      = roundFn (decodeSt rs) (decodeWord rs "kk") (decodeWord rs "ww") := by
  -- Phase 1: unfold the body + spec, resolve all scalar-slot lookups
  -- (`+decide` decides the `==` conditions, `reduceIte` collapses the `if`-chain).
  simp +decide only [roundExec, setE, SExpr.eval, decodeSt, decodeWord, rsSetScalar,
    reduceIte, roundFn, bigSigma0, bigSigma1, chFn, majFn,
    t1E, t2E, sig0E, sig1E, chE, majE, rorE, redE]
  -- Phase 2: push `ofNat 32` inward through the Nat-masked ops to `BitVec` ops.
  simp only [BitVec.ofNat_add, BitVec.ofNat_xor, BitVec.ofNat_and,
    ofNat_mask_shr, ofNat_mask_shl]
  -- Phase 3: the residual is a `BitVec 32` identity over decoded atoms, one per
  -- state field.
  congr 1 <;> bv_decide

/-- **The round-body obligation, discharged concretely.**  Packages
    `roundBody_exec` (the body's `RustExec` realises `roundExec`) with
    `roundExec_decode` (that decodes to the FIPS `roundFn`): the concrete
    `LowCT` round body steps to a state whose decode is the FIPS round applied
    to the decoded input.  This is the loop-side analogue of the unroll-side
    `roundBody_denote` — the op-faithfulness that the capstone
    `rfor_loop_realizes_compFold` takes as hypothesis is, for this body, a
    theorem (`K[r]`/`W[r]` supplied in slots `kk`/`ww`). -/
theorem roundBody_realizes {N : Nat} {leafSpec : LeafSpec} (rs : RustState) :
    ∃ rs', RustExec N leafSpec roundBody rs rs'
      ∧ decodeSt rs' = roundFn (decodeSt rs) (decodeWord rs "kk") (decodeWord rs "ww") :=
  ⟨roundExec rs, roundBody_exec rs, roundExec_decode rs⟩

/-! ### Closing the residual: per-round `K[r]`/`W[r]` and the full loop

`roundExec` reads the round constant/word from fixed slots `kk`/`ww`.  In the
real loop these vary by round: the per-iteration transformer
`rfor_realizes_fold` builds receives the counter `k`, so we inject `K[k]`/`W[k]`
into `kk`/`ww` before the arithmetic.  `roundStepC` is that transformer, and
`rforFold_roundStepC_realizes_compFold` ties the whole varying-`K`/`W` loop to
FIPS `compFold` by induction on the trip count — closing the value bridge for
the *actual* SHA-256 compression schedule (any `K W : Nat → BitVec 32`,
e.g. the `kBV` constants and the §9 message schedule). -/

/-- The per-round transformer: inject `K[k]`/`W[k]` at counter `k`, run the
    round arithmetic. -/
def roundStepC (K W : Nat → BitVec 32) (k : Nat) (rs : RustState) : RustState :=
  roundExec (rsSetScalar (rsSetScalar rs "kk" (K k).toNat) "ww" (W k).toNat)

/-- The injected step decodes to the FIPS round at `K[k]`/`W[k]`: injecting into
    `kk`/`ww` leaves the working words `a..h` untouched, and the round reads back
    exactly `K[k]`/`W[k]`. -/
theorem roundStepC_decode (K W : Nat → BitVec 32) (k : Nat) (rs : RustState) :
    decodeSt (roundStepC K W k rs) = roundFn (decodeSt rs) (K k) (W k) := by
  unfold roundStepC
  rw [roundExec_decode]
  have hd : decodeSt (rsSetScalar (rsSetScalar rs "kk" (K k).toNat) "ww" (W k).toNat)
      = decodeSt rs := by simp +decide [decodeSt, rsSetScalar]
  have hk : decodeWord (rsSetScalar (rsSetScalar rs "kk" (K k).toNat) "ww" (W k).toNat) "kk"
      = K k := by simp +decide [decodeWord, rsSetScalar]
  have hw : decodeWord (rsSetScalar (rsSetScalar rs "kk" (K k).toNat) "ww" (W k).toNat) "ww"
      = W k := by simp +decide [decodeWord, rsSetScalar]
  rw [hd, hk, hw]

/-- **Residual closed: the full varying-`K`/`W` round loop realizes `compFold`.**
    The `n`-fold of the concrete round body — with `K[k]`/`W[k]` injected at each
    counter `k` — decodes to FIPS `compFold init K W n`, for any constant table
    `K` and message schedule `W`.  `O(1)` proof term, no unrolling. -/
theorem rforFold_roundStepC_realizes_compFold (K W : Nat → BitVec 32)
    (rs0 : RustState) (init : St) (n : Nat) :
    decodeSt (rforFold (roundStepC K W) (encodeSt rs0 init) n) = compFold init K W n := by
  induction n with
  | zero => simpa using! decode_encode rs0 init
  | succ n ih =>
      simp only [rforFold, compFold]
      rw [roundStepC_decode, ih]

end ValueBridge
