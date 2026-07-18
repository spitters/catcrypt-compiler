/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody

/-!
# Counted loop over a **multi-accumulator** (product) state: `loopNAccum`

`MultiBinderLoopBody.loopNMulti` packages the counted-loop keystone for a
multi-binder straight-line body over **one** accumulator cell `accTy`. Real
crypto loops carry **several** live values across iterations: a sponge state
(Keccak's 25 lanes), a Montgomery / X25519 ladder's `(x₂, z₂, x₃, z₃)`, a
running `(carry, digit)` pair, a Fibonacci-style `(a, b)` recurrence. This file
closes that gap.

## The packing route (why, and what it costs)

`JForProg`'s accumulator is a single `JasminTy`, and `JasminTy`'s alphabet
(`reg w` / `stackArr w n` / `inlineInt` / `bool`) has **no product/pair
constructor** — the single-accumulator `JForProg` shape is hard-wired (flagged in
`MultiBinderLoopBody`'s scope note). The honest, sorry-free route the existing
types support is therefore **packing**: model `k` accumulator cells of width `w`
as one **wide** `reg (k*w)` register, with each cell occupying a `w`-bit lane.
The loop body is then an arbitrary straight-line `Com jasminDialect [reg (k*w)]
(reg (k*w))` that reads its input lanes (via `shrImm` / `shlImm` / `regArith
and`) and reassembles the updated lanes — exactly the AVX-lane discipline
`zmmLane` / `zmmOfLanes` already use for ZMM registers, here at the
accumulator-state level.

Under this packing, a multi-accumulator loop **is** a special case of the
multi-binder loop `loopNMulti` at `accTy = reg (k*w)`: the keystone
`loopNMulti_lower_denote_iterate` applies **verbatim** — the emitted counted
loop's run equals `step^[n]` over the packed `BitVec (k*w)` state, where `step`
is the body's denotation. No new loop machinery is needed.

## What is genuinely new here

1. **`packLanes` / `lane`** — the lane (un)packing for a `k`-cell × `w`-bit
   packed accumulator, with `lane_packLanes` proving the projection of cell `i`
   recovers exactly the `i`-th input cell. This is the *faithfulness* witness:
   a packed `reg (k*w)` is a genuine product of `k` cells, not a lossy encoding.

2. **`loopNAccum`** — the multi-accumulator counted-loop constructor: a thin,
   documented specialisation of `loopNMulti` to `accTy = reg (k*w)`. Its keystone
   `loopNAccum_lower_denote_iterate` is `loopNMulti_lower_denote_iterate` —
   reused, not re-proved.

3. A worked **2-accumulator** example: the **Fibonacci** step
   `(a, b) ↦ (b, a + b)` packed into one `reg 128` (cell 0 = low 64 = `a`,
   cell 1 = high 64 = `b`), run `n` times. We give its emitted-loop denotation in
   `step^[n]` form *and* a concrete `n = 5` KAT computing
   `(1, 1) → (1, 2) → (2, 3) → (3, 5) → (5, 8) → (8, 13)` — i.e. the packed
   state `(8, 13)` — byte-for-byte. SORRY-FREE.

## Conditioned scope (honest)

The soundness inherits exactly the two hypotheses of the multi-binder keystone,
neither a `sorry`:

* `hLeaf : LeafAgrees leafSem` — the opaque-leaf edge, carried throughout the
  emit theory.
* `hSL : StraightLine body` — every binder is a non-`stackStore` op (the
  fresh-name discipline; excludes the in-place aliasing `stackStore`).

What this does **not** cover: a true **heterogeneous** product `JasminTy`
(cells of *different* types, or arrays mixed with registers). The packing models
`k` cells of a **common** width `w` (the homogeneous register-lane case); a
genuine heterogeneous product would need a `JasminTy.prod` constructor (a
`JForProg`-shape change, out of scope here and explicitly avoided — we do not
touch `JForProg`). For the ladder/sponge/recurrence loops that motivate this, the
cells are uniform-width registers, so the packed `reg (k*w)` model is faithful
(`lane_packLanes`).

0 sorries; the only carried hypotheses are `LeafAgrees` and `StraightLine body`,
inherited verbatim from `loopNMulti`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiAccumLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.LoopLowering
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBinderLoopBody
open CatCrypt.Crypto.Jasmin (JasminProg)

/-! ## 1. Lane (un)packing for a `k`-cell × `w`-bit packed accumulator

A packed accumulator state is a `BitVec (k*w)` carrying `k` cells, cell `i` in
bit-window `[i*w, i*w + w)`. `lane i` projects cell `i`; `packLanes` assembles a
state from a cell-indexed family. `lane_packLanes` proves projection inverts
packing — the faithfulness witness that the packed `reg (k*w)` is a genuine
`k`-fold product of `w`-bit cells. -/

/-- The packed-accumulator type carrying `k` cells of `w` bits each. -/
abbrev PackedTy (k w : Nat) : JasminTy := .reg (k * w)

/-- Project cell `i` (a `w`-bit window) out of a packed `BitVec (k*w)` state,
    little-endian (cell 0 = low `w` bits). The accumulator-level analogue of
    `JasminDialect.zmmLane`. -/
def lane {k w : Nat} (v : BitVec (k * w)) (i : Fin k) : BitVec w :=
  BitVec.extractLsb' (w * i.val) w v

/-- Assemble a packed `BitVec (k*w)` state from a cell-indexed family of `w`-bit
    cells, little-endian (cell 0 in the low `w` bits). Inverse of `lane`. -/
def packLanes {k w : Nat} (f : Fin k → BitVec w) : BitVec (k * w) :=
  match k with
  | 0 => (0 : BitVec (0 * w))
  | k + 1 =>
      let rest : BitVec (k * w) := packLanes (fun j : Fin k => f j.succ)
      (rest ++ f 0).cast (by ring)

/-- `extractLsb'` commutes with a width `cast`: casting the underlying bitvector
    does not move any bit, so it leaves the extracted window unchanged. -/
private theorem extractLsb'_cast {n m : Nat} (h : n = m) (x : BitVec n)
    (s len : Nat) :
    BitVec.extractLsb' s len (x.cast h) = BitVec.extractLsb' s len x := by
  subst h; rfl

/-- `extractLsb' 0 w` of a `w`-bit vector is the identity (the whole vector). -/
private theorem extractLsb'_zero_self {w : Nat} (x : BitVec w) :
    BitVec.extractLsb' 0 w x = x := by
  ext j; simp

/-- **Faithfulness.** Projecting cell `i` of a packed state recovers exactly the
    `i`-th input cell: `lane (packLanes f) i = f i`. So the packed `reg (k*w)`
    accumulator is a genuine `k`-fold product of `w`-bit cells — packing loses no
    information. By induction on `k`, splitting on whether `i` is cell 0 (the low
    `w`-bit append slice) or a higher cell (the recursive `rest`). -/
theorem lane_packLanes {k w : Nat} (f : Fin k → BitVec w) (i : Fin k) :
    lane (packLanes f) i = f i := by
  induction k with
  | zero => exact absurd i.isLt (by omega)
  | succ k ih =>
      rcases i with ⟨iv, hiv⟩
      cases iv with
      | zero =>
          show lane (packLanes f) ⟨0, hiv⟩ = f ⟨0, hiv⟩
          unfold lane packLanes
          rw [extractLsb'_cast]
          rw [show w * (⟨0, hiv⟩ : Fin (k + 1)).val = 0 from by simp]
          rw [BitVec.extractLsb'_append_eq_of_add_le (by omega)]
          rw [extractLsb'_zero_self]
          rfl
      | succ m =>
          have hm : m < k := by omega
          have ihm := ih (fun j : Fin k => f j.succ) ⟨m, hm⟩
          show lane (packLanes f) ⟨m + 1, hiv⟩ = f ⟨m + 1, hiv⟩
          unfold lane packLanes
          rw [extractLsb'_cast]
          rw [BitVec.extractLsb'_append_eq_of_le (by
            calc w ≤ w * (m + 1) := Nat.le_mul_of_pos_right w (by omega)
            _ = w * (⟨m + 1, hiv⟩ : Fin (k + 1)).val := by simp)]
          unfold lane at ihm
          rw [show w * (⟨m + 1, hiv⟩ : Fin (k + 1)).val - w
              = w * (⟨m, hm⟩ : Fin k).val from by simp [Nat.mul_succ]]
          rw [ihm]
          rfl

/-! ## 2. The multi-accumulator counted-loop constructor `loopNAccum`

A `MultiAccumBody k w` is an arbitrary straight-line `Com` over the packed
accumulator `reg (k*w)` — it reads input lanes and reassembles updated lanes.
`loopNAccum n body` runs it `n` times. It is **definitionally** `loopNMulti` at
`accTy = PackedTy k w`, so the multi-binder keystone applies verbatim. -/

/-- A multi-accumulator loop body: an arbitrary straight-line `Com` over the
    packed `k`-cell × `w`-bit accumulator. -/
abbrev MultiAccumBody (k w : Nat) : Type :=
  MultiBinderBody (PackedTy k w)

/-- **The multi-accumulator counted-loop constructor.** `loopNAccum n body` runs
    the packed-state body `body` exactly `n` times over the `k`-cell × `w`-bit
    packed accumulator. Definitionally `loopNMulti` at `accTy = reg (k*w)`. -/
def loopNAccum {k w : Nat} (n : Nat) (body : MultiAccumBody k w) :
    JForProg (PackedTy k w) :=
  loopNMulti n body

/-- `loopNAccum` is the packed `loopNMulti`. -/
theorem loopNAccum_eq {k w : Nat} (n : Nat) (body : MultiAccumBody k w) :
    loopNAccum n body = loopNMulti n body := rfl

/-- One step of `loopNAccum` is the body's denotation on the packed state. -/
@[simp] theorem loopNAccum_step {k w : Nat} (n : Nat) (body : MultiAccumBody k w)
    (acc : BitVec (k * w)) :
    (loopNAccum n body).step acc = body.denote (.cons acc .nil) := rfl

/-! ## 3. The lowering and its soundness (the multi-accumulator keystone)

`loopNAccum` lowers via `JForProg.toProg`; the emitted loop is run by
`bodyStepRun`. Soundness: the emitted run equals `step^[n]` over the packed
state — *directly* `loopNMulti_lower_denote_iterate`, no new proof. -/

/-- The lowering of a multi-accumulator counted loop to a single-function
    `JasminProg` with a `Cfor`. -/
def loopNAccum_lower {k w : Nat} (name : String) (n : Nat)
    (body : MultiAccumBody k w) : JasminProg :=
  (loopNAccum n body).toProg name

/-- **Keystone (multi-accumulator, iterate form).** The emitted counted loop over
    the packed `k`-cell state, run `n` times, equals `step^[n] init`, where
    `step` is the body's denotation on the packed state. This is
    `MultiBinderLoopBody.loopNMulti_lower_denote_iterate` at the packed accumulator
    `reg (k*w)` — reused, not re-proved. Conditioned on `LeafAgrees` and
    `StraightLine body`. -/
theorem loopNAccum_lower_denote_iterate {k w : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (n : Nat) (body : MultiAccumBody k w)
    (hSL : StraightLine body) (init : BitVec (k * w)) :
    loopRun (loopNAccum n body) (bodyStepRun leafSem (loopNAccum n body)) init
      = (fun acc => body.denote (.cons acc .nil))^[n] init :=
  loopNMulti_lower_denote_iterate hLeaf n body hSL init

/-! ## 4. Worked example: a 2-accumulator **Fibonacci** loop in one `reg 128`

The Fibonacci recurrence `(a, b) ↦ (b, a + b)` is the minimal genuine
*multi-accumulator* loop: two live values, each updated from both. We pack it
into one `reg 128` — cell 0 (low 64 bits) = `a`, cell 1 (high 64 bits) = `b` —
and emit the body as a straight-line `Com [reg 128] (reg 128)`:

    let b'  = acc >>> 64        -- b in low 64  (shrImm 128 64)
    let a   = acc & 0xFFFF…FF   -- a in low 64  (regArith and, 2^64-1 mask)
    let s   = a + b'            -- a + b (mod 2^128, but only low 64 used) : the new high cell
    let hi  = s <<< 64          -- (a+b) into high 64  (shlImm 128 64)
    let r   = hi | b'           -- pack: high = a+b, low = b
    ret r

Its denotation on packed `acc` is `((((acc &&& mask) + (acc >>> 64)) <<< 64) |||
(acc >>> 64))`, which is the packed `(b, a+b)`. We prove the iterate-form
emitted-loop denotation and a concrete `n = 5` KAT from packed seed `(a,b)=(1,1)`. -/

/-- The low-64 mask `2^64 - 1` as a `reg 128` constant (selects cell 0 = `a`). -/
def mask64 : BitVec 128 := BitVec.ofNat 128 (2 ^ 64 - 1)

/-- The Fibonacci step packed into one `reg 128`: cell 0 = low 64 = `a`,
    cell 1 = high 64 = `b`; the new packed state is `(b, a + b)`. The mask
    constant is materialised as its own `regConst` binder (a nullary op cannot be
    inlined as a `Ctxt.Var` argument). de-Bruijn indices track the growing
    context `[r, hi, s, a, b', m, acc]`. -/
def fibBody : MultiAccumBody 2 64 :=
  -- m = regConst (2^64-1)              ctx after: [m, acc]
  .var (.mk (.regConst 128 (2 ^ 64 - 1)) rfl .nil)
  -- b' = acc >>> 64    acc = .there .here       ctx after: [b', m, acc]
  (.var (.mk (.shrImm 128 64) rfl (.cons (.there .here) .nil))
  -- a = acc & m        acc = .there (.there .here), m = .there .here   ctx: [a, b', m, acc]
  (.var (.mk (.regArith .and 128) rfl
      (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- s = a + b'         a = .here, b' = .there .here     ctx: [s, a, b', m, acc]
  (.var (.mk (.regArith .add 128) rfl
      (.cons .here (.cons (.there .here) .nil)))
  -- hi = s <<< 64      s = .here                        ctx: [hi, s, a, b', m, acc]
  (.var (.mk (.shlImm 128 64) rfl (.cons .here .nil))
  -- r = hi ||| b'      hi = .here, b' = .there (.there (.there .here))  ctx: [r, …]
  (.var (.mk (.regArith .or 128) rfl
      (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  (.ret .here))))))

/-- The closed-form packed Fibonacci step on a `BitVec 128`. -/
def fibStep (acc : BitVec 128) : BitVec 128 :=
  (((acc &&& mask64) + (acc >>> 64)) <<< 64) ||| (acc >>> 64)

/-- The emitted Fibonacci body denotes the closed-form packed step `fibStep`. -/
@[simp] theorem fibBody_denote (acc : BitVec 128) :
    fibBody.denote (.cons acc .nil) = fibStep acc := rfl

/-- The Fibonacci body is `StraightLine` (every binder is a non-`stackStore`
    `regArith` / `shrImm` / `shlImm` op). -/
theorem fibBody_straightLine : StraightLine fibBody := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
    · intro w n h; exact absurd h (by simp)

/-- **Worked example (iterate form).** The emitted
    `for i = 0 to 5 { acc = pack(b, a+b) }` 2-accumulator counted loop, run via the
    evaluator, denotes the 5-fold composition of the packed Fibonacci step.
    Instance of `loopNAccum_lower_denote_iterate` at `k = 2`, `w = 64`. -/
theorem fibBody_loop_iterate {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (init : BitVec 128) :
    loopRun (loopNAccum 5 fibBody) (bodyStepRun leafSem (loopNAccum 5 fibBody)) init
      = fibStep^[5] init := by
  have h := loopNAccum_lower_denote_iterate hLeaf 5 fibBody fibBody_straightLine init
  simpa using h

/-- The packed seed `(a, b) = (1, 1)`: `a` in low 64, `b` in high 64. -/
def fibSeed : BitVec 128 := packLanes (k := 2) (w := 64) (fun i => if i = 0 then 1 else 1)

/-- **Worked example (concrete KAT).** From packed seed `(a, b) = (1, 1)`, the
    emitted 2-accumulator loop run 5 times computes the packed state `(8, 13)`:
    `(1,1) → (1,2) → (2,3) → (3,5) → (5,8) → (8,13)`. Cell 0 (low 64) = `8`,
    cell 1 (high 64) = `13`. We project both lanes byte-for-byte. -/
theorem fibBody_loop_kat {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem) :
    let out := loopRun (loopNAccum 5 fibBody)
      (bodyStepRun leafSem (loopNAccum 5 fibBody)) fibSeed
    lane (k := 2) (w := 64) out 0 = (8 : BitVec 64) ∧
    lane (k := 2) (w := 64) out 1 = (13 : BitVec 64) := by
  simp only []
  rw [fibBody_loop_iterate hLeaf]
  refine ⟨?_, ?_⟩ <;> · unfold fibStep fibSeed packLanes lane mask64; decide

end CatCrypt.Crypto.SecureCompilation.VIR.MultiAccumLoop
