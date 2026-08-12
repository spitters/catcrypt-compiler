/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Transfer
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote

/-!
# The ascent refinement calculus over LowCT — structural core

The proof-producing *abstraction* (ascent) leg dual to the descent relational
compiler (`RelationalCompile`): LowCT → clean Lean spec with a machine-checked
`Corres` correspondence, in the AutoCorres/Ascent style, over the **real**
compositional denotation `semScalar` (`TranslateDialectScalarDenote.semScalar`).

Division of labor:
* **`Corres`** (here) owns the monad/control structure and the arithmetic side
  conditions (the precondition `P`) — the structural lemmas `corres_seq`/`_skip`/
  `_block`/`_weaken` rest on `semScalar`'s definitional Kleisli-in-`Option` fold.
  This is the AutoCorres pattern: the abstraction proof piggybacks on a proven
  embedding of an imperative language into type theory, so every refinement step
  is discharged against the real denotation rather than a bespoke semantics.
* **ParamTransfer** (`Transfer.Related`/`RelatedBinOp`) owns the unconditional
  value representation change (`γV`): the word iso `BitVec 64 ≅ ZMod 2^64` (below)
  and — for the store phase — the Hex dense-storage↔Mathlib limb-packing.

This module is the structural core plus the Phase-1 word representation instance.
The value leaves (`corres_setExpr`, wiring `Related` into the state relation) and
the control/store phases build on top.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The correspondence relation over the real `semScalar` -/

/-- `Corres SR P fa c`: from a concrete `SEnvScalar` related by `SR` to an abstract
    state satisfying precondition `P`, the concrete command `c` makes progress under
    the real `semScalar` (`= some _`, Phase 0) to a concrete state related to the
    abstract result `fa`. Forward simulation, generic in the state relation `SR` and
    abstract state `AState`; the value abstraction plugs into `SR`. -/
def Corres {AState : Type} (SR : SEnvScalar → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : LowCT) : Prop :=
  ∀ env a, SR env a → P a → ∃ env', semScalar c env = some env' ∧ SR env' (fa a)

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- `RSkip`. -/
theorem corres_skip : Corres SR (fun _ => True) id .RSkip := by
  intro env a hSR _; exact ⟨env, rfl, hSR⟩

/-- `RBlock` is transparent to `semScalar`, so it transports the body's `Corres`. -/
theorem corres_block {P : AState → Prop} {fa : AState → AState} {body : LowCT}
    (h : Corres SR P fa body) : Corres SR P fa (.RBlock body) := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  exact ⟨env', hstep, hSR'⟩

/-- `RSeq` — the sequencing lemma (the `corres_bind`), resting on the definitional
    `semScalar (RSeq a b) = (semScalar a).bind (semScalar b)`. Requires the first
    phase to re-establish the second's precondition. -/
theorem corres_seq {P Q : AState → Prop} {fa ga : AState → AState} {c₁ c₂ : LowCT}
    (h₁ : Corres SR P fa c₁) (h₂ : Corres SR Q ga c₂) (hpre : ∀ a, P a → Q (fa a)) :
    Corres SR P (fun a => ga (fa a)) (.RSeq c₁ c₂) := by
  intro env a hSR hP
  obtain ⟨env₁, hstep₁, hSR₁⟩ := h₁ env a hSR hP
  obtain ⟨env₂, hstep₂, hSR₂⟩ := h₂ env₁ (fa a) hSR₁ (hpre a hP)
  refine ⟨env₂, ?_, hSR₂⟩
  simp only [semScalar, hstep₁, Option.bind_some, hstep₂]

/-- Strengthen the precondition (contravariant in `P`). -/
theorem corres_weaken {P P' : AState → Prop} {fa : AState → AState} {c : LowCT}
    (h : Corres SR P fa c) (himp : ∀ a, P' a → P a) : Corres SR P' fa c := by
  intro env a hSR hP'; exact h env a hSR (himp a hP')

/-! ## Phase-1 value layer via ParamTransfer: `BitVec 64 ≅ ZMod 2^64`

The unconditional word representation change, as a ParamTransfer `RelatedBinOp`
square (`enc (op x y) = bop (enc x) (enc y)`). ParamTransfer's `composeBinOp`
then transfers whole word-op trees. The move to a prime field `ZMod p` adds a
reduce/no-overflow side condition that lives in `Corres`'s precondition `P`. -/

/-- The word encoding: `BitVec 64 ↦ ZMod 2^64`. -/
def wEnc (w : BitVec 64) : ZMod (2 ^ 64) := (w.toNat : ZMod (2 ^ 64))

/-- Wrapping addition realizes `ZMod 2^64` addition — unconditionally. -/
instance wEncAdd : Transfer.RelatedBinOp wEnc (· + ·) (· + ·) where
  comm x y := by
    simp only [wEnc, BitVec.toNat_add, Nat.cast_add, ZMod.natCast_mod]

/-- Wrapping multiplication realizes `ZMod 2^64` multiplication — unconditionally. -/
instance wEncMul : Transfer.RelatedBinOp wEnc (· * ·) (· * ·) where
  comm x y := by
    simp only [wEnc, BitVec.toNat_mul, Nat.cast_mul, ZMod.natCast_mod]

/-- Wrapping subtraction realizes `ZMod 2^64` subtraction — unconditionally
    (`BitVec 64` is the ring `ZMod 2^64`). -/
instance wEncSub : Transfer.RelatedBinOp wEnc (· - ·) (· - ·) where
  comm x y := by
    have key : wEnc ((x - y) + y) = wEnc (x - y) + wEnc y := wEncAdd.comm (x - y) y
    rw [sub_add_cancel] at key
    rw [key]; ring

/-- ParamTransfer's `composeBinOp` transfers a whole word-op tree through `wEnc` by
    pure instance resolution: the `leaf` instance seats each `BitVec 64` variable at
    its `wEnc`-encoding, `composeBinOp` composes the registered squares. No manual
    proof — this is exactly the value-leaf mechanism the ascent tactic invokes. -/
example (x y : BitVec 64) : wEnc (x * x + y) = wEnc x * wEnc x + wEnc y :=
  (inferInstance : Transfer.Related wEnc (x * x + y) (wEnc x * wEnc x + wEnc y)).rel

example (x y z : BitVec 64) : wEnc (x * y - z) = wEnc x * wEnc y - wEnc z :=
  (inferInstance : Transfer.Related wEnc (x * y - z) (wEnc x * wEnc y - wEnc z)).rel

/-! ## Phase-1 Param-engine bridge: one registration, both engines

The three `RelatedBinOp` squares above (`wEncAdd`/`wEncMul`/`wEncSub`) drive the
`Related` engine (`composeBinOp`/`inferInstance`). ParamTransfer's `Param` engine
(`#transfer`/`translateAll`) instead consumes curried `@[param]` `RArrow` witnesses.
Rather than a second proof, `Transfer.Param.paramWitnessOfRelatedBinOp` *derives*
each `RArrow` witness from the already-registered square — the `BitVec.toNat_*`/`ZMod`
content lives in exactly one place (the `RelatedBinOp` instance), and both engines
resolve the word ops through it. This mirrors `bbMulParam`/`bbAddParam` in
ParamTransfer's `Examples/ParamCryptoDomains.lean`. -/

open Transfer.Param

/-- Word addition, `Param`-engine witness. `RArrow (encRel wEnc) (RArrow …)` is the
    curried binary function relation over the encoding graph `encRel wEnc a b := wEnc a = b`;
    on `wEnc`-related arguments the concrete `BitVec 64` `+` and the abstract
    `ZMod 2^64` `+` agree. Registered with `@[param]` (keyed under `HAdd.hAdd`).
    Derived from the `RelatedBinOp` square `wEncAdd` — no re-proof. -/
@[param] theorem wEncAddParam :
    RArrow (encRel wEnc) (RArrow (encRel wEnc) (encRel wEnc))
      (HAdd.hAdd : BitVec 64 → BitVec 64 → BitVec 64)
      (HAdd.hAdd : ZMod (2 ^ 64) → ZMod (2 ^ 64) → ZMod (2 ^ 64)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc) (op := (· + ·)) (bop := (· + ·))

/-- Word multiplication, `Param`-engine witness. As `wEncAddParam`, derived from
    the `RelatedBinOp` square `wEncMul` and keyed under `HMul.hMul`. -/
@[param] theorem wEncMulParam :
    RArrow (encRel wEnc) (RArrow (encRel wEnc) (encRel wEnc))
      (HMul.hMul : BitVec 64 → BitVec 64 → BitVec 64)
      (HMul.hMul : ZMod (2 ^ 64) → ZMod (2 ^ 64) → ZMod (2 ^ 64)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc) (op := (· * ·)) (bop := (· * ·))

/-- Word subtraction, `Param`-engine witness. As `wEncAddParam`, derived from the
    `RelatedBinOp` square `wEncSub` and keyed under `HSub.hSub`. -/
@[param] theorem wEncSubParam :
    RArrow (encRel wEnc) (RArrow (encRel wEnc) (encRel wEnc))
      (HSub.hSub : BitVec 64 → BitVec 64 → BitVec 64)
      (HSub.hSub : ZMod (2 ^ 64) → ZMod (2 ^ 64) → ZMod (2 ^ 64)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc) (op := (· - ·)) (bop := (· - ·))

/-- The `Param`-engine witness applied directly at reflexive arguments yields the
    word equation, exactly as `bbAddParam a a rfl b b rfl` does for the field. -/
example (x y : BitVec 64) : wEnc (x + y) = wEnc x + wEnc y :=
  wEncAddParam x _ rfl y _ rfl

/-- A whole `wEnc` word-op tree closed through the **`Param` engine** — the composed
    `@[param]` `RArrow` witnesses above — as opposed to the `Related`-engine
    `composeBinOp` used for the same tree earlier. Same commuting-square content, the
    *other* registry: the register-once bridge feeds one square to both. -/
theorem wEncTreeAddParam (x y : BitVec 64) :
    wEnc (x * x + y) = wEnc x * wEnc x + wEnc y :=
  wEncAddParam (x * x) _ (wEncMulParam x _ rfl x _ rfl) y _ rfl

/-- The subtraction tree, likewise through the `Param`-engine witnesses. -/
theorem wEncTreeSubParam (x y z : BitVec 64) :
    wEnc (x * y - z) = wEnc x * wEnc y - wEnc z :=
  wEncSubParam (x * y) _ (wEncMulParam x _ rfl y _ rfl) z _ rfl

/-! ### `param_auto` on `wEnc` trees: a documented negative

The `param_auto` coordinator closes an *`enc = id`* word tree (ParamTransfer's Baby
Bear example `a * b + c = bbFieldAdd (bbFieldMul a b) c`) by routing to its `rcongr`/
`param_solve` surfaces. It does **not** close a `wEnc`-wrapped tree
(`wEnc (x * x + y) = …`): the descent reads the outer `Eq` at the *identity* encoding,
rewrites to a `Related id …` / raw-`Eq` leaf, and hands that leaf to `grind`, which
cannot discharge the `wEnc (op a b) = bop (wEnc a) (wEnc b)` commuting identity — that
content lives in the `RelatedBinOp` square and is only applied when the encoding `wEnc`
is the relation head (the `Related wEnc …`/`composeBinOp` route, or the composed
`@[param]` witnesses above). So for `enc ≠ id` word trees the two working surfaces are
`composeBinOp` (`Related` engine) and the composed `@[param]` witnesses (`Param`
engine); `param_auto` remains the coordinator for the field/`enc = id` case. -/

/-! ### Word-phase `∀`-domain (`TransferDom`): documented gap

`param_transfer`'s `∀`-rule resolves a `TransferDom A A'` carrying a
`Param .map0 .map2a A A'` — a *backward* section `A' → A` with `map_in_R`. For the
word phase that domain would be `TransferDom (BitVec 64) (ZMod 2^64)`, whose
backward leg is a decoder `ZMod 2^64 → BitVec 64`. The round-trip exists
(`ZMod.val` then `BitVec.ofNat 64`, inverse to `wEnc` on canonical residues), but
the resulting domain is *non-diagonal*, and — exactly as ParamTransfer documents
for its own `ZMod ↔ limbs` case in `ParamCryptoDomains.lean` — the `∀`-rule then
delivers a pointwise obligation phrased against a *limb* predicate the caller must
supply by hand, blocked on the annotation-inference gap, not on a missing
primitive. So the word-phase representation change is carried by the op-level
`@[param]`/`RelatedBinOp` witnesses above (which both engines share), and no
word-phase `TransferDom` is registered here. -/

/-! ## Concrete Phase-1 state relation + a real value leaf

`SRword` ties the ParamTransfer encoding `wEnc` into the state relation: the abstract
value at each name is the `wEnc`-encoding of the concrete `.sword 64` it holds. The
literal-assignment leaf `corres_setScalar` is then discharged against the real
`semScalar` `RScalarSet` arm. This is where ParamTransfer owns the value level. -/

/-- The word-phase state relation: every name holds a `.sword 64` whose ParamTransfer
    encoding `wEnc` is the abstract value. -/
def SRword (env : SEnvScalar) (a : String → ZMod (2 ^ 64)) : Prop :=
  ∀ x, ∃ w : BitVec 64, env x = some ⟨.sword 64, w⟩ ∧ wEnc w = a x

/-- `RScalarSet name n` — the literal-assignment value leaf. The abstract sets `name`
    to `(n : ZMod 2^64) = wEnc (ofNat 64 n)`, discharged against the real `semScalar`
    arm `some (env.upd name (.sword 64) (BitVec.ofNat 64 n))`. -/
theorem corres_setScalar (name : String) (n : Nat) :
    Corres SRword (fun _ => True)
      (fun a s => if s = name then (n : ZMod (2 ^ 64)) else a s)
      (.RScalarSet name n) := by
  intro env a hSR _
  refine ⟨env.upd name (t := .sword 64) (BitVec.ofNat 64 n), rfl, ?_⟩
  intro x
  by_cases hx : x = name
  · subst hx
    exact ⟨BitVec.ofNat 64 n, by simp [SEnvScalar.upd],
      by simp [wEnc, BitVec.toNat_ofNat, ZMod.natCast_mod]⟩
  · obtain ⟨w, hw, hwn⟩ := hSR x
    exact ⟨w, by simp [SEnvScalar.upd, hx, hw], by simp [hx, hwn]⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
