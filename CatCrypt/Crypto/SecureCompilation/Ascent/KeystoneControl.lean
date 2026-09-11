/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.EmitBridge
public import CatCrypt.Crypto.SecureCompilation.Ascent.Control

/-!
# Discharging the keystone adapter `hAgree` for control kernels

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`);
see `Corres.lean`._

`Ascent/EmitBridge.lean`'s `keystone` requires the closed-kernel adapter

  `hAgree : ∀ e, semScalar c env₀ = some e → e name = some ⟨.sword 64, val⟩`

— the tracked output word at the written `name` is a fixed word, independent of
the entry env `env₀`. For a straight-line closed kernel (`RScalarSet`) this is
`rfl` (see `keystone_setScalar`). For kernels with **control** (`RIfNz` φ-merge,
`RFor` bounded loop) it is a real lemma: the output word is still a fixed word
computable from the kernel (`valOf c`), because every value the kernel reads is
one it wrote earlier from a literal.

This module proves that env-independence for the two covered control shapes and
instantiates `keystone` with it, yielding `keystone_if` / `keystone_for`
analogous to `keystone_setScalar`.

## `RIfNz` (φ-merge)

The closed conditional kernel is
`RSeq (RScalarSet g gv) (RIfNz g (RScalarSet r tv) (RScalarSet r ev))`:
the guard `g` is *set to a literal* `gv` before the branch reads it, so the cmov
`phiSelect (ofNat gv) (ofNat tv) (ofNat ev)` the `RIfNz` arm computes is a fixed
word — env-independent. `ifClosed_hAgree` proves exactly this seam.

## `RFor` (bounded loop)

The closed loop kernel `RFor x N (RScalarSet r v)` (with `N ≥ 1`) writes the
literal `ofNat v` into `r` on the last trip, so the loop output at `r` is `ofNat
v`, independent of the entry env. `forClosed_hAgree` proves this via
`semRForD`'s last-trip peel.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (asSingleScalarSet)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## `RIfNz` closed kernel: definitions -/

/-- The closed φ-merge conditional kernel: set the guard `g` to a literal `gv`,
    then a single-name conditional whose branches both set `r` to a literal. -/
def ifClosedKernel (g r : String) (gv tv ev : Nat) : LowCT :=
  .RSeq (.RScalarSet g gv)
    (.RIfNz g (.RScalarSet r tv) (.RScalarSet r ev))

/-- The fixed output word of `ifClosedKernel`: the cmov of the two literal
    branches on the *literal* guard word `ofNat gv`. Independent of the entry env. -/
def ifClosedVal (gv tv ev : Nat) : BitVec 64 :=
  phiSelect (w := 64) (BitVec.ofNat 64 gv) (BitVec.ofNat 64 tv) (BitVec.ofNat 64 ev)

/-! ## `RIfNz` env-independence (the keystone adapter) -/

/-- **`ifClosed_hAgree`.** The output word of the closed φ-merge kernel at the
    written name `r` is the fixed word `ifClosedVal gv tv ev`, for **any** entry
    env `env₀`. This is the control-kernel replacement for the `rfl` that
    discharges `keystone`'s `hAgree` in the straight-line case. -/
theorem ifClosed_hAgree (g r : String) (gv tv ev : Nat) (env₀ : SEnvScalar) :
    ∀ e, semScalar (ifClosedKernel g r gv tv ev) env₀ = some e →
      e r = some ⟨.sword 64, ifClosedVal gv tv ev⟩ := by
  intro e he
  -- The `RIfNz` arm reads `g` (= `ofNat gv`) from the guard-set env.
  have hg : (env₀.upd g (t := .sword 64) (BitVec.ofNat 64 gv)) g
      = some ⟨.sword 64, BitVec.ofNat 64 gv⟩ := by simp [SEnvScalar.upd]
  -- Compute the sequenced semantics: set `g := gv`, then run the `RIfNz` arm.
  have hstep : semScalar (ifClosedKernel g r gv tv ev) env₀
      = some ((env₀.upd g (t := .sword 64) (BitVec.ofNat 64 gv)).upd r (t := .sword 64)
          (ifClosedVal gv tv ev)) := by
    -- The guard-set `RScalarSet` and the `Option.bind` both reduce definitionally,
    -- leaving the `RIfNz` arm run at the guard-set env.
    show semScalar (.RIfNz g (.RScalarSet r tv) (.RScalarSet r ev))
        (env₀.upd g (t := .sword 64) (BitVec.ofNat 64 gv)) = _
    simp [semScalar, hg, asSingleScalarSet, ifClosedVal]
  rw [hstep] at he
  injection he with he'
  subst he'
  simp [SEnvScalar.upd]

/-! ## The control-kernel keystone for `RIfNz` -/

/-- **`keystone_if`.** The keystone instantiated at the closed φ-merge kernel:
    the branch abstraction (`corres_setScalar` for the guard, `corres_if` for the
    branch, sequenced by `corres_seq`) plus the env-independence adapter
    `ifClosed_hAgree` discharge `keystone`, so an emit output `Emit (ifClosedVal ..)`
    is pinned to the clean-spec branch select
    `if gv = 0 then ev else tv` in `ZMod 2^64`. Analogous to `keystone_setScalar`,
    but for a genuine conditional kernel. -/
theorem keystone_if {β : Type} (Emit : BitVec 64 → β)
    (g r : String) (gv tv ev : Nat) (jdenote : β)
    (hEmit : jdenote = Emit (ifClosedVal gv tv ev)) :
    jdenote = Emit (ifClosedVal gv tv ev)
      ∧ wEnc (ifClosedVal gv tv ev)
          = (if (gv : ZMod (2 ^ 64)) = 0 then (ev : ZMod (2 ^ 64)) else (tv : ZMod (2 ^ 64))) := by
  let env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩
  -- The branch abstraction: guard-set then a genuine φ-merge conditional.
  have hCorres :
      Corres SRword (fun _ => True)
        (fun a => (fun b s => if s = r then
              (if b g = 0 then (ev : ZMod (2 ^ 64)) else (tv : ZMod (2 ^ 64))) else b s)
            (fun s => if s = g then (gv : ZMod (2 ^ 64)) else a s))
        (ifClosedKernel g r gv tv ev) :=
    corres_seq (SR := SRword) (corres_setScalar g gv) (corres_if g r tv ev) (fun _ _ => trivial)
  have h := keystone Emit (ifClosedKernel g r gv tv ev) r (ifClosedVal gv tv ev) _ (fun _ => True)
    env₀ (fun _ => wEnc 0) jdenote
    hCorres (fun _ => ⟨0, rfl, rfl⟩) trivial (ifClosed_hAgree g r gv tv ev env₀) hEmit
  refine ⟨h.1, ?_⟩
  rw [h.2]; simp

/-- A concrete closed branch kernel: a literal-`0` guard selects the else-value
    `9`, so the pinned clean spec is `(9 : ZMod 2^64)`. Exhibits `keystone_if` is
    non-vacuous (a real conditional keystone that closes). -/
theorem keystone_if_example :
    (ifClosedVal 0 7 9) = (ifClosedVal 0 7 9)
      ∧ wEnc (ifClosedVal 0 7 9) = (9 : ZMod (2 ^ 64)) := by
  have h := keystone_if (β := BitVec 64) id "c" "o" 0 7 9 (ifClosedVal 0 7 9) rfl
  refine ⟨h.1, ?_⟩
  rw [h.2]; simp

/-! ## `RFor` closed kernel: definitions

The closed bounded-loop kernel writes the literal `v` into `r` each trip and
resets the counter `x` to `0` after the body, so both the loop output at `r` and
the per-trip abstract step are counter-independent — the reset is what lets the
`n`-independent loop-invariant step `forStep` model the concrete `RSeq (RScalarSet
x n) body` under the every-name relation `SRword` (`corres_for`'s hypothesis
shape). -/

/-- The closed bounded-loop kernel: `N` trips, each setting `r := v` (literal) then
    resetting the counter `x := 0`. -/
def forClosedKernel (x r : String) (v N : Nat) : LowCT :=
  .RFor x N (.RSeq (.RScalarSet r v) (.RScalarSet x 0))

/-- The counter-independent loop-invariant abstract step: set `x := 0`, `r := v`. -/
def forStep (x r : String) (v : Nat) :
    (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a s => if s = x then (0 : ZMod (2 ^ 64)) else if s = r then (v : ZMod (2 ^ 64)) else a s

/-- Swap a `Corres`'s abstract function for a pointwise-equal one. -/
theorem corres_fa_congr {AState : Type} {SR : SEnvScalar → AState → Prop}
    {P : AState → Prop} {f g : AState → AState} {c : LowCT}
    (h : Corres SR P f c) (hfg : ∀ a, f a = g a) : Corres SR P g c := by
  intro env a hSR hP
  obtain ⟨env', hs, hSR'⟩ := h env a hSR hP
  exact ⟨env', hs, hfg a ▸ hSR'⟩

/-! ## `RFor` env-independence (the keystone adapter) -/

/-- **`forClosed_hAgree`.** With `r ≠ x`, the closed bounded-loop kernel's output
    at `r` is the fixed literal word `ofNat v`, for **any** entry env — the last
    trip writes `r := v` and the counter reset `x := 0` leaves `r` untouched. The
    control-kernel `hAgree` for the loop. -/
theorem forClosed_hAgree (x r : String) (v N' : Nat) (hne : r ≠ x) (env₀ : SEnvScalar) :
    ∀ e, semScalar (forClosedKernel x r v (N' + 1)) env₀ = some e →
      e r = some ⟨.sword 64, BitVec.ofNat 64 v⟩ := by
  intro e he
  -- Peel the last trip of `semRForD`.
  have he' :
      (match semRForD (fun e => semScalar (.RSeq (.RScalarSet r v) (.RScalarSet x 0)) e) x N' env₀ with
        | some envPre =>
            semScalar (.RSeq (.RScalarSet r v) (.RScalarSet x 0))
              (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 N'))
        | none => none) = some e := he
  cases hpre :
      semRForD (fun e => semScalar (.RSeq (.RScalarSet r v) (.RScalarSet x 0)) e) x N' env₀ with
  | none => rw [hpre] at he'; simp at he'
  | some envPre =>
      rw [hpre] at he'
      simp only [semScalar, Option.bind_some] at he'
      injection he' with he''
      subst he''
      simp [SEnvScalar.upd, hne]

/-! ## The control-kernel keystone for `RFor` -/

/-- **`keystone_for`.** The keystone instantiated at the closed bounded-loop
    kernel: `corres_for` supplies the loop abstraction (each trip realized by
    `forStep`, glued from three `corres_setScalar`s and re-based to the fixed step
    by `corres_fa_congr`), and `forClosed_hAgree` is the env-independence adapter.
    With `r ≠ x` the emit output `Emit (ofNat v)` is pinned to the clean-spec
    literal `(v : ZMod 2^64)`. Analogous to `keystone_setScalar`, but for a
    genuine bounded loop. -/
theorem keystone_for {β : Type} (Emit : BitVec 64 → β)
    (x r : String) (v N' : Nat) (hne : r ≠ x) (jdenote : β)
    (hEmit : jdenote = Emit (BitVec.ofNat 64 v)) :
    jdenote = Emit (BitVec.ofNat 64 v)
      ∧ wEnc (BitVec.ofNat 64 v) = (v : ZMod (2 ^ 64)) := by
  let env₀ : SEnvScalar := fun _ => some ⟨.sword 64, (0 : BitVec 64)⟩
  -- Each trip: counter-set is overwritten, so the fixed `forStep` models it.
  have hbody : ∀ n : Nat,
      Corres SRword (fun _ => True) (forStep x r v)
        (.RSeq (.RScalarSet x n) (.RSeq (.RScalarSet r v) (.RScalarSet x 0))) := by
    intro n
    refine corres_fa_congr
      (corres_seq (SR := SRword) (corres_setScalar x n)
        (corres_seq (SR := SRword) (corres_setScalar r v) (corres_setScalar x 0)
          (fun _ _ => trivial)) (fun _ _ => trivial)) ?_
    intro a
    funext s
    simp only [forStep]
    by_cases hsx : s = x
    · simp [hsx]
    · by_cases hsr : s = r <;> simp [hsx, hsr]
  -- The bounded loop realizes the `N`-fold of `forStep`.
  have hloop :
      Corres SRword (fun _ => True) (nfold (forStep x r v) (N' + 1))
        (forClosedKernel x r v (N' + 1)) :=
    corres_for (SR := SRword) x (.RSeq (.RScalarSet r v) (.RScalarSet x 0)) hbody
      (fun _ _ => trivial) (N' + 1)
  -- The loop output at `r` is the counter-independent literal `v`.
  have hval : nfold (forStep x r v) (N' + 1) (fun _ => wEnc 0) r = (v : ZMod (2 ^ 64)) := by
    show forStep x r v (nfold (forStep x r v) N' (fun _ => wEnc 0)) r = _
    simp [forStep, hne]
  have h := keystone Emit (forClosedKernel x r v (N' + 1)) r (BitVec.ofNat 64 v) _ (fun _ => True)
    env₀ (fun _ => wEnc 0) jdenote
    hloop (fun _ => ⟨0, rfl, rfl⟩) trivial (forClosed_hAgree x r v N' hne env₀) hEmit
  exact ⟨h.1, h.2.trans hval⟩

/-- A concrete closed loop kernel (`3` trips, counter `"i"`, output `"o" := 5`):
    the pinned clean spec is `(5 : ZMod 2^64)`. Exhibits `keystone_for` is
    non-vacuous (a real bounded-loop keystone that closes). -/
theorem keystone_for_example :
    (BitVec.ofNat 64 5) = (BitVec.ofNat 64 5)
      ∧ wEnc (BitVec.ofNat 64 5) = (5 : ZMod (2 ^ 64)) :=
  keystone_for (β := BitVec 64) id "i" "o" 5 2 (by decide) (BitVec.ofNat 64 5) rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
