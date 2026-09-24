/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves

/-!
# C-tie: compile-from-hax output realizes an abstract `Dependencies` record

This module is the **security-tie** step of the verified compiler, scoped to the
*mechanism*. It answers the question:

> *Do our security proofs keep working when the primitives they reason about are
> emitted by the verified `compileFromHax` compiler rather than written by hand?*

It does so by reproducing the **`SurfaceDeps` contract in miniature**: an
abstract dependency record `RoundDeps` with one field per SHA-256 round
primitive, an abstract *spec* instance `roundDepsSpec` (the FIPS 180-4 formulas a
security proof assumes the primitives compute), and a *realization* instance
`toRoundDeps` whose fields are the **functions the verified-compiled jasmin `Com`
artifacts compute**. The tie theorem `toRoundDeps_eq_spec` proves these are equal:

> the function the verified-compiled jasmin `Com` computes **is** the abstract
> spec field the security layer assumes.

Concretely the compiled functions are extracted from the committed leaves
(`CompileFromHaxLeaves`): `bigSigma0_compiles`, `bigSigma1_compiles`,
`maj_compiles`, `ch_compiles`. Each of those packages an existential
`∃ c, compileFromHax … = some c ∧ ∀ inputs, c.denote … = <FIPS spec>`; here we
*consume* that existential exactly as a downstream `SurfaceDeps` would — destructure
it to obtain the compiled `Com`, define the function it computes, and use the
value-agreement clause to discharge the realization equality.

## Why this is the answer to "do the security proofs keep working"

A `SurfaceDeps`-style bridge wires concrete primitive realizations into an
abstract `Dependencies` structure that a security/UC theorem consumes
(`to<X>Deps : <X>Dependencies`, see e.g. `HPKE/SurfaceDeps.lean`). The abstract
proof is parametric over the `Dependencies`; it only ever reasons through the
*spec* the fields are assumed to satisfy. Therefore:

* If `toRoundDeps = roundDepsSpec` (this file's `toRoundDeps_eq_spec`), then any
  abstract theorem of the shape
  `∀ (D : RoundDeps 32), D = roundDepsSpec → <security property of a scheme using D>`
  **applies verbatim to the compiled artifact** `toRoundDeps` — with **no new
  axioms**: the compiled-leaf value-agreement (`compileFromHax_meets_spec` routed
  through each `*_compiles`) composes with the abstract security proof by plain
  equality substitution.

`appliesToCompiled` is exactly that composition, stated and proved generically.

## Scope

This proves the **connective principle**: a verified-compiled leaf (a
`Com jasmin` proven equal to its FIPS spec) realizes an abstract `Dependencies`
field that a security-style theorem consumes — value-agreement composes with the
abstract proof, *no new axioms*. The per-real-protocol tie — wiring these into,
e.g., a concrete SHA-256/HMAC `Dependencies` and its full UC theorem — is the
fan-out, not re-proved here; this file pins down the mechanism on the round
primitives. CT / robust-security *preservation* for this compiled output is a
separate, independently-proved property (the RD5 `thirDialect` RHP arc), not in
scope here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLeaves

/-! ## §1  The abstract dependency record

`RoundDeps w` is the miniature `Dependencies`: an abstract structure whose fields
are the SHA-256 round primitives a security proof reasons through. A scheme proof
would be parametric over a `RoundDeps w` and only ever use the *spec* its fields
satisfy. Two single-input primitives (`bigSigma0`, `bigSigma1`) and two
three-input primitives (`maj`, `ch`) cover both leaf arities. -/

/-- The abstract SHA-256-round dependency record. A security proof over a scheme
    that uses these primitives is parametric over a `RoundDeps w`; the fields are
    the primitives it assumes available. -/
structure RoundDeps (w : Nat) where
  /-- The big-sigma-0 compression-function primitive. -/
  bigSigma0 : BitVec w → BitVec w
  /-- The big-sigma-1 compression-function primitive. -/
  bigSigma1 : BitVec w → BitVec w
  /-- The majority primitive. -/
  maj : BitVec w → BitVec w → BitVec w → BitVec w
  /-- The choose primitive. -/
  ch : BitVec w → BitVec w → BitVec w → BitVec w

/-! ## §2  The abstract spec instance (what a security proof assumes)

`roundDepsSpec` fills each field with the FIPS 180-4 formula — exactly the value a
security proof assumes the primitive computes. This is the *abstract* side of the
bridge: no compiler, no extraction, just the reference semantics. -/

/-- The abstract spec instance: each field is the FIPS 180-4 reference formula a
    SHA-256 security proof assumes the primitive computes. -/
def roundDepsSpec : RoundDeps 32 where
  bigSigma0 := fun x => x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
  bigSigma1 := fun x => x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
  maj := fun x y z => (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
  ch := fun x y z => (x &&& y) ^^^ ((~~~x) &&& z)

/-! ## §3  The compiled functions (what the verified compiler emits)

For each round primitive we extract, from the committed `*_compiles` leaf, the
function the verified-compiled jasmin `Com` actually computes:
`fun … => (the compiled Com).denote (inputValuation …)`. We destructure each
existential leaf — exactly as a downstream `SurfaceDeps` consumer would — to name
the compiled `Com` and carry its value-agreement clause. -/

/-- The compiled big-sigma-0 `Com` together with its FIPS value-agreement, taken
    from the committed leaf `bigSigma0_compiles`. -/
noncomputable def bigSigma0Compiled := bigSigma0_compiles.choose
theorem bigSigma0Compiled_spec :
    compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma0Src = some bigSigma0Compiled ∧
    ∀ (x : BitVec 32),
      bigSigma0Compiled.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22 :=
  bigSigma0_compiles.choose_spec

/-- The compiled big-sigma-1 `Com` together with its FIPS value-agreement. -/
noncomputable def bigSigma1Compiled := bigSigma1_compiles.choose
theorem bigSigma1Compiled_spec :
    compileFromHax (w := 32) (nIn := 1) ["x"] bigSigma1Src = some bigSigma1Compiled ∧
    ∀ (x : BitVec 32),
      bigSigma1Compiled.denote (inputValuation 32 1 (fun _ => x))
        = x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25 :=
  bigSigma1_compiles.choose_spec

/-- The compiled majority `Com` together with its FIPS value-agreement. -/
noncomputable def majCompiled := maj_compiles.choose
theorem majCompiled_spec :
    compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] majSrc = some majCompiled ∧
    ∀ (x y z : BitVec 32),
      majCompiled.denote (inputValuation 32 3 ![x, y, z])
        = (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z) :=
  maj_compiles.choose_spec

/-- The compiled choose `Com` together with its FIPS value-agreement. -/
noncomputable def chCompiled := ch_compiles.choose
theorem chCompiled_spec :
    compileFromHax (w := 32) (nIn := 3) ["x", "y", "z"] chSrc = some chCompiled ∧
    ∀ (x y z : BitVec 32),
      chCompiled.denote (inputValuation 32 3 ![x, y, z])
        = (x &&& y) ^^^ ((~~~x) &&& z) :=
  ch_compiles.choose_spec

/-- The function the verified-compiled big-sigma-0 jasmin `Com` computes. -/
noncomputable def compiledBigSigma0Fn : BitVec 32 → BitVec 32 :=
  fun x => bigSigma0Compiled.denote (inputValuation 32 1 (fun _ => x))

/-- The function the verified-compiled big-sigma-1 jasmin `Com` computes. -/
noncomputable def compiledBigSigma1Fn : BitVec 32 → BitVec 32 :=
  fun x => bigSigma1Compiled.denote (inputValuation 32 1 (fun _ => x))

/-- The function the verified-compiled majority jasmin `Com` computes. -/
noncomputable def compiledMajFn : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun x y z => majCompiled.denote (inputValuation 32 3 ![x, y, z])

/-- The function the verified-compiled choose jasmin `Com` computes. -/
noncomputable def compiledChFn : BitVec 32 → BitVec 32 → BitVec 32 → BitVec 32 :=
  fun x y z => chCompiled.denote (inputValuation 32 3 ![x, y, z])

/-! ## §4  The tie theorems: compiled function = abstract spec field

Each tie theorem says the **function the verified-compiled jasmin `Com` computes
is the abstract spec field** the security layer assumes. They are immediate from
the value-agreement clause of the committed leaves. -/

/-- **Tie (Σ₀).** The compiled big-sigma-0 function equals `roundDepsSpec.bigSigma0`. -/
theorem compiledBigSigma0Fn_eq : compiledBigSigma0Fn = roundDepsSpec.bigSigma0 := by
  funext x; exact bigSigma0Compiled_spec.2 x

/-- **Tie (Σ₁).** The compiled big-sigma-1 function equals `roundDepsSpec.bigSigma1`. -/
theorem compiledBigSigma1Fn_eq : compiledBigSigma1Fn = roundDepsSpec.bigSigma1 := by
  funext x; exact bigSigma1Compiled_spec.2 x

/-- **Tie (Maj).** The compiled majority function equals `roundDepsSpec.maj`. -/
theorem compiledMajFn_eq : compiledMajFn = roundDepsSpec.maj := by
  funext x y z; exact majCompiled_spec.2 x y z

/-- **Tie (Ch).** The compiled choose function equals `roundDepsSpec.ch`. -/
theorem compiledChFn_eq : compiledChFn = roundDepsSpec.ch := by
  funext x y z; exact chCompiled_spec.2 x y z

/-! ## §5  The realization instance and the `SurfaceDeps` shape

`toRoundDeps` is the **`SurfaceDeps` shape**: the verified-compiled leaves fill
the abstract `Dependencies` fields. `toRoundDeps_eq_spec` is the *realization
theorem* — the compiled leaves equal the spec the abstract security proof reasons
about. This is the file's deliverable. -/

/-- The realization instance: the abstract `RoundDeps` filled with the functions
    the **verified compiler emits** for each round primitive. This is the
    `SurfaceDeps` shape — `to<X>Deps` wiring concrete (here compiler-emitted)
    realizations into the abstract dependency record. -/
noncomputable def toRoundDeps : RoundDeps 32 where
  bigSigma0 := compiledBigSigma0Fn
  bigSigma1 := compiledBigSigma1Fn
  maj := compiledMajFn
  ch := compiledChFn

/-- **The realization theorem.** The compiled-leaf realization instance equals the
    abstract FIPS spec instance: the verified compiler's emitted round primitives
    compute exactly what a SHA-256 security proof assumes. Every field is closed by
    the corresponding §4 tie theorem (compiled function = spec field), which in turn
    is the value-agreement clause of the committed `*_compiles` leaf. -/
theorem toRoundDeps_eq_spec : toRoundDeps = roundDepsSpec := by
  unfold toRoundDeps
  rw [compiledBigSigma0Fn_eq, compiledBigSigma1Fn_eq, compiledMajFn_eq, compiledChFn_eq]

/-! ## §6  The generic transfer lemma (record-agnostic, reusable)

The connective principle is **not** specific to `RoundDeps` or to SHA-256: it
holds for *any* dependency record type. `tie_transfer` states it once, abstracted
over the dependency type `Deps` and over both the spec and the compiled-
realization instances: **any** property `P` proved of the abstract spec instance
transfers to the compiled-realization instance, given the field-by-field
realization equality `compiledD = specD`.

That single equality is what each protocol discharges from its own leaves: the
leaves' `*_compiles` value-agreement composed with the abstract per-field tie
(compiled function = spec field) composed with the repr-bridge — exactly the §4–§5
chain culminating in `toRoundDeps_eq_spec` for the SHA-256 pilot here. Once a
protocol has that equality, it reuses `tie_transfer` verbatim to push **any**
security property of its abstract `Dependencies` onto the compiler-emitted
realization, with no new axioms (just `▸`). -/

/-- **Generic security-tie transfer (record-agnostic).** For any dependency type
    `Deps`, any property `P : Deps → Prop`, and any two instances `specD`,
    `compiledD : Deps`, the realization equality `compiledD = specD` transfers
    every property proven of the spec instance to the compiled instance.

    This is the reusable core of the compile-from-hax security tie: a downstream
    protocol proves `compiledD = specD` field-by-field from its leaves'
    `*_compiles` value-agreement (∘ abstract per-field tie ∘ repr-bridge), then
    feeds that equality here to inherit any abstract security property `P` of
    `specD` on the verified-compiler-emitted `compiledD` — with **no new axioms**
    (the proof is a single `▸`). The SHA-256 `appliesToCompiled` below is the
    first client. -/
theorem tie_transfer {Deps : Type*} (P : Deps → Prop) {specD compiledD : Deps}
    (hreal : compiledD = specD) (h : P specD) : P compiledD :=
  hreal ▸ h

/-- **Compiled artifact inherits any abstract dependency property.** For every
    property `P` of `RoundDeps 32`, if `P` holds of the abstract spec instance then
    it holds of the compiler-emitted realization instance. The mechanized statement
    that compile-from-hax output plugs into the abstract security layer: a security
    theorem proved over `roundDepsSpec` transfers verbatim to `toRoundDeps`, the
    verified compiler's emitted primitives — with no new axioms.

    This is the **first client** of the generic, record-agnostic
    `tie_transfer`: it instantiates `tie_transfer` at `Deps := RoundDeps 32` with
    the SHA-256 realization equality `toRoundDeps_eq_spec`. -/
theorem appliesToCompiled (P : RoundDeps 32 → Prop) (h : P roundDepsSpec) :
    P toRoundDeps :=
  tie_transfer P toRoundDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie
