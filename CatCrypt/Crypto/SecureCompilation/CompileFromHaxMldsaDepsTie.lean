/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaReduce32
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPoly
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomeryTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecompose
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecomposeFull
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie

/-!
# Representation bridge: the verified compiler emits ML-DSA's per-coefficient
# reduce primitives, tied to an abstract per-coefficient `Dependencies` record

This module is the **ML-DSA instance** of the compile-from-hax security-tie
mechanism pinned generically in `CompileFromHaxSecurityTie` (the SHA-256 round
pilot). It reproduces the `SurfaceDeps`-in-miniature shape — an abstract
per-coefficient dependency record `MldsaReduceDeps`, a *spec* instance
`mldsaReduceDepsSpec` (the FIPS-204 reference per-coefficient functions a
correctness argument reasons through), and a *realization* instance
`toMldsaReduceDeps` whose fields are the functions the **verified
`compileFromHax` compiler emits** — and proves they are equal field-by-field
(`toMldsaReduceDeps_eq_spec`). The generic `tie_transfer` then transfers any
property of the spec instance onto the compiled realization with no new axioms.

## What is tied (functional correctness, per-coefficient, `BitVec 64`)

Each field is the per-coefficient signed-`int32` body of an ML-DSA-65 reduce
primitive (`q = 8380417`), carried sign-extended into `BitVec 64` (the owned
`PolyEmit` / `*Emit` convention). All come from the committed
`*_compiles` leaves; the realization equality is their value-agreement clause:

| Field          | Compiled leaf (`*_compiles`)        | Emit form / abstract tie                          |
|----------------|-------------------------------------|---------------------------------------------------|
| `reduce32`     | `mldsaReduce32_compiles`            | `mldsaReduce32Form` (`mldsaReduce32Form_sub_eq_quotient`) |
| `caddq`        | `mldsaCaddq_compiles`               | `mldsaCaddqFold`  (`mldsaCaddqFold_eq_centeredCanonical`) |
| `montgomery`   | `mldsaMontgomery_compiles`          | `mldsaMontgomeryForm` (`mldsaMontgomery_montgomery_congruence`) |
| `power2roundA1`| `power2roundA1_compiles`            | `power2roundA1Spec` (`power2roundReconstruct_eq`) |
| `power2roundA0`| `power2roundA0_compiles`            | `power2roundA0Spec` (`power2roundReconstruct_eq`) |
| `decomposeA0`  | `mldsaDecomposeA0_compiles`         | `mldsaDecomposeA0Form` (`decomposeA0_signMask_select`) |

The right column lists the committed *abstract* identity each emit
form satisfies (mod-`q` congruence / canonical-range / reconstruction); those are
proved in the leaf modules and are not re-proved here. This file is the
**functional-correctness tie**: it states *the emitted artifact computes exactly
the per-coefficient reduce function the spec specifies*, framed as
`compiled = spec`, not as a new security bound.

## Representation gap to the protocol `Dependencies`

The abstract `MLDSADependencies` / `PureMLDSACrypto` fields that the ML-DSA
*security* proof consumes (`HaxTypes.lean`) operate at the **whole-`Vec` / whole-
`Poly`** level — `f_highBits : Vec → Vec`, `f_lowBits : Vec → Vec`,
`f_mat_vecL_mul : Mat → VecL → Vec`, … — over **abstract, uninterpreted** carrier
types (`Vec`, `VecL`, `Mat`, `MLDSAPoly`). The single per-coefficient field,
`f_mod_q : MLDSACoeff → MLDSACoeff` (with `MLDSACoeff = UInt32`), is likewise an
**uninterpreted structure field**: no in-tree `PureMLDSACrypto` instance pins it
to the FIPS-204 Barrett `reduce32` body. There is therefore **no concrete
`Dependencies` field whose definition is one of these leaves**, so wiring a leaf
*into* `f_mod_q` / `f_highBits` (an `:= a` style placeholder substitution) would
be tying to an uninterpreted/placeholder field — exactly what the task forbids.

What this file does is the **repr-bridge layer**: pin an
abstract per-coefficient reduce-`Dependencies` record (`MldsaReduceDeps`, the
representation the leaves actually live at — per-coeff `BitVec 64`), give it the
FIPS reference spec, and prove the verified-compiler-emitted leaves realize that
spec. This is the canonical mechanism from `CompileFromHaxSecurityTie`, applied
to the ML-DSA reduce family. The remaining gap — a concrete `PureMLDSACrypto`
whose `f_highBits`/`f_lowBits`/`f_mod_q` are *defined* (lifting these per-coeff
`BitVec 64` bodies through `UInt32 ≃ BitVec 32` and over a 256-coefficient
`Poly`/`Vec`) — is a vector-lift + carrier-instantiation step, not a tie to an
existing definition; it is out of scope here.

## UC vacuity of the ML-DSA `*_uc_secure` conclusions

`SurfaceDeps.mldsa_hax_uc_secure` is `UCEmulates 0 …` proved by
`intro A; use A; exact le_of_eq (sdist_self _)` — simulator = adversary, ε = 0,
i.e. it is the trivial *(composition plumbing)* lift and says nothing
protocol-specific (per the project's standing note that crypto `*_uc_security`
are often `∃ ε, ε ≤ bound := ⟨_, le_refl⟩`). The ML-DSA bound lives in
`mldsa_eufcma_security` (Kiltz–Lyubashevsky–Schaffner) and is parametric over the
abstract `Dependencies`, never reaching down to `f_mod_q`. The tie in this file is
therefore meaningful **at the functional-correctness layer** — the emitted leaf
computes the FIPS reduce/caddq/montgomery/power2round/decompose function — and
that meaning is independent of whether the downstream UC conclusion is vacuous.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDepsTie

open CatCrypt.Crypto.SecureCompilation.ThirToComFront (inputValuation)
open CatCrypt.Crypto.SecureCompilation.CompileFromHax (compileFromHax)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaReduce32
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaPoly
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaMontgomery
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecompose
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDecomposeFull
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSecurityTie (tie_transfer)

/-! ## §1  The abstract per-coefficient reduce-dependency record

`MldsaReduceDeps` is the miniature `Dependencies` at the **per-coefficient
`BitVec 64`** representation — the layer the verified-compiled leaves actually
live at. A reduce-family correctness argument is parametric over a
`MldsaReduceDeps` and reasons only through the spec its fields satisfy. -/

/-- The abstract ML-DSA per-coefficient reduce-primitive dependency record. Each
    field is the signed-`int32` reduce body carried in `BitVec 64`. -/
structure MldsaReduceDeps where
  /-- Barrett `reduce32`: arbitrary `int32` → centered representative. -/
  reduce32 : BitVec 64 → BitVec 64
  /-- Conditional add of `q` (`caddq`): centered residue → canonical `[0,q)`. -/
  caddq : BitVec 64 → BitVec 64
  /-- Signed Montgomery reduce: `a → a·R⁻¹ mod q` (`R = 2³²`). -/
  montgomery : BitVec 64 → BitVec 64
  /-- `power2round` high part `a1 = (a + 2^{D-1}-1) >> D`. -/
  power2roundA1 : BitVec 64 → BitVec 64
  /-- `power2round` low part `a0 = a − (a1 << D)`. -/
  power2roundA0 : BitVec 64 → BitVec 64
  /-- `decompose` low part `a0` (with branchless boundary fix-up). -/
  decomposeA0 : BitVec 64 → BitVec 64

/-! ## §2  The spec instance (the FIPS-204 reference per-coefficient functions)

`mldsaReduceDepsSpec` fills each field with the explicit closed **emit form** the
corresponding leaf denotes to — the FIPS-204 reference per-coefficient body. These
are exactly the functions whose abstract reduce/canonical/congruence/reconstruction
identities are proved in the leaf modules (`mldsaReduce32Form_sub_eq_quotient`,
`mldsaCaddqFold_eq_centeredCanonical`, `mldsaMontgomery_montgomery_congruence`,
`power2roundReconstruct_eq`, `decomposeA0_signMask_select`). -/

/-- The abstract spec instance: each field is the FIPS-204 reference emit form the
    corresponding `compileFromHax` leaf is proved to denote to. -/
def mldsaReduceDepsSpec : MldsaReduceDeps where
  reduce32 := mldsaReduce32Form
  caddq := mldsaCaddqFold
  montgomery := mldsaMontgomeryForm
  power2roundA1 := power2roundA1Spec
  power2roundA0 := power2roundA0Spec
  decomposeA0 := mldsaDecomposeA0Form

/-! ## §3  The compiled functions (what the verified compiler emits)

For each reduce primitive we extract, from the committed `*_compiles` leaf, the
function the verified-compiled jasmin `Com` actually computes:
`fun a => (the compiled Com).denote (inputValuation 64 1 ![a])`. We destructure
each existential leaf — exactly as a downstream `SurfaceDeps` consumer would — to
name the compiled `Com` and carry its value-agreement clause. -/

/-- The compiled `reduce32` `Com` together with its emit-form value-agreement. -/
noncomputable def reduce32Compiled := mldsaReduce32_compiles.choose
theorem reduce32Compiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] mldsaReduce32Src = some reduce32Compiled ∧
    ∀ (a : BitVec 64),
      reduce32Compiled.denote (inputValuation 64 1 ![a]) = mldsaReduce32Form a :=
  mldsaReduce32_compiles.choose_spec

/-- The compiled `caddq` `Com` together with its mask-blend value-agreement. -/
noncomputable def caddqCompiled := mldsaCaddq_compiles.choose
theorem caddqCompiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] mldsaCaddqSrc = some caddqCompiled ∧
    ∀ (a : BitVec 64),
      caddqCompiled.denote (inputValuation 64 1 ![a]) = mldsaCaddqFold a :=
  mldsaCaddq_compiles.choose_spec

/-- The compiled signed-Montgomery `Com` together with its emit-form value-agreement. -/
noncomputable def montgomeryCompiled := mldsaMontgomery_compiles.choose
theorem montgomeryCompiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] mldsaMontgomerySrc = some montgomeryCompiled ∧
    ∀ (a : BitVec 64),
      montgomeryCompiled.denote (inputValuation 64 1 ![a]) = mldsaMontgomeryForm a :=
  mldsaMontgomery_compiles.choose_spec

/-- The compiled `power2round` high-part `Com` together with its value-agreement. -/
noncomputable def power2roundA1Compiled := power2roundA1_compiles.choose
theorem power2roundA1Compiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA1Src = some power2roundA1Compiled ∧
    ∀ (a : BitVec 64),
      power2roundA1Compiled.denote (inputValuation 64 1 ![a]) = power2roundA1Spec a :=
  power2roundA1_compiles.choose_spec

/-- The compiled `power2round` low-part `Com` together with its value-agreement. -/
noncomputable def power2roundA0Compiled := power2roundA0_compiles.choose
theorem power2roundA0Compiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] power2roundA0Src = some power2roundA0Compiled ∧
    ∀ (a : BitVec 64),
      power2roundA0Compiled.denote (inputValuation 64 1 ![a]) = power2roundA0Spec a :=
  power2roundA0_compiles.choose_spec

/-- The compiled `decompose` low-part `Com` together with its value-agreement. -/
noncomputable def decomposeA0Compiled := mldsaDecomposeA0_compiles.choose
theorem decomposeA0Compiled_spec :
    compileFromHax (w := 64) (nIn := 1) ["a"] mldsaDecomposeA0Src = some decomposeA0Compiled ∧
    ∀ (a : BitVec 64),
      decomposeA0Compiled.denote (inputValuation 64 1 ![a]) = mldsaDecomposeA0Form a :=
  mldsaDecomposeA0_compiles.choose_spec

/-- The function the verified-compiled `reduce32` jasmin `Com` computes. -/
noncomputable def compiledReduce32Fn : BitVec 64 → BitVec 64 :=
  fun a => reduce32Compiled.denote (inputValuation 64 1 ![a])

/-- The function the verified-compiled `caddq` jasmin `Com` computes. -/
noncomputable def compiledCaddqFn : BitVec 64 → BitVec 64 :=
  fun a => caddqCompiled.denote (inputValuation 64 1 ![a])

/-- The function the verified-compiled signed-Montgomery jasmin `Com` computes. -/
noncomputable def compiledMontgomeryFn : BitVec 64 → BitVec 64 :=
  fun a => montgomeryCompiled.denote (inputValuation 64 1 ![a])

/-- The function the verified-compiled `power2round` high-part jasmin `Com` computes. -/
noncomputable def compiledPower2roundA1Fn : BitVec 64 → BitVec 64 :=
  fun a => power2roundA1Compiled.denote (inputValuation 64 1 ![a])

/-- The function the verified-compiled `power2round` low-part jasmin `Com` computes. -/
noncomputable def compiledPower2roundA0Fn : BitVec 64 → BitVec 64 :=
  fun a => power2roundA0Compiled.denote (inputValuation 64 1 ![a])

/-- The function the verified-compiled `decompose` low-part jasmin `Com` computes. -/
noncomputable def compiledDecomposeA0Fn : BitVec 64 → BitVec 64 :=
  fun a => decomposeA0Compiled.denote (inputValuation 64 1 ![a])

/-! ## §4  The tie theorems: compiled function = FIPS reference emit form

Each tie theorem says the **function the verified-compiled jasmin `Com` computes
is the FIPS-204 reference emit form** the spec field carries. They are immediate
from the value-agreement clause of the committed `*_compiles` leaves. -/

/-- **Tie (`reduce32`).** Compiled function = `mldsaReduceDepsSpec.reduce32`. -/
theorem compiledReduce32Fn_eq : compiledReduce32Fn = mldsaReduceDepsSpec.reduce32 := by
  funext a; exact reduce32Compiled_spec.2 a

/-- **Tie (`caddq`).** Compiled function = `mldsaReduceDepsSpec.caddq`. -/
theorem compiledCaddqFn_eq : compiledCaddqFn = mldsaReduceDepsSpec.caddq := by
  funext a; exact caddqCompiled_spec.2 a

/-- **Tie (`montgomery`).** Compiled function = `mldsaReduceDepsSpec.montgomery`. -/
theorem compiledMontgomeryFn_eq : compiledMontgomeryFn = mldsaReduceDepsSpec.montgomery := by
  funext a; exact montgomeryCompiled_spec.2 a

/-- **Tie (`power2round` high).** Compiled function = `mldsaReduceDepsSpec.power2roundA1`. -/
theorem compiledPower2roundA1Fn_eq :
    compiledPower2roundA1Fn = mldsaReduceDepsSpec.power2roundA1 := by
  funext a; exact power2roundA1Compiled_spec.2 a

/-- **Tie (`power2round` low).** Compiled function = `mldsaReduceDepsSpec.power2roundA0`. -/
theorem compiledPower2roundA0Fn_eq :
    compiledPower2roundA0Fn = mldsaReduceDepsSpec.power2roundA0 := by
  funext a; exact power2roundA0Compiled_spec.2 a

/-- **Tie (`decompose` low).** Compiled function = `mldsaReduceDepsSpec.decomposeA0`. -/
theorem compiledDecomposeA0Fn_eq :
    compiledDecomposeA0Fn = mldsaReduceDepsSpec.decomposeA0 := by
  funext a; exact decomposeA0Compiled_spec.2 a

/-! ## §5  The realization instance and the realization theorem

`toMldsaReduceDeps` is the **`SurfaceDeps` shape**: the verified-compiled leaves
fill the abstract per-coefficient reduce-`Dependencies` fields.
`toMldsaReduceDeps_eq_spec` is the *realization theorem* — the compiled leaves
equal the FIPS reference spec the correctness layer reasons about. -/

/-- The realization instance: the abstract per-coefficient reduce record filled
    with the functions the **verified compiler emits** for each reduce primitive. -/
noncomputable def toMldsaReduceDeps : MldsaReduceDeps where
  reduce32 := compiledReduce32Fn
  caddq := compiledCaddqFn
  montgomery := compiledMontgomeryFn
  power2roundA1 := compiledPower2roundA1Fn
  power2roundA0 := compiledPower2roundA0Fn
  decomposeA0 := compiledDecomposeA0Fn

/-- **The realization theorem.** The compiled-leaf realization instance equals the
    FIPS-204 reference spec instance: the verified compiler's emitted ML-DSA reduce
    primitives compute exactly the per-coefficient functions the reference (and
    the leaf-module abstract ties `mldsaReduce32Form_sub_eq_quotient`,
    `mldsaCaddqFold_eq_centeredCanonical`, `mldsaMontgomery_montgomery_congruence`,
    `power2roundReconstruct_eq`, `decomposeA0_signMask_select`) reason about. Every
    field is closed by its §4 tie theorem, which is the value-agreement clause of
    the committed `*_compiles` leaf. -/
theorem toMldsaReduceDeps_eq_spec : toMldsaReduceDeps = mldsaReduceDepsSpec := by
  unfold toMldsaReduceDeps
  rw [compiledReduce32Fn_eq, compiledCaddqFn_eq, compiledMontgomeryFn_eq,
    compiledPower2roundA1Fn_eq, compiledPower2roundA0Fn_eq, compiledDecomposeA0Fn_eq]

/-! ## §6  Transfer: any property of the spec transfers to the compiled realization

Instantiates the generic, record-agnostic `tie_transfer` (from
`CompileFromHaxSecurityTie`) at `Deps := MldsaReduceDeps` with the ML-DSA
realization equality `toMldsaReduceDeps_eq_spec`: any property `P` proved of the
FIPS reference spec instance transfers verbatim to the verified-compiler-emitted
realization, with no new axioms (a single `▸`). -/

/-- **Compiled ML-DSA reduce primitives inherit any abstract spec property.** For
    every property `P` of `MldsaReduceDeps`, if `P` holds of the FIPS reference
    spec instance `mldsaReduceDepsSpec` then it holds of the verified-compiler-
    emitted realization `toMldsaReduceDeps`. The mechanized statement that the
    compile-from-hax reduce-leaf output plugs into the abstract per-coefficient
    reduce-`Dependencies` layer — with no new axioms. Instantiates the generic
    `tie_transfer` with `toMldsaReduceDeps_eq_spec`. -/
theorem appliesToCompiled (P : MldsaReduceDeps → Prop) (h : P mldsaReduceDepsSpec) :
    P toMldsaReduceDeps :=
  tie_transfer P toMldsaReduceDeps_eq_spec h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxMldsaDepsTie
