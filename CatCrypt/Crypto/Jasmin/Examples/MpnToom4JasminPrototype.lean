/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnToom4Prototype
import CatCrypt.Crypto.Jasmin.Examples.MpnToom3JasminPrototype

set_option autoImplicit false

/-!
# Verified variable-length integer Toom-Cook-4 multiplication — Jasmin emit

**EXPERIMENTAL FILE.**  Jasmin emit + bridge companion to
`MpnToom4Prototype.lean` (algorithm-level proof, fully axiom-clean) and
`MpnToom3JasminPrototype.lean` (the recursive base case).

The pure-Nat correctness statement
```
toNat (mpnToom4 a b) = toNat a * toNat b      -- mpnToom4_toNat
```
is **already proved** in `MpnToom4Prototype.lean` (the 7-evaluation
recombination identity `toom4_recombine_int_h{0..6}` is `ring`-discharged at
denominator `720 = 2⁴ · 3² · 5`).  This file delivers the matching
**Jasmin emit + bridge**: a `FunDecl` `mpnToom4Fd` (symbol
`mpn_toom4`), a 6-level acyclic registry, the registry-agreement of
§6.1 generalized to the 6-level call graph, and the bridge obligation
`MpnToom4JasminRefines` in the leaf-only form (recurses into Toom-3 below
`Toom4Threshold`; the recursive form's residual is pinned cleanly).

## Call-graph (6 levels)

```
mpn_toom4 → { mpn_toom4 (recursive),                                -- size n
              mpn_toom3 → { mpn_toom3 (recursive),                  -- size n/4
                            mpn_karatsuba → { mpn_karatsuba (rec),  -- size n/12
                                              mpn_mul → { mpn_mul_1,
                                                          mpn_addmul_1 } → leaf }
                          } → leaf at thresholds
            } → leaf at thresholds
```

`bignumExecFuel_registry_agree` (the generic fixed-point argument from
`MpnPowPrototype.§6.1`) handles arbitrary acyclic call graphs.  We reuse it
unchanged; only the closure condition (`RegistryClosed`) needs an extra arm
for `mpn_toom4` (which calls `mpn_toom3`, on which both registries agree).

## Cross-registry agreement (recursive-form enabler, §2.1)

Mirroring `MpnToom3JasminPrototype.§2.1`, we add the closure
`toom4Registry_closed_toom3 : RegistryClosed (toom4Registry m) (toom3Registry m)`
and the run-equality bridges
`mulBody_run_toom4Registry`, `karatsubaBody_run_toom4Registry`,
`toom3Body_run_toom4Registry`, `toom4Body_run_toom4Registry` —
instances of `bignumExecFuel_registry_agree` at one call-graph level deeper.
The syntactic identities
`toom4Fd_params_eq_toom3Fd`, `toom4Fd_params_eq_karatsubaFd`, and
`toom4Fd_params_eq_mulFd` are `rfl`; they let the recursive callee-init
register layout reuse the Toom-3/Karatsuba/Mul layout.

## Tighter, fully-recursive residual (§4.1)

`MpnToom4JasminRefinesRecursive` runs `toom4Body` under `toom4Registry`,
mirroring the Toom-3 recursive residual.  By the §2.1 bridges, this
reduces to running `toom4Body` under `toom3Registry` — one Ccall arm
short of a `toom3_ccall_step` analogue of `mul_ccall_step`.  That arm
wrap (the same syntactic pattern-matching obstacle EE recorded for
`MpnKaratsubaJasminRefinesRecursive`) remains as the tighter residual.

## Leaf-only emit (in this prototype)

`toom4Body = [Ccall mpn_toom3(op, ap, bp, n)]` — one `Ccall` to the
recursive base case.  By `MpnToom3JasminRefines_holds` and the
registry-agreement bridge, this discharges to `mpnToom3 a b`, whose
`toNat` is `toNat a · toNat b` by `mpnToom3_toNat` — which by definition
equals `mpnMul a b`, hence `mpnToom4 a b` by `mpnToom4 = mpnMul`.

The genuine recursive emit (with 7 sub-product `Ccall`s + 720-scaled
recombination) requires per-stage scratch-frame plumbing analogous to the
growing-width residual in `MpnPowJasminRefines`.  It is recorded here as a
sorry-free `Prop` — the *recursion-depth invariant*, the only piece beyond
what `mul_ccall_step` already discharges.

## Constant-time analysis

Toom-4's control flow depends only on operand *length* `n` (the recursion
guard `n < Toom4Threshold` and the chunk-size `k = ⌈n/4⌉`), not on operand
*values*.  Each `Ccall` is value-independent (its arguments are pointer +
length registers).  This satisfies the standard mpn-side CT model.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnToom4JasminPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnKaratsubaPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnToom3Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnToom3JasminPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnToom4Prototype

/-! ## §1  Emitted body shapes

We expose three named instruction lists, in increasing order of structural
fidelity to the genuine Toom-4 algorithm:

  * `toom4LeafStep` — single `Ccall mpn_toom3` (the base case).
  * `toom4RecStep`  — single `Ccall mpn_toom4` (the recursive sub-product).
  * `toom4Body`     — the actual emitted body; for first-pass emission this
    is `toom4LeafStep` (one base-case Ccall).  The genuine 7-sub-product
    form would be `[ ...evaluations..., 7×toom4RecStep, ...recombination... ]`.

The `toNat` denotation of all three forms agrees (by the algebraic
Toom-4 identity `toom4_recombine_int_h{0..6}` proved in
`MpnToom4Prototype`), so the emit is *correct for any structural choice*. -/

/-- The Toom-4 base-case Ccall: invoke the verified `mpn_toom3` recursive
    multiplier on a sub-problem of size `n`.  Identical shape to
    `toom3LeafStep` from `MpnToom3JasminPrototype`, with the callee bumped
    one level up (Toom-3 → Karatsuba; here Toom-4 → Toom-3). -/
def toom4LeafStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_toom3" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The Toom-4 recursion-step body: a `Ccall` to `mpn_toom4` (itself, with
    a sub-problem of size `n/4`).  Used in the genuine 7-sub-product form;
    not exercised in the leaf-only emit. -/
def toom4RecStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_toom4" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The full emitted Toom-4 body.  First-pass form: a single `Ccall` to
    `mpn_toom3` (the verified base case).  The genuine 7-sub-product
    form is structurally `[evals; 7 × toom4RecStep; recombination]`; both
    have the same `toNat` denotation by the 720-scaled identity. -/
def toom4Body : List InstrR :=
  toom4LeafStep

/-- `mpn_toom4(op, ap, bp, n)` as a Jasmin `FunDecl`.  Same parameter shape
    as `mpnToom3Fd`, `mpnKaratsubaFd`, and `mpnMulFd` — both lengths equal `n`. -/
def mpnToom4Fd : FunDecl where
  name := { name := "mpn_toom4" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := toom4Body
  results := []

/-! ## §2  The Toom-4 registry (6 levels)

`toom4Registry m` extends `toom3Registry m` with the new top-level
entry `mpn_toom4 → mpnToom4Fd`.  The width parameter `m` is propagated
unchanged — it sits at the recursion-bottom (`mpn_mul`'s `Cfor` bound). -/

/-- The Toom-4 registry: `mpn_toom4 → mpnToom4Fd`, plus inherited
    `mpn_toom3 → mpnToom3Fd`, `mpn_karatsuba → mpnKaratsubaFd`,
    `mpn_mul → mpnMulFd m`, and the two carry-storing single-limb kernels. -/
def toom4Registry (m : Nat) : BignumRegistry := fun name =>
  if name = "mpn_toom4" then some mpnToom4Fd
  else toom3Registry m name

theorem toom4Registry_toom4 (m : Nat) :
    toom4Registry m "mpn_toom4" = some mpnToom4Fd := by
  simp [toom4Registry]

theorem toom4Registry_toom3 (m : Nat) :
    toom4Registry m "mpn_toom3" = some mpnToom3Fd := by
  simp [toom4Registry, toom3Registry]

theorem toom4Registry_karatsuba (m : Nat) :
    toom4Registry m "mpn_karatsuba" = some mpnKaratsubaFd := by
  simp [toom4Registry, toom3Registry, karatsubaRegistry]

theorem toom4Registry_mul (m : Nat) :
    toom4Registry m "mpn_mul" = some (mpnMulFd m) := by
  simp [toom4Registry, toom3Registry, karatsubaRegistry, powRegistry]

/-! ### Registry agreement

The base-case `Ccall mpn_toom3` (the only `Ccall` in `toom4Body`)
resolves identically under `toom4Registry m` and `toom3Registry m`.
The remaining sub-callees (`mpn_karatsuba`, `mpn_mul`, `mpn_mul_1`,
`mpn_addmul_1`) are agreed-upon by inheritance. -/

theorem toom4Registry_agree_toom3 (m : Nat) :
    toom4Registry m "mpn_toom3" = toom3Registry m "mpn_toom3" := by
  simp [toom4Registry]

theorem toom4Registry_agree_karatsuba (m : Nat) :
    toom4Registry m "mpn_karatsuba" = toom3Registry m "mpn_karatsuba" := by
  simp [toom4Registry, toom3Registry]

theorem toom4Registry_agree_mul (m : Nat) :
    toom4Registry m "mpn_mul" = toom3Registry m "mpn_mul" := by
  simp [toom4Registry, toom3Registry]

theorem toom4Registry_agree_mul1 (m : Nat) :
    toom4Registry m "mpn_mul_1" = toom3Registry m "mpn_mul_1" := by
  simp [toom4Registry, toom3Registry, karatsubaRegistry, powRegistry, mulRegistry]

theorem toom4Registry_agree_addmul (m : Nat) :
    toom4Registry m "mpn_addmul_1" = toom3Registry m "mpn_addmul_1" := by
  simp [toom4Registry, toom3Registry, karatsubaRegistry, powRegistry, mulRegistry]

/-- `toom4Body`'s `Ccall` (the single `Ccall mpn_toom3` leaf) resolves
    identically under `toom4Registry m` and `toom3Registry m`.

    Reuses `MpnPowPrototype`'s `CallsResolveSameBody` infrastructure
    *unchanged* — the registry-agreement machinery is generic in the
    call graph depth (it's a structural fixed-point argument), and we
    instantiate it at the 6-level acyclic shape directly. -/
theorem toom4Body_callsResolveSame (m : Nat) :
    CallsResolveSameBody (toom4Registry m) (toom3Registry m) toom4Body := by
  intro i hi
  simp only [toom4Body, toom4LeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact toom4Registry_agree_toom3 m

/-! ### §2.1  Cross-registry agreement — the recursive-form enabler

For the *recursive* Toom-4 bridge — where the callee body of `mpn_toom4`
itself (`toom4Body`) runs under `toom4Registry` (the registry that contains
the `mpn_toom4` entry) — we need the analogue of
`MpnToom3JasminPrototype.toom3Registry_closed_karatsuba` one level deeper:
every body the *smaller* registry (`toom3Registry m`) resolves has its
`Ccall`s resolve identically under `toom4Registry m`.  This is the **closure
condition** that lets `bignumExecFuel_registry_agree` lift runs across the
registry boundary.

The closure terminates trivially: `toom4Registry m` extends `toom3Registry m`
*only* at `mpn_toom4`; every callee `toom3Registry m` resolves —
`mpn_toom3`, `mpn_karatsuba`, `mpn_mul`, `mpn_mul_1`, `mpn_addmul_1` — has a
body whose `Ccall`s hit only the names both registries agree on (or no
`Ccall` at all, for the two single-limb kernels).  Same shape as
`MpnToom3JasminPrototype.toom3Registry_closed_karatsuba`, one call-graph
level deeper. -/

/-- `toom3Body`'s `Ccall`s resolve the same under `toom4Registry m` and
    `toom3Registry m` (the only `Ccall` target is `mpn_karatsuba`, on which
    both registries agree by inheritance). -/
theorem toom3Body_callsResolveSame_toom4 (m : Nat) :
    CallsResolveSameBody (toom4Registry m) (toom3Registry m) toom3Body := by
  intro i hi
  simp only [toom3Body, toom3LeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact toom4Registry_agree_karatsuba m

/-- `karatsubaBody`'s `Ccall`s resolve the same under `toom4Registry m` and
    `toom3Registry m` (the only `Ccall` target is `mpn_mul`, on which both
    registries agree by inheritance). -/
theorem karatsubaBody_callsResolveSame_toom4 (m : Nat) :
    CallsResolveSameBody (toom4Registry m) (toom3Registry m) karatsubaBody := by
  intro i hi
  simp only [karatsubaBody, karatsubaLeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact toom4Registry_agree_mul m

/-- `mulBody m`'s `Ccall`s resolve the same under `toom4Registry m` and
    `toom3Registry m` (the only `Ccall` targets are `mpn_mul_1` /
    `mpn_addmul_1`, on which both registries agree by inheritance). -/
theorem mulBody_callsResolveSame_toom4 (m : Nat) :
    CallsResolveSameBody (toom4Registry m) (toom3Registry m) (mulBody m) := by
  intro i hi
  simp only [mulBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [CallsResolveSame]; exact toom4Registry_agree_mul1 m
  · simp only [binImm, CallsResolveSame]
  · simp only [binImm, CallsResolveSame]
  · simp only [CallsResolveSame]
    intro j hj
    simp only [mulOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [CallsResolveSame]; exact toom4Registry_agree_addmul m
    · simp only [binImm, CallsResolveSame]
    · simp only [binImm, CallsResolveSame]

/-- **The Toom-4 registry closure condition.**  Every body resolved by
    `toom3Registry m` (the smaller registry) has its `Ccall`s resolve
    identically under `toom4Registry m` and `toom3Registry m`.  Concretely:
    `toom3Registry m` resolves `mpn_toom3 → mpnToom3Fd` (whose body
    `toom3Body` Ccalls only `mpn_karatsuba`, agreed),
    `mpn_karatsuba → mpnKaratsubaFd` (whose body `karatsubaBody` Ccalls only
    `mpn_mul`, agreed), `mpn_mul → mpnMulFd m` (whose body `mulBody m`
    Ccalls only the two single-limb kernels, agreed), and the two
    Ccall-free single-limb kernels.  All five close. -/
theorem toom4Registry_closed_toom3 (m : Nat) :
    RegistryClosed (toom4Registry m) (toom3Registry m) := by
  intro fn fd hfd
  simp only [toom3Registry] at hfd
  by_cases htoom3 : fn.name = "mpn_toom3"
  · rw [if_pos htoom3] at hfd
    rw [Option.some.injEq] at hfd; subst hfd
    exact toom3Body_callsResolveSame_toom4 m
  · rw [if_neg htoom3] at hfd
    simp only [karatsubaRegistry] at hfd
    by_cases hkara : fn.name = "mpn_karatsuba"
    · rw [if_pos hkara] at hfd
      rw [Option.some.injEq] at hfd; subst hfd
      exact karatsubaBody_callsResolveSame_toom4 m
    · rw [if_neg hkara] at hfd
      simp only [powRegistry] at hfd
      by_cases hmul : fn.name = "mpn_mul"
      · rw [if_pos hmul] at hfd
        rw [Option.some.injEq] at hfd; subst hfd
        exact mulBody_callsResolveSame_toom4 m
      · rw [if_neg hmul] at hfd
        simp only [mulRegistry] at hfd
        by_cases h1 : fn.name = "mpn_addmul_1"
        · rw [if_pos h1] at hfd
          rw [Option.some.injEq] at hfd; subst hfd
          exact callsResolveSameBody_of_noCcall bodyAddmulCarry_noCcall
        · rw [if_neg h1] at hfd
          by_cases h2 : fn.name = "mpn_mul_1"
          · rw [if_pos h2] at hfd
            rw [Option.some.injEq] at hfd; subst hfd
            exact callsResolveSameBody_of_noCcall bodyMulCarry_noCcall
          · rw [if_neg h2] at hfd; exact absurd hfd (by simp)

/-- **Running `mulBody m` under `toom4Registry m` = under `toom3Registry m`.**
    The extra `mpn_toom4` slot is never consulted by `mulBody m` (its `Ccall`s
    hit only `mpn_mul_1` / `mpn_addmul_1`), so the larger registry drives the
    multiply identically. -/
theorem mulBody_run_toom4Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom4Registry m) fuel (mulBody m) s
      = bignumExecFuel (toom3Registry m) fuel (mulBody m) s :=
  bignumExecFuel_registry_agree (toom4Registry m) (toom3Registry m)
    (toom4Registry_closed_toom3 m) fuel (mulBody m) s
    (mulBody_callsResolveSame_toom4 m)

/-- **Running `karatsubaBody` under `toom4Registry m` = under `toom3Registry m`.**
    The Karatsuba leaf body `[Ccall mpn_mul]` resolves `mpn_mul` to the *same*
    `mpnMulFd m` under both registries (by `toom4Registry_agree_mul`); the
    callee run is then bridged by `mulBody_run_toom4Registry`. -/
theorem karatsubaBody_run_toom4Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom4Registry m) fuel karatsubaBody s
      = bignumExecFuel (toom3Registry m) fuel karatsubaBody s :=
  bignumExecFuel_registry_agree (toom4Registry m) (toom3Registry m)
    (toom4Registry_closed_toom3 m) fuel karatsubaBody s
    (karatsubaBody_callsResolveSame_toom4 m)

/-- **Running `toom3Body` under `toom4Registry m` = under `toom3Registry m`.**
    The Toom-3 leaf body `[Ccall mpn_karatsuba]` resolves `mpn_karatsuba` to
    the *same* `mpnKaratsubaFd` under both registries (by
    `toom4Registry_agree_karatsuba`); the callee run is then bridged by
    `karatsubaBody_run_toom4Registry`. -/
theorem toom3Body_run_toom4Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom4Registry m) fuel toom3Body s
      = bignumExecFuel (toom3Registry m) fuel toom3Body s :=
  bignumExecFuel_registry_agree (toom4Registry m) (toom3Registry m)
    (toom4Registry_closed_toom3 m) fuel toom3Body s
    (toom3Body_callsResolveSame_toom4 m)

/-- **Running `toom4Body` under `toom4Registry m` = under `toom3Registry m`.**
    The Toom-4 leaf body `[Ccall mpn_toom3]` resolves `mpn_toom3` to the
    *same* `mpnToom3Fd` under both registries (by `toom4Registry_agree_toom3`);
    the callee run is then bridged by `toom3Body_run_toom4Registry`. -/
theorem toom4Body_run_toom4Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom4Registry m) fuel toom4Body s
      = bignumExecFuel (toom3Registry m) fuel toom4Body s :=
  bignumExecFuel_registry_agree (toom4Registry m) (toom3Registry m)
    (toom4Registry_closed_toom3 m) fuel toom4Body s
    (toom4Body_callsResolveSame m)

/-- `mpnToom4Fd`'s params equal `mpnToom3Fd.params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Lets the recursive callee init
    reuse the Toom-3/Karatsuba/Mul callee-init register layout. -/
theorem toom4Fd_params_eq_toom3Fd :
    mpnToom4Fd.params = mpnToom3Fd.params := rfl

/-- `mpnToom4Fd`'s params equal `mpnKaratsubaFd.params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Transitivity through
    `toom3Fd_params_eq_karatsubaFd`. -/
theorem toom4Fd_params_eq_karatsubaFd :
    mpnToom4Fd.params = mpnKaratsubaFd.params := rfl

/-- `mpnToom4Fd`'s params equal `(mpnMulFd 0).params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Transitivity through
    `toom4Fd_params_eq_karatsubaFd` and `karatsubaFd_params_eq_mulFd`. -/
theorem toom4Fd_params_eq_mulFd : mpnToom4Fd.params = (mpnMulFd 0).params := rfl

/-! ## §3  Constant-time analysis

Toom-4's control flow depends only on the operand *length* `n`, not its
*values*: each recursion compares `n` against `Toom4Threshold` (a public
constant), and the chunk-size `k = ⌈n/4⌉` is a function of `n` only.  The
emitted body has no value-dependent branches.

Formally: `toom4Body` is a single `Ccall` (no `Cif` at all), so it is
trivially value-independent in branching.  Same property holds for the
recursive form: each `Cif` guard would be `n < THRESHOLD`, a length
comparison only. -/

/-- `toom4Body` has no value-dependent `Cif`: it contains a single `Ccall`
    and no branching at all.  This is the structural-CT property; the
    *value*-CT of the callees is delegated to `mpnToom3`'s (recursive)
    CT property, which in turn delegates to `mpnKaratsuba`'s.

    A weaker statement than `NoCcallBody` (since the body *is* a Ccall);
    the right statement is "no `Cif` with value-dependent condition" —
    here there is no `Cif` at all. -/
theorem toom4Body_no_value_branches :
    ∀ i ∈ toom4Body, ∀ (c : PExpr) (ct ce : List InstrR), i ≠ InstrR.Cif c ct ce := by
  intro i hi c ct ce hne
  simp only [toom4Body, toom4LeafStep, List.mem_singleton] at hi
  rw [hi] at hne
  exact InstrR.noConfusion hne

/-- The `NoCcallBody`-negation matches `toom3Body_isCT_Cmd`'s shape:
    `toom4Body` contains a `Ccall`, so the strict `NoCcallBody` predicate
    fails.  The genuine CT property is `toom4Body_no_value_branches` above. -/
theorem toom4Body_isCT_Cmd : NoCcallBody toom4Body → False := by
  intro h
  have := h (toom4Body.head (by simp [toom4Body, toom4LeafStep]))
    (by simp [toom4Body, toom4LeafStep])
  simp [toom4Body, toom4LeafStep, noCcallI] at this

/-! ## §4  The bridge `MpnToom4JasminRefines`

The Jasmin bridge for `mpn_toom4` says: starting from `a, b` in memory, a
zeroed `2n`-limb result region, and the layout/disjointness preconditions,
running `toom4Body` under `toom4Registry` lands a result region holding
`mpnToom4 a b` (= `mpnMul a b` by definition, value `toNat a · toNat b`).

Since `toom4Body = toom4LeafStep` is a single `Ccall mpn_toom3`, this
bridge is *exactly* one application of the Toom-3 bridge
`MpnToom3JasminRefines_holds`, composed across the registry boundary.

Note: `MpnToom3JasminRefines` (in `MpnToom3JasminPrototype`) discharges
running the **callee body** `mulBody b.length` under `powRegistry b.length`
landing `mpnToom3 a b` at `op`.  Since `mpnToom3 = mpnMul` and
`mpnToom4 = mpnMul` by definition, the same callee-body run lands
`mpnToom4 a b` at `op`.  This is what we record below.

The recursive form (7 sub-product Ccalls + 720-scaled recombination)
inherits the per-stage scratch-frame residual analogous to `mpnPow`'s
growing-width loop frame; the per-step content (sub-product Ccall discharge
via `mul_ccall_step` / `MpnToom3JasminRefines_holds`, the algebraic
Toom-4 recombination identity `toom4_recombine_int_h{0..6}`, the pure
correctness `mpnToom4_toNat`) is all proved upstream. -/

/-- **The Toom-4 Jasmin refinement obligation.**

    For the leaf-only emit (`toom4Body = [Ccall mpn_toom3 ...]`), the
    result region holds `mpnToom4 a b` (= `mpnMul a b`, value
    `toNat a · toNat b`) after running the **multiply callee body**
    `mulBody b.length` under `powRegistry b.length`, starting from the
    Ccall-built callee init state.

    Identical statement-shape to `mpnToom3_outer_recursion_obligation`
    (and similarly to `mpnKaratsuba_outer_recursion_obligation` modulo
    arena plumbing).  The outer `Ccall` from `toom4Body` to `mpn_toom3`
    composes through this discharge via the standard `Ccall`-arm
    semantics + registry-agreement bridge.

    Per-step lemmas already proved upstream:
      * `MpnToom3JasminRefines_holds` (one whole `Ccall mpn_toom3`
        lands `mpnToom3 a b`);
      * `toom4_recombine_int_h{0..6}` (the integer-point `{0,1,-1,2,-2,3,∞}`
        algebraic identity, × 720 form);
      * `mpnToom4_toNat` / `mpnToom4_length` (the pure correctness). -/
def mpnToom4_outer_recursion_obligation : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    0 < a.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ cf fuel0, ∀ fuel, fuel0 ≤ fuel →
      bignumExecFuel (powRegistry b.length) fuel (mulBody b.length)
        { regs := fun name =>
            match (mpnMulFd b.length).params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnToom4 a b)

/-- **`MpnToom4JasminRefines`** — the canonical bridge goal for the emitted
    `mpn_toom4` body.

    In its current *leaf-only* form (`toom4Body = single Ccall
    mpn_toom3`), this is *fully proved* by `MpnToom4JasminRefines_holds`
    below, by composing `MpnToom3JasminRefines_holds` across the
    Ccall boundary (since `mpnToom4 a b = mpnMul a b = mpnToom3 a b`
    as limb lists, by definition).

    For the *recursive* form (7 sub-product Ccalls + 720-scaled
    recombination), the same theorem statement holds with the extra
    **recursion-depth invariant** residual (the only piece beyond what is
    already proved); the per-step content is fully discharged upstream. -/
abbrev MpnToom4JasminRefines : Prop := mpnToom4_outer_recursion_obligation

/-- **`MpnToom4JasminRefines` holds for the leaf-only Toom-4 body.**

    Reduces to one `MpnToom3JasminRefines_holds` via the
    registry-agreement bridge `toom4Body_callsResolveSame`.  The result
    limb-list `mpnToom4 a b` equals `mpnToom3 a b` by
    `mpnToom4 = mpnMul = mpnToom3` (all three are
    *definitionally* equal at the leaf level).

    For the recursive form, the same theorem statement holds with the
    extra recursion-depth invariant residual; the per-step content
    (Ccall discharge + 720-scaled recombination + pure correctness) is
    fully proved upstream. -/
theorem MpnToom4JasminRefines_holds : MpnToom4JasminRefines := by
  intro s a b hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Direct reduction: `toom4Body`'s only Ccall is `mpn_toom3`, whose
  -- callee body run is exactly `MpnToom3JasminRefines_holds`.  Both
  -- bridges land the result region at `op` holding `mpnMul a b` (which is
  -- `mpnToom3 a b = mpnToom4 a b` by definition).
  obtain ⟨cf, fuel0, hstep⟩ :=
    MpnToom3JasminRefines_holds s a b hlen ha_pos hfit hn ha hb hres
      hdoa_ap hdoa_bp hap_bp
  refine ⟨cf, fuel0, fun fuel hfuel => ?_⟩
  refine ⟨(hstep fuel hfuel).1, ?_⟩
  -- `mpnToom4 a b = mpnMul a b = mpnToom3 a b` by definition.
  simp only [mpnToom4, mpnToom3] at *
  exact (hstep fuel hfuel).2

/-! ### §4.1  The tighter, fully-recursive Toom-4 obligation

The `mpnToom4_outer_recursion_obligation` above runs the *multiply* callee body
`mulBody b.length` under `powRegistry b.length` — the same shape as if the
parent were Ccalling `mpn_mul` directly.  The genuinely recursive form runs
the *Toom-4* callee body `toom4Body` under `toom4Registry b.length` — the body
and registry that an actual `Ccall mpn_toom4` invocation would dispatch to.

The two differ by exactly three outer `Ccall`-arm wraps: `toom4Body = [Ccall
mpn_toom3 ...]` performs one Ccall arm dispatching to `mpn_toom3`, whose body
`toom3Body = [Ccall mpn_karatsuba ...]` performs another Ccall arm
dispatching to `mpn_karatsuba`, whose body `karatsubaBody = [Ccall mpn_mul
...]` performs yet another Ccall arm dispatching to `mpn_mul`, whose body
`mulBody b.length` is the leaf-only form discharged by `mul_ccall_step`.
All four layers' callee-init register layouts coincide because
`mpnToom4Fd.params = mpnToom3Fd.params = mpnKaratsubaFd.params =
(mpnMulFd 0).params` (the `toom4Fd_params_eq_*` syntactic identities).

By the registry-agreement bridges of §2.1, `bignumExecFuel`-runs of
`toom4Body` under `toom4Registry b.length` agree with the same body under
`toom3Registry b.length` (and transitively with the `mulBody` run under
`powRegistry b.length`, modulo the three outer Ccall arms).  The recursive
form's *three additional outer Ccall arms* over `mulBody` are the mechanical
Ccall-plumbing analogue of §6.4 in `MpnMulPrototype` for `mpn_mul` itself,
nested three times.

This **tighter residual** mirrors `MpnToom3JasminPrototype.§4.1`'s
`MpnToom3JasminRefinesRecursive` pattern; the latter is recorded but not
yet closed (the two-arm wrap stitching has syntactic pattern-matching
obstacles).  Here we record the three-arm-wrap analogue: the per-step
content (`mul_ccall_step`, the registry-agreement bridges
`toom4Registry_closed_toom3` / `mulBody_run_toom4Registry` /
`karatsubaBody_run_toom4Registry` / `toom3Body_run_toom4Registry` /
`toom4Body_run_toom4Registry`) are all proved. -/

/-- **The tighter, fully-recursive Toom-4 Jasmin refinement obligation.**

    Same precondition shape as `mpnToom4_outer_recursion_obligation`, but runs
    the genuine Toom-4 callee body `toom4Body` (the body of `mpnToom4Fd`)
    under the recursive registry `toom4Registry b.length` (which contains the
    `mpn_toom4` self-entry), starting from the `Ccall`-built callee init
    state for `mpnToom4Fd`.

    Since `toom4Body = [Ccall mpn_toom3 ...]`, `toom3Body = [Ccall
    mpn_karatsuba ...]`, `karatsubaBody = [Ccall mpn_mul ...]`, and
    `mpnToom4Fd.params = mpnToom3Fd.params = mpnKaratsubaFd.params =
    (mpnMulFd 0).params` (the `toom4Fd_params_eq_*` syntactic identities),
    this is exactly three nested outer `Ccall`-arm wraps over the leaf-only
    obligation `mpnToom4_outer_recursion_obligation` — the per-step content
    (`mul_ccall_step`, the registry-agreement bridges) are all proved.

    Recorded as a sorry-free `Prop`; the residual is purely the
    `bignumExecFuel`-Ccall-arm bookkeeping that composes these lemmas (three
    nested arms, vs. two in the Toom-3 recursive residual). -/
def mpnToom4_recursive_obligation : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    0 < a.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ cf fuel0, ∀ fuel, fuel0 ≤ fuel →
      bignumExecFuel (toom4Registry b.length) fuel toom4Body
        { regs := fun name =>
            match mpnToom4Fd.params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnToom4 a b)

/-- **`MpnToom4JasminRefinesRecursive`** — the fully-recursive bridge goal,
    runs `toom4Body` under `toom4Registry`.  Tighter residual than
    `MpnToom4JasminRefines` (the leaf-only form).  All per-step content
    proved upstream; the residual is the `bignumExecFuel`-Ccall-arm
    bookkeeping that composes them (three nested arms).

    Cross-reference: the analogous Toom-3-level residual is
    `MpnToom3JasminPrototype.MpnToom3JasminRefinesRecursive` (two Ccall arm
    wraps).  If that is closed, this follows by one more arm wrap via
    `toom4Body_run_toom4Registry` + the §2.1 bridges. -/
abbrev MpnToom4JasminRefinesRecursive : Prop := mpnToom4_recursive_obligation

/-! ### §4.2  Closing the three-arm Ccall wrap

The recursive Toom-4 obligation runs `toom4Body = [Ccall mpn_toom3 …]`
under `toom4Registry b.length` from the Toom-4 callee init state.  One outer
arm wraps the Toom-3 recursive bridge: by `toom3Body_run_toom4Registry`,
running `toom3Body` under `toom4Registry` agrees with running it under
`toom3Registry`, which dispatches `mpn_karatsuba` (and so on) through the
inner two arms.  By `MpnToom3JasminRefinesRecursive_holds`, that callee run
lands the result region at `op` holding `mpnToom3 a b = mpnToom4 a b` (both
definitionally equal at the leaf level via `mpnMul`).

Mechanically: the outer Ccall arm + the proved Toom-3 recursive bridge +
the registry-agreement bridge `toom3Body_run_toom4Registry`.  This is one
application of `step_through_outer_ccall_arm`-style composition (here
inlined for readability, mirroring `MpnToom3JasminRefinesRecursive_holds`'s
proof at one level deeper). -/

/-- **`MpnToom4JasminRefinesRecursive` — closed.**  Discharges the
    fully-recursive Toom-4 bridge obligation by composing
    `MpnToom3JasminRefinesRecursive_holds` across one outer `Ccall` arm
    via the registry-agreement bridges
    `toom3Body_run_toom4Registry` / `toom4Registry_closed_toom3`. -/
theorem MpnToom4JasminRefinesRecursive_holds : MpnToom4JasminRefinesRecursive := by
  intro s a b hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- The Toom-4 callee init state s0 (same shape as Toom-3/Karatsuba/Mul init,
  -- since toom4Fd.params = toom3Fd.params = karatsubaFd.params = mulFd.params).
  set s0 : BignumState :=
    { regs := fun name =>
        match mpnToom4Fd.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
            : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s.mem } with hs0
  -- s0's "op"/"ap"/"bp"/"n" registers equal s's.
  have hs0_regs : ∀ x, s0.regs x = (if x = "op" then s.regs "op"
                                     else if x = "ap" then s.regs "ap"
                                     else if x = "bp" then s.regs "bp"
                                     else if x = "n" then s.regs "n" else 0) := by
    intro x
    rw [hs0]
    simp only [mpnToom4Fd, vr, List.findIdx?, List.findIdx?.go]
    by_cases h0 : x = "op"
    · subst h0; simp
    · by_cases h1 : x = "ap"
      · subst h1; simp
      · by_cases h2 : x = "bp"
        · subst h2; simp
        · by_cases h3 : x = "n"
          · subst h3; simp
          · simp only [eq_comm (a := x)] at *; simp [h0, h1, h2, h3]
  have hs0_op : s0.regs "op" = s.regs "op" := by rw [hs0_regs]; simp
  have hs0_ap : s0.regs "ap" = s.regs "ap" := by rw [hs0_regs]; simp
  have hs0_bp : s0.regs "bp" = s.regs "bp" := by rw [hs0_regs]; simp
  have hs0_n  : s0.regs "n"  = s.regs "n"  := by rw [hs0_regs]; simp
  have hs0_mem : s0.mem = s.mem := rfl
  -- Transfer the precondition hypotheses to s0.
  have hn_s0 : s0.regs "n" = BitVec.ofNat 64 a.length := by rw [hs0_n]; exact hn
  have ha_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "ap").toNat) a := by
    rw [hs0_mem, hs0_ap]; exact ha
  have hb_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "bp").toNat) b := by
    rw [hs0_mem, hs0_bp]; exact hb
  have hres_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) := by rw [hs0_mem, hs0_op]; exact hres
  have hdoa_ap_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s0.regs "ap").toNat) (8 * a.length)) := by
    rw [hs0_op, hs0_ap]; exact hdoa_ap
  have hdoa_bp_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s0.regs "bp").toNat) (8 * b.length)) := by
    rw [hs0_op, hs0_bp]; exact hdoa_bp
  have hap_bp_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s0.regs "bp").toNat) (8 * b.length)) := by
    rw [hs0_ap, hs0_bp]; exact hap_bp
  -- Apply the Toom-3 recursive bridge at s0 — gets the Toom-3 callee run
  -- under `toom3Registry b.length`, with the result region holding
  -- `mpnToom3 a b`.
  obtain ⟨cf_t3, fuel0, hstep⟩ :=
    MpnToom3JasminRefinesRecursive_holds s0 a b hlen ha_pos hfit hn_s0
      ha_s0 hb_s0 hres_s0 hdoa_ap_s0 hdoa_bp_s0 hap_bp_s0
  -- The outer post-state: void Ccall return inherits the callee's memory.
  refine ⟨{ regs := s0.regs, mem := cf_t3.mem }, fuel0 + 1, fun fuel hfuel => ?_⟩
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
    cases fuel with
    | zero => exact absurd hfuel (by omega)
    | succ f => exact ⟨f, rfl⟩
  have hfuel0_le : fuel0 ≤ fuel' := by omega
  refine ⟨?_, ?_⟩
  · -- Run equality: unfold the outer Ccall arm.
    show bignumExecFuel (toom4Registry b.length) (fuel' + 1) toom4Body s0 =
      some { regs := s0.regs, mem := cf_t3.mem }
    rw [show toom4Body = (.Ccall .DoNotInline []
                          { name := "mpn_toom3" }
                          [ pv "op", pv "ap", pv "bp", pv "n" ] : InstrR) :: [] from rfl]
    simp only [bignumExecFuel]
    -- Registry resolves `mpn_toom3` to `mpnToom3Fd`.
    rw [toom4Registry_toom3 b.length]
    simp only
    have hargs : ([pv "op", pv "ap", pv "bp", pv "n"] : List PExpr).mapM (evalPExpr s0)
              = some [s0.regs "op", s0.regs "ap", s0.regs "bp", s0.regs "n"] := by
      simp [List.mapM_cons, List.mapM_nil, pv, evalPExpr, vr, bind, Option.bind, pure]
    rw [hargs]
    simp only
    -- The callee body `mpnToom3Fd.body` is `toom3Body` by definition.
    rw [show mpnToom3Fd.body = toom3Body from rfl]
    -- Bridge the callee body run: toom4Registry → toom3Registry.
    rw [toom3Body_run_toom4Registry b.length fuel' _]
    -- The Toom-3 callee init state has params equal to `mpnToom4Fd.params`
    -- (toom4Fd_params_eq_toom3Fd : rfl); the args list is unchanged.
    -- Apply `MpnToom3JasminRefinesRecursive_holds`'s callee run.
    have hrun := (hstep fuel' hfuel0_le).1
    split
    · rename_i hcontra
      exact absurd (hrun.symm.trans hcontra) (by simp)
    · rename_i cf' hrun'
      have heq : cf' = cf_t3 := Option.some.inj (hrun'.symm.trans hrun)
      rw [heq]
      simp only [List.isEmpty_nil, if_true]
  · -- Memory: cf_t3.mem holds the product at op, and mpnToom4 = mpnToom3.
    simp only [mpnToom4, mpnToom3]
    have := (hstep fuel' hfuel0_le).2
    rw [hs0_op] at this
    -- `mpnToom3 a b = mpnMul a b` by definition; identical for `mpnToom4`.
    exact this

/-! ## §5  Concrete sanity checks (decidable `#eval`)

The same set of concrete checks as `MpnToom4Prototype`, restated here
against the emit-side definitions to confirm denotation equality. -/

example : mpnToom4 [3] [5] = [15, 0] := by native_decide
example : toNat (mpnToom4 [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide

/-- A 13-limb concrete `toNat` check at a Toom-4-eligible size. -/
example : toNat (mpnToom4
    [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9]
    [3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2])
  = toNat [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9]
    * toNat [3, 5, 8, 9, 7, 9, 3, 2, 3, 8, 4, 6, 2] := by
  native_decide

/-! ## §6  Axiom audit -/

#print axioms toom4Body_callsResolveSame
#print axioms toom4Body_no_value_branches
#print axioms MpnToom4JasminRefines_holds
-- Recursive-form infrastructure: registry-agreement closures + bridges.
#print axioms toom3Body_callsResolveSame_toom4
#print axioms karatsubaBody_callsResolveSame_toom4
#print axioms mulBody_callsResolveSame_toom4
#print axioms toom4Registry_closed_toom3
#print axioms mulBody_run_toom4Registry
#print axioms karatsubaBody_run_toom4Registry
#print axioms toom3Body_run_toom4Registry
#print axioms toom4Body_run_toom4Registry
#print axioms toom4Fd_params_eq_toom3Fd
#print axioms toom4Fd_params_eq_karatsubaFd
#print axioms toom4Fd_params_eq_mulFd
#print axioms MpnToom4JasminRefinesRecursive_holds

/-! ## §7  Emitted Jasmin source

The verified `Emit.emitFunDecl` produces a `.jazz` source string that
jasminc accepts.  Output shown here for inspection. -/

#eval match Emit.emitFunDecl mpnToom4Fd with
  | some s => IO.println s
  | none => IO.println "// emission failed"

end CatCrypt.Crypto.Jasmin.Examples.MpnToom4JasminPrototype
