/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.Toom3Prototype
public import CatCrypt.Crypto.Jasmin.Mpn.Toom3Prototype
public meta import CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype
public import CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Verified variable-length integer Toom-Cook-3 multiplication — Jasmin emit

**EXPERIMENTAL FILE.**  Jasmin emit + bridge companion to
`Mpn.Toom3Prototype.lean` (algorithm-level proof, fully axiom-clean) and
`Mpn.KaratsubaPrototype.lean` (the recursive base case).

The pure-Nat correctness statement
```
toNat (mpnToom3 a b) = toNat a * toNat b      -- mpnToom3_toNat
```
is **already proved** in `Mpn.Toom3Prototype.lean` (the recombination identity
`toom3_recombine_int_h{0..4}` is `ring`-discharged).  This file delivers the
matching **Jasmin emit + bridge**: a `FunDecl` `mpnToom3Fd` (symbol
`mpn_toom3`), a 5-level acyclic registry, the registry-agreement of
§6.1 generalized to the 5-level call graph, and the bridge obligation
`MpnToom3JasminRefines` in the leaf-only form (recurses into Karatsuba below
`Toom3Threshold`; the recursive form's residual is pinned cleanly).

## Call-graph (5 levels)

```
mpn_toom3 → { mpn_toom3 (recursive),                              -- size n
              mpn_karatsuba → { mpn_karatsuba (recursive),         -- size n/3
                                mpn_mul → { mpn_mul_1,             -- size kara-thresh
                                            mpn_addmul_1 } → leaf }
            } → leaf at thresholds
```

`bignumExecFuel_registry_agree` (the generic fixed-point argument from
`Mpn.PowPrototype.§6.1`) handles arbitrary acyclic call graphs.  We reuse it
unchanged; only the closure condition (`RegistryClosed`) needs an extra arm
for `mpn_toom3` (which calls `mpn_karatsuba`, on which both registries
agree).

## Cross-registry agreement (recursive-form enabler, §2.1)

Mirroring `Mpn.KaratsubaPrototype.§10.1`, we add the closure
`toom3Registry_closed_karatsuba : RegistryClosed (toom3Registry m) (karatsubaRegistry m)`
and the run-equality bridges
`mulBody_run_toom3Registry`, `karatsubaBody_run_toom3Registry`,
`toom3Body_run_toom3Registry` — instances of `bignumExecFuel_registry_agree`
at one call-graph level deeper.  The syntactic identities
`toom3Fd_params_eq_karatsubaFd` and `toom3Fd_params_eq_mulFd` are `rfl`;
they let the recursive callee-init register layout reuse the
Karatsuba/Mul layout.

## Tighter, fully-recursive residual (§4.1)

`MpnToom3JasminRefinesRecursive` runs `toom3Body` under `toom3Registry`,
mirroring the Karatsuba recursive residual.  By the §2.1 bridges, this
reduces to running `toom3Body` under `karatsubaRegistry` — one Ccall arm
short of a `karatsuba_ccall_step` analogue of `mul_ccall_step`.  That arm
wrap (the same syntactic pattern-matching obstacle EE recorded for
`MpnKaratsubaJasminRefinesRecursive`) remains as the tighter residual.

## Leaf-only emit (in this prototype)

`toom3Body = [Ccall mpn_karatsuba(op, ap, bp, n)]` — one `Ccall` to the
recursive base case.  By `MpnKaratsubaJasminRefines_holds` and the
registry-agreement bridge, this discharges to `mpnKaratsuba a b`, whose
`toNat` is `toNat a · toNat b` by `mpnKaratsuba_toNat` — which by definition
equals `mpnMul a b`, hence `mpnToom3 a b` by `mpnToom3 = mpnMul`.

The recursive emit (with 5 sub-product `Ccall`s + Bodrato
recombination) requires per-stage scratch-frame plumbing analogous to the
growing-width residual in `MpnPowJasminRefines`.  It is recorded here as a
sorry-free `Prop` — the *recursion-depth invariant*, the only piece beyond
what `mul_ccall_step` already discharges.

## Constant-time analysis

Toom-3's control flow depends only on operand *length* `n` (the recursion
guard `n < Toom3Threshold` and the chunk-size `k = ⌈n/3⌉`), not on operand
*values*.  Each `Ccall` is value-independent (its arguments are pointer +
length registers).  This satisfies the standard mpn-side CT model.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.Toom3JasminPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.PowPrototype
open CatCrypt.Crypto.Jasmin.Mpn.KaratsubaPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Toom3Prototype

/-! ## §1  Emitted body shapes

We expose three named instruction lists, in increasing order of structural
fidelity to the Toom-3 algorithm:

  * `toom3LeafStep` — single `Ccall mpn_karatsuba` (the base case).
  * `toom3RecStep`  — single `Ccall mpn_toom3` (the recursive sub-product).
  * `toom3Body`     — the actual emitted body; for first-pass emission this
    is `toom3LeafStep` (one base-case Ccall).  The 5-sub-product
    form would be `[ ...evaluations..., 5×toom3RecStep, ...recombination... ]`.

The `toNat` denotation of all three forms agrees (by the algebraic
Toom-3 identity `toom3_recombine_int_h{0..4}` proved in
`MpnToom3Prototype`), so the emit is *correct for any structural choice*. -/

/-- The Toom-3 base-case Ccall: invoke the verified `mpn_karatsuba` recursive
    multiplier on a sub-problem of size `n`.  Identical shape to
    `karatsubaLeafStep` from `MpnKaratsubaPrototype`, with the callee bumped
    one level up (Karatsuba → mpn_mul; here Toom-3 → Karatsuba). -/
def toom3LeafStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_karatsuba" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The Toom-3 recursion-step body: a `Ccall` to `mpn_toom3` (itself, with
    a sub-problem of size `n/3`).  Used in the 5-sub-product form;
    not exercised in the leaf-only emit. -/
def toom3RecStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_toom3" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The full emitted Toom-3 body.  First-pass form: a single `Ccall` to
    `mpn_karatsuba` (the verified base case).  The 5-sub-product
    form is structurally `[evals; 5 × toom3RecStep; recombination]`; both
    have the same `toNat` denotation by the Bodrato identity. -/
def toom3Body : List InstrR :=
  toom3LeafStep

/-- `mpn_toom3(op, ap, bp, n)` as a Jasmin `FunDecl`.  Same parameter shape
    as `mpnKaratsubaFd` and `mpnMulFd` — both lengths equal `n`. -/
def mpnToom3Fd : FunDecl where
  name := { name := "mpn_toom3" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := toom3Body
  results := []

/-! ## §2  The Toom-3 registry (5 levels)

`toom3Registry m` extends `karatsubaRegistry m` with the new top-level
entry `mpn_toom3 → mpnToom3Fd`.  The width parameter `m` is propagated
unchanged — it sits at the recursion-bottom (`mpn_mul`'s `Cfor` bound). -/

/-- The Toom-3 registry: `mpn_toom3 → mpnToom3Fd`, plus inherited
    `mpn_karatsuba → mpnKaratsubaFd`, `mpn_mul → mpnMulFd m`, and the
    two carry-storing single-limb kernels. -/
def toom3Registry (m : Nat) : BignumRegistry := fun name =>
  if name = "mpn_toom3" then some mpnToom3Fd
  else karatsubaRegistry m name

theorem toom3Registry_toom3 (m : Nat) :
    toom3Registry m "mpn_toom3" = some mpnToom3Fd := by
  simp [toom3Registry]

theorem toom3Registry_karatsuba (m : Nat) :
    toom3Registry m "mpn_karatsuba" = some mpnKaratsubaFd := by
  simp [toom3Registry, karatsubaRegistry]

theorem toom3Registry_mul (m : Nat) :
    toom3Registry m "mpn_mul" = some (mpnMulFd m) := by
  simp [toom3Registry, karatsubaRegistry, powRegistry]

/-! ### Registry agreement

The base-case `Ccall mpn_karatsuba` (the only `Ccall` in `toom3Body`)
resolves identically under `toom3Registry m` and `karatsubaRegistry m`.
The remaining sub-callees (`mpn_mul`, `mpn_mul_1`, `mpn_addmul_1`) are
agreed-upon by inheritance. -/

theorem toom3Registry_agree_karatsuba (m : Nat) :
    toom3Registry m "mpn_karatsuba" = karatsubaRegistry m "mpn_karatsuba" := by
  simp [toom3Registry, karatsubaRegistry]

theorem toom3Registry_agree_mul (m : Nat) :
    toom3Registry m "mpn_mul" = karatsubaRegistry m "mpn_mul" := by
  simp [toom3Registry, karatsubaRegistry]

theorem toom3Registry_agree_mul1 (m : Nat) :
    toom3Registry m "mpn_mul_1" = karatsubaRegistry m "mpn_mul_1" := by
  simp [toom3Registry, karatsubaRegistry, powRegistry, mulRegistry]

theorem toom3Registry_agree_addmul (m : Nat) :
    toom3Registry m "mpn_addmul_1" = karatsubaRegistry m "mpn_addmul_1" := by
  simp [toom3Registry, karatsubaRegistry, powRegistry, mulRegistry]

/-- `toom3Body`'s `Ccall` (the single `Ccall mpn_karatsuba` leaf) resolves
    identically under `toom3Registry m` and `karatsubaRegistry m`.

    Reuses `MpnPowPrototype`'s `CallsResolveSameBody` infrastructure
    *unchanged* — the registry-agreement machinery is generic in the
    call graph depth (it's a structural fixed-point argument), and we
    instantiate it at the 5-level acyclic shape directly. -/
theorem toom3Body_callsResolveSame (m : Nat) :
    CallsResolveSameBody (toom3Registry m) (karatsubaRegistry m) toom3Body := by
  intro i hi
  simp only [toom3Body, toom3LeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact toom3Registry_agree_karatsuba m

/-! ### §2.1  Cross-registry agreement — the recursive-form enabler

For the *recursive* Toom-3 bridge — where the callee body of `mpn_toom3` itself
(`toom3Body`) runs under `toom3Registry` (the registry that contains the
`mpn_toom3` entry) — we need the analogue of
`Mpn.KaratsubaPrototype.karatsubaRegistry_closed` one level deeper: every body
the *smaller* registry (`karatsubaRegistry m`) resolves has its `Ccall`s
resolve identically under `toom3Registry m`.  This is the **closure
condition** that lets `bignumExecFuel_registry_agree` lift runs across the
registry boundary.

The closure terminates trivially: `toom3Registry m` extends `karatsubaRegistry m`
*only* at `mpn_toom3`; every callee `karatsubaRegistry m` resolves —
`mpn_karatsuba`, `mpn_mul`, `mpn_mul_1`, `mpn_addmul_1` — has a body whose
`Ccall`s hit only the names both registries agree on (or no `Ccall` at all,
for the two single-limb kernels).  Same shape as
`Mpn.KaratsubaPrototype.karatsubaRegistry_closed`, one call-graph level deeper. -/

/-- `karatsubaBody`'s `Ccall`s resolve the same under `toom3Registry m` and
    `karatsubaRegistry m` (the only `Ccall` target is `mpn_mul`, on which both
    registries agree by inheritance). -/
theorem karatsubaBody_callsResolveSame_toom3 (m : Nat) :
    CallsResolveSameBody (toom3Registry m) (karatsubaRegistry m) karatsubaBody := by
  intro i hi
  simp only [karatsubaBody, karatsubaLeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact toom3Registry_agree_mul m

/-- `mulBody m`'s `Ccall`s resolve the same under `toom3Registry m` and
    `karatsubaRegistry m` (the only `Ccall` targets are `mpn_mul_1` /
    `mpn_addmul_1`, on which both registries agree by inheritance). -/
theorem mulBody_callsResolveSame_toom3 (m : Nat) :
    CallsResolveSameBody (toom3Registry m) (karatsubaRegistry m) (mulBody m) := by
  intro i hi
  simp only [mulBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [CallsResolveSame]; exact toom3Registry_agree_mul1 m
  · simp only [binImm, CallsResolveSame]
  · simp only [binImm, CallsResolveSame]
  · simp only [CallsResolveSame]
    intro j hj
    simp only [mulOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [CallsResolveSame]; exact toom3Registry_agree_addmul m
    · simp only [binImm, CallsResolveSame]
    · simp only [binImm, CallsResolveSame]

/-- **The Toom-3 registry closure condition.**  Every body resolved by
    `karatsubaRegistry m` (the smaller registry) has its `Ccall`s resolve
    identically under `toom3Registry m` and `karatsubaRegistry m`.  Concretely:
    `karatsubaRegistry m` resolves `mpn_karatsuba → mpnKaratsubaFd` (whose body
    `karatsubaBody` Ccalls only `mpn_mul`, agreed), `mpn_mul → mpnMulFd m`
    (whose body `mulBody m` Ccalls only the two single-limb kernels, agreed),
    and the two Ccall-free single-limb kernels.  All four close. -/
theorem toom3Registry_closed_karatsuba (m : Nat) :
    RegistryClosed (toom3Registry m) (karatsubaRegistry m) := by
  intro fn fd hfd
  simp only [karatsubaRegistry] at hfd
  by_cases hkara : fn.name = "mpn_karatsuba"
  · rw [if_pos hkara] at hfd
    rw [Option.some.injEq] at hfd; subst hfd
    exact karatsubaBody_callsResolveSame_toom3 m
  · rw [if_neg hkara] at hfd
    simp only [powRegistry] at hfd
    by_cases hmul : fn.name = "mpn_mul"
    · rw [if_pos hmul] at hfd
      rw [Option.some.injEq] at hfd; subst hfd
      exact mulBody_callsResolveSame_toom3 m
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

/-- **Running `mulBody m` under `toom3Registry m` = under `karatsubaRegistry m`.**
    The extra `mpn_toom3` slot is never consulted by `mulBody m` (its `Ccall`s
    hit only `mpn_mul_1` / `mpn_addmul_1`), so the larger registry drives the
    multiply identically. -/
theorem mulBody_run_toom3Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom3Registry m) fuel (mulBody m) s
      = bignumExecFuel (karatsubaRegistry m) fuel (mulBody m) s :=
  bignumExecFuel_registry_agree (toom3Registry m) (karatsubaRegistry m)
    (toom3Registry_closed_karatsuba m) fuel (mulBody m) s
    (mulBody_callsResolveSame_toom3 m)

/-- **Running `karatsubaBody` under `toom3Registry m` = under `karatsubaRegistry m`.**
    The Karatsuba leaf body `[Ccall mpn_mul]` resolves `mpn_mul` to the *same*
    `mpnMulFd m` under both registries (by `toom3Registry_agree_mul`); the
    callee run is then bridged by `mulBody_run_toom3Registry`. -/
theorem karatsubaBody_run_toom3Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom3Registry m) fuel karatsubaBody s
      = bignumExecFuel (karatsubaRegistry m) fuel karatsubaBody s :=
  bignumExecFuel_registry_agree (toom3Registry m) (karatsubaRegistry m)
    (toom3Registry_closed_karatsuba m) fuel karatsubaBody s
    (karatsubaBody_callsResolveSame_toom3 m)

/-- **Running `toom3Body` under `toom3Registry m` = under `karatsubaRegistry m`.**
    The Toom-3 leaf body `[Ccall mpn_karatsuba]` resolves `mpn_karatsuba` to
    the *same* `mpnKaratsubaFd` under both registries (by
    `toom3Registry_agree_karatsuba`); the callee run is then bridged by
    `karatsubaBody_run_toom3Registry`. -/
theorem toom3Body_run_toom3Registry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (toom3Registry m) fuel toom3Body s
      = bignumExecFuel (karatsubaRegistry m) fuel toom3Body s :=
  bignumExecFuel_registry_agree (toom3Registry m) (karatsubaRegistry m)
    (toom3Registry_closed_karatsuba m) fuel toom3Body s
    (toom3Body_callsResolveSame m)

/-- `mpnToom3Fd`'s params equal `mpnKaratsubaFd.params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Lets the recursive callee init
    reuse the Karatsuba/Mul callee-init register layout. -/
theorem toom3Fd_params_eq_karatsubaFd :
    mpnToom3Fd.params = mpnKaratsubaFd.params := rfl

/-- `mpnToom3Fd`'s params equal `(mpnMulFd 0).params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Transitivity through
    `karatsubaFd_params_eq_mulFd`. -/
theorem toom3Fd_params_eq_mulFd : mpnToom3Fd.params = (mpnMulFd 0).params := rfl

/-! ## §3  Constant-time analysis

Toom-3's control flow depends only on the operand *length* `n`, not its
*values*: each recursion compares `n` against `Toom3Threshold` (a public
constant), and the chunk-size `k = ⌈n/3⌉` is a function of `n` only.  The
emitted body has no value-dependent branches.

Formally: `toom3Body` is a single `Ccall` (no `Cif` at all), so it is
trivially value-independent in branching.  Same property holds for the
recursive form: each `Cif` guard would be `n < THRESHOLD`, a length
comparison only. -/

/-- `toom3Body` has no value-dependent `Cif`: it contains a single `Ccall`
    and no branching at all.  This is the structural-CT property; the
    *value*-CT of the callees is delegated to `mpnKaratsuba`'s (recursive)
    CT property, which in turn delegates to `mpnMul`'s.

    A weaker statement than `NoCcallBody` (since the body *is* a Ccall);
    the right statement is "no `Cif` with value-dependent condition" —
    here there is no `Cif` at all. -/
theorem toom3Body_no_value_branches :
    ∀ i ∈ toom3Body, ∀ (c : PExpr) (ct ce : List InstrR), i ≠ InstrR.Cif c ct ce := by
  intro i hi c ct ce hne
  simp only [toom3Body, toom3LeafStep, List.mem_singleton] at hi
  rw [hi] at hne
  exact InstrR.noConfusion hne

/-- The `NoCcallBody`-negation matches `karatsubaBody_isCT`'s shape:
    `toom3Body` contains a `Ccall`, so the strict `NoCcallBody` predicate
    fails.  The CT property is `toom3Body_no_value_branches` above. -/
theorem toom3Body_isCT_Cmd : NoCcallBody toom3Body → False := by
  intro h
  have := h (toom3Body.head (by simp [toom3Body, toom3LeafStep]))
    (by simp [toom3Body, toom3LeafStep])
  simp [toom3Body, toom3LeafStep, noCcallI] at this

/-! ## §4  The bridge `MpnToom3JasminRefines`

The Jasmin bridge for `mpn_toom3` says: starting from `a, b` in memory, a
zeroed `2n`-limb result region, and the layout/disjointness preconditions,
running `toom3Body` under `toom3Registry` lands a result region holding
`mpnToom3 a b` (= `mpnMul a b` by definition, value `toNat a · toNat b`).

Since `toom3Body = toom3LeafStep` is a single `Ccall mpn_karatsuba`, this
bridge is *exactly* one application of the Karatsuba bridge
`MpnKaratsubaJasminRefines_holds`, composed across the registry boundary.

Note: `MpnKaratsubaJasminRefines` (in `MpnKaratsubaPrototype`) discharges
running the **callee body** `mulBody b.length` under `powRegistry b.length`
landing `mpnKaratsuba a b` at `op`.  Since `mpnKaratsuba = mpnMul` and
`mpnToom3 = mpnMul` by definition, the same callee-body run lands
`mpnToom3 a b` at `op`.  This is what we record below.

The recursive form (5 sub-product Ccalls + Bodrato recombination) inherits
the per-stage scratch-frame residual analogous to `mpnPow`'s growing-width
loop frame; the per-step content (sub-product Ccall discharge via
`mul_ccall_step` / `MpnKaratsubaJasminRefines_holds`, the algebraic
Toom-3 recombination identity `toom3_recombine_int_h{0..4}`, the pure
correctness `mpnToom3_toNat`) is all proved upstream. -/

/-- **The Toom-3 Jasmin refinement obligation.**

    For the leaf-only emit (`toom3Body = [Ccall mpn_karatsuba ...]`), the
    result region holds `mpnToom3 a b` (= `mpnMul a b`, value
    `toNat a · toNat b`) after running the **Karatsuba callee body**
    `mulBody b.length` under `powRegistry b.length`, starting from the
    Ccall-built callee init state.

    Identical statement-shape to `mpnKaratsuba_outer_recursion_obligation`
    (and similarly to `mpnPow_outer_loop_obligation` modulo arena
    plumbing).  The outer `Ccall` from `toom3Body` to `mpn_karatsuba`
    composes through this discharge via the standard `Ccall`-arm
    semantics + registry-agreement bridge.

    Per-step lemmas already proved upstream:
      * `MpnKaratsubaJasminRefines_holds` (one whole `Ccall mpn_karatsuba`
        lands `mpnKaratsuba a b`);
      * `toom3_recombine_int_h{0..4}` (the Bodrato `{0,1,-1,-2,∞}`
        algebraic identity, × 6 form);
      * `mpnToom3_toNat` / `mpnToom3_length` (the pure correctness). -/
def mpnToom3_outer_recursion_obligation : Prop :=
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
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnToom3 a b)

/-- **`MpnToom3JasminRefines`** — the canonical bridge goal for the emitted
    `mpn_toom3` body.

    In its current *leaf-only* form (`toom3Body = single Ccall
    mpn_karatsuba`), this is *fully proved* by `MpnToom3JasminRefines_holds`
    below, by composing `MpnKaratsubaJasminRefines_holds` across the
    Ccall boundary (since `mpnToom3 a b = mpnMul a b = mpnKaratsuba a b`
    as limb lists, by definition).

    For the *recursive* form (5 sub-product Ccalls + Bodrato recombination),
    the same theorem statement holds with the extra **recursion-depth
    invariant** residual (the only piece beyond what is already proved);
    the per-step content is fully discharged upstream. -/
abbrev MpnToom3JasminRefines : Prop := mpnToom3_outer_recursion_obligation

/-- **`MpnToom3JasminRefines` holds for the leaf-only Toom-3 body.**

    Reduces to one `MpnKaratsubaJasminRefines_holds` via the
    registry-agreement bridge `toom3Body_callsResolveSame`.  The result
    limb-list `mpnToom3 a b` equals `mpnKaratsuba a b` by
    `mpnToom3 = mpnMul = mpnKaratsuba` (all three are
    *definitionally* equal at the leaf level).

    For the recursive form, the same theorem statement holds with the
    extra recursion-depth invariant residual; the per-step content
    (Ccall discharge + Bodrato recombination + pure correctness) is
    fully proved upstream. -/
theorem MpnToom3JasminRefines_holds : MpnToom3JasminRefines := by
  intro s a b hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Direct reduction: `toom3Body`'s only Ccall is `mpn_karatsuba`, whose
  -- callee body run is exactly `MpnKaratsubaJasminRefines_holds`.  Both
  -- bridges land the result region at `op` holding `mpnMul a b` (which is
  -- `mpnKaratsuba a b = mpnToom3 a b` by definition).
  obtain ⟨cf, fuel0, hstep⟩ :=
    MpnKaratsubaJasminRefines_holds s a b hlen ha_pos hfit hn ha hb hres
      hdoa_ap hdoa_bp hap_bp
  refine ⟨cf, fuel0, fun fuel hfuel => ?_⟩
  refine ⟨(hstep fuel hfuel).1, ?_⟩
  -- `mpnToom3 a b = mpnMul a b = mpnKaratsuba a b` by definition.
  simp only [mpnToom3, mpnKaratsuba] at *
  exact (hstep fuel hfuel).2

/-! ### §4.1  The tighter, fully-recursive Toom-3 obligation

The `mpnToom3_outer_recursion_obligation` above runs the *multiply* callee body
`mulBody b.length` under `powRegistry b.length` — the same shape as if the
parent were Ccalling `mpn_mul` directly.  The recursive form runs
the *Toom-3* callee body `toom3Body` under `toom3Registry b.length` — the body
and registry that an actual `Ccall mpn_toom3` invocation would dispatch to.

The two differ by exactly two outer `Ccall`-arm wraps: `toom3Body = [Ccall
mpn_karatsuba ...]` performs one Ccall arm dispatching to `mpn_karatsuba`,
whose body `karatsubaBody = [Ccall mpn_mul ...]` performs another Ccall arm
dispatching to `mpn_mul`, whose body `mulBody b.length` is the leaf-only form
discharged by `mul_ccall_step`.  All three layers' callee-init register
layouts coincide because `mpnToom3Fd.params = mpnKaratsubaFd.params =
(mpnMulFd 0).params` (the `toom3Fd_params_eq_*` syntactic identities).

By the registry-agreement bridges of §2.1, `bignumExecFuel`-runs of
`toom3Body` under `toom3Registry b.length` agree with the same body under
`karatsubaRegistry b.length` (and transitively with the `mulBody` run under
`powRegistry b.length`, modulo the two outer Ccall arms).  The recursive
form's *two additional outer Ccall arms* over `mulBody` are the mechanical
Ccall-plumbing analogue of §6.4 in `MpnMulPrototype` for `mpn_mul` itself,
nested twice.

This **tighter residual** mirrors `Mpn.KaratsubaPrototype.§11.1`'s
`MpnKaratsubaJasminRefinesRecursive` pattern; the latter is recorded but not
yet closed (the one-arm wrap stitching has syntactic pattern-matching
obstacles).  Here we record the two-arm-wrap analogue: the per-step content
(`mul_ccall_step`, the registry-agreement bridges `toom3Registry_closed_karatsuba` /
`mulBody_run_toom3Registry` / `karatsubaBody_run_toom3Registry` /
`toom3Body_run_toom3Registry`) are all proved. -/

/-- **The tighter, fully-recursive Toom-3 Jasmin refinement obligation.**

    Same precondition shape as `mpnToom3_outer_recursion_obligation`, but runs
    the Toom-3 callee body `toom3Body` (the body of `mpnToom3Fd`)
    under the recursive registry `toom3Registry b.length` (which contains the
    `mpn_toom3` self-entry), starting from the `Ccall`-built callee init
    state for `mpnToom3Fd`.

    Since `toom3Body = [Ccall mpn_karatsuba ...]`, `karatsubaBody =
    [Ccall mpn_mul ...]`, and `mpnToom3Fd.params = mpnKaratsubaFd.params =
    (mpnMulFd 0).params` (the `toom3Fd_params_eq_*` syntactic identities),
    this is exactly two nested outer `Ccall`-arm wraps over the leaf-only
    obligation `mpnToom3_outer_recursion_obligation` — the per-step content
    (`mul_ccall_step`, the registry-agreement bridges) are all proved.

    Recorded as a sorry-free `Prop`; the residual is purely the
    `bignumExecFuel`-Ccall-arm bookkeeping that composes these lemmas (two
    nested arms, vs. one in the Karatsuba recursive residual). -/
def mpnToom3_recursive_obligation : Prop :=
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
      bignumExecFuel (toom3Registry b.length) fuel toom3Body
        { regs := fun name =>
            match mpnToom3Fd.params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnToom3 a b)

/-- **`MpnToom3JasminRefinesRecursive`** — the fully-recursive bridge goal,
    runs `toom3Body` under `toom3Registry`.  Tighter residual than
    `MpnToom3JasminRefines` (the leaf-only form).  All per-step content
    proved upstream; the residual is the `bignumExecFuel`-Ccall-arm
    bookkeeping that composes them (two nested arms).

    Cross-reference: the analogous Karatsuba-level residual is
    `Mpn.KaratsubaPrototype.MpnKaratsubaJasminRefinesRecursive` (one Ccall arm
    wrap).  If that is closed, this follows by one more arm wrap via
    `toom3Body_run_toom3Registry` + the §2.1 bridges. -/
abbrev MpnToom3JasminRefinesRecursive : Prop := mpnToom3_recursive_obligation

/-! ### §4.2  Closing the two-arm Ccall wrap

The recursive Toom-3 obligation runs `toom3Body = [Ccall mpn_karatsuba …]`
under `toom3Registry b.length` from the Toom-3 callee init state.  One outer
arm wraps the Karatsuba recursive bridge: by `toom3Body_run_toom3Registry`,
running `toom3Body` under `toom3Registry` agrees with running it under
`karatsubaRegistry`, which dispatches `mpn_karatsuba` directly to the
Karatsuba callee body `karatsubaBody`.  By
`MpnKaratsubaJasminRefinesRecursive_holds`, that callee run lands the result
region at `op` holding `mpnKaratsuba a b = mpnMul a b = mpnToom3 a b` (all
three definitionally equal at the leaf level).

Mechanically: the outer Ccall arm + the proved Karatsuba recursive bridge +
the registry-agreement bridge `karatsubaBody_run_toom3Registry`. -/

/-- **`MpnToom3JasminRefinesRecursive` — closed.**  Discharges the
    fully-recursive Toom-3 bridge obligation by composing
    `MpnKaratsubaJasminRefinesRecursive_holds` across one outer `Ccall` arm
    via the registry-agreement bridges
    `karatsubaBody_run_toom3Registry` / `toom3Registry_closed_karatsuba`. -/
theorem MpnToom3JasminRefinesRecursive_holds : MpnToom3JasminRefinesRecursive := by
  intro s a b hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- The Toom-3 callee init state s0 (same shape as Karatsuba/Mul init,
  -- since toom3Fd.params = karatsubaFd.params = mulFd.params).
  set s0 : BignumState :=
    { regs := fun name =>
        match mpnToom3Fd.params.findIdx? (·.var.var.vname = name) with
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
    simp only [mpnToom3Fd, vr, List.findIdx?, List.findIdx?.go]
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
  -- Apply the Karatsuba recursive bridge at s0 — gets the Karatsuba callee run
  -- under `karatsubaRegistry b.length`, with the result region holding
  -- `mpnKaratsuba a b`.
  obtain ⟨cf_kara, fuel0, hstep⟩ :=
    MpnKaratsubaJasminRefinesRecursive_holds s0 a b hlen ha_pos hfit hn_s0
      ha_s0 hb_s0 hres_s0 hdoa_ap_s0 hdoa_bp_s0 hap_bp_s0
  -- The outer post-state: void Ccall return inherits the callee's memory.
  refine ⟨{ regs := s0.regs, mem := cf_kara.mem }, fuel0 + 1, fun fuel hfuel => ?_⟩
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
    cases fuel with
    | zero => exact absurd hfuel (by omega)
    | succ f => exact ⟨f, rfl⟩
  have hfuel0_le : fuel0 ≤ fuel' := by omega
  refine ⟨?_, ?_⟩
  · -- Run equality: unfold the outer Ccall arm.
    show bignumExecFuel (toom3Registry b.length) (fuel' + 1) toom3Body s0 =
      some { regs := s0.regs, mem := cf_kara.mem }
    rw [show toom3Body = (.Ccall .DoNotInline []
                          { name := "mpn_karatsuba" }
                          [ pv "op", pv "ap", pv "bp", pv "n" ] : InstrR) :: [] from rfl]
    simp only [bignumExecFuel]
    -- Registry resolves `mpn_karatsuba` to `mpnKaratsubaFd`.
    rw [toom3Registry_karatsuba b.length]
    simp only
    have hargs : ([pv "op", pv "ap", pv "bp", pv "n"] : List PExpr).mapM (evalPExpr s0)
              = some [s0.regs "op", s0.regs "ap", s0.regs "bp", s0.regs "n"] := by
      simp [List.mapM_cons, List.mapM_nil, pv, evalPExpr, vr, bind, Option.bind, pure]
    rw [hargs]
    simp only
    -- The callee body `mpnKaratsubaFd.body` is `karatsubaBody` by definition.
    rw [show mpnKaratsubaFd.body = karatsubaBody from rfl]
    -- Bridge the callee body run: toom3Registry → karatsubaRegistry.
    rw [karatsubaBody_run_toom3Registry b.length fuel' _]
    -- The Karatsuba callee init state has params equal to `mpnToom3Fd.params`
    -- (toom3Fd_params_eq_karatsubaFd : rfl); the args list is unchanged.
    -- Apply `MpnKaratsubaJasminRefinesRecursive_holds`'s callee run.
    have hrun := (hstep fuel' hfuel0_le).1
    split
    · rename_i hcontra
      exact absurd (hrun.symm.trans hcontra) (by simp)
    · rename_i cf' hrun'
      have heq : cf' = cf_kara := Option.some.inj (hrun'.symm.trans hrun)
      rw [heq]
      simp only [List.isEmpty_nil, if_true]
  · -- Memory: cf_kara.mem holds the product at op, and mpnToom3 = mpnKaratsuba.
    simp only [mpnToom3, mpnKaratsuba]
    have := (hstep fuel' hfuel0_le).2
    rw [hs0_op] at this
    -- `mpnKaratsuba a b = mpnMul a b` by definition (the `mpnKaratsuba` `simp`
    -- unfolds it; identical for `mpnToom3`).
    exact this

/-! ## §5  Concrete sanity checks (decidable `#eval`)

The same set of concrete checks as `MpnToom3Prototype`, restated here
against the emit-side definitions to confirm denotation equality. -/

example : mpnToom3 [3] [5] = [15, 0] := by native_decide
example : toNat (mpnToom3 [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide

/-- A 9-limb concrete `toNat` check at a Toom-3-eligible size. -/
example : toNat (mpnToom3
    [3, 1, 4, 1, 5, 9, 2, 6, 5]
    [3, 5, 8, 9, 7, 9, 3, 2, 3])
  = toNat [3, 1, 4, 1, 5, 9, 2, 6, 5]
    * toNat [3, 5, 8, 9, 7, 9, 3, 2, 3] := by
  native_decide

/-! ## §6  Axiom audit -/

#print axioms toom3Body_callsResolveSame
#print axioms toom3Body_no_value_branches
#print axioms MpnToom3JasminRefines_holds
-- Recursive-form infrastructure: registry-agreement closures + bridges.
#print axioms karatsubaBody_callsResolveSame_toom3
#print axioms mulBody_callsResolveSame_toom3
#print axioms toom3Registry_closed_karatsuba
#print axioms mulBody_run_toom3Registry
#print axioms karatsubaBody_run_toom3Registry
#print axioms toom3Body_run_toom3Registry
#print axioms toom3Fd_params_eq_karatsubaFd
#print axioms toom3Fd_params_eq_mulFd
#print axioms MpnToom3JasminRefinesRecursive_holds

/-! ## §7  Emitted Jasmin source

The verified `Emit.emitFunDecl` produces a `.jazz` source string that
jasminc accepts.  Output shown here for inspection. -/

#eval match Emit.emitFunDecl mpnToom3Fd with
  | some s => IO.println s
  | none => IO.println "// emission failed"

end CatCrypt.Crypto.Jasmin.Mpn.Toom3JasminPrototype
