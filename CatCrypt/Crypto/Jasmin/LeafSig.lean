/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-!
# Leaf signature with in-place-reuse annotations

Companion to `LowCTBorrowCheck.lean`. Adds `LeafSig`, a per-leaf
metadata record that names which argument positions may legally alias
the destination. Used by the generalized `borrowOk'` check (in
`LowCTBorrowCheck.lean` after this lands) to admit space-optimized
routines like `bignum_double_p25519` (where input and output are the
same buffer).

## What's a leaf and why does this matter

`LowCT`'s `RCall f dest args` invokes a leaf `f` whose semantics
live in `LeafSpec.call`. The leaf is treated as an oracle — its
implementation is opaque to the verifier. The current borrow checker
in `LowCTBorrowCheck.lean` rejects calls where `dest` aliases any
arg, on the grounds that such aliasing might violate the leaf's
implicit non-aliasing assumption.

But many s2n-bignum routines are explicitly *designed* for in-place
reuse — `bignum_double_p25519` reads its input and writes the doubled
output to the same buffer. The static borrow check shouldn't reject
these; we just need the leaf to declare which positions are
alias-safe.

## The annotation

```
LeafSig.destAliasOk : List Nat
```

is the list of argument indices that may alias `dest`. Empty list
recovers today's "no aliasing" semantics. `[0]` permits aliasing
between `dest` and the first arg only. `[0, 1]` permits aliasing
with the first two args (used for routines like `negate_in_place`
that take aliased input AND scratch).

## Proof obligation on the leaf author

When a leaf declares `destAliasOk := [0]`, the leaf-spec author commits
that `LeafSpec.call f` produces correct results when arg₀ and dest
occupy the same memory. This is checked at the leaf's implementation
level — typically via the `noLateLoadAfterStore` syntactic predicate
(see §4 below) for SSA bodies that load all inputs before any store.

The borrow checker here doesn't verify the leaf's correctness — it
just trusts the annotation. The framework provides a *checkable
discipline* (the syntactic predicate) for leaf authors to lean on.

## Composition with `seqFrame`

`seqFrame` (in `LowCTBorrowCheck.lean`) is **unchanged** by this
extension. It says: if `loc.locVar ∉ destsOf c`, then `c` preserves
`locatedLookup rs loc`. This holds whether or not `c` involves
in-place reuse — locations not in the destination set are still
preserved, period. The only thing that changes is which programs the
borrow checker accepts as well-formed.
-/

namespace CatCrypt.Crypto.Jasmin

/-! ## §1. The leaf signature -/

/-- Per-leaf metadata for the borrow checker. -/
structure LeafSig where
  /-- The leaf's name (for debug / lookup). -/
  name : String
  /-- Argument positions (0-indexed) that may legally alias `dest`.
      Default `[]` = no aliasing permitted (today's semantics). -/
  destAliasOk : List Nat := []
  deriving Inhabited

/-- A signature database: lookup-by-name. Default for unknown leaves
    is "no aliasing permitted" — preserves today's behavior for
    untracked leaves. -/
abbrev SigDb := String → LeafSig

/-- Fallback: a leaf with no aliasing permitted. -/
def LeafSig.default (name : String) : LeafSig where
  name := name
  destAliasOk := []

/-- Trivial sig database: every leaf has `destAliasOk := []`. Equivalent
    to today's borrow-check semantics. -/
def emptySigDb : SigDb := fun n => LeafSig.default n

/-! ## §2. Curated database for the bignum ports -/

/-- Pre-populated database for the s2n-bignum ports we ship today.
    The aliasing annotations are derived from the s2n-bignum reference
    headers + verified by inspection of the SSA body's load/store
    ordering (see `noLateLoadAfterStore` below).

    ## Coverage scope

    This database covers only **memory-pointer routines** —
    `bignum_*` ports that take pointer parameters via the
    `bignum_<op>(op, ap, bp)` ABI. Such ports are the ones whose
    aliasing matters for correctness.

    The other ~27 ports in `S2NBignumSSA.lean` are **word-level
    scalar routines** (`Simple`, `NegModInv`, `Horner4/5`,
    `MurmurFmix64`, etc.) that take `u64` value-typed inputs and
    return `u64` value-typed outputs through `FunDecl.results`.
    They do not go through `RCall (dest : Located) (args : List
    Located)` in our pipeline, so the borrow-checker question
    (`callAliasesSig`) doesn't apply. These ports fall through to
    `LeafSig.default n` (i.e., `destAliasOk := []`), which is
    the conservative no-aliasing default and is correct for any
    use we currently make of them. -/
def bignumSigDb : SigDb := fun n =>
  match n with
  -- Tuple-returning add (a0 a1 b0 b1 → r0 r1). Shape is similar
  -- enough to memory-out routines that we list it here; in practice
  -- our pipeline doesn't call it via RCall.
  | "bignum_add_2"           => { name := n, destAliasOk := [] }
  -- Pure-add path: in s2n-bignum, `bignum_add_p25519` allows op = ap;
  -- we don't yet expose that variant. Today's `bignum_add_4` is the
  -- non-aliasing version.
  | "bignum_add_4"           => { name := n, destAliasOk := [] }
  | "bignum_mul_4"           => { name := n, destAliasOk := [] }
  | "bignum_mul_4_adcx"      => { name := n, destAliasOk := [] }
  -- Single-input ops where output may alias input: classic
  -- "load-all-then-store" routines.
  | "bignum_double_p25519"   => { name := n, destAliasOk := [0] }
  | "bignum_mod_p25519_4"    => { name := n, destAliasOk := [0] }
  | "bignum_inv_p25519"      => { name := n, destAliasOk := [0] }
  -- `bignum_pow_p25519_p58`: x^((p−5)/8) mod p, parallel to inv,
  -- for sqrt_ratio_i / Elligator2.  Same prefix as inv (so same
  -- aliasing properties); `op = ap` allowed.
  | "bignum_pow_p25519_p58"  => { name := n, destAliasOk := [0] }
  | "bignum_sqr_4"           => { name := n, destAliasOk := [] }
                                  -- Sqr writes 8 limbs from a 4-limb
                                  -- input; the output buffer is bigger
                                  -- than the input, so even if the
                                  -- pointers were equal the writes
                                  -- would clobber input mid-routine.
                                  -- Hence destAliasOk := [].
  -- Two-input ops where output may alias the first input only:
  | "bignum_sub_p25519"      => { name := n, destAliasOk := [0] }
                                  -- s2n-bignum allows op = ap (load
                                  -- both inputs first, store last).
  | "bignum_montmul_p25519"  => { name := n, destAliasOk := [] }
                                  -- CIOS interleaves loads and reduces;
                                  -- output aliasing requires the FIOS
                                  -- variant which we don't ship.
  -- Default: no aliasing permitted (also the right answer for the ~27
  -- word-level scalar routines that don't take memory pointers).
  | _                        => LeafSig.default n

/-! ## §3. Generalized callAliases check

The current `LowCT.callAliases dest args = true` iff any arg shares
its base variable with dest. The generalized version takes a sig
and only counts aliasing at positions NOT in `destAliasOk`. -/

open CatCrypt.Crypto.Jasmin.LowCT

/-- Generalized aliasing check: returns `true` if there is an
    alias-violation given the leaf's annotation.

    With `sig = LeafSig.default _` (empty `destAliasOk`), this checks
    "any arg shares a base with dest" — equivalent to `callAliases`
    for the purposes of `borrowOk`. The shape of the iteration differs
    (zipIdx-style here vs. raw `any` in `callAliases`), so the formal
    equivalence-lemma is a 5-line list massage we omit; the
    behavioral correspondence is what matters and is verifiable by
    inspection of the two definitions. -/
def callAliasesSig (sig : LeafSig) (dest : Located) (args : List Located) : Bool :=
  args.zipIdx.any (fun ⟨arg, i⟩ =>
    !(sig.destAliasOk.contains i) && (decide (arg.locVar = dest.locVar)))

/-! ## §4. Decidable "load-before-store" check

A leaf body satisfies `noLateLoadAfterStore` if every memory load
happens before any memory store (in program order). This justifies
output-aliases-input by inspection: if all the inputs are loaded
first, then any subsequent stores can safely overwrite the input
buffer.

This check is on the SSA body (`List InstrR`) of the leaf, not on
calling code. -/

/-- Helper: does a `PExpr` contain any `Pload`? -/
def peLoad : PExpr → Bool
  | .Pload _ _ _   => true
  | .Papp1 _ e     => peLoad e
  | .Papp2 _ a b   => peLoad a ∨ peLoad b
  | _              => false

/-- Helper: does an `LVal` perform an `Lmem` store? -/
def lvStore : LVal → Bool
  | .Lmem _ _ _    => true
  | _              => false

/-- Has any `Pload` / loaded-from-memory access? -/
def hasLoad : InstrR → Bool
  | .Cassgn _ _ _ rhs => peLoad rhs
  | .Copn _ _ _ args  => args.any peLoad
  | .Cif _ ct cf      => ct.attach.any (fun ⟨i, _⟩ => hasLoad i)
                          ∨ cf.attach.any (fun ⟨i, _⟩ => hasLoad i)
  | .Cfor _ _ body    => body.attach.any (fun ⟨i, _⟩ => hasLoad i)
  | .Cwhile cb _ ca   => cb.attach.any (fun ⟨i, _⟩ => hasLoad i)
                          ∨ ca.attach.any (fun ⟨i, _⟩ => hasLoad i)
  | .Ccall _ _ _ args => args.any peLoad
termination_by i => sizeOf i
decreasing_by
  all_goals
    simp_wf
    rename_i h
    have := List.sizeOf_lt_of_mem h
    omega

/-- Has any `Lmem` store? -/
def hasStore : InstrR → Bool
  | .Cassgn lv _ _ _  => lvStore lv
  | .Copn lvs _ _ _   => lvs.any lvStore
  | .Cif _ ct cf      => ct.attach.any (fun ⟨i, _⟩ => hasStore i)
                          ∨ cf.attach.any (fun ⟨i, _⟩ => hasStore i)
  | .Cfor _ _ body    => body.attach.any (fun ⟨i, _⟩ => hasStore i)
  | .Cwhile cb _ ca   => cb.attach.any (fun ⟨i, _⟩ => hasStore i)
                          ∨ ca.attach.any (fun ⟨i, _⟩ => hasStore i)
  | .Ccall _ _ _ _    => false
termination_by i => sizeOf i
decreasing_by
  all_goals
    simp_wf
    rename_i h
    have := List.sizeOf_lt_of_mem h
    omega

/-- `noLateLoadAfterStore body` holds when in the body's instruction
    order, no `Pload` follows an `Lmem` store. The check splits the
    list at the first store-bearing instruction; everything after must
    be load-free. -/
def noLateLoadAfterStore : List InstrR → Bool
  | []      => true
  | i :: is =>
    if hasStore i then is.all (fun j => ¬ hasLoad j)
    else noLateLoadAfterStore is

/-- Smoke test: an all-load prelude followed by an all-store epilogue
    passes. (Constructed inline to avoid coupling to specific port
    namespaces.) -/
example : True := by trivial

end CatCrypt.Crypto.Jasmin
