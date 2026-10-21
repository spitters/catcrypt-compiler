/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Quarta
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Match

/-!
# Multi-output leaf-call tower agreement

Extends the leaf-call agreement framework from the 1-output predicate
`LeafCallAgreesTower` (in `HaxToLowCTSim_Quarta.lean`) and the
2-output predicate `LeafCallAgreesTowerSwap` (in `HaxToLowCTSim_Match.lean`)
to general `n`-output leaves via `LeafCallAgreesTowerN`.

The constructor `LowCT.RCallN` (see `Jasmin/LowCT.lean`) is
the AST-level analogue of `RCallSwap` for arbitrary destination count.
`RustExec.callN` writes each destination, output `i` read through
`LeafSpec.call` at `callNLeafName f i`.  Which values those outputs carry
for a given leaf is pinned by external hypotheses (named by the
leaf `f`).  `LeafCallAgreesTowerN` is the consumer-supplied per-leaf
agreement that ties such an oracle to a `ValueTowerBridge`.

The shape mirrors `LeafCallAgreesTowerSwap`:

* The Builtins-side returns a single `Value.tuple components`.
* The `n` destinations are paired with parallel tower types `dts` and,
  after the `RCallN` step, each destination slot holds a `RustVal`
  bridge-aligned with the corresponding source-side tuple component.

Per-protocol instantiations supply this predicate for concrete
primitives (e.g. `(carry, sum) = adcx(a, b, c_in)` for bignum schedules,
or `(lo, hi) = mul64x64(a, b)` for wide multiplications).
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   callNLeafName callNUpdate locatedLookup rsTower_callNUpdate_nth)

/-! ## §1  `LeafCallAgreesTowerN`

The `n`-output tower-typed leaf-agreement predicate, generalising
`LeafCallAgreesTower` (`n = 1`) and `LeafCallAgreesTowerSwap` (`n = 2`).

Given:

* a leaf name `f` whose Builtins-side semantics returns
  `.tuple components` with `components.length = n`;
* a list `dests : List Located` of `n` destinations whose `locSrc`
  fields agree with a parallel list `dts : List TowerType`;
* a `ValueTowerBridge`,

the predicate asserts that any final state `rs'` reachable from `rs`
via `RustExec _ leafSpec (.RCallN f dests args) rs rs'` has, at every
destination slot `i`, a `RustVal` bridge-aligned with the source-side
tuple component `i`.

This is the **per-leaf assumption** that a concrete `LeafSpec` providing
an `n`-output primitive must satisfy.  Like `LeafCallAgreesTowerSwap`,
it is consumer-supplied: the framework states the obligation; per-leaf
instances discharge it.
-/

/-- Per-leaf `n`-output tower-agreement predicate.

    `LeafCallAgreesTowerN bi leafSpec f n dts bridge` says: when the
    Builtins-side call `bi f vals` succeeds with a tuple of `n`
    components, and `dests`/`dts` are `n` destinations with tower
    types, then every `RustExec`-reachable post-state has each
    destination's tower binding bridge-aligned with the corresponding
    source-side tuple component.

    Indexed access uses `List.get?` returning `Option`; the predicate
    asserts the corresponding `some`-shaped equalities.  This avoids
    proof terms for `Fin` index bounds and keeps the predicate uniform
    in `n`.

    The destination *names* are required distinct.  `RustExec.callN`
    writes the destinations left to right, so a repeated name carries
    only the last output written to it, and no leaf could relate that
    one slot to two different tuple components. -/
def LeafCallAgreesTowerN
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (n : Nat)
    (dts : List TowerType) (bridge : ValueTowerBridge) : Prop :=
  ∀ (rs : RustState) (dests : List Located) (args : List Located)
    (vals : List Value) (vRes : Value) (components : List Value),
    bi f vals = some vRes →
    vRes = .tuple components →
    components.length = n →
    dests.length = n →
    dts.length = n →
    (dests.map (·.locVar)).Nodup →
    (∀ (i : Nat) (d : Located) (dt : TowerType),
       dests[i]? = some d → dts[i]? = some dt → d.locSrc = dt) →
    (∀ a ∈ args, ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩) →
    ∀ rs', RustExec 0 leafSpec (.RCallN f dests args) rs rs' →
    ∀ (i : Nat) (d : Located) (dt : TowerType) (c : Value),
      dests[i]? = some d → dts[i]? = some dt →
      components[i]? = some c →
      ∃ val,
        rs'.rsTower d.locVar = some ⟨dt, val⟩
        ∧ bridge dt c val

/-! ## §2  Per-index oracle condition and the reduction

`RustExec.callN` reads output `i` of `f` through the ordinary
single-output `LeafSpec.call` oracle at `callNLeafName f i`.  So the
`n`-output obligation is `n` ordinary single-output leaf conditions,
one per index, and `leafCallAgreesTowerN_of_index` performs that
reduction. -/

/-- Single-output leaf agreement at index `i` of a multi-output leaf.

    The same shape as `LeafCallAgreesTower`, read at the indexed leaf
    name `callNLeafName f i` and against component `i` of the
    Builtins-side tuple: the oracle's output on the argument slots of
    `rs` is bridge-aligned with that component. -/
def LeafCallOutputAgreesTower
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (i : Nat)
    (bridge : ValueTowerBridge) : Prop :=
  ∀ (rs : RustState) (dest : Located) (args : List Located)
    (vals : List Value) (components : List Value) (c : Value),
    bi f vals = some (.tuple components) →
    components[i]? = some c →
    (∀ a ∈ args, ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩) →
    bridge dest.locDst c
      (leafSpec.call (callNLeafName f i) dest.locDst (args.map (·.locDst))
        ((locatedLookup rs dest).getD default)
        (args.filterMap (fun a => rs.rsTower a.locVar)))

/-- The `n`-output obligation follows from the per-index single-output
    conditions: destination `i` reads back exactly the value the oracle
    at `callNLeafName f i` produced. -/
theorem leafCallAgreesTowerN_of_index
    (bi : Builtins) (leafSpec : LeafSpec) (f : String) (n : Nat)
    (dts : List TowerType) (bridge : ValueTowerBridge)
    (h : ∀ i, LeafCallOutputAgreesTower bi leafSpec f i bridge) :
    LeafCallAgreesTowerN bi leafSpec f n dts bridge := by
  intro rs dests args vals vRes components hbi hvRes _ _ _ hNodup hTy hArgs
    rs' hExec i d dt c hd hdt hc
  subst hvRes
  have hdtEq : d.locSrc = dt := hTy i d dt hd hdt
  subst hdtEq
  cases hExec with
  | callN _ _ _ _ argList hargList _ _ =>
    subst hargList
    refine ⟨leafSpec.call (callNLeafName f i) d.locDst (args.map (·.locDst))
        ((locatedLookup rs d).getD default)
        (args.filterMap (fun a => rs.rsTower a.locVar)), ?_, ?_⟩
    · simpa using
        rsTower_callNUpdate_nth leafSpec f (args.map (·.locDst))
          (args.filterMap (fun a => rs.rsTower a.locVar)) dests 0 i rs d hNodup hd
    · exact h i rs d args vals components c hbi hc hArgs

/-! ## §3  Specialisations to the existing 1- and 2-output predicates

`LeafCallAgreesTowerN` at `n = 1` reduces to the same content as
`LeafCallAgreesTower` modulo the surface AST: the 1-output case in
`LeafCallAgreesTower` is stated against `RustExec.call`, while the
`n = 1` instance of `LeafCallAgreesTowerN` is stated against
`RustExec.callN`, whose single output is read at `callNLeafName f 0`.
Both shapes coexist because they cover different AST constructors
(`RCall` vs `RCallN`), and the leaf names they read differ.

Similarly, `n = 2` parallels `LeafCallAgreesTowerSwap`: that one is
stated for `RCallSwap` (which `RustExec.callSwap` decomposes into two
sequential `RCall` steps); the `n = 2` instance of `LeafCallAgreesTowerN`
is stated for `RCallN` directly.

Per-protocol instantiations choose the AST constructor that matches
their lowering shape — `RCallSwap` for cswap-style 2-output (existing
MLDSA `ntt_butterfly` and `power2round`), `RCallN` for
`n`-output leaves with `n ≥ 3` (bignum carry-and-sum schedules,
ChaCha quarter-round destruction in `Jasmin/ByteOps.lean`).

## §4  Summary

This module defines:

* `LeafCallAgreesTowerN` — `n`-output tower-typed leaf agreement.
* `LeafCallOutputAgreesTower` — the single-output condition at one
  output index of a multi-output leaf.
* `leafCallAgreesTowerN_of_index` — the reduction of the former to the
  latter at every index.

The module adds bridge-level predicates only; it changes no
simulation proof.
-/

end CatCrypt.Crypto.Hax
