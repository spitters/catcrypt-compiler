/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxFrontPrep
public import CatCrypt.Crypto.Hax.ANormCoreDenote
public import CatCrypt.Crypto.Hax.HaxRepeatCount
public import HaxLean.Phase.WhileTrueFlag

/-!
# The acceptance tests of the front and the body they select

The front prepares a function body by `haxFrontPrep` and A-normalisation (`haxFrontAnf`),
reads the literal counts of `repeat` into the calls (`repeatCountInline`), and then chooses
among the normal form and its rewritings by `ere` and `tailSome` (`anfEPick`) and, at the
end, between the chosen form and its rewriting onto the flag `haxFrontFlag` (`wtFn`). The
choices are made by acceptance tests, a `FrontOracle`: `plain a` says that the normal form
`a` is taken as it is, and `ok b` is the side condition on the body `b` taken.

This module holds the definitions that are generic in the acceptance tests. compileA
instantiates `FrontOracle` at `shapeAccepts` (`HaxFrontPrepShape`), through `nfBody` and
`haxFrontShapeOk` of `NFFront`.

## Main definitions

* `haxFrontAnf` — `haxFrontPrep` followed by A-normalisation
* `FrontOracle` — the acceptance tests by which the front selects the body
* `haxFrontRouteOkP`, `haxFrontAnfEP`, `haxFrontBodyP`, `haxFrontOkP` — the choice of the
  body and its side conditions under acceptance tests
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr)
open _root_.Hax.WhileTrueFlag (wtFn wtOk)

/-- Steps 1–4 of the front: `haxFrontPrep` followed by A-normalisation. -/
def haxFrontAnf (e : ImpExpr) : ImpExpr := aNormalizeTotal (haxFrontPrep e)

/-- The acceptance tests by which the front selects the body of step 5: `plain a` holds
    when the normal form `a` is taken as it is, and otherwise the body is the rewriting of
    `a` onto the flag `haxFrontFlag`; `ok b` is the side condition on the body `b` taken. -/
structure FrontOracle where
  /-- The normal form is taken as it is. -/
  plain : ImpExpr → Bool
  /-- The side condition on the body taken. -/
  ok : ImpExpr → Bool

/-- The side conditions of step 5 of the front on a normal form `a` under the acceptance
    tests `O`: `O.ok a` when `a` is taken as it is (`O.plain a`), and otherwise
    `wtOk haxFrontFlag` of `a` and `O.ok` of its rewriting onto the flag. -/
def haxFrontRouteOkP (O : FrontOracle) (a : ImpExpr) : Bool :=
  if O.plain a then O.ok a else wtOk haxFrontFlag a && O.ok (wtFn haxFrontFlag a)

/-- Step 4 of the front under `O`: the normal form `haxFrontAnf e` with the literal counts
    of `repeat` read into the calls (`repeatCountInline`), chosen by `haxFrontRouteOkP O`
    among that form, its rewriting by `ere` and the latter rewritten by `tailSome`
    (`anfEPick`). -/
def haxFrontAnfEP (O : FrontOracle) (e : ImpExpr) : ImpExpr :=
  anfEPick (haxFrontRouteOkP O) (repeatCountInline (haxFrontAnf e))

/-- The body of step 5 under `O`: the normal form `haxFrontAnfEP O e` when it is taken as it
    is, and otherwise its rewriting onto `haxFrontFlag`. At `shapeAccepts` it is the body
    `nfBody` of compileA's front. -/
def haxFrontBodyP (O : FrontOracle) (e : ImpExpr) : ImpExpr :=
  let a := haxFrontAnfEP O e
  if O.plain a then a else wtFn haxFrontFlag a

/-- The side conditions of the route under `O`: `aNormTDenoteOk` of `haxFrontPrep e` and
    `haxFrontRouteOkP O` of `haxFrontAnfEP O e`. At `shapeAccepts` they are
    `haxFrontShapeOk`. -/
def haxFrontOkP (O : FrontOracle) (e : ImpExpr) : Bool :=
  aNormTDenoteOk (haxFrontPrep e) && haxFrontRouteOkP O (haxFrontAnfEP O e)

end CatCrypt.Crypto.Hax
