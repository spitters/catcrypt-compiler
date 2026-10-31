/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

@[expose] public section

set_option autoImplicit false

/-!
# The interface of a front of the hax compiler

A front of the hax compiler is a `FrontLegOf`: a type of source programs, a source semantics
that reads a run of a source program off an entry state of the address machine through a
System V layout `AbiLayout`, a compile function from a source program and a layout to a
route program `RouteProg`, the export names of the back half, and the leg: from every entry
state satisfying `σ.Regions`, every value `v` of a source run is the source value `denVal` of
the route program's denotation at a valuation that `σ` reads off the entry state
(`AbiValOf`). The leg of a `FrontLegOfJ` at a structured program supplies the valuation and
the fuel that the correctness theorem `RegionBackend.compileRegion_correct` of the region
back half takes (`NFEntry.compileR_correct`).

## Main definitions

* `AnyRouteProg` — a route program with its context and its result type.
* `FrontLegOf` — a front: source programs, their semantics, the compile function, the export
  names and the leg.
* `AnyRouteProgJ`, `FrontLegOfJ` — the same for a compile function to a `RouteProgJ`
  program, whose leg reads the denotation at some fuel and at the call environment of the
  front; `FrontLegOf.toJ` embeds a front.
* `RouteProgJ.envDenote` — the denotation of a `RouteProgJ` program at a call environment.

## Main results

* `FrontLegOf.leg` — the leg of a front, the field the back half composes with.
* `RouteProgJ.envDenote_empty`, `RouteProgJ.envDenote_regions_of_callFree` — at the
  environment in which every call refuses, and on a structured program without `call`, the
  denotation at a call environment is `RouteProgJ.denoteF`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open _root_.Hax (Value)

/-- A route program together with its context and the type of its result. -/
abbrev AnyRouteProg : Type :=
  Σ Γ : Ctxt jasminDialect, Σ t : JasminTy, RouteProg Γ t

/-- **A front of the hax compiler.** `Src` are the source programs; `Runs σ s sa v` states
    that the source program `s`, started from the entry state `sa` read through the layout
    `σ`, returns the value `v`; `front σ s` is the route program the front compiles `s` to
    under `σ`, or `none`; `names fname σ` are the export names of the back half; `leg` states
    that every value of a source run from an entry state satisfying `σ.Regions` is the source
    value `denVal` of the route program's denotation at a valuation `σ` reads off that entry
    state. -/
structure FrontLegOf where
  /-- The source programs. -/
  Src : Type
  /-- The source semantics read off an entry state through a layout. -/
  Runs : AbiLayout → Src → AState → Value → Prop
  /-- The compile function to a route program. -/
  front : AbiLayout → Src → Option AnyRouteProg
  /-- The export names of the back half, from the function symbol and the layout. -/
  names : String → AbiLayout → AbiNames
  /-- The leg: a source value is the source value of the route program's denotation at a
      valuation the layout reads off the entry state. -/
  leg : ∀ (σ : AbiLayout) (s : Src) (p : AnyRouteProg), front σ s = some p →
    ∀ (sa : AState) (v : Value), σ.Regions sa → Runs σ s sa v →
      ∃ V : Ctxt.Valuation p.1, AbiValOf σ sa V ∧ v = denVal p.2.1 (p.2.2.denote V)

/-- A program of `RouteProgJ` together with its context and the type of its result. -/
abbrev AnyRouteProgJ : Type :=
  Σ Γ : Ctxt jasminDialect, Σ t : JasminTy, RouteProgJ Γ t

/-- The denotation of a `RouteProgJ` program at the call environment `E` and the fuel
    `fuel`: `some` of `RouteProg.denote` for a route program, and the one result of
    `NFProg.denoteAt E fuel` for a structured program, whose `call` nodes are answered by
    `E`. -/
def RouteProgJ.envDenote {Γ : Ctxt jasminDialect} {t : JasminTy} (E : CallEnv jasminDialect)
    (fuel : Nat) : RouteProgJ Γ t → Ctxt.Valuation Γ → Option ⟦t⟧
  | .straightLoop rp, V => some (rp.denote V)
  | .regions p, V => (p.denoteAt E fuel V).map oneResult

/-- At the call environment in which every call refuses, the denotation at an environment
    is `RouteProgJ.denoteF`. -/
theorem RouteProgJ.envDenote_empty {Γ : Ctxt jasminDialect} {t : JasminTy} (fuel : Nat)
    (rp : RouteProgJ Γ t) (V : Ctxt.Valuation Γ) :
    rp.envDenote CallEnv.empty fuel V = rp.denoteF fuel V := rfl

/-- A structured program without `call` denotes at every call environment as
    `RouteProgJ.denoteF` reads it. -/
theorem RouteProgJ.envDenote_regions_of_callFree {Γ : Ctxt jasminDialect} {t : JasminTy}
    (E : CallEnv jasminDialect) (fuel : Nat) (p : NFProg jasminDialect Γ [t])
    (hp : p.callFree = true) (V : Ctxt.Valuation Γ) :
    (RouteProgJ.regions p).envDenote E fuel V = (RouteProgJ.regions p).denoteF fuel V :=
  congrArg (Option.map oneResult) (NFProg.denoteAt_of_callFree p hp E CallEnv.empty fuel V)

/-- **A front of the hax compiler to `RouteProgJ`.** The fields of `FrontLegOf`, with the
    compile function to a `RouteProgJ` program and a call environment `env s fuel` of
    `jasminDialect` for each source program and fuel, the environment in which every call
    refuses unless given. `leg` states that every value of a source run from an entry state
    satisfying `σ.Regions` is the source value `denVal` of a value the compiled program
    denotes at some fuel, at the call environment of that fuel and at a valuation `σ` reads
    off that entry state. At the default environment the denotation is
    `RouteProgJ.denoteF` (`RouteProgJ.envDenote_empty`). -/
structure FrontLegOfJ where
  /-- The source programs. -/
  Src : Type
  /-- The source semantics read off an entry state through a layout. -/
  Runs : AbiLayout → Src → AState → Value → Prop
  /-- The compile function to a `RouteProgJ` program. -/
  front : AbiLayout → Src → Option AnyRouteProgJ
  /-- The export names of the back half, from the function symbol and the layout. -/
  names : String → AbiLayout → AbiNames
  /-- The call environment that answers the `call` nodes of the compiled program of a source
      program, at a fuel of the callees. -/
  env : Src → Nat → CallEnv jasminDialect := fun _ _ => CallEnv.empty
  /-- The leg: a source value is the source value of a value the compiled program denotes at
      some fuel and the call environment of that fuel, at a valuation the layout reads off
      the entry state. -/
  leg : ∀ (σ : AbiLayout) (s : Src) (p : AnyRouteProgJ), front σ s = some p →
    ∀ (sa : AState) (v : Value), σ.Regions sa → Runs σ s sa v →
      ∃ (V : Ctxt.Valuation p.1) (fuel : Nat) (x : ⟦p.2.1⟧), AbiValOf σ sa V ∧
        p.2.2.envDenote (env s fuel) fuel V = some x ∧ v = denVal p.2.1 x

/-- A front to `RouteProg` as a front to `RouteProgJ`, through `RouteProgJ.straightLoop`. -/
def FrontLegOf.toJ (L : FrontLegOf) : FrontLegOfJ where
  Src := L.Src
  Runs := L.Runs
  front σ s := (L.front σ s).map fun p => ⟨p.1, p.2.1, .straightLoop p.2.2⟩
  names := L.names
  leg σ s p hf sa v hreg hrun := by
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
    obtain ⟨V, hV, hv⟩ := L.leg σ s q hq sa v hreg hrun
    exact ⟨V, 0, _, hV, rfl, hv⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
