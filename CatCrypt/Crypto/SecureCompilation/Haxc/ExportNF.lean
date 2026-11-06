/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.BackHalf
public import CatCrypt.Crypto.SecureCompilation.Haxc.FrontLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin

/-!
# The route program of a program of `NFProg jasminDialect`

`exportNF p` is the route program `RouteProg` of a program `p` of `NFProg jasminDialect`
with one result: the program `NFProgCatToJasmin.jasminNFToComL p` of `ComL` when `p` is in
the one-carried loop fragment, and `none` otherwise. A program made of let-bindings and a
return exports to the embedding of its straight-line program `NFProg.toCom? p`
(`exportNF_of_toCom?`).

## Main definitions

* `exportNF` — the route program of a program of `NFProg jasminDialect`.
* `exportNFJ` — the program `RouteProgJ` of a program: `exportNF`, else the program itself
  for the region back half when its region legalisation `legalizeRegion` (the identity)
  passes `regionExportableB` and it has no `call` (`exportNFJ_regions`).
* `onlyCalls` — the test that every `call` of a program is at a signature of a list.
* `exportRegion` — the program itself for the region back half when its region legalisation
  passes `regionExportableB` and every `call` of it is at a signature of a list `L`
  (`onlyCalls L`). At the empty list it is the last alternative of `exportNFJ` alone
  (`exportRegion_nil`).

## Main results

* `exportNF_of_toCom?`, `exportNF_eq_straight_orElse_loop` — the export of a straight-line
  program is `RouteProg.straight`, and the export is the straight-line reading when it
  exists and the program of `ComL` otherwise.
* `exportNF_denote` — `p` denotes, at every fuel, the one value its route program denotes.
* `exportNF_ctLeak` — the route program leaks the events of the run `NFProg.leakRun` of `p`,
  from `NFLeakLower.jasminNFToComLAt_ctLeak` on the looped program.
* `exportNF_routeCT` — a program constant time for labels `L` (`NFCT`) exports to a route
  program constant time for `L` (`RouteCT`).
* `exportNFJ_denote`, `exportNFJ_ctLeak`, `exportNFJ_routeCT` — `p` and its program
  `exportNFJ p` at the same fuel both fail or both succeed with the same value and the same
  events, and constant time at a fuel passes to the export (`RouteCTJ`).
* `onlyCalls_nil`, `onlyCalls_of_callFree` — at the empty list the test is `NFProg.callFree`,
  and a program without `call` passes the test at every list.
* `exportRegion_nil`, `exportRegion_of_callFree` — the region export at the empty list is
  the test `regionExportableB` of the region legalisation on a program without `call`, and on
  a program without `call` the region export at every list is the region export at the empty list.
* `exportNFJ_isSome_of_exportRegion`, `exportRegion_denoteF` — a program the region export
  accepts at the empty list is accepted by `exportNFJ`, and a result of the region export
  and a result of `exportNFJ` have the same denotation at every fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (jasminNFToComL
  jasminNFToComLAt_denote jasminNFToComL_of_toCom?)

/-- **The route program of a program of `NFProg jasminDialect`** with one result: the
    program `jasminNFToComL p` of `ComL` as `RouteProg.loop`, and `none` when `p` is outside
    the one-carried loop fragment. -/
def exportNF {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    Option (RouteProg Γ t) :=
  (jasminNFToComL p).map RouteProg.loop

/-- A program `NFProg.toCom?` reads as the straight-line program `c` exports to
    `RouteProg.straight c`. -/
theorem exportNF_of_toCom? {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {c : Com jasminDialect Γ t} (hc : p.toCom? = some c) :
    exportNF p = some (.straight c) := by
  unfold exportNF
  rw [jasminNFToComL_of_toCom? p hc]
  rfl

/-- The export is the straight-line program `NFProg.toCom?` as `RouteProg.straight` when `p`
    is made of let-bindings and a return, and the program `jasminNFToComL p` as
    `RouteProg.loop` otherwise. -/
theorem exportNF_eq_straight_orElse_loop {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) :
    exportNF p =
      ((p.toCom?).map RouteProg.straight <|> (jasminNFToComL p).map RouteProg.loop) := by
  rcases hs : p.toCom? with _ | c
  · rfl
  · rw [exportNF_of_toCom? hs]
    rfl

/-- **Preservation.** When `exportNF p = some rp`, the program `p` denotes, at every fuel
    and valuation, `some` of the one value `rp` denotes. -/
theorem exportNF_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) {rp : RouteProg Γ t} (h : exportNF p = some rp)
    (fuel : Nat) (W : Ctxt.Valuation Γ) :
    p.denote fuel W = some (.cons (rp.denote W) .nil) := by
  unfold exportNF at h
  obtain ⟨jc, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  exact jasminNFToComLAt_denote p t rfl jc hj fuel W

/-! ## The leakage of the export -/

section Leak

open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (jasminNFToComLAt jforNode)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakLower
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open MultiBlockLowering (hvAppend)

/-- **The leakage of the export.** When `exportNF p = some rp`, the program `p` runs from
    `W` to some results and events, and `rp` leaks those events at the leakage model
    `jLeakModel Pj`. -/
theorem exportNF_ctLeak (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) {rp : RouteProg Γ t}
    (h : exportNF p = some rp) (W : Ctxt.Valuation Γ) :
    ∃ r, NFProg.leakRun (jLeakModel Pj) fuel p W = some r ∧
      RouteProg.ctLeak Pj rp W = r.2 := by
  unfold exportNF at h
  obtain ⟨jc, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Dialects.NFLeakLower.jasminNFToComLAt_ctLeak _ fuel p t rfl jc hj W

/-- **Constant time through the export.** A program of `NFProg jasminDialect` constant time
    for the labels `L` exports to a route program constant time for `L`. -/
theorem exportNF_routeCT (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) {rp : RouteProg Γ t}
    (h : exportNF p = some rp) (L : Labels Γ) (hct : NFCT (jLeakModel Pj) L fuel p) :
    RouteCT Pj L rp := by
  intro W₁ W₂ hW
  obtain ⟨r₁, h₁, e₁⟩ := exportNF_ctLeak Pj fuel p h W₁
  obtain ⟨r₂, h₂, e₂⟩ := exportNF_ctLeak Pj fuel p h W₂
  have hs := hct W₁ W₂ hW
  rw [h₁, h₂, Option.map_some, Option.map_some, Option.some.injEq] at hs
  rw [e₁, e₂, hs]

end Leak

/-! ## The export to a route program or a structured program -/

section ExportJ

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck

/-- **The program `RouteProgJ` of a program of `NFProg jasminDialect`** with one result: the
    route program `exportNF p` as `RouteProgJ.straightLoop`, else the program itself as
    `RouteProgJ.regions` when its region legalisation `legalizeRegion p` passes the test
    `regionExportableB` of the region exporter and it has no `call` (`NFProg.callFree`), else
    `none`. -/
def exportNFJ {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    Option (RouteProgJ Γ t) :=
  (exportNF p).map RouteProgJ.straightLoop
    <|> (if (regionExportableB (legalizeRegion p) && p.callFree) = true then
        some (RouteProgJ.regions p)
      else none)

/-- A program `exportNF` accepts exports to its route program under `exportNFJ`. -/
theorem exportNFJ_of_exportNF {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {rp : RouteProg Γ t} (h : exportNF p = some rp) :
    exportNFJ p = some (.straightLoop rp) := by
  unfold exportNFJ
  rw [h]
  rfl

/-- A program that `exportNF` refuses, whose region legalisation passes `regionExportableB`
    and that has no `call`, exports to itself as `RouteProgJ.regions`. -/
theorem exportNFJ_regions {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (hs : exportNF p = none)
    (hB : regionExportableB (legalizeRegion p) = true)
    (hc : p.callFree = true) : exportNFJ p = some (.regions p) := by
  unfold exportNFJ
  rw [hs, hB, hc]
  rfl

/-- **Every `call` of the program is at a signature of the list `L`**: a symbol with the
    types of its arguments and of its results. -/
def onlyCalls (L : List (String × List JasminTy × List JasminTy)) :
    {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => onlyCalls L k
  | _, _, .forLoop _ _ body k => onlyCalls L body && onlyCalls L k
  | _, _, .ifThenElse _ thn els k => onlyCalls L thn && onlyCalls L els && onlyCalls L k
  | _, _, .whileLoop _ body k => onlyCalls L body && onlyCalls L k
  | _, _, .call (as := as) (rs := rs) f _ k => L.contains (f, as, rs) && onlyCalls L k

/-- At the empty list the test `onlyCalls` is `NFProg.callFree`. -/
theorem onlyCalls_nil {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : onlyCalls [] p = p.callFree := by
  induction p with
  | ret vs => rfl
  | var e k ih => exact ih
  | forLoop count inits body k ihb ihk => simp only [onlyCalls, NFProg.callFree, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [onlyCalls, NFProg.callFree, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk => simp only [onlyCalls, NFProg.callFree, ihb, ihk]
  | call f args k ih => simp [onlyCalls, NFProg.callFree]

/-- A program without `call` passes the test `onlyCalls` at every list. -/
theorem onlyCalls_of_callFree (L : List (String × List JasminTy × List JasminTy))
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    (h : p.callFree = true) : onlyCalls L p = true := by
  induction p with
  | ret vs => rfl
  | var e k ih => exact ih h
  | forLoop count inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at h
      simp only [onlyCalls, ihb h.1, ihk h.2, Bool.and_self]
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at h
      simp only [onlyCalls, iht h.1.1, ihe h.1.2, ihk h.2, Bool.and_self]
  | whileLoop inits body k ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at h
      simp only [onlyCalls, ihb h.1, ihk h.2, Bool.and_self]
  | call f args k ih => simp [NFProg.callFree] at h

/-- **The region export of a program of `NFProg jasminDialect`** with one result, at the
    list `L` of the signatures of the declared procedures: the program itself as
    `RouteProgJ.regions` when its region legalisation `legalizeRegion p` passes the test
    `regionExportableB` of the region exporter and every `call` of it is at a signature of
    `L` (`onlyCalls L`), else `none`. At the empty list it is the last alternative of
    `exportNFJ`, without the exporter tried before it (`exportRegion_nil`). The region back
    half `compileRegion` refuses a program with a `call`, so a result with a `call` is
    compiled by no back half. -/
def exportRegion (L : List (String × List JasminTy × List JasminTy))
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    Option (RouteProgJ Γ t) :=
  if (regionExportableB (legalizeRegion p) && onlyCalls L p) = true then
    some (RouteProgJ.regions p)
  else none

/-- **The region export at the empty list** is the program itself when its region
    legalisation passes `regionExportableB` and it has no `call` (`NFProg.callFree`), else
    `none`. -/
theorem exportRegion_nil {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) :
    exportRegion [] p =
      if (regionExportableB (legalizeRegion p) && p.callFree) = true then
        some (RouteProgJ.regions p)
      else none := by
  unfold exportRegion
  rw [onlyCalls_nil]

/-- **On a program without `call` the region export at every list is the region export at
    the empty list.** -/
theorem exportRegion_of_callFree (L : List (String × List JasminTy × List JasminTy))
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (h : p.callFree = true) : exportRegion L p = exportRegion [] p := by
  unfold exportRegion
  rw [onlyCalls_nil, onlyCalls_of_callFree L p h, h]

/-- A result of the region export of `p` is `RouteProgJ.regions p`. -/
theorem exportRegion_eq_some {L : List (String × List JasminTy × List JasminTy)}
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {rp : RouteProgJ Γ t} (h : exportRegion L p = some rp) :
    rp = .regions p := by
  unfold exportRegion at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A program the region export accepts at the empty list is accepted by `exportNFJ`. -/
theorem exportNFJ_isSome_of_exportRegion {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {rp : RouteProgJ Γ t} (h : exportRegion [] p = some rp) :
    ∃ rp', exportNFJ p = some rp' := by
  rw [exportRegion_nil] at h
  unfold exportNFJ
  rcases exportNF p with _ | r
  · exact ⟨rp, h⟩
  · exact ⟨_, rfl⟩

/-- **Preservation, bisimulation form.** When `exportNFJ p = some rp`, the program `p` and
    the program `rp` at the same fuel both fail or both succeed, and `p` returns the one value
    `rp` denotes. -/
theorem exportNFJ_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) {rp : RouteProgJ Γ t} (h : exportNFJ p = some rp)
    (fuel : Nat) (W : Ctxt.Valuation Γ) :
    p.denote fuel W = (rp.denoteF fuel W).map (HVector.cons · .nil) := by
  unfold exportNFJ at h
  rcases hs : exportNF p with _ | r
  · rw [hs] at h
    change (if (regionExportableB (legalizeRegion p) && p.callFree) = true then
      some (RouteProgJ.regions p) else none) = some rp at h
    split at h
    · obtain rfl := Option.some.inj h
      rw [RouteProgJ.denoteF_regions, Option.map_map]
      rcases p.denote fuel W with _ | v
      · rfl
      · exact congrArg some (cons_oneResult v).symm
    · cases h
  · rw [hs] at h
    change some (RouteProgJ.straightLoop r) = some rp at h
    obtain rfl := Option.some.inj h
    exact exportNF_denote p hs fuel W

/-- **The two exports of a program denote the same function.** A result of the region export
    of `p` and a result of `exportNFJ p` have the same denotation at every fuel. -/
theorem exportRegion_denoteF {L : List (String × List JasminTy × List JasminTy)}
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {rp rp' : RouteProgJ Γ t} (h : exportRegion L p = some rp)
    (h' : exportNFJ p = some rp') (fuel : Nat) (W : Ctxt.Valuation Γ) :
    rp.denoteF fuel W = rp'.denoteF fuel W := by
  obtain rfl := exportRegion_eq_some h
  rw [RouteProgJ.denoteF_regions, exportNFJ_denote p h' fuel W, Option.map_map]
  rcases rp'.denoteF fuel W with _ | x
  · rfl
  · rfl

/-- **The leakage of the export, bisimulation form.** When `exportNFJ p = some rp`, the
    events of `p` at a fuel are the events of `rp` at the same fuel, at the leakage model
    `jLeakModel Pj`. -/
theorem exportNFJ_ctLeak (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) {rp : RouteProgJ Γ t}
    (h : exportNFJ p = some rp) (W : Ctxt.Valuation Γ) :
    (NFProg.leakRun (jLeakModel Pj) fuel p W).map Prod.snd = RouteProgJ.ctLeak Pj fuel rp W := by
  unfold exportNFJ at h
  rcases hs : exportNF p with _ | r
  · rw [hs] at h
    change (if (regionExportableB (legalizeRegion p) && p.callFree) = true then
      some (RouteProgJ.regions p) else none) = some rp at h
    split at h
    · obtain rfl := Option.some.inj h
      exact (RouteProgJ.ctLeak_regions Pj fuel p W).symm
    · cases h
  · rw [hs] at h
    change some (RouteProgJ.straightLoop r) = some rp at h
    obtain rfl := Option.some.inj h
    obtain ⟨q, hq, e⟩ := exportNF_ctLeak Pj fuel p hs W
    rw [hq, Option.map_some, RouteProgJ.ctLeak_straightLoop, e]

/-- **Constant time through the export.** A program of `NFProg jasminDialect` constant time
    for the labels `L` at a fuel exports to a program constant time for `L` at that fuel. -/
theorem exportNFJ_routeCT (Pj : JLeakParams) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (p : NFProg jasminDialect Γ [t]) {rp : RouteProgJ Γ t}
    (h : exportNFJ p = some rp) (L : Labels Γ) (hct : NFCT (jLeakModel Pj) L fuel p) :
    RouteCTJ Pj L fuel rp := fun W₁ W₂ hW =>
  (exportNFJ_ctLeak Pj fuel p h W₁).symm.trans
    ((hct W₁ W₂ hW).trans (exportNFJ_ctLeak Pj fuel p h W₂))

end ExportJ

end CatCrypt.Crypto.SecureCompilation.Haxc
