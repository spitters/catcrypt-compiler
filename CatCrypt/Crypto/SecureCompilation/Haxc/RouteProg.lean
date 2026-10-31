/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import HaxLean.Value

@[expose] public section

set_option autoImplicit false

/-!
# The route's program, the export names and the source value of a denotation

The interface between a front of the hax compiler and its back half. A front produces a
`RouteProgJ`: a dialect program `RouteProg`, a `ComL` program of `jasminDialect` into which a
straight-line `Com` embeds by `comToComL`, or a structured program of
`NFProg jasminDialect`, which the region back half `RegionBackend.compileRegion` compiles.
The back half exports a program under the names `AbiNames`, and its correctness theorem reads
the program's denotation as a source value through `denVal`.

## Main results

* `AbiNames`, `exportReg`, `exportReg_rsp` — the names the physical-ABI export reads, the
  export name of a System V register, and the export name `RSP+off` of a stack word.
* `RouteProg`, `RouteProg.denote` — the dialect program a route produces, and its denotation.
* `RouteProg.straight`, `RouteProg.loop`, `RouteProg.elim`, `RouteProg.cases_straight_loop` —
  the two forms of a route program, the eliminator that dispatches on `ComL.toCom?`, and
  case analysis.
* `RouteProgJ`, `RouteProgJ.denoteF` — a route program or a structured program of
  `NFProg jasminDialect`, and its denotation at a fuel: `some` of `RouteProg.denote` for a
  route program, and the one result `oneResult` of `NFProg.denote` for a structured program
  (`none` when a do-while runs out of fuel).
* `arrVal`, `denVal` — the source value of a word array and of a denotation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL (comToComL comToComL_denote)
open _root_.Hax (Value)

/-- The names the physical-ABI export reads: the function symbol, the output and input
    array arguments of a loop export, and the System V argument registers. -/
structure AbiNames where
  /-- The function symbol. -/
  fname : String
  /-- The output array argument of a loop export. -/
  outArg : String
  /-- The input array arguments of a loop export. -/
  inArgs : List String
  /-- The argument registers, in order (`"RDI"`, `"RSI"`, ...). -/
  abiArgs : List String

/-- The export register name of a System V register: `"%rdi"` to `"RDI"`. -/
def exportReg (r : String) : String := String.ofList ((r.toList.drop 1).map Char.toUpper)

/-- The export name of the carrier name `"%rsp+" ++ s` of a stack word, `s` a string of
    decimal digits, is `"RSP+" ++ s`: `Char.toUpper` fixes digits. -/
theorem exportReg_rsp (s : String) (hs : s.toList.all Char.isDigit = true) :
    exportReg ("%rsp+" ++ s) = "RSP+" ++ s := by
  have hm : s.toList.map Char.toUpper = s.toList := by
    refine (List.map_congr_left fun c hc => ?_).trans (List.map_id _)
    have hd := List.all_eq_true.mp hs c hc
    simp only [Char.toUpper, Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd ⊢
    rw [dite_eq_right (fun h => by
      have h1 := h.1; have h2 := hd.2
      rw [UInt32.le_iff_toNat_le] at h1 h2
      exact absurd (Nat.le_trans h1 h2) (by decide))]
    rfl
  apply String.ext
  simp [exportReg, String.toList_append, hm]

/-- The dialect program a route produces: a `ComL` program. A straight-line `Com` enters by
    its embedding `comToComL` (`RouteProg.straight`). -/
structure RouteProg (Γ : Ctxt jasminDialect) (t : JasminTy) where
  /-- The program. -/
  com : ComL Γ t

/-- The route program of a straight-line program: its embedding `comToComL`. -/
def RouteProg.straight {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t) :
    RouteProg Γ t :=
  ⟨comToComL c⟩

/-- The route program of a `ComL` program. -/
def RouteProg.loop {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) : RouteProg Γ t :=
  ⟨c⟩

universe u in
/-- The eliminator of a route's program: `fs` on the straight-line program that
    `ComL.toCom?` reads from a program with no loop node, and `fl` on a program with a loop
    node. -/
@[inline] def RouteProg.elim {α : Sort u} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fs : Com jasminDialect Γ t → α) (fl : ComL Γ t → α) (p : RouteProg Γ t) : α :=
  match p.com.toCom? with
  | some c => fs c
  | none => fl p.com

universe u in
/-- The eliminator on a straight-line program. -/
@[simp] theorem RouteProg.elim_straight {α : Sort u} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fs : Com jasminDialect Γ t → α) (fl : ComL Γ t → α) (c : Com jasminDialect Γ t) :
    (RouteProg.straight c).elim fs fl = fs c := by
  simp only [RouteProg.elim, RouteProg.straight, ComL.toCom?_comToComL]

universe u in
/-- The eliminator on a program with a loop node. -/
theorem RouteProg.elim_loop {α : Sort u} {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fs : Com jasminDialect Γ t → α) (fl : ComL Γ t → α) {c : ComL Γ t}
    (h : c.toCom? = none) : (RouteProg.loop c).elim fs fl = fl c := by
  simp only [RouteProg.elim, RouteProg.loop, h]

/-- Case analysis on a route's program: a property of every straight-line program and of
    every program with a loop node holds of every route program. -/
@[elab_as_elim] theorem RouteProg.cases_straight_loop {Γ : Ctxt jasminDialect} {t : JasminTy}
    {motive : RouteProg Γ t → Prop} (p : RouteProg Γ t)
    (straight : ∀ c : Com jasminDialect Γ t, motive (.straight c))
    (loop : ∀ c : ComL Γ t, c.toCom? = none → motive (.loop c)) : motive p := by
  obtain ⟨k⟩ := p
  rcases h : k.toCom? with _ | c
  · exact loop k h
  · obtain rfl := ComL.eq_comToComL_of_toCom? h
    exact straight c

/-- The denotation of a route's program at a valuation: `ComL.denote` of its program. -/
def RouteProg.denote {Γ : Ctxt jasminDialect} {t : JasminTy} (p : RouteProg Γ t)
    (V : Ctxt.Valuation Γ) : ⟦t⟧ :=
  p.com.denote V

/-- The denotation of a straight-line program is `Com.denote`. -/
theorem RouteProg.denote_straight {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (RouteProg.straight c).denote V = c.denote V :=
  comToComL_denote c V

/-- The denotation of the route program of a `ComL` program is `ComL.denote`. -/
theorem RouteProg.denote_loop {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (V : Ctxt.Valuation Γ) : (RouteProg.loop c).denote V = c.denote V := rfl

/-- A route program `RouteProg` or a structured program of `NFProg jasminDialect` with one
    result. -/
inductive RouteProgJ : Ctxt jasminDialect → JasminTy → Type where
  /-- A straight-line or looped route program. -/
  | straightLoop {Γ : Ctxt jasminDialect} {t : JasminTy} (rp : RouteProg Γ t) :
      RouteProgJ Γ t
  /-- A structured program with one result, compiled by the region back half. -/
  | regions {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
      RouteProgJ Γ t

/-- The one result of a valuation of a context of one type. -/
def oneResult {t : JasminTy} (v : Ctxt.Valuation (d := jasminDialect) [t]) : ⟦t⟧ :=
  Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v

/-- A valuation of a context of one type is its one result followed by the empty
    valuation. -/
theorem cons_oneResult {t : JasminTy} (v : Ctxt.Valuation (d := jasminDialect) [t]) :
    HVector.cons (oneResult v) .nil = v := by
  cases v with
  | cons x xs =>
      cases xs
      rfl

/-- The denotation of a `RouteProgJ` program at the fuel `fuel`: `some` of `RouteProg.denote`
    for a route program, and the one result of `NFProg.denote fuel` for a structured
    program. -/
def RouteProgJ.denoteF {Γ : Ctxt jasminDialect} {t : JasminTy} (fuel : Nat) :
    RouteProgJ Γ t → Ctxt.Valuation Γ → Option ⟦t⟧
  | .straightLoop rp, V => some (rp.denote V)
  | .regions p, V => (p.denote fuel V).map oneResult

/-- A route program denotes `some` of its denotation, at every fuel. -/
@[simp] theorem RouteProgJ.denoteF_straightLoop {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (rp : RouteProg Γ t) (V : Ctxt.Valuation Γ) :
    (RouteProgJ.straightLoop rp).denoteF fuel V = some (rp.denote V) := rfl

/-- A structured program denotes the one result of its fuelled denotation. -/
@[simp] theorem RouteProgJ.denoteF_regions {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (p : NFProg jasminDialect Γ [t]) (V : Ctxt.Valuation Γ) :
    (RouteProgJ.regions p).denoteF fuel V = (p.denote fuel V).map oneResult := rfl

/-- The source value of a word array: the list of its words as integers. -/
def arrVal {n : Nat} (a : Fin n → BitVec 64) : Value :=
  .array ((List.range n).map fun j => .int (stackGet a j).toNat)

/-- The source value of a denotation: a word array as the list of its words, a register as
    its integer value, and the empty tuple at every other type. -/
def denVal : (t : JasminTy) → ⟦t⟧ → Value
  | .stackArr 64 _, a => arrVal a
  | .reg _, x => .int x.toNat
  | _, _ => .tuple []

end CatCrypt.Crypto.SecureCompilation.Haxc
