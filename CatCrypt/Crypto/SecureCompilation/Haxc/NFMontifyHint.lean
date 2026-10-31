/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify

/-!
# The degree analysis of `montify`

`degHint p prog` computes the degrees of the parameters and a degree assignment `DegHint` for
the rewriter `NFMontify.montify` at the modulus `p`. The analysis is untrusted: `montifyCert` decides at compile time whether
the rewriter accepts the assignment, and only an accepted assignment yields a program.

The degrees lie in `{0, 1}`. A value is *fixed at degree `0`* when no hint can move it: a
parameter that is no word, a value carried by a loop, the trip index of a counted loop, a result of a branch
or of a call that is no field call at `p`, or a binding of a type other than the word type.
A value *reaches a degree-`0` position* when it is returned, carried into a loop, used as a
loop count or a branch condition, used by an expression of a binding, or passed to a call
that is no field call at `p`. Both kinds are degree `0`, and so is every operand of an
addition or a subtraction at `p` whose other operand is degree `0`: the closure of these
values under the operand pairs of the additions and subtractions, the degree-`0` set, is
kept at degree `0`.

A word outside this set that feeds a multiplication at a greater loop depth than its own, or
feeds at least two multiplications, is converted once at its definition to degree `1`;
since a conversion sits at the definition, a value defined outside a loop is converted
before the loop (`seedSet`). Every other definition keeps the degree it produces: a product
of degrees `k₁, k₂` has degree `k₁ + k₂ − 1`, so a product with a degree-`1` operand keeps
the degree of the other operand, and a product of two degree-`0` operands is the field
multiplication at degree `0`; an addition, subtraction, negation or doubling has the degree
of its operands. An addition or a subtraction whose operands differ in degree is repaired by
moving one operand definition, the one whose conversion costs less by loop depth
(`repairRound`), until all operand pairs agree. A word parameter is a definition at loop
depth `0`; one that feeds a multiplication inside a loop is converted once at entry, so a
loop-invariant operand of the products in a loop is held at degree `1` there.

A product of two distinct degree-`0` operands with its result at degree `0` that remains
after the repair has one operand converted to degree `1`, the movable operand outside the
degree-`0` set at the smaller loop depth (`pairSeeds`); the product becomes the
reduce-multiply with its result at degree `0`, and the operand pairs are repaired again. At a
modulus that passes `mont32Cert` a conversion and a reduce-multiply cost two reductions, less
than the field multiplication of the narrow template.

The montify pass `montifyPass` runs, at each modulus of the tagged field calls that passes
`mont32Cert`, the rewriter at the analysis of that modulus and the inlining of the
reduce-multiply heads (`montifyAt`); a modulus at which either refuses leaves the program
unchanged. `montifyStep` is the pass as a step of the chain `extChain`.

## Main definitions

* `DegSrc`, `DegSkel` — the degree a definition produces, and the skeleton of a program with
  an identifier at every definition a hint can move.
* `ScanFacts`, `degScan` — the definitions fixed or used at degree `0`, the operand pairs of
  the additions and subtractions, the operands of the multiplications, and the movable
  definitions with their loop depths.
* `zeroClosure`, `seedSet`, `repairSets`, `repair`, `pairSeeds`, `skelHint`, `degHint` — the
  degree-`0` set, the definitions converted to degree `1`, the repair of the operand pairs,
  the operands converted for the remaining products of two degree-`0` operands and the
  degree assignment.
* `montFree` — the program calls no reduce-multiply head.
* `fieldMods`, `montifyAt`, `montifyMods`, `montifyPass`, `montifyStep`, `montifyStepCert` —
  the moduli of the tagged calls, the montify round at one modulus, the rounds at a list of
  moduli, the montify pass, the pass as a chain step, and its certificate.

## Main results

* `montifyAux_montFree` — a program the rewriter accepts at some assignment calls no
  reduce-multiply head.
* `montify_leaf`, `montify_leaf_of_some` — at the all-zero assignment `DegHint.leaf` the
  rewriter returns the program unchanged, on every program it accepts at some assignment.
* `montifyCert_leaf`, `montifyCert_leaf_iff` — the certificate accepts the all-zero
  assignment exactly when the head `montHead p` is read at `p` and the program calls no
  reduce-multiply head.
* `montifyPass_leak`, `montifyPass_denoteAt`, `montifyStep_leakRunC` — the montify pass keeps
  the results and the events of every leakage run at `fieldEnv E`.
* `montifyPass_of_callFree`, `montifyStep_of_callFree` — the pass keeps a program without
  `call`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (w64)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert)
open _root_.Hax.FieldTag (FieldMethod fieldTag?)
open Ctxt (Var Valuation)

/-! ## 1. The skeleton of definitions -/

/-- The degree a definition produces from the degrees of its operands, named by their
    identifiers: degree `0` (`fixed0`), a product (`mul`), or the degree of the operand of an
    addition, subtraction, negation or doubling (`lin`). -/
inductive DegSrc where
  | fixed0
  | mul (a b : Nat)
  | lin (a : Nat)

/-- **The skeleton of a program**, mirroring `DegHint`: a binding with the identifier of its
    word when it is a word (`var`), a call with the identifier of its result when it is a
    field operation at the modulus (`call`), and the skeletons of the regions and
    continuations. -/
inductive DegSkel where
  | leaf
  | var (id : Option Nat) (k : DegSkel)
  | call (id : Option Nat) (k : DegSkel)
  | loop (body k : DegSkel)
  | branch (thn els k : DegSkel)

/-- **The facts of a scan**: the next identifier; the identifiers fixed at or used at a
    degree-`0` position; the operand pairs of the additions and subtractions; the operands
    of the multiplications and squarings with the loop depth of the use; and the definitions
    a hint can move, with their sources and loop depths. -/
structure ScanFacts where
  next : Nat
  zero : List Nat
  links : List (Nat × Nat)
  muls : List (Nat × Nat)
  defs : List (Nat × DegSrc × Nat)

namespace ScanFacts

/-- `n` fresh identifiers, in order. -/
def fresh (F : ScanFacts) (n : Nat) : List Nat × ScanFacts :=
  (List.range' F.next n, { F with next := F.next + n })

/-- `n` fresh identifiers fixed at degree `0`. -/
def freshZero (F : ScanFacts) (n : Nat) : List Nat × ScanFacts :=
  let (is, F) := F.fresh n
  (is, { F with zero := is ++ F.zero })

/-- The identifiers `is` at a degree-`0` position. -/
def esc (F : ScanFacts) (is : List Nat) : ScanFacts :=
  { F with zero := is ++ F.zero }

/-- A fresh identifier for a definition of source `src` at the loop depth `dep`. -/
def freshDef (F : ScanFacts) (src : DegSrc) (dep : Nat) : Nat × ScanFacts :=
  (F.next, { F with next := F.next + 1, defs := (F.next, src, dep) :: F.defs })

/-- The operands of a definition of source `src` at the loop depth `dep`: the operands of a
    product are recorded with the depth, the operand pair `link` of an addition or a
    subtraction as a link. -/
def useSrc (F : ScanFacts) (src : DegSrc) (link : Option (Nat × Nat)) (dep : Nat) :
    ScanFacts :=
  let ms := match src with
    | .mul a b => if a = b then [(a, dep)] else [(a, dep), (b, dep)]
    | _ => []
  { F with muls := ms ++ F.muls, links := link.toList ++ F.links }

end ScanFacts

/-- The de Bruijn index of a variable. -/
def varIx {Γ : Ctxt jasminDialect} {t : JasminTy} : Var Γ t → Nat
  | .here => 0
  | .there v => varIx v + 1

/-- The identifiers of the variables of a vector, under the identifiers `env` of the
    context. -/
def argIds (env : List Nat) {Γ : Ctxt jasminDialect} :
    {ts : List JasminTy} → HVector (fun t => Var Γ t) ts → List Nat
  | [], .nil => []
  | _ :: _, .cons v vs => env.getD (varIx v) 0 :: argIds env vs

/-- **The classification of a call** at the modulus `p` on the operand identifiers `ids`,
    as `callArm` reads it: the source of the result of a field operation at `p` with word
    operands and one word result, together with the pair of operands of an addition or a
    subtraction; `none` for every other call. -/
def fieldSrc (p : Nat) (f : String) (as rs : List JasminTy) (ids : List Nat) :
    Option (DegSrc × Option (Nat × Nat)) :=
  match fieldTag? f, ids with
  | some (m, q), [a, b] =>
      if q = p ∧ m.binary = true ∧ as = [w64, w64] ∧ rs = [w64] then
        if m = .mul then some (.mul a b, none) else some (.lin a, some (a, b))
      else none
  | some (m, q), [a] =>
      if q = p ∧ m.binary = false ∧ as = [w64] ∧ rs = [w64] then
        if m = .square then some (.mul a a, none) else some (.lin a, none)
      else none
  | _, _ => none

/-- **The scan** of a program at the modulus `p` and the loop depth `dep` under the
    identifiers `env` of its context: its skeleton and the facts of its definitions and uses.
    Identifiers are allocated in the order of the definitions, so the operands of a
    definition have smaller identifiers. -/
def degScan (p : Nat) : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Nat → List Nat → ScanFacts → DegSkel × ScanFacts
  | _, _, .ret vs, _, env, F => (.leaf, F.esc (argIds env vs))
  | _, _, .var (t := t) e k, dep, env, F =>
      let F := F.esc (argIds env e.args)
      if t = w64 then
        let (i, F) := F.freshDef .fixed0 dep
        let (sk, F) := degScan p k dep (i :: env) F
        (.var (some i) sk, F)
      else
        let (is, F) := F.freshZero 1
        let (sk, F) := degScan p k dep (is ++ env) F
        (.var none sk, F)
  | _, _, .forLoop (cs := cs) count inits body k, dep, env, F =>
      let F := F.esc (argIds env (.cons count .nil) ++ argIds env inits)
      let (carried, F) := F.freshZero (cs.length + 1)
      let (sb, F) := degScan p body (dep + 1) (carried ++ env) F
      let (res, F) := F.freshZero cs.length
      let (sk, F) := degScan p k dep (res ++ env) F
      (.loop sb sk, F)
  | _, _, .ifThenElse (rs := rs) cond thn els k, dep, env, F =>
      let F := F.esc (argIds env (.cons cond .nil))
      let (st, F) := degScan p thn dep env F
      let (se, F) := degScan p els dep env F
      let (res, F) := F.freshZero rs.length
      let (sk, F) := degScan p k dep (res ++ env) F
      (.branch st se sk, F)
  | _, _, .whileLoop (cs := cs) inits body k, dep, env, F =>
      let F := F.esc (argIds env inits)
      let (carried, F) := F.freshZero cs.length
      let (sb, F) := degScan p body (dep + 1) (carried ++ env) F
      let (res, F) := F.freshZero cs.length
      let (sk, F) := degScan p k dep (res ++ env) F
      (.loop sb sk, F)
  | _, _, .call (as := as) (rs := rs) f args k, dep, env, F =>
      let ids := argIds env args
      match fieldSrc p f as rs ids with
      | some (src, link) =>
          let F := F.useSrc src link dep
          let (i, F) := F.freshDef src dep
          let (sk, F) := degScan p k dep (i :: env) F
          (.call (some i) sk, F)
      | none =>
          let F := F.esc ids
          let (res, F) := F.freshZero rs.length
          let (sk, F) := degScan p k dep (res ++ env) F
          (.call none sk, F)

/-! ## 2. The degree-`0` set and the assignment -/

/-- The neighbours of every identifier below `n` along the operand pairs `links`. -/
def linkAdj (n : Nat) (links : List (Nat × Nat)) : Array (List Nat) :=
  links.foldl (fun A ab => (A.modify ab.1 (ab.2 :: ·)).modify ab.2 (ab.1 :: ·))
    (Array.replicate n [])

/-- The worklist search of the closure: each identifier taken from the list marks its
    unmarked neighbours and adds them to the list. -/
def closeWork (adj : Array (List Nat)) : Nat → List Nat → Array Bool → Array Bool
  | 0, _, Z => Z
  | _ + 1, [], Z => Z
  | n + 1, i :: w, Z =>
      let step := fun (wz : List Nat × Array Bool) (j : Nat) =>
        if wz.2.getD j true then wz else (j :: wz.1, wz.2.setIfInBounds j true)
      let (w', Z') := (adj.getD i []).foldl step (w, Z)
      closeWork adj n w' Z'

/-- The indicator of the identifiers `is` among the identifiers below `n`. -/
def markAll (n : Nat) (is : List Nat) : Array Bool :=
  is.foldl (fun Z i => Z.setIfInBounds i true) (Array.replicate n false)

/-- **The degree-`0` set**: the closure of the identifiers fixed or used at degree `0` under
    the operand pairs of the additions and subtractions. -/
def zeroClosure (F : ScanFacts) : Array Bool :=
  closeWork (linkAdj F.next F.links) (F.zero.length + F.next + 1) F.zero
    (markAll F.next F.zero)

/-- The definitions a hint can move, by identifier below `n`: their sources and loop
    depths. -/
def defTable (n : Nat) (defs : List (Nat × DegSrc × Nat)) : Array (Option (DegSrc × Nat)) :=
  defs.foldl (fun A d => A.setIfInBounds d.1 (some d.2)) (Array.replicate n none)

/-- The loop depth of the definition `i`; `0` for a definition no hint can move. -/
def defDepth (T : Array (Option (DegSrc × Nat))) (i : Nat) : Nat :=
  match T.getD i none with
  | some (_, d) => d
  | none => 0

/-- **The definitions converted to degree `1`**: those, outside the degree-`0` set `Z`, that
    feed a multiplication at a greater loop depth than their own (the conversion is hoisted
    out of the loop) or feed at least two multiplications (one conversion serves several
    products). -/
def seedSet (n : Nat) (T : Array (Option (DegSrc × Nat))) (Z : Array Bool)
    (muls : List (Nat × Nat)) : Array Bool :=
  let step := fun (acc : Array Nat × Array Bool) (m : Nat × Nat) =>
    let c := acc.1.getD m.1 0 + 1
    let hoist := (T.getD m.1 none).isSome && decide (defDepth T m.1 < m.2)
    (acc.1.setIfInBounds m.1 c,
      if (hoist || decide (2 ≤ c)) && !(Z.getD m.1 true) && (T.getD m.1 none).isSome then
        acc.2.setIfInBounds m.1 true
      else acc.2)
  (muls.reverse.foldl step (Array.replicate n 0, Array.replicate n false)).2

/-- The degree a definition of source `src` produces from the degrees `D` of its operands;
    a product of two degree-`0` operands is kept as the field multiplication, at degree
    `0`. -/
def srcDeg (D : Array ℤ) : DegSrc → ℤ
  | .fixed0 => 0
  | .mul a b =>
      if D.getD a 0 = 0 ∧ D.getD b 0 = 0 then 0 else D.getD a 0 + D.getD b 0 - 1
  | .lin a => D.getD a 0

/-- The degree the definition `i` produces from the degrees `D` of the earlier
    definitions. -/
def natDeg (T : Array (Option (DegSrc × Nat))) (D : Array ℤ) (i : Nat) : ℤ :=
  match T.getD i none with
  | some (src, _) => srcDeg D src
  | none => 0

/-- **The degrees of all definitions** in the order of their identifiers: `0` on the set
    `F0`, `1` on the set `F1`, and otherwise the degree the definition produces. -/
def degsOf (n : Nat) (T : Array (Option (DegSrc × Nat))) (F0 F1 : Array Bool) : Array ℤ :=
  (List.range n).foldl
    (fun D i => D.push (if F0.getD i true then 0 else if F1.getD i false then 1
      else natDeg T D i))
    #[]

/-- **One round of the repair of the additions and subtractions**: for each operand pair of
    different degrees, the definition at degree `1` is moved to degree `0`, unless moving the
    other definition to degree `1` costs less; a move costs nothing when the definition
    produces the target degree, and otherwise one conversion at the loop depth of the
    definition. `none` when every pair has one degree. -/
def repairRound (n : Nat) (T : Array (Option (DegSrc × Nat))) (links : List (Nat × Nat))
    (F0 F1 : Array Bool) : Option (Array Bool × Array Bool) :=
  let D := degsOf n T F0 F1
  let cost := fun (i : Nat) (target : ℤ) =>
    if natDeg T D i = target then 0 else defDepth T i + 1
  let step := fun (acc : Bool × Array Bool × Array Bool) (ab : Nat × Nat) =>
    let (_, G0, G1) := acc
    if D.getD ab.1 0 = D.getD ab.2 0 then acc
    else
      let (hi, lo) := if D.getD ab.1 0 = 1 then (ab.1, ab.2) else (ab.2, ab.1)
      if !(G0.getD lo true) && (T.getD lo none).isSome && cost lo 1 < cost hi 0 then
        (true, G0, G1.setIfInBounds lo true)
      else (true, G0.setIfInBounds hi true, G1)
  let (changed, G0, G1) := links.foldl step (false, F0, F1)
  if changed then some (G0, G1) else none

/-- The sets at degree `0` and at degree `1` after the repair rounds, until every operand
    pair has one degree, within the fuel. -/
def repairSets (n : Nat) (T : Array (Option (DegSrc × Nat))) (links : List (Nat × Nat)) :
    Nat → Array Bool → Array Bool → Array Bool × Array Bool
  | 0, F0, F1 => (F0, F1)
  | fuel + 1, F0, F1 =>
      match repairRound n T links F0 F1 with
      | some (G0, G1) => repairSets n T links fuel G0 G1
      | none => (F0, F1)

/-- The degrees of the definitions after the repair rounds, within the fuel. -/
def repair (n : Nat) (T : Array (Option (DegSrc × Nat))) (links : List (Nat × Nat))
    (fuel : Nat) (F0 F1 : Array Bool) : Array ℤ :=
  let G := repairSets n T links fuel F0 F1
  degsOf n T G.1 G.2

/-- **The operands converted for the remaining field multiplications.** At the degrees `D`,
    a product of two distinct operands at degree `0` with its result at degree `0` is the
    field multiplication; for each such product, in the order of the identifiers, one operand
    outside the set `F0` that a hint can move is put at degree `1`, so the product becomes the
    reduce-multiply with its result at degree `0`. Of two such operands the one at the smaller
    loop depth is converted, the first on a tie; a product with an operand already put at
    degree `1` is skipped. -/
def pairSeeds (n : Nat) (T : Array (Option (DegSrc × Nat))) (D : Array ℤ)
    (F0 F1 : Array Bool) : Array Bool :=
  let movable := fun (c : Nat) => !(F0.getD c true) && (T.getD c none).isSome
  (List.range n).foldl
    (fun G1 i =>
      match T.getD i none with
      | some (.mul a b, _) =>
          if a ≠ b ∧ D.getD i 0 = 0 ∧ D.getD a 0 = 0 ∧ D.getD b 0 = 0 ∧
              G1.getD a false = false ∧ G1.getD b false = false then
            if movable a && movable b then
              G1.setIfInBounds (if defDepth T b < defDepth T a then b else a) true
            else if movable a then G1.setIfInBounds a true
            else if movable b then G1.setIfInBounds b true
            else G1
          else G1
      | _ => G1)
    F1

/-- **The assignment of a skeleton** at the degrees `D` of the definitions. -/
def skelHint (D : Array ℤ) : DegSkel → DegHint
  | .leaf => .leaf
  | .var none k => .var 0 (skelHint D k)
  | .var (some i) k => .var (D.getD i 0) (skelHint D k)
  | .call none k => .call 0 (skelHint D k)
  | .call (some i) k => .call (D.getD i 0) (skelHint D k)
  | .loop b k => .loop (skelHint D b) (skelHint D k)
  | .branch t e k => .branch (skelHint D t) (skelHint D e) (skelHint D k)

/-- **The degree analysis** at the modulus `p`: the degrees of the parameters, by index, and the
    degree assignment of the program. A word parameter is a definition at loop depth `0` that
    produces degree `0`, and every other parameter is fixed at degree `0`; the program is
    scanned; the degree-`0` set is closed under the operand pairs of the additions and
    subtractions; the definitions of `seedSet` are put at degree `1`, so a word parameter that
    feeds a multiplication inside a loop is converted once at entry; every other definition
    keeps the degree it produces; the operand pairs are repaired until they have one degree;
    one operand of each remaining product of two degree-`0` operands is put at degree `1`
    (`pairSeeds`); and the operand pairs are repaired again. -/
def degHint (p : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) : List ℤ × DegHint :=
  let n := Γ.length
  let F : ScanFacts :=
    { next := n, zero := (List.range n).filter fun i => (wordAt? Γ i).isNone, links := [],
      muls := [],
      defs := ((List.range n).filter fun i => (wordAt? Γ i).isSome).map fun i => (i, .fixed0, 0) }
  let (sk, F) := degScan p prog 0 (List.range n) F
  let T := defTable F.next F.defs
  let Z := zeroClosure F
  let fuel := 2 * F.next + 2
  let G := repairSets F.next T F.links fuel Z (seedSet F.next T Z F.muls)
  let D := repair F.next T F.links fuel G.1
    (pairSeeds F.next T (degsOf F.next T G.1 G.2) G.1 G.2)
  ((List.range n).map fun i => D.getD i 0, skelHint D sk)

/-! ## 3. The all-zero assignment -/

/-- **The program calls no reduce-multiply head.** -/
def montFree : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var _ k => montFree k
  | _, _, .forLoop _ _ body k => montFree body && montFree k
  | _, _, .ifThenElse _ thn els k => montFree thn && montFree els && montFree k
  | _, _, .whileLoop _ body k => montFree body && montFree k
  | _, _, .call f _ k => (montTag? f).isNone && montFree k

/-- A renaming that reads every variable as itself. -/
def MRen.IsId {Γ : Ctxt jasminDialect} (ρ : MRen Γ Γ) : Prop :=
  ∀ {t : JasminTy} (v : Var Γ t), ρ v = .same v

theorem idRen_isId (Γ : Ctxt jasminDialect) : MRen.IsId (idRen Γ) := fun _ => rfl

theorem MRen.IsId.lift {Γ : Ctxt jasminDialect} {ρ : MRen Γ Γ} (hρ : ρ.IsId) (s : JasminTy) :
    MRen.IsId (Γ := s :: Γ) (MRen.lift ρ (fun w => .there w) (.same .here)) := by
  intro t v
  cases v with
  | here => rfl
  | there v => simp only [MRen.lift, hρ v, Rd.rename]

theorem MRen.IsId.app {Γ : Ctxt jasminDialect} {ρ : MRen Γ Γ} (hρ : ρ.IsId) :
    ∀ cs : List JasminTy, MRen.IsId (MRen.app ρ cs)
  | [] => hρ
  | s :: cs => MRen.IsId.lift (MRen.IsId.app hρ cs) s

theorem sameVars_isId {Γ : Ctxt jasminDialect} {ρ : MRen Γ Γ} (hρ : ρ.IsId) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts), sameVars ρ vs = some vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show ((ρ v).same?.bind fun w => (sameVars ρ vs).map (HVector.cons w)) = _
      rw [hρ v, sameVars_isId hρ vs]
      rfl

theorem renExpr_isId {Γ : Ctxt jasminDialect} {ρ : MRen Γ Γ} (hρ : ρ.IsId) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : renExpr ρ e = some e := by
  obtain ⟨op, rfl, args⟩ := e
  simp only [renExpr, sameVars_isId hρ, Option.map_some]

section Leaf

variable {p : Nat} (h : mont32Cert p = true)

theorem opaqueArm_some {Γ Θ : Ctxt jasminDialect} {f : String} {as rs us : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {kk : CallK Γ rs us}
    {q : NFProg jasminDialect Θ us} (hq : opaqueArm f args ρ kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen (rs ++ Γ) Θ') (q' : NFProg jasminDialect Θ' us),
      kk ρ' = some q' := by
  obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', _⟩ := Option.map_eq_some_iff.mp hq
  exact ⟨_, _, k', hk'⟩

theorem fieldRes_some {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {g : String}
    {as us : List JasminTy} {args : HVector (fun t => Var Θ t) as} {k d : ℤ}
    {kk : CallK Γ [w64] us} {q : NFProg jasminDialect Θ us}
    (hq : fieldRes h ρ g args k d kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen ([w64] ++ Γ) Θ') (q' : NFProg jasminDialect Θ' us),
      kk ρ' = some q' := by
  obtain ⟨q0, hq0, _⟩ := Option.map_eq_some_iff.mp hq
  unfold resConv at hq0
  split at hq0
  · exact ⟨_, _, q0, hq0⟩
  · obtain ⟨q', hq', _⟩ := Option.map_eq_some_iff.mp hq0
    exact ⟨_, _, q', hq'⟩

theorem binArm_some {Γ Θ : Ctxt jasminDialect} {f : String} {a b : Var Γ w64} {ρ : MRen Γ Θ}
    {d : ℤ} {us : List JasminTy} {kk : CallK Γ [w64] us} {q : NFProg jasminDialect Θ us}
    (hq : binArm h f a b ρ d kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen ([w64] ++ Γ) Θ') (q' : NFProg jasminDialect Θ' us),
      kk ρ' = some q' := by
  unfold binArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact fieldRes_some h hq
      · split at hq
        · exact fieldRes_some h hq
        · cases hq
    · exact opaqueArm_some hq
  · exact opaqueArm_some hq

theorem unArm_some {Γ Θ : Ctxt jasminDialect} {f : String} {a : Var Γ w64} {ρ : MRen Γ Θ}
    {d : ℤ} {us : List JasminTy} {kk : CallK Γ [w64] us} {q : NFProg jasminDialect Θ us}
    (hq : unArm h f a ρ d kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen ([w64] ++ Γ) Θ') (q' : NFProg jasminDialect Θ' us),
      kk ρ' = some q' := by
  unfold unArm at hq
  split at hq
  · split at hq
    · split at hq
      · exact fieldRes_some h hq
      · split at hq
        · exact fieldRes_some h hq
        · cases hq
    · exact opaqueArm_some hq
  · exact opaqueArm_some hq

/-- A binding the rewriter accepts runs its continuation at some renaming and reading. -/
theorem varConv_some {Θ : Ctxt jasminDialect} {d : ℤ} {us : List JasminTy} {t : JasminTy}
    {kk : BindK (t :: Θ) t us} {q : NFProg jasminDialect (t :: Θ) us}
    (hq : varConv h d kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (g : Ctxt.Hom (t :: Θ) Θ') (r : Rd Θ' t)
      (q' : NFProg jasminDialect Θ' us), kk g r = some q' := by
  unfold varConv at hq
  split at hq
  · exact ⟨_, _, _, q, hq⟩
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', _⟩ := Option.map_eq_some_iff.mp hq
        exact ⟨_, _, _, q', hq'⟩
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- A call the rewriter accepts runs its continuation at some renaming. -/
theorem callArm_some {Γ Θ : Ctxt jasminDialect} {f : String} {us as rs : List JasminTy}
    {args : HVector (fun t => Var Γ t) as} {ρ : MRen Γ Θ} {d : ℤ} {kk : CallK Γ rs us}
    {q : NFProg jasminDialect Θ us} (hq : callArm h f args ρ d kk = some q) :
    ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen (rs ++ Γ) Θ') (q' : NFProg jasminDialect Θ' us),
      kk ρ' = some q' := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    exact binArm_some h hq
  · split at hq
    · rename_i _ hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      exact unArm_some h hq
    · exact opaqueArm_some hq

/-- **A program the rewriter accepts at some assignment calls no reduce-multiply head.** -/
theorem montifyAux_montFree : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    (prog : NFProg jasminDialect Γ ts) → (H : DegHint) → {Θ : Ctxt jasminDialect} →
    (ρ : MRen Γ Θ) → (q : NFProg jasminDialect Θ ts) → montifyAux h prog H ρ = some q →
      montFree prog = true
  | _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, .var e k, H, _, ρ, q, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, _⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨_, _, _, q1, hq1⟩ := varConv_some h hq0
      exact montifyAux_montFree k _ _ _ hq1
  | _, _, .forLoop count inits body k, H, _, ρ, q, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', _⟩ := Option.map_eq_some_iff.mp hq
      simp only [montFree, montifyAux_montFree body _ _ _ hb', montifyAux_montFree k _ _ _ hk',
        Bool.and_self]
  | _, _, .ifThenElse cond thn els k, H, _, ρ, q, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', _⟩ := Option.map_eq_some_iff.mp hq
      simp only [montFree, montifyAux_montFree thn _ _ _ ht', montifyAux_montFree els _ _ _ he',
        montifyAux_montFree k _ _ _ hk', Bool.and_self]
  | _, _, .whileLoop inits body k, H, _, ρ, q, hq => by
      obtain ⟨_, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', _⟩ := Option.map_eq_some_iff.mp hq
      simp only [montFree, montifyAux_montFree body _ _ _ hb', montifyAux_montFree k _ _ _ hk',
        Bool.and_self]
  | _, _, .call f args k, H, _, ρ, q, hq => by
      unfold montifyAux at hq
      split at hq
      · cases hq
      · rename_i hf
        obtain ⟨_, ρ', q', hk⟩ := callArm_some h hq
        simp only [montFree, Option.isNone_iff_eq_none.mpr (Option.not_isSome_iff_eq_none.mp hf),
          montifyAux_montFree k _ ρ' q' hk, Bool.and_self]

theorem opaqueArm_leaf {Γ : Ctxt jasminDialect} {f : String} {as rs us : List JasminTy}
    (args : HVector (fun t => Var Γ t) as) {ρ : MRen Γ Γ} (hρ : ρ.IsId) {kk : CallK Γ rs us}
    {k : NFProg jasminDialect (rs ++ Γ) us}
    (hk : ∀ ρ' : MRen (rs ++ Γ) (rs ++ Γ), ρ'.IsId → kk ρ' = some k) :
    opaqueArm f args ρ kk = some (.call f args k) := by
  simp only [opaqueArm, sameVars_isId hρ, Option.bind_some, hk _ (hρ.app rs), Option.map_some]

theorem fieldRes_leaf {Γ : Ctxt jasminDialect} {ρ : MRen Γ Γ} (hρ : ρ.IsId) (g : String)
    {as us : List JasminTy} (args : HVector (fun t => Var Γ t) as) {kk : CallK Γ [w64] us}
    {k : NFProg jasminDialect ([w64] ++ Γ) us}
    (hk : ∀ ρ' : MRen ([w64] ++ Γ) ([w64] ++ Γ), ρ'.IsId → kk ρ' = some k) :
    fieldRes h ρ g args 0 0 kk = some (.call g args k) := by
  simp only [fieldRes, resConv, ite_true, resK, rdOf]
  rw [hk _ (hρ.lift w64)]
  rfl

theorem binArm_leaf {Γ : Ctxt jasminDialect} {f : String} (a b : Var Γ w64) {ρ : MRen Γ Γ}
    (hρ : ρ.IsId) {us : List JasminTy} {kk : CallK Γ [w64] us}
    {k : NFProg jasminDialect ([w64] ++ Γ) us}
    (hk : ∀ ρ' : MRen ([w64] ++ Γ) ([w64] ++ Γ), ρ'.IsId → kk ρ' = some k) :
    binArm h f a b ρ 0 kk = some (.call f (.cons a (.cons b .nil)) k) := by
  unfold binArm
  split
  · split
    · rw [ite_eq_right (by simp [hρ a, hρ b, Rd.deg]), ite_eq_left (by simp [hρ a, hρ b, Rd.deg])]
      have e := fieldRes_leaf h hρ f (.cons (ρ a).var (.cons (ρ b).var .nil)) hk
      simpa only [hρ a, hρ b, Rd.var, Rd.deg] using e
    · exact opaqueArm_leaf _ hρ hk
  · exact opaqueArm_leaf _ hρ hk

theorem unArm_leaf {Γ : Ctxt jasminDialect} {f : String} (a : Var Γ w64) {ρ : MRen Γ Γ}
    (hρ : ρ.IsId) {us : List JasminTy} {kk : CallK Γ [w64] us}
    {k : NFProg jasminDialect ([w64] ++ Γ) us}
    (hk : ∀ ρ' : MRen ([w64] ++ Γ) ([w64] ++ Γ), ρ'.IsId → kk ρ' = some k) :
    unArm h f a ρ 0 kk = some (.call f (.cons a .nil) k) := by
  unfold unArm
  split
  · split
    · rw [ite_eq_right (by simp [hρ a, Rd.deg]), ite_eq_left (by simp [hρ a, Rd.deg])]
      have e := fieldRes_leaf h hρ f (.cons (ρ a).var .nil) hk
      simpa only [hρ a, Rd.var, Rd.deg] using e
    · exact opaqueArm_leaf _ hρ hk
  · exact opaqueArm_leaf _ hρ hk

theorem callArm_leaf {Γ : Ctxt jasminDialect} {f : String} {us as rs : List JasminTy}
    (args : HVector (fun t => Var Γ t) as) {ρ : MRen Γ Γ} (hρ : ρ.IsId) {kk : CallK Γ rs us}
    {k : NFProg jasminDialect (rs ++ Γ) us}
    (hk : ∀ ρ' : MRen (rs ++ Γ) (rs ++ Γ), ρ'.IsId → kk ρ' = some k) :
    callArm h f args ρ 0 kk = some (.call f args k) := by
  unfold callArm
  split
  · rename_i hs
    obtain ⟨h1, h2⟩ := hs
    subst h1 h2
    cases args with
    | cons a args =>
      cases args with
      | cons b args =>
        cases args
        exact binArm_leaf h a b hρ hk
  · split
    · rename_i _ hs
      obtain ⟨h1, h2⟩ := hs
      subst h1 h2
      cases args with
      | cons a args =>
        cases args
        exact unArm_leaf h a hρ hk
    · exact opaqueArm_leaf args hρ hk

/-- **At the all-zero assignment the rewriter keeps a program** that calls no reduce-multiply
    head, at every renaming that reads each variable as itself. -/
theorem montifyAux_leaf : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    (prog : NFProg jasminDialect Γ ts) → montFree prog = true → (ρ : MRen Γ Γ) → ρ.IsId →
      montifyAux h prog .leaf ρ = some prog
  | _, _, .ret vs, _, ρ, hρ => by
      simp only [montifyAux, sameVars_isId hρ, Option.map_some]
  | _, _, .var e k, hf, ρ, hρ => by
      have hk := montifyAux_leaf k hf
      simp only [montifyAux, renExpr_isId hρ, Option.bind_some, varConv, DegHint.deg, ite_true,
        DegHint.next]
      rw [hk _ (hρ.lift _)]
      rfl
  | _, _, .forLoop (cs := cs) count inits body k, hf, ρ, hρ => by
      simp only [montFree, Bool.and_eq_true] at hf
      simp only [montifyAux, hρ count, Rd.same?, Option.bind_some, sameVars_isId hρ,
        DegHint.sub1, DegHint.next, montifyAux_leaf body hf.1 _ (MRen.IsId.app (hρ.lift _) cs),
        montifyAux_leaf k hf.2 _ (hρ.app cs), Option.map_some]
  | _, _, .ifThenElse (rs := rs) cond thn els k, hf, ρ, hρ => by
      simp only [montFree, Bool.and_eq_true] at hf
      simp only [montifyAux, hρ cond, Rd.same?, Option.bind_some, DegHint.sub1, DegHint.sub2,
        DegHint.next, montifyAux_leaf thn hf.1.1 _ hρ, montifyAux_leaf els hf.1.2 _ hρ,
        montifyAux_leaf k hf.2 _ (hρ.app rs), Option.map_some]
  | _, _, .whileLoop (cs := cs) inits body k, hf, ρ, hρ => by
      simp only [montFree, Bool.and_eq_true] at hf
      simp only [montifyAux, sameVars_isId hρ, Option.bind_some, DegHint.sub1, DegHint.next,
        montifyAux_leaf body hf.1 _ (hρ.app cs), montifyAux_leaf k hf.2 _ (hρ.app cs),
        Option.map_some]
  | _, _, .call f args k, hf, ρ, hρ => by
      simp only [montFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hf
      unfold montifyAux
      rw [ite_eq_right (by simp [hf.1])]
      exact callArm_leaf h args hρ fun ρ' hρ' => montifyAux_leaf k hf.2 ρ' hρ'

/-- **The all-zero assignment keeps the program**: when `montTag?` reads the head
    `montHead p` at `p`, `montify` at no parameter degree and `DegHint.leaf` returns a program
    that calls no reduce-multiply head unchanged. -/
theorem montify_leaf (hm : montTag? (montHead p) = some p) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (hf : montFree prog = true) :
    montify h [] .leaf prog = some prog := by
  simp only [montify, hm, ite_true, paramDegs_nil, entryConv_nil]
  exact montifyAux_leaf h prog hf _ (idRen_isId Γ)

/-- **Every program the rewriter accepts is kept at the all-zero assignment.** -/
theorem montify_leaf_of_some (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog q : NFProg jasminDialect Γ ts)
    (hq : montify h pd H prog = some q) :
    montify h [] .leaf prog = some prog := by
  unfold montify at hq
  split at hq
  · rename_i hm
    obtain ⟨_, ρ', q', hq'⟩ := entryConv_some h _ _ _ q hq
    exact montify_leaf h hm prog (montifyAux_montFree h prog H _ q' hq')
  · cases hq

/-- **The certificate accepts the all-zero assignment** on every program it accepts at some
    assignment. -/
theorem montifyCert_leaf (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hc : montifyCert h pd H prog = true) :
    montifyCert h [] .leaf prog = true := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hc
  simp only [montifyCert, montify_leaf_of_some h pd H prog q hq, Option.isSome_some]

/-- **The certificate at the all-zero assignment** holds exactly when `montTag?` reads the
    head `montHead p` at `p` and the program calls no reduce-multiply head. -/
theorem montifyCert_leaf_iff {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) :
    montifyCert h [] .leaf prog = true ↔
      montTag? (montHead p) = some p ∧ montFree prog = true := by
  constructor
  · intro hc
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hc
    unfold montify at hq
    split at hq
    · rename_i hm
      rw [paramDegs_nil, entryConv_nil] at hq
      exact ⟨hm, montifyAux_montFree h prog _ _ q hq⟩
    · cases hq
  · rintro ⟨hm, hf⟩
    simp only [montifyCert, montify_leaf h hm prog hf, Option.isSome_some]

end Leaf

/-! ## 4. The montify step -/

section Step

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

/-- A symbol a program that passes `montFree` calls is no reduce-multiply head. -/
theorem montTag?_of_montFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : montFree p = true) {f : String}
    {as rs : List JasminTy} (hc : p.Calls f as rs) : montTag? f = none := by
  induction p with
  | ret => exact hc.elim
  | var e k ih => exact ih hp hc
  | forLoop _ _ _ _ ihb ihk =>
      simp only [montFree, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [montFree, Bool.and_eq_true] at hp
      rcases hc with h | h | h
      exacts [iht hp.1.1 h, ihe hp.1.2 h, ihk hp.2 h]
  | whileLoop _ _ _ ihb ihk =>
      simp only [montFree, Bool.and_eq_true] at hp
      rcases hc with h | h
      exacts [ihb hp.1 h, ihk hp.2 h]
  | call g _ k ih =>
      simp only [montFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      rcases hc with ⟨rfl, -, -⟩ | h
      exacts [hp.1, ih hp.2 h]

/-- The moduli of the tagged field calls of a program, in the order of the calls. -/
def fieldMods : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → List Nat
  | _, _, .ret _ => []
  | _, _, .var _ k => fieldMods k
  | _, _, .forLoop _ _ body k => fieldMods body ++ fieldMods k
  | _, _, .ifThenElse _ thn els k => fieldMods thn ++ fieldMods els ++ fieldMods k
  | _, _, .whileLoop _ body k => fieldMods body ++ fieldMods k
  | _, _, .call f _ k => ((fieldTag? f).map Prod.snd).toList ++ fieldMods k

/-- A program without `call` has no tagged field call. -/
theorem fieldMods_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) : fieldMods p = [] := by
  induction p with
  | ret => rfl
  | var e k ih => exact ih hp
  | forLoop _ _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldMods, ihb hp.1, ihk hp.2, List.append_nil]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldMods, iht hp.1.1, ihe hp.1.2, ihk hp.2, List.append_nil]
  | whileLoop _ _ _ ihb ihk =>
      simp only [NFProg.callFree, Bool.and_eq_true] at hp
      simp only [fieldMods, ihb hp.1, ihk hp.2, List.append_nil]
  | call _ _ _ _ => simp [NFProg.callFree] at hp

/-- **The montify round at a modulus `p` with `mont32Cert p`**: the rewriter `montify` at the
    analysis `degHint p prog`, then the inlining of the reduce-multiply heads at the library
    `montLibJ`. The program itself when the rewriter refuses the analysis, the inlining
    refuses, or a reduce-multiply call remains. -/
def montifyAt {p : Nat} (h : mont32Cert p = true) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ ts :=
  match montify h (degHint p prog).1 (degHint p prog).2 prog with
  | some q =>
      match NFProg.inline? montLibJ q with
      | some q' => if montFree q' then q' else prog
      | none => prog
  | none => prog

/-- The montify rounds at the moduli `ps`, in order, at each modulus that passes
    `mont32Cert`. -/
def montifyMods {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    List Nat → NFProg jasminDialect Γ ts → NFProg jasminDialect Γ ts
  | [], prog => prog
  | p :: ps, prog =>
      montifyMods ps (if h : mont32Cert p = true then montifyAt h prog else prog)

/-- **The montify pass**: the montify rounds at the moduli of the tagged field calls of the
    program. -/
def montifyPass {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) : NFProg jasminDialect Γ ts :=
  montifyMods (fieldMods prog).eraseDups prog

section Leak

variable (M : LeakModel jasminDialect) (hA : ∀ bop w, M.kind (.regArith bop w) = .quiet)
  (hK : ∀ w n, M.kind (.regConst w n) = .quiet) (E : CallEnv jasminDialect) (fuel : Nat)
include hA hK

/-- **A montify round keeps the results and the events.** A leakage run at `fieldEnv E` of a
    program is a leakage run of the program `montifyAt` returns, at a leakage model whose
    register arithmetic and register constants are quiet: the rewriter keeps the run at
    `montEnv (fieldEnv E)` (`montify_leakSound`), the inlining keeps it
    (`montLibJ_leakSound`), and the result calls no reduce-multiply head, at which alone
    `montEnv (fieldEnv E)` and `fieldEnv E` differ. -/
theorem montifyAt_leak {p : Nat} (h : mont32Cert p = true) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ)
    (r : Valuation (d := jasminDialect) ts × List CTLeak)
    (hr : Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel prog X = some r) :
    Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel (montifyAt h prog) X = some r := by
  unfold montifyAt
  split
  · rename_i q hq
    split
    · rename_i q' hq'
      split
      · rename_i hmf
        have h1 := montify_leakSound h M hK E fuel _ _ prog q hq X r hr
        have h2 := VIR.NFProg.leakRunMC_inline? M (montEnv (fieldEnv E))
          (montLibJ_leakSound M hA hK (fieldEnv E) fuel) q hq' h1
        rw [Dialects.NFLeak.NFProg.leakRunMC_congr M q' (montEnv (fieldEnv E)) (fieldEnv E)
          (fun f as rs x hc => montEnv_of_none _ (montTag?_of_montFree q' hmf hc) as rs x)]
          at h2
        exact h2
      · exact hr
    · exact hr
  · exact hr

/-- The montify rounds at a list of moduli keep the results and the events. -/
theorem montifyMods_leak {Γ : Ctxt jasminDialect} {ts : List JasminTy} :
    ∀ (ps : List Nat) (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ)
      (r : Valuation (d := jasminDialect) ts × List CTLeak),
      Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel prog X = some r →
      Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel (montifyMods ps prog) X = some r
  | [], _, _, _, hr => hr
  | p :: ps, prog, X, r, hr => by
      refine montifyMods_leak ps _ X r ?_
      split
      · rename_i h
        exact montifyAt_leak M hA hK E fuel h prog X r hr
      · exact hr

/-- **The montify pass keeps the results and the events** of every leakage run at
    `fieldEnv E`, at a leakage model whose register arithmetic and register constants are
    quiet. -/
theorem montifyPass_leak {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ)
    (r : Valuation (d := jasminDialect) ts × List CTLeak)
    (hr : Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel prog X = some r) :
    Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel (montifyPass prog) X = some r :=
  montifyMods_leak M hA hK E fuel _ prog X r hr

end Leak

/-- **The montify pass keeps the results** of every run at `fieldEnv E`: `montifyPass_leak`
    at the leakage model `quietModel`. -/
theorem montifyPass_denoteAt (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (X : Valuation Γ)
    (R : Valuation (d := jasminDialect) ts)
    (hR : prog.denoteAt (fieldEnv E) fuel X = some R) :
    (montifyPass prog).denoteAt (fieldEnv E) fuel X = some R := by
  rw [← Dialects.NFLeak.NFProg.leakRunMC_fst quietModel] at hR ⊢
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hR
  rw [montifyPass_leak quietModel (fun _ _ => rfl) (fun _ _ => rfl) E fuel prog X r hr,
    Option.map_some]

/-- **The montify pass keeps a program without `call`.** -/
theorem montifyPass_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) (hp : prog.callFree = true) : montifyPass prog = prog := by
  simp only [montifyPass, fieldMods_of_callFree prog hp]
  rfl

/-- **The montify pass as a chain step.** It never refuses. -/
def montifyStep (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    Step (NFProg jasminDialect Γ ts) (NFProg jasminDialect Γ ts) :=
  ⟨"montify", fun p => some (montifyPass p)⟩

/-- **The certificate of the montify step** at the semantics at `fieldEnv E`, with equal inputs
    and outputs (`montifyPass_denoteAt`). -/
def montifyStepCert (E : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    StepCert (montifyStep Γ ts).run (nfSemE (fieldEnv E) fuel Γ ts)
      (nfSemE (fieldEnv E) fuel Γ ts) where
  relIn V W := W = V
  relOut o o' := o' = o
  sound := by
    rintro p q V W o hf rfl hd
    obtain rfl : montifyPass p = q := Option.some.inj hf
    exact ⟨o, montifyPass_denoteAt E fuel p _ o hd, rfl⟩

/-- **A leakage run before the montify step is a leakage run of its result**, at a leakage
    model whose register arithmetic and register constants are quiet. -/
theorem montifyStep_leakRunC (M : LeakModel jasminDialect)
    (hA : ∀ bop w, M.kind (.regArith bop w) = .quiet)
    (hK : ∀ w n, M.kind (.regConst w n) = .quiet) (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} {p q : NFProg jasminDialect Γ ts}
    (hf : (montifyStep Γ ts).run p = some q) {V : Valuation Γ}
    {r : Valuation (d := jasminDialect) ts × List CTLeak}
    (hr : Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel p V = some r) :
    Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel q V = some r := by
  obtain rfl : montifyPass p = q := Option.some.inj hf
  exact montifyPass_leak M hA hK E fuel p V r hr

/-- **The montify step keeps a program without `call`.** -/
theorem montifyStep_of_callFree {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) :
    (montifyStep Γ ts).run p = some p :=
  congrArg some (montifyPass_of_callFree p hp)

end Step

end CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
