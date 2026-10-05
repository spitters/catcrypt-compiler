/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.Ascent.Coverage
public import HaxAscent.RustSemantics.ToRustMS
public meta import Lean

/-!
# The `RustM` corollary of the ascent

`ascendRustM ns fs` runs after `Hax.Ascent.Gen.ascendExtraction ns` and, for each
function `f` of `fs` whose correspondence `Ns.HaxGen.f.corres_full : FnCorres bi e entry G
gen` was proved, declares the `RustM` reading of its literal as a corollary:

* `Ns.HaxGen.f.rustM` — `fnCorres_toRustM` at the width of the literal: for every argument
  tuple `a` with `G a`, every Aeneas environment related by the encoding to the runtime
  environment `ρI a`, and every value `r` that `toRustM ty e` returns there, the run of the
  literal returns `.int (enc r)` from some fuel on;
* `Ns.HaxGen.f.rustM_total` — `toRustM_isOk_of_totalOk`: the reading returns a value on
  every Aeneas environment that binds the parameters and the globals of `f`, declared when
  the literal passes `totalOk`.

The runtime environment `ρI a` binds each parameter to its component of `a` and each global
`g` to `Ns.HaxGen.g.gen ()`. The only per-function proof obligation of `rustM` is the
equation `runWord ty.numBits e (ρI a) = gen a`, closed by `rfl`; the width `ty` is the
unique width tag of the literal's operation names, and a literal with no tag or with two
widths gets no corollary.

A function is reported `rustM` (with `total` when `rustM_total` is declared) or with the
first word of the reason it has no corollary: `early:` (the correspondence is for an early
return), `type:` (a parameter, a global or the result is not an `Int`), `width:`, or
`bridge:` (the equation is not closed by `rfl`).

`rustMSFn` declares the state-passing corollary
(`HaxAscent/RustSemantics/ToRustMS.lean`) for every function whose correspondence is
stated over the table `extBuiltins T fns` of the extraction:

* `Ns.HaxGen.f.rustMS` — `fnCorres_toRustMS` with the reading of calls `appExt fns`: for
  every argument tuple `a` with `G a`, every environment `ρ` whose encoding is `entry a`,
  and every value `v` that `toRustMS (appExt fns) e ρ` returns, `v.toValue = enc (gen a)`.

It has no per-function proof obligation beyond two Boolean checks the kernel decides: the
literal is in the fragment `toRustMS` reads (`fragOk`, over the names of `fns`), and the
names of `fns` are free in the runtime table and in `T` (`ExtNamesOk`). It is reported
`rustMS`, or `early:`, `table:` or `fragment:`. Arrays, tuples, counted loops, casts
between widths and calls to the functions of the extraction are in the fragment.

## Main results

* `ascendRustM`: declares `Ns.HaxGen.f.rustM` and `Ns.HaxGen.f.rustM_total` for each
  proved function in the word fragment, and `Ns.HaxGen.f.rustMS` for each proved function
  in the fragment of `toRustMS`.
* `hax_ascend_rustm`: the command running the ascent generator and then `ascendRustM`.

`hax_ascend_rustm Ns` runs the generator and then `ascendRustM` on every proved function,
and reports the count.
-/

@[expose] public section

meta section

open Lean Meta Elab
open Lean.Elab.Term (TermElabM)

namespace CatCrypt.Hax.RustSemantics.AscendRustM

open Hax.Ascent.Gen (FnReport addThm budgeted)

/-- The string literals of an expression. -/
partial def strLits (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .lit (.strVal s) => acc.push s
  | .app f a => strLits a (strLits f acc)
  | .lam _ t b _ | .forallE _ t b _ => strLits b (strLits t acc)
  | .letE _ t v b _ => strLits b (strLits v (strLits t acc))
  | .mdata _ b | .proj _ _ b => strLits b acc
  | _ => acc

/-- The widths of the tagged operation names `op#w` among `names`. -/
def tagWidths (names : Array String) : List Nat := Id.run do
  let mut ws : List Nat := []
  for s in names do
    match s.splitOn "#" with
    | [_, t] =>
      if let some w := t.toNat? then
        unless ws.contains w do ws := w :: ws
    | _ => pure ()
  return ws

/-- The unsigned scalar type of a width. -/
def uTyOf? : Nat → Option Name
  | 8 => some ``Aeneas.Std.UScalarTy.U8
  | 16 => some ``Aeneas.Std.UScalarTy.U16
  | 32 => some ``Aeneas.Std.UScalarTy.U32
  | 64 => some ``Aeneas.Std.UScalarTy.U64
  | 128 => some ``Aeneas.Std.UScalarTy.U128
  | _ => none

/-- The strings of a list literal. -/
def strList? (e : Expr) : MetaM (Option (List String)) := do
  let e ← whnfR e
  let some (_, xs) := e.listLit? | return none
  let mut out : List String := []
  for x in xs do
    match (← whnfR x) with
    | .lit (.strVal s) => out := out ++ [s]
    | _ => return none
  return some out

/-- The environment `updEnv (… (updEnv base k₁ v₁) …) kₙ vₙ`: later pairs shadow earlier
    ones. -/
def mkUpdEnv (base : Expr) (kvs : List (String × Expr)) : MetaM Expr :=
  kvs.foldlM (fun ρ (k, v) =>
    mkAppM ``CatCrypt.Hax.RustSemantics.updEnv #[ρ, mkStrLit k, v]) base

/-- Definitional equality decided by the kernel, which unfolds the literal and the
    string comparisons of `WordOp.ofName` where `Meta.isDefEq` gives up. -/
def kernelDefEq (env : Environment) (lctx : LocalContext) (a b : Expr) : Bool :=
  match Kernel.isDefEq env lctx a b with
  | .ok r => r
  | .error _ => false

/-- The `RustM` corollary of one function; the result is the status. -/
def rustMFn (ns : Name) (f : String) : TermElabM String := do
  let gen (s : String) : Name := ns ++ `HaxGen ++ Name.mkSimple s
  let corresN := gen f ++ `corres_full
  let env ← getEnv
  unless env.contains corresN do return "early: no FnCorres"
  let cinfo ← getConstInfo corresN
  let res ← budgeted <| forallTelescope cinfo.type fun insts body => do
    let body ← whnfR body
    unless body.isAppOfArity ``Hax.Ascent.FnCorres 8 do
      return "early: not an FnCorres"
    let args := body.getAppArgs
    let A := args[1]!
    let β := args[2]!
    let e := args[4]!
    let gFn := args[7]!
    unless ← isDefEq β (mkConst ``Int) do return "type: result"
    -- width
    let some litName := e.constName? | return "width: literal is not a constant"
    let some litVal := (← getConstInfo litName).value? | return "width: no literal value"
    let ws := tagWidths (strLits litVal)
    let w ← match ws with
      | [w] => pure w
      | [] => return "width: no tagged operation"
      | _ => return s!"width: several widths {ws}"
    let some tyN := uTyOf? w | return s!"width: {w}"
    let ty := mkConst tyN
    -- parameters and globals
    let fnE := mkAppN (mkConst (gen ("fn_" ++ f))) insts
    let fnV ← whnfD fnE
    unless fnV.isAppOfArity ``Hax.Ascent.ExtFn.mk 4 do return "type: ExtFn"
    let some params ← strList? fnV.getAppArgs[1]! | return "type: parameters"
    let some globals ← strList? fnV.getAppArgs[2]! | return "type: globals"
    let intE := mkConst ``Int
    let zeroEnv ← withLocalDeclD `x (mkConst ``String) fun x =>
      mkLambdaFVars #[x] (mkIntLit 0)
    withLocalDeclD `a A fun a => do
      -- the global values
      let mut gvs : List (String × Expr) := []
      for g in globals do
        let gN := gen g ++ `gen
        unless (← getEnv).contains gN do return s!"type: global {g}"
        let gv := mkApp (mkAppN (mkConst gN) insts) (mkConst ``Unit.unit)
        unless ← isDefEq (← inferType gv) intE do return s!"type: global {g}"
        gvs := gvs ++ [(g, gv)]
      -- the parameter components
      let mut cur := a
      let mut pvs : List (String × Expr) := []
      for p in params do
        let t ← whnfR (← inferType cur)
        unless t.isAppOfArity ``Prod 2 do return s!"type: parameter {p}"
        let c ← mkAppM ``Prod.fst #[cur]
        unless ← isDefEq (← inferType c) intE do return s!"type: parameter {p}"
        pvs := pvs ++ [(p, c)]
        cur ← mkAppM ``Prod.snd #[cur]
      let ρ ← mkUpdEnv (← mkUpdEnv zeroEnv gvs) pvs.reverse
      let ρI ← mkLambdaFVars #[a] ρ
      -- the bridge equation
      let lhs ← mkAppM ``CatCrypt.Hax.RustSemantics.runWord #[ty, e, ρ]
      let rhs := mkApp gFn a
      unless kernelDefEq (← getEnv) (← getLCtx) lhs rhs do return "bridge: not rfl"
      let hbr ← mkLambdaFVars #[a] (← mkEqRefl rhs)
      let hbrTy ← mkForallFVars #[a] (← mkEq lhs rhs)
      let hbr ← mkExpectedTypeHint hbr hbrTy
      let corres := mkAppN (mkConst corresN) insts
      let pf ← mkAppOptM ``CatCrypt.Hax.RustSemantics.fnCorres_toRustM
        #[ty, none, none, none, none, none, none, corres, ρI, hbr]
      let pfTy ← inferType pf
      addThm (gen f ++ `rustM) (← mkForallFVars insts pfTy) (← mkLambdaFVars insts pf)
      -- the non-vacuity theorem
      let names := params ++ globals
      let boundE ← withLocalDeclD `x (mkConst ``String) fun x => do
        let l ← mkListLit (mkConst ``String) (names.map mkStrLit)
        mkLambdaFVars #[x] (← mkAppM ``List.contains #[l, x])
      let tot ← mkAppM ``CatCrypt.Hax.RustSemantics.totalOk #[ty, e, boundE]
      let trueE := mkConst ``Bool.true
      if kernelDefEq (← getEnv) (← getLCtx) tot trueE then
        let htot ← mkExpectedTypeHint (← mkEqRefl trueE) (← mkEq tot trueE)
        let ρAty ← mkArrow (mkConst ``String) (← mkAppM ``Option
          #[← mkAppM ``Aeneas.Std.UScalar #[ty]])
        let totPf ← withLocalDeclD `ρA ρAty fun ρA => do
          let p ← mkAppM ``CatCrypt.Hax.RustSemantics.toRustM_isOk_of_totalOk
            #[e, ρA, boundE, htot]
          mkLambdaFVars #[ρA] p
        addThm (gen f ++ `rustM_total) (← mkForallFVars insts (← inferType totPf))
          (← mkLambdaFVars insts totPf)
        return "rustM total"
      return "rustM"
  match res with
  | .ok s => return s
  | .error msg => return s!"failed: {msg.take 200}"

/-- The state-passing `RustM` corollary of one function; the result is the status. -/
def rustMSFn (ns : Name) (f : String) : TermElabM String := do
  let gen (s : String) : Name := ns ++ `HaxGen ++ Name.mkSimple s
  let corresN := gen f ++ `corres_full
  unless (← getEnv).contains corresN do return "early: no FnCorres"
  let cinfo ← getConstInfo corresN
  let res ← budgeted <| forallTelescope cinfo.type fun insts body => do
    let body ← whnfR body
    unless body.isAppOfArity ``Hax.Ascent.FnCorres 8 do
      return "early: not an FnCorres"
    let args := body.getAppArgs
    let bi ← whnfR args[0]!
    unless bi.isAppOfArity ``Hax.Ascent.extBuiltins 2 do return "table: not extBuiltins"
    let T := bi.getAppArgs[0]!
    let fns := bi.getAppArgs[1]!
    let e := args[4]!
    let trueE := mkConst ``Bool.true
    let names ← mkAppM ``List.map #[mkConst ``Hax.Ascent.ExtFn.name, fns]
    let frag ← mkAppM ``CatCrypt.Hax.RustSemantics.fragOk #[names, e]
    unless kernelDefEq (← getEnv) (← getLCtx) frag trueE do return "fragment: outside"
    let namesOk ← mkAppM ``CatCrypt.Hax.RustSemantics.ExtNamesOk #[T, fns]
    unless kernelDefEq (← getEnv) (← getLCtx) namesOk trueE do return "table: names"
    let hn ← mkExpectedTypeHint (← mkEqRefl trueE) (← mkEq namesOk trueE)
    let happ ← mkAppM ``CatCrypt.Hax.RustSemantics.appExt_ok #[T, fns, hn]
    let corres := mkAppN (mkConst corresN) insts
    let pf ← mkAppOptM ``CatCrypt.Hax.RustSemantics.fnCorres_toRustMS
      #[none, none, none, none, none, none, none, none, corres, none, happ]
    addThm (gen f ++ `rustMS) (← mkForallFVars insts (← inferType pf))
      (← mkLambdaFVars insts pf)
    return "rustMS"
  match res with
  | .ok s => return s
  | .error msg => return s!"failed: {msg.take 200}"

/-- The `RustM` corollaries of the functions `fs` of the extraction `ns`, with the status of
    each. -/
def ascendRustM (ns : Name) (fs : Array String) : TermElabM (Array (String × String)) :=
  fs.mapM fun f => return (f, ← rustMFn ns f)

/-- The state-passing `RustM` corollaries of the functions `fs` of the extraction `ns`, with
    the status of each. -/
def ascendRustMS (ns : Name) (fs : Array String) : TermElabM (Array (String × String)) :=
  fs.mapM fun f => return (f, ← rustMSFn ns f)

/-- `ascendExtraction` followed by `ascendRustM` on the functions it proves without early
    return. -/
def ascendExtractionRustM (ns : Name) :
    TermElabM (Array FnReport × Array (String × String)) := do
  let (reports, _) ← Hax.Ascent.Gen.ascendExtraction ns none
  let fs := (reports.filter (·.status == "proved")).map (·.name)
  return (reports, ← ascendRustM ns fs)

/-- `ascendExtraction` followed by `ascendRustM` and `ascendRustMS` on the functions it
    proves without early return. -/
def ascendExtractionRustMS (ns : Name) :
    TermElabM (Array FnReport × Array (String × String) × Array (String × String)) := do
  let (reports, _) ← Hax.Ascent.Gen.ascendExtraction ns none
  let fs := (reports.filter (·.status == "proved")).map (·.name)
  return (reports, ← ascendRustM ns fs, ← ascendRustMS ns fs)

end CatCrypt.Hax.RustSemantics.AscendRustM

open Lean Elab Command in
/-- `hax_ascend_rustm Ns` runs the generator on the extraction `Ns`, declares the `RustM`
    corollaries of every function it proves, and reports per function the corollary
    status, and for every function it does not prove the generator's status and cause. -/
elab "hax_ascend_rustm " ns:ident : command => do
  let (reports, rs, rss) ← liftTermElabM <|
    CatCrypt.Hax.RustSemantics.AscendRustM.ascendExtractionRustMS ns.getId
  let proved := (reports.filter (·.status.startsWith "proved")).size
  let withRustM := (rs.filter (·.2.startsWith "rustM")).size
  let total := (rs.filter (·.2 == "rustM total")).size
  let withRustMS := (rss.filter (·.2 == "rustMS")).size
  let lines := (rs.zip rss).toList.map fun ((f, s), (_, s')) => s!"| {f} | {s} | {s'} |"
  let others := (reports.filter (·.status != "proved")).toList.map fun r =>
    s!"| {r.name} | {r.status} | {r.detail.take 300} |"
  logInfo m!"{ns.getId}: {proved}/{reports.size} proved, {withRustM} with the RustM corollary, {total} with its totality, {withRustMS} with the state-passing corollary\n| function | RustM | RustMS |\n|---|---|---|\n{"\n".intercalate lines}\n| not proved | status | cause |\n|---|---|---|\n{"\n".intercalate others}"

end
