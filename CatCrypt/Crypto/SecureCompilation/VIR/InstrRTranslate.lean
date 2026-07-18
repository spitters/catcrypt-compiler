/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.JasminAST
import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror

/-!
# A verified AST translation `JasminAST.InstrR → CoqSemMirror.InstrR`

This file closes **gap #1** of `ComJasminBridge.lean`: the
`JasminAST.InstrR → CoqSemMirror.InstrR` translation that, until now, existed
*only* as the unverified `MetaM` reifier `reifyInstrRMirror%`
(`InstrRReflect.lean` §9.c) and the lossy structural walker
`Mirror.instrRToMirror` (§9.b, which only handled `Copn` and discarded the
`Var.vtype` of everything else, hardcoding `.aword .U64`).

Here we give a *real, total* `Option`-valued function `translateInstrR` and
prove it **structure-preserving** on the emit-relevant fragment, sorry-free.

## The two ASTs (the catalogued differences, `InstrRReflect.lean` §9)

| Field            | `JasminAST`                       | `CoqSemMirror`                      |
|------------------|-----------------------------------|------------------------------------|
| word sizes       | `WSize` (7: …`U256 U512`)          | `WSize` (6: …`U256`)               |
| value types      | `SType` (`sword ws`)              | `Atype` (`aword ws`)               |
| `Var` fields     | `{ vname, vtype : SType }`        | `{ vtype : Atype, vname }`         |
| `VarI` fields    | `{ var, info : VarInfo }`         | `{ v_var, v_info : Unit }`         |
| `GVar.gs`        | `Bool` (true = global)            | `VScope` (`Slocal`/`Sglob`)        |
| binop carrier    | `SOp2.Oadd (ws)`                  | `SOp2.Oadd (Op_w ws)`              |
| `Cassgn` shape   | `(lv, tag, ty, e)`                | `(lv, tag, ty, e)` (same!)         |

The `U512` ⇒ no-`U512` size narrowing and the open `SOp2` constructors are the
*only* reasons the translation is partial (`Option`): every field that lands
in-fragment has an exact, structure-preserving image.

## The emit-relevant fragment

The golden-path `Com jasminDialect` emits, for a `regArith op` binding, exactly
(see `JasminPrintSemCorrect.lean:140`)

    Cassgn (Lvar dst) tag (sword ws) (Papp2 op (Pvar a) (Pvar b))

We translate this `Cassgn`-with-`Papp2`-of-two-`Pvar`s fragment field-by-field.
Everything outside it (`Copn`, `Cif`, `Cfor`, `Cwhile`, `Ccall`, `Csyscall`;
`Pget`/`Pload`/`Papp1`/`PappN`/`Pif`/constants; `Lmem`/`Laset`/`Lasub`/`Lnone`;
the `U512` width; SIMD/wint `SOp2` constructors) is mapped to `none` — honest,
not `sorry`. Extending coverage is a mechanical added case.

## What is proved (all sorry-free)

* `translateWSize`, `translateSType`, `translateSOp2`, `translateVar`,
  `translateVarI`, `translateGVar`, `translateLVal`, `translatePExpr`,
  `translateInstrR` — real total `Option`-valued functions.
* `translateInstrR_regArith` — the **fragment-correctness lemma**: on the
  emitted shape `Cassgn (Lvar dst) tag (sword ws) (Papp2 op (Pvar a) (Pvar b))`,
  `translateInstrR` produces *exactly* the field-by-field-translated
  `CoqSemMirror.Cassgn`, with each sub-translation succeeding iff its source is
  in-fragment.
* `golden_translate` — the worked example: `x := y + 1`'s in-AST `Cassgn`
  translates to the expected `CoqSemMirror.InstrR`, exhibited by `rfl`/`decide`.
* `golden_translate_op_is_add` / `golden_translate_lval_is_x` — the translated
  instruction carries the same binop (`Oadd`) and the same destination name as
  the `ComJasminBridge.golden_add_bridge` witness `x := y + 1`.

## The remaining gap to the GENERIC bridge

This is gap #1 (the AST translation) for the *fragment*. The full generic bridge
additionally needs (a) the remaining constructors, and (b) the `Store ↔ Estate`
byte-encoding bijection (gap #2) to lift this *syntactic* preservation to a
*semantic* `SemIr-of-translate ↔ Com.denote` correspondence. We connect to the
golden-path witness here at the value level only.

0 sorries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate

/-! ### Local abbreviations for the two ASTs

Both ASTs export sorts with the *same short names* (`WSize`, `Var`, `LVal`,
`PExpr`, `InstrR`, …), so we cannot `open` both. We give the `JasminAST` side an
`A`-prefixed abbreviation and the `CoqSemMirror` side an `M`-prefixed one, and
refer to constructors via fully-qualified `.Cassgn` etc. -/

abbrev AWSize    := CatCrypt.Crypto.Jasmin.WSize
abbrev ASType    := CatCrypt.Crypto.Jasmin.SType
abbrev ASOp2     := CatCrypt.Crypto.Jasmin.SOp2
abbrev AVar      := CatCrypt.Crypto.Jasmin.Var
abbrev AVarI     := CatCrypt.Crypto.Jasmin.VarI
abbrev AGVar     := CatCrypt.Crypto.Jasmin.GVar
abbrev ALVal     := CatCrypt.Crypto.Jasmin.LVal
abbrev APExpr    := CatCrypt.Crypto.Jasmin.PExpr
abbrev AInstrR   := CatCrypt.Crypto.Jasmin.InstrR
abbrev AAssgnTag := CatCrypt.Crypto.Jasmin.AssgnTag

abbrev MWSize    := CatCrypt.Crypto.Jasmin.CoqSemMirror.WSize
abbrev MAtype    := CatCrypt.Crypto.Jasmin.CoqSemMirror.Atype
abbrev MSOp2     := CatCrypt.Crypto.Jasmin.CoqSemMirror.SOp2
abbrev MVar      := CatCrypt.Crypto.Jasmin.CoqSemMirror.Var
abbrev MVarI     := CatCrypt.Crypto.Jasmin.CoqSemMirror.VarI
abbrev MGVar     := CatCrypt.Crypto.Jasmin.CoqSemMirror.GVar
abbrev MLval     := CatCrypt.Crypto.Jasmin.CoqSemMirror.Lval
abbrev MPexpr    := CatCrypt.Crypto.Jasmin.CoqSemMirror.Pexpr
abbrev MInstrR   := CatCrypt.Crypto.Jasmin.CoqSemMirror.InstrR
abbrev MInstr    := CatCrypt.Crypto.Jasmin.CoqSemMirror.Instr
abbrev MAssgnTag := CatCrypt.Crypto.Jasmin.CoqSemMirror.AssgnTag

/-- The mirror's `mkLvar` (local-scope `GVar` builder). -/
abbrev mkLvarM := CatCrypt.Crypto.Jasmin.CoqSemMirror.mkLvar

/-! ## 1. Word sizes: 7 → 6 (drop the `U512` CatCrypt extension) -/

/-- Translate a `JasminAST.WSize` to the faithful `CoqSemMirror.WSize`.
    Partial: the CatCrypt `U512` AVX-512 register-width extension has no mirror
    image (the faithful psem port deliberately stays at six widths). -/
def translateWSize : AWSize → Option MWSize
  | .U8   => some .U8
  | .U16  => some .U16
  | .U32  => some .U32
  | .U64  => some .U64
  | .U128 => some .U128
  | .U256 => some .U256
  | .U512 => none

/-! ## 2. Value types: `SType` → `Atype`

The emit fragment only ever produces `sword ws` (registers). `sbool`/`sint`
map cleanly too; `sarr` maps to `aarr` but requires a width tag the `SType`
form does not carry, so the array case is out-of-fragment (`none`). -/

/-- Translate a `JasminAST.SType` to a `CoqSemMirror.Atype`. The register case
    `sword ws` (all the emit fragment uses) translates exactly. `sarr n` is
    out-of-fragment because `Atype.aarr` additionally carries an element-width
    `ws` that `SType.sarr` does not record. -/
def translateSType : ASType → Option MAtype
  | .sbool    => some .abool
  | .sint     => some .aint
  | .sword ws => (translateWSize ws).map .aword
  | .sarr _   => none

/-! ## 3. Binary operators: `SOp2` → `SOp2`

The `JasminAST` `SOp2` tags a size `ws` directly; the mirror tags an `OpKind`
(`Op_int`/`Op_w ws`) or `CmpKind`. We cover the scalar arithmetic the
`regArith` dialect emits (`add`/`mul`/`sub`) plus the bitwise ops; SIMD and the
comparison/`OpKind`-less variants are out-of-fragment. -/

/-- Translate a `JasminAST.SOp2` to a `CoqSemMirror.SOp2`. Covers the scalar
    word-arithmetic + bitwise operators the `regArith` dialect emits. The size
    tag is carried into `OpKind.Op_w`. SIMD (`Ov*`) and the comparison family
    are out-of-fragment (`none`). -/
def translateSOp2 : ASOp2 → Option MSOp2
  | .Obeq      => some .Obeq
  | .Oand      => some .Oand
  | .Oor       => some .Oor
  | .Oadd ws   => (translateWSize ws).map (fun w => .Oadd (.Op_w w))
  | .Omul ws   => (translateWSize ws).map (fun w => .Omul (.Op_w w))
  | .Osub ws   => (translateWSize ws).map (fun w => .Osub (.Op_w w))
  | .Oland ws  => (translateWSize ws).map .Oland
  | .Olor ws   => (translateWSize ws).map .Olor
  | .Olxor ws  => (translateWSize ws).map .Olxor
  | .Olsr ws   => (translateWSize ws).map .Olsr
  | .Olsl ws   => (translateWSize ws).map (fun w => .Olsl (.Op_w w))
  | .Oasr ws   => (translateWSize ws).map (fun w => .Oasr (.Op_w w))
  -- everything below is out-of-fragment for the emit set
  | .Odiv _ _ | .Omod _ _ | .Oeq _ | .Oneq _
  | .Olt _ _ | .Ole _ _ | .Ogt _ _ | .Oge _ _
  | .Ovadd _ _ | .Ovsub _ _ | .Ovmul _ _
  | .Ovlsr _ _ | .Ovlsl _ _ | .Ovasr _ _ => none

/-! ## 4. Assignment tags — total, exact (same five constructors) -/

/-- Translate a `JasminAST.AssgnTag` to a `CoqSemMirror.AssgnTag`.
    The five constructors are in bijection; this is total. -/
def translateAssgnTag : AAssgnTag → MAssgnTag
  | .AT_none    => .AT_none
  | .AT_keep    => .AT_keep
  | .AT_rename  => .AT_rename
  | .AT_inline  => .AT_inline
  | .AT_phinode => .AT_phinode

/-! ## 5. Variables: `Var`/`VarI`/`GVar` field-by-field -/

/-- Translate a `JasminAST.Var` to a `CoqSemMirror.Var`: keep `vname`,
    translate `vtype : SType → Atype`. -/
def translateVar (v : AVar) : Option MVar :=
  (translateSType v.vtype).map (fun t => { vname := v.vname, vtype := t })

/-- Translate a `JasminAST.VarI` to a `CoqSemMirror.VarI`: the source-info field
    (`VarInfo` vs `Unit`) is opaque on both sides and carries no semantics, so we
    drop it to `()`. -/
def translateVarI (x : AVarI) : Option MVarI :=
  (translateVar x.var).map (fun v => { v_var := v })

/-- Translate a `JasminAST.GVar` to a `CoqSemMirror.GVar`: the `gs : Bool`
    is-global flag becomes the `gs : VScope` (`true = Sglob`, `false = Slocal`). -/
def translateGVar (g : AGVar) : Option MGVar :=
  (translateVarI g.gv).map (fun v =>
    { gv := v, gs := if g.gs then .Sglob else .Slocal })

/-! ## 6. L-values and expressions, restricted to the emit fragment -/

/-- Translate a `JasminAST.LVal` to a `CoqSemMirror.Lval`. In-fragment: only the
    register-write `Lvar`. Memory/array l-values are out-of-fragment. -/
def translateLVal : ALVal → Option MLval
  | .Lvar x => (translateVarI x).map .Lvar
  | _       => none

/-- Translate a `JasminAST.PExpr` to a `CoqSemMirror.Pexpr`. In-fragment: a
    register read `Pvar`, an integer/bool constant, and the binary application
    `Papp2`. (The golden-path `regArith` rhs is `Papp2 op (Pvar a) (Pvar b)`.)
    Array/load/`Papp1`/`PappN`/`Pif` shapes are out-of-fragment. -/
def translatePExpr : APExpr → Option MPexpr
  | .Pconst z      => some (.Pconst z)
  | .Pbool b       => some (.Pbool b)
  | .Pvar g        => (translateGVar g).map .Pvar
  | .Papp2 op e1 e2 =>
      match translateSOp2 op, translatePExpr e1, translatePExpr e2 with
      | some op', some e1', some e2' => some (.Papp2 op' e1' e2')
      | _, _, _ => none
  | _ => none

/-! ## 7. The instruction-level translation -/

/-- **The verified translation.** Total `Option`-valued
    `JasminAST.InstrR → CoqSemMirror.InstrR`. In-fragment: a `Cassgn` whose
    l-value, type, and expression are all in their respective fragments
    (the `regArith`/`Papp2` golden-path shape). All other instruction
    constructors (`Copn`, `Cif`, `Cfor`, `Cwhile`, `Ccall`) are out-of-fragment
    (`none`) — honest, mechanically extensible, never `sorry`. -/
def translateInstrR : AInstrR → Option MInstrR
  | .Cassgn lv tag ty e =>
      match translateLVal lv, translateSType ty, translatePExpr e with
      | some lv', some ty', some e' =>
          some (.Cassgn lv' (translateAssgnTag tag) ty' e')
      | _, _, _ => none
  | _ => none

/-- Wrap a translated `InstrR` as a `CoqSemMirror.Instr` (the `MkI ()` head). -/
def translateInstr (i : AInstrR) : Option MInstr :=
  (translateInstrR i).map (CatCrypt.Crypto.Jasmin.CoqSemMirror.Instr.MkI ())

/-! ## 8. The fragment-correctness lemma

On the emitted `regArith`/`Papp2` shape, `translateInstrR` is exactly the
field-by-field-translated `Cassgn`: structure-preserving, with each sub-result
governed by its sub-translation. This is the syntactic-preservation content of
gap #1 over the emit fragment. -/

/-- **Fragment correctness (structure preservation).** For the golden-path
    emitted shape
    `Cassgn (Lvar dst) tag (sword ws) (Papp2 op (Pvar ga) (Pvar gb))`,
    `translateInstrR` produces the field-by-field-translated mirror `Cassgn`
    iff every field is in-fragment, and the translated fields are *exactly* the
    pointwise sub-translations — same destination l-value (`translateVarI dst`),
    same word type (`translateSType (sword ws)`), same `OpKind`-tagged operator
    (`translateSOp2 op`), same operand reads (`translateGVar ga`/`gb`), same
    tag — with the whole instruction succeeding iff every field succeeds. This
    is the load-bearing structure-preservation content of bridge gap #1 over the
    emit fragment. -/
theorem translateInstrR_regArith
    (dst : AVarI) (ga gb : AGVar) (tag : AAssgnTag) (ws : AWSize) (op : ASOp2) :
    translateInstrR
      (.Cassgn (.Lvar dst) tag (.sword ws) (.Papp2 op (.Pvar ga) (.Pvar gb)))
      = (match translateVarI dst, translateSType (.sword ws),
              translateSOp2 op, translateGVar ga, translateGVar gb with
         | some dst', some ty', some op', some ga', some gb' =>
             some (.Cassgn (.Lvar dst') (translateAssgnTag tag) ty'
                     (.Papp2 op' (.Pvar ga') (.Pvar gb')))
         | _, _, _, _, _ => none) := by
  -- Each field of the `Cassgn`/`Papp2` shape unfolds to the named
  -- sub-translation; the nested `Option`-binds align after peeling.
  simp only [translateInstrR, translateLVal, translatePExpr, Option.map]
  cases translateVarI dst <;>
  cases translateSType (.sword ws) <;>
  cases translateSOp2 op <;>
  cases translateGVar ga <;>
  cases translateGVar gb <;>
  rfl

/-! ## 9. The worked example — `x := y + 1`

The concrete `ComJasminBridge.golden_add_bridge` witness, but on the *syntactic*
side: the in-`JasminAST` `Cassgn` for `x := y + 1` translates to the expected
`CoqSemMirror.InstrR`. We exhibit the image and check the binop and destination
match the golden-path witness. -/

/-- The golden-path source `Var x : reg u64`. -/
def xVarA : AVar := { vname := "x", vtype := .sword .U64 }
/-- The golden-path source `Var y : reg u64`. -/
def yVarA : AVar := { vname := "y", vtype := .sword .U64 }

/-- The golden-path source instruction `x := y + 1` in `JasminAST`:
    `Cassgn (Lvar x) AT_none (sword U64) (Papp2 (Oadd U64) (Pvar y) (Pconst 1))`. -/
def goldenAddSrc : AInstrR :=
  .Cassgn (.Lvar { var := xVarA }) .AT_none (.sword .U64)
    (.Papp2 (.Oadd .U64)
      (.Pvar (CatCrypt.Crypto.Jasmin.GVar.mk { var := yVarA } false))
      (.Pconst 1))

/-- The expected `CoqSemMirror` image of `goldenAddSrc`. -/
def goldenAddTgt : MInstrR :=
  .Cassgn (.Lvar { v_var := { vname := "x", vtype := .aword .U64 } })
    .AT_none (.aword .U64)
    (.Papp2 (.Oadd (.Op_w .U64))
      (.Pvar (mkLvarM { v_var := { vname := "y", vtype := .aword .U64 } }))
      (.Pconst 1))

/-- **Worked example.** The golden-path `x := y + 1` translates to exactly the
    expected `CoqSemMirror.InstrR` — sorry-free, by `rfl`. -/
theorem golden_translate : translateInstrR goldenAddSrc = some goldenAddTgt := by
  rfl

/-- The translated golden instruction carries the **same binop** as the
    `ComJasminBridge` witness — a `psem.v`-side `Oadd` (here at `Op_w U64`),
    matching the `Oadd Op_int` the bridge's `addOpSem` runs. -/
theorem golden_translate_op_is_add :
    (translateInstrR goldenAddSrc).bind
      (fun ir => match ir with
        | .Cassgn _ _ _ (.Papp2 op _ _) => some op
        | _ => none)
      = some (.Oadd (.Op_w .U64)) := by
  rfl

/-- The translated golden instruction writes the **same destination** `x` as the
    `ComJasminBridge` golden witness `x := y + 1`. -/
theorem golden_translate_lval_is_x :
    (translateInstrR goldenAddSrc).bind
      (fun ir => match ir with
        | .Cassgn (.Lvar v) _ _ _ => some v.v_var.vname
        | _ => none)
      = some "x" := by
  rfl

/-! ## 10. Out-of-fragment is honest `none`, not silent loss

These confirm the translation *rejects* (returns `none`) on the shapes outside
the emit fragment, rather than silently mapping them to a placeholder (the
defect of the lossy §9.b `instrRToMirror`, which hardcoded `.aword .U64` and a
`Pconst 0` default). -/

/-- The `U512` AVX-512 register width has no faithful mirror — rejected. -/
theorem translate_u512_rejected :
    translateInstrR
      (.Cassgn (.Lvar { var := { vname := "z", vtype := .sword .U512 } })
        .AT_none (.sword .U512)
        (.Pvar (CatCrypt.Crypto.Jasmin.GVar.mk { var := xVarA } false)))
      = none := by
  rfl

/-- A `Copn` (asm-op) instruction is out of *this* fragment (it belongs to the
    §9.b `Copn` path) — rejected here rather than silently coerced. -/
theorem translate_copn_rejected
    (lvs : List ALVal) (tag : AAssgnTag)
    (op : CatCrypt.Crypto.Jasmin.SOpn) (es : List APExpr) :
    translateInstrR (.Copn lvs tag op es) = none := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
