/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.Jasmin.JazzToInstrRFacts

/-!
# Jasmin compilation units in the `CoqSemMirror` syntax

`translateFn` translates a function `JazzFn` of a Jasmin compilation unit to a function
declaration of the `psem.v` mirror by `InstrRTranslateExt`: the parameters and results by
`translateVarIExt`, the body by `translateCmdExt`, the parameter and result types read off
the translated variables. `translateUnit` translates the functions of a unit to a mirror
program `Prog` without globals; the extern signatures of a unit declare linked callees and
contribute no function to the program.

The image theorems state, for each instruction shape of the op table of `nfToJasmin`, the
mirror command `translateCmdExt` returns, over the mirror builders `mpv` (a local read),
`masgn` (an assignment at the type of its target) and `mcopn` (an asm operation without
tag), in the manner of `InstrRTranslateExt.translateInstrRExt_ccall`.

## Main definitions

* `translateFn`, `translateUnit`: the translation of a function and of a unit.
* `mpv`, `masgn`, `mcopn`, `mkCmd`, `mcf`: the mirror builders.

## Main results

* `translateUnit_mkUnit`, `translateFn_eq_some`: the translation of the unit of one
  function, and of a function whose parameters, body and results translate.
* `translateCmdExt_append_eq_some`, `translateCmdExt_seqMoves`: concatenation and sequential moves.
* Image theorems: `translateInstrRExt_cinCode` and `translateCmdExt_matCF` (the carry flag),
  `translateCmdExt_addCarryLo` (the carry pair `ADD_64`/`ADC_64`), `translateCmdExt_cmpCode`
  (the comparison idiom over `NEG_64`/`CMP_64`), `translateCmdExt_select` (the mask select),
  `translateCmdExt_mulhi` (`MULX_lo_hi_64`), `translateCmdExt_forCode` (the counter `while`
  frame), `translateCmdExt_whileCode` (the exit-flag `while`), `translateInstrRExt_ifCode` (the
  branch with its join moves), `translateInstrRExt_call` (a call with several results),
  `translateCmdExt_stackLoad` and `translateCmdExt_stackStore` (the `(uint) e` index), and
  `translateCmdExt_sarImm` (the arithmetic shift by `sarCount`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.Jasmin.CoqSemMirror (mkLvar)
open CatCrypt.Crypto.Jasmin.JazzToInstrR (opnNoneTys opnNoneTys_ADD_64 opnNoneTys_ADC_64
  opnNoneTys_NEG_64 opnNoneTys_CMP_64 opnNoneTys_MULX_64)

/-- A mirror function name. -/
abbrev MFunName := CatCrypt.Crypto.Jasmin.CoqSemMirror.FunName

/-- A mirror function definition. -/
abbrev MFunDef := CatCrypt.Crypto.Jasmin.CoqSemMirror.FunDef

/-- A mirror program. -/
abbrev MProg := CatCrypt.Crypto.Jasmin.CoqSemMirror.Prog

/-! ## 1. Functions and units -/

/-- The translation of a function: its name, the translated parameters with their types,
the translated body, and the translated results with their types. -/
def translateFn (f : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) : Option (MFunName × MFunDef) :=
  match f.fd.params.mapM (fun p => translateVarIExt p.var), translateCmdExt f.fd.body,
      f.fd.results.mapM translateVarIExt with
  | some ps, some body, some rs =>
      some ({ name := f.fd.name.name },
        { tyin := ps.map (·.v_var.vtype), params := ps, body := body,
          tyout := rs.map (·.v_var.vtype), rets := rs })
  | _, _, _ => none

/-- The translation of a unit: the program of its translated functions, without globals. -/
def translateUnit (u : CatCrypt.Crypto.Jasmin.Jazz.JazzUnit) : Option MProg :=
  (u.fns.mapM translateFn).map fun fs => { pFuncs := fs, pGlobs := [] }

/-- A function translates when its parameters, body and results translate. -/
theorem translateFn_eq_some (f : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) {ps : List MVarI}
    {body : List MInstr} {rs : List MVarI}
    (hps : f.fd.params.mapM (fun p => translateVarIExt p.var) = some ps)
    (hb : translateCmdExt f.fd.body = some body)
    (hrs : f.fd.results.mapM translateVarIExt = some rs) :
    translateFn f = some ({ name := f.fd.name.name },
      { tyin := ps.map (·.v_var.vtype), params := ps, body := body,
        tyout := rs.map (·.v_var.vtype), rets := rs }) := by
  simp [translateFn, hps, hb, hrs]

/-- The unit of one function translates to the program of that function. -/
theorem translateUnit_mkUnit (fn : CatCrypt.Crypto.Jasmin.Jazz.JazzFn) (fd : MFunName × MFunDef)
    (h : translateFn fn = some fd) :
    translateUnit (mkUnit fn) = some { pFuncs := [fd], pGlobs := [] } := by
  simp [translateUnit, mkUnit, h]

/-! ## 2. Mirror builders -/

/-- The mirror read of a local variable. -/
def mpv (x : MVarI) : MPexpr := .Pvar (mkLvar x)

/-- The mirror assignment `x = e` at the type of `x`. -/
def masgn (x : MVarI) (e : MPexpr) : MInstrR := .Cassgn (.Lvar x) .AT_none x.v_var.vtype e

/-- The mirror asm operation `o` with the l-values `lvs` and the operands `es`. -/
def mcopn (o : String) (lvs : List MLval) (es : List MPexpr) : MInstrR :=
  .Copn lvs .AT_none (.Oasm o) es

/-- A mirror command of instructions, each annotated `MkI ()`. -/
def mkCmd (c : List MInstrR) : List MInstr := c.map (.MkI ())

/-- The mirror carry flag `cf`. -/
def mcf : MVarI := { v_var := { vtype := .abool, vname := "cf" } }

/-- A discarded Boolean output. -/
def mnb : MLval := .Lnone () .abool

/-- The `b5w_ty` outputs with the carry flag and the word `x`. -/
def mCWOuts (x : MVarI) : List MLval := [mnb, .Lvar mcf, mnb, mnb, mnb, .Lvar x]

/-- The `b5w_ty` outputs with the word `x` only. -/
def mWOuts (x : MVarI) : List MLval := [mnb, mnb, mnb, mnb, mnb, .Lvar x]

/-- The mirror condition `v != 0`. -/
def mnz (v : MVarI) : MPexpr := .Papp2 (.Oneq (.Op_w .U64)) (mpv v) (.Pconst 0)

/-! ## 3. Variables, expressions and commands -/

/-- The variable of a translated local carries the translated type. -/
theorem translateSTypeExt_of_var {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateSTypeExt x.vtype = some x'.v_var.vtype := by
  unfold translateVarIExt translateVarExt at hx
  cases ht : translateSTypeExt x.vtype with
  | none => simp [ht] at hx
  | some t =>
      simp only [ht, Option.map_some, Option.some.injEq] at hx
      subst hx; rfl

/-- The carry flag translates to `mcf`. -/
theorem translateVarIExt_cf : translateVarIExt ⟨cfVar, vi0⟩ = some mcf := rfl

/-- A local read translates to `mpv`. -/
theorem translatePExprExt_pv {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translatePExprExt (pv x) = some (mpv x') :=
  translatePExprExt_pvar_local _ _ hx

/-- An integer constant translates to itself. -/
theorem translatePExprExt_cnst (z : Int) : translatePExprExt (cnst z) = some (.Pconst z) := rfl

/-- The l-value of a local translates to the mirror `Lvar`. -/
theorem translateLValExt_lvv {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateLValExt (lvv x) = some (.Lvar x') := by
  simp [lvv, translateLValExt, hx]

/-- An assignment translates to `masgn`. -/
theorem translateInstrRExt_asgn {x : JVar} {x' : MVarI} {e : CatCrypt.Crypto.Jasmin.PExpr}
    {e' : MPexpr} (hx : translateVarIExt ⟨x, vi0⟩ = some x') (he : translatePExprExt e = some e') :
    translateInstrRExt (asgn x e) = some (masgn x' e') := by
  simp [asgn, translateInstrRExt, translateLValExt_lvv hx, translateSTypeExt_of_var hx, he,
    masgn, translateAssgnTag]

/-- A binary operation over translated operands. -/
theorem translatePExprExt_papp2 {op : ASOp2} {op' : MSOp2} {e1 e2 : APExpr} {e1' e2' : MPexpr}
    (ho : translateSOp2Ext op = some op') (h1 : translatePExprExt e1 = some e1')
    (h2 : translatePExprExt e2 = some e2') :
    translatePExprExt (.Papp2 op e1 e2) = some (.Papp2 op' e1' e2') := by
  simp [translatePExprExt, ho, h1, h2]

/-- A unary operation over a translated operand. -/
theorem translatePExprExt_papp1 {op : ASOp1} {op' : MSOp1} {e : APExpr} {e' : MPexpr}
    (ho : translateSOp1 op = some op') (h : translatePExprExt e = some e') :
    translatePExprExt (.Papp1 op e) = some (.Papp1 op' e') := by
  simp [translatePExprExt, ho, h]

/-- The translation of a command with a translated head. -/
theorem translateCmdExt_cons {i : AInstrR} {c : List AInstrR} {i' : MInstrR} {c' : List MInstr}
    (hi : translateInstrRExt i = some i') (hc : translateCmdExt c = some c') :
    translateCmdExt (i :: c) = some (.MkI () i' :: c') := by
  simp [translateCmdExt, hi, hc]

/-- The translation of a concatenation of translated commands. -/
theorem translateCmdExt_append_eq_some : ∀ {a b : List AInstrR} {a' b' : List MInstr},
    translateCmdExt a = some a' → translateCmdExt b = some b' →
    translateCmdExt (a ++ b) = some (a' ++ b')
  | [], _, a', _, ha, hb => by
      simp only [translateCmdExt, Option.some.injEq] at ha; subst ha; simpa using hb
  | i :: a, b, a', b', ha, hb => by
      simp only [translateCmdExt] at ha
      cases hi : translateInstrRExt i with
      | none => simp [hi] at ha
      | some i' =>
          cases hc : translateCmdExt a with
          | none => simp [hi, hc] at ha
          | some c' =>
              simp only [hi, hc, Option.some.injEq] at ha
              subst ha
              rw [List.cons_append, translateCmdExt_cons hi (translateCmdExt_append_eq_some hc hb)]
              rfl

/-- A command of assignments translates to `mkCmd` of their images. -/
theorem translateCmdExt_mkCmd : ∀ {c : List AInstrR} {c' : List MInstrR},
    List.Forall₂ (fun i i' => translateInstrRExt i = some i') c c' →
    translateCmdExt c = some (mkCmd c')
  | _, _, .nil => rfl
  | _, _, .cons h hs => translateCmdExt_cons h (translateCmdExt_mkCmd hs)

/-- **Sequential moves.** The moves `seqMoves ps` translate to the mirror assignments of
the translated pairs. -/
theorem translateCmdExt_seqMoves {ps : List (JVar × JVar)} {ps' : List (MVarI × MVarI)}
    (h : List.Forall₂ (fun p p' => translateVarIExt ⟨p.1, vi0⟩ = some p'.1 ∧
      translateVarIExt ⟨p.2, vi0⟩ = some p'.2) ps ps') :
    translateCmdExt (seqMoves ps) = some (mkCmd (ps'.map fun p => masgn p.1 (mpv p.2))) := by
  apply translateCmdExt_mkCmd
  induction h with
  | nil => exact .nil
  | cons hp _ ih =>
      exact .cons (translateInstrRExt_asgn hp.1 (translatePExprExt_pv hp.2)) ih

/-! ## 4. Image theorems of the op table -/

/-- A discarded Boolean output translates to `mnb`. -/
theorem translateLValExt_lnone_bool :
    translateLValExt (.Lnone vi0 .sbool) = some mnb := rfl

/-- A discarded `u64` output translates to the discarded mirror word. -/
theorem translateLValExt_lnone_u64 :
    translateLValExt (.Lnone vi0 (.sword .U64)) = some (.Lnone () (.aword .U64)) := rfl

/-- The 64-bit names of the asm operations of the op table. -/
theorem asmName_U64 :
    asmName "ADC" .U64 = "ADC_64" ∧ asmName "NEG" .U64 = "NEG_64" ∧
      asmName "CMP" .U64 = "CMP_64" ∧ asmName "MULX_lo_hi" .U64 = "MULX_lo_hi_64" := by
  simp [asmName, CatCrypt.Crypto.Jasmin.WSize.bits, Nat.repr_of_ge, Nat.repr_of_lt,
    Nat.digitChar_eq_six.mpr rfl, Nat.digitChar_eq_four.mpr rfl]

/-- The l-values of translated locals. -/
theorem mapM_lvv {xs : List JVar} {xs' : List MVarI}
    (h : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs') :
    (xs.map lvv).mapM translateLValExt = some (xs'.map .Lvar) := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [List.mapM_cons, translateLValExt_lvv hx, ih]

/-- The reads of translated locals. -/
theorem mapM_pv {xs : List JVar} {xs' : List MVarI}
    (h : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs') :
    (xs.map pv).mapM translatePExprExt = some (xs'.map mpv) := by
  induction h with
  | nil => rfl
  | cons hx _ ih => simp [List.mapM_cons, translatePExprExt_pv hx, ih]

/-- An asm operation with the `b5w_ty` outputs of the carry flag and the word `x`, for an
operation whose `_` outputs are five flags and a word. -/
theorem translateInstrRExt_copnCW {o : String} {x : JVar} {x' : MVarI}
    {es : List CatCrypt.Crypto.Jasmin.PExpr} {es' : List MPexpr}
    (ho : opnNoneTys o 6 = List.replicate 5 .sbool ++ [.sword .U64])
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hes : es.mapM translatePExprExt = some es') :
    translateInstrRExt (copn o (outsCW x) es) = some (mcopn o (mCWOuts x') es') := by
  have hl : (outsCW x).length = 6 := rfl
  simp only [copn, hl, ho]
  simp only [outsCW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv hx, translateLValExt_lvv translateVarIExt_cf, hes]
  rfl

/-- An asm operation with the `b5w_ty` outputs of the word `x` only. -/
theorem translateInstrRExt_copnW {o : String} {x : JVar} {x' : MVarI}
    {es : List CatCrypt.Crypto.Jasmin.PExpr} {es' : List MPexpr}
    (ho : opnNoneTys o 6 = List.replicate 5 .sbool ++ [.sword .U64])
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hes : es.mapM translatePExprExt = some es') :
    translateInstrRExt (copn o (outsW x) es) = some (mcopn o (mWOuts x') es') := by
  have hl : (outsW x).length = 6 := rfl
  simp only [copn, hl, ho]
  simp only [outsW, outLvs, List.replicate, List.cons_append, List.nil_append,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
    translateLValExt_lvv hx, hes]
  rfl

/-- **Carry-in image.** `#ADD_64(cin, -1)` into the scratch word `t0`. -/
theorem translateInstrRExt_cinCode {cin : JVar} {cin' t0' : MVarI}
    (hcin : translateVarIExt ⟨cin, vi0⟩ = some cin')
    (ht0 : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t0') :
    translateInstrRExt (cinCode cin) =
      some (mcopn "ADD_64" (mCWOuts t0') [mpv cin', .Pconst (-1)]) :=
  translateInstrRExt_copnCW opnNoneTys_ADD_64 ht0
    (by simp [List.mapM_cons, translatePExprExt_pv hcin, translatePExprExt_cnst])

/-- **Carry materialisation image.** `x = 0; #ADC_64(x, x, cf)`. -/
theorem translateCmdExt_matCF {x : JVar} {x' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') :
    translateCmdExt (matCF x) = some (mkCmd [masgn x' (.Pconst 0),
      mcopn "ADC_64" (mWOuts x') [mpv x', mpv x', mpv mcf]]) :=
  translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx (translatePExprExt_cnst 0))
    (.cons (translateInstrRExt_copnW opnNoneTys_ADC_64 hx
      (by simp [List.mapM_cons, translatePExprExt_pv hx,
        translatePExprExt_pv translateVarIExt_cf])) .nil))

/-- **Carry-pair image.** The binding of `addCarryLo 64` to `x` on `a`, `b` and the
carry-in word `cin`: `#ADD_64(cin, -1)`, `x = a`, `#ADC_64(x, b, cf)`. -/
theorem translateCmdExt_addCarryLo {d : Nat} {x a b cin : JVar} {x' a' b' cin' t0' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hb : translateVarIExt ⟨b, vi0⟩ = some b') (hcin : translateVarIExt ⟨cin, vi0⟩ = some cin')
    (ht0 : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t0') :
    (emitOp (.addCarryLo 64) d x [a, b, cin]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [mcopn "ADD_64" (mCWOuts t0') [mpv cin', .Pconst (-1)], masgn x' (mpv a'),
        mcopn "ADC_64" (mCWOuts x') [mpv x', mpv b', mpv mcf]]) := by
  have he : emitOp (.addCarryLo 64) d x [a, b, cin] =
      some ([cinCode cin, asgn x (pv a),
        copn (asmName "ADC" .U64) (outsCW x) [pv x, pv b, pv cfVar]], x) := rfl
  have hn : asmName "ADC" .U64 = "ADC_64" := asmName_U64.1
  rw [he, Option.bind_some, hn]
  exact translateCmdExt_mkCmd (.cons (translateInstrRExt_cinCode hcin ht0)
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
      (.cons (translateInstrRExt_copnCW opnNoneTys_ADC_64 hx
        (by simp [List.mapM_cons, translatePExprExt_pv hx, translatePExprExt_pv hb,
          translatePExprExt_pv translateVarIExt_cf])) .nil)))

/-- The mirror comparison idiom at `u64`, with the scratch words `t`, `t'`: the carry of
`#NEG_64(a ^ b)` (`eq`, `ne`) or of `#CMP_64` (orderings), materialised by `#ADC_64` and
flipped by `^ 1` for the complemented codes. -/
def mcmpCode (c : JasminDialect.JasminCmp) (t t' x : MVarI) (ea eb : MPexpr) :
    List MInstrR :=
  let neq := [masgn t ea, masgn t (.Papp2 (.Olxor .U64) (mpv t) eb),
    mcopn "NEG_64" (mCWOuts t) [mpv t]]
  let below (e1 e2 : MPexpr) := [masgn t e1, masgn t' e2,
    mcopn "CMP_64" [mnb, .Lvar mcf, mnb, mnb, mnb] [mpv t, mpv t']]
  let mat := [masgn x (.Pconst 0), mcopn "ADC_64" (mWOuts x) [mpv x, mpv x, mpv mcf]]
  let flip := [masgn x (.Papp2 (.Olxor .U64) (mpv x) (.Pconst 1))]
  match c with
  | .ne => neq ++ mat
  | .eq => neq ++ mat ++ flip
  | .ult => below ea eb ++ mat
  | .uge => below ea eb ++ mat ++ flip
  | .ugt => below eb ea ++ mat
  | .ule => below eb ea ++ mat ++ flip

/-- **Comparison image.** The comparison idiom `cmpCode c U64 x ea eb` translates to
`mcmpCode c`. -/
theorem translateCmdExt_cmpCode (c : JasminDialect.JasminCmp) {x : JVar}
    {ea eb : CatCrypt.Crypto.Jasmin.PExpr} {x' t' t1' : MVarI} {ea' eb' : MPexpr}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x')
    (ht : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some t')
    (ht1 : translateVarIExt ⟨tmp 1 .U64, vi0⟩ = some t1')
    (hea : translatePExprExt ea = some ea') (heb : translatePExprExt eb = some eb') :
    translateCmdExt (cmpCode c .U64 x ea eb) = some (mkCmd (mcmpCode c t' t1' x' ea' eb')) := by
  have hneq : translateCmdExt [asgn (tmp 0 .U64) ea,
      asgn (tmp 0 .U64) (.Papp2 (.Olxor .U64) (pv (tmp 0 .U64)) eb),
      copn "NEG_64" (outsCW (tmp 0 .U64)) [pv (tmp 0 .U64)]] =
      some (mkCmd [masgn t' ea', masgn t' (.Papp2 (.Olxor .U64) (mpv t') eb'),
        mcopn "NEG_64" (mCWOuts t') [mpv t']]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn ht hea)
      (.cons (translateInstrRExt_asgn ht
        (translatePExprExt_papp2 rfl (translatePExprExt_pv ht) heb))
        (.cons (translateInstrRExt_copnCW opnNoneTys_NEG_64 ht
          (by simp [List.mapM_cons, translatePExprExt_pv ht])) .nil)))
  have hbelow : ∀ {e1 e2 : CatCrypt.Crypto.Jasmin.PExpr} {e1' e2' : MPexpr},
      translatePExprExt e1 = some e1' → translatePExprExt e2 = some e2' →
      translateCmdExt [asgn (tmp 0 .U64) e1, asgn (tmp 1 .U64) e2,
        copn "CMP_64" [none, some cfVar, none, none, none]
          [pv (tmp 0 .U64), pv (tmp 1 .U64)]] =
      some (mkCmd [masgn t' e1', masgn t1' e2',
        mcopn "CMP_64" [mnb, .Lvar mcf, mnb, mnb, mnb] [mpv t', mpv t1']]) := by
    intro e1 e2 e1' e2' h1 h2
    refine translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn ht h1)
      (.cons (translateInstrRExt_asgn ht1 h2) (.cons ?_ .nil)))
    have hl : ([none, some cfVar, none, none, none] : List (Option JVar)).length = 5 := rfl
    simp only [copn, hl, opnNoneTys_CMP_64]
    simp only [outLvs, List.replicate, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_bool,
      translateLValExt_lvv translateVarIExt_cf, translatePExprExt_pv ht,
      translatePExprExt_pv ht1]
    rfl
  have hflip : translateCmdExt [asgn x (.Papp2 (.Olxor .U64) (pv x) (cnst 1))] =
      some (mkCmd [masgn x' (.Papp2 (.Olxor .U64) (mpv x') (.Pconst 1))]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_cnst 1))) .nil)
  have hmat := translateCmdExt_matCF hx
  have hnN : asmName "NEG" .U64 = "NEG_64" := asmName_U64.2.1
  have hnC : asmName "CMP" .U64 = "CMP_64" := asmName_U64.2.2.1
  cases c <;> simp only [cmpCode, mcmpCode, mkCmd, List.map_append, hnN, hnC] <;>
    first
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hneq hmat) hflip
    | exact translateCmdExt_append_eq_some hneq hmat
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some (hbelow hea heb) hmat) hflip
    | exact translateCmdExt_append_eq_some (hbelow hea heb) hmat
    | exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some (hbelow heb hea) hmat) hflip
    | exact translateCmdExt_append_eq_some (hbelow heb hea) hmat

/-- **Mask-select image.** The binding of `select 64` to `x` on the condition `c` and the
words `a`, `b`, with the mask in the scratch word `m`: `m = c; m = -m; x = a; x = x ^ b;
x = x & m; x = x ^ b`. -/
theorem translateCmdExt_select {d : Nat} {x c a b : JVar} {x' c' a' b' m' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (hc : translateVarIExt ⟨c, vi0⟩ = some c')
    (ha : translateVarIExt ⟨a, vi0⟩ = some a') (hb : translateVarIExt ⟨b, vi0⟩ = some b')
    (hm : translateVarIExt ⟨tmp 0 .U64, vi0⟩ = some m') :
    (emitOp (.select 64) d x [c, a, b]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn m' (mpv c'), masgn m' (.Papp1 (.Oneg (.Op_w .U64)) (mpv m')),
        masgn x' (mpv a'), masgn x' (.Papp2 (.Olxor .U64) (mpv x') (mpv b')),
        masgn x' (.Papp2 (.Oland .U64) (mpv x') (mpv m')),
        masgn x' (.Papp2 (.Olxor .U64) (mpv x') (mpv b'))]) := by
  have he : emitOp (.select 64) d x [c, a, b] =
      some ([asgn (tmp 0 .U64) (pv c), asgn (tmp 0 .U64) (.Papp1 (.Oneg .U64) (pv (tmp 0 .U64))),
        asgn x (pv a), asgn x (.Papp2 (.Olxor .U64) (pv x) (pv b)),
        asgn x (.Papp2 (.Oland .U64) (pv x) (pv (tmp 0 .U64))),
        asgn x (.Papp2 (.Olxor .U64) (pv x) (pv b))], x) := rfl
  rw [he, Option.bind_some]
  exact translateCmdExt_mkCmd
    (.cons (translateInstrRExt_asgn hm (translatePExprExt_pv hc))
    (.cons (translateInstrRExt_asgn hm (translatePExprExt_papp1 rfl (translatePExprExt_pv hm)))
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hb)))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hm)))
    (.cons (translateInstrRExt_asgn hx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hx) (translatePExprExt_pv hb)))
      .nil))))))

/-- **High-multiply image.** The binding of `mulhi 64` to `x` on `a`, `b`:
`_, x = #MULX_lo_hi_64(a, b)`, the discarded low word typed `u64`. -/
theorem translateCmdExt_mulhi {d : Nat} {x a b : JVar} {x' a' b' : MVarI}
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hb : translateVarIExt ⟨b, vi0⟩ = some b') :
    (emitOp (.mulhi 64) d x [a, b]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [mcopn "MULX_lo_hi_64" [.Lnone () (.aword .U64), .Lvar x'] [mpv a', mpv b']]) := by
  have he : emitOp (.mulhi 64) d x [a, b] =
      some ([copn (asmName "MULX_lo_hi" .U64) [none, some x] [pv a, pv b]], x) := rfl
  have hn : asmName "MULX_lo_hi" .U64 = "MULX_lo_hi_64" := asmName_U64.2.2.2
  rw [he, Option.bind_some, hn]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  have hl : ([none, some x] : List (Option JVar)).length = 2 := rfl
  simp only [copn, hl, opnNoneTys_MULX_64]
  simp only [outLvs, List.getElem?_nil, Option.getD_none]
  simp only [translateInstrRExt, List.mapM_cons, List.mapM_nil, translateLValExt_lnone_u64,
    translateLValExt_lvv hx, translatePExprExt_pv ha, translatePExprExt_pv hb]
  rfl

/-- **Arithmetic-shift image.** The binding of `sarImm w n` to `x` on `a`:
`x = a; x = x >>s sarCount w n`, the count clamped to `w - 1`. -/
theorem translateCmdExt_sarImm {w n d : Nat} {x a : JVar} {x' a' : MVarI} {ws' : MWSize}
    (hws : translateWSize (wsOf w) = some ws')
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a') :
    (emitOp (.sarImm w n) d x [a]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn x' (mpv a'),
        masgn x' (.Papp2 (.Oasr (.Op_w ws')) (mpv x') (.Pconst (sarCount w n)))]) := by
  have he : emitOp (.sarImm w n) d x [a] =
      some ([asgn x (pv a), asgn x (.Papp2 (.Oasr (wsOf w)) (pv x) (cnst (sarCount w n)))], x) :=
    rfl
  rw [he, Option.bind_some]
  exact translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx (translatePExprExt_pv ha))
    (.cons (translateInstrRExt_asgn hx (translatePExprExt_papp2
      (by simp [translateSOp2Ext, translateSOp2, hws]) (translatePExprExt_pv hx)
      (translatePExprExt_cnst _))) .nil))

/-- The `(uint) i` index over a non-array local `i` translates to the unsigned
`int_of_word` of its mirror read. -/
theorem translateIdx_uint {i : JVar} {i' : MVarI} (hi : translateVarI ⟨i, vi0⟩ = some i') :
    translateIdx (.Papp1 (.Oint_of_word .U64) (pv i)) =
      some (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i')) := by
  simp [translateIdx, translatePExpr, translateSOp1, translateWSize, pv, translateGVar, hi,
    mpv, mkLvar]

/-- **Array-load image.** The binding of `stackLoad w k` to `x` on the array `a` and the
index `i`: `x = a[(uint) i]`. -/
theorem translateCmdExt_stackLoad {w k d : Nat} {x a i : JVar} {x' a' i' : MVarI}
    {ws' : MWSize} (hws : translateWSize (wsOf w) = some ws')
    (hx : translateVarIExt ⟨x, vi0⟩ = some x') (ha : translateVarIExt ⟨a, vi0⟩ = some a')
    (hi : translateVarI ⟨i, vi0⟩ = some i') :
    (emitOp (.stackLoad w k) d x [a, i]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [masgn x' (.Pget .Unaligned .AAscale ws' (mkLvar a')
        (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i')))]) := by
  have he : emitOp (.stackLoad w k) d x [a, i] =
      some ([asgn x (.Pget .AAscale (wsOf w) ⟨⟨a, vi0⟩, false⟩
        (.Papp1 (.Oint_of_word .U64) (pv i)))], x) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hx ?_) .nil)
  simp [translatePExprExt, hws, translateGVarExt, ha, translateIdx_uint hi, translateArrAccess,
    mkLvar]

/-- **Array-store image.** The binding of `stackStore w k` on the array `a`, the index `i`
and the value `v`: `a[(uint) i] = v`, in place. -/
theorem translateCmdExt_stackStore {w k d : Nat} {x a i v : JVar} {a' i' v' : MVarI}
    {ws' : MWSize} (hws : translateWSize (wsOf w) = some ws')
    (ha : translateVarIExt ⟨a, vi0⟩ = some a') (hi : translateVarI ⟨i, vi0⟩ = some i')
    (hv : translateVarIExt ⟨v, vi0⟩ = some v') :
    (emitOp (.stackStore w k) d x [a, i, v]).bind (fun r => translateCmdExt r.1) =
      some (mkCmd [.Cassgn (.Laset .Unaligned .AAscale ws' a'
        (.Papp1 (.Oint_of_word .Unsigned .U64) (mpv i'))) .AT_none (.aword ws') (mpv v')]) := by
  have he : emitOp (.stackStore w k) d x [a, i, v] =
      some ([.Cassgn (.Laset .AAscale (wsOf w) ⟨a, vi0⟩ (.Papp1 (.Oint_of_word .U64) (pv i)))
        .AT_none (.sword (wsOf w)) (pv v)], a) := rfl
  rw [he, Option.bind_some]
  refine translateCmdExt_mkCmd (.cons ?_ .nil)
  simp [translateInstrRExt, translateLValExt, hws, ha, translateIdx_uint hi, translateArrAccess,
    translateSTypeExt, translateSType, translatePExprExt_pv hv, translateAssgnTag]

/-- The condition `v != 0` translates to `mnz`. -/
theorem translatePExprExt_nz {v : JVar} {v' : MVarI} (hv : translateVarIExt ⟨v, vi0⟩ = some v') :
    translatePExprExt (nz v) = some (mnz v') :=
  translatePExprExt_papp2 rfl (translatePExprExt_pv hv) (translatePExprExt_cnst 0)

/-- **Counter-loop frame image.** The frame `forCode` of a counted loop translates to the
translated seeds, the trip index and counter initialisations, the mirror loop
`while (ctr != 0)` over the translated body, moves and advance, and the translated moves
after the loop. -/
theorem translateCmdExt_forCode {env : List JVar} {d n ci : Nat}
    {cs : List JasminDialect.JasminTy} {inits : List JVar} {b : JOut}
    {s1 body pm s2 : List MInstr} {idx' ctr' cnt' : MVarI}
    (hs1 : translateCmdExt (seqMoves ((blockVars (d + 1) cs).zip inits)) = some s1)
    (hidx : translateVarIExt ⟨mkV 'r' d u64, vi0⟩ = some idx')
    (hctr : translateVarIExt ⟨mkV 'c' n u64, vi0⟩ = some ctr')
    (hcnt : translateVarIExt ⟨env.getD ci dfltV, vi0⟩ = some cnt')
    (hb : translateCmdExt b.code = some body)
    (hpm : translateCmdExt (parMovesJ b.depth ((blockVars (d + 1) cs).zip b.res)) = some pm)
    (hs2 : translateCmdExt (seqMoves ((blockVars d cs).zip (blockVars (d + 1) cs)).reverse) =
      some s2) :
    translateCmdExt (forCode env d n cs inits ci b) =
      some (s1 ++ mkCmd [masgn idx' (.Pconst 0), masgn ctr' (mpv cnt'),
        .Cwhile .NoAlign [] (mnz ctr') () (body ++ pm ++ mkCmd
          [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
           masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))])] ++ s2) := by
  have hadv : translateCmdExt
      [asgn (mkV 'r' d u64) (.Papp2 (.Oadd .U64) (pv (mkV 'r' d u64)) (cnst 1)),
       asgn (mkV 'c' n u64) (.Papp2 (.Osub .U64) (pv (mkV 'c' n u64)) (cnst 1))] =
      some (mkCmd [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
        masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))]) :=
    translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hidx
      (translatePExprExt_papp2 rfl (translatePExprExt_pv hidx) (translatePExprExt_cnst 1)))
      (.cons (translateInstrRExt_asgn hctr
        (translatePExprExt_papp2 rfl (translatePExprExt_pv hctr) (translatePExprExt_cnst 1)))
        .nil))
  have hloop := translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hb hpm) hadv
  have hw : translateInstrRExt (.Cwhile [] (nz (mkV 'c' n u64)) (b.code ++
      parMovesJ b.depth ((blockVars (d + 1) cs).zip b.res) ++
      [asgn (mkV 'r' d u64) (.Papp2 (.Oadd .U64) (pv (mkV 'r' d u64)) (cnst 1)),
       asgn (mkV 'c' n u64) (.Papp2 (.Osub .U64) (pv (mkV 'c' n u64)) (cnst 1))])) =
      some (.Cwhile .NoAlign [] (mnz ctr') () (body ++ pm ++ mkCmd
        [masgn idx' (.Papp2 (.Oadd (.Op_w .U64)) (mpv idx') (.Pconst 1)),
         masgn ctr' (.Papp2 (.Osub (.Op_w .U64)) (mpv ctr') (.Pconst 1))])) := by
    simp only [translateInstrRExt, translateCmdExt, translatePExprExt_nz hctr, hloop]
  have hmid := translateCmdExt_mkCmd (.cons (translateInstrRExt_asgn hidx
    (translatePExprExt_cnst 0)) (.cons (translateInstrRExt_asgn hctr (translatePExprExt_pv hcnt))
    (.cons hw .nil)))
  exact translateCmdExt_append_eq_some (translateCmdExt_append_eq_some hs1 hmid) hs2

/-- **Exit-flag loop image.** The frame `whileCode` translates to the translated seeds and
the mirror loop `while { body; flag = r; moves } (flag != 0)`. -/
theorem translateCmdExt_whileCode {d : Nat} {cs : List JasminDialect.JasminTy}
    {inits : List JVar} {b : JOut} {s1 body pm : List MInstr} {flag' r' : MVarI}
    (hs1 : translateCmdExt (seqMoves ((blockVars d cs).zip inits)) = some s1)
    (hb : translateCmdExt b.code = some body)
    (hflag : translateVarIExt ⟨mkV 'r' (b.depth + cs.length) u64, vi0⟩ = some flag')
    (hr : translateVarIExt ⟨b.res.headD dfltV, vi0⟩ = some r')
    (hpm : translateCmdExt (parMovesJ b.depth ((blockVars d cs).zip b.res.tail)) = some pm) :
    translateCmdExt (whileCode d cs inits b) =
      some (s1 ++ mkCmd [.Cwhile .NoAlign (body ++ .MkI () (masgn flag' (mpv r')) :: pm)
        (mnz flag') () []]) := by
  have hbody := translateCmdExt_append_eq_some hb
    (translateCmdExt_cons (translateInstrRExt_asgn hflag (translatePExprExt_pv hr)) hpm)
  have hi : translateInstrRExt (.Cwhile (b.code ++
      asgn (mkV 'r' (b.depth + cs.length) u64) (pv (b.res.headD dfltV)) ::
        parMovesJ b.depth ((blockVars d cs).zip b.res.tail))
      (nz (mkV 'r' (b.depth + cs.length) u64)) []) =
      some (.Cwhile .NoAlign (body ++ .MkI () (masgn flag' (mpv r')) :: pm) (mnz flag') () []) := by
    simp only [translateInstrRExt, translateCmdExt, translatePExprExt_nz hflag, hbody]
  exact translateCmdExt_append_eq_some hs1 (translateCmdExt_mkCmd (.cons hi .nil))

/-- **Branch image.** The branch `ifCode` translates to the mirror `if (c != 0)` over the
translated branches, each followed by its translated join moves. -/
theorem translateInstrRExt_ifCode {env : List JVar} {d ci : Nat}
    {rs : List JasminDialect.JasminTy} {bt be : JOut} {c' : MVarI}
    {t' e' pmt pme : List MInstr}
    (hc : translateVarIExt ⟨env.getD ci dfltV, vi0⟩ = some c')
    (ht : translateCmdExt bt.code = some t') (he : translateCmdExt be.code = some e')
    (hpt : translateCmdExt (parMovesJ (bt.depth + rs.length) ((blockVars d rs).zip bt.res)) =
      some pmt)
    (hpe : translateCmdExt (parMovesJ (be.depth + rs.length) ((blockVars d rs).zip be.res)) =
      some pme) :
    translateInstrRExt (ifCode env d rs ci bt be) =
      some (.Cif (mnz c') (t' ++ pmt) (e' ++ pme)) := by
  simp only [ifCode, translateInstrRExt, translatePExprExt_nz hc, translateCmdExt_append_eq_some ht hpt,
    translateCmdExt_append_eq_some he hpe]

/-- **Call image.** The call of `f` with the result variables `xs` and the argument
variables `as` translates to the mirror call with the translated l-values and reads. -/
theorem translateInstrRExt_call (f : String) {xs as : List JVar} {xs' as' : List MVarI}
    (hxs : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') xs xs')
    (has : List.Forall₂ (fun x x' => translateVarIExt ⟨x, vi0⟩ = some x') as as') :
    translateInstrRExt (.Ccall .DoNotInline (xs.map lvv) ⟨f⟩ (as.map pv)) =
      some (.Ccall (xs'.map .Lvar) { name := f } (as'.map mpv)) := by
  simp only [translateInstrRExt, mapM_lvv hxs, mapM_pv has]

end CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz
