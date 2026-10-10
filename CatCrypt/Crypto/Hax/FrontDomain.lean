/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF

/-!
# The domain of the front `impToNF`

The front `ImpToNF.impToNF` translates an expression of a fragment of `ImpExpr` and returns
`none` on every other expression. This file states the boundary of that fragment as a
function: `frontOut` has the recursion of `impToNF` and returns, in place of `none`, the
first construct the translation does not accept, as a `Refusal`. Forgetting the refusal
gives `impToNF` (`toOption_frontOut`), so `frontRefusal?` returns no refusal exactly on the
expressions `impToNF` translates (`frontRefusal?_eq_none_iff`).

The order is that of `impToNF`: sub-expressions left to right, a condition before its arms,
the bounds of a loop before its body, the arguments of a call before the typing of its head.

## Main definitions

* `Refusal` — a construct outside the fragment: the kind, with the head, the name or the
  types concerned.
* `ModuleRefusal` — a refusal of the translation of a module: a callee with the name of an
  array operation, a function failing a shape condition, a linked function with a reserved
  name, a refusal of the entry, or calls left after the rounds of inlining.
* `frontOut`, `frontArgs` — `impToNF` and `impArgsNF` with the refusal.
* `frontRefusal?` — the refusal of `frontOut`, if any.

## Main results

* `toOption_frontOut`, `toOption_frontArgs` — forgetting the refusal gives `impToNF` and
  `impArgsNF`.
* `frontRefusal?_eq_none_iff` — no refusal exactly when `impToNF` returns a program.
* `frontRefusal?_eq_some_iff` — a refusal exactly when `impToNF` returns `none`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.FrontDomain

open _root_.Hax (ImpExpr ImpLit)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open Ctxt (Var)

/-! ## 1. Refusals -/

/-- The name of the constructor of an expression, as a construct of the source. -/
def exprHead : ImpExpr → String
  | .lit _ => "literal"
  | .var _ => "variable"
  | .letBind .. => "let"
  | .lam .. => "closure"
  | .app .. => "call"
  | .tuple _ => "tuple"
  | .proj .. => "tuple projection"
  | .ifThenElse .. => "if-then-else"
  | .match_ .. => "match"
  | .unitVal => "unit"
  | .seq .. => "seq"
  | .borrow _ => "borrow"
  | .deref _ => "deref"
  | .assign .. => "assign"
  | .forLoop .. => "for loop"
  | .forLoopRev .. => "reverse for loop"
  | .whileLoop .. => "while loop"
  | .break_ _ => "break"
  | .continue_ => "continue"
  | .earlyReturn _ => "early return"
  | .questionMark _ => "question mark"
  | .forFold .. => "forFold"
  | .forFoldRev .. => "reverse forFold"
  | .whileFold .. => "whileFold"
  | .forFoldReturn .. => "forFold with return"
  | .forFoldRevReturn .. => "reverse forFold with return"
  | .whileFoldReturn .. => "whileFold with return"
  | .cfBreak _ => "cfBreak"
  | .cfContinue _ => "cfContinue"
  | .cfBreakContinue _ => "cfBreakContinue"
  | .typeAscription .. => "type ascription"

/-- A short rendering of a type of `nfDialect`. -/
def tyName : NfTy → String
  | .bit => "bit"
  | .unit => "unit"
  | .word w => s!"w{w}"
  | .arr n t => s!"[{tyName t}; {n}]"
  | .pair a b => s!"({tyName a}, {tyName b})"
  | .uint W => s!"u{W.bits}"
  | .sint W => s!"i{W.bits}"
  | .int => "int"
  | .tnil => "()"
  | .tcons h t => s!"({tyName h} :: {tyName t})"
  | .slice t => s!"[{tyName t}]"

/-- **A construct `impToNF` does not accept.** -/
inductive Refusal where
  /-- An expression whose constructor has no arm in `impToNF`: a closure, a projection, a
      `match`, a borrow, an exit, or a loop other than `forFold` and `forFoldRev`. -/
  | construct (head : String)
  /-- A name the environment of names does not bind. -/
  | unbound (x : String)
  /-- An integer literal outside the range of its type. -/
  | literal (l : ImpLit)
  /-- A call whose head the call typing does not type at the types of its arguments. -/
  | call (f : String) (as : List NfTy)
  /-- A component of a tuple or an upper bound of a loop that is not a name or a literal. -/
  | operand (head : String)
  /-- A `forFold` or `forFoldRev` whose lower bound is not an integer literal. -/
  | loopLower (head : String)
  /-- A `forFold` whose bounds pass neither `boundOk` nor `litBoundOk`, with the type of the
      upper bound. -/
  | loopBound (t : NfTy)
  /-- A name a loop carries that its body leaves unbound or at another type. -/
  | loopCarried (x : String)
  /-- A conditional whose condition does not have the bit type. -/
  | condType (t : NfTy)
  /-- A conditional whose arms have different result types. -/
  | armTypes (a b : NfTy)
  /-- A name a conditional carries that an arm leaves unbound or at another type. -/
  | armCarried (x : String)

/-- The rendering of a refusal. -/
def Refusal.toString : Refusal → String
  | .construct h => h
  | .unbound x => s!"unbound name {x}"
  | .literal l =>
      match litInt l with
      | some (t, v) => s!"literal {v} outside {tyName t}"
      | none => "literal"
  | .call f as => s!"call {f}({", ".intercalate (as.map tyName)})"
  | .operand h => s!"non-atom operand ({h})"
  | .loopLower h => s!"forFold with a non-literal lower bound ({h})"
  | .loopBound t => s!"loop bound of type {tyName t}"
  | .loopCarried x => s!"loop-carried {x} changes type"
  | .condType t => s!"condition of type {tyName t}"
  | .armTypes a b => s!"arms of types {tyName a} and {tyName b}"
  | .armCarried x => s!"name {x} changes type in an arm"

instance : ToString Refusal := ⟨Refusal.toString⟩

/-- **A refusal of the translation of a module**, in the order of the translation. -/
inductive ModuleRefusal where
  /-- A callee has the name of an array operation (`len`, `index`, `array_update`). -/
  | arrayOpName (f : String)
  /-- The extraction of the callee `f` fails the shape condition `cond` of the front. -/
  | calleeShape (f : String) (cond : String)
  /-- A linked function has a name the base table answers or the translation reads. -/
  | linkedName (f : String)
  /-- The extraction of the entry fails the shape condition `cond` of the front. -/
  | entryShape (cond : String)
  /-- The first construct of the entry `impToNF` does not accept. -/
  | entry (r : Refusal)
  /-- The inlining of the calls of the callees refuses: a round has no body for a call, or a
      call of a callee is left after the `rounds` rounds. -/
  | inline (rounds : Nat)

/-- The rendering of a refusal of a module. -/
def ModuleRefusal.toString : ModuleRefusal → String
  | .arrayOpName f => s!"callee {f} has the name of an array operation"
  | .calleeShape f c => s!"callee {f}: {c}"
  | .linkedName f => s!"linked function {f} has a reserved name"
  | .entryShape c => c
  | .entry r => r.toString
  | .inline n => s!"a call of a callee is left after {n} rounds of inlining"

instance : ToString ModuleRefusal := ⟨ModuleRefusal.toString⟩

/-- The stage of `haxToNF` at which a refusal of a module arises: `module` for a condition
    on the callees or the linked functions, `front` for the shape condition on the entry,
    `impToNF` for a construct of the entry, `inline` for the inlining. -/
def ModuleRefusal.stage : ModuleRefusal → String
  | .arrayOpName _ => "module"
  | .calleeShape _ _ => "module"
  | .linkedName _ => "module"
  | .entryShape _ => "front"
  | .entry _ => "impToNF"
  | .inline _ => "inline"

/-! ## 2. Results with a refusal -/

/-- The value of an option, or the refusal `r`. -/
def orRefuse {α : Type} (r : Refusal) : Option α → Except Refusal α
  | some a => .ok a
  | none => .error r

theorem toOption_orRefuse {α : Type} (r : Refusal) (o : Option α) :
    (orRefuse r o).toOption = o := by
  cases o <;> rfl

theorem toOption_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) :
    (x.bind f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

theorem toOption_map {ε α β : Type} (x : Except ε α) (f : α → β) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

/-! ## 3. The front with the refusal -/

/-- The refusal of an expression that `atomOut` does not accept. -/
def atomRefusal : ImpExpr → Refusal
  | .var x => .unbound x
  | .lit l => .literal l
  | e => .operand (exprHead e)

/-- `atomOut` with the refusal. -/
def atomE {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) : Except Refusal (Out Γ) :=
  orRefuse (atomRefusal e) (atomOut σ e)

/-- `argsOut` with the refusal. -/
def atomsE {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : List ImpExpr → Except Refusal (ArgsOut Γ)
  | [] => .ok ⟨Γ, [], .nil, σ, .nil⟩
  | e :: es => (atomE σ e).bind fun o => (atomsE o.σ es).map fun os =>
      ⟨os.Δ, o.t :: os.as, o.pre.append os.pre, os.σ, .cons (os.pre.wk o.res) os.vs⟩

theorem toOption_atomsE {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (es : List ImpExpr) :
    (atomsE σ es).toOption = argsOut σ es := by
  induction es generalizing Γ with
  | nil => rfl
  | cons e es ih =>
      simp only [atomsE, argsOut, toOption_bind, toOption_map, atomE, toOption_orRefuse, ih]

/-- The first of the names `xs` that `σ` does not bind at its type of `cs`; the empty name
    when there is none. -/
def carriedMiss {Δ : Ctxt nfDialect} (σ : NfEnv Δ) : List String → List NfTy → String
  | x :: xs, c :: cs =>
      if (σ.lookup x).map (·.1) = some c then carriedMiss σ xs cs else x
  | _, _ => ""

/-- `loopOut` with the refusal: that of the body `rec`, or the carried name the body leaves
    unbound or at another type. -/
def loopE {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String) (pre₀ : NFPre nfDialect Γ Γ₃)
    (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Except Refusal (Out Δ)) :
    Except Refusal (Out Γ) :=
  let σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃) :=
    loopEnv σ₃ i xs cs (headVars cs) fun v => Var.shiftApp (d := nfDialect) cs v.there
  let oC := ctrOut cs i σB loV rev
  (rec ((i, ⟨oC.t, oC.res⟩) :: oC.σ)).bind fun ob =>
    orRefuse (.loopCarried (carriedMiss ob.σ xs cs)) <| (varsAt ob.σ xs cs).map fun rets =>
      let oU := bind1N tgt (loopEnv σ₃ i xs cs (headVars cs) fun v => Var.shiftApp cs v)
        .constUnit .nil
      Out.mk oU.Δ oU.t
        (pre₀.append (.forLoop tripV inits ((oC.pre.append ob.pre).plug (.ret rets)) oU.pre))
        oU.σ oU.res

theorem toOption_loopE {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String)
    (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Except Refusal (Out Δ)) :
    (loopE tgt pre₀ σ₃ loV tripV rev i xs cs inits rec).toOption =
      loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits fun σ => (rec σ).toOption := by
  simp only [loopE, loopOut, toOption_bind, toOption_orRefuse]

/-- `condOut` with the refusal: that of the first arm, then that of the second, then the
    different result types of the arms, or the carried name an arm leaves unbound or at
    another type. -/
def condE {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc) (σc : NfEnv Γc)
    (cV : Var Γc NfTy.bit) (xs : List String) (cs : List NfTy)
    (recA recB : Except Refusal (Out Γc)) : Except Refusal (Out Γ) :=
  recA.bind fun oa => recB.bind fun ob =>
    orRefuse
      (if ob.t = oa.t then
        .armCarried
          (if carriedMiss oa.σ xs cs = "" then carriedMiss ob.σ xs cs
            else carriedMiss oa.σ xs cs)
      else .armTypes oa.t ob.t)
      (condOut pre₀ σc cV xs cs (some oa) (some ob))

theorem toOption_condE {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc) (σc : NfEnv Γc)
    (cV : Var Γc NfTy.bit) (xs : List String) (cs : List NfTy)
    (recA recB : Except Refusal (Out Γc)) :
    (condE pre₀ σc cV xs cs recA recB).toOption =
      condOut pre₀ σc cV xs cs recA.toOption recB.toOption := by
  cases recA with
  | error r => rfl
  | ok oa =>
      cases recB with
      | error r => rfl
      | ok ob => exact toOption_orRefuse _ _

mutual
/-- **The front with the refusal**: the recursion of `impToNF`, returning in place of `none`
    the first construct the translation does not accept. -/
def frontOut (sigOf : String → List NfTy → Option NfTy) :
    Option String → {Γ : Ctxt nfDialect} → NfEnv Γ → ImpExpr → Except Refusal (Out Γ)
  | _, _, σ, .var x => atomE σ (.var x)
  | tgt, _, σ, .lit l => orRefuse (.literal l) (litOut tgt σ l)
  | tgt, _, σ, .unitVal => .ok (bind1N tgt σ .constUnit .nil)
  | tgt, _, σ, .typeAscription e _ => frontOut sigOf tgt σ e
  | tgt, _, σ, .seq a b => (frontOut sigOf none σ a).bind fun oa =>
      (frontOut sigOf tgt oa.σ b).map oa.comp
  | tgt, _, σ, .letBind x v b => (frontOut sigOf (some x) σ v).bind fun ov =>
      (frontOut sigOf tgt ((x, ⟨ov.t, ov.res⟩) :: ov.σ) b).map ov.comp
  | tgt, _, σ, .assign x r => (frontOut sigOf (some x) σ r).map fun o =>
      o.comp (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil)
  | tgt, _, σ, .app f args => (frontArgs sigOf σ args).bind fun oa =>
      orRefuse (.call f oa.as) <| (sigOf f oa.as).map fun r =>
      ⟨r :: oa.Δ, r, oa.pre.append (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil),
        oa.σ.mapV .there, .here⟩
  | tgt, _, σ, .tuple es => (atomsE σ es).map fun oa =>
      let r := tupleOut tgt oa.as oa.vs
      Out.mk r.fst (tupTy oa.as) (oa.pre.append r.snd.fst) (oa.σ.mapV r.snd.fst.wk) r.snd.snd
  | tgt, _, σ, .forFold i (.lit (.int lo)) hi body =>
      let oLo := bind1 σ (.ilit .int lo) .nil
      (atomE oLo.σ hi).bind fun oHi =>
        if boundOk lo oHi.t || litBoundOk lo hi then
          let oT := bind1 oHi.σ (.trip oHi.t) (.cons (oHi.pre.wk oLo.res) (.cons oHi.res .nil))
          let W := carried oT.σ i body
          loopE tgt ((oLo.pre.append oHi.pre).append oT.pre) oT.σ
            (oT.pre.wk (oHi.pre.wk oLo.res))
            oT.res none i (W.map (·.1)) (entriesVars W).1 (entriesVars W).2
            (fun σB => frontOut sigOf none σB body)
        else .error (.loopBound oHi.t)
  | tgt, _, σ, .forFoldRev i (.lit (.int lo)) hi body =>
      let oLo := bind1 σ (.ilit .int lo) .nil
      (atomE oLo.σ hi).bind fun oHi =>
        if boundOk lo oHi.t || litBoundOk lo hi then
          let oT := bind1 oHi.σ (.trip oHi.t) (.cons (oHi.pre.wk oLo.res) (.cons oHi.res .nil))
          let oOne := bind1 oT.σ (.ilit (.word 64) 1) .nil
          let oM := bind1 oOne.σ (.bin .sub 64) (.cons (oOne.pre.wk oT.res) (.cons oOne.res .nil))
          let W := carried oM.σ i body
          loopE tgt ((((oLo.pre.append oHi.pre).append oT.pre).append oOne.pre).append oM.pre)
            oM.σ (oM.pre.wk (oOne.pre.wk (oT.pre.wk (oHi.pre.wk oLo.res))))
            (oM.pre.wk (oOne.pre.wk oT.res)) (some oM.res) i (W.map (·.1)) (entriesVars W).1
            (entriesVars W).2 (fun σB => frontOut sigOf none σB body)
        else .error (.loopBound oHi.t)
  | _, _, σ, .ifThenElse c a b => (frontOut sigOf none σ c).bind fun oc =>
      if h : oc.t = NfTy.bit then
        let W := condCarried oc.σ a b
        condE oc.pre oc.σ (h ▸ oc.res) (W.map (·.1)) (entriesVars W).1
          (frontOut sigOf none oc.σ a) (frontOut sigOf none oc.σ b)
      else .error (.condType oc.t)
  | _, _, _, .forFold _ lo _ _ => .error (.loopLower (exprHead lo))
  | _, _, _, .forFoldRev _ lo _ _ => .error (.loopLower (exprHead lo))
  | _, _, _, e => .error (.construct (exprHead e))

/-- `impArgsNF` with the refusal. -/
def frontArgs (sigOf : String → List NfTy → Option NfTy) :
    {Γ : Ctxt nfDialect} → NfEnv Γ → List ImpExpr → Except Refusal (ArgsOut Γ)
  | Γ, σ, [] => .ok ⟨Γ, [], .nil, σ, .nil⟩
  | _, σ, e :: es => (frontOut sigOf none σ e).bind fun o =>
      (frontArgs sigOf o.σ es).map fun os =>
      ⟨os.Δ, o.t :: os.as, o.pre.append os.pre, os.σ, .cons (os.pre.wk o.res) os.vs⟩
end

/-! ## 4. Agreement with `impToNF` -/

/-- Forgetting the refusal of `frontArgs` gives `impArgsNF`, when it does for `frontOut` on
    each argument. -/
theorem toOption_frontArgs (sigOf : String → List NfTy → Option NfTy) (args : List ImpExpr)
    (ih : ∀ e ∈ args, ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ),
      (frontOut sigOf tgt σ e).toOption = impToNF sigOf tgt σ e) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ),
      (frontArgs sigOf σ args).toOption = impArgsNF sigOf σ args := by
  induction args with
  | nil =>
      intro Γ σ
      simp only [frontArgs, impArgsNF, Except.toOption]
  | cons e es ihes =>
      intro Γ σ
      simp only [frontArgs, impArgsNF, toOption_bind, toOption_map,
        ih e List.mem_cons_self, ihes fun a ha => ih a (List.mem_cons_of_mem _ ha)]

/-- **Forgetting the refusal of `frontOut` gives `impToNF`.** -/
theorem toOption_frontOut (sigOf : String → List NfTy → Option NfTy) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ),
      (frontOut sigOf tgt σ e).toOption = impToNF sigOf tgt σ e := by
  induction e using ImpExpr.ind
  case lit l =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_orRefuse]
  case var x =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, atomE, toOption_orRefuse]
  case letBind x v b ihv ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, toOption_map, ihv, ihb]
  case seq a b iha ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, toOption_map, iha, ihb]
  case assign x r ih =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_map, ih]
  case typeAscription e s ih =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, ih]
  case app f args iha =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, toOption_orRefuse,
      toOption_frontArgs sigOf args iha]
  case tuple es _ =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_map, toOption_atomsE]
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ
    cases lo with
    | lit l =>
      cases l with
      | int n =>
        simp only [frontOut, impToNF, toOption_bind, atomE, toOption_orRefuse]
        congr 1
        funext oHi
        split
        · refine (toOption_loopE _ _ _ _ _ _ _ _ _ _ _).trans ?_
          congr 1
          funext Δ σB
          exact ihb _ _
        · rfl
      | _ => rfl
    | _ => rfl
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ
    cases lo with
    | lit l =>
      cases l with
      | int n =>
        simp only [frontOut, impToNF, toOption_bind, atomE, toOption_orRefuse]
        congr 1
        funext oHi
        split
        · refine (toOption_loopE _ _ _ _ _ _ _ _ _ _ _).trans ?_
          congr 1
          funext Δ σB
          exact ihb _ _
        · rfl
      | _ => rfl
    | _ => rfl
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, ihc]
    congr 1
    funext oc
    split
    · simp only [toOption_condE, iha, ihb]
    · rfl
  all_goals
    intro tgt Γ σ
    rfl

/-- **The refusal of the front**: the first construct of `e` that `impToNF` does not accept
    at the call typing `sigOf` from the environment of names `σ`, and `none` when there is
    none. -/
def frontRefusal? (sigOf : String → List NfTy → Option NfTy) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) : Option Refusal :=
  match frontOut sigOf tgt σ e with
  | .ok _ => none
  | .error r => some r

/-- **The front refuses nothing exactly when `impToNF` returns a program.** -/
theorem frontRefusal?_eq_none_iff (sigOf : String → List NfTy → Option NfTy)
    (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) :
    frontRefusal? sigOf tgt σ e = none ↔ (impToNF sigOf tgt σ e).isSome = true := by
  rw [← toOption_frontOut, frontRefusal?]
  cases frontOut sigOf tgt σ e <;> simp [Except.toOption]

/-- **The front returns a refusal exactly when `impToNF` returns no program.** -/
theorem frontRefusal?_eq_some_iff (sigOf : String → List NfTy → Option NfTy)
    (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) :
    (∃ r, frontRefusal? sigOf tgt σ e = some r) ↔ impToNF sigOf tgt σ e = none := by
  rw [← toOption_frontOut, frontRefusal?]
  cases frontOut sigOf tgt σ e <;> simp [Except.toOption]

end CatCrypt.Crypto.Hax.FrontDomain
