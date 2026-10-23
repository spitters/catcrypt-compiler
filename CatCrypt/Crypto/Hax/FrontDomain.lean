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
  name or a signature other than words and word arrays, a callee with an integer-slice type,
  a refusal of the entry, or calls left after the rounds of inlining.
* `callRefusal` — the refusal of an untyped call: a tagged field head at a modulus without a
  template (`ImpToNF.fieldModOk`), or a call the call typing does not type.
* `loRefusal`, `loE` — the refusal of a lower bound of a counted loop, and `loOut` with it.
* `frontOut`, `frontArgs` — `impToNF` and `impArgsNF` with the refusal.
* `frontRefusal?` — the refusal of `frontOut`, if any.
* `ilitWordOp`, `opsProg`, `opsPre` — an operation that is not an integer literal or is one in
  `[0, 2 ^ 64)` at the integer type, the `64`-bit words or an unsigned width of at most `64`
  bits; a check on every operation of a program and of a prefix.

## Main results

* `toOption_frontOut`, `toOption_frontArgs` — forgetting the refusal gives `impToNF` and
  `impArgsNF`.
* `frontRefusal?_eq_none_iff` — no refusal exactly when `impToNF` returns a program.
* `frontRefusal?_eq_some_iff` — a refusal exactly when `impToNF` returns `none`.
* `impToNF_ilitWord`, `frontOut_ilit_word` — every integer literal of the prefix `impToNF`
  returns satisfies `ilitWordOp`; with no refusal, `impToNF` returns such a prefix.
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
  /-- An expression whose constructor has no arm in `impToNF`: a closure, a `match`, a
      borrow, an exit, or a loop other than `forFold`, `forFoldRev` and `whileFold` on a
      name. -/
  | construct (head : String)
  /-- A name the environment of names does not bind. -/
  | unbound (x : String)
  /-- An integer literal outside the domain of the front (`litInt`): an integer literal
      outside `[0, 2 ^ 64)`, a literal of a signed width, or a literal of a width above
      `64` bits. -/
  | literal (l : ImpLit)
  /-- A call whose head the call typing does not type at the types of its arguments. -/
  | call (f : String) (as : List NfTy)
  /-- A call of a tagged field head `f` (`Hax.FieldTag.fieldTag?`) at a modulus `p` without a
      field template (`ImpToNF.fieldModOk`). -/
  | fieldModulus (f : String) (p : Nat)
  /-- A component of a tuple or an upper bound of a loop that is not a name or a literal. -/
  | operand (head : String)
  /-- A `forFold` or `forFoldRev` whose lower bound is neither an integer literal nor a name of
      a type `loTyOk` accepts, with its head or with the name and its type. -/
  | loopLower (head : String)
  /-- A `forFold` or `forFoldRev` whose upper bound passes neither `boundOk` nor `litBoundOk`,
      with the type of the lower bound (`int` for a literal) and that of the upper bound. -/
  | loopBound (lo t : NfTy)
  /-- A name a loop carries that its body leaves unbound or at another type. -/
  | loopCarried (x : String)
  /-- A conditional whose condition does not have the bit type. -/
  | condType (t : NfTy)
  /-- A conditional whose arms have different result types. -/
  | armTypes (a b : NfTy)
  /-- A name a conditional carries that an arm leaves unbound or at another type. -/
  | armCarried (x : String)
  /-- A call of `repeat` whose count is not an integer literal in `[0, 2 ^ 64)`; `impToNF`
      translates a call of `repeat` only at such a count (`repeatArgs?`). -/
  | arrayFill
  /-- A projection of the component `i` of a value of the type `t` that is not a tuple type
      with more than `i` components (`projOut`). -/
  | projection (t : NfTy) (i : Nat)
  /-- A `whileFold` whose flag, after the carried names are bound, is a name of the type `t`
      other than the bit type (`whileOut`). -/
  | whileGuard (t : NfTy)

/-- The rendering of a refusal. -/
def Refusal.toString : Refusal → String
  | .construct h => h
  | .unbound x => s!"unbound name {x}"
  | .literal l =>
      match l with
      | .int n => s!"integer literal {n} outside [0, 2^64)"
      | .uintLit W n => s!"literal {n} of width u{W.bits} above 64 bits"
      | .sintLit W n => s!"literal {n} of signed width i{W.bits}"
      | _ => "literal"
  | .call f as => s!"call {f}({", ".intercalate (as.map tyName)})"
  | .fieldModulus f p => s!"field call {f} at the modulus {p} without a template"
  | .operand h => s!"non-atom operand ({h})"
  | .loopLower h => s!"loop lower bound ({h}) neither a literal nor a word or unsigned name"
  | .loopBound lo t => s!"loop bounds of types {tyName lo} and {tyName t}"
  | .loopCarried x => s!"loop-carried {x} changes type"
  | .condType t => s!"condition of type {tyName t}"
  | .armTypes a b => s!"arms of types {tyName a} and {tyName b}"
  | .armCarried x => s!"name {x} changes type in an arm"
  | .whileGuard t => s!"while flag of type {tyName t}"
  | .arrayFill => "array fill (call repeat)"
  | .projection t i => s!"projection {i} of a value of type {tyName t}"

instance : ToString Refusal := ⟨Refusal.toString⟩

/-- **A refusal of the translation of a module**, in the order of the translation. -/
inductive ModuleRefusal where
  /-- A callee has the name of an array operation (`len`, `index`, `array_update`). -/
  | arrayOpName (f : String)
  /-- The extraction of the callee `f` fails the shape condition `cond` of the front. -/
  | calleeShape (f : String) (cond : String)
  /-- A linked function has a name the base table answers or the translation reads. -/
  | linkedName (f : String)
  /-- A linked function has a parameter or a result whose type is neither the `64`-bit word
      nor an array of `64`-bit words. -/
  | linkedSig (f : String)
  /-- A parameter or the result of the callee `f` has a type containing an integer slice
      (`.slice .int`). -/
  | intSlice (f : String)
  /-- The extraction of the entry fails the shape condition `cond` of the front. -/
  | entryShape (cond : String)
  /-- The first construct of the entry `impToNF` does not accept. -/
  | entry (r : Refusal)
  /-- The result of the entry has the type `t`: the unit type or a tuple. -/
  | entryResult (t : String)
  /-- The inlining of the calls of the callees refuses: a round has no body for a call, or a
      call of a callee is left after the `rounds` rounds. -/
  | inline (rounds : Nat)

/-- The rendering of a refusal of a module. -/
def ModuleRefusal.toString : ModuleRefusal → String
  | .arrayOpName f => s!"callee {f} has the name of an array operation"
  | .calleeShape f c => s!"callee {f}: {c}"
  | .linkedName f => s!"linked function {f} has a reserved name"
  | .linkedSig f => s!"linked function {f} has a signature other than words and word arrays"
  | .intSlice f => s!"callee {f} has an integer-slice type"
  | .entryShape c => c
  | .entry r => r.toString
  | .entryResult t => s!"entry result of type {t}"
  | .inline n => s!"a call of a callee is left after {n} rounds of inlining"

instance : ToString ModuleRefusal := ⟨ModuleRefusal.toString⟩

/-- The stage of `haxToNF` at which a refusal of a module arises: `module` for a condition
    on the callees or the linked functions, `front` for the shape condition on the entry
    and for its result type, `impToNF` for a construct of the entry, `inline` for the
    inlining. -/
def ModuleRefusal.stage : ModuleRefusal → String
  | .arrayOpName _ => "module"
  | .calleeShape _ _ => "module"
  | .linkedName _ => "module"
  | .linkedSig _ => "module"
  | .intSlice _ => "module"
  | .entryShape _ => "front"
  | .entry _ => "impToNF"
  | .entryResult _ => "front"
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

/-- The refusal of a call the call typing does not type: `Refusal.fieldModulus` at a tagged
    field head whose modulus fails `fieldModOk`, `Refusal.call` otherwise. -/
def callRefusal (f : String) (as : List NfTy) : Refusal :=
  match _root_.Hax.FieldTag.fieldTag? f with
  | some (_, p) => if fieldModOk p then .call f as else .fieldModulus f p
  | none => .call f as

/-- The refusal of an expression that `atomOut` does not accept. -/
def atomRefusal : ImpExpr → Refusal
  | .var x => .unbound x
  | .lit l => .literal l
  | e => .operand (exprHead e)

/-- `atomOut` with the refusal. -/
def atomE {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) : Except Refusal (Out Γ) :=
  orRefuse (atomRefusal e) (atomOut σ e)

/-- The refusal of a lower bound of a counted loop that `loOut` does not accept: an integer
    literal outside `[0, 2 ^ 64)`, a name the environment of names does not bind, a name of a
    type `loTyOk` refuses, and a lower bound that is neither an integer literal nor a name. -/
def loRefusal {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : ImpExpr → Refusal
  | .lit (.int n) => .literal (.int n)
  | .var x =>
      match σ.lookup x with
      | some p => .loopLower s!"{x} : {tyName p.1}"
      | none => .unbound x
  | e => .loopLower (exprHead e)

/-- The type of a lower bound of a counted loop: the type of a name, `int` otherwise. -/
def loTy {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : ImpExpr → NfTy
  | .var x => ((σ.lookup x).map (·.1)).getD .int
  | _ => .int

/-- `loOut` with the refusal. -/
def loE {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (lo : ImpExpr) :
    Except Refusal (Expr nfDialect Γ NfTy.int) :=
  orRefuse (loRefusal σ lo) (loOut σ lo)

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

/-- `whileOut` with the refusal: the unbound flag, the flag of a type other than the bit type,
    that of the body `rec`, or the carried name the body leaves unbound or at another type. -/
def whileE {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (g : String)
    (xs : List String) (cs : List NfTy) (inits : HVector (fun t => Var Γ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Except Refusal (Out Δ)) :
    Except Refusal (Out Γ) :=
  let σB : NfEnv (cs ++ Γ) := whileEnv σ xs cs (headVars cs) fun v => Var.shiftApp cs v
  (orRefuse (.unbound g) (σB.lookup g)).bind fun p =>
    if h : p.1 = NfTy.bit then
      (rec σB).bind fun ob =>
        orRefuse (.loopCarried (carriedMiss ob.σ xs cs)) <| (varsAt ob.σ xs cs).map fun rets =>
          let oU := bind1N tgt σB .constUnit .nil
          Out.mk oU.Δ oU.t (.whileLoop inits (whileOutStep cs (h ▸ p.2) ob rets) oU.pre) oU.σ oU.res
    else .error (.whileGuard p.1)

theorem toOption_whileE {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (g : String)
    (xs : List String) (cs : List NfTy) (inits : HVector (fun t => Var Γ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Except Refusal (Out Δ)) :
    (whileE tgt σ g xs cs inits rec).toOption =
      whileOut tgt σ g xs cs inits fun σ => (rec σ).toOption := by
  simp only [whileE, whileOut, toOption_bind, toOption_orRefuse]
  congr 1
  funext p
  split
  · simp only [toOption_bind, toOption_orRefuse]
  · rfl

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

/-- `repeatOut` with the refusal: the refusal of the atom `x`, and `Refusal.call "repeat"` at
    the type of `x` when it is not the type of `64`-bit words. -/
def repeatE {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (x : ImpExpr) (N : Int) :
    Except Refusal (Out Γ) :=
  (atomE σ x).bind fun ox =>
    if h : ox.t = .word 64 then
      .ok (ox.comp (bind1N tgt ox.σ (.arrRepeat N.toNat (.word 64)) (.cons (h ▸ ox.res) .nil)))
    else .error (.call "repeat" [ox.t, .int])

theorem toOption_repeatE {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ)
    (x : ImpExpr) (N : Int) : (repeatE tgt σ x N).toOption = repeatOut tgt σ x N := by
  simp only [repeatE, repeatOut, atomE, toOption_bind, toOption_orRefuse]
  congr 1
  funext ox
  split <;> rfl

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
  | tgt, _, σ, .app f args =>
      if f = "repeat" then
        (orRefuse .arrayFill (repeatArgs? f args)).bind fun p => repeatE tgt σ p.1 p.2
      else (frontArgs sigOf σ args).bind fun oa =>
        orRefuse (callRefusal f oa.as) <| (sigOf f oa.as).map fun r =>
        ⟨r :: oa.Δ, r, oa.pre.append (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil),
          oa.σ.mapV .there, .here⟩
  | tgt, _, σ, .tuple es => (atomsE σ es).map fun oa =>
      let r := tupleOut tgt oa.as oa.vs
      Out.mk r.fst (tupTy oa.as) (oa.pre.append r.snd.fst) (oa.σ.mapV r.snd.fst.wk) r.snd.snd
  | tgt, _, σ, .proj e i => (frontOut sigOf none σ e).bind fun oe =>
      orRefuse (.projection oe.t i) ((projOut tgt oe.σ oe.t oe.res i).map oe.comp)
  | tgt, _, σ, .forFold i lo hi body => (loE σ lo).bind fun eLo =>
      let oLo := loBind σ eLo
      (atomE oLo.σ hi).bind fun oHi =>
        if boundOk 0 oHi.t || litBoundOk 0 hi then
          let oT := bind1 oHi.σ (.trip oHi.t) (.cons (oHi.pre.wk oLo.res) (.cons oHi.res .nil))
          let W := carried oT.σ i body
          loopE tgt ((oLo.pre.append oHi.pre).append oT.pre) oT.σ
            (oT.pre.wk (oHi.pre.wk oLo.res))
            oT.res none i (W.map (·.1)) (entriesVars W).1 (entriesVars W).2
            (fun σB => frontOut sigOf none σB body)
        else .error (.loopBound (loTy σ lo) oHi.t)
  | tgt, _, σ, .forFoldRev i lo hi body => (loE σ lo).bind fun eLo =>
      let oLo := loBind σ eLo
      (atomE oLo.σ hi).bind fun oHi =>
        if boundOk 0 oHi.t || litBoundOk 0 hi then
          let oT := bind1 oHi.σ (.trip oHi.t) (.cons (oHi.pre.wk oLo.res) (.cons oHi.res .nil))
          let oOne := bind1 oT.σ (.ilit (.word 64) 1) .nil
          let oM := bind1 oOne.σ (.bin .sub 64) (.cons (oOne.pre.wk oT.res) (.cons oOne.res .nil))
          let W := carried oM.σ i body
          loopE tgt ((((oLo.pre.append oHi.pre).append oT.pre).append oOne.pre).append oM.pre)
            oM.σ (oM.pre.wk (oOne.pre.wk (oT.pre.wk (oHi.pre.wk oLo.res))))
            (oM.pre.wk (oOne.pre.wk oT.res)) (some oM.res) i (W.map (·.1)) (entriesVars W).1
            (entriesVars W).2 (fun σB => frontOut sigOf none σB body)
        else .error (.loopBound (loTy σ lo) oHi.t)
  | _, _, σ, .ifThenElse c a b => (frontOut sigOf none σ c).bind fun oc =>
      if h : oc.t = NfTy.bit then
        let W := condCarried oc.σ a b
        condE oc.pre oc.σ (h ▸ oc.res) (W.map (·.1)) (entriesVars W).1
          (frontOut sigOf none oc.σ a) (frontOut sigOf none oc.σ b)
      else .error (.condType oc.t)
  | tgt, _, σ, .whileFold (.var g) body =>
      let W := condCarried σ body body
      whileE tgt σ g (W.map (·.1)) (entriesVars W).1 (entriesVars W).2
        (fun σB => frontOut sigOf none σB body)
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
    by_cases hf : f = "repeat"
    · subst hf
      simp only [frontOut, impToNF, if_true, toOption_bind, toOption_orRefuse, toOption_repeatE]
    · simp only [frontOut, hf, if_false, impToNF_app_call sigOf tgt σ hf,
        toOption_bind, toOption_orRefuse, toOption_frontArgs sigOf args iha]
  case tuple es _ =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_map, toOption_atomsE]
  case proj e i ih =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, toOption_orRefuse, ih]
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, loE, atomE, toOption_orRefuse]
    congr 1
    funext eLo
    congr 1
    funext oHi
    split
    · refine (toOption_loopE _ _ _ _ _ _ _ _ _ _ _).trans ?_
      congr 1
      funext Δ σB
      exact ihb _ _
    · rfl
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, loE, atomE, toOption_orRefuse]
    congr 1
    funext eLo
    congr 1
    funext oHi
    split
    · refine (toOption_loopE _ _ _ _ _ _ _ _ _ _ _).trans ?_
      congr 1
      funext Δ σB
      exact ihb _ _
    · rfl
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ
    simp only [frontOut, impToNF, toOption_bind, ihc]
    congr 1
    funext oc
    split
    · simp only [toOption_condE, iha, ihb]
    · rfl
  case whileFold c body _ ihb =>
    intro tgt Γ σ
    cases c with
    | var g =>
        simp only [frontOut, impToNF]
        refine (toOption_whileE _ _ _ _ _ _ _).trans ?_
        congr 1
        funext Δ σB
        exact ihb _ _
    | _ => rfl
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

/-! ## 5. The integer literals of the output -/

/-- An operation that is not an integer literal, or an integer literal in `[0, 2 ^ 64)` at the
    integer type, at the `64`-bit words or at an unsigned width of at most `64` bits. -/
def ilitWordOp : NfOp → Bool
  | .named _ op => ilitWordOp op
  | .ilit t v => decide (0 ≤ v) && decide (v < 2 ^ 64) &&
      (hax64NFWordTy t ||
        match t with
        | .uint W => decide (W.bits ≤ 64)
        | _ => false)
  | _ => true

/-- An integer literal satisfies `ilitWordOp` exactly when its value is in `[0, 2 ^ 64)` and
    its type is the integer type, the `64`-bit words or an unsigned width of at most `64`
    bits. -/
theorem ilitWordOp_ilit_iff (t : NfTy) (v : Int) :
    ilitWordOp (.ilit t v) = true ↔ 0 ≤ v ∧ v < 2 ^ 64 ∧
      (t = .int ∨ t = .word 64 ∨ ∃ W : _root_.Hax.IntWidth, t = .uint W ∧ W.bits ≤ 64) := by
  cases t with
  | word w =>
      by_cases hw : w = 64
      · subst hw
        simp [ilitWordOp, hax64NFWordTy]
      · simp [ilitWordOp, hax64NFWordTy, hw]
  | uint W => simp [ilitWordOp, hax64NFWordTy, and_assoc]
  | _ => simp [ilitWordOp, hax64NFWordTy]

/-- Every operation of a program, in every region and continuation, satisfies `P`. -/
def opsProg (P : NfOp → Bool) :
    {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => P e.op && opsProg P k
  | _, _, .forLoop _ _ body k => opsProg P body && opsProg P k
  | _, _, .ifThenElse _ thn els k => opsProg P thn && opsProg P els && opsProg P k
  | _, _, .whileLoop _ body k => opsProg P body && opsProg P k
  | _, _, .call _ _ k => opsProg P k

/-- Every operation of a prefix, in every region and continuation, satisfies `P`. -/
def opsPre (P : NfOp → Bool) : {Γ Δ : Ctxt nfDialect} → NFPre nfDialect Γ Δ → Bool
  | _, _, .nil => true
  | _, _, .var e p => P e.op && opsPre P p
  | _, _, .forLoop _ _ body p => opsProg P body && opsPre P p
  | _, _, .ifThenElse _ thn els p => opsProg P thn && opsProg P els && opsPre P p
  | _, _, .whileLoop _ body p => opsProg P body && opsPre P p

theorem opsPre_append (P : NfOp → Bool) {Γ Δ Θ : Ctxt nfDialect} (p : NFPre nfDialect Γ Δ)
    (q : NFPre nfDialect Δ Θ) : opsPre P (p.append q) = (opsPre P p && opsPre P q) := by
  induction p with
  | nil => simp [NFPre.append, opsPre]
  | var e p ih => simp [NFPre.append, opsPre, ih, Bool.and_assoc]
  | forLoop _ _ body p ih => simp [NFPre.append, opsPre, ih, Bool.and_assoc]
  | ifThenElse _ thn els p ih => simp [NFPre.append, opsPre, ih, Bool.and_assoc]
  | whileLoop _ body p ih => simp [NFPre.append, opsPre, ih, Bool.and_assoc]

theorem opsProg_plug (P : NfOp → Bool) {Γ Δ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFPre nfDialect Γ Δ) (k : NFProg nfDialect Δ ts) :
    opsProg P (p.plug k) = (opsPre P p && opsProg P k) := by
  induction p with
  | nil => simp [NFPre.plug, opsPre]
  | var e p ih => simp [NFPre.plug, opsPre, opsProg, ih, Bool.and_assoc]
  | forLoop _ _ body p ih => simp [NFPre.plug, opsPre, opsProg, ih, Bool.and_assoc]
  | ifThenElse _ thn els p ih => simp [NFPre.plug, opsPre, opsProg, ih, Bool.and_assoc]
  | whileLoop _ body p ih => simp [NFPre.plug, opsPre, opsProg, ih, Bool.and_assoc]

theorem ilitWordOp_mkEN {Γ : Ctxt nfDialect} (tgt : Option String) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) :
    ilitWordOp (mkEN tgt op args).op = ilitWordOp op := by
  cases tgt <;> rfl

theorem opsPre_bind1N {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) :
    opsPre ilitWordOp (bind1N tgt σ op args).pre = ilitWordOp op := by
  simp [bind1N, opsPre, ilitWordOp_mkEN]

theorem opsPre_bind1 {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) :
    opsPre ilitWordOp (bind1 σ op args).pre = ilitWordOp op := by
  simp [bind1, opsPre, mkE]

/-- The integer literals `litInt` types lie in `[0, 2 ^ 64)` at the `64`-bit words or at an
    unsigned width of at most `64` bits. -/
theorem litInt_ilitWord {l : ImpLit} {t : NfTy} {v : Int} (h : litInt l = some (t, v)) :
    ilitWordOp (.ilit t v) = true := by
  cases l with
  | int n =>
      by_cases hc : 0 ≤ n ∧ n < 2 ^ 64
      · simp only [litInt, if_pos hc, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ilitWordOp, hax64NFWordTy, Bool.true_or, Bool.and_true, Bool.and_eq_true,
          decide_eq_true_eq]
        exact hc
      · simp only [litInt, if_neg hc, reduceCtorEq] at h
  | uintLit W n =>
      by_cases hw : W.bits ≤ 64
      · simp only [litInt, if_pos hw, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h1 : n % W.modulus < W.modulus := Nat.mod_lt _ (Nat.two_pow_pos _)
        have h2 : W.modulus ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
        simp only [ilitWordOp, hw, decide_true, Bool.or_true, Bool.and_true,
          Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp only [litInt, if_neg hw, reduceCtorEq] at h
  | _ => simp [litInt] at h

theorem litOut_ilitWord {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (l : ImpLit)
    {o : Out Γ} (h : litOut tgt σ l = some o) : opsPre ilitWordOp o.pre = true := by
  cases l with
  | bool b =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      simp [opsPre_bind1N, ilitWordOp]
  | unit =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      simp [opsPre_bind1N, ilitWordOp]
  | int n | uintLit W n | sintLit W n =>
      simp only [litOut, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hl, hs⟩ := h
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        rw [opsPre_bind1N]
        exact litInt_ilitWord hl
      · cases hs

theorem atomOut_ilitWord {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (a : ImpExpr) {o : Out Γ}
    (h : atomOut σ a = some o) : opsPre ilitWordOp o.pre = true := by
  cases a with
  | var x =>
      simp only [atomOut, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
  | lit l => exact litOut_ilitWord none σ l h
  | _ => simp [atomOut] at h

theorem argsOut_ilitWord (es : List ImpExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
      opsPre ilitWordOp oa.pre = true := by
  induction es with
  | nil =>
      intro Γ σ oa h
      simp only [argsOut, Option.some.injEq] at h
      subst h
      rfl
  | cons e es ih =>
      intro Γ σ oa h
      simp only [argsOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      simp only [opsPre_append, atomOut_ilitWord σ e ho, ih o.σ hos, Bool.and_self]

theorem tupleOut_ilitWord {Γ : Ctxt nfDialect} (tgt : Option String) (as : List NfTy)
    (vs : HVector (fun t => Var Γ t) as) :
    opsPre ilitWordOp (tupleOut tgt as vs).snd.fst = true := by
  induction as generalizing tgt with
  | nil => cases vs; simp [tupleOut, opsPre, ilitWordOp_mkEN, ilitWordOp]
  | cons a as ih =>
      cases vs with
      | cons v vs =>
          rw [tupleOut]
          simp [opsPre_append, opsPre, ilitWordOp_mkEN, ilitWordOp, ih]

theorem ctrOut_ilitWord {Γ₃ : Ctxt nfDialect} (cs : List NfTy) (i : String)
    (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) :
    opsPre ilitWordOp (ctrOut cs i σB loV rev).pre = true := by
  cases rev <;> simp [ctrOut, Out.comp, opsPre_append, opsPre_bind1N, opsPre_bind1, ilitWordOp]

theorem loopOut_ilitWord {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String)
    (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ))
    (hpre : opsPre ilitWordOp pre₀ = true)
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (o : Out Δ), rec σ = some o →
      opsPre ilitWordOp o.pre = true)
    {o : Out Γ} (h : loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits rec = some o) :
    opsPre ilitWordOp o.pre = true := by
  simp only [loopOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨ob, hob, rets, -, rfl⟩ := h
  simp [opsPre_append, opsPre, opsProg_plug, opsProg, hpre, ctrOut_ilitWord, hrec _ _ hob,
    opsPre_bind1N, ilitWordOp]

theorem whileOut_ilitWord {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ)
    (g : String) (xs : List String) (cs : List NfTy) (inits : HVector (fun t => Var Γ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ))
    (hrec : ∀ {Δ : Ctxt nfDialect} (σ : NfEnv Δ) (o : Out Δ), rec σ = some o →
      opsPre ilitWordOp o.pre = true)
    {o : Out Γ} (h : whileOut tgt σ g xs cs inits rec = some o) :
    opsPre ilitWordOp o.pre = true := by
  simp only [whileOut, Option.bind_eq_some_iff] at h
  obtain ⟨p, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ob, hob, rets, -, rfl⟩ := h
    simp [opsPre, whileOutStep, opsProg_plug, opsProg, hrec _ _ hob, opsPre_bind1N, ilitWordOp]
  · cases h

theorem condOut_ilitWord {Γ Γc : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γc)
    (σc : NfEnv Γc) (cV : Var Γc NfTy.bit) (xs : List String) (cs : List NfTy)
    (recA recB : Option (Out Γc)) (hpre : opsPre ilitWordOp pre₀ = true)
    (hA : ∀ oa, recA = some oa → opsPre ilitWordOp oa.pre = true)
    (hB : ∀ ob, recB = some ob → opsPre ilitWordOp ob.pre = true)
    {o : Out Γ} (h : condOut pre₀ σc cV xs cs recA recB = some o) :
    opsPre ilitWordOp o.pre = true := by
  simp only [condOut, Option.bind_eq_some_iff] at h
  obtain ⟨oa, hoa, ob, hob, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ra, -, rb, -, h⟩ := h
    split at h <;> (subst h; simp [opsPre_append, opsPre, opsProg_plug, opsProg, hpre,
      hA oa hoa, hB ob hob, opsPre_bind1N, ilitWordOp])
  · cases h

/-- The lower bound of a counted loop under the bounds of `boundOk` or of `litBoundOk` lies
    in `[0, 2 ^ 64)`. -/
theorem lo_range_of_bound {lo : Int} {t : NfTy} {hi : ImpExpr}
    (hb : (boundOk lo t || litBoundOk lo hi) = true) : 0 ≤ lo ∧ lo < 2 ^ 64 := by
  rcases Bool.or_eq_true_iff.mp hb with hb | hb
  · cases t with
    | uint W =>
        simp only [boundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact hb.1
    | word w =>
        simp only [boundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact hb.1
    | _ => simp [boundOk] at hb
  · match hi, hb with
    | .lit (.int n), hb =>
        simp only [litBoundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
        exact hb.1

/-- The binding of a lower bound `loOut` accepts satisfies `ilitWordOp`: an integer literal
    in `[0, 2 ^ 64)` at the integer type, or `boundInt`. -/
theorem loOut_ilitWord {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (lo : ImpExpr)
    {e : Expr nfDialect Γ NfTy.int} (h : loOut σ lo = some e) :
    opsPre ilitWordOp (loBind σ e).pre = true := by
  match lo, h with
  | .lit (.int n), h =>
      simp only [loOut] at h
      split at h
      · rename_i hn
        cases h
        have h1 : n < 2 ^ 64 := hn.2
        simp [loBind, opsPre, mkE, ilitWordOp, hax64NFWordTy, hn.1]
        omega
      · cases h
  | .var x, h =>
      simp only [loOut, Option.bind_eq_some_iff] at h
      obtain ⟨p, -, h⟩ := h
      split at h
      · cases h
        simp [loBind, opsPre, mkE, ilitWordOp]
      · cases h

/-- The prefix of `impArgsNF` satisfies `ilitWordOp` when the prefix of `impToNF` on each
    argument does. -/
theorem impArgsNF_ilitWord (sigOf : String → List NfTy → Option NfTy) (args : List ImpExpr)
    (ih : ∀ e ∈ args, ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : Out Γ),
      impToNF sigOf tgt σ e = some o → opsPre ilitWordOp o.pre = true) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (oa : ArgsOut Γ),
      impArgsNF sigOf σ args = some oa → opsPre ilitWordOp oa.pre = true := by
  induction args with
  | nil =>
      intro Γ σ oa h
      simp only [impArgsNF, Option.some.injEq] at h
      subst h
      rfl
  | cons e es ihes =>
      intro Γ σ oa h
      simp only [impArgsNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      simp only [opsPre_append, ih e List.mem_cons_self none σ o ho,
        ihes (fun a ha => ih a (List.mem_cons_of_mem _ ha)) o.σ os hos, Bool.and_self]

/-- The bindings of `projOut` have no integer literal. -/
theorem projOut_ilitWord (tgt : Option String) (i : Nat) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (t : NfTy) (x : Var Γ t) {o : Out Γ},
      projOut tgt σ t x i = some o → opsPre ilitWordOp o.pre = true := by
  induction i with
  | zero =>
      intro Γ σ t x o h
      cases t with
      | tcons h₀ t =>
          simp only [projOut, Option.some.injEq] at h
          subst h
          simp [opsPre_bind1N, ilitWordOp]
      | _ => simp [projOut] at h
  | succ i ih =>
      intro Γ σ t x o h
      cases t with
      | tcons h₀ t =>
          simp only [projOut, Option.map_eq_some_iff] at h
          obtain ⟨o₂, ho₂, rfl⟩ := h
          simp only [Out.comp, opsPre_append, opsPre_bind1, ih _ _ _ ho₂, ilitWordOp,
            Bool.and_self]
      | _ => simp [projOut] at h

/-- **The integer literals of the front's output**: every integer literal of a prefix
    `impToNF` returns lies in `[0, 2 ^ 64)`, at the integer type, at the `64`-bit words or at
    an unsigned width of at most `64` bits. -/
theorem impToNF_ilitWord (sigOf : String → List NfTy → Option NfTy) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (o : Out Γ),
      impToNF sigOf tgt σ e = some o → opsPre ilitWordOp o.pre = true := by
  induction e using ImpExpr.ind
  case lit l =>
    intro tgt Γ σ o h
    exact litOut_ilitWord tgt σ l h
  case var x =>
    intro tgt Γ σ o h
    exact atomOut_ilitWord σ (.var x) h
  case unitVal =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.some.injEq] at h
    subst h
    simp [opsPre_bind1N, ilitWordOp]
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    simp only [Out.comp, opsPre_append, ihv _ _ _ hov, ihb _ _ _ hob, Bool.and_self]
  case seq a b iha ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    simp only [Out.comp, opsPre_append, iha _ _ _ hoa, ihb _ _ _ hob, Bool.and_self]
  case assign x r ih =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨o', ho', rfl⟩ := h
    simp [Out.comp, opsPre_append, ih _ _ _ ho', opsPre_bind1N, ilitWordOp]
  case typeAscription e s ih =>
    intro tgt Γ σ o h
    simp only [impToNF] at h
    exact ih _ _ _ h
  case app f args iha =>
    intro tgt Γ σ o h
    rcases impToNF_app_cases sigOf tgt σ h with ⟨x, N, -, h⟩ | ⟨-, oa, hoa, r, -, rfl⟩
    · simp only [repeatOut, Option.bind_eq_some_iff] at h
      obtain ⟨ox, hox, h⟩ := h
      split at h
      · cases h
        simp [Out.comp, bind1N, opsPre_append, opsPre, atomOut_ilitWord σ x hox,
          ilitWordOp_mkEN, ilitWordOp]
      · cases h
    · simp [opsPre_append, opsPre, impArgsNF_ilitWord sigOf args iha _ _ hoa, ilitWordOp_mkEN,
        ilitWordOp]
  case tuple es _ =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, rfl⟩ := h
    simp only [opsPre_append, argsOut_ilitWord es σ hoa, tupleOut_ilitWord, Bool.and_self]
  case proj e i ih =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oe, hoe, op, hop, rfl⟩ := h
    simp only [Out.comp, opsPre_append, ih _ _ _ hoe, projOut_ilitWord tgt i _ _ _ hop,
      Bool.and_self]
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, hHi, h⟩ := h
    split at h
    · refine loopOut_ilitWord _ _ _ _ _ _ _ _ _ _ _ ?_ (fun σB o' ho' => ihb _ σB o' ho') h
      simp only [opsPre_append, opsPre_bind1, atomOut_ilitWord _ _ hHi, loOut_ilitWord σ lo hLo,
        ilitWordOp, Bool.and_self]
    · cases h
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨eLo, hLo, oHi, hHi, h⟩ := h
    split at h
    · refine loopOut_ilitWord _ _ _ _ _ _ _ _ _ _ _ ?_ (fun σB o' ho' => ihb _ σB o' ho') h
      simp only [opsPre_append, opsPre_bind1, atomOut_ilitWord _ _ hHi, loOut_ilitWord σ lo hLo,
        ilitWordOp, hax64NFWordTy, Bool.and_self]
      decide
    · cases h
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ o h
    simp only [impToNF, Option.bind_eq_some_iff] at h
    obtain ⟨oc, hoc, h⟩ := h
    split at h
    · exact condOut_ilitWord _ _ _ _ _ _ _ (ihc _ _ _ hoc) (fun oa ha => iha _ _ _ ha)
        (fun ob hb => ihb _ _ _ hb) h
    · cases h
  case whileFold c body _ ihb =>
    intro tgt Γ σ o h
    cases c with
    | var g =>
        exact whileOut_ilitWord _ _ _ _ _ _ _ (fun σB o' ho' => ihb _ σB o' ho')
          (by simpa only [impToNF] using h)
    | _ => simp [impToNF] at h
  all_goals
    intro tgt Γ σ o h
    simp [impToNF] at h

/-- **With no refusal, the integer literals of the front's output are words**: when `frontRefusal?` returns no refusal, `impToNF` returns a program every integer literal
    of which lies in `[0, 2 ^ 64)`, at the integer type, at the `64`-bit words or at an
    unsigned width of at most `64` bits. -/
theorem frontOut_ilit_word (sigOf : String → List NfTy → Option NfTy) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (e : ImpExpr) (h : frontRefusal? sigOf tgt σ e = none) :
    ∃ o, impToNF sigOf tgt σ e = some o ∧ opsPre ilitWordOp o.pre = true := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ((frontRefusal?_eq_none_iff sigOf tgt σ e).mp h)
  exact ⟨o, ho, impToNF_ilitWord sigOf e tgt σ o ho⟩

end CatCrypt.Crypto.Hax.FrontDomain
