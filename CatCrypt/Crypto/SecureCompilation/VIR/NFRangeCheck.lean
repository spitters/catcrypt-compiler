/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
public import HaxLean.Range.Domain

/-!
# An interval checker for NF programs

`NFRange.check S A p` runs the NF program `p` over abstract values from the abstract
environment `A` and returns the abstract values of its results, or `none` when it cannot show
that no operation of `p` fails. An abstract value (`AVal`) is, by the type of the value:

* for a word, an integer interval of the domain `RangeDomain` that holds its `toNat`
  (`Iv.Has`);
* for a bit, its value when known (`Option Bool`) and the facts that hold when it is `true`
  and when it is `false` (`ABit`); a fact (`Fact`) compares two words of the context by their
  levels, the positions counted from the bottom of the context, which stay valid under the
  variables a program binds;
* for an array, the abstract value of its elements;
* for every other type, no information.

A leaf call is read through a name specification (`NameSpec`): its transfer function `xfer`
gives the abstract result of a call from the abstract values of its arguments, or refuses
it; `cmp?` and `conn?` name the comparisons and Boolean connectives, from which the checker
derives the facts of the bit a call returns. `NameSpec.SoundAt S T` states what these mean for
a leaf table `T`. `aeSpec` is the specification of the names of the Aeneas reading of calls
(`aeCallV`, `AeneasFront/NFToRustM.lean`): the tagged word operations, the checked operations
`Add#t`, `Sub#t`, `Mul#t`, which it accepts only when the exact result lies below `2 ^ w`, the
comparisons, connectives, complements, casts, `index`, `array_update` and `select`.

The checker reads the operations `const`, `constBit`, `constUnit`, `ilit`, `notB`, `andB`,
`orB`, `named` and `call`. A branch is checked arm by arm, each arm under the environment
refined by the value of the condition and its facts (`AEnv.refineBit`); an arm that cannot run
is skipped (`AEnv.reach`), so a branch to an aborting arm, the reading of a panic guard, is
accepted when the condition of the abort is known `false`. A counted loop with a constant trip
count of at most `NameSpec.unroll` is checked iteration by iteration; another counted loop is
checked against an invariant of the carried values: the entry values, then up to two joins with
the values after one more iteration, then their widening to the full range of the types
(`loopFix`).

## Refusals

`refusal S A p` is the reason of a refusal:

* a reachable `abort`;
* a call the transfer function of its name refuses, with the abstract arguments;
* an integer literal outside its type;
* an operation other than those read above;
* an exit-flag loop (`whileLoop`) and a call of a symbol (`call`);
* a counted loop whose carried values leave each candidate invariant.

## Main definitions

* `Fact`, `ABit`, `AVal`, `AVals`, `AEnv` — the abstract values and environments.
* `AVal.Mem`, `AVals.Mem`, `Fact.Holds`, `AEnv.Sat` — their meaning.
* `Conn`, `NameSpec`, `NameSpec.SoundAt` — the specification of the leaf names and its
  soundness for a leaf table.
* `evalOp`, `evalExpr` — the abstract operations.
* `AEnv.refineBit`, `AEnv.reach` — the refinement by a branch condition.
* `loopFix` — the search for a loop invariant.
* `run`, `check`, `refusal` — the checker, its result and its refusal reason.
* `aeSpec` — the specification of the names of the Aeneas reading.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFRange

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)

/-! ## 1. Abstract values -/

/-- A fact between two words of a context, by their levels: the `toNat` of the word at level
    `l` is below (`strict`) or at most the `toNat` of the word at level `r`. -/
structure Fact where
  /-- Whether the comparison is strict. -/
  strict : Bool
  /-- The level of the left word. -/
  l : Nat
  /-- The level of the right word. -/
  r : Nat
  deriving DecidableEq, Repr

/-- The abstract value of a bit: its value when known, and the facts that hold when it is
    `true` (`tt`) and when it is `false` (`ff`). -/
structure ABit where
  /-- The value of the bit, when known. -/
  val : Option Bool
  /-- The facts that hold when the bit is `true`. -/
  tt : List Fact
  /-- The facts that hold when the bit is `false`. -/
  ff : List Fact
  deriving DecidableEq, Repr

/-- The bit of the known value `b`, with no fact. -/
def ABit.known (b : Bool) : ABit := ⟨some b, [], []⟩

/-- The negation of an abstract bit: the value negated, the facts exchanged. -/
def ABit.not (a : ABit) : ABit := ⟨a.val.map (!·), a.ff, a.tt⟩

/-- The conjunction of two abstract bits: `true` with the facts of both. -/
def ABit.and (a b : ABit) : ABit :=
  ⟨match a.val, b.val with
    | some false, _ | _, some false => some false
    | some true, some true => some true
    | _, _ => none,
   a.tt ++ b.tt, []⟩

/-- The disjunction of two abstract bits: `false` with the facts of both. -/
def ABit.or (a b : ABit) : ABit :=
  ⟨match a.val, b.val with
    | some true, _ | _, some true => some true
    | some false, some false => some false
    | _, _ => none,
   [], a.ff ++ b.ff⟩

/-- The abstract value of a value of the type `t`. -/
@[reducible] def AVal : NfTy → Type
  | .bit => ABit
  | .word _ => Iv
  | .arr _ t => AVal t
  | _ => Unit

/-- The abstract values of a list of types. -/
abbrev AVals (ts : List NfTy) : Type := HVector AVal ts

/-- The abstract environment of a context. -/
abbrev AEnv (Γ : Ctxt nfDialect) : Type := HVector AVal Γ

/-- The abstract value of every value of the type `t`. -/
def AVal.top : (t : NfTy) → AVal t
  | .bit => (⟨none, [], []⟩ : ABit)
  | .word w => ((0, 2 ^ w - 1) : Iv)
  | .arr _ t => AVal.top t
  | .unit | .pair _ _ | .uint _ | .sint _ | .int | .tnil | .tcons _ _ | .slice _ => ()

/-- The join of two abstract values: the hull of intervals, the common value and facts of
    bits. -/
def AVal.join : (t : NfTy) → AVal t → AVal t → AVal t
  | .bit, a, b =>
    (⟨if a.val = b.val then a.val else none, a.tt.filter (· ∈ b.tt),
      a.ff.filter (· ∈ b.ff)⟩ : ABit)
  | .word _, a, b => ivHull a b
  | .arr _ t, a, b => AVal.join t a b
  | .unit, _, _ | .pair _ _, _, _ | .uint _, _, _ | .sint _, _, _ | .int, _, _ | .tnil, _, _
  | .tcons _ _, _, _ | .slice _, _, _ => ()

/-- The inclusion of abstract values. -/
def AVal.le : (t : NfTy) → AVal t → AVal t → Bool
  | .bit, a, b =>
    (b.val.isNone || a.val == b.val) && b.tt.all (· ∈ a.tt) && b.ff.all (· ∈ a.ff)
  | .word _, a, b => ivLe a b
  | .arr _ t, a, b => AVal.le t a b
  | .unit, _, _ | .pair _ _, _, _ | .uint _, _, _ | .sint _, _, _ | .int, _, _ | .tnil, _, _
  | .tcons _ _, _, _ | .slice _, _, _ => true

/-- The widening of `a` by `b`: `a` when `b` lies in it, the full range of the type
    otherwise. -/
def AVal.widen (t : NfTy) (a b : AVal t) : AVal t :=
  if AVal.le t b a then a else AVal.top t

/-- Whether an abstract value holds of no value: an empty interval, or a nonempty array of
    elements of empty abstract value. -/
def AVal.empty : (t : NfTy) → AVal t → Bool
  | .word _, a => decide (a.2 < a.1)
  | .arr n t, a => decide (0 < n) && AVal.empty t a
  | .bit, _ | .unit, _ | .pair _ _, _ | .uint _, _ | .sint _, _ | .int, _ | .tnil, _
  | .tcons _ _, _ | .slice _, _ => false

/-- The abstract value without the facts on a level of `n` or more. -/
def AVal.restrict (n : Nat) : (t : NfTy) → AVal t → AVal t
  | .bit, a =>
    (⟨a.val, a.tt.filter (fun f => f.l < n && f.r < n),
      a.ff.filter (fun f => f.l < n && f.r < n)⟩ : ABit)
  | .arr _ t, a => AVal.restrict n t a
  | .word _, a => a
  | .unit, a | .pair _ _, a | .uint _, a | .sint _, a | .int, a | .tnil, a | .tcons _ _, a
  | .slice _, a => a

/-- The abstract value of the integer literal `v` at the type `t`: the point `v` at a word,
    no information at every other type. -/
def AVal.ofLit (t : NfTy) (v : Int) : AVal t :=
  match t with
  | .word _ => ivPoint v
  | t => AVal.top t

/-- An abstract value as a string, for refusal messages. -/
def AVal.str : (t : NfTy) → AVal t → String
  | .bit, a => reprStr a
  | .word _, a => reprStr a
  | .arr _ t, a => "arr " ++ AVal.str t a
  | .unit, _ | .pair _ _, _ | .uint _, _ | .sint _, _ | .int, _ | .tnil, _ | .tcons _ _, _
  | .slice _, _ => "_"

/-- The interval of a word's abstract value. -/
def wordArg : (t : NfTy) → AVal t → Option Iv
  | .word _, a => some a
  | _, _ => none

/-- The abstract value of a bit. -/
def bitArg : (t : NfTy) → AVal t → Option ABit
  | .bit, a => some a
  | _, _ => none

/-- The length and element interval of an array of words. -/
def arrArg : (t : NfTy) → AVal t → Option (Nat × Iv)
  | .arr n (.word _), a => some (n, a)
  | _, _ => none

namespace AVals

/-- The full ranges of the types `ts`. -/
def top : (ts : List NfTy) → AVals ts
  | [] => .nil
  | t :: ts => .cons (AVal.top t) (top ts)

/-- The pointwise join. -/
def join : {ts : List NfTy} → AVals ts → AVals ts → AVals ts
  | [], .nil, .nil => .nil
  | t :: _, .cons a as, .cons b bs => .cons (AVal.join t a b) (join as bs)

/-- The pointwise inclusion. -/
def le : {ts : List NfTy} → AVals ts → AVals ts → Bool
  | [], .nil, .nil => true
  | t :: _, .cons a as, .cons b bs => AVal.le t a b && le as bs

/-- The pointwise widening. -/
def widen : {ts : List NfTy} → AVals ts → AVals ts → AVals ts
  | [], .nil, .nil => .nil
  | t :: _, .cons a as, .cons b bs => .cons (AVal.widen t a b) (widen as bs)

/-- The values without the facts on a level of `n` or more. -/
def restrict (n : Nat) : {ts : List NfTy} → AVals ts → AVals ts
  | [], .nil => .nil
  | t :: _, .cons a as => .cons (AVal.restrict n t a) (restrict n as)

/-- Whether one of the abstract values holds of no value. -/
def isEmpty : {ts : List NfTy} → AVals ts → Bool
  | [], .nil => false
  | t :: _, .cons a as => AVal.empty t a || isEmpty as

/-- The abstract values as strings, for refusal messages. -/
def strs : {ts : List NfTy} → AVals ts → List String
  | [], .nil => []
  | t :: _, .cons a as => AVal.str t a :: strs as

end AVals

/-! ## 2. Meaning -/

/-- An abstract value holds of a value: its interval holds the `toNat` of a word, its known
    value is the bit, its element value holds of every element of an array. The facts of a
    bit are read by `AEnv.Sat`. -/
def AVal.Mem : (t : NfTy) → AVal t → t.denote → Prop
  | .bit, a, b => a.val = none ∨ a.val = some b
  | .word _, a, x => a.Has x.toNat
  | .arr _ t, a, f => ∀ j, AVal.Mem t a (f j)
  | .unit, _, _ | .pair _ _, _, _ | .uint _, _, _ | .sint _, _, _ | .int, _, _ | .tnil, _, _
  | .tcons _ _, _, _ | .slice _, _, _ => True

/-- Each abstract value holds of the value at its position. -/
def AVals.Mem : {ts : List NfTy} → AVals ts → HVector NfTy.denote ts → Prop
  | [], .nil, .nil => True
  | t :: _, .cons a as, .cons x xs => AVal.Mem t a x ∧ AVals.Mem as xs

/-- The position of the level `l` in a context of length `len`. -/
def levelIdx (len l : Nat) : Option Nat := if l < len then some (len - 1 - l) else none

/-- The level of a variable. -/
def varLevel {Γ : Ctxt nfDialect} {t : NfTy} (v : Var Γ t) : Nat :=
  Γ.length - 1 - varIdx v
where
  /-- The position of a variable. -/
  varIdx : {Γ : Ctxt nfDialect} → {t : NfTy} → Var Γ t → Nat
    | _, _, .here => 0
    | _, _, .there v => varIdx v + 1

/-- The `toNat` of a word value, as an integer. -/
def wordInt : (t : NfTy) → t.denote → Option Int
  | .word _, x => some (x.toNat : Int)
  | _, _ => none

/-- The integer of the word at a position of a valuation. -/
def valIntAt : {Γ : Ctxt nfDialect} → Valuation Γ → Nat → Option Int
  | [], .nil, _ => none
  | t :: _, .cons x _, 0 => wordInt t x
  | _ :: _, .cons _ V, n + 1 => valIntAt V n

/-- The bit at a position of a valuation. -/
def valBitAt : {Γ : Ctxt nfDialect} → Valuation Γ → Nat → Option Bool
  | [], .nil, _ => none
  | .bit :: _, .cons x _, 0 => some x
  | _ :: _, .cons _ _, 0 => none
  | _ :: _, .cons _ V, n + 1 => valBitAt V n

/-- A fact holds of a valuation. -/
def Fact.Holds {Γ : Ctxt nfDialect} (V : Valuation Γ) (f : Fact) : Prop :=
  ∃ m n, (levelIdx Γ.length f.l).bind (valIntAt V) = some m ∧
    (levelIdx Γ.length f.r).bind (valIntAt V) = some n ∧
    (if f.strict then m < n else m ≤ n)

namespace AEnv

/-- The abstract value of a variable. -/
def get : {Γ : Ctxt nfDialect} → {t : NfTy} → AEnv Γ → Var Γ t → AVal t
  | _, _, .cons a _, .here => a
  | _, _, .cons _ A, .there v => get A v

/-- The environment with the abstract value of a variable replaced. -/
def set : {Γ : Ctxt nfDialect} → {t : NfTy} → AEnv Γ → Var Γ t → AVal t → AEnv Γ
  | _, _, .cons _ A, .here, a => .cons a A
  | _, _, .cons b A, .there v, a => .cons b (set A v a)

/-- The abstract values of a list of variables. -/
def getArgs {Γ : Ctxt nfDialect} (A : AEnv Γ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts → AVals ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (A.get v) (getArgs A vs)

/-- The interval of the word at a position. -/
def ivAt : {Γ : Ctxt nfDialect} → AEnv Γ → Nat → Option Iv
  | [], .nil, _ => none
  | t :: _, .cons a _, 0 => wordArg t a
  | _ :: _, .cons _ A, n + 1 => ivAt A n

/-- The abstract bit at a position. -/
def bitAt : {Γ : Ctxt nfDialect} → AEnv Γ → Nat → Option ABit
  | [], .nil, _ => none
  | t :: _, .cons a _, 0 => bitArg t a
  | _ :: _, .cons _ A, n + 1 => bitAt A n

/-- The interval of a word's abstract value replaced. -/
def setWord : (t : NfTy) → AVal t → Iv → AVal t
  | .word _, _, i => i
  | .bit, a, _ | .arr _ _, a, _ | .unit, a, _ | .pair _ _, a, _ | .uint _, a, _
  | .sint _, a, _ | .int, a, _ | .tnil, a, _ | .tcons _ _, a, _ | .slice _, a, _ => a

/-- The environment with the interval of the word at a position replaced. -/
def setIvAt : {Γ : Ctxt nfDialect} → AEnv Γ → Nat → Iv → AEnv Γ
  | [], .nil, _, _ => .nil
  | t :: _, .cons a A, 0, i => .cons (setWord t a i) A
  | _ :: _, .cons a A, n + 1, i => .cons a (setIvAt A n i)

/-- The environment refined by a fact: the upper bound of its left word lowered to the upper
    bound of its right word, and the lower bound of its right word raised to the lower bound of
    its left word. -/
def applyFact {Γ : Ctxt nfDialect} (A : AEnv Γ) (f : Fact) : AEnv Γ :=
  match levelIdx Γ.length f.l, levelIdx Γ.length f.r with
  | some il, some ir =>
    match A.ivAt il, A.ivAt ir with
    | some a, some b =>
      let d : Int := if f.strict then 1 else 0
      (A.setIvAt il (a.1, min a.2 (b.2 - d))).setIvAt ir (max b.1 (a.1 + d), b.2)
    | _, _ => A
  | _, _ => A

/-- The environment of the arm of a branch on the bit `c` taken when `c` is `b`: the bit set
    to `b` and the environment refined by the facts that hold then. -/
def refineBit {Γ : Ctxt nfDialect} (A : AEnv Γ) (c : Var Γ .bit) (b : Bool) : AEnv Γ :=
  let a : ABit := A.get c
  (if b then a.tt else a.ff).foldl applyFact (A.set c { a with val := some b })

/-- Whether the arm taken when `c` is `b` may run: the bit is not known to be `!b`, and the
    refined environment holds of some valuation. -/
def reach {Γ : Ctxt nfDialect} (A : AEnv Γ) (c : Var Γ .bit) (b : Bool) : Bool :=
  (A.get c).val != some (!b) && !AVals.isEmpty (A.refineBit c b)

/-- An abstract environment holds of a valuation: each abstract value holds of the value of
    its variable, and the facts of each bit for its value hold. -/
def Sat {Γ : Ctxt nfDialect} (A : AEnv Γ) (V : Valuation Γ) : Prop :=
  AVals.Mem A V ∧ ∀ n a b, A.bitAt n = some a → valBitAt V n = some b →
    ∀ f ∈ (if b then a.tt else a.ff), f.Holds V

end AEnv

/-! ## 3. Name specifications -/

/-- The Boolean connectives a leaf name may denote. -/
inductive Conn where
  /-- Conjunction of two bits. -/
  | and
  /-- Disjunction of two bits. -/
  | or
  /-- Negation of a bit. -/
  | not
  deriving DecidableEq, Repr

/-- The specification of the leaf names: a transfer function, the comparisons and the
    connectives, and the largest constant trip count the checker unrolls. -/
structure NameSpec where
  /-- The abstract result of a call of `f` at the argument types `as` and the result type `r`
      from the abstract values of its arguments; `none` refuses the call. -/
  xfer : (f : String) → (as : List NfTy) → (r : NfTy) → AVals as → Option (AVal r)
  /-- The comparison a name denotes on two words. -/
  cmp? : String → Option NfPred := fun _ => none
  /-- The connective a name denotes on bits. -/
  conn? : String → Option Conn := fun _ => none
  /-- The largest constant trip count of a counted loop that is checked iteration by
      iteration. -/
  unroll : Nat := 64

/-- A name specification is sound for a leaf table: a call its transfer function accepts on
    arguments in their abstract values has a value in the abstract result, a comparison name
    answers with its comparison, and a connective name with its connective. -/
structure NameSpec.SoundAt (S : NameSpec) (T : NfLeafTable) : Prop where
  xfer : ∀ f as r (avs : AVals as) a xs, S.xfer f as r avs = some a → AVals.Mem avs xs →
    ∃ y, T.call f as r xs = some y ∧ AVal.Mem r a y
  cmp : ∀ f p w (x y : BitVec w) b, S.cmp? f = some p →
    T.call f [.word w, .word w] .bit (.cons x (.cons y .nil)) = some b → b = p.denote x y
  and_ : ∀ f (x y b : Bool), S.conn? f = some .and →
    T.call f [.bit, .bit] .bit (.cons x (.cons y .nil)) = some b → b = (x && y)
  or_ : ∀ f (x y b : Bool), S.conn? f = some .or →
    T.call f [.bit, .bit] .bit (.cons x (.cons y .nil)) = some b → b = (x || y)
  not_ : ∀ f (x b : Bool), S.conn? f = some .not →
    T.call f [.bit] .bit (.cons x .nil) = some b → b = !x

/-- The facts of an unsigned comparison of the words at the levels `l` and `r`, for `true` and
    for `false`; none for a signed comparison. -/
def cmpFacts (p : NfPred) (l r : Nat) : List Fact × List Fact :=
  match p with
  | .ult => ([⟨true, l, r⟩], [⟨false, r, l⟩])
  | .ule => ([⟨false, l, r⟩], [⟨true, r, l⟩])
  | .ugt => ([⟨true, r, l⟩], [⟨false, l, r⟩])
  | .uge => ([⟨false, r, l⟩], [⟨true, l, r⟩])
  | .eq => ([⟨false, l, r⟩, ⟨false, r, l⟩], [])
  | .ne => ([], [⟨false, l, r⟩, ⟨false, r, l⟩])
  | _ => ([], [])

/-- The abstract bit of a call of `f` whose transfer function gave `a`: for a connective, the
    connective of the abstract bits of the arguments; for a comparison of two words of one
    width, `a` with the facts of the comparison of their levels. -/
def callBit (S : NameSpec) {Γ : Ctxt nfDialect} (A : AEnv Γ) (f : String) :
    (as : List NfTy) → HVector (fun t => Var Γ t) as → ABit → ABit
  | [.bit, .bit], .cons x (.cons y .nil), a =>
    match S.conn? f with
    | some .and => let c := ABit.and (A.get x) (A.get y); { c with val := c.val <|> a.val }
    | some .or => let c := ABit.or (A.get x) (A.get y); { c with val := c.val <|> a.val }
    | _ => a
  | [.bit], .cons x .nil, a =>
    match S.conn? f with
    | some .not => let c := ABit.not (A.get x); { c with val := c.val <|> a.val }
    | _ => a
  | [.word w, .word w'], .cons x (.cons y .nil), a =>
    match S.cmp? f with
    | some p =>
      if w = w' then
        let fs := cmpFacts p (varLevel x) (varLevel y)
        { a with tt := fs.1, ff := fs.2 }
      else a
    | none => a
  | _, _, a => a

/-! ## 4. Abstract operations -/

/-- The abstract value of a call: the transfer function's result without facts, with the facts
    of `callBit` at a bit. -/
def callXfer (S : NameSpec) {Γ : Ctxt nfDialect} (A : AEnv Γ) (f : String) (as : List NfTy)
    (r : NfTy) (args : HVector (fun t => Var Γ t) as) : Except String (AVal r) :=
  let avs := A.getArgs args
  match S.xfer f as r avs with
  | none => .error s!"call {f} refused at {AVals.strs avs}"
  | some a =>
    match r, AVal.restrict 0 r a with
    | .bit, a => .ok (callBit S A f as args a)
    | _, a => .ok a

/-- The abstract value of an operation on variables of the environment `A`. -/
def evalOp (S : NameSpec) {Γ : Ctxt nfDialect} (A : AEnv Γ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Except String (AVal op.ret)
  | .const _ v, _ => .ok (ivPoint v.toNat)
  | .constBit b, _ => .ok (ABit.known b)
  | .constUnit, _ => .ok ()
  | .ilit t v, _ =>
    if (NfTy.ofLit? t v).isSome then .ok (AVal.ofLit t v)
    else .error s!"literal {v} outside the type {reprStr t}"
  | .notB, .cons x .nil => .ok (ABit.not (A.get x))
  | .andB, .cons x (.cons y .nil) => .ok (ABit.and (A.get x) (A.get y))
  | .orB, .cons x (.cons y .nil) => .ok (ABit.or (A.get x) (A.get y))
  | .call f as r, args => callXfer S A f as r args
  | .named _ op, args => evalOp S A op args
  | .abort _, _ => .error "a reachable abort"
  | op, _ => .error s!"operation {reprStr op} outside the checked class"

/-- The abstract value of an expression. -/
def evalExpr (S : NameSpec) {Γ : Ctxt nfDialect} {t : NfTy} (A : AEnv Γ)
    (e : Expr nfDialect Γ t) : Except String (AVal t) :=
  match e with
  | ⟨op, h, args⟩ => h ▸ evalOp S A op args

/-! ## 5. The checker -/

/-- The invariant of a counted loop with the abstract iteration `step`, from the candidate
    `J`: `J` when one iteration from it stays in it; otherwise, with `n + 1` attempts left, the
    join of `J` with the values after the iteration, widened before the last attempt. -/
def loopFix {cs : List NfTy} (step : AVals cs → Except String (AVals cs)) :
    Nat → AVals cs → Except String (AVals cs)
  | 0, J => do
    let r ← step J
    if AVals.le r J then pure J
    else .error s!"loop: the carried values {AVals.strs r} leave the invariant {AVals.strs J}"
  | n + 1, J => do
    let r ← step J
    if AVals.le r J then pure J
    else loopFix step n (if n = 0 then AVals.widen J (AVals.join J r) else AVals.join J r)

/-- The checker: the abstract values of the results of `p` from the abstract environment `A`,
    or the reason of a refusal. -/
def run (S : NameSpec) : {Γ : Ctxt nfDialect} → {ts : List NfTy} → AEnv Γ →
    NFProg nfDialect Γ ts → Except String (AVals ts)
  | _, _, A, .ret vs => .ok (A.getArgs vs)
  | _, _, A, .var e k => do
    let a ← evalExpr S A e
    run S (.cons a A) k
  | Γ, _, A, .forLoop (cs := cs) cnt inits body k => do
    let ci : Iv := A.get cnt
    let a0 : AVals cs := A.getArgs inits
    let step : Iv → AVals cs → Except String (AVals cs) := fun ctr J =>
      AVals.restrict Γ.length <$>
        run S (hvAppend (d := nfDialect) (f := AVal) J (HVector.cons (t := NfTy.word 64) ctr A))
          body
    let J ← if ci.2 ≤ 0 then pure a0
      else if ci.1 = ci.2 ∧ ci.2 ≤ S.unroll then
        (List.range ci.2.toNat).foldlM (fun J i => step (ivPoint i) J) a0
      else loopFix (step (0, ci.2 - 1)) 3 a0
    run S (hvAppend (d := nfDialect) (f := AVal) J A) k
  | Γ, _, A, .ifThenElse (rs := rs) c thn els k => do
    let rt ← if A.reach c true then some <$> run S (A.refineBit c true) thn else pure none
    let re ← if A.reach c false then some <$> run S (A.refineBit c false) els else pure none
    let r : AVals rs := match rt, re with
      | some x, some y => AVals.join x y
      | some x, none => x
      | none, some y => y
      | none, none => AVals.top rs
    run S (hvAppend (d := nfDialect) (f := AVal) (AVals.restrict Γ.length r) A) k
  | _, _, _, .whileLoop _ _ _ => .error "an exit-flag loop (whileLoop) is outside the checked class"
  | _, _, _, .call f _ _ => .error s!"the call of the symbol {f} is outside the checked class"

/-- **The interval checker**: the abstract values of the results of `p` from `A`, or `none`
    when the checker cannot show that no operation of `p` fails. -/
def check (S : NameSpec) {Γ : Ctxt nfDialect} {ts : List NfTy} (A : AEnv Γ)
    (p : NFProg nfDialect Γ ts) : Option (AVals ts) :=
  (run S A p).toOption

/-- The reason the checker refuses `p` from `A`; `none` when it accepts. -/
def refusal (S : NameSpec) {Γ : Ctxt nfDialect} {ts : List NfTy} (A : AEnv Γ)
    (p : NFProg nfDialect Γ ts) : Option String :=
  match run S A p with
  | .error e => some e
  | .ok _ => none

/-! ## 6. The names of the Aeneas reading

The names are those of `aeCallV` (`AeneasFront/NFToRustM.lean`). A word argument is read as an
Aeneas word of the width of the tag, which needs its value below `2 ^ w`; the tag `size` is read
at `32` bits, at most the width of `usize` on every platform. A result is decoded at the result
type of the call, which needs a word below `2 ^ w` of that type. -/

/-- The width tags of the tagged names and the widths they are read at. -/
def aeTags : List (String × Nat) := [("8", 8), ("16", 16), ("32", 32), ("64", 64), ("size", 32)]

/-- The tagged binary word operations of the Aeneas reading. -/
inductive AeWordOp where
  | band | bor | bxor | wadd | wsub | wmul | shr | shl | rotr | rotl
  deriving DecidableEq, Repr

/-- The names of the word operations before their tag. -/
def aeWordOps : List (String × AeWordOp) :=
  [("BitAnd#", .band), ("BitOr#", .bor), ("BitXor#", .bxor), ("wrapping_add#", .wadd),
   ("wrapping_sub#", .wsub), ("wrapping_mul#", .wmul), ("Shr#", .shr), ("Shl#", .shl),
   ("rotate_right#", .rotr), ("rotate_left#", .rotl)]

/-- The word operations read at the tag `size`: those whose value does not depend on the
    width. -/
def AeWordOp.atSize : AeWordOp → Bool
  | .band | .bor | .bxor | .shr => true
  | _ => false

/-- The checked operations of the Aeneas reading. -/
inductive AeChecked where
  | add | sub | mul
  deriving DecidableEq, Repr

/-- The operation and width of a tagged word operation name. -/
def aeWordName? (f : String) : Option (AeWordOp × Nat) :=
  aeTags.findSome? fun (tag, b) => aeWordOps.findSome? fun (pre, o) =>
    if f == pre ++ tag && (tag != "size" || o.atSize) then some (o, b) else none

/-- The operation and width of a checked name `Add#t`, `Sub#t` or `Mul#t`. -/
def aeCheckedName? (f : String) : Option (AeChecked × Nat) :=
  aeTags.findSome? fun (tag, b) =>
    [("Add#", AeChecked.add), ("Sub#", .sub), ("Mul#", .mul)].findSome? fun (pre, o) =>
      if f == pre ++ tag then some (o, b) else none

/-- The width of a name `pre ++ t` at a tag `t` other than `size`. -/
def aeTagAt? (pre f : String) : Option Nat :=
  aeTags.findSome? fun (tag, b) => if tag != "size" && f == pre ++ tag then some b else none

/-- The comparison of a comparison name. -/
def aeCmp? : String → Option NfPred
  | "Lt" => some .ult
  | "Le" => some .ule
  | "Gt" => some .ugt
  | "Ge" => some .uge
  | "Eq" => some .eq
  | "Ne" => some .ne
  | _ => none

/-- The connective of a connective name. -/
def aeConn? : String → Option Conn
  | "&&" => some .and
  | "||" => some .or
  | "Not" => some .not
  | _ => none

/-- An interval of values below `2 ^ b`. -/
def below (b : Nat) (i : Iv) : Bool := decide (i.2 < (2 : Int) ^ b)

/-- The interval with its lower bound raised to `0`; it holds every `toNat` the interval
    holds. -/
def nn (i : Iv) : Iv := (max 0 i.1, i.2)

/-- The abstract result at the result type `r` of a word in `i`, when `i` lies below `2 ^ w`
    for the width `w` of `r`. -/
def retWord (r : NfTy) (i : Iv) : Option (AVal r) :=
  match r with
  | .word w => if below w i then some i else none
  | _ => none

/-- The abstract result at the result type `r` of a bit. -/
def retBit (r : NfTy) (a : ABit) : Option (AVal r) :=
  match r with
  | .bit => some a
  | _ => none

/-- The abstract result at the result type `r` of an array of `n` words in `i`, when `r` is an
    array of `n` words of a width `w` and `i` lies below `2 ^ w`. -/
def retArr (r : NfTy) (n : Nat) (i : Iv) : Option (AVal r) :=
  match r with
  | .arr m (.word w) => if m = n && below w i then some i else none
  | _ => none

/-- The value of a comparison of two words of nonnegative intervals, when the intervals decide
    it. -/
def cmpVal (p : NfPred) (a b : Iv) : Option Bool :=
  match p with
  | .ult => if a.2 < b.1 then some true else if b.2 ≤ a.1 then some false else none
  | .ule => if a.2 ≤ b.1 then some true else if b.2 < a.1 then some false else none
  | .ugt => if b.2 < a.1 then some true else if a.2 ≤ b.1 then some false else none
  | .uge => if b.2 ≤ a.1 then some true else if a.2 < b.1 then some false else none
  | .eq =>
    if a.1 = a.2 ∧ b.1 = b.2 ∧ a.1 = b.1 then some true
    else if a.2 < b.1 ∨ b.2 < a.1 then some false else none
  | .ne =>
    if a.1 = a.2 ∧ b.1 = b.2 ∧ a.1 = b.1 then some false
    else if a.2 < b.1 ∨ b.2 < a.1 then some true else none
  | _ => none

/-- The bit above the highest bit at which the bounds of `x` differ or the bounds of `y`
    differ. -/
def xorPrefixBit (x y : Iv) : Nat :=
  Nat.log2 ((x.1.toNat ^^^ x.2.toNat) ||| (y.1.toNat ^^^ y.2.toNat)) + 1

/-- The interval of the exclusive or of words of the nonnegative intervals `x` and `y` whose
    bounds agree above the bit `k`: the bits above `k` are the exclusive or of those of the
    bounds, the `k` low bits are free. `none` when the bounds differ above `k`. -/
def xorPrefix (k : Nat) (x y : Iv) : Option Iv :=
  if x.1.toNat / 2 ^ k = x.2.toNat / 2 ^ k ∧ y.1.toNat / 2 ^ k = y.2.toNat / 2 ^ k then
    let P : Nat := (x.1.toNat / 2 ^ k ^^^ y.1.toNat / 2 ^ k) * 2 ^ k
    some ((P : Int), (P : Int) + 2 ^ k - 1)
  else none

/-- The interval of a tagged word operation at the width `b` on words of the nonnegative
    intervals `x` and `y`; `none` when a shift amount may reach the width or a rotation amount
    `2 ^ 32`. The exclusive or with the point `2 ^ k` of words below `2 ^ k` is their sum with
    `2 ^ k`; otherwise the exclusive or has the bits on which the bounds of both intervals
    agree (`xorPrefix`), below the power of two above both upper bounds. A wrapping sum whose
    exact interval lies at or above `2 ^ b` is that interval less `2 ^ b`. -/
def wordXfer (o : AeWordOp) (b : Nat) (x y : Iv) : Option Iv :=
  let top : Iv := (0, 2 ^ b - 1)
  match o with
  | .band => some (0, min x.2 y.2)
  | .bor => some (0, min (2 ^ b - 1) (2 ^ (Nat.log2 (max x.2 y.2).toNat + 1) - 1))
  | .bxor =>
    if y.1 = y.2 ∧ y.1 = 2 ^ y.1.toNat.log2 ∧ x.2 < y.1 then some (x.1 + y.1, x.2 + y.1)
    else match xorPrefix (xorPrefixBit x y) x y with
      | some I => some (I.1, min I.2 (min (2 ^ b - 1)
          (2 ^ (Nat.log2 (max x.2 y.2).toNat + 1) - 1)))
      | none => some (0, min (2 ^ b - 1) (2 ^ (Nat.log2 (max x.2 y.2).toNat + 1) - 1))
  | .wadd =>
    let s := ivAddZ x y
    some (if s.2 < 2 ^ b then s else if 2 ^ b ≤ s.1 then (s.1 - 2 ^ b, s.2 - 2 ^ b) else top)
  | .wsub => let s := ivSubZ x y; some (if 0 ≤ s.1 then s else top)
  | .wmul => let s : Iv := (x.1 * y.1, x.2 * y.2); some (if s.2 < 2 ^ b then s else top)
  | .shr => if y.2 < b then some (x.1 / 2 ^ y.2.toNat, x.2 / 2 ^ y.1.toNat) else none
  | .shl =>
    if y.2 < b then
      let s : Iv := (x.1 * 2 ^ y.1.toNat, x.2 * 2 ^ y.2.toNat)
      some (if s.2 < 2 ^ b then s else top)
    else none
  | .rotr | .rotl => if y.2 < 2 ^ 32 then some top else none

/-- The interval of a checked operation at the width `b` on words of the nonnegative intervals
    `x` and `y`; `none` when the exact result may leave `[0, 2 ^ b)`. -/
def checkedXfer (o : AeChecked) (b : Nat) (x y : Iv) : Option Iv :=
  match o with
  | .add => let s := ivAddZ x y; if s.2 < 2 ^ b then some s else none
  | .sub => let s := ivSubZ x y; if 0 ≤ s.1 then some s else none
  | .mul => let s : Iv := (x.1 * y.1, x.2 * y.2); if s.2 < 2 ^ b then some s else none

/-- The transfer function of the unary names: `Not` on a bit, the complement `Not#t` and the
    cast `cast#t` of a `u64` word. -/
def aeXfer1 (f : String) (r a : NfTy) (x : AVal a) : Option (AVal r) :=
  if f = "Not" then do
    let p ← bitArg a x
    retBit r p.not
  else match aeTagAt? "Not#" f with
  | some b => do
    let i ← wordArg a x
    if below b i then retWord r (2 ^ b - 1 - (nn i).2, 2 ^ b - 1 - (nn i).1) else none
  | none => match aeTagAt? "cast#" f with
    | some b => do
      let i ← wordArg a x
      if below 64 i then retWord r (if i.2 < 2 ^ b then i else (0, 2 ^ b - 1)) else none
    | none => none

/-- The transfer function of the binary names: the tagged word operations, the checked
    operations, the comparisons of `u64` words, the connectives and `index`. -/
def aeXfer2 (f : String) (r a c : NfTy) (x : AVal a) (y : AVal c) : Option (AVal r) :=
  match aeWordName? f with
  | some (o, b) => do
    let i ← wordArg a x
    let j ← wordArg c y
    if below b i && below b j then retWord r (← wordXfer o b (nn i) (nn j)) else none
  | none => match aeCheckedName? f with
  | some (o, b) => do
    let i ← wordArg a x
    let j ← wordArg c y
    if below b i && below b j then retWord r (← checkedXfer o b (nn i) (nn j)) else none
  | none => match aeCmp? f with
  | some p => do
    let i ← wordArg a x
    let j ← wordArg c y
    if below 64 i && below 64 j then retBit r ⟨cmpVal p (nn i) (nn j), [], []⟩ else none
  | none => match aeConn? f with
  | some .and => do retBit r (ABit.and (← bitArg a x) (← bitArg c y))
  | some .or => do retBit r (ABit.or (← bitArg a x) (← bitArg c y))
  | _ =>
    if f = "index" then do
      let (n, e) ← arrArg a x
      let i ← wordArg c y
      if below 64 e && decide (n < 2 ^ 32) && below 32 i && decide (i.2 < n) then retWord r e
      else none
    else none

/-- The transfer function of the ternary names: `array_update` of an array of `u64` words and
    `select` of one of two `u64` words by a bit. -/
def aeXfer3 (f : String) (r a c d : NfTy) (x : AVal a) (y : AVal c) (z : AVal d) :
    Option (AVal r) :=
  if f = "array_update" then do
    let (n, e) ← arrArg a x
    let i ← wordArg c y
    let v ← wordArg d z
    if below 64 e && decide (n < 2 ^ 32) && below 32 i && decide (i.2 < n) && below 64 v then
      retArr r n (ivHull e v)
    else none
  else if f = "select" then do
    let k ← bitArg a x
    let i ← wordArg c y
    let j ← wordArg d z
    if below 64 i && below 64 j then
      retWord r (match k.val with
        | some true => i
        | some false => j
        | none => ivHull i j)
    else none
  else none

/-- The transfer function of the names of the Aeneas reading, by the number of arguments. -/
def aeXfer (f : String) : (as : List NfTy) → (r : NfTy) → AVals as → Option (AVal r)
  | [a], r, .cons x .nil => aeXfer1 f r a x
  | [a, c], r, .cons x (.cons y .nil) => aeXfer2 f r a c x y
  | [a, c, d], r, .cons x (.cons y (.cons z .nil)) => aeXfer3 f r a c d x y z
  | _, _, _ => none

/-- **The specification of the names of the Aeneas reading.** -/
def aeSpec : NameSpec where
  xfer := aeXfer
  cmp? := aeCmp?
  conn? := aeConn?

/-! ## 7. Examples -/

section Examples

/-- The literal `n` as a 64-bit word. -/
def litW {Γ : Ctxt nfDialect} (n : Int) : Expr nfDialect Γ (.word 64) :=
  ⟨.ilit (.word 64) n, rfl, .nil⟩

/-- A call of a binary name on two 64-bit words. -/
def call2 {Γ : Ctxt nfDialect} (f : String) (r : NfTy) (x y : Var Γ (.word 64)) :
    Expr nfDialect Γ r :=
  ⟨.call f [.word 64, .word 64] r, rfl, .cons x (.cons y .nil)⟩

/-- `x + 1` by the checked addition `Add#64` on the input `x`. -/
def incr : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW 1) (.var (call2 "Add#64" (.word 64) .here (.there .here)) (.ret (.cons .here .nil)))

/-- The input `x` in `[0, 100]`. -/
def small : AEnv [.word 64] := .cons ((0, 100) : Iv) .nil

/-- The input `x` in the full 64-bit range. -/
def full : AEnv [.word 64] := .cons ((0, 2 ^ 64 - 1) : Iv) .nil

example : (check aeSpec small incr).isSome = true := by decide
example : (check aeSpec full incr).isSome = false := by decide

/-- The panic guard `massert (x < 200)` on the input `x`, in the form of the reader: the
    branch on `!(x < 200)` to an aborting arm, then the return of `x`. -/
def guarded : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW 200) <|
  .var (call2 "Lt" .bit (.there .here) .here) <|
  .var ⟨.notB, rfl, .cons .here .nil⟩ <|
  .ifThenElse .here (.var ⟨.abort .unit, rfl, .nil⟩ (.ret .nil)) (.ret .nil) <|
  .ret (.cons (.there (.there (.there .here))) .nil)

example : (check aeSpec small guarded).isSome = true := by decide
example : (check aeSpec full guarded).isSome = false := by decide

/-- The branch on `x < 10` whose arm `x < 10` doubles `x` by the checked `Add#8`: accepted
    by the refinement of `x` in that arm. -/
def refined : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW 10) <|
  .var (call2 "Lt" .bit (.there .here) .here) <|
  .ifThenElse .here
    (.var (call2 "Add#8" (.word 64) (.there (.there .here)) (.there (.there .here)))
      (.ret (.cons .here .nil)))
    (.ret (.cons (.there (.there .here)) .nil)) <|
  .ret (.cons .here .nil)

example : (check aeSpec full refined).isSome = true := by decide

/-- A counted loop of four iterations adding `x` to an accumulator from `0` by `Add#64`. -/
def sum4 : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW 4) <|
  .var (litW 0) <|
  .forLoop (.there .here) (.cons .here .nil)
    (.var (call2 "Add#64" (.word 64) .here (.there (.there (.there (.there .here)))))
      (.ret (.cons .here .nil))) <|
  .ret (.cons .here .nil)

example : (check aeSpec small sum4).isSome = true := by decide
example : (check aeSpec full sum4).isSome = false := by decide

/-- A counted loop of `1000` iterations, beyond `NameSpec.unroll`, adding `x` to an
    accumulator from `0` by the operation `f`. -/
def sumLong (f : String) : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW 1000) <|
  .var (litW 0) <|
  .forLoop (.there .here) (.cons .here .nil)
    (.var (call2 f (.word 64) .here (.there (.there (.there (.there .here)))))
      (.ret (.cons .here .nil))) <|
  .ret (.cons .here .nil)

example : (check aeSpec small (sumLong "wrapping_add#64")).isSome = true := by decide
example : (check aeSpec small (sumLong "Add#64")).isSome = false := by decide

/-- The sign extension of the `i32` pattern `x` (the exclusive or with the sign bit `2 ^ 31`,
    then the wrapping difference with it), followed by the checked `x + x` at `32` bits:
    accepted for `x` in `[0, 100]`, where the sign extension is `x`. -/
def sext32 : NFProg nfDialect [.word 64] [.word 64] :=
  .var (litW (2 ^ 31)) <|
  .var (call2 "BitXor#64" (.word 64) (.there .here) .here) <|
  .var (call2 "wrapping_sub#64" (.word 64) .here (.there .here)) <|
  .var (call2 "Add#32" (.word 64) .here .here) <|
  .ret (.cons .here .nil)

example : (check aeSpec small sext32).isSome = true := by decide

/-- The wrapping sum `2 ^ 64 - 1 + 2 = 1` of two literals, followed by the checked `+ 1` at
    `8` bits: accepted, since the wrapping sum is the point `1`. -/
def wrapLits : NFProg nfDialect [] [.word 64] :=
  .var (litW (2 ^ 64 - 1)) <|
  .var (litW 2) <|
  .var (call2 "wrapping_add#64" (.word 64) (.there .here) .here) <|
  .var (litW 1) <|
  .var (call2 "Add#8" (.word 64) (.there .here) .here) <|
  .ret (.cons .here .nil)

example : (check aeSpec .nil wrapLits).isSome = true := by decide

end Examples

end CatCrypt.Crypto.SecureCompilation.VIR.NFRange
