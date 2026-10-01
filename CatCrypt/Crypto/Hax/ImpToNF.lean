/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
public import CatCrypt.Crypto.Hax.DenoteKeeps
public import HaxLean.Phase.ContinueFlag
public import CatCrypt.Hax.Ascent.Fuel
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgDCE
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTyped

/-!
# The front from the normal form of `HaxLean` to `NFProg nfDialect`

`impToNF` translates an `ImpExpr` in the normal form `NF` of `HaxLean` to an `NFProg`
program over `nfDialect`. The source semantics is `denote'`, which threads one global
environment: a `letBind` and an `assign` both update the environment, and a binding made
inside a loop body survives the iteration. The translation is single static assignment:
an environment of names `NfEnv Γ` maps each name to the newest variable holding its
value, a binding or an assignment rebinds the name, and a counted loop carries, as its
tuple, every name of the environment the body may bind (`frameOk` with the binding check
`· != x` fails), the loop counter excepted.

Values. The source values of a type `t` are the encodings `enc t x` of the values `x` of
`⟦t⟧`: an unsigned integer of a width is `.uint W`, a signed one `.sint W`, an unbounded
integer `.int`, a bit `.bool`, a tuple `.tuple`, a slice `.array`. The relation between a
source environment and a valuation is `EnvRel`: every name of `NfEnv` reads in the
environment the encoding of its variable's value.

Calls. Every call `app f args` is the leaf call `NfOp.call f as r`, at the types `as` of
its atoms and the result type `r = sigOf f as`; the leaf table is `tableOf bi`, which
encodes the arguments, calls the builtin and decodes the result. The hypothesis
`TypedCalls bi sigOf` states that every builtin, called on encoded arguments of the types
`as`, returns the encoding of a value of type `sigOf f as`; it is the only assumption on
the builtins.

Fragment. A literal, a variable, `unitVal`, `typeAscription`, `seq`, `letBind`, `assign`,
a call on atoms, a tuple of atoms, and a counted loop `forFold` with a non-negative integer
literal as lower bound, an atom of an unsigned integer or word type of at most `64` bits
(`boundOk`) or an integer literal below `2 ^ 64` (`litBoundOk`) as upper bound, and a body in
the fragment. Every other constructor is `none`.

Readback. `nfToImp` reads an `NFProg` program back to an `ImpExpr` from a reading `RBEnv`
of its context: a binding named by `NfOp.named` is a `letBind` of its source name, an
unnamed call a `letBind` of a fresh temporary, and a counted loop whose body starts with a
named counter is a `forFold` on that name. `nfRoute` is the front, `NFProg.dce`, and the
readback; its run keeps the value of the source run (`nfRoute_run`), so the typed exit
lowering of the route simulates the source (`nfRoute_simulates_exit`).

## Main definitions

* `enc`, `dec`, `encAll` — the encoding of the values of an `NfTy` as source values, and
  the partial decoding.
* `tableOf`, `TypedCalls` — the leaf table of a builtin table, and its typing hypothesis.
* `NfEnv`, `NfEnv.lookup`, `EnvRel` — the environment of names and its relation to a
  source environment.
* `Out`, `ArgsOut` — the output of the front on an expression and on a list of atoms.
* `loopOut` — the counted loop of the front.
* `impToNF` — the front.
* `PDen`, `PDenP` — the denotation of a prefix and of a program with the leaves of
  `tableOf bi`.
* `Sound` — the simulation statement for one expression.
* `CarriedRel`, `FrameRel` — the carried names and the other names of a loop.
* `RB`, `RBEnv`, `rbProg`, `nfToImp` — the readings of variables and the readback.
* `RBRel`, `RBSound` — the relation of a reading to a source environment, and the
  simulation statement of the readback.
* `Out.prog`, `nfRoute` — the program of an output, and the route through `NFProg`.
* `entryCtx`, `entryEnv`, `entryRB`, `EntryTyped`, `nfRouteEntry` — the parameters of a
  function body and the route from them.
* `ScalarBin`, `ScalarUn`, `ScalarCmp`, `hax64BinTable`, `hax64UnTable`, `hax64CmpTable` —
  the scalar calls of `u64` code at the widths `8`, `16`, `32`, `64`, with their operation.
* `hax64ScalarSig`, `hax64SigOf` — the call typing of `u64` code: a `64`-bit word result for
  an integer call, a bit for a comparison.

## Main results

* `atomOut_sound`, `argsOut_sound`, `tupleOut_sound`, `seq_sound`, `letBind_sound`,
  `assign_sound`, `app_sound`, `tuple_sound` — the constructs other than the loop.
* `loop_sound`, `loopOut_sound`, `forFold_sound` — the counted loop: the trips of
  `denoteForLoop'` against the fold of `NFProg.forLoop`.
* `impToNF_sound` — the front simulates `denote'`.
* `rbLoop_run` — the trips of a counted loop against the run of its readback.
* `rbProg_sound_aux`, `nfToImp_denote` — the readback simulates the denotation.
* `nfRoute_run`, `nfRoute_simulates_exit` — the route through `NFProg` keeps the value,
  and its typed exit lowering simulates the source.
* `entryEnv_rel`, `entryRB_rel`, `nfRouteEntry_simulates_exit` — the environment of names
  and the reading of the parameters of a function body, related to a source environment
  typed at the parameters (`EntryTyped`).
* `hax64BinTable_sem`, `hax64UnTable_sem`, `hax64CmpTable_sem` — the scalar calls compute
  their operation.
* `hax64Builtins_typedCalls` — the call typing `hax64SigOf` of `u64` code is sound for
  `Hax.hax64Builtins`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpToNF

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins IntWidth denote' denoteArgs')
open _root_.Hax.InlineLocalClosures (frameOk)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## 1. Values -/

/-- The components of a tuple value, and a one-element list for every other value. -/
def tailVals : Value → List Value
  | .tuple vs => vs
  | v => [v]

/-- The source value of a value of an `NfTy`. -/
def enc : (t : NfTy) → t.denote → Value
  | .bit, b => .bool b
  | .unit, _ => .unit
  | .word _, x => .int x.toNat
  | .arr _ t, f => .array (List.ofFn fun i => enc t (f i))
  | .pair a b, p => .tuple [enc a p.1, enc b p.2]
  | .uint W, x => .uint W x.toNat
  | .sint W, x => .sint W x.toInt
  | .int, x => .int x
  | .tnil, _ => .tuple []
  | .tcons h t, p => .tuple (enc h p.1 :: tailVals (enc t p.2))
  | .slice t, xs => .array (xs.map (enc t))

/-- The value of the type `t` whose encoding has the components `vs` after a first one:
    the tuple of `vs` when `t` is a tuple type, the single value of `vs` otherwise, and a
    control-flow value, which `dec` decodes at no type, when `vs` has another length. -/
def tailVal (t : NfTy) (vs : List Value) : Value :=
  match t, vs with
  | .tnil, vs => .tuple vs
  | .tcons _ _, vs => .tuple vs
  | _, [v] => v
  | _, _ => .controlFlow false .unit

/-- The value of the type `t` a source value encodes, at the types the front produces;
    `none` for every other value. -/
def dec : (t : NfTy) → Value → Option t.denote
  | .bit, .bool b => some b
  | .unit, .unit => some ()
  | .word w, .int n => if 0 ≤ n ∧ n < 2 ^ w then some (BitVec.ofNat w n.toNat) else none
  | .uint W, .uint W' n =>
      if W' = W ∧ n < 2 ^ W.bits then some (BitVec.ofNat W.bits n) else none
  | .sint W, .sint W' n =>
      if W' = W ∧ -2 ^ (W.bits - 1) ≤ n ∧ n < 2 ^ (W.bits - 1) then
        some (BitVec.ofInt W.bits n)
      else none
  | .int, .int n => some n
  | .tnil, .tuple [] => some ()
  | .tcons h t, .tuple (v :: vs) =>
      (dec h v).bind fun x => (dec t (tailVal t vs)).map fun y => (x, y)
  | .slice t, .array vs => vs.mapM (dec t)
  | .arr n t, .array vs =>
      (vs.mapM (dec t)).bind fun ys =>
        if h : ys.length = n then some fun i => ys[i.1]'(h ▸ i.2) else none
  | _, _ => none

/-- The source values of a vector of values. -/
def encAll : (as : List NfTy) → HVector NfTy.denote as → List Value
  | [], .nil => []
  | a :: as, .cons x xs => enc a x :: encAll as xs

/-- The leaf table of the builtins `bi`: a call encodes its arguments, calls the builtin,
    and decodes the result at the result type. -/
def tableOf (bi : Builtins) : NfLeafTable :=
  ⟨fun f as r xs => (bi f (encAll as xs)).bind (dec r)⟩

/-- **The typing of the builtins.** Whenever `sigOf f as = some r`, a call of the builtin
    `f` on the encodings of values of the types `as` returns the encoding of a value of
    type `r` that `dec r` decodes. -/
def TypedCalls (bi : Builtins) (sigOf : String → List NfTy → Option NfTy) : Prop :=
  ∀ f as r, sigOf f as = some r → ∀ (xs : HVector NfTy.denote as) (v : Value),
    bi f (encAll as xs) = some v → ∃ y, dec r v = some y ∧ v = enc r y

/-! ## 2. Environments of names -/

/-- An environment of names over the context `Γ`: each name with the variable holding
    its value; the first entry of a name is the current one. -/
abbrev NfEnv (Γ : Ctxt nfDialect) : Type := List (String × (Σ t : NfTy, Var Γ t))

/-- The current variable of a name. -/
def NfEnv.lookup {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (x : String) : Option (Σ t : NfTy, Var Γ t) :=
  (σ.find? (·.1 == x)).map (·.2)

/-- An environment of names moved along a map of variables. -/
def NfEnv.mapV {Γ Δ : Ctxt nfDialect} (f : ∀ {t : NfTy}, Var Γ t → Var Δ t) (σ : NfEnv Γ) :
    NfEnv Δ :=
  σ.map fun p => (p.1, ⟨p.2.1, f p.2.2⟩)

/-- Every name of the environment `σ` reads in the source environment `env` the encoding
    of its variable's value in `V`. -/
def EnvRel {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (env : Env) (V : Valuation Γ) : Prop :=
  ∀ x t (v : Var Γ t), σ.lookup x = some ⟨t, v⟩ → env x = some (enc t (v.lookup V))

/-! ## 3. The front -/

/-- The expression applying the operation `op` to the variables `args`. -/
def mkE {Γ : Ctxt nfDialect} (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) :
    Expr nfDialect Γ op.ret :=
  ⟨op, rfl, args⟩

/-- The output of the front on an expression over `Γ`: a prefix to the context `Δ`, the
    environment of names at its hole, and the variable of the value, of type `t`. -/
structure Out (Γ : Ctxt nfDialect) where
  /-- The context at the hole. -/
  Δ : Ctxt nfDialect
  /-- The type of the value. -/
  t : NfTy
  /-- The prefix. -/
  pre : NFPre nfDialect Γ Δ
  /-- The environment of names at the hole. -/
  σ : NfEnv Δ
  /-- The variable of the value. -/
  res : Var Δ t

/-- The output of the front on a list of atoms: a prefix to `Δ`, the environment of names
    at its hole, and the variables of the values, of the types `as`. -/
structure ArgsOut (Γ : Ctxt nfDialect) where
  /-- The context at the hole. -/
  Δ : Ctxt nfDialect
  /-- The types of the values. -/
  as : List NfTy
  /-- The prefix. -/
  pre : NFPre nfDialect Γ Δ
  /-- The environment of names at the hole. -/
  σ : NfEnv Δ
  /-- The variables of the values. -/
  vs : HVector (fun t => Var Δ t) as

/-- One binding of the operation `op` on the variables `args`, the environment of names
    shifted past it, its variable as the value. -/
def bind1 {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) : Out Γ :=
  ⟨op.ret :: Γ, op.ret, .var (mkE op args) .nil, σ.mapV .there, .here⟩

/-- The expression applying the operation `op` to the variables `args`, with the source name
    `x` when `tgt = some x` (`NfOp.named`). -/
def mkEN {Γ : Ctxt nfDialect} (tgt : Option String) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) : Expr nfDialect Γ op.ret :=
  match tgt with
  | none => ⟨op, rfl, args⟩
  | some x => ⟨.named x op, rfl, args⟩

/-- `bind1` with the source name `tgt` on the binding. -/
def bind1N {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) : Out Γ :=
  ⟨op.ret :: Γ, op.ret, .var (mkEN tgt op args) .nil, σ.mapV .there, .here⟩

/-- The output `o₂` from the hole of `o`, composed after `o`. -/
def Out.comp {Γ : Ctxt nfDialect} (o : Out Γ) (o₂ : Out o.Δ) : Out Γ :=
  ⟨o₂.Δ, o₂.t, o.pre.append o₂.pre, o₂.σ, o₂.res⟩

/-- The type and the integer value of a literal at the types of `NfTy.ofLit?`. -/
def litInt : ImpLit → Option (NfTy × Int)
  | .int n => some (.int, n)
  | .uintLit W n => some (.uint W, ((n % W.modulus : Nat) : Int))
  | .sintLit W n => some (.sint W, n)
  | _ => none

/-- A literal: a bit, the unit value, or an integer literal that `NfTy.ofLit?` accepts, its
    binding with the source name `tgt`. -/
def litOut {Γ : Ctxt nfDialect} (tgt : Option String) (σ : NfEnv Γ) : ImpLit → Option (Out Γ)
  | .bool b => some (bind1N tgt σ (.constBit b) .nil)
  | .unit => some (bind1N tgt σ .constUnit .nil)
  | l => (litInt l).bind fun ⟨t, v⟩ =>
      if (NfTy.ofLit? t v).isSome then some (bind1N tgt σ (.ilit t v) .nil) else none

/-- An atom: a variable of the environment of names, or a literal. -/
def atomOut {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : ImpExpr → Option (Out Γ)
  | .var x => (σ.lookup x).map fun p => ⟨Γ, p.1, .nil, σ, p.2⟩
  | .lit l => litOut none σ l
  | _ => none

/-- A list of atoms, left to right. -/
def argsOut {Γ : Ctxt nfDialect} (σ : NfEnv Γ) : List ImpExpr → Option (ArgsOut Γ)
  | [] => some ⟨Γ, [], .nil, σ, .nil⟩
  | e :: es => (atomOut σ e).bind fun o => (argsOut o.σ es).map fun os =>
      ⟨os.Δ, o.t :: os.as, o.pre.append os.pre, os.σ, .cons (os.pre.wk o.res) os.vs⟩

/-- The tuple type of the component types `as`. -/
def tupTy : List NfTy → NfTy
  | [] => .tnil
  | a :: as => .tcons a (tupTy as)

/-- The bindings building the tuple of the variables `vs`, and its variable; the last
    binding has the source name `tgt`. -/
def tupleOut : {Γ : Ctxt nfDialect} → (tgt : Option String) → (as : List NfTy) →
    HVector (fun t => Var Γ t) as → (Δ : Ctxt nfDialect) × NFPre nfDialect Γ Δ × Var Δ (tupTy as)
  | Γ, tgt, [], .nil => ⟨.tnil :: Γ, .var (mkEN tgt .tnilV .nil) .nil, .here⟩
  | _, tgt, a :: as, .cons v vs =>
      let r := tupleOut none as vs
      Sigma.mk (NfTy.tcons a (tupTy as) :: r.fst)
        (r.snd.fst.append (.var (mkEN tgt (.tconsV a (tupTy as))
          (.cons (r.snd.fst.wk v) (.cons r.snd.snd .nil))) .nil), .here)

/-- The first `cs.length` variables of `cs ++ Γ`, in order. -/
def headVars {Γ : Ctxt nfDialect} :
    (cs : List NfTy) → HVector (fun t => Var (d := nfDialect) (cs ++ Γ) t) cs
  | [] => .nil
  | _ :: cs => .cons .here (HVector.renameVars (fun v => v.there) (headVars cs))

/-- The names `xs` bound to the variables `vs`, in front of `σ`. -/
def NfEnv.bindAll {Δ : Ctxt nfDialect} : (xs : List String) → (as : List NfTy) →
    HVector (fun t => Var Δ t) as → NfEnv Δ → NfEnv Δ
  | x :: xs, a :: as, .cons v vs, σ => (x, ⟨a, v⟩) :: NfEnv.bindAll xs as vs σ
  | _, _, _, σ => σ

/-- The carried entries of a loop: the current entry of each name of `σ` other than
    `i` that the body `b` may bind. -/
def carried {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (b : ImpExpr) :
    List (String × (Σ t : NfTy, Var Γ t)) :=
  ((σ.map (·.1)).eraseDups.filter fun x =>
      x != i && !frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b).filterMap
    fun x => (σ.lookup x).map fun p => (x, p)

/-- The types and the variables of a list of entries. -/
def entriesVars {Γ : Ctxt nfDialect} :
    List (String × (Σ t : NfTy, Var Γ t)) → (cs : List NfTy) × HVector (fun t => Var Γ t) cs
  | [] => ⟨[], .nil⟩
  | (_, ⟨t, v⟩) :: es => ⟨t :: (entriesVars es).1, .cons v (entriesVars es).2⟩

/-- The current variables of the names `xs` at the types `cs`; `none` when a name is
    unbound or bound at another type. -/
def varsAt {Δ : Ctxt nfDialect} (σ : NfEnv Δ) :
    (xs : List String) → (cs : List NfTy) → Option (HVector (fun t => Var Δ t) cs)
  | [], [] => some .nil
  | x :: xs, c :: cs => (σ.lookup x).bind fun p =>
      if h : p.1 = c then (varsAt σ xs cs).map (.cons (h ▸ p.2)) else none
  | _, _ => none

/-- The bounds the counted loop of the front accepts: a non-negative lower bound and an
    upper bound of an unsigned integer type or a word type of at most `64` bits, so that the
    trip count is below `2 ^ 64`. -/
def boundOk (lo : Int) : NfTy → Bool
  | .uint W => decide (0 ≤ lo) && decide (W.bits ≤ 64)
  | .word w => decide (0 ≤ lo) && decide (w ≤ 64)
  | _ => false

/-- The literal upper bounds the counted loop of the front accepts beside `boundOk`: a
    non-negative lower bound and an integer literal below `2 ^ 64`, so that the trip count is
    below `2 ^ 64`. -/
def litBoundOk (lo : Int) : ImpExpr → Bool
  | .lit (.int n) => decide (0 ≤ lo) && decide (n < 2 ^ 64)
  | _ => false

/-- The environment of names of a loop body or of the continuation of a loop: the carried
    names `xs` bound to the first variables, in front of the names of `σ` other than the
    counter `i`, moved by `g`. -/
def loopEnv {Γ₃ Δ : Ctxt nfDialect} (σ : NfEnv Γ₃) (i : String) (xs : List String)
    (cs : List NfTy) (hv : HVector (fun t => Var Δ t) cs)
    (g : ∀ {t : NfTy}, Var Γ₃ t → Var Δ t) : NfEnv Δ :=
  NfEnv.bindAll xs cs hv (NfEnv.mapV g (σ.filter fun p => p.1 != i))

/-- **The counted loop of the front.** After the prefix `pre₀` to the context `Γ₃`, with
    the environment of names `σ₃`, the lower bound in `loV` and the trip count in `tripV`,
    the loop carrying the names `xs` at the types `cs` from the variables `inits`: the body
    binds the counter `i` to `lo + k` (`ctr`, with the source name `i`), runs the translation
    `rec` of the source body, and returns the carried names; the continuation binds the unit
    value, with the source name `tgt`. -/
def loopOut {Γ Γ₃ : Ctxt nfDialect} (tgt : Option String) (pre₀ : NFPre nfDialect Γ Γ₃)
    (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64)) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ)) : Option (Out Γ) :=
  let σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃) :=
    loopEnv σ₃ i xs cs (headVars cs) fun v => Var.shiftApp (d := nfDialect) cs v.there
  let oC := bind1N (some i) σB .ctr
    (.cons (Var.shiftApp cs (Var.there loV))
      (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))
  (rec ((i, ⟨NfTy.int, oC.res⟩) :: oC.σ)).bind fun ob =>
    (varsAt ob.σ xs cs).map fun rets =>
      let oU := bind1N tgt (loopEnv σ₃ i xs cs (headVars cs) fun v => Var.shiftApp cs v)
        .constUnit .nil
      Out.mk oU.Δ oU.t
        (pre₀.append (.forLoop tripV inits ((oC.pre.append ob.pre).plug (.ret rets)) oU.pre))
        oU.σ oU.res

/-- The front: the `NFProg` prefix computing the value of an expression of the fragment,
    from the environment of names `σ`. The binding of the value has the source name `tgt`
    (the name a `letBind` or an `assign` gives it), and the counter binding of a loop the
    name of the counter. -/
def impToNF (sigOf : String → List NfTy → Option NfTy) :
    Option String → {Γ : Ctxt nfDialect} → NfEnv Γ → ImpExpr → Option (Out Γ)
  | _, _, σ, .var x => atomOut σ (.var x)
  | tgt, _, σ, .lit l => litOut tgt σ l
  | tgt, _, σ, .unitVal => some (bind1N tgt σ .constUnit .nil)
  | tgt, _, σ, .typeAscription e _ => impToNF sigOf tgt σ e
  | tgt, _, σ, .seq a b => (impToNF sigOf none σ a).bind fun oa =>
      (impToNF sigOf tgt oa.σ b).map oa.comp
  | tgt, _, σ, .letBind x v b => (impToNF sigOf (some x) σ v).bind fun ov =>
      (impToNF sigOf tgt ((x, ⟨ov.t, ov.res⟩) :: ov.σ) b).map ov.comp
  | tgt, _, σ, .assign x r => (impToNF sigOf (some x) σ r).map fun o =>
      o.comp (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil)
  | tgt, _, σ, .app f args => (argsOut σ args).bind fun oa => (sigOf f oa.as).map fun r =>
      ⟨r :: oa.Δ, r, oa.pre.append (.var (mkEN tgt (.call f oa.as r) oa.vs) .nil),
        oa.σ.mapV .there, .here⟩
  | tgt, _, σ, .tuple es => (argsOut σ es).map fun oa =>
      let r := tupleOut tgt oa.as oa.vs
      Out.mk r.fst (tupTy oa.as) (oa.pre.append r.snd.fst) (oa.σ.mapV r.snd.fst.wk) r.snd.snd
  | tgt, _, σ, .forFold i (.lit (.int lo)) hi body =>
      let oLo := bind1 σ (.ilit .int lo) .nil
      (atomOut oLo.σ hi).bind fun oHi =>
        if boundOk lo oHi.t || litBoundOk lo hi then
          let oT := bind1 oHi.σ (.trip oHi.t) (.cons (oHi.pre.wk oLo.res) (.cons oHi.res .nil))
          let W := carried oT.σ i body
          loopOut tgt ((oLo.pre.append oHi.pre).append oT.pre) oT.σ
            (oT.pre.wk (oHi.pre.wk oLo.res))
            oT.res i (W.map (·.1)) (entriesVars W).1 (entriesVars W).2
            (fun σB => impToNF sigOf none σB body)
        else none
  | _, _, _, _ => none

/-! ## 4. Values and environments of names -/

open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)

/-- An encoded value is not a control-flow value. -/
theorem enc_ne_controlFlow (t : NfTy) (x : t.denote) (b : Bool) (u : Value) :
    enc t x ≠ .controlFlow b u := by
  cases t <;> simp [enc]

/-- The components after the first of a value `dec` decodes at `t` from `tailVal t vs` are
    `vs`. -/
theorem tailVals_tailVal {t : NfTy} {vs : List Value} {x : t.denote}
    (h : dec t (tailVal t vs) = some x) : tailVals (tailVal t vs) = vs := by
  cases t with
  | tnil => rfl
  | tcons _ _ => rfl
  | _ =>
      match vs, h with
      | [v], h => cases v <;> simp_all [tailVal, tailVals, dec]
      | [], h => simp [tailVal, dec] at h
      | _ :: _ :: _, h => simp [tailVal, dec] at h

/-- **`dec` is sound**: a value it decodes is the encoding of the decoded value. -/
theorem dec_sound : ∀ (t : NfTy) (v : Value) (x : t.denote), dec t v = some x → v = enc t x
  | .bit, v, x, h => by cases v <;> simp_all [dec, enc]
  | .unit, v, x, h => by cases v <;> simp_all [dec, enc]
  | .int, v, x, h => by cases v <;> simp_all [dec, enc]
  | .uint W, v, x, h => by
      cases v with
      | uint W' n =>
          simp only [dec] at h
          split at h
          · rename_i hc
            obtain ⟨rfl, hn⟩ := hc
            simp only [Option.some.injEq] at h
            subst h
            simp [enc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
          · cases h
      | _ => simp [dec] at h
  | .sint W, v, x, h => by
      cases v with
      | sint W' n =>
          simp only [dec] at h
          split at h
          · rename_i hc
            obtain ⟨rfl, hn⟩ := hc
            simp only [Option.some.injEq] at h
            subst h
            simp only [enc, BitVec.toInt_ofInt, Value.sint.injEq, true_and]
            rw [Int.bmod_eq_of_le] <;> cases W' <;> simp_all [IntWidth.bits]
          · cases h
      | _ => simp [dec] at h
  | .tnil, v, x, h => by
      cases v with
      | tuple vs => cases vs <;> simp_all [dec, enc]
      | _ => simp [dec] at h
  | .tcons h₀ t, v, x, h => by
      cases v with
      | tuple vs =>
          cases vs with
          | nil => simp [dec] at h
          | cons w ws =>
              simp only [dec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
              obtain ⟨a, ha, b, hb, rfl⟩ := h
              have e1 := dec_sound h₀ w a ha
              have e2 := dec_sound t (tailVal t ws) b hb
              simp only [enc]
              rw [← e1, ← e2, tailVals_tailVal hb]
      | _ => simp [dec] at h
  | .slice t, v, x, h => by
      cases v with
      | array vs =>
          simp only [dec] at h
          simp only [enc]
          congr 1
          induction vs generalizing x with
          | nil => simp_all
          | cons w ws ih =>
              rw [List.mapM_cons] at h
              rcases ha : dec t w with _ | a
              · simp [ha] at h
              rcases has : ws.mapM (dec t) with _ | as
              · simp [ha, has] at h
              simp only [ha, has, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              simp only [List.map_cons, List.cons.injEq]
              exact ⟨dec_sound t w a ha, ih as has⟩
      | _ => simp [dec] at h
  | .arr n t, v, x, h => by
      cases v with
      | array vs =>
          simp only [dec, Option.bind_eq_some_iff] at h
          obtain ⟨ys, hys, h⟩ := h
          split at h
          · rename_i hn
            subst hn
            simp only [Option.some.injEq] at h
            subst h
            have hmap : ∀ (us : List Value) (zs : List t.denote), us.mapM (dec t) = some zs →
                us = zs.map (enc t) := by
              intro us
              induction us with
              | nil =>
                  intro zs hz
                  simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hz
                  subst hz
                  rfl
              | cons w ws ih =>
                  intro zs hz
                  rw [List.mapM_cons] at hz
                  rcases ha : dec t w with _ | a
                  · simp [ha] at hz
                  rcases has : ws.mapM (dec t) with _ | as
                  · simp [ha, has] at hz
                  simp only [ha, has, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                    Option.some.injEq] at hz
                  subst hz
                  simp only [List.map_cons, List.cons.injEq]
                  exact ⟨dec_sound t w a ha, ih as has⟩
            simp only [enc]
            rw [hmap vs ys hys]
            congr 1
            apply List.ext_getElem <;> simp
          · cases h
      | _ => simp [dec] at h
  | .word w, v, x, h => by
      cases v with
      | int n =>
          simp only [dec] at h
          split at h
          · rename_i hc
            simp only [Option.some.injEq] at h
            subst h
            have hc2 : n < ((2 ^ w : Nat) : Int) := by exact_mod_cast hc.2
            have hn : n.toNat < 2 ^ w := by omega
            simp only [enc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Value.int.injEq]
            omega
          · cases h
      | _ => simp [dec] at h
  | .pair _ _, v, x, h => by cases v <;> simp [dec] at h

/-- The current variable of a name after one more entry. -/
theorem NfEnv.lookup_cons {Γ : Ctxt nfDialect} (y : String) (p : Σ t : NfTy, Var Γ t)
    (σ : NfEnv Γ) (x : String) :
    NfEnv.lookup ((y, p) :: σ) x = if y = x then some p else σ.lookup x := by
  by_cases h : y = x
  · subst h; simp [NfEnv.lookup]
  · simp [NfEnv.lookup, h]

/-- The current variable of a name in a moved environment of names. -/
theorem NfEnv.lookup_mapV {Γ Δ : Ctxt nfDialect} (f : ∀ {t : NfTy}, Var Γ t → Var Δ t)
    (σ : NfEnv Γ) (x : String) :
    (σ.mapV f).lookup x = (σ.lookup x).map fun p => ⟨p.1, f p.2⟩ := by
  induction σ with
  | nil => rfl
  | cons q σ ih =>
      obtain ⟨y, p⟩ := q
      show NfEnv.lookup ((y, ⟨p.1, f p.2⟩) :: NfEnv.mapV f σ) x = _
      rw [NfEnv.lookup_cons, NfEnv.lookup_cons, ih]
      split <;> rfl

/-- A moved environment of names keeps the relation when every moved variable reads the
    same value. -/
theorem EnvRel.mapV {Γ Δ : Ctxt nfDialect} {σ : NfEnv Γ} {env : Env} {V : Valuation Γ}
    (h : EnvRel σ env V) (f : ∀ {t : NfTy}, Var Γ t → Var Δ t) {W : Valuation Δ}
    (hf : ∀ (t : NfTy) (v : Var Γ t), (f v).lookup W = v.lookup V) :
    EnvRel (σ.mapV f) env W := by
  intro x t v hx
  rw [NfEnv.lookup_mapV, Option.map_eq_some_iff] at hx
  obtain ⟨⟨t', v'⟩, hv', heq⟩ := hx
  simp only [Sigma.mk.injEq] at heq
  obtain ⟨rfl, hv⟩ := heq
  rw [h x t' v' hv', ← hf t' v', eq_of_heq hv]

/-- Binding a name to a variable whose value encodes the bound source value keeps the
    relation. -/
theorem EnvRel.cons {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {env : Env} {V : Valuation Γ}
    (h : EnvRel σ env V) (x : String) (t : NfTy) (r : Var Γ t) :
    EnvRel ((x, ⟨t, r⟩) :: σ) (env.extend x (enc t (r.lookup V))) V := by
  intro y t' v hy
  rw [NfEnv.lookup_cons] at hy
  by_cases hxy : x = y
  · subst hxy
    simp only [if_true, Option.some.injEq, Sigma.mk.injEq] at hy
    obtain ⟨rfl, hv⟩ := hy
    rw [Env.extend_same, eq_of_heq hv]
  · rw [if_neg hxy] at hy
    rw [Env.extend_other _ _ _ _ (Ne.symm hxy)]
    exact h y t' v hy

/-! ## 5. Prefixes -/

/-- The denotation of a prefix over `nfDialect` with the leaves of `tableOf bi`. -/
abbrev PDen (bi : Builtins) (fuel : Nat) {Γ Δ : Ctxt nfDialect} (p : NFPre nfDialect Γ Δ)
    (V : Valuation Γ) : Option (Valuation Δ) :=
  @NFPre.denote nfDialect _ _ _ _ (nfDenote (tableOf bi)) fuel Γ Δ p V

/-- The prefix of one binding denotes the valuation extended with the value of the
    operation. -/
theorem PDen_bind1 (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (V : Valuation Γ) :
    PDen bi fuel (bind1 σ op args).pre V =
      (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).map V.extend := by
  simp only [PDen, bind1, NFPre.denote, mkE, Expr.denoteM, nfDenote_denoteM]
  cases nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) <;> rfl

/-- `PDen_bind1` for a binding with a source name. -/
theorem PDen_bind1N (bi : Builtins) (fuel : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (V : Valuation Γ) :
    PDen bi fuel (bind1N tgt σ op args).pre V =
      (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).map V.extend := by
  cases tgt with
  | none => exact PDen_bind1 bi fuel σ op args V
  | some x =>
      simp only [PDen, bind1N, mkEN, NFPre.denote, Expr.denoteM, nfDenote_denoteM]
      show (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun y => some (V.extend y)) = _
      cases nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) <;> rfl

/-- The prefix of a composed output denotes the second prefix at the hole of the first. -/
theorem PDen_append (bi : Builtins) (fuel : Nat) {Γ Δ Θ : Ctxt nfDialect}
    (p : NFPre nfDialect Γ Δ) (q : NFPre nfDialect Δ Θ) (V : Valuation Γ) :
    PDen bi fuel (p.append q) V = (PDen bi fuel p V).bind (PDen bi fuel q) :=
  @NFPre.denote_append nfDialect _ _ _ _ (nfDenote (tableOf bi)) fuel Γ Δ Θ p q V

/-- **The simulation statement** for the expression `e` and the output `o` of the front
    from `σ`: a run of `denote' bi fuel e` from an environment related to `V` to a value
    is matched, at every fuel `tf` of the target, by a valuation `W` of the hole of the
    prefix, related to the final environment, whose result variable encodes the value. -/
def Sound (bi : Builtins) (fuel : Nat) (e : ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (o : Out Γ) : Prop :=
  ∀ (env : Env) (V : Valuation Γ) (v : Value) (env' : Env), EnvRel σ env V →
    (denote' bi fuel e).run env = (.val v, env') →
    ∀ tf, ∃ W, PDen bi tf o.pre V = some W ∧ EnvRel o.σ env' W ∧ v = enc o.t (o.res.lookup W)

/-- The output of one binding is sound when the operation, on the values of its
    arguments, gives a value whose encoding is the source value, and the run leaves the
    environment unchanged. -/
theorem sound_bind1 (bi : Builtins) (fuel : Nat) (e : ImpExpr) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    (h : ∀ env V v env', EnvRel σ env V → (denote' bi fuel e).run env = (.val v, env') →
      env' = env ∧ ∃ x, nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x ∧
        v = enc op.ret x) :
    Sound bi fuel e σ (bind1 σ op args) := by
  intro env V v env' hrel hrun tf
  obtain ⟨rfl, x, hx, rfl⟩ := h env V v env' hrel hrun
  refine ⟨V.extend x, ?_, ?_, rfl⟩
  · rw [PDen_bind1, hx]; rfl
  · exact hrel.mapV (fun v => Var.there v) fun _ _ => rfl

/-- `sound_bind1` for a binding with a source name. -/
theorem sound_bind1N (bi : Builtins) (fuel : Nat) (e : ImpExpr) (tgt : Option String)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
    (h : ∀ env V v env', EnvRel σ env V → (denote' bi fuel e).run env = (.val v, env') →
      env' = env ∧ ∃ x, nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some x ∧
        v = enc op.ret x) :
    Sound bi fuel e σ (bind1N tgt σ op args) := by
  intro env V v env' hrel hrun tf
  obtain ⟨rfl, x, hx, rfl⟩ := h env V v env' hrel hrun
  refine ⟨V.extend x, ?_, ?_, rfl⟩
  · rw [PDen_bind1N, hx]; rfl
  · exact hrel.mapV (fun v => Var.there v) fun _ _ => rfl

/-- The value of an integer literal at its type encodes the source literal. -/
theorem ofLit_enc {l : ImpLit} {t : NfTy} {v : Int} (hl : litInt l = some (t, v))
    {x : t.denote} (hx : NfTy.ofLit? t v = some x) : Value.ofLit l = enc t x := by
  cases l with
  | int n =>
      simp only [litInt, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp only [NfTy.ofLit?, Option.some.injEq] at hx
      subst hx; rfl
  | uintLit W n =>
      simp only [litInt, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp only [NfTy.ofLit?] at hx
      split at hx
      · simp only [Option.some.injEq] at hx
        subst hx
        simp only [Value.ofLit, enc, BitVec.ofInt_natCast, BitVec.toNat_ofNat,
          IntWidth.modulus, Nat.mod_mod]
      · cases hx
  | sintLit W n =>
      simp only [litInt, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      simp only [NfTy.ofLit?] at hx
      split at hx
      · rename_i hr
        simp only [Option.some.injEq] at hx
        subst hx
        simp only [Value.ofLit, enc, BitVec.toInt_ofInt]
        congr 1
        rw [Int.bmod_eq_of_le] <;> cases W <;> simp_all [IntWidth.bits]
      · cases hx
  | bool b => simp [litInt] at hl
  | unit => simp [litInt] at hl

open _root_.Hax.ContinueFlag (var_run lit_run unitVal_run letBind_run seq_run app_run
  args_nil_run args_cons_run forLoop_ge_run forLoop_zero_run forLoop_succ_run)

/-- A literal is sound. -/
theorem litOut_sound (bi : Builtins) (fuel : Nat) (tgt : Option String) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) (l : ImpLit) {o : Out Γ} (h : litOut tgt σ l = some o) :
    Sound bi fuel (.lit l) σ o := by
  have hsrc : ∀ (env : Env) (v : Value) (env' : Env),
      (denote' bi fuel (.lit l)).run env = (.val v, env') → env' = env ∧ v = Value.ofLit l := by
    intro env v env' hr
    rw [lit_run] at hr
    cases hr
    exact ⟨rfl, rfl⟩
  cases l with
  | bool b =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      exact sound_bind1N bi fuel _ tgt σ _ _ fun env V v env' _ hr => by
        obtain ⟨rfl, rfl⟩ := hsrc env v env' hr
        exact ⟨rfl, b, rfl, rfl⟩
  | unit =>
      simp only [litOut, Option.some.injEq] at h
      subst h
      exact sound_bind1N bi fuel _ tgt σ _ _ fun env V v env' _ hr => by
        obtain ⟨rfl, rfl⟩ := hsrc env v env' hr
        exact ⟨rfl, (), rfl, rfl⟩
  | int n | uintLit W n | sintLit W n =>
      simp only [litOut, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hl, hs⟩ := h
      split at hs
      · rename_i hsome
        simp only [Option.some.injEq] at hs
        subst hs
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
        exact sound_bind1N bi fuel _ tgt σ _ _ fun env V v' env' _ hr => by
          obtain ⟨rfl, rfl⟩ := hsrc env v' env' hr
          exact ⟨rfl, x, hx, ofLit_enc hl hx⟩
      · cases hs

/-- An atom is sound, and its run leaves the environment unchanged. -/
theorem atomOut_sound (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (a : ImpExpr) {o : Out Γ} (h : atomOut σ a = some o) : Sound bi fuel a σ o := by
  cases a with
  | var x =>
      simp only [atomOut, Option.map_eq_some_iff] at h
      obtain ⟨⟨t, r⟩, hx, rfl⟩ := h
      intro env V v env' hrel hrun tf
      rw [var_run] at hrun
      have he := hrel x t r hx
      rw [he] at hrun
      cases hrun
      exact ⟨V, rfl, hrel, rfl⟩
  | lit l => exact litOut_sound bi fuel none σ l h
  | _ => simp [atomOut] at h

/-- The run of an atom of `atomOut` leaves the environment unchanged. -/
theorem atomOut_env (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (a : ImpExpr) {o : Out Γ} (h : atomOut σ a = some o) (env : Env) :
    ((denote' bi fuel a).run env).2 = env := by
  cases a with
  | var x =>
      rw [var_run]
      cases env x <;> rfl
  | lit l => rw [lit_run]
  | _ => simp [atomOut] at h

/-! ## 6. Steps of `denote'` at a value that is not a control-flow value -/

section Steps

variable (bi : Builtins) (fuel : Nat)

/-- The arguments after a first argument that runs to a value that is not a control-flow
    value. -/
theorem args_cons_run_val {e : ImpExpr} (es : List ImpExpr) {env e1 : Env} {v : Value}
    (h : (denote' bi fuel e).run env = (.val v, e1)) (hv : ∀ b u, v ≠ .controlFlow b u) :
    (denoteArgs' bi fuel (e :: es)).run env =
      (((denoteArgs' bi fuel es).run e1).1.map (v :: ·), ((denoteArgs' bi fuel es).run e1).2) := by
  rw [args_cons_run, h]
  cases v with
  | controlFlow b u => exact absurd rfl (hv b u)
  | _ => rfl

/-- A binding whose right-hand side runs to a value that is not a control-flow value runs
    its body from the extended environment. -/
theorem letBind_run_val (x : String) {val : ImpExpr} (body : ImpExpr) {env e1 : Env}
    {v : Value} (h : (denote' bi fuel val).run env = (.val v, e1))
    (hv : ∀ b u, v ≠ .controlFlow b u) :
    (denote' bi fuel (.letBind x val body)).run env = (denote' bi fuel body).run (e1.extend x v) := by
  rw [letBind_run, h]
  cases v with
  | controlFlow b u => exact absurd rfl (hv b u)
  | _ => rfl

/-- A sequence whose first part runs to a value that is not a control-flow value runs its
    second part. -/
theorem seq_run_val {a : ImpExpr} (b : ImpExpr) {env e1 : Env} {v : Value}
    (h : (denote' bi fuel a).run env = (.val v, e1)) (hv : ∀ b u, v ≠ .controlFlow b u) :
    (denote' bi fuel (.seq a b)).run env = (denote' bi fuel b).run e1 := by
  rw [seq_run, h]
  cases v with
  | controlFlow b u => exact absurd rfl (hv b u)
  | _ => rfl

/-- An assignment whose right-hand side runs to a value that is not a control-flow value
    extends the environment and returns the unit value. -/
theorem assign_run_val (x : String) {r : ImpExpr} {env e1 : Env} {v : Value}
    (h : (denote' bi fuel r).run env = (.val v, e1)) (hv : ∀ b u, v ≠ .controlFlow b u) :
    (denote' bi fuel (.assign x r)).run env = (.val .unit, e1.extend x v) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure, modify, modifyGet,
    MonadStateOf.modifyGet] at h ⊢
  rw [h]
  cases v with
  | controlFlow b u => exact absurd rfl (hv b u)
  | _ => rfl

/-- A run of a step whose outcome is a value splits into the run of its first part. -/
theorem run_val_split {α : Type} (m : StateM Env α) (env : Env) :
    ∃ a e1, m.run env = (a, e1) := ⟨_, _, rfl⟩

end Steps

/-! ## 7. Lists of atoms, calls and tuples -/

/-- A list of atoms is sound: its run leaves the values encoded by the variables of the
    output, at a valuation of the hole related to the final environment. -/
theorem argsOut_sound (bi : Builtins) (fuel : Nat) (es : List ImpExpr) :
    ∀ {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {oa : ArgsOut Γ}, argsOut σ es = some oa →
    ∀ (env : Env) (V : Valuation Γ) (vals : List Value) (env' : Env), EnvRel σ env V →
    (denoteArgs' bi fuel es).run env = (some vals, env') →
    ∀ tf, ∃ W, PDen bi tf oa.pre V = some W ∧ EnvRel oa.σ env' W ∧
      vals = encAll oa.as (Expr.lookupArgs oa.vs W) := by
  induction es with
  | nil =>
      intro Γ σ oa h env V vals env' hrel hr tf
      simp only [argsOut, Option.some.injEq] at h
      subst h
      rw [args_nil_run] at hr
      cases hr
      exact ⟨V, rfl, hrel, rfl⟩
  | cons e es ih =>
      intro Γ σ oa h env V vals env' hrel hr tf
      simp only [argsOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨o, ho, os, hos, rfl⟩ := h
      obtain ⟨a, e1, h1⟩ := run_val_split (denote' bi fuel e) env
      have he1 : e1 = env := by
        have := atomOut_env bi fuel σ e ho env
        rw [h1] at this; exact this
      subst he1
      cases a with
      | val v =>
          obtain ⟨W1, hW1, hrel1, rfl⟩ := atomOut_sound bi fuel σ e ho e1 V v e1 hrel h1 tf
          rw [args_cons_run_val bi fuel es h1 (enc_ne_controlFlow _ _)] at hr
          obtain ⟨m, e2, h2⟩ := run_val_split (denoteArgs' bi fuel es) e1
          rw [h2] at hr
          cases m with
          | none => cases hr
          | some vals' =>
              cases hr
              obtain ⟨W2, hW2, hrel2, rfl⟩ := ih o.σ hos e1 W1 vals' e2 hrel1 h2 tf
              refine ⟨W2, ?_, hrel2, ?_⟩
              · rw [PDen_append, hW1]; exact hW2
              · show _ :: _ = enc o.t ((os.pre.wk o.res).lookup W2) :: _
                rw [@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) tf _ _ _ os.pre
                  o.res _ _ hW2]
      | _ =>
          rw [args_cons_run, h1] at hr
          cases hr

/-- The bindings of `tupleOut` denote a valuation in which the tuple variable encodes the
    tuple of the encodings of the components. -/
theorem tupleOut_sound (bi : Builtins) (tf : Nat) :
    ∀ {Γ : Ctxt nfDialect} (tgt : Option String) (as : List NfTy)
      (vs : HVector (fun t => Var Γ t) as)
      (V : Valuation Γ), ∃ W, PDen bi tf (tupleOut tgt as vs).2.1 V = some W ∧
        enc (tupTy as) ((tupleOut tgt as vs).2.2.lookup W) =
          .tuple (encAll as (Expr.lookupArgs vs V))
  | _, tgt, [], .nil, V => by cases tgt <;> exact ⟨V.extend (), rfl, rfl⟩
  | _, tgt, a :: as, .cons v vs, V => by
      have ih := tupleOut_sound bi tf none as vs V
      show ∃ W, PDen bi tf ((tupleOut none as vs).2.1.append
          (.var (mkEN tgt (.tconsV a (tupTy as))
            (.cons ((tupleOut none as vs).2.1.wk v) (.cons (tupleOut none as vs).2.2 .nil)))
              .nil)) V = some W ∧
          enc (NfTy.tcons a (tupTy as))
            ((Var.here : Var (NfTy.tcons a (tupTy as) :: (tupleOut none as vs).1) _).lookup W) =
          .tuple (encAll (a :: as) (Expr.lookupArgs (.cons v vs) V))
      generalize tupleOut none as vs = T at ih ⊢
      obtain ⟨Δ, p, rv⟩ := T
      obtain ⟨W1, hW1, henc⟩ := ih
      refine ⟨W1.extend (v.lookup V, rv.lookup W1), ?_, ?_⟩
      · rw [PDen_append, hW1, Option.bind_some]
        cases tgt <;>
        · show (some ((p.wk v).lookup W1, rv.lookup W1)).bind
            (fun x => some (W1.extend (t := NfTy.tcons a (tupTy as)) x)) = _
          rw [@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) tf _ _ _ p v _ _ hW1]
          rfl
      · show Value.tuple (enc a (v.lookup V) :: tailVals (enc (tupTy as) (rv.lookup W1))) = _
        rw [henc]
        rfl

/-! ## 8. The constructs other than the loop -/

/-- A sequence of two sound outputs is sound. -/
theorem seq_sound (bi : Builtins) (fuel : Nat) {a b : ImpExpr} {Γ : Ctxt nfDialect}
    {σ : NfEnv Γ} {oa : Out Γ} (ha : Sound bi fuel a σ oa) {ob : Out oa.Δ}
    (hb : Sound bi fuel b oa.σ ob) : Sound bi fuel (.seq a b) σ (oa.comp ob) := by
  intro env V v env' hrel hrun tf
  obtain ⟨ra, e1, h1⟩ := run_val_split (denote' bi fuel a) env
  cases ra with
  | val va =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := ha env V va e1 hrel h1 tf
      rw [seq_run_val bi fuel b h1 (enc_ne_controlFlow _ _)] at hrun
      obtain ⟨W2, hW2, hrel2, rfl⟩ := hb e1 W1 v env' hrel1 hrun tf
      exact ⟨W2, by show PDen bi tf (oa.pre.append ob.pre) V = _; rw [PDen_append, hW1]; exact hW2,
        hrel2, rfl⟩
  | _ => rw [seq_run, h1] at hrun; cases hrun

/-- A binding of a sound output, followed by a sound output from the environment of names
    with the bound name, is sound. -/
theorem letBind_sound (bi : Builtins) (fuel : Nat) (x : String) {v b : ImpExpr}
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {ov : Out Γ} (hv : Sound bi fuel v σ ov)
    {ob : Out ov.Δ} (hb : Sound bi fuel b ((x, ⟨ov.t, ov.res⟩) :: ov.σ) ob) :
    Sound bi fuel (.letBind x v b) σ (ov.comp ob) := by
  intro env V w env' hrel hrun tf
  obtain ⟨rv, e1, h1⟩ := run_val_split (denote' bi fuel v) env
  cases rv with
  | val wv =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := hv env V wv e1 hrel h1 tf
      rw [letBind_run_val bi fuel x b h1 (enc_ne_controlFlow _ _)] at hrun
      obtain ⟨W2, hW2, hrel2, rfl⟩ := hb _ W1 w env' (hrel1.cons x ov.t ov.res) hrun tf
      exact ⟨W2, by show PDen bi tf (ov.pre.append ob.pre) V = _; rw [PDen_append, hW1]; exact hW2,
        hrel2, rfl⟩
  | _ => rw [letBind_run, h1] at hrun; cases hrun

/-- An assignment of a sound output is sound. -/
theorem assign_sound (bi : Builtins) (fuel : Nat) (x : String) (tgt : Option String)
    {r : ImpExpr} {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ} (hr : Sound bi fuel r σ o) :
    Sound bi fuel (.assign x r) σ
      (o.comp (bind1N tgt ((x, ⟨o.t, o.res⟩) :: o.σ) .constUnit .nil)) := by
  intro env V w env' hrel hrun tf
  obtain ⟨rv, e1, h1⟩ := run_val_split (denote' bi fuel r) env
  cases rv with
  | val wv =>
      obtain ⟨W1, hW1, hrel1, rfl⟩ := hr env V wv e1 hrel h1 tf
      rw [assign_run_val bi fuel x h1 (enc_ne_controlFlow _ _)] at hrun
      cases hrun
      refine ⟨W1.extend (), ?_, (hrel1.cons x o.t o.res).mapV (fun v => Var.there v)
        fun _ _ => rfl, rfl⟩
      exact (PDen_append bi tf o.pre _ V).trans
        (by rw [hW1, Option.bind_some]
            exact (PDen_bind1N bi tf tgt _ .constUnit .nil W1).trans rfl)
  | _ =>
      simp only [denote', StateT.run, bind, StateT.bind, pure, modify, modifyGet,
        MonadStateOf.modifyGet] at h1 hrun
      rw [h1] at hrun
      cases hrun

/-- A call of a builtin on atoms is sound under `TypedCalls`. -/
theorem app_sound (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (fuel : Nat) (tgt : Option String) (f : String)
    (args : List ImpExpr) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.app f args) = some o) : Sound bi fuel (.app f args) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, r, hr, rfl⟩ := h
  intro env V v env' hrel hrun tf
  obtain ⟨m, e1, h1⟩ := run_val_split (denoteArgs' bi fuel args) env
  rw [app_run, h1] at hrun
  cases m with
  | none => cases hrun
  | some vals =>
      obtain ⟨W, hW, hrel1, rfl⟩ := argsOut_sound bi fuel args σ hoa env V vals e1 hrel h1 tf
      dsimp only at hrun
      cases hb : bi f (encAll oa.as (Expr.lookupArgs oa.vs W)) with
      | none => rw [hb] at hrun; cases hrun
      | some w =>
          rw [hb] at hrun
          cases hrun
          obtain ⟨y, hy, rfl⟩ := hT f oa.as r hr _ _ hb
          refine ⟨W.extend y, ?_, hrel1.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
          show PDen bi tf (oa.pre.append _) V = _
          rw [PDen_append, hW, Option.bind_some]
          cases tgt <;>
          · show ((tableOf bi).call f oa.as r (Expr.lookupArgs oa.vs W)).bind
              (fun x => some (W.extend (t := r) x)) = _
            simp only [tableOf, hb, Option.bind_some, hy]

/-- A tuple of atoms is sound. -/
theorem tuple_sound (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (es : List ImpExpr) {Γ : Ctxt nfDialect}
    (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.tuple es) = some o) : Sound bi fuel (.tuple es) σ o := by
  simp only [impToNF, Option.map_eq_some_iff] at h
  obtain ⟨oa, hoa, rfl⟩ := h
  intro env V v env' hrel hrun tf
  obtain ⟨m, e1, h1⟩ := run_val_split (denoteArgs' bi fuel es) env
  rw [_root_.Hax.InlineLocalClosures.tuple_run, h1] at hrun
  cases m with
  | none => cases hrun
  | some vals =>
      cases hrun
      obtain ⟨W, hW, hrel1, rfl⟩ := argsOut_sound bi fuel es σ hoa env V vals env' hrel h1 tf
      have ht := tupleOut_sound bi tf tgt oa.as oa.vs W
      generalize tupleOut tgt oa.as oa.vs = T at ht ⊢
      obtain ⟨Δ, p, rv⟩ := T
      obtain ⟨W2, hW2, henc⟩ := ht
      refine ⟨W2, ?_, hrel1.mapV _ fun t u =>
        @NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) tf _ _ _ p u _ _ hW2,
        henc.symm⟩
      show PDen bi tf (oa.pre.append p) V = _
      rw [PDen_append, hW, Option.bind_some]
      exact hW2

/-! ## 9. The carried names of a loop -/

/-- The names `xs` read in `env` the encodings of the values `acc` at the types `cs`. -/
def CarriedRel (env : Env) :
    (xs : List String) → (cs : List NfTy) → Valuation (d := nfDialect) cs → Prop
  | x :: xs, c :: cs, .cons a acc => env x = some (enc c a) ∧ CarriedRel env xs cs acc
  | _, _, _ => True

/-- The names of `σ` other than `i` and the names `xs` read in `env` the encodings of
    the values of their variables in `V`. -/
def FrameRel {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (xs : List String) (env : Env)
    (V : Valuation Γ) : Prop :=
  ∀ x, x ∉ xs → x ≠ i → ∀ t (v : Var Γ t), σ.lookup x = some ⟨t, v⟩ →
    env x = some (enc t (v.lookup V))

/-- The environment of names with the names `xs` bound to `vs` in front of `σ` is related
    to `env` when the names `xs` read the values of `vs` and every other name of `σ` reads
    the value of its variable. -/
theorem EnvRel.bindAll {Δ : Ctxt nfDialect} {env : Env} {W : Valuation Δ} :
    ∀ (xs : List String) (cs : List NfTy) (vs : HVector (fun t => Var Δ t) cs)
      (σ : NfEnv Δ), xs.length = cs.length → CarriedRel env xs cs (Expr.lookupArgs vs W) →
      ∀ y, (y ∉ xs → ∀ t (v : Var Δ t), σ.lookup y = some ⟨t, v⟩ →
        env y = some (enc t (v.lookup W))) →
      ∀ t (v : Var Δ t), (NfEnv.bindAll xs cs vs σ).lookup y = some ⟨t, v⟩ →
        env y = some (enc t (v.lookup W))
  | x :: xs, c :: cs, .cons u vs, σ, hlen, hc, y, hy, t, v, hl => by
      rw [show NfEnv.bindAll (x :: xs) (c :: cs) (.cons u vs) σ =
        (x, ⟨c, u⟩) :: NfEnv.bindAll xs cs vs σ from rfl, NfEnv.lookup_cons] at hl
      by_cases hxy : x = y
      · subst hxy
        simp only [if_true, Option.some.injEq, Sigma.mk.injEq] at hl
        obtain ⟨rfl, hv⟩ := hl
        rw [← eq_of_heq hv]
        exact hc.1
      · rw [if_neg hxy] at hl
        exact EnvRel.bindAll xs cs vs σ (by simpa using hlen) hc.2 y
          (fun hn => hy (by simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hxy, hn⟩)) t v hl
  | [], _, _, σ, _, _, y, hy, t, v, hl => by
      simp only [NfEnv.bindAll] at hl
      exact hy List.not_mem_nil t v hl
  | _ :: _, [], .nil, _, hlen, _, _, _, _, _, _ => by simp at hlen

/-- The first variables of `cs ++ Γ` read the values in front of the valuation. -/
theorem lookupArgs_headVars {Γ : Ctxt nfDialect} (X : Valuation Γ) :
    (cs : List NfTy) → (acc : Valuation (d := nfDialect) cs) →
    Expr.lookupArgs (headVars (Γ := Γ) cs) (hvAppend acc X) = acc
  | [], .nil => rfl
  | c :: cs, .cons a acc => by
      show HVector.cons a (Expr.lookupArgs (HVector.renameVars (fun v => v.there)
        (headVars cs)) (HVector.cons a (hvAppend acc X))) = _
      have : ∀ {ts : List NfTy} (hv : HVector (fun t => Var (d := nfDialect) (cs ++ Γ) t) ts),
          Expr.lookupArgs (HVector.renameVars (fun v => Var.there (s := c) v) hv)
            (HVector.cons a (hvAppend acc X)) = Expr.lookupArgs hv (hvAppend acc X) := by
        intro ts hv
        induction hv with
        | nil => rfl
        | cons v hv ih =>
            show HVector.cons _ _ = HVector.cons _ _
            rw [ih]; rfl
      rw [this, lookupArgs_headVars X cs acc]

/-- The current variable of a name in an environment of names without the name `i`. -/
theorem NfEnv.lookup_filter_ne {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i x : String) :
    NfEnv.lookup (σ.filter fun p => p.1 != i) x = if x = i then none else σ.lookup x := by
  induction σ with
  | nil => split <;> rfl
  | cons q σ ih =>
      obtain ⟨y, p⟩ := q
      by_cases hyi : y = i
      · subst hyi
        rw [List.filter_cons_of_neg (by simp), ih, NfEnv.lookup_cons]
        by_cases hx : x = y
        · subst hx; simp
        · simp [hx, Ne.symm hx]
      · rw [List.filter_cons_of_pos (by simpa using hyi), NfEnv.lookup_cons, ih,
          NfEnv.lookup_cons]
        by_cases hx : x = i
        · subst hx; simp [hyi]
        · simp [hx]

/-- The values of the current variables of the names `xs` read in a related environment
    are carried. -/
theorem CarriedRel.of_varsAt {Δ : Ctxt nfDialect} {σ : NfEnv Δ} {env : Env}
    {W : Valuation Δ} (hrel : EnvRel σ env W) :
    ∀ (xs : List String) (cs : List NfTy) {rets : HVector (fun t => Var Δ t) cs},
      varsAt σ xs cs = some rets → CarriedRel env xs cs (Expr.lookupArgs rets W)
  | [], [], _, _ => trivial
  | x :: xs, c :: cs, rets, h => by
      simp only [varsAt, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hx, h⟩ := h
      split at h
      · rename_i htc
        subst htc
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨rs, hrs, rfl⟩ := h
        exact ⟨hrel x t v hx, CarriedRel.of_varsAt hrel xs cs hrs⟩
      · cases h
  | [], _ :: _, _, h => by simp [varsAt] at h
  | _ :: _, [], _, h => by simp [varsAt] at h

/-- The types of a list of entries have its length. -/
theorem entriesVars_length {Γ : Ctxt nfDialect} :
    (L : List (String × (Σ t : NfTy, Var Γ t))) → (entriesVars L).1.length = L.length
  | [] => rfl
  | _ :: L => congrArg (· + 1) (entriesVars_length L)

/-- Entries that are current in a related environment of names carry their values. -/
theorem CarriedRel.of_entries {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {env : Env}
    {V : Valuation Γ} (hrel : EnvRel σ env V) :
    (L : List (String × (Σ t : NfTy, Var Γ t))) → (∀ p ∈ L, σ.lookup p.1 = some p.2) →
    CarriedRel env (L.map (·.1)) (entriesVars L).1 (Expr.lookupArgs (entriesVars L).2 V)
  | [], _ => trivial
  | (x, ⟨t, v⟩) :: L, h =>
      ⟨hrel x t v (h _ List.mem_cons_self),
        CarriedRel.of_entries hrel L fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

/-- Every carried entry is current. -/
theorem carried_lookup {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (b : ImpExpr) :
    ∀ p ∈ carried σ i b, σ.lookup p.1 = some p.2 := by
  intro p hp
  simp only [carried, List.mem_filterMap, Option.map_eq_some_iff] at hp
  obtain ⟨x, -, q, hq, rfl⟩ := hp
  exact hq

/-- A current name other than `i` that is not carried is not bound by the body. -/
theorem frameOk_of_not_carried {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (b : ImpExpr)
    {x : String} {q : Σ t : NfTy, Var Γ t} (hq : σ.lookup x = some q) (hxi : x ≠ i)
    (hx : x ∉ (carried σ i b).map (·.1)) :
    frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b = true := by
  by_contra hf
  apply hx
  have hmem : x ∈ σ.map (·.1) := by
    simp only [NfEnv.lookup, Option.map_eq_some_iff, List.find?_eq_some_iff_append] at hq
    obtain ⟨p, ⟨hp, as, bs, rfl, -⟩, -⟩ := hq
    simp only [beq_iff_eq] at hp
    simp [hp]
  simp only [carried, List.map_filterMap, List.mem_filterMap, List.mem_filter,
    List.mem_eraseDups, Option.map_map]
  refine ⟨x, ⟨hmem, ?_⟩, by simp [hq]⟩
  rw [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true']
  exact ⟨hxi, Bool.eq_false_iff.mpr hf⟩

/-- The loop counter is not carried. -/
theorem not_mem_carried {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (i : String) (b : ImpExpr) :
    i ∉ (carried σ i b).map (·.1) := by
  simp only [carried, List.map_filterMap, List.mem_filterMap, List.mem_filter, Option.map_map,
    not_exists, not_and]
  intro x hx
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
  cases hl : σ.lookup x <;> simp
  exact fun h => hx.2.1 h

/-- The environment of names of a loop body or of the continuation of a loop: the carried
    names bound to `hv`, in front of the other names of `σ` other than `i`, moved by `g`. -/
theorem EnvRel.loopEnv {Γ₃ Δ : Ctxt nfDialect} (σ : NfEnv Γ₃) (i : String)
    (xs : List String) (cs : List NfTy) (hlen : xs.length = cs.length)
    (hv : HVector (fun t => Var Δ t) cs) (g : ∀ {t : NfTy}, Var Γ₃ t → Var Δ t) {env : Env}
    {V₃ : Valuation Γ₃} {W : Valuation Δ} (hc : CarriedRel env xs cs (Expr.lookupArgs hv W))
    (hf : FrameRel σ i xs env V₃) (hg : ∀ (t : NfTy) (v : Var Γ₃ t), (g v).lookup W = v.lookup V₃) :
    EnvRel (NfEnv.bindAll xs cs hv (NfEnv.mapV g (σ.filter fun p => p.1 != i))) env W := by
  intro y t v hl
  refine EnvRel.bindAll xs cs hv _ hlen hc y ?_ t v hl
  intro hy t' v' hl'
  rw [NfEnv.lookup_mapV, Option.map_eq_some_iff] at hl'
  obtain ⟨⟨t0, v0⟩, h0, heq⟩ := hl'
  simp only [Sigma.mk.injEq] at heq
  obtain ⟨rfl, hv'⟩ := heq
  rw [NfEnv.lookup_filter_ne] at h0
  split at h0
  · cases h0
  · rename_i hyi
    rw [hf y hy hyi t0 v0 h0, ← eq_of_heq hv', hg]

/-! ## 10. The loop -/

/-- The denotation of a program over `nfDialect` with the leaves of `tableOf bi`. -/
abbrev PDenP (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) : Option (Valuation (d := nfDialect) ts) :=
  @NFProg.denote nfDialect _ _ _ _ (nfDenote (tableOf bi)) fuel Γ ts p V

/-- A composed prefix denotes the valuation the second prefix reaches from the hole of the
    first. -/
theorem PDen_append_some (bi : Builtins) (fuel : Nat) {Γ Δ Θ : Ctxt nfDialect}
    {p : NFPre nfDialect Γ Δ} {q : NFPre nfDialect Δ Θ} {V : Valuation Γ} {W : Valuation Δ}
    {W' : Valuation Θ} (hp : PDen bi fuel p V = some W) (hq : PDen bi fuel q W = some W') :
    PDen bi fuel (p.append q) V = some W' := by
  rw [PDen_append, hp, Option.bind_some, hq]

/-- A prefix filled with a return denotes the returned variables at its hole. -/
theorem PDenP_plug_ret (bi : Builtins) (fuel : Nat) {Γ Δ : Ctxt nfDialect} {cs : List NfTy}
    (p : NFPre nfDialect Γ Δ) (rets : HVector (fun t => Var Δ t) cs) (V : Valuation Γ)
    {W : Valuation Δ} (h : PDen bi fuel p V = some W) :
    PDenP bi fuel (p.plug (.ret rets)) V = some (Expr.lookupArgs rets W) := by
  unfold PDenP
  rw [@NFPre.denote_plug nfDialect _ _ _ _ (nfDenote (tableOf bi)) fuel _ _ _ p (.ret rets) V]
  unfold PDen at h
  rw [h]
  rfl

/-- A counted loop whose trip count reads `n` and whose body folds the carried tuple over the
    trip indices `0, …, n - 1` to `acc` denotes the valuation its continuation reaches from
    `acc`. -/
theorem PDen_forLoop_some (bi : Builtins) (fuel : Nat) {Γ Δ : Ctxt nfDialect}
    {cs : List NfTy} {count : Var Γ (NfTy.word 64)} {inits : HVector (fun t => Var Γ t) cs}
    {body : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ) cs} {p : NFPre nfDialect (cs ++ Γ) Δ}
    {V : Valuation Γ} {acc : Valuation (d := nfDialect) cs} {W : Valuation Δ} (n : Nat)
    (hn : (count.lookup V).toNat = n)
    (hfold : (List.range' 0 n).foldlM (fun a j => PDenP bi fuel body
      (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
      (Expr.lookupArgs inits V) = some acc)
    (hp : PDen bi fuel p (hvAppend acc V) = some W) :
    PDen bi fuel (.forLoop count inits body p) V = some W := by
  show ((List.range (count.lookup V).toNat).foldlM (fun a j => PDenP bi fuel body
      (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
      (Expr.lookupArgs inits V)).bind (fun a => PDen bi fuel p (hvAppend a V)) = some W
  rw [hn, List.range_eq_range', hfold, Option.bind_some, hp]

/-- A step of `denoteForLoop'` whose body runs to a value that is not a control-flow value
    continues with the next counter. -/
theorem forLoop_succ_run_val (bi : Builtins) (n : Nat) (i : String) {lo hi : Int}
    (body : ImpExpr) {env e2 : Env} {w : Value} (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) = (.val w, e2))
    (hw : ∀ b u, w ≠ .controlFlow b u) :
    (_root_.Hax.denoteForLoop' bi (n + 1) i lo hi body).run env =
      (_root_.Hax.denoteForLoop' bi n i (lo + 1) hi body).run e2 := by
  rw [forLoop_succ_run bi n i lo hi body env h, hb]
  cases w with
  | controlFlow b u => exact absurd rfl (hw b u)
  | _ => rfl

/-- **The loop.** Let every run of the body from an environment satisfying `Inv`, extended
    with the counter `lo + k`, to a value be matched by the target body at the trip index
    `k`, to a valuation of the carried tuple satisfying `Inv` with the final environment.
    Then a run of `denoteForLoop'` from the counter `lo + k` to a value, with `m` trips left
    and `k + m < 2 ^ 64`, is matched by the fold of the target body over the trip indices
    `k, …, k + m - 1`. -/
theorem loop_sound (bi : Builtins) (i : String)
    (body : ImpExpr) (lo h : Int) {Γ₃ : Ctxt nfDialect} (V₃ : Valuation Γ₃) {cs : List NfTy}
    (bodyP : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ₃) cs) (tf : Nat)
    (Inv : Env → Valuation (d := nfDialect) cs → Prop)
    (HS : ∀ (k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (rb : Outcome)
      (e₂ : Env), k < 2 ^ 64 → Inv env acc →
      (denote' bi fuel body).run (env.extend i (.int (lo + k))) = (rb, e₂) →
      (∃ w, rb = .val w) → ∃ w acc', rb = .val w ∧ (∀ b u, w ≠ .controlFlow b u) ∧
        PDenP bi tf bodyP (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) = some acc' ∧
        Inv e₂ acc') :
    ∀ (m k fuel : Nat) (env : Env) (acc : Valuation (d := nfDialect) cs) (r : Value) (e : Env),
      (h - (lo + k)).toNat = m → k + m < 2 ^ 64 → Inv env acc →
      (_root_.Hax.denoteForLoop' bi fuel i (lo + k) h body).run env = (.val r, e) →
      r = .unit ∧ ∃ acc', (List.range' k m).foldlM
        (fun a j => PDenP bi tf bodyP (hvAppend a (.cons (BitVec.ofNat 64 j) V₃))) acc =
          some acc' ∧ Inv e acc' := by
  intro m
  induction m with
  | zero =>
      intro k fuel env acc r e hm _ hinv hrun
      rw [forLoop_ge_run bi fuel i _ h body env (by omega)] at hrun
      cases hrun
      exact ⟨rfl, acc, rfl, hinv⟩
  | succ m ih =>
      intro k fuel env acc r e hm hk hinv hrun
      have hlt : lo + k < h := by omega
      cases fuel with
      | zero =>
          rw [forLoop_zero_run bi i _ h body env hlt] at hrun
          cases hrun
      | succ f =>
          obtain ⟨rb, e₂, hb⟩ := run_val_split (denote' bi (f + 1) body)
            (env.extend i (.int (lo + k)))
          cases rb with
          | val w =>
              obtain ⟨w, acc', hw, hcf, hacc', hinv'⟩ := HS k (f + 1) env acc _ e₂
                (by omega) hinv hb ⟨w, rfl⟩
              cases hw
              rw [forLoop_succ_run_val bi f i body hlt hb hcf] at hrun
              have hk1 : lo + k + 1 = lo + ((k + 1 : Nat) : Int) := by push_cast; ring
              rw [hk1] at hrun
              obtain ⟨hr, acc'', hfold, hinv''⟩ :=
                ih (k + 1) f e₂ acc' r e (by omega) (by omega) hinv' hrun
              refine ⟨hr, acc'', ?_, hinv''⟩
              rw [List.range'_succ, List.foldlM_cons]
              show (PDenP bi tf bodyP (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))).bind _ = _
              rw [hacc', Option.bind_some]
              exact hfold
          | _ =>
              rw [forLoop_succ_run bi f i _ h body env hlt, hb] at hrun
              cases hrun

/-- A run to a value of a `forFold` with a literal lower bound, whose upper bound runs to
    an encoded value, is a run of the loop on the bound `NfTy.toInt?` reads. -/
theorem forFold_enc_run (bi : Builtins) (fuel : Nat) (i : String) (lo : Int)
    (hi body : ImpExpr) {env e1 env' : Env} {r : Value} {t : NfTy} {x : t.denote}
    (hh : (denote' bi fuel hi).run env = (.val (enc t x), e1))
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) hi body)).run env = (.val r, env')) :
    ∃ h, NfTy.toInt? t x = some h ∧
      (_root_.Hax.denoteForLoop' bi fuel i lo h body).run e1 = (.val r, env') := by
  simp only [denote', StateT.run, bind, StateT.bind, pure, StateT.pure, Value.ofLit] at hh hrun
  rw [hh] at hrun
  cases t <;> simp only [enc] at hrun
  all_goals first
    | exact ⟨_, rfl, hrun⟩
    | cases hrun

/-- **The counted loop of the front is sound.** Let the prefix `pre₀` denote `V₃`, related
    by `σ₃` to `env`, with `lo` in `loV` and the trip count `(h - lo).toNat` in `tripV`;
    let the names `xs` carry the values of `inits`, every name of `σ₃` other than `i` and
    the names `xs` be one the body does not bind, and `rec` be sound for the body. A run of
    `denoteForLoop'` from `lo` to `h`, with fewer than `2 ^ 64` trips, is then matched by the
    output of `loopOut`. -/
theorem loopOut_sound (bi : Builtins) (fuel : Nat) (body : ImpExpr) (tgt : Option String)
    {Γ Γ₃ : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64)) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ)) {o : Out Γ}
    (h₀ : loopOut tgt pre₀ σ₃ loV tripV i xs cs inits rec = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ}, rec σ' = some o' →
      ∀ fuel', Sound bi fuel' body σ' o')
    (hlen : xs.length = cs.length)
    (hfr : ∀ x, x ∉ xs → x ≠ i → ∀ q, σ₃.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) body = true)
    (env : Env) (V : Valuation Γ) (V₃ : Valuation Γ₃)
    (tf : Nat) (hpre : PDen bi tf pre₀ V = some V₃) (hrel : EnvRel σ₃ env V₃)
    (hcar : CarriedRel env xs cs (Expr.lookupArgs inits V₃)) (lo h : Int)
    (hlo : loV.lookup V₃ = lo) (htrip : tripV.lookup V₃ = BitVec.ofNat 64 (h - lo).toNat)
    (hM : (h - lo).toNat < 2 ^ 64) (r : Value) (env' : Env)
    (hrun : (_root_.Hax.denoteForLoop' bi fuel i lo h body).run env = (.val r, env')) :
    ∃ W, PDen bi tf o.pre V = some W ∧ EnvRel o.σ env' W ∧ r = enc o.t (o.res.lookup W) := by
  simp only [loopOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₀
  obtain ⟨ob, hob, rets, hrets, rfl⟩ := h₀
  -- the invariant of the loop: the carried names and the frame
  let Inv : Env → Valuation (d := nfDialect) cs → Prop := fun e acc =>
    CarriedRel e xs cs acc ∧ FrameRel σ₃ i xs e V₃
  have HS : ∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs) (rb : Outcome)
      (e₂ : Env), k < 2 ^ 64 → Inv e acc →
      (denote' bi f body).run (e.extend i (.int (lo + k))) = (rb, e₂) →
      (∃ w, rb = .val w) → ∃ w acc', rb = .val w ∧ (∀ b u, w ≠ .controlFlow b u) ∧
        PDenP bi tf ((NFPre.append (bind1N (some i) (loopEnv σ₃ i xs cs (headVars cs)
            fun v => Var.shiftApp (d := nfDialect) cs v.there) .ctr
            (.cons (Var.shiftApp cs (Var.there loV))
              (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))).pre
            ob.pre).plug (.ret rets))
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) = some acc' ∧ Inv e₂ acc' := by
    intro k f e acc rb e₂ hk hinv hb hval
    obtain ⟨w, rfl⟩ := hval
    have hB : EnvRel (loopEnv σ₃ i xs cs (headVars cs)
        fun v => Var.shiftApp (d := nfDialect) cs v.there) e
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) :=
      EnvRel.loopEnv σ₃ i xs cs hlen (headVars cs) _
        (W := hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
        (by rw [lookupArgs_headVars]; exact hinv.1) hinv.2
        (by intro t v; rw [Var.lookup_shiftApp]; rfl)
    have hctr : nfDenoteOp (tableOf bi) .ctr
        (Expr.lookupArgs (.cons (Var.shiftApp cs (Var.there loV))
          (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))) =
          some (lo + (k : Int)) := by
      have hargs : Expr.lookupArgs (.cons (Var.shiftApp cs (Var.there loV))
          (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
          HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
            (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) .nil) := by
        show HVector.cons ((Var.shiftApp cs (Var.there loV)).lookup _)
          (HVector.cons ((Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))).lookup _)
            .nil) = _
        rw [Var.lookup_shiftApp, Var.lookup_shiftApp, ← hlo]
        rfl
      rw [hargs]
      show some (lo + ((BitVec.ofNat 64 k).toNat : Int)) = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
    have hpC : ∀ tf', PDen bi tf' (bind1N (some i) (loopEnv σ₃ i xs cs (headVars cs)
        fun v => Var.shiftApp (d := nfDialect) cs v.there) .ctr
        (.cons (Var.shiftApp cs (Var.there loV))
          (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))).pre
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
        some (Ctxt.Valuation.extend (t := NfTy.int)
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
          (lo + (k : Int))) := by
      intro tf'
      exact (PDen_bind1N bi tf' (some i) _ .ctr _ _).trans
        ((congrArg (Option.map _) hctr).trans rfl)
    have hC := (hB.mapV (fun v => Var.there (s := NfTy.int) v) fun _ _ => rfl).cons i NfTy.int
      (@Var.here nfDialect (cs ++ NfTy.word 64 :: Γ₃) NfTy.int)
      (V := Ctxt.Valuation.extend (t := NfTy.int)
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) (lo + (k : Int)))
    obtain ⟨W', hW', hrel', rfl⟩ := HB _ hob f _ _ w e₂ hC hb tf
    refine ⟨_, Expr.lookupArgs rets W', rfl, enc_ne_controlFlow _ _, ?_, ?_, ?_⟩
    · exact PDenP_plug_ret bi tf _ rets _ (PDen_append_some bi tf (hpC tf) hW')
    · exact CarriedRel.of_varsAt hrel' xs cs hrets
    · intro x hx hxi t v hl
      rw [denote'_keeps bi body (hfr x hx hxi _ hl) f _ hb (by rintro ⟨_, h⟩; cases h),
        Env.extend_other _ _ _ _ hxi]
      exact hinv.2 x hx hxi t v hl
  have hrun0 : (_root_.Hax.denoteForLoop' bi fuel i (lo + ((0 : Nat) : Int)) h body).run env =
      (.val r, env') := by simpa using hrun
  obtain ⟨rfl, accF, hfold, hinvF⟩ := loop_sound bi i body lo h V₃ _ tf Inv HS
    ((h - lo).toNat) 0 fuel env (Expr.lookupArgs inits V₃) r env' (by simp) (by simpa using hM)
    ⟨hcar, fun x _ _ t v hl => hrel x t v hl⟩ hrun0
  refine ⟨HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.unit) () (hvAppend accF V₃), ?_, ?_, rfl⟩
  · refine PDen_append_some bi tf hpre
      (PDen_forLoop_some bi tf ((h - lo).toNat) ?_ hfold ?_)
    · rw [htrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM]
    · exact (PDen_bind1N bi tf tgt _ .constUnit .nil _).trans rfl
  · exact (EnvRel.loopEnv σ₃ i xs cs hlen (headVars cs) (fun v => Var.shiftApp cs v)
      (W := hvAppend accF V₃) (by rw [lookupArgs_headVars]; exact hinvF.1) hinvF.2
      (fun t v => Var.lookup_shiftApp cs accF v V₃)).mapV (fun v => Var.there v)
      (W := HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.unit) () (hvAppend accF V₃))
      fun _ _ => rfl

/-- A run to a value of a `forFold` with a literal lower bound runs its upper bound to a
    value. -/
theorem forFold_hi_val (bi : Builtins) (fuel : Nat) (i : String) (lo : Int)
    (hi body : ImpExpr) {env env' : Env} {r : Value}
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) hi body)).run env = (.val r, env')) :
    ∃ hv e1, (denote' bi fuel hi).run env = (.val hv, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure, StateT.pure, Value.ofLit] at hrun
  rcases hh : denote' bi fuel hi env with ⟨o1, e1⟩
  rw [hh] at hrun
  cases o1 with
  | val v => exact ⟨v, e1, hh⟩
  | _ => cases hrun

/-- Under the bounds of `boundOk`, the trip count is below `2 ^ 64`. -/
theorem trip_lt_of_boundOk {lo : Int} {t : NfTy} {x : t.denote} {h : Int}
    (hb : boundOk lo t = true) (hx : NfTy.toInt? t x = some h) : (h - lo).toNat < 2 ^ 64 := by
  cases t with
  | uint W =>
      simp only [boundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [NfTy.toInt?, Option.some.injEq] at hx
      subst hx
      have h1 : x.toNat < 2 ^ W.bits := x.isLt
      have h2 : 2 ^ W.bits ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hb.2
      omega
  | word w =>
      simp only [boundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
      simp only [NfTy.toInt?, Option.some.injEq] at hx
      subst hx
      have h1 : x.toNat < 2 ^ w := x.isLt
      have h2 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hb.2
      omega
  | _ => simp [boundOk] at hb

/-- The integer `NfTy.toInt?` reads off a value encoding as the integer `n` is `n`. -/
theorem toInt_of_enc_int {t : NfTy} {x : t.denote} {n h : Int} (he : enc t x = .int n)
    (hx : NfTy.toInt? t x = some h) : h = n := by
  cases t <;> simp only [enc, reduceCtorEq] at he <;> simp only [NfTy.toInt?] at hx
  · obtain rfl := Option.some.inj hx
    exact Value.int.inj he
  · obtain rfl := Option.some.inj hx
    exact Value.int.inj he

/-- Under the bounds of `boundOk` or of `litBoundOk`, the trip count is below `2 ^ 64`. -/
theorem trip_lt_of_bound {lo : Int} {t : NfTy} {x : t.denote} {h : Int} {hi : ImpExpr}
    (hb : (boundOk lo t || litBoundOk lo hi) = true) (hx : NfTy.toInt? t x = some h)
    (hlit : ∀ n, hi = .lit (.int n) → enc t x = .int n) : (h - lo).toNat < 2 ^ 64 := by
  rcases Bool.or_eq_true_iff.mp hb with hb | hb
  · exact trip_lt_of_boundOk hb hx
  · match hi, hb with
    | .lit (.int n), hb =>
        simp only [litBoundOk, Bool.and_eq_true, decide_eq_true_eq] at hb
        obtain rfl := toInt_of_enc_int (hlit n rfl) hx
        omega

/-- **A counted loop is sound**, when the front is sound for its body. -/
theorem forFold_sound (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (fuel : Nat) (tgt : Option String) (i : String) (lo : Int) (hi body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.forFold i (.lit (.int lo)) hi body) = some o)
    (HB : ∀ {Γ' : Ctxt nfDialect} (σ' : NfEnv Γ') {o' : Out Γ'},
      impToNF sigOf none σ' body = some o' → ∀ fuel', Sound bi fuel' body σ' o') :
    Sound bi fuel (.forFold i (.lit (.int lo)) hi body) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨oHi, hHi, hL⟩ := h
  split at hL
  case isFalse => cases hL
  rename_i hbd
  intro env V r env' hrel hrun tf
  obtain ⟨hv, e1, hh⟩ := forFold_hi_val bi fuel i lo hi body hrun
  have he1 : e1 = env := by
    have := atomOut_env bi fuel _ hi hHi env
    rw [hh] at this; exact this
  subst he1
  have hrelLo : EnvRel (bind1 σ (.ilit .int lo) .nil).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) :=
    hrel.mapV (fun v => Var.there v) fun _ _ => rfl
  have hLo : ∀ tf', PDen bi tf' (bind1 σ (.ilit .int lo) .nil).pre V =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo V) := fun tf' =>
    (PDen_bind1 bi tf' σ (.ilit .int lo) .nil V).trans rfl
  have hHiS := atomOut_sound bi fuel _ hi hHi e1 _ hv e1 hrelLo hh
  obtain ⟨W2, hW2, hrel2, rfl⟩ := hHiS tf
  obtain ⟨hInt, htoInt, hloop⟩ := forFold_enc_run bi fuel i lo hi body hh hrun
  have hloW : (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2 = lo :=
    (@NFPre.lookup_wk nfDialect _ _ _ _ (nfDenote (tableOf bi)) tf _ _ _ oHi.pre _ _ _ hW2).trans
      rfl
  have hargsT : Expr.lookupArgs (HVector.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res)
      (HVector.cons oHi.res .nil)) W2 =
      HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
        (HVector.cons (t := oHi.t) (oHi.res.lookup W2) .nil) := by
    show HVector.cons ((oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res).lookup W2)
      (HVector.cons (oHi.res.lookup W2) .nil) = _
    rw [hloW]
    rfl
  have hTrip : PDen bi tf (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).pre W2 =
      some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) := by
    refine (PDen_bind1 bi tf _ (.trip oHi.t) _ W2).trans ?_
    refine (congrArg (fun a => Option.map _ (nfDenoteOp (tableOf bi) (.trip oHi.t) a))
      hargsT).trans ?_
    show Option.map _ ((NfTy.toInt? oHi.t (oHi.res.lookup W2)).map
      fun hi => BitVec.ofNat 64 (hi - lo).toNat) = _
    rw [htoInt]
    rfl
  have hrelT : EnvRel (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (bind1 σ (.ilit .int lo) .nil).res) (.cons oHi.res .nil))).σ e1
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - lo).toNat) W2) :=
    hrel2.mapV (fun v => Var.there v) fun _ _ => rfl
  exact loopOut_sound bi fuel body tgt _ _ _ _ i _ _ _ _ hL
    (fun σ' _ h' fuel' => HB σ' h' fuel')
    (by rw [List.length_map, entriesVars_length])
    (fun x hx hxi _ hl => frameOk_of_not_carried _ i body hl hxi hx)
    e1 V _ tf (PDen_append_some bi tf (PDen_append_some bi tf (hLo tf) hW2) hTrip) hrelT
    (CarriedRel.of_entries hrelT _ (carried_lookup _ i body)) lo hInt hloW rfl
    (trip_lt_of_bound hbd htoInt fun n hn => by
      subst hn
      rw [lit_run] at hh
      have h1 := (Prod.mk.inj hh).1
      injection h1 with h2
      exact h2.symm) r env' hloop

/-! ## 11. The front simulates `denote'` -/

/-- **The front simulates `denote'`.** Under the typing hypothesis `TypedCalls bi sigOf`,
    for every expression `e` the front translates from `σ`, and every source fuel, a run of
    `denote' bi fuel e` from an environment related to a valuation `V` to a value is
    matched, at every target fuel, by the prefix: it denotes a valuation of its hole related
    to the final environment, and the variable of the value encodes the value. -/
theorem impToNF_sound (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf tgt σ e = some o → ∀ fuel, Sound bi fuel e σ o := by
  induction e using ImpExpr.ind
  case lit l => intro tgt Γ σ o h fuel; exact litOut_sound bi fuel tgt σ l h
  case var x => intro tgt Γ σ o h fuel; exact atomOut_sound bi fuel σ _ h
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    exact letBind_sound bi fuel x (ihv _ σ hov fuel) (ihb _ _ hob fuel)
  case seq a b iha ihb =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    exact seq_sound bi fuel (iha _ σ hoa fuel) (ihb _ _ hob fuel)
  case assign x r ih =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨o', ho', rfl⟩ := h
    exact assign_sound bi fuel x tgt (ih _ σ ho' fuel)
  case app f args _ =>
    intro tgt Γ σ o h fuel; exact app_sound bi sigOf hT fuel tgt f args σ h
  case tuple es _ => intro tgt Γ σ o h fuel; exact tuple_sound bi sigOf fuel tgt es σ h
  case unitVal =>
    intro tgt Γ σ o h fuel
    simp only [impToNF, Option.some.injEq] at h
    subst h
    exact sound_bind1N bi fuel _ tgt σ _ _ fun env V v env' _ hr => by
      rw [unitVal_run] at hr
      cases hr
      exact ⟨rfl, (), rfl, rfl⟩
  case typeAscription e s ih =>
    intro tgt Γ σ o h fuel env V v env' hrel hrun tf
    have hr : (denote' bi fuel (.typeAscription e s)).run env = (denote' bi fuel e).run env := by
      simp only [denote']
    rw [hr] at hrun
    exact ih _ σ h fuel env V v env' hrel hrun tf
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h fuel
    cases lo with
    | lit l =>
        cases l with
        | int n =>
            exact forFold_sound bi sigOf fuel tgt i n hi body σ h
              fun σ' _ h' fuel' => ihb none σ' h' fuel'
        | _ => simp [impToNF] at h
    | _ => simp [impToNF] at h
  all_goals intro tgt Γ σ o h; simp [impToNF] at h

/-! ## 12. The readback -/

/-- How the readback reads a variable of an `NFProg` program. -/
inductive RB where
  /-- The value is held in the source name `n`. -/
  | name (n : String)
  /-- The value is the literal `l`. -/
  | lit (l : ImpLit)
  /-- The value is the tuple of the atoms `as`. -/
  | tup (as : List ImpExpr)
  /-- The value is the trip count of a loop from the literal lower bound `lo` to the upper
      bound the atom `hi` reads. -/
  | trip (lo : Int) (hi : ImpExpr)
  /-- The value is the trip index of the enclosing loop. -/
  | idx
  /-- The value is not readable. -/
  | gone

/-- The atom reading a variable: its name or its literal. -/
def RB.atom? : RB → Option ImpExpr
  | .name n => some (.var n)
  | .lit l => some (.lit l)
  | _ => none

/-- The expression reading a variable as a result: its name, its literal or its tuple. -/
def RB.expr? : RB → Option ImpExpr
  | .name n => some (.var n)
  | .lit l => some (.lit l)
  | .tup as => some (.tuple as)
  | _ => none

/-- The source names a reading reads. -/
def RB.names : RB → List String
  | .name n => [n]
  | .tup as => as.filterMap fun | .var n => some n | _ => none
  | .trip _ (.var n) => [n]
  | _ => []

/-- A reading of every variable of `Γ`. -/
abbrev RBEnv (Γ : Ctxt nfDialect) : Type := ∀ {t : NfTy}, Var Γ t → RB

/-- The reading of `Γ` extended by the reading `r` of a new variable. -/
def RBEnv.cons {Γ : Ctxt nfDialect} {s : NfTy} (r : RB) (ρ : RBEnv Γ) : RBEnv (s :: Γ)
  | _, .here => r
  | _, .there v => ρ v

/-- The reading with every reading of a name of `ns` made unreadable. -/
def RBEnv.clobber {Γ : Ctxt nfDialect} (ns : List String) (ρ : RBEnv Γ) : RBEnv Γ :=
  fun v => if (ρ v).names.any (ns.contains ·) then .gone else ρ v

/-- The reading with every trip-index reading made unreadable. -/
def RBEnv.dropIdx {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) : RBEnv Γ :=
  fun v => match ρ v with
    | .idx => .gone
    | r => r

/-- The reading of `cs ++ Γ` with the variables of `cs` held in the names `ns`. -/
def RBEnv.appNames {Γ : Ctxt nfDialect} : (cs : List NfTy) → List String → RBEnv Γ →
    RBEnv (cs ++ Γ)
  | [], _, ρ => ρ
  | _ :: cs, n :: ns, ρ => RBEnv.cons (.name n) (RBEnv.appNames cs ns ρ)
  | _ :: cs, [], ρ => RBEnv.cons .gone (RBEnv.appNames cs [] ρ)

/-- The names the readings of the variables `vs` read. -/
def hvNames {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts → List String
  | [], .nil => []
  | _ :: _, .cons v vs => (ρ v).names ++ hvNames ρ vs

/-- The names the reading of `Γ` reads. -/
def RBEnv.allNames {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) : List String :=
  hvNames ρ (allVars (d := nfDialect) Γ)

/-- The atoms reading the variables `vs`. -/
def rbAtoms {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts → Option (List ImpExpr)
  | [], .nil => some []
  | _ :: _, .cons v vs => (ρ v).atom?.bind fun a => (rbAtoms ρ vs).map (a :: ·)

/-- The literal of the value `v` at the type `t` of an `ilit`. -/
def litOfIlit : NfTy → Int → Option ImpLit
  | .int, v => some (.int v)
  | .uint W, v => some (.uintLit W v.toNat)
  | .sint W, v => some (.sintLit W v)
  | _, _ => none

/-- The right-hand side reading back the operation `op` on the variables `args`. -/
def rbRhs {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Option ImpExpr
  | .call f _ _, args => (rbAtoms ρ args).map (.app f)
  | .ilit t v, _ => (litOfIlit t v).map .lit
  | .constBit b, _ => some (.lit (.bool b))
  | .constUnit, _ => some (.lit .unit)
  | .tnilV, _ => some (.tuple [])
  | .tconsV _ _, .cons a (.cons b .nil) =>
      match (ρ a).atom?, ρ b with
      | some x, .tup as => some (.tuple (x :: as))
      | _, _ => none
  | _, _ => none

/-- The readback of one binding: a `letBind` of a name (`emit`; `tmp` when the name is a
    fresh temporary), or a reading of the new variable without a binding (`inline`). -/
inductive RBBind where
  /-- Bind the name `n` to `rhs`. -/
  | emit (n : String) (rhs : ImpExpr) (tmp : Bool)
  /-- Read the new variable by `r`. -/
  | inline (r : RB)

/-- The name of the `c`-th fresh temporary. -/
def tmpName (c : Nat) : String := "%nf" ++ toString c

/-- The readback of the binding of the operation `op` on `args`. -/
def rbBind {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) (c : Nat) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Option RBBind
  | .named n op, args => (rbRhs ρ op args).map fun rhs => .emit n rhs false
  | .call f _ _, args => (rbAtoms ρ args).map fun xs => .emit (tmpName c) (.app f xs) true
  | .ilit t v, _ => (litOfIlit t v).map fun l => .inline (.lit l)
  | .constBit b, _ => some (.inline (.lit (.bool b)))
  | .constUnit, _ => some (.inline (.lit .unit))
  | .trip t, .cons lo (.cons hi .nil) =>
      match ρ lo with
      | .lit (.int lo') =>
          if boundOk lo' t then (ρ hi).atom?.map fun h => .inline (.trip lo' h) else none
      | _ => none
  | .tnilV, _ => some (.inline (.tup []))
  | .tconsV _ _, .cons a (.cons b .nil) =>
      match (ρ a).atom?, ρ b with
      | some x, .tup as => some (.inline (.tup (x :: as)))
      | _, _ => none
  | _, _ => none

/-- The atom is the variable `n`. -/
def isVarOf (n : String) : ImpExpr → Bool
  | .var m => m == n
  | _ => false

/-- The assignments writing the values of the atoms `as` back to the carried names `cn`,
    then `unitVal`; an assignment of a name to itself is left out. `none` when a later atom
    reads a name an earlier assignment writes. -/
def rbAssigns : List String → List ImpExpr → Option ImpExpr
  | [], [] => some .unitVal
  | n :: ns, a :: as =>
      if isVarOf n a then rbAssigns ns as
      else if as.any (isVarOf n) then none
      else (rbAssigns ns as).map (.seq (.assign n a))
  | _, _ => none

/-- The names of a list of variable atoms; `none` when an atom is a literal. -/
def namesOf : List ImpExpr → Option (List String)
  | [] => some []
  | .var n :: as => (namesOf as).map (n :: ·)
  | _ => none

/-- The name and the arguments of a named counter operation `named i ctr`. -/
def ctrOf? {Γ : Ctxt nfDialect} :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig →
      Option (String × Var Γ NfTy.int × Var Γ (NfTy.word 64))
  | .named i .ctr, args => some (i, args.head, args.tail.head)
  | _, _ => none

/-- The continuation of the readback at a return: from the reading of the context and the
    returned variables, the code ending the program and the next fresh temporary. -/
abbrev RK (ts : List NfTy) : Type :=
  ∀ {Δ : Ctxt nfDialect}, RBEnv Δ → HVector (fun t => Var Δ t) ts → Nat → Option (ImpExpr × Nat)

/-- **The readback** of an `NFProg` program from the reading `ρ` of its context, with the
    fresh temporaries from `c` and the continuation `rk` at its return: a named binding is a
    `letBind` of its name, an unnamed call a `letBind` of a fresh temporary, and a literal,
    a unit, a tuple and a trip count are read without a binding; a counted loop whose count
    reads as a trip count and whose body starts with a named `ctr` is a `forFold` on that
    name, its carried values held in the names of its initial atoms and written back by
    `assign` at the end of the body. A binding of a name makes every reading of the name
    unreadable, and a loop is read back only when, by `frameOk`, it binds no name the
    reading of the context still reads. -/
def rbProg : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → RBEnv Γ →
    Nat → RK ts → Option (ImpExpr × Nat)
  | _, _, .ret vs, ρ, c, rk => rk ρ vs c
  | _, _, .var e k, ρ, c, rk =>
      (rbBind ρ c e.op e.args).bind fun b =>
        match b with
        | .emit n rhs tmp =>
            (rbProg k (RBEnv.cons (.name n) (ρ.clobber [n])) (if tmp then c + 1 else c) rk).map
              fun r => (.letBind n rhs r.1, r.2)
        | .inline r => rbProg k (RBEnv.cons r ρ) c rk
  | _, _, .forLoop (cs := cs) count inits body k, ρ, c, rk =>
      match body with
      | .var e rest =>
        (ctrOf? e.op e.args).bind fun ⟨i, a, b⟩ =>
          match ρ count with
          | .trip lo hi =>
            (rbAtoms ρ inits).bind fun xs => (namesOf xs).bind fun cn =>
              if cn.Nodup then
                let ρΓ : RBEnv _ := RBEnv.clobber cn ρ
                let ρB : RBEnv (cs ++ NfTy.word 64 :: _) :=
                  RBEnv.appNames cs cn (RBEnv.cons .idx (RBEnv.dropIdx ρΓ))
                match ρB a, ρB b with
                | .lit (.int lo'), .idx =>
                    if lo' = lo then
                      (rbProg rest (RBEnv.cons (.name i) (ρB.clobber [i])) c
                          (fun ρ' vs c' => (rbAtoms ρ' vs).bind fun as =>
                            (rbAssigns cn as).map (·, c'))).bind fun bc =>
                        let loopIE := ImpExpr.forFold i (.lit (.int lo)) hi bc.1
                        if (RBEnv.allNames ρΓ).all fun n =>
                            frameOk (fun _ => true) (fun m => m != n) (fun _ => true) loopIE then
                          (rbProg k (RBEnv.appNames cs cn ρΓ) bc.2 rk).map fun r =>
                            (.seq loopIE r.1, r.2)
                        else none
                    else none
                | _, _ => none
              else none
          | _ => none
      | _ => none
  | _, _, .ifThenElse .., _, _, _ => none
  | _, _, .whileLoop .., _, _, _ => none

/-- **The readback** of a program with one result: `rbProg` with the result read as an
    expression. -/
def nfToImp {Γ : Ctxt nfDialect} {t : NfTy} (p : NFProg nfDialect Γ [t]) (ρ : RBEnv Γ) :
    Option ImpExpr :=
  (rbProg p ρ 0 fun ρ' vs c => match vs with
    | .cons v .nil => (ρ' v).expr?.map (·, c)).map (·.1)

/-! ## 13. The readback simulates the denotation -/

/-- The atom `a` reads the value `w` in `env`. -/
def AtomEval (env : Env) : ImpExpr → Value → Prop
  | .var n, w => env n = some w
  | .lit l, w => Value.ofLit l = w
  | _, _ => False

/-- The atoms `as` read the values `ws` in `env`. -/
def AtomsEval (env : Env) : List ImpExpr → List Value → Prop
  | [], [] => True
  | a :: as, w :: ws => AtomEval env a w ∧ AtomsEval env as ws
  | _, _ => False

/-- The reading `r` reads the value `w` in `env`. -/
def RBOk (env : Env) : RB → Value → Prop
  | .name n, w => env n = some w
  | .lit l, w => Value.ofLit l = w
  | .tup as, w => ∃ ws, AtomsEval env as ws ∧ w = .tuple ws
  | .trip lo hi, w => ∃ h : Int, (∃ hv, AtomEval env hi hv ∧
      (hv = .int h ∨ ∃ (W : IntWidth) (n : Nat), hv = .uint W n ∧ h = n)) ∧
      (h - lo).toNat < 2 ^ 64 ∧ w = .int ((h - lo).toNat : Int)
  | .idx, _ => True
  | .gone, _ => True

/-- Every variable of `Γ` reads, by `ρ`, in `env` the encoding of its value in `V`. -/
def RBRel {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) (env : Env) (V : Valuation Γ) : Prop :=
  ∀ (t : NfTy) (v : Var Γ t), RBOk env (ρ v) (enc t (v.lookup V))

/-- An atom reads the same value in two environments that agree at its name. -/
theorem AtomEval.congr {env env' : Env} {a : ImpExpr} {w : Value}
    (h : ∀ n, a = .var n → env' n = env n) (ha : AtomEval env a w) : AtomEval env' a w := by
  cases a with
  | var n => show env' n = some w; rw [h n rfl]; exact ha
  | lit l => exact ha
  | _ => exact ha.elim

/-- Atoms read the same values in two environments that agree at their names. -/
theorem AtomsEval.congr {env env' : Env} :
    ∀ {as : List ImpExpr} {ws : List Value}, (∀ n, ImpExpr.var n ∈ as → env' n = env n) →
      AtomsEval env as ws → AtomsEval env' as ws
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, ⟨ha, has⟩ =>
      ⟨AtomEval.congr (fun n hn => h n (hn ▸ List.mem_cons_self)) ha,
        AtomsEval.congr (fun n hn => h n (List.mem_cons_of_mem _ hn)) has⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- A reading reads the same value in two environments that agree at the names it reads. -/
theorem RBOk.congr {env env' : Env} {r : RB} {w : Value}
    (h : ∀ n ∈ r.names, env' n = env n) (hr : RBOk env r w) : RBOk env' r w := by
  cases r with
  | name n => show env' n = some w; rw [h n (by simp [RB.names])]; exact hr
  | lit l => exact hr
  | tup as =>
      obtain ⟨ws, hws, rfl⟩ := hr
      refine ⟨ws, AtomsEval.congr (fun n hn => h n ?_) hws, rfl⟩
      simp only [RB.names, List.mem_filterMap]
      exact ⟨_, hn, rfl⟩
  | trip lo hi =>
      obtain ⟨hh, ⟨hv, hhv, hrep⟩, hb, rfl⟩ := hr
      refine ⟨hh, ⟨hv, AtomEval.congr (fun n hn => h n ?_) hhv, hrep⟩, hb, rfl⟩
      subst hn
      simp [RB.names]
  | idx => trivial
  | gone => trivial

/-- The reading extended by the reading of a new variable is related to the valuation
    extended by its value. -/
theorem RBRel.cons {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (h : RBRel ρ env V) {s : NfTy} {r : RB} {x : s.denote} (hr : RBOk env r (enc s x)) :
    RBRel (RBEnv.cons (s := s) r ρ) env (V.extend x) := by
  intro t v
  cases v with
  | here => exact hr
  | there v => exact h t v

/-- Binding the name `n` keeps the relation of the reading with the readings of `n` made
    unreadable. -/
theorem RBRel.clobber_extend {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env}
    {V : Valuation Γ} (h : RBRel ρ env V) (n : String) (w : Value) :
    RBRel (RBEnv.clobber [n] ρ) (env.extend n w) V := by
  intro t v
  simp only [RBEnv.clobber]
  split
  · trivial
  · rename_i hn
    refine RBOk.congr (fun m hm => ?_) (h t v)
    have hmn : m ≠ n := by
      intro hmn; subst hmn
      exact hn (List.any_eq_true.mpr ⟨m, hm, by simp⟩)
    exact Env.extend_other _ _ _ _ hmn

/-- An atom runs to the value it reads, leaving the environment unchanged. -/
theorem AtomEval.run (bi : Builtins) (fuel : Nat) {env : Env} {a : ImpExpr} {w : Value}
    (h : AtomEval env a w) : (denote' bi fuel a).run env = (.val w, env) := by
  cases a with
  | var n =>
      rw [var_run]
      change env n = some w at h
      rw [h]
  | lit l =>
      rw [lit_run]
      change Value.ofLit l = w at h
      rw [h]
  | _ => exact h.elim

/-- The encodings of a vector of values contain no control-flow value. -/
theorem encAll_ne_controlFlow : ∀ (as : List NfTy) (xs : HVector NfTy.denote as),
    ∀ w ∈ encAll as xs, ∀ b u, w ≠ .controlFlow b u
  | [], .nil, _, h => by simp [encAll] at h
  | a :: as, .cons x xs, w, h => by
      simp only [encAll, List.mem_cons] at h
      rcases h with rfl | h
      · exact enc_ne_controlFlow a x
      · exact encAll_ne_controlFlow as xs w h

/-- Atoms run, left to right, to the values they read, leaving the environment unchanged,
    when no value is a control-flow value. -/
theorem AtomsEval.run (bi : Builtins) (fuel : Nat) {env : Env} :
    ∀ {as : List ImpExpr} {ws : List Value}, AtomsEval env as ws →
      (∀ w ∈ ws, ∀ b u, w ≠ .controlFlow b u) →
      (denoteArgs' bi fuel as).run env = (some ws, env)
  | [], [], _, _ => args_nil_run bi fuel env
  | a :: as, w :: ws, ⟨ha, has⟩, hcf => by
      rw [args_cons_run_val bi fuel as (AtomEval.run bi fuel ha)
        (hcf w List.mem_cons_self),
        AtomsEval.run bi fuel has fun w' hw' => hcf w' (List.mem_cons_of_mem _ hw')]
      rfl
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- The atom of a reading reads the value the reading reads. -/
theorem RB.atom?_eval {env : Env} {r : RB} {a : ImpExpr} {w : Value} (h : r.atom? = some a)
    (hr : RBOk env r w) : AtomEval env a w := by
  cases r with
  | name n => simp only [RB.atom?, Option.some.injEq] at h; subst h; exact hr
  | lit l => simp only [RB.atom?, Option.some.injEq] at h; subst h; exact hr
  | _ => simp [RB.atom?] at h

/-- The atoms of the readings of variables read the encodings of their values. -/
theorem rbAtoms_eval {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (hrel : RBRel ρ env V) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts) {xs : List ImpExpr},
      rbAtoms ρ vs = some xs → AtomsEval env xs (encAll ts (Expr.lookupArgs vs V))
  | [], .nil, xs, h => by
      simp only [rbAtoms, Option.some.injEq] at h; subst h; trivial
  | t :: ts, .cons v vs, xs, h => by
      change ((ρ v).atom?.bind fun a => (rbAtoms ρ vs).map (a :: ·)) = some xs at h
      rcases ha : (ρ v).atom? with _ | a
      · rw [ha] at h; cases h
      rcases has : rbAtoms ρ vs with _ | as
      · rw [ha, has] at h; cases h
      rw [ha, has] at h
      cases h
      exact ⟨RB.atom?_eval ha (hrel t v), rbAtoms_eval hrel vs has⟩

/-- The components of an encoded tuple contain no control-flow value. -/
theorem enc_tuple_ne_controlFlow : ∀ (t : NfTy) (y : t.denote) (ws : List Value),
    enc t y = .tuple ws → ∀ w ∈ ws, ∀ b u, w ≠ .controlFlow b u
  | .tnil, _, ws, h => by simp only [enc, Value.tuple.injEq] at h; subst h; simp
  | .tcons h₀ t, y, ws, h => by
      simp only [enc, Value.tuple.injEq] at h
      subst h
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact enc_ne_controlFlow h₀ y.1
      · cases he : enc t y.2 with
        | tuple vs =>
            rw [he] at hw
            exact enc_tuple_ne_controlFlow t y.2 vs he w hw
        | _ =>
            rw [he] at hw
            simp only [tailVals, List.mem_singleton] at hw
            subst hw
            rw [← he]
            exact enc_ne_controlFlow t y.2
  | .pair a b, y, ws, h => by
      simp only [enc, Value.tuple.injEq] at h
      subst h
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact enc_ne_controlFlow a y.1
      · exact enc_ne_controlFlow b y.2
  | .bit, _, _, h | .unit, _, _, h | .word _, _, _, h | .arr _ _, _, _, h
  | .uint _, _, _, h | .sint _, _, _, h | .int, _, _, h | .slice _, _, _, h => by
      simp [enc] at h

/-- The literal of an `ilit` reads the encoding of its value. -/
theorem litOfIlit_ofLit {t : NfTy} {v : Int} {l : ImpLit} {y : t.denote}
    (hl : litOfIlit t v = some l) (hy : NfTy.ofLit? t v = some y) : Value.ofLit l = enc t y := by
  cases t with
  | int =>
      simp only [litOfIlit, Option.some.injEq] at hl
      simp only [NfTy.ofLit?, Option.some.injEq] at hy
      subst hl hy; rfl
  | uint W =>
      simp only [litOfIlit, Option.some.injEq] at hl
      subst hl
      simp only [NfTy.ofLit?] at hy
      split at hy
      · rename_i hr
        simp only [Option.some.injEq] at hy
        subst hy
        have h0 : (v.toNat : Int) = v := Int.toNat_of_nonneg hr.1
        have h1 : v.toNat < 2 ^ W.bits := by
          have h2 := hr.2
          rw [← h0] at h2
          exact_mod_cast h2
        have h3 : (BitVec.ofInt W.bits v).toNat = v.toNat := by
          conv_lhs => rw [← h0]
          rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
        simp only [Value.ofLit, enc, IntWidth.modulus, Nat.mod_eq_of_lt h1, h3]
      · cases hy
  | sint W =>
      simp only [litOfIlit, Option.some.injEq] at hl
      subst hl
      simp only [NfTy.ofLit?] at hy
      split at hy
      · rename_i hr
        simp only [Option.some.injEq] at hy
        subst hy
        simp only [Value.ofLit, enc, BitVec.toInt_ofInt, Value.sint.injEq, true_and]
        rw [Int.bmod_eq_of_le] <;> cases W <;> simp_all [IntWidth.bits]
      · cases hy
  | _ => simp [litOfIlit] at hl

/-- A right-hand side of the readback runs to the encoding of the value of its operation,
    leaving the environment unchanged. -/
theorem rbRhs_sound (bi : Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ρ : RBEnv Γ}
    {env : Env} {V : Valuation Γ} (hrel : RBRel ρ env V) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) {rhs : ImpExpr}
      {y : op.ret.denote}, rbRhs ρ op args = some rhs →
      nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some y →
      (denote' bi fuel rhs).run env = (.val (enc op.ret y), env)
  | .call f as r, args, rhs, y, h, hy => by
      change (rbAtoms ρ args).map (ImpExpr.app f) = some rhs at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨xs, hxs, rfl⟩ := h
      change (bi f (encAll as (Expr.lookupArgs args V))).bind (dec r) = some y at hy
      rw [Option.bind_eq_some_iff] at hy
      obtain ⟨w, hw, hdec⟩ := hy
      rw [app_run, AtomsEval.run bi fuel (rbAtoms_eval hrel args hxs)
        (encAll_ne_controlFlow _ _)]
      simp only [hw]
      rw [dec_sound r w y hdec]
  | .ilit t v, _, rhs, y, h, hy => by
      change (litOfIlit t v).map ImpExpr.lit = some rhs at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨l, hl, rfl⟩ := h
      exact (lit_run bi fuel l env).trans (by rw [litOfIlit_ofLit hl hy])
  | .constBit b, _, rhs, y, h, hy => by
      change some (ImpExpr.lit (.bool b)) = some rhs at h
      change some b = some y at hy
      simp only [Option.some.injEq] at h hy
      subst h hy
      exact (lit_run bi fuel _ env).trans rfl
  | .constUnit, _, rhs, y, h, hy => by
      change some (ImpExpr.lit .unit) = some rhs at h
      simp only [Option.some.injEq] at h
      subst h
      exact (lit_run bi fuel _ env).trans rfl
  | .tnilV, _, rhs, y, h, hy => by
      change some (ImpExpr.tuple []) = some rhs at h
      simp only [Option.some.injEq] at h
      subst h
      rw [_root_.Hax.InlineLocalClosures.tuple_run, args_nil_run]
      rfl
  | .tconsV h₀ t, .cons a (.cons b .nil), rhs, y, h, hy => by
      change (match (ρ a).atom?, ρ b with
        | some x, .tup as => some (ImpExpr.tuple (x :: as))
        | _, _ => none) = some rhs at h
      change some (a.lookup V, b.lookup V) = some y at hy
      simp only [Option.some.injEq] at hy
      subst hy
      rcases hx : (ρ a).atom? with _ | x
      · rw [hx] at h; cases h
      rcases hrb : ρ b with _ | _ | as | _ | _ | _ <;> rw [hx, hrb] at h <;> try cases h
      have hb : RBOk env (ρ b) (enc t (b.lookup V)) := hrel t b
      rw [hrb] at hb
      obtain ⟨ws, hws, hbt⟩ := hb
      rw [_root_.Hax.InlineLocalClosures.tuple_run,
        AtomsEval.run bi fuel (as := x :: as) (ws := enc h₀ (a.lookup V) :: ws)
          ⟨RB.atom?_eval hx (hrel h₀ a), hws⟩ (fun w hw b' u => by
            simp only [List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact enc_ne_controlFlow h₀ _ b' u
            · exact enc_tuple_ne_controlFlow t _ ws hbt w hw b' u)]
      show (Outcome.val (.tuple (enc h₀ (a.lookup V) :: ws)), env) =
        (Outcome.val (.tuple (enc h₀ (a.lookup V) :: tailVals (enc t (b.lookup V)))), env)
      rw [hbt]
      rfl
  | .const _ _, _, _, _, h, _ | .bin _ _, _, _, _, h, _ | .un _ _, _, _, _, h, _
  | .cast _ _, _, _, _, h, _ | .scast _ _, _, _, _, h, _ | .cmp _ _, _, _, _, h, _
  | .andB, _, _, _, h, _ | .orB, _, _, _, h, _ | .xorB, _, _, _, h, _
  | .eqB, _, _, _, h, _ | .notB, _, _, _, h, _ | .index _ _, _, _, _, h, _
  | .update _ _, _, _, _, h, _ | .arrLit _ _, _, _, _, h, _ | .arrRepeat _ _, _, _, _, h, _
  | .mkPair _ _, _, _, _, h, _ | .fst _ _, _, _, _, h, _ | .snd _ _, _, _, _, h, _
  | .ctr, _, _, _, h, _ | .trip _, _, _, _, h, _ | .thead _ _, _, _, _, h, _
  | .ttail _ _, _, _, _, h, _ | .named _ _, _, _, _, h, _ => by
      simp [rbRhs] at h

/-- What the readback of a binding states about the value `w` of the binding: an emitted
    right-hand side runs to `w` at every fuel, leaving the environment unchanged; an inline
    reading reads `w`. -/
def RBBindOk (bi : Builtins) (env : Env) : RBBind → Value → Prop
  | .emit _ rhs _, w => ∀ fuel, (denote' bi fuel rhs).run env = (.val w, env)
  | .inline r, w => RBOk env r w

/-- **The readback of a binding is sound.** -/
theorem rbBind_sound (bi : Builtins) {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env}
    {V : Valuation Γ} (hrel : RBRel ρ env V) (c : Nat) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) {b : RBBind}
      {y : op.ret.denote}, rbBind ρ c op args = some b →
      nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) = some y →
      RBBindOk bi env b (enc op.ret y)
  | .named n op, args, b, y, h, hy => by
      change (rbRhs ρ op args).map (fun rhs => RBBind.emit n rhs false) = some b at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨rhs, hrhs, rfl⟩ := h
      exact fun fuel => rbRhs_sound bi fuel hrel op args hrhs hy
  | .call f as r, args, b, y, h, hy => by
      change (rbAtoms ρ args).map (fun xs => RBBind.emit (tmpName c) (.app f xs) true) =
        some b at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨xs, hxs, rfl⟩ := h
      intro fuel
      exact rbRhs_sound bi fuel hrel (.call f as r) args
        (show (rbAtoms ρ args).map (ImpExpr.app f) = some (.app f xs) by rw [hxs]; rfl) hy
  | .ilit t v, _, b, y, h, hy => by
      change (litOfIlit t v).map (fun l => RBBind.inline (.lit l)) = some b at h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨l, hl, rfl⟩ := h
      exact litOfIlit_ofLit hl hy
  | .constBit bt, _, b, y, h, hy => by
      change some (RBBind.inline (.lit (.bool bt))) = some b at h
      change some bt = some y at hy
      simp only [Option.some.injEq] at h hy
      subst h hy
      rfl
  | .constUnit, _, b, y, h, hy => by
      change some (RBBind.inline (.lit .unit)) = some b at h
      simp only [Option.some.injEq] at h
      subst h
      rfl
  | .trip t, .cons lo (.cons hi .nil), b, y, h, hy => by
      change (match ρ lo with
        | .lit (.int lo') =>
            if boundOk lo' t then (ρ hi).atom?.map fun h => RBBind.inline (.trip lo' h) else none
        | _ => none) = some b at h
      have hlo : RBOk env (ρ lo) (enc .int (lo.lookup V)) := hrel _ lo
      have hhi : RBOk env (ρ hi) (enc t (hi.lookup V)) := hrel _ hi
      rcases hρlo : ρ lo with _ | l | _ | _ | _ | _ <;> rw [hρlo] at h <;> try cases h
      cases l with
      | int lo' =>
          rw [hρlo] at hlo
          change Value.ofLit (.int lo') = .int (lo.lookup V) at hlo
          simp only [Value.ofLit, Value.int.injEq] at hlo
          dsimp only at h
          split at h
          · rename_i hbd
            rw [Option.map_eq_some_iff] at h
            obtain ⟨hx, hhx, rfl⟩ := h
            have hev := RB.atom?_eval hhx hhi
            cases t with
            | uint W =>
                change ((NfTy.toInt? (.uint W) (hi.lookup V)).map
                  fun hh => BitVec.ofNat 64 (hh - lo.lookup V).toNat) = some y at hy
                simp only [NfTy.toInt?, Option.map_some, Option.some.injEq] at hy
                subst hy
                have hlt := trip_lt_of_boundOk hbd (x := hi.lookup V)
                  (h := ((hi.lookup V).toNat : Int)) rfl
                refine ⟨((hi.lookup V).toNat : Int), ⟨_, hev, Or.inr ⟨W, _, rfl, rfl⟩⟩, ?_, ?_⟩
                · exact hlt
                · show Value.int ((BitVec.ofNat 64 _).toNat : Int) = _
                  rw [BitVec.toNat_ofNat, ← hlo, Nat.mod_eq_of_lt hlt]
            | word w =>
                change ((NfTy.toInt? (.word w) (hi.lookup V)).map
                  fun hh => BitVec.ofNat 64 (hh - lo.lookup V).toNat) = some y at hy
                simp only [NfTy.toInt?, Option.map_some, Option.some.injEq] at hy
                subst hy
                have hlt := trip_lt_of_boundOk hbd (x := hi.lookup V)
                  (h := ((hi.lookup V).toNat : Int)) rfl
                refine ⟨((hi.lookup V).toNat : Int), ⟨_, hev, Or.inl rfl⟩, ?_, ?_⟩
                · exact hlt
                · show Value.int ((BitVec.ofNat 64 _).toNat : Int) = _
                  rw [BitVec.toNat_ofNat, ← hlo, Nat.mod_eq_of_lt hlt]
            | _ => simp [boundOk] at hbd
          · cases h
      | _ => cases h
  | .tnilV, _, b, y, h, hy => by
      change some (RBBind.inline (.tup [])) = some b at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨[], trivial, rfl⟩
  | .tconsV h₀ t, .cons a (.cons b' .nil), b, y, h, hy => by
      change (match (ρ a).atom?, ρ b' with
        | some x, .tup as => some (RBBind.inline (.tup (x :: as)))
        | _, _ => none) = some b at h
      change some (a.lookup V, b'.lookup V) = some y at hy
      simp only [Option.some.injEq] at hy
      subst hy
      rcases hx : (ρ a).atom? with _ | x
      · rw [hx] at h; cases h
      rcases hrb : ρ b' with _ | _ | as | _ | _ | _ <;> rw [hx, hrb] at h <;> try cases h
      have hb : RBOk env (ρ b') (enc t (b'.lookup V)) := hrel t b'
      rw [hrb] at hb
      obtain ⟨ws, hws, hbt⟩ := hb
      refine ⟨enc h₀ (a.lookup V) :: ws, ⟨RB.atom?_eval hx (hrel h₀ a), hws⟩, ?_⟩
      show Value.tuple (enc h₀ (a.lookup V) :: tailVals (enc t (b'.lookup V))) = _
      rw [hbt]
      rfl
  | .const _ _, _, _, _, h, _ | .bin _ _, _, _, _, h, _ | .un _ _, _, _, _, h, _
  | .cast _ _, _, _, _, h, _ | .scast _ _, _, _, _, h, _ | .cmp _ _, _, _, _, h, _
  | .andB, _, _, _, h, _ | .orB, _, _, _, h, _ | .xorB, _, _, _, h, _
  | .eqB, _, _, _, h, _ | .notB, _, _, _, h, _ | .index _ _, _, _, _, h, _
  | .update _ _, _, _, _, h, _ | .arrLit _ _, _, _, _, h, _ | .arrRepeat _ _, _, _, _, h, _
  | .mkPair _ _, _, _, _, h, _ | .fst _ _, _, _, _, h, _ | .snd _ _, _, _, _, h, _
  | .ctr, _, _, _, h, _ | .thead _ _, _, _, _, h, _ | .ttail _ _, _, _, _, h, _ => by
      simp [rbBind] at h

/-- The names `ns` hold the values `ws` in `env`. -/
def NamesVals (env : Env) : List String → List Value → Prop
  | [], [] => True
  | n :: ns, w :: ws => env n = some w ∧ NamesVals env ns ws
  | _, _ => False

/-- The assignments of `rbAssigns` run to the unit value, the names holding the values of
    the atoms and every other name unchanged. -/
theorem rbAssigns_run (bi : Builtins) (fuel : Nat) :
    ∀ (ns : List String) (as : List ImpExpr), ns.Nodup → ∀ {ie : ImpExpr},
      rbAssigns ns as = some ie → ∀ {env : Env} {ws : List Value}, AtomsEval env as ws →
      (∀ w ∈ ws, ∀ b u, w ≠ .controlFlow b u) →
      ∃ env', (denote' bi fuel ie).run env = (.val .unit, env') ∧ NamesVals env' ns ws ∧
        ∀ m, m ∉ ns → env' m = env m
  | [], [], _, ie, h, env, ws, hev, _ => by
      simp only [rbAssigns, Option.some.injEq] at h
      subst h
      cases ws with
      | nil => exact ⟨env, unitVal_run bi fuel env, trivial, fun _ _ => rfl⟩
      | cons _ _ => exact hev.elim
  | n :: ns, a :: as, hnd, ie, h, env, ws, hev, hcf => by
      cases ws with
      | nil => exact hev.elim
      | cons w ws =>
      obtain ⟨ha, has⟩ := hev
      have hnd' := (List.nodup_cons.mp hnd)
      simp only [rbAssigns] at h
      split at h
      · rename_i hv
        obtain ⟨env', hrun, hnv, hfr⟩ := rbAssigns_run bi fuel ns as hnd'.2 h has
          (fun w' hw' => hcf w' (List.mem_cons_of_mem _ hw'))
        refine ⟨env', hrun, ⟨?_, hnv⟩, fun m hm => hfr m (fun h' => hm (List.mem_cons_of_mem _ h'))⟩
        rw [hfr n hnd'.1]
        cases a with
        | var m =>
            simp only [isVarOf, beq_iff_eq] at hv
            subst hv
            exact ha
        | _ => simp [isVarOf] at hv
      · split at h
        · cases h
        · rename_i hv hany
          rw [Option.map_eq_some_iff] at h
          obtain ⟨ie', hie', rfl⟩ := h
          have has' : AtomsEval (env.extend n w) as ws := by
            refine AtomsEval.congr (fun m hm => ?_) has
            have hmn : m ≠ n := by
              intro hmn; subst hmn
              exact hany (List.any_eq_true.mpr ⟨_, hm, by simp [isVarOf]⟩)
            exact Env.extend_other _ _ _ _ hmn
          obtain ⟨env', hrun, hnv, hfr⟩ := rbAssigns_run bi fuel ns as hnd'.2 hie' has'
            (fun w' hw' => hcf w' (List.mem_cons_of_mem _ hw'))
          have hw := hcf w List.mem_cons_self
          refine ⟨env', ?_, ⟨?_, hnv⟩, fun m hm => ?_⟩
          · rw [seq_run_val bi fuel ie' (assign_run_val bi fuel n (AtomEval.run bi fuel ha) hw)
              (fun b u h => by cases h)]
            exact hrun
          · rw [hfr n hnd'.1, Env.extend_same]
          · simp only [List.mem_cons, not_or] at hm
            rw [hfr m hm.2, Env.extend_other _ _ _ _ hm.1]
  | [], _ :: _, _, _, h, _, _, _, _ => by simp [rbAssigns] at h
  | _ :: _, [], _, _, h, _, _, _, _ => by simp [rbAssigns] at h

/-- The names read by shifted variables are the names read below the binding. -/
theorem hvNames_shiftVars {Γ : Ctxt nfDialect} {s : NfTy} (ρ : RBEnv (s :: Γ)) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts),
      hvNames ρ (shiftVars (s := s) vs) = hvNames (fun v => ρ v.there) vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show (ρ v.there).names ++ hvNames ρ (shiftVars vs) = (ρ v.there).names ++ _
      rw [hvNames_shiftVars ρ vs]

/-- Every name a variable's reading reads is a name of the reading of the context. -/
theorem mem_allNames : ∀ {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) {t : NfTy} (v : Var Γ t)
    {n : String}, n ∈ (ρ v).names → n ∈ RBEnv.allNames ρ
  | _ :: Γ, ρ, _, .here, n, h => by
      show n ∈ hvNames ρ (allVars (d := nfDialect) (_ :: Γ))
      show n ∈ (ρ .here).names ++ hvNames ρ (shiftVars (allVars Γ))
      exact List.mem_append_left _ h
  | _ :: Γ, ρ, _, .there v, n, h => by
      show n ∈ (ρ .here).names ++ hvNames ρ (shiftVars (allVars Γ))
      rw [hvNames_shiftVars]
      exact List.mem_append_right _ (mem_allNames (fun v => ρ v.there) v h)

/-- The relation holds in an environment that agrees at every name the reading reads. -/
theorem RBRel.congr {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env env' : Env} {V : Valuation Γ}
    (h : RBRel ρ env V) (hag : ∀ n ∈ RBEnv.allNames ρ, env' n = env n) : RBRel ρ env' V :=
  fun t v => RBOk.congr (fun n hn => hag n (mem_allNames ρ v hn)) (h t v)

/-- Making readings unreadable keeps the relation. -/
theorem RBRel.clobber {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (h : RBRel ρ env V) (ns : List String) : RBRel (RBEnv.clobber ns ρ) env V := by
  intro t v
  simp only [RBEnv.clobber]
  split
  · trivial
  · exact h t v

/-- Dropping the trip-index readings keeps the relation. -/
theorem RBRel.dropIdx {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (h : RBRel ρ env V) : RBRel (RBEnv.dropIdx ρ) env V := by
  intro t v
  have := h t v
  simp only [RBEnv.dropIdx]
  split
  · trivial
  · exact this

/-- The reading with the carried variables held in the names `cn` is related when the
    names hold the encodings of the carried values. -/
theorem RBRel.appNames {Γ : Ctxt nfDialect} {ρ : RBEnv Γ} {env : Env} {V : Valuation Γ}
    (h : RBRel ρ env V) :
    ∀ (cs : List NfTy) (cn : List String) (acc : Valuation (d := nfDialect) cs),
      NamesVals env cn (encAll cs acc) → RBRel (RBEnv.appNames cs cn ρ) env (hvAppend acc V)
  | [], [], .nil, _ => h
  | c :: cs, n :: cn, .cons a acc, hv =>
      RBRel.cons (s := c) (RBRel.appNames h cs cn acc hv.2) (r := .name n) (x := a) hv.1
  | [], _ :: _, .nil, hv => hv.elim
  | _ :: _, [], .cons _ _, hv => hv.elim

/-- In the reading of a loop body, the only trip-index reading is the trip index, whose
    value encodes the index `k`. -/
theorem idx_appNames {Γ : Ctxt nfDialect} (ρ : RBEnv Γ) (V : Valuation Γ) (k : Nat)
    (hk : k < 2 ^ 64) :
    ∀ (cs : List NfTy) (cn : List String) (acc : Valuation (d := nfDialect) cs) {t : NfTy}
      (v : Var (d := nfDialect) (cs ++ NfTy.word 64 :: Γ) t),
      RBEnv.appNames cs cn (RBEnv.cons .idx (RBEnv.dropIdx ρ)) v = .idx →
      enc t (v.lookup (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V))) =
        .int k
  | [], _, .nil, _, .here, _ => by
      show Value.int ((BitVec.ofNat 64 k).toNat : Int) = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  | [], _, .nil, _, .there v, h => by
      change RBEnv.dropIdx ρ v = .idx at h
      simp only [RBEnv.dropIdx] at h
      split at h <;> simp_all
  | _ :: cs, n :: cn, .cons _ acc, _, .here, h => by cases h
  | _ :: cs, [], .cons _ acc, _, .here, h => by cases h
  | _ :: cs, n :: cn, .cons _ acc, _, .there v, h =>
      idx_appNames ρ V k hk cs cn acc v h
  | _ :: cs, [], .cons _ acc, _, .there v, h =>
      idx_appNames ρ V k hk cs [] acc v h

/-- A `forFold` with a literal lower bound whose upper bound is an atom reading an integer
    or an unsigned integer runs as the loop on that bound. -/
theorem forFold_atom_run (bi : Builtins) (fuel : Nat) (i : String) (lo : Int)
    (hiE body : ImpExpr) {env : Env} {hv : Value} {h : Int} (hh : AtomEval env hiE hv)
    (hrep : hv = .int h ∨ ∃ (W : IntWidth) (n : Nat), hv = .uint W n ∧ h = n) :
    (denote' bi fuel (.forFold i (.lit (.int lo)) hiE body)).run env =
      (_root_.Hax.denoteForLoop' bi fuel i lo h body).run env := by
  have hr := AtomEval.run bi fuel hh
  simp only [denote', StateT.run, bind, StateT.bind, pure, StateT.pure, Value.ofLit] at hr ⊢
  rw [hr]
  rcases hrep with rfl | ⟨W, n, rfl, rfl⟩ <;> rfl

/-- **The readback loop runs.** Let every target trip from a state satisfying `Inv` be
    matched by a run of the readback body, from the environment with the counter bound, to a
    value that is not a control-flow value, in a state satisfying `Inv`. Then a fold of the
    target body over `m` trips from the index `k` is matched, at every large enough fuel, by
    `denoteForLoop'` from the counter `lo + k`. -/
theorem rbLoop_run (bi : Builtins) (tf : Nat) (i : String) (lo h : Int) (bodyIE : ImpExpr)
    {Γ : Ctxt nfDialect} (V : Valuation Γ) {cs : List NfTy}
    (bodyP : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ) cs)
    (Inv : Env → Valuation (d := nfDialect) cs → Prop)
    (HS : ∀ (k : Nat) (env : Env) (acc acc' : Valuation (d := nfDialect) cs), k < 2 ^ 64 →
      Inv env acc →
      PDenP bi tf bodyP (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V)) =
        some acc' →
      ∃ f w e₂, (denote' bi f bodyIE).run (env.extend i (.int (lo + k))) = (.val w, e₂) ∧
        (∀ b u, w ≠ .controlFlow b u) ∧ Inv e₂ acc') :
    ∀ (m k : Nat) (env : Env) (acc accF : Valuation (d := nfDialect) cs),
      (h - (lo + k)).toNat = m → k + m < 2 ^ 64 → Inv env acc →
      (List.range' k m).foldlM (fun a j => PDenP bi tf bodyP
        (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V))) acc = some accF →
      ∃ F₀, ∀ F, F₀ ≤ F → ∃ envF,
        (_root_.Hax.denoteForLoop' bi F i (lo + k) h bodyIE).run env = (.val .unit, envF) ∧
          Inv envF accF := by
  intro m
  induction m with
  | zero =>
      intro k env acc accF hm _ hinv hfold
      simp only [List.range'_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hfold
      subst hfold
      exact ⟨0, fun F _ => ⟨env, forLoop_ge_run bi F i _ h bodyIE env (by omega), hinv⟩⟩
  | succ m ih =>
      intro k env acc accF hm hk hinv hfold
      rw [List.range'_succ, List.foldlM_cons] at hfold
      rcases hacc : PDenP bi tf bodyP
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V)) with _ | acc'
      · rw [hacc] at hfold; cases hfold
      rw [hacc] at hfold
      obtain ⟨f, w, e₂, hb, hcf, hinv'⟩ := HS k env acc acc' (by omega) hinv hacc
      obtain ⟨F₁, hF₁⟩ := ih (k + 1) e₂ acc' accF (by omega) (by omega) hinv' hfold
      refine ⟨max f (F₁ + 1), fun F hF => ?_⟩
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
      have hlt : lo + k < h := by omega
      have hb' : (denote' bi (F' + 1) bodyIE).run (env.extend i (.int (lo + k))) =
          (.val w, e₂) := by
        have hmono := Hax.Ascent.denote'_fuel_mono bi (fuel := f) (fuel' := F' + 1)
          (e := bodyIE) (env := env.extend i (.int (lo + k)))
          (by change Hax.Ascent.isErr ((denote' bi f bodyIE).run _).1 = false; rw [hb]; rfl)
          (by omega)
        show denote' bi (F' + 1) bodyIE _ = _
        rw [hmono]
        exact hb
      rw [forLoop_succ_run_val bi F' i bodyIE hlt hb' hcf]
      have hk1 : lo + k + 1 = lo + ((k + 1 : Nat) : Int) := by push_cast; ring
      rw [hk1]
      exact hF₁ F' (by omega)

/-- A named counter operation has the result type `int` and the value `lo + i` of its
    arguments. -/
theorem ctrOf?_sound (bi : Builtins) {Γ : Ctxt nfDialect} {op : NfOp}
    {args : HVector (fun t => Var Γ t) op.sig} {i : String} {a : Var Γ NfTy.int}
    {b : Var Γ (NfTy.word 64)} (h : ctrOf? op args = some (i, a, b)) :
    ∃ hr : op.ret = NfTy.int, ∀ V : Valuation Γ,
      nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) =
        some (hr ▸ ((fun (x : Int) (y : BitVec 64) => x + (y.toNat : Int))
          (a.lookup V) (b.lookup V))) := by
  cases op <;> try (simp [ctrOf?] at h; done)
  rename_i n op
  cases op <;> try (simp [ctrOf?] at h; done)
  change some (n, args.head, args.tail.head) = some (i, a, b) at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨rfl, fun V => ?_⟩
  rcases args with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  rfl

/-- Variable atoms read the values their names hold. -/
theorem namesOf_vals {env : Env} :
    ∀ {xs : List ImpExpr} {cn : List String} {ws : List Value}, namesOf xs = some cn →
      AtomsEval env xs ws → NamesVals env cn ws
  | [], cn, [], h, _ => by simp only [namesOf, Option.some.injEq] at h; subst h; trivial
  | .var n :: xs, cn, w :: ws, h, ⟨hw, hws⟩ => by
      simp only [namesOf, Option.map_eq_some_iff] at h
      obtain ⟨cn', hcn', rfl⟩ := h
      exact ⟨hw, namesOf_vals hcn' hws⟩
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
  | .lit _ :: _, _, _ :: _, h, _ => by simp [namesOf] at h
  | .letBind .. :: _, _, _ :: _, h, _ | .lam .. :: _, _, _ :: _, h, _
  | .app .. :: _, _, _ :: _, h, _ | .tuple .. :: _, _, _ :: _, h, _
  | .proj .. :: _, _, _ :: _, h, _ | .ifThenElse .. :: _, _, _ :: _, h, _
  | .match_ .. :: _, _, _ :: _, h, _ | .unitVal :: _, _, _ :: _, h, _
  | .seq .. :: _, _, _ :: _, h, _ | .borrow .. :: _, _, _ :: _, h, _
  | .deref .. :: _, _, _ :: _, h, _ | .assign .. :: _, _, _ :: _, h, _
  | .forLoop .. :: _, _, _ :: _, h, _ | .forLoopRev .. :: _, _, _ :: _, h, _
  | .whileLoop .. :: _, _, _ :: _, h, _ | .break_ .. :: _, _, _ :: _, h, _
  | .continue_ :: _, _, _ :: _, h, _ | .earlyReturn .. :: _, _, _ :: _, h, _
  | .questionMark .. :: _, _, _ :: _, h, _ | .forFold .. :: _, _, _ :: _, h, _
  | .forFoldRev .. :: _, _, _ :: _, h, _ | .whileFold .. :: _, _, _ :: _, h, _
  | .forFoldReturn .. :: _, _, _ :: _, h, _ | .forFoldRevReturn .. :: _, _, _ :: _, h, _
  | .whileFoldReturn .. :: _, _, _ :: _, h, _ | .cfBreak .. :: _, _, _ :: _, h, _
  | .cfContinue .. :: _, _, _ :: _, h, _ | .cfBreakContinue .. :: _, _, _ :: _, h, _
  | .typeAscription .. :: _, _, _ :: _, h, _ => by simp [namesOf] at h

/-- The soundness of a readback continuation for the returned values `out` and the
    postcondition `Q`: from a related reading of the returned variables, its code runs to
    an outcome that is not an error, satisfying `Q`. -/
def RKSound (bi : Builtins) {ts : List NfTy} (rk : RK ts) (out : Valuation (d := nfDialect) ts)
    (Q : Outcome → Env → Prop) : Prop :=
  ∀ {Δ : Ctxt nfDialect} (ρ' : RBEnv Δ) (vs : HVector (fun t => Var Δ t) ts) (c₁ : Nat)
    (ie₁ : ImpExpr) (c₁' : Nat) (env₁ : Env) (W : Valuation Δ),
    rk ρ' vs c₁ = some (ie₁, c₁') → RBRel ρ' env₁ W → Expr.lookupArgs vs W = out →
    ∃ fuel r env₂, (denote' bi fuel ie₁).run env₁ = (r, env₂) ∧
      Hax.Ascent.isErr r = false ∧ Q r env₂

/-- **The soundness of the readback** of the program `p`: a denotation of `p` to `out` from
    a valuation related to `env` is matched by a run of the readback, at some fuel, to an
    outcome that is not an error and satisfies the postcondition of a sound continuation. -/
def RBSound (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ (ρ : RBEnv Γ) (c : Nat) (rk : RK ts) (ie : ImpExpr) (c' : Nat),
    rbProg p ρ c rk = some (ie, c') →
    ∀ (env : Env) (V : Valuation Γ) (out : Valuation (d := nfDialect) ts), RBRel ρ env V →
    PDenP bi tf p V = some out → ∀ (Q : Outcome → Env → Prop), RKSound bi rk out Q →
    ∃ fuel r env₂, (denote' bi fuel ie).run env = (r, env₂) ∧
      Hax.Ascent.isErr r = false ∧ Q r env₂

/-- `RBSound` of the continuation of a binding, and `True` for every other program. -/
def RBSoundTail (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} :
    NFProg nfDialect Γ ts → Prop
  | .var _ k => RBSound bi tf k
  | _ => True

/-- **The readback is sound.** -/
theorem rbProg_sound_aux (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : RBSound bi tf p ∧ RBSoundTail bi tf p := by
  induction p with
  | ret vs =>
      refine ⟨fun ρ c rk ie c' h env V out hrel hp Q hQ => ?_, trivial⟩
      change rk ρ vs c = some (ie, c') at h
      change some (Expr.lookupArgs vs V) = some out at hp
      simp only [Option.some.injEq] at hp
      exact hQ ρ vs c ie c' env V h hrel hp
  | var e k ih =>
      refine ⟨fun ρ c rk ie c' h env V out hrel hp Q hQ => ?_, ih.1⟩
      obtain ⟨op, rfl, args⟩ := e
      change ((rbBind ρ c op args).bind fun b => match b with
        | .emit n rhs tmp =>
            (rbProg k (RBEnv.cons (.name n) (RBEnv.clobber [n] ρ)) (if tmp then c + 1 else c)
              rk).map fun r => (ImpExpr.letBind n rhs r.1, r.2)
        | .inline r => rbProg k (RBEnv.cons r ρ) c rk) = some (ie, c') at h
      rcases hb : rbBind ρ c op args with _ | b
      · rw [hb] at h; cases h
      rw [hb, Option.bind_some] at h
      change (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => PDenP bi tf k (V.extend x)) = some out at hp
      rcases hy : nfDenoteOp (tableOf bi) op (Expr.lookupArgs args V) with _ | y
      · rw [hy] at hp; cases hp
      rw [hy, Option.bind_some] at hp
      have hbs := rbBind_sound bi hrel c op args hb hy
      cases b with
      | emit n rhs tmp =>
          dsimp only at h
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨ie₁, c₁⟩, h₁, heq⟩ := h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          have hrel' : RBRel (RBEnv.cons (.name n) (RBEnv.clobber [n] ρ))
              (env.extend n (enc op.ret y)) (V.extend y) :=
            (hrel.clobber_extend n _).cons (Env.extend_same _ _ _)
          obtain ⟨fuel, r, env₂, hr, herr, hq⟩ := ih.1 _ _ rk ie₁ c₁ h₁ _ _ out hrel' hp Q hQ
          refine ⟨fuel, r, env₂, ?_, herr, hq⟩
          rw [letBind_run_val bi fuel n ie₁ (hbs fuel) (enc_ne_controlFlow _ _)]
          exact hr
      | inline r =>
          exact ih.1 _ _ rk ie c' h env _ out (hrel.cons hbs) hp Q hQ
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      refine ⟨fun ρ c rk ie c' h env V out hrel hp Q hQ => ?_, trivial⟩
      cases body with
      | var e rest =>
          have ihr : RBSound bi tf rest := ihb.2
          obtain ⟨op, hop, args⟩ := e
          simp only [rbProg] at h
          rcases hc : ctrOf? op args with _ | ⟨i, a, b⟩
          · rw [hc] at h; cases h
          obtain ⟨hr, hctr⟩ := ctrOf?_sound bi hc
          subst hop
          rw [hc, Option.bind_some] at h
          dsimp only at h
          rcases hcount : ρ count with _ | _ | _ | ⟨lo, hi⟩ | _ | _ <;> rw [hcount] at h <;>
            dsimp only at h <;> try cases h
          rcases hxs : rbAtoms ρ inits with _ | xs
          · rw [hxs] at h; cases h
          rw [hxs, Option.bind_some] at h
          rcases hcn : namesOf xs with _ | cn
          · rw [hcn] at h; cases h
          rw [hcn, Option.bind_some] at h
          by_cases hnd : cn.Nodup
          swap
          · rw [if_neg hnd] at h; cases h
          rw [if_pos hnd] at h
          split at h
          case h_2 => cases h
          rename_i lo' hra hrb
          split at h
          case isFalse => cases h
          rename_i hlo'
          subst hlo'
          rw [Option.bind_eq_some_iff] at h
          obtain ⟨⟨bIE, c₁⟩, hbody, h⟩ := h
          dsimp only at h
          split at h
          case isFalse => cases h
          rename_i hfr
          rw [Option.map_eq_some_iff] at h
          obtain ⟨⟨rIE, c₂⟩, hkr, heq⟩ := h
          simp only [Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          -- the target loop
          have hp' : ((List.range (count.lookup V : BitVec 64).toNat).foldlM
              (fun acc j => PDenP bi tf (NFProg.var ⟨op, rfl, args⟩ rest)
                (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
              (Expr.lookupArgs inits V)).bind (fun acc => PDenP bi tf k (hvAppend acc V)) =
              some out := hp
          rw [Option.bind_eq_some_iff] at hp'
          obtain ⟨accF, hfold, hkout⟩ := hp'
          -- the trip count
          have hcv : RBOk env (ρ count) (enc (NfTy.word 64) (count.lookup V)) := hrel _ count
          rw [hcount] at hcv
          obtain ⟨hh, ⟨hv, hhv, hrep⟩, hlt, hcenc⟩ := hcv
          have hcnt : (count.lookup V : BitVec 64).toNat = (hh - lo').toNat := by
            change Value.int ((count.lookup V : BitVec 64).toNat : Int) = _ at hcenc
            simp only [Value.int.injEq] at hcenc
            exact_mod_cast hcenc
          rw [hcnt, List.range_eq_range'] at hfold
          -- the initial carried values
          have hcar0 : NamesVals env cn (encAll cs (Expr.lookupArgs inits V)) :=
            namesOf_vals hcn (rbAtoms_eval hrel inits hxs)
          let Inv : Env → Valuation (d := nfDialect) cs → Prop := fun e acc =>
            NamesVals e cn (encAll cs acc) ∧
              ∀ n ∈ RBEnv.allNames (RBEnv.clobber cn ρ), e n = env n
          have hrelΓ : ∀ e, (∀ n ∈ RBEnv.allNames (RBEnv.clobber cn ρ), e n = env n) →
              RBRel (RBEnv.clobber cn ρ) e V := fun e he => (hrel.clobber cn).congr he
          -- the frame of the loop body
          have hfrb : ∀ n ∈ RBEnv.allNames (RBEnv.clobber cn ρ), (i != n) = true ∧
              frameOk (fun _ => true) (fun m => m != n) (fun _ => true) bIE = true := by
            intro n hn
            have := List.all_eq_true.mp hfr n hn
            simp only [frameOk, Bool.and_eq_true] at this
            exact ⟨this.1.1.1, this.2⟩
          have HS : ∀ (kk : Nat) (e : Env) (acc acc' : Valuation (d := nfDialect) cs),
              kk < 2 ^ 64 → Inv e acc →
              PDenP bi tf (NFProg.var ⟨op, rfl, args⟩ rest)
                  (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)) =
                some acc' →
              ∃ f w e₂, (denote' bi f bIE).run (e.extend i (.int (lo' + kk))) = (.val w, e₂) ∧
                (∀ b u, w ≠ .controlFlow b u) ∧ Inv e₂ acc' := by
            intro kk e acc acc' hkk hinv hpb
            have hrelB : RBRel (RBEnv.appNames cs cn (RBEnv.cons .idx
                (RBEnv.dropIdx (RBEnv.clobber cn ρ)))) e
                (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)) :=
              RBRel.appNames (((hrelΓ e hinv.2).dropIdx).cons (r := .idx) trivial) cs cn acc
                hinv.1
            change (nfDenoteOp (tableOf bi) op (Expr.lookupArgs args _)).bind
              (fun x => PDenP bi tf rest (Valuation.extend _ x)) = some acc' at hpb
            rw [hctr, Option.bind_some] at hpb
            have ha := hrelB _ a
            beta_reduce at ha
            rw [hra] at ha
            have ha' : a.lookup (hvAppend acc
                (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)) = lo' := by
              change Value.int lo' = Value.int _ at ha
              exact (Value.int.inj ha).symm
            have hb := idx_appNames (RBEnv.clobber cn ρ) V kk hkk cs cn acc b hrb
            have hb' : ((b.lookup (hvAppend acc
                (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)) : BitVec 64).toNat :
                  Int) = kk := by
              change Value.int _ = Value.int _ at hb
              exact Value.int.inj hb
            have henc : ∀ {T : NfTy} (h : NfTy.int = T) (z : Int), enc T (h ▸ z) = .int z := by
              intro T h z; subst h; rfl
            have hrel'' := ((hrelB.clobber_extend i (.int (lo' + kk))).cons (s := op.ret)
              (r := .name i)
              (x := hr ▸ ((fun (x : Int) (y : BitVec 64) => x + (y.toNat : Int))
                (a.lookup (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)))
                (b.lookup (hvAppend acc
                  (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 kk) V)))))
              (by
                show (e.extend i (.int (lo' + kk))) i = some _
                rw [Env.extend_same, henc hr.symm, ha']
                beta_reduce
                rw [hb']))
            obtain ⟨f, r, e₂, hrun, herr, hQ'⟩ := ihr _ c _ bIE c₁ hbody _ _ acc' hrel'' hpb
              (fun r e₂ => r = .val .unit ∧ NamesVals e₂ cn (encAll cs acc'))
              (by
                intro Δ ρ' vs c₃ ie₁ c₃' env₁ W hrk hrelW hvs
                change (rbAtoms ρ' vs).bind (fun as => (rbAssigns cn as).map (·, c₃)) =
                  some (ie₁, c₃') at hrk
                rcases has : rbAtoms ρ' vs with _ | as
                · rw [has] at hrk; cases hrk
                rw [has, Option.bind_some, Option.map_eq_some_iff] at hrk
                obtain ⟨ie₂, hie₂, heq⟩ := hrk
                cases heq
                have hev := rbAtoms_eval hrelW vs has
                rw [hvs] at hev
                obtain ⟨env', hrun', hnv, _⟩ := rbAssigns_run bi 0 cn as hnd hie₂ hev
                  (encAll_ne_controlFlow _ _)
                exact ⟨0, _, _, hrun', rfl, rfl, hnv⟩)
            obtain ⟨rfl, hnv⟩ := hQ'
            refine ⟨f, .unit, e₂, hrun, fun b u h => (by cases h), hnv, fun n hn => ?_⟩
            obtain ⟨hin, hfn⟩ := hfrb n hn
            rw [denote'_keeps bi bIE hfn f _ hrun (by rintro ⟨_, h⟩; cases h),
              Env.extend_other _ _ _ _ (by simpa using (bne_iff_ne.mp hin).symm),
              hinv.2 n hn]
          obtain ⟨F₀, hF₀⟩ := rbLoop_run bi tf i lo' hh bIE V
            (NFProg.var ⟨op, rfl, args⟩ rest) Inv HS (hh - lo').toNat 0 env
            (Expr.lookupArgs inits V) accF (by simp) (by omega) ⟨hcar0, fun _ _ => rfl⟩ hfold
          obtain ⟨envF, hloopF, hinvF⟩ := hF₀ F₀ le_rfl
          obtain ⟨f₂, r, env₂, hrun₂, herr₂, hq₂⟩ := ihk.1 _ c₁ rk rIE c₂ hkr envF
            (hvAppend accF V) out (RBRel.appNames (hrelΓ envF hinvF.2) cs cn accF hinvF.1)
            hkout Q hQ
          have h0 : (denote' bi F₀ (.forFold i (.lit (.int lo')) hi bIE)).run env =
              (.val .unit, envF) := by
            rw [forFold_atom_run bi _ i lo' hi bIE hhv hrep]
            simpa using hloopF
          have hloop' : (denote' bi (max F₀ f₂) (.forFold i (.lit (.int lo')) hi bIE)).run env =
              (.val .unit, envF) := by
            have hmono := Hax.Ascent.denote'_fuel_mono bi (fuel := F₀) (fuel' := max F₀ f₂)
              (e := .forFold i (.lit (.int lo')) hi bIE) (env := env)
              (by change Hax.Ascent.isErr ((denote' bi F₀ _).run env).1 = false
                  rw [h0]; rfl)
              (le_max_left _ _)
            show denote' bi (max F₀ f₂) _ env = _
            rw [hmono]
            exact h0
          have hrun₂' : (denote' bi (max F₀ f₂) rIE).run envF = (r, env₂) := by
            have hmono := Hax.Ascent.denote'_fuel_mono bi (fuel := f₂) (fuel' := max F₀ f₂)
              (e := rIE) (env := envF)
              (by change Hax.Ascent.isErr ((denote' bi f₂ rIE).run envF).1 = false
                  rw [hrun₂]; exact herr₂)
              (le_max_right _ _)
            show denote' bi (max F₀ f₂) rIE envF = _
            rw [hmono]
            exact hrun₂
          refine ⟨max F₀ f₂, r, env₂, ?_, herr₂, hq₂⟩
          rw [seq_run_val bi _ rIE hloop' (fun b u h => by cases h)]
          exact hrun₂'
      | _ => simp [rbProg] at h
  | ifThenElse cond thn els k _ _ _ =>
      refine ⟨fun ρ c rk ie c' h => ?_, trivial⟩
      simp [rbProg] at h
  | whileLoop inits body k _ _ =>
      refine ⟨fun ρ c rk ie c' h => ?_, trivial⟩
      simp [rbProg] at h

/-- The expression of a reading runs to the value the reading reads, leaving the environment
    unchanged, when the components of a tuple value are no control-flow values. -/
theorem RB.expr?_run (bi : Builtins) (fuel : Nat) {env : Env} {r : RB} {x : ImpExpr}
    {w : Value} (h : r.expr? = some x) (hr : RBOk env r w)
    (hcf : ∀ ws, w = .tuple ws → ∀ w' ∈ ws, ∀ b u, w' ≠ .controlFlow b u) :
    (denote' bi fuel x).run env = (.val w, env) := by
  cases r with
  | name n =>
      simp only [RB.expr?, Option.some.injEq] at h; subst h
      exact AtomEval.run bi fuel (a := .var n) hr
  | lit l =>
      simp only [RB.expr?, Option.some.injEq] at h; subst h
      exact AtomEval.run bi fuel (a := .lit l) hr
  | tup as =>
      simp only [RB.expr?, Option.some.injEq] at h; subst h
      obtain ⟨ws, hws, rfl⟩ := hr
      rw [_root_.Hax.InlineLocalClosures.tuple_run, AtomsEval.run bi fuel hws (hcf ws rfl)]
  | trip _ _ | idx | gone => simp [RB.expr?] at h

/-- **The readback simulates the denotation.** If the readback of the one-result program
    `p` from the reading `ρ` is `ie`, and `p` denotes, from a valuation related to `env`, the
    value `y`, then `ie` runs from `env`, at some fuel, to the encoding of `y`. -/
theorem nfToImp_denote (bi : Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {t : NfTy}
    (p : NFProg nfDialect Γ [t]) (ρ : RBEnv Γ) {ie : ImpExpr} (h : nfToImp p ρ = some ie)
    {env : Env} {V : Valuation Γ} {y : t.denote} (hrel : RBRel ρ env V)
    (hp : PDenP bi tf p V = some (.cons y .nil)) :
    ∃ fuel env₂, (denote' bi fuel ie).run env = (.val (enc t y), env₂) := by
  simp only [nfToImp, Option.map_eq_some_iff] at h
  obtain ⟨⟨ie', c'⟩, h, rfl⟩ := h
  obtain ⟨fuel, r, env₂, hrun, -, hq⟩ := (rbProg_sound_aux bi tf p).1 ρ 0 _ ie' c' h env V
    _ hrel hp (fun r _ => r = .val (enc t y)) (by
      intro Δ ρ' vs c₁ ie₁ c₁' env₁ W hrk hrelW hvs
      obtain ⟨v, vs'⟩ : ∃ v, vs = .cons v .nil := by
        rcases vs with _ | ⟨v, _ | _⟩; exact ⟨v, rfl⟩
      subst vs'
      change ((ρ' v).expr?.map (·, c₁)) = some (ie₁, c₁') at hrk
      rw [Option.map_eq_some_iff] at hrk
      obtain ⟨x, hx, heq⟩ := hrk
      cases heq
      have hy : v.lookup W = y := by
        change HVector.cons (v.lookup W) .nil = _ at hvs
        cases hvs; rfl
      subst hy
      exact ⟨0, _, _, RB.expr?_run bi 0 hx (hrelW t v) (enc_tuple_ne_controlFlow t _), rfl,
        rfl⟩)
  subst hq
  exact ⟨fuel, env₂, hrun⟩

/-! ## 14. The route through `NFProg` -/

/-- The program of an output of the front: its prefix, ending in the return of its result
    variable. -/
def Out.prog {Γ : Ctxt nfDialect} (o : Out Γ) : NFProg nfDialect Γ [o.t] :=
  o.pre.plug (.ret (.cons o.res .nil))

/-- **The route through `NFProg`** of an expression: the front `impToNF` from the
    environment of names `σ`, dead-code elimination `NFProg.dce`, and the readback
    `nfToImp` from the reading `ρ`. -/
def nfRoute (sigOf : String → List NfTy → Option NfTy) {Γ : Ctxt nfDialect} (σ : NfEnv Γ)
    (ρ : RBEnv Γ) (e : ImpExpr) : Option ImpExpr :=
  (impToNF sigOf none σ e).bind fun o => nfToImp (NFProg.dce o.prog) ρ

/-- **The route through `NFProg` keeps the value.** Under `TypedCalls bi sigOf`, from an
    environment related to a valuation `V` by both `σ` and `ρ`, a run of `e` to a value is
    matched by a run, at some fuel, of its route through `NFProg` to the same value. -/
theorem nfRoute_run (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {ρ : RBEnv Γ}
    {e e' : ImpExpr} (h : nfRoute sigOf σ ρ e = some e') {env : Env} {V : Valuation Γ}
    (hσ : EnvRel σ env V) (hρ : RBRel ρ env V) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denote' bi fuel e).run env = (.val v, env')) :
    ∃ fuel' env₂, (denote' bi fuel' e').run env = (.val v, env₂) := by
  simp only [nfRoute, Option.bind_eq_some_iff] at h
  obtain ⟨o, ho, hnf⟩ := h
  obtain ⟨W, hpre, -, rfl⟩ := impToNF_sound bi sigOf hT e none σ ho fuel env V v env' hσ hrun 0
  have hp : PDenP bi 0 o.prog V = some (.cons (o.res.lookup W) .nil) :=
    PDenP_plug_ret bi 0 o.pre (.cons o.res .nil) V hpre
  have hd : PDenP bi 0 (NFProg.dce o.prog) V = some (.cons (o.res.lookup W) .nil) :=
    @NFProg.denote_dce nfDialect _ _ _ _ (nfDenote (tableOf bi)) _ _ o.prog 0 V _ hp
  exact nfToImp_denote bi 0 _ ρ hnf hρ hd

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec) in
/-- **The typed exit lowering of the route through `NFProg` simulates the source.** Under
    `TypedCalls bi sigOf` and the leaf conditions of `haxToLowCTFnT_simulates_exit`, for an
    expression `e` whose route through `NFProg` is in the fragment `exitSimOkT A R` and lowers
    to `c`, a run of `e` to a value from an environment related to a valuation by `σ` and
    `ρ`, and to a `RustState` by the placement `A`, is matched by a run of `c` to a state
    whose result slot agrees with the value. -/
theorem nfRoute_simulates_exit (bi : Builtins) (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls bi sigOf) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {ρ : RBEnv Γ} {e e' : ImpExpr} {c : LowCT}
    (h : nfRoute sigOf σ ρ e = some e') (hok : exitSimOkT A R true true e' = true)
    (hK : haxToLowCTFnT A e' = some c) {env : Env} {V : Valuation Γ}
    (hσ : EnvRel σ env V) (hρ : RBRel ρ env V) {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denote' bi fuel e).run env = (.val v, env')) (rs : RustState)
    (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeAgreesT br R (.val v) rs' := by
  obtain ⟨fuel', env₂, hrun'⟩ := nfRoute_run bi sigOf hT h hσ hρ hrun
  exact haxToLowCTFnT_simulates_exit bi N leafSpec br A R hL e' c hok hK fuel' env env₂
    (.val v) rs hrun' ⟨v, rfl⟩ hag

/-! ## 15. The entry of a function -/

/-- The context of the parameters `ps`, each a name with its type; the first parameter is the
    newest variable. -/
def entryCtx (ps : List (String × NfTy)) : Ctxt nfDialect := ps.map (·.2)

/-- The environment of names of the parameters `ps`: each name bound to its variable. -/
def entryEnv : (ps : List (String × NfTy)) → NfEnv (entryCtx ps)
  | [] => []
  | (x, t) :: ps => (x, ⟨t, Var.here⟩) :: NfEnv.mapV (fun v => Var.there v) (entryEnv ps)

/-- The reading of the parameters `ps`: each variable read as its name. -/
def entryRB : (ps : List (String × NfTy)) → RBEnv (entryCtx ps)
  | [], _, v => nomatch v
  | (x, _) :: ps, _, v => RBEnv.cons (.name x) (entryRB ps) v

/-- The source environment `env` holds, at the name of each parameter of `ps`, the encoding
    of its value in `V`. -/
def EntryVals (env : Env) : (ps : List (String × NfTy)) → Valuation (entryCtx ps) → Prop
  | [], _ => True
  | (x, t) :: _, .cons y V => env x = some (enc t y) ∧ EntryVals env _ V

/-- The source environment `env` holds, at the name of each parameter of `ps`, the encoding
    of a value of its type. -/
def EntryTyped (env : Env) (ps : List (String × NfTy)) : Prop :=
  ∀ x t, (x, t) ∈ ps → ∃ y : t.denote, env x = some (enc t y)

/-- An environment holding encodings at the parameters holds the encodings of a valuation. -/
theorem entryVals_of_typed {env : Env} :
    ∀ {ps : List (String × NfTy)}, EntryTyped env ps → ∃ V, EntryVals env ps V
  | [], _ => ⟨.nil, trivial⟩
  | (x, t) :: ps, h => by
      obtain ⟨y, hy⟩ := h x t List.mem_cons_self
      obtain ⟨V, hV⟩ := entryVals_of_typed (ps := ps)
        (fun x' t' hm => h x' t' (List.mem_cons_of_mem _ hm))
      exact ⟨.cons y V, hy, hV⟩

/-- The environment of names of the parameters is related to a valuation whose encodings
    the source environment holds. -/
theorem entryEnv_rel {env : Env} :
    ∀ {ps : List (String × NfTy)} {V : Valuation (entryCtx ps)}, EntryVals env ps V →
      EnvRel (entryEnv ps) env V
  | [], .nil, _ => by
      intro x t v hx
      simp [entryEnv, NfEnv.lookup] at hx
  | (x, t) :: ps, .cons y V, ⟨hy, hV⟩ => by
      intro x' t' v hx'
      change NfEnv.lookup ((x, ⟨t, Var.here⟩) ::
        NfEnv.mapV (fun v => Var.there v) (entryEnv ps)) x' = _ at hx'
      rw [NfEnv.lookup_cons] at hx'
      split at hx'
      · rename_i hxx
        subst hxx
        cases hx'
        exact hy
      · exact EnvRel.mapV (entryEnv_rel hV) (fun v => Var.there v) (W := .cons y V)
          (fun _ _ => rfl) x' t' v hx'

/-- The reading of the parameters is related to a valuation whose encodings the source
    environment holds. -/
theorem entryRB_rel {env : Env} :
    ∀ {ps : List (String × NfTy)} {V : Valuation (entryCtx ps)}, EntryVals env ps V →
      RBRel (entryRB ps) env V
  | [], .nil, _ => fun _ v => nomatch v
  | (x, t) :: ps, .cons y V, ⟨hy, hV⟩ => fun t' v => by
      cases v with
      | here => exact hy
      | there v => exact entryRB_rel hV t' v

/-- The route through `NFProg` of a function body with the parameters `ps`. -/
def nfRouteEntry (sigOf : String → List NfTy → Option NfTy) (ps : List (String × NfTy))
    (e : ImpExpr) : Option ImpExpr :=
  nfRoute sigOf (entryEnv ps) (entryRB ps) e

open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec) in
/-- **The typed exit lowering of the route through `NFProg` of a function body simulates
    the source**, from every source environment holding at the parameters `ps` the encodings
    of values of their types (`EntryTyped`). -/
theorem nfRouteEntry_simulates_exit (bi : Builtins)
    (sigOf : String → List NfTy → Option NfTy) (hT : TypedCalls bi sigOf) (N : Nat)
    (leafSpec : LeafSpec) (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A))
    {ps : List (String × NfTy)} {e e' : ImpExpr} {c : LowCT}
    (h : nfRouteEntry sigOf ps e = some e') (hok : exitSimOkT A R true true e' = true)
    (hK : haxToLowCTFnT A e' = some c) {env : Env} (hent : EntryTyped env ps) {fuel : Nat}
    {v : Value} {env' : Env} (hrun : (denote' bi fuel e).run env = (.val v, env'))
    (rs : RustState) (hag : envAgreesT br A env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeAgreesT br R (.val v) rs' := by
  obtain ⟨V, hV⟩ := entryVals_of_typed hent
  exact nfRoute_simulates_exit bi sigOf hT N leafSpec br A R hL h hok hK (entryEnv_rel hV)
    (entryRB_rel hV) hrun rs hag

/-! ## 16. The call typing of the `u64` table -/

/-- `TypedCalls` passes to a sub-table: a table whose every value at a typed call is a value
    of `bi`. -/
theorem TypedCalls.mono {bi bi' : Builtins} {sigOf : String → List NfTy → Option NfTy}
    (h : TypedCalls bi sigOf)
    (hsub : ∀ f as r, sigOf f as = some r → ∀ vals v, bi' f vals = some v → bi f vals = some v) :
    TypedCalls bi' sigOf :=
  fun f as r hr xs v hv => h f as r hr xs v (hsub f as r hr _ v hv)

/-- The binary integer operations of `u64` code: the wrapping addition, subtraction and
    multiplication, the bitwise conjunction, disjunction and exclusive disjunction, the shifts
    and the rotations at a width, the high word of the `128`-bit product, and the checked
    addition. -/
inductive ScalarBin where
  /-- Wrapping addition. -/
  | add
  /-- Wrapping subtraction. -/
  | sub
  /-- Wrapping multiplication. -/
  | mul
  /-- Bitwise conjunction. -/
  | and
  /-- Bitwise disjunction. -/
  | or
  /-- Bitwise exclusive disjunction. -/
  | xor
  /-- Left shift. -/
  | shl
  /-- Logical right shift. -/
  | shr
  /-- Rotation right. -/
  | rotr
  /-- Rotation left. -/
  | rotl
  /-- High word of the `128`-bit product. -/
  | mulhi
  /-- Checked addition. -/
  | addc
  deriving DecidableEq, Repr

/-- The value of a binary operation at the width `w` on the natural numbers of two words, as
    `Hax.hax64WordOps` computes it on words; `none` where Rust panics. -/
def ScalarBin.nat : ScalarBin → Nat → Nat → Nat → Option Nat
  | .add, w, x, y => some ((x + y) % 2 ^ w)
  | .sub, w, x, y => some ((x % 2 ^ w + 2 ^ w - y % 2 ^ w) % 2 ^ w)
  | .mul, w, x, y => some ((x * y) % 2 ^ w)
  | .and, w, x, y => some ((x % 2 ^ w) &&& (y % 2 ^ w))
  | .or, w, x, y => some ((x % 2 ^ w) ||| (y % 2 ^ w))
  | .xor, w, x, y => some ((x % 2 ^ w) ^^^ (y % 2 ^ w))
  | .shl, w, x, y => if y < w then some (((x % 2 ^ w) <<< y) % 2 ^ w) else none
  | .shr, w, x, y => if y < w then some ((x % 2 ^ w) >>> y) else none
  | .rotr, w, x, y => some (_root_.Hax.rotrNat w x y)
  | .rotl, w, x, y => some (_root_.Hax.rotlNat w x y)
  | .mulhi, _, x, y => some ((x * y) >>> 64)
  | .addc, _, x, y => if x + y < 2 ^ 64 then some (x + y) else none

/-- The unary integer operations of `u64` code: the complement at a width, the wrapping
    negation of a `64`-bit word, and the truncation to a width. -/
inductive ScalarUn where
  /-- Complement. -/
  | not
  /-- Wrapping negation. -/
  | neg
  /-- Truncation. -/
  | cast
  deriving DecidableEq, Repr

/-- The value of a unary operation at the width `w` on an integer, as `Hax.hax64WordOps`
    computes it. -/
def ScalarUn.val : ScalarUn → Nat → Int → Option Value
  | .not, w, a => _root_.Hax.u64UnOp a fun x => 2 ^ w - 1 - x % 2 ^ w
  | .neg, _, a => _root_.Hax.u64UnOp a fun x => (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64
  | .cast, w, a => if 0 ≤ a then some (.int (a.toNat % 2 ^ w : Nat)) else none

/-- The comparisons of `u64` code, with a Boolean result. -/
inductive ScalarCmp where
  /-- Equality. -/
  | eq
  /-- Disequality. -/
  | ne
  /-- Less than. -/
  | lt
  /-- At most. -/
  | le
  /-- Greater than. -/
  | gt
  /-- At least. -/
  | ge
  deriving DecidableEq, Repr

/-- The value of a comparison on two integers, as `Hax.hax64WordOps` computes it. -/
def ScalarCmp.val : ScalarCmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => !(a == b)
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)

/-- The binary integer calls of `u64` code with their operation and width; the width `size`
    is `64`. -/
def hax64BinTable : List (String × ScalarBin × Nat) :=
  [("wrapping_add#8", .add, 8), ("wrapping_sub#8", .sub, 8), ("wrapping_mul#8", .mul, 8),
    ("BitAnd#8", .and, 8), ("BitOr#8", .or, 8), ("BitXor#8", .xor, 8), ("Shl#8", .shl, 8),
    ("Shr#8", .shr, 8), ("rotate_right#8", .rotr, 8), ("rotate_left#8", .rotl, 8),
    ("wrapping_add#16", .add, 16), ("wrapping_sub#16", .sub, 16),
    ("wrapping_mul#16", .mul, 16), ("BitAnd#16", .and, 16), ("BitOr#16", .or, 16),
    ("BitXor#16", .xor, 16), ("Shl#16", .shl, 16), ("Shr#16", .shr, 16),
    ("rotate_right#16", .rotr, 16), ("rotate_left#16", .rotl, 16),
    ("wrapping_add#32", .add, 32), ("wrapping_sub#32", .sub, 32),
    ("wrapping_mul#32", .mul, 32), ("BitAnd#32", .and, 32), ("BitOr#32", .or, 32),
    ("BitXor#32", .xor, 32), ("Shl#32", .shl, 32), ("Shr#32", .shr, 32),
    ("rotate_right#32", .rotr, 32), ("rotate_left#32", .rotl, 32),
    ("wrapping_add#64", .add, 64), ("wrapping_sub#64", .sub, 64),
    ("wrapping_mul#64", .mul, 64), ("BitAnd#64", .and, 64), ("BitOr#64", .or, 64),
    ("BitXor#64", .xor, 64), ("Shl#64", .shl, 64), ("Shr#64", .shr, 64),
    ("rotate_right#64", .rotr, 64), ("rotate_left#64", .rotl, 64),
    ("wrapping_add#size", .add, 64), ("wrapping_sub#size", .sub, 64),
    ("wrapping_mul#size", .mul, 64), ("BitAnd#size", .and, 64), ("BitOr#size", .or, 64),
    ("BitXor#size", .xor, 64), ("Shl#size", .shl, 64), ("Shr#size", .shr, 64),
    ("rotate_right#size", .rotr, 64), ("rotate_left#size", .rotl, 64),
    ("shl#64", .shl, 64), ("shr#64", .shr, 64), ("mulhi#64", .mulhi, 64), ("Add", .addc, 64)]

/-- The unary integer calls of `u64` code with their operation and width. -/
def hax64UnTable : List (String × ScalarUn × Nat) :=
  [("Not#8", .not, 8), ("Not#16", .not, 16), ("Not#32", .not, 32), ("Not#64", .not, 64),
    ("Not#size", .not, 64), ("wrapping_neg#64", .neg, 64), ("cast#8", .cast, 8),
    ("cast#16", .cast, 16), ("cast#32", .cast, 32), ("cast#64", .cast, 64),
    ("cast#size", .cast, 64)]

/-- The comparison calls of `u64` code with their comparison. -/
def hax64CmpTable : List (String × ScalarCmp) :=
  [("Eq", .eq), ("eq", .eq), ("Ne", .ne), ("ne", .ne), ("Lt", .lt), ("lt", .lt),
    ("Le", .le), ("le", .le), ("Gt", .gt), ("gt", .gt), ("Ge", .ge), ("ge", .ge)]

/-- The operation and the width of a binary integer call. -/
def scalarBinOf (f : String) : Option (ScalarBin × Nat) :=
  (hax64BinTable.find? (·.1 == f)).map (·.2)

/-- The operation and the width of a unary integer call. -/
def scalarUnOf (f : String) : Option (ScalarUn × Nat) :=
  (hax64UnTable.find? (·.1 == f)).map (·.2)

/-- The comparison of a comparison call. -/
def scalarCmpOf (f : String) : Option ScalarCmp :=
  (hax64CmpTable.find? (·.1 == f)).map (·.2)

/-- The scalar calls of `u64` code the route through `NFProg` types: the binary and unary
    integer calls and the comparisons. -/
def hax64NFScalar : List String :=
  hax64BinTable.map (·.1) ++ hax64UnTable.map (·.1) ++ hax64CmpTable.map (·.1)

/-- The types whose values encode as integers: `int` and the `64`-bit word. -/
def hax64NFWordTy : NfTy → Bool
  | .int => true
  | .word 64 => true
  | _ => false

/-- The call typing of `u64` code on integer arrays of a fixed length `n`, at an index of a
    `hax64NFWordTy` type: `index` of an array is an integer; `array_update` of an array with
    a value of a `hax64NFWordTy` type is an array of the same length. -/
def hax64SigOfArr (f : String) (as : List NfTy) : Option NfTy :=
  match f, as with
  | "index", [.arr _ .int, ti] => if hax64NFWordTy ti then some .int else none
  | "array_update", [.arr n .int, ti, t] =>
      if hax64NFWordTy ti && hax64NFWordTy t then some (.arr n .int) else none
  | _, _ => none

/-- The call typing of the scalar calls of `u64` code on operands of `hax64NFWordTy` types: a
    binary or unary integer call has a `64`-bit word result, a comparison a bit. -/
def hax64ScalarSig (f : String) : List NfTy → Option NfTy
  | [a, b] =>
      if hax64NFWordTy a && hax64NFWordTy b then
        if (scalarBinOf f).isSome then some (.word 64)
        else if (scalarCmpOf f).isSome then some .bit
        else none
      else none
  | [a] => if hax64NFWordTy a && (scalarUnOf f).isSome then some (.word 64) else none
  | _ => none

/-- **The call typing of `u64` code**: a scalar call by `hax64ScalarSig`; at an index of a
    `hax64NFWordTy` type, `index` of an integer slice is an integer and `array_update` of an
    integer slice with a value of a `hax64NFWordTy` type is an integer slice; on
    fixed-length arrays, `hax64SigOfArr`. -/
def hax64SigOf (f : String) (as : List NfTy) : Option NfTy :=
  match hax64ScalarSig f as with
  | some r => some r
  | none =>
    match f, as with
    | "index", [.slice .int, ti] => if hax64NFWordTy ti then some .int else none
    | "array_update", [.slice .int, ti, t] =>
        if hax64NFWordTy ti && hax64NFWordTy t then some (.slice .int) else none
    | _, _ => hax64SigOfArr f as

/-- The encoding of a value of a `hax64NFWordTy` type is an integer. -/
theorem hax64NFWordTy_enc {t : NfTy} (ht : hax64NFWordTy t = true) (x : t.denote) :
    ∃ z : Int, enc t x = .int z := by
  match t, ht with
  | .int, _ => exact ⟨x, rfl⟩
  | .word 64, _ => exact ⟨_, rfl⟩

/-- A value of `u64BinOp` is an integer. -/
theorem u64BinOp_int {a b : Int} {g : Nat → Nat → Option Nat} {v : Value}
    (h : _root_.Hax.u64BinOp a b g = some v) : ∃ z : Int, v = .int z := by
  unfold _root_.Hax.u64BinOp at h
  split at h
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨r, -, rfl⟩ := h
    exact ⟨_, rfl⟩
  · cases h

/-- `<|> none` is the identity on `Option Value`. -/
theorem orElse_none_eq (x : Option Value) : (x <|> none) = x := by
  cases x <;> rfl

/-- An entry a lookup by name finds in a table is a member of the table. -/
theorem mem_of_find?_map {α : Type} {L : List (String × α)} {f : String} {p : α}
    (h : (L.find? (·.1 == f)).map (·.2) = some p) : (f, p) ∈ L := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have h1 := List.find?_some he
  simp only [beq_iff_eq] at h1
  subst h1
  exact List.mem_of_find?_eq_some he

/-- The binary integer calls of the table compute `ScalarBin.nat` by `u64BinOp`. -/
theorem hax64BinTable_sem :
    ∀ e ∈ hax64BinTable, ∀ a b : Int, _root_.Hax.hax64Builtins e.1 [.int a, .int b] =
      (_root_.Hax.u64BinOp a b (e.2.1.nat e.2.2) <|> none) := by
  simp only [hax64BinTable, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> intro a b <;> rfl

/-- The unary integer calls of the table compute `ScalarUn.val`. -/
theorem hax64UnTable_sem :
    ∀ e ∈ hax64UnTable, ∀ a : Int,
      _root_.Hax.hax64Builtins e.1 [.int a] = (e.2.1.val e.2.2 a <|> none) := by
  simp only [hax64UnTable, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> intro a <;> rfl

/-- The comparison calls of the table compute `ScalarCmp.val`. -/
theorem hax64CmpTable_sem :
    ∀ e ∈ hax64CmpTable, ∀ a b : Int,
      _root_.Hax.hax64Builtins e.1 [.int a, .int b] = (some (.bool (e.2.val a b)) <|> none) := by
  simp only [hax64CmpTable, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> intro a b <;> rfl

/-- The widths of the binary integer calls are at most `64`. -/
theorem hax64BinTable_w : ∀ e ∈ hax64BinTable, e.2.2 ≤ 64 := by decide

/-- The widths of the unary integer calls are at most `64`. -/
theorem hax64UnTable_w : ∀ e ∈ hax64UnTable, e.2.2 ≤ 64 := by decide

/-- The scalar calls are none of the array constructors and array comparisons. -/
theorem hax64NFScalar_ne_arr {f : String} (hf : f ∈ hax64NFScalar) :
    f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" := by
  have h : ∀ g ∈ hax64NFScalar,
      g ≠ "array_lit" ∧ g ≠ "repeat" ∧ g ≠ "eq#arr" ∧ g ≠ "ne#arr" := by decide
  exact h f hf

/-- A value of `u64BinOp` is the integer of a value of the operation on two words. -/
theorem u64BinOp_some {a b : Int} {g : Nat → Nat → Option Nat} {v : Value}
    (h : _root_.Hax.u64BinOp a b g = some v) :
    ∃ r : Nat, g a.toNat b.toNat = some r ∧ v = .int r ∧ a = a.toNat ∧ a.toNat < 2 ^ 64 ∧
      b = b.toNat ∧ b.toNat < 2 ^ 64 := by
  unfold _root_.Hax.u64BinOp at h
  split at h
  · rename_i hc
    rcases hg : g a.toNat b.toNat with _ | r
    · simp [hg] at h
    · rw [hg] at h
      obtain rfl := Option.some.inj h
      exact ⟨r, rfl, rfl, by omega, by omega, by omega, by omega⟩
  · cases h

/-- A value of a binary integer operation at a width of at most `64` on two words is below
    `2 ^ 64`. -/
theorem ScalarBin.nat_lt (o : ScalarBin) {w x y r : Nat} (hw : w ≤ 64) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (h : o.nat w x y = some r) : r < 2 ^ 64 := by
  have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
  have hm : ∀ n, n % 2 ^ w < 2 ^ 64 := fun n =>
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hp
  cases o <;> simp only [ScalarBin.nat] at h
  case add | sub | mul => obtain rfl := Option.some.inj h; exact hm _
  case and => obtain rfl := Option.some.inj h; exact lt_of_le_of_lt Nat.and_le_left (hm x)
  case or => obtain rfl := Option.some.inj h; exact Nat.or_lt_two_pow (hm x) (hm y)
  case xor => obtain rfl := Option.some.inj h; exact Nat.xor_lt_two_pow (hm x) (hm y)
  case shl =>
    split at h
    · obtain rfl := Option.some.inj h; exact hm _
    · cases h
  case shr =>
    split at h
    · obtain rfl := Option.some.inj h
      exact lt_of_le_of_lt (Nat.shiftRight_le _ _) (hm x)
    · cases h
  case rotr | rotl => obtain rfl := Option.some.inj h; exact hm _
  case mulhi =>
    obtain rfl := Option.some.inj h
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity)]
    exact Nat.mul_lt_mul'' hx hy
  case addc =>
    split at h
    · obtain rfl := Option.some.inj h; assumption
    · cases h

/-- A value of a unary integer operation at a width of at most `64` is the integer of a
    natural number below `2 ^ 64`. -/
theorem ScalarUn.val_int (o : ScalarUn) {w : Nat} (hw : w ≤ 64) {a : Int} {v : Value}
    (h : o.val w a = some v) : ∃ r : Nat, v = .int r ∧ r < 2 ^ 64 := by
  have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
  have h0 : 0 < 2 ^ w := by positivity
  cases o <;> simp only [ScalarUn.val, _root_.Hax.u64UnOp] at h <;> split at h
  all_goals cases h
  · exact ⟨_, rfl, by omega⟩
  · exact ⟨_, rfl, Nat.mod_lt _ (by positivity)⟩
  · exact ⟨_, rfl, lt_of_lt_of_le (Nat.mod_lt _ h0) hp⟩

/-- A natural number below `2 ^ 64` decodes as a `64`-bit word. -/
theorem dec_word64_nat {r : Nat} (hr : r < 2 ^ 64) :
    ∃ y, dec (.word 64) (.int r) = some y ∧ Value.int r = enc (.word 64) y := by
  have hr' : (r : Int) < 2 ^ 64 := by exact_mod_cast hr
  refine ⟨BitVec.ofNat 64 r, ?_, ?_⟩
  · simp only [dec, Int.natCast_nonneg, hr', and_self, if_true, Int.toNat_natCast]
  · simp only [enc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]

/-- **The scalar call typing is sound for `Hax.hax64Builtins`.** -/
theorem hax64ScalarSig_typed (f : String) (as : List NfTy) (r : NfTy)
    (hr : hax64ScalarSig f as = some r) (xs : HVector NfTy.denote as) (v : Value)
    (hv : _root_.Hax.hax64Builtins f (encAll as xs) = some v) :
    ∃ y, dec r v = some y ∧ v = enc r y := by
  match as, xs, hr with
  | [ta, tb], .cons x₁ (.cons x₂ .nil), hr =>
    simp only [hax64ScalarSig] at hr
    split at hr
    · rename_i hab
      simp only [Bool.and_eq_true] at hab
      obtain ⟨a, ha⟩ := hax64NFWordTy_enc hab.1 x₁
      obtain ⟨b, hb⟩ := hax64NFWordTy_enc hab.2 x₂
      change _root_.Hax.hax64Builtins f [enc ta x₁, enc tb x₂] = some v at hv
      rw [ha, hb] at hv
      split at hr
      · rename_i hbin
        cases hr
        obtain ⟨⟨o, w⟩, hp⟩ := Option.isSome_iff_exists.mp hbin
        have hmem := mem_of_find?_map hp
        rw [hax64BinTable_sem _ hmem, orElse_none_eq] at hv
        obtain ⟨r', hr', rfl, -, hax, -, hbx⟩ := u64BinOp_some hv
        exact dec_word64_nat (ScalarBin.nat_lt o (hax64BinTable_w _ hmem) hax hbx hr')
      · split at hr
        · rename_i hcmp
          cases hr
          obtain ⟨c, hp⟩ := Option.isSome_iff_exists.mp hcmp
          rw [hax64CmpTable_sem _ (mem_of_find?_map hp), orElse_none_eq] at hv
          cases hv
          exact ⟨_, rfl, rfl⟩
        · cases hr
    · cases hr
  | [ta], .cons x₁ .nil, hr =>
    simp only [hax64ScalarSig] at hr
    split at hr
    · rename_i hab
      cases hr
      simp only [Bool.and_eq_true] at hab
      obtain ⟨a, ha⟩ := hax64NFWordTy_enc hab.1 x₁
      change _root_.Hax.hax64Builtins f [enc ta x₁] = some v at hv
      rw [ha] at hv
      obtain ⟨⟨o, w⟩, hp⟩ := Option.isSome_iff_exists.mp hab.2
      have hmem := mem_of_find?_map hp
      rw [hax64UnTable_sem _ hmem, orElse_none_eq] at hv
      obtain ⟨r', rfl, hr'⟩ := ScalarUn.val_int o (hax64UnTable_w _ hmem) hv
      exact dec_word64_nat hr'
    · cases hr
  | [], _, hr => simp [hax64ScalarSig] at hr
  | _ :: _ :: _ :: _, _, hr => simp [hax64ScalarSig] at hr

/-- The calls `hax64ScalarSig` types are the scalar calls of `hax64NFScalar`. -/
theorem hax64ScalarSig_name {f : String} {as : List NfTy} {r : NfTy}
    (h : hax64ScalarSig f as = some r) : f ∈ hax64NFScalar := by
  simp only [hax64NFScalar, List.mem_append, List.mem_map]
  unfold hax64ScalarSig at h
  split at h
  · split at h
    · split at h
      · rename_i hbin
        obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hbin
        exact Or.inl (Or.inl ⟨_, mem_of_find?_map hp, rfl⟩)
      · split at h
        · rename_i hcmp
          obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hcmp
          exact Or.inr ⟨_, mem_of_find?_map hp, rfl⟩
        · cases h
    · cases h
  · split at h
    · rename_i hun
      simp only [Bool.and_eq_true] at hun
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hun.2
      exact Or.inl (Or.inr ⟨_, mem_of_find?_map hp, rfl⟩)
    · cases h
  · cases h

/-- A list of integers decodes as an integer slice. -/
theorem dec_slice_int : ∀ (vs : List Value), (∀ v ∈ vs, ∃ z : Int, v = .int z) →
    ∃ ys, dec (.slice .int) (.array vs) = some ys ∧ Value.array vs = enc (.slice .int) ys
  | [], _ => ⟨[], rfl, rfl⟩
  | v :: vs, h => by
      obtain ⟨z, rfl⟩ := h v List.mem_cons_self
      obtain ⟨ys, hd, he⟩ := dec_slice_int vs fun w hw => h w (List.mem_cons_of_mem _ hw)
      refine ⟨z :: ys, ?_, ?_⟩
      · change (Value.int z :: vs).mapM (dec .int) = some (z :: ys)
        change vs.mapM (dec .int) = some ys at hd
        simp [List.mapM_cons, hd, dec]
      · change Value.array vs = Value.array (ys.map (enc .int)) at he
        simp only [Value.array.injEq] at he
        change Value.array (Value.int z :: vs) = Value.array ((z :: ys).map (enc .int))
        rw [List.map_cons, ← he]
        rfl

/-- The calls `hax64SigOf` types are the scalar calls of `hax64NFScalar`, `index` and
    `array_update`. -/
theorem hax64SigOf_name {f : String} {as : List NfTy} {r : NfTy}
    (h : hax64SigOf f as = some r) : f ∈ hax64NFScalar ∨ f = "index" ∨ f = "array_update" := by
  unfold hax64SigOf at h
  split at h
  · rename_i hs
    exact Or.inl (hax64ScalarSig_name hs)
  · split at h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · unfold hax64SigOfArr at h
      split at h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · cases h

/-- A list of `n` integers decodes as an integer array of length `n`. -/
theorem dec_arr_int {n : Nat} (vs : List Value) (hvs : ∀ v ∈ vs, ∃ z : Int, v = .int z)
    (hn : vs.length = n) :
    ∃ f, dec (.arr n .int) (.array vs) = some f ∧ Value.array vs = enc (.arr n .int) f := by
  obtain ⟨ys, hd, he⟩ := dec_slice_int vs hvs
  change vs.mapM (dec .int) = some ys at hd
  change Value.array vs = Value.array (ys.map (enc .int)) at he
  simp only [Value.array.injEq] at he
  have hl : ys.length = n := by rw [← hn, he, List.length_map]
  subst hl
  refine ⟨fun i => ys[i.1], ?_, ?_⟩
  · simp only [dec, hd, Option.bind_some, dite_true]
  · simp only [enc, he, Value.array.injEq]
    apply List.ext_getElem <;> simp

/-- The call typing of `u64` code on fixed-length integer arrays is sound for
    `Hax.hax64Builtins`. -/
theorem hax64Builtins_typedCallsArr (f : String) (as : List NfTy) (r : NfTy)
    (hr : hax64SigOfArr f as = some r) (xs : HVector NfTy.denote as) (v : Value)
    (hv : _root_.Hax.hax64Builtins f (encAll as xs) = some v) :
    ∃ y, dec r v = some y ∧ v = enc r y := by
  unfold hax64SigOfArr at hr
  split at hr
  · rename_i n ti
    split at hr
    · rename_i hti
      simp only [Option.some.injEq] at hr
      subst hr
      match xs with
      | .cons g (.cons i .nil) =>
        obtain ⟨zi, hzi⟩ := hax64NFWordTy_enc hti i
        change (_root_.Hax.hax64WordOps "index" [enc (.arr n .int) g, enc ti i] <|>
          _root_.Hax.widthArrayOps "index" [enc (.arr n .int) g, enc ti i]) = some v at hv
        rw [hzi] at hv
        change (_root_.Hax.hax64WordOps "index"
            [.array (List.ofFn fun k => enc .int (g k)), .int zi] <|>
          _root_.Hax.widthArrayOps "index"
            [.array (List.ofFn fun k => enc .int (g k)), .int zi]) = some v at hv
        rw [_root_.Hax.hax64WordOps_index] at hv
        change _root_.Hax.widthArrayOps "index"
          [.array (List.ofFn fun k => enc .int (g k)), .int zi] = some v at hv
        rw [_root_.Hax.widthArrayOps_index_int] at hv
        split at hv
        · rcases hy : (List.ofFn fun k => enc .int (g k))[zi.toNat]? with _ | y
          · rw [hy] at hv; cases hv
          · rw [hy] at hv
            obtain ⟨k, hk⟩ := List.mem_ofFn.mp (List.mem_of_getElem? hy)
            subst hk
            change some (Value.int (g k)) = some v at hv
            cases hv
            exact ⟨g k, rfl, rfl⟩
        · cases hv
    · cases hr
  · rename_i n ti t
    split at hr
    · rename_i ht
      simp only [Bool.and_eq_true] at ht
      simp only [Option.some.injEq] at hr
      subst hr
      match xs with
      | .cons g (.cons i (.cons x .nil)) =>
        obtain ⟨zi, hzi⟩ := hax64NFWordTy_enc ht.1 i
        obtain ⟨z, hz⟩ := hax64NFWordTy_enc ht.2 x
        change (_root_.Hax.hax64WordOps "array_update"
            [.array (List.ofFn fun k => enc .int (g k)), enc ti i, enc t x] <|>
          _root_.Hax.widthArrayOps "array_update"
            [.array (List.ofFn fun k => enc .int (g k)), enc ti i, enc t x]) = some v at hv
        rw [hzi, _root_.Hax.hax64WordOps_array_update] at hv
        change _root_.Hax.widthArrayOps "array_update"
          [.array (List.ofFn fun k => enc .int (g k)), .int zi, enc t x] = some v at hv
        rw [_root_.Hax.widthArrayOps_array_update_int, hz] at hv
        split at hv
        · cases hv
          refine dec_arr_int _ (fun w hw => ?_) (by simp)
          rcases List.mem_or_eq_of_mem_set hw with hw | rfl
          · obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw
            exact ⟨g k, rfl⟩
          · exact ⟨z, rfl⟩
        · cases hv
    · cases hr
  · cases hr

/-- **The call typing of `u64` code is sound for `Hax.hax64Builtins`.** -/
theorem hax64Builtins_typedCalls : TypedCalls _root_.Hax.hax64Builtins hax64SigOf := by
  intro f as r hr xs v hv
  unfold hax64SigOf at hr
  split at hr
  · rename_i hs
    cases hr
    exact hax64ScalarSig_typed f as _ hs xs v hv
  · split at hr
    · rename_i ti _
      split at hr
      · rename_i hti
        simp only [Option.some.injEq] at hr
        subst hr
        match xs with
        | .cons ys (.cons i .nil) =>
          obtain ⟨zi, hzi⟩ := hax64NFWordTy_enc hti i
          change (_root_.Hax.hax64WordOps "index" [.array (ys.map (enc .int)), enc ti i] <|>
            _root_.Hax.widthArrayOps "index" [.array (ys.map (enc .int)), enc ti i]) =
              some v at hv
          rw [hzi, _root_.Hax.hax64WordOps_index] at hv
          change _root_.Hax.widthArrayOps "index" [.array (ys.map (enc .int)), .int zi] =
            some v at hv
          rw [_root_.Hax.widthArrayOps_index_int] at hv
          split at hv
          · rw [List.getElem?_map] at hv
            rcases hy : ys[zi.toNat]? with _ | y
            · rw [hy] at hv; cases hv
            · rw [hy] at hv
              change some (Value.int y) = some v at hv
              cases hv
              exact ⟨y, rfl, rfl⟩
          · cases hv
      · cases hr
    · split at hr
      · rename_i ti t _ ht
        simp only [Bool.and_eq_true] at ht
        simp only [Option.some.injEq] at hr
        subst hr
        match xs with
        | .cons ys (.cons i (.cons x .nil)) =>
          obtain ⟨zi, hzi⟩ := hax64NFWordTy_enc ht.1 i
          obtain ⟨z, hz⟩ := hax64NFWordTy_enc ht.2 x
          change (_root_.Hax.hax64WordOps "array_update"
              [.array (ys.map (enc .int)), enc ti i, enc t x] <|>
            _root_.Hax.widthArrayOps "array_update"
              [.array (ys.map (enc .int)), enc ti i, enc t x]) = some v at hv
          rw [hzi, _root_.Hax.hax64WordOps_array_update] at hv
          change _root_.Hax.widthArrayOps "array_update"
            [.array (ys.map (enc .int)), .int zi, enc t x] = some v at hv
          rw [_root_.Hax.widthArrayOps_array_update_int, hz] at hv
          have hints : ∀ w ∈ ys.map (enc .int), ∃ z : Int, w = .int z := by
            intro w hw
            rw [List.mem_map] at hw
            obtain ⟨y, -, rfl⟩ := hw
            exact ⟨y, rfl⟩
          split at hv
          · cases hv
            refine dec_slice_int _ fun w hw => ?_
            rcases List.mem_or_eq_of_mem_set hw with hw | rfl
            · exact hints w hw
            · exact ⟨z, rfl⟩
          · cases hv
      · cases hr
    · exact hax64Builtins_typedCallsArr f as r hr xs v hv

end CatCrypt.Crypto.Hax.ImpToNF
