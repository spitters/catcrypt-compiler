/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.BignumExec
public import CatCrypt.Crypto.Jasmin.BignumExec
public meta import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import CatCrypt.Crypto.Jasmin.JasminCoqSemMirror
public import Lean


@[expose] public section
set_option autoImplicit false

/-!
# Reflect Lean value-level programs to `List InstrR` (Jasmin bignum bodies)

Modeled after `CatCrypt.Crypto.Jasmin.LowCTReflect`'s `reifyLowCT%`
elaborator (Lean ⇒ `LowCT` AST).  This file does the analogous lift
for the lower Jasmin layer:

```
Lean value-level f : (BitVec 64)^k → (BitVec 64)^k
        |
        |   reifyInstrR%
        v
List InstrR  (= the body of a `mpn_*` kernel)
```

## MVP scope (2026-05-28)

The MVP supports the **straight-line ADX idiom** of `MpnAddMul1AdxPrototype`:

* `mulx a b : BitVec 64 × BitVec 64` — emits `Copn [hiName, loName] := MULX(a, b)`
* `adcx dst src cf_in : BitVec 64 × BitVec 64` — emits `Copn [cfName, rName] := ADCX(...)`
* `adox dst src of_in : BitVec 64 × BitVec 64` — emits `Copn [ofName, rName] := ADOX(...)`

Pair-returning ops use the convention:

```lean
let p := mulx a b
let hi := p.1
let lo := p.2
...
```

The reifier reads `p`'s subsequent `.1` / `.2` projection lets to learn the
user-chosen names for each of the op's outputs, then emits ONE `Copn` with
the right 2-LVal bundle.  This mirrors the real ADX kernel emit shape exactly.

## What's NOT yet in scope

* Loop reflection (`Cfor`) — deferred to next batch
* Conditional reflection (`Cif`)
* `Ccall` composition across reified kernels
* Memory load/store reification (`Pload` / `Lmem` LVals)
* Single-LVal `Cassgn` for tail bindings

The MVP demonstrates the **infrastructure** — the elaborator walks an Expr,
binds parameter and let-binders, matches known op heads, and emits a
correctly-shaped `List InstrR`.  Adding `Cfor` etc. is mechanical follow-up.

## Authoring convention

The user writes:

```lean
def addmulStepLean
    (acc a b : BitVec 64) (cfIn ofIn : BitVec 64) :
    BitVec 64 × BitVec 64 × BitVec 64 :=
  let pm := InstrRReflect.mulx a b
  let hi := pm.1
  let lo := pm.2
  let pa := InstrRReflect.adcx acc lo cfIn
  let cf := pa.1
  let acc' := pa.2
  let po := InstrRReflect.adox acc' hi ofIn
  let of := po.1
  let acc'' := po.2
  (cf, of, acc'')
```

and then:

```lean
def addmulStepReified : List InstrR := reifyInstrR% addmulStepLean
```

The reifier returns the actual `List InstrR` body suitable for feeding into
`bignumExecFuel`.
-/

namespace CatCrypt.Crypto.Jasmin.InstrRReflect

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open Lean Meta Elab

/-! ## §1. Surface ops (the "known heads" the reifier intercepts)

These are **value-level Lean functions** that mirror real x86 BMI2 / x86-64
instructions.  Crucially, they delegate to the *same* primitives that
`BignumExec.execInstr` uses for the matching `Oasm` arm — this makes the
correspondence theorem (§Examples) a straightforward `rfl` / structural
unfold:

| Surface       | `BignumExec` primitive | `Oasm` arm |
|---------------|------------------------|------------|
| `mulx a b`    | `BignumExec.mulx a b`  | `"MULX"`   |
| `adcx d s c`  | `addCarryIn d s c`     | `"ADCX"`   |
| `adox d s o`  | `addCarryIn d s o`     | `"ADOX"`   |

ADCX and ADOX share the same arithmetic; they differ only in which carry
flag the CPU updates (CF vs OF).  At the `BitVec` arithmetic level both are
`addCarryIn` (matching the Intel SDM and `BignumExec.execInstr`'s `"ADCX"`/
`"ADOX"` arms which both call `addCarryIn`). -/

/-- `MULX a b = (hi, lo)` with `hi.toNat <<< 64 ||| lo.toNat = a.toNat * b.toNat`.
    Mirrors `BignumExec.mulx`.  No flag side-effects.

    We keep `mulx` a plain `def` (not `@[irreducible]`) so that `decide` /
    `native_decide` / kernel reduction can evaluate it on concrete inputs
    (which is what the demonstrator's correspondence proof uses).  The
    elaborator's `whnf` does NOT unfold a plain non-reducible `def`, so
    `getAppFnArgs` still recovers the `mulx` head name reliably. -/
def mulx (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  BignumExec.mulx a b

/-- `ADCX dst src cf_in = (cf_out, r)` where `r = dst + src + (cf_in & 1)` and
    `cf_out` is the carry-out (0 or 1).  Mirrors `BignumExec.addCarryIn`.
    BMI2 ADCX only updates CF (no other flags). -/
def adcx (dst src cf_in : BitVec 64) : BitVec 64 × BitVec 64 :=
  BignumExec.addCarryIn dst src cf_in

/-- `ADOX dst src of_in = (of_out, r)` where `r = dst + src + (of_in & 1)` and
    `of_out` is the carry-out.  Same arithmetic as `adcx` (BMI2 ADOX only
    differs in updating OF instead of CF). -/
def adox (dst src of_in : BitVec 64) : BitVec 64 × BitVec 64 :=
  BignumExec.addCarryIn dst src of_in

/-- Correspondence unfold lemmas — these are the bridge between the surface
    ops (`mulx`/`adcx`/`adox`) and the `BignumExec` primitives that the
    `Oasm "MULX"/"ADCX"/"ADOX"` arms of `execInstr` call.  Tagged `@[simp]`
    so they can be folded into the correspondence proof. -/
@[simp] theorem mulx_eq (a b : BitVec 64) :
    mulx a b = BignumExec.mulx a b := rfl

@[simp] theorem adcx_eq (dst src cf_in : BitVec 64) :
    adcx dst src cf_in = BignumExec.addCarryIn dst src cf_in := rfl

@[simp] theorem adox_eq (dst src of_in : BitVec 64) :
    adox dst src of_in = BignumExec.addCarryIn dst src of_in := rfl

/-! ## §2. Known-op table

The reifier matches each `let p := <head> args ...` binding against this
table.  Each entry records:

* `head` — the Lean `Name` of the axiom
* `asm`  — the `Oasm` instruction name (`"MULX"`, `"ADCX"`, `"ADOX"`)
* `arity` — number of arguments (used to validate full application)
* `outs`  — number of `LVal`s in the Copn bundle (always 2 for the MVP)

§2–§7 are Lean metaprogramming (the op table, the `ToExpr` instances, the
`MetaM` walker and the `reifyInstrR%` elaborator) and sit in a
`meta section`; the value-level surface (§1, §8) stays outside it.
-/

meta section

/-- Spec of a known pair-returning ADX op. -/
structure KnownPairOp where
  head  : Name
  asm   : String
  arity : Nat
  outs  : Nat
  deriving Inhabited

/-- The known-op table.  Extending this is mechanical: add an entry + an axiom. -/
def knownPairOps : List KnownPairOp :=
  [ { head := ``mulx, asm := "MULX", arity := 2, outs := 2 }
  , { head := ``adcx, asm := "ADCX", arity := 3, outs := 2 }
  , { head := ``adox, asm := "ADOX", arity := 3, outs := 2 } ]

/-- Lookup a head name in the known-op table. -/
def lookupOp? (n : Name) : Option KnownPairOp :=
  knownPairOps.find? (·.head == n)

/-! ## §3. `ToExpr` instances for the JasminAST.

The elaborator needs to splice a `List InstrR` value back into a Lean term.
We derive the `ToExpr` instances for the relevant subset.  These are
mechanically derivable for everything except the `BitVec`/`Int` literals
that already have library instances. -/

deriving instance Lean.ToExpr for WSize
deriving instance Lean.ToExpr for SType
deriving instance Lean.ToExpr for VarInfo
deriving instance Lean.ToExpr for Var
deriving instance Lean.ToExpr for VarI
deriving instance Lean.ToExpr for GVar
deriving instance Lean.ToExpr for ArrAccess
deriving instance Lean.ToExpr for SignExtend
deriving instance Lean.ToExpr for SOp1
deriving instance Lean.ToExpr for SOp2
deriving instance Lean.ToExpr for OpN
deriving instance Lean.ToExpr for AssgnTag
deriving instance Lean.ToExpr for InlineInfo
deriving instance Lean.ToExpr for AsmOp
deriving instance Lean.ToExpr for SOpn
deriving instance Lean.ToExpr for FunName
deriving instance Lean.ToExpr for LoopDir
deriving instance Lean.ToExpr for Range
deriving instance Lean.ToExpr for PExpr
deriving instance Lean.ToExpr for LVal
deriving instance Lean.ToExpr for InstrR

/-! ## §4. Small builders mirroring `Mpn.Mul1Prototype.{vr, pv}`

We replicate these locally (not `import`ed) to keep `InstrRReflect`
dependency-light: only `BignumExec`. -/

/-- A `u64` `Var`. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- `Pvar` reading register `s` (local, not global). -/
def pv (s : String) : PExpr :=
  .Pvar { gv := { var := vr s }, gs := false }

/-- Lvar writing register `s`. -/
def lv (s : String) : LVal := .Lvar { var := vr s }

/-! ## §5. Reifier core

The reifier walks the let-chain inside a lambda-bound function.  It tracks a
small "naming environment" mapping each FVarId to its emitted register
string.  Function parameters get their `userName` as the register name; let-
binders get *their* `userName`; and projections of a pair-binder are folded
into the producing Copn's LVal list. -/

/-- Naming environment: FVarId ↦ register-name string. -/
abbrev RegEnv := Std.HashMap FVarId String

/-- Look up the register name associated with a Lean fvar.  Throws an
    elaboration error if the fvar is not bound (i.e., not in our env). -/
def lookupVar (env : RegEnv) (fv : FVarId) : MetaM String := do
  match env[fv]? with
  | some s => pure s
  | none   =>
      let n ← fv.getUserName
      throwError "InstrRReflect: free variable {n} not in scope (not a known register)"

/-- If `e` is an `FVar`, return the name from `env`.  Otherwise fail.
    No `whnf`: known-op argument positions are always already bound fvars
    (lambda parameters or let-binders), and unfolding would lose names. -/
def reifyAtomVar (env : RegEnv) (e : Expr) : MetaM String := do
  unless e.isFVar do
    throwError "InstrRReflect: expected a bound variable, got:{indentExpr e}"
  lookupVar env e.fvarId!

/-- Recognize `Prod.fst <inst> <fv>` or `Prod.snd <inst> <fv>` and return
    `(side, fv)` where `side = 0` for `.fst` and `side = 1` for `.snd`.

    Two surface shapes are accepted:
    1. `Expr.proj ``Prod 0 p` / `Expr.proj ``Prod 1 p` — the projection
       form Lean lowers `p.1`/`p.2` to.  This is the form we actually see
       in 4.29 (verified empirically via the build error pre-fix).
    2. `Prod.fst α β p` — the explicit `App App App Const` form (kept as a
       fallback for surface shapes that haven't been lowered to `.proj`).

    No `whnf` is called: unfolding might erase the constant name we need
    (and projection targets are always already bound fvars after the
    `letTelescope` walk in `reifyBody`).
-/
def matchProj? (e : Expr) : MetaM (Option (Nat × FVarId)) := do
  match e with
  | .proj ``Prod 0 inner =>
      if inner.isFVar then return some (0, inner.fvarId!) else return none
  | .proj ``Prod 1 inner =>
      if inner.isFVar then return some (1, inner.fvarId!) else return none
  | _ =>
    match e.getAppFnArgs with
    | (``Prod.fst, args) =>
        if args.size ≥ 3 then
          let arg := args[2]!
          if arg.isFVar then return some (0, arg.fvarId!) else return none
        else
          return none
    | (``Prod.snd, args) =>
        if args.size ≥ 3 then
          let arg := args[2]!
          if arg.isFVar then return some (1, arg.fvarId!) else return none
        else
          return none
    | _ => pure none

/-- Match the value of a let-binder against the known-op table.  Returns
    `(opSpec, argExprs)` for a fully-applied known head, or `none` otherwise.

    We deliberately do **not** call `whnf` on `v` before pattern-matching:
    `whnf` would unfold a plain `def` like `mulx` into its body (here,
    `BignumExec.mulx a b`), losing the head name we want to dispatch on.
    The user's surface code is always *syntactically* `mulx a b`, so a
    direct `getAppFnArgs` finds the head.  -/
def matchKnownOp? (v : Expr) : MetaM (Option (KnownPairOp × Array Expr)) := do
  let (fn, args) := v.getAppFnArgs
  match lookupOp? fn with
  | some spec =>
      if args.size == spec.arity then return some (spec, args) else return none
  | none => return none

/-- One emitted Copn slot.  The `dests` array is initialized to the natural
    `out_0, out_1, …` placeholders; subsequent projection lets *patch* the
    array with the user's chosen names.  When we reach end-of-chain, we emit
    a Copn using the patched names. -/
structure PendingCopn where
  /-- Index of the producing let-binder in the chain (used for ordering). -/
  idx     : Nat
  /-- The op spec (asm name, arity, outs). -/
  spec    : KnownPairOp
  /-- Per-output user-chosen register name.  `none` means "user never
      projected this output"; we still emit an LVal but with a synthetic
      `__unused_<idx>_<j>` name (the BignumExec semantics doesn't care
      about unused outputs — they bind a register that's never read). -/
  destNames : Array (Option String)
  /-- The argument PVar names. -/
  argNames  : Array String
  deriving Inhabited

/-- The reifier state: a list of pending Copns indexed by the producing
    let-binder's FVarId (so projection lets can find their producer). -/
structure ReifyState where
  pendings : Std.HashMap FVarId PendingCopn := {}
  /-- Sequential list of (idx, fvar) producer assignments (for ordering). -/
  order    : Array (Nat × FVarId)              := #[]

/-- Build a synthetic name for an output the user never projected. -/
def synthName (idx j : Nat) : String :=
  "__inst" ++ toString idx ++ "_out" ++ toString j

/-- Finalize one pending Copn into an `InstrR` value.  Uses synthetic names
    for un-projected outputs. -/
def finalizePending (p : PendingCopn) : InstrR :=
  let lvs : List LVal := (List.range p.spec.outs).map fun j =>
    let nm := (p.destNames[j]?.bind id).getD (synthName p.idx j)
    lv nm
  let es : List PExpr := p.argNames.toList.map pv
  .Copn lvs .AT_none (.Oasm ⟨p.spec.asm⟩) es

/-! ## §6. The walker

Walks the let-chain.  For each let-binder, three cases:

1. The value is a known pair-op → record a `PendingCopn` keyed by the
   binder's FVarId.  (We don't emit yet — we wait to learn the
   per-output user names via subsequent projection lets.)
2. The value is `<producer-fv>.1` / `.2` → patch the producer's
   `destNames[j]` with this binder's userName.
3. Anything else → error (or extend the known-op table).

After all lets are walked, emit the `PendingCopn`s in order.
-/

/-- Walk one let-binder's value; update state accordingly.  Returns the
    extended `RegEnv` (binding the let-fvar to its register name). -/
def stepLet (env : RegEnv) (st : ReifyState)
    (fv : FVarId) (v : Expr) (uname : String) :
    MetaM (RegEnv × ReifyState) := do
  -- Case (2): projection of a known producer
  match ← matchProj? v with
  | some (side, prodFv) =>
      match st.pendings[prodFv]? with
      | some pending =>
          -- Patch the producer's destNames[side] with this binder's name.
          let mut destNames := pending.destNames
          destNames := destNames.set! side (some uname)
          let pending' := { pending with destNames := destNames }
          let pendings' := st.pendings.insert prodFv pending'
          let env' := env.insert fv uname
          return (env', { st with pendings := pendings' })
      | none =>
          throwError
            "InstrRReflect: projection on {← prodFv.getUserName} but its \
             producer is not a known op"
  | none =>
      -- Case (1): full application of a known head
      match ← matchKnownOp? v with
      | some (spec, argExprs) =>
          let argNames ← argExprs.mapM fun a => reifyAtomVar env a
          let idx := st.order.size
          let pending : PendingCopn :=
            { idx       := idx
              spec      := spec
              destNames := Array.replicate spec.outs none
              argNames  := argNames }
          let pendings' := st.pendings.insert fv pending
          let order'    := st.order.push (idx, fv)
          let env'      := env.insert fv uname
          return (env', { pendings := pendings', order := order' })
      | none =>
          throwError
            "InstrRReflect: unsupported let-value in let {uname} (expected a \
             known pair-op like `mulx`/`adcx`/`adox` or a `.1`/`.2` projection \
             of one):{indentExpr v}"

/-- Emit pending Copns in original chain order. -/
def emitPendings (st : ReifyState) : List InstrR :=
  let pairs := st.order.toList.filterMap fun (_idx, fv) =>
    st.pendings[fv]?
  pairs.map finalizePending

/-- The top-level reifier.  Walks lambdas (binding params into the env) and
    lets (extending the env + recording pendings), then emits the final
    `List InstrR`. -/
def reifyBody (e : Expr) : MetaM (List InstrR) := do
  let e ← whnf e
  lambdaTelescope e fun params inner => do
    let mut env : RegEnv := {}
    for p in params do
      let nm ← p.fvarId!.getUserName
      env := env.insert p.fvarId! nm.toString
    letTelescope inner fun letVars _finalExpr => do
      let mut env := env
      let mut st  : ReifyState := {}
      for lv in letVars do
        let fv := lv.fvarId!
        let decl ← fv.getDecl
        match decl with
        | .cdecl .. =>
            -- Lambda-bound inside the body (e.g. nested fun) — bind name.
            let nm ← fv.getUserName
            env := env.insert fv nm.toString
        | .ldecl (value := v) .. =>
            let nm ← fv.getUserName
            let (env', st') ← stepLet env st fv v nm.toString
            env := env'
            st  := st'
      pure (emitPendings st)

/-! ## §7. `reifyInstrR%` elaborator -/

/-- `reifyInstrR% f` — given a value-level Lean function `f` whose body is a
    let-chain over the known pair-ops (`mulx` / `adcx` / `adox`) and `.1`/`.2`
    projections, produce the equivalent `List InstrR` body.

    The output is a Lean term of type `List InstrR` that can be fed to
    `bignumExecFuel`. -/
elab "reifyInstrR% " e:term : term => do
  let e' ← Term.elabTerm e none
  let e' ← instantiateMVars e'
  let body ← reifyBody e'
  return Lean.toExpr body

end            -- meta section

/-! ## §8. Self-test (kept here so any breakage shows up immediately)

This block reifies a tiny three-op kernel and `#eval`'s the result.  The
actual correspondence theorem lives in `Examples/InstrRReflectDemo.lean`. -/

/-- The smallest non-trivial ADX kernel: one MULX, one ADCX, one ADOX. -/
def selfTestKernel
    (acc a b cfIn ofIn : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let pm := mulx a b
  let hi := pm.1
  let lo := pm.2
  let pa := adcx acc lo cfIn
  let cf := pa.1
  let acc1 := pa.2
  let po := adox acc1 hi ofIn
  let ofOut := po.1
  let acc2 := po.2
  (cf, ofOut, acc2)

/-- The reified `List InstrR`. -/
def selfTestReified : List InstrR := reifyInstrR% selfTestKernel

/-! ## §9. Mirror target: `JasminCoqSemMirror.InstrR`

The original reifier targets `JasminAST.InstrR` (the older AST defined
in `JasminAST.lean`).  Below we add a parallel target for the newer
`JasminCoqSemMirror.InstrR` (the line-by-line port of jasminc's Coq
operational semantics, defined in `JasminCoqSemMirror.lean`).

The two ASTs differ:

| Field | Old `JasminAST` | New `CoqSemMirror` |
|---|---|---|
| Asm-op carrier | `AsmOp` (struct `{ name : String }`) | `String` (inline) |
| `Sopn` wrapper | `SOpn.Oasm op` (op : AsmOp) | `Sopn.Oasm op` (op : String) |
| `LVal.Lvar` carrier | `VarI := { var : Var, info : VarInfo }` | `VarI := { v_var : Var, v_info : Unit }` |
| `Var` field names | `vname, vtype` | `vname, vtype` (same!) |
| `Var.vtype` type | `SType` | `Atype` |
| `Var.vtype` for u64 reg | `.sword .U64` | `.aword .U64` |
| `Pvar` carrier | `GVar := { gv, gs : Bool }` | `GVar := { gv, gs : VScope }` |
| `Copn` ordering | `(lvs, tag, op, es)` | `(xs, tag, op, es)` (same shape) |
| `Cassgn` ordering | `(lv, tag, ty, e)` | `(lv, tag, ty, e)` (same shape) |

The structural translation is mechanical.  We expose:

* Small builders `vrM`, `pvM`, `lvM` over the new AST.
* `ToExpr` instances for the new AST.
* An emitter `finalizePendingMirror` that produces a
  `CoqSemMirror.Instr` from the same `PendingCopn` shape we already use.
* An elaborator `reifyInstrRMirror%` that wraps the *existing* walker
  (`reifyBody`) and converts each emitted IR instruction.
-/

-- Derive `ToExpr` for the new AST at the *top level* (not inside `Mirror`)
-- so the auto-generated instance names live in the namespace where the
-- types do.  The instances are metaprogramming and sit in a `meta section`.

meta section

deriving instance Lean.ToExpr for CoqSemMirror.WSize
deriving instance Lean.ToExpr for CoqSemMirror.Signedness
deriving instance Lean.ToExpr for CoqSemMirror.OpKind
deriving instance Lean.ToExpr for CoqSemMirror.CmpKind
deriving instance Lean.ToExpr for CoqSemMirror.SOp1
deriving instance Lean.ToExpr for CoqSemMirror.SOp2
deriving instance Lean.ToExpr for CoqSemMirror.OpN
deriving instance Lean.ToExpr for CoqSemMirror.Atype
deriving instance Lean.ToExpr for CoqSemMirror.Var
deriving instance Lean.ToExpr for CoqSemMirror.VarI
deriving instance Lean.ToExpr for CoqSemMirror.VScope
deriving instance Lean.ToExpr for CoqSemMirror.GVar
deriving instance Lean.ToExpr for CoqSemMirror.ArrAccess
deriving instance Lean.ToExpr for CoqSemMirror.Aligned
deriving instance Lean.ToExpr for CoqSemMirror.AssgnTag
deriving instance Lean.ToExpr for CoqSemMirror.Align
deriving instance Lean.ToExpr for CoqSemMirror.Sopn
deriving instance Lean.ToExpr for CoqSemMirror.FunName
deriving instance Lean.ToExpr for CoqSemMirror.Dir
deriving instance Lean.ToExpr for CoqSemMirror.Pexpr
deriving instance Lean.ToExpr for CoqSemMirror.Range
deriving instance Lean.ToExpr for CoqSemMirror.Lval

end            -- meta section

namespace Mirror

/-- A `u64` `Var` in the new AST (uses `Atype.aword .U64`, not `SType`). -/
def vrM (s : String) : CoqSemMirror.Var :=
  { vname := s, vtype := .aword .U64 }

/-- `Pvar` reading register `s` (local scope). -/
def pvM (s : String) : CoqSemMirror.Pexpr :=
  .Pvar (CoqSemMirror.mkLvar { v_var := vrM s })

/-- `Lvar` writing register `s`. -/
def lvM (s : String) : CoqSemMirror.Lval := .Lvar { v_var := vrM s }

/-- Build a `Copn` `CoqSemMirror.InstrR` for an asm-op `asmName` with
    output names `outNames` and argument names `argNames`.  Always uses
    `AT_none`. -/
def buildCopn (asmName : String) (outNames argNames : List String) :
    CoqSemMirror.InstrR :=
  let lvs : List CoqSemMirror.Lval := outNames.map lvM
  let es  : List CoqSemMirror.Pexpr := argNames.map pvM
  .Copn lvs .AT_none (.Oasm asmName) es

/-- Wrap a `CoqSemMirror.InstrR` in `Instr.MkI ()`. -/
def mkIM (ir : CoqSemMirror.InstrR) : CoqSemMirror.Instr := .MkI () ir

-- `InstrR` is mutually recursive with `Instr`; `deriving ToExpr` on a
-- mutual block isn't supported, so we hand-write the two instances via
-- explicit recursion.
meta section

open Lean in
mutual
partial def instrRToExpr : CoqSemMirror.InstrR → Expr
  | .Cassgn lv tag ty e =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Cassgn)
        #[Lean.toExpr lv, Lean.toExpr tag, Lean.toExpr ty, Lean.toExpr e]
  | .Copn xs tag op es =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Copn)
        #[Lean.toExpr xs, Lean.toExpr tag, Lean.toExpr op, Lean.toExpr es]
  | .Csyscall xs o es =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Csyscall)
        #[Lean.toExpr xs, Lean.toExpr o, Lean.toExpr es]
  | .Cif cond cthen celse =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Cif)
        #[Lean.toExpr cond, instrListToExpr cthen, instrListToExpr celse]
  | .Cfor v r body =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Cfor)
        #[Lean.toExpr v, Lean.toExpr r, instrListToExpr body]
  | .Cwhile al cbefore cond ii cafter =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Cwhile)
        #[Lean.toExpr al, instrListToExpr cbefore, Lean.toExpr cond,
          Lean.toExpr ii, instrListToExpr cafter]
  | .Ccall xs fn es =>
      mkAppN (mkConst ``CoqSemMirror.InstrR.Ccall)
        #[Lean.toExpr xs, Lean.toExpr fn, Lean.toExpr es]

partial def instrToExpr : CoqSemMirror.Instr → Expr
  | .MkI ii ir =>
      mkAppN (mkConst ``CoqSemMirror.Instr.MkI)
        #[Lean.toExpr ii, instrRToExpr ir]

partial def instrListToExpr : List CoqSemMirror.Instr → Expr
  | [] =>
      mkApp (mkConst ``List.nil [.zero]) (mkConst ``CoqSemMirror.Instr)
  | i :: is =>
      mkAppN (mkConst ``List.cons [.zero])
        #[mkConst ``CoqSemMirror.Instr, instrToExpr i, instrListToExpr is]
end

instance : Lean.ToExpr CoqSemMirror.InstrR where
  toTypeExpr := Lean.mkConst ``CoqSemMirror.InstrR
  toExpr := instrRToExpr

instance : Lean.ToExpr CoqSemMirror.Instr where
  toTypeExpr := Lean.mkConst ``CoqSemMirror.Instr
  toExpr := instrToExpr

end            -- meta section

end Mirror

/-! ### §9.b. Translation: `JasminAST.InstrR` → `CoqSemMirror.Instr`

We reuse the existing `reifyBody` walker (which produces a list of the
old AST's `InstrR`s) and translate each one to the new AST.  The
translation for the MVP scope (`Copn` only) is uniform.

`Copn lvs AT_none (Oasm ⟨asmName⟩) es`  ↦
  `MkI () (Copn (map lvalToMirror lvs) AT_none (Oasm asmName)
                (map pexprToMirror es))`

The conversion functions assume MVP shape (Lvar / Pvar over plain
register names); other shapes fall back to a uniform default that
preserves the constructor count but loses field info.  Extending the
conversion is mechanical: add a case in `lvalToMirror`/`pexprToMirror`
matching the new AST constructor needed.

Both ASTs export sorts named `InstrR`, `Lval`/`LVal`, `Pexpr`/`PExpr`,
`Sopn`/`SOpn` — so we use fully-qualified names below to make the
direction of translation explicit.

The translation is consumed only by the `reifyInstrRMirror%` elaborator,
so it sits in a `meta section`. -/

namespace Mirror

meta section

/-- Translate the old AST `LVal` to a new AST `Lval`.
    Only the MVP shape `Lvar { var := { vname, vtype := .sword .U64 } }`
    is mapped exactly; other shapes go to a placeholder `Lnone`. -/
def lvalToMirror :
    CatCrypt.Crypto.Jasmin.LVal → CatCrypt.Crypto.Jasmin.CoqSemMirror.Lval
  | .Lvar x =>
      let v : CatCrypt.Crypto.Jasmin.CoqSemMirror.Var :=
        { vname := x.var.vname, vtype := .aword .U64 }
      .Lvar { v_var := v }
  | _ => .Lnone () (.aword .U64)

/-- Translate the old AST `PExpr` to a new AST `Pexpr`.  MVP shape:
    `Pvar { gv := { var := { vname, .sword .U64 } } }`. -/
def pexprToMirror :
    CatCrypt.Crypto.Jasmin.PExpr → CatCrypt.Crypto.Jasmin.CoqSemMirror.Pexpr
  | .Pvar g =>
      let v : CatCrypt.Crypto.Jasmin.CoqSemMirror.Var :=
        { vname := g.gv.var.vname, vtype := .aword .U64 }
      .Pvar (CatCrypt.Crypto.Jasmin.CoqSemMirror.mkLvar { v_var := v })
  | _ => .Pconst 0

/-- Translate the old AST asm-op marker to the new AST's string-tagged
    `Sopn.Oasm`. -/
def sopnToMirror :
    CatCrypt.Crypto.Jasmin.SOpn → CatCrypt.Crypto.Jasmin.CoqSemMirror.Sopn
  | .Oasm op => .Oasm op.name

/-- Translate one old AST `InstrR` to a new AST `Instr`.  MVP scope:
    we cover `Copn` (the MULX/ADCX/ADOX case) and pass other constructors
    through to a uniform default. -/
def instrRToMirror :
    CatCrypt.Crypto.Jasmin.InstrR → CatCrypt.Crypto.Jasmin.CoqSemMirror.Instr
  | .Copn lvs _tag op es =>
      .MkI ()
        (.Copn (lvs.map lvalToMirror) .AT_none (sopnToMirror op)
               (es.map pexprToMirror))
  | _ =>
      .MkI () (.Cassgn (.Lnone () (.aword .U64)) .AT_none
                       (.aword .U64) (.Pconst 0))

/-- Translate a list of old AST `InstrR` to the new AST `Cmd`. -/
def cmdToMirror (irs : List CatCrypt.Crypto.Jasmin.InstrR) :
    CatCrypt.Crypto.Jasmin.CoqSemMirror.Cmd :=
  irs.map instrRToMirror

end            -- meta section

end Mirror

/-! ### §9.c. `reifyInstrRMirror%` elaborator

Same input as `reifyInstrR%`, but the output term has type
`CoqSemMirror.Cmd` (= `List CoqSemMirror.Instr`).  Implementation:
run the existing walker, then translate the result via
`cmdToMirror`. -/

meta section

elab "reifyInstrRMirror% " e:term : term => do
  let e' ← Term.elabTerm e none
  let e' ← instantiateMVars e'
  let body ← reifyBody e'
  let mirrorBody := Mirror.cmdToMirror body
  return Lean.toExpr mirrorBody

end            -- meta section

/-! ## §10. Mirror-side self-test -/

/-- Smoke test: reify the same `selfTestKernel` against the new AST.
    Output should be a 3-instruction `Cmd` of `Copn`s for MULX/ADCX/ADOX. -/
def selfTestReifiedMirror : CoqSemMirror.Cmd :=
  reifyInstrRMirror% selfTestKernel

/-- Sanity: the mirror reflection produces 3 instructions (one per ADX op). -/
example : selfTestReifiedMirror.length = 3 := by
  native_decide

/-- The asm-op name of the first instruction is `"MULX"`. -/
def firstAsmName? : Option String :=
  match selfTestReifiedMirror.head? with
  | some (.MkI _ (.Copn _ _ (.Oasm s) _)) => some s
  | _ => none

example : firstAsmName? = some "MULX" := by native_decide

/-- The asm-op names across the 3 instructions, in order, are
    `["MULX", "ADCX", "ADOX"]`. -/
def allAsmNames : List String :=
  selfTestReifiedMirror.filterMap fun
    | .MkI _ (.Copn _ _ (.Oasm s) _) => some s
    | _ => none

example : allAsmNames = ["MULX", "ADCX", "ADOX"] := by native_decide

/-- LHS register names of the 3 Copn instructions, concatenated. -/
def allLhsNames : List String :=
  selfTestReifiedMirror.flatMap fun
    | .MkI _ (.Copn lvs _ _ _) =>
        lvs.filterMap fun
          | .Lvar v => some v.v_var.vname
          | _       => none
    | _ => []

end CatCrypt.Crypto.Jasmin.InstrRReflect
