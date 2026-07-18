/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinFront
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Named-SSA → `Com jasminDialect` builder

`FieldEmitGoldenPath.fieldCondSub251Com` is a 7-binding `Com jasminDialect` whose
operand references are hand-written de-Bruijn chains
(`.cons (.there (.there (.there (.there .here)))) …`). Hand-authoring those chains
for the big straight-line field/curve kernels (64-term GF(256) dot products, CIOS
Montgomery multiply) is impractical and error-prone: a miscounted `.there` silently
references the wrong binding.

This file provides the **forward** builder — the inverse of
`ScalarLinFront.comToReg`, which goes `Com → RegProg` by naming each binding by its
de-Bruijn *level*. Here we start from a named straight-line SSA program (inputs
pre-named by level `0 … nInputs-1`; each binding names its result by its own level
`nInputs + k` and its operands by the levels they reference) and **generate** the
`Com jasminDialect` with the de-Bruijn indices resolved automatically.

## The de-Bruijn inversion

The context grows on the **left** (`Com.var : Com d (t :: Γ) s → Com d Γ s`), so the
most-recent binding is de-Bruijn index `0` (`Ctxt.Var.here`) and `Ctxt.Var.there`
shifts one binding older. A name at **level** `L`, in a context of `depth` bindings,
sits at de-Bruijn **index** `depth - 1 - L` — exactly the formula
`ScalarLinFront.resolveName` reads in the reverse direction. So:

* `mkVar Γ i` builds the `Ctxt.Var Γ (.reg 64)` for index `i` by structural recursion
  on `Γ`/`i` (`.here` at `0`, `.there` on the tail), returning `none` out of bounds or
  when the head type is not `.reg 64`. This is the helper that resolves the dependent
  `Ctxt.Var` from a computed index.
* `levelVar Γ depth L` first turns a level into an index (`depth - 1 - L`) then calls
  `mkVar`.

The builder walks the binding list, building one `Com.var` per binding with its `Expr`
assembled from `mkVar`-resolved operands, and recursing under the extended context
`(.reg 64) :: Γ`. Because every supported op (`regArith`, `mulhi`, immediate shifts,
`regConst`) has an all-`reg 64` (or empty) signature, the `HVector` of argument
variables is built by a small `argsReg64` recursion that checks each signature slot
is `.reg 64`.

The output is an honest `Com jasminDialect` term — golden-provable exactly like a
hand-written one (`ComOK`, `Com.denote`, `com_arm_e2e`/`com_riscv_e2e`). The worked
re-derivation of `fieldCondSub251Com` at the end proves the generated `Com`'s
`Com.denote` is *definitionally equal* (`rfl`) to the hand-authored one.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ComBuilder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

/-! ## 1. `mkVar`: resolve a dependent `Ctxt.Var` from a de-Bruijn index

The crux of the inversion. Given a context `Γ` and an index `i`, produce the
intrinsically-typed `Ctxt.Var Γ (.reg 64)` if `i` is in range and the binding it
references has type `.reg 64`. The dependent match on `Γ` is what lets `.here`
typecheck (its motive forces `Γ = (.reg 64) :: Γ'`); `.there` is layered on the
recursive call into the tail. -/

/-- Build `Ctxt.Var Γ (.reg 64)` from de-Bruijn index `i`, by recursion on the
    context. `none` if `i` is out of range, or if the binding at `i` is not a
    `reg 64`. This resolves the dependent `Ctxt.Var` whose constructor chain
    (`.there^i .here`) the caller would otherwise have to hand-author. -/
def mkVar : (Γ : Ctxt jasminDialect) → (i : Nat) → Option (Ctxt.Var Γ (.reg 64))
  | [], _ => none
  | (.reg 64) :: _, 0 => some .here
  | _ :: _, 0 => none                      -- head present but not `reg 64`
  | _ :: Γ', (i + 1) => (mkVar Γ' i).map .there

/-- Resolve a binding **level** `L` (its stable name) to a `Ctxt.Var` in a context of
    `depth` bindings. The index is `depth - 1 - L`, the exact inverse of
    `ScalarLinFront.resolveName`. -/
def levelVar (Γ : Ctxt jasminDialect) (depth L : Nat) :
    Option (Ctxt.Var Γ (.reg 64)) :=
  mkVar Γ (depth - 1 - L)

/-! ## 2. `argsReg64`: build the argument `HVector` from resolved variables

Every supported op has signature `[]`, `[.reg 64]`, or `[.reg 64, .reg 64]` — all
`reg 64`. Given the op's signature `tys` and the operand levels, build the
`HVector (fun ty => Ctxt.Var Γ ty) tys`, requiring each `ty` to be `.reg 64` and the
operand count to match. -/

/-- Build the typed argument `HVector` from a list of operand levels, against the op
    signature `tys`. Each signature slot must be `.reg 64` and resolve in range. -/
def argsReg64 (Γ : Ctxt jasminDialect) (depth : Nat) :
    (tys : List JasminTy) → List Nat →
    Option (HVector (fun ty => Ctxt.Var Γ ty) tys)
  | [], [] => some .nil
  | [], _ :: _ => none                     -- too many operands
  | _ :: _, [] => none                     -- too few operands
  | (.reg 64) :: tys, L :: Ls =>
      match levelVar Γ depth L, argsReg64 Γ depth tys Ls with
      | some v, some rest => some (.cons v rest)
      | _, _ => none
  | _ :: _, _ :: _ => none                 -- signature slot not `reg 64`

/-! ## 3. The named-SSA program and the builder -/

/-- One binding of a named straight-line SSA program: an op and the **levels** of its
    operands (in argument order). The result's level is positional (it is
    `nInputs + index-of-this-binding`), so it is not stored. -/
structure Binding where
  /-- The dialect op (e.g. `.regArith .add 64`, `.regConst 64 251`, `.shrImm 64 63`). -/
  op : JasminOp
  /-- Operand levels, in the op's argument order. -/
  argLevels : List Nat

/-- A named straight-line SSA program over `nInputs` pre-named inputs (levels
    `0 … nInputs-1`): a list of bindings, then the level of the value to return. -/
structure NamedSSA where
  /-- Number of pre-named inputs. -/
  nInputs : Nat
  /-- The straight-line bindings, in order. Binding `k` has result level
      `nInputs + k`. -/
  bindings : List Binding
  /-- The level of the value to return. -/
  retLevel : Nat

/-- Build the `Expr` for one binding in context `Γ` at the given `depth`. The op's
    return type must be `.reg 64` (`retTy_eq` is then `rfl`-provable by the caller via
    the decidable check below); operands are resolved by `argsReg64`. -/
def buildExpr (Γ : Ctxt jasminDialect) (depth : Nat) (b : Binding)
    (hret : @DialectSignature.ret jasminDialect _ b.op = (.reg 64 : JasminTy)) :
    Option (Expr jasminDialect Γ (.reg 64)) :=
  match argsReg64 Γ depth (@DialectSignature.sig jasminDialect _ b.op) b.argLevels with
  | some args => some { op := b.op, retTy_eq := hret, args := args }
  | none => none

/-- Decide whether an op returns `.reg 64`, producing the `retTy_eq` witness on the
    `some` branch. Keeps the builder total without an external proof obligation. -/
def retIsReg64? (op : JasminOp) :
    Option (PLift (@DialectSignature.ret jasminDialect _ op = (.reg 64 : JasminTy))) :=
  if h : @DialectSignature.ret jasminDialect _ op = (.reg 64 : JasminTy)
  then some ⟨h⟩ else none

/-- The core builder: walk the binding list, emitting one `Com.var` per binding under
    a context that grows on the left (`(.reg 64) :: Γ`), and close with `Com.ret` on
    the return level. Returns `none` on any unresolved operand / non-`reg 64` op /
    out-of-range level. -/
def buildCom : (Γ : Ctxt jasminDialect) → (depth : Nat) → (bindings : List Binding) →
    (retLevel : Nat) → Option (Com jasminDialect Γ (.reg 64))
  | Γ, depth, [], retLevel =>
      match levelVar Γ depth retLevel with
      | some v => some (.ret v)
      | none => none
  | Γ, depth, b :: bs, retLevel =>
      match retIsReg64? b.op with
      | none => none
      | some hret =>
          match buildExpr Γ depth b hret.down with
          | none => none
          | some e =>
              match buildCom ((.reg 64) :: Γ) (depth + 1) bs retLevel with
              | some body => some (.var e body)
              | none => none

/-- Top-level builder: a `NamedSSA` over `nInputs` inputs builds a `Com` over the
    all-`reg 64` input context `List.replicate nInputs (.reg 64)`. The starting depth
    is `nInputs` (the inputs occupy levels `0 … nInputs-1`). -/
def build (p : NamedSSA) :
    Option (Com jasminDialect (List.replicate p.nInputs (.reg 64)) (.reg 64)) :=
  buildCom (List.replicate p.nInputs (.reg 64)) p.nInputs p.bindings p.retLevel

/-! ## 3b. The builder preserves `ComOK`

The forward builder turns a `NamedSSA` into a `Com`; the *value* layer
(`Com.denote`) and *emit* layer (`com_arm_e2e`/`com_riscv_e2e`) both need the
kernel to be in the supported straight-line fragment (`ComOK`). Rather than
hand-author one `ComOK.var` witness per binding (which re-introduces exactly the
positional fragility the builder removed), we prove it **once and generically**:
if every binding's op is `SupportedOp`, then any `Com` the builder produces is
`ComOK`. This makes the whole pipeline turnkey — a new kernel needs only a
per-binding `SupportedOp` check (one `decide`/`Or.inl`-chain), never a
de-Bruijn-shaped `ComOK` proof. -/

/-- A `NamedSSA` whose every binding uses a supported op. The premise of
    `build_preserves_ComOK`. -/
def AllBindingsSupported (bindings : List Binding) : Prop :=
  ∀ b ∈ bindings, SupportedOp b.op

/-- **The builder preserves `ComOK` (core, on `buildCom`).** If every binding op is
    `SupportedOp` and `buildCom` succeeds, the resulting `Com` is `ComOK`. By
    induction on the binding list: the `[]` case is `ComOK.ret`; the cons case
    reads `SupportedOp b.op` off the head (the emitted `Expr` has `op := b.op`)
    and recurses under the extended context. -/
theorem buildCom_preserves_ComOK :
    ∀ (Γ : Ctxt jasminDialect) (depth : Nat) (bindings : List Binding) (retLevel : Nat)
      (c : Com jasminDialect Γ (.reg 64)),
      AllBindingsSupported bindings →
      buildCom Γ depth bindings retLevel = some c → ComOK c := by
  intro Γ depth bindings
  induction bindings generalizing Γ depth with
  | nil =>
      intro retLevel c _ hbuild
      simp only [buildCom] at hbuild
      cases hlv : levelVar Γ depth retLevel with
      | none => simp only [hlv] at hbuild; exact absurd hbuild (by simp)
      | some v =>
          simp only [hlv, Option.some.injEq] at hbuild
          subst hbuild; exact ComOK.ret v
  | cons b bs ih =>
      intro retLevel c hsupp hbuild
      simp only [buildCom] at hbuild
      cases hret : retIsReg64? b.op with
      | none => simp only [hret] at hbuild; exact absurd hbuild (by simp)
      | some hr =>
          simp only [hret] at hbuild
          cases hexpr : buildExpr Γ depth b hr.down with
          | none => simp only [hexpr] at hbuild; exact absurd hbuild (by simp)
          | some e =>
              simp only [hexpr] at hbuild
              cases hbody : buildCom ((.reg 64) :: Γ) (depth + 1) bs retLevel with
              | none => simp only [hbody] at hbuild; exact absurd hbuild (by simp)
              | some body =>
                  simp only [hbody, Option.some.injEq] at hbuild
                  subst hbuild
                  -- the emitted expr `e` has `e.op = b.op`, so `SupportedOp e.op`
                  have hsupp_b : SupportedOp b.op := hsupp b (List.mem_cons_self ..)
                  have heop : e.op = b.op := by
                    simp only [buildExpr] at hexpr
                    cases hargs :
                        argsReg64 Γ depth (@DialectSignature.sig jasminDialect _ b.op) b.argLevels with
                    | none => simp only [hargs] at hexpr; exact absurd hexpr (by simp)
                    | some args =>
                        simp only [hargs, Option.some.injEq] at hexpr
                        subst hexpr; rfl
                  refine ComOK.var (e := e) ?_ ?_
                  · rw [heop]; exact hsupp_b
                  · exact ih ((.reg 64) :: Γ) (depth + 1) retLevel body
                      (fun b' hb' => hsupp b' (List.mem_cons_of_mem _ hb')) hbody

/-- **The builder preserves `ComOK` (top level, on `build`).** Turnkey: a
    `NamedSSA` whose every binding is `SupportedOp`, when `build` succeeds,
    yields a `ComOK` kernel — no per-binding de-Bruijn `ComOK.var` chain. -/
theorem build_preserves_ComOK (p : NamedSSA) (c : Com jasminDialect (List.replicate p.nInputs (.reg 64)) (.reg 64))
    (hsupp : AllBindingsSupported p.bindings)
    (hbuild : build p = some c) : ComOK c :=
  buildCom_preserves_ComOK _ _ _ _ _ hsupp hbuild

/-! ## 3c. The builder preserves `Com.denote` — a computable level-indexed evaluator

`build_preserves_ComOK` discharges the *structural* (`ComOK`) obligation generically.
The remaining per-kernel obligation is the *value* one: `condSub251Built_denote` is a
`rfl` that unfolds the whole `Com.denote` against a hand-written ALU expression. That
`rfl` works for a 7-binding kernel but is opaque (it does not *say* what the kernel
computes) and gets expensive for the big straight-line kernels.

This section gives a **computable abstract evaluator** `NamedSSA.eval` over level-indexed
`BitVec 64` environments and proves `build_preserves_denote`: a generated `Com`'s
`Com.denote` equals `eval` on the matching inputs. With it, a denote fact becomes a
`decide`/`native_decide` *computation* on `eval` rather than a per-kernel `Com.denote`
`rfl`.

### The environment

The evaluator's environment is a total function `Nat → BitVec 64` ("level ↦ value");
out-of-range / wrong-type levels read `0`. The `Com`'s `Valuation` (de-Bruijn, dependent,
context grows on the left) is bridged to it by `valIdx`: the value at **de-Bruijn index**
`i` of `V`, as a `BitVec 64` (or `0` if `i` is out of range or the slot is not `reg 64`).
A level `L` in a `depth`-deep context lives at de-Bruijn index `depth - 1 - L`. -/

/-- The value at de-Bruijn index `i` of a `Valuation`, read as a `BitVec 64`
    (`0` if `i` is out of range or the slot is not a `reg 64`). The semantic
    counterpart of `mkVar` (which resolves the *variable* at index `i`); the
    bridge lemma `mkVar_lookup` ties the two together. -/
def valIdx : (Γ : Ctxt jasminDialect) → Ctxt.Valuation Γ → Nat → BitVec 64
  | [], _, _ => 0
  | (.reg 64) :: _, V, 0 => V.head
  | _ :: _, _, 0 => 0
  | _ :: _, V, (i + 1) => valIdx _ V.tail i

/-- **Bridge lemma.** When `mkVar Γ i` resolves a variable, its `lookup` in any
    valuation `V` is exactly `valIdx Γ V i`. The dependent `Var.lookup` is thereby
    reduced to a plain index read. By induction on `Γ`/`i`, matching `mkVar`. -/
theorem mkVar_lookup :
    ∀ (Γ : Ctxt jasminDialect) (i : Nat) (v : Ctxt.Var Γ (.reg 64))
      (V : Ctxt.Valuation Γ),
      mkVar Γ i = some v → v.lookup V = valIdx Γ V i := by
  intro Γ i
  fun_induction mkVar Γ i with
  | case1 => intro v V h; simp at h
  | case2 =>
      intro v V h; simp only [Option.some.injEq] at h; subst h
      cases V with | cons x xs => rfl
  | case3 => intro v V h; simp at h
  | case4 t Γ' i ih =>
      intro v V h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨v', hv', rfl⟩ := h
      cases V with
      | cons x xs =>
          have e1 : (Ctxt.Var.there v').lookup (HVector.cons x xs) = v'.lookup xs := rfl
          have e2 : valIdx (t :: Γ') (HVector.cons x xs) i.succ = valIdx Γ' xs i := by
            rw [valIdx]; rfl
          rw [e1, e2]; exact ih v' xs hv'

/-! ### Reading an operand `HVector` out of an env

`argsReg64` resolves the operand `HVector` of `Ctxt.Var`s for a binding. Its
semantic mirror is `envArgs`: read the *values* of those operand levels straight
out of a level-indexed env. The bridge lemma `argsReg64_lookupArgs` says: when
`argsReg64` succeeds, looking its variables up in `V` gives the same `HVector` as
reading the operand levels out of the matching env (under the `valIdx`↔env
correspondence at the given depth). -/

/-- Read the operand values for an op signature `tys` (all `.reg 64`) out of a
    level-indexed env, by operand `argLevels`. `none` if a slot is not `.reg 64`
    or the operand count mismatches — exactly when `argsReg64` is `none`. -/
def envArgs (env : Nat → BitVec 64) :
    (tys : List JasminTy) → List Nat →
    Option (HVector (fun t => ⟦t⟧) tys)
  | [], [] => some .nil
  | [], _ :: _ => none
  | _ :: _, [] => none
  | (.reg 64) :: tys, L :: Ls =>
      (envArgs env tys Ls).map (fun rest => .cons (env L) rest)
  | _ :: _, _ :: _ => none

/-- **Bridge lemma for operands.** With the env reading each level `L` as
    `valIdx Γ V (depth - 1 - L)` (the `valIdx`↔env correspondence at `depth`),
    resolving the `argsReg64` variables in `V` (`Expr.lookupArgs`) coincides with
    reading the operand levels straight out of the env (`envArgs`): whenever both
    succeed, they produce the same operand `HVector`. By induction on `tys`/`Ls`,
    using `mkVar_lookup` at each `.reg 64` slot. -/
theorem argsReg64_lookupArgs
    (Γ : Ctxt jasminDialect) (depth : Nat) (V : Ctxt.Valuation Γ)
    (env : Nat → BitVec 64)
    (hcorr : ∀ L, L < depth → env L = valIdx Γ V (depth - 1 - L)) :
    ∀ (tys : List JasminTy) (Ls : List Nat)
      (args : HVector (fun ty => Ctxt.Var Γ ty) tys)
      (vals : HVector (fun t => ⟦t⟧) tys),
      (∀ L ∈ Ls, L < depth) →
      argsReg64 Γ depth tys Ls = some args →
      envArgs env tys Ls = some vals →
      Expr.lookupArgs args V = vals := by
  intro tys Ls
  fun_induction argsReg64 Γ depth tys Ls with
  | case1 =>
      intro args vals _ ha hv
      simp only [Option.some.injEq] at ha
      simp only [envArgs, Option.some.injEq] at hv
      subst ha; subst hv; rfl
  | case2 => intro args vals _ ha hv; simp at ha
  | case3 => intro args vals _ ha hv; simp at ha
  | case4 tys L Ls vv rest hrest hlv ih =>
      intro args vals hwf ha hv
      simp only [Option.some.injEq] at ha
      subst ha
      simp only [envArgs, Option.map_eq_some_iff] at hv
      obtain ⟨rv, hrv, rfl⟩ := hv
      have he : Expr.lookupArgs (HVector.cons vv rest) V
          = HVector.cons (vv.lookup V) (Expr.lookupArgs rest V) := rfl
      have hL : L < depth := hwf L (List.mem_cons_self ..)
      have hrestwf : ∀ L' ∈ Ls, L' < depth :=
        fun L' hL' => hwf L' (List.mem_cons_of_mem _ hL')
      rw [he, hcorr L hL, mkVar_lookup Γ (depth - 1 - L) vv V hlv,
        ih rest rv hrestwf hrest hrv]
  | case5 => intro args vals _ ha hv; simp at ha
  | case6 => intro args vals _ ha hv; simp at ha

/-! ### The evaluator

`evalExpr` is the value-level mirror of `buildExpr`: it reads a binding's operands
out of an env (`envArgs`), then applies the **dialect's own** op denotation
(`DialectDenote.denote`) — the very same function `Expr.denote` uses. Because the
op-semantics is shared verbatim (rather than re-spelled per op), the per-binding
value agreement is `rfl` and no op enumeration appears anywhere.

`evalCom` walks the binding list exactly as `buildCom` does, appending each result
at its level (`depth`), and returns the env value at `retLevel`. `NamedSSA.eval`
seeds the env with `inputs` at levels `0 … nInputs-1` and runs `evalCom`. -/

/-- Value-level mirror of `buildExpr`: read the operands of binding `b` out of
    `env` (`envArgs`), apply the dialect's op denotation, and coerce the result to
    `BitVec 64` via the `ret = .reg 64` witness. `none` exactly when `buildExpr`
    is `none` (operand resolution fails). -/
def evalExpr (env : Nat → BitVec 64) (b : Binding)
    (hret : @DialectSignature.ret jasminDialect _ b.op = (.reg 64 : JasminTy)) :
    Option (BitVec 64) :=
  match envArgs env (@DialectSignature.sig jasminDialect _ b.op) b.argLevels with
  | some vals =>
      some (cast (congrArg TyDenote.denote hret)
        (@DialectDenote.denote jasminDialect _ _ jasminDenote b.op vals))
  | none => none

/-- Extend a level-indexed env with a new binding's value at level `lvl`. -/
def envExtend (env : Nat → BitVec 64) (lvl : Nat) (v : BitVec 64) :
    Nat → BitVec 64 :=
  fun L => if L = lvl then v else env L

/-- Value-level mirror of `buildCom`: fold the bindings into the env (each result
    stored at its level `depth`), then read off `retLevel`. Returns `none` on the
    same conditions `buildCom` does (non-`reg 64` op / unresolved operand). -/
def evalCom : (env : Nat → BitVec 64) → (depth : Nat) → (bindings : List Binding) →
    (retLevel : Nat) → Option (BitVec 64)
  | env, _, [], retLevel => some (env retLevel)
  | env, depth, b :: bs, retLevel =>
      match retIsReg64? b.op with
      | none => none
      | some hret =>
          match evalExpr env b hret.down with
          | none => none
          | some v => evalCom (envExtend env depth v) (depth + 1) bs retLevel

/-- **The computable abstract evaluator.** Seed a level-indexed env with `inputs`
    at levels `0 … nInputs-1` (all higher levels start at `0`, to be filled by the
    bindings), run `evalCom` from `depth = nInputs`, and read the value at
    `retLevel`. `none` if any binding's op is non-`reg 64` or an operand is
    unresolved (exactly when `build` is `none`). -/
def NamedSSA.eval (p : NamedSSA) (inputs : List (BitVec 64)) : Option (BitVec 64) :=
  evalCom (fun L => inputs[L]?.getD 0) p.nInputs p.bindings p.retLevel

/-! ### `build_preserves_denote`

The `Com.denote` of a built kernel equals `NamedSSA.eval` on matching inputs. The
core is the `buildCom`/`evalCom` lockstep (`buildCom_denote_evalCom`): under the
`valIdx`↔env correspondence at the current `depth`, the two agree, and the `var`
step re-establishes the correspondence at `depth + 1` (the new binding's value is
the same on both sides — definitionally, because `Expr.denote` and `evalExpr` call
the *same* `DialectDenote.denote`). -/

/-- The env↔valuation correspondence that the lockstep maintains: at depth `depth`,
    every **in-scope** env level `L < depth` equals the de-Bruijn slot
    `depth - 1 - L` of the valuation. The bound `L < depth` is load-bearing: a level
    `≥ depth` is out of scope (not yet bound), and the truncated `depth - 1 - L = 0`
    would spuriously read the head — so the correspondence is asserted only on
    in-scope levels, exactly the ones a well-formed program's operands reference. -/
def EnvCorr (Γ : Ctxt jasminDialect) (V : Ctxt.Valuation Γ)
    (env : Nat → BitVec 64) (depth : Nat) : Prop :=
  ∀ L, L < depth → env L = valIdx Γ V (depth - 1 - L)

/-- **Operand well-formedness** for the lockstep at `depth`: every binding's operand
    levels are in scope when that binding is processed (binding `k`, at depth
    `depth + k`, references only levels `< depth + k`), and the final `retLevel` is
    in scope (`< depth + bindings.length`). This is the no-forward-reference / SSA
    dominance condition: it rules out an operand pointing at a not-yet-bound (or
    self) level, which `levelVar`'s truncated index would otherwise resolve to the
    wrong (head) slot. Mirrors the `buildCom`/`evalCom` recursion. -/
def BindingsWF : (depth : Nat) → (bindings : List Binding) → (retLevel : Nat) → Prop
  | depth, [], retLevel => retLevel < depth
  | depth, b :: bs, retLevel =>
      (∀ L ∈ b.argLevels, L < depth) ∧ BindingsWF (depth + 1) bs retLevel

/-- **Per-binding value agreement.** When the operands resolve (`buildExpr` and
    `evalExpr` both succeed under the env↔valuation correspondence), the `Com`
    expression's denotation equals the evaluator's binding value. The two are
    literally the same `DialectDenote.denote` applied to the same operand vector
    (bridged by `argsReg64_lookupArgs`); the `retTy_eq ▸ …` casts coincide. -/
theorem buildExpr_denote_evalExpr
    (Γ : Ctxt jasminDialect) (depth : Nat) (V : Ctxt.Valuation Γ)
    (env : Nat → BitVec 64) (hcorr : EnvCorr Γ V env depth)
    (b : Binding) (hwf : ∀ L ∈ b.argLevels, L < depth)
    (hret : @DialectSignature.ret jasminDialect _ b.op = (.reg 64 : JasminTy))
    (e : Expr jasminDialect Γ (.reg 64)) (v : BitVec 64)
    (he : buildExpr Γ depth b hret = some e)
    (hv : evalExpr env b hret = some v) :
    e.denote V = v := by
  cases hargs : argsReg64 Γ depth (@DialectSignature.sig jasminDialect _ b.op) b.argLevels with
  | none => rw [buildExpr, hargs] at he; simp at he
  | some args =>
      cases hvals : envArgs env (@DialectSignature.sig jasminDialect _ b.op) b.argLevels with
      | none => rw [evalExpr, hvals] at hv; simp at hv
      | some vals =>
          rw [buildExpr, hargs] at he
          rw [evalExpr, hvals] at hv
          simp only [Option.some.injEq] at he hv
          subst he; subst hv
          -- both sides are a cast/▸ of the same `DialectDenote.denote b.op (·)`
          -- on equal operand vectors (bridge lemma), with `hret`-derived casts.
          have hbridge : Expr.lookupArgs args V = vals :=
            argsReg64_lookupArgs Γ depth V env hcorr _ b.argLevels args vals hwf hargs hvals
          show (hret ▸ DialectDenote.denote b.op (Expr.lookupArgs args V))
              = cast (congrArg TyDenote.denote hret)
                  (@DialectDenote.denote jasminDialect _ _ jasminDenote b.op vals)
          rw [hbridge, eqRec_eq_cast]

/-- **The lockstep core.** Under the env↔valuation correspondence at `depth`,
    `buildCom`'s `Com.denote` equals `evalCom`. By induction on the binding list
    (via `fun_induction`-style structural recursion matching `buildCom`/`evalCom`):
    the `[]` case is the `retLevel` lookup (`mkVar_lookup` + correspondence); the
    cons case uses `buildExpr_denote_evalExpr` for the new value and re-establishes
    the correspondence at `depth + 1` (`envExtend_corr`). -/
theorem buildCom_denote_evalCom :
    ∀ (Γ : Ctxt jasminDialect) (depth : Nat) (bindings : List Binding) (retLevel : Nat)
      (c : Com jasminDialect Γ (.reg 64)) (V : Ctxt.Valuation Γ)
      (env : Nat → BitVec 64) (v : BitVec 64),
      EnvCorr Γ V env depth →
      BindingsWF depth bindings retLevel →
      buildCom Γ depth bindings retLevel = some c →
      evalCom env depth bindings retLevel = some v →
      Com.denote c V = v := by
  intro Γ depth bindings
  induction bindings generalizing Γ depth with
  | nil =>
      intro retLevel c V env v hcorr hwf hbuild heval
      simp only [BindingsWF] at hwf
      simp only [buildCom] at hbuild
      simp only [evalCom, Option.some.injEq] at heval
      cases hlv : levelVar Γ depth retLevel with
      | none => rw [hlv] at hbuild; simp at hbuild
      | some rv =>
          rw [hlv] at hbuild
          simp only [Option.some.injEq] at hbuild
          subst hbuild
          subst heval
          simp only [Com.denote]
          rw [mkVar_lookup Γ (depth - 1 - retLevel) rv V hlv]
          exact (hcorr retLevel hwf).symm
  | cons b bs ih =>
      intro retLevel c V env v hcorr hwf hbuild heval
      simp only [BindingsWF] at hwf
      obtain ⟨hwfb, hwfbs⟩ := hwf
      simp only [buildCom] at hbuild
      simp only [evalCom] at heval
      cases hret : retIsReg64? b.op with
      | none => simp only [hret] at hbuild; exact absurd hbuild (by simp)
      | some hr =>
          simp only [hret] at hbuild heval
          cases hexpr : buildExpr Γ depth b hr.down with
          | none => simp only [hexpr] at hbuild; exact absurd hbuild (by simp)
          | some e =>
              cases hev : evalExpr env b hr.down with
              | none => simp only [hev] at heval; exact absurd heval (by simp)
              | some bv =>
                  simp only [hexpr] at hbuild
                  simp only [hev] at heval
                  cases hbody : buildCom ((.reg 64) :: Γ) (depth + 1) bs retLevel with
                  | none => simp only [hbody] at hbuild; exact absurd hbuild (by simp)
                  | some body =>
                      simp only [hbody, Option.some.injEq] at hbuild
                      subst hbuild
                      simp only [Com.denote]
                      -- the new binding's value agrees on both sides
                      have hval : e.denote V = bv :=
                        buildExpr_denote_evalExpr Γ depth V env hcorr b hwfb hr.down e bv hexpr hev
                      -- correspondence preserved at depth+1 under the extended env/valuation
                      have hcorr' : EnvCorr ((.reg 64) :: Γ)
                          (V.extend (e.denote V)) (envExtend env depth bv) (depth + 1) := by
                        intro L hLlt
                        simp only [envExtend]
                        by_cases hLd : L = depth
                        · simp only [if_pos hLd]
                          have hz : depth + 1 - 1 - L = 0 := by omega
                          have he2 : valIdx ((.reg 64) :: Γ) (V.extend (e.denote V))
                              (depth + 1 - 1 - L) = e.denote V := by rw [hz]; rfl
                          rw [he2, hval]
                        · simp only [if_neg hLd]
                          have hLlt' : L < depth := by omega
                          have hge : depth + 1 - 1 - L = (depth - 1 - L) + 1 := by omega
                          have he3 : valIdx ((.reg 64) :: Γ) (V.extend (e.denote V))
                              (depth + 1 - 1 - L) = valIdx Γ V (depth - 1 - L) := by
                            rw [hge, valIdx]; rfl
                          rw [he3]; exact hcorr L hLlt'
                      exact ih ((.reg 64) :: Γ) (depth + 1) retLevel body
                        (V.extend (e.denote V)) (envExtend env depth bv) v hcorr' hwfbs hbody heval

/-- **Build preserves denotation (top level).** A generated `Com`'s `Com.denote`
    at a valuation built from `inputs` equals `NamedSSA.eval` at those inputs. The
    valuation is the inputs in de-Bruijn order (level `i` at index `nInputs-1-i`),
    which is exactly the all-`reg 64` input context `build` runs over. Turnkey: a
    denote fact is now an `eval` computation, not a per-kernel `Com.denote` `rfl`. -/
theorem build_preserves_denote
    (p : NamedSSA)
    (c : Com jasminDialect (List.replicate p.nInputs (JasminTy.reg 64)) (.reg 64))
    (V : @Ctxt.Valuation jasminDialect _ (List.replicate p.nInputs (JasminTy.reg 64)))
    (inputs : List (BitVec 64)) (v : BitVec 64)
    (hcorr : EnvCorr (List.replicate p.nInputs (JasminTy.reg 64)) V
              (fun L => inputs[L]?.getD 0) p.nInputs)
    (hwf : BindingsWF p.nInputs p.bindings p.retLevel)
    (hbuild : build p = some c)
    (heval : p.eval inputs = some v) :
    Com.denote c V = v :=
  buildCom_denote_evalCom _ _ _ _ _ V _ v hcorr hwf hbuild heval

/-! ## 4. Worked re-derivation of `fieldCondSub251Com`

`fieldCondSub251Com` (one input `a` at level `0`) is:

```
v1 := 251              -- regConst
v2 := v0 - v1          -- a - 251
v3 := v2 >>> 63
v4 := 0                -- regConst
v5 := v4 - v3          -- 0 - bit
v6 := v5 & v1          -- m & 251
v7 := v2 + v6          -- t + masked
ret v7
```

Each operand is named by the **level** it references; the builder resolves the
de-Bruijn `.there` chains the hand-written term spells out explicitly. -/

/-- The named-SSA description of the GF(251) conditional-subtract reduce. -/
def condSub251SSA : NamedSSA where
  nInputs := 1
  bindings :=
    [ ⟨.regConst 64 251, []⟩      -- v1 := 251
    , ⟨.regArith .sub 64, [0, 1]⟩ -- v2 := v0 - v1
    , ⟨.shrImm 64 63, [2]⟩        -- v3 := v2 >>> 63
    , ⟨.regConst 64 0, []⟩        -- v4 := 0
    , ⟨.regArith .sub 64, [4, 3]⟩ -- v5 := v4 - v3
    , ⟨.regArith .and 64, [5, 1]⟩ -- v6 := v5 & v1
    , ⟨.regArith .add 64, [2, 6]⟩ -- v7 := v2 + v6
    ]
  retLevel := 7

/-- The builder succeeds and produces a `Com` over the single-input context. -/
def condSub251Built : Com jasminDialect [.reg 64] (.reg 64) :=
  (build condSub251SSA).get (by decide)

/-- **The generated `Com` denotes the same ALU expression as the hand-written one** —
    a definitional `rfl`, exactly as `FieldEmitGoldenPath.fieldCondSub251Com_denote`.
    This is the load-bearing check: the auto-resolved de-Bruijn indices coincide with
    the hand-authored `.there` chains, so the two `Com`s have identical denotation. -/
theorem condSub251Built_denote (a : BitVec 64) :
    Com.denote condSub251Built (.cons a .nil)
      = (a - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64)) :=
  rfl

/-- **Every binding of `condSub251SSA` is `SupportedOp`** — the only per-kernel
    obligation the turnkey path leaves: a flat dispatch over the seven ops (two
    `regConst`, one `shrImm`, four `regArith` in `{sub, and, add}`). No de-Bruijn
    structure appears. -/
theorem condSub251SSA_allSupported : AllBindingsSupported condSub251SSA.bindings := by
  intro b hb
  simp only [condSub251SSA, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h <;> subst h <;> unfold SupportedOp <;> simp

/-- **The generated `Com` is `ComOK` — for free, via `build_preserves_ComOK`.**
    This is the turnkey payoff: no per-binding de-Bruijn `ComOK.var` chain, just
    the generic builder lemma fed the flat `SupportedOp` check
    (`condSub251SSA_allSupported`) and the `build … = some …` witness (`rfl`).
    `com_arm_e2e` / `com_riscv_e2e` then apply directly to `condSub251Built`. -/
theorem condSub251Built_ok : ComOK condSub251Built :=
  build_preserves_ComOK condSub251SSA condSub251Built condSub251SSA_allSupported rfl

/-! ## 5. The abstract evaluator is faithful (demonstration of `build_preserves_denote`)

`condSub251Built_denote` discharges the value layer by an opaque `Com.denote`
`rfl`. The evaluator route makes the same fact a *computation*: -/

/-- **The evaluator computes the kernel's value.** A concrete `#eval`-style check:
    `condSub251` on input `300` returns `49` (`300 - 251 = 49`; the conditional-
    subtract mask is off since `49 ≥ 0`). A `decide`/`native_decide` on `eval`,
    not a `Com.denote` unfolding. -/
theorem condSub251_eval_300 : NamedSSA.eval condSub251SSA [300] = some 49 := by
  decide

/-- **The evaluator is symbolically faithful.** For every input `a`, the evaluator
    returns exactly the ALU expression `condSub251Built_denote` proves the generated
    `Com` denotes — confirming `NamedSSA.eval` mirrors the dialect semantics. -/
theorem condSub251_eval_symbolic (a : BitVec 64) :
    NamedSSA.eval condSub251SSA [a]
      = some ((a - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64))) :=
  rfl

/-- **`condSub251SSA` is well-formed** (no forward/self operand references), the
    side condition `build_preserves_denote` needs: each binding's operands and the
    `retLevel` are in scope at the point they are read. -/
theorem condSub251SSA_wf : BindingsWF 1 condSub251SSA.bindings 7 := by
  unfold condSub251SSA
  simp only [BindingsWF]
  norm_num [List.mem_cons]

/-- **The generated `Com`'s denotation equals the evaluator** — the turnkey value
    fact via `build_preserves_denote`, instantiated at the single input `a`. The
    `Com.denote` is no longer pinned by a per-kernel `rfl`; it is the computable
    `NamedSSA.eval` (here `condSub251_eval_symbolic` / `condSub251_eval_300`). -/
theorem condSub251Built_denote_via_eval (a : BitVec 64) :
    Com.denote condSub251Built (.cons a .nil)
      = ((a - (251 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64))) := by
  have hcorr : EnvCorr [JasminTy.reg 64] (.cons a .nil)
      (fun L => ([a] : List (BitVec 64))[L]?.getD 0) 1 := by
    intro L hL; interval_cases L; rfl
  have := build_preserves_denote condSub251SSA condSub251Built (.cons a .nil) [a] _
    hcorr condSub251SSA_wf rfl (condSub251_eval_symbolic a)
  exact this

end CatCrypt.Crypto.SecureCompilation.ComBuilder
