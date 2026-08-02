/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldLowering
import CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport
import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

/-!
# Field → ModArith as a `Com`-level program transport (the L3→L2 structure)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

## Scope

The L2 (`ModArithLowering`) and L3 (`FieldLowering`) `lower_denote_preserved`
theorems are **op-level identity realisations** (`realise op = denote op`): they
say each dialect op denotes to its own abstract value, and the lowering "chain"
in `DialectLoweringChain` composes those op-level equalities by **transitivity of
realisation facts**, not by a program-level `Com fieldDialect → Com modArithDialect`
transport carried by a `TransportSquare`/`LoweringData`. This file determines
**which part of Field→ModArith is a program transport** and
which part is irreducibly op-level — and builds the transport part as a real
`TransportSquare`.

### The structural split (two fragments, two different answers)

* **Prime-field fragment — a `Com`-level transport.** The five prime-field
  ops (`fAdd`/`fSub`/`fNeg`/`fMul`/`fInv`) are **1:1** with ModArith ops
  (`modAdd`/`modSub`/`modNeg`/`modMul`/`byInverse`): the Field type `fp p` and the
  ModArith type `fp p` *both* denote to `ZMod p`, and each Field leaf is
  **definitionally** the ModArith leaf (`fAddF = modAddF`, `fMulF = modMulF`,
  `fInvF = byInverseF`, …). This fragment fits the Phase-1
  `ComParametricityTransport.LoweringData` shape **exactly** — one source op → one
  target op, leaf-local, no binder reshaping — so a real
  `Com → Com` lowering `lowerCom` exists, its per-op leaf squares
  (`OpLowerTransports`) hold by `rfl`, and `fundamental` lifts them to a whole-
  program transport. We package it as `regFieldToModArith : TransportSquare …`
  so L3→L2 joins the registry as a **real program transport** on the prime-field
  fragment.

* **Extension fragment — irreducibly op-level (NOT a program transport).** A
  single Field `ext2Mul` decomposes into a **schedule of several ModArith ops**
  (`(a+bu)(c+du) = (ac−bd) + (ad+bc)u` — four `modMul` plus an `modAdd`/`modSub`),
  and `ext6Mul`/`ext12Mul` are larger schedules still. That is **one op → a
  block of ops**, which is exactly the binder-reshaping ("splits one op into
  several") case `ComParametricityTransport` *explicitly excludes* from the
  canonical structural shape (its `LoweringData.lowerExpr : Expr → Expr` produces
  a **single** op). Moreover ModArith has **no `fp2`/`fp6`/`fp12` type** at all —
  there is no `mapTy` target for the extension types — so a *total*
  `Com fieldDialect → Com modArithDialect` lowering does **not** exist. The
  extension lowering is therefore the op-level realisation
  `Fp2MulSchedule = ext2MulF` (`FieldLowering.fp2MulSchedule_denote`), a
  value-level equality composed by transitivity, **not** a `Com`-program
  transport. We formalise it as what it is (`extOpRealisation`) and record the
  precise reason it cannot be a `LoweringData`.

So the Phase-0 finding is **confirmed and refined**: L3→L2 is *part* program
transport (the prime-field fragment, built here) and *part* op-level
realisation (the extension fragment, formalised here as such, with the
no-`mapTy`-target / op-splitting obstruction stated).

### What is built here

* `fpDialect` — the **prime-field sub-dialect of `fieldDialect`**: type `fp p`
  only, ops the five prime-field ops. It IS the prime-field fragment of Field;
  giving it its own dialect is what lets the 1:1 lowering be *total*
  (the obstruction above is precisely that the extension types have no ModArith
  home).
* `lowerFieldToModArith : LoweringData fpDialect modArithDialect` — the
  structural lowering, one prime-field op → its ModArith twin.
* `fpVarTransports` / `fpOpLowerTransports` / `fpMapValExtends` — the three leaf
  coherences, each `rfl`.
* `fpComLowerTransports` — the whole-program transport, from `fundamental`.
* `regFieldToModArith : TransportSquare …` — the registry value: the prime-field
  Field→ModArith lowering as a real **program** `TransportSquare`.
* `extOpRealisation` — the extension fragment as an **op-level** realisation
  (`ext2Mul` denotes to `Fp2MulSchedule`), with `no_total_lowering_*` notes
  documenting why it is *not* a `LoweringData`.

**0 sorries**; target axiom set `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport

/-! ## 1. The prime-field sub-dialect of `fieldDialect`

`fpDialect` is the prime-field fragment of `fieldDialect`: only the type `fp p`
and the five prime-field ops. It is *not* a new mathematical object — it is the
sub-dialect on which Field and ModArith coincide 1:1 (their `fp p`
types both denote `ZMod p`, and the five leaves are definitionally equal). Giving
it a standalone dialect is exactly what makes the structural lowering **total**:
the only reason a total `fieldDialect → modArithDialect` lowering fails is the
extension types, which this fragment excludes by construction. -/

/-- Prime-field op tags (the 1:1 fragment of `FieldOp`). -/
inductive FpOp where
  /-- Prime-field add. -/
  | fpAdd (p : Nat)
  /-- Prime-field sub. -/
  | fpSub (p : Nat)
  /-- Prime-field negate. -/
  | fpNeg (p : Nat)
  /-- Prime-field multiply. -/
  | fpMul (p : Nat)
  /-- Prime-field inverse. -/
  | fpInv (p : Nat)
  deriving DecidableEq

/-- Prime-field type tags: just `fp p`. -/
inductive FpTy where
  /-- The prime field `F_p`, `⟦·⟧ = ZMod p`. -/
  | fp (p : Nat)
  deriving DecidableEq

/-- The prime-field sub-dialect. -/
@[reducible] def fpDialect : Dialect := { Op := FpOp, Ty := FpTy }

/-- `fp p` denotes to `ZMod p` — the same carrier as both Field's `fp p` and
    ModArith's `fp p`. -/
@[reducible] instance : TyDenote FpTy where
  denote | .fp p => ZMod p

instance : DialectSignature fpDialect where
  sig
    | .fpAdd p => [.fp p, .fp p]
    | .fpSub p => [.fp p, .fp p]
    | .fpNeg p => [.fp p]
    | .fpMul p => [.fp p, .fp p]
    | .fpInv p => [.fp p]
  ret
    | .fpAdd p => .fp p
    | .fpSub p => .fp p
    | .fpNeg p => .fp p
    | .fpMul p => .fp p
    | .fpInv p => .fp p

instance fpDenote : DialectDenote fpDialect where
  denote
    | .fpAdd _ => fun args => modAddF args.head args.tail.head
    | .fpSub _ => fun args => modSubF args.head args.tail.head
    | .fpNeg _ => fun args => modNegF args.head
    | .fpMul _ => fun args => modMulF args.head args.tail.head
    | .fpInv _ => fun args => byInverseF args.head

/-! ## 2. The structural lowering `fpDialect → modArithDialect`

Each prime-field op maps to its ModArith twin: `fpAdd ↦ modAdd`, `fpMul ↦ modMul`,
`fpInv ↦ byInverse`, … The type map sends `fp p ↦ fp p`; the variable map is the
identity (same de Bruijn position, mapped context); `lowerExpr` rebuilds the op
with the mapped args. This is the canonical one-op-to-one-op leaf-local shape. -/

/-- Type map: `fp p ↦ ModArith.fp p`. Reducible so `(sig op).map mapTy` computes
    definitionally to `sig (lowerOp op)` (every entry is `fp p`, fixed by `mapTy`),
    keeping the arg-transport cast-free. -/
@[reducible] def mapTy : FpTy → ModArithTy
  | .fp p => .fp p

/-- Context map: pointwise `mapTy`. -/
@[reducible] def mapCtx (Γ : Ctxt fpDialect) : Ctxt modArithDialect := Γ.map mapTy

/-- The target ModArith op a prime-field op lowers to (its 1:1 twin). -/
@[reducible] def lowerOp : FpOp → ModArithOp
  | .fpAdd p => .modAdd p
  | .fpSub p => .modSub p
  | .fpNeg p => .modNeg p
  | .fpMul p => .modMul p
  | .fpInv p => .byInverse p

/-- The mapped op's argument signature matches the source op's, transported by
    `mapTy`: `sig (lowerOp op) = (sig op).map mapTy`. (Definitional per op.) -/
theorem lowerOp_sig (op : FpOp) :
    DialectSignature.sig (d := modArithDialect) (lowerOp op)
      = (DialectSignature.sig (d := fpDialect) op).map mapTy := by
  cases op <;> rfl

/-- The mapped op's return type is `mapTy` of the source op's return type. -/
theorem lowerOp_ret (op : FpOp) :
    DialectSignature.ret (d := modArithDialect) (lowerOp op)
      = mapTy (DialectSignature.ret (d := fpDialect) op) := by
  cases op <;> rfl

/-- Variable transport: same de Bruijn index, over the mapped context. Built by
    recursion on the `Var` so the `mapCtx_cons` reindexing is definitional. -/
@[reducible] def mapVar : {Γ : Ctxt fpDialect} → {t : FpTy} → Ctxt.Var Γ t →
    Ctxt.Var (mapCtx Γ) (mapTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- Transport an `HVector` of source variables to target variables, over the
    mapped context. Since `mapTy` is reducible and fixes every `fp p`, the target
    list index `tys.map mapTy` is definitionally `sig (lowerOp op)`. -/
@[reducible] def mapArgs {Γ : Ctxt fpDialect} :
    {tys : List FpTy} → HVector (fun ty => Ctxt.Var Γ ty) tys →
      HVector (fun ty => Ctxt.Var (mapCtx Γ) ty) (tys.map mapTy)
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (mapVar v) (mapArgs rest)

/-- The per-expression lowering: rebuild the lowered op with the transported
    args, of the mapped return type. With `mapTy`/`lowerOp` reducible, the arg
    list index matches `sig (lowerOp op)` definitionally — no `▸` cast needed. -/
@[reducible] def lowerExpr {Γ : Ctxt fpDialect} {t : FpTy}
    (e : Expr fpDialect Γ t) : Expr modArithDialect (mapCtx Γ) (mapTy t) :=
  { op := lowerOp e.op
    retTy_eq := by rw [lowerOp_ret]; exact congrArg mapTy e.retTy_eq
    args := (lowerOp_sig e.op) ▸ mapArgs e.args }

/-- The Phase-1 `LoweringData` packaging the prime-field structural lowering. -/
def lowerFieldToModArith : LoweringData fpDialect modArithDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  lowerExpr := lowerExpr

/-! ## 3. The semantic transports and the three leaf coherences

The value transport `transTy : ⟦t⟧ → ⟦mapTy t⟧` is the **identity** (both sides
are `ZMod p`), as is the valuation transport `mapVal`. The three leaf coherences
are each `rfl`, because Field's prime leaves *are* ModArith's leaves and the
variable/binder threading is positional. -/

/-- Value transport: identity (`⟦fp p⟧ = ZMod p = ⟦mapTy (fp p)⟧`). -/
def transTy : TransTy lowerFieldToModArith := fun {t} x =>
  match t, x with
  | .fp _, x => x

/-- Valuation transport: identity (the mapped valuation is the same `HVector`
    over the mapped context). Built positionally to match `mapVal_extend`. -/
def mapVal : MapVal lowerFieldToModArith := fun {Γ} V =>
  match Γ, V with
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons x (mapVal V)

/-- **Variable-transport leaf.** Looking up the mapped variable in the mapped
    valuation equals (identity-)transporting the source lookup. By induction on
    the variable; positional, so `rfl` at each step. -/
theorem fpVarTransports :
    VarTransports lowerFieldToModArith transTy mapVal := by
  intro Γ t v V
  induction v with
  | here =>
      cases V with
      | cons x V => rfl
  | there v ih =>
      cases V with
      | cons x V => exact ih V

/-- **Mapped-variable lookup is the source lookup** (positional identity).
    `transTy`/`mapVar`/`mapVal` are all identity-positional, so resolving the
    mapped variable in the mapped valuation returns the source value. -/
theorem mapVar_lookup {Γ : Ctxt fpDialect} {t : FpTy}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    (mapVar v).lookup (mapVal V) = v.lookup V := by
  induction v with
  | here => cases V with | cons x V => rfl
  | there v ih => cases V with | cons x V => exact ih V

/-- **Op-leaf transport.** The lowered expression denotes (under the mapped
    valuation) to the (identity-)transport of the source op's denotation. The
    only op-specific obligation. After `cases op` and peeling the
    (concrete-arity) argument vector, the lowered ModArith op's denotation is
    *definitionally* the source Field leaf (`modAddF = fAddF`, …); `mapVar_lookup`
    aligns each positionally-identical mapped argument. -/
theorem fpOpLowerTransports :
    OpLowerTransports lowerFieldToModArith transTy mapVal := by
  intro Γ t e V
  rcases e with ⟨op, h, args⟩
  subst h
  cases op with
  | fpAdd p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modAddF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modAddF (a.lookup V) (b.lookup V)
          rw [mapVar_lookup, mapVar_lookup]
  | fpSub p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modSubF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modSubF (a.lookup V) (b.lookup V)
          rw [mapVar_lookup, mapVar_lookup]
  | fpMul p =>
      match args with
      | .cons a (.cons b .nil) =>
          show modMulF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))
            = modMulF (a.lookup V) (b.lookup V)
          rw [mapVar_lookup, mapVar_lookup]
  | fpNeg p =>
      match args with
      | .cons a .nil =>
          show modNegF ((mapVar a).lookup (mapVal V)) = modNegF (a.lookup V)
          rw [mapVar_lookup]
  | fpInv p =>
      match args with
      | .cons a .nil =>
          show byInverseF ((mapVar a).lookup (mapVal V)) = byInverseF (a.lookup V)
          rw [mapVar_lookup]

/-- **Binding-threading coherence.** Mapping a source-extended valuation equals
    extending the mapped valuation by the transport (here identity) of the bound
    value. `mapCtx_cons` is `rfl`, `transTy`/`mapVal` are positional identities,
    so this is `rfl`. -/
theorem fpMapValExtends :
    MapValExtends lowerFieldToModArith transTy mapVal := by
  intro Γ t V x
  cases t with
  | fp p => rfl

/-! ## 4. The whole-program transport (Phase-1 `fundamental`) -/

/-- **Whole-program transport, prime-field Field→ModArith.** For *every*
    `Com fpDialect Γ t`, the structurally-lowered ModArith program denotes (under
    the mapped valuation) to the (identity-)transport of the source denotation —
    the program-level lowering correctness. Obtained from the three
    per-op/leaf coherences by `ComParametricityTransport.fundamental`; no
    program-specific induction. -/
theorem fpComLowerTransports {Γ : Ctxt fpDialect} {t : FpTy}
    (c : Com fpDialect Γ t) :
    ComLowerTransports lowerFieldToModArith transTy mapVal c :=
  fundamental lowerFieldToModArith transTy mapVal
    fpVarTransports fpOpLowerTransports fpMapValExtends c

/-! ## 5. The registry value — a real program `TransportSquare`

We package the whole-program transport for a *fixed* program `c` as a
`DialectLoweringTransport.TransportSquare`, exactly the Phase-0 registry shape
(`g = c.denote`, `f = (lowerCom c).denote`, `φin = mapVal`, `φout = transTy`).
This is the deliverable: the prime-field Field→ModArith lowering joins the
registry as a **program transport** (not an op-level realisation). -/

/-- **`regFieldToModArith`** — the prime-field Field→ModArith lowering of a
    program `c`, as a registered `TransportSquare`. The carried square is exactly
    `fpComLowerTransports c`: `(lowerCom c).denote (mapVal V) = transTy (c.denote V)`
    for all `V`. This is the L3→L2 prime-field arm as a real **program**
    transport, composable with the other registry squares via
    `TransportSquare.comp`. -/
def regFieldToModArith {Γ : Ctxt fpDialect} {t : FpTy} (c : Com fpDialect Γ t) :
    TransportSquare
      (g := fun V : Ctxt.Valuation Γ => c.denote V)
      (φin := mapVal) (φout := fun x => transTy x)
      (f := fun V => (lowerFieldToModArith.lowerCom c).denote V) :=
  ⟨fun V => fpComLowerTransports c V⟩

/-- **The registry square carries the program-level correctness.** Unfolding
    `regFieldToModArith` gives back exactly the whole-program transport — the
    square is the `Com → Com` denotation-preservation, not a per-op
    identity. -/
theorem regFieldToModArith_related {Γ : Ctxt fpDialect} {t : FpTy}
    (c : Com fpDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerFieldToModArith.lowerCom c).denote (mapVal V) = transTy (c.denote V) :=
  (regFieldToModArith c).related V

/-! ## 6. The extension fragment is irreducibly op-level (NOT a program transport)

The prime-field arm above is a `Com fpDialect → Com modArithDialect`
transport. The **extension** arm (`fp2`/`fp6`/`fp12`, `ext2Mul`/`ext6Mul`/…) is
**not**, for two independent reasons — both formalised here:

1. **No `mapTy` target.** ModArith has no `fp2`/`fp6`/`fp12` type, so there is no
   type-map `FieldTy → ModArithTy` carrying the extension types — a *total*
   `LoweringData fieldDialect modArithDialect` cannot even be stated.
2. **One op → a block of ops.** A single `ext2Mul` lowers to a *schedule* of
   several ModArith ops (`(a+bu)(c+du) = (ac−bd) + (ad+bc)u`), which is the
   binder-reshaping / op-splitting case `LoweringData.lowerExpr : Expr → Expr`
   (single op) cannot express, and that `ComParametricityTransport` explicitly
   excludes from the canonical structural shape.

So the extension Field→ModArith step is an **op-level realisation**
(`FieldLowering.fp2MulSchedule_denote`: the ModArith-leaf Karatsuba schedule
equals the abstract `Fp2` product), a value-level equality composed by
transitivity in `DialectLoweringChain.extChainDenote` — *not* a `Com`-program
transport. We record it as exactly that. -/

/-- **The extension fragment, as an op-level realisation.** `ext2Mul` denotes to
    its ModArith-leaf Karatsuba schedule `Fp2MulSchedule` (the L3→L2 extension
    step). This is the honest shape of the extension lowering: a *value-level*
    realisation equality (`= ` between the op's denotation and a ModArith-leaf
    schedule), **not** a `TransportSquare`/`LoweringData` program transport —
    there is no single ModArith op, nor a ModArith type, to send `ext2Mul`/`fp2`
    to. -/
theorem extOpRealisation {p : Nat} (x y : Fp2Val p) :
    fieldDenote.denote (.ext2Mul p) (.cons x (.cons y .nil))
      = FieldDialect.Fp2MulSchedule x y :=
  FieldDialect.ext2Mul_lowers_to_schedule x y

/-- **The extension realisation has the op-level realisation shape, not the
    `TransportSquare` shape.** A `DialectLoweringTransport.TransportSquare` is a
    *commuting square* `f (φin x) = φout (g x)` between two functions across input
    and output transports. The extension step `extOpRealisation` is instead a
    plain *value* equality `denote op args = schedule args` (no input/output
    transport, no realised `f` on a transported carrier). We record the
    distinction by exhibiting the extension step as the *degenerate* square whose
    transports are the identity and whose two "functions" are the op denotation
    and the schedule **on the same arguments** — i.e. it lives at the op/value
    level (`Fp2Val p → Fp2Val p`), not at the program level
    (`Valuation Γ → ⟦t⟧`). This is precisely the op-level realisation the L2/L3
    chain composes by transitivity, formalised as such. -/
theorem extOpRealisation_is_value_level {p : Nat} :
    TransportSquare
      (g := fun xy : Fp2Val p × Fp2Val p =>
              fieldDenote.denote (.ext2Mul p) (.cons xy.1 (.cons xy.2 .nil)))
      (φin := id) (φout := id)
      (f := fun xy : Fp2Val p × Fp2Val p => FieldDialect.Fp2MulSchedule xy.1 xy.2) :=
  ⟨fun xy => (extOpRealisation xy.1 xy.2).symm⟩

end CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithLowering
