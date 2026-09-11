/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink

/-!
# C8 field-leaf: compiling an ML-KEM field op through the two-front combiner

ML-KEM's scalar field-coefficient operations (`add` / `sub` / `mul` / `reduce`)
are arithmetic in `𝔽_q` with `q = 3329`. The extracted hax shapes
(`MLKEM/Extraction/Mlkem_haxpipe.lean`) are

```text
reduce_impExpr = let x = x; cast#16[Rem[x, Q]]
add_impExpr    = let a = a; let b = b; reduce[Add[cast#32[a], cast#32[b]]]
```

i.e. they use `Rem`/`Div`, the cross-width `cast#16`/`cast#32` tags, and the
global constant `Q`. None of these live in the compile-from-hax front's
bitwise/ARX subset (`recogBin`/`recogShift` recognise `Add`/`Sub`/`Mul` and the
shifts/rotates, but not `Rem`, the cast tags, or a free global const). Teaching
the front modular arithmetic is the wrong move.

The **right** move is the C8 two-front combiner (`CompileFromHaxLink.lean`):

* the **transparent** structure of the field op — the integer sum `Add[a,b]` —
  is genuinely *in* the front's subset and is compiled value-preservingly by the
  whole `ImpExpr → Thir → Com jasminDialect` pipeline;
* the **opaque** field reduction `reduce` is treated as a registered fast
  **leaf** with intended semantics `spec x = x % 3329`. Its agreement to the
  opaque dialect call `jasminExtSem "reduce" …` is the Barrett-kernel author's
  obligation — a *hypothesis*, never an axiom (`jasminExtSem "reduce"` lands in
  the opaque `_, _, retTy => default` arm of `JasminDialect.jasminExtSem`, so the
  equality is genuinely unprovable here, exactly as for the toy `"f"` leaf).

So `add a b = reduce(a + b)` compiles as: the front's supported `Rhs.add` for
`a + b`, then the opaque `reduce`-call leaf linked to `· % 3329`. This is
**Option A** of the task: `reduce` is a registered `LeafSpec`, the field-add
outer is built through the front (`ThirToComFront`), and the result is routed
through the committed C8 linking lemma (`extCall_denote_via_leaf`), mirroring
`CompileFromHaxLink.linked_example` — no fresh compiler proof.

## Which option, honestly

This is **Option A**. The `Rhs.call`'s arguments are `List Atom` (`lit`/`lvar`/
`inp`), *not* nested binops, so the field-add is in its natural A-normal form

```text
let s = add(a, b);     -- Rhs.add: the SUPPORTED integer sum (front subset)
let r = reduce(s);     -- Rhs.call "reduce" [lvar "s"]: the opaque field-reduce leaf
ret r
```

which is exactly the two-front shape: a transparent front-compiled `Add`
followed by the opaque `reduce` leaf whose `· % 3329` correctness is the carried
C8 obligation.

## On the residual (honest)

The **synthetic** field-add `mlkemFieldAddThir` is used rather than the literal
`add_impExpr`. The precise residual blocking the literal extracted form from the
front: (1) the `cast#32`/`cast#16` width tags on the operands (a `castStrip`
mirror of `stripWidthSuffix` rewriting the `cast#w` heads is the small additional
pre-pass that would clear these), (2) the free global const `Q` (the front has no
global-constant environment — it would be inlined to its literal `3329` by a
const-folding pre-pass), and (3) the `Rem` inside `reduce` (which is precisely
what we route to the leaf, so it is *not* a residual — it is the design). The C8
field-leaf composition demonstrated here is independent of (1)/(2): they are
cosmetic front pre-passes, whereas (3) — the modular reduction — is the genuine
opaque-leaf obligation this file discharges via the registry.

## What is mechanized vs. carried

* **Mechanized:** the front compiles the integer `Add[a,b]` value-preservingly
  (`mlkemFieldAdd_isSome`, routed through the committed front lowering); and the
  *linking composition* — substituting the opaque `reduce` call by its leaf
  `spec` (`extCall_denote_via_leaf` / the `reduceLeaf.agrees` rewrite).
* **Carried (a hypothesis, not an axiom):** the per-leaf agreement
  `jasminExtSem "reduce" … = (· % 3329)` — the Barrett-kernel correctness proof a
  fast-leaf author discharges. We thread it as the `LeafSpec.agrees` field /
  the hypothesis of `mlkem_field_add_via_leaf`, exactly as
  `CompileFromHaxLink.linked_example` threads its `hagree`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxField

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## §1  The ML-KEM modulus and the field-reduce leaf -/

/-- The ML-KEM modulus `q = 3329`, as a `BitVec 32`. -/
def mlkemQ : BitVec 32 := 3329

/-- The field-reduce call name (`reduce_impExpr`'s head, treated as the leaf). -/
def reduceName : String := "reduce"

/-- The field-reduce leaf's intended semantics: `spec x = x % 3329`. A single
    `BitVec 32` argument leaf — the canonical-representative reduction modulo the
    ML-KEM prime. Mirrors `reduce_impExpr = cast#16[Rem[x, Q]]` at the working
    width (the `cast#16` truncation is `id` on a `< q` residue, so the leaf's
    semantic content is the `Rem[·, Q]`). -/
def reduceSpec : (Fin 1 → BitVec 32) → BitVec 32 := fun a => a 0 % mlkemQ

/-! ## §2  The field-add outer through the front

The field op `add a b = reduce(a + b)` in A-normal form, built directly through
`ThirToComFront`: the integer sum is the front-supported `Rhs.add` on the two
inputs, and `reduce` is the opaque single-argument call on that local. The front
lowers this to a `Com jasminDialect` whose `reduce` node is an opaque `extCall`. -/

/-- The field-add outer THIR (`nIn = 2`, inputs `a = inp 0`, `b = inp 1`):

    ```text
    let s = add(a, b);     -- Rhs.add: the supported integer sum
    let r = reduce(s);     -- the opaque field-reduce leaf call
    ret r
    ```
-/
def mlkemFieldAddThir : Thir :=
  .let_ "s" (.add (.inp 0) (.inp 1))
   (.let_ "r" (.call reduceName [.lvar "s"])
    (.ret (.lvar "r")))

/-- The field-add outer lowers (the front returns `some`) at width `32`,
    `nIn = 2`. Closed straight-line term: `native_decide`. -/
theorem mlkemFieldAdd_isSome :
    (thirToJasmin (w := 32) (nIn := 2) [] (initFState 32 2) mlkemFieldAddThir).isSome := by
  native_decide

/-- The field-add outer `Com` (the front's output). -/
def mlkemFieldAddCom : Com jasminDialect (frontCtxt 32 2 []) (rW 32) :=
  (thirToJasmin (w := 32) (nIn := 2) [] (initFState 32 2) mlkemFieldAddThir).get
    mlkemFieldAdd_isSome

/-! ## §3  Value-preservation relative to the opaque `reduce` call

Before linking, the compiled outer denotes to `jasminExtSem "reduce" …` applied
to the integer sum `a + b` — the opaque external-call value. This is the
front's `compileFromHax`-style outer obligation (proved via `thirToJasmin_denote`),
correct *relative to* the `reduce` call. -/

/-- **The field-add outer, relative to the opaque `reduce` call.** For inputs
    `a`, `b`, the compiled outer denotes to `jasminExtSem "reduce" …` applied to
    `a + b` (the front-compiled integer sum) — the opaque field-reduce value,
    *before* linking. -/
theorem mlkemFieldAddCom_denote_opaque (a b : BitVec 32) :
    (mlkemFieldAddCom).denote (inputValuation 32 2 (fun i => if i = 0 then a else b))
      = jasminExtSem reduceName (callArgTys 32 1) (rW 32)
          (HVector.cons ((a + b) : ⟦rW 32⟧) HVector.nil) := by
  set I : Fin 2 → BitVec 32 := fun i => if i = 0 then a else b with hI
  have hc : thirToJasmin (w := 32) (nIn := 2) [] (initFState 32 2) mlkemFieldAddThir
      = some (mlkemFieldAddCom) := (Option.some_get _).symm
  have hfront := thirToJasmin_denote (w := 32) (nIn := 2) []
    I mlkemFieldAddThir (LEnv.empty 32) (initFState 32 2)
    (inputValuation 32 2 I) (mlkemFieldAddCom) (initAgree I) hc
  -- The THIR denotation: `let s = a + b; let r = reduce(s); ret r` evaluates to
  -- `jasminExtSem "reduce" …` of the single argument `a + b`.
  have ha : inpGet (nIn := 2) I 0 = a := by
    simp only [inpGet, show (0 : Nat) < 2 by decide, dif_pos, hI]; rfl
  have hb : inpGet (nIn := 2) I 1 = b := by
    simp only [inpGet, show (1 : Nat) < 2 by decide, dif_pos, hI]
    norm_num
  have hthir : Thir.denote (w := 32) (nIn := 2) I mlkemFieldAddThir (LEnv.empty 32)
      = some (jasminExtSem reduceName (callArgTys 32 1) (rW 32)
          (HVector.cons ((a + b) : ⟦rW 32⟧) HVector.nil)) := by
    simp only [mlkemFieldAddThir, Thir.denote, Rhs.denote, Atom.denote, atomsHV,
      ha, hb, Option.bind_some, Option.map_some, LEnv.set, if_pos, String.reduceEq]
    rfl
  rw [hthir] at hfront
  exact (Option.some.injEq _ _ ▸ hfront).symm

/-! ## §4  The registry: register `reduce` as a verified field leaf

The C8 leaf registry holds the `reduce` leaf with its `· % 3329` spec. Its
`agrees` field is the carried hypothesis — the Barrett-kernel author's
obligation that the fast reduce kernel computes the canonical residue. -/

/-- The `reduce` leaf entry, given its agreement hypothesis. -/
def reduceLeaf
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem reduceName (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = reduceSpec (hvToFun args)) :
    LeafSpec 32 :=
  { name := reduceName, n := 1, spec := reduceSpec, agrees := hagree }

/-- The field registry holding exactly the `reduce` leaf, given its agreement. -/
def mlkemFieldRegistry
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem reduceName (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = reduceSpec (hvToFun args)) :
    LeafRegistry 32 :=
  (LeafRegistry.empty 32).insert (reduceLeaf hagree)

/-- The field registry resolves `"reduce"` to the field-reduce leaf — the call is
    C8-linkable. -/
theorem mlkemFieldRegistry_resolves
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem reduceName (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = reduceSpec (hvToFun args)) :
    Resolves (mlkemFieldRegistry hagree) reduceName (reduceLeaf hagree) :=
  insert_resolves (LeafRegistry.empty 32) _

/-! ## §5  The linked field-add: the two-front combiner composes

Given the leaf agreement, the whole compiled field-add outer denotes to the
spec-defined value `(a + b) % 3329` — the canonical ML-KEM field-add. The front's
value-preservation (`mlkemFieldAddCom_denote_opaque`, the transparent integer
`Add`) is composed with the carried `reduce`-leaf obligation (`hagree`, the
opaque modular reduction) into one whole field-op statement. -/

/-- **The ML-KEM field-add via the C8 leaf (the two-front combiner).** *Given*
    the per-leaf agreement `hagree` — the Barrett-kernel author's obligation that
    the opaque `reduce` call computes `· % 3329`, a *hypothesis*, not an axiom
    (`jasminExtSem "reduce"` is opaque) — the whole compiled field-add outer
    denotes to the canonical ML-KEM field sum `(a + b) % 3329` for all inputs
    `a`, `b`.

    The transparent, front-compiled integer `Add[a,b]`
    (`mlkemFieldAddCom_denote_opaque`) is composed with the opaque field-reduce
    leaf (`reduceSpec = · % 3329`, linked through the committed C8 lemma) into one
    statement: the field op `add a b = reduce(a + b)` is a *verified-compiled
    integer Add* THEN the *reduce leaf whose Barrett correctness is the carried
    C8 obligation*. The leaf agreement is carried; the composition is
    mechanized. -/
theorem mlkem_field_add_via_leaf
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem reduceName (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = reduceSpec (hvToFun args))
    (a b : BitVec 32) :
    (mlkemFieldAddCom).denote (inputValuation 32 2 (fun i => if i = 0 then a else b))
      = (a + b) % mlkemQ := by
  -- Step 1 (mechanized): outer value-preservation relative to the opaque call.
  rw [mlkemFieldAddCom_denote_opaque a b]
  -- Step 2 (the carried leaf obligation): link the opaque `reduce` to its spec.
  rw [hagree (HVector.cons ((a + b) : ⟦rW 32⟧) HVector.nil)]
  -- Step 3 (compute): `reduceSpec` of the single argument `a + b` is `(a+b) % q`.
  show reduceSpec (hvToFun (HVector.cons ((a + b) : ⟦rW 32⟧) HVector.nil)) = (a + b) % mlkemQ
  simp only [reduceSpec, hvToFun, hvNth, Fin.cases_zero, HVector.head]

/-- **The C8 link, surfaced at the `extCall`-node level.** The committed
    `extCall_denote_via_leaf` rewrites the opaque `reduce` `extCall`-node's
    denotation to `reduceSpec` of its denoted argument, for any in-scope argument
    variable and valuation — the registry side of the field-add composition,
    routed through the committed C8 linking lemma (no fresh compiler proof). -/
theorem reduce_extCall_via_leaf
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys 32 1)),
        (jasminExtSem reduceName (callArgTys 32 1) (rW 32) args : ⟦rW 32⟧)
          = reduceSpec (hvToFun args))
    {Γ : Ctxt jasminDialect}
    (args : HVector (fun ty => Ctxt.Var Γ ty) (callArgTys 32 1))
    (V : Ctxt.Valuation Γ) :
    (extCallExpr (w := 32) (n := 1) reduceName args).denote V
      = reduceSpec (hvToFun (Expr.lookupArgs args V)) :=
  extCall_denote_via_leaf (mlkemFieldRegistry hagree) reduceName (reduceLeaf hagree)
    (mlkemFieldRegistry_resolves hagree) rfl args V

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxField
