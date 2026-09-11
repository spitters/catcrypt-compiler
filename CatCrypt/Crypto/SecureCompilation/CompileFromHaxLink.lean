/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C8: the leaf registry and linker for the two crypto-authoring fronts

CatCrypt grows verified crypto kernels through **two complementary fronts**:

* **compile-from-hax** (`CompileFromHax.lean`, C2/C3): a hax-extracted `ImpExpr`
  is compiled value-preservingly into a `Com jasminDialect`. This is the *outer*
  authoring front — whole crypto functions written in Rust and lowered.
* **author-in-Com** fast leaves (`FAEST/Leaves.lean`, `LatticeToJasminDenote`,
  the `VIR/*Emit.lean` kernels): a hand-tuned, separately-verified `Com` (or its
  spec) for a single named primitive (NTT, AES-128, SHAKE, a field multiply…).

The two fronts meet at the **`extCall` seam**. A compiled-from-hax outer `Com`
that calls a fast leaf `f` (via the front's `Rhs.call "f" args`, lowered to the
dialect's `extCall "f"`) contains an opaque `extCall "f"` node whose denotation
is `jasminExtSem "f" …` — an **opaque constant**. The outer compiler proves the
outer is value-preserving *relative to that opaque call*; it says nothing about
what `f` actually computes.

**Linking** closes the seam: a *leaf registry* maps each call `name` to a
verified `LeafSpec` — the leaf's intended semantics `spec` together with the
**agreement** proof `jasminExtSem name … = spec`. Substituting each opaque call
by its leaf spec makes the whole-primitive denotation spec-defined rather than
opaque. This module builds the registry, the linking meta-theorem, and a toy
worked example.

## What is mechanized vs. what is the author's obligation

* **Mechanized (this file):** the *linking composition*. Given a registry that
  resolves a call to a leaf whose `agrees` holds, the linker rewrites the
  opaque `extCall`-node's denotation to the leaf's `spec` (`extCall_denote_via_leaf`),
  and composes the outer's `compileFromHax`-style value-preservation with the
  leaf agreement into one whole-primitive statement (`linked_example`).
* **The author's obligation (a hypothesis, never an axiom):** the per-leaf
  `agrees : jasminExtSem name … = spec`. `jasminExtSem` is an opaque constant on
  every non-lattice leaf name, so this equality is *not* provable here — it is
  exactly the proof a fast-leaf author discharges (for a real leaf like the NTT
  it is the negacyclic-convolution theorem; for AES-128 it is the validated
  libjade/jasmin leaf KAT, cf. `FAEST.Leaves.AesLeafAgrees`). We therefore take
  `agrees` as a *field of the registry entry* / a *hypothesis of the linking
  lemma*, not an `axiom`. Linking is honest: it composes a proved outer with a
  *carried* leaf obligation; it never invents the leaf's meaning.

This mirrors the existing leaf-agreement vocabulary —
`LatticeToJasminDenote.LeafAgrees`, `JasminPrintSemCorrect.LeafAgrees`, and
`FAEST.Leaves.FaestLeafAgrees` — and lifts it to the *registry* level so a whole
outer `Com` can be linked against a *map* of leaves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink

open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## §1  Argument view: a homogeneous call `HVector` as a `Fin n → BitVec w`

A width-`w` front call with `n` arguments resolves its operands to
`HVector (fun t => ⟦t⟧) (callArgTys w n)`, where `callArgTys w n = replicate n
(rW w)` and `⟦rW w⟧ = BitVec w`. A `LeafSpec`'s intended semantics is more
naturally a function of the `n` `BitVec w` arguments, so we expose the canonical
view `hvToFun` turning the call `HVector` into a `Fin n → BitVec w`. -/

/-- The `i`-th `BitVec w` argument of a homogeneous call `HVector` indexed by
    `callArgTys w n = replicate n (rW w)`. Recurses on `n`/the HVector together;
    `Fin n` guarantees the head/tail peel is well-typed at each step. -/
def hvNth {w : Nat} :
    (n : Nat) → HVector (fun t => ⟦t⟧) (callArgTys w n) → Fin n → BitVec w
  | 0,     _,    i => i.elim0
  | n + 1, args, i =>
      -- `callArgTys w (n+1) = rW w :: callArgTys w n`, so `args` is a `cons`.
      Fin.cases (args.head : ⟦rW w⟧) (fun j => hvNth n args.tail j) i

/-- The canonical view of a homogeneous call `HVector` as a `Fin n → BitVec w`. -/
def hvToFun {w n : Nat} (args : HVector (fun t => ⟦t⟧) (callArgTys w n)) :
    Fin n → BitVec w :=
  hvNth n args

/-! ## §2  The leaf and the registry

A `LeafSpec w` is one fast leaf: the call `name`, its arity `n`, the intended
semantics `spec` (a function of the `n` `BitVec w` arguments), and the
**agreement** field `agrees` tying the opaque `jasminExtSem name …` to `spec`.
`agrees` is the per-leaf proof obligation the fast author discharges; it lives in
the structure so a populated registry is by construction a registry of *verified*
leaves. -/

/-- A verified fast leaf at width `w`: a named external call, its arity, intended
    `BitVec w` semantics, and the agreement proof that the opaque dialect call
    `jasminExtSem name (callArgTys w n) (rW w)` computes exactly `spec` of its
    arguments (viewed via `hvToFun`). The `agrees` field is the per-leaf
    obligation — for a real leaf it is the kernel's correctness theorem (NTT
    convolution, AES KAT, …). -/
structure LeafSpec (w : Nat) where
  /-- The external call name this leaf resolves (`extCall name`). -/
  name : String
  /-- The leaf's arity: the number of `rW w` arguments. -/
  n : Nat
  /-- The leaf's intended semantics, a function of its `n` `BitVec w` arguments. -/
  spec : (Fin n → BitVec w) → BitVec w
  /-- **The per-leaf obligation.** The opaque dialect call semantics
      `jasminExtSem name …` equals `spec` of the arguments (under `hvToFun`).
      Carried, not an axiom: `jasminExtSem` is opaque on a genuine leaf name, so
      this equality is the fast author's correctness proof. -/
  agrees : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys w n)),
      (jasminExtSem name (callArgTys w n) (rW w) args : ⟦rW w⟧)
        = spec (hvToFun args)

/-- A leaf registry at width `w`: a partial map from a call `name` to its
    verified leaf. A populated entry is *by construction* a verified leaf (it
    carries `agrees`), so the registry is the set of currently-linkable leaves. -/
def LeafRegistry (w : Nat) := String → Option (LeafSpec w)

/-- The empty registry resolves nothing. -/
def LeafRegistry.empty (w : Nat) : LeafRegistry w := fun _ => none

/-- Register a leaf `ls` under its own `name`, shadowing any prior binding. -/
def LeafRegistry.insert {w : Nat} (R : LeafRegistry w) (ls : LeafSpec w) :
    LeafRegistry w :=
  fun nm => if nm = ls.name then some ls else R nm

/-- A registry *resolves* `name` to leaf `ls` when it maps `name` to `some ls`
    *and* `ls`'s own name is `name` (well-formed entry — its agreement is about
    the call it is keyed under). -/
def Resolves {w : Nat} (R : LeafRegistry w) (name : String) (ls : LeafSpec w) :
    Prop := R name = some ls ∧ ls.name = name

/-- A freshly-inserted leaf is resolved by the extended registry. -/
theorem insert_resolves {w : Nat} (R : LeafRegistry w) (ls : LeafSpec w) :
    Resolves (R.insert ls) ls.name ls := by
  refine ⟨?_, rfl⟩
  simp [LeafRegistry.insert]

/-! ## §3  The linking lemma at the `extCall`-node level

The dialect's `extCall name (callArgTys w n) (rW w)` op denotes (by
`jasminDenote`) to `jasminExtSem name (callArgTys w n) (rW w)` of its resolved
arguments. So an `extCall`-node `Expr` denotes to that opaque constant; the leaf
`agrees` rewrites it to the leaf `spec`. This is the FAEST `*LeafExpr_denote`
pattern (an `extCall`'s `Expr.denote` is `jasminExtSem` by `rfl`) followed by the
registry's resolved agreement. -/

/-- Build the `extCall "name"` leaf `Expr` from a homogeneous argument `Var`
    `HVector` (`n` copies of `rW w`) in scope. The shape the front's `Rhs.call`
    lowering (`rhsExpr (.call …)`) produces. -/
def extCallExpr {w n : Nat} {Γ : Ctxt jasminDialect}
    (name : String)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (callArgTys w n)) :
    Expr jasminDialect Γ (rW w) :=
  { op := .extCall name (callArgTys w n) (rW w)
    retTy_eq := rfl
    args := args }

/-- The `extCall` leaf `Expr` denotes (under any valuation) to `jasminExtSem` of
    its resolved arguments — the dialect's opaque-leaf semantics. By `rfl`:
    `Expr.denote` of an `extCall` (with `retTy_eq = rfl`) is `jasminExtSem`
    applied to `Expr.lookupArgs`. This is the bridge point a concrete leaf
    discharges via its `agrees`. -/
theorem extCallExpr_denote {w n : Nat} {Γ : Ctxt jasminDialect}
    (name : String)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (callArgTys w n))
    (V : Ctxt.Valuation Γ) :
    (extCallExpr (w := w) (n := n) name args).denote V
      = jasminExtSem name (callArgTys w n) (rW w) (Expr.lookupArgs args V) :=
  rfl

/-- **The linking lemma (`extCall`-node level).** When a registry `R` resolves a
    call `name` to a verified leaf `ls`, the opaque `extCall name`-node's
    denotation equals `ls.spec` applied to its denoted arguments. The leaf's
    `agrees` rewrites the opaque `jasminExtSem` occurrence to `spec` — the
    opaque call is *linked* to the verified leaf's meaning. -/
theorem extCall_denote_via_leaf {w n : Nat} {Γ : Ctxt jasminDialect}
    (R : LeafRegistry w) (name : String) (ls : LeafSpec w)
    (hres : Resolves R name ls) (hn : ls.n = n)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (callArgTys w n))
    (V : Ctxt.Valuation Γ) :
    (extCallExpr (w := w) (n := n) name args).denote V
      = (hn ▸ ls.spec) (hvToFun (Expr.lookupArgs args V)) := by
  subst hn
  obtain ⟨_, hname⟩ := hres
  subst hname
  rw [extCallExpr_denote, ls.agrees (Expr.lookupArgs args V)]

/-! ## §4  The `link` skeleton: folding resolution over a call list

The mechanical composition step. `linkNames R names` resolves *every* call name
in `names` against the registry, returning the list of verified leaves (or
`none` on the first unresolved name). For the toy outer below the list has one
entry; the fold is the skeleton a multi-call outer drives. The value of the
linker is the lemma above plus this honest "every call resolves to a verified
leaf" gate. -/

/-- Resolve a list of call names against the registry, collecting the verified
    leaves. `none` on the first unresolved name (an unlinked call — its meaning
    would remain opaque). The mechanical composition skeleton over the calls of
    an outer `Com`. -/
def linkNames {w : Nat} (R : LeafRegistry w) :
    List String → Option (List (LeafSpec w))
  | [] => some []
  | nm :: rest =>
      (R nm).bind fun ls => (linkNames R rest).map fun lss => ls :: lss

/-- Linking a single fully-resolved name yields the singleton leaf list. -/
theorem linkNames_singleton {w : Nat} (R : LeafRegistry w) (name : String)
    (ls : LeafSpec w) (h : R name = some ls) :
    linkNames R [name] = some [ls] := by
  simp [linkNames, h]

/-! ## §5  The toy worked example

The smallest outer with one `extCall`, linked to one verified leaf.

* **Outer:** `let r = f(inp[0]); ret r` — a single-argument external call to `f`.
  We build it directly through the front (`ThirToComFront`): a `Thir` with one
  `Rhs.call "f" [inp 0]`, lowered by `thirToJasmin` at the empty local scope
  with `nIn = 1`, width `w`. The front's value-preservation theorem
  (`thirToJasmin_denote`, via `initAgree`) ties the outer `Com`'s denotation to
  the THIR denotation, which is `jasminExtSem "f" …` of the input — the opaque
  call.
* **Leaf:** `spec_f x = x + x`, registered under `"f"`. Its `agrees` —
  `jasminExtSem "f" … = (· + ·)`-shaped — is taken as a **hypothesis**, not an
  axiom: `jasminExtSem "f"` is opaque (the `_, _, retTy => default` arm), so this
  equality is precisely what a real `f`-leaf author would prove. Here it stands
  for that obligation.
* **Result (`linked_example`):** *given* the leaf agreement, the whole compiled
  outer's denotation is the spec-defined value `spec_f (inp[0]) = x + x`. The
  registry+linker has composed the outer's value-preservation with the leaf's
  agreement into one whole-primitive statement. -/

/-- The single external call name of the toy outer. -/
def fName : String := "f"

/-- The toy outer THIR: `let r = f(inp[0]); ret r`. One single-argument external
    call to `f`, returning its result. -/
def outerThir : Thir :=
  .let_ "r" (.call fName [.inp 0]) (.ret (.lvar "r"))

/-- The toy outer compiles (the front lowering returns `some`) at any width `w`
    with `nIn = 1`. The body is a closed straight-line term, so the lowering is
    computed. -/
theorem outerThir_lowers (w : Nat) :
    (thirToJasmin (w := w) (nIn := 1) [] (initFState w 1) outerThir).isSome := by
  -- `f(inp 0)` resolves its one argument `inp 0` to a `Var` (input word 0 of a
  -- 1-word file), so `rhsExpr (.call …)` and then the `ret` both succeed.
  simp only [outerThir, thirToJasmin, rhsExpr, atomsToVarHV, Atom.toVar,
    initFState, FState.push, inputVarRep, Option.map_some, if_true]
  rfl

/-- The toy outer `Com` (the front's output) at width `w`. -/
def outerCom (w : Nat) : Com jasminDialect (frontCtxt w 1 []) (rW w) :=
  (thirToJasmin (w := w) (nIn := 1) [] (initFState w 1) outerThir).get
    (outerThir_lowers w)

/-- The leaf's intended semantics: `spec_f x = x + x` (a single-argument leaf).
    Any concrete `BitVec w` function would do; `x + x` is a stand-in for a real
    fast leaf (a field doubling, a rotate, an NTT step…). -/
def spec_f {w : Nat} : (Fin 1 → BitVec w) → BitVec w := fun a => a 0 + a 0

/-- **The toy outer's value-preservation, relative to the opaque call.** For any
    input `x`, the compiled outer `Com` denotes to `jasminExtSem "f" …` applied
    to `x` — the opaque external-call value, *before* linking. This is the
    `compileFromHax`-style outer obligation (here proved via the front
    `thirToJasmin_denote`): the outer is correct *relative to* the call `f`. -/
theorem outerCom_denote_opaque (w : Nat) (x : BitVec w) :
    (outerCom w).denote (inputValuation w 1 (fun _ => x))
      = jasminExtSem fName (callArgTys w 1) (rW w)
          (HVector.cons (x : ⟦rW w⟧) HVector.nil) := by
  -- The front's value-preservation: `Thir.denote = Com.denote` for the outer.
  have hc : thirToJasmin (w := w) (nIn := 1) [] (initFState w 1) outerThir
      = some (outerCom w) := (Option.some_get _).symm
  have hfront := thirToJasmin_denote (w := w) (nIn := 1) []
    (fun _ => x) outerThir (LEnv.empty w) (initFState w 1)
    (inputValuation w 1 (fun _ => x)) (outerCom w) (initAgree (fun _ => x)) hc
  -- The THIR denotation of `let r = f(inp 0); ret r` is `jasminExtSem "f" …` of
  -- the input word `x` (`inpGet (fun _ => x) 0 = x`).
  have hthir : Thir.denote (w := w) (nIn := 1) (fun _ => x) outerThir (LEnv.empty w)
      = some (jasminExtSem fName (callArgTys w 1) (rW w)
          (HVector.cons (x : ⟦rW w⟧) HVector.nil)) := by
    have hx : inpGet (nIn := 1) (fun _ => x) 0 = x := by
      simp only [inpGet, show (0 : Nat) < 1 by decide, dif_pos]
    simp only [outerThir, Thir.denote, Rhs.denote, atomsHV, Atom.denote, hx,
      Option.bind_some, Option.map_some, LEnv.set, if_pos]
    rfl
  rw [hthir] at hfront
  exact (Option.some.injEq _ _ ▸ hfront).symm

/-- The registry holding exactly the toy leaf for `"f"`, given its agreement.
    The agreement is the **hypothesis** `hagree` — the fast author's obligation —
    threaded into the `LeafSpec.agrees` field. -/
def toyRegistry {w : Nat}
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys w 1)),
        (jasminExtSem fName (callArgTys w 1) (rW w) args : ⟦rW w⟧)
          = spec_f (hvToFun args)) :
    LeafRegistry w :=
  (LeafRegistry.empty w).insert
    { name := fName, n := 1, spec := spec_f, agrees := hagree }

/-- **The toy linked example — the linker composes.** *Given* the per-leaf
    agreement `hagree` (the fast author's obligation, a hypothesis — not an
    axiom, since `jasminExtSem "f"` is opaque), the whole compiled outer's
    denotation is the **spec-defined** value `spec_f x = x + x` for every input
    `x`. The outer's value-preservation (`outerCom_denote_opaque`) is composed
    with the leaf agreement (`hagree`) into one whole-primitive statement: the
    registry+linker has turned the opaque-call outer into a spec-defined kernel. -/
theorem linked_example {w : Nat}
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys w 1)),
        (jasminExtSem fName (callArgTys w 1) (rW w) args : ⟦rW w⟧)
          = spec_f (hvToFun args))
    (x : BitVec w) :
    (outerCom w).denote (inputValuation w 1 (fun _ => x)) = x + x := by
  -- Step 1 (mechanized): outer value-preservation relative to the opaque call.
  rw [outerCom_denote_opaque w x]
  -- Step 2 (the carried leaf obligation): link the opaque call to the spec.
  rw [hagree (HVector.cons (x : ⟦rW w⟧) HVector.nil)]
  -- Step 3 (compute): `spec_f` of the single argument `x` is `x + x`.
  show spec_f (hvToFun (HVector.cons (x : ⟦rW w⟧) HVector.nil)) = x + x
  simp only [spec_f, hvToFun, hvNth, Fin.cases_zero]
  rfl

/-- The toy registry resolves `"f"` to the toy leaf (the registry side of the
    composition: the call `f` is linkable). -/
theorem toyRegistry_resolves {w : Nat}
    (hagree : ∀ (args : HVector (fun t => ⟦t⟧) (callArgTys w 1)),
        (jasminExtSem fName (callArgTys w 1) (rW w) args : ⟦rW w⟧)
          = spec_f (hvToFun args)) :
    Resolves (toyRegistry hagree) fName
      { name := fName, n := 1, spec := spec_f, agrees := hagree } :=
  insert_resolves (LeafRegistry.empty w) _

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxLink
