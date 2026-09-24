/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote

/-!
# De-specialized compiler-correctness theorem: generic dialect-lowering correctness

The lattice theorem `compile_correct_all`
(`CatCrypt/Crypto/SecureCompilation/VIR/Compiler.lean`) is the end-to-end
statement *"running the emitted owned jasmin program reads back the source
denotation"* — but **only for the one lattice route** (`lowerLatticeToJasmin`,
`mapTy = tau`, `mapCtx = (·.map tau)`). This module proves the **general**
theorem of which it is an instance.

## What is de-specialized

The lattice route's correctness is, structurally, two composable facts:

1. **Whole-program transport** — the dialect lowering preserves denotation:
   `(lower c).denote (mapVal V) = transTy (c.denote V)`. For the lattice route
   this is `lowerLatticeToJasmin_denote_eq`; the *generic* form is
   `ComParametricityTransport.fundamental`, which lifts the per-op leaf squares
   (`VarTransports` / `OpLowerTransports` / `MapValExtends`) to the whole `Com`
   by induction on the program skeleton, for **any** structural
   `LoweringData d jasminDialect`.

2. **Owned backend execution** — running the emitted single-function jasmin
   program equals its `Com.denote`: `runProg leafSem com V = com.denote V`. This
   is `WholeFnLowering.lowerComToProg_sem_eq'`, the **owned** whole-function
   backend (no jasminc), generic over the jasmin `Com` (it needs only
   `StraightLine` and the opaque-leaf agreement edge; both SSA-naming
   side-conditions are discharged inside it).

Composing (1) ∘ (2) gives, for an arbitrary source dialect `d` and an arbitrary
structural lowering `L : LoweringData d jasminDialect`:

    runProg leafSem (L.lowerCom c) (mapVal V) = transTy (c.denote V)

i.e. **the owned-emitted artifact computes the transport of the source
denotation** — the CompCert-shape equation, independent of the lattice poly
type. `compileVia`/`compileVia_correct` below are exactly this. The lattice
theorem is recovered by instantiating at the lattice maps (`§3`).

## Scope

* **Owned backend only.** Execution goes through
  `WholeFnLowering.runProg`/`lowerComToProg_sem_eq'`. No `jasminc`, no `.jazz`
  pretty-printing, no `jasminc_preserves_ct` anywhere.
* The generic theorem carries, as **explicit hypotheses**, exactly the
  obligations its two ingredients need: the three leaf/coherence squares of
  `fundamental` and the `StraightLine` + jasmin opaque-leaf-agreement
  (`JasminPrintSemCorrect.LeafAgrees`) of `lowerComToProg_sem_eq'`.
* This is the **dialect-level + owned-execution** theorem. The per-slot
  structured read-back (`runOutputToWords`) and the per-ISA Sail validation that
  `Compiler.compile_correct_all` additionally folds in are *downstream* of this
  equation (they post-compose a read-back and assert a model `validated` field);
  they are **not** re-stated here; this module states the generic
  dialect-lowering + owned-run correctness.
* All proofs are complete; target axiom set
  `{propext, Classical.choice, Quot.sound}`, no custom axioms.

For the §3 lattice recovery: the lattice route's maps are
*standalone defs* (`LatticeToJasminDenote.transTy`/`mapVal`,
`LatticeToJasmin.mapVar`/`lowerExpr`/`lowerLatticeToJasmin`) rather than fields
of a named `LoweringData`. We package them into `latticeLoweringData` here and
show its `lowerCom` agrees with `lowerLatticeToJasmin`, so `compileVia` at
`latticeLoweringData` *is* the lattice compile — making the lattice theorem a
literal instance of `compileVia_correct`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.WholeFnLowering

variable {d : Dialect}
variable [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-! ## 1. The de-specialized compile

`compileVia L c` is the dialect lowering `L.lowerCom c` — the emitted jasmin
`Com`. Its codomain follows `L.mapCtx`/`L.mapTy`, **not** the fixed lattice poly
type; that is the whole point of de-specialization. -/

/-- **The de-specialized compile.** Lower a source-dialect program `c` across an
    arbitrary structural lowering `L` into jasmin. Codomain is determined by
    `L.mapCtx`/`L.mapTy`. This is the generic analogue of `Compiler.compile`'s
    lattice branch (`lowerLatticeToJasmin`), with the lattice maps abstracted
    into the parameter `L`. -/
def compileVia (L : LoweringData d jasminDialect) {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) : Com jasminDialect (L.mapCtx Γ) (L.mapTy t) :=
  L.lowerCom c

/-! ## 2. The generic correctness theorem

The abstracted lattice proof: `fundamental` (whole-program transport) composed
with `lowerComToProg_sem_eq'` (owned backend execution). -/

/-- **`compileVia_correct` — the generic dialect-lowering + owned-execution
    correctness theorem.**

    For an arbitrary source dialect `d`, an arbitrary structural lowering
    `L : LoweringData d jasminDialect` with value transport `transTy` and
    valuation transport `mapVal`, the **owned**-emitted jasmin program
    `compileVia L c`, run under a word-level evaluator `leafSem`, computes the
    `transTy`-transport of the source program's denotation:

        runProg leafSem (compileVia L c) (mapVal V) = transTy (c.denote V)

    The hypotheses are exactly those of the two ingredients, none by fiat:
    * the three transport squares `hVar`/`hOp`/`hExt` that
      `ComParametricityTransport.fundamental` needs (per-op leaves);
    * `hStraight` (the lowered jasmin program is straight-line) and `hJLeaf`
      (the jasmin opaque-`extCall` leaves agree with `leafSem`) that the owned
      whole-function backend `lowerComToProg_sem_eq'` needs.

    This is `Compiler.compile_correct_all`'s lattice body with the lattice
    `LoweringData` replaced by the parameter `L`: `fundamental L … V` rewrites
    the lowered denotation to `transTy (c.denote V)`, and
    `lowerComToProg_sem_eq'` bridges `runProg … = (lowered).denote …`. No
    `jasminc`. -/
theorem compileVia_correct
    (L : LoweringData d jasminDialect)
    (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : OpLowerTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal)
    {leafSem : LeafSem} (hJLeaf : JasminPrintSemCorrect.LeafAgrees leafSem)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (hStraight : StraightLine (compileVia L c))
    (V : Ctxt.Valuation Γ) :
    runProg leafSem (compileVia L c) (mapVal V) = transTy (c.denote V) := by
  -- Owned backend: `runProg leafSem (lowered) (mapVal V) = (lowered).denote (mapVal V)`.
  rw [lowerComToProg_sem_eq' hJLeaf (compileVia L c) hStraight (mapVal V)]
  -- Whole-program transport square: `(lowered).denote (mapVal V) = transTy (c.denote V)`.
  exact fundamental L transTy mapVal hVar hOp hExt c V

/-! ## 3. The lattice theorem as a literal instance

The lattice route's maps (`tau`, `mapVar`, `lowerExpr`) are standalone defs, not
fields of a `LoweringData`. We package them here into `latticeLoweringData` and
show its canonical `lowerCom` *is* `lowerLatticeToJasmin` — so `compileVia` at
`latticeLoweringData` is exactly the lattice compile, and `compileVia_correct`
specializes to the (owned) lattice end-to-end equation. -/

open CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote

/-- **The lattice lowering, packaged as a `LoweringData`.** `mapTy = tau`,
    `mapCtx = (·.map tau)` (with `cons` commuting by `rfl`), and the variable /
    expression leaves are the existing `LatticeToJasmin.mapVar` / `lowerExpr`.
    This is the `L` for which `compileVia L = lowerLatticeToJasmin`. -/
def latticeLoweringData : LoweringData latticeDialect jasminDialect where
  mapTy := tau
  mapCtx := fun Γ => Γ.map tau
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => mapVar v
  lowerExpr := fun e => lowerExpr e

/-- The packaged lattice lowering's canonical `Com` recursion **is**
    `lowerLatticeToJasmin`: both map `.ret v ↦ .ret (mapVar v)` and
    `.var e body ↦ .var (lowerExpr e) (recurse body)`, and `mapCtx_cons` is
    `rfl` so the `▸` cast in `LoweringData.lowerCom` vanishes. By `Com`
    induction. -/
theorem latticeLoweringData_lowerCom {Γ : Ctxt latticeDialect} {t : LatticeTy} :
    ∀ (c : Com latticeDialect Γ t),
      latticeLoweringData.lowerCom c = lowerLatticeToJasmin c
  | .ret _ => rfl
  | .var e body =>
      congrArg (Com.var (lowerExpr e)) (latticeLoweringData_lowerCom body)


/-- `compileVia` at the packaged lattice lowering is exactly the lattice compile
    `lowerLatticeToJasmin`. -/
theorem compileVia_lattice {Γ : Ctxt latticeDialect} {t : LatticeTy}
    (c : Com latticeDialect Γ t) :
    compileVia latticeLoweringData c = lowerLatticeToJasmin c :=
  latticeLoweringData_lowerCom c

/-- The lattice variable square is the existing `mapVal_lookup`. -/
theorem latticeVarTransports :
    VarTransports latticeLoweringData
      (fun {_t} v => transTy v) (fun {_Γ} V => mapVal V) :=
  fun v V => mapVal_lookup v V

/-- The lattice binding-threading square is the existing `mapVal_extend`. -/
theorem latticeMapValExtends :
    MapValExtends latticeLoweringData
      (fun {_t} v => transTy v) (fun {_Γ} V => mapVal V) :=
  fun V x => mapVal_extend V x

/-- **The lattice theorem, recovered as an instance of `compileVia_correct`.**

    Under the lattice op-leaf square (`LatticeToJasminDenote.LeafAgrees`,
    i.e. `OpLowerTransports` for the lattice lowering) and the **owned** jasmin
    backend's straight-line + opaque-leaf-agreement hypotheses, running the
    lattice-emitted jasmin program computes the `transTy`-transport of the source
    lattice program's denotation:

        runProg leafSem (lowerLatticeToJasmin c) (mapVal V) = transTy (c.denote V)

    This is the de-specialized `compileVia_correct` at `latticeLoweringData`,
    rewritten through `compileVia_lattice`. It demonstrates that the lattice
    route is a *literal* instance of the generic theorem — the lattice-specific
    `latticeNttMul_compile_correct` / `compile_correct_all` body is reproduced
    here with the lattice maps abstracted into the parameter `L` of §2.

    The lattice `OpLowerTransports` hypothesis `hLatLeaf` is unconditionally
    dischargeable downstream (`LatticeToJasminDenoteUncond` proves the concrete
    `extCall`-spec'd version); we carry it as a hypothesis to keep this file's
    import surface to the parametric layer. -/
theorem latticeKeystone_via
    (hLatLeaf : OpLowerTransports latticeLoweringData
      (fun {_t} v => transTy v) (fun {_Γ} V => mapVal V))
    {leafSem : LeafSem} (hJLeaf : JasminPrintSemCorrect.LeafAgrees leafSem)
    {Γ : Ctxt latticeDialect} {t : LatticeTy} (c : Com latticeDialect Γ t)
    (hStraight : StraightLine (lowerLatticeToJasmin c))
    (V : Ctxt.Valuation Γ) :
    runProg leafSem (lowerLatticeToJasmin c) (mapVal V) = transTy (c.denote V) := by
  have hStraight' : StraightLine (compileVia latticeLoweringData c) := by
    rw [compileVia_lattice]; exact hStraight
  have h := compileVia_correct latticeLoweringData
    (fun {_t} v => transTy v) (fun {_Γ} V => mapVal V)
    latticeVarTransports hLatLeaf latticeMapValExtends hJLeaf c hStraight' V
  rw [compileVia_lattice] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.VIR.CompilerGeneric
