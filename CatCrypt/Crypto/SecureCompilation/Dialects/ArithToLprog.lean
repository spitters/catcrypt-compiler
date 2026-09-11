/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.ArithToJasminDenote
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# `Com(arith) → Lprog(jasmin)` — the D6 jasmin sibling backend

The D6 phase of the MLIR dialect-alignment restructure keeps the **linearized
jasmin** target (`Lprog`) as a *sibling* backend descending from the neutral,
upstream-aligned `arith` mid-level, **parallel to the owned x86 target**. Both
backends start from the same neutral `Com arithDialect` program; this file wires
the jasmin sibling:

```text
            Com arithDialect Γ t            -- the neutral mid-level (D0 gate)
           /                    \
   lowerArithToJasmin       (owned x86 ISel, separate file)
           |
   Com jasminDialect ...           -- verified, denotation-preserving (D0)
           |
        Com.toLprog                -- existing jasmin-Com linearizer
           |
          Lprog                    -- linearized jasmin (the `jasminc`-fed form)
```

The point of D6 is the **perf comparison** against `jasminc`'s own pipeline and
the `jasminc_preserves_ct` anchor: by descending the jasmin `Lprog` from the
*same* neutral `arith` mid-level as the owned x86 path, the two targets share a
common, verified front half (`lowerArithToJasmin`) and diverge only in the
target-native back half.

## What composes, and what does not (honest provenance)

The composed lowering `arithToLprog` reuses two existing pieces:

* **Front half — `lowerArithToJasmin` (`ArithToJasmin.lean` /
  `ArithToJasminDenote.lean`)** is a *verified, denotation-preserving*
  `Com arithDialect → Com jasminDialect` lowering. `lowerArithToJasmin_denote`
  proves it preserves `Com.denote` exactly (the per-value transport `transTy` is
  the identity, so there is no value drift). This half is fully proved.

* **Back half — `Com.toLprog` (`VIR/JasminLprogExport.lean`)** is a *total*
  `Com jasminDialect → Lprog` linearizer. Its proved guarantees are
  **structural**: `Com.toLprog_wf` (exactly one export function with the given
  name), `Com.toLprog_body_ends_Lret` (the emitted body ends with `Lret`). Its
  *semantic*-preservation across `Com.toLprog` is the proved predicate
  `ComLsemExportFaithful` (`VIR/JasminLsemGeneralFaithful.lean`, with the
  `…MC` / `…Leaf` fragment extensions) over jasmin's program-indexed linear
  semantics `lsem` — established for the modeled straight-line / mul-carry /
  ScalarLeafN fragments. For Coms outside those fragments, whole-program
  denotation preservation across `Com.toLprog` is not yet covered in-tree.

Consequently, the preservation we obtain *for free* for `arithToLprog` is the
**composition of the verified front-half denote-preservation with the
structural back-half well-formedness** — stated honestly below. The full
end-to-end `Com.denote = lsem (arithToLprog …)` holds for the fragments
`ComLsemExportFaithful[MC/Leaf]` covers; the back half is otherwise structural.

## Relationship to the CT anchor

The `jasminc_preserves_ct` axiom (`SecureCompilation/JasminCompilerBridge.lean`)
is stated over the separate `Jasmin/` AST (`JasminProg` + `isCT_Cmd`), *not* over
`Lprog`. So this file does **not** discharge a CT obligation; it positions the
`Lprog` sibling at the point in the pipeline that feeds `jasminc`, whose CT
preservation is the trusted anchor. The contribution here is the *neutral-mid-
level provenance* of the jasmin target — it now descends from `arith`, sibling to
the owned x86 backend — together with the structural + front-half-denote
guarantees that compose through.

0 sorries, 0 axioms. Semantic preservation across `Com.toLprog` is the proved
`ComLsemExportFaithful[MC/Leaf]` predicate over `lsem` for its modeled
fragments, not an axiom.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Arith

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## 1. The sibling lowering `Com(arith) → Lprog(jasmin)`

Compose the verified `lowerArithToJasmin` (neutral `arith` → `Com jasminDialect`)
with the existing total `Com.toLprog` linearizer. The optional `immSlotMap`
(immediate-slot substitution, see `JasminLprogExport.ImmSlotMap`) is threaded
through to the back half. -/

/-- **The D6 jasmin sibling lowering.** Lower a neutral-`arith` program straight
    to linearized jasmin `Lprog`, by composing the verified arith→jasmin dialect
    lowering with the existing jasmin-Com linearizer `Com.toLprog`. This is the
    `Lprog` target descending from the same neutral mid-level as the owned x86
    backend. -/
def arithToLprog {Γ : Ctxt arithDialect} {t : ArithTy}
    (com : Com arithDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) : Lprog :=
  Com.toLprog (lowerArithToJasmin com) fname immSlotMap

/-! ## 2. Preservation that composes through

The front half is denote-preserving (`lowerArithToJasmin_denote`); the back half
is structurally well-formed (`Com.toLprog_wf`, `Com.toLprog_body_ends_Lret`).
Each composes into a statement about `arithToLprog`. The whole-program *semantic*
preservation across the back half is the proved `ComLsemExportFaithful[MC/Leaf]`
predicate over `lsem`, for the fragments those predicates model. -/

/-- **Structural well-formedness composes through.** `arithToLprog` always emits
    exactly one function, named `fname`, marked as an export — inherited verbatim
    from `Com.toLprog_wf` applied to the lowered jasmin program. -/
theorem arithToLprog_wf {Γ : Ctxt arithDialect} {t : ArithTy}
    (com : Com arithDialect Γ t) (fname : String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    (arithToLprog com fname immSlotMap).lp_funcs.length = 1 ∧
      ((arithToLprog com fname immSlotMap).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((arithToLprog com fname immSlotMap).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) :=
  Com.toLprog_wf (lowerArithToJasmin com) fname

/-- **The emitted body ends with `Lret`.** The control-flow legality the
    linearizer requires (every function body terminates in `Lret`) composes
    through to the arith sibling. (Stated for the default immediate-slot map, the
    form `Com.toLprog_body_ends_Lret` proves.) -/
theorem arithToLprog_body_ends_Lret {Γ : Ctxt arithDialect} {t : ArithTy}
    (com : Com arithDialect Γ t) :
    ((comToLfundef (lowerArithToJasmin com)).lfd_body).getLast?.map Linstr.li_i
      = some .Lret :=
  Com.toLprog_body_ends_Lret (lowerArithToJasmin com)

/-- **Front-half denote preservation (verified, exact).** The denotation of the
    *jasmin program* that `arithToLprog` linearizes equals `transTy` of the
    original arith program's denotation — i.e. the part of the pipeline preceding
    `Com.toLprog` carries the source semantics with no drift. This is the verified
    half of the sibling lowering; it is exactly `lowerArithToJasmin_denote`,
    restated for the program fed into the linearizer.

    (The remaining `lsem (arithToLprog …) = ⟦jasmin program⟧` step across
    `Com.toLprog` is the proved `ComLsemExportFaithful[MC/Leaf]` predicate over
    jasmin's linear semantics, for the fragments it models — see this file's
    module docstring.) -/
theorem arithToLprog_jasmin_denote {Γ : Ctxt arithDialect} {t : ArithTy}
    (com : Com arithDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerArithToJasmin com).denote (mapVal V) = transTy (com.denote V) :=
  lowerArithToJasmin_denote com V

/-! ## 3. Worked example — the arith `smokeProg` through the sibling backend

Lower the two-input `smokeProg` (`a + b` over `[i32, i32]`, from `Arith.lean`) to
`Lprog` and check the structural shape (`#eval`-able + `rfl`-provable). -/

/-- The `smokeProg` lowered to its jasmin `Lprog` sibling form. -/
def smokeLprog : Lprog := arithToLprog smokeProg "arith_smoke_add"

-- One export function, named, body terminates in `Lret`.
example : smokeLprog.lp_funcs.length = 1 := rfl
example : smokeLprog.lp_funcs.head?.map Prod.fst = some "arith_smoke_add" := rfl
example :
    (arithToLprog_wf smokeProg "arith_smoke_add").2.2
      = (show smokeLprog.lp_funcs.head?.map (fun p => p.2.lfd_export) = some true from rfl) :=
  rfl
example :
    ((comToLfundef (lowerArithToJasmin smokeProg)).lfd_body).getLast?.map Linstr.li_i
      = some .Lret :=
  arithToLprog_body_ends_Lret smokeProg

-- The front half preserves the denotation of the smoke program (`7 + 35 = 42`),
-- so the linearized sibling is built on a semantics-preserving front.
example :
    (lowerArithToJasmin smokeProg).denote
        (mapVal (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil)))
      = transTy (smokeProg.denote (.cons (7 : BitVec 32) (.cons (35 : BitVec 32) .nil))) :=
  arithToLprog_jasmin_denote smokeProg _

-- Evaluable end to end: the emitted linear body is a concrete instruction list.
#eval smokeLprog.lp_funcs.length
#eval (smokeLprog.lp_funcs.head?.map (fun p => p.2.lfd_body.length)).getD 0
#eval Lprog.toText smokeLprog

end CatCrypt.Crypto.SecureCompilation.Dialects.Arith
