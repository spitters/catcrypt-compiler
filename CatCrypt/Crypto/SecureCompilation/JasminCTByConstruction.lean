/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The index-free fragment of `Com jasminDialect` is constant-time by construction

`ThirCTByConstruction` shows the front IR (`thirDialect`) is CT by construction
*unconditionally* — it has no op that can branch or index on data. The next IR
down, `jasminDialect`, is **not** unconditionally CT: it adds two
data-indexed memory ops, `stackLoad` / `stackStore` (scalar-indexed element
access into a stack array). A *secret* index into those is an
address/timing channel.

This file makes that boundary precise:

* `jasminOpAddrSurface : JasminOp → Bool` — the addressing-surface classifier.
  It is `true` for **exactly** `stackLoad` / `stackStore` and `false` for every
  other op (`addr_surface_iff_indexed`). All the arithmetic, the carry chain,
  the widening multiply, the immediate shifts/rotates, the **branchless**
  `select` (a cmov, not a branch), the packed-SIMD lane op, constants, and the
  leaf calls are pure dataflow.
* `ComJasminCTByConstruction` / the decision `comJasminCT?` — a `Com jasminDialect`
  is CT by construction iff it contains **no** `stackLoad` / `stackStore`
  (`comJasminCT?_eq_true_iff`). This is the index-free fragment, and it is exactly
  the shape the straight-line field/bignum kernels live in (register-only
  `regArith` / `mulhi` / `addCarry*` / `regConst`, spills at compile-time-constant
  frame offsets — no data-indexed array access).

Unlike `thirDialect`, the predicate here is **non-trivial**: `addressing_surface_is_real`
witnesses a `stackLoad` op that the classifier rejects, so the obligation is not
vacuous. This is the precise statement of what the jasmin→machine lowering must
preserve: the middle interface (`SecureCompileChain.LoweringCTPreserving`) reduces
from "preserve arbitrary CT" to **"keep every `stackLoad` / `stackStore` index
public"** — for the index-free kernel fragment it is discharged structurally,
here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The addressing-surface classifier -/

/-- A jasmin op is an **addressing surface** iff it performs a data-indexed
    memory access — i.e. it is `stackLoad` or `stackStore`. Those are the only
    two `JasminOp` constructors whose timing/address footprint can depend on a
    (possibly secret) operand; every other op is straight-line dataflow. -/
def jasminOpAddrSurface : JasminOp → Bool
  | .stackLoad _ _  => true
  | .stackStore _ _ => true
  | _               => false

/-- **The classifier is exact.** `jasminOpAddrSurface op` is `true` precisely
    when `op` is a `stackLoad` or a `stackStore` — the data-indexed memory ops.
    The point is that *no other* `JasminOp` constructor is an addressing or
    control surface. -/
theorem addr_surface_iff_indexed (op : JasminOp) :
    jasminOpAddrSurface op = true ↔
      (∃ w n, op = .stackLoad w n) ∨ (∃ w n, op = .stackStore w n) := by
  cases op <;>
    simp [jasminOpAddrSurface]

/-- The branchless constant-time `select` (a `cmov`) is **not** an addressing
    surface — both arms are always evaluated, so it introduces no channel. -/
theorem select_no_addr_surface (w : Nat) :
    jasminOpAddrSurface (.select w) = false := rfl

/-- Two-address arithmetic is dataflow, never an addressing surface. -/
theorem regArith_no_addr_surface (op : JasminBinOp) (w : Nat) :
    jasminOpAddrSurface (.regArith op w) = false := rfl

/-! ## 2. The index-free fragment of `Com jasminDialect` -/

/-- A `Com jasminDialect` is **constant-time by construction** when every op it
    binds is index-free (no addressing surface). This is the jasmin-level
    analogue of `ThirCTByConstruction.ComCTByConstruction`, but here it is a
    real restriction: it carves out the index-free fragment. -/
def ComJasminCTByConstruction {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body =>
      jasminOpAddrSurface e.op = false ∧ ComJasminCTByConstruction body

/-- The decision procedure for the index-free fragment (the jasmin-level
    counterpart of `compilableCT?`). -/
def comJasminCT? {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    Com jasminDialect Γ t → Bool
  | .ret _ => true
  | .var e body => (!jasminOpAddrSurface e.op) && comJasminCT? body

/-- `comJasminCT?` decides `ComJasminCTByConstruction`. -/
theorem comJasminCT?_eq_true_iff {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (c : Com jasminDialect Γ t) :
    comJasminCT? c = true ↔ ComJasminCTByConstruction c := by
  induction c with
  | ret v => simp [comJasminCT?, ComJasminCTByConstruction]
  | var e body ih =>
      simp only [comJasminCT?, ComJasminCTByConstruction, Bool.and_eq_true,
        Bool.not_eq_true', ih]

/-- Building a CT-by-construction program from an index-free head op and a
    CT-by-construction body. -/
theorem ComJasminCTByConstruction.var_of {Γ : Ctxt jasminDialect}
    {t s : jasminDialect.Ty} (e : Expr jasminDialect Γ t)
    (body : Com jasminDialect (t :: Γ) s)
    (he : jasminOpAddrSurface e.op = false)
    (hbody : ComJasminCTByConstruction body) :
    ComJasminCTByConstruction (.var e body) :=
  ⟨he, hbody⟩

/-! ## 3. Non-vacuity: jasmin can express an addressing surface -/

/-- **The obligation is real.** Unlike `thirDialect` (where CT-by-construction
    holds for *every* program), `jasminDialect` has an op the classifier rejects:
    a `stackLoad` is an addressing surface, so a `Com` binding it is **not** CT by
    construction. This is exactly why the jasmin→machine lowering carries the real
    obligation "keep the index public" for the indexed ops — it is not vacuous. -/
theorem addressing_surface_is_real (w n : Nat) :
    jasminOpAddrSurface (.stackLoad w n) = true ∧
    jasminOpAddrSurface (.stackStore w n) = true :=
  ⟨rfl, rfl⟩

end CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
