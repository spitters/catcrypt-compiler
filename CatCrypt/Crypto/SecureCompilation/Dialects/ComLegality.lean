/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn

set_option autoImplicit false

/-!
# D0: a verified legality helper over `Com jasminDialect`

The flattening front (`ScalarLinDeBruijn`) accepts a *neutral* jasmin fragment:
the binary ALU ops, the widening-high multiply, the immediate shifts, and the
materialised constants, all at width 64. The predicate that carves out this
fragment is `ScalarLinDeBruijn.SupportedOp`, and the front's golden-path
witnesses (`ComOK`) discharge it op-by-op. The pre-MLIR-restructure emit path
used a *partial* legality check: `gatherJBlock` returned `none` the moment it
met an op outside that set.

This file is the **D0 verified legality helper** of the MLIR dialect-alignment
plan: a *total, decidable* predicate over a whole `Com jasminDialect` program
that generalises the `gatherJBlock`-returns-`none` guard into a typed, *proven*
"every op is in the legal (`SupportedOp`) set" check. It is OURS — a Lean-side
firewall over the typed AST — not Veir's untrusted driver.

Contents:

* `isSupportedOp : JasminOp → Bool` — a decidable boolean mirror of the
  four-way `SupportedOp` disjunction, with `isSupportedOp_iff` proving the two
  coincide (hence `DecidablePred SupportedOp`).
* `comAllSupported : Com jasminDialect Γ t → Bool` — the structural legality
  walk: every let-bound op must pass `isSupportedOp`.
* `ComSupported : Com jasminDialect Γ t → Prop` — the propositional legality
  predicate, with `comAllSupported_iff` proving the boolean walk decides it.

`comAllSupported_iff` is the headline: a decidable check **provably equivalent**
to "every op in the program lies in the `SupportedOp` legal set".
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn (SupportedOp)

/-! ## 1. A decidable boolean mirror of `SupportedOp` -/

/-- Which `JasminBinOp`s the binary-ALU disjunct of `SupportedOp` admits:
    `add`, `sub`, `mul`, `and`, `or`, `xor` (but not the additive
    `shl`/`shr`/`andn`, which the front routes through the immediate-shift
    arms or rejects). -/
def isSupportedBinOp : JasminBinOp → Bool
  | .add | .sub | .mul | .and | .or | .xor => true
  | .shl | .shr | .andn => false

/-- Boolean decision procedure for `SupportedOp`: `true` on exactly the
    width-64 binary ALU ops (`isSupportedBinOp`), the width-64 widening-high
    multiply, the width-64 immediate left/right shifts, and the width-64
    materialised constants; `false` on every other op (wrong width, stack
    load/store, casts, external calls, packed ZMM, carry-chain words, native
    rotate, arithmetic shift, select, multi-result call). -/
def isSupportedOp : JasminOp → Bool
  | .regArith bop 64 => isSupportedBinOp bop
  | .mulhi 64 => true
  | .shrImm 64 _ => true
  | .shlImm 64 _ => true
  | .regConst 64 _ => true
  | _ => false

/-- **Soundness + completeness of the boolean mirror.** `isSupportedOp` decides
    `SupportedOp` exactly. -/
theorem isSupportedOp_iff (op : JasminOp) : isSupportedOp op = true ↔ SupportedOp op := by
  cases op with
  | regArith bop w =>
    rcases eq_or_ne w 64 with rfl | hw
    · cases bop <;> simp [isSupportedOp, isSupportedBinOp, SupportedOp]
    · simp only [isSupportedOp, SupportedOp]
      cases bop <;> simp_all
  | mulhi w =>
    rcases eq_or_ne w 64 with rfl | hw <;>
      simp only [isSupportedOp, SupportedOp] <;> simp_all
  | shrImm w n =>
    rcases eq_or_ne w 64 with rfl | hw <;>
      simp only [isSupportedOp, SupportedOp] <;> simp_all
  | shlImm w n =>
    rcases eq_or_ne w 64 with rfl | hw <;>
      simp only [isSupportedOp, SupportedOp] <;> simp_all
  | regConst w n =>
    rcases eq_or_ne w 64 with rfl | hw <;>
      simp only [isSupportedOp, SupportedOp] <;> simp_all
  | _ => simp [isSupportedOp, SupportedOp]

/-- `SupportedOp` is decidable, via the boolean mirror `isSupportedOp`. -/
instance : DecidablePred SupportedOp :=
  fun op => decidable_of_iff _ (isSupportedOp_iff op)

/-! ## 2. The `Com`-wide legality walk -/

/-- The structural legality walk over a whole `Com jasminDialect` program:
    `true` iff every let-bound op passes `isSupportedOp`. The `ret` leaf is
    always legal (it binds no op). -/
def comAllSupported : {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => isSupportedOp e.op && comAllSupported body

@[simp] theorem comAllSupported_ret {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (v : Var Γ t) : comAllSupported (Com.ret v) = true := rfl

@[simp] theorem comAllSupported_var {Γ : Ctxt jasminDialect}
    {t s : jasminDialect.Ty} (e : Expr jasminDialect Γ t)
    (body : Com jasminDialect (t :: Γ) s) :
    comAllSupported (Com.var e body) = (isSupportedOp e.op && comAllSupported body) := rfl

/-! ## 3. The propositional legality predicate + soundness bridge -/

/-- The propositional legality predicate: every let-bound op of the program
    lies in the `SupportedOp` legal set. The `ret` leaf is always legal. -/
inductive ComSupported : {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    Com jasminDialect Γ t → Prop where
  /-- A `ret` leaf binds no op and is always legal. -/
  | ret {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (v : Var Γ t) :
      ComSupported (Com.ret v)
  /-- A `var` is legal iff its bound op is `SupportedOp` and its body is legal. -/
  | var {Γ : Ctxt jasminDialect} {t s : jasminDialect.Ty}
      (e : Expr jasminDialect Γ t) (body : Com jasminDialect (t :: Γ) s) :
      SupportedOp e.op → ComSupported body → ComSupported (Com.var e body)

/-- **The verified legality helper.** The decidable boolean walk
    `comAllSupported` is provably equivalent to the propositional legality
    predicate `ComSupported`: a `Com jasminDialect` program passes the boolean
    check iff every one of its ops lies in the `SupportedOp` legal set. -/
theorem comAllSupported_iff {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (c : Com jasminDialect Γ t) : comAllSupported c = true ↔ ComSupported c := by
  induction c with
  | ret v => simp [comAllSupported_ret]; exact ComSupported.ret v
  | var e body ih =>
    rw [comAllSupported_var, Bool.and_eq_true, ih, isSupportedOp_iff]
    constructor
    · rintro ⟨hop, hbody⟩; exact ComSupported.var e body hop hbody
    · intro h; cases h with
      | var _ _ hop hbody => exact ⟨hop, hbody⟩

end CatCrypt.Crypto.SecureCompilation.Dialects
