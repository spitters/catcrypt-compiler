/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# Structural correctness of the `Com jasminDialect → JasminProg` lowering

This file proves **v0 ("no information loss") structural faithfulness**
properties for the AST lowering `lowerComToProg` in `JasminPrint.lean`,
mirroring `CatCryptPrintCorrect.lean` for the CatCrypt dialect.

## What we prove

Full semantic correctness (`denote (lowerComToProg c) ≃ c.denote`) would
require a denotation for the Jasmin AST. The verified-compilation literature
calls the achievable mid-tier *structural faithfulness*: the emitted program
faithfully reflects the shape of the source `Com`. The CatCrypt analogue
(`CatCryptPrintCorrect.lean`) proves an op-count / op-list invariant for its
*text* printer (`opList_length_eq_opCount`, `printBody_var_eq/ret_eq`); the
Jasmin lowering emits an *AST*, so the directly-analogous statement is about
the emitted instruction list rather than newline structure.

1. **Op count / op list** (`Com.jOpCount`, `Com.jOpList`,
   `Com.jOpList_length_eq_jOpCount`): the number of `Com.var` constructors
   along the let-chain, and the list of op tags. `jOpList` length equals
   `jOpCount`. This is the exact analogue of `Com.opCount` / `Com.opList`
   in `CatCryptPrintCorrect.lean`.

2. **Body-length preservation** (`lowerCom_length`): `lowerCom` emits
   **exactly one `InstrR` per `Com.var`** — the emitted instruction list has
   length equal to `jOpCount`. This is the structural invariant the body
   printer satisfies, proved by induction on `Com` exactly like
   `CatCryptPrintCorrect`'s body-shape lemmas.

3. **FunDecl body-length = op count** (`lowerComToProg_body_length`): the
   single `FunDecl` emitted by `lowerComToProg` has a body whose length is
   `jOpCount com`. This is the top-level analogue of "one printed line per
   binding" — here, one Jasmin instruction per binding.

4. **One function emitted, parameter count = context length**
   (`lowerComToProg_one_func`, `lowerComToProg_params_length`): the lowering
   always produces a single-function program whose parameter count equals the
   length of the source free context `Γ` (each free variable is materialised
   as one named parameter). Proved by induction on `Γ` via `paramsAndMapFrom`.

5. **Smoke-test instantiation**: the existing `JasminPrint.smokeProg` has
   `jOpCount = 2`, its emitted body has length 2, one function, and two
   parameters — recovering the hand-stated `smoke_two_instrs` /
   `smoke_two_params` facts as instances of the general theorems.

## What is *not* in v0

- **Semantic equivalence**: `c.denote ≃ ⟦lowerComToProg c⟧` with respect to a
  Jasmin reference semantics. The Jasmin AST here has no Lean denotation, so
  this is out of scope (the same boundary as `CatCryptPrintCorrect`'s deferred
  parser/semantics tier).
- **Per-op instruction shape**: that each op kind lowers to the specific
  `InstrR` constructor documented in `JasminPrint`'s mapping table. The
  length invariant is op-kind-agnostic and suffices to rule out an op being
  silently dropped or duplicated.

The v0 properties rule out trivial lowering bugs (an op dropped, a binding
losing its instruction, a wrong parameter count) without committing to a
Jasmin semantics.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.Jasmin

/-! ## 1. Operation count and op list (jasmin analogue of `Com.opCount`) -/

namespace Com

/-- The number of `Com.var` constructors along the let-chain. Jasmin analogue
    of `CatCryptPrintCorrect`'s `Com.opCount`. -/
def jOpCount :
    {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + jOpCount body

/-- The list of operation tags appearing in the let-chain. `ret ↦ []`;
    `var e body ↦ e.op :: jOpList body`. -/
def jOpList :
    {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    Com jasminDialect Γ t → List JasminOp
  | _, _, .ret _ => []
  | _, _, .var e body => e.op :: jOpList body

/-- `jOpList` length equals `jOpCount`. -/
theorem jOpList_length_eq_jOpCount :
    {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    (c : Com jasminDialect Γ t) → c.jOpList.length = c.jOpCount
  | _, _, .ret _ => rfl
  | _, _, .var _ body => by
    simp only [jOpList, jOpCount, List.length_cons,
      jOpList_length_eq_jOpCount body]
    omega

end Com

/-! ## 2. Body-length preservation: one `InstrR` per `Com.var`

`lowerCom` walks the `Com` emitting `instr :: rest` for each `Com.var` and
`[]` for `Com.ret`, so the emitted instruction list has exactly one entry per
binding. This is the inductive invariant analogous to `CatCryptPrintCorrect`'s
`printBody_var_eq` (each `var` contributes exactly one printed line). -/

/-- `lowerCom` emits exactly one `InstrR` per `Com.var`: the length of the
    emitted instruction list equals `jOpCount`. Proved by induction on `Com`
    (note `vm`/`next` are universally quantified so the IH applies to the
    `extend`-ed resolver and incremented counter). -/
theorem lowerCom_length :
    {Γ : Ctxt jasminDialect} → {t : jasminDialect.Ty} →
    (com : Com jasminDialect Γ t) → (vm : VarMap Γ) → (next : Nat) →
    (lowerCom vm next com).fst.length = com.jOpCount
  | _, _, .ret v, vm, next => by
    simp [lowerCom, Com.jOpCount]
  | _, _, .var e body, vm, next => by
    -- Unfold one step of `lowerCom`; the `let`s are definitional.
    show ((lowerExpr vm e (resultName vm e ("v" ++ toString next)))
            :: (lowerCom (vm.extend (resultName vm e ("v" ++ toString next)))
                  (next + 1) body).fst).length
          = (Com.var e body).jOpCount
    simp only [List.length_cons, Com.jOpCount,
      lowerCom_length body (vm.extend (resultName vm e ("v" ++ toString next)))
        (next + 1)]
    omega

/-! ## 3. Top-level: `lowerComToProg` structural facts -/

/-- `lowerComToProg` emits exactly one function. -/
theorem lowerComToProg_one_func
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (name : String) (com : Com jasminDialect Γ t) :
    (lowerComToProg name com).funcs.length = 1 := rfl

/-- The body of the single emitted `FunDecl` has length `jOpCount com`:
    one Jasmin instruction per source binding. This is the AST analogue of
    `CatCryptPrintCorrect`'s "one printed line per `Com.var`". -/
theorem lowerComToProg_body_length
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (name : String) (com : Com jasminDialect Γ t) :
    ((lowerComToProg name com).funcs.head?.map (fun fd => fd.body.length))
      = some com.jOpCount := by
  -- `lowerComToProg`'s body is `(lowerCom vm 0 com).fst`; its length is
  -- `jOpCount` by `lowerCom_length`.
  show some ((lowerCom (paramsAndMap Γ).snd 0 com).fst.length) = some com.jOpCount
  rw [lowerCom_length com (paramsAndMap Γ).snd 0]

/-! ## 4. Parameter count = free-context length

Each free variable of `Γ` is materialised as one named function parameter by
`paramsAndMapFrom`, so the parameter list has length `Γ.length`. Proved by
induction on `Γ`. -/

/-- `paramsAndMapFrom base Γ` produces a parameter list of length `Γ.length`. -/
theorem paramsAndMapFrom_length :
    (base : Nat) → (Γ : Ctxt jasminDialect) →
    (paramsAndMapFrom base Γ).fst.length = Γ.length
  | _, [] => rfl
  | base, t :: rest => by
    show ((⟨mkVarI ("p" ++ toString base) t⟩ : FunParam)
            :: (paramsAndMapFrom (base + 1) rest).fst).length
          = (t :: rest).length
    simp only [List.length_cons, paramsAndMapFrom_length (base + 1) rest]

/-- The single emitted `FunDecl` has parameter count equal to `Γ.length`:
    each free variable becomes one named parameter. -/
theorem lowerComToProg_params_length
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (name : String) (com : Com jasminDialect Γ t) :
    ((lowerComToProg name com).funcs.head?.map (fun fd => fd.params.length))
      = some Γ.length := by
  show some ((paramsAndMap Γ).fst.length) = some Γ.length
  unfold paramsAndMap
  rw [paramsAndMapFrom_length 0 Γ]

/-! ## 5. Smoke test on `JasminDialect.smokeProg`

`smokeProg` is `regArith add` then `castW 32 64` on `[reg 32, reg 32]`,
so `jOpCount = 2`, two parameters, body length 2 — recovering the hand-stated
`JasminPrint.smoke_two_instrs` / `smoke_two_params` as instances. -/

namespace Test

/-- The smoke program has two bindings (`add`, `castW`). -/
theorem smoke_jOpCount : Com.jOpCount JasminDialect.smokeProg = 2 := by decide

/-- The op-list has two entries (consistent with `jOpCount`). -/
theorem smoke_jOpList_length :
    (Com.jOpList JasminDialect.smokeProg).length = 2 := by
  rw [Com.jOpList_length_eq_jOpCount]; exact smoke_jOpCount

/-- The emitted body has length 2 — recovered from the general
    `lowerComToProg_body_length` + `smoke_jOpCount`, matching the hand-stated
    `JasminPrint.smoke_two_instrs`. -/
theorem smoke_body_length :
    ((lowerComToProg "smoke" JasminDialect.smokeProg).funcs.head?.map
      (fun fd => fd.body.length)) = some 2 := by
  rw [lowerComToProg_body_length]; rw [smoke_jOpCount]

/-- The emitted program has two parameters — recovered from the general
    `lowerComToProg_params_length`, matching `JasminPrint.smoke_two_params`. -/
theorem smoke_params_length :
    ((lowerComToProg "smoke" JasminDialect.smokeProg).funcs.head?.map
      (fun fd => fd.params.length)) = some 2 := by
  rw [lowerComToProg_params_length]; rfl

/-- One function is emitted. -/
theorem smoke_one_func :
    (lowerComToProg "smoke" JasminDialect.smokeProg).funcs.length = 1 :=
  lowerComToProg_one_func _ _

end Test

end CatCrypt.Crypto.SecureCompilation.VIR
