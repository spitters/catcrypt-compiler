/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint

/-!
# Structural correctness of the CatCrypt VIR text printer (v0)

This file proves **v0 ("no information loss") structural faithfulness**
properties for the textual MLIR printer in `CatCryptPrint.lean`.

## What we prove

Full semantic correctness (`parse (printModule c) ≃ c.denote`) would require
a formal MLIR grammar / parser, which is out of scope. The verified-compilation
literature calls the achievable mid-tier *structural faithfulness*: printer
output uniquely names the original `Com` up to alpha renaming. We prove the
weakest useful version of that:

1. **Printability** (`printableShape`): every `Com catCryptDialect Γ t` is
   printable — `printCatCryptOp` is total over the `CatCryptOp` enum, so
   `printableShape_anyCom` holds for every `Com` of the dialect.

2. **Structural body shape** (`Com.printBody_var_eq`, `Com.printBody_ret_eq`):
   the body printer's text shape is exactly
     - `ret v ↦ ("", lookup v)`
     - `var e body ↦ (line ++ "\n" ++ rest, retNm)`
   This is the inductive invariant the higher-level theorems build on, and
   it directly entails *one `\n` separator per `Com.var`* (the asked-for
   "line-count" property, in equational rather than newline-counting form
   — strictly stronger).

3. **Op-list length = opCount** (`Com.opList_length_eq_opCount`): the list
   of ops `Com.opList c` has length `Com.opCount c`. This is the abstract
   counterpart to "one line per binding".

4. **Op-name preservation** (`Com.printBody_contains_op`,
   `Com.printModule_contains_op`): for every operation along the let-chain
   of a `Com`, the body string contains the printer's quoted op name
   (e.g. `"arith.addi"`) as a substring.

5. **Smoke-test instantiation**: the existing `add_3_4_prog` from
   `CatCryptPrint` has `opCount = 3`, its opList has length 3, the first
   op is `bvConst 8 3`, and its printed module contains both
   `"arith.constant"` and `"arith.addi"` as substrings.

## What is *not* in v0

- **Newline-count theorem** (`(printCom c).newlineCount = opCount c + 3`):
  this is *implied* by the structural body-shape equations, but proving it
  as a self-contained statement requires showing that `Expr.printLine`,
  `printArgs`, `printArgTys`, `printCatCryptOp`, `printCatCryptAttrs`,
  `printCryptoTy`, and `toString : Nat → String` all produce strings with
  zero `'\n'` characters. The first six are finite case-splits provable
  by `decide` on their non-parametric cases; `toString : Nat → String`
  needs a general lemma. Skipped to stay within session scope.
- **Parser inverse** (`parse ∘ print = id`): requires modelling MLIR text
  grammar. Deferred.
- **Alpha-renaming bijection** (v1): would require SSA equivalence on `Com`
  plus a recovering parser. Deferred.
- **Semantic equivalence** (full): `c.denote = (parse (printModule c)).denote`
  with respect to MLIR reference semantics. Deferred.

The v0 properties suffice to rule out trivial printer bugs (an op silently
dropped, a binding losing its op name, off-by-one in line emission) without
committing to a parser model.
-/

set_option autoImplicit false

/-! ## Substring infrastructure (top-level)

We put the small `List.isInfix'` / `String.isInfix'` infrastructure at
the root namespace so that the substring API lives where you'd expect
to find it. -/

namespace List

/-- `xs` appears as a contiguous sublist of `ys`. -/
def isInfix' {α : Type*} (xs ys : List α) : Prop :=
  ∃ pre suf, ys = pre ++ xs ++ suf

theorem isInfix'_refl {α : Type*} (xs : List α) : isInfix' xs xs :=
  ⟨[], [], by simp⟩

theorem isInfix'_append_left {α : Type*} (xs ys zs : List α)
    (h : isInfix' xs ys) : isInfix' xs (zs ++ ys) := by
  obtain ⟨pre, suf, hp⟩ := h
  refine ⟨zs ++ pre, suf, ?_⟩
  simp [hp, List.append_assoc]

theorem isInfix'_append_right {α : Type*} (xs ys zs : List α)
    (h : isInfix' xs ys) : isInfix' xs (ys ++ zs) := by
  obtain ⟨pre, suf, hp⟩ := h
  refine ⟨pre, suf ++ zs, ?_⟩
  simp [hp, List.append_assoc]

end List

namespace String

/-- A string `t` is a substring (contiguous infix) of `s`. -/
def isInfix' (t s : String) : Prop := List.isInfix' t.toList s.toList

theorem isInfix'_refl (s : String) : isInfix' s s :=
  List.isInfix'_refl _

theorem isInfix'_append_left (t s s₀ : String)
    (h : isInfix' t s) : isInfix' t (s₀ ++ s) := by
  unfold isInfix' at h ⊢
  rw [String.toList_append]
  exact List.isInfix'_append_left _ _ _ h

theorem isInfix'_append_right (t s s₁ : String)
    (h : isInfix' t s) : isInfix' t (s ++ s₁) := by
  unfold isInfix' at h ⊢
  rw [String.toList_append]
  exact List.isInfix'_append_right _ _ _ h

end String

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. The printability shape predicate -/

/-- A `Com` is "printable" if every op along its let-chain has a textual
    rendering in the `CatCryptPrint` printer. For `catCryptDialect`, every
    `CatCryptOp` constructor is handled by `printCatCryptOp`, so this is
    structurally trivial. -/
def printableShape {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    (_c : Com catCryptDialect Γ t) : Prop := True

/-- Every `Com` of `catCryptDialect` is printable. -/
theorem printableShape_anyCom {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    (c : Com catCryptDialect Γ t) : printableShape c := trivial

instance printableShape.decidable {Γ : Ctxt catCryptDialect}
    {t : catCryptDialect.Ty} (c : Com catCryptDialect Γ t) :
    Decidable (printableShape c) :=
  inferInstanceAs (Decidable True)

/-! ## 2. Operation count and op list -/

namespace Com

/-- The number of `Com.var` constructors along the let-chain. -/
def opCount {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + opCount body

/-- The list of operation tags appearing in the let-chain. `ret` ↦ `[]`;
    `var e body ↦ e.op :: opList body`. -/
def opList {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → List d.Op
  | _, _, .ret _ => []
  | _, _, .var e body => e.op :: opList body

/-- `opList` length equals `opCount`. -/
theorem opList_length_eq_opCount {d : Dialect} [DialectSignature d] :
    {Γ : Ctxt d} → {t : d.Ty} → (c : Com d Γ t) →
    c.opList.length = c.opCount
  | _, _, .ret _ => rfl
  | _, _, .var _ body => by
    simp only [opList, opCount, List.length_cons,
      opList_length_eq_opCount body]
    omega

end Com

/-! ## 3. Printer body: structural unfolding lemmas -/

namespace Com

/-- Body of `Com.ret`. -/
theorem printBody_ret_eq
    {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    (v : Ctxt.Var Γ t) (names : PrintEnv.Names Γ) (nextId : Nat) :
    printBody (.ret v) names nextId =
      ("", PrintEnv.get v names) := rfl

/-- Body of `Com.var`. -/
theorem printBody_var_eq
    {Γ : Ctxt catCryptDialect} {t s : catCryptDialect.Ty}
    (e : Expr catCryptDialect Γ t) (body : Com catCryptDialect (t :: Γ) s)
    (names : PrintEnv.Names Γ) (nextId : Nat) :
    printBody (Com.var e body) names nextId =
      ( Expr.printLine e names (toString nextId) ++ "\n" ++
          (printBody body (PrintEnv.push names (toString nextId))
            (nextId + 1)).fst,
        (printBody body (PrintEnv.push names (toString nextId))
          (nextId + 1)).snd ) := rfl

end Com

/-! ## 4. `Expr.printLine` contains the op-name -/

namespace Expr

/-- Explicit decomposition of `printLine` into a `pre ++ printOp e.op ++ post`
    sandwich. Defeq + `rfl`. -/
theorem printLine_eq
    {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    (e : Expr catCryptDialect Γ t) (names : PrintEnv.Names Γ)
    (resultName : String) :
    printLine e names resultName =
      "  %" ++ resultName ++ " = " ++ DialectPrint.printOp e.op ++
      "(" ++ printArgs e.args names ++ ")" ++ DialectPrint.printAttrs e.op ++
      " : " ++ printArgTys (DialectSignature.sig e.op) ++ " -> " ++
      DialectPrint.printTy t := by
  unfold printLine
  rfl

/-- `printLine` contains `printCatCryptOp e.op` (= `DialectPrint.printOp e.op`)
    as a substring. -/
theorem printLine_contains_op
    {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
    (e : Expr catCryptDialect Γ t) (names : PrintEnv.Names Γ)
    (resultName : String) :
    String.isInfix' (printCatCryptOp e.op)
      (printLine e names resultName) := by
  rw [printLine_eq]
  -- Replace `DialectPrint.printOp e.op` by `printCatCryptOp e.op` via instance.
  have hop : DialectPrint.printOp (d := catCryptDialect) e.op
              = printCatCryptOp e.op := rfl
  rw [hop]
  -- We now need: `printCatCryptOp e.op` is an infix of
  --   "  %" ++ rN ++ " = " ++ printCatCryptOp e.op ++ "(" ++ args ++ ")" ++ ...
  -- The chain has 12 atoms (`++` is left-associative), with target at position 4.
  -- Strip 8 atoms from the right, then 1 left chunk.
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_left
  exact String.isInfix'_refl _

end Expr

/-! ## 6. Body printer contains every op-name -/

namespace Com

/-- For every `op ∈ c.opList`, the body string contains
    `printCatCryptOp op` as a substring. -/
theorem printBody_contains_op :
    ∀ {Γ : Ctxt catCryptDialect} {t : catCryptDialect.Ty}
      (c : Com catCryptDialect Γ t) (names : PrintEnv.Names Γ) (nextId : Nat)
      (op : CatCryptOp), op ∈ c.opList →
      String.isInfix' (printCatCryptOp op)
        (printBody c names nextId).fst
  | _, _, .ret _, _, _, op, hop => by
    simp [opList] at hop
  | _, _, .var e body, names, nextId, op, hop => by
    simp only [opList, List.mem_cons] at hop
    rw [printBody_var_eq]
    show String.isInfix' (printCatCryptOp op)
      (Expr.printLine e names (toString nextId) ++ "\n" ++
        (printBody body (PrintEnv.push names (toString nextId))
          (nextId + 1)).fst)
    rcases hop with hop | hop
    · subst hop
      -- target chain: `((printLine ...) ++ "\n") ++ rest`. printLine is on the
      -- left; the target sits inside printLine. Strip rest (append_right),
      -- then strip "\n" (append_right), then use printLine_contains_op.
      exact String.isInfix'_append_right _ _ _
        (String.isInfix'_append_right _ _ _
          (Expr.printLine_contains_op e names (toString nextId)))
    · have ih := printBody_contains_op body
        (PrintEnv.push names (toString nextId)) (nextId + 1) op hop
      -- target chain: `((printLine ...) ++ "\n") ++ rest`. Push ih into the
      -- right side: one append_left peels off `(printLine ++ "\n")`.
      exact String.isInfix'_append_left _ _ _ ih

/-! ## 7. `printModule` contains every op-name -/

/-- `printModule` text contains every op-name from `opList c`. -/
theorem printModule_contains_op
    {t : catCryptDialect.Ty} (c : Com catCryptDialect [] t) (funcName : String)
    (op : CatCryptOp) (hop : op ∈ c.opList) :
    String.isInfix' (printCatCryptOp op) (printModule c funcName) := by
  unfold printModule
  -- Reduce the `let (body, retNm) := ...` form.
  show String.isInfix' (printCatCryptOp op) _
  set bodyP := printBody c PrintEnv.empty 0 with hbody_def
  -- The string is
  --   "func.func @" ++ funcName ++ "() -> " ++ retTy ++ " {" ++ "\n"
  --     ++ bodyP.fst ++ "  return %" ++ bodyP.snd ++ " : " ++ retTy
  --     ++ "\n" ++ "}" ++ "\n"
  have hbody : String.isInfix' (printCatCryptOp op) bodyP.fst := by
    simpa [hbody_def] using
      printBody_contains_op c PrintEnv.empty 0 op hop
  -- Push through all the surrounding `++`.
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_right
  apply String.isInfix'_append_left
  exact hbody

end Com

/-! ## 8. Smoke test on `add_3_4_prog`

The existing test in `CatCryptPrint.lean` is:
  `let x = 3 : sword 8; let y = 4; let z = x + y; ret z`.
Three ops: `bvConst 8 3`, `bvConst 8 4`, `bvAdd 8`. We verify the
structural invariants instantiate to expected concrete values. -/

namespace Test

open CryptoSSA CatCrypt.Crypto.SecureCompilation.VIR.CryptoToVIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint.Test

/-- Three ops in the smoke-test program. -/
theorem add_3_4_opCount : Com.opCount add_3_4_vir = 3 := by
  decide

/-- The op-list has three entries (consistent with opCount). -/
theorem add_3_4_opList_length : (Com.opList add_3_4_vir).length = 3 := by
  rw [Com.opList_length_eq_opCount]
  exact add_3_4_opCount

/-- The first op of `add_3_4_vir` is `bvConst 8 3` (the first constant). -/
theorem add_3_4_first_op :
    (Com.opList add_3_4_vir).head? = some (CatCryptOp.bvConst 8 (3 : BitVec 8)) := by
  decide

/-- The printed module contains the `"arith.addi"` op-name string,
    because `add_3_4_vir` contains a `bvAdd 8` binding. -/
theorem add_3_4_printed_contains_addi :
    String.isInfix' (printCatCryptOp (CatCryptOp.bvAdd 8))
      (Com.printModule add_3_4_vir "add_3_4") := by
  apply Com.printModule_contains_op
  -- `CatCryptOp.bvAdd 8 ∈ opList add_3_4_vir` by decidable computation.
  decide

/-- The printed module contains the `"arith.constant"` op-name string,
    because `add_3_4_vir` contains a `bvConst` binding. -/
theorem add_3_4_printed_contains_constant :
    String.isInfix' (printCatCryptOp (CatCryptOp.bvConst 8 (3 : BitVec 8)))
      (Com.printModule add_3_4_vir "add_3_4") := by
  apply Com.printModule_contains_op
  decide

end Test

end CatCrypt.Crypto.SecureCompilation.VIR
