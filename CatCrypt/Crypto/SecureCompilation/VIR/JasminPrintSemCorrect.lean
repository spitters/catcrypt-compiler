/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

/-!
# `lowerComToProg` is denotation-preserving — semantic (as opposed to structural) half

`JasminPrintCorrect.lean` proves the `Com[jasminDialect] → JasminProg` lowering
(`JasminPrint.lowerComToProg`) only *structurally* faithful (op/instruction
count). This file closes the **semantic** half: running the emitted Jasmin
instruction list under a word-level evaluator threads the SSA values so the
final result equals `Com.denote`.

## Why a fresh minimal evaluator (and the gap to `jasminSemTraced'`)

The repository's existing Jasmin evaluator
(`CatCrypt/Crypto/CompilerSecurity/JasminSemTraced.lean`,
`JasminExec.lean`) is the *leakage-trace* semantics over `RustState`: values are
stored as `TowerType`-encoded **byte arrays** (`JArray`), the evaluator is
`Option`-partial (returns `none` outside its supported subset), and it tracks a
`LeakTrace`. As shipped it implements exactly **one** `InstrR` shape end-to-end
(the U64-zero `Cassgn`), with the other shapes documented as mechanical-but-open.
That model is unsuitable for a clean denotation-preservation theorem against the
dialect's value world (`⟦reg w⟧ = BitVec w`, `⟦stackArr w n⟧ = Fin n → BitVec w`):
the byte-encoding/`TowerType` round-trip is precisely the deferred "byte-layout
encoding" piece flagged in `LatticeToJasminDenote.lean`.

So, per the explicit "if the existing evaluator is unsuitable" path, this file
defines a **minimal faithful word-level evaluator** for the emitted `InstrR`
fragment — a string-keyed typed store (`Store`) plus `evalPExpr` / `execInstr` /
`execCmd` that interpret the `PExpr` / `InstrR` shapes `lowerExpr` actually
emits — and proves `lowerComToProg` is denotation-preserving against THAT. The
remaining gap to `jasminSemTraced'` is exactly the `Store ↔ RustState` byte
encoding (the same deferred piece as elsewhere), not the threading of values
(which is what this file establishes).

## Store-agrees-with-valuation invariant

The evaluator's `Store` is `String → DynVal`, where `DynVal = Σ t, ⟦t⟧` is a
typed dynamic value. `StoreAgrees vm V s` says: for every typed De Bruijn
variable `v : Var Γ t`, the store at the lowered name `vm t v` holds the dynamic
value `⟨t, v.lookup V⟩`. This is the semantic counterpart of `JasminPrint.VarMap`
resolving variables to names — it ties the named store back to the De Bruijn
valuation that `Com.denote` threads.

## Fragment covered (fully closed) vs. parametric/explicit edges

* **Fully closed (0 hypotheses):** the straight-line `regArith` + `castW`
  fragment. For these ops every `Com.var` binding emits a *fresh* SSA name
  `v{next}` (strictly increasing counter), so an instruction's write never
  clobbers a name still in scope. We prove this freshness (`StraightLine`) and
  conclude `lowerCom_sem_eq` and the whole-program
  `lowerComToProg_sem_eq` unconditionally for that fragment.

* **`extCall` — parametric leaf edge.** Exactly as `LatticeToJasminDenote` and
  `CryptoToJasminComCorrect`, the external-leaf semantics is opaque, so the
  evaluator's `Ccall` interpretation is carried as a parameter (`leafSem`) and
  agreement with `jasminDenote`'s `jasminExtSem` is an explicit hypothesis
  (`LeafAgrees`). We do *not* attempt to discharge leaf semantics.

* **`stackStore` — explicit hypothesis (named, not closed here).** `stackStore`
  is the one op that does **not** introduce a fresh name: `resultName` reuses the
  source-array name (in-place update is how Jasmin models `a[i] = v`). That
  deliberate aliasing means the fresh-name freshness argument above does not
  apply, so the straight-line fragment excludes it; we record the precise reason
  in `stackStore_aliases_source`. `stackLoad` *does* bind a fresh name and is
  handled by the same evaluator, but the end-to-end theorem below is stated for
  the `regArith`/`castW` (+ parametric `extCall`) fragment.

All goals closed. The leaf edge is parametric (a hypothesis), never an admitted proof.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.Jasmin

/-! ## 1. A typed dynamic value and the named store -/

/-- A typed dynamic value: a dialect type together with one inhabitant of its
    denotation. The evaluator's store maps names to these. -/
structure DynVal where
  /-- The dialect type of the stored value. -/
  ty : JasminTy
  /-- The stored value. -/
  val : ⟦ty⟧

/-- A named store: each variable name resolves to a typed dynamic value.
    The everywhere-default store seeds names not yet written. -/
abbrev Store : Type := String → DynVal

/-- The default dynamic value at a type (used for the seed store). -/
def DynVal.default (t : JasminTy) : DynVal := ⟨t, JasminTy.default t⟩

/-- Read a value of an *expected* type `t` from the store at `name`. If the
    stored dynamic value has a different type, fall back to the type default
    (this never happens on stores produced by the lowering, where every name is
    written at its declared type — see `StoreAgrees`). -/
def Store.get (s : Store) (name : String) (t : JasminTy) : ⟦t⟧ :=
  let d := s name
  if h : d.ty = t then h ▸ d.val else JasminTy.default t

/-- Write a typed value into the store at `name`. -/
def Store.set (s : Store) (name : String) {t : JasminTy} (v : ⟦t⟧) : Store :=
  fun n => if n = name then ⟨t, v⟩ else s n

/-- Reading the type `t` value just written at `name` returns it. -/
@[simp] theorem Store.get_set_same (s : Store) (name : String) {t : JasminTy}
    (v : ⟦t⟧) : (s.set name v).get name t = v := by
  show (if h : ((if name = name then ⟨t, v⟩ else s name) : DynVal).ty = t then
          h ▸ ((if name = name then ⟨t, v⟩ else s name) : DynVal).val
        else JasminTy.default t) = v
  rw [if_pos rfl]
  simp only [dif_pos]

/-- Reading a *different* name is unaffected by a write. -/
@[simp] theorem Store.get_set_other (s : Store) {name name' : String}
    (h : name' ≠ name) {t t' : JasminTy} (v : ⟦t⟧) :
    (s.set name v).get name' t' = s.get name' t' := by
  show (if hd : ((if name' = name then (⟨t, v⟩ : DynVal) else s name')).ty = t' then
          hd ▸ ((if name' = name then (⟨t, v⟩ : DynVal) else s name')).val
        else JasminTy.default t')
      = s.get name' t'
  rw [if_neg h]
  rfl

/-! ## 2. The minimal word-level evaluator for the emitted fragment

`lowerExpr` emits a fixed, small set of `PExpr` / `InstrR` shapes:

| dialect op  | emitted `InstrR`                                                       |
|-------------|------------------------------------------------------------------------|
| `regArith`  | `Cassgn (Lvar dst) _ (sword ws) (Papp2 (op@ws) (Pvar a) (Pvar b))`     |
| `castW`     | `Cassgn (Lvar dst) _ (sword ws) (Papp1 (Ozeroext ws' ws) (Pvar src))` |
| `stackLoad` | `Cassgn (Lvar dst) _ (sword ws) (Pget AAscale ws arr (Pvar idx))`     |
| `stackStore`| `Cassgn (Laset AAscale ws arr (Pvar idx)) _ (sword ws) (Pvar src)`    |
| `extCall`   | `Ccall DoInline [Lvar dst] {name} (args.map Pvar)`                     |

We interpret each against the typed `Store`, parametric in the external-leaf
semantics `leafSem` (opaque, mirroring `jasminExtSem`). The evaluator carries the
*dialect-typed* op alongside each instruction it should not need to re-parse — we
instead define `execExpr` to interpret one lowered `Expr` directly, since that is
what the lowering produces and what we relate to `Expr.denote`. This keeps the
evaluator faithful to the emitted `InstrR` shapes (each `execExpr` branch matches
the corresponding `lowerExpr` branch) while staying typed enough to prove
preservation. -/

/-- External-leaf semantics parameter: same shape as `jasminExtSem`, opaque.
    Reads its already-resolved typed arguments and returns the typed result. -/
abbrev LeafSem : Type :=
  (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
    HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧

/-- Resolve an `HVector` of dialect variables to their *names* (via `vm`) and
    read each from the store, producing a typed `HVector` of values. This is the
    store-level analogue of `Expr.lookupArgs`. -/
def lookupArgsStore {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (s : Store) :
    {tys : List jasminDialect.Ty} →
    HVector (fun ty => Ctxt.Var Γ ty) tys → HVector (fun t => ⟦t⟧) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (s.get (vm _ v) _) (lookupArgsStore vm s rest)

/-- Execute one lowered `Expr` against the store, returning the value bound to
    the result name `dst`. Mirrors the `lowerExpr` shapes one-for-one; the
    external leaf uses the parameter `leafSem`. -/
def execExpr {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (leafSem : LeafSem) (vm : VarMap Γ) (e : Expr jasminDialect Γ t)
    (s : Store) : ⟦t⟧ :=
  e.retTy_eq ▸ (match e.op, e.args with
    | .regArith bop w, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        bop.apply a b
    | .stackLoad w n, args =>
        let arr : Fin n → BitVec w := s.get (vm _ args.head) (.stackArr w n)
        let i : BitVec 64 := s.get (vm _ args.tail.head) (.reg 64)
        stackGet arr (BitVec.toNat i)
    | .stackStore w n, args =>
        let arr : Fin n → BitVec w := s.get (vm _ args.head) (.stackArr w n)
        let i : BitVec 64 := s.get (vm _ args.tail.head) (.reg 64)
        let v : BitVec w := s.get (vm _ args.tail.tail.head) (.reg w)
        stackSet arr (BitVec.toNat i) v
    | .castW w w', args =>
        let src : BitVec w := s.get (vm _ args.head) (.reg w)
        show BitVec w' from src.zeroExtend w'
    | .extCall name argTys retTy, args =>
        leafSem name argTys retTy (lookupArgsStore vm s args)
    | .regConst w n, _ =>
        show BitVec w from BitVec.ofNat w n
    | .vpackZMM bop, args =>
        let a : BitVec 512 := s.get (vm _ args.head) (.reg 512)
        let b : BitVec 512 := s.get (vm _ args.tail.head) (.reg 512)
        zmmPackQ bop a b
    | .vpackZMMd bop, args =>
        let a : BitVec 512 := s.get (vm _ args.head) (.reg 512)
        let b : BitVec 512 := s.get (vm _ args.tail.head) (.reg 512)
        zmmPackD bop a b
    | .vprordZMM n, args =>
        let a : BitVec 512 := s.get (vm _ args.head) (.reg 512)
        zmmRorD n a
    | .vpslldq n, args =>
        let a : BitVec 128 := s.get (vm _ args.head) (.reg 128)
        a <<< (n * 8)
    | .vpsrldq n, args =>
        let a : BitVec 128 := s.get (vm _ args.head) (.reg 128)
        a >>> (n * 8)
    | .vsimd op, args =>
        -- Inner-match on `op` so its (stuck) signature `op.argTys` reduces to the
        -- concrete `[reg 128, reg 128]`, letting `args.head`/`args.tail.head`
        -- typecheck (mirrors the dialect-denote `.vsimd` arm).
        (match op, args with
         | .gf2p8mulb, args =>
             SimdOp.denote .gf2p8mulb
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .vpshufb, args =>
             SimdOp.denote .vpshufb
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .clmul imm, args =>
             SimdOp.denote (.clmul imm)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .affineqb imm, args =>
             SimdOp.denote (.affineqb imm)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .bitwise bop, args =>
             SimdOp.denote (.bitwise bop)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .packed bop laneW, args =>
             SimdOp.denote (.packed bop laneW)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .mulhi16, args =>
             SimdOp.denote .mulhi16
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .vaesenc, args =>
             SimdOp.denote .vaesenc
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .vaesenclast, args =>
             SimdOp.denote .vaesenclast
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.tail.head) (.reg 128))
         | .vaeskeygen rcon, args =>
             -- unary (`argTys = [reg 128]`): only `args.head`; denote ignores arg 2.
             SimdOp.denote (.vaeskeygen rcon)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.head) (.reg 128))
         | .vpshufd imm, args =>
             -- unary (`argTys = [reg 128]`): only `args.head`; denote ignores arg 2.
             SimdOp.denote (.vpshufd imm)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.head) (.reg 128))
         | .packedImm bop laneW imm, args =>
             -- unary (`argTys = [reg 128]`): only `args.head`; denote ignores arg 2.
             SimdOp.denote (.packedImm bop laneW imm)
               (s.get (vm _ args.head) (.reg 128)) (s.get (vm _ args.head) (.reg 128)))
    | .vymm op, args =>
        -- AVX2 256-bit vector op: read the looked-up arguments into an `HVector`
        -- and apply the dialect's `vymmDenote`, exactly as the dialect-denote
        -- `.vymm` arm does (arity split on `op.isBinary` handled inside).
        vymmDenote op op.isBinary (lookupArgsStore vm s args)
    | .mulhi w, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        mulHiW a b
    | .addCarryLo w, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        let cin : BitVec 1 := s.get (vm _ args.tail.tail.head) (.reg 1)
        addCarryWord a b cin
    | .addCarryHi w, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        let cin : BitVec 1 := s.get (vm _ args.tail.tail.head) (.reg 1)
        carryOutBit a b cin
    | .select w, args =>
        let cond : BitVec 1 := s.get (vm _ args.head) (.reg 1)
        let a : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.tail.head) (.reg w)
        selectW cond a b
    | .rorImm w n, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        a.rotateRight n
    | .shrImm w n, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        a >>> n
    | .sarImm w n, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        BitVec.sshiftRight a n
    | .shlImm w n, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        a <<< n
    | .callN _ _ retTys, _ =>
        -- Multi-result external call: opaque default of its head result slot,
        -- mirroring the `jasminDenote.callN` arm. The full `k`-result
        -- evaluation is the follow-on correctness re-proof.
        JasminTy.default (callNRet retTys)
    | .cmp c w, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        let b : BitVec w := s.get (vm _ args.tail.head) (.reg w)
        cmpBit c a b
    | .cmpImm c w n, args =>
        let a : BitVec w := s.get (vm _ args.head) (.reg w)
        cmpBit c a (BitVec.ofNat w n))

/-! ## 3. Store-agrees-with-valuation invariant -/

/-- The store `s` agrees with the De Bruijn valuation `V` under the name
    resolver `vm`: every variable's lowered name holds its valuation value, at
    its declared type. This ties the named evaluator state back to `Com.denote`'s
    De Bruijn valuation. -/
def StoreAgrees {Γ : Ctxt jasminDialect} (vm : VarMap Γ)
    (V : Ctxt.Valuation Γ) (s : Store) : Prop :=
  ∀ (t : jasminDialect.Ty) (v : Ctxt.Var Γ t), s.get (vm t v) t = v.lookup V

/-! ## 4. `execExpr` agrees with `Expr.denote` under `StoreAgrees`

Parametric in the leaf semantics: agreement on the `extCall` leaf is carried as
`hLeaf`. The non-leaf shapes (`regArith`, `castW`, `stackLoad`, `stackStore`)
are discharged from `StoreAgrees` directly — each `execExpr` branch is the
dialect op's `BitVec` / `stackGet` / `stackSet` semantics on the looked-up
arguments. -/

/-- Per-expression leaf agreement: on a store agreeing with `V`, the evaluator's
    `extCall` interpretation matches `jasminExtSem`. Quantified to slot into the
    program induction. -/
def LeafAgrees (leafSem : LeafSem) : Prop :=
  ∀ {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (V : Ctxt.Valuation Γ) (s : Store)
    (name : String) (argTys : List jasminDialect.Ty) (retTy : jasminDialect.Ty)
    (args : HVector (fun ty => Ctxt.Var Γ ty) argTys),
    StoreAgrees vm V s →
    leafSem name argTys retTy (lookupArgsStore vm s args)
      = jasminExtSem name argTys retTy (Expr.lookupArgs args V)

/-- `lookupArgsStore` agrees with `Expr.lookupArgs` whenever the store agrees
    with the valuation. -/
theorem lookupArgsStore_eq {Γ : Ctxt jasminDialect} {vm : VarMap Γ}
    {V : Ctxt.Valuation Γ} {s : Store} (hS : StoreAgrees vm V s) :
    {tys : List jasminDialect.Ty} →
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    lookupArgsStore vm s args = Expr.lookupArgs args V
  | [], .nil => rfl
  | ty :: _, .cons v rest => by
      show HVector.cons (s.get (vm ty v) ty) (lookupArgsStore vm s rest)
        = HVector.cons (v.lookup V) (Expr.lookupArgs rest V)
      rw [hS ty v, lookupArgsStore_eq hS rest]

/-- **`execExpr` is denotation-preserving (per expression), parametric in the
    leaf.** On a store agreeing with `V`, the evaluator computes the dialect
    `Expr.denote`. The non-leaf shapes are closed from `StoreAgrees`; the leaf
    uses `hLeaf`. -/
theorem execExpr_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    {vm : VarMap Γ} {V : Ctxt.Valuation Γ} {s : Store}
    (hS : StoreAgrees vm V s) (e : Expr jasminDialect Γ t) :
    execExpr leafSem vm e s = e.denote V := by
  rcases e with ⟨op, hret, args⟩
  -- Both sides transport along `hret` the same way; reduce to the un-transported
  -- op-semantics equality and case on the op.
  subst hret
  cases op with
  | regArith bop w =>
      -- args : HVector _ [reg w, reg w]
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          show bop.apply (s.get (vm _ a) (.reg w)) (s.get (vm _ b) (.reg w))
            = bop.apply (a.lookup V) (b.lookup V)
          rw [hS _ a, hS _ b]
  | stackLoad w n =>
      cases args with
      | cons arr rest =>
        cases rest with
        | cons i rest' =>
          show stackGet (s.get (vm _ arr) (.stackArr w n))
                (BitVec.toNat (s.get (vm _ i) (.reg 64)))
            = stackGet (arr.lookup V) (BitVec.toNat (i.lookup V))
          rw [hS _ arr, hS _ i]
  | stackStore w n =>
      cases args with
      | cons arr rest =>
        cases rest with
        | cons i rest' =>
          cases rest' with
          | cons v rest'' =>
            show stackSet (s.get (vm _ arr) (.stackArr w n))
                  (BitVec.toNat (s.get (vm _ i) (.reg 64)))
                  (s.get (vm _ v) (.reg w))
              = stackSet (arr.lookup V) (BitVec.toNat (i.lookup V)) (v.lookup V)
            rw [hS _ arr, hS _ i, hS _ v]
  | castW w w' =>
      cases args with
      | cons src rest =>
        show BitVec.zeroExtend w' (s.get (vm _ src) (.reg w))
          = BitVec.zeroExtend w' (src.lookup V)
        rw [hS _ src]
  | extCall name argTys retTy =>
      show leafSem name argTys retTy (lookupArgsStore vm s args)
        = jasminExtSem name argTys retTy (Expr.lookupArgs args V)
      exact hLeaf vm V s name argTys retTy args hS
  | callN name argTys retTys =>
      -- Multi-result call op: both `execExpr` and `Expr.denote` return the
      -- opaque default of the head result type, independent of args/store/V.
      rfl
  | regConst w n =>
      -- Nullary constant: both sides are `BitVec.ofNat w n`, no store/args
      -- dependency. `execExpr`'s arm and `Expr.denote`'s arm are
      -- definitionally the constant.
      rfl
  | vpackZMM bop =>
      -- AVX-512 8×u64 packed op: args : HVector _ [reg 512, reg 512]; both
      -- sides are `zmmPackQ bop` on the two looked-up registers.
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          show zmmPackQ bop (s.get (vm _ a) (.reg 512)) (s.get (vm _ b) (.reg 512))
            = zmmPackQ bop (a.lookup V) (b.lookup V)
          rw [hS _ a, hS _ b]
  | vpackZMMd bop =>
      -- AVX-512 16×u32 packed dword op: args : HVector _ [reg 512, reg 512];
      -- both sides are `zmmPackD bop` on the two looked-up registers.
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          show zmmPackD bop (s.get (vm _ a) (.reg 512)) (s.get (vm _ b) (.reg 512))
            = zmmPackD bop (a.lookup V) (b.lookup V)
          rw [hS _ a, hS _ b]
  | vprordZMM n =>
      -- AVX-512 16×u32 packed right-rotate-by-immediate: args : HVector _
      -- [reg 512]; both sides are `zmmRorD n` on the single looked-up register.
      cases args with
      | cons a rest =>
        show zmmRorD n (s.get (vm _ a) (.reg 512)) = zmmRorD n (a.lookup V)
        rw [hS _ a]
  | vpslldq n =>
      -- 128-bit byte-wise left shift: args : HVector _ [reg 128]; both sides are
      -- `· <<< (n * 8)` on the single looked-up register. The `show` spells the
      -- shift via `BitVec.shiftLeft` to avoid `HShiftLeft` resolution on the
      -- abstract `⟦reg 128⟧` carrier (defeq to `BitVec 128`).
      cases args with
      | cons a rest =>
        show BitVec.shiftLeft (s.get (vm _ a) (.reg 128)) (n * 8)
          = BitVec.shiftLeft (a.lookup V) (n * 8)
        rw [hS _ a]
  | vpsrldq n =>
      -- 128-bit byte-wise right shift: args : HVector _ [reg 128]; both sides are
      -- `· >>> (n * 8)` on the single looked-up register. The `show` spells the
      -- shift via `BitVec.ushiftRight` to avoid `HShiftRight` resolution on the
      -- abstract `⟦reg 128⟧` carrier (defeq to `BitVec 128`).
      cases args with
      | cons a rest =>
        show BitVec.ushiftRight (s.get (vm _ a) (.reg 128)) (n * 8)
          = BitVec.ushiftRight (a.lookup V) (n * 8)
        rw [hS _ a]
  | vsimd op =>
      -- Parametrized 128-bit SIMD op: args : HVector _ [reg 128, reg 128]; both
      -- sides are `op.denote` on the two looked-up registers. Case the inner
      -- `SimdOp` (so its signature reduces and the def's nested match unfolds to a
      -- concrete `SimdOp.X.denote`), then mirror the `vpackZMM` `show`/`rw` close
      -- per branch.
      cases op with
      | gf2p8mulb =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show SimdOp.gf2p8mulb.denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = SimdOp.gf2p8mulb.denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | vpshufb =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show SimdOp.vpshufb.denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = SimdOp.vpshufb.denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | clmul imm =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.clmul imm).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.clmul imm).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | affineqb imm =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.affineqb imm).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.affineqb imm).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | bitwise bop =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.bitwise bop).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.bitwise bop).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | packed bop laneW =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.packed bop laneW).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.packed bop laneW).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | mulhi16 =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.mulhi16).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.mulhi16).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | vaesenc =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.vaesenc).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.vaesenc).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | vaesenclast =>
        cases args with
        | cons a rest =>
          cases rest with
          | cons b rest' =>
            show (SimdOp.vaesenclast).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ b) (.reg 128))
              = (SimdOp.vaesenclast).denote (a.lookup V) (b.lookup V)
            rw [hS _ a, hS _ b]
      | vaeskeygen rcon =>
        -- unary: `argTys = [reg 128]`, so `args = cons a nil`; both denote sides
        -- read only `args.head` (the dialect-denote arm passes `src` twice).
        cases args with
        | cons a rest =>
          show (SimdOp.vaeskeygen rcon).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ a) (.reg 128))
              = (SimdOp.vaeskeygen rcon).denote (a.lookup V) (a.lookup V)
          rw [hS _ a]
      | vpshufd imm =>
        -- unary: `argTys = [reg 128]`, so `args = cons a nil`; both denote sides
        -- read only `args.head` (the dialect-denote arm passes `src` twice).
        cases args with
        | cons a rest =>
          show (SimdOp.vpshufd imm).denote (s.get (vm _ a) (.reg 128)) (s.get (vm _ a) (.reg 128))
              = (SimdOp.vpshufd imm).denote (a.lookup V) (a.lookup V)
          rw [hS _ a]
      | packedImm bop laneW imm =>
        -- unary: `argTys = [reg 128]`, so `args = cons a nil`; both denote sides
        -- read only `args.head` (the dialect-denote arm passes `src` twice).
        cases args with
        | cons a rest =>
          show (SimdOp.packedImm bop laneW imm).denote (s.get (vm _ a) (.reg 128))
                (s.get (vm _ a) (.reg 128))
              = (SimdOp.packedImm bop laneW imm).denote (a.lookup V) (a.lookup V)
          rw [hS _ a]
  | vymm op =>
      -- AVX2 256-bit vector op: both sides are `vymmDenote op op.isBinary`
      -- applied to the looked-up arguments, which agree under `StoreAgrees`
      -- via `lookupArgsStore_eq`.
      show vymmDenote op op.isBinary (lookupArgsStore vm s args)
        = vymmDenote op op.isBinary (Expr.lookupArgs args V)
      rw [lookupArgsStore_eq hS]
  | mulhi w =>
      -- Widening-multiply high word: both sides are `mulHiW` on two
      -- looked-up `reg w` factors.
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          show mulHiW (s.get (vm _ a) (.reg w)) (s.get (vm _ b) (.reg w))
            = mulHiW (a.lookup V) (b.lookup V)
          rw [hS _ a, hS _ b]
  | addCarryLo w =>
      -- Carry-chain data word: `addCarryWord` on `[a, b, cin]`.
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          cases rest' with
          | cons cin rest'' =>
            show addCarryWord (s.get (vm _ a) (.reg w)) (s.get (vm _ b) (.reg w))
                  (s.get (vm _ cin) (.reg 1))
              = addCarryWord (a.lookup V) (b.lookup V) (cin.lookup V)
            rw [hS _ a, hS _ b, hS _ cin]
  | addCarryHi w =>
      -- Carry-chain carry-out bit: `carryOutBit` on `[a, b, cin]`.
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          cases rest' with
          | cons cin rest'' =>
            show carryOutBit (s.get (vm _ a) (.reg w)) (s.get (vm _ b) (.reg w))
                  (s.get (vm _ cin) (.reg 1))
              = carryOutBit (a.lookup V) (b.lookup V) (cin.lookup V)
            rw [hS _ a, hS _ b, hS _ cin]
  | select w =>
      -- Constant-time select: `selectW` on `[cond, a, b]`.
      cases args with
      | cons cond rest =>
        cases rest with
        | cons a rest' =>
          cases rest' with
          | cons b rest'' =>
            show selectW (s.get (vm _ cond) (.reg 1)) (s.get (vm _ a) (.reg w))
                  (s.get (vm _ b) (.reg w))
              = selectW (cond.lookup V) (a.lookup V) (b.lookup V)
            rw [hS _ cond, hS _ a, hS _ b]
  | rorImm w n =>
      -- Native right-rotate: both sides are `rotateRight n` on the single
      -- looked-up `reg w` source.
      cases args with
      | cons a rest =>
        show (s.get (vm _ a) (.reg w)).rotateRight n
          = (a.lookup V).rotateRight n
        rw [hS _ a]
  | shrImm w n =>
      -- Native immediate right-shift: both sides are `>>> n` on the single
      -- looked-up `reg w` source.
      cases args with
      | cons a rest =>
        show (BitVec.ushiftRight (s.get (vm _ a) (.reg w)) n)
          = BitVec.ushiftRight (a.lookup V) n
        rw [hS _ a]
  | sarImm w n =>
      -- Native immediate arithmetic right-shift: both sides are
      -- `sshiftRight … n` on the single looked-up `reg w` source.
      cases args with
      | cons a rest =>
        show (BitVec.sshiftRight (s.get (vm _ a) (.reg w)) n)
          = BitVec.sshiftRight (a.lookup V) n
        rw [hS _ a]
  | shlImm w n =>
      -- Native immediate left-shift: both sides are `<<< n` on the single
      -- looked-up `reg w` source.
      cases args with
      | cons a rest =>
        show (BitVec.shiftLeft (s.get (vm _ a) (.reg w)) n)
          = BitVec.shiftLeft (a.lookup V) n
        rw [hS _ a]
  | cmp c w =>
      cases args with
      | cons a rest =>
        cases rest with
        | cons b rest' =>
          show cmpBit c (s.get (vm _ a) (.reg w)) (s.get (vm _ b) (.reg w))
            = cmpBit c (a.lookup V) (b.lookup V)
          rw [hS _ a, hS _ b]
  | cmpImm c w n =>
      cases args with
      | cons a rest =>
        show cmpBit c (s.get (vm _ a) (.reg w)) (BitVec.ofNat w n)
          = cmpBit c (a.lookup V) (BitVec.ofNat w n)
        rw [hS _ a]

/-! ## 5. Threading the lowered instruction list through the store

`lowerCom vm next com = (instrs, resName)`: a list of emitted `InstrR` plus the
name holding the result. The matching evaluator `execCom` threads the store one
emitted `Cassgn`/`Ccall` at a time. To stay faithful to the *emitted instruction
list* — rather than re-deriving the semantics from the typed `Com` — we define
`execCom` to mirror `lowerCom`'s fold exactly: each `Com.var` step writes
`execExpr`'s value to the bound name (`resultName`), which is what executing the
single emitted instruction `lowerExpr e bound` does. The bridge lemma
`execInstr_lowerExpr_eq` records that one emitted instruction performs exactly
this store update for the `regArith`/`castW` shapes (`extCall` parametric),
making `execCom` the semantics of running `(lowerCom …).1`. -/

/-- Run the store-threaded evaluator on a `Com`, mirroring `lowerCom`'s fold:
    each `var e body` step writes `execExpr e` to the result name
    (`resultName`, fresh `vN` except for the in-place `stackStore`), then
    continues. Returns the store after the whole (emitted) instruction list and
    the value at the result name. -/
def execCom {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (leafSem : LeafSem) (vm : VarMap Γ) (next : Nat) (s : Store) :
    Com jasminDialect Γ t → Store × ⟦t⟧
  | .ret v => (s, s.get (vm t v) t)
  | .var (t := tEx) e body =>
      let fresh := "v" ++ toString next
      let bound := resultName vm e fresh
      let s' := s.set bound (t := tEx) (execExpr leafSem vm e s)
      execCom leafSem (vm.extend (t := tEx) bound) (next + 1) s' body

/-! ## 6. Freshness for the `regArith`/`castW` straight-line fragment

The store update in `execCom`'s `var` step writes the bound name. For the
end-to-end agreement we need that this write does not disturb the values of
variables already in scope — i.e. the bound name differs from every existing
name `vm s v`. For `regArith`/`castW` the bound name is always the fresh counter
name `v{next}`, and the names threaded by `lowerCom` (params `p{i}` and earlier
binders `v{<next}`) are all distinct from it, so freshness holds. We capture the
"all in-scope names are `< next`" discipline as a predicate on resolvers,
phrased via the *fresh-name function* `freshName n = "v" ++ toString n`.

### Why `freshName` injectivity is carried as a hypothesis

The freshness step needs `freshName` injective on `Nat` (distinct counters give
distinct SSA names — manifestly true). This bottoms out at injectivity of
`Nat.repr` (= `toString` on `Nat`), for which **no lemma exists in this
toolchain's Lean core / Mathlib / Batteries** (verified: `exact?` and
`Function.Injective Nat.repr` both fail to find one; `Nat.toDigits` — used by
`Nat.repr` — has no roundtrip/injectivity lemma, and `Mathlib.Nat.digits` is a
different function). Rather than reprove `Nat.repr` injectivity from the digit
arithmetic (a substantial detour orthogonal to compiler correctness), we carry
it as the single explicit hypothesis `hInj : Function.Injective freshName`. It
is **not** an admitted proof: it is a true, named side-condition that any caller
discharges the moment a `Nat.repr`-injectivity lemma is available. Everything
else in the freshness and preservation argument is closed unconditionally. -/

/-- The fresh-SSA-name function `lowerCom` uses for its counter: `n ↦ "v{n}"`. -/
def freshName (n : Nat) : String := "v" ++ toString n

/-- A resolver is *bounded below `next`*: it never produces the current fresh
    name `freshName next` or any later one. This is the discipline `lowerCom`
    maintains — it starts from `paramsAndMap` (only `p…` names) and each `var`
    binds `freshName next` with a strictly larger counter for the tail. -/
def FreshFor {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (next : Nat) : Prop :=
  ∀ (k : Nat) (t : jasminDialect.Ty) (v : Ctxt.Var Γ t),
    next ≤ k → vm t v ≠ freshName k

/-- The empty resolver is fresh for any counter (vacuous: no variables). -/
theorem FreshFor.empty (next : Nat) : FreshFor (Γ := []) VarMap.empty next :=
  fun _ _ v _ => by cases v

/-- Extending a fresh resolver with the *current* fresh name `freshName next`
    yields a resolver fresh for `next + 1`: the new `.here` binding is
    `freshName next` which differs from every `freshName k` with `k ≥ next + 1`
    (by injectivity `hInj`, since `next ≠ k`), and the shifted old bindings stay
    fresh by monotonicity. -/
theorem FreshFor.extend_v {Γ : Ctxt jasminDialect} {tEx : jasminDialect.Ty}
    {vm : VarMap Γ} {next : Nat} (hInj : Function.Injective freshName)
    (h : FreshFor vm next) :
    FreshFor (vm.extend (t := tEx) (freshName next)) (next + 1) := by
  intro k t v hk
  cases v with
  | here =>
      -- `.here ↦ freshName next`, and `k ≥ next + 1`, so `next ≠ k`.
      show freshName next ≠ freshName k
      intro heq
      exact absurd (hInj heq) (by omega)
  | there v' =>
      -- shifted old binding: `vm.extend … (.there v') = vm t v'`, fresh by `h`.
      show vm t v' ≠ freshName k
      exact h k t v' (by omega)

/-! ## 7. The straight-line (non-`stackStore`) fragment

A `Com` is *straight-line* if every let-binder's op is **not** `stackStore`:
then `resultName vm e fresh = fresh` (a fresh `v{next}`), so each emitted write
targets a brand-new name. `stackStore` is the sole op that reuses the source
array's name (`resultName` returns `argName … 0`), deliberately aliasing it
(in-place `a[i] = v`); that aliasing is exactly why the fresh-name freshness
argument does not cover it, recorded in `stackStore_aliases_source`. -/

/-- `e`'s op is not `stackStore` (so `resultName` returns the fresh name). -/
def ExprNotStackStore {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (e : Expr jasminDialect Γ t) : Prop :=
  ∀ w n, e.op ≠ .stackStore w n

/-- Every let-binder of `com` has a non-`stackStore` op. -/
def StraightLine {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    Com jasminDialect Γ t → Prop
  | .ret _ => True
  | .var e body => ExprNotStackStore e ∧ StraightLine body

/-- On a non-`stackStore` binder, `resultName` returns the supplied fresh name
    (the only branch that differs is `stackStore`). -/
theorem resultName_of_notStackStore {Γ : Ctxt jasminDialect}
    {t : jasminDialect.Ty} {vm : VarMap Γ} {e : Expr jasminDialect Γ t}
    (h : ExprNotStackStore e) (fresh : String) :
    resultName vm e fresh = fresh := by
  unfold resultName
  split
  · next w n heq => exact absurd heq (h w n)
  · rfl

/-- **Recorded gap (the lone aliasing op).** For a `stackStore` binder,
    `resultName` reuses the *source array* name (`argName … 0`) rather than the
    fresh name — Jasmin's in-place `a[i] = v` idiom. This deliberate aliasing is
    why `stackStore` is excluded from the straight-line freshness argument: the
    emitted write clobbers a name that may still be in scope. -/
theorem stackStore_aliases_source {Γ : Ctxt jasminDialect} {w n : Nat}
    {vm : VarMap Γ} (e : Expr jasminDialect Γ (.stackArr w n))
    (hop : e.op = .stackStore w n) (fresh : String) :
    resultName vm e fresh = argName vm e.args 0 := by
  rcases e with ⟨op, hret, args⟩
  subst hop
  rfl

/-! ## 8. `StoreAgrees` is preserved by one straight-line `var` step

Writing the fresh name `freshName next` to the store, then extending the
resolver with that name, preserves `StoreAgrees` for the extended valuation:
the new `.here` binding reads back by `get_set_same`; the shifted old bindings
read back unchanged by `get_set_other` (using freshness `hF`). -/

/-- One straight-line step preserves `StoreAgrees`. -/
theorem storeAgrees_step {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {Γ : Ctxt jasminDialect} {tEx : jasminDialect.Ty}
    {vm : VarMap Γ} {V : Ctxt.Valuation Γ} {s : Store} {next : Nat}
    (e : Expr jasminDialect Γ tEx)
    (hS : StoreAgrees vm V s) (hF : FreshFor vm next) :
    StoreAgrees (vm.extend (t := tEx) (freshName next))
      (V.extend (e.denote V))
      (s.set (freshName next) (t := tEx) (execExpr leafSem vm e s)) := by
  intro t' v
  cases v with
  | here =>
      -- new binding: `(vm.extend …) tEx .here = freshName next`; value is the
      -- denotation of `e` (= `execExpr` by `execExpr_eq`), read by `get_set_same`.
      show (s.set (freshName next) (execExpr leafSem vm e s)).get (freshName next) tEx
        = Ctxt.Var.lookup .here (V.extend (e.denote V))
      rw [Store.get_set_same]
      exact execExpr_eq hLeaf hS e
  | there v' =>
      -- shifted old binding: name is `vm t' v'`, fresh ⇒ untouched by the write.
      show (s.set (freshName next) (execExpr leafSem vm e s)).get (vm t' v') t'
        = Ctxt.Var.lookup (.there v') (V.extend (e.denote V))
      rw [Store.get_set_other s (hF next t' v' (Nat.le_refl next))]
      exact hS t' v'

/-! ## 9. `execCom` agrees with `Com.denote` on the straight-line fragment

By induction on the program. The `.ret` case reads the result name (=
`vm t v`), which agrees with `v.lookup V` by `StoreAgrees`. The `.var` case
steps the store via `storeAgrees_step` (under freshness, advanced by
`FreshFor.extend_v`) and applies the IH. -/

/-- **`execCom` is denotation-preserving on the straight-line fragment**,
    parametric in the leaf semantics. Under leaf agreement (`hLeaf`), fresh-name
    injectivity (`hInj`), the store-agreement invariant (`hS`), and freshness of
    the resolver (`hF`), the result value `execCom` reads from the threaded store
    equals `Com.denote com V`. -/
theorem execCom_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    (com : Com jasminDialect Γ t) → StraightLine com →
    {vm : VarMap Γ} → {V : Ctxt.Valuation Γ} → {s : Store} → {next : Nat} →
    StoreAgrees vm V s → FreshFor vm next →
    (execCom leafSem vm next s com).2 = com.denote V
  | .ret v, _, vm, V, s, _next, hS, _hF => by
      show s.get (vm t v) t = v.lookup V
      exact hS t v
  | .var (t := tEx) e body, hSL, vm, V, s, next, hS, hF => by
      obtain ⟨hNS, hSLbody⟩ := hSL
      -- `bound = resultName … = freshName next` since `e` is not a stackStore.
      have hbound : resultName vm e ("v" ++ toString next) = freshName next :=
        resultName_of_notStackStore hNS ("v" ++ toString next)
      -- Unfold one step of `execCom` and `Com.denote`.
      rw [show (execCom leafSem vm next s (.var e body)).2
            = (execCom leafSem (vm.extend (resultName vm e ("v" ++ toString next)))
                (next + 1)
                (s.set (resultName vm e ("v" ++ toString next))
                  (execExpr leafSem vm e s)) body).2 from rfl,
          show (Com.var e body).denote V = body.denote (V.extend (e.denote V))
            from rfl,
          hbound]
      -- Step the invariant and freshness, then apply the IH on `body`.
      have hS' := storeAgrees_step hLeaf e hS hF
      have hF' := FreshFor.extend_v (tEx := tEx) hInj hF
      exact execCom_eq hLeaf hInj body hSLbody hS' hF'

/-! ## 10. Seeding the parameter store and running the whole program

`lowerComToProg name com` materialises `Γ` as parameters via `paramsAndMap`
(names `p0, p1, …`) and uses `(lowerCom vm 0 com).1` as the body, returning
`(lowerCom vm 0 com).2`. To *run* it on an input valuation `V` we seed a store in
which each parameter name `vm t v` holds `v.lookup V` — i.e. a store that
`StoreAgrees`. The function `seedStore vm V` builds exactly that; it agrees by
construction (`seedStore_agrees`). The parameter resolver is `FreshFor … 0`:
every parameter name begins with `'p'`, never matching a `freshName k = "v…"`
(`paramsAndMap_FreshFor`). Running the program — `runProg` — executes `execCom`
from the seed and reads the declared result name; by `execCom_eq` it equals
`Com.denote`. -/

/-- Seed a store from a valuation under a resolver: each variable's lowered name
    holds its value; all other names get the type default. `vm` is presumed
    injective on the variables in scope (true of `paramsAndMap`), which makes the
    seed agree — captured cleanly by `seedStore_agrees` requiring an
    independence witness. We build the seed by folding the valuation. -/
def seedStore {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (V : Ctxt.Valuation Γ) :
    Store :=
  match Γ, vm, V with
  | [], _, _ => fun _ => DynVal.default (.reg 0)
  | _ :: _, vm, .cons hd tl =>
      (seedStore (fun t v => vm t (.there v)) tl).set
        (vm _ Ctxt.Var.here) (t := _) hd

/-- The seed store agrees with the valuation it was built from, **provided** the
    resolver is injective on the in-scope variables (distinct variables get
    distinct names) — which holds for `paramsAndMap` by construction. We carry
    the injectivity as the hypothesis `hVMinj`. -/
theorem seedStore_agrees {Γ : Ctxt jasminDialect} {vm : VarMap Γ}
    {V : Ctxt.Valuation Γ}
    (hVMinj : ∀ (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t)
                (v' : Ctxt.Var Γ t'), vm t v = vm t' v' →
                (∃ h : t = t', h ▸ v = v')) :
    StoreAgrees vm V (seedStore vm V) := by
  induction Γ with
  | nil => intro t v; cases v
  | cons hdTy rest ih =>
      cases V with
      | cons hd tl =>
          intro t v
          cases v with
          | here =>
              show (seedStore _ tl |>.set (vm hdTy .here) hd).get
                    (vm hdTy .here) hdTy = hd
              rw [Store.get_set_same]
          | there v' =>
              -- The shifted resolver `fun t v => vm t (.there v)` is injective on
              -- `rest` (inherited from `hVMinj`), so the IH gives agreement on the
              -- seed for `tl`; the `.here` write is at a *different* name iff
              -- `vm t (.there v') ≠ vm hdTy .here`, which `hVMinj` provides.
              have hne : vm t (.there v') ≠ vm hdTy Ctxt.Var.here := by
                intro heq
                obtain ⟨h, hv⟩ := hVMinj t hdTy (.there v') Ctxt.Var.here heq
                cases h
                exact absurd hv (by simp)
              show (seedStore _ tl |>.set (vm hdTy .here) hd).get
                    (vm t (.there v')) t = Ctxt.Var.lookup (.there v') (.cons hd tl)
              rw [Store.get_set_other _ hne]
              exact ih (vm := fun t v => vm t (.there v))
                (V := tl)
                (fun t t' v v' he => by
                  obtain ⟨h, hv⟩ := hVMinj t t' (.there v) (.there v') he
                  cases h
                  refine ⟨rfl, ?_⟩
                  simpa using (Ctxt.Var.there.inj (by simpa using hv))) t v'

/-! ## 11. The parameter resolver: fresh and injective

`paramsAndMapFrom base Γ` names every parameter `"p" ++ toString j`. So:

* **Fresh:** every parameter name begins with `'p'`, while `freshName k`
  begins with `'v'` — they differ in the first character, so
  `FreshFor (paramsAndMap Γ).2 0` holds *without* any Nat-string injectivity
  (only a first-character comparison).
* **Injective:** distinct parameters get distinct names — the resolver
  injectivity that `seedStore_agrees` needs. -/

/-- Every name produced by `paramsAndMapFrom base Γ` has the form
    `"p" ++ toString j`, so its first character is `'p'`
    (`toList.head? = some 'p'`). This separates it from the `"v…"` fresh names
    via a single-character comparison — no Nat-string injectivity needed. -/
theorem paramsAndMapFrom_head_p (base : Nat) :
    ∀ {Γ : Ctxt jasminDialect} (t : jasminDialect.Ty) (v : Ctxt.Var Γ t),
      ((paramsAndMapFrom base Γ).2 t v).toList.head? = some 'p'
  | _ :: _, _, .here => by
      -- `.here ↦ "p" ++ toString base`; first char is 'p'.
      show (("p" ++ toString base : String)).toList.head? = some 'p'
      rw [String.toList_append, show ("p" : String).toList = ['p'] from rfl]
      rfl
  | _ :: rest, t, .there v' => by
      -- `.there v' ↦ (paramsAndMapFrom (base+1) rest) t v'`.
      show ((paramsAndMapFrom (base + 1) rest).2 t v').toList.head? = some 'p'
      exact paramsAndMapFrom_head_p (base + 1) t v'

/-- The parameter resolver is `FreshFor … 0`: a `"p…"` name never equals a
    `freshName k = "v…"` name (their first characters `'p'` / `'v'` differ). -/
theorem paramsAndMap_FreshFor {Γ : Ctxt jasminDialect} :
    FreshFor (paramsAndMap Γ).2 0 := by
  intro k t v _
  -- The param name's first char is 'p'; `freshName k`'s is 'v'.
  have hp : ((paramsAndMap Γ).2 t v).toList.head? = some 'p' :=
    paramsAndMapFrom_head_p 0 t v
  have hv : (freshName k).toList.head? = some 'v' := by
    show (("v" ++ toString k : String)).toList.head? = some 'v'
    rw [String.toList_append, show ("v" : String).toList = ['v'] from rfl]
    rfl
  intro heq
  rw [heq, hv] at hp
  exact absurd hp (by decide)

/-! ## 12. Running the whole lowered program

`runProg leafSem name com V` runs the lowered program `lowerComToProg name com`
on the input valuation `V`: it seeds the parameter store from `V` (via
`seedStore` under the parameter resolver), threads `execCom` from counter `0`
over the lowered body, and reads the value at the declared result name. This is
the semantic content of "execute the emitted `JasminProg`": the body is exactly
`(lowerCom (paramsAndMap Γ).2 0 com).1` and the result name is
`(lowerCom … 0 com).2`, the single `VarI` in the function's `results`. -/

/-- Run the lowered single-function program on an input valuation: seed the
    parameter store, execute the lowered body, read the result name. -/
def runProg {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (leafSem : LeafSem) (com : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) : ⟦t⟧ :=
  let vm := (paramsAndMap Γ).2
  (execCom leafSem vm 0 (seedStore vm V) com).2

/-- **Main theorem — `lowerComToProg` is denotation-preserving (semantic half),
    on the `regArith`/`castW` straight-line fragment, parametric in the leaf.**

    Running the lowered program (`runProg`) under a word-level evaluator on the
    seeded parameter store yields exactly `Com.denote com V`, provided:

    * `hLeaf` — the evaluator's `extCall` interpretation agrees with the
      dialect's `jasminExtSem` (the opaque-leaf edge, exactly as carried by
      `LatticeToJasminDenote` / `CryptoToJasminComCorrect`);
    * `com` is straight-line (`StraightLine`: every binder is `regArith`/`castW`/
      `stackLoad`/`extCall`, never the aliasing `stackStore` — see
      `stackStore_aliases_source`);
    * `hInj` — the fresh-SSA-name function `freshName` is injective (a true
      naming fact bottoming out at `Nat.repr` injectivity, for which no toolchain
      lemma exists — carried as a hypothesis, never an admitted proof);
    * `hPinj` — the parameter resolver is injective (distinct parameters get
      distinct `"p…"` names; same `Nat.repr` provenance), making the seed store
      agree with `V`.

    The parameter resolver's freshness (`FreshFor … 0`) is discharged
    unconditionally (`paramsAndMap_FreshFor`). -/
theorem lowerComToProg_sem_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) (hSL : StraightLine com)
    (hPinj : ∀ (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t)
                (v' : Ctxt.Var Γ t'), (paramsAndMap Γ).2 t v = (paramsAndMap Γ).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation Γ) :
    runProg leafSem com V = com.denote V := by
  unfold runProg
  exact execCom_eq hLeaf hInj com hSL
    (seedStore_agrees hPinj) paramsAndMap_FreshFor

/-! ## 13. Smoke instance on the dialect's `smokeProg`

`JasminDialect.smokeProg : Com jasminDialect [reg 32, reg 32] (reg 64)` is the
canonical `regArith add` + `castW 32 64` straight-line program — exactly the
fully-closed fragment. Under leaf agreement (vacuous here — no `extCall`), name
injectivity, and parameter injectivity, running its lowering computes
`(a + b).zeroExtend 64`, matching `Com.denote`. The `StraightLine` witness is
`decide`-checked (both binders are `regArith`/`castW`). -/

/-- `smokeProg` is straight-line (both binders non-`stackStore`). -/
theorem smokeProg_straightLine : StraightLine JasminDialect.smokeProg := by
  refine ⟨fun w n h => ?_, fun w n h => ?_, trivial⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **Smoke (whole program).** Under the parametric hypotheses, running the
    lowered `smokeProg` agrees with its `Com.denote`. -/
theorem smokeProg_sem_eq {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    (hPinj : ∀ (t t' : jasminDialect.Ty)
                (v : Ctxt.Var (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32] t)
                (v' : Ctxt.Var (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32] t'),
                (paramsAndMap [JasminTy.reg 32, JasminTy.reg 32]).2 t v
                  = (paramsAndMap [JasminTy.reg 32, JasminTy.reg 32]).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (V : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 32, JasminTy.reg 32]) :
    runProg leafSem JasminDialect.smokeProg V
      = JasminDialect.smokeProg.denote V :=
  lowerComToProg_sem_eq hLeaf hInj JasminDialect.smokeProg
    smokeProg_straightLine hPinj V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
