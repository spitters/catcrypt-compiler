/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# A *denoting* MLIR `arith` dialect in the VIR framework

> **STATUS — MLIR-CORRESPONDENCE LAYER, NOT THE EMIT PATH.** This dialect's
> content is `rfl` semantic-agreement lemmas proving CatCrypt ops match upstream
> MLIR `arith`; it has NO lowering out and carries ZERO emit traffic. It
> duplicates `jasminDialect`'s scalar word ops, which ARE the real substrate. See
> `CatCrypt/Crypto/SecureCompilation/VIR/DIALECTS.md`.

The MLIR emission pass `CatCryptOp.toArithOpCode`
(`ComToVeir_CatCryptDialect.lean`) maps each arithmetic / bit / control
`CatCryptOp` to a Veir `OpCode` (`arith.addi`, `arith.subi`, …). But Veir's
`OpCode` is a bare tag enum with **no denotation**, so that lowering is only
*structurally* correct — there is no statement, let alone proof, that it
preserves the BitVec meaning of the source op.

This file supplies the missing semantic foundation. It defines a **local**
denoting MLIR `arith` dialect `mlirArithDialect` inside the VIR
`Dialect`/`DialectDenote` framework (the same framework `catCryptDialect`
lives in), with the *standard MLIR `arith` integer semantics*:

| op          | denotation                |
|-------------|---------------------------|
| `addi w`    | BitVec `+`                |
| `subi w`    | BitVec `-`                |
| `muli w`    | BitVec `*`                |
| `xori w`    | BitVec `^^^`              |
| `andi w`    | BitVec `&&&`              |
| `ori  w`    | BitVec `|||`              |
| `shli w k`  | `· <<< k`                 |
| `shrui w k` | `BitVec.ushiftRight · k`  |
| `cmpi w`    | `decide (· = ·)` (eq pred) |
| `select t`  | `if · then · else ·`      |
| `constant`  | the literal               |
| `extsi n`   | `if · then allOnes else 0`|

The bit-level (`i1`) ops (`xori1`/`andi1`/`ori1`/`cmpi1`/`xnori1`) are the
`bit`-typed analogues of the catCrypt `xor`/`and`/`or`/`eqBit`/`not` ops; in
real MLIR these are the same `arith.xori`/… opcodes at width `i1` — we keep
them as separate constructors here only so the `DialectSignature` can pin the
`bit` argument/return types exactly.

The semantics are deliberately chosen to **match** `catCryptDialect`'s BitVec
denotations. The payoff is the per-op **semantic agreement** lemmas in §3:
for each catCrypt arith op, its `DialectDenote.denote` equals the matching
`mlirArithDialect` op's `DialectDenote.denote` on the same arguments. These
are the per-op analogue of the jasmin `LeafAgrees` and the crux that makes a
full denotation-preserving `Com catCryptDialect → Com mlirArithDialect`
translation provable.

All agreement lemmas close by `rfl` (the denotations are definitionally the
same function), confirming the two dialects assign identical meaning to the
arith fragment.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-! ## 1. Op tags

The MLIR `arith` ops we lower to. Types reuse `CryptoTy` (so `sword w` and
`bit` denote to `BitVec w` and `Bool`, matching `catCryptDialect` exactly). -/

/-- Operation tags for the local denoting MLIR `arith` dialect. Each
    constructor corresponds to a registered MLIR `arith.*` opcode that
    `CatCryptOp.toArithOpCode` targets. Width / shift-amount / element-type
    static data is carried as parameters, mirroring `CatCryptOp`. -/
inductive MlirArithOp where
  -- integer (iN) arithmetic
  | constant (w : Nat) (v : BitVec w)        -- `arith.constant`
  | addi (w : Nat)                           -- `arith.addi`
  | subi (w : Nat)                           -- `arith.subi`
  | muli (w : Nat)                           -- `arith.muli`
  | xori (w : Nat)                           -- `arith.xori`
  | andi (w : Nat)                           -- `arith.andi`
  | ori  (w : Nat)                           -- `arith.ori`
  | xoriAllOnes (w : Nat)                     -- `arith.xori %x, allOnes` (= `bvNot`)
  | shli (w : Nat) (k : Nat)                 -- `arith.shli`
  | shrui (w : Nat) (k : Nat)                -- `arith.shrui`
  | cmpi (w : Nat)                           -- `arith.cmpi eq` : (iN, iN) → i1
  -- bit (i1) arithmetic — `arith.*` at width 1
  | constantBit (v : Bool)                   -- `arith.constant` (i1)
  | xori1                                    -- `arith.xori` (i1)
  | andi1                                    -- `arith.andi` (i1)
  | ori1                                     -- `arith.ori`  (i1)
  | cmpi1                                    -- `arith.cmpi eq` (i1) → i1
  | xnori1                                   -- `arith.xori %x, true` (= `not`)
  -- control / extension
  | select (t : CryptoTy)                    -- `arith.select`
  | extsi (n : Nat)                       -- `arith.extsi i1 → iN` (allOnes-or-0 mask)
  deriving DecidableEq

/-! ## 2. The dialect, signature and denotation -/

/-- The local MLIR `arith` dialect: `Op` is `MlirArithOp`, `Ty` is `CryptoTy`
    (shared with `catCryptDialect`, so the `TyDenote CryptoTy` instance from
    `CatCryptDialect.lean` applies). -/
@[reducible] def mlirArithDialect : Dialect :=
  { Op := MlirArithOp, Ty := CryptoTy }

/-- Operation signatures: argument types + return type. Chosen to match the
    catCrypt op the constructor mirrors. -/
instance : DialectSignature mlirArithDialect where
  sig op := match op with
    | .constant _ _ => []
    | .addi w | .subi w | .muli w | .xori w | .andi w | .ori w =>
        [.sword w, .sword w]
    | .xoriAllOnes w => [.sword w]
    | .shli w _ | .shrui w _ => [.sword w]
    | .cmpi w => [.sword w, .sword w]
    | .constantBit _ => []
    | .xori1 | .andi1 | .ori1 | .cmpi1 => [.bit, .bit]
    | .xnori1 => [.bit]
    | .select t => [.bit, t, t]
    | .extsi _ => [.bit]
  ret op := match op with
    | .constant w _ => .sword w
    | .addi w | .subi w | .muli w | .xori w | .andi w | .ori w
    | .xoriAllOnes w => .sword w
    | .shli w _ | .shrui w _ => .sword w
    | .cmpi _ => .bit
    | .constantBit _ => .bit
    | .xori1 | .andi1 | .ori1 | .cmpi1 | .xnori1 => .bit
    | .select t => t
    | .extsi n => .sword n

/-- Operation denotation: the **standard MLIR `arith` integer semantics**.
    Each clause is chosen to coincide with `catCryptDenote`'s clause for the
    op `toArithOpCode` maps from (see §3). -/
instance mlirArithDenote : DialectDenote mlirArithDialect where
  denote op := match op with
    | .constant _ v => fun _ => v
    | .addi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a + b
    | .subi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a - b
    | .muli w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a * b
    | .xori w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a ^^^ b
    | .andi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a &&& b
    | .ori w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a ||| b
    | .xoriAllOnes w => fun args =>
        show BitVec w from ~~~(args.head : BitVec w)
    | .shli w k => fun args =>
        let a : BitVec w := args.head
        a <<< k
    | .shrui w k => fun args =>
        let a : BitVec w := args.head
        BitVec.ushiftRight a k
    | .cmpi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        decide (a = b)
    | .constantBit v => fun _ => v
    | .xori1 => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        Bool.xor a b
    | .andi1 => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        a && b
    | .ori1 => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        a || b
    | .cmpi1 => fun args =>
        let a : Bool := args.head
        let b : Bool := args.tail.head
        (Bool.xor a b).not
    | .xnori1 => fun args => !(args.head : Bool)
    | .select _ => fun args =>
        if (args.head : Bool) then args.tail.head else args.tail.tail.head
    | .extsi n => fun args =>
        show BitVec n from
          if (args.head : Bool) then BitVec.allOnes n else 0

/-! ## 3. Per-op semantic agreement

For each catCrypt arith op, its `DialectDenote.denote` equals the
corresponding `mlirArithDialect` op's `DialectDenote.denote` on the same
arguments. Because the two `DialectDenote` instances were written with
matching clauses (and identical `DialectSignature.sig`/`ret`, so the argument
`HVector` and return types coincide definitionally), every lemma closes by
`rfl`.

This is the per-op analogue of the jasmin `LeafAgrees` family: it certifies
that each target of `toArithOpCode` denotes to the same function as its
source. -/

section Agreement

/-- `bvAdd w` agrees with `addi w`. -/
theorem agree_bvAdd (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvAdd w)
      = DialectDenote.denote (d := mlirArithDialect) (.addi w) := rfl

/-- `bvSub w` agrees with `subi w`. -/
theorem agree_bvSub (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvSub w)
      = DialectDenote.denote (d := mlirArithDialect) (.subi w) := rfl

/-- `bvMul w` agrees with `muli w`. -/
theorem agree_bvMul (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvMul w)
      = DialectDenote.denote (d := mlirArithDialect) (.muli w) := rfl

/-- `bvXor w` agrees with `xori w`. -/
theorem agree_bvXor (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvXor w)
      = DialectDenote.denote (d := mlirArithDialect) (.xori w) := rfl

/-- `bvAnd w` agrees with `andi w`. -/
theorem agree_bvAnd (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvAnd w)
      = DialectDenote.denote (d := mlirArithDialect) (.andi w) := rfl

/-- `bvOr w` agrees with `ori w`. -/
theorem agree_bvOr (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvOr w)
      = DialectDenote.denote (d := mlirArithDialect) (.ori w) := rfl

/-- `bvNot w` agrees with `xoriAllOnes w` (`arith.xori %x, allOnes`). -/
theorem agree_bvNot (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvNot w)
      = DialectDenote.denote (d := mlirArithDialect) (.xoriAllOnes w) := rfl

/-- `bvShiftL w k` agrees with `shli w k`. -/
theorem agree_bvShiftL (w k : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvShiftL w k)
      = DialectDenote.denote (d := mlirArithDialect) (.shli w k) := rfl

/-- `bvShiftR w k` agrees with `shrui w k`. -/
theorem agree_bvShiftR (w k : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvShiftR w k)
      = DialectDenote.denote (d := mlirArithDialect) (.shrui w k) := rfl

/-- `bvEq w` agrees with `cmpi w` (`arith.cmpi eq`). -/
theorem agree_bvEq (w : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bvEq w)
      = DialectDenote.denote (d := mlirArithDialect) (.cmpi w) := rfl

/-- `bvConst w v` agrees with `constant w v` (`arith.constant`). -/
theorem agree_bvConst (w : Nat) (v : BitVec w) :
    DialectDenote.denote (d := catCryptDialect) (.bvConst w v)
      = DialectDenote.denote (d := mlirArithDialect) (.constant w v) := rfl

/-- `ite t` agrees with `select t` (`arith.select`). -/
theorem agree_ite (t : CryptoTy) :
    DialectDenote.denote (d := catCryptDialect) (.ite t)
      = DialectDenote.denote (d := mlirArithDialect) (.select t) := rfl

/-- `bitToSword n` agrees with `extsi n` (`arith.extsi` of an `i1`: the allOnes-or-0 mask). -/
theorem agree_bitToSword (n : Nat) :
    DialectDenote.denote (d := catCryptDialect) (.bitToSword n)
      = DialectDenote.denote (d := mlirArithDialect) (.extsi n) := rfl

/-- bit-level `xor` agrees with `xori1` (`arith.xori` at i1). -/
theorem agree_xor :
    DialectDenote.denote (d := catCryptDialect) .xor
      = DialectDenote.denote (d := mlirArithDialect) .xori1 := rfl

/-- bit-level `and` agrees with `andi1` (`arith.andi` at i1). -/
theorem agree_and :
    DialectDenote.denote (d := catCryptDialect) .and
      = DialectDenote.denote (d := mlirArithDialect) .andi1 := rfl

/-- bit-level `or` agrees with `ori1` (`arith.ori` at i1). -/
theorem agree_or :
    DialectDenote.denote (d := catCryptDialect) .or
      = DialectDenote.denote (d := mlirArithDialect) .ori1 := rfl

/-- bit-level `eqBit` agrees with `cmpi1` (`arith.cmpi eq` at i1). -/
theorem agree_eqBit :
    DialectDenote.denote (d := catCryptDialect) .eqBit
      = DialectDenote.denote (d := mlirArithDialect) .cmpi1 := rfl

/-- bit-level `not` agrees with `xnori1` (`arith.xori %x, true`). -/
theorem agree_not :
    DialectDenote.denote (d := catCryptDialect) .not
      = DialectDenote.denote (d := mlirArithDialect) .xnori1 := rfl

/-- bit-level `constBit b` agrees with `constantBit b` (`arith.constant` i1). -/
theorem agree_constBit (b : Bool) :
    DialectDenote.denote (d := catCryptDialect) (.constBit b)
      = DialectDenote.denote (d := mlirArithDialect) (.constantBit b) := rfl

end Agreement

/-! ## 4. The op-correspondence and a denotation-preservation SKETCH

The agreement lemmas above are the per-op crux. To package the full pass we
record the op correspondence `catToArith` (the semantic-level counterpart of
`CatCryptOp.toArithOpCode`) and STATE the `Com → Com` denotation-preservation
theorem, mirroring `CryptoToJasminComCorrect.cryptoDialectToJasminCom_denote_eq`.

Only the arith fragment of `CatCryptOp` is in the domain of `catToArith`; the
algebraic-datatype / memref / extCall ops are out of scope for an arith pass
(they have no `arith.*` target), so the translation is partial (`Option`),
exactly like the jasmin front. The general preservation theorem is stated as a
prose sketch and not proved; the agreement lemmas of §3 are the inputs that
make its `.var` case discharge. -/

/-- Semantic-level op correspondence: the arith fragment of `CatCryptOp`,
    each mapped to the `MlirArithOp` whose denotation §3 proves equal. Returns
    `none` on the non-arith ops (pair/sum/memref/extCall/constUnit), matching
    `toArithOpCode`'s `catcrypt.unknown` fallback. -/
def catToArith : CatCryptOp → Option MlirArithOp
  | .constBit b => some (.constantBit b)
  | .xor => some .xori1
  | .and => some .andi1
  | .or => some .ori1
  | .not => some .xnori1
  | .eqBit => some .cmpi1
  | .bvConst w v => some (.constant w v)
  | .bvXor w => some (.xori w)
  | .bvAnd w => some (.andi w)
  | .bvOr w => some (.ori w)
  | .bvNot w => some (.xoriAllOnes w)
  | .bvAdd w => some (.addi w)
  | .bvSub w => some (.subi w)
  | .bvMul w => some (.muli w)
  | .bvEq w => some (.cmpi w)
  | .bvShiftL w k => some (.shli w k)
  | .bvShiftR w k => some (.shrui w k)
  | .ite t => some (.select t)
  | .bitToSword n => some (.extsi n)
  | .constUnit | .mkPair _ _ | .fst _ _ | .snd _ _ | .inl _ _ | .inr _ _
  | .memrefZero _ | .memrefSet _ _ | .memrefGet _ _
  | .memrefSetDyn _ | .memrefGetDyn _ | .memrefGetDyn128 _ | .extCall _ _ _
  | .memrefWSetDyn _ _ | .memrefWGetDyn _ _
  | .bvAdd64 _ | .bvAdc _
  | .bvRor _ _ | .bvRol _ _ | .bvShiftRA _ _ | .andn _
  | .bvShiftLV _ | .bvShiftRV _
  | .bvMulHi _ | .bvAddCarryLo _ | .bvAddCarryHi _
  | .vsimd _ | .vpshufdC _ | .vaeskeygenC _ | .vpsrldqC _ | .vpslldqC _
  | .vconst128 _
  | .vsha256rnds2 | .vsha256msg1 | .vsha256msg2
  | .sampleBit | .sampleBv _ => none

/-- The semantic op-correspondence `catToArith` preserves signatures: when it
    succeeds, source and target have the same argument types and return type.
    (Definitional — every successful case has matching `sig`/`ret` by
    construction.) -/
theorem catToArith_sig (op : CatCryptOp) (op' : MlirArithOp)
    (h : catToArith op = some op') :
    DialectSignature.sig (d := catCryptDialect) op
      = DialectSignature.sig (d := mlirArithDialect) op'
    ∧ DialectSignature.ret (d := catCryptDialect) op
      = DialectSignature.ret (d := mlirArithDialect) op' := by
  cases op <;>
    simp only [catToArith, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨rfl, rfl⟩

/-- **Master per-op agreement.** Whenever `catToArith` succeeds with `op'`,
    the two dialects denote `op` and `op'` to the same function. This is the
    uniform statement of §3, discharged by case analysis (each case `rfl`). It
    is the single hypothesis a full `Com→Com` preservation proof consumes.

    The dependent rewrite is along `catToArith_sig`, transporting the
    `mlirArithDialect` denotation back to the source op's argument/return
    types. -/
theorem catToArith_denote (op : CatCryptOp) (op' : MlirArithOp)
    (h : catToArith op = some op') :
    HEq (DialectDenote.denote (d := catCryptDialect) op)
        (DialectDenote.denote (d := mlirArithDialect) op') := by
  cases op <;>
    simp only [catToArith, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact HEq.rfl

/-! ### Translation + preservation theorem (SKETCH, stated not proven)

A denotation-preserving `Com catCryptDialect → Com mlirArithDialect`
translation would: (1) translate each `Expr` via `catToArith` on its op
(failing — `Option` — on a non-arith op), reusing the *identical*
`Ctxt`/`Var`/`HVector` machinery since both dialects share `Ty = CryptoTy`;
(2) thread that through `Com.var`/`Com.ret`. Because the types coincide
(`mapCtx`/`mapTy` are the identity here, unlike the jasmin case), the
transport `transport` collapses to the identity and the preservation
statement is `(translate c).denote V = c.denote V`.

The structure mirrors `cryptoDialectToJasminCom_denote_eq`: the `.ret` case is a
variable-lookup identity; the `.var` case combines `catToArith_denote` for the
bound expression with the induction hypothesis for the body. It is DEFERRED (see
the closing note) — the §3 agreement lemmas (equivalently `catToArith_denote`)
are exactly the per-op input that the `.var` case needs. -/

/-! ### 5. Variable / argument transport between the two dialects

Both dialects share `Ty = CryptoTy`, so `Ctxt` and `Ctxt.Valuation` are
*literally the same* types on either side (they reduce to `List CryptoTy` and
`HVector (fun t => ⟦t⟧) Γ`, mentioning the dialect only through the shared
`TyDenote CryptoTy` instance). The one piece that is *not* definitionally shared
is `Ctxt.Var`: it is an inductive **indexed by the `Dialect` value**, so
`Var catCryptDialect Γ t` and `Var mlirArithDialect Γ t` are distinct types even
though their constructors mention only `d.Ty`. We bridge them with a structural
transport `varCM`, which lookup respects (`varCM_lookup`). The argument
`HVector` is bridged pointwise by `argsCM`, which `lookupArgs` respects
(`argsCM_lookup`). These collapse the only nontrivial transport in the pass. -/

/-- Transport a De Bruijn variable from the `catCryptDialect` indexing to the
    `mlirArithDialect` one. Structural identity (`here ↦ here`, `there ↦ there`);
    needed only because `Ctxt.Var` is indexed by the whole `Dialect` value. -/
def varCM {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    Ctxt.Var (d := catCryptDialect) Γ t → Ctxt.Var (d := mlirArithDialect) Γ t
  | .here => .here
  | .there v => .there (varCM v)

/-- Looking up a transported variable in a (shared) valuation gives the same
    value as looking up the original. By induction on the variable. -/
theorem varCM_lookup {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (v : Ctxt.Var (d := catCryptDialect) Γ t) (V : Ctxt.Valuation Γ) :
    (varCM v).lookup V = v.lookup V := by
  induction v with
  | here => cases V; rfl
  | there v ih => cases V; exact ih _

/-- Transport an `HVector` of `catCryptDialect` variables to one of
    `mlirArithDialect` variables over the same index list, pointwise via
    `varCM`. -/
def argsCM {Γ : Ctxt catCryptDialect} :
    {tys : List CryptoTy} →
    HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys →
    HVector (fun ty => Ctxt.Var (d := mlirArithDialect) Γ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (varCM v) (argsCM rest)

/-- Resolving a transported argument vector against a valuation gives the same
    resolved `HVector` of values as the original. By induction on the list /
    vector, using `varCM_lookup` per entry. -/
theorem argsCM_lookup {Γ : Ctxt catCryptDialect} :
    {tys : List CryptoTy} →
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tys) →
    (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (d := mlirArithDialect) (argsCM args) V
      = Expr.lookupArgs (d := catCryptDialect) args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((varCM v).lookup V)
        (Expr.lookupArgs (d := mlirArithDialect) (argsCM rest) V) = _
      rw [varCM_lookup, argsCM_lookup rest V]
      rfl

/-- Heterogeneous congruence for the two op denotations applied to transported
    arguments. Stated fully generically over the (free) argument-type lists
    `s`/`s'` and return types `r`/`r'`, so the type equalities `hty`/`hr` are
    `cases`-eliminable: once substituted, the function HEq `hf` and the
    `argsCM_lookup` agreement of the resolved arguments collapse the goal to a
    plain `congrArg`. This is the single dependent-transport step in the pass; it
    is the analogue of the `cast`/`HEq`/`eq_of_heq` discharge in
    `cryptoDialectToJasminCom_denote_eq`, minus the `mapTy` threading. -/
theorem denote_cong {Γ : Ctxt catCryptDialect}
    {s s' : List CryptoTy} {r r' : CryptoTy}
    (f : HVector (fun t => ⟦t⟧) s → ⟦r⟧)
    (g : HVector (fun t => ⟦t⟧) s' → ⟦r'⟧)
    (hty : s = s') (hr : r = r') (hf : HEq f g)
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) s)
    (V : Ctxt.Valuation Γ) :
    HEq (g (Expr.lookupArgs (d := mlirArithDialect) (hty ▸ argsCM args) V))
        (f (Expr.lookupArgs (d := catCryptDialect) args V)) := by
  cases hty
  cases hr
  cases hf
  exact heq_of_eq (congrArg f (argsCM_lookup args V))

/-! ### 6. Constructive `Com → Com` translation -/

/-- Translate a single `catCryptDialect` expression to a `mlirArithDialect`
    expression at the **same** context and return type. Looks the op up in
    `catToArith`; on a non-arith op returns `none`. On success it rebuilds the
    `Expr`, transporting the argument `HVector` (pointwise via `argsCM`, then
    along the arg-type-list equality) and the return-type witness along the
    signature-preservation fact `catToArith_sig`. -/
def translateExpr {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) : Option (Expr mlirArithDialect Γ t) :=
  match h : catToArith e.op with
  | none => none
  | some op' =>
      let hsig := catToArith_sig e.op op' h
      some { op := op'
             retTy_eq := hsig.2 ▸ e.retTy_eq
             args := hsig.1 ▸ argsCM e.args }

/-- Translate a `catCryptDialect` program to a `mlirArithDialect` program at the
    same context and return type. `.ret v ↦ .ret (varCM v)`. `.var e body ↦
    .var e' body'` once both `translateExpr e` and the recursive `translate body`
    succeed; `none` if any bound op is non-arith. -/
def translate : {Γ : Ctxt catCryptDialect} → {t : CryptoTy} →
    Com catCryptDialect Γ t → Option (Com mlirArithDialect Γ t)
  | _, _, .ret v => some (.ret (varCM v))
  | _, _, .var e body =>
      match translateExpr e with
      | none => none
      | some e' =>
          match translate body with
          | none => none
          | some body' => some (.var e' body')

/-! ### 7. The denotation-preservation theorem

`translate` is denotation-preserving. The `.ret` case is a variable-lookup
identity (`Com.denote` of a return is `v.lookup V`; `varCM_lookup` closes it).
The `.var` case combines the per-expression agreement (the bound `Expr`s denote
equally, via `catToArith_denote` + `argsCM_lookup`) with the induction
hypothesis on the body. This mirrors
`CryptoToJasminComCorrect.cryptoDialectToJasminCom_denote_eq`, but is strictly easier:
there is no `mapTy`/`mapCtx`, so the valuation transport is the identity. -/

/-- Per-expression agreement: a translated expression denotes to the same value
    as its source on the same valuation. The transported `HVector` resolves to
    the same values (`argsCM_lookup`) and the op denotations agree by
    `catToArith_denote`; the return-type / arg-type-list casts are discharged by
    substituting the signature equalities. -/
theorem translateExpr_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t) (e' : Expr mlirArithDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : translateExpr e = some e') :
    e'.denote V = e.denote V := by
  -- Destruct `e` so its `op`, `retTy_eq`, `args` fields are exposed.
  obtain ⟨op, hret, args⟩ := e
  -- It suffices to prove the heterogeneous equality.
  apply eq_of_heq
  -- Reduce `translateExpr`; the op must be arith (`some op'`).
  simp only [translateExpr] at h
  split at h
  · exact absurd h (by simp)
  · next op' hop =>
      simp only [Option.some.injEq] at h
      -- Per-op agreement (HEq of the denotations) + signature preservation.
      have hden := catToArith_denote op op' hop
      obtain ⟨hsigArg, hsigRet⟩ := catToArith_sig op op' hop
      subst h
      -- Peel the two `retTy_eq ▸` casts in `Expr.denote` via `eqRec_heq`, leaving
      -- the op-denotations applied to the (transported) looked-up args.
      simp only [Expr.denote]
      refine HEq.trans (eqRec_heq _ _) (HEq.trans ?_ (eqRec_heq _ _).symm)
      -- The remaining heterogeneous congruence is exactly `denote_cong`.
      exact denote_cong _ _ hsigArg hsigRet hden args V

/-- **Translation preserves denotation.** Whenever `translate c = some c'`, the
    two programs denote to the same value on every valuation. -/
theorem translate_denote_eq {Γ : Ctxt catCryptDialect} {t : CryptoTy} :
    (c : Com catCryptDialect Γ t) → (c' : Com mlirArithDialect Γ t) →
    (V : Ctxt.Valuation Γ) → translate c = some c' → c'.denote V = c.denote V
  | .ret v, c', V, h => by
      -- `.ret v ↦ .ret (varCM v)`; both denote to a lookup, equal by `varCM_lookup`.
      simp only [translate, Option.some.injEq] at h
      subst h
      show (varCM v).lookup V = v.lookup V
      exact varCM_lookup v V
  | .var e body, c', V, h => by
      -- `.var e body ↦ .var e' body'` once both sub-translations succeed.
      simp only [translate] at h
      split at h
      · exact absurd h (by simp)
      · next e' he =>
          split at h
          · exact absurd h (by simp)
          · next body' hbody =>
              simp only [Option.some.injEq] at h
              subst h
              -- Step both denotations through the `.var` clause of `Com.denote`.
              show body'.denote ((V.extend (e'.denote V)))
                = body.denote (V.extend (e.denote V))
              -- The bound expressions agree, so the extended valuations match;
              -- then apply the body IH.
              rw [translateExpr_denote_eq e e' V he]
              exact translate_denote_eq body body' _ hbody

end CatCrypt.Crypto.SecureCompilation.VIR.MlirArithDialect
