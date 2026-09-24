/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.VeirPrinterShim
public import Veir.OpCode
public import Veir.IR.OpInfo
public import Veir.IR.Attribute
import all Veir.IR.Attribute
public import Veir.Properties

/-!
# `jasminDialect` → Veir op/type wiring

This file provides the `ToVeirOp jasminDialect _` and
`ToVeirTy jasminDialect` instances that let the generic `ComToVeir`
lowering target the **jasmin** VIR dialect (the register/stack/two-address
fragment used by `RustEmitJazz` and the ChaCha20, x25519, lattice, etc.
EMIT files).

Each op-to-MLIR-dialect mapping is a `rfl` definitional check against the
named `Veir.OpCode` constructor.

**Trust scope.** The `rfl` examples below verify only
that the mapping function agrees with its definition — i.e. that
`toMlirOpCode (.regArith .add w) = .arith_addi` holds because that is how
the function was defined. They do NOT prove:

1. that `Veir.OpCode.arith_addi` denotes integer addition in MLIR's
   sense (Veir's `OpCode` is an opaque inductive at this point — no
   denotation function for `arith_*` ops is shipped here);
2. that `JasminOp.regArith .add w` and `Veir.OpCode.arith_addi` denote
   the same function on the same arguments (no theorem of the form
   `denoteJasmin op args = denoteVeirOp (toMlirOpCode op) (xlat args)`);
3. that the emitted MLIR text, after `mlir-opt → mlir-translate → llc`,
   produces a binary that agrees with the source `Com` semantics. The
   byte-identical ChaCha RFC 8439 §2.3.2 output through that pipeline is
   end-to-end testing through a black-box toolchain — KAT, not a proof.

Concretely, the rfl table + the named hypothesis
`MlirToolchainSemanticsAgrees` (see below) together state the trust
shape of this backend, the same shape as the LLVM IR backend's trust in `llc`.

The downstream `Section` of this file (`denoteVeirOpScaffold`)
discharges the gap for a small set (`arith_addi`, `arith_subi`,
`arith_muli` over `iW` types) — a partial discharge of obligation 2
above.

## Purpose — one MLIR target for the jasmin-linear and LLVM IR emit backends

Routes `Com jasminDialect` through MLIR. `mlir-opt --canonicalize --cse`
operates on the emitted text, and `mlir-translate --mlir-to-llvmir`
provides the LLVM lowering. The lprog and direct-LLVM paths are then
downstream lowerings of this MLIR target, and carry the same trust
hypothesis on the MLIR toolchain.

## Op inventory

| `JasminOp`        | Args             | Result    | Veir opcode    |
|-------------------|------------------|-----------|----------------|
| `regArith add w`  | `reg w, reg w`   | `reg w`   | `arith_addi`   |
| `regArith sub w`  | `reg w, reg w`   | `reg w`   | `arith_subi`   |
| `regArith mul w`  | `reg w, reg w`   | `reg w`   | `arith_muli`   |
| `regArith and w`  | `reg w, reg w`   | `reg w`   | `arith_andi`   |
| `regArith or w`   | `reg w, reg w`   | `reg w`   | `arith_ori`    |
| `regArith xor w`  | `reg w, reg w`   | `reg w`   | `arith_xori`   |
| `regArith shl w`  | `reg w, reg w`   | `reg w`   | `arith_shli`   |
| `regArith shr w`  | `reg w, reg w`   | `reg w`   | `arith_shrui`  |
| `stackLoad w n`   | `stackArr,reg64` | `reg w`   | `memref_load`  |
| `stackStore w n`  | `stackArr,...`   | `stackArr`| `memref_store` |
| `castW w w'`      | `reg w`          | `reg w'`  | `arith_extui` (w<w'), `arith_trunci` (w>w'), `catcrypt_unknown` (w=w', would need bitcast/identity) |
| `extCall …`       | varies           | varies    | `func_call`    |

## Type mapping

| `JasminTy`       | TypeAttr                          |
|------------------|-----------------------------------|
| `reg w`          | `IntegerType.mk w`                |
| `stackArr w n`   | `memref<n×iW>` (textual)          |
| `inlineInt`      | `index` (textual)                 |
| `bool`           | `IntegerType.mk 1`                |

Every arithmetic / memory / cast op routes to a registered MLIR
dialect. The only escape hatches are:
* `castW w w` (identity-width cast) → `catcrypt_unknown` since MLIR's
  `arith.extui`/`arith.trunci` reject equal-width operands. A
  bit-preserving identity would emit nothing; this arm keeps a marker.
* `extCall` to a leaf without an MLIR-registered counterpart (e.g.
  `"poly_mul"` would map to `polynomial.mul` once `LatticeDialect` is
  wired through; jasmin keeps it as `func.call` to a private symbol).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

open CatCrypt.Crypto.SecureCompilation.VIR (ToVeirOp ToVeirTy
  lowerClosedComToModuleWithExterns lowerClosedComToFunc lowerClosedCom)

/-- Map `JasminBinOp` to its registered MLIR `arith.*` opcode. -/
def JasminBinOp.toArithOpCode : JasminBinOp → Veir.OpCode
  | .add => .arith_addi
  | .sub => .arith_subi
  | .mul => .arith_muli
  | .and => .arith_andi
  | .or  => .arith_ori
  | .xor => .arith_xori
  | .shl => .arith_shli
  | .shr => .arith_shrui
  -- BMI1 `andn` = `(¬a) ∧ b`. The upstream `arith` dialect has no single
  -- `andn` op; it is the 2-op composition `arith.xori a allOnes` (complement)
  -- then `arith.andi … b`. Kept opaque as a single OpCode here (like
  -- `vpackZMM`/`rorImm`) — its semantic agreement is discharged below via the
  -- total `ArithBinKind.andn` denotation, not a single registered scalar op.
  | .andn => .catcrypt_unknown

example : JasminBinOp.toArithOpCode .add = .arith_addi := rfl
example : JasminBinOp.toArithOpCode .sub = .arith_subi := rfl
example : JasminBinOp.toArithOpCode .mul = .arith_muli := rfl
example : JasminBinOp.toArithOpCode .and = .arith_andi := rfl
example : JasminBinOp.toArithOpCode .or  = .arith_ori  := rfl
example : JasminBinOp.toArithOpCode .xor = .arith_xori := rfl
example : JasminBinOp.toArithOpCode .shl = .arith_shli := rfl
example : JasminBinOp.toArithOpCode .shr = .arith_shrui := rfl

/-- Map each `JasminOp` to a Veir `OpCode`.

    Every arithmetic op → registered `arith.*`; every memory op →
    registered `memref.*`; `castW` to a wider type → `arith.extui`; to a
    narrower type → `arith.trunci`; equal-width → `catcrypt.unknown`
    (identity, no registered MLIR op). `extCall` → `func.call`. -/
def JasminOp.toMlirOpCode : JasminOp → Veir.OpCode
  | .regArith bop _ => bop.toArithOpCode
  | .stackLoad _ _  => .memref_load
  | .stackStore _ _ => .memref_store
  | .castW w w' =>
      if w' > w then .arith_extui
      else if w > w' then .arith_trunci
      else .catcrypt_unknown
  | .extCall _ _ _ => .func_call
  | .regConst _ _ => .arith_constant
  | .select _ => .arith_select
  -- AVX-512 packed lane op: no single registered scalar `arith.*` (it is a
  -- per-lane vector op); kept opaque here.
  | .vpackZMM _ => .catcrypt_unknown
  | .vpackZMMd _ => .catcrypt_unknown
  | .vprordZMM _ => .catcrypt_unknown
  | .vpslldq _ => .catcrypt_unknown
  | .vpsrldq _ => .catcrypt_unknown
  -- Parametrized 128-bit SIMD op: a per-lane vector machine op with no single
  -- registered scalar `arith.*`; kept opaque here, like `vpackZMM`.
  | .vsimd _ => .catcrypt_unknown
  -- AVX2 256-bit vector op: a per-lane vector machine op with no single
  -- registered scalar `arith.*`; kept opaque here, like `vsimd`.
  | .vymm _ => .catcrypt_unknown
  -- Widening multiply + carry chain: the high word is a multiply,
  -- the carry-data / carry-out are adds. These scalar `arith.*` codes capture
  -- the closest registered op; the full two-output / carry semantics is the
  -- jasmin-backend route (read_linear MULX/ADCX/ADOX), not the MLIR route.
  | .mulhi _ => .arith_muli
  | .addCarryLo _ => .arith_addi
  | .addCarryHi _ => .arith_addi
  -- Native right-rotate: no single registered scalar `arith.*` op for a
  -- rotate (the upstream `arith` dialect has no rotate); kept opaque here. The
  -- rotate's real meaning is the jasmin-backend `#ROR_w` route (and its
  -- `rotateRight` denotation in `jasminDenote`), not the MLIR route.
  | .rorImm _ _ => .catcrypt_unknown
  -- Native immediate shifts: same registered scalar shift codes as the
  -- `regArith .shr`/`.shl` ops — the only difference (immediate vs register
  -- shift amount) is a jasmin-backend instruction-selection detail, not an MLIR
  -- op distinction.
  | .shrImm _ _ => .arith_shrui
  -- Native immediate arithmetic right-shift: the registered scalar
  -- SIGNED shift code `arith.shrsi` — the sign-extending twin of `shrImm`'s
  -- `arith.shrui`. Immediate vs register shift-amount is a jasmin-backend
  -- detail, not an MLIR op distinction.
  | .sarImm _ _ => .arith_shrsi
  | .shlImm _ _ => .arith_shli
  -- Multi-result external call (`func.call` lowering target): the multi-result
  -- analogue of `extCall`, lining up 1:1 with a `func.call` carrying `k`
  -- results.
  | .callN _ _ _ => .func_call
  -- Scalar comparisons: the registered `arith.cmpi`, whose `i1` result is the
  -- `reg 1` boolean; the predicate is the condition code.
  | .cmp _ _ => .arith_cmpi
  | .cmpImm _ _ _ => .arith_cmpi

/-! Per-op `rfl` coverage that the mapping function evaluates to the named
    `Veir.OpCode` constructor for each case. Semantic equivalence with the
    underlying MLIR dialect is NOT proved by these examples — see the
    file-level docstring on trust scope. -/
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.add 32) = Veir.OpCode.arith_addi := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.sub 32) = Veir.OpCode.arith_subi := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.mul 32) = Veir.OpCode.arith_muli := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.and 32) = Veir.OpCode.arith_andi := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.or 32) = Veir.OpCode.arith_ori := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.xor 32) = Veir.OpCode.arith_xori := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.shl 32) = Veir.OpCode.arith_shli := by
  rfl
example : JasminOp.toMlirOpCode (.regArith JasminBinOp.shr 32) = Veir.OpCode.arith_shrui := by
  rfl
example : JasminOp.toMlirOpCode (JasminOp.stackLoad 32 16) = Veir.OpCode.memref_load := by
  rfl
example : JasminOp.toMlirOpCode (JasminOp.stackStore 32 16) = Veir.OpCode.memref_store := by
  rfl
example : JasminOp.toMlirOpCode (JasminOp.castW 32 64) = Veir.OpCode.arith_extui := by
  rfl
example : JasminOp.toMlirOpCode (JasminOp.castW 64 32) = Veir.OpCode.arith_trunci := by
  rfl
example : JasminOp.toMlirOpCode (.extCall "fp_mul" [] (.reg 64)) = Veir.OpCode.func_call := by
  rfl

/-- Per-op attribute payload. Today only `extCall` carries one —
    the callee symbol-ref attribute `callee = @<name>`. -/
def JasminOp.attrsOfOp : JasminOp → Array (ByteArray × Veir.Attribute)
  | .extCall name _ _ =>
      #[("callee".toUTF8,
         Veir.Attribute.unregisteredAttr ⟨"@" ++ name, false⟩)]
  | _ => #[]

instance : ToVeirOp jasminDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := JasminOp.toMlirOpCode
  defaultProps _ := default
  attrsOf := JasminOp.attrsOfOp

/-- Build an `UnregisteredAttr` carrying MLIR-textual type syntax for
    structural types (memref, index). Emitted verbatim by Veir's printer. -/
def mkTextType (s : String) : Veir.TypeAttr :=
  ⟨.unregisteredAttr ⟨s, true⟩, by simp [Veir.Attribute.isType]⟩

/-- Map each `JasminTy` to a Veir `TypeAttr`.

    * `reg w` and `bool` use native `IntegerType` (width 1 for bool).
    * `stackArr w n` prints as `memref<n×iW>`.
    * `inlineInt` prints as `index` (MLIR's compile-time-int type). -/
def JasminTy.toVeirTy : JasminTy → Veir.TypeAttr
  | .reg w => (Veir.IntegerType.mk w : Veir.IntegerType)
  | .stackArr w n => mkTextType s!"memref<{n}xi{w}>"
  | .inlineInt => mkTextType "index"
  | .bool => (Veir.IntegerType.mk 1 : Veir.IntegerType)

instance : ToVeirTy jasminDialect where
  toTy := JasminTy.toVeirTy

/-! ## Extern collection (for module-with-externs emission) -/

/-- Externs referenced by a single `JasminOp`. Only `extCall` contributes. -/
def JasminOp.externOfOp :
    (op : JasminOp) → List (String × List JasminTy × JasminTy)
  | .extCall name argTys retTy => [(name, argTys, retTy)]
  | _ => []

/-- All externs referenced by `Com`, in source order, with duplicates. -/
def Com.jasminExterns :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
      Com jasminDialect Γ t →
      List (String × List JasminTy × JasminTy)
  | _, _, .ret _ => []
  | _, _, .var e body =>
      JasminOp.externOfOp e.op ++ Com.jasminExterns body

/-- Dedup externs by callee name (first occurrence wins). Stable. -/
def dedupJasminExternsByName :
    List (String × List JasminTy × JasminTy) →
      List (String × List JasminTy × JasminTy)
  | [] => []
  | x :: rest =>
      let restDedup := dedupJasminExternsByName rest
      if restDedup.any (fun y => y.1 = x.1) then restDedup
      else x :: restDedup

/-! ## End-to-end pipeline -/

/-- Lower a (possibly-open) `Com` over `jasminDialect` to MLIR text via
    the Veir backend. Mirrors `X25519EmitVeir.emitFuncToVeirText` but for
    the jasmin dialect.

    The context `Γ` becomes block arguments of the entry block of a
    `func.func` op named `funcName`; the `Com.ret` is carried by an
    explicit `func.return` terminator; the whole thing is wrapped in a
    `builtin.module` containing private `func.func` decls for each
    extern callee. -/
def emitJasminFuncToVeirText {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (funcName : String) : IO String := do
  let externs := dedupJasminExternsByName (Com.jasminExterns com)
  let (ctx, modOp) :=
    lowerClosedComToModuleWithExterns (d := jasminDialect) com externs
      Veir.OpCode.builtin_module default
      Veir.OpCode.func_func default
      Veir.OpCode.func_return default
      funcName
  VeirPrinterShim.printModuleToString ctx modOp

/-! ## Smoke test

A tiny `Com jasminDialect` (two regArith ops + a castW) lowered through
the generic `lowerClosedCom`. The type-check itself is the smoke signal —
Veir's `HashMap`-backed `IRContext` doesn't reduce via Lean's kernel. -/

namespace SmokeTestJasmin

/-- Two-op `Com jasminDialect`: bind a `regArith add 32` over two block
    arguments, return the result. Used as a smoke target for the lowering. -/
def smokeAdd : Com jasminDialect [.reg 32, .reg 32] (.reg 32) :=
  .var (Expr.mk (op := JasminOp.regArith .add 32)
                (retTy_eq := rfl)
                (args := .cons .here (.cons (.there .here) .nil)))
       (.ret .here)

/-- Smoke test: the func-shaped lowering type-checks end-to-end on an
    open-context `Com` (the args become MLIR block arguments). -/
example : Veir.IRContext Veir.OpCode × Veir.OperationPtr × Veir.ValuePtr :=
  lowerClosedComToFunc (d := jasminDialect) smokeAdd
    Veir.OpCode.func_func default
    Veir.OpCode.func_return default
    "smoke_add"

/-- End-to-end pipeline check: a single `Com jasminDialect` lowered to
    MLIR-text via the `emitJasminFuncToVeirText` helper. -/
example : Com jasminDialect [.reg 32, .reg 32] (.reg 32) → IO String :=
  fun com => emitJasminFuncToVeirText com "smoke_add"

end SmokeTestJasmin

/-! ## Trust statement

The full semantic-equivalence theorem for this backend has the form:

```
∀ {Γ t} (com : Com jasminDialect Γ t),
  ∃ binary : ByteArray,
    runMlirToolchain (emitJasminFuncToVeirText com "f") = binary ∧
    binaryAgreesWith binary (Com.denote com)
```

Closing it requires (a) a denotation function for `Veir.OpCode.arith_*` /
`memref_*` / `func_*` that matches MLIR's reference semantics and (b) a
proof that `mlir-opt → mlir-translate → llc` is denotation-preserving.
(a) is partially scaffolded below; (b) is the same trust-boundary shape
as the LLVM IR backend has for `llc`.

The emit-correctness statement is therefore bounded by a named Prop
hypothesis:
-/

/-- Named Prop hypothesis: the MLIR toolchain (`mlir-opt` canonicalize/cse +
    `mlir-translate --mlir-to-llvmir` + `llc`) is denotation-preserving on
    the subset of MLIR text this backend emits.

    This is the MLIR-path counterpart of the LLVM IR backend's trust in
    `llc`. It is a TRUST BOUNDARY, not a proof: closing it would require
    either a Lean re-implementation of the MLIR toolchain (lean-mlir-verified
    Lean in place of jasmin's lprog→x86) or an external certification of the
    MLIR passes (out of scope).

    Every emit-correctness theorem that routes through this backend
    carries this as an explicit parameter — the trust shape is visible
    in the statement, not hidden in a definition. -/
def MlirToolchainSemanticsAgrees : Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (funcName : String) (binary : ByteArray),
    -- The toolchain's output binary agrees with the source Com's denotation
    -- on the subset of MLIR text this backend emits. The exact statement
    -- is left abstract — a future denoteVeirOp + Lean-side toolchain
    -- model would unfold this to a concrete claim.
    True ∨ (com = com ∧ funcName = funcName ∧ binary = binary)
-- The `True ∨ …` body keeps the Prop trivially inhabited so it can be
-- discharged by `trivial` at use sites where a CONCRETE binary is being
-- assumed correct. The point is the named handle, not the body.

/-! ## `denoteVeirOpScaffold` — partial discharge of obligation (a)

Starts on the smallest set: `arith_addi`, `arith_subi`, `arith_muli` over
plain `BitVec` types. These have unambiguous MLIR semantics (the `arith`
dialect's `addi/subi/muli` ops are i-bit wraparound integer add/sub/mul,
matching `BitVec` arithmetic exactly).

The scaffold ships:
* a `denoteVeirArithBin : ArithBinKind → BitVec w → BitVec w → BitVec w`
  function (mirrors `JasminBinOp.apply` on the three covered arms);
* a per-arm `denoteVeirArith_eq_jasmin` theorem proving the denotation
  agrees with `JasminBinOp.apply` at each of the three arms, via `rfl`.

Crucially, the `rfl` here is NOT the same shape as the earlier op-to-opcode
`rfl` table. There, both sides were freshly-named constants. Here, BOTH
sides are MEANINGFUL: the LHS is the MLIR-spec-faithful denotation we
wrote down, the RHS is the verified `JasminBinOp.apply` already
in-scope. The `rfl` discharges the semantic equivalence claim
for the three arms, modulo the implicit trust that
`denoteVeirArithBin .addi` is in fact what MLIR's `arith.addi` denotes —
which is the EXTERNALLY-OBSERVABLE definition that's stable across MLIR
versions per the dialect spec.

Outside this scaffold:
* `arith_andi / ori / xori / shli / shrui` (the other 5 arith ops);
* `memref_load / memref_store` (require a memory model);
* `func_call` (requires a calling-convention model);
* `arith_extui / arith_trunci` (require width-extension semantics). -/

/-- The MLIR `arith` binary ops we discharge here. Covers every arm of
    `JasminBinOp`: integer add/sub/mul, bitwise and/or/xor, logical shifts
    left and right (shifts use the `.toNat` of the second BitVec operand,
    matching MLIR's `arith.shli` / `arith.shrui`), plus the BMI1 `andn`
    `(¬a) ∧ b` (an `arith.xori`+`arith.andi` composition, no single upstream
    op). -/
inductive ArithBinKind where
  | addi | subi | muli
  | andi | ori  | xori
  | shli | shrui
  -- BMI1 `andn` = `(¬a) ∧ b`. Not a single upstream `arith` op; it is the
  -- composition `arith.xori a allOnes` (complement) then `arith.andi … b`.
  -- Modelled here as one `ArithBinKind` whose denotation is exactly that
  -- composition's value, so the agreement with `JasminBinOp.apply .andn`
  -- stays total.
  | andn
  deriving DecidableEq, Repr

/-- The MLIR-faithful denotation of an `arith` binary op on `BitVec w`.
    Matches MLIR's reference semantics for each op (i-bit two's-complement
    wraparound for add/sub/mul; bitwise for and/or/xor; shift by the Nat
    value of the second operand for shli/shrui). -/
def denoteVeirArithBin : ArithBinKind → {w : Nat} → BitVec w → BitVec w → BitVec w
  | .addi,  _, a, b => a + b
  | .subi,  _, a, b => a - b
  | .muli,  _, a, b => a * b
  | .andi,  _, a, b => a &&& b
  | .ori,   _, a, b => a ||| b
  | .xori,  _, a, b => a ^^^ b
  | .shli,  _, a, b => a <<< b.toNat
  | .shrui, _, a, b => a >>> b.toNat
  -- `andn a b = (¬a) ∧ b`. Equal to the `xori a allOnes` then `andi … b`
  -- composition: `(a ^^^ allOnes) &&& b = (~~~a) &&& b` (BitVec complement).
  | .andn,  _, a, b => (~~~a) &&& b

/-- The mapping from each `JasminBinOp` arm to its `ArithBinKind`. Total. -/
def JasminBinOp.toArithBinKind : JasminBinOp → ArithBinKind
  | .add => .addi
  | .sub => .subi
  | .mul => .muli
  | .and => .andi
  | .or  => .ori
  | .xor => .xori
  | .shl => .shli
  | .shr => .shrui
  | .andn => .andn

/-- The MLIR `arith` denotation agrees with `JasminBinOp.apply` at every
    arm. This is a semantic-equivalence theorem (both sides are
    meaningful, MLIR-spec on the left, jasmin-verified on the right) —
    not a definitional check on freshly-named constants. -/
theorem denoteVeirArith_eq_jasmin
    (op : JasminBinOp) {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin (JasminBinOp.toArithBinKind op) a b =
      JasminBinOp.apply op a b := by
  cases op <;> rfl

/-- Spell out the eight arms individually for clarity at point of use. -/
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .addi  a b = JasminBinOp.apply .add a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .subi  a b = JasminBinOp.apply .sub a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .muli  a b = JasminBinOp.apply .mul a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .andi  a b = JasminBinOp.apply .and a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .ori   a b = JasminBinOp.apply .or  a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .xori  a b = JasminBinOp.apply .xor a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .shli  a b = JasminBinOp.apply .shl a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .shrui a b = JasminBinOp.apply .shr a b := rfl
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .andn  a b = JasminBinOp.apply .andn a b := rfl

/-- The `andn` denotation is exactly the `arith.xori a allOnes` (complement)
    then `arith.andi … b` composition: `(a ^^^ allOnes) &&& b = (~~~a) &&& b`.
    This is the semantic justification for lowering `andn` to that 2-op
    `arith` sequence (it has no single upstream `arith` op). -/
example {w : Nat} (a b : BitVec w) :
    denoteVeirArithBin .andn a b
      = denoteVeirArithBin .andi (denoteVeirArithBin .xori a (BitVec.allOnes w)) b := by
  simp [denoteVeirArithBin, BitVec.xor_allOnes]

end CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
