/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Veir.IR.Basic
import all Veir.IR.Attribute
public import CatCrypt.Crypto.SecureCompilation.VIR.ComToVeir_CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# `modArithDialect` and `fieldDialect` → VeIR's prime-ir forms

The lowering of our `modArithDialect` and `fieldDialect` to VeIR's `mod_arith`
and `field` dialects in prime-ir's form, with `!mod_arith.int<p : iW>`,
`!field.pf<p : iW>` and `!field.ef<…>` types.

Our types carry neither a storage width nor the tower constant of `Fp6`, so the
lowering takes an `AlgebraicPrintCtx` that supplies both. Side conditions,
checked over the whole program before lowering (`modArithModule`, `fieldModule`),
reject a program that disagrees with the context: a modulus that the width does
not hold, a Montgomery `rInv` that does not invert the radix `2 ^ W`, a bitcast
whose word width is not `W`, an `Fp6`/`Fp12` multiply whose `ξ₀` is not the
context's, and the reductions from a word, which have no VeIR operation.

Ops that are not one operation lower through `ToVeirOp.expand?`: copies and
tensor reinterprets are aliases, `montReduce` is `mod_arith.mont_reduce` of the
stored word and a zero high word, `mulHi` and the carry-chain adds are the
`arith` sequences of the `catCryptDialect` lowering, and `frobenius2 p` is
`field.powui` by `p`.

## Main definitions

* `AlgebraicPrintCtx`: the storage width of a modulus and the tower constant.
* `modArithToVeirOp`, `modArithToVeirTy`, `fieldToVeirOp`, `fieldToVeirTy`: the
  lowering under a print context.
* `modArithModule`, `fieldModule`: the checked `builtin.module` of a program.
* `moduleText`: the text `Veir.Printer.printModule` prints for a module whose
  operations have no successors, as a `String`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirAlgebraic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-! ## Print context and types -/

/-- The parameters prime-ir's algebraic types carry and ours do not: the storage
    width of a modulus, and the constant `ξ₀` of the tower
    `Fp6 = Fp2[v]/(v³ − (ξ₀ + u))` over a modulus. -/
structure AlgebraicPrintCtx where
  /-- The storage width `W` of the modulus `p`, printed as `: iW`. -/
  width : Nat → Nat
  /-- The tower constant `ξ₀` over the modulus `p`, when the program uses the tower. -/
  towerXi0 : Nat → Option Nat

/-- prime-ir's inferred storage width of a modulus: `bit_ceil(activeBits p)`. -/
def primeIrWidth (p : Nat) : Nat := Nat.nextPowerOfTwo (Nat.log2 p + 1)

/-- The print context with prime-ir's inferred widths and no tower. -/
def AlgebraicPrintCtx.inferred : AlgebraicPrintCtx where
  width := primeIrWidth
  towerXi0 := fun _ => none

/-- The integer type `iw`. -/
def intTy (w : Nat) : Veir.TypeAttr := (Veir.IntegerType.mk w : Veir.IntegerType)

/-- The integer attribute `v : iw`. -/
def intAttr (v : Nat) (w : Nat) : Veir.IntegerAttr := ⟨v, Veir.IntegerType.mk w⟩

/-- `!mod_arith.int<p : iw>`. -/
def modArithTy (p w : Nat) : Veir.TypeAttr :=
  ({ modulus := intAttr p w } : Veir.ModArithType)

/-- `tensor<n x τ>`. -/
def tensorTy (n : Nat) (τ : Veir.TypeAttr) : Veir.TypeAttr :=
  ⟨.rankedTensorType { shape := #[n], elementType := τ.val }, by simp [Veir.Attribute.isType]⟩

/-- `!field.pf<p : iw>`. -/
def primeFieldTy (p w : Nat) : Veir.TypeAttr :=
  ⟨.primeFieldType { modulus := intAttr p w }, by simp [Veir.Attribute.isType]⟩

/-- `!field.ef<2x!field.pf<p : iw>, (p - 1) : iw>`: `Fp2 = Fp[u]/(u² + 1)`. -/
def ext2Ty (p w : Nat) : Veir.TypeAttr :=
  ⟨.extensionFieldType
    { degree := 2, base := (primeFieldTy p w).val, nonResidue := .integerAttr (intAttr (p - 1) w) },
   by simp [Veir.Attribute.isType]⟩

/-- `!field.ef<3xFp2, dense<[ξ₀, 1]> : tensor<2xiw>>`: `Fp6 = Fp2[v]/(v³ − (ξ₀ + u))`. -/
def ext6Ty (p w ξ0 : Nat) : Veir.TypeAttr :=
  ⟨.extensionFieldType
    { degree := 3, base := (ext2Ty p w).val,
      nonResidue := .denseElementsAttr { value := s!"[{ξ0}, 1]", type := s!"tensor<2xi{w}>" } },
   by simp [Veir.Attribute.isType]⟩

/-- `!field.ef<2xFp6, v>` with `v = (0, 1, 0)` in `Fp6`: `Fp12 = Fp6[w]/(w² − v)`.
    The shape `tensor<3x2xiw>` of `v` follows the `Fp6`-over-`Fp2` nesting. -/
def ext12Ty (p w ξ0 : Nat) : Veir.TypeAttr :=
  ⟨.extensionFieldType
    { degree := 2, base := (ext6Ty p w ξ0).val,
      nonResidue := .denseElementsAttr
        { value := "[[0, 0], [1, 0], [0, 0]]", type := s!"tensor<3x2xi{w}>" } },
   by simp [Veir.Attribute.isType]⟩

/-! ## Side conditions -/

/-- Whether the width `w` holds the modulus `p` in prime-ir's sense: `p` is at least
    `2`, not a power of two, and below `2 ^ w`. -/
def modulusFits (p w : Nat) : Bool :=
  1 < p && (p &&& (p - 1)) != 0 && p < 2 ^ w

/-- Fail with `msg` unless `b`. -/
def require (b : Bool) (msg : String) : Except String Unit :=
  if b then .ok () else .error msg

/-- The check that the width of the print context holds the modulus `p`. -/
def AlgebraicPrintCtx.checkModulus (pc : AlgebraicPrintCtx) (p : Nat) : Except String Unit :=
  require (modulusFits p (pc.width p))
    s!"modulus {p} does not fit the storage width i{pc.width p} of the print context"

/-- The check that `rInv` is the inverse of the Montgomery radix `2 ^ W` mod `p`. -/
def AlgebraicPrintCtx.checkRInv (pc : AlgebraicPrintCtx) (p rInv : Nat) : Except String Unit :=
  require (rInv * 2 ^ pc.width p % p == 1 % p)
    s!"rInv = {rInv} is not the inverse of 2^{pc.width p} mod {p}"

/-- The check that the print context has a tower over `p`. -/
def AlgebraicPrintCtx.checkTower (pc : AlgebraicPrintCtx) (p : Nat) : Except String Unit :=
  require (pc.towerXi0 p).isSome s!"the print context has no tower over {p}"

/-- Check every type of the context and every op of the program, with the types
    of its operands and result. -/
def checkCom {d : Dialect.{0, 0}} [DialectSignature d]
    (checkOp : d.Op → Except String Unit) (checkTy : d.Ty → Except String Unit) :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Except String Unit
  | Γ, _, .ret _ => (Γ : List d.Ty).forM checkTy
  | _, _, .var e body => do
      checkOp e.op
      (DialectSignature.sig e.op).forM checkTy
      checkTy (DialectSignature.ret e.op)
      checkCom checkOp checkTy body

/-! ## `modArithDialect` -/

/-- The VeIR type of a `ModArithTy` under the print context. -/
def ModArithTy.toVeirTyIn (pc : AlgebraicPrintCtx) : ModArithTy → Veir.TypeAttr
  | .fp p => modArithTy p (pc.width p)
  | .fpVec p n => tensorTy n (modArithTy p (pc.width p))
  | .word w => intTy w
  | .carry => intTy 1

/-- The check of a `ModArithTy` against the print context. -/
def ModArithTy.checkIn (pc : AlgebraicPrintCtx) : ModArithTy → Except String Unit
  | .fp p => pc.checkModulus p
  | .fpVec p _ => pc.checkModulus p
  | .word w => require (0 < w) "zero-width word"
  | .carry => .ok ()

/-- The VeIR op-code of a `ModArithOp` printed as one operation. The ops that
    lower through an expansion, and the reductions from a word, which have no
    VeIR operation and are rejected by `ModArithOp.checkIn`, map to
    `catcrypt.unknown`. -/
def ModArithOp.toVeirOpCode : ModArithOp → Veir.OpCode
  | .modAdd _ => .mod_arith .add
  | .modSub _ => .mod_arith .sub
  | .modNeg _ => .mod_arith .negate
  | .modMul _ => .mod_arith .mul
  | .modConst _ _ => .mod_arith .constant
  | .byInverse _ => .mod_arith .inverse
  | .batchInverse _ _ => .mod_arith .inverse
  | .montMul _ _ => .mod_arith .mont_mul
  | .montInverse _ _ => .mod_arith .mont_inverse
  | .residueEncode _ _ => .mod_arith .bitcast
  | .residueDecode _ _ => .mod_arith .bitcast
  | _ => .catcrypt .unknown

/-- The properties of the operation of a `ModArithOp`: the value `c.val : iW` of
    `mod_arith.constant`, and the default properties otherwise. -/
def ModArithOp.propsIn (pc : AlgebraicPrintCtx) (o : ModArithOp) :
    Veir.propertiesOf (ModArithOp.toVeirOpCode o) :=
  match o with
  | .modConst p c =>
      ({ value := intAttr c.val (pc.width p) } : Veir.ModArithConstantProperties)
  | _ => default

/-- `a + b + cin` as `arith.extui` of `cin` and two `arith.addui_extended`; the
    data word is result 0 of step 2, the two carries result 1 of steps 1 and 2. -/
def addCarrySteps (w : Nat) : List (VeirExpandStep Veir.OpCode) :=
  [ { op := .arith .extui, props := default, operands := [.arg 2],
      results := [some (intTy w)] },
    { op := .arith .addui_extended, props := (), operands := [.arg 0, .arg 1],
      results := [some (intTy w), some (intTy 1)] },
    { op := .arith .addui_extended, props := (), operands := [.res 1 0, .res 0 0],
      results := [some (intTy w), some (intTy 1)] } ]

/-- The expansions of `modArithDialect`: copies and the tensor reinterprets are
    aliases, `montReduce` is `mod_arith.mont_reduce` of the stored word and a zero
    high word, `mulHi` is the second result of `arith.mului_extended`, and the
    carry-chain adds are the `arith.addui_extended` chain. -/
def ModArithOp.expandIn (pc : AlgebraicPrintCtx) :
    ModArithOp → Option (VeirExpansion Veir.OpCode)
  | .modCopy _ | .polyToTensor _ _ | .polyFromTensor _ _ =>
      some { steps := [], value := .arg 0 }
  | .montReduce p _ =>
      let w := pc.width p
      some
        { steps :=
            [ { op := .mod_arith .bitcast, props := (), operands := [.arg 0],
                results := [some (intTy w)] },
              { op := .arith .constant,
                props := ({ value := intAttr 0 w } : Veir.ArithConstantProperties),
                operands := [], results := [some (intTy w)] },
              { op := .mod_arith .mont_reduce, props := (),
                operands := [.res 0 0, .res 1 0], results := [none] } ]
          value := .res 2 0 }
  | .mulHi w =>
      some
        { steps :=
            [ { op := .arith .mului_extended, props := (), operands := [.arg 0, .arg 1],
                results := [some (intTy w), some (intTy w)] } ]
          value := .res 0 1 }
  | .addCarryLo w => some { steps := addCarrySteps w, value := .res 2 0 }
  | .addCarryHi w =>
      some
        { steps := addCarrySteps w ++
            [ { op := .arith .ori, props := default, operands := [.res 1 1, .res 2 1],
                results := [some (intTy 1)] } ]
          value := .res 3 0 }
  | _ => none

/-- The side conditions of a `ModArithOp` under the print context: the modulus fits
    the width, `rInv` inverts the radix `2 ^ W`, the word width of a bitcast is the
    storage width, and the op has a VeIR form. -/
def ModArithOp.checkIn (pc : AlgebraicPrintCtx) : ModArithOp → Except String Unit
  | .modAdd p | .modSub p | .modNeg p | .modMul p | .modConst p _ | .modCopy p
  | .byInverse p | .batchInverse p _ | .polyToTensor p _ | .polyFromTensor p _ =>
      pc.checkModulus p
  | .montMul p rInv | .montInverse p rInv | .montReduce p rInv => do
      pc.checkModulus p
      pc.checkRInv p rInv.val
  | .residueEncode p w | .residueDecode p w => do
      pc.checkModulus p
      require (w == pc.width p)
        s!"bitcast between i{w} and a modulus of storage width i{pc.width p}"
  | .modReduce _ _ | .solinasReduce _ _ | .barrettReduce _ _ =>
      .error "reductions from a word have no VeIR operation"
  | .mulHi w | .addCarryLo w | .addCarryHi w => require (0 < w) "zero-width word"

/-- The lowering of `modArithDialect` under a print context. -/
@[reducible] def modArithToVeirOp (pc : AlgebraicPrintCtx) : ToVeirOp modArithDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := ModArithOp.toVeirOpCode
  defaultProps := ModArithOp.propsIn pc
  expand? := ModArithOp.expandIn pc

/-- The types of `modArithDialect` under a print context. -/
@[reducible] def modArithToVeirTy (pc : AlgebraicPrintCtx) : ToVeirTy modArithDialect where
  toTy := ModArithTy.toVeirTyIn pc

/-! ## `fieldDialect` -/

/-- The VeIR type of a `FieldTy` under the print context. -/
def FieldTy.toVeirTyIn (pc : AlgebraicPrintCtx) : FieldTy → Veir.TypeAttr
  | .fp p => primeFieldTy p (pc.width p)
  | .fp2 p => ext2Ty p (pc.width p)
  | .fp6 p => ext6Ty p (pc.width p) ((pc.towerXi0 p).getD 0)
  | .fp12 p => ext12Ty p (pc.width p) ((pc.towerXi0 p).getD 0)

/-- The check of a `FieldTy` against the print context. -/
def FieldTy.checkIn (pc : AlgebraicPrintCtx) : FieldTy → Except String Unit
  | .fp p | .fp2 p => pc.checkModulus p
  | .fp6 p | .fp12 p => do
      pc.checkModulus p
      pc.checkTower p

/-- The VeIR op-code of a `FieldOp` printed as one operation; the ops that lower
    through an expansion map to `catcrypt.unknown`. -/
def FieldOp.toVeirOpCode : FieldOp → Veir.OpCode
  | .fAdd _ | .ext2Add _ | .ext6Add _ | .ext12Add _ => .field .add
  | .fSub _ | .ext2Sub _ | .ext6Sub _ | .ext12Sub _ => .field .sub
  | .fMul _ | .ext2Mul _ | .ext6Mul _ _ | .ext12Mul _ _ => .field .mul
  | .fNeg _ => .field .negate
  | .fInv _ => .field .inverse
  | .fConst _ _ => .field .constant
  | .fieldDouble _ => .field .double
  | .fieldSquare _ => .field .square
  | .fCopy _ | .frobenius2 _ => .catcrypt .unknown

/-- The properties of the operation of a `FieldOp`: the value `c.val : iW` of
    `field.constant`, and the default properties otherwise. -/
def FieldOp.propsIn (pc : AlgebraicPrintCtx) (o : FieldOp) :
    Veir.propertiesOf (FieldOp.toVeirOpCode o) :=
  match o with
  | .fConst p c =>
      ({ value := .integerAttr (intAttr c.val (pc.width p)) } : Veir.FieldConstantProperties)
  | _ => default

/-- The expansions of `fieldDialect`: `fCopy` is an alias, and `frobenius2 p` is
    `field.powui` by the exponent `p`, an `arith.constant` of the storage width
    (`powui` reads the exponent as unsigned). -/
def FieldOp.expandIn (pc : AlgebraicPrintCtx) : FieldOp → Option (VeirExpansion Veir.OpCode)
  | .fCopy _ => some { steps := [], value := .arg 0 }
  | .frobenius2 p =>
      let w := pc.width p
      some
        { steps :=
            [ { op := .arith .constant,
                props := ({ value := intAttr p w } : Veir.ArithConstantProperties),
                operands := [], results := [some (intTy w)] },
              { op := .field .powui, props := ({ unroll := none } : Veir.FieldPowUIProperties),
                operands := [.arg 0, .res 0 0], results := [none] } ]
          value := .res 1 0 }
  | _ => none

/-- The side conditions of a `FieldOp` under the print context: the modulus fits the
    width, a tower op has a tower over its modulus, and an `Fp6`/`Fp12` multiply
    carries the context's `ξ₀`. -/
def FieldOp.checkIn (pc : AlgebraicPrintCtx) : FieldOp → Except String Unit
  | .fAdd p | .fSub p | .fNeg p | .fMul p | .fInv p | .fConst p _ | .fCopy p
  | .fieldDouble p | .fieldSquare p | .ext2Mul p | .ext2Add p | .ext2Sub p
  | .frobenius2 p => pc.checkModulus p
  | .ext6Add p | .ext6Sub p | .ext12Add p | .ext12Sub p => do
      pc.checkModulus p
      pc.checkTower p
  | .ext6Mul p ξ0 | .ext12Mul p ξ0 => do
      pc.checkModulus p
      require (pc.towerXi0 p == some ξ0.val)
        s!"the multiply carries ξ₀ = {ξ0.val}, the print context {pc.towerXi0 p}"

/-- The lowering of `fieldDialect` under a print context. -/
@[reducible] def fieldToVeirOp (pc : AlgebraicPrintCtx) : ToVeirOp fieldDialect where
  Op := Veir.OpCode
  hasOpInfo := inferInstance
  toOp := FieldOp.toVeirOpCode
  defaultProps := FieldOp.propsIn pc
  expand? := FieldOp.expandIn pc

/-- The types of `fieldDialect` under a print context. -/
@[reducible] def fieldToVeirTy (pc : AlgebraicPrintCtx) : ToVeirTy fieldDialect where
  toTy := FieldTy.toVeirTyIn pc

/-! ## Modules -/

/-- The `builtin.module` holding `func.func @name` lowered from a `modArithDialect`
    program, when its side conditions pass. -/
def modArithModule (pc : AlgebraicPrintCtx) {Γ : Ctxt modArithDialect} {t : ModArithTy}
    (com : Com modArithDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  checkCom (ModArithOp.checkIn pc) (ModArithTy.checkIn pc) com
  letI := modArithToVeirOp pc
  letI := modArithToVeirTy pc
  pure (lowerClosedComToModuleWithExterns (d := modArithDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

/-- The `builtin.module` holding `func.func @name` lowered from a `fieldDialect`
    program, when its side conditions pass. -/
def fieldModule (pc : AlgebraicPrintCtx) {Γ : Ctxt fieldDialect} {t : FieldTy}
    (com : Com fieldDialect Γ t) (name : String) :
    Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr) := do
  checkCom (FieldOp.checkIn pc) (FieldTy.checkIn pc) com
  letI := fieldToVeirOp pc
  letI := fieldToVeirTy pc
  pure (lowerClosedComToModuleWithExterns (d := fieldDialect) com []
    (Veir.OpCode.builtin .module) default
    (Veir.OpCode.func .func) VeirPrinterShim.funcFuncProps
    (Veir.OpCode.func .return) default name)

/-! ## MLIR text -/

/-- `n` levels of two-space indentation. -/
def indentText : Nat → String
  | 0 => ""
  | n + 1 => "  " ++ indentText n

/-- The text of a value, as `Veir.Printer.printValue` prints it. -/
def valueText (ctx : Veir.IRContext Veir.OpCode) : Veir.ValuePtr → String
  | .opResult r =>
      let res := r.get! ctx
      if (res.owner.get! ctx).results.size = 1 then s!"%{res.owner.id}"
      else s!"%{res.owner.id}#{res.index}"
  | .blockArgument b =>
      let a := b.get! ctx
      s!"%arg{a.owner.id}_{a.index}"

/-- The results, name, operands and properties of an operation, as
    `Veir.Printer.printOperation` prints them before its regions. -/
def opHeadText (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr) : String :=
  let o := op.get! ctx
  let n := op.getNumResults! ctx
  let results :=
    if n ≠ 0 then s!"%{op.id}" ++ (if n > 1 then s!":{n}" else "") ++ " = " else ""
  let name := String.fromUTF8! (Veir.IsOpCode.name o.opType)
  let operands := ", ".intercalate
    ((List.range (op.getNumOperands! ctx)).map fun i => valueText ctx (op.getOperand! ctx i))
  let attrDict := Veir.IsOpCode.toAttrDict o.opType (op.getProperties! ctx o.opType)
  let props :=
    if attrDict.size = 0 then "" else s!" <{Veir.DictionaryAttr.fromArray attrDict.toArray}>"
  results ++ "\"" ++ name ++ "\"(" ++ operands ++ ")" ++ props

/-- The discardable attributes and the type of an operation, as
    `Veir.Printer.printOperation` prints them after its regions. -/
def opTailText (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr) : String :=
  let o := op.get! ctx
  let attrs := if o.attrs.entries.size = 0 then "" else s!" {o.attrs}"
  let ins := ", ".intercalate
    ((List.range (op.getNumOperands! ctx)).map fun i =>
      toString ((op.getOperand! ctx i).getType! ctx))
  let n := op.getNumResults! ctx
  let resTy (i : Nat) : Veir.TypeAttr := ((op.getResult i).get! ctx).type
  let outs :=
    if n = 0 then "()"
    else if n = 1 then
      match (resTy 0).val with
      | .functionType _ => s!"({resTy 0})"
      | _ => toString (resTy 0)
    else "(" ++ ", ".intercalate ((List.range n).map fun i => toString (resTy i)) ++ ")"
  attrs ++ " : (" ++ ins ++ ") -> " ++ outs

mutual
/-- The text of an operation and the operations after it in its block. -/
partial def opListText (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr)
    (indent : Nat) : String :=
  opText ctx op indent ++
    match (op.get! ctx).next with
    | some nxt => opListText ctx nxt indent
    | none => ""

/-- The text of a block and the blocks after it in its region. -/
partial def blockListText (ctx : Veir.IRContext Veir.OpCode) (blk : Veir.BlockPtr)
    (indent : Nat) : String :=
  let args := ", ".intercalate
    ((List.range (blk.getNumArguments! ctx)).map fun i =>
      s!"%arg{blk.id}_{i} : {((blk.getArgument i).get! ctx).type}")
  let head := indentText indent ++ s!"^{blk.id}(" ++ args ++ "):\n"
  let body :=
    match (blk.get! ctx).firstOp with
    | some first => opListText ctx first (indent + 1)
    | none => ""
  head ++ body ++
    match (blk.get! ctx).next with
    | some nxt => blockListText ctx nxt indent
    | none => ""

/-- The text of an operation without successors, as `Veir.Printer.printOperation`
    prints it; an unregistered operation prints under its generic name. -/
partial def opText (ctx : Veir.IRContext Veir.OpCode) (op : Veir.OperationPtr)
    (indent : Nat) : String :=
  let nr := op.getNumRegions! ctx
  let regionText (i : Nat) : String :=
    match ((op.getRegion! ctx i).get! ctx).firstBlock with
    | none => "{" ++ indentText indent ++ "}"
    | some b => "{\n" ++ blockListText ctx b (indent + 1) ++ indentText indent ++ "}"
  let regions :=
    if nr = 0 then "" else " (" ++ ", ".intercalate ((List.range nr).map regionText) ++ ")"
  indentText indent ++ opHeadText ctx op ++ regions ++ opTailText ctx op ++ "\n"
end

/-- The MLIR text of a module, or the side condition it fails. -/
def moduleText (m : Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr)) :
    String :=
  match m with
  | .ok (ctx, op) => opText ctx op 0
  | .error e => "error: " ++ e

/-- Write the module, printed by `Veir.Printer.printModule`, to `path`; fail with
    the side condition when the module has none. -/
def writeModule (m : Except String (Veir.IRContext Veir.OpCode × Veir.OperationPtr))
    (path : System.FilePath) : IO Unit :=
  match m with
  | .ok (ctx, op) => VeirPrinterShim.printModuleToFile ctx op path
  | .error e => throw (IO.userError e)

end CatCrypt.Crypto.SecureCompilation.VIR.ComToVeirAlgebraic
