/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.Arith
public import CatCrypt.Crypto.SecureCompilation.Dialects.Memref
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminValTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend

/-!
# The operations shared by `catCryptDialect` and `jasminDialect`

`SharedOp` is the set of operations that `catCryptDialect` and `jasminDialect` both
have with the same meaning. It is the sum of seven components:

| component | operations | `catCryptDialect` | `jasminDialect` |
|---|---|---|---|
| `arith` | `ArithOp` with `InRange` | `bvAdd`, …, `bvMulHi`, `bvShiftL/R`, `bvConst` | `regArith`, `mulhi`, `shlImm/shrImm`, `regConst` |
| `arithExt` | `ArithExtOp` | `andn`, `bvShiftLV/RV`, `bvShiftRA`, `bvEq`, `ite (.sword w)` | `regArith .andn/.shl/.shr`, `sarImm`, `cmp .eq`, `select` |
| `carry` | `CarryOp` | `bvAddCarryLo/Hi` | `addCarryLo/Hi` |
| `rotate` | `RotateOp` | `bvRor` | `rorImm` |
| `memref` | `MemrefOp` | `memrefWGetDyn/SetDyn` | `stackLoad/stackStore` |
| `func` | `FuncOp` | `extCall` with coded types | `extCall` |
| `vec` | `Vec128Op` | `vsimd (.packed _ _)`, `vsimd (.bitwise _)`, `vsimd .mulhi16` | the same `vsimd` |

Each component carries a signature and a denotation over `CryptoTy` (the
`catCryptDialect` alphabet) and over `JasminTy` (the `jasminDialect` alphabet). The
denotation over `CryptoTy` is that of the `catCryptDialect` operation, the denotation
over `JasminTy` that of the `jasminDialect` operation. The boolean is `.bit` over
`CryptoTy` and `.reg 1` over `JasminTy`. The two are related along the type map
`CryptoToJasminCom.mapTy` and the value transport `ctTransTy`.

## Main definitions

* `CarryOp`, `RotateOp`, `SCode`, `SRetCode`, `FuncOp`, `Vec128Op`: the components
  beside `ArithOp`, `ArithExtOp` and `MemrefOp`.
* `SharedOp`: the sum of the components.
* the instances `DialectSignature`, `DialectDenote` of each component and of
  `SharedOp` over `CryptoTy` and over `JasminTy`.

## Main results

* `sharedSigMaps`: `mapTy` carries the signatures over `CryptoTy` to those over
  `JasminTy`.
* `sharedOpsCommute`: every shared operation commutes with `ctTransTy`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SharedDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (mulHiC addCarryWordC carryOutBitC
  memWGetDyn memWSetDyn)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy jasminExtSem_reg)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (SigMaps OpsCommute)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.Arith (ArithOp ArithExtOp)
open CatCrypt.Crypto.SecureCompilation.Dialects.Memref (MemrefOp)

/-! ## 1. The components beside `ArithOp`, `ArithExtOp` and `MemrefOp` -/

/-- The carry-chain add: its data word and its carry-out bit. -/
inductive CarryOp where
  /-- The data word `a + b + cin`. -/
  | addCarryLo (w : Nat)
  /-- The carry-out bit of `a + b + cin`. -/
  | addCarryHi (w : Nat)
  deriving DecidableEq

/-- The right rotate by an immediate. -/
inductive RotateOp where
  /-- `a.rotateRight n`. -/
  | rorImm (w n : Nat)
  deriving DecidableEq

/-- The argument types of a shared external call: a word, a buffer of words, a bit. -/
inductive SCode where
  | word (w : Nat)
  | buf (w n : Nat)
  | bit
  deriving DecidableEq

/-- The return types of a shared external call: a word or a bit. -/
inductive SRetCode where
  | word (w : Nat)
  | bit
  deriving DecidableEq

/-- The external call `name` with argument types `as` and return type `r`. -/
inductive FuncOp where
  | call (name : String) (as : List SCode) (r : SRetCode)
  deriving DecidableEq

/-- The 128-bit packed operations: the per-lane binary op at lane width `lw`, the
    bitwise op, the signed high half of the 16-bit lane product. -/
inductive Vec128Op where
  | vpack128 (bop : JasminBinOp) (lw : Nat)
  | vbit128 (bop : JasminBinOp)
  | vmulhi16
  deriving DecidableEq

/-! ## 2. The type codes -/

/-- An argument code read as a `CryptoTy`. -/
def SCode.toCrypto : SCode → CryptoTy
  | .word w => .sword w
  | .buf w n => .memrefW w n
  | .bit => .bit

/-- An argument code read as a `JasminTy`. -/
def SCode.toJasmin : SCode → JasminTy
  | .word w => .reg w
  | .buf w n => .stackArr w n
  | .bit => .reg 1

/-- A return code read as a `CryptoTy`. -/
def SRetCode.toCrypto : SRetCode → CryptoTy
  | .word w => .sword w
  | .bit => .bit

/-- A return code read as a `JasminTy`. -/
def SRetCode.toJasmin : SRetCode → JasminTy
  | .word w => .reg w
  | .bit => .reg 1

/-- The `JasminTy` reading of argument codes is the `mapTy` image of their `CryptoTy`
    reading. -/
theorem SCode.map_toJasmin (as : List SCode) :
    as.map SCode.toJasmin = (as.map SCode.toCrypto).map mapTy := by
  induction as with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [List.map_cons, ih] <;> rfl

/-! ## 3. Signatures and denotations over `CryptoTy` -/

instance arithCryptoSig : DialectSignature (⟨ArithOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .addi w | .subi w | .muli w | .andi w | .ori w | .xori w
    | .mului_extended_hi w => [.sword w, .sword w]
    | .shrui_imm w _ | .shli_imm w _ => [.sword w]
    | .constant _ _ => []
  ret op := match op with
    | .addi w | .subi w | .muli w | .andi w | .ori w | .xori w
    | .mului_extended_hi w | .shrui_imm w _ | .shli_imm w _ | .constant w _ => .sword w

instance arithCryptoDenote : DialectDenote (⟨ArithOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .addi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a + b
    | .subi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a - b
    | .muli w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a * b
    | .andi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a &&& b
    | .ori w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a ||| b
    | .xori w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; a ^^^ b
    | .mului_extended_hi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; mulHiC a b
    | .shrui_imm w n => fun args =>
        let a : BitVec w := args.head; BitVec.ushiftRight a (shiftMask w n)
    | .shli_imm w n => fun args => let a : BitVec w := args.head; a <<< shiftMask w n
    | .constant w n => fun _ => (BitVec.ofNat w n : BitVec w)

instance arithExtCryptoSig : DialectSignature (⟨ArithExtOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .andni w | .shli w | .shrui w | .cmpi_eq w => [.sword w, .sword w]
    | .shrsi_imm w _ => [.sword w]
    | .select w => [.bit, .sword w, .sword w]
  ret op := match op with
    | .andni w | .shli w | .shrui w | .shrsi_imm w _ | .select w => .sword w
    | .cmpi_eq _ => .bit

instance arithExtCryptoDenote : DialectDenote (⟨ArithExtOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .andni w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; (~~~a) &&& b
    | .shli w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        a <<< shiftMask w b.toNat
    | .shrui w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        a >>> shiftMask w b.toNat
    | .shrsi_imm w n => fun args => let a : BitVec w := args.head; BitVec.sshiftRight a n
    | .cmpi_eq w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        (decide (a = b) : Bool)
    | .select _ => fun args =>
        if (args.head : Bool) then args.tail.head else args.tail.tail.head

instance carryCryptoSig : DialectSignature (⟨CarryOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .addCarryLo w | .addCarryHi w => [.sword w, .sword w, .sword 1]
  ret op := match op with
    | .addCarryLo w => .sword w
    | .addCarryHi _ => .sword 1

instance carryCryptoDenote : DialectDenote (⟨CarryOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .addCarryLo w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        addCarryWordC a b cin
    | .addCarryHi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        carryOutBitC a b cin

instance rotateCryptoSig : DialectSignature (⟨RotateOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .rorImm w _ => [.sword w]
  ret op := match op with
    | .rorImm w _ => .sword w

instance rotateCryptoDenote : DialectDenote (⟨RotateOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .rorImm w n => fun args => let a : BitVec w := args.head; a.rotateRight n

instance memrefCryptoSig : DialectSignature (⟨MemrefOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .load w n => [.memrefW w n, .sword 64]
    | .store w n => [.memrefW w n, .sword 64, .sword w]
  ret op := match op with
    | .load w _ => .sword w
    | .store w n => .memrefW w n

instance memrefCryptoDenote : DialectDenote (⟨MemrefOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .load w n => fun args =>
        let arr : Fin n → BitVec w := args.head; let i : BitVec 64 := args.tail.head
        memWGetDyn arr i.toNat
    | .store w n => fun args =>
        let arr : Fin n → BitVec w := args.head; let i : BitVec 64 := args.tail.head
        let v : BitVec w := args.tail.tail.head
        memWSetDyn arr i.toNat v

instance funcCryptoSig : DialectSignature (⟨FuncOp, CryptoTy⟩ : Dialect) where
  sig op := match op with
    | .call _ as _ => as.map SCode.toCrypto
  ret op := match op with
    | .call _ _ r => r.toCrypto

instance funcCryptoDenote : DialectDenote (⟨FuncOp, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .call _ _ r => fun _ => CryptoTy.default r.toCrypto

instance vecCryptoSig : DialectSignature (⟨Vec128Op, CryptoTy⟩ : Dialect) where
  sig _ := [.sword 128, .sword 128]
  ret _ := .sword 128

instance vecCryptoDenote : DialectDenote (⟨Vec128Op, CryptoTy⟩ : Dialect) where
  denote op := match op with
    | .vpack128 bop lw => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote (.packed bop lw) a b
    | .vbit128 bop => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote (.bitwise bop) a b
    | .vmulhi16 => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote .mulhi16 a b

/-! ## 4. Signatures and denotations over `JasminTy` -/

instance arithJasminSig : DialectSignature (⟨ArithOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .addi w | .subi w | .muli w | .andi w | .ori w | .xori w
    | .mului_extended_hi w => [.reg w, .reg w]
    | .shrui_imm w _ | .shli_imm w _ => [.reg w]
    | .constant _ _ => []
  ret op := match op with
    | .addi w | .subi w | .muli w | .andi w | .ori w | .xori w
    | .mului_extended_hi w | .shrui_imm w _ | .shli_imm w _ | .constant w _ => .reg w

instance arithJasminDenote : DialectDenote (⟨ArithOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .addi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.add.apply a b
    | .subi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.sub.apply a b
    | .muli w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.mul.apply a b
    | .andi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.and.apply a b
    | .ori w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.or.apply a b
    | .xori w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.xor.apply a b
    | .mului_extended_hi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head; mulHiW a b
    | .shrui_imm w n => fun args => let a : BitVec w := args.head; a >>> shiftMask w n
    | .shli_imm w n => fun args => let a : BitVec w := args.head; a <<< shiftMask w n
    | .constant w n => fun _ => (BitVec.ofNat w n : BitVec w)

instance arithExtJasminSig : DialectSignature (⟨ArithExtOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .andni w | .shli w | .shrui w | .cmpi_eq w => [.reg w, .reg w]
    | .shrsi_imm w _ => [.reg w]
    | .select w => [.reg 1, .reg w, .reg w]
  ret op := match op with
    | .andni w | .shli w | .shrui w | .shrsi_imm w _ | .select w => .reg w
    | .cmpi_eq _ => .reg 1

instance arithExtJasminDenote : DialectDenote (⟨ArithExtOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .andni w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.andn.apply a b
    | .shli w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.shl.apply a b
    | .shrui w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        JasminBinOp.shr.apply a b
    | .shrsi_imm w n => fun args => let a : BitVec w := args.head; BitVec.sshiftRight a n
    | .cmpi_eq w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        cmpBit .eq a b
    | .select w => fun args =>
        let c : BitVec 1 := args.head; let a : BitVec w := args.tail.head
        let b : BitVec w := args.tail.tail.head
        selectW c a b

instance carryJasminSig : DialectSignature (⟨CarryOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .addCarryLo w | .addCarryHi w => [.reg w, .reg w, .reg 1]
  ret op := match op with
    | .addCarryLo w => .reg w
    | .addCarryHi _ => .reg 1

instance carryJasminDenote : DialectDenote (⟨CarryOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .addCarryLo w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        addCarryWord a b cin
    | .addCarryHi w => fun args =>
        let a : BitVec w := args.head; let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        carryOutBit a b cin

instance rotateJasminSig : DialectSignature (⟨RotateOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .rorImm w _ => [.reg w]
  ret op := match op with
    | .rorImm w _ => .reg w

instance rotateJasminDenote : DialectDenote (⟨RotateOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .rorImm w n => fun args => let a : BitVec w := args.head; a.rotateRight n

instance memrefJasminSig : DialectSignature (⟨MemrefOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .load w n => [.stackArr w n, .reg 64]
    | .store w n => [.stackArr w n, .reg 64, .reg w]
  ret op := match op with
    | .load w _ => .reg w
    | .store w n => .stackArr w n

instance memrefJasminDenote : DialectDenote (⟨MemrefOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .load w n => fun args =>
        let arr : Fin n → BitVec w := args.head; let i : BitVec 64 := args.tail.head
        stackGet arr i.toNat
    | .store w n => fun args =>
        let arr : Fin n → BitVec w := args.head; let i : BitVec 64 := args.tail.head
        let v : BitVec w := args.tail.tail.head
        stackSet arr i.toNat v

instance funcJasminSig : DialectSignature (⟨FuncOp, JasminTy⟩ : Dialect) where
  sig op := match op with
    | .call _ as _ => as.map SCode.toJasmin
  ret op := match op with
    | .call _ _ r => r.toJasmin

instance funcJasminDenote : DialectDenote (⟨FuncOp, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .call name as r => fun args => jasminExtSem name (as.map SCode.toJasmin) r.toJasmin args

instance vecJasminSig : DialectSignature (⟨Vec128Op, JasminTy⟩ : Dialect) where
  sig _ := [.reg 128, .reg 128]
  ret _ := .reg 128

instance vecJasminDenote : DialectDenote (⟨Vec128Op, JasminTy⟩ : Dialect) where
  denote op := match op with
    | .vpack128 bop lw => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote (.packed bop lw) a b
    | .vbit128 bop => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote (.bitwise bop) a b
    | .vmulhi16 => fun args =>
        let a : BitVec 128 := args.head; let b : BitVec 128 := args.tail.head
        SimdOp.denote .mulhi16 a b

/-! ## 5. The components commute with `ctTransTy` -/

/-- `mapTy` carries the signatures of the `arith` ops. -/
theorem arithSigMaps : SigMaps ArithOp mapTy :=
  ⟨fun o => by cases o <;> rfl, fun o => by cases o <;> rfl⟩

/-- The `arith` ops commute with `ctTransTy`. -/
theorem arithOpsCommute : OpsCommute mapTy arithSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> rfl

/-- `mapTy` carries the signatures of the `arith` extension ops; the 1-bit result of
    `cmpi_eq` and condition of `select` are `.bit` over `CryptoTy`. -/
theorem arithExtSigMaps : SigMaps ArithExtOp mapTy :=
  ⟨fun o => by cases o <;> rfl, fun o => by cases o <;> rfl⟩

/-- The `arith` extension ops commute with `ctTransTy`: on `cmpi_eq` the comparison bit
    is `BitVec.ofBool` of the boolean, on `select` the `selectW` of `BitVec.ofBool c` is
    the `if` on `c`. -/
theorem arithExtOpsCommute :
    OpsCommute mapTy arithExtSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o
  case cmpi_eq w =>
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩
    show cmpBit .eq (a : BitVec w) b
      = BitVec.ofBool (@decide (a = b) (instDecidableEqBitVec a b))
    by_cases h : (a : BitVec w) = b <;> simp [cmpBit, JasminCmp.holds, h]
  case select w =>
    rcases xs with _ | ⟨c, _ | ⟨a, _ | ⟨b, _⟩⟩⟩
    show selectW (BitVec.ofBool c) a b = if c then a else b
    cases c <;> rfl
  all_goals (rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩; rfl)

/-- `mapTy` carries the signatures of the carry ops. -/
theorem carrySigMaps : SigMaps CarryOp mapTy :=
  ⟨fun o => by cases o <;> rfl, fun o => by cases o <;> rfl⟩

/-- The carry ops commute with `ctTransTy`. -/
theorem carryOpsCommute : OpsCommute mapTy carrySigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o <;> rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> rfl

/-- `mapTy` carries the signature of the rotate op. -/
theorem rotateSigMaps : SigMaps RotateOp mapTy :=
  ⟨fun o => by cases o; rfl, fun o => by cases o; rfl⟩

/-- The rotate op commutes with `ctTransTy`. -/
theorem rotateOpsCommute : OpsCommute mapTy rotateSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o
  rcases xs with _ | ⟨a, _⟩
  rfl

/-- `mapTy` carries the signatures of the memref ops. -/
theorem memrefSigMaps : SigMaps MemrefOp mapTy :=
  ⟨fun o => by cases o <;> rfl, fun o => by cases o <;> rfl⟩

/-- The memref ops commute with `ctTransTy`: `memWGetDyn`/`memWSetDyn` are
    `stackGet`/`stackSet`. -/
theorem memrefOpsCommute : OpsCommute mapTy memrefSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o with
  | load w n =>
    rcases xs with _ | ⟨a, _ | ⟨b, _⟩⟩
    cases n <;> rfl
  | store w n =>
    rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩
    cases n <;> rfl

/-- `mapTy` carries the signatures of the external calls. -/
theorem funcSigMaps : SigMaps FuncOp mapTy :=
  ⟨fun o => by cases o; exact SCode.map_toJasmin _,
   fun o => by cases o with | call _ _ r => cases r <;> rfl⟩

/-- The external calls commute with `ctTransTy`: both sides are the default value of
    the return type, since `jasminExtSem` at a `.reg` return type is the default. -/
theorem funcOpsCommute : OpsCommute mapTy funcSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o with
  | call name as r =>
    cases r with
    | word w => exact (jasminExtSem_reg _ _ _ _).trans rfl
    | bit => exact (jasminExtSem_reg _ _ _ _).trans rfl

/-- `mapTy` carries the signatures of the 128-bit packed ops. -/
theorem vecSigMaps : SigMaps Vec128Op mapTy :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The 128-bit packed ops commute with `ctTransTy`. -/
theorem vecOpsCommute : OpsCommute mapTy vecSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o <;> rcases xs with _ | ⟨a, _ | ⟨b, _⟩⟩ <;> rfl

/-! ## 6. The sum `SharedOp` -/

/-- **The shared operations** of `catCryptDialect` and `jasminDialect`: the sum of the
    seven components. The `arith` constants are restricted to `ArithOp.InRange`. -/
inductive SharedOp where
  | arith (o : {o : ArithOp // o.InRange})
  | arithExt (o : ArithExtOp)
  | carry (o : CarryOp)
  | rotate (o : RotateOp)
  | memref (o : MemrefOp)
  | func (o : FuncOp)
  | vec (o : Vec128Op)
  deriving DecidableEq

section Sum

variable {T : Type}
  [DialectSignature (⟨ArithOp, T⟩ : Dialect)] [DialectSignature (⟨ArithExtOp, T⟩ : Dialect)]
  [DialectSignature (⟨CarryOp, T⟩ : Dialect)] [DialectSignature (⟨RotateOp, T⟩ : Dialect)]
  [DialectSignature (⟨MemrefOp, T⟩ : Dialect)] [DialectSignature (⟨FuncOp, T⟩ : Dialect)]
  [DialectSignature (⟨Vec128Op, T⟩ : Dialect)]

/-- The signature of `SharedOp` over a type alphabet with signatures for every
    component: the signature of the component. -/
@[reducible] instance sharedSig : DialectSignature (⟨SharedOp, T⟩ : Dialect) where
  sig op := match op with
    | .arith o => DialectSignature.sig (d := ⟨ArithOp, T⟩) o.1
    | .arithExt o => DialectSignature.sig (d := ⟨ArithExtOp, T⟩) o
    | .carry o => DialectSignature.sig (d := ⟨CarryOp, T⟩) o
    | .rotate o => DialectSignature.sig (d := ⟨RotateOp, T⟩) o
    | .memref o => DialectSignature.sig (d := ⟨MemrefOp, T⟩) o
    | .func o => DialectSignature.sig (d := ⟨FuncOp, T⟩) o
    | .vec o => DialectSignature.sig (d := ⟨Vec128Op, T⟩) o
  ret op := match op with
    | .arith o => DialectSignature.ret (d := ⟨ArithOp, T⟩) o.1
    | .arithExt o => DialectSignature.ret (d := ⟨ArithExtOp, T⟩) o
    | .carry o => DialectSignature.ret (d := ⟨CarryOp, T⟩) o
    | .rotate o => DialectSignature.ret (d := ⟨RotateOp, T⟩) o
    | .memref o => DialectSignature.ret (d := ⟨MemrefOp, T⟩) o
    | .func o => DialectSignature.ret (d := ⟨FuncOp, T⟩) o
    | .vec o => DialectSignature.ret (d := ⟨Vec128Op, T⟩) o

variable [TyDenote T]
  [DialectDenote (⟨ArithOp, T⟩ : Dialect)] [DialectDenote (⟨ArithExtOp, T⟩ : Dialect)]
  [DialectDenote (⟨CarryOp, T⟩ : Dialect)] [DialectDenote (⟨RotateOp, T⟩ : Dialect)]
  [DialectDenote (⟨MemrefOp, T⟩ : Dialect)] [DialectDenote (⟨FuncOp, T⟩ : Dialect)]
  [DialectDenote (⟨Vec128Op, T⟩ : Dialect)]

/-- The denotation of `SharedOp`: the denotation of the component. -/
@[reducible] instance sharedDenote : DialectDenote (⟨SharedOp, T⟩ : Dialect) where
  denote op := match op with
    | .arith o => DialectDenote.denote (d := ⟨ArithOp, T⟩) o.1
    | .arithExt o => DialectDenote.denote (d := ⟨ArithExtOp, T⟩) o
    | .carry o => DialectDenote.denote (d := ⟨CarryOp, T⟩) o
    | .rotate o => DialectDenote.denote (d := ⟨RotateOp, T⟩) o
    | .memref o => DialectDenote.denote (d := ⟨MemrefOp, T⟩) o
    | .func o => DialectDenote.denote (d := ⟨FuncOp, T⟩) o
    | .vec o => DialectDenote.denote (d := ⟨Vec128Op, T⟩) o

end Sum

/-! ## 7. The shared operations commute with `ctTransTy` -/

/-- **`mapTy` carries the signatures of the shared operations** over `CryptoTy` to
    those over `JasminTy`. -/
theorem sharedSigMaps : SigMaps SharedOp mapTy where
  sig_eq o := by
    cases o with
    | arith o => exact arithSigMaps.sig_eq o.1
    | arithExt o => exact arithExtSigMaps.sig_eq o
    | carry o => exact carrySigMaps.sig_eq o
    | rotate o => exact rotateSigMaps.sig_eq o
    | memref o => exact memrefSigMaps.sig_eq o
    | func o => exact funcSigMaps.sig_eq o
    | vec o => exact vecSigMaps.sig_eq o
  ret_eq o := by
    cases o with
    | arith o => exact arithSigMaps.ret_eq o.1
    | arithExt o => exact arithExtSigMaps.ret_eq o
    | carry o => exact carrySigMaps.ret_eq o
    | rotate o => exact rotateSigMaps.ret_eq o
    | memref o => exact memrefSigMaps.ret_eq o
    | func o => exact funcSigMaps.ret_eq o
    | vec o => exact vecSigMaps.ret_eq o

/-- **Every shared operation commutes with `ctTransTy`**: the operation over
    `JasminTy` applied to the transported arguments is the transport of the operation
    over `CryptoTy`. -/
theorem sharedOpsCommute : OpsCommute mapTy sharedSigMaps ctTransTy (fun _ => True) := by
  intro o _ xs
  cases o with
  | arith o => exact arithOpsCommute o.1 trivial xs
  | arithExt o => exact arithExtOpsCommute o trivial xs
  | carry o => exact carryOpsCommute o trivial xs
  | rotate o => exact rotateOpsCommute o trivial xs
  | memref o => exact memrefOpsCommute o trivial xs
  | func o => exact funcOpsCommute o trivial xs
  | vec o => exact vecOpsCommute o trivial xs

end CatCrypt.Crypto.SecureCompilation.VIR.SharedDialect
