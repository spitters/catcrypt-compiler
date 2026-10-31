/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
public import CatCrypt.Crypto.PrimeIR.Proof.FieldModelBridge
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont4Instances
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.MontInstances

@[expose] public section

set_option autoImplicit false

/-!
# The Montgomery field template at the bytes, at five primes

The bytes-correctness theorem of the Montgomery template (`FieldBytes.field_correct_bytes`
for the product, `field2_correct_bytes` for every covered binary program, here the square,
the sum and the difference) at the Montgomery records of the P-256 base prime
(`Mont4Instances.p256`, four limbs), the secp256k1 base prime (`Mont4Instances.secp256k1`,
four limbs), the P-384 base prime (`MontInstances.p384`, six limbs), the BN254 base prime
(`Mont4Instances.bn254`, four limbs) and the BLS12-381 base prime
(`MontInstances.bls12381`, six limbs). The limb-count side condition `n < 2 ^ 64` is
discharged; the compile hypothesis `compileRegion … (NFProg.ofCom …) = some (P', bytes)` of
the region back half is kept as a hypothesis, for every export names.

The hax function `fe_mul_add` (`a * b + c`) of the `primeir_hax` crate at the P-256 base
prime, under the layout `fieldAbi 3 4`: the compiler theorem `field_correct_auto` at the
front `fieldLeg P256 ["a", "b", "c"]`, which routes it to the Montgomery template of
`Mont4Instances.p256` (`fieldTemplateOf_p256`), and its composition with the bridge
`FieldModelBridge.fe_mul_add_bridge_fp256Mont`, which states that the machine reads back the
Montgomery limbs of the Montgomery value of the surface function's result.

The compile hypothesis of a template instance (sections 2 to 6) is satisfiable exactly when
`compileRegion` accepts the program. No theorem of this module states acceptance.

## Main results

* `field2_correct_bytes`: the bytes theorem of a binary field program accepted by `GoodVB`.
* `p256_mul_correct_bytes`, `secp256k1_mul_correct_bytes`, `p384_mul_correct_bytes`: the
  product at the three primes.
* `p256_add_correct_bytes`, `secp256k1_add_correct_bytes`, `p384_add_correct_bytes`: the
  sum at the three primes.
* `p256_sub_correct_bytes`, `secp256k1_sub_correct_bytes`, `p384_sub_correct_bytes`: the
  difference at the three primes, for the program binding `x - y` over `[x, y]`.
* `p256_sqr_correct_bytes`, `secp256k1_sqr_correct_bytes`, `p384_sqr_correct_bytes`,
  `bn254_sqr_correct_bytes`, `bls12381_sqr_correct_bytes`: the square at the five primes, for
  the program binding `fieldSquare x` over `[x, y]`.
* `bn254_mul_correct_bytes`, `bls12381_mul_correct_bytes`, `bn254_add_correct_bytes`,
  `bls12381_add_correct_bytes`, `bn254_sub_correct_bytes`, `bls12381_sub_correct_bytes`: the
  product, sum and difference at the BN254 and BLS12-381 base primes.
* `limbParamsOf_p256`, `fieldTemplateOf_p256`: the template that `fieldTemplateOf` chooses at
  the P-256 base prime is the Montgomery template of `Mont4Instances.p256`.
* `fe_mul_add_correct_p256`: `field_correct_auto` for `fe_mul_add` at the P-256 base prime.
* `fe_mul_add_bytes_p256`: its composition with `fe_mul_add_bridge_fp256Mont`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldInstances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (fieldCom arrLimbs GoodVB opGoodB)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldBytes (field_correct_bytes)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldCorrect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (wordsFn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open _root_.Hax (Value Env)

/-! ## 1. A binary field program at the bytes -/

/-- **A binary field program at the bytes.** For a field program `c` over `[x, y]` accepted
    by `GoodVB P` and a result `(P', bytes)` of `compileRegion` on its limb program
    (`NFProg.ofCom`) under the layout `fieldAbi2 n`: from every machine state `sa` satisfying the layout's regions, whose
    arrays at `%rdx` and `%rsi` hold the Montgomery limbs of `x` and `y`, the bytes decode to a
    program that halts in a state from which the layout reads back the words of an array
    whose limbs are the Montgomery limbs of the value of `c`. -/
theorem field2_correct_bytes {n : Nat} (P : LimbParams n) (hn : n < 2 ^ 64)
    (c : Com fieldDialect [.fp P.p, .fp P.p] (.fp P.p)) (hc : GoodVB P c = true)
    (a : AbiNames) {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 n) a (NFProg.ofCom (fieldCom P c)) = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 n).Regions sa) (x y : ZMod P.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0 = enc P x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0 = enc P y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin n → BitVec 64, (fieldAbi2 n).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr n 0 = enc P (c.denote (.cons x (.cons y .nil))) := by
  have hcf : compileField P c = some (.straight (fieldCom P c)) := by
    simp [compileField_eq, hc]
  obtain ⟨prog, sa', hd, hh, hr, -⟩ :=
    compileRegion_correct h sa (abiVal2 n P.p sa) (abiValOf_fieldAbi2 n P.p sa) hreg 0
      (NFProg.denote_ofCom _ 0 _)
  refine ⟨prog, sa', hd, hh, (fieldCom P c).denote (abiVal2 n P.p sa), hr, ?_⟩
  have hm := compileField2_denote P hn hcf sa x y hx hy
  rwa [RouteProg.denote_straight] at hm

/-- The sum is accepted by `GoodVB` at every Montgomery record. -/
theorem goodVB_addProg {n : Nat} (P : LimbParams n) : GoodVB P (addProg P.p) = true := by
  simp [GoodVB, opGoodB, addProg]

/-! ## 2. The product at the three primes -/

/-- **The field product at the bytes at the P-256 base prime** (four limbs). -/
theorem p256_mul_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.p256 (mulProg Mont4Instances.p256.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.p256.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.p256 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.p256 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.p256 (x * y) :=
  field_correct_bytes Mont4Instances.p256 (by decide) a h sa hreg x y hx hy

/-- **The field product at the bytes at the secp256k1 base prime** (four limbs). -/
theorem secp256k1_mul_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.secp256k1 (mulProg Mont4Instances.secp256k1.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.secp256k1.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.secp256k1 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.secp256k1 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.secp256k1 (x * y) :=
  field_correct_bytes Mont4Instances.secp256k1 (by decide) a h sa hreg x y hx hy

/-- **The field product at the bytes at the P-384 base prime** (six limbs). -/
theorem p384_mul_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom MontInstances.p384 (mulProg MontInstances.p384.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.p384.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.p384 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.p384 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.p384 (x * y) :=
  field_correct_bytes MontInstances.p384 (by decide) a h sa hreg x y hx hy

/-! ## 3. The sum at the three primes -/

/-- **The field sum at the bytes at the P-256 base prime** (four limbs). -/
theorem p256_add_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.p256 (addProg Mont4Instances.p256.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.p256.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.p256 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.p256 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.p256 (x + y) :=
  field2_correct_bytes Mont4Instances.p256 (by decide) _ (goodVB_addProg _) a h sa hreg
    x y hx hy

/-- **The field sum at the bytes at the secp256k1 base prime** (four limbs). -/
theorem secp256k1_add_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.secp256k1 (addProg Mont4Instances.secp256k1.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.secp256k1.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.secp256k1 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.secp256k1 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.secp256k1 (x + y) :=
  field2_correct_bytes Mont4Instances.secp256k1 (by decide) _ (goodVB_addProg _) a h sa
    hreg x y hx hy

/-- **The field sum at the bytes at the P-384 base prime** (six limbs). -/
theorem p384_add_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom MontInstances.p384 (addProg MontInstances.p384.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.p384.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.p384 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.p384 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.p384 (x + y) :=
  field2_correct_bytes MontInstances.p384 (by decide) _ (goodVB_addProg _) a h sa hreg
    x y hx hy

/-! ## 4. The difference at the three primes -/

/-- The difference `x - y` is accepted by `GoodVB` at every Montgomery record. -/
theorem goodVB_subProg {n : Nat} (P : LimbParams n) :
    GoodVB P (.var ⟨.fSub P.p, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)
      : Com fieldDialect [.fp P.p, .fp P.p] (.fp P.p)) = true := by
  simp [GoodVB, opGoodB]

/-- **The field difference at the bytes at the P-256 base prime** (four limbs). -/
theorem p256_sub_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom (Γ := [_, _]) Mont4Instances.p256
        (.var ⟨.fSub Mont4Instances.p256.p, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.p256.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.p256 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.p256 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.p256 (x - y) :=
  field2_correct_bytes Mont4Instances.p256 (by decide) _ (goodVB_subProg _) a h sa hreg
    x y hx hy

/-- **The field difference at the bytes at the secp256k1 base prime** (four limbs). -/
theorem secp256k1_sub_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom (Γ := [_, _]) Mont4Instances.secp256k1
        (.var ⟨.fSub Mont4Instances.secp256k1.p, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.secp256k1.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.secp256k1 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.secp256k1 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.secp256k1 (x - y) :=
  field2_correct_bytes Mont4Instances.secp256k1 (by decide) _ (goodVB_subProg _) a h sa
    hreg x y hx hy

/-- **The field difference at the bytes at the P-384 base prime** (six limbs). -/
theorem p384_sub_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom (Γ := [_, _]) MontInstances.p384
        (.var ⟨.fSub MontInstances.p384.p, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.p384.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.p384 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.p384 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.p384 (x - y) :=
  field2_correct_bytes MontInstances.p384 (by decide) _ (goodVB_subProg _) a h sa hreg
    x y hx hy

/-! ## 5. The square at five primes

The square is the program binding the dialect operation `fieldSquare` at `x` over `[x, y]`,
which `fieldCom` lowers to the Montgomery square block `Mont.sqrBlk`. -/

/-- The square `fieldSquare x` is accepted by `GoodVB` at every Montgomery record. -/
theorem goodVB_sqrProg {n : Nat} (P : LimbParams n) :
    GoodVB P (.var ⟨.fieldSquare P.p, rfl, .cons .here .nil⟩ (.ret .here)
      : Com fieldDialect [.fp P.p, .fp P.p] (.fp P.p)) = true := by
  simp [GoodVB, opGoodB]

/-- **The field square at the bytes at the P-256 base prime** (four limbs). -/
theorem p256_sqr_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom (Γ := [.fp Mont4Instances.p256.p, .fp Mont4Instances.p256.p])
        Mont4Instances.p256
        (.var ⟨.fieldSquare Mont4Instances.p256.p, rfl, .cons .here .nil⟩ (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.p256.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.p256 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.p256 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.p256 (x * x) :=
  field2_correct_bytes Mont4Instances.p256 (by decide) _ (goodVB_sqrProg _) a h sa hreg
    x y hx hy

/-- **The field square at the bytes at the secp256k1 base prime** (four limbs). -/
theorem secp256k1_sqr_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom
        (Γ := [.fp Mont4Instances.secp256k1.p, .fp Mont4Instances.secp256k1.p])
        Mont4Instances.secp256k1
        (.var ⟨.fieldSquare Mont4Instances.secp256k1.p, rfl, .cons .here .nil⟩ (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.secp256k1.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.secp256k1 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.secp256k1 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.secp256k1 (x * x) :=
  field2_correct_bytes Mont4Instances.secp256k1 (by decide) _ (goodVB_sqrProg _) a h sa
    hreg x y hx hy

/-- **The field square at the bytes at the P-384 base prime** (six limbs). -/
theorem p384_sqr_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom (Γ := [.fp MontInstances.p384.p, .fp MontInstances.p384.p])
        MontInstances.p384
        (.var ⟨.fieldSquare MontInstances.p384.p, rfl, .cons .here .nil⟩ (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.p384.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.p384 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.p384 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.p384 (x * x) :=
  field2_correct_bytes MontInstances.p384 (by decide) _ (goodVB_sqrProg _) a h sa hreg
    x y hx hy

/-- **The field square at the bytes at the BN254 base prime** (four limbs). -/
theorem bn254_sqr_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom (Γ := [.fp Mont4Instances.bn254.p, .fp Mont4Instances.bn254.p])
        Mont4Instances.bn254
        (.var ⟨.fieldSquare Mont4Instances.bn254.p, rfl, .cons .here .nil⟩ (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.bn254.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.bn254 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.bn254 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.bn254 (x * x) :=
  field2_correct_bytes Mont4Instances.bn254 (by decide) _ (goodVB_sqrProg _) a h sa hreg
    x y hx hy

/-- **The field square at the bytes at the BLS12-381 base prime** (six limbs). -/
theorem bls12381_sqr_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom
        (Γ := [.fp MontInstances.bls12381.p, .fp MontInstances.bls12381.p])
        MontInstances.bls12381
        (.var ⟨.fieldSquare MontInstances.bls12381.p, rfl, .cons .here .nil⟩ (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.bls12381.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.bls12381 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.bls12381 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.bls12381 (x * x) :=
  field2_correct_bytes MontInstances.bls12381 (by decide) _ (goodVB_sqrProg _) a h sa
    hreg x y hx hy

/-! ## 6. The product, sum and difference at BN254 and BLS12-381 -/

/-- **The field product at the bytes at the BN254 base prime** (four limbs). -/
theorem bn254_mul_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.bn254 (mulProg Mont4Instances.bn254.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.bn254.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.bn254 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.bn254 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.bn254 (x * y) :=
  field_correct_bytes Mont4Instances.bn254 (by decide) a h sa hreg x y hx hy

/-- **The field product at the bytes at the BLS12-381 base prime** (six limbs). -/
theorem bls12381_mul_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom MontInstances.bls12381 (mulProg MontInstances.bls12381.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.bls12381.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.bls12381 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.bls12381 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.bls12381 (x * y) :=
  field_correct_bytes MontInstances.bls12381 (by decide) a h sa hreg x y hx hy

/-- **The field sum at the bytes at the BN254 base prime** (four limbs). -/
theorem bn254_add_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom Mont4Instances.bn254 (addProg Mont4Instances.bn254.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.bn254.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.bn254 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.bn254 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.bn254 (x + y) :=
  field2_correct_bytes Mont4Instances.bn254 (by decide) _ (goodVB_addProg _) a h sa hreg
    x y hx hy

/-- **The field sum at the bytes at the BLS12-381 base prime** (six limbs). -/
theorem bls12381_add_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom MontInstances.bls12381 (addProg MontInstances.bls12381.p)))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.bls12381.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.bls12381 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.bls12381 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.bls12381 (x + y) :=
  field2_correct_bytes MontInstances.bls12381 (by decide) _ (goodVB_addProg _) a h sa
    hreg x y hx hy

/-- **The field difference at the bytes at the BN254 base prime** (four limbs). -/
theorem bn254_sub_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 4) a
      (NFProg.ofCom (fieldCom (Γ := [_, _]) Mont4Instances.bn254
        (.var ⟨.fSub Mont4Instances.bn254.p, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 4).Regions sa) (x y : ZMod Mont4Instances.bn254.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.bn254 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.bn254 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 4 → BitVec 64, (fieldAbi2 4).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 4 0 = enc Mont4Instances.bn254 (x - y) :=
  field2_correct_bytes Mont4Instances.bn254 (by decide) _ (goodVB_subProg _) a h sa hreg
    x y hx hy

/-- **The field difference at the bytes at the BLS12-381 base prime** (six limbs). -/
theorem bls12381_sub_correct_bytes (a : AbiNames)
    {P' : Lprog} {bytes : List (BitVec 8)}
    (h : compileRegion (fieldAbi2 6) a
      (NFProg.ofCom (fieldCom (Γ := [_, _]) MontInstances.bls12381
        (.var ⟨.fSub MontInstances.bls12381.p, rfl, .cons .here (.cons (.there .here) .nil)⟩
          (.ret .here))))
      = some (P', bytes))
    (sa : AState) (hreg : (fieldAbi2 6).Regions sa) (x y : ZMod MontInstances.bls12381.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") 6) 6 0 = enc MontInstances.bls12381 x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") 6) 6 0 = enc MontInstances.bls12381 y) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ∃ arr : Fin 6 → BitVec 64, (fieldAbi2 6).ResultOf sa sa' (arrVal arr)
        ∧ arrLimbs arr 6 0 = enc MontInstances.bls12381 (x - y) :=
  field2_correct_bytes MontInstances.bls12381 (by decide) _ (goodVB_subProg _) a h sa
    hreg x y hx hy

/-! ## 7. `fe_mul_add` at the P-256 base prime -/

open CatCrypt.Util (P256)

/-- The Montgomery record that `limbParamsOf` computes at the P-256 base prime is
    `Mont4Instances.p256`. -/
theorem limbParamsOf_p256 : limbParamsOf P256 = some ⟨4, Mont4Instances.p256⟩ := by
  rfl

/-- The P-256 base prime is not recognised as `2 ^ k - c` with `c < 2 ^ 64`. -/
theorem solinasParamsOf_p256 : solinasParamsOf P256 = none := by
  decide

/-- The template of the P-256 base prime is the Montgomery template of
    `Mont4Instances.p256`. -/
theorem fieldTemplateOf_p256 :
    ∃ hn, fieldTemplateOf P256 = some ⟨4, montTemplate Mont4Instances.p256 hn⟩ :=
  fieldTemplateOf_of_mont solinasParamsOf_p256 limbParamsOf_p256

/-- **`field_correct_auto` for `fe_mul_add` at the P-256 base prime**, under the layout
    `fieldAbi 3 4`: the output array in `%rdi` and the operands `a`, `b`, `c` in `%rcx`,
    `%rdx`, `%rsi`, for the route program `q` of the front, the straight-line program `c`
    that `ComL.toCom?` reads from it and a result of `compileRegion` on `NFProg.ofCom c`, the
    call of the row `primeir/fe_mul_add_p256` of `field-bytes-emit`. -/
theorem fe_mul_add_correct_p256 (fname : String) {q : AnyRouteProg}
    (hf : (fieldLeg P256 ["a", "b", "c"]).front (fieldAbi 3 4) Primeir.fe_mul_add_texpr = some q)
    {c : Com jasminDialect q.1 q.2.1} (hcq : q.2.2.com.toCom? = some c)
    (P' : Lprog) (bytes : List (BitVec 8))
    (hc : compileRegion (fieldAbi 3 4) (nfAbiNames fname (fieldAbi 3 4)) (NFProg.ofCom c)
      = some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 3 4).Regions sa) (v : Value)
    (hrun : fieldRuns P256 ["a", "b", "c"] (fieldAbi 3 4) Primeir.fe_mul_add_texpr sa v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 3 4).ResultOf sa sa' v :=
  field_correct_auto P256 _ _ _ fname hf hcq P' bytes hc sa hsep v hrun

open CatCrypt.Crypto.PrimeIR.Fp256Mont (Canon montVal) in
open CatCrypt.Crypto.PrimeIR.FieldModelBridge (fe_mul_add_bridge_fp256Mont) in
/-- **`fe_mul_add` from the surface function to the bytes at the P-256 base prime.** For a
    result `(P', bytes)` of the region back half `compileRegion` on the program `NFProg.ofCom k`
    of the straight-line program `k` of the route program the field front returns on
    `fe_mul_add`, and canonical Montgomery limb
    arrays `a`, `b`, `c` of the surface type: from every entry state `sa` satisfying the
    regions of `fieldAbi 3 4`, whose arrays at `%rcx`, `%rdx`, `%rsi` hold the Montgomery limbs
    of the Montgomery values of `a`, `b`, `c`, with an environment binding `a`, `b`, `c` to
    the representatives of these values, the bytes decode to a program that halts in a state
    from which the layout reads back every word array `arr` whose limbs are the Montgomery
    limbs of the Montgomery value of `fe_mul_add a b c`. -/
theorem fe_mul_add_bytes_p256 [Primeir.PrimeirDeps] (fname : String) {q : AnyRouteProg}
    (hf : (fieldLeg P256 ["a", "b", "c"]).front (fieldAbi 3 4) Primeir.fe_mul_add_texpr = some q)
    {k : Com jasminDialect q.1 q.2.1} (hk : q.2.2.com.toCom? = some k)
    (P' : Lprog) (bytes : List (BitVec 8))
    (hcomp : compileRegion (fieldAbi 3 4) (nfAbiNames fname (fieldAbi 3 4)) (NFProg.ofCom k)
      = some (P', bytes))
    (sa : AState) (hsep : (fieldAbi 3 4).Regions sa) (a b c : Primeir.Fp256Mont_T)
    (ha : Canon a) (hb : Canon b) (hc : Canon c) (env : Env)
    (hea : env "a" = some (.int ((montVal a).val : Int)))
    (heb : env "b" = some (.int ((montVal b).val : Int)))
    (hec : env "c" = some (.int ((montVal c).val : Int)))
    (hxa : arrLimbs (wordsFn sa (sa.regs "%rcx") 4) 4 0 = enc Mont4Instances.p256 (montVal a))
    (hxb : arrLimbs (wordsFn sa (sa.regs "%rdx") 4) 4 0 = enc Mont4Instances.p256 (montVal b))
    (hxc : arrLimbs (wordsFn sa (sa.regs "%rsi") 4) 4 0 = enc Mont4Instances.p256 (montVal c))
    (arr : Fin 4 → BitVec 64)
    (harr : arrLimbs arr 4 0 = enc Mont4Instances.p256 (montVal (Primeir.fe_mul_add a b c))) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ (fieldAbi 3 4).ResultOf sa sa' (arrVal arr) := by
  obtain ⟨hn, hT⟩ := fieldTemplateOf_p256
  obtain ⟨-, env', hrun⟩ := fe_mul_add_bridge_fp256Mont 0 a b c ha hb hc env hea heb hec
  exact fe_mul_add_correct_p256 fname hf hk P' bytes hcomp sa hsep (arrVal arr)
    ⟨4, montTemplate Mont4Instances.p256 hn, hT, rfl,
      .cons (montVal a) (.cons (montVal b) (.cons (montVal c) .nil)),
      montVal (Primeir.fe_mul_add a b c), env, 0, env',
      ⟨hxa, hea, hxb, heb, hxc, hec, trivial⟩, hrun, arr, harr, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldInstances
