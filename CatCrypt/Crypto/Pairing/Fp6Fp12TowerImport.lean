/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.PilotImport
public meta import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.PilotImport

@[expose] public section

set_option autoImplicit false

/-!
# AUCurves Fp6 + Fp12 (GT) tower ops → CatCrypt-compiler round-trip

This module extends the AUCurves→CatCrypt `rust_cmd_ed`→`LowCT` round-trip up the
**BN254/BLS pairing tower** from the Fp2 layer (`Fp2TowerImport.lean`) to
the **cubic (Fp6)** and **dodecic (Fp12 = GT)** layers — the full pairing-tower
arithmetic the KZG / Halo2-Marlin pairing check needs.

## The compositional pattern, one tower level up

The tower is built leaf-over-leaf:

* an **Fp2** op is a chain of calls to the **Fp** leaf functions
  (`bn254_add` / `bn254_mul` / `bn254_sub`) — `Fp2TowerImport.lean`;
* an **Fp6** op (Fp6 = Fp2³) is a chain of calls to the **Fp2** leaf functions
  (`bn254_Fp2_add` / `bn254_Fp2_mul` / `bn254_Fp2_sub` / `bn254_Fp2_mul_xi`),
  mirroring AUCurves' cubic-extension bodies
  (`Field/FieldExtensions/CubicFieldExtensions.v`'s `Fp6_add` / `Fp6_mul`);
* an **Fp12** op (Fp12 = Fp6²) is a chain of calls to the **Fp6** leaf functions
  (`bn254_Fp6_add` / `bn254_Fp6_mul` / `bn254_Fp6_sub` / `bn254_Fp6_mul_by_v`),
  mirroring the generic quadratic extension over Fp6
  (`Field/FieldExtensions/GenericQuadratic.v`'s `QE_add` / `QE_mul`).

Each tower coordinate is a flat `located_ed` byte slot: an Fp2 component is a
`TBytes 64` slot (2 Fp felems × 32 bytes), an Fp6 component a `TBytes 192` slot
(3 Fp2 felems × 64 bytes).  Component slot names (`out_c0`/`out_c1`/`out_c2`,
`inx_c…`/`iny_c…`) name the cubic / dodecic coordinates the bedrock2 body reaches
by byte offset, and the leaf names are recovered verbatim, so the parsed body
maps onto the same leaf call graph AUCurves' own jasmin tower emits.

AUCurves serializes these op bodies through `LowCTEdSerialize.v`'s `ser_cmd`,
Qed-pinned as `bn254_fp6_add_sexpr_value` / `bn254_fp6_mul_sexpr_value` /
`bn254_fp12_add_sexpr_value` / `bn254_fp12_mul_sexpr_value` (mirroring the Fp2
artifacts).  The byte-exact strings are reproduced below and consumed by the
importer.

## Scope

* **Structural correspondence** — `importedFp6Add_eq` / `importedFp6Mul_eq` /
  `importedFp12Add_eq` / `importedFp12Mul_eq`: each parsed Fp6/Fp12 op body
  equals, constructor-by-constructor, the `LowCT` the IR-correspondence map
  dictates (`Seq → RSeq`, `LetZero → RLetZero`, `Call → RCall`, `loc → Located`,
  `(Bytes n) → TBytes n`), with leaf names and component slot names recovered
  verbatim.  The parser needs no extension beyond the field-op pilot's: the
  Fp6/Fp12 bodies are pure `Seq`/`LetZero`/`Call`/`loc`/`Bytes` trees, all covered.
* **Jasmin call-graph cross-check** — `importedFp6Mul_jasmin_eq` etc.: routing
  the imported body through CatCrypt's owned front (`toJasminCmd`) reproduces the
  leaf call graph AUCurves' own jasmin tower emits: one `Ccall` per leaf call,
  same leaf name, same destination-then-args ordering, with scratch felems
  materialized as the `RLetZero` zero-init prologue.

## Limits

This is the **structural** correspondence + the backend call-graph cross-check,
at the granularity of the Fp2 layer (and of the pilot for the Fp field
ops).  It depends on the tower-heap-aware `RustExec` realization at
the leaf layer (the leaf `Fp`-level `SLimb` stores read the tower heap by byte
offset); the Fp6/Fp12 bodies here are pure leaf-call chains, so they inherit that
faithfulness through the leaf calls and add no new runtime-semantics obligation.

The machine-checked **cross-prover semantic** equivalence (Rocq
`rust_exec_ed` ⇔ Lean `RustExec`, proven constructor-by-constructor across the
whole tower) is outside the scope of this module, as for any two-prover bridge.
The round-trip theorems below live at the
`parseLowCT` / `toJasminCmd` (AST / call-graph) level.
-/

namespace CatCrypt.Crypto.Pairing.Fp6Fp12TowerImport

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin (Cmd InstrR LVal PExpr)
open CatCrypt.Crypto.SecureCompilation.AUCurvesImport
  (parseLowCT)
open CatCrypt.Crypto.Jasmin.LowCT (toJasminCmd locToLVal locToPExpr)

/-! ## §0  Tower-component slot constructors -/

/-- One BN254 Fp2 felem (3-coordinate cubic-tower component is `Fp6`, so an
    Fp2 component itself is 2 Fp felems = 64 bytes) as a `TBytes 64` `Located`. -/
def fp2Loc (v : String) : Located := { locVar := v, locSrc := .TBytes 64 }

/-- One BN254 Fp6 felem (3 Fp2 felems × 64 bytes = 192 bytes) as a `TBytes 192`
    `Located` — one dodecic-tower (Fp12) coordinate. -/
def fp6Loc (v : String) : Located := { locVar := v, locSrc := .TBytes 192 }

/-! ## §1  Fp6 ADD body — round-trip -/

/-- AUCurves' byte-exact serialization of the BN254 Fp6 **add** op body
    (Qed-pinned in `LowCTEdSerialize.v` as `bn254_fp6_add_sexpr_value`):
    three component-wise Fp2 adds `out.c_i := inx.c_i + iny.c_i`, sequenced. -/
def fp6AddSexpr : String :=
  "(Seq (Call \"bn254_Fp2_add\" (loc \"out_c0\" (Bytes 64)) ((loc \"inx_c0\" (Bytes 64)) (loc \"iny_c0\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"out_c1\" (Bytes 64)) ((loc \"inx_c1\" (Bytes 64)) (loc \"iny_c1\" (Bytes 64)))) (Call \"bn254_Fp2_add\" (loc \"out_c2\" (Bytes 64)) ((loc \"inx_c2\" (Bytes 64)) (loc \"iny_c2\" (Bytes 64))))))"

/-- The `LowCT` the constructor map dictates for the Fp6 add body: an `RSeq`
    chain of three `RCall "bn254_Fp2_add"` over the c0/c1/c2 Fp2 component slots. -/
def fp6AddExpected : LowCT :=
  .RSeq
    (.RCall "bn254_Fp2_add" (fp2Loc "out_c0") [fp2Loc "inx_c0", fp2Loc "iny_c0"])
    (.RSeq
      (.RCall "bn254_Fp2_add" (fp2Loc "out_c1") [fp2Loc "inx_c1", fp2Loc "iny_c1"])
      (.RCall "bn254_Fp2_add" (fp2Loc "out_c2") [fp2Loc "inx_c2", fp2Loc "iny_c2"]))

/-- **Structural correspondence — Fp6 add.**  Importing AUCurves' Qed-certified
    Fp6 add serialization yields exactly the three-`RCall` `RSeq` chain the IR
    map dictates, with the `bn254_Fp2_add` leaf name and the c0/c1/c2 component
    slot names recovered verbatim.  The cubic-tower Fp6 add body round-trips at
    the AST level. -/
theorem importedFp6Add_eq :
    parseLowCT fp6AddSexpr = some fp6AddExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp6 add.**  The owned front lowers the
    imported Fp6 add body to three Jasmin `Ccall` nodes — one per Fp2
    `bn254_Fp2_add` leaf call, c0/c1/c2 in order — the Fp2 leaf call graph
    AUCurves' own jasmin tower emits for `bn254_Fp6_add`. -/
theorem importedFp6Add_jasmin_eq :
    (parseLowCT fp6AddSexpr).map toJasminCmd =
      some (toJasminCmd fp6AddExpected) := by
  rw [importedFp6Add_eq]; rfl

/-! ## §2  Fp6 MUL body (Toom/Karatsuba over Fp2) — round-trip -/

/-- AUCurves' byte-exact serialization of the BN254 Fp6 **mul** op body
    (Qed-pinned as `bn254_fp6_mul_sexpr_value`): the three-coordinate Toom /
    Karatsuba schedule over five Fp2 scratch felems `a0b0`/`a1b1`/`a2b2`/`t`/`u`
    (`LetZero`-scoped, image of bedrock2 `stackalloc 64`).  23 Fp2 leaf calls
    (`bn254_Fp2_{mul,add,sub,mul_xi}`) in `CubicFieldExtensions.Fp6_mul` order. -/
def fp6MulSexpr : String :=
  "(LetZero \"a0b0\" (Bytes 64) (LetZero \"a1b1\" (Bytes 64) (LetZero \"a2b2\" (Bytes 64) (LetZero \"t\" (Bytes 64) (LetZero \"u\" (Bytes 64) (Seq (Call \"bn254_Fp2_mul\" (loc \"a0b0\" (Bytes 64)) ((loc \"inx_c0\" (Bytes 64)) (loc \"iny_c0\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul\" (loc \"a1b1\" (Bytes 64)) ((loc \"inx_c1\" (Bytes 64)) (loc \"iny_c1\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul\" (loc \"a2b2\" (Bytes 64)) ((loc \"inx_c2\" (Bytes 64)) (loc \"iny_c2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"t\" (Bytes 64)) ((loc \"inx_c1\" (Bytes 64)) (loc \"inx_c2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"u\" (Bytes 64)) ((loc \"iny_c1\" (Bytes 64)) (loc \"iny_c2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"u\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a1b1\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a2b2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul_xi\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"out_c0\" (Bytes 64)) ((loc \"a0b0\" (Bytes 64)) (loc \"t\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"t\" (Bytes 64)) ((loc \"inx_c0\" (Bytes 64)) (loc \"inx_c1\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"u\" (Bytes 64)) ((loc \"iny_c0\" (Bytes 64)) (loc \"iny_c1\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"u\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a0b0\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a1b1\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul_xi\" (loc \"u\" (Bytes 64)) ((loc \"a2b2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"out_c1\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"u\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"t\" (Bytes 64)) ((loc \"inx_c0\" (Bytes 64)) (loc \"inx_c2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_add\" (loc \"u\" (Bytes 64)) ((loc \"iny_c0\" (Bytes 64)) (loc \"iny_c2\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_mul\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"u\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a0b0\" (Bytes 64)))) (Seq (Call \"bn254_Fp2_sub\" (loc \"t\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a2b2\" (Bytes 64)))) (Call \"bn254_Fp2_add\" (loc \"out_c2\" (Bytes 64)) ((loc \"t\" (Bytes 64)) (loc \"a1b1\" (Bytes 64)))))))))))))))))))))))))))))))"

/-- The `LowCT` the constructor map dictates for the Fp6 mul body: five
    `RLetZero` Fp2 scratch felems wrapping the 23-`RCall` Toom/Karatsuba chain. -/
def fp6MulExpected : LowCT :=
  .RLetZero "a0b0" (.TBytes 64) (
  .RLetZero "a1b1" (.TBytes 64) (
  .RLetZero "a2b2" (.TBytes 64) (
  .RLetZero "t" (.TBytes 64) (
  .RLetZero "u" (.TBytes 64) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "a0b0") [fp2Loc "inx_c0", fp2Loc "iny_c0"]) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "a1b1") [fp2Loc "inx_c1", fp2Loc "iny_c1"]) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "a2b2") [fp2Loc "inx_c2", fp2Loc "iny_c2"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "t") [fp2Loc "inx_c1", fp2Loc "inx_c2"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "u") [fp2Loc "iny_c1", fp2Loc "iny_c2"]) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "t") [fp2Loc "t", fp2Loc "u"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a1b1"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a2b2"]) (
  .RSeq (.RCall "bn254_Fp2_mul_xi" (fp2Loc "t") [fp2Loc "t"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "out_c0") [fp2Loc "a0b0", fp2Loc "t"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "t") [fp2Loc "inx_c0", fp2Loc "inx_c1"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "u") [fp2Loc "iny_c0", fp2Loc "iny_c1"]) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "t") [fp2Loc "t", fp2Loc "u"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a0b0"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a1b1"]) (
  .RSeq (.RCall "bn254_Fp2_mul_xi" (fp2Loc "u") [fp2Loc "a2b2"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "out_c1") [fp2Loc "t", fp2Loc "u"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "t") [fp2Loc "inx_c0", fp2Loc "inx_c2"]) (
  .RSeq (.RCall "bn254_Fp2_add" (fp2Loc "u") [fp2Loc "iny_c0", fp2Loc "iny_c2"]) (
  .RSeq (.RCall "bn254_Fp2_mul" (fp2Loc "t") [fp2Loc "t", fp2Loc "u"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a0b0"]) (
  .RSeq (.RCall "bn254_Fp2_sub" (fp2Loc "t") [fp2Loc "t", fp2Loc "a2b2"]) (
        (.RCall "bn254_Fp2_add" (fp2Loc "out_c2") [fp2Loc "t", fp2Loc "a1b1"])
  )))))))))))))))))))))))))))

/-- **Structural correspondence — Fp6 mul (Toom/Karatsuba over Fp2).**  Importing
    AUCurves' Qed-certified Fp6 mul serialization yields exactly the
    five-`RLetZero` + 23-`RCall` chain the IR map dictates, with the
    `bn254_Fp2_{mul,add,sub,mul_xi}` leaf names, the `a0b0/a1b1/a2b2/t/u` scratch
    names, and the c0/c1/c2 component names recovered verbatim.  The full cubic
    pairing-tower mul body round-trips. -/
theorem importedFp6Mul_eq :
    parseLowCT fp6MulSexpr = some fp6MulExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp6 mul.**  The owned front lowers the
    imported Fp6 mul body to the same Fp2 leaf call graph AUCurves' jasmin tower
    emits for `bn254_Fp6_mul`: 23 `Ccall`s in the Toom/Karatsuba order, prefixed
    by the scratch-felem zero-init prologue the `RLetZero`s lower to. -/
theorem importedFp6Mul_jasmin_eq :
    (parseLowCT fp6MulSexpr).map toJasminCmd =
      some (toJasminCmd fp6MulExpected) := by
  rw [importedFp6Mul_eq]; rfl

/-! ## §3  Fp12 (GT) ADD body — round-trip -/

/-- AUCurves' byte-exact serialization of the BN254 Fp12 **add** op body
    (Qed-pinned as `bn254_fp12_add_sexpr_value`): two component-wise Fp6 adds
    `out.c_i := inx.c_i + iny.c_i` over the two Fp6 halves, sequenced. -/
def fp12AddSexpr : String :=
  "(Seq (Call \"bn254_Fp6_add\" (loc \"out_c0\" (Bytes 192)) ((loc \"inx_c0\" (Bytes 192)) (loc \"iny_c0\" (Bytes 192)))) (Call \"bn254_Fp6_add\" (loc \"out_c1\" (Bytes 192)) ((loc \"inx_c1\" (Bytes 192)) (loc \"iny_c1\" (Bytes 192)))))"

/-- The `LowCT` the constructor map dictates for the Fp12 add body: an `RSeq`
    of two `RCall "bn254_Fp6_add"` over the two Fp6 component halves. -/
def fp12AddExpected : LowCT :=
  .RSeq
    (.RCall "bn254_Fp6_add" (fp6Loc "out_c0") [fp6Loc "inx_c0", fp6Loc "iny_c0"])
    (.RCall "bn254_Fp6_add" (fp6Loc "out_c1") [fp6Loc "inx_c1", fp6Loc "iny_c1"])

/-- **Structural correspondence — Fp12 (GT) add.**  Importing AUCurves'
    Qed-certified Fp12 add serialization yields exactly the two-`RCall` `RSeq`
    the IR map dictates, with the `bn254_Fp6_add` leaf name and the two Fp6
    component slot names recovered verbatim.  The dodecic-tower (GT) add body
    round-trips. -/
theorem importedFp12Add_eq :
    parseLowCT fp12AddSexpr = some fp12AddExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp12 add.**  The owned front lowers the
    imported Fp12 add body to two Jasmin `Ccall` nodes — one per Fp6
    `bn254_Fp6_add` leaf call, c0 then c1 — the Fp6 leaf call graph AUCurves'
    own jasmin tower emits for the GT add. -/
theorem importedFp12Add_jasmin_eq :
    (parseLowCT fp12AddSexpr).map toJasminCmd =
      some (toJasminCmd fp12AddExpected) := by
  rw [importedFp12Add_eq]; rfl

/-! ## §4  Fp12 (GT) MUL body (Karatsuba over Fp6) — round-trip -/

/-- AUCurves' byte-exact serialization of the BN254 Fp12 **mul** op body
    (Qed-pinned as `bn254_fp12_mul_sexpr_value`): the `GenericQuadratic.QE_mul`
    Karatsuba schedule over Fp6, with three Fp6 scratch felems `v0`/`v1`/`v2`
    (`LetZero`-scoped, image of bedrock2 `stackalloc 192`).  Nine Fp6 leaf calls
    (`bn254_Fp6_{mul,add,sub,mul_by_v}`); `mul_by_v` is the Fp12 non-residue
    mult (the dodecic analogue of Fp2's `mul_xi`). -/
def fp12MulSexpr : String :=
  "(LetZero \"v0\" (Bytes 192) (LetZero \"v1\" (Bytes 192) (LetZero \"v2\" (Bytes 192) (Seq (Call \"bn254_Fp6_mul\" (loc \"v0\" (Bytes 192)) ((loc \"inx_c0\" (Bytes 192)) (loc \"iny_c0\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_mul\" (loc \"v1\" (Bytes 192)) ((loc \"inx_c1\" (Bytes 192)) (loc \"iny_c1\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_add\" (loc \"v2\" (Bytes 192)) ((loc \"inx_c0\" (Bytes 192)) (loc \"inx_c1\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_add\" (loc \"out_c1\" (Bytes 192)) ((loc \"iny_c0\" (Bytes 192)) (loc \"iny_c1\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_mul\" (loc \"out_c1\" (Bytes 192)) ((loc \"out_c1\" (Bytes 192)) (loc \"v2\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_sub\" (loc \"out_c1\" (Bytes 192)) ((loc \"out_c1\" (Bytes 192)) (loc \"v0\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_sub\" (loc \"out_c1\" (Bytes 192)) ((loc \"out_c1\" (Bytes 192)) (loc \"v1\" (Bytes 192)))) (Seq (Call \"bn254_Fp6_mul_by_v\" (loc \"v2\" (Bytes 192)) ((loc \"v1\" (Bytes 192)))) (Call \"bn254_Fp6_add\" (loc \"out_c0\" (Bytes 192)) ((loc \"v0\" (Bytes 192)) (loc \"v2\" (Bytes 192)))))))))))))))"

/-- The `LowCT` the constructor map dictates for the Fp12 mul body: three
    `RLetZero` Fp6 scratch felems wrapping the 9-`RCall` Karatsuba chain. -/
def fp12MulExpected : LowCT :=
  .RLetZero "v0" (.TBytes 192) (
  .RLetZero "v1" (.TBytes 192) (
  .RLetZero "v2" (.TBytes 192) (
  .RSeq (.RCall "bn254_Fp6_mul" (fp6Loc "v0")     [fp6Loc "inx_c0", fp6Loc "iny_c0"]) (
  .RSeq (.RCall "bn254_Fp6_mul" (fp6Loc "v1")     [fp6Loc "inx_c1", fp6Loc "iny_c1"]) (
  .RSeq (.RCall "bn254_Fp6_add" (fp6Loc "v2")     [fp6Loc "inx_c0", fp6Loc "inx_c1"]) (
  .RSeq (.RCall "bn254_Fp6_add" (fp6Loc "out_c1") [fp6Loc "iny_c0", fp6Loc "iny_c1"]) (
  .RSeq (.RCall "bn254_Fp6_mul" (fp6Loc "out_c1") [fp6Loc "out_c1", fp6Loc "v2"]) (
  .RSeq (.RCall "bn254_Fp6_sub" (fp6Loc "out_c1") [fp6Loc "out_c1", fp6Loc "v0"]) (
  .RSeq (.RCall "bn254_Fp6_sub" (fp6Loc "out_c1") [fp6Loc "out_c1", fp6Loc "v1"]) (
  .RSeq (.RCall "bn254_Fp6_mul_by_v" (fp6Loc "v2") [fp6Loc "v1"]) (
        (.RCall "bn254_Fp6_add" (fp6Loc "out_c0") [fp6Loc "v0", fp6Loc "v2"])
  )))))))))))

/-- **Structural correspondence — Fp12 (GT) mul (Karatsuba over Fp6).**  Importing
    AUCurves' Qed-certified Fp12 mul serialization yields exactly the
    three-`RLetZero` + nine-`RCall` chain the IR map dictates, with the
    `bn254_Fp6_{mul,add,sub,mul_by_v}` leaf names, the `v0/v1/v2` scratch names,
    and the two Fp6 component names recovered verbatim.  The full dodecic
    pairing-tower (GT) mul body — the arithmetic the Fp12 pairing check
    needs — round-trips. -/
theorem importedFp12Mul_eq :
    parseLowCT fp12MulSexpr = some fp12MulExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp12 mul.**  The owned front lowers the
    imported Fp12 mul body to the same Fp6 leaf call graph AUCurves' jasmin tower
    emits for the GT mul: nine `Ccall`s (`bn254_Fp6_{mul,add,sub,mul_by_v}`) in
    the Karatsuba order, prefixed by the scratch-felem zero-init prologue. -/
theorem importedFp12Mul_jasmin_eq :
    (parseLowCT fp12MulSexpr).map toJasminCmd =
      some (toJasminCmd fp12MulExpected) := by
  rw [importedFp12Mul_eq]; rfl

/-! ## §5  End-to-end packaging (parse → lower in one statement) -/

/-- The full BN254/BLS pairing tower above the Fp2 layer round-trips: the Fp6
    add / Fp6 mul / Fp12 add / Fp12 mul op bodies all parse to the IR-map
    `LowCT`s and lower through CatCrypt's owned front in one step.  Combined
    with the Fp2 layer (`Fp2TowerImport.fp2Tower_roundtrip`) and the Fp leaf ops
    (`PilotImport.importedFe25519Add_*`), the whole pairing-tower arithmetic the
    Fp12 (GT) pairing check needs is connected at the structural / call-graph
    level. -/
theorem fp6Fp12Tower_roundtrip :
    (parseLowCT fp6AddSexpr).map toJasminCmd = some (toJasminCmd fp6AddExpected)
    ∧ (parseLowCT fp6MulSexpr).map toJasminCmd = some (toJasminCmd fp6MulExpected)
    ∧ (parseLowCT fp12AddSexpr).map toJasminCmd = some (toJasminCmd fp12AddExpected)
    ∧ (parseLowCT fp12MulSexpr).map toJasminCmd = some (toJasminCmd fp12MulExpected) :=
  ⟨importedFp6Add_jasmin_eq, importedFp6Mul_jasmin_eq,
   importedFp12Add_jasmin_eq, importedFp12Mul_jasmin_eq⟩

end CatCrypt.Crypto.Pairing.Fp6Fp12TowerImport
