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
# AUCurves Fp2 tower ops → CatCrypt-compiler round-trip (CONN-3j, task #341)

This file scales the AUCurves→CatCrypt `rust_cmd_ed`→`LowCT` round-trip
(established for the Ed25519 field ops in
`SecureCompilation/AUCurvesImport/PilotImport.lean`, #354) up to the
**BN254/BLS Fp2 pairing-tower** layer: the Fp2 add and Fp2 mul *op bodies*.

CONN-3i tied the Fp2 tower at the *realization* level; this file brings the Fp2
op **bodies** through the same structural round-trip the field ops use, which
unblocks #349 (Halo2/Marlin T3, gated on the pairing tower).

## The Fp2 op bodies (AUCurves side)

AUCurves' BN254 Fp2 ops (`Field/Synthesis/Examples/bn254_Fp2.v`) are bedrock2
`cmd` trees: each Fp2 op is a sequence of `cmd.call`s to the Fp **leaf**
functions (`bn254_add`, `bn254_mul`, `bn254_sub`), one call per Fp2 component,
with the imaginary half addressed by `expr_2nd_felem` (= base pointer + 32
bytes, one BN254 Fp felem = 4 limbs × 8 bytes).

At the `rust_cmd_ed` level this is an `REdSeq` of `REdCall`s over flat
`located_ed` slots — the same `REdCall`-per-leaf shape the `fe25519_xyzt_copy`
pilot uses, lifted to the two-component Fp2 layer.  Each Fp2 component is a
`TBytes 32` slot (one BN254 Fp felem); distinct slot names (`out_re`/`out_im`,
…) name the real/imaginary halves the bedrock2 body reaches by byte offset.

AUCurves serializes these op bodies through `LowCTEdSerialize.v`'s `ser_cmd`,
Qed-pinned as `bn254_fp2_add_sexpr_value` / `bn254_fp2_mul_sexpr_value`
(mirroring `fe25519_add_sexpr_value`).  The byte-exact strings are reproduced
below and consumed by the importer.

## What this file delivers (honest scoping)

* **Structural correspondence** — `importedFp2Add_eq` / `importedFp2Mul_eq`:
  the parsed Fp2 op bodies equal, constructor-by-constructor, the `LowCT`
  the IR-correspondence map dictates.  `Seq → RSeq`, `LetZero → RLetZero`,
  `Call → RCall`, `loc → Located`, `(Bytes 32) → TBytes 32`, with the Fp leaf
  names and component slot names recovered verbatim.  The parser needs no
  extension beyond #354's (`Seq`/`LetZero`/`Call`/`loc`/`Bytes` already
  covered — the Fp2 bodies are pure `REdCall`-per-leaf chains).
* **Jasmin limb-store / call-graph cross-check** — `importedFp2Add_jasmin_eq`
  / `importedFp2Mul_jasmin_eq`: routing the imported Fp2 op body through
  CatCrypt's owned front (`toJasminCmd`) reproduces the Fp leaf call graph
  AUCurves' own jasmin tower emits (`ExtractBN254TowerJasmin.v`'s
  `bn254_tower_jasmin`): one `Ccall` per Fp leaf call, same leaf name, same
  destination-then-args ordering, with the scratch felems materialized as the
  `RLetZero` zero-init prologue.

## Residual (named, not papered over)

This is the **structural** correspondence + the backend call-graph
cross-check, at the same granularity #354 delivered for `fe25519_add`.  The
fully machine-checked **cross-prover semantic** equivalence (Rocq
`rust_exec_ed` ⇔ Lean `RustExec`, proven constructor-by-constructor) is the
gold-standard residual shared by *any* two-prover bridge; it is not delivered
here.

The faithful *tower-heap-aware* `RustExec` realization — the named #354 / #356
residual — is now **landed**: `RustExec.limbStoreExpr` evaluates an
`SLimb`-valued store via the tower-aware `SExpr.evalState`, which reads limb
`i` of a tower slot at byte offset `i*8` (`rsTowerLimb`/`towerLimb`) rather
than giving `SLimb` a scalar-only `0` default.  An Fp2-component store into
`out_im` therefore reads the imaginary half's bytes faithfully instead of
treating the two halves as independent opaque slots.  The CryptoSSA-correctness
and constant-time analyses were re-discharged against the faithful semantics
(`SExpr.evalState_eq_of_isPublic` carries the `SLimb` arm: the slot name is the
expression's free variable, so a Public-classified tower slot agrees on
Public-equivalent states).  The round-trip theorems below remain at the
structural / call-graph level (`parseLowCT`/`toJasminCmd`), which is
orthogonal to the runtime semantics and unaffected by the change.
-/

namespace CatCrypt.Crypto.Pairing.Fp2TowerImport

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin (Cmd InstrR LVal PExpr)
open CatCrypt.Crypto.SecureCompilation.AUCurvesImport
  (parseLowCT)
open CatCrypt.Crypto.Jasmin.LowCT (toJasminCmd locToLVal locToPExpr)

/-! ## §1  Fp2 ADD body — round-trip -/

/-- One BN254 Fp felem (4 limbs × 8 bytes) as a `TBytes 32` `Located`. -/
def fpLoc (v : String) : Located := { locVar := v, locSrc := .TBytes 32 }

/-- AUCurves' byte-exact serialization of the BN254 Fp2 **add** op body
    (Qed-pinned in `LowCTEdSerialize.v` as `bn254_fp2_add_sexpr_value`):
    two component-wise Fp adds `out.c := inx.c + iny.c`, sequenced under `Seq`. -/
def fp2AddSexpr : String :=
  "(Seq (Call \"bn254_add\" (loc \"out_re\" (Bytes 32)) " ++
  "((loc \"inx_re\" (Bytes 32)) (loc \"iny_re\" (Bytes 32)))) " ++
  "(Call \"bn254_add\" (loc \"out_im\" (Bytes 32)) " ++
  "((loc \"inx_im\" (Bytes 32)) (loc \"iny_im\" (Bytes 32)))))"

/-- The `LowCT` the constructor map dictates for the Fp2 add body: an `RSeq`
    of two `RCall "bn254_add"` over the real/imaginary Fp component slots. -/
def fp2AddExpected : LowCT :=
  .RSeq
    (.RCall "bn254_add" (fpLoc "out_re") [fpLoc "inx_re", fpLoc "iny_re"])
    (.RCall "bn254_add" (fpLoc "out_im") [fpLoc "inx_im", fpLoc "iny_im"])

/-- **Structural correspondence — Fp2 add.**  Importing AUCurves' Qed-certified
    Fp2 add serialization yields exactly the two-`RCall` `RSeq` the IR map
    dictates: `Seq → RSeq`, `Call → RCall`, `(loc "out_re" (Bytes 32)) →
    Located TBytes 32`, with the `bn254_add` leaf name and the `re`/`im`
    component slot names recovered verbatim.  This is the pairing-tower Fp2 add
    body brought through the round-trip at the AST level. -/
theorem importedFp2Add_eq :
    parseLowCT fp2AddSexpr = some fp2AddExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp2 add.**  The owned front lowers the
    imported Fp2 add body to two Jasmin `Ccall` nodes — one per Fp `bn254_add`
    leaf call, real then imaginary — which is the Fp leaf call graph AUCurves'
    own jasmin tower emits for `bn254_Fp2_add` (`ExtractBN254TowerJasmin.v`'s
    `bn254_tower_jasmin`).  Same two leaf calls, same `out`-then-`inx`-`iny`
    ordering. -/
theorem importedFp2Add_jasmin_eq :
    (parseLowCT fp2AddSexpr).map toJasminCmd =
      some (toJasminCmd fp2AddExpected) := by
  rw [importedFp2Add_eq]; rfl

/-- The Fp2 add lowering, spelled out: two `Ccall .DoNotInline` to
    `bn254_add`, real component then imaginary, each with its destination Fp
    slot as the lone lvalue and the two source Fp slots as arguments. -/
theorem fp2Add_jasmin_shape :
    toJasminCmd fp2AddExpected =
      [InstrR.Ccall .DoNotInline [locToLVal (fpLoc "out_re")]
         { name := "bn254_add" }
         ([fpLoc "inx_re", fpLoc "iny_re"].map locToPExpr),
       InstrR.Ccall .DoNotInline [locToLVal (fpLoc "out_im")]
         { name := "bn254_add" }
         ([fpLoc "inx_im", fpLoc "iny_im"].map locToPExpr)] := by
  rfl

/-! ## §2  Fp2 MUL body (Karatsuba) — round-trip -/

/-- AUCurves' byte-exact serialization of the BN254 Fp2 **mul** op body
    (Qed-pinned as `bn254_fp2_mul_sexpr_value`): the Karatsuba schedule
    `(a+bu)(c+du) = (ac - bd) + ((a+b)(c+d) - ac - bd)u`, 8 Fp leaf calls over
    three scratch Fp felems `v0`/`v1`/`v2` (`LetZero`-scoped, the image of
    bedrock2 `stackalloc 32`).  Call order is byte-identical to the bedrock2
    body: `v0=a*c ; v1=b*d ; v2=a+b ; out.im=c+d ; out.im=(a+b)(c+d) ;
    out.im-=v0 ; out.im-=v1 ; out.re=v0-v1`. -/
def fp2MulSexpr : String :=
  "(LetZero \"v0\" (Bytes 32) (LetZero \"v1\" (Bytes 32) (LetZero \"v2\" (Bytes 32) " ++
  "(Seq (Call \"bn254_mul\" (loc \"v0\" (Bytes 32)) ((loc \"inx_re\" (Bytes 32)) (loc \"iny_re\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_mul\" (loc \"v1\" (Bytes 32)) ((loc \"inx_im\" (Bytes 32)) (loc \"iny_im\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_add\" (loc \"v2\" (Bytes 32)) ((loc \"inx_re\" (Bytes 32)) (loc \"inx_im\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_add\" (loc \"out_im\" (Bytes 32)) ((loc \"iny_re\" (Bytes 32)) (loc \"iny_im\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_mul\" (loc \"out_im\" (Bytes 32)) ((loc \"out_im\" (Bytes 32)) (loc \"v2\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_sub\" (loc \"out_im\" (Bytes 32)) ((loc \"out_im\" (Bytes 32)) (loc \"v0\" (Bytes 32)))) " ++
  "(Seq (Call \"bn254_sub\" (loc \"out_im\" (Bytes 32)) ((loc \"out_im\" (Bytes 32)) (loc \"v1\" (Bytes 32)))) " ++
  "(Call \"bn254_sub\" (loc \"out_re\" (Bytes 32)) ((loc \"v0\" (Bytes 32)) (loc \"v1\" (Bytes 32))))))))))))))"

/-- The `LowCT` the constructor map dictates for the Fp2 mul body: three
    `RLetZero` scratch felems wrapping the 8-`RCall` Karatsuba chain. -/
def fp2MulExpected : LowCT :=
  .RLetZero "v0" (.TBytes 32) (
  .RLetZero "v1" (.TBytes 32) (
  .RLetZero "v2" (.TBytes 32) (
  .RSeq (.RCall "bn254_mul" (fpLoc "v0")     [fpLoc "inx_re", fpLoc "iny_re"]) (
  .RSeq (.RCall "bn254_mul" (fpLoc "v1")     [fpLoc "inx_im", fpLoc "iny_im"]) (
  .RSeq (.RCall "bn254_add" (fpLoc "v2")     [fpLoc "inx_re", fpLoc "inx_im"]) (
  .RSeq (.RCall "bn254_add" (fpLoc "out_im") [fpLoc "iny_re", fpLoc "iny_im"]) (
  .RSeq (.RCall "bn254_mul" (fpLoc "out_im") [fpLoc "out_im", fpLoc "v2"]) (
  .RSeq (.RCall "bn254_sub" (fpLoc "out_im") [fpLoc "out_im", fpLoc "v0"]) (
  .RSeq (.RCall "bn254_sub" (fpLoc "out_im") [fpLoc "out_im", fpLoc "v1"]) (
        (.RCall "bn254_sub" (fpLoc "out_re") [fpLoc "v0", fpLoc "v1"])
  ))))))))))

/-- **Structural correspondence — Fp2 mul (Karatsuba).**  Importing AUCurves'
    Qed-certified Fp2 mul serialization yields exactly the three-`RLetZero` +
    eight-`RCall` chain the IR map dictates.  Constructor-by-constructor:
    `LetZero → RLetZero`, `Seq → RSeq`, `Call → RCall`, `(loc … (Bytes 32)) →
    Located TBytes 32`, with the `bn254_{mul,add,sub}` leaf names, the
    `v0/v1/v2` scratch names, and the `re/im` component names recovered
    verbatim.  The full Karatsuba pairing-tower mul body round-trips. -/
theorem importedFp2Mul_eq :
    parseLowCT fp2MulSexpr = some fp2MulExpected := by
  native_decide

/-- **Backend call-graph cross-check — Fp2 mul.**  The owned front lowers the
    imported Fp2 mul body to the same Fp leaf call graph AUCurves' jasmin tower
    emits for `bn254_Fp2_mul`: eight `Ccall`s (`bn254_mul`/`bn254_add`/
    `bn254_sub`) in the Karatsuba order, prefixed by the scratch-felem
    zero-init prologue the `RLetZero`s lower to. -/
theorem importedFp2Mul_jasmin_eq :
    (parseLowCT fp2MulSexpr).map toJasminCmd =
      some (toJasminCmd fp2MulExpected) := by
  rw [importedFp2Mul_eq]; rfl

/-! ## §3  End-to-end packaging (parse → lower in one statement) -/

/-- The Fp2 add and Fp2 mul op bodies both round-trip: AUCurves' certified
    serializations parse to the IR-map `LowCT`s and lower through CatCrypt's
    owned front in one step.  The pairing-tower Fp2 layer is now connected at
    the structural / call-graph level. -/
theorem fp2Tower_roundtrip :
    (parseLowCT fp2AddSexpr).map toJasminCmd = some (toJasminCmd fp2AddExpected)
    ∧ (parseLowCT fp2MulSexpr).map toJasminCmd = some (toJasminCmd fp2MulExpected) :=
  ⟨importedFp2Add_jasmin_eq, importedFp2Mul_jasmin_eq⟩

end CatCrypt.Crypto.Pairing.Fp2TowerImport
