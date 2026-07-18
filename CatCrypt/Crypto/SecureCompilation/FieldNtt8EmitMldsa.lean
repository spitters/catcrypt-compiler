/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Byte-correct 8-point forward NTT over `F_q` (`q = 8380417`, ML-DSA), OWNED x86

The ML-DSA / Dilithium sibling of `FieldNtt8EmitQ.lean` (`q = 3329`): a COMPLETE
8-point radix-2 decimation-in-time (DIT) forward NTT built by composing twelve
Cooley–Tukey butterflies (3 layers × 4). The prime `q = 8380417 = 2^23 − 2^13 + 1`
is ~23-bit, so the twiddle multiply uses **Montgomery** reduction (a single Barrett
mul overflows the modular range); the Montgomery REDC word block is the same as
`FieldMulEmitMldsa.mulBody`.

`ntt8MldsaCom` is FRONT-GENERATED through `translateDialectControl` +
`cryptoDialectToJasminCom` from a covered `LowCT` body — no jasminc, no hand-`Com`.

## Montgomery convention (the KAT depends on it)

`montmul(w, b) = (w · b · R⁻¹) mod q`, `R = 2^32`, `R⁻¹ = 8265825`. Inputs, outputs,
and twiddles are in the Montgomery domain: a twiddle `ζ` is supplied as `ζR mod q`,
and the unit twiddle `ω⁰` is the **Montgomery one** `R mod q = 4193792` (NOT plain 1).
Twiddle Montgomery values: `ω⁰R = 4193792`, `ω¹R = 5771523`, `ω²R = 25847`,
`ω³R = 7861508`. Schedule (same as the `q = 3329` sibling): L1 all `ω⁰`; L2
`ω⁰,ω⁰,ω²,ω²`; L3 `ω⁰,ω²,ω¹,ω³`.

## ABI

`extern void ntt8_mldsa(uint64_t *out, const uint64_t *inp);` — `inp[0..7] = x0..x7`
(Montgomery residues in `[0,q)`), `out[0..7] = y0..y7`. `RDI = out`, `RSI = inp`,
`abiW := 64`. Validated byte-for-byte by `bench/field_kernel_compare/ntt8_mldsa_kat.c`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldNtt8EmitMldsa

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi InLoadMap OutStoreMap Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)

/-- The `reg 64` dialect type. -/
abbrev r64 : JasminTy := .reg 64

/-- Number of input words loaded from `inp`: `x0..x7`. -/
abbrev NIN : Nat := 8

/-! ## 1. The straight-line `LowCT` body (Montgomery butterflies) -/

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Branch-free conditional subtract into `dst` (correct for `src < 2q`):
    `dst_s := src − q;  dst := dst_s + (q & (0 − (dst_s >>> 63)))`, `q = 8380417`. -/
def csubStmts (dst src : String) : List LowCT := [
  .RScalarSetExpr (dst ++ "_s") (.SSub (.SVar src) (.SLit 8380417)),
  .RScalarSetExpr dst
    (.SAdd (.SVar (dst ++ "_s"))
      (.SAnd (.SLit 8380417)
        (.SSub (.SLit 0) (.SShr (.SVar (dst ++ "_s")) (.SLit 63))))) ]

/-- `dst := montmul(w, b) = (w·b·R⁻¹) mod q` where `w` is an `SExpr` twiddle
    literal and `b` a variable: Montgomery REDC (`FieldMulEmitMldsa.mulBody`) then
    one csub. `prod := w·b; mraw := prod·qinvNeg; m := mraw & mask32; mq := m·q;
    sum := prod + mq; t := sum >>> 32; dst := csub(t)`. -/
def mulModStmtsE (dst : String) (w : SExpr) (b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_prod") (.SMul w (.SVar b)),
    .RScalarSetExpr (dst ++ "_mraw") (.SMul (.SVar (dst ++ "_prod")) (.SLit 4236238847)),
    .RScalarSetExpr (dst ++ "_m")    (.SAnd (.SVar (dst ++ "_mraw")) (.SLit 4294967295)),
    .RScalarSetExpr (dst ++ "_mq")   (.SMul (.SVar (dst ++ "_m")) (.SLit 8380417)),
    .RScalarSetExpr (dst ++ "_sum")  (.SAdd (.SVar (dst ++ "_prod")) (.SVar (dst ++ "_mq"))),
    .RScalarSetExpr (dst ++ "_t")    (.SShr (.SVar (dst ++ "_sum")) (.SLit 32)) ]
  ++ csubStmts dst (dst ++ "_t")

/-- `dst := (a + b) mod q`: `a + b` then one csub. -/
def addModStmts (dst a b : String) : List LowCT :=
  .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar b)) :: csubStmts dst (dst ++ "_u")

/-- `dst := (a − b) mod q`: `a + (q − b)` then one csub. -/
def subModStmts (dst a b : String) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "_d") (.SSub (.SLit 8380417) (.SVar b)),
    .RScalarSetExpr (dst ++ "_u") (.SAdd (.SVar a) (.SVar (dst ++ "_d"))) ]
  ++ csubStmts dst (dst ++ "_u")

/-- One full butterfly `(up, lo) := (a + montmul(w,b), a − montmul(w,b)) mod q`. -/
def bflyStmts (up lo a b : String) (w : SExpr) : List LowCT :=
  mulModStmtsE (up ++ "_t") w b ++
  addModStmts up a (up ++ "_t") ++
  subModStmts lo a (up ++ "_t")

/-- **The whole 8-point forward-NTT body as one `LowCT` `RSeq` chain**: twelve
    DIT butterflies (Montgomery twiddles `4193792 / 25847 / 5771523 / 7861508`),
    then eight trailing output copies `o0 := y0, …, o7 := y7`. -/
def ntt8MldsaBody : LowCT := seqAll (
  bflyStmts "a0" "a4" "x0" "x4" (.SLit 4193792) ++
  bflyStmts "a1" "a5" "x1" "x5" (.SLit 4193792) ++
  bflyStmts "a2" "a6" "x2" "x6" (.SLit 4193792) ++
  bflyStmts "a3" "a7" "x3" "x7" (.SLit 4193792) ++
  bflyStmts "b0" "b2" "a0" "a2" (.SLit 4193792) ++
  bflyStmts "b1" "b3" "a1" "a3" (.SLit 4193792) ++
  bflyStmts "b4" "b6" "a4" "a6" (.SLit 25847) ++
  bflyStmts "b5" "b7" "a5" "a7" (.SLit 25847) ++
  bflyStmts "y0" "y1" "b0" "b1" (.SLit 4193792) ++
  bflyStmts "y2" "y3" "b2" "b3" (.SLit 25847) ++
  bflyStmts "y4" "y5" "b4" "b5" (.SLit 5771523) ++
  bflyStmts "y6" "y7" "b6" "b7" (.SLit 7861508) ++
  [ .RScalarSetExpr "o0" (.SVar "y0"),
    .RScalarSetExpr "o1" (.SVar "y1"),
    .RScalarSetExpr "o2" (.SVar "y2"),
    .RScalarSetExpr "o3" (.SVar "y3"),
    .RScalarSetExpr "o4" (.SVar "y4"),
    .RScalarSetExpr "o5" (.SVar "y5"),
    .RScalarSetExpr "o6" (.SVar "y6"),
    .RScalarSetExpr "o7" (.SVar "y7") ])

/-! ## 2. Source context + `VarMap` -/

/-- The source context: 8 `u64` scalar slots (the 8 real inputs). -/
def srcCtx : Ctx := List.replicate NIN (.sword 64)

/-- The source `VarMap`: word 7 (`x7`) bound first (deepest), word 0 (`x0`) last. -/
def srcVM : VarMap srcCtx :=
  (((((((VarMap.empty.bind "x7").bind "x6").bind "x5").bind "x4").bind
      "x3").bind "x2").bind "x1").bind "x0"

/-! ## 3. The front-emitted program -/

/-- Push `ntt8MldsaBody` through the front and cap with `ret <name>`. -/
def frontComAt (name : String) : Option (Com catCryptDialect srcCtx (.sword 64)) :=
  match translateDialectControl srcVM ntt8MldsaBody with
  | some r =>
      match r.vm.lookup name with
      | some ⟨.sword 64, v⟩ => r.cont (Com.ret (toVIRVar v))
      | _ => none
  | none => none

/-- The front-emitted NTT lowered to the jasmin dialect (capped at `o7`). -/
def ntt8MldsaLoweredOpt :=
  (frontComAt "o7").bind DialectToJasminCom.cryptoDialectToJasminCom

/-- The front translates and lowers end-to-end. -/
theorem ntt8MldsaLowered_isSome : ntt8MldsaLoweredOpt.isSome := by native_decide

/-- The input context of the `Com`: the 8 `r64` input words `[x0..x7]`. -/
abbrev inCtxt : Ctxt jasminDialect := List.replicate NIN r64

/-- **The whole 8-point forward-NTT kernel as a `Com jasminDialect`** —
    FRONT-GENERATED, not hand-built. -/
def ntt8MldsaCom : Com jasminDialect inCtxt r64 :=
  ntt8MldsaLoweredOpt.get ntt8MldsaLowered_isSome

/-- **Provenance**: the front pipeline is DEFINITIONALLY the deployed `Com`. -/
theorem ntt8MldsaCom_provenance :
    (frontComAt "o7").bind DialectToJasminCom.cryptoDialectToJasminCom
      = some ntt8MldsaCom :=
  (Option.some_get ntt8MldsaLowered_isSome).symm

/-! ## 4. The ABI maps -/

/-- Input-load map: argument slot → `(base, byte-offset)`. Input word
    `i = (NIN−1) − slot` from `inp[i]` at byte offset `8·i`. -/
def inLoadMap : InLoadMap := fun slot =>
  if slot ≤ NIN - 1 then some ("RSI", ((NIN - 1) - slot) * 8) else none

/-- Output-store map: eight stores `y0..y7` to `out[0..7]` at `u64` offsets. -/
def outStoreMap : OutStoreMap :=
  [("RDI", 0), ("RDI", 8), ("RDI", 16), ("RDI", 24),
   ("RDI", 32), ("RDI", 40), ("RDI", 48), ("RDI", 56)]

/-! ## 5. The owned `Lprog` and rendered `.s` -/

/-- The `ntt8_mldsa` kernel as an owned-RA two-address `Lprog`. -/
def ntt8MldsaLprog : Lprog :=
  Com.toLprogPhysAbi ntt8MldsaCom "ntt8_mldsa"
    (fun _ => none) (fun _ => none) inLoadMap outStoreMap
    (abiArgs := ["RDI", "RSI"]) (abiTyin := [64, 64]) (residence := none)
    (abiW := 64)

/-- The owned AT&T `.s` text for `ntt8_mldsa`. -/
def ntt8MldsaOwnedAsm : String := renderLprogAtt ntt8MldsaLprog

/-- The output path for the field-kernel-emitted `.s`. -/
def ntt8MldsaTarget : System.FilePath :=
  "bench/field_kernel_compare/gen_com/ntt8_mldsa.s"

/-- **The byte-correct ML-DSA 8-point-NTT owned-emit driver.** -/
def emitNtt8Mldsa : IO Unit := do
  IO.FS.createDirAll "bench/field_kernel_compare/gen_com"
  let asm := ntt8MldsaOwnedAsm
  IO.FS.writeFile ntt8MldsaTarget asm
  IO.println s!"FIELD-NTT8-MLDSA emit OK : {ntt8MldsaTarget} ({asm.toUTF8.size} bytes, symbol ntt8_mldsa)"

/-- One owned function emitted, named `ntt8_mldsa`. -/
theorem ntt8Mldsa_one_func :
    ntt8MldsaLprog.lp_funcs.length = 1
      ∧ ntt8MldsaLprog.lp_funcs.head?.map Prod.fst = some "ntt8_mldsa" :=
  ⟨rfl, rfl⟩

/-! ## 6. Independent plain-`Nat` `% 8380417` Montgomery reference

Self-consistent with the emitted word blocks (`montmul(w,b) = (w·b·R⁻¹) mod q`,
`R⁻¹ = 8265825`, twiddles in Montgomery form) and byte-checked against the C
harness `ntt8_mldsa_kat.c` (which the byte-KAT gates). -/

/-- Independent Montgomery `F_q` multiply: `(a·b·R⁻¹) % q`. -/
def fqMontMulNat (a b : Nat) : Nat := (a * b * 8265825) % 8380417

/-- Independent `F_q` add: `(a+b) % q`. -/
def fqAddNat (a b : Nat) : Nat := (a + b) % 8380417

/-- Independent `F_q` subtract: `(a + q − (b % q)) % q`. -/
def fqSubNat (a b : Nat) : Nat := (a + 8380417 - b % 8380417) % 8380417

/-- Independent stepwise Montgomery butterfly. -/
def bflyNat (a b w : Nat) : Nat × Nat :=
  let t := fqMontMulNat w b
  (fqAddNat a t, fqSubNat a t)

/-- **Independent plain-`Nat` `% 8380417` Montgomery 8-point DIT forward NTT.** -/
def ntt8MldsaNatRef (g : Nat → Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let x0 := g 0 % 8380417; let x1 := g 1 % 8380417; let x2 := g 2 % 8380417
  let x3 := g 3 % 8380417; let x4 := g 4 % 8380417; let x5 := g 5 % 8380417
  let x6 := g 6 % 8380417; let x7 := g 7 % 8380417
  let (a0, a4) := bflyNat x0 x4 4193792
  let (a1, a5) := bflyNat x1 x5 4193792
  let (a2, a6) := bflyNat x2 x6 4193792
  let (a3, a7) := bflyNat x3 x7 4193792
  let (b0, b2) := bflyNat a0 a2 4193792
  let (b1, b3) := bflyNat a1 a3 4193792
  let (b4, b6) := bflyNat a4 a6 25847
  let (b5, b7) := bflyNat a5 a7 25847
  let (y0, y1) := bflyNat b0 b1 4193792
  let (y2, y3) := bflyNat b2 b3 25847
  let (y4, y5) := bflyNat b4 b5 5771523
  let (y6, y7) := bflyNat b6 b7 7861508
  (y0, y1, y2, y3, y4, y5, y6, y7)

end CatCrypt.Crypto.SecureCompilation.FieldNtt8EmitMldsa
