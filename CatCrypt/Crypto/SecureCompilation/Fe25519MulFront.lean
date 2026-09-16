/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront

@[expose] public section

set_option autoImplicit false

/-!
# Curve25519 field multiply `fe25519_mul` (256×256 → 256 mod `2^255 − 19`), front-compiled

A 4-limb Curve25519 field multiply `out = (a · b) mod p`, `p = 2^255 − 19`,
sourced as a `LowCT` body and carried to owned x86 by the verified descent:

```
  feMulBody (LowCT: RArrLoad / RScalarSetExpr limb math / RArrStore)
    --(translateDialectControl)--> Com catCryptDialect inΓ (.memref 4)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …
    --(Com.toLprogPhysAbi, [RDI,RSI,RDX] memref ABI)--> Lprog
    --(renderOwned)--> bench/x25519_fieldmul_compare/gen_com/fe25519_mul_front.s
```

No `Com` / `Lcmd` / `JInstr` is built by hand anywhere in this path. It is a
front-sourced sibling of the hand-scheduled `X86Backend.Fe25519MulKernel`, which
emits a different symbol to a different path; neither module reads the other.

## 32-bit limbs in 64-bit words

The covered `SExpr` alphabet (`SMul`/`SAdd`/`SSub`/`SAnd`/`SXor`/`SShr`/`SShl`)
carries no carry flag, so the kernel works in 32-bit limbs held in 64-bit words.
Every partial product of two 32-bit halves is below `2^64`, and an
operand-scanning column `acc + A·B + carry` stays below `2^64`
(`(2^32−1) + (2^32−1)^2 + (2^32−1) = 2^64 − 1`), so the carry is a word split
`carry = t >>> 32`, `limb = t &&& (2^32−1)`. The limb generators `genMul`,
`genAdd` and `genSub` are shared with `Secp256k1FeMulFront`.

## Reduction

The `8×8` operand-scanning multiply gives the 16-limb product `P`. With
`2^256 ≡ 38 (mod p)`, a fold replaces the high half by `38 ·` it:
`R = P[0..7] + 38 · P[8..]`. Three folds bring the value below `2^256`: the
first gives `R₁ < 2^263`, so `R₁ >>> 256 < 2^7` and `R₂ < 2^256 + 38 · 2^7`;
either `R₂ < 2^256`, or its low half is below `2^13` and `R₃ < 2^14`.

A value below `2^256` is then folded at the `2^255` boundary, using
`2^255 ≡ 19 (mod p)`: clear bit 255 and add `19` times that bit. The result is
below `2^255 + 19`, hence below `2p`, and a branch-free conditional subtract of
`p` canonicalises it into `[0, p)`.

## ABI

```c
extern void fe25519_mul_front(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   a[0..3], b[0..3] : little-endian 4×u64 canonical residues in [0, p)
//   out[0..3] = (a * b) mod (2^255 - 19)
```

`RDI = out`, `RSI = a`, `RDX = b` (the SysV 3-pointer memref ABI), each pointer a
4-cell (`.memref 4`, 32-byte) `u64` frame — the calling convention of
`fe25519_mul_x86_from_lean`, so the same harness can link either symbol.

## Gates

`emit` fails with an `IO.userError` when the front or the lowering declines, so a
successful `lake exe fe25519mulfront` run is the front-compile and lowering
check. The value gate is the external byte KAT in
`bench/x25519_fieldmul_compare` against GMP `mpz` mod `p` and against the
hand-scheduled kernel. This module carries no evaluation and no theorem.
-/

namespace CatCrypt.Crypto.SecureCompilation.Fe25519MulFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (sv seqAll genMul genAdd genSub loadLimbs splitLimbs recombineStore halfNames
   mask32 inΓ inVM)

/-! ## 0. Constants -/

/-- The Curve25519 base prime `p = 2^255 − 19`. -/
def pNat : Nat := 57896044618658097711785492504343953926634992332820282019728792003956564819949

/-- The little-endian 32-bit limbs of `p` (`pl32[0]` least significant). -/
def pl32 : List Nat := (List.range 8).map (fun i => (pNat >>> (32 * i)) &&& mask32)

/-- `38 = 2 · 19`, the folding constant for `2^256 ≡ 38 (mod p)`. -/
def c38 : Nat := 38

/-- `2^31 − 1`, the mask that clears bit 255 of the top 32-bit limb. -/
def mask31 : Nat := 2147483647

/-! ## 1. The `feMul` body -/

/-- Bind the constant cell indices `ix0 .. ix3`, the zero slot, the folding
    constant and the 32-bit limbs of `p`. -/
def constInit : List LowCT :=
  ((List.range 4).map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT)))
  ++ [ (.RScalarSetExpr "ZZ" (.SLit 0) : LowCT),
       (.RScalarSetExpr "C38" (.SLit c38) : LowCT) ]
  ++ ((List.range 8).map (fun i => (.RScalarSetExpr s!"PL{i}" (.SLit (pl32.getD i 0)) : LowCT)))

/-- One fold `R = lo(8) + 38 · hi(rest)` of a 32-bit-limb list. Returns the
    bindings and the result-limb names; a list of at most 8 limbs is returned
    unchanged. -/
def genFold38 (zero c0N : String) (full : List String) (pfx : String) :
    List LowCT × List String :=
  let lo := full.take 8
  let hi := full.drop 8
  if hi.isEmpty then
    ([], full)
  else
    let (mc, chi) := genMul zero [c0N] hi (pfx ++ "m")
    let (ac, res) := genAdd zero lo chi (pfx ++ "a")
    (mc ++ ac, res)

/-- The full front body: load and split both operands into 32-bit halves,
    multiply, fold three times at `2^256`, fold once at `2^255`, conditionally
    subtract `p`, recombine to `u64` and store. -/
def feMulBody : LowCT := Id.run do
  let mut cmds : List LowCT := constInit
  cmds := cmds ++ loadLimbs "a" "au" ++ splitLimbs "au" "A"
  cmds := cmds ++ loadLimbs "b" "bu" ++ splitLimbs "bu" "B"
  -- 8×8 operand-scanning multiply → 16 product limbs
  let (mc, prod) := genMul "ZZ" (halfNames "A") (halfNames "B") "M"
  cmds := cmds ++ mc
  -- three folds of 38 · high
  let (f1c, r1) := genFold38 "ZZ" "C38" prod "F1"
  let (f2c, r2) := genFold38 "ZZ" "C38" r1 "F2"
  let (f3c, r3) := genFold38 "ZZ" "C38" r2 "F3"
  cmds := cmds ++ f1c ++ f2c ++ f3c
  let lo8 := r3.take 8
  -- fold at the 2^255 boundary: clear bit 255, add 19 times it
  cmds := cmds ++
    [ (.RScalarSetExpr "HB" (.SShr (sv (lo8[7]!)) (.SLit 31)) : LowCT),
      (.RScalarSetExpr "HB19" (.SMul (sv "HB") (.SLit 19)) : LowCT),
      (.RScalarSetExpr "HM7" (.SAnd (sv (lo8[7]!)) (.SLit mask31)) : LowCT) ]
  let cleared : List String := (lo8.take 7) ++ ["HM7"]
  let (hc, h9) := genAdd "ZZ" cleared ["HB19"] "H"
  cmds := cmds ++ hc
  let red8 := h9.take 8
  -- one conditional subtract of p
  let pN := (List.range 8).map (fun i => s!"PL{i}")
  let (sc, dN, bw) := genSub "ZZ" red8 pN "S"
  cmds := cmds ++ sc
  -- select: keep `red8` iff `red8 < p` (bw = 1), else the difference `dN`
  cmds := cmds ++ [ (.RScalarSetExpr "MMR" (.SSub (.SLit 0) (sv bw)) : LowCT),
                    (.RScalarSetExpr "MM" (.SAnd (sv "MMR") (.SLit mask32)) : LowCT),
                    (.RScalarSetExpr "NM" (.SXor (sv "MM") (.SLit mask32)) : LowCT) ]
  let rNames : List String := (List.range 8).map (fun i => s!"R{i}")
  for i in [0:8] do
    cmds := cmds ++ [ (.RScalarSetExpr (rNames[i]!)
      (.SAdd (.SAnd (sv (red8[i]!)) (sv "MM")) (.SAnd (sv (dN[i]!)) (sv "NM"))) : LowCT) ]
  -- recombine 8 halves → 4 u64 and store
  cmds := cmds ++ recombineStore "R" "O"
  return seqAll cmds

/-! ## 2. Front-compile, lower

The context and `VarMap` are the shared head-first `[b, a, out]` 3-pointer memref
frame of `Secp256k1FeMulFront`: `comToLfundef` reverses context↔argument order, so
`out` bound deepest lands in `RDI`, `a` in `RSI` and `b` in `RDX`. -/

/-- Push the body through the direct control front and cap with `ret out`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM feMulBody with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowered to a `Com jasminDialect`
    (`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore`). -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-! ## 3. Owned emit driver -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- The lowered kernel as an owned AT&T `.s` under the SysV 3-pointer ABI. -/
def feMulAsm : Option String :=
  loweredOpt.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (Com.toLprogPhysAbi s.2.2 "fe25519_mul_front"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true)))

/-- Write the front-generated kernel to `gen_com/fe25519_mul_front.s`. -/
def emit (path : System.FilePath) : IO Unit := do
  match feMulAsm with
  | some a => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path a
      IO.println s!"FE25519-MUL-FRONT emit OK : {path} ({a.toUTF8.size} bytes, symbol fe25519_mul_front, {(a.splitOn "\n").length} lines)"
  | none => throw (IO.userError "front-compile of fe25519_mul_front failed (front/lowering declined)")

end CatCrypt.Crypto.SecureCompilation.Fe25519MulFront
