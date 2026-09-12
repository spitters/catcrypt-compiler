/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# Generic-prime SOS Montgomery field multiply, FRONT-COMPILED (SQIsign level-1 instance)

This module front-generates a Separated-Operand-Scanning (SOS) Montgomery
multiply `out = a · b · R⁻¹ mod p` (`R = 2^256`) for an arbitrary odd prime,
instantiated at the SQIsign NIST level-1 base field prime
`p5248 = 5·2^248 − 1` (the-sqisign reference, `fp_p5248_64.c`), a 251-bit prime
held in four 64-bit limbs. It reuses the verified front
(`translateDialectControl` + `cryptoDialectToJasminCom`) and the 32-bit
half-limb operand-scanning generators (`genMul`/`genAdd`/`genSub`) from
`Secp256k1FeMulFront`. No hand-built `Com`/`Lcmd`/`JInstr`.

```
  montMulBody (LowCT)
    --(translateDialectControl)--> Com catCryptDialect inΓ (.memref 4)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …
    --(Com.toLprogPhysAbi, [RDI,RSI,RDX])--> Lprog --(renderOwned)--> .s
```

## The algorithm (32-bit words, carry-free through the covered `SExpr` alphabet)

Both operands are 8 little-endian 32-bit half-limbs held in 64-bit words (the
phase-1 representation — every column accumulator stays `< 2^64`, so `SMul/SAdd/
SSub/SAnd/SShr/SShl/SXor` never truncates).

* `T = A × B` — 16-limb operand-scanning product (`genMul`).
* Montgomery reduce, 8 word-steps `i = 0 .. 7`:
  * `mᵢ = (T[i] · nPrime) &&& mask32`, `nPrime = (−p⁻¹) mod 2^32` (a literal).
  * `T := T + (mᵢ · p) · 2^{32 i}` — `mᵢ·p` is `genMul [mᵢ] pLimbs` (9 limbs),
    aligned with `i` leading zero limbs, added with `genAdd`. This zeroes `T[i]`.
* After 8 steps `T[0..7] = 0`; the reduced value is `T ⁄ 2^256` in the high limbs
  (`< 2p`). One branch-free conditional subtract of `p` canonicalises into `[0, p)`
  (a 9-limb trial subtract that includes the top carry limb, as in phase-2 `feAdd`).

`p5248 < 2^256`, so the four 64-bit limbs / eight 32-bit half-limbs and the
8-step reduction are the same shape as the P-256 instance.

## ABI

```c
extern void sqisign_fp_mont_mul(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   a,b : Montgomery-form residues (4×u64 LE);  out = a·b·R⁻¹ mod p5248
```
`RDI = out`, `RSI = a`, `RDX = b`. Each pointer a 4-cell (`.memref 4`) `u64` frame.

## Main definitions

* `pNat`: the SQIsign level-1 prime `p5248 = 5·2^248 − 1`.
* `nPrimeWord` / `pInvWord`: the Montgomery reduction word and 2-adic inverse mod
  `2^32`, with `pInvWord_spec` / `nPrimeWord_spec` verifying `p·p⁻¹ ≡ 1` and
  `p·nPrime ≡ −1 (mod 2^32)`.
* `montMulBody`: the generic SOS Montgomery-multiply `LowCT` body for `pNat`.
* `montMulAsm` / `emit` / `emitMain`: the owned AT&T `.s` for `sqisign_fp_mont_mul`,
  front-compiled through `translateDialectControl → cryptoDialectToJasminCom →
  toLprogPhysAbi → renderOwned`.
-/

namespace CatCrypt.Crypto.SecureCompilation.SqisignFieldMulMontFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (genMul genAdd genSub seqAll sv mask32 loadLimbs splitLimbs recombineStore halfNames)

/-! ## 0. Constants — the SQIsign level-1 base prime and its Montgomery inverse word -/

/-- SQIsign NIST level-1 prime `p5248 = 5·2^248 − 1` (`= 2^250 + 2^248 − 1`,
    a 251-bit prime, 4×64-bit limbs), from the-sqisign `fp_p5248_64.c`. -/
def pNat : Nat := 5 * 2^248 - 1

/-- The little-endian 32-bit limbs of `p` (`pl32[0]` least significant). -/
def pl32 : List Nat := (List.range 8).map (fun i => (pNat >>> (32 * i)) &&& mask32)

/-- `2^32`, the word modulus for the Montgomery word inverse. -/
def wMod : Nat := 4294967296

/-- One Newton step for the 2-adic inverse mod `2^32`: `x ↦ x·(2 − p·x) mod 2^32`. -/
def invStep (x : Nat) : Nat := (x * (2 + wMod - (pNat * x) % wMod)) % wMod

/-- `p⁻¹ mod 2^32` by 5 Newton doublings from `x₀ = 1` (`p` is odd ⇒ converges;
    5 steps cover the 32 bits: 1→2→4→8→16→32). -/
def pInvWord : Nat := invStep (invStep (invStep (invStep (invStep 1))))

/-- `nPrime = (−p⁻¹) mod 2^32`, the CIOS/SOS reduction word multiplier. -/
def nPrimeWord : Nat := (wMod - pInvWord) % wMod

/-- Sanity: `p · pInvWord ≡ 1 (mod 2^32)` and `p · nPrimeWord ≡ −1 (mod 2^32)`. -/
theorem pInvWord_spec : (pNat * pInvWord) % wMod = 1 := by norm_num [pNat, pInvWord, wMod, invStep]
theorem nPrimeWord_spec : (pNat * nPrimeWord) % wMod = wMod - 1 := by
  norm_num [pNat, nPrimeWord, pInvWord, wMod, invStep]

/-! ## 1. Body builders -/

/-- Bind constant cell indices `ix0..3`, the zero slot `ZZ`, the reduction word
    `NP = nPrime`, and the eight 32-bit limbs of `p` (`PL0..PL7`). -/
def constInit : List LowCT :=
  ((List.range 4).map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT)))
  ++ [ (.RScalarSetExpr "ZZ" (.SLit 0) : LowCT),
       (.RScalarSetExpr "NP" (.SLit nPrimeWord) : LowCT) ]
  ++ ((List.range 8).map (fun i => (.RScalarSetExpr s!"PL{i}" (.SLit (pl32.getD i 0)) : LowCT)))

/-- The eight 32-bit limb names of `p` bound by `constInit`. -/
def plNames : List String := (List.range 8).map (fun i => s!"PL{i}")

/-- One SOS Montgomery word-step at index `i`: given the current accumulator limb
    names `T` (length ≥ i+1), emit `m = (T[i]·NP)&mask`, `mp = m·p` (9 limbs),
    and `T' = T + (i zeros ++ mp)`. Returns the new bindings and the new
    accumulator names (length `|T|+1`). -/
def montStep (i : Nat) (T : List String) : List LowCT × List String := Id.run do
  let pfx := s!"MS{i}"
  let mut cmds : List LowCT := []
  -- m = (T[i] * NP) & mask32   (single 32-bit reduction word)
  let mTmp := s!"{pfx}mt"
  let mNm  := s!"{pfx}m"
  cmds := cmds ++ [ (.RScalarSetExpr mTmp (.SMul (sv (T.getD i "ZZ")) (sv "NP")) : LowCT),
                    (.RScalarSetExpr mNm (.SAnd (sv mTmp) (.SLit mask32)) : LowCT) ]
  -- mp = m * p  (1 × 8 → 9 limbs)
  let (mpC, mp) := genMul "ZZ" [mNm] plNames (pfx ++ "P")
  cmds := cmds ++ mpC
  -- align mp at word offset i, then add into T
  let aligned : List String := (List.replicate i "ZZ") ++ mp
  let (addC, T') := genAdd "ZZ" T aligned (pfx ++ "A")
  cmds := cmds ++ addC
  return (cmds, T')

/-- The eight-step Montgomery reduction over a 16-limb product `T0`. Returns the
    bindings and the final accumulator names. -/
def montReduce (T0 : List String) : List LowCT × List String := Id.run do
  let mut cmds : List LowCT := []
  let mut T := T0
  for i in [0:8] do
    let (c, T') := montStep i T
    cmds := cmds ++ c
    T := T'
  return (cmds, T)

/-- The full front body: load `a`,`b`, split to 32-bit halves, multiply, Montgomery
    reduce, conditional-subtract `p`, recombine, store. -/
def montMulBody : LowCT := Id.run do
  let mut cmds : List LowCT := constInit
  cmds := cmds ++ loadLimbs "a" "au" ++ splitLimbs "au" "A"
  cmds := cmds ++ loadLimbs "b" "bu" ++ splitLimbs "bu" "B"
  -- 8×8 operand-scanning multiply → 16 product limbs
  let (mc, prod) := genMul "ZZ" (halfNames "A") (halfNames "B") "M"
  cmds := cmds ++ mc
  -- Montgomery reduce (8 word-steps); low 8 limbs are zeroed, value in the high part
  let (rc, T) := montReduce prod
  cmds := cmds ++ rc
  -- reduced value = T / 2^256 : the 9 limbs T[8..16] (< 2p, so ≤ 9 limbs)
  let hi9 : List String := (List.range 9).map (fun k => T.getD (8 + k) "ZZ")
  -- conditional subtract p (extend p to a 9th 0 limb; keep hi iff hi < p)
  let pN9 : List String := plNames ++ ["ZZ"]
  let (sc, dN, bw) := genSub "ZZ" hi9 pN9 "S"
  cmds := cmds ++ sc
  cmds := cmds ++ [ (.RScalarSetExpr "MMR" (.SSub (.SLit 0) (sv bw)) : LowCT),
                    (.RScalarSetExpr "MM" (.SAnd (sv "MMR") (.SLit mask32)) : LowCT),
                    (.RScalarSetExpr "NM" (.SXor (sv "MM") (.SLit mask32)) : LowCT) ]
  let rNames : List String := (List.range 8).map (fun i => s!"R{i}")
  for i in [0:8] do
    cmds := cmds ++ [ (.RScalarSetExpr (rNames[i]!)
      (.SAdd (.SAnd (sv (hi9[i]!)) (sv "MM")) (.SAnd (sv (dN[i]!)) (sv "NM"))) : LowCT) ]
  cmds := cmds ++ recombineStore "R" "O"
  return seqAll cmds

/-! ## 2. Input context + `VarMap` (`out ← RDI`, `a ← RSI`, `b ← RDX`) -/

/-- Head-first kernel context `[b, a, out]`, each a 4-cell `u64` memref. -/
def inΓ : Ctx := [.memref 4, .memref 4, .memref 4]

/-- `out` deepest (→ RDI), then `a` (→ RSI), then `b` (head → RDX). -/
def inVM : VarMap inΓ :=
  ((VarMap.empty.bind (t := .memref 4) "out").bind
    (t := .memref 4) "a").bind (t := .memref 4) "b"

/-! ## 3. Front-compile, lower -/

/-- Push the body through the direct control front and cap with `ret out`. -/
def frontCom : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM montMulBody with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted dialect program lowers to a `Com jasminDialect`. -/
def loweredOpt :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontCom with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-! ## 4. Front-compile / lower

The body front-compiles (`translateDialectControl` + `ret out`) and lowers
end-to-end to `Com jasminDialect`. That the front produces `some` is exercised by
the emit driver (`emit` throws when `montMulAsm` is `none`) and, together with
value correctness, by the external GMP byte-KAT; a reflective `frontCom.isSome`
gate would native-compile the whole reflection pipeline at multi-GB cost for the
same fact. -/

/-! ## 5. Byte-KAT reference (value-tie, external)

The Montgomery denote-tie `denote a b = limbs4 (a·b·R⁻¹ mod p)` is checked
externally by a byte KAT: assemble `sqisign_fp_mont_mul_owned.s`, and for random
`a,b < p` compare against GMP: `r = a·b·R⁻¹ mod p` with `R = 2^256`,
`R⁻¹ = mpz_invert(2^256, p)`. -/

/-- Recombine 4 LE `u64` cells to a `Nat`. -/
def valOf (ws : List Nat) : Nat :=
  ws[0]! + 2 ^ 64 * ws[1]! + 2 ^ 128 * ws[2]! + 2 ^ 192 * ws[3]!

/-- Split a `Nat` into 4 LE `u64` limbs. -/
def limbs4 (n : Nat) : List Nat :=
  [n % 2 ^ 64, n / 2 ^ 64 % 2 ^ 64, n / 2 ^ 128 % 2 ^ 64, n / 2 ^ 192 % 2 ^ 64]

/-! ## 6. Owned emit driver -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- The lowered kernel as an owned AT&T `.s` under the SysV 3-pointer ABI. -/
def montMulAsm : Option String :=
  loweredOpt.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (Com.toLprogPhysAbi s.2.2 "sqisign_fp_mont_mul"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true)))

/-- Write the front-generated kernel to the given path. -/
def emit (path : System.FilePath) : IO Unit := do
  match montMulAsm with
  | some a => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path a
      IO.println s!"SQISIGN-FP-MONT-MUL emit OK : {path} ({a.toUTF8.size} bytes)"
  | none => throw (IO.userError "front-compile of sqisign_fp_mont_mul failed")

/-- Emit the owned `.s` to the bench directory (path relative to the repo root). -/
def emitMain : IO Unit :=
  emit "bench/sqisign_fieldmul_compare/gen_com/sqisign_fp_mont_mul_owned.s"

/-! ## 7. CIOS-scheduled variant

A Coarsely-Integrated-Operand-Scanning (CIOS) schedule for the same
`out = a · b · R⁻¹ mod p5248`, over the same 32-bit half-limb representation and
the same covered `SExpr` alphabet as the SOS body above. It computes no full
`2n`-limb product: each multiplier half-limb `b[i]` drives one integrated
multiply-then-reduce pass over a nine-half-limb accumulator, which is divided by
`2^32` (dropped one half-limb) each pass. The accumulator stays nine half-limbs
wide across all eight passes, so the count of simultaneously-live limb names is
bounded by the accumulator width plus the per-pass transient partials, rather
than the sixteen product limbs the SOS body holds live through its reduction. -/

/-- One CIOS outer pass on multiplier half-limb `Bi`:
    `T ← ((T + a·Bi) + m·p) ⁄ 2^32` with `m = (low(T + a·Bi) · nPrime) &&& mask`,
    so the low half-limb of `T + a·Bi + m·p` is zero and dropping it divides by
    `2^32`. `aHalves` are the eight 32-bit half-limbs of `a`; `T` is the current
    nine-half-limb accumulator. Returns the bindings and the next nine-half-limb
    accumulator. -/
def montStepCios (i : Nat) (aHalves : List String) (Bi : String) (T : List String) :
    List LowCT × List String := Id.run do
  let pfx := s!"CI{i}"
  let mut cmds : List LowCT := []
  -- part = a · Bi   (8 × 1 → 9 half-limbs)
  let (pc, part) := genMul "ZZ" aHalves [Bi] (pfx ++ "P")
  cmds := cmds ++ pc
  -- T1 = T + part
  let (a1, T1) := genAdd "ZZ" T part (pfx ++ "A")
  cmds := cmds ++ a1
  -- m = (T1[0] · NP) & mask32
  let mTmp := s!"{pfx}mt"
  let mNm  := s!"{pfx}m"
  cmds := cmds ++ [ (.RScalarSetExpr mTmp (.SMul (sv (T1.getD 0 "ZZ")) (sv "NP")) : LowCT),
                    (.RScalarSetExpr mNm (.SAnd (sv mTmp) (.SLit mask32)) : LowCT) ]
  -- mp = m · p   (1 × 8 → 9 half-limbs)
  let (mc, mp) := genMul "ZZ" [mNm] plNames (pfx ++ "Q")
  cmds := cmds ++ mc
  -- T2 = T1 + mp ; the low half-limb of T2 is 0 by the choice of m
  let (a2, T2) := genAdd "ZZ" T1 mp (pfx ++ "B")
  cmds := cmds ++ a2
  -- divide by 2^32: drop the zero low half-limb, keep nine half-limbs
  return (cmds, (T2.drop 1).take 9)

/-- The CIOS-scheduled front body: load `a`,`b`, split to 32-bit halves, run eight
    integrated multiply-reduce passes over a nine-half-limb accumulator,
    conditional-subtract `p`, recombine, store. -/
def montMulBodyCios : LowCT := Id.run do
  let mut cmds : List LowCT := constInit
  cmds := cmds ++ loadLimbs "a" "au" ++ splitLimbs "au" "A"
  cmds := cmds ++ loadLimbs "b" "bu" ++ splitLimbs "bu" "B"
  let aHalves := halfNames "A"
  let bHalves := halfNames "B"
  let mut T : List String := List.replicate 9 "ZZ"
  for i in [0:8] do
    let (c, T') := montStepCios i aHalves (bHalves[i]!) T
    cmds := cmds ++ c
    T := T'
  -- reduced value in T (< 2p), nine half-limbs; conditional subtract p
  let hi9 : List String := (List.range 9).map (fun k => T.getD k "ZZ")
  let pN9 : List String := plNames ++ ["ZZ"]
  let (sc, dN, bw) := genSub "ZZ" hi9 pN9 "S"
  cmds := cmds ++ sc
  cmds := cmds ++ [ (.RScalarSetExpr "MMR" (.SSub (.SLit 0) (sv bw)) : LowCT),
                    (.RScalarSetExpr "MM" (.SAnd (sv "MMR") (.SLit mask32)) : LowCT),
                    (.RScalarSetExpr "NM" (.SXor (sv "MM") (.SLit mask32)) : LowCT) ]
  let rNames : List String := (List.range 8).map (fun i => s!"R{i}")
  for i in [0:8] do
    cmds := cmds ++ [ (.RScalarSetExpr (rNames[i]!)
      (.SAdd (.SAnd (sv (hi9[i]!)) (sv "MM")) (.SAnd (sv (dN[i]!)) (sv "NM"))) : LowCT) ]
  cmds := cmds ++ recombineStore "R" "O"
  return seqAll cmds

/-- Push the CIOS body through the direct control front and cap with `ret out`. -/
def frontComCios : Option (Com catCryptDialect inΓ (.memref 4)) :=
  match translateDialectControl inVM montMulBodyCios with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 4, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The CIOS front body lowered to a `Com jasminDialect`. -/
def loweredOptCios :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match frontComCios with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

/-- The lowered CIOS kernel as an owned AT&T `.s` under the SysV 3-pointer ABI. -/
def montMulAsmCios : Option String :=
  loweredOptCios.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned
      (Com.toLprogPhysAbi s.2.2 "sqisign_fp_mont_mul_cios"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true)))

/-- Write the front-generated CIOS kernel to the given path. -/
def emitCios (path : System.FilePath) : IO Unit := do
  match montMulAsmCios with
  | some a => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path a
      IO.println s!"SQISIGN-FP-MONT-MUL-CIOS emit OK : {path} ({a.toUTF8.size} bytes)"
  | none => throw (IO.userError "front-compile of sqisign_fp_mont_mul_cios failed")

/-- Emit the CIOS owned `.s` to the bench directory (path relative to the repo root). -/
def emitMainCios : IO Unit :=
  emitCios "bench/sqisign_fieldmul_compare/gen_com/sqisign_fp_mont_mul_cios_owned.s"

end CatCrypt.Crypto.SecureCompilation.SqisignFieldMulMontFront

open CatCrypt.Crypto.SecureCompilation.SqisignFieldMulMontFront in
/-- Entry point for `lake env lean --run`: writes the SOS owned `.s`, or the
CIOS-scheduled owned `.s` when passed the `cios` argument. -/
def main (args : List String) : IO Unit :=
  if args.contains "cios" then emitMainCios else emitMain
