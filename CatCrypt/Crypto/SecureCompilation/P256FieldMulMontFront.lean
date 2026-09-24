/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
public import CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# Generic-prime CIOS/SOS Montgomery field multiply, FRONT-COMPILED (P-256 instance)

`Secp256k1FeMulFront` front-generates a
4-limb field multiply for the **Solinas** prime `p = 2^256 − 2^32 − 977` via the
cheap fold `2^256 ≡ 2^32 + 977`. That trick only works for pseudo-Mersenne primes
(secp256k1, Ed25519 `2^255−19`). The pairing / P-256 field-leaves
(`Pairing/{P256,Bls12381,Bn254}Emit.lean`) are over **generic** primes with no
such fold, so the Solinas front does not produce their `extCall` field/point
leaves.

This module front-generates a **Separated-Operand-Scanning (SOS) Montgomery**
multiply `out = a · b · R⁻¹ mod p` (`R = 2^256`) for an arbitrary odd prime,
instantiated at the NIST P-256 base field
`p = 2^256 − 2^224 + 2^192 + 2^96 − 1`, reusing the SAME verified front
(`translateDialectControl` + `cryptoDialectToJasminCom`) and the SAME 32-bit
half-limb operand-scanning generators (`genMul`/`genAdd`/`genSub`) that
`Secp256k1FeMulFront` uses. NO hand-built `Com`/`Lcmd`/`JInstr`.

```
  montMulBody (LowCT)
    --(translateDialectControl)--> Com catCryptDialect inΓ (.memref 4)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …
    --(Com.toLprogPhysAbi, [RDI,RSI,RDX])--> Lprog --(renderLprogAtt)--> .s
```

## The algorithm (32-bit words, carry-free through the covered `SExpr` alphabet)

Both operands are 8 little-endian 32-bit half-limbs held in 64-bit words (the
`Secp256k1FeMulFront` representation — every column accumulator stays `< 2^64`, so `SMul/SAdd/SSub/SAnd/
SShr/SShl/SXor` never truncates).

* `T = A × B` — 16-limb operand-scanning product (`genMul`).
* Montgomery reduce, 8 word-steps `i = 0 .. 7`:
  * `mᵢ = (T[i] · nPrime) &&& mask32`, `nPrime = (−p⁻¹) mod 2^32` (a literal).
  * `T := T + (mᵢ · p) · 2^{32 i}` — `mᵢ·p` is `genMul [mᵢ] pLimbs` (9 limbs),
    aligned with `i` leading zero limbs, added with `genAdd`. This zeroes `T[i]`.
* After 8 steps `T[0..7] = 0`; the reduced value is `T ⁄ 2^256` in the high limbs
  (`< 2p`). One branch-free conditional subtract of `p` canonicalises into `[0, p)`
  (a 9-limb trial subtract that includes the top carry limb, as in `feAdd`).

## ABI

```c
extern void p256_fe_mont_mul(uint64_t *out, const uint64_t *a, const uint64_t *b);
//   a,b : Montgomery-form residues (4×u64 LE);  out = a·b·R⁻¹ mod p
```
`RDI = out`, `RSI = a`, `RDX = b`. Each pointer a 4-cell (`.memref 4`) `u64` frame.

## Scope

Front-compile + lower gates (`§4`). The module shows that the front expresses
generic Montgomery multiplication. The Montgomery VALUE-tie (`denote =
a·b·R⁻¹ mod p`) is the subject of a byte KAT against a GMP reference (`§5`); an
in-Lean denote proof is outside the scope of this module.
-/

namespace CatCrypt.Crypto.SecureCompilation.P256FieldMulMontFront

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

/-! ## 0. Constants — the P-256 base prime and its Montgomery inverse word -/

/-- NIST P-256 base prime `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`. -/
def pNat : Nat := 115792089210356248762697446949407573530086143415290314195533631308867097853951

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
theorem pInvWord_spec : (pNat * pInvWord) % wMod = 1 := by native_decide
theorem nPrimeWord_spec : (pNat * nPrimeWord) % wMod = wMod - 1 := by native_decide

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

/-! ## 4. Front-compile / lower gates -/

/-- The body front-compiles (`translateDialectControl` + `ret out`). -/
theorem frontCom_isSome : frontCom.isSome := by native_decide

/-- The kernel lowers end-to-end to `Com jasminDialect`. -/
theorem lowered_isSome : loweredOpt.isSome := by native_decide

/-! ## 5. Byte KAT (value-tie)

The Montgomery denote-tie `denote a b = limbs4 (a·b·R⁻¹ mod p)` is the subject of an
external byte KAT (§6 below is a stub): assemble `p256_fe_mont_mul.s`, and for random `a,b < p`
compare against GMP:  `r = a*b*R^{-1} mod p` with `R = 2^256`,
`R^{-1} = mpz_invert(2^256, p)`. -/

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
      (Com.toLprogPhysAbi s.2.2 "p256_fe_mont_mul"
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := ["RDI", "RSI", "RDX"]) (abiTyin := [64, 64, 64])
        (residence := none) (abiW := 0) (forceLivePin := true)))

/-- Write the front-generated kernel to `gen_com/p256_fe_mont_mul.s`. -/
def emit (path : System.FilePath) : IO Unit := do
  match montMulAsm with
  | some a => do
      if let some d := path.parent then IO.FS.createDirAll d
      IO.FS.writeFile path a
      IO.println s!"P256-FE-MONT-MUL emit OK : {path} ({a.toUTF8.size} bytes)"
  | none => throw (IO.userError "front-compile of p256_fe_mont_mul failed")

end CatCrypt.Crypto.SecureCompilation.P256FieldMulMontFront
