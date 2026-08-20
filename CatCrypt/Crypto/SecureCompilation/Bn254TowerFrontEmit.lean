/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
import CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse
import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect

set_option autoImplicit false

/-!
# BN254 `Fp2` add / sub / copy (`j_bn254_Fp2_*`), FRONT-COMPILED to owned x86

The `bench/bn254_compare/jasmin_tower` bench's `tower_subset.s` exports the
BN254 pairing-tower `Fp2 = Fp[u]/(u² + 1)` additive leaves
`j_bn254_Fp2_add` / `j_bn254_Fp2_sub` / `j_bn254_Fp2_felem_copy` (64-byte
`Fp2` operands: `c0` at cells `0..3`, `c1` at cells `4..7`, little-endian
4-limb `Fp` halves).  This module sources those kernels end-to-end through the
verified front — NO hand-built `Com` / `Lcmd` anywhere in the emit path (the
same straight-line route as `Mersenne31FrontEmit`):

```
  body (LowCT: RArrLoad / RScalarSetExpr carry-chain field math / RArrStore)
    --(translateDialectCarrySelect: the C6 carry-chain instruction-selection
       front — the bSltu carry/borrow windows become bvAddCarryLo/bvAddCarryHi
       ADC-class chains; everything else falls through to
       translateDialectControl)--> Com catCryptDialect inΓ (.memref 8)
    --(cryptoDialectToJasminCom)--> Com jasminDialect …   (stackLoad/stackStore)
    --(Com.toLprogPhysAbi, [RDI,RSI(,RDX)] memref ABI)--> Lprog
    --(renderLprogAtt)--> bench/bn254_compare/jasmin_tower/gen_com/tower_owned.s
```

The per-rewrite denotation-preservation lemmas of the selection live in
`Dialects/CarryChainSelect.lean` (`select_addStart_*` / `select_addMid_*` /
`select_subStart_*` / `select_subMid_*`, all-inputs `bv_decide`); the §6
`denote = independent Nat spec` gates below re-check the *selected* pipeline
end-to-end on the anchor vectors.

## The three kernels (SysV pointer ABI, eight `u64` cells per pointer)

```c
extern void j_bn254_Fp2_add(uint64_t *out, const uint64_t *x, const uint64_t *y);
//   out[c] = (x[c] + y[c]) mod p  componentwise on the c0/c1 halves
extern void j_bn254_Fp2_sub(uint64_t *out, const uint64_t *x, const uint64_t *y);
//   out[c] = (x[c] - y[c]) mod p  componentwise on the c0/c1 halves
extern void j_bn254_Fp2_felem_copy(uint64_t *out, const uint64_t *x);
//   out[0..7] = x[0..7]
```

for canonical residues `x, y ∈ [0, p)` per half, over the BN254 base prime
`p = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47`.

## Field math (branch-free, covered `SExpr` alphabet)

Each `Fp` half is a 4-limb carry chain.  The carry/borrow bit of every limb
step is synthesised branch-free by the proven `bSltu` shape of
`MultiLimbKernel.add2Prog`:

`x <u y  =  ((~(x ^ y) & (x − y)) | (~x & y)) >> 63`

(no `SLt` — that arm has no jasmin lowering; `|` is `(a ^ b) ^ (a & b)`).

* **modadd**: ripple ADD chain (canonical inputs give `a + b < 2p < 2²⁵⁵`, so
  the 4-limb sum cannot wrap), trial subtract of `p` with a ripple borrow
  chain, then the branch-free select `r = (s & m) + (d & ~m)` on the final
  borrow's mask `m = 0 − w₃` (`w₃ = 1` iff `s < p`).
* **modsub**: ripple SUB borrow chain, then the masked add-back
  `r = d + (p & m)` with a ripple carry chain (`m = 0 − w₃`, `w₃ = 1` iff
  `a < b`); the final carry is exactly the `2²⁵⁶` wrap and is dropped.
* **copy**: eight load/store pairs.

All constant-time (no data-dependent branch, no secret-indexed access — the
cell indices are the constants `0..7`).

## Gates

In-model: the three bodies front-compile, lower, and render (`§5`), and the
add/sub front programs denote to the **independent** `Nat` `(x ± y) % p` spec
(computed with `Nat` `%`, not the emitted carry shape) on the published
EIP-197 BN254 G2 generator coordinates (the exact
`bench/bn254_compare/jasmin_tower/bn254_tower_kat.rs` anchor, Montgomery form)
plus edge vectors (`§6`, `native_decide`).  The deployed `.s` is gated by the
external byte KAT (`cargo run --bin bn254_tower_kat`: byte-identical to the
AUCurves verified-bedrock2 Rust tower `tower::bn254_Fp2_add/sub/felem_copy`).

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/Bn254TowerFrontEmit.lean
Invoke (emit the `.s`):
  lake env lean --run bench/bn254_compare/jasmin_tower/tower_owned_emit.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Bn254TowerFrontEmit

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
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (translateDialectCarrySelect)

/-! ## 0. The BN254 base prime and the shared `SExpr` carry-chain pieces -/

/-- The BN254 (alt-bn128) base prime. -/
def pNat : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The prime's little-endian 64-bit limbs (`pl[0]` least significant). -/
def pl : List Nat :=
  [4332616871279656263, 10917124144477883021, 13281191951274694749, 3486998266802970665]

/-- `pl` recombines to the BN254 prime. -/
theorem pl_value :
    pl[0]! + 2 ^ 64 * pl[1]! + 2 ^ 128 * pl[2]! + 2 ^ 192 * pl[3]! = pNat := by
  native_decide

/-- All-ones 64-bit literal. -/
def ones : Nat := 18446744073709551615

/-- Bitwise NOT via XOR with all-ones. -/
def notE (e : SExpr) : SExpr := .SXor e (.SLit ones)

/-- Bitwise OR via `(a ^ b) ^ (a & b)`. -/
def orE (a b : SExpr) : SExpr := .SXor (.SXor a b) (.SAnd a b)

/-- `dst := (x <u y)` as `0`/`1`, branch-free (the proven
    `MultiLimbKernel.add2Prog` `bSltu` synthesis:
    `((~(x^y) & (x−y)) | (~x & y)) >> 63`).  Scratch slots `dst ++ "q"` /
    `dst ++ "r"`. -/
def ltuCmds (dst : String) (x y : SExpr) : List LowCT :=
  [ .RScalarSetExpr (dst ++ "q") (.SAnd (notE x) y),
    .RScalarSetExpr (dst ++ "r") (.SAnd (notE (.SXor x y)) (.SSub x y)),
    .RScalarSetExpr dst
      (.SShr (orE (.SVar (dst ++ "q")) (.SVar (dst ++ "r"))) (.SLit 63)) ]

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- Named variable shorthand. -/
def v (n : String) : SExpr := .SVar n

/-! ## 1. Loads, stores, index slots -/

/-- Bind the constant cell indices `ix0 .. ix7`. -/
def idxInit : List LowCT :=
  (List.range 8).map (fun i => (.RScalarSetExpr s!"ix{i}" (.SLit i) : LowCT))

/-- Load one 4-limb `Fp` half of the 8-cell operand `arr` at cell offset `o`
    into scalar slots `d0 .. d3`. -/
def loadHalf (arr d : String) (o : Nat) : List LowCT :=
  (List.range 4).map (fun j =>
    (.RArrLoad ⟨s!"{d}{j}", .TU64⟩ ⟨arr, .TBytes 64⟩ s!"ix{o + j}" : LowCT))

/-- Store the result slots `r0 .. r3` into `out` at cell offset `o`. -/
def storeHalf (r : String) (o : Nat) : List LowCT :=
  (List.range 4).map (fun j =>
    (.RArrStore ⟨"out", .TBytes 64⟩ s!"ix{o + j}" ⟨s!"{r}{j}", .TU64⟩ : LowCT))

/-! ## 2. The per-half modadd / modsub carry-chain bodies -/

/-- One `Fp` half of the modadd: load `x`/`y` cells `o..o+3`, ripple-ADD chain
    (`s`), trial subtract of `p` with ripple borrow (`e`, final borrow `w3`),
    branch-free select, store.  All slot names carry the half prefix `pfx`. -/
def modAddHalf (pfx : String) (o : Nat) : List LowCT :=
  let a := fun (j : Nat) => v s!"{pfx}a{j}"
  let b := fun (j : Nat) => v s!"{pfx}b{j}"
  let s := fun (j : Nat) => v s!"{pfx}s{j}"
  let e := fun (j : Nat) => v s!"{pfx}e{j}"
  let g := fun (j : Nat) => v s!"{pfx}g{j}"
  let c := fun (j : Nat) => v s!"{pfx}c{j}"
  let w := fun (j : Nat) => v s!"{pfx}w{j}"
  loadHalf "x" (pfx ++ "a") o ++ loadHalf "y" (pfx ++ "b") o
  -- ripple ADD chain: s = a + b  (a, b < p ⇒ s < 2p < 2^255, no 4-limb wrap)
  ++ [ .RScalarSetExpr s!"{pfx}s0" (.SAdd (a 0) (b 0)) ]
  ++ ltuCmds s!"{pfx}c0" (s 0) (a 0)
  ++ ((List.range 2).flatMap (fun k =>
      let j := k + 1
      [ (.RScalarSetExpr s!"{pfx}t{j}" (.SAdd (a j) (b j)) : LowCT) ]
      ++ ltuCmds s!"{pfx}ca{j}" (v s!"{pfx}t{j}") (a j)
      ++ [ .RScalarSetExpr s!"{pfx}s{j}" (.SAdd (v s!"{pfx}t{j}") (c (j - 1))) ]
      ++ ltuCmds s!"{pfx}cb{j}" (s j) (v s!"{pfx}t{j}")
      ++ [ .RScalarSetExpr s!"{pfx}c{j}"
            (.SAdd (v s!"{pfx}ca{j}") (v s!"{pfx}cb{j}")) ]))
  ++ [ .RScalarSetExpr s!"{pfx}t3" (.SAdd (a 3) (b 3)),
       .RScalarSetExpr s!"{pfx}s3" (.SAdd (v s!"{pfx}t3") (c 2)) ]
  -- trial subtract: e = s − p, ripple borrow w (w3 = 1 iff s < p)
  ++ [ .RScalarSetExpr s!"{pfx}e0" (.SSub (s 0) (.SLit pl[0]!)) ]
  ++ ltuCmds s!"{pfx}w0" (s 0) (.SLit pl[0]!)
  ++ ((List.range 3).flatMap (fun k =>
      let j := k + 1
      [ (.RScalarSetExpr s!"{pfx}g{j}" (.SSub (s j) (.SLit pl[j]!)) : LowCT) ]
      ++ ltuCmds s!"{pfx}wa{j}" (s j) (.SLit pl[j]!)
      ++ [ .RScalarSetExpr s!"{pfx}e{j}" (.SSub (g j) (w (j - 1))) ]
      ++ ltuCmds s!"{pfx}wb{j}" (g j) (w (j - 1))
      ++ [ .RScalarSetExpr s!"{pfx}w{j}"
            (.SAdd (v s!"{pfx}wa{j}") (v s!"{pfx}wb{j}")) ]))
  -- branch-free select on the final borrow: keep s iff s < p
  ++ [ .RScalarSetExpr s!"{pfx}m" (.SSub (.SLit 0) (w 3)) ]
  ++ ((List.range 4).map (fun j =>
      (.RScalarSetExpr s!"{pfx}r{j}"
        (.SAdd (.SAnd (s j) (v s!"{pfx}m"))
               (.SAnd (e j) (notE (v s!"{pfx}m")))) : LowCT)))
  ++ storeHalf (pfx ++ "r") o

/-- One `Fp` half of the modsub: ripple SUB borrow chain (`e`, final borrow
    `w3 = 1` iff `x < y`), masked add-back of `p` with a ripple carry chain
    (final carry = the `2²⁵⁶` wrap, dropped), store. -/
def modSubHalf (pfx : String) (o : Nat) : List LowCT :=
  let a := fun (j : Nat) => v s!"{pfx}a{j}"
  let b := fun (j : Nat) => v s!"{pfx}b{j}"
  let e := fun (j : Nat) => v s!"{pfx}e{j}"
  let g := fun (j : Nat) => v s!"{pfx}g{j}"
  let k' := fun (j : Nat) => v s!"{pfx}k{j}"
  let r := fun (j : Nat) => v s!"{pfx}r{j}"
  let c := fun (j : Nat) => v s!"{pfx}c{j}"
  let w := fun (j : Nat) => v s!"{pfx}w{j}"
  loadHalf "x" (pfx ++ "a") o ++ loadHalf "y" (pfx ++ "b") o
  -- ripple SUB borrow chain: e = a − b, borrow w (w3 = 1 iff a < b)
  ++ [ .RScalarSetExpr s!"{pfx}e0" (.SSub (a 0) (b 0)) ]
  ++ ltuCmds s!"{pfx}w0" (a 0) (b 0)
  ++ ((List.range 3).flatMap (fun kk =>
      let j := kk + 1
      [ (.RScalarSetExpr s!"{pfx}g{j}" (.SSub (a j) (b j)) : LowCT) ]
      ++ ltuCmds s!"{pfx}wa{j}" (a j) (b j)
      ++ [ .RScalarSetExpr s!"{pfx}e{j}" (.SSub (g j) (w (j - 1))) ]
      ++ ltuCmds s!"{pfx}wb{j}" (g j) (w (j - 1))
      ++ [ .RScalarSetExpr s!"{pfx}w{j}"
            (.SAdd (v s!"{pfx}wa{j}") (v s!"{pfx}wb{j}")) ]))
  -- masked add-back: r = e + (p & m), m = 0 − w3
  ++ [ .RScalarSetExpr s!"{pfx}m" (.SSub (.SLit 0) (w 3)),
       .RScalarSetExpr s!"{pfx}k0" (.SAnd (.SLit pl[0]!) (v s!"{pfx}m")),
       .RScalarSetExpr s!"{pfx}r0" (.SAdd (e 0) (k' 0)) ]
  ++ ltuCmds s!"{pfx}c0" (r 0) (e 0)
  ++ ((List.range 2).flatMap (fun kk =>
      let j := kk + 1
      [ (.RScalarSetExpr s!"{pfx}k{j}" (.SAnd (.SLit pl[j]!) (v s!"{pfx}m")) : LowCT),
        .RScalarSetExpr s!"{pfx}u{j}" (.SAdd (e j) (k' j)) ]
      ++ ltuCmds s!"{pfx}ca{j}" (v s!"{pfx}u{j}") (e j)
      ++ [ .RScalarSetExpr s!"{pfx}r{j}" (.SAdd (v s!"{pfx}u{j}") (c (j - 1))) ]
      ++ ltuCmds s!"{pfx}cb{j}" (r j) (v s!"{pfx}u{j}")
      ++ [ .RScalarSetExpr s!"{pfx}c{j}"
            (.SAdd (v s!"{pfx}ca{j}") (v s!"{pfx}cb{j}")) ]))
  ++ [ .RScalarSetExpr s!"{pfx}k3" (.SAnd (.SLit pl[3]!) (v s!"{pfx}m")),
       .RScalarSetExpr s!"{pfx}u3" (.SAdd (e 3) (k' 3)),
       .RScalarSetExpr s!"{pfx}r3" (.SAdd (v s!"{pfx}u3") (c 2)) ]
  ++ storeHalf (pfx ++ "r") o

/-! ## 3. The three straight-line bodies -/

/-- `j_bn254_Fp2_add` body: componentwise 4-limb modadd on the two halves. -/
def fp2AddBody : LowCT :=
  seqAll (idxInit ++ modAddHalf "u" 0 ++ modAddHalf "v" 4)

/-- `j_bn254_Fp2_sub` body: componentwise 4-limb modsub on the two halves. -/
def fp2SubBody : LowCT :=
  seqAll (idxInit ++ modSubHalf "u" 0 ++ modSubHalf "v" 4)

/-- `j_bn254_Fp2_felem_copy` body: eight load/store pairs. -/
def fp2CopyBody : LowCT :=
  seqAll (idxInit
    ++ (List.range 8).flatMap (fun j =>
        [ (.RArrLoad ⟨s!"cw{j}", .TU64⟩ ⟨"x", .TBytes 64⟩ s!"ix{j}" : LowCT),
          .RArrStore ⟨"out", .TBytes 64⟩ s!"ix{j}" ⟨s!"cw{j}", .TU64⟩ ]))

/-! ## 4. Input contexts + `VarMap`s

`comToLfundef` reverses context↔argument order: `argName j` is context entry
`nArgs−1−j`.  To land `out ← argName 0 ← RDI`, `x ← RSI`, `y ← RDX`, `out`
must be bound first (deepest) and the context (head-first) is `[y, x, out]`. -/

/-- Binary-kernel context, head-first `[y, x, out]` (all 8-cell memrefs). -/
def inΓ3 : Ctx := [.memref 8, .memref 8, .memref 8]

/-- Binary-kernel `VarMap`: `out` deepest (→ RDI), then `x` (→ RSI), then `y`
    (head, → RDX). -/
def inVM3 : VarMap inΓ3 :=
  ((VarMap.empty.bind (t := .memref 8) "out").bind
    (t := .memref 8) "x").bind (t := .memref 8) "y"

/-- Unary-kernel context, head-first `[x, out]`. -/
def inΓ2 : Ctx := [.memref 8, .memref 8]

/-- Unary-kernel `VarMap`: `out` deepest (→ RDI), then `x` (head, → RSI). -/
def inVM2 : VarMap inΓ2 :=
  (VarMap.empty.bind (t := .memref 8) "out").bind (t := .memref 8) "x"

/-! ## 5. Front-compile, lower, render -/

/-- Push a body through the carry-selecting front at context `Γ`/`vm` and cap
    with `ret out` (the post-store memref).  `none` if the front declines. -/
def frontCom {Γ : Ctx} (vm : VarMap Γ) (body : LowCT) :
    Option (Com catCryptDialect Γ (.memref 8)) :=
  match translateDialectCarrySelect vm body with
  | some r =>
      match r.vm.lookup "out" with
      | some ⟨.memref 8, vv⟩ => r.cont (Com.ret (toVIRVar vv))
      | _ => none
  | none => none

/-- The front-emitted `j_bn254_Fp2_add` dialect program. -/
def addFrontCom : Option (Com catCryptDialect inΓ3 (.memref 8)) :=
  frontCom inVM3 fp2AddBody
/-- The front-emitted `j_bn254_Fp2_sub` dialect program. -/
def subFrontCom : Option (Com catCryptDialect inΓ3 (.memref 8)) :=
  frontCom inVM3 fp2SubBody
/-- The front-emitted `j_bn254_Fp2_felem_copy` dialect program. -/
def copyFrontCom : Option (Com catCryptDialect inΓ2 (.memref 8)) :=
  frontCom inVM2 fp2CopyBody

/-- Lower a front dialect program to a `Com jasminDialect`
    (`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore`). -/
def toJasmin {Γ : Ctx} (com : Option (Com catCryptDialect Γ (.memref 8))) :
    Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t) :=
  match com with
  | some c =>
      match DialectToJasminCom.cryptoDialectToJasminCom c with
      | some jc => some ⟨_, _, jc⟩
      | none => none
  | none => none

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Com.toLprogPhysAbi Lprog)

/-- Render an owned `Lprog` for a lowered kernel under the SysV pointer ABI
    (`abiArgs`, eight `u64` cells per pointer). The ADX carry-chain fuser
    (`AdxChainFuse.fuseAdxChain`) runs after physical lowering and before the AT&T
    printer, coalescing each value-threaded `ADCX`/`ADCXHI`/`ADCX` limb triple into
    a live-flag `adcx` chain (dropping the `setc`/`movzbq`/`bt` round-trip). -/
def toAsm (name : String) (abiArgs : List String)
    (j : Option (Σ Γj : Ctxt jasminDialect, Σ t : JasminTy, Com jasminDialect Γj t)) :
    Option String :=
  (j.map (fun s =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.AdxChainFuse.fuseAdxChain
      (Com.toLprogPhysAbi s.2.2 name
        (fun _ => none) (fun _ => none) (fun _ => none) []
        (abiArgs := abiArgs) (abiTyin := abiArgs.map (fun _ => 64))
        (residence := none) (abiW := 0)
        (forceLivePin := true)))).map CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned

/-- The owned AT&T `.s` of `j_bn254_Fp2_add` (RDI = out, RSI = x, RDX = y). -/
def addAsm : Option String :=
  toAsm "j_bn254_Fp2_add" ["RDI", "RSI", "RDX"] (toJasmin addFrontCom)
/-- The owned AT&T `.s` of `j_bn254_Fp2_sub` (RDI = out, RSI = x, RDX = y). -/
def subAsm : Option String :=
  toAsm "j_bn254_Fp2_sub" ["RDI", "RSI", "RDX"] (toJasmin subFrontCom)
/-- The owned AT&T `.s` of `j_bn254_Fp2_felem_copy` (RDI = out, RSI = x). -/
def copyAsm : Option String :=
  toAsm "j_bn254_Fp2_felem_copy" ["RDI", "RSI"] (toJasmin copyFrontCom)

/-- The three bodies front-compile (`translateDialectControl` + `ret out`). -/
theorem frontCom_isSome :
    addFrontCom.isSome ∧ subFrontCom.isSome ∧ copyFrontCom.isSome := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The three kernels lower end-to-end to `Com jasminDialect` and render to
    owned `.s` (no hand `Com`/`Lcmd`, no jasminc). -/
theorem kernelAsm_clean :
    addAsm.isSome ∧ subAsm.isSome ∧ copyAsm.isSome := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. In-model `denote = spec` vs the INDEPENDENT `Nat` `% p` spec

The valuations bind each pointer's eight cells; the denotation returns the
post-store `out` memref.  The specs recombine each half to a `Nat`, apply
`Nat` `%` arithmetic directly, and split back into limbs — independent of the
emitted carry-chain shape. -/

/-- Recombine cells `o..o+3` of an 8-word vector. -/
def valH (ws : List Nat) (o : Nat) : Nat :=
  ws[o]! + 2 ^ 64 * ws[o + 1]! + 2 ^ 128 * ws[o + 2]! + 2 ^ 192 * ws[o + 3]!

/-- Split a `Nat` into four little-endian 64-bit limbs. -/
def limbs4 (n : Nat) : List Nat :=
  [n % 2 ^ 64, n / 2 ^ 64 % 2 ^ 64, n / 2 ^ 128 % 2 ^ 64, n / 2 ^ 192 % 2 ^ 64]

/-- Independent spec of `Fp2` add: componentwise `(x + y) % p`. -/
def addSpec (x y : List Nat) : List Nat :=
  limbs4 ((valH x 0 + valH y 0) % pNat) ++ limbs4 ((valH x 4 + valH y 4) % pNat)

/-- Independent spec of `Fp2` sub: componentwise `(x + p − y) % p`. -/
def subSpec (x y : List Nat) : List Nat :=
  limbs4 ((valH x 0 + pNat - valH y 0) % pNat)
    ++ limbs4 ((valH x 4 + pNat - valH y 4) % pNat)

/-- An 8-cell memref valuation from a list of words. -/
def vecOf (ws : List Nat) : Fin 8 → BitVec 64 :=
  fun i => BitVec.ofNat 64 ws[i.val]!

/-- Binary-kernel valuation, head-first `[y, x, out]` (matches `inΓ3`). -/
def encodeVal3 (xv yv : Fin 8 → BitVec 64) : @Ctxt.Valuation catCryptDialect _ inΓ3 :=
  .cons yv (.cons xv (.cons (fun _ => (0 : BitVec 64)) .nil))

/-- Unary-kernel valuation, head-first `[x, out]` (matches `inΓ2`). -/
def encodeVal2 (xv : Fin 8 → BitVec 64) : @Ctxt.Valuation catCryptDialect _ inΓ2 :=
  .cons xv (.cons (fun _ => (0 : BitVec 64)) .nil)

/-- Denote a binary front kernel and read out all eight cells. -/
def denoteCells3 (com : Option (Com catCryptDialect inΓ3 (.memref 8)))
    (x y : List Nat) : Option (List Nat) :=
  com.map (fun c =>
    (List.range 8).map (fun i =>
      (c.denote (encodeVal3 (vecOf x) (vecOf y)) ⟨i % 8, Nat.mod_lt _ (by decide)⟩).toNat))

/-- Denote the unary front kernel and read out all eight cells. -/
def denoteCells2 (com : Option (Com catCryptDialect inΓ2 (.memref 8)))
    (x : List Nat) : Option (List Nat) :=
  com.map (fun c =>
    (List.range 8).map (fun i =>
      (c.denote (encodeVal2 (vecOf x)) ⟨i % 8, Nat.mod_lt _ (by decide)⟩).toNat))

/-- The published EIP-197 BN254 G2 generator `Qx` (Montgomery form) — the
    `bn254_tower_kat.rs` anchor. -/
def qxW : List Nat :=
  [0x8e83b5d102bc2026, 0xdceb1935497b0172, 0xfbb8264797811adf, 0x19573841af96503b,
   0xafb4737da84c6140, 0x6043dd5a5802d8c4, 0x09e950fc52a02f86, 0x14fef0833aea7b6b]

/-- The published EIP-197 BN254 G2 generator `Qy` (Montgomery form). -/
def qyW : List Nat :=
  [0x619dfa9d886be9f6, 0xfe7fd297f59e9b78, 0xff9e1a62231b7dfe, 0x28fd7eebae9e4206,
   0x64095b56c71856ee, 0xdc57f922327d3cbb, 0x55f935be33351076, 0x0da4a0e693fd6482]

/-- `Fp2` zero. -/
def zeroW : List Nat := [0, 0, 0, 0, 0, 0, 0, 0]

/-- Both halves `p − 1` (the largest canonical residue). -/
def pm1W : List Nat := limbs4 (pNat - 1) ++ limbs4 (pNat - 1)

/-- Both halves `1`. -/
def oneW : List Nat := [1, 0, 0, 0, 1, 0, 0, 0]

/-- Add sample pairs: the EIP-197 anchor both ways plus carry / reduction
    edges (`(p−1) + (p−1)` exercises the subtract path; `(p−1) + 1 = p ↦ 0`
    the exact-`p` edge; `0 + (p−1)` the no-subtract path). -/
def addSamples : List (List Nat × List Nat) :=
  [ (qxW, qyW), (qyW, qxW), (zeroW, zeroW), (pm1W, pm1W), (pm1W, oneW),
    (zeroW, pm1W), (qxW, pm1W) ]

/-- Sub sample pairs: the anchor both ways (one direction borrows), `x − x`,
    `0 − 1` (full borrow ↦ `p − 1`), `(p−1) − 1`. -/
def subSamples : List (List Nat × List Nat) :=
  [ (qxW, qyW), (qyW, qxW), (qxW, qxW), (zeroW, oneW), (pm1W, oneW),
    (zeroW, pm1W) ]

/-- **`j_bn254_Fp2_add` denote = independent spec** on every sample pair. -/
theorem add_denote_spec :
    addSamples.all (fun (x, y) =>
      denoteCells3 addFrontCom x y == some (addSpec x y)) = true := by
  native_decide

/-- **`j_bn254_Fp2_sub` denote = independent spec** on every sample pair. -/
theorem sub_denote_spec :
    subSamples.all (fun (x, y) =>
      denoteCells3 subFrontCom x y == some (subSpec x y)) = true := by
  native_decide

/-- **`j_bn254_Fp2_felem_copy` denote = identity** on the sample vectors. -/
theorem copy_denote_spec :
    [qxW, qyW, pm1W, oneW].all (fun x =>
      denoteCells2 copyFrontCom x == some x) = true := by
  native_decide

/-! ## 7. Emit driver -/

/-- Write the three front-generated kernels into ONE owned `.s`. -/
def emit (path : System.FilePath) : IO Unit := do
  match addAsm, subAsm, copyAsm with
  | some aa, some sa, some ca =>
      IO.FS.writeFile path (aa ++ "\n" ++ sa ++ "\n" ++ ca)
  | _, _, _ =>
      throw (IO.userError
        "front-compile of the BN254 Fp2 tower kernels failed (front/lowering declined)")

end CatCrypt.Crypto.SecureCompilation.Bn254TowerFrontEmit
