/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulOwnedEmit

set_option autoImplicit false

/-!
# plonky3 `fri_proof`: the FRONT-COMPILED spine phases, validated against the spec pin

`bench/plonky3_compare/fri_proof_link.s` (whitelist row `# L`) is the jasminc
compilation of `plonky3_fri_prove_obj`
(`bench/plonky3_compare/include/plonky3_fri_proof_leaves.jinc`), a whole-prover
spine: per layer `L < 4` — leaf-hash the codeword, Merkle-commit, open 3 queries
with 2 authentication paths each, FRI-fold — then the degree-1 remainder.  Its
bit-exact executable reference is the spec pin
`bench/plonky3_compare/fri_proof_ref.lean` (machine-validated word-for-word over
the full 546-word object against the independent C oracle
`bench_fri_proof_from_rustcmd.c`).  The pin is the acceptance oracle for any
owned re-emit; `bench/` files are not importable, so §1 restates the needed
fragment verbatim (same definitions, same KAT inputs).

This module front-compiles the spine's phase families through the committed
front combinators — no hand-authored `Com`/`Lcmd`/`JInstr`/`.s`:

* **§3–§4 The FRI fold chain + remainder (5 phases, ONE `ComL` spine).**
  `foldChainComL` chains four per-layer fold loops and the remainder through
  `rolledForLoopNRtCont` (each phase's `.ret .here` replaced by the
  front-compiled next phase).  The per-trip body is covered LowCT: Barrett
  `(a·b) mod p` over `SMul`/`SMulHiU` + the branchless conditional subtraction,
  and the fold-point weight `inv(2x_i) = inv2 · ω_L^{-i}` recomputed per trip
  from the loop counter's bits (no loop-carried multiplier, so the single
  accumulator is the codeword buffer itself; the folded values are the same
  canonical field elements the pin computes via `_fp_inv`).
  `denote = the pin's fold/remainder values` at the pin's KAT inputs
  (coeffs `{7,3,5,2}` column LDE, alpha `{101,202,303,404}`), including
  count-driven prefix runs (counts `(16,0,0,0)` stop after layer 0).

* **§5–§6 The Merkle commit (leaf-hash ; level-compress), leaf-hash phase
  continuation-composed with a genuine NESTED runtime loop.**
  `merkleComL` = `rolledForLoopNRtCont` (leaf-hash loop, the 4-lane
  wrapping-u64 `_p3_hleaf_u64` mixer inlined as covered LowCT) whose
  continuation is `rolledForLoopNRtNested` (outer level `lvl < log₂ n`, inner
  trip `n >> (lvl+1)` recomputed per level — the halving shape — with the
  `_p3_compress_u64` mixer inlined).  The tree is built in ONE flat buffer with
  shift-computed level bases (`8n − (8n >> lvl)` lanes), so no ping-pong buffer
  is needed; the produced digests are identical to the pin's ping-pong
  `merkleRoot`.  `denote = the pin's `buildLeafHashes` leaf level AND
  `merkleRoot` root` at `n = 8` on pin-derived data.

* **§4b The fold chain at COMPILE-TIME counts (two registers).**
  `foldChainFxComL` is the same 5-phase spine through the fixed-trip
  continuation combinator `rolledForLoopNCont`
  (`TranslateDialectPhaseCompose` §2b): every trip count (`16 >> L`, `1`) lives
  in the loop node, the ABI is `(acc, alpha)`, and no SysV integer register
  carries a count — the whole-spine count-argument pressure is gone.
  `denote` = the same pin fold/remainder values as §4.

* **§6b The query/auth-path walk (3 query phases, ONE `ComL`).**
  Per query `q`: ONE runtime-trip loop over tree levels — NO loop-carried
  walker (level-`l` sibling is `(pos >> l) ^ 1`, its digest at the §5 flat base
  `256 − (256 >> l)`, all recomputed from the loop counter each trip); the
  openings `cur[ipos]`/`cur[ineg]`, the index words, and the root copy are
  written idempotently per trip.  `denote` = the pin's WHOLE 136-word layer-0
  proof block (`friProveObj` words `0..135`) on a flat tree seeded with the
  pin's level digests.

* **§6c ONE layer, ONE `ComL` (all four phase families chained).**
  `layerSpine` = fixed-trip leaf-hash (`rolledForLoopNCont`) ; mid-chain
  nested level-compress (`rolledForLoopNRtNestedCont`) ; the three §6b walks ;
  the fixed-count layer-0 fold.  The tree is seeded ZERO — the walks read
  digests the spine itself built.  `denote` = the pin's layer-0 block
  (`layer_denote_block`) and the pin's layer-1 codeword (`layer_denote_fold`).

## What still blocks the whole-artifact flip (precise; the row stays `# L`)

1. **Whole-spine assembly breadth.**  A full `plonky3_fri_prove_obj` is ~50
   chained phases (4 layers × (leaf-hash ; nested Merkle ; 3 queries × (opening
   ; 2 path walks) ; fold) + remainder).  Every phase family is now
   front-compiled AND chained for one whole layer (§6c); the remaining assembly
   is the 4-layer fan-out — per-layer constants (`n = 32 >> L`, flat bases,
   `qb = 136·L + …`) and the layer-`L` codeword hand-off — mechanical breadth,
   not a front gap.
2. **Multi-written-buffer physAbi render.**  The §6c layer spine writes THREE
   caller buffers (tree, proof block, codeword) through distinct pointer
   arguments; `ComL.toLfundefPhysAbi` is structurally single-written-out — it
   takes ONE `outArg` and aliases exactly that acc thread
   (`aliasRegBody`/`canonicalizeMemrefThread`); `inArgs` bases get their own
   qsave reload slots but their memref THREADS (the rebound acc vars of a
   phase whose accumulator is not `outArg`) are never canonicalized onto one
   pointer.  Rendering the §6c spine needs the export generalized to a LIST
   of written-buffer threads (per-thread alias + per-thread reload slot).
   The §6c spine is therefore pinned in-model only, and the rendered
   fragments (§7) stay single-out-buffer.  (An alternative whole-artifact
   route with no export change: per-layer single-out fragments — counts AND
   flat bases as register args — composed by an owned `Com.toLprogArrAbi`
   call-orchestration, the `bn254_orch_owned.s` pattern.)
3. **imm64 render.**  The Barrett constant `μ = ⌊2⁶⁴/p⌋` and the mixer constants
   (`0x9E3779B97F4A7C15`, `0xBF58476D1CE4E5B9`) are 64-bit immediates; §7 gates
   the rendered `.s` on the absence of `UNHANDLED` markers, but a byte-KAT of
   the rendered fragments against the C oracle is the orchestrator's asm-gate
   (in-model `denote = spec` is NOT the asm-KAT).

No `sorry`, no new axiom.

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/VIR/Plonky3FriProofFrontEmit.lean
Invoke (emit the fragment `.s`):
  lake env lean --run bench/plonky3_compare/fri_frontphases_emit.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
  (rolledForLoopNRtCont rolledForLoopNCont rolledForLoopNRtNestedCont)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. The spec-pin fragment (restated from `bench/plonky3_compare/fri_proof_ref.lean`)

The definitions below are the pin's, verbatim (same names, same arithmetic, same
KAT inputs) — the pin file lives under `bench/` and cannot be imported.  The pin
itself is machine-validated word-for-word against the independent C oracle, so
these ARE the acceptance semantics. -/

/-- BabyBear prime `p = 2^31 - 2^27 + 1` (pin). -/
def bbP : UInt64 := 2013265921
/-- BabyBear multiplicative generator (pin). -/
def bbG : UInt64 := 31

/-- `_fp_reduce`: branchless single conditional subtraction of `p` (pin). -/
def fReduce (x : UInt64) : UInt64 :=
  let t := x - bbP
  let m := if (t >>> 63) == 1 then bbP else 0
  t + m

def fAdd (a b : UInt64) : UInt64 := fReduce (a + b)
def fSub (a b : UInt64) : UInt64 := fReduce (bbP + a - b)
/-- `(a*b) mod p` for canonical operands (pin). -/
def fMul (a b : UInt64) : UInt64 := (a * b) % bbP

/-- 64-iteration square-and-multiply (pin). -/
def fPow (base exp : UInt64) : UInt64 := Id.run do
  let mut r : UInt64 := 1
  let mut c : UInt64 := base % bbP
  let mut e : UInt64 := exp
  for _ in [0:64] do
    if (e &&& 1) == 1 then r := fMul r c
    c := fMul c c
    e := e >>> 1
  return r

/-- Fermat inverse, `0 ↦ 0` (pin). -/
def fInv (a : UInt64) : UInt64 := if a == 0 then 0 else fPow a (bbP - 2)

/-- `bb_root_of_unity(k) = G^((p-1) >> k)` (pin). -/
def fRou (k : Nat) : UInt64 := fPow bbG ((bbP - 1) >>> (UInt64.ofNat k))

/-- Horner poly evaluation (pin). -/
def fPolyEval (coeffs : Array UInt64) (x : UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for i in [0:coeffs.size] do
    let idx := coeffs.size - 1 - i
    acc := fAdd (fMul acc x) coeffs[idx]!
  return acc

/-- `fri_fold`: `p'(x^2) = (p(x)+p(-x))/2 + alpha*(p(x)-p(-x))/(2x)` (pin). -/
def friFold (ep en x alpha : UInt64) : UInt64 :=
  let sum := fAdd ep en
  let diff := fSub ep en
  let inv2 := fInv 2
  let inv2x := fInv (fMul 2 x)
  let peven := fMul sum inv2
  let podd := fMul diff inv2x
  fAdd peven (fMul alpha podd)

/-- `_p3_hleaf_u64(v)` — the 4-lane wrapping-u64 leaf mixer (pin). -/
def golden : UInt64 := 0x9E3779B97F4A7C15
def split  : UInt64 := 0xBF58476D1CE4E5B9

def p3Hleaf (v : UInt64) : Array UInt64 := Id.run do
  let mut o : Array UInt64 := Array.replicate 4 0
  let mut cur := v
  for i in [0:4] do
    let t := (cur * golden + UInt64.ofNat i) * split
    o := o.set! i t
    cur := t
  let mut prev := o[0]!
  for i in [1:4] do
    prev := prev * 0xA3
    o := o.set! i (o[i]! + prev)
    prev := o[i]!
  return o

/-- `_p3_compress_u64(l, r)` — the 4-lane two-to-one mixer (pin). -/
def p3Compress (l r : Array UInt64) : Array UInt64 := Id.run do
  let mut o : Array UInt64 := Array.replicate 4 0
  for i in [0:4] do
    let a := l[i]!
    let b := r[i]!
    let t := (a + b) * 0x9E + UInt64.ofNat i
    let x := a * 0x6D
    o := o.set! i ((t ^^^ x) ^^^ b)
  let mut prev := o[0]!
  for i in [1:4] do
    prev := prev * 0xC5
    o := o.set! i (o[i]! ^^^ prev)
    prev := o[i]!
  return o

/-- Leaf-hash array for `n` field words (pin, 128-lane buffer). -/
def buildLeafHashes (cur : Array UInt64) (n : Nat) : Array UInt64 := Id.run do
  let mut leaves : Array UInt64 := Array.replicate 128 0
  for i in [0:n] do
    let d := p3Hleaf cur[i]!
    for j in [0:4] do leaves := leaves.set! (i*4 + j) d[j]!
  return leaves

/-- Merkle root by ping-pong halving compress (pin). -/
def merkleRoot (leaves : Array UInt64) (n : Nat) : Array UInt64 := Id.run do
  let mut a := leaves
  let mut pairs := n
  while pairs > 1 do
    let mut b : Array UInt64 := Array.replicate 128 0
    for j in [0:pairs/2] do
      let lo := Array.ofFn (n := 4) (fun k => a[(2*j)*4 + k.val]!)
      let hi := Array.ofFn (n := 4) (fun k => a[(2*j+1)*4 + k.val]!)
      let d := p3Compress lo hi
      for k in [0:4] do b := b.set! (j*4 + k) d[k]!
    a := b
    pairs := pairs / 2
  return Array.ofFn (n := 4) (fun k => a[k.val]!)

/-- Authentication path (20 words = 5 sibling digests) for `leafIndex` (pin). -/
def merklePath (leaves : Array UInt64) (n : Nat) (leafIndex : Nat) : Array UInt64 := Id.run do
  let mut outPath : Array UInt64 := Array.replicate 20 0
  let mut a := leaves
  let mut pairs := n
  let mut level := 0
  let mut x := leafIndex
  while pairs > 1 do
    let sib := x ^^^ 1
    for k in [0:4] do outPath := outPath.set! (level*4 + k) a[sib*4 + k]!
    let mut b : Array UInt64 := Array.replicate 128 0
    for j in [0:pairs/2] do
      let lo := Array.ofFn (n := 4) (fun k => a[(2*j)*4 + k.val]!)
      let hi := Array.ofFn (n := 4) (fun k => a[(2*j+1)*4 + k.val]!)
      let d := p3Compress lo hi
      for k in [0:4] do b := b.set! (j*4 + k) d[k]!
    a := b
    pairs := pairs / 2
    x := x >>> 1
    level := level + 1
  return outPath

/-- The KAT column LDE `p(x) = 7 + 3x + 5x² + 2x³` on `K₃₂` (pin). -/
def buildColumnLde : Array UInt64 := Id.run do
  let coeffs : Array UInt64 := #[7, 3, 5, 2]
  let omega := fRou 5
  let mut evals : Array UInt64 := Array.replicate 32 0
  let mut x : UInt64 := 1
  for i in [0:32] do
    evals := evals.set! i (fPolyEval coeffs x)
    x := fMul x omega
  return evals

/-- The KAT layer challenges (pin). -/
def alphaKAT : Array UInt64 := #[101, 202, 303, 404]

/-- The KAT query indices (pin). -/
def qidxKAT : Array UInt64 := #[3, 11, 26, 0]

/-- The pin's fold arm: `cur` after the first `k` FRI fold layers (mirrors the
    `friProveObj` Phase-3 loop verbatim — fresh `next` buffer, rolling `xpow`). -/
def foldLayersSpec (evals alpha : Array UInt64) (k : Nat) : Array UInt64 := Id.run do
  let mut cur := evals
  for L in [0:k] do
    let n := 32 >>> L
    let half := n / 2
    let logn := 5 - L
    let ol := fRou logn
    let a := alpha[L]!
    let mut next : Array UInt64 := Array.replicate 32 0
    let mut xpow : UInt64 := 1
    for i in [0:half] do
      next := next.set! i (friFold cur[i]! cur[i + half]! xpow a)
      xpow := fMul xpow ol
    cur := next
  return cur

/-- The pin's remainder arm: `[(e0+e1)/2, (e0-e1)/2]` of the final codeword. -/
def remainderSpec (cur : Array UInt64) : Array UInt64 :=
  let inv2 := fInv 2
  #[fMul (fAdd cur[0]! cur[1]!) inv2, fMul (fSub cur[0]! cur[1]!) inv2]

/-! The pin's whole prover (layout constants + `friProveObj`, verbatim) — the
acceptance semantics for the query/auth-path phases: the layer-0 block is
`proof[0..135]` (root lanes `0..3`, then 3 queries × 44 words each). -/

def numLayers : Nat := 4
def numQueries : Nat := 3
def layerU64 : Nat := 136
def pathU64 : Nat := 20
def queryU64 : Nat := 44
def lanes : Nat := 4
def proofU64 : Nat := 546

/-- `plonky3_fri_prove_obj`: the flat 546-word FRI proof object (pin). -/
def friProveObj (evals alpha qidx : Array UInt64) : Array UInt64 := Id.run do
  let mut proof : Array UInt64 := Array.replicate proofU64 0
  let mut cur := evals
  for L in [0:numLayers] do
    let n := 32 >>> L
    let half := n / 2
    let logn := 5 - L
    let lbase := L * layerU64
    let leaves := buildLeafHashes cur n
    let root := merkleRoot leaves n
    for k in [0:4] do proof := proof.set! (lbase + k) root[k]!
    for q in [0:numQueries] do
      let qb := lbase + lanes + q * queryU64
      let ipos := (qidx[q]!.toNat) % n
      let ineg := (ipos + half) % n
      proof := proof.set! (qb + 0) cur[ipos]!
      proof := proof.set! (qb + 1) cur[ineg]!
      proof := proof.set! (qb + 2) (UInt64.ofNat ipos)
      proof := proof.set! (qb + 3) (UInt64.ofNat ineg)
      let pp := merklePath leaves n ipos
      for k in [0:20] do proof := proof.set! (qb + 4 + k) pp[k]!
      let pn := merklePath leaves n ineg
      for k in [0:20] do proof := proof.set! (qb + 4 + pathU64 + k) pn[k]!
    let ol := fRou logn
    let a := alpha[L]!
    let mut next : Array UInt64 := Array.replicate 32 0
    let mut xpow : UInt64 := 1
    for i in [0:half] do
      next := next.set! i (friFold cur[i]! cur[i + half]! xpow a)
      xpow := fMul xpow ol
    cur := next
  let inv2 := fInv 2
  proof := proof.set! (numLayers * layerU64 + 0) (fMul (fAdd cur[0]! cur[1]!) inv2)
  proof := proof.set! (numLayers * layerU64 + 1) (fMul (fSub cur[0]! cur[1]!) inv2)
  return proof

/-! ## 2. Covered-LowCT field macros (Barrett mul, branchless csub)

Statement-level macros (each intermediate is a fresh named scalar, so no
subexpression is duplicated — the lowered op count is linear).  The Barrett
constant `μ = ⌊2⁶⁴/p⌋` gives `q = hi64(x·μ) ∈ {⌊x/p⌋-1, ⌊x/p⌋}` for `x < 2⁶²`,
so two conditional subtractions canonicalise `x - q·p`.  The branchless csub is
the `_fp_reduce` shape (dialect `bvSub` wraps, so `(t >>> 63)` is the borrow). -/

/-- `p` as a `Nat` literal. -/
def bbPn : Nat := 2013265921
/-- Barrett constant `μ = ⌊2⁶⁴ / p⌋`. -/
def muBB : Nat := (2 ^ 64) / bbPn
/-- `inv2 = (p+1)/2`, pinned through the pin's own `fInv`. -/
def inv2n : Nat := (fInv 2).toNat

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- `RScalarSetExpr` shorthand. -/
def setE (x : String) (e : SExpr) : LowCT := .RScalarSetExpr x e

/-- Branchless conditional subtraction: `dst := src - p + (p if src < p)`. -/
def csubL (dst src : String) : List LowCT :=
  [ setE (dst ++ "T") (.SSub (.SVar src) (.SLit bbPn)),
    setE (dst ++ "M") (.SAnd (.SLit bbPn)
      (.SSub (.SLit 0) (.SShr (.SVar (dst ++ "T")) (.SLit 63)))),
    setE dst (.SAdd (.SVar (dst ++ "T")) (.SVar (dst ++ "M"))) ]

/-- Barrett `(a·b) mod p` (operands canonical, product < 2⁶²): low product,
    `q = hi64(lo·μ)`, `r = lo - q·p`, two csubs.

    `μ` is bound ONCE (`Mu`) and a **discarded** low `μ`-product (`QloD`, never
    read) precedes the `SMulHiU` — the `FheShoupOwnedEmit` recipe: post-RA the
    two are exactly the shared-second-source `MUL` + `MULXHI` pair
    `fuseMulHiLprog` keys on, so the standalone high word materialises as ONE
    real two-output `mulx` (the renderer issues no standalone `MULXHI` line —
    an unfused high-word binding would drop the write). -/
def mulL (dst : String) (a b : SExpr) : List LowCT :=
  [ setE (dst ++ "Lo") (.SMul a b),
    setE (dst ++ "Mu") (.SLit muBB),
    setE (dst ++ "QloD") (.SMul (.SVar (dst ++ "Lo")) (.SVar (dst ++ "Mu"))),
    setE (dst ++ "Q") (.SMulHiU (.SVar (dst ++ "Lo")) (.SVar (dst ++ "Mu"))),
    setE (dst ++ "R") (.SSub (.SVar (dst ++ "Lo"))
      (.SMul (.SVar (dst ++ "Q")) (.SLit bbPn))) ]
  ++ csubL (dst ++ "C") (dst ++ "R") ++ csubL dst (dst ++ "C")

/-- `(a+b) mod p` for canonical operands: one csub. -/
def addL (dst : String) (a b : SExpr) : List LowCT :=
  [ setE (dst ++ "S") (.SAdd a b) ] ++ csubL dst (dst ++ "S")

/-- `(p + a - b) mod p` for canonical operands: one csub. -/
def subL (dst : String) (a b : SExpr) : List LowCT :=
  [ setE (dst ++ "D") (.SSub (.SAdd (.SLit bbPn) a) b) ] ++ csubL dst (dst ++ "D")

/-! ## 3. The FRI fold chain, front-compiled (4 fold phases + remainder, ONE `ComL`)

Accumulator layout: `acc : memref 34` — slots `0..31` the in-place codeword
(layer `L` writes `acc[i]` for `i < 16 >> L`, reading `acc[i]` and
`acc[i + 16>>L]`; the tail keeps stale previous-layer words the later phases
never read), slots `32/33` the remainder coefficients.

The fold-point weight is recomputed per trip from the counter's bits:
`inv(2·ω_L^i) = inv2 · Π_b (ω_L^{-2^b})^{bit_b(i)}` — the per-layer constants
`ω_L^{-2^b}` are computed through the pin's own `fPow`/`fInv`/`fRou` (§1), so
the emitted immediates are pinned to the pin's arithmetic, and the folded
values are the same canonical field elements the pin computes via `_fp_inv`. -/

/-- `ω_L = rou(5-L)` raised to `-2^b`: the layer-`L` bit-`b` inverse-power. -/
def olInvPow (L b : Nat) : Nat :=
  (fPow (fInv (fRou (5 - L))) (UInt64.ofNat (1 <<< b))).toNat

/-- The `acc` array slot (34 words). -/
def accArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"acc", .TBytes (8 * 34)⟩
/-- The `alpha` array slot (4 words). -/
def alphaArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"alpha", .TBytes (8 * 4)⟩

/-- One fold trip of layer `L`:
    `acc[idx] := friFold acc[idx] acc[idx + 16>>L] (ω_L^idx) alpha[L]`,
    with `inv(2x)` recomputed from `idx`'s bits (covered LowCT, no call). -/
def foldBody (L : Nat) : LowCT := seqAll <|
  [ setE "ih" (.SAdd (.SVar "idx") (.SLit (16 >>> L))),
    .RArrLoad ⟨"ep", .TU64⟩ accArr "idx",
    .RArrLoad ⟨"en", .TU64⟩ accArr "ih",
    setE "lc" (.SLit L),
    .RArrLoad ⟨"av", .TU64⟩ alphaArr "lc" ]
  ++ addL "sum" (.SVar "ep") (.SVar "en")
  ++ subL "dif" (.SVar "ep") (.SVar "en")
  ++ [ setE "w0" (.SLit inv2n) ]
  ++ (List.range (4 - L)).flatMap (fun b =>
      [ setE s!"m{b}" (.SSub (.SLit 0)
          (.SAnd (.SShr (.SVar "idx") (.SLit b)) (.SLit 1))),
        setE s!"f{b}" (.SXor (.SLit 1)
          (.SAnd (.SXor (.SLit 1) (.SLit (olInvPow L b))) (.SVar s!"m{b}"))) ]
      ++ mulL s!"w{b+1}" (.SVar s!"w{b}") (.SVar s!"f{b}"))
  ++ mulL "pe" (.SVar "sum") (.SLit inv2n)
  ++ mulL "po" (.SVar "dif") (.SVar s!"w{4-L}")
  ++ mulL "ap" (.SVar "av") (.SVar "po")
  ++ addL "tt" (.SVar "pe") (.SVar "ap")
  ++ [ .RArrStore accArr "idx" ⟨"tt", .TU64⟩ ]

/-- The remainder trip (idempotent — reads `acc[0..1]`, writes `acc[32..33]`):
    `acc[32] := (e0+e1)·inv2`, `acc[33] := (e0-e1)·inv2`. -/
def remBody : LowCT := seqAll <|
  [ setE "rz0" (.SLit 0), setE "rz1" (.SLit 1),
    setE "rz32" (.SLit 32), setE "rz33" (.SLit 33),
    .RArrLoad ⟨"re0", .TU64⟩ accArr "rz0",
    .RArrLoad ⟨"re1", .TU64⟩ accArr "rz1" ]
  ++ addL "rs" (.SVar "re0") (.SVar "re1")
  ++ subL "rd" (.SVar "re0") (.SVar "re1")
  ++ mulL "rc0" (.SVar "rs") (.SLit inv2n)
  ++ mulL "rc1" (.SVar "rd") (.SLit inv2n)
  ++ [ .RArrStore accArr "rz32" ⟨"rc0", .TU64⟩,
       .RArrStore accArr "rz33" ⟨"rc1", .TU64⟩ ]

/-- Fold-phase body context: accumulator `acc`, loop index `idx`, invariant
    `alpha`. -/
def foldΓ : Ctx := [.memref 34, .sword 64, .memref 4]

/-- Fold-phase VarMap. -/
def foldVm : VarMap foldΓ :=
  (((VarMap.empty.bind (t := .memref 4) "alpha").bind
      (t := .sword 64) "idx").bind (t := .memref 34) "acc")

/-- Remainder body context: accumulator `acc`, loop index `idx` (no invariant). -/
def remΓ : Ctx := [.memref 34, .sword 64]

/-- Remainder VarMap. -/
def remVm : VarMap remΓ :=
  ((VarMap.empty.bind (t := .sword 64) "idx").bind (t := .memref 34) "acc")

/-- The chain's outer (kernel-argument) context, newest-first:
    `[cnt3, cnt2, cnt1, cnt0, alpha, acc]` — ABI
    `p3_fri_fold_chain(acc, alpha, n0, n1, n2, n3)` =
    `(RDI, RSI, RDX, RCX, R8, R9)`. -/
abbrev ΓF : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .reg 64, .reg 64, .stackArr 64 4, .stackArr 64 34]

/-- The jasmin image of the fold accumulator. -/
abbrev accT : JasminTy := mapTy (CryptoTy.memref 34)

/-- Generic fold phase over any outer context (the combinator is context
    polymorphic; the chain instantiates it at successive extensions). -/
def phaseFold (L : Nat) {Γ : Ctxt jasminDialect}
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accT)
    (alphaV : Ctxt.Var Γ (mapTy (CryptoTy.memref 4)))
    {s : JasminTy} (cont : ComL (accT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNRtCont (Γouter := Γ) (accCTy := .memref 34)
    (invCTys := [.memref 4]) foldVm "acc" (foldBody L)
    count init (.cons alphaV .nil) cont

/-- Generic remainder phase. -/
def phaseRem {Γ : Ctxt jasminDialect}
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accT) :
    Option (ComL Γ accT) :=
  rolledForLoopNRtCont (Γouter := Γ) (accCTy := .memref 34)
    (invCTys := []) remVm "acc" remBody count init .nil (.ret .here)

/-- The whole fold chain: layer-0..3 folds then the remainder, ONE `ComL` spine
    (each phase is the previous phase's continuation; no hand-authored `Com`).
    Counts are runtime registers; the KAT driver passes `(16, 8, 4, 2)` (the
    remainder reuses `cnt3` — its body is idempotent). -/
def foldChainComL : Option (ComL ΓF accT) := do
  let pR ← phaseRem
    (Γ := accT :: accT :: accT :: accT :: ΓF)
    (count := .there (.there (.there (.there .here))))
    (init := .here)
  let p3 ← phaseFold 3
    (Γ := accT :: accT :: accT :: ΓF)
    (count := .there (.there (.there .here)))
    (init := .here)
    (alphaV := .there (.there (.there (.there (.there (.there (.there .here)))))))
    (cont := pR)
  let p2 ← phaseFold 2
    (Γ := accT :: accT :: ΓF)
    (count := .there (.there (.there .here)))
    (init := .here)
    (alphaV := .there (.there (.there (.there (.there (.there .here))))))
    (cont := p3)
  let p1 ← phaseFold 1
    (Γ := accT :: ΓF)
    (count := .there (.there (.there .here)))
    (init := .here)
    (alphaV := .there (.there (.there (.there (.there .here)))))
    (cont := p2)
  phaseFold 0
    (Γ := ΓF)
    (count := .there (.there (.there .here)))
    (init := .there (.there (.there (.there (.there .here)))))
    (alphaV := .there (.there (.there (.there .here))))
    (cont := p1)

/-- **The 5-phase fold chain front-compiles.** -/
theorem foldChainComL_isSome : foldChainComL.isSome := by native_decide

/-! ## 4. denote = the pin's fold/remainder values at the pin's KAT inputs -/

/-- KAT seed for the accumulator: `evals` (the pin's column LDE) in slots
    `0..31`, remainder slots zero. -/
def accSeed : Fin 34 → BitVec 64 := fun i =>
  if i.val < 32 then BitVec.ofNat 64 (buildColumnLde[i.val]!.toNat) else 0

/-- KAT alpha row. -/
def alphaSeed : Fin 4 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (alphaKAT[i.val]!.toNat)

/-- Outer valuation at counts `(n0, n1, n2, n3)`. -/
def foldVal (n0 n1 n2 n3 : Nat) : Ctxt.Valuation ΓF :=
  .cons (BitVec.ofNat 64 n3) (.cons (BitVec.ofNat 64 n2)
    (.cons (BitVec.ofNat 64 n1) (.cons (BitVec.ofNat 64 n0)
      (.cons alphaSeed (.cons accSeed .nil)))))

/-- Selected denoted slots of the chain result, as `List Nat`. -/
def foldDenoteSlots (n0 n1 n2 n3 : Nat) (idxs : List Nat) : Option (List Nat) :=
  foldChainComL.map (fun c =>
    idxs.map (fun i =>
      (ComL.denote c (foldVal n0 n1 n2 n3)
        ⟨i % 34, Nat.mod_lt _ (by decide)⟩).toNat))

/-- Spec-side slot list helper. -/
def specSlots (a : Array UInt64) (idxs : List Nat) : List Nat :=
  idxs.map (fun i => (a[i]!).toNat)

/-- **denote = the pin's final codeword + remainder** at the full KAT counts
    `(16, 8, 4, 2)`: `acc[0..1]` is the layer-4 codeword, `acc[32..33]` the
    remainder — the pin's `proof[544..545]`. -/
theorem foldChain_denote_full :
    foldDenoteSlots 16 8 4 2 [0, 1, 32, 33]
      = some (specSlots (foldLayersSpec buildColumnLde alphaKAT 4) [0, 1]
              ++ specSlots (remainderSpec (foldLayersSpec buildColumnLde alphaKAT 4)) [0, 1]) := by
  native_decide

/-- **denote = the pin's layer-0 fold** at counts `(16, 0, 0, 0)` (the later
    phases run zero trips — SAME program, count-driven): `acc[0..15]` is the
    16-word layer-1 codeword. -/
theorem foldChain_denote_layer0 :
    foldDenoteSlots 16 0 0 0 (List.range 16)
      = some (specSlots (foldLayersSpec buildColumnLde alphaKAT 1) (List.range 16)) := by
  native_decide

/-- **denote = the seed at all-zero counts** (every phase empty — the counts
    genuinely drive the fold). -/
theorem foldChain_denote_zero :
    foldDenoteSlots 0 0 0 0 (List.range 34)
      = some ((List.range 34).map (fun i =>
          (accSeed ⟨i % 34, Nat.mod_lt _ (by decide)⟩).toNat)) := by
  native_decide

/-! ## 4b. The fold chain at COMPILE-TIME trip counts — zero count registers

`rolledForLoopNCont` (the fixed-trip continuation combinator,
`TranslateDialectPhaseCompose` §2b) carries each phase's trip count in the loop
node itself (`16 >> L` per fold layer, `1` for the remainder), so the chain's
ABI shrinks from `(acc, alpha, n0, n1, n2, n3)` to `(acc, alpha)` — TWO
registers. A whole-spine assembly with many distinct compile-time counts
therefore consumes no SysV integer registers for counts at all. -/

/-- Generic fixed-trip fold phase: layer `L` at compile-time count `16 >> L`. -/
def phaseFoldFx (L : Nat) {Γ : Ctxt jasminDialect}
    (init : Ctxt.Var Γ accT)
    (alphaV : Ctxt.Var Γ (mapTy (CryptoTy.memref 4)))
    {s : JasminTy} (cont : ComL (accT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNCont (Γouter := Γ) (accCTy := .memref 34)
    (invCTys := [.memref 4]) (16 >>> L) foldVm "acc" (foldBody L)
    init (.cons alphaV .nil) cont

/-- Generic fixed-trip remainder phase (one trip). -/
def phaseRemFx {Γ : Ctxt jasminDialect} (init : Ctxt.Var Γ accT) :
    Option (ComL Γ accT) :=
  rolledForLoopNCont (Γouter := Γ) (accCTy := .memref 34)
    (invCTys := []) 1 remVm "acc" remBody init .nil (.ret .here)

/-- The two-register fold-chain context, newest-first: `[alpha, acc]` — ABI
    `p3_fri_fold_chain_fx(acc, alpha)` = `(RDI, RSI)`. -/
abbrev ΓFx : Ctxt jasminDialect := [.stackArr 64 4, .stackArr 64 34]

/-- The fold chain with ALL trip counts compile-time: layer-0..3 folds then the
    remainder, ONE `ComL` spine, no count arguments. -/
def foldChainFxComL : Option (ComL ΓFx accT) := do
  let pR ← phaseRemFx
    (Γ := accT :: accT :: accT :: accT :: ΓFx)
    (init := .here)
  let p3 ← phaseFoldFx 3
    (Γ := accT :: accT :: accT :: ΓFx)
    (init := .here)
    (alphaV := .there (.there (.there .here)))
    (cont := pR)
  let p2 ← phaseFoldFx 2
    (Γ := accT :: accT :: ΓFx)
    (init := .here)
    (alphaV := .there (.there .here))
    (cont := p3)
  let p1 ← phaseFoldFx 1
    (Γ := accT :: ΓFx)
    (init := .here)
    (alphaV := .there .here)
    (cont := p2)
  phaseFoldFx 0
    (Γ := ΓFx)
    (init := .there .here)
    (alphaV := .here)
    (cont := p1)

/-- **The fixed-count 5-phase fold chain front-compiles.** -/
theorem foldChainFxComL_isSome : foldChainFxComL.isSome := by native_decide

/-- Two-register valuation (alpha, acc — no counts). -/
def foldFxVal : Ctxt.Valuation ΓFx := .cons alphaSeed (.cons accSeed .nil)

/-- Selected denoted slots of the fixed-count chain result. -/
def foldFxDenoteSlots (idxs : List Nat) : Option (List Nat) :=
  foldChainFxComL.map (fun c =>
    idxs.map (fun i =>
      (ComL.denote c foldFxVal ⟨i % 34, Nat.mod_lt _ (by decide)⟩).toNat))

/-- **denote = the pin's final codeword + remainder** — same acceptance values as
    `foldChain_denote_full`, with every count carried in the loop nodes. -/
theorem foldChainFx_denote_full :
    foldFxDenoteSlots [0, 1, 32, 33]
      = some (specSlots (foldLayersSpec buildColumnLde alphaKAT 4) [0, 1]
              ++ specSlots (remainderSpec (foldLayersSpec buildColumnLde alphaKAT 4)) [0, 1]) := by
  native_decide

/-! ## 5. The Merkle commit: leaf-hash phase ; NESTED level-compress phase

Flat single-buffer tree at `n = 8` leaves: `nodes : memref 60` — level `l`
(row size `n >> l`) starts at lane `8n − (8n >> l)` (`0, 32, 48, 56`), root at
`56..59`.  Phase A leaf-hashes `src[i]` into row `i` (the `_p3_hleaf_u64` mixer
inlined); its continuation is the genuine nested runtime loop (outer `lvl < 3`,
inner `j < n >> (lvl+1)` recomputed per level) compressing row pairs with the
`_p3_compress_u64` mixer inlined.  The digests are identical to the pin's
ping-pong build. -/

/-- The `nodes` array slot (60 lanes). -/
def nodesArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"nd", .TBytes (8 * 60)⟩
/-- The `src` array slot (8 words). -/
def srcArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"src", .TBytes (8 * 8)⟩

/-- Phase A trip: `nd[4·idx .. 4·idx+3] := hleaf(src[idx])` (mixer inlined). -/
def hleafBody : LowCT := seqAll <|
  [ .RArrLoad ⟨"v", .TU64⟩ srcArr "idx",
    setE "i4"  (.SShl (.SVar "idx") (.SLit 2)),
    setE "i41" (.SAdd (.SVar "i4") (.SLit 1)),
    setE "i42" (.SAdd (.SVar "i4") (.SLit 2)),
    setE "i43" (.SAdd (.SVar "i4") (.SLit 3)),
    -- t_i = (prev * GOLDEN + i) * SPLIT
    setE "g0" (.SMul (.SVar "v") (.SLit golden.toNat)),
    setE "t0" (.SMul (.SVar "g0") (.SLit split.toNat)),
    setE "g1" (.SAdd (.SMul (.SVar "t0") (.SLit golden.toNat)) (.SLit 1)),
    setE "t1" (.SMul (.SVar "g1") (.SLit split.toNat)),
    setE "g2" (.SAdd (.SMul (.SVar "t1") (.SLit golden.toNat)) (.SLit 2)),
    setE "t2" (.SMul (.SVar "g2") (.SLit split.toNat)),
    setE "g3" (.SAdd (.SMul (.SVar "t2") (.SLit golden.toNat)) (.SLit 3)),
    setE "t3" (.SMul (.SVar "g3") (.SLit split.toNat)),
    -- chain: prev *= 0xA3; o_i += prev
    setE "p1" (.SMul (.SVar "t0") (.SLit 0xA3)),
    setE "o1" (.SAdd (.SVar "t1") (.SVar "p1")),
    setE "p2" (.SMul (.SVar "o1") (.SLit 0xA3)),
    setE "o2" (.SAdd (.SVar "t2") (.SVar "p2")),
    setE "p3" (.SMul (.SVar "o2") (.SLit 0xA3)),
    setE "o3" (.SAdd (.SVar "t3") (.SVar "p3")),
    .RArrStore nodesArr "i4"  ⟨"t0", .TU64⟩,
    .RArrStore nodesArr "i41" ⟨"o1", .TU64⟩,
    .RArrStore nodesArr "i42" ⟨"o2", .TU64⟩,
    .RArrStore nodesArr "i43" ⟨"o3", .TU64⟩ ]

/-- Phase A body context: accumulator `nd`, loop index `idx`, invariant `src`. -/
def hleafΓ : Ctx := [.memref 60, .sword 64, .memref 8]

/-- Phase A VarMap. -/
def hleafVm : VarMap hleafΓ :=
  (((VarMap.empty.bind (t := .memref 8) "src").bind
      (t := .sword 64) "idx").bind (t := .memref 60) "nd")

/-- Nested inner-count body: `cnt := n >> (lvl + 1)` (per-level halving trip). -/
def compCountBody : LowCT :=
  .RScalarSetExpr "cnt" (.SShr (.SVar "n") (.SAdd (.SVar "lvl") (.SLit 1)))

/-- Nested inner-update trip: compress node pair `(2j, 2j+1)` of level `lvl`
    into node `j` of level `lvl+1` — level bases `8n − (8n >> l)` lanes, the
    `_p3_compress_u64` mixer inlined. -/
def compBody : LowCT := seqAll <|
  [ setE "nn"  (.SShl (.SVar "n") (.SLit 3)),
    setE "sb"  (.SSub (.SVar "nn") (.SShr (.SVar "nn") (.SVar "lvl"))),
    setE "lp1" (.SAdd (.SVar "lvl") (.SLit 1)),
    setE "db"  (.SSub (.SVar "nn") (.SShr (.SVar "nn") (.SVar "lp1"))),
    setE "j8"  (.SShl (.SVar "j") (.SLit 3)),
    setE "sl0" (.SAdd (.SVar "sb") (.SVar "j8")),
    setE "sl1" (.SAdd (.SVar "sl0") (.SLit 1)),
    setE "sl2" (.SAdd (.SVar "sl0") (.SLit 2)),
    setE "sl3" (.SAdd (.SVar "sl0") (.SLit 3)),
    setE "sl4" (.SAdd (.SVar "sl0") (.SLit 4)),
    setE "sl5" (.SAdd (.SVar "sl0") (.SLit 5)),
    setE "sl6" (.SAdd (.SVar "sl0") (.SLit 6)),
    setE "sl7" (.SAdd (.SVar "sl0") (.SLit 7)),
    .RArrLoad ⟨"l0", .TU64⟩ nodesArr "sl0",
    .RArrLoad ⟨"l1", .TU64⟩ nodesArr "sl1",
    .RArrLoad ⟨"l2", .TU64⟩ nodesArr "sl2",
    .RArrLoad ⟨"l3", .TU64⟩ nodesArr "sl3",
    .RArrLoad ⟨"r0", .TU64⟩ nodesArr "sl4",
    .RArrLoad ⟨"r1", .TU64⟩ nodesArr "sl5",
    .RArrLoad ⟨"r2", .TU64⟩ nodesArr "sl6",
    .RArrLoad ⟨"r3", .TU64⟩ nodesArr "sl7",
    -- o_i = ((l+r)·0x9E + i) ^ (l·0x6D) ^ r
    setE "s0" (.SAdd (.SVar "l0") (.SVar "r0")),
    setE "u0" (.SMul (.SVar "s0") (.SLit 0x9E)),
    setE "x0" (.SMul (.SVar "l0") (.SLit 0x6D)),
    setE "c0" (.SXor (.SXor (.SVar "u0") (.SVar "x0")) (.SVar "r0")),
    setE "s1" (.SAdd (.SVar "l1") (.SVar "r1")),
    setE "u1" (.SAdd (.SMul (.SVar "s1") (.SLit 0x9E)) (.SLit 1)),
    setE "x1" (.SMul (.SVar "l1") (.SLit 0x6D)),
    setE "c1" (.SXor (.SXor (.SVar "u1") (.SVar "x1")) (.SVar "r1")),
    setE "s2" (.SAdd (.SVar "l2") (.SVar "r2")),
    setE "u2" (.SAdd (.SMul (.SVar "s2") (.SLit 0x9E)) (.SLit 2)),
    setE "x2" (.SMul (.SVar "l2") (.SLit 0x6D)),
    setE "c2" (.SXor (.SXor (.SVar "u2") (.SVar "x2")) (.SVar "r2")),
    setE "s3" (.SAdd (.SVar "l3") (.SVar "r3")),
    setE "u3" (.SAdd (.SMul (.SVar "s3") (.SLit 0x9E)) (.SLit 3)),
    setE "x3" (.SMul (.SVar "l3") (.SLit 0x6D)),
    setE "c3" (.SXor (.SXor (.SVar "u3") (.SVar "x3")) (.SVar "r3")),
    -- chain: prev *= 0xC5; o_i ^= prev
    setE "q1" (.SMul (.SVar "c0") (.SLit 0xC5)),
    setE "w1" (.SXor (.SVar "c1") (.SVar "q1")),
    setE "q2" (.SMul (.SVar "w1") (.SLit 0xC5)),
    setE "w2" (.SXor (.SVar "c2") (.SVar "q2")),
    setE "q3" (.SMul (.SVar "w2") (.SLit 0xC5)),
    setE "w3" (.SXor (.SVar "c3") (.SVar "q3")),
    setE "j4" (.SShl (.SVar "j") (.SLit 2)),
    setE "d0" (.SAdd (.SVar "db") (.SVar "j4")),
    setE "d1" (.SAdd (.SVar "d0") (.SLit 1)),
    setE "d2" (.SAdd (.SVar "d0") (.SLit 2)),
    setE "d3" (.SAdd (.SVar "d0") (.SLit 3)),
    .RArrStore nodesArr "d0" ⟨"c0", .TU64⟩,
    .RArrStore nodesArr "d1" ⟨"w1", .TU64⟩,
    .RArrStore nodesArr "d2" ⟨"w2", .TU64⟩,
    .RArrStore nodesArr "d3" ⟨"w3", .TU64⟩ ]

/-- Inner-count context: outer index `lvl`, invariant `n`. -/
def compCountΓ : Ctx := [.sword 64, .sword 64]

/-- Inner-count VarMap. -/
def compCountVm : VarMap compCountΓ :=
  ((VarMap.empty.bind (t := .sword 64) "n").bind (t := .sword 64) "lvl")

/-- Inner-update context: accumulator `nd`, inner `j`, outer `lvl`,
    invariant `n`. -/
def compΓ : Ctx := [.memref 60, .sword 64, .sword 64, .sword 64]

/-- Inner-update VarMap. -/
def compVm : VarMap compΓ :=
  ((((VarMap.empty.bind (t := .sword 64) "n").bind
      (t := .sword 64) "lvl").bind
      (t := .sword 64) "j").bind (t := .memref 60) "nd")

/-- Merkle outer context, newest-first: `[lvlcnt, leafcnt, src, nodes]` — ABI
    `p3_merkle_flat8(nodes, src, n, levels)` = `(RDI, RSI, RDX, RCX)`. -/
abbrev ΓM : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .stackArr 64 8, .stackArr 64 60]

/-- The jasmin image of the nodes accumulator. -/
abbrev ndT : JasminTy := mapTy (CryptoTy.memref 60)

/-- The Merkle spine: leaf-hash loop whose continuation is the genuine NESTED
    level-compress loop (inner trip `n >> (lvl+1)` recomputed per level). -/
def merkleComL : Option (ComL ΓM ndT) := do
  let pB ← rolledForLoopNRtNested (Γouter := ndT :: ΓM) (accCTy := .memref 60)
    (invCTys := [.sword 64])
    compCountVm "cnt" compCountBody
    compVm "nd" compBody
    (outerCount := .there .here)
    (init := .here)
    (invs := .cons (.there (.there .here)) .nil)
  rolledForLoopNRtCont (Γouter := ΓM) (accCTy := .memref 60)
    (invCTys := [.memref 8])
    hleafVm "nd" hleafBody
    (count := .there .here)
    (init := .there (.there (.there .here)))
    (invs := .cons (.there (.there .here)) .nil)
    (cont := pB)

/-- **The Merkle spine front-compiles** (leaf-hash phase + genuine nested
    level loop, ONE `ComL`). -/
theorem merkleComL_isSome : merkleComL.isSome := by native_decide

/-! ## 6. denote = the pin's leaf hashes AND Merkle root (`n = 8`, pin data) -/

/-- Pin-derived source row: the first 8 words of the KAT column LDE. -/
def merkleSrc : Array UInt64 :=
  Array.ofFn (n := 8) (fun i => buildColumnLde[i.val]!)

/-- Source valuation row. -/
def merkleSrcSeed : Fin 8 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (merkleSrc[i.val]!.toNat)

/-- Outer valuation: `lvlcnt = 3`, `leafcnt = 8`, `src`, `nodes` zero. -/
def merkleVal : Ctxt.Valuation ΓM :=
  .cons (BitVec.ofNat 64 3) (.cons (BitVec.ofNat 64 8)
    (.cons merkleSrcSeed (.cons (fun _ => (0 : BitVec 64)) .nil)))

/-- Selected denoted lanes of the Merkle spine result. -/
def merkleDenoteSlots (idxs : List Nat) : Option (List Nat) :=
  merkleComL.map (fun c =>
    idxs.map (fun i =>
      (ComL.denote c merkleVal ⟨i % 60, Nat.mod_lt _ (by decide)⟩).toNat))

/-- **denote = the pin's leaf level** (`buildLeafHashes` lanes `0..31`). -/
theorem merkle_denote_leaves :
    merkleDenoteSlots (List.range 32)
      = some (specSlots (buildLeafHashes merkleSrc 8) (List.range 32)) := by
  native_decide

/-- **denote = the pin's Merkle root** (`merkleRoot` at lanes `56..59` — the
    flat build's digests coincide with the pin's ping-pong build). -/
theorem merkle_denote_root :
    merkleDenoteSlots [56, 57, 58, 59]
      = some (specSlots (merkleRoot (buildLeafHashes merkleSrc 8) 8) [0, 1, 2, 3]) := by
  native_decide

/-! ## 6b. The query/auth-path walk: 3 query phases, no loop-carried walker

Layer-0 shape (`n = 32`, `half = 16`, 5 tree levels): per query `q < 3`, the pin
opens `cur[ipos]`/`cur[ineg]` (`ipos = qidx[q] & 31`, `ineg = (ipos+16) & 31`) and
walks two authentication paths. The level-`l` walk needs NO loop-carried state:
the level-`l` sibling is node `(idx >> l) ^ 1`, its digest lives in the FLAT tree
(§5 layout, `8n = 256` lanes, level base `256 − (256 >> l)`) — everything is
recomputed from the loop counter and the query constants each trip. Each per-query
phase is ONE runtime-trip loop over levels (count = 5); the openings and the root
copy (`qp[0..3] := tree[248..251]`, the pin's `proof[lbase..lbase+3]`) are written
idempotently every trip. The 3 phases chain through `rolledForLoopNRtCont` into
ONE `ComL`; `denote` = the pin's whole 136-word layer-0 block. -/

/-- The flat Merkle tree slot for `n = 32` (256 lanes, level `l` at
    `256 − (256 >> l)`, root at `248..251`). -/
def treeArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"tr", .TBytes (8 * 256)⟩
/-- The layer codeword slot (32 words). -/
def cur32Arr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"cw", .TBytes (8 * 32)⟩
/-- The query-index slot (4 words). -/
def qxArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"qx", .TBytes (8 * 4)⟩
/-- The layer proof-block slot (136 words: root lanes + 3×44 query words). -/
def qpArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"qp", .TBytes (8 * 136)⟩

/-- One trip of query `q`'s walk at level `idx`: openings + root copy
    (idempotent), then the level-`idx` sibling digests of BOTH paths —
    `sib = (pos >> idx) ^ 1`, digest at flat lane `256 − (256 >> idx) + 4·sib`. -/
def qwalkBody (q : Nat) : LowCT :=
  let qb := 4 + 44 * q
  seqAll <|
  [ setE "qc" (.SLit q),
    .RArrLoad ⟨"qv", .TU64⟩ qxArr "qc",
    setE "ipos" (.SAnd (.SVar "qv") (.SLit 31)),
    setE "ineg" (.SAnd (.SAdd (.SVar "ipos") (.SLit 16)) (.SLit 31)),
    .RArrLoad ⟨"ep", .TU64⟩ cur32Arr "ipos",
    .RArrLoad ⟨"en", .TU64⟩ cur32Arr "ineg",
    setE "k0" (.SLit (qb + 0)),
    setE "k1" (.SLit (qb + 1)),
    setE "k2" (.SLit (qb + 2)),
    setE "k3" (.SLit (qb + 3)),
    .RArrStore qpArr "k0" ⟨"ep", .TU64⟩,
    .RArrStore qpArr "k1" ⟨"en", .TU64⟩,
    .RArrStore qpArr "k2" ⟨"ipos", .TU64⟩,
    .RArrStore qpArr "k3" ⟨"ineg", .TU64⟩ ]
  ++ (List.range 4).flatMap (fun k =>
      [ setE s!"rs{k}" (.SLit (248 + k)),
        .RArrLoad ⟨s!"rv{k}", .TU64⟩ treeArr s!"rs{k}",
        setE s!"rd{k}" (.SLit k),
        .RArrStore qpArr s!"rd{k}" ⟨s!"rv{k}", .TU64⟩ ])
  ++ [ setE "cb" (.SLit 256),
       setE "bl" (.SSub (.SVar "cb") (.SShr (.SVar "cb") (.SVar "idx"))),
       setE "i4" (.SShl (.SVar "idx") (.SLit 2)),
       setE "sp" (.SXor (.SShr (.SVar "ipos") (.SVar "idx")) (.SLit 1)),
       setE "sp4" (.SShl (.SVar "sp") (.SLit 2)),
       setE "pb0" (.SAdd (.SVar "bl") (.SVar "sp4")),
       setE "pb1" (.SAdd (.SVar "pb0") (.SLit 1)),
       setE "pb2" (.SAdd (.SVar "pb0") (.SLit 2)),
       setE "pb3" (.SAdd (.SVar "pb0") (.SLit 3)),
       .RArrLoad ⟨"pd0", .TU64⟩ treeArr "pb0",
       .RArrLoad ⟨"pd1", .TU64⟩ treeArr "pb1",
       .RArrLoad ⟨"pd2", .TU64⟩ treeArr "pb2",
       .RArrLoad ⟨"pd3", .TU64⟩ treeArr "pb3",
       setE "dp0" (.SAdd (.SVar "i4") (.SLit (qb + 4))),
       setE "dp1" (.SAdd (.SVar "dp0") (.SLit 1)),
       setE "dp2" (.SAdd (.SVar "dp0") (.SLit 2)),
       setE "dp3" (.SAdd (.SVar "dp0") (.SLit 3)),
       .RArrStore qpArr "dp0" ⟨"pd0", .TU64⟩,
       .RArrStore qpArr "dp1" ⟨"pd1", .TU64⟩,
       .RArrStore qpArr "dp2" ⟨"pd2", .TU64⟩,
       .RArrStore qpArr "dp3" ⟨"pd3", .TU64⟩,
       setE "sn" (.SXor (.SShr (.SVar "ineg") (.SVar "idx")) (.SLit 1)),
       setE "sn4" (.SShl (.SVar "sn") (.SLit 2)),
       setE "nb0" (.SAdd (.SVar "bl") (.SVar "sn4")),
       setE "nb1" (.SAdd (.SVar "nb0") (.SLit 1)),
       setE "nb2" (.SAdd (.SVar "nb0") (.SLit 2)),
       setE "nb3" (.SAdd (.SVar "nb0") (.SLit 3)),
       .RArrLoad ⟨"qd0", .TU64⟩ treeArr "nb0",
       .RArrLoad ⟨"qd1", .TU64⟩ treeArr "nb1",
       .RArrLoad ⟨"qd2", .TU64⟩ treeArr "nb2",
       .RArrLoad ⟨"qd3", .TU64⟩ treeArr "nb3",
       setE "dn0" (.SAdd (.SVar "i4") (.SLit (qb + 24))),
       setE "dn1" (.SAdd (.SVar "dn0") (.SLit 1)),
       setE "dn2" (.SAdd (.SVar "dn0") (.SLit 2)),
       setE "dn3" (.SAdd (.SVar "dn0") (.SLit 3)),
       .RArrStore qpArr "dn0" ⟨"qd0", .TU64⟩,
       .RArrStore qpArr "dn1" ⟨"qd1", .TU64⟩,
       .RArrStore qpArr "dn2" ⟨"qd2", .TU64⟩,
       .RArrStore qpArr "dn3" ⟨"qd3", .TU64⟩ ]

/-- Query-walk body context: accumulator `qp`, loop index `idx`, invariants
    `cw`/`tr`/`qx`. -/
def qwΓ : Ctx := [.memref 136, .sword 64, .memref 32, .memref 256, .memref 4]

/-- Query-walk VarMap. -/
def qwVm : VarMap qwΓ :=
  (((((VarMap.empty.bind (t := .memref 4) "qx").bind
      (t := .memref 256) "tr").bind
      (t := .memref 32) "cw").bind
      (t := .sword 64) "idx").bind (t := .memref 136) "qp")

/-- The jasmin images of the query-walk buffers. -/
abbrev qpT : JasminTy := mapTy (CryptoTy.memref 136)
abbrev trT : JasminTy := mapTy (CryptoTy.memref 256)

/-- Generic per-query walk phase (context polymorphic, like `phaseFold`). -/
def phaseQuery (q : Nat) {Γ : Ctxt jasminDialect}
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ qpT)
    (curV : Ctxt.Var Γ (mapTy (CryptoTy.memref 32)))
    (trV : Ctxt.Var Γ trT)
    (qxV : Ctxt.Var Γ (mapTy (CryptoTy.memref 4)))
    {s : JasminTy} (cont : ComL (qpT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNRtCont (Γouter := Γ) (accCTy := .memref 136)
    (invCTys := [.memref 32, .memref 256, .memref 4]) qwVm "qp" (qwalkBody q)
    count init (.cons curV (.cons trV (.cons qxV .nil))) cont

/-- The query-walk outer context, newest-first:
    `[cnt, qidx, tree, cur, qproof]` — ABI
    `p3_fri_query_walk(qproof, cur, tree, qidx, levels)` =
    `(RDI, RSI, RDX, RCX, R8)`. -/
abbrev ΓQ : Ctxt jasminDialect :=
  [.reg 64, .stackArr 64 4, .stackArr 64 256, .stackArr 64 32, .stackArr 64 136]

/-- The 3-query walk chain: query-0..2 phases, ONE `ComL` spine (each phase is the
    previous phase's continuation); all three share the one `levels` count. -/
def queryComL : Option (ComL ΓQ qpT) := do
  let p2 ← phaseQuery 2
    (Γ := qpT :: qpT :: ΓQ)
    (count := .there (.there .here))
    (init := .here)
    (curV := .there (.there (.there (.there (.there .here)))))
    (trV := .there (.there (.there (.there .here))))
    (qxV := .there (.there (.there .here)))
    (cont := .ret .here)
  let p1 ← phaseQuery 1
    (Γ := qpT :: ΓQ)
    (count := .there .here)
    (init := .here)
    (curV := .there (.there (.there (.there .here))))
    (trV := .there (.there (.there .here)))
    (qxV := .there (.there .here))
    (cont := p2)
  phaseQuery 0
    (Γ := ΓQ)
    (count := .here)
    (init := .there (.there (.there (.there .here))))
    (curV := .there (.there (.there .here)))
    (trV := .there (.there .here))
    (qxV := .there .here)
    (cont := p1)

/-- **The 3-query walk chain front-compiles.** -/
theorem queryComL_isSome : queryComL.isSome := by native_decide

/-! ### 6b'. denote = the pin's layer-0 proof block (root + openings + paths)

The standalone walk takes the FLAT tree as an input; the KAT valuation seeds it
with the pin's own level digests scattered at the flat bases (the §5 layout at
`n = 32`). The denote pin below then forces every walked lane to agree with the
pin's ping-pong `merklePath` — a wrong flat base, sibling index, or level count
would break a path word. -/

/-- KAT-input constructor: the pin's ping-pong levels scattered into the flat
    layout (level `l` at `256 − (256 >> l)`; lanes `252..255` unused). -/
def flatTree32 : Array UInt64 := Id.run do
  let mut nd : Array UInt64 := Array.replicate 256 0
  let mut a := buildLeafHashes buildColumnLde 32
  let mut pairs := 32
  for l in [0:6] do
    let base := 256 - (256 >>> l)
    for j in [0:pairs*4] do nd := nd.set! (base + j) a[j]!
    let mut b : Array UInt64 := Array.replicate 128 0
    for j in [0:pairs/2] do
      let lo := Array.ofFn (n := 4) (fun k => a[(2*j)*4 + k.val]!)
      let hi := Array.ofFn (n := 4) (fun k => a[(2*j+1)*4 + k.val]!)
      let d := p3Compress lo hi
      for k in [0:4] do b := b.set! (j*4 + k) d[k]!
    a := b
    pairs := pairs / 2
  return nd

/-- Flat-tree valuation row. -/
def treeSeed : Fin 256 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (flatTree32[i.val]!.toNat)

/-- Layer-0 codeword valuation row (the pin's column LDE). -/
def curSeed32 : Fin 32 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (buildColumnLde[i.val]!.toNat)

/-- Query-index valuation row. -/
def qxSeed : Fin 4 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (qidxKAT[i.val]!.toNat)

/-- Outer valuation at `levels = cnt`; `qproof` seeded zero. -/
def queryVal (cnt : Nat) : Ctxt.Valuation ΓQ :=
  .cons (BitVec.ofNat 64 cnt) (.cons qxSeed (.cons treeSeed
    (.cons curSeed32 (.cons (fun _ => (0 : BitVec 64)) .nil))))

/-- Selected denoted slots of the walk result. -/
def queryDenoteSlots (cnt : Nat) (idxs : List Nat) : Option (List Nat) :=
  queryComL.map (fun c =>
    idxs.map (fun i =>
      (ComL.denote c (queryVal cnt) ⟨i % 136, Nat.mod_lt _ (by decide)⟩).toNat))

/-- **denote = the pin's whole layer-0 proof block** (`friProveObj` words
    `0..135`: root lanes, then per query the openings `cur[ipos]`/`cur[ineg]`,
    the indices, and BOTH 20-word authentication paths) at `levels = 5`. -/
theorem query_denote_layer0 :
    queryDenoteSlots 5 (List.range 136)
      = some (specSlots (friProveObj buildColumnLde alphaKAT qidxKAT)
                (List.range 136)) := by
  native_decide

/-- **denote = the zero seed at `levels = 0`** (no trips — the count genuinely
    drives the walk; nothing is written). -/
theorem query_denote_zero :
    queryDenoteSlots 0 (List.range 136)
      = some (List.replicate 136 0) := by
  native_decide

/-! ## 6c. ONE layer, ONE `ComL`: leaf-hash ; nested compress ; 3 queries ; fold

The full layer-0 spine through ALL FOUR committed phase families in a single
front-compiled `ComL`: fixed-trip leaf-hash (`rolledForLoopNCont`, `N = 32`),
genuine nested level-compress mid-chain (`rolledForLoopNRtNestedCont`, outer
`lvl < 5`, inner `32 >> (lvl+1)` recomputed per level), the three query/path
walks, then the layer-0 fold at fixed count 16 (`phaseFoldFx 0`). The tree
buffer is seeded ZERO — the walks read the digests the chain itself built.
Two final-continuation variants observe the two written buffers: the proof
block (`.ret` at the query result) and the folded codeword (`.ret .here`). -/

/-- Leaf-hash phase at `n = 32` into the flat tree (fixed trip count 32). -/
def hleaf32Body : LowCT := seqAll <|
  [ .RArrLoad ⟨"v", .TU64⟩ cur32Arr "idx",
    setE "i4"  (.SShl (.SVar "idx") (.SLit 2)),
    setE "i41" (.SAdd (.SVar "i4") (.SLit 1)),
    setE "i42" (.SAdd (.SVar "i4") (.SLit 2)),
    setE "i43" (.SAdd (.SVar "i4") (.SLit 3)),
    setE "g0" (.SMul (.SVar "v") (.SLit golden.toNat)),
    setE "t0" (.SMul (.SVar "g0") (.SLit split.toNat)),
    setE "g1" (.SAdd (.SMul (.SVar "t0") (.SLit golden.toNat)) (.SLit 1)),
    setE "t1" (.SMul (.SVar "g1") (.SLit split.toNat)),
    setE "g2" (.SAdd (.SMul (.SVar "t1") (.SLit golden.toNat)) (.SLit 2)),
    setE "t2" (.SMul (.SVar "g2") (.SLit split.toNat)),
    setE "g3" (.SAdd (.SMul (.SVar "t2") (.SLit golden.toNat)) (.SLit 3)),
    setE "t3" (.SMul (.SVar "g3") (.SLit split.toNat)),
    setE "p1" (.SMul (.SVar "t0") (.SLit 0xA3)),
    setE "o1" (.SAdd (.SVar "t1") (.SVar "p1")),
    setE "p2" (.SMul (.SVar "o1") (.SLit 0xA3)),
    setE "o2" (.SAdd (.SVar "t2") (.SVar "p2")),
    setE "p3" (.SMul (.SVar "o2") (.SLit 0xA3)),
    setE "o3" (.SAdd (.SVar "t3") (.SVar "p3")),
    .RArrStore treeArr "i4"  ⟨"t0", .TU64⟩,
    .RArrStore treeArr "i41" ⟨"o1", .TU64⟩,
    .RArrStore treeArr "i42" ⟨"o2", .TU64⟩,
    .RArrStore treeArr "i43" ⟨"o3", .TU64⟩ ]

/-- Leaf-hash body context (`n = 32` twin of `hleafΓ`). -/
def hleaf32Γ : Ctx := [.memref 256, .sword 64, .memref 32]

/-- Leaf-hash VarMap (`n = 32`). -/
def hleaf32Vm : VarMap hleaf32Γ :=
  (((VarMap.empty.bind (t := .memref 32) "cw").bind
      (t := .sword 64) "idx").bind (t := .memref 256) "tr")

/-- Nested inner-count body at `n = 32`: `cnt := 32 >> (lvl + 1)`. -/
def comp32CountBody : LowCT := seqAll
  [ setE "c32" (.SLit 32),
    setE "cnt" (.SShr (.SVar "c32") (.SAdd (.SVar "lvl") (.SLit 1))) ]

/-- Inner-count context (`n = 32`; no invariants). -/
def comp32CountΓ : Ctx := [.sword 64]

/-- Inner-count VarMap (`n = 32`). -/
def comp32CountVm : VarMap comp32CountΓ :=
  VarMap.empty.bind (t := .sword 64) "lvl"

/-- Nested inner-update trip at `n = 32`: compress node pair `(2j, 2j+1)` of
    level `lvl` into node `j` of level `lvl+1` — flat bases from `8n = 256`. -/
def comp32Body : LowCT := seqAll <|
  [ setE "nn"  (.SLit 256),
    setE "sb"  (.SSub (.SVar "nn") (.SShr (.SVar "nn") (.SVar "lvl"))),
    setE "lp1" (.SAdd (.SVar "lvl") (.SLit 1)),
    setE "db"  (.SSub (.SVar "nn") (.SShr (.SVar "nn") (.SVar "lp1"))),
    setE "j8"  (.SShl (.SVar "j") (.SLit 3)),
    setE "sl0" (.SAdd (.SVar "sb") (.SVar "j8")),
    setE "sl1" (.SAdd (.SVar "sl0") (.SLit 1)),
    setE "sl2" (.SAdd (.SVar "sl0") (.SLit 2)),
    setE "sl3" (.SAdd (.SVar "sl0") (.SLit 3)),
    setE "sl4" (.SAdd (.SVar "sl0") (.SLit 4)),
    setE "sl5" (.SAdd (.SVar "sl0") (.SLit 5)),
    setE "sl6" (.SAdd (.SVar "sl0") (.SLit 6)),
    setE "sl7" (.SAdd (.SVar "sl0") (.SLit 7)),
    .RArrLoad ⟨"l0", .TU64⟩ treeArr "sl0",
    .RArrLoad ⟨"l1", .TU64⟩ treeArr "sl1",
    .RArrLoad ⟨"l2", .TU64⟩ treeArr "sl2",
    .RArrLoad ⟨"l3", .TU64⟩ treeArr "sl3",
    .RArrLoad ⟨"r0", .TU64⟩ treeArr "sl4",
    .RArrLoad ⟨"r1", .TU64⟩ treeArr "sl5",
    .RArrLoad ⟨"r2", .TU64⟩ treeArr "sl6",
    .RArrLoad ⟨"r3", .TU64⟩ treeArr "sl7",
    setE "s0" (.SAdd (.SVar "l0") (.SVar "r0")),
    setE "u0" (.SMul (.SVar "s0") (.SLit 0x9E)),
    setE "x0" (.SMul (.SVar "l0") (.SLit 0x6D)),
    setE "c0" (.SXor (.SXor (.SVar "u0") (.SVar "x0")) (.SVar "r0")),
    setE "s1" (.SAdd (.SVar "l1") (.SVar "r1")),
    setE "u1" (.SAdd (.SMul (.SVar "s1") (.SLit 0x9E)) (.SLit 1)),
    setE "x1" (.SMul (.SVar "l1") (.SLit 0x6D)),
    setE "c1" (.SXor (.SXor (.SVar "u1") (.SVar "x1")) (.SVar "r1")),
    setE "s2" (.SAdd (.SVar "l2") (.SVar "r2")),
    setE "u2" (.SAdd (.SMul (.SVar "s2") (.SLit 0x9E)) (.SLit 2)),
    setE "x2" (.SMul (.SVar "l2") (.SLit 0x6D)),
    setE "c2" (.SXor (.SXor (.SVar "u2") (.SVar "x2")) (.SVar "r2")),
    setE "s3" (.SAdd (.SVar "l3") (.SVar "r3")),
    setE "u3" (.SAdd (.SMul (.SVar "s3") (.SLit 0x9E)) (.SLit 3)),
    setE "x3" (.SMul (.SVar "l3") (.SLit 0x6D)),
    setE "c3" (.SXor (.SXor (.SVar "u3") (.SVar "x3")) (.SVar "r3")),
    setE "q1" (.SMul (.SVar "c0") (.SLit 0xC5)),
    setE "w1" (.SXor (.SVar "c1") (.SVar "q1")),
    setE "q2" (.SMul (.SVar "w1") (.SLit 0xC5)),
    setE "w2" (.SXor (.SVar "c2") (.SVar "q2")),
    setE "q3" (.SMul (.SVar "w2") (.SLit 0xC5)),
    setE "w3" (.SXor (.SVar "c3") (.SVar "q3")),
    setE "j4" (.SShl (.SVar "j") (.SLit 2)),
    setE "d0" (.SAdd (.SVar "db") (.SVar "j4")),
    setE "d1" (.SAdd (.SVar "d0") (.SLit 1)),
    setE "d2" (.SAdd (.SVar "d0") (.SLit 2)),
    setE "d3" (.SAdd (.SVar "d0") (.SLit 3)),
    .RArrStore treeArr "d0" ⟨"c0", .TU64⟩,
    .RArrStore treeArr "d1" ⟨"w1", .TU64⟩,
    .RArrStore treeArr "d2" ⟨"w2", .TU64⟩,
    .RArrStore treeArr "d3" ⟨"w3", .TU64⟩ ]

/-- Inner-update context (`n = 32`; accumulator `tr`, inner `j`, outer `lvl`). -/
def comp32Γ : Ctx := [.memref 256, .sword 64, .sword 64]

/-- Inner-update VarMap (`n = 32`). -/
def comp32Vm : VarMap comp32Γ :=
  (((VarMap.empty.bind (t := .sword 64) "lvl").bind
      (t := .sword 64) "j").bind (t := .memref 256) "tr")

/-- Fixed-trip leaf-hash phase (`N = 32`, no count register). -/
def phaseLeaf32 {Γ : Ctxt jasminDialect}
    (init : Ctxt.Var Γ trT) (srcV : Ctxt.Var Γ (mapTy (CryptoTy.memref 32)))
    {s : JasminTy} (cont : ComL (trT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNCont (Γouter := Γ) (accCTy := .memref 256)
    (invCTys := [.memref 32]) 32 hleaf32Vm "tr" hleaf32Body
    init (.cons srcV .nil) cont

/-- Mid-chain nested level-compress phase (`n = 32`). -/
def phaseCompress32 {Γ : Ctxt jasminDialect}
    (outerCount : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ trT)
    {s : JasminTy} (cont : ComL (trT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNRtNestedCont (Γouter := Γ) (accCTy := .memref 256)
    (invCTys := [])
    comp32CountVm "cnt" comp32CountBody
    comp32Vm "tr" comp32Body
    outerCount init .nil cont

/-- The layer-spine outer context, newest-first:
    `[cnt, qidx, alpha, acc, tree, cur, qproof]` (in-model; `cnt = 5` serves as
    both the compress outer count and the walk level count). -/
abbrev ΓL : Ctxt jasminDialect :=
  [.reg 64, .stackArr 64 4, .stackArr 64 4, .stackArr 64 34,
   .stackArr 64 256, .stackArr 64 32, .stackArr 64 136]

/-- The whole layer-0 spine — leaf-hash ; nested compress ; query-0..2 ; fold —
    parametric in the final continuation (which written buffer to return). -/
def layerSpine {s : JasminTy}
    (fin : ComL (accT :: qpT :: qpT :: qpT :: trT :: trT :: ΓL) s) :
    Option (ComL ΓL s) := do
  let pF ← phaseFoldFx 0
    (Γ := qpT :: qpT :: qpT :: trT :: trT :: ΓL)
    (init := .there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (alphaV := .there (.there (.there (.there (.there (.there (.there .here)))))))
    (cont := fin)
  let pE ← phaseQuery 2
    (Γ := qpT :: qpT :: trT :: trT :: ΓL)
    (count := .there (.there (.there (.there .here))))
    (init := .here)
    (curV := .there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (trV := .there (.there .here))
    (qxV := .there (.there (.there (.there (.there .here)))))
    (cont := pF)
  let pD ← phaseQuery 1
    (Γ := qpT :: trT :: trT :: ΓL)
    (count := .there (.there (.there .here)))
    (init := .here)
    (curV := .there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (trV := .there .here)
    (qxV := .there (.there (.there (.there .here))))
    (cont := pE)
  let pC ← phaseQuery 0
    (Γ := trT :: trT :: ΓL)
    (count := .there (.there .here))
    (init := .there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (curV := .there (.there (.there (.there (.there (.there (.there .here)))))))
    (trV := .here)
    (qxV := .there (.there (.there .here)))
    (cont := pD)
  let pB ← phaseCompress32
    (Γ := trT :: ΓL)
    (outerCount := .there .here)
    (init := .here)
    (cont := pC)
  phaseLeaf32
    (Γ := ΓL)
    (init := .there (.there (.there (.there .here))))
    (srcV := .there (.there (.there (.there (.there .here)))))
    (cont := pB)

/-- Variant returning the layer proof block (the query-2 result). -/
def layerQpComL : Option (ComL ΓL qpT) := layerSpine (.ret (.there .here))

/-- Variant returning the folded codeword buffer (the fold result). -/
def layerFoldComL : Option (ComL ΓL accT) := layerSpine (.ret .here)

/-- Layer-spine valuation: `cnt = 5`, tree AND proof block seeded ZERO (built by
    the spine itself), codeword buffers seeded with the pin's column LDE. -/
def layerVal : Ctxt.Valuation ΓL :=
  .cons (BitVec.ofNat 64 5) (.cons qxSeed (.cons alphaSeed
    (.cons accSeed (.cons (fun _ => (0 : BitVec 64))
      (.cons curSeed32 (.cons (fun _ => (0 : BitVec 64)) .nil))))))

/-- **denote = the pin's whole layer-0 proof block from a ZERO-seeded tree**: the
    walks read digests the spine's own leaf-hash + nested compress phases wrote. -/
theorem layer_denote_block :
    (layerQpComL.map (fun c =>
      (List.range 136).map (fun i =>
        (ComL.denote c layerVal ⟨i % 136, Nat.mod_lt _ (by decide)⟩).toNat)))
      = some (specSlots (friProveObj buildColumnLde alphaKAT qidxKAT)
                (List.range 136)) := by
  native_decide

/-- **denote = the pin's layer-1 codeword** through the same spine's final fold
    phase (fixed count 16). -/
theorem layer_denote_fold :
    (layerFoldComL.map (fun c =>
      (List.range 16).map (fun i =>
        (ComL.denote c layerVal ⟨i % 34, Nat.mod_lt _ (by decide)⟩).toNat)))
      = some (specSlots (foldLayersSpec buildColumnLde alphaKAT 1)
                (List.range 16)) := by
  native_decide

/-! ## 7. Render the front-compiled fragments to owned `.s` -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulOwnedEmit
  (fuseMulHiLprog)

/-- The fold chain rendered:
    `p3_fri_fold_chain(acc, alpha, n0, n1, n2, n3)`.
    `fuseMulHiLprog` coalesces each Barrett discarded-low `MUL` + `MULXHI`
    pair into the printer's real two-output `mulx` (see `mulL`). -/
def foldChainAsm : Option String :=
  foldChainComL.map (fun c =>
    renderLprogAtt (fuseMulHiLprog
      (ComL.toLprogPhysAbi c "p3_fri_fold_chain" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI", "RDX", "RCX", "R8", "R9"] [64, 64, 64, 64, 64, 64])
      (saveRdx := true)))

/-- The Merkle spine rendered: `p3_merkle_flat8(nodes, src, n, levels)`. -/
def merkleAsm : Option String :=
  merkleComL.map (fun c =>
    renderLprogAtt
      (ComL.toLprogPhysAbi c "p3_merkle_flat8" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI", "RDX", "RCX"] [64, 64, 64, 64]))

/-- The fixed-count fold chain rendered: `p3_fri_fold_chain_fx(acc, alpha)` —
    TWO registers, every trip count an immediate in the loop nodes. -/
def foldChainFxAsm : Option String :=
  foldChainFxComL.map (fun c =>
    renderLprogAtt (fuseMulHiLprog
      (ComL.toLprogPhysAbi c "p3_fri_fold_chain_fx" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI"] [64, 64])
      (saveRdx := true)))

/-- The 3-query walk rendered:
    `p3_fri_query_walk(qproof, cur, tree, qidx, levels)`. -/
def queryAsm : Option String :=
  queryComL.map (fun c =>
    renderLprogAtt
      (ComL.toLprogPhysAbi c "p3_fri_query_walk" (argName 0)
        [argName 1, argName 2, argName 3]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI", "RDX", "RCX", "R8"] [64, 64, 64, 64, 64]))

/-- All four fragments render. -/
theorem fragments_render :
    foldChainAsm.isSome ∧ merkleAsm.isSome
    ∧ foldChainFxAsm.isSome ∧ queryAsm.isSome := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The concatenated fragment `.s`. -/
def frontAsm : String :=
  (foldChainAsm.getD "") ++ "\n" ++ (merkleAsm.getD "") ++ "\n"
    ++ (foldChainFxAsm.getD "") ++ "\n" ++ (queryAsm.getD "") ++ "\n"

/-- The rendered `.s` carries all four export symbols, no `UNHANDLED` marker
    (the imm64 Barrett/mixer constants render), and real two-output `mulx`
    lines (every Barrett high word fused — no dropped `MULXHI` binding). -/
theorem frontAsm_clean :
    strContains frontAsm "p3_fri_fold_chain" = true
    ∧ strContains frontAsm "p3_merkle_flat8" = true
    ∧ strContains frontAsm "p3_fri_fold_chain_fx" = true
    ∧ strContains frontAsm "p3_fri_query_walk" = true
    ∧ strContains frontAsm "UNHANDLED" = false
    ∧ strContains frontAsm "mulx" = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 8. Emit driver

The fragments are front-reachable pieces of the `fri_proof` spine only — the
whole-artifact `plonky3_fri_prove_obj` re-emit (and the whitelist flip of
`fri_proof_link.s`) is gated on the 4-layer assembly breadth + the asm byte-KAT
(module header). -/

/-- Write `bench/plonky3_compare/gen_com/fri_proof_frontphases.s`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  let path := "bench/plonky3_compare/gen_com/fri_proof_frontphases.s"
  IO.FS.writeFile path frontAsm
  IO.println s!"wrote {path} (front-compiled fri_proof fold-chain [runtime + fixed counts] + Merkle + query-walk phases; no jasminc, no hand Com/Lcmd)"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit
