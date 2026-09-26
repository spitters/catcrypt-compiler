/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module


@[expose] public section
/-
Executable bit-exact reference for `plonky3_fri_prove_obj`
(`bench/plonky3_compare/include/plonky3_fri_proof_leaves.jinc`).

This is the `denote = spec` TARGET the owned x86 emit of `plonky3_fri_prove_obj_rc`
must reproduce: a pure Lean function over `Array UInt64` mirroring the prover
phase-by-phase (BabyBear Barrett field arithmetic + the u64-lane surrogate Merkle
hash + the FRI fold chain + the flat 546-word proof scatter). It is validated by
running it against the independent C reference prover `ref_fri_prove_obj`
(`bench_fri_proof_from_rustcmd.c`, the `fri.rs::fri_prove_column` recipe — the
same GOLDEN oracle the KAT itself uses), byte-for-byte over the full 546-word
object on the KAT inputs (coeffs {7,3,5,2}, alpha {101,202,303,404},
qidx {3,11,26,0}).

Self-contained (no project imports); run with `lake env lean --run`.
-/

namespace Plonky3FriProofRef

/-- BabyBear prime `p = 2^31 - 2^27 + 1`. -/
def bbP : UInt64 := 2013265921
/-- BabyBear multiplicative generator. -/
def bbG : UInt64 := 31

/-! ## Field arithmetic (Barrett/branchless, byte-identical to the `.jinc`) -/

/-- `_fp_reduce`: branchless single conditional subtraction of `p`. -/
def fReduce (x : UInt64) : UInt64 :=
  let t := x - bbP
  let m := if (t >>> 63) == 1 then bbP else 0
  t + m

def fAdd (a b : UInt64) : UInt64 := fReduce (a + b)
def fSub (a b : UInt64) : UInt64 := fReduce (bbP + a - b)
/-- `_fp_mul`: `(a*b) mod p` (operands `< p < 2^31`, product `< 2^62`, no wrap). -/
def fMul (a b : UInt64) : UInt64 := (a * b) % bbP

/-- `_fp_pow`: 64-iteration square-and-multiply. -/
def fPow (base exp : UInt64) : UInt64 := Id.run do
  let mut r : UInt64 := 1
  let mut c : UInt64 := base % bbP
  let mut e : UInt64 := exp
  for _ in [0:64] do
    if (e &&& 1) == 1 then r := fMul r c
    c := fMul c c
    e := e >>> 1
  return r

/-- `_fp_inv`: Fermat inverse (`0` maps to `0`). -/
def fInv (a : UInt64) : UInt64 := if a == 0 then 0 else fPow a (bbP - 2)

/-- `bb_root_of_unity(k) = G^((p-1) >> k)`. -/
def fRou (k : Nat) : UInt64 := fPow bbG ((bbP - 1) >>> (UInt64.ofNat k))

/-- Horner poly evaluation `sum coeffs[i] x^i`. -/
def fPolyEval (coeffs : Array UInt64) (x : UInt64) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for i in [0:coeffs.size] do
    let idx := coeffs.size - 1 - i
    acc := fAdd (fMul acc x) coeffs[idx]!
  return acc

/-- `fri_fold`: `p'(x^2) = (p(x)+p(-x))/2 + alpha*(p(x)-p(-x))/(2x)`. -/
def friFold (ep en x alpha : UInt64) : UInt64 :=
  let sum := fAdd ep en
  let diff := fSub ep en
  let inv2 := fInv 2
  let inv2x := fInv (fMul 2 x)
  let peven := fMul sum inv2
  let podd := fMul diff inv2x
  fAdd peven (fMul alpha podd)

/-! ## u64-lane surrogate Merkle hash (`plonky3_merkle_leaves.jinc`, wrapping u64) -/

def golden : UInt64 := 0x9E3779B97F4A7C15
def split  : UInt64 := 0xBF58476D1CE4E5B9

/-- `_p3_hleaf_u64(v) -> o[4]`. -/
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

/-- `_p3_compress_u64(l[4], r[4]) -> o[4]`. -/
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

/-! ## Merkle build / authentication path (ping-pong over 4-lane digests) -/

/-- Build the `n`-leaf surrogate-hash array from `n` field words. -/
def buildLeafHashes (cur : Array UInt64) (n : Nat) : Array UInt64 := Id.run do
  let mut leaves : Array UInt64 := Array.replicate 128 0
  for i in [0:n] do
    let d := p3Hleaf cur[i]!
    for j in [0:4] do leaves := leaves.set! (i*4 + j) d[j]!
  return leaves

/-- Merkle root (4 lanes) by ping-pong halving compress. -/
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

/-- Authentication path (20 words = 5 sibling digests) for `leafIndex`. -/
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

/-! ## The prover (6 phases, layout from the `.jinc` docstring) -/

def numLayers : Nat := 4
def numQueries : Nat := 3
def layerU64 : Nat := 136
def pathU64 : Nat := 20
def queryU64 : Nat := 44
def lanes : Nat := 4
def proofU64 : Nat := 546

/-- `plonky3_fri_prove_obj`: produce the flat 546-word FRI proof object. -/
def friProveObj (evals alpha qidx : Array UInt64) : Array UInt64 := Id.run do
  let mut proof : Array UInt64 := Array.replicate proofU64 0
  let mut cur := evals
  for L in [0:numLayers] do
    let n := 32 >>> L
    let half := n / 2
    let logn := 5 - L
    let lbase := L * layerU64
    -- Phase 1: leaf-hash; Phase 2: Merkle root (commitment)
    let leaves := buildLeafHashes cur n
    let root := merkleRoot leaves n
    for k in [0:4] do proof := proof.set! (lbase + k) root[k]!
    -- Phase 4: per-query openings + two auth paths
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
    -- Phase 3: fold cur (n) -> next (half) via real fri_fold, x_i = rou(logn)^i
    let ol := fRou logn
    let a := alpha[L]!
    let mut next : Array UInt64 := Array.replicate 32 0
    let mut xpow : UInt64 := 1
    for i in [0:half] do
      next := next.set! i (friFold cur[i]! cur[i + half]! xpow a)
      xpow := fMul xpow ol
    cur := next
  -- Phase 5: remainder coeffs [(e0+e1)/2, (e0-e1)/2]
  let inv2 := fInv 2
  proof := proof.set! (numLayers * layerU64 + 0) (fMul (fAdd cur[0]! cur[1]!) inv2)
  proof := proof.set! (numLayers * layerU64 + 1) (fMul (fSub cur[0]! cur[1]!) inv2)
  return proof

/-- Build the KAT column LDE: `p(x) = 7 + 3x + 5x^2 + 2x^3` on `K_32`. -/
def buildColumnLde : Array UInt64 := Id.run do
  let coeffs : Array UInt64 := #[7, 3, 5, 2]
  let omega := fRou 5
  let mut evals : Array UInt64 := Array.replicate 32 0
  let mut x : UInt64 := 1
  for i in [0:32] do
    evals := evals.set! i (fPolyEval coeffs x)
    x := fMul x omega
  return evals

def main : IO Unit := do
  let evals := buildColumnLde
  let alpha : Array UInt64 := #[101, 202, 303, 404]
  let qidx : Array UInt64 := #[3, 11, 26, 0]
  let proof := friProveObj evals alpha qidx
  for w in proof do
    IO.println (toString w.toNat)

end Plonky3FriProofRef

def main : IO Unit := Plonky3FriProofRef.main
