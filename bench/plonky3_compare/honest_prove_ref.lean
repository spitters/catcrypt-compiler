/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

@[expose] public section
/-
Executable bit-exact reference for `hp_prove`
(`bench/plonky3_compare/include/plonky3_honest_prover.jinc`).

This is the `denote = spec` TARGET the owned x86 emit of `hp_prove` must reproduce:
a pure Lean function over `Array UInt64` mirroring the honest Plonky3
Fibonacci-STARK prover phase-by-phase over the VERIFIED Poseidon2-BabyBear
permutation (no splitmix surrogate on the commit / FRI / Fiat-Shamir / PoW path):

  1. trace LDE (radix-2 coset NTT, `plonky3_trace_lde_3_8`)
  2. depth-5 codeword Merkle tree (`_hp_build_tree32`) over the verified
     PaddingFreeSponge<16,8,8> leaf hash + TruncatedPermutation<2,8,16> compress
  3. Fiat-Shamir duplex absorb/squeeze → beta  (`_hp_fs_*` over `p2_perm`)
  4. FRI fold 32 → 16 → 8 → 4 → 2 + fold-layer Merkle tree (`_hp_build_tree16`)
  5. proof-of-work GRIND: smallest nonce with `perm(root0 ‖ nonce)[0] & 255 == 0`
  6. 8-query auth-path opening (`_hp_open_query`) + 980-word object scatter

The data-dependent PoW grind (phase 5) is the motivating consumer of the
landed `whileLcmd`/`runWhile` primitive (`LprogControlFlow`, §7): we model the
grind as a `runWhile` over a `JState 64` whose `NONCE` register the body
increments and whose guard re-tests the public Fiat-Shamir PoW predicate, and
show the fuel-bounded `runWhile` lands on the same searched nonce as the pure
spec (and as the emitted prover). `fuel` is the grind difficulty bound; once the
guard goes false the result is fuel-robust (`runWhile_succ_of_halted`).

Validated by running it against the jasminc-emitted `hp_prove`
(`plonky3_honest_prove.s`, the real artifact, via `honest_prove_dump.c`)
byte-for-byte over the full 980-word object on the KAT Fibonacci trace
(height 8, width 3, a₀=0, b₀=1).

Run with `lake env lean --run bench/plonky3_compare/honest_prove_ref.lean`.
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

namespace Plonky3HonestProveRef

/-! ## BabyBear field arithmetic (byte-identical to the `_pr_*`/`_p2_*` jinc shims) -/

/-- BabyBear prime `p = 2^31 - 2^27 + 1`. -/
def bbP : UInt64 := 2013265921
/-- BabyBear multiplicative generator. -/
def bbG : UInt64 := 31

/-- `_pr_reduce` / `_p2_csub`: branchless single conditional subtraction of `p`
    (input `< 2p`; for a canonical input it is the identity). -/
def red (x : UInt64) : UInt64 :=
  let t := x - bbP
  if (t >>> 63) == 1 then t + bbP else t

/-- `_pr_add` / `_p2_fadd`: `(a+b) mod p` for canonical operands. -/
def fAdd (a b : UInt64) : UInt64 := red (a + b)
/-- `_pr_sub` / `_p2_fsub`: `(p + a - b) mod p`. -/
def fSub (a b : UInt64) : UInt64 := red (bbP + a - b)
/-- `_pr_mul` / `_p2_fmul`: `(a*b) mod p` (operands `< p < 2^31`, product `< 2^62`). -/
def fMul (a b : UInt64) : UInt64 := (a * b) % bbP

/-- `_pr_pow`: 64-iteration square-and-multiply. -/
def fPow (base exp : UInt64) : UInt64 := Id.run do
  let mut r : UInt64 := 1
  let mut c : UInt64 := base
  let mut e : UInt64 := exp
  for _ in [0:64] do
    if (e &&& 1) == 1 then r := fMul r c
    c := fMul c c
    e := e >>> 1
  return r

/-- `_pr_inv`: Fermat inverse (`0` maps to `0`). -/
def fInv (a : UInt64) : UInt64 := if a == 0 then 0 else fPow a (bbP - 2)

/-! ## Verified Poseidon2-BabyBear permutation (width 16), constants from
    `plonky3_poseidon2_hash.jinc`. -/

def diagV : Array UInt64 := #[
  2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918,
  2013265917, 2005401601, 1509949441, 1761607681, 2013265906, 7864320, 125829120, 15]

def rcInit : Array UInt64 := #[
  1774958255, 1185780729, 1621102414, 1796380621, 588815102, 1932426223, 1925334750, 747903232,
  89648862, 360728943, 977184635, 1425273457, 256487465, 1200041953, 572403254, 448208942,
  1215789478, 944884184, 953948096, 547326025, 646827752, 889997530, 1536873262, 86189867,
  1065944411, 32019634, 333311454, 456061748, 1963448500, 1827584334, 1391160226, 1348741381,
  88424255, 104111868, 1763866748, 79691676, 1988915530, 1050669594, 359890076, 573163527,
  222820492, 159256268, 669703072, 763177444, 889367200, 256335831, 704371273, 25886717,
  51754520, 1833211857, 454499742, 1384520381, 777848065, 1053320300, 1851729162, 344647910,
  401996362, 1046925956, 5351995, 1212119315, 754867989, 36972490, 751272725, 506915399]

def rcFin : Array UInt64 := #[
  1922082829, 1870549801, 1502529704, 1990744480, 1700391016, 1702593455, 321330495, 528965731,
  183414327, 1886297254, 1178602734, 1923111974, 744004766, 549271463, 1781349648, 542259047,
  1536158148, 715456982, 503426110, 340311124, 1558555932, 1226350925, 742828095, 1338992758,
  1641600456, 1843351545, 301835475, 43203215, 386838401, 1520185679, 1235297680, 904680097,
  1491801617, 1581784677, 913384905, 247083962, 532844013, 107190701, 213827818, 1979521776,
  1358282574, 1681743681, 1867507480, 1530706910, 507181886, 695185447, 1172395131, 1250800299,
  1503161625, 817684387, 498481458, 494676004, 1404253825, 108246855, 59414691, 744214112,
  890862029, 1342765939, 1417398904, 1897591937, 1066647396, 1682806907, 1015795079, 1619482808]

def rcInt : Array UInt64 := #[
  1518359488, 1765533241, 945325693, 422793067, 311365592, 1311448267, 1629555936, 1009879353,
  190525218, 786108885, 557776863, 212616710, 605745517]

/-- `_p2_sbox`: `x^7` over BabyBear. -/
def sbox (x : UInt64) : UInt64 :=
  let x2 := fMul x x
  let x4 := fMul x2 x2
  let t  := fMul x2 x
  fMul x4 t

/-- `_p2_mds`: the external (full-round) MDS layer over the 16-lane state. -/
def mds (s : Array UInt64) : Array UInt64 := Id.run do
  let mut s := s
  for blk in [0:4] do
    let base := blk * 4
    let a := s[base]!; let b := s[base+1]!; let c := s[base+2]!; let d := s[base+3]!
    let t01 := fAdd a b
    let t23 := fAdd c d
    let t0123 := fAdd t01 t23
    let t11 := fAdd t0123 b
    let t33 := fAdd t0123 d
    let two0 := fAdd a a
    let two2 := fAdd c c
    let n3 := fAdd t33 two0
    let n1 := fAdd t11 two2
    let n0 := fAdd t11 t01
    let n2 := fAdd t33 t23
    s := s.set! base n0 |>.set! (base+1) n1 |>.set! (base+2) n2 |>.set! (base+3) n3
  for k in [0:4] do
    let s0 := s[k]!; let s1 := s[k+4]!; let s2 := s[k+8]!; let s3 := s[k+12]!
    let sumk := fAdd (fAdd (fAdd s0 s1) s2) s3
    s := s.set! k (fAdd s[k]! sumk)
    s := s.set! (k+4) (fAdd s[k+4]! sumk)
    s := s.set! (k+8) (fAdd s[k+8]! sumk)
    s := s.set! (k+12) (fAdd s[k+12]! sumk)
  return s

/-- `_p2_internal_mat`: the internal (partial-round) diagonal matrix layer. -/
def internalMat (s : Array UInt64) : Array UInt64 := Id.run do
  let mut s := s
  let mut sum := s[0]!
  for i in [1:16] do sum := fAdd sum s[i]!
  let two0 := fAdd s[0]! s[0]!
  s := s.set! 0 (fSub sum two0)
  for i in [1:16] do
    let v := diagV[i]!
    let t := fMul v s[i]!
    s := s.set! i (fAdd t sum)
  return s

/-- `p2_perm`: the 8-full + 13-partial Poseidon2-BabyBear permutation. -/
def perm (inp : Array UInt64) : Array UInt64 := Id.run do
  let mut dst := inp
  dst := mds dst
  for r in [0:4] do
    let base := r * 16
    for k in [0:16] do
      let x := fAdd dst[k]! rcInit[base+k]!
      dst := dst.set! k (sbox x)
    dst := mds dst
  for r in [0:13] do
    let x := fAdd dst[0]! rcInt[r]!
    dst := dst.set! 0 (sbox x)
    dst := internalMat dst
  for r in [0:4] do
    let base := r * 16
    for k in [0:16] do
      let x := fAdd dst[k]! rcFin[base+k]!
      dst := dst.set! k (sbox x)
    dst := mds dst
  return dst

/-! ## p3 hashes over the verified permutation. -/

/-- `_p2_sponge_row` (PaddingFreeSponge<16,8,8>): hash a width-≤8 row → 8 lanes. -/
def spongeRow (row : Array UInt64) : Array UInt64 := Id.run do
  let mut st : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do st := st.set! i (red row[i]!)
  let po := perm st
  return Array.ofFn (n := 8) (fun k => po[k.val]!)

/-- `_p2_compress` (TruncatedPermutation<2,8,16>): 2-to-1 of two 8-lane digests. -/
def compress (l r : Array UInt64) : Array UInt64 := Id.run do
  let mut st : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do st := st.set! i l[i]!
  for i in [0:8] do st := st.set! (8+i) r[i]!
  let po := perm st
  return Array.ofFn (n := 8) (fun k => po[k.val]!)

/-- `_hp_leaf_row3`: hash a width-3 row to an 8-lane leaf. -/
def leafRow3 (v0 v1 v2 : UInt64) : Array UInt64 :=
  spongeRow #[v0, v1, v2, 0, 0, 0, 0, 0]

/-- `_hp_leaf_fe`: hash a single field element to an 8-lane leaf. -/
def leafFe (v : UInt64) : Array UInt64 :=
  spongeRow #[v, 0, 0, 0, 0, 0, 0, 0]

/-! ## Radix-2 Cooley-Tukey NTT over BabyBear (`_pr_ntt*`/`_pr_intt8`). -/

/-- Reverse the low `bits` bits of `i`. -/
def bitrev (bits : Nat) (i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut t := i
  for _ in [0:bits] do
    r := r * 2 + (t % 2)
    t := t / 2
  return r

/-- In-place forward radix-2 DIT NTT of `n = 2^logn` elements with root `omega`. -/
def ntt (logn : Nat) (io : Array UInt64) (omega : UInt64) : Array UInt64 := Id.run do
  let n := io.size
  let mut a : Array UInt64 := Array.replicate n 0
  for idx in [0:n] do a := a.set! idx io[bitrev logn idx]!
  for layer in [0:logn] do
    let size := 1 <<< (layer + 1)
    let half := size / 2
    let wsize := fPow omega (UInt64.ofNat (n / size))
    let mut blk := 0
    while blk < n do
      let mut wpow : UInt64 := 1
      for pos in [0:half] do
        let lo := a[blk + pos]!
        let hi := a[blk + pos + half]!
        let t := fMul wpow hi
        a := a.set! (blk + pos) (fAdd lo t)
        a := a.set! (blk + pos + half) (fSub lo t)
        wpow := fMul wpow wsize
      blk := blk + size
  return a

/-- `_pr_intt8`: inverse 8-point NTT (forward with `omega⁻¹`, scaled by `n⁻¹`). -/
def intt8 (io : Array UInt64) (omega : UInt64) : Array UInt64 := Id.run do
  let oi := fInv omega
  let mut r := ntt 3 io oi
  let ni := fInv 8
  for i in [0:8] do r := r.set! i (fMul r[i]! ni)
  return r

/-- `plonky3_trace_lde_3_8`: `u64[24]` trace → `u64[96]` width-3 interleaved LDE. -/
def traceLde (tr : Array UInt64) : Array UInt64 := Id.run do
  let mut o : Array UInt64 := Array.replicate 96 0
  let omegaTrace := fPow bbG ((bbP - 1) >>> 3)
  let omegaN := fPow bbG ((bbP - 1) >>> 5)
  for col in [0:3] do
    -- (a) extract + canonicalize this column's 8 trace samples
    let mut colbuf : Array UInt64 := Array.replicate 8 0
    for row in [0:8] do colbuf := colbuf.set! row (red tr[3*row + col]!)
    -- (b) inverse NTT over H → coefficient form
    colbuf := intt8 colbuf omegaTrace
    -- (c) zero-pad 8 → 32
    let mut ldeCol : Array UInt64 := Array.replicate 32 0
    for row in [0:8] do ldeCol := ldeCol.set! row colbuf[row]!
    -- (d) coset twist: ldeCol[i] *= 31^i (rolling)
    let mut w : UInt64 := 1
    for row in [0:32] do
      ldeCol := ldeCol.set! row (fMul ldeCol[row]! w)
      w := fMul w bbG
    -- (e) forward NTT over K → LDE evaluations
    ldeCol := ntt 5 ldeCol omegaN
    -- (f) interleave row-major
    for row in [0:32] do o := o.set! (3*row + col) ldeCol[row]!
  return o

/-! ## Codeword + fold-layer Merkle trees (`_hp_build_tree32`/`_hp_build_tree16`). -/

/-- Copy an 8-lane digest into `nodes` at lane offset `off`. -/
def putDigest (nodes : Array UInt64) (off : Nat) (d : Array UInt64) : Array UInt64 := Id.run do
  let mut nodes := nodes
  for i in [0:8] do nodes := nodes.set! (off + i) d[i]!
  return nodes

/-- Read the 8-lane digest at lane offset `off`. -/
def getDigest (nodes : Array UInt64) (off : Nat) : Array UInt64 :=
  Array.ofFn (n := 8) (fun k => nodes[off + k.val]!)

/-- `_hp_build_tree32`: depth-5 codeword tree over the 32 width-3 LDE rows.
    Levels packed contiguously: leaves(256), l16(128), l8(64), l4(32), l2(16),
    root(8) → 504 lanes. -/
def buildTree32 (lde : Array UInt64) : Array UInt64 := Id.run do
  let mut nodes : Array UInt64 := Array.replicate 504 0
  for leaf in [0:32] do
    let d := leafRow3 lde[3*leaf]! lde[3*leaf+1]! lde[3*leaf+2]!
    nodes := putDigest nodes (leaf*8) d
  -- level 1: 16 nodes at 256
  for j in [0:16] do
    let d := compress (getDigest nodes ((2*j)*8)) (getDigest nodes ((2*j+1)*8))
    nodes := putDigest nodes (256 + j*8) d
  -- level 2: 8 nodes at 384
  for j in [0:8] do
    let d := compress (getDigest nodes (256 + (2*j)*8)) (getDigest nodes (256 + (2*j+1)*8))
    nodes := putDigest nodes (384 + j*8) d
  -- level 3: 4 nodes at 448
  for j in [0:4] do
    let d := compress (getDigest nodes (384 + (2*j)*8)) (getDigest nodes (384 + (2*j+1)*8))
    nodes := putDigest nodes (448 + j*8) d
  -- level 4: 2 nodes at 480
  for j in [0:2] do
    let d := compress (getDigest nodes (448 + (2*j)*8)) (getDigest nodes (448 + (2*j+1)*8))
    nodes := putDigest nodes (480 + j*8) d
  -- root at 496
  let d := compress (getDigest nodes 480) (getDigest nodes 488)
  nodes := putDigest nodes 496 d
  return nodes

/-- `_hp_build_tree16`: depth-4 tree over 16 field-element leaves.
    Levels: l16(128), l8(64), l4(32), l2(16), root(8) → 248 lanes. -/
def buildTree16 (ev : Array UInt64) : Array UInt64 := Id.run do
  let mut nd : Array UInt64 := Array.replicate 248 0
  for leaf in [0:16] do nd := putDigest nd (leaf*8) (leafFe ev[leaf]!)
  for j in [0:8] do
    let d := compress (getDigest nd ((2*j)*8)) (getDigest nd ((2*j+1)*8))
    nd := putDigest nd (128 + j*8) d
  for j in [0:4] do
    let d := compress (getDigest nd (128 + (2*j)*8)) (getDigest nd (128 + (2*j+1)*8))
    nd := putDigest nd (192 + j*8) d
  for j in [0:2] do
    let d := compress (getDigest nd (192 + (2*j)*8)) (getDigest nd (192 + (2*j+1)*8))
    nd := putDigest nd (224 + j*8) d
  let d := compress (getDigest nd 224) (getDigest nd 232)
  nd := putDigest nd 240 d
  return nd

/-- `_hp_authpath32`: 5 sibling digests (40 lanes) for codeword index `idx0`. -/
def authpath32 (nodes : Array UInt64) (idx0 : Nat) : Array UInt64 := Id.run do
  let mut path : Array UInt64 := Array.replicate 40 0
  let bases : Array Nat := #[0, 256, 384, 448, 480]
  let mut idx := idx0
  for lvl in [0:5] do
    let sib := idx ^^^ 1
    let src := bases[lvl]! + sib*8
    for i in [0:8] do path := path.set! (lvl*8 + i) nodes[src + i]!
    idx := idx >>> 1
  return path

/-- `_hp_authpath16`: 4 sibling digests (32 lanes) for fold-layer index `idx0`. -/
def authpath16 (nd : Array UInt64) (idx0 : Nat) : Array UInt64 := Id.run do
  let mut path : Array UInt64 := Array.replicate 32 0
  let bases : Array Nat := #[0, 128, 192, 224]
  let mut idx := idx0
  for lvl in [0:4] do
    let sib := idx ^^^ 1
    let src := bases[lvl]! + sib*8
    for i in [0:8] do path := path.set! (lvl*8 + i) nd[src + i]!
    idx := idx >>> 1
  return path

/-! ## Fiat-Shamir duplex challenger (`_hp_fs_*`). -/

/-- `_hp_fs_absorb8`: overwrite the rate (lanes 0..8, reduced) then permute. -/
def fsAbsorb8 (st : Array UInt64) (blk : Array UInt64) : Array UInt64 := Id.run do
  let mut st := st
  for i in [0:8] do st := st.set! i (red blk[i]!)
  return perm st

/-- `_hp_fs_squeeze`: permute again (read-side reads lane 0 afterward). -/
def fsSqueeze (st : Array UInt64) : Array UInt64 := perm st

/-! ## The PoW grind via the `runWhile` data-dependent-while primitive.

The honest prover's phase-6 grind is `h0 = 1; while (h0 != 0) { fs[8] = nonce;
h0 = perm(fs)[0] & 255; if (h0 != 0) nonce += 1 }`. The guard is over PUBLIC
Fiat-Shamir transcript state (`LprogControlFlow` §7.3 classifies it
`public-while`), so it is the motivating consumer of the landed `whileLcmd` /
`runWhile` primitive. We model it as a `runWhile` over a `JState 64`:

* state: the search counter lives in the `NONCE` register;
* body `[JInstr.add "NONCE" (.imm 1)]`: increment the nonce (machine `ADD`,
  interpreted by `runBlock`);
* guard `s ↦ powH0 (nonce s) ≠ 0`: re-test the public PoW predicate.

`runWhile fuel guard body s₀` then lands on the smallest nonce with
`perm(root0 ‖ nonce)[0] & 255 == 0` — the same value the pure spec and the
emitted prover produce. `fuel` is the grind difficulty bound (≥ the found
nonce); above it the result is fuel-robust (`runWhile_succ_of_halted`). -/

/-- `_hp_pow_test` lane-0: `perm(root0[0..8] ‖ nonce ‖ 0…)[0]`, masked to 8 bits. -/
def powH0 (root0 : Array UInt64) (nonce : UInt64) : UInt64 := Id.run do
  let mut fs : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do fs := fs.set! i root0[i]!
  fs := fs.set! 8 nonce
  let po := perm fs
  return po[0]! &&& 255

/-- The `runWhile` grind: increment-`NONCE` body + public PoW guard. -/
def grindBody : List (JInstr 64) := [JInstr.add "NONCE" (.imm 1)]

def grindGuard (root0 : Array UInt64) : JState 64 → Bool :=
  fun s => powH0 root0 (UInt64.ofNat (s.get "NONCE").toNat) != 0

/-- Run the grind via `runWhile` from `NONCE = 0`, returning the searched nonce. -/
def grindNonce (root0 : Array UInt64) (fuel : Nat) : UInt64 :=
  let s0 : JState 64 := { regs := fun _ => 0 }
  let sFinal := runWhile fuel (grindGuard root0) grindBody s0
  UInt64.ofNat (sFinal.get "NONCE").toNat

/-! ## The prover (980-word object). -/

/-- FRI fold combinator `q = (a+b) + beta*(a-b)`. -/
def friFoldBeta (a b beta : UInt64) : UInt64 :=
  let s := fAdd a b
  let d := fSub a b
  fAdd s (fMul d beta)

/-- `_hp_open_query`: serialize one query record at `base` (120 lanes). -/
def openQuery (out lde nodes nd16 f16 : Array UInt64) (q base : Nat) : Array UInt64 := Id.run do
  let mut out := out
  out := out.set! (base + 0) (UInt64.ofNat q)
  out := out.set! (base + 1) lde[3*q]!
  out := out.set! (base + 2) lde[3*q+1]!
  out := out.set! (base + 3) lde[3*q+2]!
  let path := authpath32 nodes q
  for i in [0:40] do out := out.set! (base + 4 + i) path[i]!
  let qp := q ^^^ 16
  out := out.set! (base + 44) lde[3*qp]!
  out := out.set! (base + 45) lde[3*qp+1]!
  out := out.set! (base + 46) lde[3*qp+2]!
  let pathp := authpath32 nodes qp
  for i in [0:40] do out := out.set! (base + 47 + i) pathp[i]!
  let qq := q &&& 15
  out := out.set! (base + 87) f16[qq]!
  let path16 := authpath16 nd16 qq
  for i in [0:32] do out := out.set! (base + 88 + i) path16[i]!
  return out

/-- `hp_prove`: the full honest prover. `p0 = u64[24]` Fibonacci trace →
    `u64[980]` flat proof object. -/
def hpProve (p0 : Array UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.replicate 980 0
  -- 1. LDE
  let lde := traceLde p0
  -- 2. codeword Merkle tree
  let nodes := buildTree32 lde
  let root0 := getDigest nodes 496
  for i in [0:8] do out := out.set! i root0[i]!
  -- 3. Fiat-Shamir: absorb pub, root0; squeeze beta
  let mut fs : Array UInt64 := Array.replicate 16 0
  let pubBlk : Array UInt64 := #[p0[0]!, p0[1]!, p0[23]!, 0, 0, 0, 0, 0]
  fs := fsAbsorb8 fs pubBlk
  fs := fsAbsorb8 fs root0
  fs := fsSqueeze fs
  let beta := red fs[0]!
  -- 4. FRI fold 32 → 16 on column-0 values
  let mut col0 : Array UInt64 := Array.replicate 16 0
  for i in [0:16] do col0 := col0.set! i (red lde[3*i]!)
  let mut f16 : Array UInt64 := Array.replicate 16 0
  for i in [0:16] do
    f16 := f16.set! i (friFoldBeta col0[i]! (red lde[3*(i+16)]!) beta)
  let nd16 := buildTree16 f16
  let root16 := getDigest nd16 240
  for i in [0:8] do out := out.set! (8 + i) root16[i]!
  -- final poly: 16 → 8 → 4 → 2 (col0 reused as scratch)
  for i in [0:8] do col0 := col0.set! i (friFoldBeta f16[i]! f16[8+i]! beta)
  for i in [0:4] do col0 := col0.set! i (friFoldBeta col0[i]! col0[4+i]! beta)
  for i in [0:2] do col0 := col0.set! i (friFoldBeta col0[i]! col0[2+i]! beta)
  out := out.set! 16 col0[0]!
  out := out.set! 17 col0[1]!
  out := out.set! 18 beta
  -- 5. PoW grind via runWhile (fuel = grind difficulty bound, 8 bits → ≤ 4096)
  let nonce := grindNonce root0 4096
  out := out.set! 19 nonce
  -- 6. query phase + serialization
  let mut fq : Array UInt64 := Array.replicate 16 0
  fq := fsAbsorb8 fq pubBlk
  fq := fsAbsorb8 fq root0
  fq := fsAbsorb8 fq root16
  fq := fsAbsorb8 fq #[nonce, 0, 0, 0, 0, 0, 0, 0]
  for r in [0:8] do
    fq := fsSqueeze fq
    let q := ((red fq[0]!) &&& 31).toNat
    let base := 20 + r*120
    out := openQuery out lde nodes nd16 f16 q base
  return out

/-! ## KAT harness: the Fibonacci width-3 height-8 trace. -/

/-- Build the KAT trace `a₀=0, b₀=1`, rows `(a, b, a+b)`. -/
def buildTrace : Array UInt64 := Id.run do
  let mut trace : Array UInt64 := Array.replicate 24 0
  let mut a : UInt64 := 0
  let mut b : UInt64 := 1
  for row in [0:8] do
    trace := trace.set! (3*row + 0) a
    trace := trace.set! (3*row + 1) b
    let c := a + b
    trace := trace.set! (3*row + 2) c
    a := b; b := c
  return trace

def main : IO Unit := do
  let trace := buildTrace
  let proof := hpProve trace
  for w in proof do
    IO.println (toString w.toNat)

end Plonky3HonestProveRef

def main : IO Unit := Plonky3HonestProveRef.main
