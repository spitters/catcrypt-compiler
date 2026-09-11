/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuardWhile
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuardWhile
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

@[expose] public section

set_option autoImplicit false

/-!
# plonky3 `honest_prove`: the FRONT-COMPILED spine phases, validated against the spec pin

`plonky3_honest_prove.s` (whitelist row `# L`) is the jasminc compilation of
`hp_prove` (`bench/plonky3_compare/include/plonky3_honest_prover.jinc`), the honest
Fibonacci-STARK prover over the verified Poseidon2-BabyBear permutation:
trace-LDE → depth-5 Merkle → Fiat-Shamir → FRI fold `32→16→8→4→2` → PoW grind →
8-query opening → 980-word scatter.  Its bit-exact executable reference is the
spec pin `bench/plonky3_compare/honest_prove_ref.lean` (machine-validated
word-for-word against the linked jasminc artifact via `honest_prove_dump.c`);
`bench/` files are not importable, so §1 restates the needed fragment verbatim
and re-pins its two data-dependent words (`beta`, `nonce`) by `native_decide`.

What front-compiles here (committed combinators only — no hand-authored
`Com`/`Lcmd`/`JInstr`/`.s`):

* **§2–§3 The FRI fold chain (4 phases, ONE `ComL` spine).**  `hpFoldChainComL`
  chains `hp_prove`'s §4 fold phases through `rolledForLoopNRtCont`: phase 1
  folds the column-0 LDE rows (`buf[i] := foldβ(red lde[3i], red lde[3(i+16)])`,
  the pin's `col0` extraction merged into the fold read), phases 2–4 halve in
  place (`16→8→4→2`).  The Fiat-Shamir challenge `beta` rides in the
  accumulator's spare slot (`buf[16]`), so the chain is a single-accumulator
  fold.  `denote = the pin's `out[16..17]`` on the pin's KAT trace — the LDE
  input is the restated `traceLde (buildTrace)` and `beta` the restated
  Fiat-Shamir value, itself re-pinned to the machine-validated word-18
  (`1994889016`).

* **§4 The PoW grind (data-dependent while, front-compiled).**  `hp_prove`'s §6
  grind is `while (h0 != 0) { permute; h0 := lane0 & 255; nonce += (h0≠0) }` —
  the exact `RWhileNz`-with-leaf-call shape of
  `TranslateDialectDataWhile`/`TranslateDialectLoopCallLink`.  `grindWhileProg`
  front-compiles the body (leaf `RCall` → real linked `Lcall`, branch-free
  conditional increment `(h0+255)>>8`) and wraps it in the guard-driven
  `whileLinstrRM`.  Structure gates: real `Lcond` back-edge, real `Lcall`, no
  `CALL:` shadow.  The in-model interpreter denote runs against a SMALL
  surrogate leaf (`h0 = (nonce ^ 5) & 255`, halting at nonce 5, trip read off
  the run) — the real Poseidon2 leaf's `LinstrRM` image is ~10³ instructions and
  the A2 interpreter's register store is linear-lookup, so the real-perm
  in-model grind run is out of `native_decide` range (gap 2 below); the REAL
  grind semantics is instead pinned purely: §1's `findNonce` over the restated
  permutation lands on the machine-validated word-19 (`nonce = 99`).

## What still blocks the whole-artifact flip (precise; the row stays `# L`)

1. **Callee-leaf owned emits + linked composition.**  `hp_prove`'s heavy phases
   are calls to real callees (`plonky3_trace_lde_3_8`, `_hp_build_tree32`,
   `_hp_fs_absorb8`, `_hp_open_query`) whose loop spines must themselves be
   front-emitted `.s` and linked (the owned Poseidon2 permute + sponge leaves
   exist: `poseidon2_bb_owned.s`, `p2_sponge_owned.s`; the tree/authpath/query
   spines do not).  The Merkle tree shape is §5–§6 of the fri_proof twin module
   (`Plonky3FriProofFrontEmit.merkleComL` — leaf-hash ; nested level loop) with
   the mixer swapped for the 8-lane Poseidon2 leaf call: the CONTROL shape is
   front-covered, the missing piece is the per-iteration multi-word (8-lane)
   leaf-call marshalling (`LeafGen` writes ONE destination register; an 8-lane
   digest callee needs the SysV memref-pointer marshalling of
   `loopBodyCallLcmd`).
2. **In-model validation scale for call-carrying spines.**  Call-carrying phases
   denote through the A2/A3 `LstateM` interpreter (`lsemFuelMemLC`), whose
   register/array stores are association-chain closures — fine at validate
   sizes, out of range for a 63-permutation Merkle build × 8 queries.  The
   whole-artifact `denote = pin` gate needs either an efficient interpreter
   carrier or the C-side byte-KAT directly (the orchestrator's asm-gate).
3. **Query-loop addressing.**  The 8-query loop's record base `20 + r·120` is
   the runtime-stride shape (front-covered by
   `RuntimeStrideRowFrontValidate`); the per-query record writer
   (`_hp_open_query`) is a straight-line + two-authpath spine, front-coverable
   by the same walker-free trick as the fri_proof twin (level-`l` index =
   `q >> l`), assembly not done here.

No `sorry`, no new axiom.

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/VIR/Plonky3HonestProveFrontEmit.lean
Invoke (emit the fragment `.s`):
  lake env lean --run bench/plonky3_compare/hp_frontphases_emit.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HonestProveFrontEmit

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
  (rolledForLoopNRtCont)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit
  (bbP bbG fReduce fAdd fSub fMul fPow fInv bbPn muBB setE csubL mulL addL subL
    specSlots)

/-- `RSeq`-chain (the fri_proof twin's `seqAll`; aliased because
    `TranslateDialectLoopCallLink` exports a `seqAll` too). -/
def sqAll : List LowCT → LowCT :=
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriProofFrontEmit.seqAll

/-! ## 1. The spec-pin fragment (restated from
    `bench/plonky3_compare/honest_prove_ref.lean`)

The field layer (`fReduce`/`fAdd`/`fSub`/`fMul`/`fPow`/`fInv`) is shared with the
fri_proof twin (identical pin definitions).  Below: the verified
Poseidon2-BabyBear permutation constants + rounds, the p3 hashes, the coset-NTT
trace LDE, the codeword tree, the Fiat-Shamir duplex, the fold combinator, the
PoW predicate, and the KAT trace — all verbatim from the pin. -/

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

/-- `_p2_sbox`: `x^7` (pin). -/
def sbox (x : UInt64) : UInt64 :=
  let x2 := fMul x x
  let x4 := fMul x2 x2
  let t  := fMul x2 x
  fMul x4 t

/-- `_p2_mds` (pin). -/
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

/-- `_p2_internal_mat` (pin). -/
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

/-- `p2_perm`: 8-full + 13-partial Poseidon2-BabyBear (pin). -/
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

/-- `_p2_sponge_row` (PaddingFreeSponge<16,8,8>) (pin). -/
def spongeRow (row : Array UInt64) : Array UInt64 := Id.run do
  let mut st : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do st := st.set! i (fReduce row[i]!)
  let po := perm st
  return Array.ofFn (n := 8) (fun k => po[k.val]!)

/-- `_p2_compress` (TruncatedPermutation<2,8,16>) (pin). -/
def compress (l r : Array UInt64) : Array UInt64 := Id.run do
  let mut st : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do st := st.set! i l[i]!
  for i in [0:8] do st := st.set! (8+i) r[i]!
  let po := perm st
  return Array.ofFn (n := 8) (fun k => po[k.val]!)

/-- `_hp_leaf_row3` (pin). -/
def leafRow3 (v0 v1 v2 : UInt64) : Array UInt64 :=
  spongeRow #[v0, v1, v2, 0, 0, 0, 0, 0]

/-- Reverse the low `bits` bits of `i` (pin). -/
def bitrev (bits : Nat) (i : Nat) : Nat := Id.run do
  let mut r := 0
  let mut t := i
  for _ in [0:bits] do
    r := r * 2 + (t % 2)
    t := t / 2
  return r

/-- Forward radix-2 DIT NTT (pin). -/
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

/-- `_pr_intt8` (pin). -/
def intt8 (io : Array UInt64) (omega : UInt64) : Array UInt64 := Id.run do
  let oi := fInv omega
  let mut r := ntt 3 io oi
  let ni := fInv 8
  for i in [0:8] do r := r.set! i (fMul r[i]! ni)
  return r

/-- `plonky3_trace_lde_3_8` (pin). -/
def traceLde (tr : Array UInt64) : Array UInt64 := Id.run do
  let mut o : Array UInt64 := Array.replicate 96 0
  let omegaTrace := fPow bbG ((bbP - 1) >>> 3)
  let omegaN := fPow bbG ((bbP - 1) >>> 5)
  for col in [0:3] do
    let mut colbuf : Array UInt64 := Array.replicate 8 0
    for row in [0:8] do colbuf := colbuf.set! row (fReduce tr[3*row + col]!)
    colbuf := intt8 colbuf omegaTrace
    let mut ldeCol : Array UInt64 := Array.replicate 32 0
    for row in [0:8] do ldeCol := ldeCol.set! row colbuf[row]!
    let mut w : UInt64 := 1
    for row in [0:32] do
      ldeCol := ldeCol.set! row (fMul ldeCol[row]! w)
      w := fMul w bbG
    ldeCol := ntt 5 ldeCol omegaN
    for row in [0:32] do o := o.set! (3*row + col) ldeCol[row]!
  return o

/-- Digest write helper (pin). -/
def putDigest (nodes : Array UInt64) (off : Nat) (d : Array UInt64) : Array UInt64 := Id.run do
  let mut nodes := nodes
  for i in [0:8] do nodes := nodes.set! (off + i) d[i]!
  return nodes

/-- Digest read helper (pin). -/
def getDigest (nodes : Array UInt64) (off : Nat) : Array UInt64 :=
  Array.ofFn (n := 8) (fun k => nodes[off + k.val]!)

/-- `_hp_build_tree32` (pin). -/
def buildTree32 (lde : Array UInt64) : Array UInt64 := Id.run do
  let mut nodes : Array UInt64 := Array.replicate 504 0
  for leaf in [0:32] do
    let d := leafRow3 lde[3*leaf]! lde[3*leaf+1]! lde[3*leaf+2]!
    nodes := putDigest nodes (leaf*8) d
  for j in [0:16] do
    let d := compress (getDigest nodes ((2*j)*8)) (getDigest nodes ((2*j+1)*8))
    nodes := putDigest nodes (256 + j*8) d
  for j in [0:8] do
    let d := compress (getDigest nodes (256 + (2*j)*8)) (getDigest nodes (256 + (2*j+1)*8))
    nodes := putDigest nodes (384 + j*8) d
  for j in [0:4] do
    let d := compress (getDigest nodes (384 + (2*j)*8)) (getDigest nodes (384 + (2*j+1)*8))
    nodes := putDigest nodes (448 + j*8) d
  for j in [0:2] do
    let d := compress (getDigest nodes (448 + (2*j)*8)) (getDigest nodes (448 + (2*j+1)*8))
    nodes := putDigest nodes (480 + j*8) d
  let d := compress (getDigest nodes 480) (getDigest nodes 488)
  nodes := putDigest nodes 496 d
  return nodes

/-- `_hp_fs_absorb8` (pin). -/
def fsAbsorb8 (st : Array UInt64) (blk : Array UInt64) : Array UInt64 := Id.run do
  let mut st := st
  for i in [0:8] do st := st.set! i (fReduce blk[i]!)
  return perm st

/-- `_hp_fs_squeeze` (pin). -/
def fsSqueeze (st : Array UInt64) : Array UInt64 := perm st

/-- FRI fold combinator `q = (a+b) + beta*(a-b)` (pin). -/
def friFoldBeta (a b beta : UInt64) : UInt64 :=
  let s := fAdd a b
  let d := fSub a b
  fAdd s (fMul d beta)

/-- `_hp_pow_test` lane-0 (pin). -/
def powH0 (root0 : Array UInt64) (nonce : UInt64) : UInt64 := Id.run do
  let mut fs : Array UInt64 := Array.replicate 16 0
  for i in [0:8] do fs := fs.set! i root0[i]!
  fs := fs.set! 8 nonce
  let po := perm fs
  return po[0]! &&& 255

/-- The KAT Fibonacci trace (pin). -/
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

/-! ### 1.1 The pin-derived KAT values (re-pinned to the machine-validated words) -/

/-- The KAT trace LDE. -/
def ldeKAT : Array UInt64 := traceLde buildTrace

/-- The KAT codeword-tree root (`nodes[496..503]`). -/
def root0KAT : Array UInt64 := getDigest (buildTree32 ldeKAT) 496

/-- The KAT Fiat-Shamir challenge `beta` (absorb pub ; absorb root0 ; squeeze). -/
def betaKAT : UInt64 := Id.run do
  let tr := buildTrace
  let mut fs : Array UInt64 := Array.replicate 16 0
  let pubBlk : Array UInt64 := #[tr[0]!, tr[1]!, tr[23]!, 0, 0, 0, 0, 0]
  fs := fsAbsorb8 fs pubBlk
  fs := fsAbsorb8 fs root0KAT
  fs := fsSqueeze fs
  return fReduce fs[0]!

/-- The pure PoW grind: smallest nonce ≤ fuel with `powH0 = 0`. -/
def findNonce (root0 : Array UInt64) : Nat → UInt64 → UInt64
  | 0, nonce => nonce
  | fuel + 1, nonce =>
      if powH0 root0 nonce != 0 then findNonce root0 fuel (nonce + 1) else nonce

/-- **`beta` re-pins to the machine-validated proof word 18.** -/
theorem betaKAT_word18 : betaKAT.toNat = 1994889016 := by native_decide

/-- **The PoW grind re-pins to the machine-validated proof word 19
    (`nonce = 99`).** -/
theorem grind_word19 : (findNonce root0KAT 4096 0).toNat = 99 := by native_decide

/-- The pin's §4 fold arm after `k` phases (phase 1 = the `col0`-extraction fold
    `32→16`, phases 2–4 the in-place halvings `16→8→4→2`; mirrors `hpProve` with
    the fold buffer unified). -/
def hpFoldSpec (lde : Array UInt64) (beta : UInt64) (k : Nat) : Array UInt64 := Id.run do
  let mut buf : Array UInt64 := Array.replicate 16 0
  if k ≥ 1 then
    for i in [0:16] do
      buf := buf.set! i
        (friFoldBeta (fReduce lde[3*i]!) (fReduce lde[3*(i+16)]!) beta)
  if k ≥ 2 then
    for i in [0:8] do buf := buf.set! i (friFoldBeta buf[i]! buf[8+i]! beta)
  if k ≥ 3 then
    for i in [0:4] do buf := buf.set! i (friFoldBeta buf[i]! buf[4+i]! beta)
  if k ≥ 4 then
    for i in [0:2] do buf := buf.set! i (friFoldBeta buf[i]! buf[2+i]! beta)
  return buf

/-! ## 2. The FRI fold chain, front-compiled (4 phases, ONE `ComL`)

Accumulator `buf : memref 17` — slots `0..15` the fold buffer, slot `16` the
Fiat-Shamir challenge `beta` (an input the phases only read, riding in the
accumulator so each phase stays a single-accumulator fold).  Phase 1 reads the
interleaved width-3 LDE (`lde[3i]` column 0) — the stride-3 element index is
computed per trip; phases 2–4 halve in place. -/

/-- The `buf` array slot (17 words). -/
def bufArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"buf", .TBytes (8 * 17)⟩
/-- The `lde` array slot (96 words). -/
def ldeArr : CatCrypt.Crypto.Jasmin.LowCT.Located := ⟨"lde", .TBytes (8 * 96)⟩

/-- Phase-1 trip: `buf[idx] := foldβ(red lde[3idx], red lde[3idx+48], buf[16])`. -/
def hpFold1Body : LowCT := sqAll <|
  [ setE "i3"   (.SMul (.SVar "idx") (.SLit 3)),
    setE "i348" (.SAdd (.SVar "i3") (.SLit 48)),
    setE "z16"  (.SLit 16),
    .RArrLoad ⟨"lv", .TU64⟩ ldeArr "i3",
    .RArrLoad ⟨"lw", .TU64⟩ ldeArr "i348",
    .RArrLoad ⟨"bt", .TU64⟩ bufArr "z16" ]
  ++ csubL "aa" "lv"
  ++ csubL "bb" "lw"
  ++ addL "ss" (.SVar "aa") (.SVar "bb")
  ++ subL "dd" (.SVar "aa") (.SVar "bb")
  ++ mulL "tm" (.SVar "dd") (.SVar "bt")
  ++ addL "oo" (.SVar "ss") (.SVar "tm")
  ++ [ .RArrStore bufArr "idx" ⟨"oo", .TU64⟩ ]

/-- Phase trip at half `h ∈ {8,4,2}`:
    `buf[idx] := foldβ(buf[idx], buf[idx+h], buf[16])`. -/
def hpFoldBody (h : Nat) : LowCT := sqAll <|
  [ setE "ih"  (.SAdd (.SVar "idx") (.SLit h)),
    setE "z16" (.SLit 16),
    .RArrLoad ⟨"aa", .TU64⟩ bufArr "idx",
    .RArrLoad ⟨"bb", .TU64⟩ bufArr "ih",
    .RArrLoad ⟨"bt", .TU64⟩ bufArr "z16" ]
  ++ addL "ss" (.SVar "aa") (.SVar "bb")
  ++ subL "dd" (.SVar "aa") (.SVar "bb")
  ++ mulL "tm" (.SVar "dd") (.SVar "bt")
  ++ addL "oo" (.SVar "ss") (.SVar "tm")
  ++ [ .RArrStore bufArr "idx" ⟨"oo", .TU64⟩ ]

/-- Phase-1 body context: accumulator `buf`, index `idx`, invariant `lde`. -/
def hp1Γ : Ctx := [.memref 17, .sword 64, .memref 96]

/-- Phase-1 VarMap. -/
def hp1Vm : VarMap hp1Γ :=
  (((VarMap.empty.bind (t := .memref 96) "lde").bind
      (t := .sword 64) "idx").bind (t := .memref 17) "buf")

/-- Halving-phase body context: accumulator `buf`, index `idx`. -/
def hpHΓ : Ctx := [.memref 17, .sword 64]

/-- Halving-phase VarMap. -/
def hpHVm : VarMap hpHΓ :=
  ((VarMap.empty.bind (t := .sword 64) "idx").bind (t := .memref 17) "buf")

/-- The chain's outer context, newest-first:
    `[cnt2, cnt4, cnt8, cnt16, lde, buf]` — ABI
    `hp_fri_fold_chain(buf, lde, n16, n8, n4, n2)` =
    `(RDI, RSI, RDX, RCX, R8, R9)`. -/
abbrev ΓH : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .reg 64, .reg 64, .stackArr 64 96, .stackArr 64 17]

/-- The jasmin image of the fold accumulator. -/
abbrev bufT : JasminTy := mapTy (CryptoTy.memref 17)

/-- Generic halving phase over any outer context. -/
def phaseHalve (h : Nat) {Γ : Ctxt jasminDialect}
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ bufT)
    {s : JasminTy} (cont : ComL (bufT :: Γ) s) : Option (ComL Γ s) :=
  rolledForLoopNRtCont (Γouter := Γ) (accCTy := .memref 17)
    (invCTys := []) hpHVm "buf" (hpFoldBody h) count init .nil cont

/-- The whole `hp_prove` §4 fold chain: phase 1 (`32→16` off the LDE) then the
    in-place halvings `16→8→4→2`, ONE `ComL` spine.  Counts are runtime
    registers; the KAT driver passes `(16, 8, 4, 2)`. -/
def hpFoldChainComL : Option (ComL ΓH bufT) := do
  let p4 ← phaseHalve 2
    (Γ := bufT :: bufT :: bufT :: ΓH)
    (count := .there (.there (.there .here)))
    (init := .here)
    (cont := .ret .here)
  let p3 ← phaseHalve 4
    (Γ := bufT :: bufT :: ΓH)
    (count := .there (.there (.there .here)))
    (init := .here)
    (cont := p4)
  let p2 ← phaseHalve 8
    (Γ := bufT :: ΓH)
    (count := .there (.there (.there .here)))
    (init := .here)
    (cont := p3)
  rolledForLoopNRtCont (Γouter := ΓH) (accCTy := .memref 17)
    (invCTys := [.memref 96]) hp1Vm "buf" hpFold1Body
    (count := .there (.there (.there .here)))
    (init := .there (.there (.there (.there (.there .here)))))
    (invs := .cons (.there (.there (.there (.there .here)))) .nil)
    (cont := p2)

/-- **The 4-phase `hp_prove` fold chain front-compiles.** -/
theorem hpFoldChainComL_isSome : hpFoldChainComL.isSome := by native_decide

/-! ## 3. denote = the pin's fold values on the pin's KAT trace -/

/-- KAT LDE row (96 words). -/
def ldeSeed : Fin 96 → BitVec 64 := fun i =>
  BitVec.ofNat 64 (ldeKAT[i.val]!.toNat)

/-- KAT accumulator seed: fold slots zero, `buf[16] = beta`. -/
def bufSeed : Fin 17 → BitVec 64 := fun i =>
  if i.val == 16 then BitVec.ofNat 64 betaKAT.toNat else 0

/-- Outer valuation at counts `(n16, n8, n4, n2)`. -/
def hpVal (n16 n8 n4 n2 : Nat) : Ctxt.Valuation ΓH :=
  .cons (BitVec.ofNat 64 n2) (.cons (BitVec.ofNat 64 n4)
    (.cons (BitVec.ofNat 64 n8) (.cons (BitVec.ofNat 64 n16)
      (.cons ldeSeed (.cons bufSeed .nil)))))

/-- Selected denoted slots of the chain result. -/
def hpDenoteSlots (n16 n8 n4 n2 : Nat) (idxs : List Nat) : Option (List Nat) :=
  hpFoldChainComL.map (fun c =>
    idxs.map (fun i =>
      (ComL.denote c (hpVal n16 n8 n4 n2)
        ⟨i % 17, Nat.mod_lt _ (by decide)⟩).toNat))

/-- **denote = the pin's `out[16..17]`** (the final degree-1 polynomial) at the
    full KAT counts. -/
theorem hpFoldChain_denote_full :
    hpDenoteSlots 16 8 4 2 [0, 1]
      = some (specSlots (hpFoldSpec ldeKAT betaKAT 4) [0, 1]) := by
  native_decide

/-- **denote = the pin's `f16` row** at counts `(16, 0, 0, 0)` (later phases run
    zero trips — SAME program, count-driven). -/
theorem hpFoldChain_denote_f16 :
    hpDenoteSlots 16 0 0 0 (List.range 16)
      = some (specSlots (hpFoldSpec ldeKAT betaKAT 1) (List.range 16)) := by
  native_decide

/-- **denote = the seed at all-zero counts** (identity — the counts
    drive the phases; slot 16 still carries `beta`). -/
theorem hpFoldChain_denote_zero :
    hpDenoteSlots 0 0 0 0 (List.range 17)
      = some ((List.range 17).map (fun i =>
          (bufSeed ⟨i % 17, Nat.mod_lt _ (by decide)⟩).toNat)) := by
  native_decide

/-! ## 4. The PoW grind, front-compiled (data-dependent while + leaf call)

`hp_prove` §6: `h0 = 1; while (h0 != 0) { fs[8] = nonce; h0 = perm(fs)[0] & 255;
if (h0 != 0) nonce += 1 }`.  The body is front-compiled covered LowCT — the
permutation is a leaf `RCall` (→ real linked `Lcall`), the mask a covered `SAnd`,
the conditional increment branch-free (`(h0 + 255) >> 8` is `1` iff `h0 ≠ 0` for
`h0 < 256`) — wrapped in the guard-driven `whileLinstrRM` (`TranslateDialectDataWhile`).

The in-model denote runs against a SMALL surrogate leaf (`h0r = nonce ^ 5`,
halting at nonce `5`); the REAL Poseidon2 grind semantics is pinned purely in
§1.1 (`findNonce = 99`, the machine-validated word 19).  The real-leaf in-model
run is gap 2 of the module header. -/

/-- Grind body: `h0r := pow(nonce); h0 := h0r & 255; nonce2 := nonce + ((h0+255)>>8)`. -/
def grindBody : LowCT := sqAll [
  .RCall "p3_pow_h0" ⟨"h0r", .TU64⟩ [⟨"nonce", .TU64⟩],
  setE "h0" (.SAnd (.SVar "h0r") (.SLit 255)),
  setE "i1" (.SAdd (.SVar "h0") (.SLit 255)),
  setE "i2" (.SShr (.SVar "i1") (.SLit 8)),
  setE "nonce2" (.SAdd (.SVar "nonce") (.SVar "i2")) ]

/-- Grind body context: accumulator `nonce`, invariant `seed` (unused scalar,
    keeps the shape binary). -/
def grindΓ : Ctx := [.sword 64, .sword 64]

/-- Grind VarMap: `nonce ↦ acc`, `seed ↦ invariant`. -/
def grindVm : VarMap grindΓ :=
  ((VarMap.empty.bind (t := .sword 64) "seed").bind (t := .sword 64) "nonce")

/-- The front-compiled grind body `Com` (or `none`). -/
def grindFrontJ :
    Option (Com jasminDialect (mapCtx grindΓ) (mapTy (.sword 64))) :=
  frontLoopBodyJ (accCTy := .sword 64) grindVm "nonce2" grindBody

/-- **The grind body front-compiles** (leaf `RCall` + branch-free increment). -/
theorem grindFrontJ_isSome : grindFrontJ.isSome := by native_decide

/-- The surrogate PoW leaf for the in-model run: `dst := nonce ^ 5`. -/
def grindLeafGen : LeafGen := fun sym dst args =>
  if sym = "p3_pow_h0" then
    match args with
    | [a] => some [(LinstrR.Lopn [.reg dst] "XOR:64" [a, .imm 5], MemTag.reg none)]
    | _ => none
  else none

/-- The front-lowered grind body instructions (`straightOpsMemCall` image). -/
def grindFrontBody : List LinstrRM :=
  (grindFrontJ.map (fun c => straightOpsMemCall 2 grindLeafGen c 2)).getD []

/-- The grind `LeafEnvM` (surrogate `p3_pow_h0`). -/
def grindEnv : LeafEnvM :=
  envOfBindings ((grindFrontJ.map (fun c => leafBindings 2 grindLeafGen c 2)).getD [])

/-- Body tail: persist the fresh nonce (SSA `r13`, the `nonce2` landing slot)
    into `a1`, and the masked `h0` (SSA `r5`) into the guard register `g`. -/
def grindExtra : List LinstrRM :=
  [ (LinstrR.Lopn [.reg "a1"] "ADD:64" [.reg "r13", .imm 0], MemTag.reg none),
    (LinstrR.Lopn [.reg "g"]  "ADD:64" [.reg "r5", .imm 0], MemTag.reg none) ]

/-- The full grind loop body. -/
def grindLoopBody : List LinstrRM := grindFrontBody ++ grindExtra

/-- The guard-driven grind program: `whileLinstrRM 0 "g" [] body` — the body
    leaves the freshly-masked `h0` in `g`, the `Lcond` re-tests it each pass. -/
def grindProg : LprogM := singletonProgM "f" (whileLinstrRM 0 "g" [] grindLoopBody)

/-- Start: `nonce = 0` in `a1`, `seed = 0` in `a0`. -/
def grindStart : LstatePMC :=
  { base := ((({} : LstateM).setReg "a0" (0#64)).setReg "a1" (0#64))
    lfn := "f"
    rstack := [] }

/-- **The emitted grind carries a REAL `Lcond` back-edge and a REAL linked
    `Lcall`** (no `CALL:` shadow) — the `hp_prove` grind shape, front-compiled. -/
theorem grind_realBackEdge_realCall :
    hasBackEdge grindProg.body = true
      ∧ hasRealCall grindLoopBody = true
      ∧ hasCallShadow grindLoopBody = false := by native_decide

/-- **denote = the surrogate grind fold**: the interpreter follows the
    guard-driven back-edge until `h0 = (nonce ^ 5) & 255 = 0` and the nonce
    decodes to `5` — the searched value. -/
theorem grind_denote_nonce5 :
    (lsemFuelMemLC grindEnv grindProg 400 grindStart).map
        (fun t => decodeM t.base "a1" 64) = some (some (5#64)) := by native_decide

/-- **The interpreter run equals the `runWhileMem` do-while denotation** (guard
    `g ≠ 0` recomputed each pass, data-dependent trip). -/
theorem grind_denote_eq_runWhileMem :
    (lsemFuelMemLC grindEnv grindProg 400 grindStart).map
        (fun t => decodeM t.base "a1" 64)
      = (runWhileMem grindEnv (fun b => condNZ b (.reg "g")) grindLoopBody 20
          grindStart.base).map (fun b => decodeM b "a1" 64) := by native_decide

/-- **The data-dependent trip is read off the run** (`6` = nonces `0..5`). -/
theorem grind_trips :
    whileTripsMem grindEnv (fun b => condNZ b (.reg "g")) grindLoopBody 20
        grindStart.base = 6 := by native_decide

/-! ## 5. Render the front-compiled fold chain to owned `.s` -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.FheMontMulEmit
  (fuseMulHiLprog)

/-- The fold chain rendered: `hp_fri_fold_chain(buf, lde, n16, n8, n4, n2)`.
    `fuseMulHiLprog` coalesces each Barrett discarded-low `MUL` + `MULXHI`
    pair into the printer's real two-output `mulx` (see
    `Plonky3FriProofFrontEmit.mulL`). -/
def hpFoldChainAsm : Option String :=
  hpFoldChainComL.map (fun c =>
    CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (fuseMulHiLprog
      (ComL.toLprogPhysAbi c "hp_fri_fold_chain" (argName 0) [argName 1]
        (fun _ => none) (fun _ => none)
        ["RDI", "RSI", "RDX", "RCX", "R8", "R9"] [64, 64, 64, 64, 64, 64])
      (saveRdx := true)))

-- Rendered-asm correctness is the external C KAT; an in-Lean strContains check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 6. Emit driver

The fragment is a front-reachable piece of the `hp_prove` spine only — the
whole-artifact re-emit (and the whitelist flip of `plonky3_honest_prove.s`) is
gated on the callee-leaf emits + the interpreter-scale/asm-KAT gates (module
header). -/

/-- Write `bench/plonky3_compare/gen_com/honest_prove_frontphases.s`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/plonky3_compare/gen_com"
  let path := "bench/plonky3_compare/gen_com/honest_prove_frontphases.s"
  IO.FS.writeFile path ((hpFoldChainAsm.getD "") ++ "\n")
  IO.println s!"wrote {path} (front-compiled hp_prove fold-chain phase; no jasminc, no hand Com/Lcmd)"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HonestProveFrontEmit
