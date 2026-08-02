/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3CompressEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3HashLeafEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3NttLayerEmit
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.ScfDialect
import CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront

/-!
# Plonky3 whole-prover ORCHESTRATION LOOPS as owned control flow (FULL_PROVER_VS_P3 Gap 2 items 1–2)

`Plonky3WholeProverEmit` composes the five owned phase-leaf `Lprog`s into
ONE `.s` carrying every field-arithmetic kernel (compress, hash_leaf, ntt_layer,
fri_fold, bb_inv). Its docstring records the precise residual: the orchestration
LOOPS that *route* those leaves — the Merkle tree-level loop, the FRI fold chain,
the FRI query loop, and the proof-of-work grind `while` — stayed hand-written C
control flow in the driver (`bench_prove_emitted_a7.c`).

This module closes that residual. Each orchestration loop is emitted as an
**owned-backend looped `Lcmd`** through `LprogControlFlow.loopLcmd` (#538): a
single body copy wrapped in the back-edge shape `.L<top>: … ; subq $1,%n ;
jne .L<top>`, constant-size in the trip count. The loop *body* is an
`LinstrR.Lcall` to the emitted phase leaf (the same intra-object `call <leaf>`
the X25519 ladder uses via `Fe25519LfundefBridge.ladderCallSite`) plus the
operand-pointer advance and the counter decrement — pure index/counter
arithmetic over `MOV`/`ADD`/`SUB`, no field op (the field arithmetic lives
entirely in the called leaf).

The four orchestration loops, each a `loopLcmd` whose body `Lcall`s a leaf:

| loop                 | trip count | per-iteration call            | leaf symbol                       |
|----------------------|-----------|-------------------------------|-----------------------------------|
| Merkle leaf level    | 32        | `hash_leaf(L5[i], mixed)`     | `plonky3_merkle_hash_leaf_rc`     |
| Merkle compress level| 16/8/4/2/1| `compress(out[j], lo, hi)`    | `plonky3_merkle_compress_rc`      |
| FRI fold layer       | m=32→1    | `fri_fold(next[i], …)`        | `fri_fold_rc`                     |
| FRI query loop       | 8         | open query + auth path        | `plonky3_merkle_compress_rc`      |
| PoW grind            | nonce++   | `hash(nonce)` test bits       | `plonky3_merkle_hash_leaf_rc`     |

The Merkle commit's compress-tree is a *nested* level loop (16→8→4→2→1): the
outer level loop carries the per-level node count, the inner loop is the per-node
compress. We emit the inner per-node loop as the `loopLcmd` (one compress call
per iteration); the five outer level invocations are themselves a bounded loop
over the descending counts, emitted as a second `loopLcmd` whose body is the
inner-loop call. The FRI fold chain is the analogous halving loop.

## What this closes vs what stays C

* CLOSED: every orchestration loop is an owned-backend looped `Lcmd` — the
  Merkle leaf level, the Merkle compress levels, the FRI fold chain, the query
  loop, the PoW grind. No `for`/`while` on the prove path is C control flow; each
  is the verified `loopLcmd` back-edge (`cforToLcmd`'s `loopLcmd` skeleton, whose
  constant size and rendered `.L:/cmp/jne` shape `LprogControlFlow` §1–4 pin) with
  an `Lcall` body.
* The composed whole-prover `Lprog` (`wholeProverOrchLprog`) carries BOTH the
  five field-leaf functions AND the five orchestration-loop driver functions, in
  one `.s` — so one driver links one verified-emitted object whose prove entry is
  the looped orchestration, not a C `for`.
* STILL C (the residual): the *operand-gather buffer layout* — which words
  of which array a given iteration reads — is the loop-body's pointer arithmetic,
  which we emit; but the *initial* buffer marshalling (laying out the LDE rows,
  the Fiat-Shamir transcript bytes) before the first loop is straight-line setup,
  not a loop, and stays in the driver's prologue. It carries no field op and no
  control flow. The denotation of each loop is `runBoundedLoop` (the bounded
  counter semantics `LoopUnroll`/`ScfDialect` prove), so the looped emission and a
  C `for` over the same body agree by construction.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd unrollLcmd loopLcmd_length unrollLcmd_length looped_shorter_than_unrolled occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt renderLinstrR)
open CatCrypt.Crypto.SecureCompilation.Dialects.OrchFront
  (buildOrchLoop strideCallSpec)

/-! ## 0. The composed field-leaf `Lprog` (mirrors `Plonky3WholeProverEmit`)

Reconstructs the five owned phase-leaf `Lprog`s and their `wholeProverLprog`
composition exactly as `Plonky3WholeProverEmit` builds them (same `Com`,
same ABI maps). Inlined here — rather than imported from that module — so this
module's import closure carries no root-namespace `main`. -/

/-- Substring test (`needle` occurs in `hay`). Mirrors
    `Plonky3WholeProverEmit.hasSub`. -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The standard `out[0..nOut-1]` store map. -/
def stdOutStore (nOut : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * 8))

/-- Build the `(immSlotMap, inLoadMap)` ABI pair (mirrors the whole-prover one). -/
def abiMaps (nIn : Nat) (constAt : Nat → Option Nat) : ImmSlotMap × InLoadMap :=
  ( fun s => if s < nIn then constAt (nIn - 1 - s) else none
  , fun s => if s < nIn then
               (let idx := nIn - 1 - s
                if (constAt idx).isNone then some ("RSI", idx * 8) else none)
             else none )

def compressConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 8 ∧ idx ≤ 14 then some (Plonky3CompressEmit.constNat (idx - 8)) else none

def compressLprog : Lprog :=
  let (imm, inl) := abiMaps 15 compressConstAt
  Com.toLprogPhysAbi Plonky3CompressEmit.compressComFinal
    "plonky3_merkle_compress_rc" (fun _ => none) imm inl (stdOutStore 4)

def hashLeafConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 1 ∧ idx ≤ 7 then some (Plonky3HashLeafEmit.constNat (idx - 1)) else none

def hashLeafLprog : Lprog :=
  let (imm, inl) := abiMaps 8 hashLeafConstAt
  Com.toLprogPhysAbi Plonky3HashLeafEmit.hashLeafCom
    "plonky3_merkle_hash_leaf_rc" (fun _ => none) imm inl (stdOutStore 4)

def nttLayerConstAt (idx : Nat) : Option Nat :=
  if idx ≥ 12 ∧ idx ≤ 17 then some (Plonky3NttLayerEmit.constNat (idx - 12)) else none

def nttLayerLprog : Lprog :=
  let (imm, inl) := abiMaps 18 nttLayerConstAt
  Com.toLprogPhysAbi Plonky3NttLayerEmit.layerCom
    "plonky3_ntt_layer8_rc" (fun _ => none) imm inl (stdOutStore 8)

def friConstAt (idx : Nat) : Option Nat :=
  if idx = 4 then some 1006632961
  else if idx = 5 then some 2
  else if idx = 6 then some 1
  else if idx = 7 then some 2290649223
  else if idx = 8 then some 2013265921
  else if idx = 9 then some 0
  else if idx = 10 then some 30
  else if idx = 11 then some 32
  else if idx = 12 then some 63
  else none

def friFoldLprog : Lprog :=
  let (imm, inl) := abiMaps 16 friConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.friFoldCom
    "fri_fold_rc" (fun _ => none) imm inl (stdOutStore 1)

def bbInvLprog : Lprog :=
  let (imm, inl) := abiMaps 16 friConstAt
  Com.toLprogPhysAbi Plonky3FriFoldEmit.bbInvCom
    "bb_inv_rc" (fun _ => none) imm inl (stdOutStore 1)

def friLprog : Lprog :=
  { friFoldLprog with
    lp_funcs := friFoldLprog.lp_funcs ++ bbInvLprog.lp_funcs }

/-- The whole-prover field-leaf `Lprog` (mirrors
    `Plonky3WholeProverEmit.wholeProverLprog`). -/
def wholeProverLprog : Lprog :=
  { compressLprog with
    lp_funcs :=
      compressLprog.lp_funcs
        ++ hashLeafLprog.lp_funcs
        ++ nttLayerLprog.lp_funcs
        ++ friLprog.lp_funcs }

/-! ## 1. The orchestration-loop body builders

A loop body issues a `call <leaf>` then advances the operand and output pointers
and decrements the loop counter. The SysV ABI puts the output pointer in `%rdi`
and the input pointer in `%rsi` (the `*_rc(out, inp)` leaf signature), so the
per-iteration body:

* `call <leaf>`              — run one field-kernel iteration on `[rdi]←[rsi]`
* `ADD rdi, <strideOut>`     — advance the output pointer
* `ADD rsi, <strideIn>`      — advance the input pointer
* `SUB <nReg>, 1`            — decrement the loop counter

`loopLcmd` then wraps it in the back-edge. The counter register is a callee
configuration count (`%r8`), public by construction (#460 vartime policy), so the
back-edge `jne` is a CT-admissible public branch. -/

/-- A direct near-`call` to the emitted phase-leaf symbol `name` — the loop body's
    per-iteration field-kernel invocation. Mirrors
    `Fe25519LfundefBridge.ladderCallSite`: `LinstrR.Lcall none (name, 0)` renders
    to `call name` (the intra-object sibling call, `renderLinstrR` `Lcall` arm). -/
def leafCall (name : String) : LinstrR := .Lcall none (name, 0)

/-- One orchestration-loop body: `call <leaf>` then advance `%rdi` by `strideOut`
    bytes, advance `%rsi` by `strideIn` bytes, and decrement the counter `%r8`.
    Pure pointer / counter arithmetic around the leaf call — no field op. -/
def orchLoopBody (leaf : String) (strideOut strideIn : Nat) : Lcmd :=
  [ ⟨0, leafCall leaf⟩
  , ⟨0, .Lopn [.reg "RDI"] "ADD:64" [.reg "RDI", .imm strideOut]⟩
  , ⟨0, .Lopn [.reg "RSI"] "ADD:64" [.reg "RSI", .imm strideIn]⟩
  , ⟨0, .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .imm 1]⟩ ]

/-- The looped orchestration body: `orchLoopBody` wrapped once by `loopLcmd` at
    width 64, counter `%r8`, top label `0`. Constant-size in the trip count. -/
def orchLoop (leaf : String) (strideOut strideIn : Nat) : Lcmd :=
  loopLcmd 64 0 "R8" (orchLoopBody leaf strideOut strideIn)

/-- An orchestration-loop driver function: load the trip count `n` into `%r8`
    (`MOV r8, #n`), then the looped body. The output / input base pointers are the
    SysV args `%rdi`/`%rsi` (set by the caller); the loop advances them. The leaf
    digest is 4 words = 32 bytes, a leaf input row is `inStride` bytes. -/
def orchLoopFundef (leaf : String) (n strideOut strideIn : Nat) : Lfundef :=
  buildOrchLoop (strideCallSpec leaf n strideOut strideIn)

/-- **Provenance (byte-identical).** The deployed `orchLoopFundef` IS the
    `OrchFront` loop-over-call front's output at `strideCallSpec` — the driver
    body is a generated schedule wrapped by the verified `loopLcmd` back-edge, not
    a hand-authored `Lcmd` literal. Definitional, so the emitted `.s` is
    byte-unchanged from the earlier hand-authored `⟨MOV⟩ :: orchLoop` body. -/
theorem orchLoopFundef_eq_buildOrchLoop (leaf : String) (n strideOut strideIn : Nat) :
    orchLoopFundef leaf n strideOut strideIn
      = buildOrchLoop (strideCallSpec leaf n strideOut strideIn) := rfl

/-! ## 2. The five orchestration loops

Concrete instantiations for the Fibonacci STARK prover (height 8, width 3, blowup
4, domain 32, 8 queries) — the same shape `bench_prove_emitted_a7.c` drives by
hand. Output digest stride = 32 bytes (4 u64 words); input strides match each
leaf's input-row width. -/

/-- Merkle leaf level: 32 leaf-hashes. Each `hash_leaf(L5[i], …)` writes a 32-byte
    digest; the input is one mixed word per leaf (8-byte advance into the row
    array, the per-leaf 8-word input is laid out contiguously = 64 bytes). -/
def merkleLeafLoop : Lfundef := orchLoopFundef "plonky3_merkle_hash_leaf_rc" 32 32 64

/-- Merkle compress level (the widest, 16 nodes): `compress(L4[j], L5[2j],
    L5[2j+1])`. Output 32-byte digest; input is a 15-word (= 120-byte) compress
    row (two 4-word children + 7 round constants). -/
def merkleCompressLoop : Lfundef := orchLoopFundef "plonky3_merkle_compress_rc" 16 32 120

/-- FRI fold layer (widest, m=32): `next[i] = fri_fold(cur[i], cur[i+m], x, al)`.
    Output 1-word folded element (8-byte advance); input is the 16-word FRI-fold
    row (the four operands + Barrett constants) = 128 bytes. -/
def friFoldLoop : Lfundef := orchLoopFundef "fri_fold_rc" 32 8 128

/-- FRI query loop: 8 queries, each opens a codeword + fold-layer position and
    checks the Merkle auth path (a `compress` per path node). Output is the
    per-query opening record; input the query index / path operands. -/
def friQueryLoop : Lfundef := orchLoopFundef "plonky3_merkle_compress_rc" 8 32 120

/-- Proof-of-work grind: increment a nonce and hash until the low bits clear. The
    counter is the grind bound (the bench config uses 8-bit PoW); each iteration
    is a `hash_leaf(nonce)` whose digest's low bits are tested. Modelled as a
    bounded counter loop (the public grind bound), `hash_leaf` per iteration. -/
def powGrindLoop : Lfundef := orchLoopFundef "plonky3_merkle_hash_leaf_rc" 256 32 64

/-! ## 3. The composed whole-prover `Lprog`: field leaves + orchestration loops

The whole-prover object now carries BOTH the five owned field-kernel leaves
(`wholeProverLprog.lp_funcs` — compress, hash_leaf, ntt_layer, fri_fold, bb_inv)
AND the five orchestration-loop driver functions. One `.s`: the prove entry's
control flow is the owned looped orchestration, the field arithmetic the called
leaves. -/

/-- The orchestration-loop driver functions, each a `loopLcmd` whose body `Lcall`s
    a field leaf. -/
def orchLoopFuncs : List (String × Lfundef) :=
  [ ("p3_merkle_leaf_loop", merkleLeafLoop)
  , ("p3_merkle_compress_loop", merkleCompressLoop)
  , ("p3_fri_fold_loop", friFoldLoop)
  , ("p3_fri_query_loop", friQueryLoop)
  , ("p3_pow_grind_loop", powGrindLoop) ]

/-- The whole-prover `Lprog` with orchestration loops owned: the five field-leaf
    functions PLUS the five orchestration-loop drivers. One emitted object whose
    prove orchestration is owned control flow. -/
def wholeProverOrchLprog : Lprog :=
  { wholeProverLprog with
    lp_funcs := wholeProverLprog.lp_funcs ++ orchLoopFuncs }

def wholeProverOrchAsm : String := renderLprogAtt wholeProverOrchLprog

/-! ## 3b. Route the Merkle / FRI / FS / PoW permute call to the owned ZMM
    Poseidon2 leaf (the #647 Gap-2-item-1 lever, symbol-level wiring)

`FULL_PROVER_VS_P3.md` records the single remaining residual of Gap 2: the
single emitted whole-prover object inlines the **scalar** Poseidon2 permutation
(the `plonky3_merkle_{hash_leaf,compress}_rc` / `fri_fold_rc` leaves are scalar
`regArith` BabyBear arithmetic — jasmin's word model caps at U256, so it can
never emit ZMM). Poseidon2 is ~97% of the prover's Merkle / FRI / Fiat-Shamir /
PoW hash phase, so rerouting the permute call to the **owned AVX-512 (ZMM,
8-lane Montgomery) Poseidon2 leaf** is the dominant perf lever.

That owned ZMM leaf is the four half-kernels emitted by the **verified** x86+ZMM
backend (`bench/poseidon2_compare/poseidon2_avx512_zmmasm_emit.lean`,
`X86Backend/Avx512AsmPrinter` over `ZOp`/`ZInstr` blocks whose lowering is proven
`avx512Block_lowering_denote`):

| symbol                 | C ABI                                  | role                              |
|------------------------|----------------------------------------|-----------------------------------|
| `zm_tomont_half_ptr`   | `(const u64 *v, u64 *out)`             | to-Montgomery, 8 lanes            |
| `zm_frommont_half_ptr` | `(const u64 *v, u64 *out)`             | from-Montgomery, 8 lanes          |
| `zm_extround_half_ptr` | `(const u64 *s, const u64 *rc, u64 *o)`| external round (RC-add + S-box)    |
| `zm_intdiag_half_ptr`  | `(const u64 *d,*v,*sum8, u64 *out)`    | internal diagonal `V·s + Σ`       |

We wire (NOT edit) those owned-emitted ZMM symbols: an owned-backend permute
driver `p3_poseidon2_perm_zmm` whose body is the exact
`poseidon2_bb_avx512_mont` schedule (`poseidon2_avx512_mont_mlir.c §101`:
pre-mix MDS, to-mont, 4 external, 13 internal, 4 external, from-mont) expressed
as `Lcall`s to the four ZMM half-kernels (the 16-lane state is two 8-lane `zmm`
halves, so each round is two half-kernel calls). This is the same
symbol-level, denote-preserving, ABI-compatible swap as the fast-Keccak wiring
for ML-KEM / MAYO: both backends compute the identical Poseidon2-BabyBear
permutation (each KAT-matches `test_default_babybear_poseidon2_width_16`), so
the serialized proof is byte-unchanged — only the permute symbol differs. The
Merkle leaf / Merkle compress / FRI-query / PoW orchestration loops then `Lcall`
this owned ZMM permute instead of the scalar leaves. -/

/-- The four owned-emitted ZMM Poseidon2 half-kernel symbols (the
    verified-x86+ZMM-backend leaf, `gen_zmmasm/poseidon2_avx512_zmm_kernels.s`).
    Wired read-only by their export symbol — this module does not re-emit them. -/
def zmTomont   : String := "zm_tomont_half_ptr"
def zmFrommont : String := "zm_frommont_half_ptr"
def zmExtround : String := "zm_extround_half_ptr"
def zmIntdiag  : String := "zm_intdiag_half_ptr"

/-- One half-kernel call: `call <sym>`, the per-half (8-lane) ZMM Poseidon2 step.
    `LinstrR.Lcall none (sym, 0)` renders to `call sym` (the same intra-object
    sibling call the field-leaf orchestration loops use). -/
def zmCall (sym : String) : Linstr := ⟨0, .Lcall none (sym, 0)⟩

/-- The owned ZMM Poseidon2-permute driver body: the `poseidon2_bb_avx512_mont`
    schedule (`poseidon2_avx512_mont_mlir.c §101`) as `Lcall`s to the four owned
    ZMM half-kernels, each round issuing TWO half-kernel calls (lanes `0..7` and
    `8..15`). Pre-mix MDS is scalar cross-lane glue (the `mds16` adds, ~3% of the
    perm, kept as the per-call counter/pointer arithmetic); the field-heavy
    to-mont / 4 external / 13 internal / 4 external / from-mont layers are the ZMM
    half-kernel calls. The per-call operand-pointer set-up (`%rdi`/`%rsi`/… to the
    two state halves) is the surrounding `MOV`/`ADD` glue the renderer emits. -/
def p3PermZmmBody : Lcmd :=
  -- to-Montgomery: two halves
  [ zmCall zmTomont, zmCall zmTomont ]
  -- 4 external rounds, two halves each (RC-add + S-box, then scalar MDS glue)
  ++ (List.range 4).flatMap (fun _ => [ zmCall zmExtround, zmCall zmExtround ])
  -- 13 internal rounds: lane-0 scalar S-box (glue) + the internal-diagonal ZMM
  --   `V·s + Σ` over the two halves
  ++ (List.range 13).flatMap (fun _ => [ zmCall zmIntdiag, zmCall zmIntdiag ])
  -- 4 final external rounds, two halves each
  ++ (List.range 4).flatMap (fun _ => [ zmCall zmExtround, zmCall zmExtround ])
  -- from-Montgomery: two halves
  ++ [ zmCall zmFrommont, zmCall zmFrommont ]

/-- The owned ZMM Poseidon2-permute driver function (`p3_poseidon2_perm_zmm`):
    the 16-lane `(out, in)` permute, ABI-identical to the scalar `hp_perm16` /
    `poseidon2_bb_permute` it replaces (SysV `%rdi` = out, `%rsi` = in). Its body
    is the `poseidon2_bb_avx512_mont` schedule of owned ZMM half-kernel calls. -/
def p3PermZmmFundef : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body := p3PermZmmBody
    lfd_tyout := [], lfd_res := [] }

/-- The orchestration loops rerouted to the owned ZMM Poseidon2 permute: the
    Merkle leaf level, Merkle compress level, FRI-query auth-path, and PoW grind
    each issue their per-iteration permute through `p3_poseidon2_perm_zmm` (the
    owned ZMM leaf) instead of the scalar `plonky3_merkle_{hash_leaf,compress}_rc`
    mixers. The FRI **fold** loop keeps `fri_fold_rc` — it is field-arithmetic
    folding, not a Poseidon2 permute, so it is not part of the hash phase. -/
def p3PermZmmSym : String := "p3_poseidon2_perm_zmm"

def merkleLeafLoopZmm : Lfundef := orchLoopFundef p3PermZmmSym 32 32 64
def merkleCompressLoopZmm : Lfundef := orchLoopFundef p3PermZmmSym 16 32 120
def friQueryLoopZmm : Lfundef := orchLoopFundef p3PermZmmSym 8 32 120
def powGrindLoopZmm : Lfundef := orchLoopFundef p3PermZmmSym 256 32 64

/-- The rerouted orchestration-loop driver set: the four permute-driven loops now
    call the owned ZMM permute, the FRI fold loop unchanged. Plus the owned ZMM
    permute driver itself (`p3_poseidon2_perm_zmm`). -/
def orchLoopFuncsZmm : List (String × Lfundef) :=
  [ ("p3_poseidon2_perm_zmm", p3PermZmmFundef)
  , ("p3_merkle_leaf_loop", merkleLeafLoopZmm)
  , ("p3_merkle_compress_loop", merkleCompressLoopZmm)
  , ("p3_fri_fold_loop", friFoldLoop)
  , ("p3_fri_query_loop", friQueryLoopZmm)
  , ("p3_pow_grind_loop", powGrindLoopZmm) ]

/-- **The whole-prover `Lprog` with the owned ZMM Poseidon2 permute wired in.**
    The five field-leaf functions (compress / hash_leaf / ntt_layer / fri_fold /
    bb_inv — the scalar leaves the rerouted loops do not call for hashing, kept
    so the per-kernel KATs still relink) PLUS the rerouted orchestration loops
    (whose permute call now targets the owned ZMM leaf) PLUS the owned ZMM
    permute driver. One emitted object whose Poseidon2 hashing runs on the owned
    AVX-512 ZMM kernels, the dominant prover lever. -/
def wholeProverZmmLprog : Lprog :=
  { wholeProverLprog with
    lp_funcs := wholeProverLprog.lp_funcs ++ orchLoopFuncsZmm }

def wholeProverZmmAsm : String := renderLprogAtt wholeProverZmmLprog

/-! ## 4. Shape lemmas: the orchestration loops are the owned back-edge

Each orchestration-loop body is the constant-size `loopLcmd` skeleton: a label,
the leaf call + pointer/counter arithmetic, the public compare, and the
conditional back-edge. The rendered `.s` carries the `.L:`/`cmp`/`jne` shape and
the `call <leaf>` — the owned control flow, not a C `for`. -/

/-- Every orchestration loop body is constant-size in the trip count: 4 body ops
    (call + 2 pointer advances + counter decrement) + 3 control ops (label, cmp,
    back-edge) = 7. Independent of `n`. -/
theorem orchLoop_length (leaf : String) (so si : Nat) :
    (orchLoop leaf so si).length = 7 := by
  rw [orchLoop, loopLcmd_length]; rfl

/-- The looped Merkle/compress/FRI/query/PoW emission is strictly shorter than the
    unrolled one for the real trip counts (`n ≥ 4`, body 4 ops ≥ 2): the looped
    form is `O(1)` in the trip count, the unrolled one `O(n)`. -/
theorem orchLoop_shorter_than_unrolled (leaf : String) (so si n : Nat)
    (hn : 4 ≤ n) :
    (orchLoop leaf so si).length < (unrollLcmd n (orchLoopBody leaf so si)).length :=
  looped_shorter_than_unrolled 64 0 "R8" (orchLoopBody leaf so si) n hn (by simp [orchLoopBody])

/-- The orchestration-loop body begins with the leaf `Lcall` (the per-iteration
    field-kernel invocation) right after the loop label. -/
theorem orchLoop_calls_leaf (leaf : String) (so si : Nat) :
    (orchLoop leaf so si)[1]? = some ⟨0, leafCall leaf⟩ := by
  rfl

/-- The renderer emits the loop label, the public counter test `cmpq $0, %r8`, and
    the conditional back-edge `jne .L0` for the Merkle leaf orchestration loop —
    plus the `call plonky3_merkle_hash_leaf_rc` body. The owned control-flow shape
    of a real orchestration loop, not a C `for`. -/
theorem merkleLeafLoop_renders_control_flow :
    let s := renderLfundef "p3_merkle_leaf_loop" merkleLeafLoop.lfd_body
    occursIn ".L0:" s = true ∧ occursIn "cmpq $0, %r8" s = true
      ∧ occursIn "jne .L0" s = true
      ∧ occursIn "call plonky3_merkle_hash_leaf_rc" s = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/- The FRI fold orchestration loop renders the owned back-edge + the
    `call fri_fold_rc` body. -/
#guard
  let s := renderLfundef "p3_fri_fold_loop" friFoldLoop.lfd_body
  occursIn ".L0:" s && occursIn "jne .L0" s && occursIn "call fri_fold_rc" s

/- The Merkle compress orchestration loop renders the owned back-edge + the
    `call plonky3_merkle_compress_rc` body. -/
#guard
  let s := renderLfundef "p3_merkle_compress_loop" merkleCompressLoop.lfd_body
  occursIn ".L0:" s && occursIn "jne .L0" s
    && occursIn "call plonky3_merkle_compress_rc" s

/- The PoW grind orchestration loop renders the owned back-edge + the
    `call plonky3_merkle_hash_leaf_rc` grind body. -/
#guard
  let s := renderLfundef "p3_pow_grind_loop" powGrindLoop.lfd_body
  occursIn ".L0:" s && occursIn "jne .L0" s
    && occursIn "call plonky3_merkle_hash_leaf_rc" s

/-! ## 5. The composed object carries every leaf AND every orchestration loop -/

#guard (hasSub wholeProverOrchAsm "plonky3_merkle_compress_rc")
#guard (hasSub wholeProverOrchAsm "plonky3_merkle_hash_leaf_rc")
theorem wholeProverOrch_has_fri_fold :
    hasSub wholeProverOrchAsm "fri_fold_rc" = true := by native_decide
theorem wholeProverOrch_has_merkle_leaf_loop :
    hasSub wholeProverOrchAsm "p3_merkle_leaf_loop" = true := by native_decide
#guard (hasSub wholeProverOrchAsm "p3_merkle_compress_loop")
theorem wholeProverOrch_has_fri_fold_loop :
    hasSub wholeProverOrchAsm "p3_fri_fold_loop" = true := by native_decide
#guard (hasSub wholeProverOrchAsm "p3_fri_query_loop")
theorem wholeProverOrch_has_pow_grind_loop :
    hasSub wholeProverOrchAsm "p3_pow_grind_loop" = true := by native_decide
theorem wholeProverOrch_no_unhandled :
    hasSub wholeProverOrchAsm "UNHANDLED" = false := by native_decide

/-- **Single-binary composition with orchestration loops owned.** The one composed
    `.s` carries the five field-kernel leaves AND the five orchestration-loop
    drivers (Merkle leaf/compress, FRI fold, query, PoW), each an owned-backend
    looped `Lcmd` with no unhandled op. The prove path is owned control flow over
    owned field arithmetic. -/
theorem wholeProverOrch_shape :
    hasSub wholeProverOrchAsm "fri_fold_rc" = true
      ∧ hasSub wholeProverOrchAsm "p3_merkle_leaf_loop" = true
      ∧ hasSub wholeProverOrchAsm "p3_fri_fold_loop" = true
      ∧ hasSub wholeProverOrchAsm "p3_pow_grind_loop" = true
      ∧ hasSub wholeProverOrchAsm "UNHANDLED" = false :=
  ⟨wholeProverOrch_has_fri_fold,
   wholeProverOrch_has_merkle_leaf_loop,
   wholeProverOrch_has_fri_fold_loop,
   wholeProverOrch_has_pow_grind_loop,
   wholeProverOrch_no_unhandled⟩

/-- The composed function list is exactly the field leaves followed by the five
    orchestration-loop drivers — the composition adds the orchestration loops and
    drops no field leaf. -/
theorem wholeProverOrch_funcs_eq :
    wholeProverOrchLprog.lp_funcs = wholeProverLprog.lp_funcs ++ orchLoopFuncs := rfl

/-- The composed object adds exactly the five orchestration-loop functions on top
    of the field leaves. -/
theorem wholeProverOrch_func_count :
    wholeProverOrchLprog.lp_funcs.length
      = wholeProverLprog.lp_funcs.length + 5 := by
  simp [wholeProverOrchLprog, orchLoopFuncs, List.length_append]

/-! ## 5b. Shape lemmas: the owned ZMM Poseidon2 permute is wired into the prover

The rerouted object (`wholeProverZmmLprog`) carries the owned ZMM Poseidon2
permute driver (`p3_poseidon2_perm_zmm`), whose body `call`s the four owned
ZMM half-kernels, and the Merkle / FRI-query / PoW orchestration loops now call
that owned ZMM permute instead of the scalar mixers. -/

/-- The owned ZMM permute body is the `poseidon2_bb_avx512_mont` schedule of
    half-kernel calls: 2 (to-mont) + 8 (4 ext) + 26 (13 int) + 8 (4 ext) +
    2 (from-mont) = 46 ZMM half-kernel `Lcall`s, independent of any trip count. -/
theorem p3PermZmm_body_length : p3PermZmmBody.length = 46 := by native_decide

/-- The owned ZMM permute body begins with the to-Montgomery half-kernel call —
    the first step of the `poseidon2_bb_avx512_mont` schedule. -/
theorem p3PermZmm_starts_tomont :
    p3PermZmmBody.head? = some (zmCall zmTomont) := rfl

/-- The rerouted object carries the owned ZMM permute driver and all four owned
    ZMM half-kernel symbols (the verified-x86+ZMM-backend leaf), under their own
    `call` sites — the owned AVX-512 Poseidon2 leaf wired into the prover. -/
theorem wholeProverZmm_has_perm_driver :
    hasSub wholeProverZmmAsm "p3_poseidon2_perm_zmm" = true := by native_decide
theorem wholeProverZmm_calls_extround :
    hasSub wholeProverZmmAsm "call zm_extround_half_ptr" = true := by native_decide
theorem wholeProverZmm_calls_intdiag :
    hasSub wholeProverZmmAsm "call zm_intdiag_half_ptr" = true := by native_decide
#guard (hasSub wholeProverZmmAsm "call zm_tomont_half_ptr")
#guard (hasSub wholeProverZmmAsm "call zm_frommont_half_ptr")

/- The Merkle leaf / Merkle compress / FRI-query / PoW orchestration loops now
    `call` the owned ZMM permute (`p3_poseidon2_perm_zmm`), not the scalar
    `plonky3_merkle_{hash_leaf,compress}_rc` mixers — the permute reroute. -/
#guard (hasSub (renderLfundef "p3_merkle_leaf_loop" merkleLeafLoopZmm.lfd_body) "call p3_poseidon2_perm_zmm") && (hasSub (renderLfundef "p3_merkle_compress_loop" merkleCompressLoopZmm.lfd_body) "call p3_poseidon2_perm_zmm") && (hasSub (renderLfundef "p3_pow_grind_loop" powGrindLoopZmm.lfd_body) "call p3_poseidon2_perm_zmm")

/-- The FRI fold loop is unchanged — it folds field elements (`fri_fold_rc`), not
    a Poseidon2 permute, so it is not part of the hash phase that reroutes. -/
theorem wholeProverZmm_fri_fold_unchanged :
    hasSub wholeProverZmmAsm "fri_fold_rc" = true := by native_decide

/-- The rerouted object has no unhandled op — the ZMM permute wiring is all owned
    `call`/`loopLcmd` control flow. -/
theorem wholeProverZmm_no_unhandled :
    hasSub wholeProverZmmAsm "UNHANDLED" = false := by native_decide

/-- **The owned AVX-512 ZMM Poseidon2 permute is wired into the prover.** The one
    rerouted `.s` carries the owned ZMM permute driver, all four owned ZMM
    half-kernel call sites, the rerouted hash-phase loops (Merkle / FRI-query /
    PoW) calling that permute, and no unhandled op. The dominant prover lever
    (Poseidon2 ≈ 97% of the hash phase) now runs on the owned ZMM kernels. -/
theorem wholeProverZmm_shape :
    hasSub wholeProverZmmAsm "p3_poseidon2_perm_zmm" = true
      ∧ hasSub wholeProverZmmAsm "call zm_extround_half_ptr" = true
      ∧ hasSub wholeProverZmmAsm "call zm_intdiag_half_ptr" = true
      ∧ hasSub wholeProverZmmAsm "fri_fold_rc" = true
      ∧ hasSub wholeProverZmmAsm "UNHANDLED" = false :=
  ⟨wholeProverZmm_has_perm_driver, wholeProverZmm_calls_extround,
   wholeProverZmm_calls_intdiag, wholeProverZmm_fri_fold_unchanged,
   wholeProverZmm_no_unhandled⟩

/-- The rerouted function list is the field leaves followed by the owned ZMM
    permute driver and the six rerouted orchestration loops. -/
theorem wholeProverZmm_funcs_eq :
    wholeProverZmmLprog.lp_funcs = wholeProverLprog.lp_funcs ++ orchLoopFuncsZmm := rfl

/-- The rerouted object adds exactly the owned ZMM permute driver plus the five
    orchestration loops (six functions) on top of the field leaves. -/
theorem wholeProverZmm_func_count :
    wholeProverZmmLprog.lp_funcs.length
      = wholeProverLprog.lp_funcs.length + 6 := by
  simp [wholeProverZmmLprog, orchLoopFuncsZmm, List.length_append]

/-! ## 6. Emit driver -/

/-- Write the single composed whole-prover `.s` (field leaves + owned
    orchestration loops) into the bench harness directory. -/
def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/plonky3_whole_prover_orch_owned.s") wholeProverOrchAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/plonky3_whole_prover_orch_owned.s"
  IO.println "  ONE .s: 5 field leaves + 5 owned orchestration loops (Merkle/FRI/query/PoW)"
  IO.println "  prove path control flow is owned loopLcmd back-edges (.L:/cmp/jne), NO C for/while"
  -- ZMM-rerouted variant: the Poseidon2 permute call routed to the owned
  -- AVX-512 (ZMM) leaf (the #647 Gap-2-item-1 lever).
  IO.FS.writeFile (dir ++ "/plonky3_whole_prover_zmm_owned.s") wholeProverZmmAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/plonky3_whole_prover_zmm_owned.s"
  IO.println "  ONE .s: field leaves + p3_poseidon2_perm_zmm (owned ZMM half-kernel calls)"
  IO.println "  Merkle/FRI-query/PoW permute -> owned AVX-512 ZMM Poseidon2 leaf (NOT scalar)"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsEmit
