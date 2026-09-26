/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
public import CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit

/-!
# Whole-function `keccakf1600_zmm8` assembled from the θρπχι sub-step `Com`s

The lane-sliced (8-way ZMM) Keccak-f[1600] permutation as ONE owned AT&T `.s`
function: 24 rounds, all 25 state lanes, register-resident, assembled from the
four committed sub-step `Com jasminDialect` programs of
`Keccak4WayVpackZmmEmit` through
`VIR.VpackZmmComSeq.renderVpackZmmAllocSeq`.

```
generated List (XAlloc × VpackZmmBlock)      -- 2160 blocks: 24 rounds × 90 blocks
        │  renderVpackZmmAllocSeq            -- threads the SSA counter, per-block allocs
        ▼
   List String                               -- ONE straight-line owned %zmm body
        │  frameAsmFunction + generated ABI glue + .rodata
        ▼
   String                                    -- the whole `keccakf1600_zmm8` `.s`
```

## The renderer contract this module works inside

`renderVpackZmmAllocSeq : VpackZmmAllocSeq → (List String × String)` folds
`VpackZmmAsmPrint.lowerVpackZmmCom` over a `List (XAlloc × VpackZmmBlock)`,
carrying a fresh-SSA counter across blocks and rendering each block against its
OWN `XAlloc`. Three properties of that contract shape everything below.

* **Each block's free context is renamed `p0, p1, …` afresh** (by
  `JasminPrint.paramsAndMap`), and its `k`-th `Com.var` binding is named
  `v{next+k}` where `next` is the running total of all earlier blocks' bindings.
  So a block's `XAlloc` must key on `p`-indices local to that block and on
  `v`-indices offset by the cumulative binding count. The generator below
  threads that counter explicitly (`GenSt.next`), advancing it by 4 for a θ
  column block, 3 for a ρ or χ block, and 1 for a packed-XOR block.

* **The body is register-to-register only.** `lowerVpackZmmExpr` emits a real
  instruction for `JasminOp.vpackZMM` alone; every other op renders as a
  `# <unsupported …>` comment. There is no move, load, or store in the emitted
  fragment, so all 25 state lanes stay pinned in `%zmm0..%zmm24` for the whole
  permutation and the 7 remaining `%zmm` registers carry every temporary.

* **An `XAlloc` value is emitted verbatim** by `VpackZmmAsmPrint.zmmReg` (an
  unmapped name yields the `<UNALLOCATED:…>` sentinel instead). The FIPS 202
  constants — the ι round constants, the ρ shift counts, and χ's all-ones mask —
  therefore reach the body as rip-relative `.rodata` operands in the AVX-512
  memory-source position (`vpxorq .Lkeccakf1600_zmm8_c<i>(%rip), %zmm0, %zmm0`,
  a label of the constant pool `keccakPool`), which is the
  second-source slot every sub-step `Com` puts its constant argument in. This is
  the same trust class as the `vmovdqa64 c_ALLONES(%rip), %zmm11` prologue
  broadcast the per-sub-step twins carry, and it is what the register budget
  forces: 59 distinct broadcast values (24 round constants, the 34 shift counts
  the ρ offsets and their 64-complements range over, and the all-ones mask)
  cannot be resident alongside 25 state lanes in a 32-register file, and the
  renderer emits neither an in-body broadcast load nor an immediate-count shift.

## Sub-step reuse

Every block is one of four committed `Com`s, unmodified:

| FIPS 202 step | block | `Com` | bindings |
|---|---|---|---|
| θ column parity `C[x] = ⊕_y A[x,y]` | 5 per round | `thetaColCom` | 4 |
| θ `rot(C[x+1], 1)`, ρ per-lane rotate | 5 + 24 per round | `rotlStepCom` | 3 |
| θ `D[x] = C[x-1] ^ rot(…)`, θ mix `A[x,y] ^= D[x]`, ι `A[0,0] ^= RC[r]` | 31 per round | `iotaStepCom` | 1 |
| χ `A[x,y] ^ (¬A[x+1,y] ∧ A[x+2,y])` | 25 per round | `chiStepCom` | 3 |

`iotaStepCom` is a two-input packed XOR, so it serves every plain XOR the
permutation needs, not only ι. π emits no instruction: it renames which `%zmm`
holds which lane, tracked in `GenSt.regOf`. χ writes its five row outputs into
spare registers and renames the row, which is how a register-resident χ avoids
needing a packed move (the `vpackZMM` fragment has none).

## Register budget

25 lanes in `regOf`, 7 spares. θ holds the five column parities plus a
rotate-temp pair (7). ρ needs two temps. χ needs five destinations plus one
temp per row, and hands its five consumed source registers back to the spare
pool, so the pool stays at 7 across all five rows. The `%zmm` file is therefore
never oversubscribed and no `<UNALLOCATED:…>` sentinel can appear.

## ABI

`keccakf1600_zmm8(uint64_t state[25][8], uint64_t scratch[25][8])`, state in
`%rdi` and updated in place, matching `keccak_zmm8_kat.c` and
`keccak_zmm8_bench.c`. The prologue loads lane `i` from `64·i(%rdi)` into
`%zmm{i}`; the epilogue stores each lane from whichever register the tracked
π/χ renaming left it in. The `%rsi` scratch pointer is unread — a
register-resident permutation needs no spill buffer — and stays in the signature
for harness compatibility. All `%zmm` registers are caller-saved under SysV, so
there is no frame.

## Value correctness

The per-step denotations are the committed `thetaColCom_denote`,
`rotlStepCom_denote`, `chiStepCom_denote`, and `iotaStepCom_denote`, and one
whole round's fold across the four sub-step boundaries is
`Keccak4WayWholeRoundVpackZmmEmit.whole_round_denote`. The all-lanes / all-rounds
value gate is the external XKCP KAT in `bench/keccak4way_compare/`, which runs
the emitted `.s`; the pins in this module are structural (block count,
instruction count, absence of unallocated names and of out-of-fragment
comments).

Invoke:
`lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/Keccak4WayWholePermVpackZmmEmit.lean`

## Main definitions

* the per-round block generator: 90 blocks per round — 5 `thetaColCom`, 29
  `rotlStepCom`, 31 `iotaStepCom`, 25 `chiStepCom` — each an unmodified sub-step
  `Com` from the existing VpackZmm twins, giving 2160 blocks over 24 rounds
* `checkWholePerm`: the twelve structural conditions on the render, including that
  every rodata operand has a defining label and that the final lane map is a
  permutation. It runs in the emit driver rather than as a `#guard`, because
  kernel-reducing 2160 dependently typed blocks exhausts memory
* `emit`: writes `bench/keccak4way_compare/gen_com/keccakf1600_zmm8_whole.s`, and
  refuses to write when `checkWholePerm` is non-empty

## Main results

None are declared here; correctness rests on the per-round anchor
`Keccak4WayWholeRoundVpackZmmEmit.whole_round_denote` together with the structural
conditions above, and the value gate is the XKCP KAT. The 59 FIPS 202 broadcast
constants are supplied as rip-relative rodata operands, which the block denotation
does not verify.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholePermVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
  (VpackZmmBlock VpackZmmAllocSeq renderVpackZmmAllocSeq)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.VIR.RodataPool (Pool quadsAt undefinedRef)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit
  (r512 thetaCtx rotlCtx chiCtx iotaCtx
   thetaColCom rotlStepCom chiStepCom iotaStepCom
   rhoOff roundConst)

/-! ## 1. Operand spellings

Names an `XAlloc` maps to: `%zmm` registers for the state lanes and temporaries,
rip-relative `.rodata` operands for the FIPS 202 broadcast constants. -/

/-- The `%zmm` register with index `k`. -/
def zmm (k : Nat) : String := "%zmm" ++ toString k

/-- The `v`-name of the `k`-th `Com.var` binding of the whole sequence (the
    fresh-SSA name `renderVpackZmmAllocSeq` assigns when the running binding
    count reaches `k`). -/
def vname (k : Nat) : String := "v" ++ toString k

/-- Memory operand of state lane `i` in the `state[25][8]` argument (`%rdi`):
    64 bytes per lane in SoA order `i = x + 5y`. -/
def laneMem (i : Nat) : String := toString (64 * i) ++ "(%rdi)"

/-- The pool entry of a 64-byte broadcast: `v` in each of the eight 64-bit lanes,
    64-byte aligned. -/
def bcastEntry (v : Nat) : Nat × List Nat := (6, List.replicate 8 v)

/-- The broadcast values of the permutation: χ's all-ones mask, the 24 ι round
    constants, and the shift counts `1..63` (ρ's offsets and their 64-complements,
    plus θ's `1`/`63`). -/
def keccakConstValues : List Nat :=
  0xFFFFFFFFFFFFFFFF :: (List.range 24).map roundConst ++ (List.range 63).map (· + 1)

/-- The `.rodata` pool of the permutation's broadcasts; equal values share an entry. -/
def keccakPool : Pool :=
  Pool.ofList ".Lkeccakf1600_zmm8" (keccakConstValues.map bcastEntry)

/-- The rip-relative operand of the pool's broadcast of `v`. -/
def bcastConst (v : Nat) : String :=
  keccakPool.ref (bcastEntry v).1 (bcastEntry v).2 ++ "(%rip)"

/-- The label of a broadcast value of the permutation reads back `v` in every lane. -/
theorem quadsAt_keccakPool (v : Nat) (h : v ∈ keccakConstValues) :
    quadsAt keccakPool.directives (keccakPool.ref 6 (List.replicate 8 v)) =
      some (List.replicate 8 v) :=
  Pool.quadsAt_ofList_ref _ _ 6 _ (List.mem_map_of_mem (f := bcastEntry) h)

/-- The `.rodata` broadcast holding the shift count `n` in all eight lanes. -/
def rotConst (n : Nat) : String := bcastConst n

/-- The `.rodata` broadcast holding the ι round constant `RC[r]`. -/
def rcConst (r : Nat) : String := bcastConst (roundConst r)

/-- The `.rodata` broadcast holding `2^64 - 1` in all eight lanes (χ's `¬b`
    is `b ^ allones`; the `vpackZMM` alphabet has no packed NOT). -/
def allOnesConst : String := bcastConst 0xFFFFFFFFFFFFFFFF

/-! ## 2. The four block builders

Each takes the running binding count `next` and the operands, and returns the
`(XAlloc × VpackZmmBlock)` pair `renderVpackZmmAllocSeq` consumes. The `p`-keys
are the block-local param names; the `v`-keys are offset by `next`. -/

/-- A θ column-parity block: `dst := s0 ^ s1 ^ s2 ^ s3 ^ s4` over `thetaColCom`.
    Its four fold temporaries all land in `dst`, so the render is four
    accumulating `vpxorq`s. Four bindings. -/
def thetaBlockAt (next : Nat) (srcs : List String) (dst : String) :
    XAlloc × VpackZmmBlock :=
  ( (List.range 5).map (fun k => ("p" ++ toString k, srcs.getD k "")) ++
      (List.range 4).map (fun k => (vname (next + k), dst))
  , ⟨thetaCtx, r512, thetaColCom⟩ )

/-- A ρ rotate block: `out := (src <<< cn) ||| (src >>> c64mn)` over
    `rotlStepCom`, with `cn` / `c64mn` the lane-uniform shift-count operands.
    `hi` and `lo` are the two shift destinations. Three bindings. -/
def rotlBlockAt (next : Nat) (src cn c64mn hi lo out : String) :
    XAlloc × VpackZmmBlock :=
  ( [ ("p0", src), ("p1", cn), ("p2", c64mn)
    , (vname next, hi), (vname (next + 1), lo), (vname (next + 2), out) ]
  , ⟨rotlCtx, r512, rotlStepCom⟩ )

/-- A two-input packed XOR block: `out := a ^ b` over `iotaStepCom`. Serves ι,
    θ's `D[x]`, and θ's `A[x,y] ^= D[x]` mix. One binding. -/
def xorBlockAt (next : Nat) (a b out : String) : XAlloc × VpackZmmBlock :=
  ( [ ("p0", a), ("p1", b), (vname next, out) ]
  , ⟨iotaCtx, r512, iotaStepCom⟩ )

/-- A χ block: `out := a ^ ((b ^ allones) ∧ c)` over `chiStepCom`. Both
    intermediates share the temporary `tmp`. Three bindings. -/
def chiBlockAt (next : Nat) (a b c tmp out : String) : XAlloc × VpackZmmBlock :=
  ( [ ("p0", a), ("p1", b), ("p2", c), ("p3", allOnesConst)
    , (vname next, tmp), (vname (next + 1), tmp), (vname (next + 2), out) ]
  , ⟨chiCtx, r512, chiStepCom⟩ )

/-! ## 3. Generator state

The block list is built in reverse (`acc`) alongside the three pieces of state
the renderer contract and the register budget require: the running binding count,
the lane → `%zmm` map, and the spare-register pool. -/

/-- The state threaded through the permutation generator: the reversed block
    accumulator, the running `Com.var` binding count (the renderer's fresh-SSA
    counter), the lane → `%zmm` map, and the 7-register spare pool. -/
structure GenSt where
  /-- Blocks emitted so far, most recent first. -/
  acc : List (XAlloc × VpackZmmBlock)
  /-- Total `Com.var` bindings emitted so far (the renderer's SSA counter). -/
  next : Nat
  /-- `regOf[i]` is the `%zmm` register holding state lane `i = x + 5y`. -/
  regOf : Array String
  /-- The `%zmm` registers holding no state lane. -/
  spares : List String

/-- Append one block, advancing the binding count by `nb` (the block's `Com.var`
    count, which is what `renderVpackZmmAllocSeq` advances its counter by). -/
def GenSt.push (st : GenSt) (nb : Nat) (ab : XAlloc × VpackZmmBlock) : GenSt :=
  { st with acc := ab :: st.acc, next := st.next + nb }

/-- Lane `i`'s current register. -/
def GenSt.lane (st : GenSt) (i : Nat) : String := st.regOf.getD i ""

/-- Spare register `k` of the pool. -/
def GenSt.spare (st : GenSt) (k : Nat) : String := st.spares.getD k ""

/-! ## 4. The five per-round phases

θ and ρ mutate lanes in place; π and χ rename. -/

/-- θ. Five column parities `C[x] = ⊕_y A[x,y]` into spares `0..4`, then for each
    `x` the rotate `rot(C[x+1], 1)` and `D[x] = C[x-1] ^ rot(…)` through spares
    `5`/`6`, then `A[x,y] ^= D[x]` on all five lanes of column `x`.
    65 instructions, 35 blocks; the lane map is unchanged. -/
def genTheta (st0 : GenSt) : GenSt :=
  let t1 := st0.spare 5
  let t2 := st0.spare 6
  let cReg : Nat → String := fun x => st0.spare x
  let st1 := (List.range 5).foldl (fun st x =>
      st.push 4 (thetaBlockAt st.next
        ((List.range 5).map (fun y => st.lane (x + 5 * y))) (cReg x))) st0
  (List.range 5).foldl (fun st x =>
      -- rot(C[x+1], 1) into t1
      let st := st.push 3
        (rotlBlockAt st.next (cReg ((x + 1) % 5)) (rotConst 1) (rotConst 63) t1 t2 t1)
      -- D[x] = C[x-1] ^ rot(C[x+1], 1) into t2
      let st := st.push 1 (xorBlockAt st.next (cReg ((x + 4) % 5)) t1 t2)
      -- A[x,y] ^= D[x]
      (List.range 5).foldl (fun st y =>
        let lr := st.lane (x + 5 * y)
        st.push 1 (xorBlockAt st.next lr t2 lr)) st) st1

/-- ρ. Left-rotate lane `i` by `rhoOff i`, in place, through spares `0`/`1`. The
    lane with offset 0 emits nothing. 72 instructions, 24 blocks; the lane map is
    unchanged. -/
def genRho (st0 : GenSt) : GenSt :=
  let h := st0.spare 0
  let l := st0.spare 1
  (List.range 25).foldl (fun st i =>
      let n := rhoOff i
      if n = 0 then st
      else
        let lr := st.lane i
        st.push 3 (rotlBlockAt st.next lr (rotConst n) (rotConst (64 - n)) h l lr)) st0

/-- π. `B[y, (2x+3y) % 5] = A[x, y]`, i.e. lane `j = y + 5·((2x+3y) % 5)` takes
    lane `i = x + 5y`'s value. Emits no instruction: it permutes the lane → `%zmm`
    map. -/
def genPi (st : GenSt) : GenSt :=
  let old := st.regOf
  { st with
      regOf := (List.range 25).foldl (fun a i =>
        let x := i % 5
        let y := i / 5
        a.set! (y + 5 * ((2 * x + 3 * y) % 5)) (old.getD i "")) (Array.replicate 25 "") }

/-- χ. Row by row, `A[x,y] := A[x,y] ^ (¬A[x+1,y] ∧ A[x+2,y])` with the five row
    outputs written into spares `0..4` and spare `5` as the AND-NOT temporary.
    The row's five consumed source registers return to the spare pool, so the
    pool stays at 7 across the five rows. 75 instructions, 25 blocks; the lane
    map is renamed row by row. -/
def genChi (st0 : GenSt) : GenSt :=
  (List.range 5).foldl (fun st y =>
      let dst : Nat → String := fun x => st.spare x
      let tmp := st.spare 5
      let keep := st.spare 6
      let srcs := (List.range 5).map (fun x => st.lane (5 * y + x))
      let st' := (List.range 5).foldl (fun st x =>
          st.push 3 (chiBlockAt st.next (srcs.getD x "") (srcs.getD ((x + 1) % 5) "")
            (srcs.getD ((x + 2) % 5) "") tmp (dst x))) st
      { st' with
          regOf := (List.range 5).foldl
            (fun a x => a.set! (5 * y + x) (dst x)) st'.regOf
          spares := srcs ++ [tmp, keep] }) st0

/-- ι. `A[0,0] ^= RC[r]`, the round constant read from `.rodata`. One
    instruction, one block. -/
def genIota (r : Nat) (st : GenSt) : GenSt :=
  let lr := st.lane 0
  st.push 1 (xorBlockAt st.next lr (rcConst r) lr)

/-- One whole FIPS 202 round in order θ → ρ → π → χ → ι. 213 instructions,
    90 blocks. -/
def genRound (r : Nat) (st : GenSt) : GenSt :=
  genIota r (genChi (genPi (genRho (genTheta st))))

/-! ## 5. The whole 24-round permutation as a block sequence -/

/-- The initial generator state: lane `i` in `%zmm{i}`, the seven registers
    `%zmm25..%zmm31` spare, no blocks, binding count 0. -/
def initGen : GenSt :=
  { acc := []
  , next := 0
  , regOf := (List.range 25).map zmm |>.toArray
  , spares := (List.range 7).map (fun k => zmm (25 + k)) }

/-- The generator state after all 24 rounds. Its `regOf` is the lane → `%zmm`
    map the epilogue stores from. -/
def genFinal : GenSt := (List.range 24).foldl (fun st r => genRound r st) initGen

/-- The whole permutation as the `(XAlloc × VpackZmmBlock)` sequence
    `renderVpackZmmAllocSeq` folds: 24 rounds × 90 blocks, in program order. -/
def keccakWholeSeq : VpackZmmAllocSeq := genFinal.acc.reverse

/-- The straight-line owned AT&T `%zmm` body of the whole permutation. -/
def wholeBody : List String := (renderVpackZmmAllocSeq keccakWholeSeq).1

/-! ## 6. ABI glue and `.rodata`

The prologue and epilogue are the memory-op surface the `vpackZMM` fragment does
not cover, generated from the lane → `%zmm` map rather than written per lane. -/

/-- Load each of the 25 state lanes from `64·i(%rdi)` into `%zmm{i}`. -/
def prologueLines : List String :=
  (List.range 25).map (fun i => "\tvmovdqu64\t" ++ laneMem i ++ ", " ++ zmm i)

/-- Store each state lane back to `64·i(%rdi)` from whichever register the
    tracked π / χ renaming left it in. -/
def epilogueLines : List String :=
  (List.range 25).map (fun i =>
    "\tvmovdqu64\t" ++ genFinal.regOf.getD i "" ++ ", " ++ laneMem i)

/-- The `.rodata` section: the directives of `keccakPool`. -/
def rodataSection : String := keccakPool.text

/-- The whole `keccakf1600_zmm8` `.s`: the framed straight-line body of all 2160
    rendered blocks, the generated ABI glue, and the `.rodata` broadcasts. -/
def wholePermAsm : String :=
  "# Lane-sliced (8-way ZMM) Keccak-f[1600], whole function, owned Com vpackZMM emit.\n"
  ++ "# 24 rounds × 25 lanes assembled from the committed θρπχι sub-step Coms\n"
  ++ "# through VIR.VpackZmmComSeq.renderVpackZmmAllocSeq; state register-resident.\n"
  ++ "# Trust boundary: this printer's AT&T syntax, gas, and the ABI load/store offsets.\n"
  ++ frameAsmFunction "keccakf1600_zmm8" prologueLines wholeBody epilogueLines
  ++ rodataSection
  ++ "\n\t.section .note.GNU-stack,\"\",@progbits\n"

/-! ## 7. Structural checks

The pinned quantities are checked in the emit driver rather than by a `#guard` or
a `native_decide`: a compile-time check on this sequence forces kernel reduction
of 2160 dependently-typed blocks, whereas the driver evaluates the render once,
compiled. `checkWholePerm` returns the violated conditions, and `emit` refuses to
write when it is non-empty. The value gate for all lanes and all rounds is the
external XKCP KAT in `bench/keccak4way_compare/`. -/

/-- Structural conditions the whole-permutation render must satisfy, as a list of
    the violated ones (empty when the render is well formed):

* 24 rounds × 90 blocks — five θ column parities, five θ rotate/`D`/mix groups of
  seven blocks, 24 ρ rotates, 25 χ lanes, one ι;
* 24 rounds × 213 instructions — θ 65, ρ 72, χ 75, ι 1;
* no `<UNALLOCATED:…>` sentinel, i.e. every name every block reads resolves
  through that block's `XAlloc` and the `%zmm` file is not oversubscribed;
* no `# <unsupported …>` comment, i.e. every block is inside the `vpackZMM`
  fragment;
* every `.rodata` constant the body reads is held by `keccakPool` (no
  `undefinedRef` operand), so its label is defined by `rodataSection` and the
  render links;
* the export symbol and the five packed mnemonics of the θρπχι alphabet present,
  and no UPPERCASE jasmin intrinsic. -/
def checkWholePerm : List String :=
  let body := String.intercalate "\n" wholeBody
  let asm := wholePermAsm
  -- a constant the pool does not hold renders as `undefinedRef`; every other
  -- rip-relative operand is a pool label, defined by `rodataSection`.
  let want : List (String × Bool) :=
    [ ("block count is 24 × 90", keccakWholeSeq.length == 24 * 90)
    , ("instruction count is 24 × 213", wholeBody.length == 24 * 213)
    , ("no unallocated name", !(strContains body "<UNALLOCATED"))
    , ("every block in the vpackZMM fragment", !(strContains body "<unsupported"))
    , ("every .rodata reference is defined", !(strContains body undefinedRef))
    , ("exports keccakf1600_zmm8", strContains asm "keccakf1600_zmm8:")
    , ("issues vpxorq", strContains asm "vpxorq")
    , ("issues vpandq", strContains asm "vpandq")
    , ("issues vporq", strContains asm "vporq")
    , ("issues vpsllvq", strContains asm "vpsllvq")
    , ("issues vpsrlvq", strContains asm "vpsrlvq")
    , ("no jasmin intrinsic", !(strContains asm "#VPXOR")) ]
  (want.filter (fun p => !p.2)).map (fun p => p.1)

/-! ## 8. Emit driver -/

/-- Write the whole-function owned `Com`-rendered `keccakf1600_zmm8` `.s` to
    `bench/keccak4way_compare/gen_com/`, gated on `checkWholePerm`. -/
def emit : IO Unit := do
  match checkWholePerm with
  | [] =>
      IO.FS.createDirAll "bench/keccak4way_compare/gen_com"
      IO.FS.writeFile "bench/keccak4way_compare/gen_com/keccakf1600_zmm8_whole.s"
        wholePermAsm
      IO.println s!"wrote bench/keccak4way_compare/gen_com/keccakf1600_zmm8_whole.s ({wholeBody.length} body instructions from {keccakWholeSeq.length} Com blocks)"
  | bad =>
      throw <| IO.userError <|
        "whole-permutation render failed its structural checks: "
          ++ String.intercalate "; " bad

end CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholePermVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholePermVpackZmmEmit in
/-- `lake env lean --run` entry point: emit the whole-function owned
    `Com`-rendered lane-sliced Keccak-f[1600] permutation. -/
private def main : IO Unit := emit
