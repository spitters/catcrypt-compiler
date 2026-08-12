/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint

/-!
# Owned `.s` emit for lane-sliced Keccak-f[1600] migrated onto the unified `Com jasminDialect` (512-bit ZMM)

`bench/keccak4way_compare/` runs the lane-sliced (8-way ZMM / low-4 = AVX2 ymm)
Keccak-f[1600] permutation: the 25-lane state is held in 25 `reg 512` (ZMM)
registers `S0..S24`, where lane `k` of `Sᵢ` is sponge `k`'s state-lane
`i = x + 5y`. One packed θρπχι round advances all eight sponges in lock-step, with
**no cross-lane routing** (θ XORs whole registers; ρ rotates each 64-bit lane in
place; π renames registers; χ is `a ^ (¬b ∧ c)` per lane; ι XORs a broadcast
round constant). So the packed permutation denotes `N` independent scalar Keccak
permutations.

The pre-migration emit expressed each θρπχι sub-step as a bespoke `Avx512Model.ZOp`
block (`thetaBlk`/`rhoPiBlk`/`chiBlk`/`iotaBlk`), lowered through
`Avx512Lowering.lowerZBlock` to the bespoke `ZInstr` machine and rendered by
`Avx512AsmPrinter.renderZInstr`. That bespoke `Avx512Model` machine is gone from this
package; what survives here is the **SIMD-dialect-unification** twin: the same per-step
op-blocks as straight-line `Com jasminDialect` programs over `reg 512` (ZMM) registers,
rendered through `VpackZmmAsmPrint.renderVpackZmmCom` (`JasminOp.vpackZMM`) +
`VsimdAsmPrint.frameAsmFunction`.

```
keccak sub-step Com  (Com jasminDialect, vpackZMM .xor/.and/.or/.shl/.shr ops)
        │  XAlloc (caller-supplied: param + SSA-result → %zmm)
        ▼  VpackZmmAsmPrint.renderVpackZmmCom
   List String  (owned AT&T %zmm body lines)
        │  VsimdAsmPrint.frameAsmFunction  (SysV ABI load/store glue)
        ▼
   String        (a complete owned `.s`)
```

The import set is exactly `VpackZmmAsmPrint` (→ `JasminPrint`/`JasminDialect`,
the de-Bruijn→name walk + the `%zmm` operand renderer; `VsimdAsmPrint`'s `XAlloc`
/ `frameAsmFunction` reused transitively). The bespoke `Avx512Model`
(`ZInstr`/`ZState`/`runZBlock`) and its `Avx512AsmPrinter` are **not** in the
lowering or printing path of this emit.

## Op mapping (the whole θρπχι alphabet rides `vpackZMM`)

| Keccak sub-op            | bespoke `ZOp`        | `Com jasminDialect` op          | denote          |
|--------------------------|----------------------|---------------------------------|-----------------|
| θ column parity, mix     | `.xor`               | `vpackZMM .xor` (`vpxorq`)      | `zmmPackQ .xor` |
| χ `(¬b ∧ c)` mask        | `.and`               | `vpackZMM .and` (`vpandq`)      | `zmmPackQ .and` |
| ρ rotate `hi \|\| lo`    | `.or`                | `vpackZMM .or`  (`vporq`)       | `zmmPackQ .or`  |
| ρ rotate `src <<< n`     | `.shl src n` (imm)   | `vpackZMM .shl` (`vpsllvq`)     | `zmmPackQ .shl` |
| ρ rotate `src >>> 64-n`  | `.shr src (64-n)`    | `vpackZMM .shr` (`vpsrlvq`)     | `zmmPackQ .shr` |
| χ `¬b`                   | `.xor b ALLONES`     | `vpackZMM .xor` (`vpxorq`)      | `zmmPackQ .xor` |
| ι `A[0,0] ^= RC[r]`      | `.xor S0 RCr`        | `vpackZMM .xor` (`vpxorq`)      | `zmmPackQ .xor` |

The whole permutation stays inside `{vpxorq, vpandq, vporq, vpsllvq, vpsrlvq}`,
each a `JasminOp.vpackZMM` arm the unified dialect already denotes (`zmmPackQ`),
with `Avx512Lowering` off the path.

### ρ rotate: immediate-shift → broadcast-count variable shift (documented)

The bespoke `rotlBlk` rotates a lane by `n` via the two **immediate** shifts
`src <<< n` / `src >>> (64-n)` (jasmin `#VPSLL_8u64` / `#VPSRL_8u64` with a
compile-time count). The unified `vpackZMM .shl` / `.shr` are the **per-lane
variable** shifts `vpsllvq` / `vpsrlvq`: `zmmPackQ .shl a b` shifts lane `k` of
`a` by `(zmmLane b k).toNat`. To realise the constant rotate we thread a
**broadcast-constant register** `Cn` whose every 64-bit lane holds the rotate
amount `n` (a `.rodata` `.quad`-×8 broadcast, loaded with `vmovdqa64 c_rotN(%rip),
%zmm`, exactly the trust class of the bespoke `c_ALLONES` / `c_RCr` broadcasts the
driver already threads). With `Cn` and `C64mn` (holding `n` and `64-n`
respectively in every lane), `vpsllvq %Cn` / `vpsrlvq %C64mn` compute the same
per-lane value as the bespoke immediate shifts, because a variable shift whose
count register is a lane-uniform constant **is** that immediate shift,
lane-for-lane. KAT (the external C harness on the emitted `.s`), not a byte-diff
against the immediate form, is the value gate — the `.rodata` broadcast is a
distinct (equivalent) encoding, and `gas` assembles both.

(χ's `¬b` is `b ^ ALLONES` for the same broadcast-constant reason — there is no
packed-NOT `vpackZMM` arm; `ALLONES` is the lane-uniform all-ones broadcast.)

## Value-correctness grounding (REV-12 safe)

Per-step ZMM value correctness is grounded by (1) the small `denote = spec`
characterizations below (each `rfl`: a sub-step `Com.denote` unfolds through the
`vpackZMM` arms to its `zmmPackQ` composite), plus (2) the external C KAT
(`bench/keccak4way_compare/`) that **runs the emitted `.s`** on all lanes against
the official Keccak-f[1600] test vector — NOT an in-kernel multi-round
`native_decide`.

Invoke:
`lake build CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit`
or `lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/Keccak4WayVpackZmmEmit.lean`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
  (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-! ## 0. FIPS 202 constants (lane index `i = x + 5y`)

Re-listed in the linear lane order this emit uses: the ρ offsets of FIPS 202 §3.2.2 and
the 24 ι round constants of Table 2. -/

/-- ρ left-rotation offset for lane `i = x + 5y` (FIPS 202 §3.2.2). -/
def rhoOff : Nat → Nat
  | 0 => 0  | 1 => 1  | 2 => 62 | 3 => 28 | 4 => 27
  | 5 => 36 | 6 => 44 | 7 => 6  | 8 => 55 | 9 => 20
  | 10 => 3 | 11 => 10 | 12 => 43 | 13 => 25 | 14 => 39
  | 15 => 41 | 16 => 45 | 17 => 15 | 18 => 21 | 19 => 8
  | 20 => 18 | 21 => 2 | 22 => 61 | 23 => 56 | 24 => 14
  | _ => 0

/-- The 24 ι round constants `RC[r]` (FIPS 202 Table 2). -/
def roundConst : Nat → Nat
  |  0 => 0x0000000000000001 |  1 => 0x0000000000008082
  |  2 => 0x800000000000808A |  3 => 0x8000000080008000
  |  4 => 0x000000000000808B |  5 => 0x0000000080000001
  |  6 => 0x8000000080008081 |  7 => 0x8000000000008009
  |  8 => 0x000000000000008A |  9 => 0x0000000000000088
  | 10 => 0x0000000080008009 | 11 => 0x000000008000000A
  | 12 => 0x000000008000808B | 13 => 0x800000000000008B
  | 14 => 0x8000000000008089 | 15 => 0x8000000000008003
  | 16 => 0x8000000000008002 | 17 => 0x8000000000000080
  | 18 => 0x000000000000800A | 19 => 0x800000008000000A
  | 20 => 0x8000000080008081 | 21 => 0x8000000000008080
  | 22 => 0x0000000080000001 | 23 => 0x8000000080008008
  |  _ => 0

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-! ## 1. χ AND-NOT sub-step as a `Com jasminDialect` program

The χ lane idiom `out = a ^ ((¬b) ∧ c)`, with `¬b = b ^ ALLONES` (the all-ones
broadcast register). Input context `[a, b, c, allones]` (each `reg 512`, de-Bruijn
`a = 0`, `b = 1`, `c = 2`, `allones = 3`):

```
nb  := vpackZMM xor b allones    -- ¬b      (vpxorq)
mb  := vpackZMM and nb c         -- ¬b ∧ c  (vpandq)
out := vpackZMM xor a mb         -- a ^ (¬b ∧ c)  (vpxorq)
ret out
```
-/

/-- Input context of the χ AND-NOT step: `[a, b, c, allones]`, each `reg 512`. -/
abbrev chiCtx : Ctxt jasminDialect := [r512, r512, r512, r512]

/-- The χ AND-NOT lane step `out = a ^ ((b ^ allones) ∧ c)` as a three-binding
    `Com jasminDialect` over `reg 512` — the dialect-native equivalent of the
    bespoke `chiBlk` per-lane `xor; and; xor` (`¬b ∧ c`, with `¬b = b ^ ALLONES`).
    De-Bruijn: `a = .here`, `b = .there .here`, `c = .there (.there .here)`,
    `allones = .there (.there (.there .here))`. -/
def chiStepCom : Com jasminDialect chiCtx r512 :=
  -- nb := b ^ allones  (b = de Bruijn 1, allones = 3)
  .var (.mk (.vpackZMM .xor) rfl
          (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
    -- mb := nb ∧ c   (nb = 0 now, a=1, b=2, c=3, allones=4)
    (.var (.mk (.vpackZMM .and) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      -- out := a ^ mb   (mb = 0, nb = 1, a = 2)
      (.var (.mk (.vpackZMM .xor) rfl
              (.cons (.there (.there .here)) (.cons .here .nil)))
        (.ret .here)))

/-- **χ AND-NOT denotation pin.** `chiStepCom` denotes to
    `zmmPackQ .xor a (zmmPackQ .and (zmmPackQ .xor b allones) c)` — exactly the
    composite the bespoke `chiBlk` computes per lane (`a ^ (¬b ∧ c)`, `¬b =
    b ^ allones`). The proof is `rfl`: the three `vpackZMM` bindings unfold
    through the `vpackZMM`/`zmmPackQ` denote arm. -/
theorem chiStepCom_denote (a b c allones : BitVec 512) :
    chiStepCom.denote (.cons a (.cons b (.cons c (.cons allones .nil))))
      = zmmPackQ .xor a (zmmPackQ .and (zmmPackQ .xor b allones) c) :=
  rfl

/-! ## 2. ρ rotate-synthesis sub-step as a `Com jasminDialect` program

The ρ per-lane left-rotate `rotl(src, n) = (src <<< n) ||| (src >>> (64-n))`,
realised with the unified per-lane variable shifts `vpsllvq` / `vpsrlvq` whose
count register is a lane-uniform broadcast constant (`cn` = `n` per lane,
`c64mn` = `64-n` per lane). Input context `[src, cn, c64mn]`:

```
hi  := vpackZMM shl src cn      -- src <<< n        (vpsllvq, cn broadcasts n)
lo  := vpackZMM shr src c64mn   -- src >>> (64-n)   (vpsrlvq, c64mn broadcasts 64-n)
out := vpackZMM or  hi lo       -- hi | lo          (vporq)
ret out
```
-/

/-- Input context of the ρ rotate step: `[src, cn, c64mn]`, each `reg 512`
    (`cn` / `c64mn` are the broadcast shift-count constant registers). -/
abbrev rotlCtx : Ctxt jasminDialect := [r512, r512, r512]

/-- The ρ rotate `out = (src <<< cn) ||| (src >>> c64mn)` as a three-binding
    `Com jasminDialect` over `reg 512` — the dialect-native equivalent of the
    bespoke `rotlBlk`'s `shl; shr; or`. The shift counts `cn` / `c64mn` are
    broadcast-constant registers (lane-uniform `n` / `64-n`); a per-lane variable
    shift whose count register is lane-uniform equals the bespoke immediate shift,
    lane-for-lane. De-Bruijn: `src = .here`, `cn = .there .here`,
    `c64mn = .there (.there .here)`. -/
def rotlStepCom : Com jasminDialect rotlCtx r512 :=
  -- hi := src <<< cn   (src = 0, cn = 1)
  .var (.mk (.vpackZMM .shl) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- lo := src >>> c64mn   (hi = 0, src = 1, cn = 2, c64mn = 3)
    (.var (.mk (.vpackZMM .shr) rfl
            (.cons (.there .here) (.cons (.there (.there (.there .here))) .nil)))
      -- out := hi ||| lo   (lo = 0, hi = 1)
      (.var (.mk (.vpackZMM .or) rfl
              (.cons (.there .here) (.cons .here .nil)))
        (.ret .here)))

/-- **ρ rotate denotation pin.** `rotlStepCom` denotes to
    `zmmPackQ .or (zmmPackQ .shl src cn) (zmmPackQ .shr src c64mn)` — the
    `(src <<< cn) ||| (src >>> c64mn)` composite, the dialect image of the bespoke
    `rotlBlk`. When `cn` / `c64mn` broadcast `n` / `64-n`, this is the per-lane
    left-rotate by `n`. The proof is `rfl`. -/
theorem rotlStepCom_denote (src cn c64mn : BitVec 512) :
    rotlStepCom.denote (.cons src (.cons cn (.cons c64mn .nil)))
      = zmmPackQ .or (zmmPackQ .shl src cn) (zmmPackQ .shr src c64mn) :=
  rfl

/-! ## 3. ι round-constant XOR sub-step as a `Com jasminDialect` program

The ι step `A[0,0] ^= RC[r]`, with `RC[r]` a broadcast-constant register. Input
context `[s0, rc]`:

```
out := vpackZMM xor s0 rc      -- s0 ^ RC[r]   (vpxorq)
ret out
```
-/

/-- Input context of the ι step: `[s0, rc]`, each `reg 512` (`rc` = broadcast
    round-constant register). -/
abbrev iotaCtx : Ctxt jasminDialect := [r512, r512]

/-- The ι step `out = s0 ^ rc` as a single `vpackZMM .xor` binding — the
    dialect-native equivalent of the bespoke `iotaBlk`'s lone `.xor S0 RCr`.
    De-Bruijn: `s0 = .here`, `rc = .there .here`. -/
def iotaStepCom : Com jasminDialect iotaCtx r512 :=
  .var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **ι denotation pin.** `iotaStepCom` denotes to `zmmPackQ .xor s0 rc` — the
    bespoke `iotaBlk`'s `A[0,0] ^= RC[r]` per lane. The proof is `rfl`. -/
theorem iotaStepCom_denote (s0 rc : BitVec 512) :
    iotaStepCom.denote (.cons s0 (.cons rc .nil)) = zmmPackQ .xor s0 rc :=
  rfl

/-! ## 4. θ diffusion sub-step as a `Com jasminDialect` program

The θ column-mix XOR tree for one column `C[x] = ⊕_y A[x,y]`, the four-fold XOR
the bespoke `thetaBlk` issues. Input context `[a0, a1, a2, a3, a4]`:

```
t1 := vpackZMM xor a0 a1
t2 := vpackZMM xor t1 a2
t3 := vpackZMM xor t2 a3
c  := vpackZMM xor t3 a4
ret c
```
-/

/-- Input context of the θ column-parity step: `[a0, a1, a2, a3, a4]`, each
    `reg 512`. -/
abbrev thetaCtx : Ctxt jasminDialect := [r512, r512, r512, r512, r512]

/-- The θ column-parity XOR tree `C[x] = a0 ^ a1 ^ a2 ^ a3 ^ a4` as a four-binding
    `Com jasminDialect` over `reg 512` — the dialect-native equivalent of the
    bespoke `thetaBlk`'s per-column `.xor` chain (left-associated). De-Bruijn:
    `a0 = .here`, `a1 = .there .here`, …, `a4 = .there^4 .here`. -/
def thetaColCom : Com jasminDialect thetaCtx r512 :=
  -- t1 := a0 ^ a1
  .var (.mk (.vpackZMM .xor) rfl
          (.cons .here (.cons (.there .here) .nil)))
    -- t2 := t1 ^ a2   (t1=0, a0=1, a1=2, a2=3, a3=4, a4=5)
    (.var (.mk (.vpackZMM .xor) rfl
            (.cons .here (.cons (.there (.there (.there .here))) .nil)))
      -- t3 := t2 ^ a3  (t2=0, t1=1, a0=2, a1=3, a2=4, a3=5, a4=6)
      (.var (.mk (.vpackZMM .xor) rfl
              (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
        -- c := t3 ^ a4  (t3=0, t2=1, t1=2, a0=3, a1=4, a2=5, a3=6, a4=7)
        (.var (.mk (.vpackZMM .xor) rfl
                (.cons .here
                  (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
          (.ret .here))))

set_option maxHeartbeats 1000000 in
/-- **θ column-parity denotation pin.** `thetaColCom` denotes to the
    left-associated XOR fold `((((a0 ⊕ a1) ⊕ a2) ⊕ a3) ⊕ a4)` over `zmmPackQ .xor`
    — the bespoke `thetaBlk`'s per-column `C[x]`. The proof is `rfl` (the
    five-input fold needs a raised heartbeat budget for the `whnf` reduction). -/
theorem thetaColCom_denote (a0 a1 a2 a3 a4 : BitVec 512) :
    thetaColCom.denote (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil)))))
      = zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor a0 a1) a2) a3) a4 :=
  rfl

/-! ## 5. Rendered body lines + denote-faithful `.s` for each sub-step

Each sub-step renders through `renderVpackZmmCom` to its owned AT&T `%zmm` lines.
AT&T EVEX order is `op src2, src1, dst`. -/

/-- `%zmm` allocation for the χ AND-NOT step: params `a/b/c/allones` → `%zmm0..3`,
    `nb` → `%zmm4`, `mb` → `%zmm4` (reused), `out` → `%zmm0`. -/
def chiAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
   ("v0", "%zmm4"), ("v1", "%zmm4"), ("v2", "%zmm0")]

/-- The χ AND-NOT body renders to exactly its three owned AT&T `%zmm` lines
    (`vpxorq` ¬b, `vpandq` ¬b∧c, `vpxorq` a^…). -/
theorem chi_body_lines :
    (renderVpackZmmCom chiAlloc chiStepCom).1
      = [ "\tvpxorq %zmm3, %zmm1, %zmm4"
        , "\tvpandq %zmm2, %zmm4, %zmm4"
        , "\tvpxorq %zmm4, %zmm0, %zmm0" ] := by
  native_decide

/-- `%zmm` allocation for the ρ rotate step: params `src/cn/c64mn` → `%zmm0..2`,
    `hi` → `%zmm3`, `lo` → `%zmm4`, `out` → `%zmm0`. -/
def rotlAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"),
   ("v0", "%zmm3"), ("v1", "%zmm4"), ("v2", "%zmm0")]

/-- The ρ rotate body renders to exactly its three owned AT&T `%zmm` lines
    (`vpsllvq` src<<<cn, `vpsrlvq` src>>>c64mn, `vporq` hi|lo). -/
theorem rotl_body_lines :
    (renderVpackZmmCom rotlAlloc rotlStepCom).1
      = [ "\tvpsllvq %zmm1, %zmm0, %zmm3"
        , "\tvpsrlvq %zmm2, %zmm0, %zmm4"
        , "\tvporq %zmm4, %zmm3, %zmm0" ] := by
  native_decide

/-- `%zmm` allocation for the ι step: params `s0/rc` → `%zmm0/1`, `out` → `%zmm0`. -/
def iotaAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("v0", "%zmm0")]

/-- The ι body renders to its single owned AT&T `%zmm` line (`vpxorq` s0^rc). -/
theorem iota_body_lines :
    (renderVpackZmmCom iotaAlloc iotaStepCom).1
      = [ "\tvpxorq %zmm1, %zmm0, %zmm0" ] := by
  native_decide

/-- `%zmm` allocation for the θ column step: params `a0..a4` → `%zmm0..4`, the
    XOR-fold temps `t1/t2/t3`/`c` reuse `%zmm0`. -/
def thetaAlloc : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
   ("p4", "%zmm4"),
   ("v0", "%zmm0"), ("v1", "%zmm0"), ("v2", "%zmm0"), ("v3", "%zmm0")]

/-- The θ column body renders to its four owned AT&T `%zmm` lines (the XOR fold). -/
theorem theta_body_lines :
    (renderVpackZmmCom thetaAlloc thetaColCom).1
      = [ "\tvpxorq %zmm1, %zmm0, %zmm0"
        , "\tvpxorq %zmm2, %zmm0, %zmm0"
        , "\tvpxorq %zmm3, %zmm0, %zmm0"
        , "\tvpxorq %zmm4, %zmm0, %zmm0" ] := by
  native_decide

/-! ## 6. The framed owned `.s` for one packed θρπχι round op-block

We frame the four sub-steps (θ column, ρ rotate, χ AND-NOT, ι) under one export
symbol `keccak_f1600_round_vpackzmm`, with SysV-ABI load/store glue. The state
lanes and the broadcast constants (`ALLONES`, the per-`n` rotate-count `.rodata`
broadcasts, the round constant) are loaded into `%zmm` registers by the driver
(the `vmovdqa64 c_X(%rip), %zmm` idiom of the bespoke driver), the same trust
class as the prologue loads. -/

/-- The framed owned `.s` for the χ AND-NOT op-block, symbol
    `keccak_chi_vpackzmm`. `a/b/c` from `(%rsi)`/`64(%rsi)`/`128(%rsi)`,
    `allones` broadcast from `.rodata`, result to `(%rdi)`. -/
def chiExportAsm : String :=
  frameAsmFunction "keccak_chi_vpackzmm"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqu64\t64(%rsi), %zmm1"
    , "\tvmovdqu64\t128(%rsi), %zmm2"
    , "\tvmovdqa64\tc_ALLONES(%rip), %zmm3" ]
    (renderVpackZmmCom chiAlloc chiStepCom).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The framed owned `.s` for the ρ rotate op-block (for offset `n = 1`, the θ
    `rotl(C, 1)` and a representative ρ lane), symbol `keccak_rotl_vpackzmm`. The
    shift-count broadcasts `c_rot_n` / `c_rot_64mn` come from `.rodata`. -/
def rotlExportAsm (n : Nat) : String :=
  frameAsmFunction "keccak_rotl_vpackzmm"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqa64\tc_rot_" ++ toString n ++ "(%rip), %zmm1"
    , "\tvmovdqa64\tc_rot_" ++ toString (64 - n) ++ "(%rip), %zmm2" ]
    (renderVpackZmmCom rotlAlloc rotlStepCom).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The framed owned `.s` for the ι op-block (round `r`), symbol
    `keccak_iota_vpackzmm`. The round-constant broadcast `c_RCr` comes from
    `.rodata`. -/
def iotaExportAsm (r : Nat) : String :=
  frameAsmFunction "keccak_iota_vpackzmm"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqa64\tc_RC" ++ toString r ++ "(%rip), %zmm1" ]
    (renderVpackZmmCom iotaAlloc iotaStepCom).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The framed owned `.s` for the θ column-parity op-block, symbol
    `keccak_theta_vpackzmm`. The five column lanes come from `(%rsi)` …
    `256(%rsi)`. -/
def thetaExportAsm : String :=
  frameAsmFunction "keccak_theta_vpackzmm"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqu64\t64(%rsi), %zmm1"
    , "\tvmovdqu64\t128(%rsi), %zmm2"
    , "\tvmovdqu64\t192(%rsi), %zmm3"
    , "\tvmovdqu64\t256(%rsi), %zmm4" ]
    (renderVpackZmmCom thetaAlloc thetaColCom).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The full owned `.s` for the packed θρπχι sub-step op-blocks (all four
    framed functions concatenated), the dialect-native twin of the bespoke
    `Avx512Model`-rendered Keccak emit. -/
def keccak_round_vpackzmm_asm : String :=
  "# Lane-sliced Keccak-f[1600] θρπχι sub-step op-blocks, owned Com vpackZMM emit.\n"
  ++ "# No Avx512Model, no jasminc — rendered by VpackZmmAsmPrint.renderVpackZmmCom.\n"
  ++ thetaExportAsm ++ "\n"
  ++ rotlExportAsm 1 ++ "\n"
  ++ chiExportAsm ++ "\n"
  ++ iotaExportAsm 0 ++ "\n"

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println keccak_round_vpackzmm_asm

/-! ## 7. Structural smoke pins on the emitted `.s` text

These reproduce the pre-migration emit's posture (the packed alphabet present, no
UPPERCASE jasmin intrinsic, 512-bit `%zmm`), now over the `Com`-rendered `.s`. -/

/- The emit issues the packed XOR (θ/χ/ι, lowercase owned `%zmm` mnemonic). -/
#guard (strContains keccak_round_vpackzmm_asm "vpxorq")

/- The emit issues the packed AND (χ `¬b ∧ c`). -/
#guard (strContains keccak_round_vpackzmm_asm "vpandq")

/- The emit issues the packed OR (ρ rotate `hi | lo`). -/
#guard (strContains keccak_round_vpackzmm_asm "vporq")

/- The emit issues the per-lane variable left shift (ρ `src <<< n`,
    broadcast-count). -/
#guard (strContains keccak_round_vpackzmm_asm "vpsllvq")

/- The emit issues the per-lane variable right shift (ρ `src >>> (64-n)`). -/
#guard (strContains keccak_round_vpackzmm_asm "vpsrlvq")

/- The body uses 512-bit `%zmm` registers. -/
#guard (strContains keccak_round_vpackzmm_asm "%zmm")

/- No UPPERCASE jasmin intrinsic survives — the owned (no-jasminc) path. -/
#guard !(strContains keccak_round_vpackzmm_asm "#VPADD_8u64")

/- The export symbols are present. -/
#guard (strContains keccak_round_vpackzmm_asm "keccak_theta_vpackzmm:")
    && (strContains keccak_round_vpackzmm_asm "keccak_chi_vpackzmm:")

/-! ## 8. Emit driver -/

/-- Write the owned-backend (`Com`-rendered AVX-512 ZMM) Keccak θρπχι sub-step
    `.s` to `bench/keccak4way_compare/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak4way_compare/gen_com"
  IO.FS.writeFile "bench/keccak4way_compare/gen_com/keccak_round_vpackzmm.s"
    keccak_round_vpackzmm_asm
  IO.println "wrote bench/keccak4way_compare/gen_com/keccak_round_vpackzmm.s (owned Com vpackZMM θρπχι sub-steps)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit in
/-- `lake env lean --run` entry point: emit the owned `Com`-rendered Keccak
    θρπχι sub-step op-blocks. -/
private def main : IO Unit := emit
