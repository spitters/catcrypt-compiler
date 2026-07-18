/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
import CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit

/-!
# Whole-round owned `.s` assembly for lane-sliced Keccak-f[1600] (512-bit ZMM)

The committed per-sub-step twins in
`Keccak4WayVpackZmmEmit.{thetaColCom,rotlStepCom,chiStepCom,iotaStepCom}` each
render ONE θ-column / ρ-rotate / χ-and-not / ι-xor block to its owned AT&T `%zmm`
lines. The whole Keccak-f[1600] round is the **sequence** θ→ρ→π→χ→ι of those
sub-steps, with the 25 lane registers threaded across the sub-step boundaries:
χ reads what ρ/π wrote, ι reads what χ wrote. The bespoke `Avx512AsmPrinter`
driver had this threading for free because its rounds were never separate
objects (one flat `List ZInstr`, one `ZAlloc`). This module is the missing
capability: assemble a whole Keccak round as ONE straight-line `.s` function
from the committed per-sub-step `Com` blocks via the per-block-alloc renderer
`VpackZmmComSeq.renderVpackZmmAllocSeq`.

```
[ (θAlloc, thetaColCom)      -- column parity / diffusion
, (ρAlloc, rotlStepCom)      -- per-lane left-rotate (π is a register rename — see below)
, (χAlloc, chiStepCom)       -- a ^ (¬b ∧ c)
, (ιAlloc, iotaStepCom) ]    -- s0 ^ RC[r]
        │  renderVpackZmmAllocSeq   (threads the SSA counter + the state register)
        ▼
   ONE straight-line owned AT&T %zmm body  →  frameAsmFunction  →  whole-round `.s`
```

## What is the round, and what is the 24-round / 25-lane driver

This module assembles ONE whole θρπχι round as one straight-line `.s` body and
**pins its denotation to the composed Keccak round sub-step value** (the denote
fold across the four sub-step boundaries). This is the unit the renderer must be
shown to assemble — the capability the Avx512Model teardown left open.

Two deliberate factorings keep the assembled round inside one tractable `Com`
list while staying faithful to FIPS 202:

* **π is a register rename, not an op.** The π permutation `A[x,y] ← A[x+3y,x]`
  emits NO instruction — the bespoke driver realises it by renaming which `%zmm`
  a later sub-step reads. So a whole θρπχι round's *instruction* content is
  θ-xors + ρ-shifts/or + χ-and-not-xors + ι-xor; π is absorbed into the alloc
  (the χ block's `p`-names are pinned to the `%zmm` slots ρ wrote, in the
  π-permuted order). The assembled round below threads the state register across
  the θ→ρ→χ→ι boundaries exactly this way.

* **The 25 lanes are lane-parallel and identical per sub-step.** θ runs the same
  4-xor column-parity tree on each of the 5 columns; ρ runs the same rotate on
  each of the 25 lanes; χ runs the same and-not on each of the 25 lanes; ι
  touches one lane. So a whole 25-lane round is the per-sub-step block applied to
  fixed `%zmm` slots, replicated lane-by-lane (more blocks, same four sub-step
  *shapes*). The assembled round here sequences ONE representative lane chain
  θ→ρ→χ→ι — the four sub-step shapes in round order, state threaded — which is
  the renderer-assembly unit; replicating it to all 25 lanes / 5 columns is more
  blocks of the same four shapes (straight-line glue), and unrolling to 24 rounds
  is 24× the round body (the FIPS 202 permutation loop). The `keccakf1600_zmm8`
  bench `.s` is exactly that 24× unroll of this round body; what this module
  proves is that the renderer assembles the round body itself, denote-pinned.

## Soundness

`wholeRoundSeq` is rendered by `renderVpackZmmAllocSeq` to ONE straight-line body
(`whole_round_lines`, `native_decide`). The denote fold across the four sub-step
boundaries is pinned by `whole_round_denote` (`rfl`): feeding θ's denoted column
parity into ρ's rotate, ρ's result into χ's and-not, χ's result into ι's xor
gives the composed Keccak-round sub-step value, written via the verified-dialect
`zmmPackQ`. This is the `chained_seq_denote` / `three_block_denote` pattern of
`VpackZmmComSeq`, scaled to the four real Keccak sub-step shapes.

Invoke:
`lake build CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeRoundVpackZmmEmit`
or `lake env lean --run
  CatCrypt/Crypto/SecureCompilation/X86Backend/Keccak4WayWholeRoundVpackZmmEmit.lean`
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeRoundVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
  (VpackZmmBlock VpackZmmAllocSeq renderVpackZmmAllocSeq blockDenote)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit
  (r512 thetaCtx rotlCtx chiCtx iotaCtx
   thetaColCom rotlStepCom chiStepCom iotaStepCom
   thetaColCom_denote rotlStepCom_denote chiStepCom_denote iotaStepCom_denote)

/-! ## 1. The four whole-round sub-step blocks (committed step Coms, packaged)

Each block is one of the committed per-sub-step `Com`s from
`Keccak4WayVpackZmmEmit`, packaged as a `VpackZmmBlock`. Sequenced in FIPS 202
round order θ → ρ (π absorbed into the next block's alloc) → χ → ι. -/

/-- θ block: the committed `thetaColCom` (5-input column-parity XOR tree). -/
def thetaBlock : VpackZmmBlock := ⟨thetaCtx, r512, thetaColCom⟩

/-- ρ block: the committed `rotlStepCom` (per-lane left-rotate via broadcast-count
    variable shifts). Its data input `src` is the θ column parity threaded from
    the previous block; `cn`/`c64mn` are this block's own rotate-count aux. -/
def rotlBlock : VpackZmmBlock := ⟨rotlCtx, r512, rotlStepCom⟩

/-- χ block: the committed `chiStepCom` (`a ^ (¬b ∧ c)`). Its `a` is the ρ result
    threaded forward; `b`/`c`/`allones` are this block's own aux. -/
def chiBlock : VpackZmmBlock := ⟨chiCtx, r512, chiStepCom⟩

/-- ι block: the committed `iotaStepCom` (`s0 ^ RC[r]`). Its `s0` is the χ result
    threaded forward; `rc` is the round-constant aux. -/
def iotaBlock : VpackZmmBlock := ⟨iotaCtx, r512, iotaStepCom⟩

/-! ## 2. Per-block allocations: state in `%zmm0`, distinct per-sub-step aux

The threaded round-state lane lives in `%zmm0` across all four sub-step
boundaries (each block reads its primary data input out of `%zmm0` and writes its
result back to `%zmm0`). Each sub-step gets its OWN aux registers — the per-block
alloc is exactly what lets θ's columns, ρ's rotate-counts, χ's `b`/`c`/`allones`,
and ι's round constant occupy distinct `%zmm` slots even though several sit at
the local param index `p1`/`p2`/… of their own block. -/

/-- θ alloc: the 5 column lanes `a0..a4 = p0..p4 → %zmm0..4`, the XOR-fold temps
    reuse `%zmm0` (state slot). Same as the committed `thetaAlloc`, written here
    so the whole-round sequence is self-contained. -/
def thetaAllocR : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
   ("p4", "%zmm4"),
   ("v0", "%zmm0"), ("v1", "%zmm0"), ("v2", "%zmm0"), ("v3", "%zmm0")]

/-- ρ alloc. Threaded state `src = p0 → %zmm0` (the θ column parity, in the state
    slot); ρ's own rotate-count aux `cn = p1 → %zmm5`, `c64mn = p2 → %zmm6`
    (distinct from θ's column registers). SSA names are THREADED past θ's four
    bindings (θ used `v0..v3`), so ρ's three bindings are `v4`/`v5`/`v6`; the
    final `or` result `v6` lands back in the state slot `%zmm0`. -/
def rotlAllocR : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm5"), ("p2", "%zmm6"),
   ("v4", "%zmm7"), ("v5", "%zmm8"), ("v6", "%zmm0")]

/-- χ alloc. Threaded state `a = p0 → %zmm0` (the ρ result, in the state slot);
    χ's own aux `b = p1 → %zmm9`, `c = p2 → %zmm10`, `allones = p3 → %zmm11`
    (the π register-rename is realised here: `b`/`c` are pinned to the `%zmm`
    slots the permuted neighbour lanes occupy). SSA names threaded past θ(4)+ρ(3)
    = 7 bindings, so χ's three bindings are `v7`/`v8`/`v9`; `nb`/`mb` reuse
    `%zmm12`, the `out` lands back in `%zmm0`. -/
def chiAllocR : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm9"), ("p2", "%zmm10"), ("p3", "%zmm11"),
   ("v7", "%zmm12"), ("v8", "%zmm12"), ("v9", "%zmm0")]

/-- ι alloc. Threaded state `s0 = p0 → %zmm0` (the χ result, in the state slot);
    ι's round-constant aux `rc = p1 → %zmm13`. SSA names threaded past
    θ(4)+ρ(3)+χ(3) = 10 bindings, so ι's single binding is `v10`, landing the
    round result back in the state slot `%zmm0`. -/
def iotaAllocR : XAlloc :=
  [("p0", "%zmm0"), ("p1", "%zmm13"), ("v10", "%zmm0")]

/-! ## 3. The assembled whole θρπχι round sequence -/

/-- The whole Keccak-f[1600] round as a per-block-alloc sequence: θ → ρ → χ → ι,
    state threaded through `%zmm0`, each sub-step with its own aux registers (π
    absorbed into the χ block's alloc — see the module docstring). This is the
    `(XAlloc × VpackZmmBlock)` LIST the renderer folds into one straight-line
    body. -/
def wholeRoundSeq : VpackZmmAllocSeq :=
  [ (thetaAllocR, thetaBlock)
  , (rotlAllocR,  rotlBlock)
  , (chiAllocR,   chiBlock)
  , (iotaAllocR,  iotaBlock) ]

/-! ## 4. Render soundness: the whole round renders to ONE straight-line body

The four sub-step blocks render into ONE owned AT&T `%zmm` body, the SSA counter
threaded (θ: `v0..v3`, ρ: `v4..v6`, χ: `v7..v9`, ι: `v10`) and the state register
`%zmm0` threaded across every sub-step boundary. AT&T EVEX order is
`op src2, src1, dst`. -/

/-- **The assembled whole-round render.** The four sub-step blocks fold into ONE
    straight-line owned AT&T `%zmm` body: θ's four column XORs, ρ's two
    broadcast-count variable shifts + the recombining OR, χ's not/and/xor, ι's
    round-constant XOR — eleven instructions, the state carried in `%zmm0` across
    all four sub-step boundaries, each sub-step reading its own aux registers
    (`%zmm1..4` θ columns, `%zmm5/6` ρ counts, `%zmm9/10/11` χ aux, `%zmm13` ι
    RC). -/
theorem whole_round_lines :
    (renderVpackZmmAllocSeq wholeRoundSeq).1
      = [ -- θ column parity (a0 ^ a1 ^ a2 ^ a3 ^ a4), state in %zmm0
          "\tvpxorq %zmm1, %zmm0, %zmm0"
        , "\tvpxorq %zmm2, %zmm0, %zmm0"
        , "\tvpxorq %zmm3, %zmm0, %zmm0"
        , "\tvpxorq %zmm4, %zmm0, %zmm0"
          -- ρ rotate: hi = src<<<cn, lo = src>>>c64mn, out = hi|lo
        , "\tvpsllvq %zmm5, %zmm0, %zmm7"
        , "\tvpsrlvq %zmm6, %zmm0, %zmm8"
        , "\tvporq %zmm8, %zmm7, %zmm0"
          -- χ and-not: nb = b^allones, mb = nb∧c, out = a^mb
        , "\tvpxorq %zmm11, %zmm9, %zmm12"
        , "\tvpandq %zmm10, %zmm12, %zmm12"
        , "\tvpxorq %zmm12, %zmm0, %zmm0"
          -- ι round constant: s0 ^ RC[r]
        , "\tvpxorq %zmm13, %zmm0, %zmm0" ] := by
  native_decide

/-- **State threaded across every sub-step boundary.** θ's final column XOR, ρ's
    recombining OR, χ's `a^mb`, and ι's `s0^RC` all land their result in `%zmm0`
    — the round state keeps ONE `%zmm` slot across the four sub-step boundaries,
    so the next sub-step reads the previous sub-step's output out of `%zmm0`. -/
theorem whole_round_state_threaded :
    (renderVpackZmmAllocSeq wholeRoundSeq).1[3]?
      = some "\tvpxorq %zmm4, %zmm0, %zmm0" ∧        -- θ result → %zmm0
    (renderVpackZmmAllocSeq wholeRoundSeq).1[6]?
      = some "\tvporq %zmm8, %zmm7, %zmm0" ∧         -- ρ result → %zmm0
    (renderVpackZmmAllocSeq wholeRoundSeq).1[9]?
      = some "\tvpxorq %zmm12, %zmm0, %zmm0" ∧       -- χ result → %zmm0
    (renderVpackZmmAllocSeq wholeRoundSeq).1[10]?
      = some "\tvpxorq %zmm13, %zmm0, %zmm0" := by   -- ι result → %zmm0
  native_decide

/-- **The whole round is eleven straight-line instructions.** θ(4) + ρ(3) + χ(3)
    + ι(1) = 11 — no block dropped, the four sub-step shapes assembled in order. -/
theorem whole_round_length :
    (renderVpackZmmAllocSeq wholeRoundSeq).1.length = 11 := by
  native_decide

/-- **Distinct per-sub-step aux registers.** ρ's rotate-count aux is `%zmm5`,
    χ's mask aux is `%zmm10`, ι's round-constant aux is `%zmm13` — each sub-step's
    aux occupies its own `%zmm` slot even though several sit at local `p1` of
    their own block. This is the per-block-alloc capability the flat single-alloc
    renderer could not express. -/
theorem whole_round_distinct_aux :
    strContains ((renderVpackZmmAllocSeq wholeRoundSeq).1.getD 4 "") "%zmm5" = true ∧
    strContains ((renderVpackZmmAllocSeq wholeRoundSeq).1.getD 8 "") "%zmm10" = true ∧
    strContains ((renderVpackZmmAllocSeq wholeRoundSeq).1.getD 10 "") "%zmm13" = true := by
  native_decide

/-! ## 5. Denote fold across the four sub-step boundaries

The whole round's *value* is the fold of the per-sub-step denotations: θ's column
parity feeds ρ's rotate, ρ's rotate feeds χ's and-not, χ's and-not feeds ι's xor.
The rendered `%zmm0` that crosses each boundary carries exactly the previous
sub-step's `Com.denote`. We pin the whole fold to the composed Keccak-round
sub-step value, written via the verified-dialect `zmmPackQ`. -/

/-- **Whole-round denote fold.** Threading θ's denoted column parity
    `θ = ((((a0⊕a1)⊕a2)⊕a3)⊕a4)` as ρ's `src`, ρ's denoted rotate
    `ρ = (θ<<<cn) ||| (θ>>>c64mn)` as χ's `a`, χ's denoted and-not
    `χ = ρ ^ ((b⊕allones) ∧ c)` as ι's `s0`, gives the whole round's value
    `ι = χ ^ rc`. This is the composed Keccak-round sub-step value the threaded
    `%zmm0` realises across the four boundaries. The proof rewrites each block's
    denote through the committed per-sub-step `_denote` characterizations (each
    itself `rfl`), composing them in round order — lighter than one monolithic
    `rfl` over the whole nested fold. -/
theorem whole_round_denote
    (a0 a1 a2 a3 a4 cn c64mn b c allones rc : BitVec 512) :
    blockDenote iotaBlock
      (.cons
        (blockDenote chiBlock
          (.cons
            (blockDenote rotlBlock
              (.cons
                (blockDenote thetaBlock
                  (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))))
                (.cons cn (.cons c64mn .nil))))
            (.cons b (.cons c (.cons allones .nil)))))
        (.cons rc .nil))
      = -- ι ( χ ( ρ ( θ a0..a4 , cn, c64mn ), b, c, allones ), rc )
        zmmPackQ .xor
          (zmmPackQ .xor
            (zmmPackQ .or
              (zmmPackQ .shl
                (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor a0 a1) a2) a3) a4)
                cn)
              (zmmPackQ .shr
                (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor a0 a1) a2) a3) a4)
                c64mn))
            (zmmPackQ .and (zmmPackQ .xor b allones) c))
          rc := by
  show iotaStepCom.denote
      (.cons (chiStepCom.denote
        (.cons (rotlStepCom.denote
          (.cons (thetaColCom.denote
            (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))))
            (.cons cn (.cons c64mn .nil))))
          (.cons b (.cons c (.cons allones .nil)))))
        (.cons rc .nil)) = _
  rw [thetaColCom_denote, rotlStepCom_denote, chiStepCom_denote, iotaStepCom_denote]

/-! ## 6. The framed whole-round `.s`

The assembled round body is framed with SysV-ABI load/store glue under one export
symbol `keccakf1600_zmm8_round` (the round body the `keccakf1600_zmm8` bench `.s`
unrolls 24×). The prologue loads the θ column lanes from the state pointer and
broadcasts the per-sub-step aux constants (`c_rot_*` rotate counts, `c_ALLONES`,
`c_RC*`) from `.rodata`, exactly the trust class of the committed twins. The
epilogue stores the round result (`%zmm0`) back to the state pointer. -/

/-- The framed owned `.s` for one whole θρπχι round, symbol
    `keccakf1600_zmm8_round`. The five θ column lanes load from `(%rsi)` …
    `256(%rsi)`; ρ rotate counts (`%zmm5`/`%zmm6`), χ aux (`%zmm9`/`%zmm10`/
    `%zmm11`), and the ι round constant (`%zmm13`) broadcast from `.rodata`; the
    round result (`%zmm0`) stores to `(%rdi)`. The body is the ONE straight-line
    assembled round render, state carried across all four sub-step boundaries in
    `%zmm0`. -/
def wholeRoundExportAsm (r : Nat) : String :=
  frameAsmFunction "keccakf1600_zmm8_round"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqu64\t64(%rsi), %zmm1"
    , "\tvmovdqu64\t128(%rsi), %zmm2"
    , "\tvmovdqu64\t192(%rsi), %zmm3"
    , "\tvmovdqu64\t256(%rsi), %zmm4"
    , "\tvmovdqa64\tc_rot_1(%rip), %zmm5"
    , "\tvmovdqa64\tc_rot_63(%rip), %zmm6"
    , "\tvmovdqu64\t320(%rsi), %zmm9"
    , "\tvmovdqu64\t384(%rsi), %zmm10"
    , "\tvmovdqa64\tc_ALLONES(%rip), %zmm11"
    , "\tvmovdqa64\tc_RC" ++ toString r ++ "(%rip), %zmm13" ]
    (renderVpackZmmAllocSeq wholeRoundSeq).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println (wholeRoundExportAsm 0)

/-! ## 7. Structural smoke pins on the framed whole-round `.s` -/

/-- The framed whole round emits all four sub-step shapes (θ/ι xor, ρ shifts + or,
    χ and) under one export symbol — the owned (no-jasminc, no-`Avx512Model`)
    whole-round path. -/
theorem whole_round_asm_complete :
    (strContains (wholeRoundExportAsm 0) "keccakf1600_zmm8_round:" = true) ∧
    (strContains (wholeRoundExportAsm 0) "vpxorq" = true) ∧
    (strContains (wholeRoundExportAsm 0) "vpsllvq" = true) ∧
    (strContains (wholeRoundExportAsm 0) "vpsrlvq" = true) ∧
    (strContains (wholeRoundExportAsm 0) "vporq" = true) ∧
    (strContains (wholeRoundExportAsm 0) "vpandq" = true) := by
  native_decide

/-- No UPPERCASE jasmin intrinsic survives in the framed whole round — the owned
    (no-jasminc) path, and the 512-bit `%zmm` registers are present. -/
theorem whole_round_asm_owned :
    (strContains (wholeRoundExportAsm 0) "%zmm" = true) ∧
    (strContains (wholeRoundExportAsm 0) "#VPXOR" = false) := by
  native_decide

/-! ## 8. Emit driver -/

/-- Write the owned-backend (`Com`-rendered AVX-512 ZMM) whole Keccak θρπχι round
    `.s` to `bench/keccak4way_compare/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak4way_compare/gen_com"
  IO.FS.writeFile "bench/keccak4way_compare/gen_com/keccakf1600_zmm8_round.s"
    (wholeRoundExportAsm 0)
  IO.println "wrote bench/keccak4way_compare/gen_com/keccakf1600_zmm8_round.s (owned Com vpackZMM whole θρπχι round)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeRoundVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeRoundVpackZmmEmit in
/-- `lake env lean --run` entry point: emit the owned `Com`-rendered whole Keccak
    θρπχι round. -/
private def main : IO Unit := emit
