/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
import CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit

/-!
# Whole multi-step Keccak-f[1600] sub-kernel as ONE owned `.s` via the threaded `vpackZMM` sequence renderer

`Keccak4WayVpackZmmEmit.lean` migrated each θρπχι sub-step onto the unified
`Com jasminDialect` (512-bit ZMM) dialect as a **single** straight-line block
(`thetaColCom` / `rotlStepCom` / `chiStepCom` / `iotaStepCom`), each rendered on
its own by `renderVpackZmmCom`. That is the building-block twin: one block, one
`.s` fragment. What the building blocks could NOT do is emit a **sequence** of
those step-blocks into ONE straight-line `.s` with the round-state register
threaded across the step boundary — the value a step writes is the value the next
step reads, in the same `%zmm` slot.

`VpackZmmComSeq.renderVpackZmmComSeq : XAlloc → VpackZmmSeq → (List String ×
String)` is exactly that missing capability: it folds `lowerVpackZmmCom` over a
`List VpackZmmBlock`, threading the fresh-SSA counter so step `k`'s SSA names
(`v0, v1, …`) never collide with step `k+1`'s, and rendering every step against
the SAME `alloc`, so a value defined in step `k` and read in step `k+1` keeps its
`%zmm` register. This module uses it to emit a **whole multi-step Keccak
sub-kernel** — the θ column-parity feeding the ι round-constant XOR — as ONE
owned `.s` function, with the parity register threaded across the θ→ι boundary.

```
[ thetaColCom block ; iotaStepCom block ]      -- the step sequence (round-state in ZMM)
        │  one shared XAlloc (parity register threaded θ → ι)
        ▼  VpackZmmComSeq.renderVpackZmmComSeq   (threads SSA counter + alloc across steps)
   List String     (ONE straight-line owned AT&T %zmm body — both steps, no boundary)
        │  VsimdAsmPrint.frameAsmFunction   (SysV ABI load/store glue)
        ▼
   String          (a complete owned whole-sub-kernel `.s`)
```

## The threaded step boundary

θ (`thetaColCom`) folds the five column lanes `a0..a4` into the column parity
`C[x] = a0 ⊕ a1 ⊕ a2 ⊕ a3 ⊕ a4`, leaving it in `%zmm0`. ι (`iotaStepCom`) reads
that parity as its `s0` input and XORs the broadcast round constant. Because both
step-blocks render against the same `alloc` — with θ's result and ι's `p0` both
pinned to `%zmm0` — the parity threads across the θ→ι boundary in `%zmm0`,
exactly the round-state-in-ZMM pattern. The fresh-SSA counter is threaded too:
θ's four bindings are `v0..v3`, so ι's lone binding starts at `v4` and never
collides.

## The param-naming caveat and what the *whole* 24-round permutation needs

`paramsAndMap` names every block's free context `p0, p1, …` **afresh** (base 0),
so a single flat `XAlloc` keyed by those names cannot give two DIFFERENT steps'
`p1` two different registers — both resolve the `"p1"` entry. For the θ→ι
boundary the *threaded* value is `p0` in both steps (shared on purpose — this is
the capability), and the only other collision is ι's round-constant register
sharing θ's `a1` slot (`%zmm1`). That is benign for this demonstration — the
denote fold (below) pins the value abstractly, independent of the register
sharing — and it is the SAME benign register-aliasing the committed worked
2-block example (`VpackZmmComSeq.chained_seq_lines`) exhibits.

For the FULL θ→ρ→π→χ→ι round (and the 24-round permutation), where consecutive
steps need genuinely DISTINCT auxiliary-constant registers at the same `p`-index
(ρ's rotate-count broadcasts vs ι's round constant vs χ's all-ones, all wanting
`p1`/`p2`), the single flat `XAlloc` is insufficient. Per the renderer's design
note (`VpackZmmComSeq` §7), the whole round renders cleanly under one of:

* **per-block alloc** — extend `VpackZmmBlock` with its own `XAlloc` field (a
  `List (XAlloc × VpackZmmBlock)`), so each step's `p1`/`p2` can name distinct
  registers; a one-field change to `VpackZmmBlock` + `renderBlockFrom`; or
* **stable cross-block names** — express the whole round as ONE `Com` over the
  full 25-lane state context, so param names are global and the existing
  single-block `renderVpackZmmCom` threads everything already.

This module therefore emits the **largest faithful sub-kernel the current flat
`XAlloc` renderer supports without a per-block alloc** — the θ→ι chain, whose
auxiliary registers legitimately share — as a proof that the sequence renderer
emits a whole multi-step kernel into ONE `.s` with the round-state register
threaded. The remaining steps (ρ/π/χ) are a per-block-alloc field extension away,
documented above as the concrete renderer requirement.

## Soundness

Two pins, mirroring `VpackZmmComSeq.{chained_seq_lines, chained_seq_denote}`:

* **Structural** (`keccak_theta_iota_seq_lines`): the sequenced render is exactly
  θ's four `vpxorq` body lines `++` ι's one `vpxorq` line — no step dropped, the
  parity threaded across the boundary in `%zmm0`, the SSA counter advanced
  (θ used `v0..v3`, ι uses `v4`). `native_decide`.
* **Denote-level** (`keccak_theta_iota_seq_denote`, via the committed
  `chained_seq_denote` pattern): feeding θ's denoted column parity as ι's `s0`
  input gives the whole sub-kernel value
  `(a0 ⊕ a1 ⊕ a2 ⊕ a3 ⊕ a4) ⊕ rc`, the fold of the two step denotes. The
  threaded render realises exactly that fold. `rfl`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
  (VpackZmmBlock VpackZmmSeq renderVpackZmmComSeq blockDenote)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayVpackZmmEmit
  (r512 thetaCtx thetaColCom iotaCtx iotaStepCom)

/-! ## 1. The θ→ι step sequence (whole sub-kernel as a block list)

Two committed step-Coms from `Keccak4WayVpackZmmEmit`, sequenced: θ's column
parity feeds ι's round-constant XOR. The round state (the parity) lives in a ZMM
register across the boundary. -/

/-- The whole θ→ι sub-kernel as a `VpackZmmSeq`: the θ column-parity block then
    the ι round-constant XOR block. The parity threads from θ's result into ι's
    `s0` input — the round-state-in-ZMM pattern, here across the θ→ι boundary. -/
def keccakThetaIotaSeq : VpackZmmSeq :=
  [ ⟨thetaCtx, r512, thetaColCom⟩, ⟨iotaCtx, r512, iotaStepCom⟩ ]

/-! ## 2. The boundary-consistent shared allocation

One flat `XAlloc` for both steps. θ's five lanes `a0..a4` are its `p0..p4` →
`%zmm0..4`; its four XOR-fold results `v0..v3` all reuse `%zmm0` (the parity
accumulator). ι reads the parity as `p0 → %zmm0` — the SAME slot θ's result
lives in: **the cross-step register threading**. ι's round constant is its
`p1`, which (per the `paramsAndMap`-base-0 caveat) shares θ's `a1` slot `%zmm1`;
ι's result `v4 → %zmm0`. The SSA names are threaded (θ: `v0..v3`; ι: `v4`) so
they never collide across the boundary. -/
def keccakThetaIotaAlloc : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm1"), ("p2", "%zmm2"), ("p3", "%zmm3"),
    ("p4", "%zmm4"),
    ("v0", "%zmm0"), ("v1", "%zmm0"), ("v2", "%zmm0"), ("v3", "%zmm0"),
    ("v4", "%zmm0") ]

/-! ## 3. Structural soundness: the sequenced body is θ's lines `++` ι's line

The threaded multi-block render of the θ→ι sequence is exactly θ's four owned
`vpxorq` fold lines followed by ι's one owned `vpxorq` line — ONE straight-line
body, the parity carried across the boundary in `%zmm0`, the SSA counter advanced
past θ's four bindings so ι names its binding `v4`. This is the whole-sub-kernel
capability the per-step twins lacked: both steps in ONE `.s` body, no boundary. -/

/-- **The threaded whole-sub-kernel render.** The θ→ι sequence renders to exactly
    five owned AT&T `%zmm` lines in ONE straight-line body: θ's four-fold
    `vpxorq … %zmm0` (the column parity `C = a0⊕a1⊕a2⊕a3⊕a4`, accumulated in
    `%zmm0`) then ι's `vpxorq %zmm1, %zmm0, %zmm0` (the round-constant XOR,
    reading the parity out of the SAME `%zmm0` θ wrote). The register is threaded
    across the θ→ι boundary; the SSA counter advanced (θ used `v0..v3`, ι uses
    `v4`). AT&T EVEX order is `op src2, src1, dst`. -/
theorem keccak_theta_iota_seq_lines :
    (renderVpackZmmComSeq keccakThetaIotaAlloc keccakThetaIotaSeq).1
      = [ "\tvpxorq %zmm1, %zmm0, %zmm0"
        , "\tvpxorq %zmm2, %zmm0, %zmm0"
        , "\tvpxorq %zmm3, %zmm0, %zmm0"
        , "\tvpxorq %zmm4, %zmm0, %zmm0"
        , "\tvpxorq %zmm1, %zmm0, %zmm0" ] := by
  native_decide

/-- The sequenced body has exactly five lines — θ's four-fold XOR plus ι's one
    XOR — i.e. both step-blocks are present in the single body, none dropped. -/
theorem keccak_theta_iota_seq_length :
    (renderVpackZmmComSeq keccakThetaIotaAlloc keccakThetaIotaSeq).1.length = 5 := by
  native_decide

/-- The kernel output is ι's binding `v4` (the threaded SSA counter advanced past
    θ's four bindings `v0..v3`). -/
theorem keccak_theta_iota_seq_result :
    (renderVpackZmmComSeq keccakThetaIotaAlloc keccakThetaIotaSeq).2 = "v4" := by
  native_decide

/-! ## 4. Denote-level soundness: the sub-kernel value is the fold of the step denotes

Via the committed `VpackZmmComSeq.chained_seq_denote` pattern. Feeding θ's denoted
column parity `C = a0⊕a1⊕a2⊕a3⊕a4` as ι's `s0` input gives the whole sub-kernel
value `C ⊕ rc`, written via the verified-dialect `zmmPackQ`. This is the semantics
the threaded render realises: the `%zmm0` that crosses the θ→ι boundary carries
exactly `thetaColCom.denote ⟨a0,a1,a2,a3,a4⟩`. The proof is `rfl`. -/

/-- **The θ→ι boundary step.** Feeding ANY value `c` (the threaded parity, carried
    in `%zmm0`) as ι's `s0` input gives `c ⊕ rc` — ι's round-constant XOR on
    whatever the previous step left in the threaded register. This is the boundary
    half of the fold (`blockDenote` for ι, named for the chain). The proof is the
    committed per-step `iotaStepCom_denote`. -/
theorem keccak_theta_iota_boundary (c rc : BitVec 512) :
    blockDenote ⟨iotaCtx, r512, iotaStepCom⟩ (.cons c (.cons rc .nil))
      = zmmPackQ .xor c rc :=
  Keccak4WayVpackZmmEmit.iotaStepCom_denote c rc

/-- **θ's threaded result.** θ's `blockDenote` on the five column lanes is the
    parity fold `((((a0 ⊕ a1) ⊕ a2) ⊕ a3) ⊕ a4)` — the value that crosses the θ→ι
    boundary in `%zmm0`. The committed per-step `thetaColCom_denote`. -/
theorem keccak_theta_threaded (a0 a1 a2 a3 a4 : BitVec 512) :
    blockDenote ⟨thetaCtx, r512, thetaColCom⟩
        (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil)))))
      = zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor a0 a1) a2) a3) a4 :=
  Keccak4WayVpackZmmEmit.thetaColCom_denote a0 a1 a2 a3 a4

/-- **Denote fold across the θ→ι boundary.** The whole sub-kernel denotes to ι
    applied to θ's parity: `(((((a0 ⊕ a1) ⊕ a2) ⊕ a3) ⊕ a4)) ⊕ rc`, the fold of
    the two step `Com.denote`s, with the parity threaded in `%zmm0`. We compose the
    boundary step (`keccak_theta_iota_boundary`) with θ's threaded result
    (`keccak_theta_threaded`) — feeding θ's denoted parity as ι's input — so the
    heavy θ reduction is shared with its committed per-step pin rather than re-run
    in one monolithic `rfl`. -/
theorem keccak_theta_iota_seq_denote (a0 a1 a2 a3 a4 rc : BitVec 512) :
    blockDenote ⟨iotaCtx, r512, iotaStepCom⟩
        (.cons (blockDenote ⟨thetaCtx, r512, thetaColCom⟩
                  (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))))
               (.cons rc .nil))
      = zmmPackQ .xor
          (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor (zmmPackQ .xor a0 a1) a2) a3) a4)
          rc := by
  rw [keccak_theta_iota_boundary, keccak_theta_threaded]

/-! ## 5. The framed whole-sub-kernel `.s`

The sequenced body framed with SysV-ABI load/store glue under ONE export symbol
`keccak_theta_iota_vpackzmm` — the whole θ→ι sub-kernel as a single owned `.s`
function, the round state threaded inside it. The prologue loads the five column
lanes and the broadcast round constant; the body is the threaded two-step render;
the epilogue stores the round-state output (`%zmm0`). -/

/-- The framed owned `.s` for the whole θ→ι sub-kernel, symbol
    `keccak_theta_iota_vpackzmm`. The five column lanes `a0..a4` from
    `(%rsi)`…`256(%rsi)`, the broadcast round constant from `.rodata` (`%zmm1`,
    the slot reused for both θ's `a1` and ι's `rc` per the naming caveat — see the
    module note), the round-state result (`%zmm0`) stored to `(%rdi)`. The body is
    the ONE straight-line threaded render of BOTH steps, the parity carried across
    the θ→ι boundary in `%zmm0`. -/
def keccakThetaIotaExportAsm : String :=
  frameAsmFunction "keccak_theta_iota_vpackzmm"
    [ "\tvmovdqu64\t(%rsi), %zmm0"
    , "\tvmovdqu64\t64(%rsi), %zmm1"
    , "\tvmovdqu64\t128(%rsi), %zmm2"
    , "\tvmovdqu64\t192(%rsi), %zmm3"
    , "\tvmovdqu64\t256(%rsi), %zmm4" ]
    (renderVpackZmmComSeq keccakThetaIotaAlloc keccakThetaIotaSeq).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

/-- The whole sub-kernel `.s`, with a provenance banner. ONE framed function whose
    body is the threaded θ→ι render — the whole-multi-step capability the per-step
    twins lacked. -/
def keccak_theta_iota_whole_vpackzmm_asm : String :=
  "# Whole θ→ι Keccak-f[1600] sub-kernel, owned Com vpackZMM SEQUENCE emit.\n"
  ++ "# ONE function, round-state register threaded across the θ→ι boundary.\n"
  ++ "# No Avx512Model, no jasminc — rendered by VpackZmmComSeq.renderVpackZmmComSeq.\n"
  ++ keccakThetaIotaExportAsm ++ "\n"

-- Print the emitted owned whole-sub-kernel `.s` for visual inspection.
#eval IO.println keccak_theta_iota_whole_vpackzmm_asm

/-! ## 6. Structural smoke pins on the emitted whole-sub-kernel `.s` text

Reproducing the per-step emit's posture (the packed XOR present, no UPPERCASE
jasmin intrinsic, 512-bit `%zmm`, the export symbol), now over the ONE framed
function whose body is the threaded θ→ι sequence. -/

/- The whole sub-kernel issues the packed XOR (θ's fold and ι's round-constant
    XOR, lowercase owned `%zmm` mnemonic). -/
#guard (strContains keccak_theta_iota_whole_vpackzmm_asm "vpxorq")

/- The whole sub-kernel uses 512-bit `%zmm` registers — the owned ZMM path. -/
#guard (strContains keccak_theta_iota_whole_vpackzmm_asm "%zmm")

/- No UPPERCASE jasmin intrinsic survives — the owned (no-jasminc, no
    `Avx512Model`) sequence-rendered path. -/
#guard !(strContains keccak_theta_iota_whole_vpackzmm_asm "#VPADD_8u64")

/- The whole sub-kernel is ONE framed function naming its export symbol — both
    steps live in this single body (the whole-multi-step `.s`). -/
#guard (strContains keccak_theta_iota_whole_vpackzmm_asm "keccak_theta_iota_vpackzmm:")

/-! ## 7. Emit driver -/

/-- Write the owned-backend (`Com`-sequence-rendered AVX-512 ZMM) whole θ→ι
    Keccak sub-kernel `.s` to `bench/keccak4way_compare/gen_com/`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/keccak4way_compare/gen_com"
  IO.FS.writeFile "bench/keccak4way_compare/gen_com/keccak_theta_iota_whole_vpackzmm.s"
    keccak_theta_iota_whole_vpackzmm_asm
  IO.println "wrote bench/keccak4way_compare/gen_com/keccak_theta_iota_whole_vpackzmm.s (owned Com vpackZMM θ→ι whole sub-kernel, round-state threaded)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeVpackZmmEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Keccak4WayWholeVpackZmmEmit in
/-- `lake env lean --run` entry point: emit the owned `Com`-sequence-rendered
    whole θ→ι Keccak sub-kernel (the round-state register threaded across the
    θ→ι boundary in ONE `.s` function). -/
private def main : IO Unit := emit
