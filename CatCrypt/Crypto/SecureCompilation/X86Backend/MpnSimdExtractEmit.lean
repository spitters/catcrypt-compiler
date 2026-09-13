/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit

/-!
# The SIMD→GP extract gap: owned `vpcmpeqq` + `vpmovmskb gpr, ymm` (model-free)

**TEST/BENCH-ONLY — STRING-TEMPLATED, not verified-compiler output.** The
emitted `bench/mpn_compare_simd_compare/gen/mpn_simd_compare_owned.s` is a body
rendered from the typed `mpnSimdChunkBlock` by the module-local printer
`renderXInst` wrapped in hand-written frame lines (string lists joined with
`String.intercalate`), with no single verified-printer descent for the whole
file. The `native_decide`/`example` checks are structural assertions; the block
denotation `mpnSimdChunk_denotation` (tied to the verified `VPCmpEmit` lane
reference) scopes the compare/extract block, not the emitted frame. It is a
bench/interop reference. The verified emit path is the FRONT-SOURCED descent.

The **model-free** mpn SIMD-compare owned `.s` emit (the `vpcmpeqq`/`vpmovmskb`
extract kernel). It writes
`bench/mpn_compare_simd_compare/gen/mpn_simd_compare_owned.s` with no dependency
on `Avx2YmmModel` / `Avx2YmmAsmPrinter` / `Avx2YmmEncoder`. Its only inputs are:

* the unified AT&T printer `VIR.YmmAsmPrint` (`YmmInstr` / `renderYmmInstr` for
  the `vmovdqu` load lines and the function frame),
* the independent verified reference `VIR.VPCmpEmit` (`vpcmpeqq_lane`,
  `vpmovmskb_lane256`, `vpcmpeqq_lane_refl`, `allOnes64`) for the lane semantics,
* the dialect lane views `VIR.YmmDialect.yOfQwordsW` / `yQwordW` (re-export from
  `VPCmpEmit`'s transitive `YmmDialectOps` import) for the packed reassembly.

## The SIMD→GP extract the mpn-compare kernel needs

The non-CT mpn compare does one `vpcmpeqq %ymm, %ymm, %ymm` per 4×u64 chunk and
collapses the 256-bit mask to a 32-bit GP-register bitmask via
`vpmovmskb gpr, ymm`, then branches on `bm == 0xFFFFFFFF`:

1. **`vpcmpeqq ymm, ymm, ymm`** — packed 4×u64 equality (all-ones / all-zeros per
   qword lane). Its `BitVec 256 → BitVec 256` denotation `vpcmpeqq256` is the
   packed reassembly of `VPCmpEmit.vpcmpeqq_lane` over the 4 qword lanes.
2. **`vpmovmskb gpr, ymm`** — the SIMD→GP byte-mask extract: the destination GP
   register gets, in bit `i`, bit 7 of input byte `i`. Its denotation
   `vpmovmskb256` IS `VPCmpEmit.vpmovmskb_lane256` (32-bit mask), the verified
   reference. This is the instruction that bridges the vector register file to a
   GP result; it is NOT a `YmmOp` (its result is `reg 32`, a GP register), so it
   is a standalone instruction arm with its own 2-line printer string.

The verified reference these denotations are checked against is `VIR.VPCmpEmit`
(`vpcmpeqq_lane`, `vpmovmskb_lane256`, `vpcmpeqq_lane_refl`), the SAME denotation
the dialect-level demonstrator (`cmp_simd_emit.lean`) carries.

## The owned `.s` kernel

The body matches the C-harness ABI of
`bench/mpn_compare_simd_compare/cmp_simd_ref.c`:

  `extern uint64_t mpn_simd_chunk_4(const uint64_t ap[4], const uint64_t bp[4]);`

(`ap`=`%rdi`, `bp`=`%rsi`, returns the 32-bit mask zero-extended in `%rax`):

  vmovdqu (%rdi), %ymm0
  vmovdqu (%rsi), %ymm1
  vpcmpeqq %ymm1, %ymm0, %ymm0
  vpmovmskb %ymm0, %eax        ; ← the SIMD→GP extract
  vzeroupper
  ret                          ; %eax already zero-extends into %rax

## Trust posture

The lane denotation is the verified artifact (re-exported from `VPCmpEmit`), and
the printer is pinned to the exact bytes/text `gas` produces (§5). The byte
encoder is NOT on the artifact path — the bench `cp`s the printer text — so it is
dropped here; the C-side KAT (`bench/mpn_compare_simd_compare/conform.c`, 50000
vectors, 5-way agreement) is the integration witness for the emitted `.s`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnSimdExtract

open CatCrypt.Crypto.SecureCompilation.VIR.VPCmpEmit
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint

/-- A 256-bit YMM register, modelled (model-free) as a flat `BitVec 256`. This is
    a local abbreviation, NOT the bespoke `Avx2Ymm.Ymm` — there is no
    `Avx2YmmModel` dependency. -/
abbrev Ymm : Type := BitVec 256

/-! ## 1. The two new lane denotations (packed `BitVec` form) -/

/-- Packed `vpcmpeqq ymm` denotation: `BitVec 256 → BitVec 256`, per 64-bit qword
    lane all-ones if equal, all-zeros otherwise. This is the packed reassembly of
    `VPCmpEmit.vpcmpeqq_lane` over the 4 qword lanes (via the dialect lane views
    `yOfQwordsW`/`yQwordW`) — pinned lane-equal to the verified per-lane reference
    in §3. -/
def vpcmpeqq256 (a b : Ymm) : Ymm :=
  yOfQwordsW (fun j => vpcmpeqq_lane (yQwordW a j.val) (yQwordW b j.val))

/-- The SIMD→GP byte-mask extract `vpmovmskb gpr, ymm`: bit `i` of the 32-bit
    result is bit 7 (the sign bit) of input byte `i`. This IS the verified
    reference `VPCmpEmit.vpmovmskb_lane256` — the destination is a GP register, so
    the result type is `BitVec 32`, not `Ymm`. -/
def vpmovmskb256 (v : Ymm) : BitVec 32 := vpmovmskb_lane256 v

/-! ## 2. The extract instruction + its model-free state transition

The minimal SIMD→GP micro-state is the ymm register file (`String → BitVec 256`)
plus the 64-bit GP result the extract writes (the kernel's `%rax`/`%eax` return
slot). No `Avx2YmmModel.YState`. -/

/-- A SIMD→GP extract micro-state: the ymm register file (a `String → BitVec 256`
    function, absent name reads zero) plus the 64-bit general-purpose result slot
    the extract writes (the kernel's `%rax` return, zero-extended). -/
structure XState where
  /-- The ymm register file. -/
  y : String → BitVec 256
  /-- The 64-bit general-purpose result slot (the extract destination, zero-
      extended). -/
  gp : BitVec 64

/-- Write a `ymm` register, leaving the others unchanged. -/
def XState.setY (s : XState) (r : String) (v : BitVec 256) : XState :=
  { s with y := fun r' => if r' = r then v else s.y r' }

/-- One SIMD→GP-extended instruction: either a register-file `YmmInstr`
    (load/store/move), the packed `vpcmpeqq`, or the `vpmovmskb` extract that
    writes the GP slot. -/
inductive XInst where
  /-- A lifted register-only `YmmInstr` (load/store/move). -/
  | yinst (i : YmmInstr)
  /-- `VPCMPEQQ dst, a, b` — packed 4×u64 equality (all-ones/all-zeros per lane). -/
  | vpcmpeqq (dst a b : String)
  /-- `VPMOVMSKB gpDst, src` — SIMD→GP byte-mask extract: `gpDst` (a GP register
      name) gets the 32-bit sign-byte mask of the `src` ymm, zero-extended to 64
      bits. -/
  | vpmovmskb (gpDst src : String)

/-- The semantics of one extended instruction. `vpmovmskb` writes the GP slot
    (zero-extended 32→64); `vpcmpeqq` writes the ymm file; `yinst` defers to the
    register-file transition (loads/stores/moves). The `yload`/`ystore` arms are
    register-file no-ops (memory is owned by the driver layer), as in the base
    model; `ymov` aliases a register. -/
def evalXInst (s : XState) : XInst → XState
  | .yinst (.alu _ _ _)   => s
  | .yinst (.ymov dst src) => s.setY dst (s.y src)
  | .yinst (.yload _ _)   => s
  | .yinst (.ystore _ _)  => s
  | .vpcmpeqq dst a b     => s.setY dst (vpcmpeqq256 (s.y a) (s.y b))
  | .vpmovmskb _ src      => { s with gp := (vpmovmskb256 (s.y src)).setWidth 64 }

/-- Straight-line fold of `evalXInst`. -/
def runXBlock (s : XState) : List XInst → XState
  | [] => s
  | i :: is => runXBlock (evalXInst s i) is

@[simp] theorem runXBlock_nil (s : XState) : runXBlock s [] = s := rfl

@[simp] theorem runXBlock_cons (s : XState) (i : XInst) (is : List XInst) :
    runXBlock s (i :: is) = runXBlock (evalXInst s i) is := rfl

/-! ## 3. The extract arms agree with the verified `VPCmpEmit` reference

The two new denotations are checked lane-for-lane against the independent
reference `VIR.VPCmpEmit` (`vpcmpeqq_lane`, `vpmovmskb_lane256`,
`vpcmpeqq_lane_refl`). This is the HONESTY GATE: the emit denotation equals the
INDEPENDENT reference, not a self-authored body. -/

/-- `vpmovmskb256` IS the verified `VPCmpEmit.vpmovmskb_lane256` reference. -/
theorem vpmovmskb256_eq_ref (v : Ymm) : vpmovmskb256 v = vpmovmskb_lane256 v := rfl

/-- On EQUAL inputs, the packed `vpcmpeqq256` collapses to the constant
    all-ones-per-lane register `yOfQwordsW (fun _ => allOnes64)` — every lane is
    `vpcmpeqq_lane x x = allOnes64` by the verified `vpcmpeqq_lane_refl`. This is
    independent of `a`, so the resulting mask is a closed computation. -/
theorem vpcmpeqq256_self (a : Ymm) :
    vpcmpeqq256 a a = yOfQwordsW (fun _ => allOnes64) := by
  simp only [vpcmpeqq256, vpcmpeqq_lane_refl]

/-- **Headline (all-equal ⇒ full mask).** On equal inputs, the extract over
    `vpcmpeqq256` yields the all-ones 32-bit mask `0xFFFFFFFF` — exactly the
    `bm == 0xFFFFFFFF` test the C driver branches on. Tied through
    `vpcmpeqq_lane_refl` (the verified `VPCmpEmit` reference) collapsing every
    lane to `allOnes64`, then `vpmovmskb_lane256` of the all-ones register. -/
theorem extract_all_equal (a : Ymm) :
    vpmovmskb256 (vpcmpeqq256 a a) = BitVec.ofNat 32 0xFFFFFFFF := by
  rw [vpcmpeqq256_self]
  native_decide

/-! ## 4. The AT&T printer for the two new arms

The `vmovdqu` load lines and the function frame come from the unified
`YmmAsmPrint` printer; the two extract arms (`vpcmpeqq`/`vpmovmskb`) carry their
own literal AT&T strings, matching the bespoke `renderXInst` output
byte-for-byte. `vpcmpeqq` is `op src2, src1, dst`; `vpmovmskb` is
`op ymmsrc, gpdst`. -/

/-- Print one `XInst` to its AT&T line. The `yinst` arm defers to the unified
    `renderYmmInstr`; the two extract arms carry their literal strings. -/
def renderXInst : XInst → String
  | .yinst i             => renderYmmInstr i
  | .vpcmpeqq dst a b    => "\tvpcmpeqq\t" ++ b ++ ", " ++ a ++ ", " ++ dst
  | .vpmovmskb gpDst src => "\tvpmovmskb\t" ++ src ++ ", " ++ gpDst

/-- Print a block's instruction lines. -/
def renderXBlockBody (block : List XInst) : List String := block.map renderXInst

-- printer pins (audited against gas mnemonic syntax)
example : renderXInst (.vpcmpeqq "%ymm0" "%ymm0" "%ymm1") = "\tvpcmpeqq\t%ymm1, %ymm0, %ymm0" := by
  native_decide
example : renderXInst (.vpmovmskb "%eax" "%ymm0") = "\tvpmovmskb\t%ymm0, %eax" := by
  native_decide

/-! ## 5. The owned `mpn_simd_chunk` kernel emit

The function frame for `mpn_simd_chunk_<n>` matches the C harness ABI:

  `extern uint64_t mpn_simd_chunk_4(const uint64_t ap[4], const uint64_t bp[4]);`

`ap`=`%rdi`, `bp`=`%rsi`, the 32-bit mask returned zero-extended in `%rax`
(`vpmovmskb` writes `%eax`, which the x86-64 ABI zero-extends into `%rax`). The
body is the load/load/compare/extract sequence, now as owned `.s` with the
SIMD→GP extract realised. -/

/-- The instruction block of one `mpn_simd_chunk` kernel (size-independent — each
    fixed-`n` export is the same one-chunk function, as in the dialect
    demonstrator). The two loads use the unified `YmmInstr.yload`. -/
def mpnSimdChunkBlock : List XInst :=
  [ .yinst (.yload "%ymm0" ⟨"%rdi", 0⟩)
  , .yinst (.yload "%ymm1" ⟨"%rsi", 0⟩)
  , .vpcmpeqq "%ymm0" "%ymm0" "%ymm1"
  , .vpmovmskb "%eax" "%ymm0" ]

/-- Render a complete owned `.s` function for `mpn_simd_chunk_<n>`: symbol
    directives, the 2-pointer-in / mask-out body, `vzeroupper`, `ret`. The
    `vpmovmskb` already leaves the 32-bit mask zero-extended in `%rax`.
    Byte-identical to the bespoke `renderMpnSimdChunkFundef`. -/
def renderMpnSimdChunkFundef (name : String) : List String :=
  [ "\t.att_syntax"
  , "\t.text"
  , "\t.p2align\t4"
  , "\t.globl\t" ++ name
  , "\t.type\t" ++ name ++ ", @function"
  , name ++ ":" ]
  ++ renderXBlockBody mpnSimdChunkBlock
  ++ [ "\tvzeroupper"
     , "\tret"
     , "\t.section\t.note.GNU-stack,\"\",@progbits" ]

/-- The function text as a single `\n`-joined string. -/
def renderMpnSimdChunkText (name : String) : String :=
  String.intercalate "\n" (renderMpnSimdChunkFundef name) ++ "\n"

/-- The full owned `.s`: one `mpn_simd_chunk_<n>` export per demonstrator size
    {4,8,16,32,64} (matching `cmp_simd_ref.c`'s `mpn_simd_chunk_4` extern). -/
def mpnSimdCompareS : String :=
  String.intercalate "\n"
    ((["mpn_simd_chunk_4", "mpn_simd_chunk_8", "mpn_simd_chunk_16",
       "mpn_simd_chunk_32", "mpn_simd_chunk_64"].map renderMpnSimdChunkText))

/-! ### Emit structural pins (byte-identical to the bespoke output) -/

/-- The kernel body is the load/load/vpcmpeqq/vpmovmskb sequence (the SIMD→GP
    extract is present). -/
example : renderXBlockBody mpnSimdChunkBlock =
    [ "\tvmovdqu\t(%rdi), %ymm0"
    , "\tvmovdqu\t(%rsi), %ymm1"
    , "\tvpcmpeqq\t%ymm1, %ymm0, %ymm0"
    , "\tvpmovmskb\t%ymm0, %eax" ] := by native_decide

/-- The frame carries the exported symbol and the AT&T return. -/
example : renderMpnSimdChunkFundef "mpn_simd_chunk_4" =
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.globl\tmpn_simd_chunk_4", "\t.type\tmpn_simd_chunk_4, @function"
    , "mpn_simd_chunk_4:"
    , "\tvmovdqu\t(%rdi), %ymm0"
    , "\tvmovdqu\t(%rsi), %ymm1"
    , "\tvpcmpeqq\t%ymm1, %ymm0, %ymm0"
    , "\tvpmovmskb\t%ymm0, %eax"
    , "\tvzeroupper", "\tret"
    , "\t.section\t.note.GNU-stack,\"\",@progbits" ] := by native_decide

/-! ## 6. The denotation of the emitted kernel == the C reference

The C harness (`cmp_simd_ref.c`) computes, per chunk:
  `bm = vpmovmskb256(vpcmpeqq256(a, b))`, branches on `bm == 0xFFFFFFFF`.
`runXBlock` over `mpnSimdChunkBlock` on a state whose `%ymm0`/`%ymm1` are loaded
with `a`/`b` leaves exactly that mask in the GP slot, and `extract_all_equal`
gives the all-equal branch value the driver tests. -/

/-- The kernel's GP result on inputs `a` (in `%ymm0`) and `b` (in `%ymm1`) is the
    32-bit `vpmovmskb`-of-`vpcmpeqq` mask — the value `cmp_simd_emit_compare`
    branches on. (The two `yload` arms are register-file no-ops in the model, so
    we model the loaded state directly.) -/
theorem mpnSimdChunk_denotation (a b : Ymm) :
    let s0 : XState := { y := fun r =>
        if r = "%ymm0" then a else if r = "%ymm1" then b else 0, gp := 0 };
    (runXBlock s0
      [ .vpcmpeqq "%ymm0" "%ymm0" "%ymm1"
      , .vpmovmskb "%eax" "%ymm0" ]).gp
      = (vpmovmskb256 (vpcmpeqq256 a b)).setWidth 64 := by
  simp [runXBlock, evalXInst, XState.setY, vpmovmskb256, vpcmpeqq256]

/-- On EQUAL inputs the kernel returns `0xFFFFFFFF` (zero-extended) — the
    `bm == 0xFFFFFFFF` "advance to next chunk" case, tied to the verified
    `VPCmpEmit` reference via `extract_all_equal`. -/
theorem mpnSimdChunk_all_equal (a : Ymm) :
    let s0 : XState := { y := fun r =>
        if r = "%ymm0" then a else if r = "%ymm1" then a else 0, gp := 0 };
    (runXBlock s0
      [ .vpcmpeqq "%ymm0" "%ymm0" "%ymm1"
      , .vpmovmskb "%eax" "%ymm0" ]).gp
      = BitVec.ofNat 64 0xFFFFFFFF := by
  have h := mpnSimdChunk_denotation a a
  simp only [h, extract_all_equal]
  native_decide

/-! ## 7. The emit driver -/

/-- Write the owned `.s` to `bench/mpn_compare_simd_compare/gen/mpn_simd_compare_owned.s`. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/mpn_compare_simd_compare/gen"
  IO.FS.writeFile "bench/mpn_compare_simd_compare/gen/mpn_simd_compare_owned.s"
    mpnSimdCompareS
  IO.println "wrote bench/mpn_compare_simd_compare/gen/mpn_simd_compare_owned.s"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnSimdExtract

-- NB: the `lake env lean --run` entry point lives in the bench driver, NOT here —
-- a root-level `def main` in a library module imported by the EmitAll
-- rot-guard collides with other root-`main` modules.
