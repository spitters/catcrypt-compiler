/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.TakeDrop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Owned AT&T printer for the linear-jasmin owned-RA `Lcmd`

The owned-RA linear path (`JasminLprogExport.Com.toLprogPhysAbi`) emits a
**physical-register, two-address** `Linear.lprog`: every body `Lopn` is already
allocated to a concrete x86 GP register (`RAX … R15`), a stack spill slot
(`k.N`), an ABI save slot (`qsave.X`), or a memory operand (`mem.<base>.<off>`),
and is in destructive two-address form (`MOV dst,src0; OP dst,src1`). The other
consumer of that `Lprog` is the *patched* jasmin `read_linear` +
`compile_lprog_to_asm`, which RE-encodes the already-allocated body to `.s`.

This module is the **owned** consumer: a direct `Lcmd → AT&T gas` text renderer,
the linear-path counterpart of `AsmPrinter.renderJInstr`, which consumes
`JInstr` blocks rather than an `Lcmd`. It removes the patched-jasmin encoder
from the scalar hash / Poseidon2 path: `Com → toLprogPhysAbi → renderLprogAtt →
.s`, assembled by `gas` exactly like the existing `*_x86_from_lean.s` kernels.

## Why this is a thin syntactic map (the same trust posture as `renderJInstr`)

The body is already RA'd (physical registers + spill slots) and two-address, so
the renderer performs **no** instruction selection, scheduling, allocation, or
optimization: one `Lopn` arm → one AT&T mnemonic line, operands resolved by a
fixed name→`%rN` / `k.N`→`off(%rsp)` map. This is the SAME map the patched
`read_linear.ml` implements (`spill_addr`, `qsave_addr_of_name`, `mem_of_name`,
`phys_reg_of_name`), transcribed Lean-side so the path does not depend on that
encoder. The trusted-but-unverified surface is then exactly `gas` (mnemonic+operands
→ bytes), the same final step every backend trusts.

## Operand-name conventions (transcribed from SSProve-lean `patches/jasmin/read_linear.ml.patch`)

* physical GP `RAX … R15` → `%rax … %r15` (32-bit subregister `%eax … %r15d`
  for U32 ops, full 64-bit register for U64 ops);
* `k.N` (spill slot) → frame slot `(F + spillBase(w,N))(%rsp)` with cell stride
  `cell = 4` (U32) or `8` (U64) — `read_linear.spill_addr`'s downward-growing
  layout, **widened to an 8-byte stride for U64** so an 8-byte load/store of
  `k.N` never overlaps `k.(N+1)` (the upstream patch hard-codes a 4-byte stride,
  a latent U64 aliasing bug — see module note);
* `qsave.X` → fixed slot (`RDI`=-128, `RSI`=-120, `RBX`=-112, `RBP`=-104,
  `R12`=-96, `R13`=-88, `R14`=-80, `R15`=-72, relative to entry `%rsp`);
* `mem.<base>.<off>` → `off(%base)`;
* `#v` immediate → `$v`.

## Stack frame (not the red zone)

The owned-RA SHA-256 body uses ~70 U32 spill cells (~280 B) plus the 64 B of
qsave slots — beyond the 128-byte System-V red zone. So `renderLfundef`
allocates a real frame: `leaq -F(%rsp), %rsp` on entry (F 16-byte-aligned, large
enough for every qsave + spill offset), every red-zone-relative offset shifted by
`+F` into the positive frame, and `leaq F(%rsp), %rsp` before `ret` (jasmin's own
frame idiom). A body that fits the red zone would use F = 0; here F is computed
from the body's max spill index.

## A note on the upstream U64 spill stride (a reported mismatch, not patched)

`read_linear.spill_addr idx = RSP - 4 - 4·idx` (a fixed **4-byte** stride) for
*all* spills, while the `MOVQ` / `:64` handler loads/stores **8 bytes**. For a
U64 kernel (Keccak, Poseidon2, SHA-512) two adjacent live spills `k.N`, `k.(N+1)`
then overlap by 4 bytes — a correctness hazard in the patched path that the U64
benches only avoided when adjacent U64 spills were not simultaneously live. The
owned renderer here uses the **width-correct** stride (`cell = 8` for U64), so it
is the more-correct of the two for the U64 path; this divergence is reported as a
finding (the upstream `spill_addr` should take the operand width), not silently
matched.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- The reserved carry-in operand name that marks an `ADCX`/`ADOX` data op whose
    carry-in is the **live CPU carry flag** already produced by the immediately
    preceding carry op — not a materialised `reg 1` data value. The ADX
    carry-chain fuser (`AdxChainFuse.fuseAdxChain`) retags a consumer's carry-in
    to this sentinel after it drops the producer's `ADCXHI` `setc`/`movzbq`
    materialisation, so the `renderLopn` `ADCX` arm below emits **no** `bt $0,cin`
    round-trip and lets the flag flow directly (the fused `adcx`/`adox` chain).
    The name is `__`-leading so it can never collide with a physical register or
    spill-slot pseudo-name. -/
def cfCarrySentinel : String := "__cfflag"

/-! ## 1. Physical-register name map (`RAX → %rax`, width-aware) -/

/-- The AT&T 64-bit register name for a physical GP name (`"RAX" → "%rax"`). The
    spill / qsave / mem names are handled separately; this is the bare-register
    case. Unknown names fall through to a lowercased `%`-prefixed form so an
    out-of-set name surfaces as an obviously-wrong operand (gas rejects it)
    rather than silently aliasing. -/
def gpReg64 : String → String
  | "RAX" => "%rax" | "RBX" => "%rbx" | "RCX" => "%rcx" | "RDX" => "%rdx"
  | "RSI" => "%rsi" | "RDI" => "%rdi" | "RBP" => "%rbp" | "RSP" => "%rsp"
  | "R8"  => "%r8"  | "R9"  => "%r9"  | "R10" => "%r10" | "R11" => "%r11"
  | "R12" => "%r12" | "R13" => "%r13" | "R14" => "%r14" | "R15" => "%r15"
  | other => "%<UNKNOWN:" ++ other ++ ">"

/-- The AT&T 8-bit (low byte) subregister name for a physical GP name
    (`"RAX" → "%al"`, `"R8" → "%r8b"`). Used by `SETcc` (`SETC`), which writes a
    byte destination; the renderer then `MOVZBQ`-zero-extends it to the full
    register. -/
def gpReg8 : String → String
  | "RAX" => "%al"  | "RBX" => "%bl"  | "RCX" => "%cl"  | "RDX" => "%dl"
  | "RSI" => "%sil" | "RDI" => "%dil" | "RBP" => "%bpl" | "RSP" => "%spl"
  | "R8"  => "%r8b" | "R9"  => "%r9b" | "R10" => "%r10b" | "R11" => "%r11b"
  | "R12" => "%r12b"| "R13" => "%r13b"| "R14" => "%r14b" | "R15" => "%r15b"
  | other => "%<UNKNOWN:" ++ other ++ ">"

/-- The AT&T 16-bit subregister name for a physical GP name (`"RAX" → "%ax"`,
    `"R8" → "%r8w"`). Used by the narrow `u16` ABI store (`MOV:16`), which writes
    a width-exact 16-bit slot (`movw %r15w, out(%rdi,…)`) without overrunning the
    neighbouring `uint16_t` element (the Frodo seam). -/
def gpReg16 : String → String
  | "RAX" => "%ax"  | "RBX" => "%bx"  | "RCX" => "%cx"  | "RDX" => "%dx"
  | "RSI" => "%si"  | "RDI" => "%di"  | "RBP" => "%bp"  | "RSP" => "%sp"
  | "R8"  => "%r8w" | "R9"  => "%r9w" | "R10" => "%r10w" | "R11" => "%r11w"
  | "R12" => "%r12w"| "R13" => "%r13w"| "R14" => "%r14w" | "R15" => "%r15w"
  | other => "%<UNKNOWN:" ++ other ++ ">"

/-- The AT&T 32-bit subregister name for a physical GP name (`"RAX" → "%eax"`,
    `"R8" → "%r8d"`). Used for U32 body ops (SHA-256, bitslice-AES bit-planes are
    U64 though). -/
def gpReg32 : String → String
  | "RAX" => "%eax" | "RBX" => "%ebx" | "RCX" => "%ecx" | "RDX" => "%edx"
  | "RSI" => "%esi" | "RDI" => "%edi" | "RBP" => "%ebp" | "RSP" => "%esp"
  | "R8"  => "%r8d" | "R9"  => "%r9d" | "R10" => "%r10d" | "R11" => "%r11d"
  | "R12" => "%r12d" | "R13" => "%r13d" | "R14" => "%r14d" | "R15" => "%r15d"
  | other => "%<UNKNOWN:" ++ other ++ ">"

/-- The AVX-512 ZMM vector-register name for a `vN`-style packed-lane operand
    (`"v0" → "%zmm0"`). The `VPACK` packed-add arm names its 512-bit
    ZMM operands through this map. **Limitation (the u512 blocker):** the owned
    GP-linear allocator (`Com.toLprogPhysAbi`) has no vector-register file, so a
    512-bit value cannot be allocated to a ZMM register through that path — it
    keeps producing GP names (`RAX`…). This namer therefore only resolves an
    operand already carrying a `vN` ZMM name (a hand-built or SIMD-RA `Lcmd`); a
    GP name surfaces as an obviously-wrong `%<NOTZMM>` form gas rejects. VPACK
    end-to-end needs a vector-RA path, which this printer does not provide. -/
def zmmReg : String → String
  | n =>
    if "v".isPrefixOf n then "%zmm" ++ (n.drop 1).toString
    else "%<NOTZMM:" ++ n ++ ">"

/-- The byte size of one spill cell for a given op width: 4 bytes for U32, 8
    bytes for U64. The owned renderer uses the **width-correct** stride (unlike
    `read_linear.spill_addr`'s fixed 4-byte stride — see module note). -/
def spillCellBytes (w : Nat) : Nat := if w = 64 then 8 else 4

/-- The bytes reserved at the **top** of the frame for the eight ABI 64-bit save
    slots (`qsave.RDI … qsave.R15`), 8 bytes each. The spill slots `k.N` live
    BELOW this block, so the two regions are disjoint by construction (the
    `read_linear` red-zone layout overlapped them once the body had >30 spills —
    SHA-256 has 70; see module note). -/
def qsaveBytes : Nat := 8 * 8

/-- The bytes reserved at the top of the frame for the ABI save slots of a body
    that issues a `call`: all twelve 8-byte cells (`qsave.RDI … qsave.R9`),
    including the slots of the 3rd-through-6th SysV pointer arguments.

    A `call` pushes its return address at `-8(%rsp)`, the first cell of the
    System-V red zone, so the red-zone placement those four slots take in a
    call-free body does not survive a call. A calling body reserves them inside
    its own frame instead. -/
def qsaveBytesCall : Nat := 12 * 8

/-- The qsave block size of a body: the twelve-cell block when the body issues a
    `call`, the eight-cell block otherwise. A call-free body reserves exactly
    `qsaveBytes`, so its frame layout — and every qsave and spill offset computed
    from it — is the one it had before the block became body-dependent. -/
def qsaveBytesFor (body : VIR.JasminLprogExport.Lcmd) : Nat :=
  if VIR.JasminLprogExport.bodyHasCall body then qsaveBytesCall else qsaveBytes

/-- The zero-based qsave slot index of a save register (`RDI`=0 … `R15`=7, plus
    the 2nd+ SysV input pointer regs `RDX`=8 … `R9`=11 for multi-input array
    loops), used to place its 8-byte cell in the frame's top block. -/
def qsaveSlot : String → Option Nat
  | "RDI" => some 0 | "RSI" => some 1
  | "RBX" => some 2 | "RBP" => some 3
  | "R12" => some 4 | "R13" => some 5
  | "R14" => some 6 | "R15" => some 7
  | "RDX" => some 8 | "RCX" => some 9
  | "R8"  => some 10 | "R9" => some 11
  | _ => none

/-- The frame offset (from the post-`leaq` `%rsp`) of qsave slot `X` in a frame of
    size `frame` whose qsave block is `qsaveB` bytes: the top of the frame holds
    the 8-byte save cells, slot `i` at `frame - 8·(i+1)`, for as many slots as
    `qsaveB` reserves.

    A slot the block does not reach is placed in the System-V red zone below
    `%rsp` at `-8·(i-7)`. The red zone is guaranteed only to a leaf, so that
    placement is sound exactly for a body that issues no `call`; `qsaveBytesFor`
    is what widens the block to hold slots 8-11 for a calling body. At the
    default `qsaveB = qsaveBytes` the eight standard slots are in-frame and slots
    8-11 are red-zone, which is the call-free layout. -/
def qsaveFrameOff (frame : Nat) (reg : String) (qsaveB : Nat := qsaveBytes) :
    Option Int :=
  (qsaveSlot reg).map (fun i =>
    if 8 * (i + 1) ≤ qsaveB then
      Int.ofNat frame - 8 * (Int.ofNat i + 1)
    else
      -(8 * (Int.ofNat i - 7)))

/-- The positive frame offset (from the post-`leaq` `%rsp`) of U32-spill slot
    `k.idx` at op width `w` in a frame of size `frame` whose qsave block is
    `qsaveB` bytes: the spill region sits BELOW that block, slot `idx` at
    `frame - qsaveB - cell·(idx+1)` (downward-growing, disjoint from qsave). -/
def spillFrameOff (frame w idx : Nat) (qsaveB : Nat := qsaveBytes) : Int :=
  Int.ofNat frame - Int.ofNat qsaveB - Int.ofNat (spillCellBytes w * (idx + 1))

/-! ## 2. Operand resolution: `LOperand` (with name conventions) → AT&T text

`frame` is the allocated frame size `F` (bytes): every red-zone-relative offset
(spill `k.N`, qsave `X`) is shifted by `+F` into the positive frame addressed off
the post-`subq` `%rsp`. Memory operands (`mem.base.off`) are NOT `%rsp`-relative
and carry no shift. -/

/-- Resolve a register *name* string (as it appears in the owned-RA body) to its
    AT&T operand text. `w` is the **op** width (selecting `%eax` vs `%rax` for a
    bare GP register); `spillW` is the **body-uniform** spill width that fixes the
    `k.N` cell stride — it must be constant across the whole body, else a slot
    would get inconsistent offsets between a `:64` op and an (untagged) reload
    MOV. `frame` is the allocated frame size, `qsaveB` the frame's qsave block
    size (which fixes where the spill region starts and which qsave slots are
    in-frame). Recognises, in priority order: spill `k.N`, ABI save `qsave.X`,
    memory `mem.<base>.<off>`, then a GP reg. -/
def resolveName (frame spillW w : Nat) (n : String)
    (qsaveB : Nat := qsaveBytes) : String :=
  if "k.".isPrefixOf n then
    match (String.toNat? (n.drop 2).toString) with
    | some idx => toString (spillFrameOff frame spillW idx qsaveB) ++ "(%rsp)"
    | none => "<BADSPILL:" ++ n ++ ">"
  else if "qsave.".isPrefixOf n then
    let reg := (n.drop 6).toString
    match qsaveFrameOff frame reg qsaveB with
    | some off => toString off ++ "(%rsp)"
    | none => "<BADQSAVE:" ++ n ++ ">"
  else if "mem.".isPrefixOf n then
    -- "mem.<base>.<off>"  (base-pointer-relative, no frame shift)
    let rest := (n.drop 4).toString
    match rest.splitOn "." with
    | [base, off] =>
        match String.toNat? off with
        | some o => (if o = 0 then "" else toString o) ++ "(" ++ gpReg64 base ++ ")"
        | none => "<BADMEM:" ++ n ++ ">"
    | _ => "<BADMEM:" ++ n ++ ">"
  else if "kv.".isPrefixOf n then
    -- a **vector spill slot** `kv.idx`: a 32-byte YMM cell in the frame's
    -- vector-spill region, anchored at the BOTTOM of the frame at offset
    -- `32·(idx+1)` from the post-`leaq` `%rsp` (slot `0(%rsp)` is reserved as the
    -- `%ymm15` save cell for spill legalization, `vecSpillScratch`). The region is
    -- disjoint from the top-anchored qsave/GP `k.N` cells, so a GP-only body
    -- reserves no vector region and stays byte-identical. `frameSize` sizes it.
    match String.toNat? (n.drop 3).toString with
    | some idx => toString (32 * (idx + 1)) ++ "(%rsp)"
    | none => "<BADVSPILL:" ++ n ++ ">"
  else if "XMM".isPrefixOf n then
    -- a packed 256-bit vector operand: the `XMM<k>` name a SIMD-RA `Lcmd`
    -- carries for a batch8 packed lane value resolves to the AVX `%ymm<k>`
    -- register (256-bit lane width), independent of the scalar op width `w`.
    "%ymm" ++ (n.drop 3).toString
  else
    -- a bare physical GP register, sized by the op width: full reg for U64, the
    -- 32-bit subreg for U32 (and as the zero-extension target of a narrow load),
    -- the 16-bit subreg for a `u16` ABI store, the 8-bit subreg for `u8`.
    if w = 64 then gpReg64 n
    else if w = 16 then gpReg16 n
    else if w = 8 then gpReg8 n
    else gpReg32 n

/-- Resolve an `LOperand` to AT&T operand text. `w` is the op width, `spillW` the
    body-uniform spill width, `frame` the frame size. An immediate becomes `$v`;
    an `arr base idx` (not produced by the scalar path) renders as a form gas
    would reject, surfacing any unexpected use.

    A **register-indexed (SIB) element** `arrIdx base idx scale` (the
    runtime-index image of `stackLoad`/`stackStore`) renders as the x86 effective
    address `(%base, %idx, scale)`: `base` and `idx` are physical GP register
    *names* (always addressed as full 64-bit registers in a SIB), and `scale` is
    the compile-time element stride in bytes (1/2/4/8 — the only scales x86 SIB
    encodes). This is the text-path analogue of `LprogBytes`' SIB encoder: a
    `LOADIDX` reads `dst ← (%base,%idx,scale)`, a `STOREIDX` writes
    `(%base,%idx,scale) ← src`. -/
def resolveOperand (frame spillW w : Nat) (o : LOperand)
    (qsaveB : Nat := qsaveBytes) : String :=
  match o with
  | .reg n => resolveName frame spillW w n qsaveB
  | .imm v => "$" ++ toString v
  | .arr b i => "<ARR:" ++ b ++ "[" ++ toString i ++ "]>"
  | .arrIdx b i s =>
      "(" ++ gpReg64 b ++ ", " ++ gpReg64 i ++ ", " ++ toString s ++ ")"

/-- True iff the resolved-name string denotes a **memory** operand (a spill `k.N`,
    qsave `X`, or `mem.<base>.<off>` reference), as opposed to a bare register.
    Used by the narrow-width (`u16`/`u8`) ABI MOV arm to discriminate a load (the
    memory operand is the *source*, so zero-extend `movz{w,b}l`) from a store (the
    memory operand is the *destination*, so a narrow `mov{w,b}`). -/
def isMemOperand : LOperand → Bool
  | .reg n => "k.".isPrefixOf n || "qsave.".isPrefixOf n || "mem.".isPrefixOf n
  | .arr _ _ => true
  | .arrIdx _ _ _ => true
  | .imm _ => false

/-- True iff the operand is a **vector spill slot** `kv.N` (a `%rsp`-relative
    32-byte YMM stack cell). Distinct from `isMemOperand` (GP `k.N` / qsave /
    `mem.<base>`); used by the packed-op legalizer to detect an illegal
    memory-destination or memory-to-memory YMM move. -/
def isVSpill : LOperand → Bool
  | .reg n => "kv.".isPrefixOf n
  | _ => false

/-- True iff the operand resolves to any memory location (GP spill / qsave /
    `mem.<base>` / vector spill). -/
def isAnyMem (o : LOperand) : Bool := isMemOperand o || isVSpill o

/-- The `%rsp`-relative operand of the vector-spill legalization scratch cell
    (slot `0` of the vector region): the 32-byte stack cell into which `%ymm15` is
    saved before it is borrowed as the bounce register for an illegal
    memory-destination vector op or a memory-to-memory `vmovdqu`, and from which it
    is restored after. Using a save/restore cell rather than a reserved register
    keeps every non-vector-spilling kernel's register allocation unchanged. -/
def vecSpillScratch : String := "0(%rsp)"

/-- The bounce register borrowed for vector-spill legalization: `%ymm15`, saved to
    `vecSpillScratch` around each use so no register is reserved. -/
def vecSpillReg : String := "%ymm15"

/-! ## 3. Mnemonic map: owned-RA body opcode → AT&T mnemonic + size suffix

The body mnemonics are the textual jasmin opcodes from
`JasminLprogExport.binOpName` / `opToLinstrR` (`ADD … SHR`, `MOV`, `MOVQ`,
`LOAD`/`STORE`), optionally carrying a `:64` width tag (`stripWidthTag` peels it).
Each maps to one AT&T mnemonic with the `l` (U32) or `q` (U64) size suffix. The
two-address `MUL` is x86 `IMUL` (signed/unsigned agree on the low word). The
constant-time conditional-move class `CMOVcc` is the branchless select a
*secret* condition must take (the move is unconditional, only the value is
selected) — the GE-solve pivot-swap primitive for MAYO/UOV/SNOVA sign. -/

/-- The op width (in bits) of a body mnemonic: 64 iff it carries the `:64` tag
    (or is the 64-bit-only `MOVQ`), 16 for `:16`, 8 for `:8`, else 32. The narrow
    tags `:16`/`:8` are carried only by the **ABI load/store** MOV of a narrow
    (`u16`/`u8`) buffer (the Frodo `uint16_t` ABI seam); the body
    *arithmetic* stays at its natural register width (low bits exact). -/
def mnemWidth (opn : String) : Nat :=
  if hasSuffix opn ":64" || opn = "MOVQ" then 64
  else if hasSuffix opn ":16" then 16
  else if hasSuffix opn ":8" then 8
  else 32

/-- Strip the width tag (`:64`, `:16`, `:8`) from a body mnemonic to recover the
    base opcode. The upstream `JasminLprogExport.stripWidthTag` only peels `:64`
    (the only tag the verified two-address legalizer ever sees); the printer also
    needs to recover the base of the narrow ABI MOVs `MOV:16`/`MOV:8`, so
    this printer-local stripper handles all three widths without disturbing the
    legalizer's tag alphabet. -/
def stripAbiTag (opn : String) : String :=
  if hasSuffix opn ":16" || hasSuffix opn ":8" then
    String.ofList (opn.toList.takeWhile (· != ':'))
  else stripWidthTag opn

/-- The AT&T size suffix for an op width (`q` for U64, `w` for U16, `b` for U8,
    `l` for U32). -/
def sizeSuffix (w : Nat) : String :=
  if w = 64 then "q" else if w = 16 then "w" else if w = 8 then "b" else "l"

/-- The AT&T base mnemonic (no size suffix) for a stripped body opcode. `none`
    for an unmodeled opcode (call), which the renderer surfaces.

    The compare class `CMP`/`TEST` is the GP-ALU flag-setting head of a
    branch: `CMP` is `SUB` discarding its result (it sets `ZF`/`CF`/`OF`/`SF`
    exactly like the differentially-validated `x86_SUB` in `JasminModel`), and
    `TEST` is the analogous `AND`-discarding-result form. They render as the
    flag-only `cmp<sz>` / `test<sz>` that a following `Lcond` Jcc reads. -/
def attBase : String → Option String
  | "ADD" => some "add" | "SUB" => some "sub"
  -- Carry/borrow-chain GP-ALU adds (single CF chain): `ADC dst, src` =
  -- `dst + src + CF`, `SBB dst, src` = `dst - src - CF`. These are the
  -- one-flag bignum add/sub chain (the `mpn_sub_n` borrow chain, and the `adc`
  -- variant of a plain add) — distinct from the two-flag ADX `ADCX`/`ADOX`.
  | "ADC" => some "adc" | "SBB" => some "sbb"
  | "AND" => some "and" | "OR"  => some "or" | "XOR" => some "xor"
  -- BMI1 `andn` (#instruction-selection lever): the **3-operand, non-destructive**
  -- VEX form `dst := (~a) & b`. Unlike the two-address `AND` (which needs a
  -- destructive `dst &= src` plus a separate `mov;not`/`xor-mask` to negate the
  -- first operand), `andn` fuses the complement and the and into one instruction
  -- with a distinct destination — the gcc `-march=native` codegen for the Keccak
  -- χ step `(~B[x+1]) & B[x+2]`. Because it writes `dst` directly (not a
  -- self-source), it is rendered by the dedicated 3-operand `renderLopn` arm
  -- (`Lopn [d] "ANDN" [a, b]` → `andnq b, a, d`), NOT the two-address arm, and is
  -- excluded from the two-address legalizer's `isBinop` alphabet.
  | "ANDN" => some "andn"
  | "SHL" => some "shl" | "SHR" => some "shr"
  | "MUL" => some "imul"
  | "MOV" => some "mov" | "MOVQ" => some "mov"
  | "LOAD" => some "mov" | "STORE" => some "mov"
  -- ZEROEXT/TRUNC are not produced by the carry-free hash/Poseidon2 bodies.
  | "TRUNC" => some "mov"
  -- Compare class: the flag-setting head of a branch.
  | "CMP" => some "cmp" | "TEST" => some "test"
  -- ADX carry-chain class. `ADCX dst, src` adds `src + CF` into
  -- `dst` and writes CF only (leaves OF); `ADOX dst, src` adds `src + OF` into
  -- `dst` and writes OF only (leaves CF). Two independent carry chains so a
  -- bignum add/addmul keeps two carries in flight with no flag spill. The
  -- carry-in is the flag (not a printed operand): the IR's third source (the
  -- `reg 1` carry bit) is dropped at render time, exactly as gas/x86 implicitly
  -- threads CF/OF. `ADCXHI`/`ADOXHI` are the IR's carry-out *bindings* (the
  -- SSA image of the post-op flag); they are NOT separate instructions — the
  -- flag is produced as a side effect of the matching `ADCX`/`ADOX`, so they
  -- render to no line (the renderLinstrR `ADCXHI`/`ADOXHI` arm drops them). -/
  | "ADCX" => some "adcx" | "ADOX" => some "adox"
  -- Constant-time conditional move class. `CMOVcc dst, src` is the
  -- branchless select `dst := cc(flags) ? src : dst`: the move *issues
  -- unconditionally* (no PC divergence, no secret-dependent branch), only the
  -- written value is selected by the flag the preceding `CMP`/`SUB`/`TEST`/`AND`
  -- set. This is the data-oblivious primitive the multivariate-signature
  -- GE-solve pivot swap needs (a masked conditional swap of two field elements);
  -- it renders exactly like a two-address binop (`cmov<cc><sz> src, dst`, with
  -- `dst` the implicit self-source of the `[d] CMOVcc [d, s]` two-address form),
  -- so it flows through the existing two-source `renderLopn` arm. The condition
  -- code names match the GP-ALU compare class: `CMOVE`/`CMOVNE` read `ZF`,
  -- `CMOVB`/`CMOVAE` read `CF`, the signed `CMOVL`/`CMOVGE` read `SF^OF`. Unlike
  -- `Lcond` (a Jcc on a *public* count), `CMOVcc` is the form a *secret*
  -- condition must take — the move is unconditional, so there is no timing
  -- channel. The value semantics is pinned by `JasminModel.x86_CMOVcc`
  -- (`if b then src else dst`); the matching `JInstr.cmove`/`cmovne`/`cmovb`
  -- arms already carry it, so a hand-built `Lcmd` swap transcribes a
  -- `native_decide`-pinned `JInstr` body (the KAT pattern `MpnLoopEmit`/
  -- `MAYO.VerifyEmit` use).
  | "CMOVE"  => some "cmove"  | "CMOVNE" => some "cmovne"
  | "CMOVB"  => some "cmovb"  | "CMOVAE" => some "cmovae"
  | "CMOVL"  => some "cmovl"  | "CMOVGE" => some "cmovge"
  -- Effective-address load `LEA dst, mem` (array-ABI orchestration). The
  -- pointer-passing marshaling around an opaque `extCall` over `.stackArr` G1/G2/GT
  -- operands (`ArrAbiOrch.comToLfundefArrAbi`) computes the address of each array
  -- buffer — an input slot `mem.RDI.off` / `mem.RSI.off` or a frame scratch
  -- `mem.RSP.off` — into the SysV argument register, then `call`s the leaf. The
  -- single-source arm resolves the memory operand to its AT&T effective address and
  -- emits `leaq <addr>, <reg>` (no value dereference — `lea` takes the address).
  | "LEA" => some "lea"
  | _ => none

/-- True for the IR carry-out *binding* mnemonics (`ADCXHI`/`ADOXHI`): the SSA
    name of the flag the matching `ADCX`/`ADOX` already produced. They carry no
    x86 instruction of their own (the flag is the data op's side effect), so the
    renderer drops them — emitting a line would double-issue the add. -/
def isCarryOutBinding (opn : String) : Bool :=
  let s := stripWidthTag opn
  s == "ADCXHI" || s == "ADOXHI"

/-- True for the MULX high-word *binding* mnemonic (`MULXHI`): the SSA name of
    the high half of a `mulx`. The matching low half is the producer's
    `regArith .mul` over the same two sources; the `mulx` instruction itself is
    emitted on the low binding (a `MUL` line), and `MULXHI` only names the high
    output, so the renderer drops it (no separate instruction). -/
def isMulHiBinding (opn : String) : Bool :=
  stripWidthTag opn == "MULXHI"

/-! ### Condition-code → Jcc mnemonic map

A `Lcond cond lbl` is the owned-RA conditional jump: branch to `lbl` when the
public condition `cond` holds. The `cond` operand names the x86 condition code
(`reg "NE"`, `reg "E"`, `reg "L"`, …) the preceding `CMP`/`TEST`/`SUB` set; we
map it to the matching `Jcc` mnemonic. The condition is on a **public** value
(a loop/limb count, a counter-zero test) — the constant-time discipline forbids
a secret-dependent branch (those compile to `CMOVcc`, no PC divergence). See the
vartime policy and `Cond.lean`'s public-condition note. -/

/-- The AT&T `Jcc` mnemonic for an x86 condition-code name (`"NE" → "jne"`).
    Covers the signed (`L`/`GE`/`LE`/`G`), unsigned (`B`/`AE`/`BE`/`A`), and
    zero/carry/sign/overflow (`E`/`NE`/`Z`/`NZ`/`C`/`NC`/`S`/`NS`/`O`/`NO`)
    codes. Unknown codes surface as an obviously-wrong mnemonic gas rejects. -/
def attCC : String → String
  | "E"  => "je"  | "Z"  => "je"
  | "NE" => "jne" | "NZ" => "jne"
  | "L"  => "jl"  | "GE" => "jge"
  | "LE" => "jle" | "G"  => "jg"
  | "B"  => "jb"  | "AE" => "jae" | "C" => "jb" | "NC" => "jae"
  | "BE" => "jbe" | "A"  => "ja"
  | "S"  => "js"  | "NS" => "jns"
  | "O"  => "jo"  | "NO" => "jno"
  | other => "j<UNKNOWN-CC:" ++ other ++ ">"

/-! ## 4. One `LinstrR` → AT&T line(s)

The two-address body `Lopn [dst] OP [src]` denotes `dst := dst OP src`, which is
exactly x86's destructive two-address form, so it renders as the single AT&T line
`op<sz> src, dst`. A `MOV`/`MOVQ`/`LOAD`/`STORE` `Lopn [dst] MOV [src]` is the
plain move `mov<sz> src, dst`. The flag-setting side effects the x86 ISA attaches
(the implicit flag lvals `read_linear` synthesises) are not part of the AT&T text
— `gas` adds them per the encoding — so the renderer emits no flag operands. -/

/-- The AT&T `set<cc>` mnemonic of a stripped materialised-comparison opcode
    `SET<cc>` (the image of `JasminOp.cmp` / `JasminOp.cmpImm`), `none` for every
    other opcode. -/
def setccAtt? : String → Option String
  | "SETE" => some "sete" | "SETNE" => some "setne"
  | "SETB" => some "setb" | "SETBE" => some "setbe"
  | "SETA" => some "seta" | "SETAE" => some "setae"
  | _ => none

/-- Render a materialised comparison `Lopn [d] SET<cc> [a, b]`
    (`d := a <cc> b ? 1 : 0`) as

        cmp  b, a        # flags of a - b
        mov  $0, d       # writes no flag
        set<cc> d8       # low byte of d

    The compare runs before `d` is written, so `d` may alias `a` or `b`; `mov`
    and `set<cc>` both accept a spilled `d`. With both compared operands in
    memory the first goes through the reserved scratch `R15`, as for `CMP`. An
    immediate first operand, and a 64-bit immediate outside the sign-extended
    32-bit range `cmp` encodes, render as a comment line gas rejects. -/
def renderSetcc (frame spillW : Nat) (cc : String) (d : LOperand) (opn : String)
    (a b : LOperand) (qsaveB : Nat) : List String :=
  let w := mnemWidth opn
  let sz := sizeSuffix w
  let aOp := resolveOperand frame spillW w a qsaveB
  let bOp := resolveOperand frame spillW w b qsaveB
  let wideImm := match b with
    | .imm v => w == 64 && v ≥ 2147483648
    | _ => false
  let immFirst := match a with
    | .imm _ => true
    | _ => false
  if immFirst || wideImm then [ "\t# UNHANDLED-SETCC " ++ opn ]
  else
    let cmpLines :=
      if isMemOperand a && isMemOperand b then
        let scratch := resolveName frame spillW w "R15" qsaveB
        [ "\tmov" ++ sz ++ " " ++ aOp ++ ", " ++ scratch,
          "\tcmp" ++ sz ++ " " ++ bOp ++ ", " ++ scratch ]
      else [ "\tcmp" ++ sz ++ " " ++ bOp ++ ", " ++ aOp ]
    -- A spill cell is cleared at the body-uniform spill width, so a later reload
    -- of the whole cell reads `0` or `1`.
    let dw := match d with
      | .reg n => if "k.".isPrefixOf n then max w spillW else w
      | _ => w
    cmpLines ++
      [ "\tmov" ++ sizeSuffix dw ++ " $0, " ++ resolveOperand frame spillW dw d qsaveB,
        "\t" ++ cc ++ " " ++ resolveOperand frame spillW 8 d qsaveB ]

/-- The AT&T mnemonic of a two-source 256-bit `YmmOp` rendered by the
    operand-order-preserving arm of `renderLopn` (`src2, src1, dst`, with only
    the first AT&T operand allowed in memory). Matching is on the exact jasmin
    mnemonic, so no name is taken for a prefix of another. -/
def ymmTwoSrcAtt? : String → Option String
  | "VPADDW" => some "vpaddw"
  | "VPSUBW" => some "vpsubw"
  | "VPMULLW" => some "vpmullw"
  | "VPMULHW" => some "vpmulhw"
  | "VPMADDWD" => some "vpmaddwd"
  | "VPCMPGTW" => some "vpcmpgtw"
  | "VPCMPGTD" => some "vpcmpgtd"
  | "VPCMPEQD" => some "vpcmpeqd"
  | "VPSIGND" => some "vpsignd"
  | "VPACKSSWB" => some "vpacksswb"
  | "VPACKSSDW" => some "vpackssdw"
  | "VPERMD" => some "vpermd"
  | "VPUNPCKLDQ" => some "vpunpckldq"
  | "VPUNPCKHDQ" => some "vpunpckhdq"
  | "VPUNPCKLQDQ" => some "vpunpcklqdq"
  | "VPUNPCKHQDQ" => some "vpunpckhqdq"
  | _ => none

/-- The AT&T mnemonic of a one-source 256-bit `YmmOp` whose immediate is carried
    in its jasmin mnemonic as `<NAME>:<n>`, keyed on the exact `<NAME>`. -/
def ymmImmUnaryAtt? : String → Option String
  | "VPSLLD" => some "vpslld"
  | "VPSRLD" => some "vpsrld"
  | "VPSRAD" => some "vpsrad"
  | "VPSLLW" => some "vpsllw"
  | "VPSRLW" => some "vpsrlw"
  | "VPSRAW" => some "vpsraw"
  | "VPSRLDQ" => some "vpsrldq"
  | _ => none

/-- The AT&T mnemonic of a two-source 256-bit `YmmOp` whose immediate is carried
    in its jasmin mnemonic as `<NAME>:<n>`, keyed on the exact `<NAME>`. -/
def ymmImmBinaryAtt? : String → Option String
  | "VPBLENDD" => some "vpblendd"
  | "VPBLENDW" => some "vpblendw"
  | "VPERM2I128" => some "vperm2i128"
  | _ => none

/-- The name part of a `<NAME>:<n>` mnemonic. -/
def immOpName (opn : String) : String := (opn.splitOn ":").headD opn

/-- Render one `Lopn dsts opn srcs` (not a carry-out / MULX-hi binding) to its
    AT&T line(s). Handles the three arities the owned-RA body produces:

    * **move** `Lopn [d] MOV/MOVQ/LOAD/STORE [s]` (one source) → `mov<sz> s, d`;
    * **two-address binop/shift** `Lopn [d] OP [d, s]` (two sources, `srcs[0] = d`
      the implicit x86 destination-source) → `op<sz> s, d`;
    * **ADX carry-chain** `Lopn [d] ADCX/ADOX [d, s, cin]` (three sources: the
      dst self-source, the data source, and the `reg 1` carry-in flag) →
      `adcx<sz> s, d` / `adox<sz> s, d`, with the carry-in first reconstructed
      into CF via `bt $0, cin` (dropped only for the fused-flag sentinel, where
      the flag flows directly). The dst self-source is the implicit x86
      destination-source, not a printed operand. -/
def renderLopn (frame spillW : Nat) (rvs : Bool := false)
    (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (qsaveB : Nat := qsaveBytes) : List String :=
  match dsts, opn, srcs with
  -- `SETcc` (`SETC`, set-on-carry → byte GPR, zero-extended): one destination,
  -- **zero** data sources (the carry-in is the implicit `CF` flag, not a printed
  -- operand). Emits the `setb`/`movzbq` pair that realises the model's `setc` arm
  -- (`d := if CF then 1 else 0`): `setb %d8` sets the low byte from CF, `movzbq
  -- %d8, %d64` zero-extends to the full register. The flag-to-GPR materialisation
  -- the open-coded carry chain (`add; setc cy`) needs to keep the carry across the
  -- loop back-edge. Only the register-direct destination is produced
  -- (the carry GPR); a spill/mem destination would surface as the `<UNKNOWN>`
  -- form gas rejects.
  | [.reg d], opn, [] =>
      if stripWidthTag opn == "SETC" then
        [ "\tsetb " ++ gpReg8 d, "\tmovzbq " ++ gpReg8 d ++ ", " ++ gpReg64 d ]
      else [ "\t# UNHANDLED-OP " ++ opn ]
  | [d], opn, [s] =>
      let base := stripAbiTag opn
      -- **YMM packed shift-by-immediate VEX** (batch8): the 256-bit unary packed
      -- logical shifts `VPSLLD:<n>` / `VPSRLD:<n>`, `d := a shift n` per 32-bit
      -- lane. The count `<n>` is carried in the mnemonic (mirroring the ZMM
      -- `VPRORD:<n>` form), so this must precede the `mnemWidth` logic below: a
      -- count of 8/16 would otherwise be misread as a narrow width tag and the
      -- shift dropped. AT&T VEX order `vpslld $<n>, %ymm<a>, %ymm<d>`; the source
      -- operand `XMM<k>` resolves to `%ymm<k>` via `resolveName`.
      if let some mn := ymmImmUnaryAtt? (immOpName opn) then
        match opn.splitOn ":", s, d with
        | [_, nStr], .reg sn, .reg dn =>
            [ "\t" ++ mn ++ " $" ++ nStr ++ ", " ++ resolveName frame spillW 32 sn qsaveB
                ++ ", " ++ resolveName frame spillW 32 dn qsaveB ]
        | _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **YMM cross-/in-lane permutes by immediate** (NTT lane routing):
      -- `VPSHUFD:<n>` (in-lane dword shuffle) / `VPERMQ:<n>` (cross-lane qword
      -- permute), `d := perm s n`. The imm `<n>` is carried in the mnemonic
      -- exactly as the shifts above; AT&T order `vp… $<n>, %ymm<s>, %ymm<d>`.
      else if immOpName opn == "VPSHUFD" || immOpName opn == "VPERMQ" then
        let mn := if immOpName opn == "VPSHUFD" then "vpshufd" else "vpermq"
        match opn.splitOn ":", s, d with
        | [_, nStr], .reg sn, .reg dn =>
            [ "\t" ++ mn ++ " $" ++ nStr ++ ", " ++ resolveName frame spillW 32 sn qsaveB
                ++ ", " ++ resolveName frame spillW 32 dn qsaveB ]
        | _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **VMOVSHDUP** (NTT odd-lane duplicate): `d := dup_odd s`. Single-source
      -- two-operand VEX move, no immediate. AT&T `vmovshdup %ymm<s>, %ymm<d>`.
      else if base == "VMOVSHDUP" || base == "VPABSD" then
        let mn := if base == "VMOVSHDUP" then "vmovshdup" else "vpabsd"
        match s, d with
        | .reg sn, .reg dn =>
            [ "\t" ++ mn ++ " " ++ resolveName frame spillW 32 sn qsaveB
                ++ ", " ++ resolveName frame spillW 32 dn qsaveB ]
        | _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **256-bit vector ABI move** (`VMOVDQU`, batch8 SoA ABI): the packed
      -- input load (`mem → %ymm`) / output store (`%ymm → mem`) and any packed
      -- spill move. The `XMM<k>` operands resolve to `%ymm<k>` (width-independent,
      -- see `resolveName`) and the `mem.<base>.<off>` operand to `off(%base)`; the
      -- unaligned `vmovdqu` handles a C buffer of any alignment. AT&T src,dst order.
      else if base == "VMOVDQU" then
        if isAnyMem s && isAnyMem d then
          -- memory-to-memory YMM move (an ABI load whose destination the RA
          -- placed in a `kv.N` spill): x86 has no mem→mem move, so bounce through
          -- `%ymm15`. When `rvs` (batch8 reserves `%ymm15`) the bounce needs no
          -- save/restore; otherwise it is saved to / restored from `vecSpillScratch`.
          (if rvs then [] else [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch ])
            ++ [ "\tvmovdqu " ++ resolveOperand frame spillW 32 s qsaveB ++ ", " ++ vecSpillReg,
                 "\tvmovdqu " ++ vecSpillReg ++ ", " ++ resolveOperand frame spillW 32 d qsaveB ]
            ++ (if rvs then [] else [ "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ])
        else
          [ "\tvmovdqu " ++ resolveOperand frame spillW 32 s qsaveB ++ ", "
              ++ resolveOperand frame spillW 32 d qsaveB ]
      else if (base == "MOV" || base == "MOVQ")
              && (match s with | .reg n => "XMM".isPrefixOf n | _ => false)
              && !isAnyMem d then
        -- A plain `MOV` reading a packed vector register into a GP register: the
        -- dead return-value materialization for a memory-return (`lfd_res = []`)
        -- kernel — the batch8 body's `comRetReg` is a vector slot, but the result
        -- is returned through memory, so `%rax` is ignored. Render the valid
        -- `movq %xmm<k>, <gp>` (low-64 extract) rather than the ill-formed
        -- `movq %ymm<k>, …` gas rejects.
        match s with
        | .reg sn =>
            [ "\tmovq %xmm" ++ (sn.drop 3).toString ++ ", "
                ++ resolveOperand frame spillW 64 d qsaveB ]
        | _ => [ "\t# UNHANDLED-VMOV " ++ opn ]
      else
      -- **imm64 store** (the fri_proof Merkle u64 mixer constants, the
      -- Ed25519 point-add constant): x86 has no imm64-to-memory encoding
      -- (`movq $imm, mem` takes a SIGN-EXTENDED imm32, so gas rejects any value
      -- ≥ 2³¹), and every GP register is in the RA pool. The constant is loaded
      -- into a borrowed register saved at the bottom of the red zone, with the
      -- save/restore discipline of the spilled `cmov`/`adcx` destinations below
      -- (call-free leaves; the export's red-zone stash slots sit at `-8·k`,
      -- never at `-128`), and stored as one 64-bit word:
      --
      --   movq scratch, -128(%rsp)
      --   movq $v, scratch        ; gas selects the imm64 `movabs` encoding
      --   movq scratch, [d]
      --   movq -128(%rsp), scratch
      --
      -- No instruction writes a flag. The scratch avoids the text of `[d]`
      -- (its base register, for a `mem.<base>` destination). Register
      -- destinations stay on the generic arm, whose `movq $v, %reg` gas also
      -- assembles as `movabs`.
      let imm64Store : Option Nat :=
        match s, attBase base with
        | .imm v, some "mov" =>
            if v > 0x7FFFFFFF && mnemWidth opn == 64 && isMemOperand d then some v
            else none
        | _, _ => none
      if let some v := imm64Store then
        let dOp := resolveOperand frame spillW 64 d qsaveB
        let freeOf : String → Bool := fun cand => (dOp.splitOn cand).length == 1
        let scratch :=
          if freeOf "%rax" then "%rax"
          else if freeOf "%rbx" then "%rbx"
          else if freeOf "%rcx" then "%rcx"
          else "%rdx"
        [ "\tmovq " ++ scratch ++ ", -128(%rsp)",
          "\tmovq $" ++ toString v ++ ", " ++ scratch,
          "\tmovq " ++ scratch ++ ", " ++ dOp,
          "\tmovq -128(%rsp), " ++ scratch ]
      else
      -- **Native immediate shift / rotate**: the count is carried
      -- IN the mnemonic (`SHR:n` / `SHL:n` / `SAR:n` / `ROR:n` / `ROL:n`, from
      -- `.shrImm` / … ), not as a source operand. This MUST be checked before the
      -- `mnemWidth`/narrow-ABI-MOV logic below: the count separator `:` collides
      -- with the `:8`/`:16`/`:64` width tags, so a count of 8/16/64 (`SHR:16`) is
      -- otherwise misread as a 16-bit width and rendered as `movw` with the shift
      -- dropped (the Hawk `t1 >> 16` bug). `parseImmShiftMnem` reads the count and
      -- the real width off the raw mnemonic. Render `op<sz> $n, %d` (prepending a
      -- `mov` when the source register differs from the destination).
      if let some (m, n, w) := parseImmShiftMnem opn then
        let dop := resolveOperand frame spillW w d qsaveB
        let sop := resolveOperand frame spillW w s qsaveB
        -- **Shift/rotate-by-0 peephole (dead-instruction drop).** A shift or
        -- rotate by 0 is the identity on the destination value (`x << 0 = x`,
        -- `x >> 0 = x`, `ror/rol x, 0 = x` — and none of these five write a flag
        -- that a following `Lcond` reads, since the body's flag consumers are
        -- fed by the `CMP`/`TEST`/`SUB` compare class, not by a by-0 shift). The
        -- front inserts one such identity `shlImm 0` per `RScalarSetExpr`
        -- binding, and the printer used to emit it verbatim (~1500 `shlq $0`
        -- no-ops in the FriFold `.s`). Drop it: a pure self-shift (`sop == dop`)
        -- emits nothing; a rebind (`sop ≠ dop`) degenerates to the copy the
        -- binding stands for (`d := s << 0 = s`), so emit only `mov s, d`. This
        -- is behaviour-preserving — the value written to `d` is identical — and
        -- removes every `shlq $0` line without touching any live computation.
        if n == 0 then
          if sop == dop then []
          else [ "\tmov" ++ sizeSuffix w ++ " " ++ sop ++ ", " ++ dop ]
        else
        let shiftLine := "\t" ++ m ++ sizeSuffix w ++ " $" ++ toString n ++ ", " ++ dop
        if sop == dop then [ shiftLine ]
        else [ "\tmov" ++ sizeSuffix w ++ " " ++ sop ++ ", " ++ dop, shiftLine ]
      else
      -- **LOADIDX / STOREIDX**: the register-indexed (SIB) array element.
      -- `LOADIDX [.arrIdx base idx scale]` reads `d ← (%base,%idx,scale)`;
      -- `STOREIDX` (3-arity form below handles the value; this single-source form
      -- is the load) renders the SIB source operand directly. The element-access
      -- width is the SIB scale (1/2/4/8 bytes), so the GP register `d` is sized by
      -- `scale·8` — a `u16` table lookup (`scale = 2`) zero-extends (`movzwl`), a
      -- `u32`/`u64` element is a plain `movl`/`movq`.
      if base == "LOADIDX" then
        match s with
        | .arrIdx _ _ scale =>
            let lw := scale * 8
            let dstW := if lw < 32 then 32 else lw
            if lw == 16 then
              [ "\tmovzwl " ++ resolveOperand frame spillW 64 s qsaveB ++ ", "
                  ++ resolveOperand frame spillW 32 d qsaveB ]
            else if lw == 8 then
              [ "\tmovzbl " ++ resolveOperand frame spillW 64 s qsaveB ++ ", "
                  ++ resolveOperand frame spillW 32 d qsaveB ]
            else
              [ "\tmov" ++ sizeSuffix dstW ++ " "
                  ++ resolveOperand frame spillW 64 s qsaveB ++ ", "
                  ++ resolveOperand frame spillW dstW d qsaveB ]
        | _ => [ "\t# UNHANDLED-LOADIDX " ++ opn ]
      -- **ZEROEXT / TRUNC** (cast_demo): a cross-width cast. `ZEROEXT` is the
      -- widening zero-extend (`movzx`), `TRUNC` the narrowing low-bits keep. The
      -- cast op does not carry its source width in the mnemonic, so the renderer
      -- assumes the narrowing/widening crosses the **byte** boundary (the cast_demo
      -- `u32 → u8 → u32` round-trip, value `x & 0xff`): `TRUNC` renders as
      -- `movzbl %src8, %dst32` (mask to the low byte — the truncation composed with
      -- the byte mask the FIPS digest byte-extract needs), and `ZEROEXT` as the
      -- same byte zero-extend of its (already-low-byte) source. Composing the two
      -- yields exactly `x & 0xff` (`castDemoCom_denote`). Both registers are 32-bit
      -- GP allocations, so the 8-bit subregister `%<reg>b` (`gpReg8`) sources the
      -- `movzbl` and the 32-bit `%<reg>d` (`gpReg32`) is its destination.
      -- **`CASTW_<w>_<w'>`** — a cast between 32- and 64-bit registers, both
      -- widths carried in the mnemonic. Writing a 32-bit register clears the
      -- upper half, so `movl` is both the 32 → 64 zero-extend and the 64 → 32
      -- truncation; a 64 → 64 cast is a register copy at full width. The widths
      -- are read off the **raw** `opn`: the `_` separator cannot be mistaken for
      -- a `:64` width tag, which `base` (`stripAbiTag opn`) would have peeled.
      else if let some (sw, dw) := parseCastWMnem opn then
        match s, d with
        | .reg sn, .reg dn =>
            if sw == 64 && dw == 64 then
              [ "\tmovq " ++ gpReg64 sn ++ ", " ++ gpReg64 dn ]
            else
              [ "\tmovl " ++ gpReg32 sn ++ ", " ++ gpReg32 dn ]
        | _, _ => [ "\t# UNHANDLED-CAST " ++ opn ]
      else if base == "ZEROEXT" || base == "TRUNC" then
        match s, d with
        | .reg sn, .reg dn => [ "\tmovzbl " ++ gpReg8 sn ++ ", " ++ gpReg32 dn ]
        | _, _ => [ "\t# UNHANDLED-CAST " ++ opn ]
      else
      let w := mnemWidth opn
      -- **Narrow ABI MOV** (`MOV:16` / `MOV:8`, Frodo): the load/store of a
      -- narrow (`u16`/`u8`) ABI buffer. A 32-bit `movl` to a `uint16_t` slot
      -- overruns the adjacent element by 2 bytes (the Frodo gap). Discriminate by
      -- operand class: a **memory source** is a LOAD ⇒ zero-extend `movz{w,b}l`
      -- into the 32-bit working register (the body arithmetic is 32-bit, low bits
      -- exact); a **memory destination** is a STORE ⇒ a width-exact `mov{w,b}` that
      -- writes only the narrow slot. A register↔register narrow MOV falls back to a
      -- plain `mov{w,b}` (rare — the ABI seam is always one memory side).
      if w == 16 || w == 8 then
        if isMemOperand s && !isMemOperand d then
          -- load: zero-extend narrow memory → 32-bit working reg
          let zext := if w == 16 then "movzwl" else "movzbl"
          [ "\t" ++ zext ++ " " ++ resolveOperand frame spillW w s qsaveB ++ ", "
              ++ resolveOperand frame spillW 32 d qsaveB ]
        else if isMemOperand d && !isMemOperand s then
          -- store: width-exact narrow write (no overrun)
          [ "\tmov" ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s qsaveB ++ ", "
              ++ resolveOperand frame spillW w d qsaveB ]
        else
          [ "\tmov" ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s qsaveB ++ ", "
              ++ resolveOperand frame spillW w d qsaveB ]
      else
      -- **Native immediate shift / rotate** fallback. The primary shift handler
      -- runs at the top of this arm (`parseImmShiftMnem`, off the raw mnemonic) so
      -- that counts of 8/16/64 are not swallowed by `stripAbiTag`/`mnemWidth`. This
      -- `base`-driven arm therefore only fires for a count that survived
      -- `stripAbiTag` intact (a non-{8,16,64} count, e.g. `SHR:7`); it is kept as a
      -- belt-and-braces path and is byte-identical to the primary handler for such
      -- counts. Render `op<sz> $n, %d` (prepending a `mov` when src ≠ dst).
      match base.splitOn ":" with
      | [mn, nStr] =>
          let immMn : Option String := match mn with
            | "ROR" => some "ror" | "ROL" => some "rol"
            | "SHL" => some "shl" | "SHR" => some "shr" | "SAR" => some "sar"
            | _ => none
          match immMn with
          | some m =>
              let dop := resolveOperand frame spillW w d qsaveB
              let sop := resolveOperand frame spillW w s qsaveB
              -- Shift/rotate-by-0 peephole (same identity-drop as the primary
              -- `parseImmShiftMnem` arm above): a count of 0 is the identity, so a
              -- self-shift emits nothing and a rebind degenerates to `mov s, d`.
              -- This fallback arm handles the front's identity `shlImm 0` copies
              -- that reach it (the ~1500 `shlq $0` no-ops), which the primary arm
              -- does not swallow.
              if nStr == "0" then
                if sop == dop then []
                else [ "\tmov" ++ sizeSuffix w ++ " " ++ sop ++ ", " ++ dop ]
              else
              let shiftLine := "\t" ++ m ++ sizeSuffix w ++ " $" ++ nStr ++ ", " ++ dop
              if sop == dop then [ shiftLine ]
              else [ "\tmov" ++ sizeSuffix w ++ " " ++ sop ++ ", " ++ dop, shiftLine ]
          | none => [ "\t# UNHANDLED-OP " ++ opn ]
      | _ =>
      match attBase base with
      | some m =>
          if isMemOperand s && isMemOperand d then
            -- **Mem-to-mem legalization** (backstop): x86 has no memory-to-memory
            -- move, but the only single-source op whose two operands are both
            -- memory is a spilled register copy (`MOV`/`MOVQ`; a `LOAD`/`STORE`
            -- always keeps one side in a register). Split it through the
            -- reserved reload scratch `R15` (`mov src, %r15 ; mov %r15, dst`).
            -- `R15` is excluded from the register allocator's pool
            -- (`gpRegNames`), so no kernel value is ever live in it — the split
            -- is behaviour-preserving. The upstream `physBodyRmap` legalizer
            -- already routes two-spill (`k.N`) `MOV`s through `R15`; this arm
            -- additionally covers a two-`mem.` frame copy, so the printer never
            -- emits an illegal `mov mem, mem` regardless of the operand class.
            [ "\t" ++ m ++ sizeSuffix w ++ " "
                ++ resolveOperand frame spillW w s qsaveB ++ ", " ++ resolveName frame spillW w "R15" qsaveB,
              "\t" ++ m ++ sizeSuffix w ++ " "
                ++ resolveName frame spillW w "R15" qsaveB ++ ", " ++ resolveOperand frame spillW w d qsaveB ]
          else
          [ "\t" ++ m ++ sizeSuffix w ++ " "
              ++ resolveOperand frame spillW w s qsaveB ++ ", " ++ resolveOperand frame spillW w d qsaveB ]
      | none => [ "\t# UNHANDLED-OP " ++ opn ]
  -- BMI1 `andn` (`ANDN`): the **non-destructive 3-operand** form. Both sources
  -- are real (neither is a `dst` self-source), and `dst` is written directly:
  -- `Lopn [d] "ANDN" [a, b]` denotes `d := (~a) & b`. AT&T VEX operand order is
  -- `andn<sz> b, a, d` (`andn src2, src1, dst` ⇒ `dst = ~src1 & src2`), so the
  -- two sources are emitted in *reverse* of their IR order (`b` then `a`), unlike
  -- the destructive two-address arm. This must precede the generic two-source arm
  -- (it also has two sources) so the ANDN operand order wins.
  | [d], opn, [a, b] =>
      -- **VPACK**: the AVX-512 ZMM packed-lane add `VPACK8u64:ADD` (8×u64,
      -- `vpaddq`) / `VPACK16u32:ADD` (16×u32, `vpaddd`). 3-operand AVX form
      -- `vpadd{q,d} %zmmB, %zmmA, %zmmD` (`src2, src1, dst`). The operands must be
      -- ZMM names (`vN`) — the owned GP-linear RA cannot allocate a 512-bit value
      -- to a vector register (the u512 blocker), so this arm renders only a
      -- vector-RA / hand-built `Lcmd`; a GP-allocated operand surfaces as the
      -- `%<NOTZMM>` form gas rejects. The lane width selects the suffix: a `u64`
      -- mnemonic → `vpaddq`, a `u32` mnemonic → `vpaddd`.
      -- The materialised comparison `SET<cc>` is rendered by `renderSetcc`.
      if (setccAtt? (stripWidthTag opn)).isSome then
        renderSetcc frame spillW ((setccAtt? (stripWidthTag opn)).getD "") d opn a b qsaveB
      else if "VPACK8u64:".isPrefixOf opn || "VPACKD:".isPrefixOf opn then
        let mn := if (opn.splitOn "u32").length > 1 then "vpaddd" else "vpaddq"
        match a, b, d with
        | .reg an, .reg bn, .reg dn =>
            [ "\t" ++ mn ++ " " ++ zmmReg bn ++ ", " ++ zmmReg an ++ ", " ++ zmmReg dn ]
        | _, _, _ => [ "\t# UNHANDLED-VPACK " ++ opn ]
      -- **YMM packed binary VEX ALU** (batch8): the 256-bit two-source packed
      -- add / bitwise ops `VPADDD` / `VPXOR` / `VPOR` / `VPAND`, `d := a OP b`.
      -- AT&T VEX 3-operand order is `src2, src1, dst`, so the sources print in
      -- reverse of their IR order (`b` then `a`): `vpxor %ymm<b>, %ymm<a>,
      -- %ymm<d>`. Operands are `XMM<k>` names resolved to `%ymm<k>` by
      -- `resolveName` (the packed-lane width is fixed by the mnemonic, so the
      -- scalar width argument is immaterial).
      -- The commutative set also carries the packed multiplies and the qword add
      -- (`VPMULDQ` signed 32×32→64, `VPMULUDQ` unsigned, `VPMULLQ` low-64,
      -- `VPADDQ` qword add) — all `a OP b = b OP a`, so the spilled-operand-first
      -- swap is sound for them exactly as for the bitwise ops.
      else if opn == "VPADDD" || opn == "VPXOR" || opn == "VPOR"
              || opn == "VPAND" || opn == "VPADDQ" || opn == "VPMULDQ"
              || opn == "VPMULUDQ" || opn == "VPMULLQ" || opn == "VPMULLD" then
        let mn := if opn == "VPADDD" then "vpaddd"
                  else if opn == "VPXOR" then "vpxor"
                  else if opn == "VPOR" then "vpor"
                  else if opn == "VPAND" then "vpand"
                  else if opn == "VPADDQ" then "vpaddq"
                  else if opn == "VPMULDQ" then "vpmuldq"
                  else if opn == "VPMULUDQ" then "vpmuludq"
                  else if opn == "VPMULLD" then "vpmulld"
                  else "vpmullq"
        match a, b, d with
        | .reg an, .reg bn, .reg dn =>
            -- AT&T VEX order is `mn <first>, <second>, <dest>` with `<first>` = `b`,
            -- `<second>` = `a`. x86 requires `<dest>` and `<second>` to be
            -- registers; `<first>` may be memory. These packed ops are commutative,
            -- so a spilled operand is placed in the first (memory-allowed) slot by
            -- swapping the two sources, and a spilled destination is computed into
            -- `%ymm15` (saved to / restored from `vecSpillScratch`) then stored.
            let bStr := resolveName frame spillW 32 bn qsaveB
            let aStr := resolveName frame spillW 32 an qsaveB
            let dStr := resolveName frame spillW 32 dn qsaveB
            let mB := isAnyMem b   -- first AT&T source in memory?
            let mA := isAnyMem a   -- second AT&T source in memory?
            if isVSpill d then
              -- spilled dest: compute into %ymm15 (saved/restored), then store.
              -- At most one source is memory here (no all-three-memory op occurs);
              -- put the memory source first (commutative) so the second is a reg.
              let (x, y) := if mA then (aStr, bStr) else (bStr, aStr)
              (if rvs then [] else [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch ])
                ++ [ "\t" ++ mn ++ " " ++ x ++ ", " ++ y ++ ", " ++ vecSpillReg,
                     "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr ]
                ++ (if rvs then [] else [ "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ])
            else if mA && mB then
              -- both sources in memory, register dest: use the dest register as the
              -- accumulator — load the first source into it, then apply the op with
              -- the second source as the (memory-allowed) first operand.
              [ "\tvmovdqu " ++ bStr ++ ", " ++ dStr,
                "\t" ++ mn ++ " " ++ aStr ++ ", " ++ dStr ++ ", " ++ dStr ]
            else if mA then
              -- only the second source is memory: swap so it is first.
              [ "\t" ++ mn ++ " " ++ aStr ++ ", " ++ bStr ++ ", " ++ dStr ]
            else
              [ "\t" ++ mn ++ " " ++ bStr ++ ", " ++ aStr ++ ", " ++ dStr ]
        | _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **YMM packed variable per-lane shift** (batch8 rotations): `VPSLLVD` /
      -- `VPSRLVD`, `d := data (<<|>>) count` lane-wise. The `Lopn` sources are
      -- `[data, count]`; AT&T VEX order is `mn <count>, <data>, <dst>` (count =
      -- src2 = first, may be memory; data = src1 and dst must be registers). NOT
      -- commutative, so a spilled `data`/`dst` is bounced through `%ymm15`
      -- (saved/restored to `vecSpillScratch`); a spilled `count` stays memory.
      else if opn == "VPSLLVD" || opn == "VPSRLVD" then
        let mn := if opn == "VPSLLVD" then "vpsllvd" else "vpsrlvd"
        match a, b, d with
        | .reg an, .imm n, .reg dn =>
            -- constant shift count: the per-lane counts are all `n`, so render the
            -- immediate form `vpslld/vpsrld $n, <data>, <dst>` (data may be memory;
            -- a spilled dst bounces through %ymm15).
            let mnImm := if opn == "VPSLLVD" then "vpslld" else "vpsrld"
            let dataStr := resolveName frame spillW 32 an qsaveB
            let dStr := resolveName frame spillW 32 dn qsaveB
            if isVSpill d then
              (if rvs then [] else [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch ])
                ++ [ "\t" ++ mnImm ++ " $" ++ toString n ++ ", " ++ dataStr ++ ", " ++ vecSpillReg,
                     "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr ]
                ++ (if rvs then [] else [ "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ])
            else
              [ "\t" ++ mnImm ++ " $" ++ toString n ++ ", " ++ dataStr ++ ", " ++ dStr ]
        | .reg an, .reg bn, .reg dn =>
            let cStr := resolveName frame spillW 32 bn qsaveB   -- count (first AT&T)
            let dataStr := resolveName frame spillW 32 an qsaveB -- data (second AT&T)
            let dStr := resolveName frame spillW 32 dn qsaveB    -- dst
            let mData := isVSpill a
            let mDst := isVSpill d
            if mDst && mData then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\tvmovdqu " ++ dataStr ++ ", " ++ vecSpillReg,
                "\t" ++ mn ++ " " ++ cStr ++ ", " ++ vecSpillReg ++ ", " ++ vecSpillReg,
                "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else if mDst then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\t" ++ mn ++ " " ++ cStr ++ ", " ++ dataStr ++ ", " ++ vecSpillReg,
                "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else if mData then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\tvmovdqu " ++ dataStr ++ ", " ++ vecSpillReg,
                "\t" ++ mn ++ " " ++ cStr ++ ", " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else
              [ "\t" ++ mn ++ " " ++ cStr ++ ", " ++ dataStr ++ ", " ++ dStr ]
        | _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **YMM packed subtract** (NTT butterflies): `VPSUBD` / `VPSUBQ`,
      -- `d := a - b` lane-wise. NOT commutative, so the operand roles are fixed:
      -- AT&T VEX order `vpsub{d,q} <b>, <a>, <d>` computes `d = a - b`, where `b`
      -- (src2, first) may be memory and `a` (src1, second) and `d` must be
      -- registers — the same spill posture as `VPSLLVD`'s data/count split with
      -- `a` in the data (must-be-reg) role and `b` in the count (may-be-mem) role.
      else if opn == "VPSUBD" || opn == "VPSUBQ" || opn == "VPANDN"
              || (ymmTwoSrcAtt? opn).isSome then
        let mn := if opn == "VPSUBD" then "vpsubd"
                  else if opn == "VPSUBQ" then "vpsubq"
                  else if opn == "VPANDN" then "vpandn"
                  else (ymmTwoSrcAtt? opn).getD "vpandn"
        match a, b, d with
        | .reg an, .reg bn, .reg dn =>
            let bStr := resolveName frame spillW 32 bn qsaveB    -- b = src2 (first, may be mem)
            let aStr := resolveName frame spillW 32 an qsaveB     -- a = src1 (second, reg)
            let dStr := resolveName frame spillW 32 dn qsaveB      -- dst (reg)
            let mA := isVSpill a
            let mDst := isVSpill d
            if mDst && mA then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\tvmovdqu " ++ aStr ++ ", " ++ vecSpillReg,
                "\t" ++ mn ++ " " ++ bStr ++ ", " ++ vecSpillReg ++ ", " ++ vecSpillReg,
                "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else if mDst then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\t" ++ mn ++ " " ++ bStr ++ ", " ++ aStr ++ ", " ++ vecSpillReg,
                "\tvmovdqu " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else if mA then
              [ "\tvmovdqu " ++ vecSpillReg ++ ", " ++ vecSpillScratch,
                "\tvmovdqu " ++ aStr ++ ", " ++ vecSpillReg,
                "\t" ++ mn ++ " " ++ bStr ++ ", " ++ vecSpillReg ++ ", " ++ dStr,
                "\tvmovdqu " ++ vecSpillScratch ++ ", " ++ vecSpillReg ]
            else
              [ "\t" ++ mn ++ " " ++ bStr ++ ", " ++ aStr ++ ", " ++ dStr ]
        | _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      -- **VPBLENDD:<n>** (NTT lane recombine): `d := blend a b n`, per-dword
      -- select `dst[i] = imm[i] ? b[i] : a[i]`. NOT commutative (the immediate
      -- fixes the operand roles), so no spilled-operand swap. AT&T VEX order
      -- `vpblendd $<n>, <b>, <a>, <d>` (src2 = b, src1 = a, dst = d).
      else if let some mn := ymmImmBinaryAtt? (immOpName opn) then
        match opn.splitOn ":", a, b, d with
        | [_, nStr], .reg an, .reg bn, .reg dn =>
            [ "\t" ++ mn ++ " $" ++ nStr ++ ", " ++ resolveName frame spillW 32 bn qsaveB
                ++ ", " ++ resolveName frame spillW 32 an qsaveB
                ++ ", " ++ resolveName frame spillW 32 dn qsaveB ]
        | _, _, _, _ => [ "\t# UNHANDLED-VYMM " ++ opn ]
      else if stripAbiTag opn == "ANDN" then
        let w := mnemWidth opn
        [ "\tandn" ++ sizeSuffix w ++ " "
            ++ resolveOperand frame spillW w b qsaveB ++ ", "
            ++ resolveOperand frame spillW w a qsaveB ++ ", "
            ++ resolveOperand frame spillW w d qsaveB ]
      -- **STOREIDX**: the register-indexed (SIB) array element store. Sources
      -- are `[.arrIdx base idx scale, val]` — the SIB destination and the stored
      -- value; the `Lopn` destination `d` names the functionally-updated array (the
      -- dialect's `stackStore` returns the new array), so it is NOT an x86 operand.
      -- AT&T order is `mov<sz> %val, (%base,%idx,scale)` with `<sz>` fixed by the
      -- element stride (scale): a `u16` store (`scale = 2`) is the width-exact
      -- `movw` (no overrun of the neighbouring element), `u32`/`u64` a `movl`/`movq`.
      else if stripAbiTag opn == "STOREIDX" then
        match a with
        | .arrIdx _ _ scale =>
            let sw := scale * 8
            [ "\tmov" ++ sizeSuffix sw ++ " "
                ++ resolveOperand frame spillW sw b qsaveB ++ ", "
                ++ resolveOperand frame spillW 64 a qsaveB ]
        | _ => [ "\t# UNHANDLED-STOREIDX " ++ opn ]
      -- **Variable-count shift** `Lopn [d] SHL/SHR/SAR [val, count]` (the Merkle
      -- level loop's `n >> (lvl+1)`: the count is a RUNTIME register, not a
      -- mnemonic-carried immediate). x86's two-address `sh{l,r} %reg, dst` does
      -- not exist — the count must be `%cl`, and `%rcx` is in the RA pool so a
      -- render-time pin would clobber a live value. Render the BMI2 3-operand
      -- form `shlx`/`shrx`/`sarx` (count in ANY register, value semantics
      -- identical — count masked mod width — and no flag writes; same BMI2
      -- baseline as the `mulx` arm): AT&T order `sh{l,r}x<sz> count, val, dst`.
      -- The count must be a register (BMI2 allows only the VALUE in memory); a
      -- spilled count surfaces as the visible sentinel, never silently.
      else if (stripAbiTag opn == "SHL" || stripAbiTag opn == "SHR"
                || stripAbiTag opn == "SAR")
              && (match b with | .imm _ => false | _ => true) then
        let w := mnemWidth opn
        let mn := match stripAbiTag opn with
          | "SHL" => "shlx" | "SAR" => "sarx" | _ => "shrx"
        if isMemOperand b then [ "\t# UNHANDLED-VARSHIFT-MEMCOUNT " ++ opn ]
        else
          [ "\t" ++ mn ++ sizeSuffix w ++ " "
              ++ resolveOperand frame spillW w b qsaveB ++ ", "
              ++ resolveOperand frame spillW w a qsaveB ++ ", "
              ++ resolveOperand frame spillW w d qsaveB ]
      else
        let w := mnemWidth opn
        let mnBase := stripAbiTag opn
        match attBase mnBase with
        | some m =>
            let bOp := resolveOperand frame spillW w b qsaveB
            let dOp := resolveOperand frame spillW w d qsaveB
            -- **Mem-to-mem legalization for the flag-only compare class.** x86 has
            -- no memory-to-memory `cmp`/`test`, and the upstream two-address
            -- legalizer (`physBodyRmap`'s `isBinop` alphabet) does not cover
            -- `CMP`/`TEST`, so a bounded-linear-scan allocation that spills both
            -- the counter and the bound reaches the printer with both operands in
            -- frame slots. Split through the reserved primary reload scratch
            -- `R15`: it is excluded from the allocator's pool (`gpRegNames`), so
            -- no kernel value is ever live in it.
            --
            -- The operand loaded into the scratch is `d` — the AT&T *destination*,
            -- the second printed operand. AT&T `cmp<sz> b, d` sets the flags from
            -- `d - b`, so `mov<sz> d, %r15 ; cmp<sz> b, %r15` sets them from
            -- `%r15 - b = d - b`: the same flags, hence the same branch taken by
            -- the following `Lcond` Jcc. Loading `b` instead would compute `b - d`
            -- and invert every ordered condition. For `TEST` the flag effect is
            -- `b & d`, symmetric in its operands, so the same split is exact.
            -- `mov` writes no flag, so nothing is disturbed between the load and
            -- the compare. Neither op writes its destination operand, so no
            -- write-back of the scratch is needed.
            if (mnBase == "CMP" || mnBase == "TEST")
                && isMemOperand b && isMemOperand d then
              let scratch := resolveName frame spillW w "R15" qsaveB
              [ "\tmov" ++ sizeSuffix w ++ " " ++ dOp ++ ", " ++ scratch,
                "\t" ++ m ++ sizeSuffix w ++ " " ++ bOp ++ ", " ++ scratch ]
            else
              [ "\t" ++ m ++ sizeSuffix w ++ " " ++ bOp ++ ", " ++ dOp ]
        | none => [ "\t# UNHANDLED-OP " ++ opn ]
  | [d], opn, [a, s, cin] =>
      let w := mnemWidth opn
      let base := stripWidthTag opn
      -- **Branchless constant-time select** `Lopn [d] CMOV:w [cond, t, f]` (from
      -- `JasminOp.select`): the data effect `d := (cond ≠ 0) ? t : f` with no
      -- PC divergence (the CT form of an `if`). Render `mov f, d; test cond,cond;
      -- cmovne t, d`. When `d` already aliases the true-value register, default to
      -- `t` and `cmove f, d` instead (so the defaulting `mov` never clobbers `t`
      -- before the conditional move reads it).
      --
      -- A destination aliasing the CONDITION register is not handled: the
      -- defaulting `mov` would overwrite `cond` before the `test` reads it. The
      -- claim that this cannot arise — that the export's argument-liveness pin
      -- leaves `d` and `cond` in distinct registers — is a statement about the
      -- register allocator with no theorem behind it. No emitted artifact
      -- contains the pattern (measured over every `.s` under `bench/`,
      -- `crates/` and `gen/`). `LoweringCoverageCmovSar.lowerLinstrExtCov2`
      -- declines the shape outright when `cn == dst`, so the JInstr route is
      -- guarded and this one is not. Hoisting the `test` above the `mov` fixes
      -- it on both byte producers and costs nothing at the value level, but it
      -- reorders every conditional select in every shipped artifact, including
      -- the SHA-256-pinned `Ed25519PointAddShipped` block.
      if base == "CMOV" then
        let dOp := resolveOperand frame spillW w d qsaveB
        let condOp := resolveOperand frame spillW w a qsaveB
        let tOp := resolveOperand frame spillW w s qsaveB
        let fOp := resolveOperand frame spillW w cin qsaveB
        let sz := sizeSuffix w
        -- `test` takes at most one memory operand, so a SPILLED CONDITION is
        -- compared against zero instead: `cmp $0, cond` sets `ZF = (cond == 0)`,
        -- the flag both conditional moves read.
        let testLine :=
          if isMemOperand a then "\tcmp" ++ sz ++ " $0, " ++ condOp
          else "\ttest" ++ sz ++ " " ++ condOp ++ ", " ++ condOp
        if isMemOperand d then
          -- **Spilled destination.** `cmov` requires a REGISTER destination, so
          -- the select runs in a borrowed register saved at the bottom of the
          -- red zone, as the spilled `adcx`/`adox` destination below does (the
          -- bodies are call-free leaves and the export's red-zone stash slots
          -- sit at `-8·k` for the ≤ 6 register ABI args, never that deep):
          --
          --   mov  scratch, -128(%rsp)
          --   mov  f, scratch
          --   test cond, cond
          --   cmovne t, scratch
          --   mov  scratch, [d]
          --   mov  -128(%rsp), scratch
          --
          -- The scratch avoids every operand's text (including SIB/mem base
          -- registers, via substring check), and `[d]` is read through `t` or
          -- `f` — when either aliases it — before the store writes it.
          let usedTexts := [dOp, condOp, tOp, fOp]
          let freeOf : String → Bool := fun cand =>
            usedTexts.all (fun t => (t.splitOn cand).length == 1)
          let scratch :=
            if freeOf "%rax" then "%rax"
            else if freeOf "%rbx" then "%rbx"
            else if freeOf "%rcx" then "%rcx"
            else "%rdx"
          [ "\tmovq " ++ scratch ++ ", -128(%rsp)",
            "\tmov" ++ sz ++ " " ++ fOp ++ ", " ++ scratch,
            testLine,
            "\tcmovne" ++ sz ++ " " ++ tOp ++ ", " ++ scratch,
            "\tmov" ++ sz ++ " " ++ scratch ++ ", " ++ dOp,
            "\tmovq -128(%rsp), " ++ scratch ]
        else if dOp == tOp then
          [ testLine, "\tcmove" ++ sz ++ " " ++ fOp ++ ", " ++ dOp ]
        else
          (if fOp == dOp then [] else [ "\tmov" ++ sz ++ " " ++ fOp ++ ", " ++ dOp ])
            ++ [ testLine, "\tcmovne" ++ sz ++ " " ++ tOp ++ ", " ++ dOp ]
      else
      -- **ADX carry-chain DATA binding** `Lopn [d] ADCX/ADOX [a, s, cin]`: compute
      -- `d := a + s + cin` where `cin` is the IR's explicit `reg 1` carry-in. Real
      -- x86 `adcx`/`adox` is two-address (`d := d + s + CF/OF`), so we expand to
      -- the PROVEN `lowerLinstrExtCov` shape (`mov a,d; adcx s,d`) and additionally
      -- materialise the explicit carry-in into the flag via `bt $0, cin` (the IR
      -- ALWAYS passes `cin` as a value — `addCarryLo`'s 3rd arg — so this is faithful
      -- for both the isolated widening AND the chained CIOS, where `cin` holds the
      -- previous limb's `setc`-materialised carry). `mov` preserves the flag, so the
      -- `bt → adcx` flag dependency is intact.
      if base == "ADCX" || base == "ADOX" then
        let mn := if base == "ADOX" then "adox" else "adcx"
        let dOp := resolveOperand frame spillW w d qsaveB
        let aOp := resolveOperand frame spillW w a qsaveB
        if !(isMemOperand d) then
          let movLine := if aOp == dOp then []
                         else [ "\tmov" ++ sizeSuffix w ++ " " ++ aOp ++ ", " ++ dOp ]
          -- FUSED carry-in (`AdxChainFuse`): the `cfCarrySentinel` carry-in means
          -- the CPU carry flag already holds the previous op's carry-out, so the
          -- `bt $0, cin` materialise-round-trip is dead — drop it and let the flag
          -- flow straight into this `adcx`/`adox`.
          let btLine := if cin == LOperand.reg cfCarrySentinel then []
                        else [ "\tbt" ++ sizeSuffix w ++ " $0, " ++ resolveOperand frame spillW w cin qsaveB ]
          movLine ++ btLine
            ++ [ "\t" ++ mn ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s qsaveB ++ ", " ++ dOp ]
        else
          -- **Spilled destination** (the carry-chain kernels under register
          -- pressure): `adcx`/`adox` require a REGISTER destination (unlike the
          -- classic two-address ALU class, whose memory-destination forms the
          -- generic arm exploits), and no scratch register exists at render time
          -- (all GPs are in the RA pool).  `push`/
          -- `pop` cannot save one either: the export stashes ABI args in the red
          -- zone (`-8(%rsp)`, `forceLivePin`), which a push would clobber.
          -- Instead borrow a scratch and save it at the BOTTOM of the red zone
          -- (`-128(%rsp)` — the export's red-zone stash slots sit at `-8·k` for
          -- the ≤ 6 register ABI args, never that deep; the bodies are call-free
          -- leaves, and the SysV red zone is interrupt/signal-safe).  `mov`
          -- leaves the flags untouched, so the CF/OF carry-out survives to the
          -- following `ADCXHI`/`ADOXHI` binding:
          --
          --   bt   $0, cin           ; CF := cin (before anything is disturbed)
          --   mov  scratch, -128(%rsp)
          --   mov  a, scratch        ; [d] still intact — reads of d-aliased
          --   adcx s, scratch        ;   source slots stay correct
          --   mov  scratch, [d]      ; [d] := result (flags untouched)
          --   mov  -128(%rsp), scratch
          --
          -- The scratch is picked to avoid every operand's text (including
          -- SIB/mem base registers, via substring check).
          let sOp := resolveOperand frame spillW w s qsaveB
          let cOp := resolveOperand frame spillW w cin qsaveB
          let usedTexts := [dOp, aOp, sOp, cOp]
          let freeOf : String → Bool := fun cand =>
            usedTexts.all (fun t => (t.splitOn cand).length == 1)
          let scratch :=
            if freeOf "%rax" then "%rax"
            else if freeOf "%rbx" then "%rbx"
            else if freeOf "%rcx" then "%rcx"
            else "%rdx"
          let sz := sizeSuffix w
          -- FUSED carry-in (`AdxChainFuse`): drop the `bt $0, cin` when the
          -- carry-in is the live-flag sentinel (the scratch save/restore `movq`s
          -- are flag-safe, so the incoming CF survives into the `adcx`/`adox`).
          let btLine := if cin == LOperand.reg cfCarrySentinel then []
                        else [ "\tbt" ++ sz ++ " $0, " ++ cOp ]
          btLine ++
          [ "\tmovq " ++ scratch ++ ", -128(%rsp)",
            "\tmov" ++ sz ++ " " ++ aOp ++ ", " ++ scratch,
            "\t" ++ mn ++ sz ++ " " ++ sOp ++ ", " ++ scratch,
            "\tmov" ++ sz ++ " " ++ scratch ++ ", " ++ dOp,
            "\tmovq -128(%rsp), " ++ scratch ]
      else
      match attBase base with
      | some m =>
          [ "\t" ++ m ++ sizeSuffix w ++ " "
              ++ resolveOperand frame spillW w s qsaveB ++ ", " ++ resolveOperand frame spillW w d qsaveB ]
      | none => [ "\t# UNHANDLED-OP " ++ opn ]
  -- BMI2 widening multiply `MULX` (byte-direct field leaves): TWO
  -- destinations `[dstLo, dstHi]` and one explicit source `src2` (the implicit
  -- src1 is `%rdx`, pinned by the kernel allocation — not a printed operand).
  -- AT&T order is `mulx src2, dstLo, dstHi` (reg form, no size suffix — the
  -- operands fix the 64-bit width) / `mulxq off(%base), dstLo, dstHi` (memory
  -- form). Matches `AsmPrinter.renderJInstr`'s `.mulx`/`.mulxMem` lines, so the
  -- text path and the `LprogBytes` byte path agree.
  | [dl, dh], opn, [s] =>
      let base := stripWidthTag opn
      if base == "MULX" || base == "MULXMEM" then
        let rs := resolveOperand frame spillW 64 s qsaveB
        let rdl := resolveOperand frame spillW 64 dl qsaveB
        let rdh := resolveOperand frame spillW 64 dh qsaveB
        let mnem := if base == "MULXMEM" then "mulxq" else "mulx"
        -- **Coincident mulx destinations.** When the owned RA homes the LOW and
        -- HIGH outputs in the SAME physical register (`rdl == rdh` — the low word
        -- is redundant, already materialised by a separate `imul`/`mul`, so its
        -- register was reused for the high word), a plain `mulx s, r, r` writes
        -- both halves to `r` and the low clobbers the high. Route the discarded
        -- low to a scratch distinct from `rdh`, `rs`, and `%rdx` (the implicit
        -- multiplicand), saved/restored through the bottom of the red zone
        -- (`-128(%rsp)`; the carry-op precedent — call-free leaves, flag-safe
        -- `movq`s) so no live value is lost. `rdl != rdh` renders byte-identically.
        if rdl == rdh then
          let scratch :=
            (["%rcx", "%rsi", "%rdi", "%r8", "%r9", "%r10", "%r11", "%rax", "%rbx"].find?
              (fun r => r != rdh && r != rs && r != "%rdx")).getD "%r11"
          [ "\tmovq " ++ scratch ++ ", -128(%rsp)",
            "\t" ++ mnem ++ " " ++ rs ++ ", " ++ scratch ++ ", " ++ rdh,
            "\tmovq -128(%rsp), " ++ scratch ]
        else
          [ "\t" ++ mnem ++ " " ++ rs ++ ", " ++ rdl ++ ", " ++ rdh ]
      else
        [ "\t# UNHANDLED-LOPN " ++ opn ++ " dsts=2 srcs=1" ]
  | dsts, opn, srcs =>
      [ "\t# UNHANDLED-LOPN " ++ opn ++ " dsts=" ++ toString dsts.length
          ++ " srcs=" ++ toString srcs.length ]

/-! ### Printer pins: batch8 YMM VEX arms

`XMM<k>` operand names resolve to the AVX `%ymm<k>` register, and the packed
binary / shift-by-immediate `renderLopn` arms emit the AT&T VEX 3-operand form
(`src2, src1, dst`). -/

-- The imm64-store arm on a `mem.RAX` destination: the constant goes through
-- `%rbx`, the first candidate absent from the destination's text, saved to and
-- restored from `-128(%rsp)`. A static pin of the printed form.
#guard renderLopn 0 0 false [.reg "mem.RAX.8"] "MOV:64" [.imm 2596001775599221991]
        = ["\tmovq %rbx, -128(%rsp)", "\tmovq $2596001775599221991, %rbx",
           "\tmovq %rbx, 8(%rax)", "\tmovq -128(%rsp), %rbx"]

#guard resolveName 0 0 32 "XMM3" = "%ymm3"
#guard renderLopn 0 0 false [.reg "XMM0"] "VPXOR" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpxor %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPADDD" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpaddd %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPSLLD:7" [.reg "XMM1"]
        = ["\tvpslld $7, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPSRLD:25" [.reg "XMM1"]
        = ["\tvpsrld $25, %ymm1, %ymm0"]
-- Lattice-coefficient lanes: the arithmetic shift, the low-word product, and the
-- non-commutative and-not (`d = ~a & b`, sources printed `b, a` like VPSUBD).
#guard renderLopn 0 0 false [.reg "XMM0"] "VPSRAD:23" [.reg "XMM1"]
        = ["\tvpsrad $23, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPMULLD" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpmulld %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPANDN" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpandn %ymm2, %ymm1, %ymm0"]
-- NTT butterfly arithmetic: signed/unsigned packed multiply, qword add, and the
-- non-commutative packed subtract (`d = a - b`, sources printed `b, a`).
#guard renderLopn 0 0 false [.reg "XMM0"] "VPMULDQ" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpmuldq %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPMULUDQ" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpmuludq %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPADDQ" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpaddq %ymm2, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPSUBD" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpsubd %ymm2, %ymm1, %ymm0"]
-- NTT lane routing: in-/cross-lane permutes by immediate, odd-lane dup, blend.
#guard renderLopn 0 0 false [.reg "XMM0"] "VPSHUFD:216" [.reg "XMM1"]
        = ["\tvpshufd $216, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPERMQ:78" [.reg "XMM1"]
        = ["\tvpermq $78, %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VMOVSHDUP" [.reg "XMM1"]
        = ["\tvmovshdup %ymm1, %ymm0"]
#guard renderLopn 0 0 false [.reg "XMM0"] "VPBLENDD:170" [.reg "XMM1", .reg "XMM2"]
        = ["\tvpblendd $170, %ymm2, %ymm1, %ymm0"]

/-- Each 256-bit immediate op renders as its own instruction. A name that
    extends another one (`VPSRLDQ` extends `VPSRLD`) is not taken for the shorter
    one, whose meaning differs: `VPSRLDQ` shifts each 128-bit half by bytes,
    `VPSRLD` each dword by bits. -/
theorem renderLopn_ymm_imm_ops :
    renderLopn 0 0 false [.reg "XMM0"] "VPSRLDQ:4" [.reg "XMM1"]
      = ["\tvpsrldq $4, %ymm1, %ymm0"] ∧
    renderLopn 0 0 false [.reg "XMM0"] "VPSRAW:3" [.reg "XMM1"]
      = ["\tvpsraw $3, %ymm1, %ymm0"] ∧
    renderLopn 0 0 false [.reg "XMM0"] "VPERM2I128:33" [.reg "XMM1", .reg "XMM2"]
      = ["\tvperm2i128 $33, %ymm2, %ymm1, %ymm0"] ∧
    renderLopn 0 0 false [.reg "XMM0"] "VPABSD" [.reg "XMM1"]
      = ["\tvpabsd %ymm1, %ymm0"] := by
  native_decide

/-- The 256-bit signed packs render as themselves, not through the 512-bit
    `VPACK8u64:` / `VPACKD:` packed-add arm whose name they extend; and a
    two-source op keeps its operand order (`src2, src1, dst`). -/
theorem renderLopn_ymm_two_src_ops :
    renderLopn 0 0 false [.reg "XMM0"] "VPACKSSDW" [.reg "XMM1", .reg "XMM2"]
      = ["\tvpackssdw %ymm2, %ymm1, %ymm0"] ∧
    renderLopn 0 0 false [.reg "XMM0"] "VPMULHW" [.reg "XMM1", .reg "XMM2"]
      = ["\tvpmulhw %ymm2, %ymm1, %ymm0"] ∧
    renderLopn 0 0 false [.reg "XMM0"] "VPERMD" [.reg "XMM1", .reg "XMM2"]
      = ["\tvpermd %ymm2, %ymm1, %ymm0"] := by
  native_decide
/- The materialised comparison and the forms the compare-and-select fusion emits;
   static pins of the printed text on single instructions. -/
#guard renderLopn 0 0 false [.reg "RCX"] "SETNE:64" [.reg "R9", .imm 0]
        = ["\tcmpq $0, %r9", "\tmovq $0, %rcx", "\tsetne %cl"]
#guard renderLopn 0 0 false [.reg "RAX"] "SETB" [.reg "RAX", .reg "RDX"]
        = ["\tcmpl %edx, %eax", "\tmovl $0, %eax", "\tsetb %al"]
#guard renderLopn 0 0 false [.reg "R9"] "CMP:64" [.reg "R9", .imm 0]
        = ["\tcmpq $0, %r9"]
#guard renderLopn 0 0 false [.reg "RAX"] "CMOVNE:64" [.reg "RAX", .reg "RDX"]
        = ["\tcmovneq %rdx, %rax"]

/-- Render one owned-RA `LinstrR` to its AT&T line(s) in a frame of size `frame`.

    Returns `[]` for `Lret`/`Lalign` (the leaf wrapper emits `ret`) and for the
    carry-out / MULX-high *bindings* (the flag / high word is a side effect of
    the matching data op), and a visible sentinel comment for any unexpected
    shape (never a silent drop). -/
def renderLinstrR (frame spillW : Nat) (i : LinstrR) (lblPfx : String := "")
    (rvs : Bool := false) (qsaveB : Nat := qsaveBytes) : List String :=
  -- `lblPfx` makes the local `.L<l>` labels **function-scoped**: gas local labels
  -- are file-scoped, so two functions in one `.s` that both wrap a `loopLcmd`
  -- (top label `0`) would emit two `.L0:` and collide at assembly. `renderLfundef`
  -- passes `<name>_`, turning the label into `.L<name>_<l>` — unique per function
  -- (the name is already a valid global symbol). Default `""` keeps the standalone
  -- single-instr KATs emitting `.L<l>`.
  match i with
  -- ADX carry-out (`ADCXHI`/`ADOXHI`) and MULX high-word (`MULXHI`) *bindings*
  -- carry no instruction of their own — the flag / high word is the matching
  -- data op's side effect. Drop them (empty line list) before the general arity
  -- arms so they never double-issue.
  | .Lopn dsts opn srcs =>
      -- The `FRAME` directive (array-ABI orchestration) is a frame-size
      -- annotation consumed by `frameSize`; it issues no x86 line (drop before the
      -- arity arms so the empty-dst form doesn't surface as UNHANDLED-LOPN).
      if opn == "FRAME" || opn == "FRAMEADD" then [] else
      -- MULX high-word binding. A FUSED body has no standalone `MULXHI` left
      -- (`fuseMulHiLprog` consumed the pair into one two-output `mulx`), so a
      -- `MULXHI` surviving to the text renderer means its high-word WRITE is
      -- missing — silent value corruption (the fri_proof Barrett high word).
      -- Emit the visible sentinel the `no UNHANDLED` shape gates catch. The
      -- byte path (`read_linear`) reassembles the pair itself and does not
      -- come through here.
      if isMulHiBinding opn then [ "\t# UNHANDLED-MULXHI-UNFUSED " ++ opn ] else
      -- ADX carry-OUT binding (`ADCXHI`/`ADOXHI`): the carry-out is the post-add
      -- flag of the matching data `ADCX`/`ADOX`. In the *chained* CIOS idiom the
      -- next limb reads it implicitly through CF, so the line is dropped; but a
      -- *standalone* widening (the `Com`-path `addCarryHi`) consumes the carry as
      -- a `reg 1` DATA value (zero-extended into the next add), so it MUST be
      -- materialised. Emit `setc`/`seto` + `movzbq` (matching the PROVEN
      -- `lowerLinstrExtCov` `ADCXHI → setc dst` expansion).
      --
      -- KNOWN GAP (carry-out flag-adjacency): `setc`/`seto` reads CF/OF from the
      -- ambient flags the matching data `ADCX`/`ADOX` set. The DATA arm above
      -- reconstructs its carry-IN from the RA-live `cin` register (`bt $0, cin`),
      -- so its `adcx`/`adox` does not depend on flag order; the carry-OUT is held
      -- in no register before this `setc`, so it cannot be reconstructed here. The
      -- read is correct only when no flag-writing instruction sits between the
      -- data op and this binding. The allocator carries no EFLAGS liveness, so
      -- nothing enforces that adjacency; the emitted bodies keep the data op and
      -- its `ADCXHI`/`ADOXHI` binding adjacent, which is what makes it hold.
      if isCarryOutBinding opn then
        match dsts with
        | [.reg dn] =>
            let setcc := if stripWidthTag opn == "ADOXHI" then "seto" else "setc"
            -- A **spilled** carry-out destination (`k.N` / qsave / mem): `setcc`
            -- takes an r/m8, so write the flag byte straight into the (first
            -- zeroed) 64-bit slot — `mov` to memory leaves the flags untouched,
            -- so the CF/OF read by `setcc` is still the matching data op's
            -- carry-out.  Register destinations keep the existing
            -- `setcc %r8b; movzbq` pair (byte-identical for existing kernels).
            if "k.".isPrefixOf dn || "qsave.".isPrefixOf dn || "mem.".isPrefixOf dn then
              let slot := resolveName frame spillW 64 dn qsaveB
              [ "\tmovq $0, " ++ slot, "\t" ++ setcc ++ " " ++ slot ]
            else
              [ "\t" ++ setcc ++ " " ++ gpReg8 dn, "\tmovzbq " ++ gpReg8 dn ++ ", " ++ gpReg64 dn ]
        | _ => []
      else
        renderLopn frame spillW rvs dsts opn srcs qsaveB
  | .Lret => []
  | .Lalign => []
  | .Llabel _ l => [ ".L" ++ lblPfx ++ toString l ++ ":" ]
  -- Control flow. A local internal label `Lgoto ("", l)` (the back-edge
  -- of a bounded loop / a forward skip) renders as `jmp .L<l>`; a remote target
  -- `Lgoto (f, l)` keeps the function symbol. `Lcond (reg cc) l` is the
  -- conditional back-edge / guard: emit `j<cc> .L<l>` mapping the public
  -- condition-code name to its `Jcc` mnemonic. The flag the Jcc reads is set by
  -- the preceding `CMP`/`SUB`/`TEST` body op (the GP-ALU compare class).
  | .Lgoto ("", l) => [ "\tjmp .L" ++ lblPfx ++ toString l ]
  | .Lgoto (f, l) => [ "\tjmp " ++ f ++ "  # .L" ++ lblPfx ++ toString l ]
  | .Lcond (.reg cc) l => [ "\t" ++ attCC cc ++ " .L" ++ lblPfx ++ toString l ]
  | .Lcond c l => [ "\t# UNHANDLED-COND " ++ c.toText ++ " .L" ++ lblPfx ++ toString l ]
  -- Cross-function call. `Lcall ra (f, _)` is a direct near `call` to the
  -- sibling function symbol `f` (an intra-object owned-RA leaf, e.g. a fe25519
  -- field op the X25519 ladder body calls). gas/`ld` resolve the `call f` against
  -- the same-object `STT_FUNC` symbol `f` (a `R_X86_64_PLT32`/intra-object rel32) —
  -- the text-path analogue of `LprogBytes.encodeLcmdReloc`'s intra-object resolution.
  -- A local target (`f = ""`, a label index) is not produced by the owned bodies
  -- (intra-function transfers are `Lgoto`/`Lcond`); it surfaces as a comment.
  | .Lcall _ (f, l) =>
      if f.isEmpty then [ "\t# UNHANDLED-LOCAL-CALL .L" ++ lblPfx ++ toString l ]
      else [ "\tcall " ++ f ]
  | other => [ "\t# UNHANDLED " ++ toString (repr other) ]

/-- `String.isPrefixOf` is `JasminLprogExport.hasPrefix` with the arguments
    swapped: both test `p.toList <+: s.toList`. `WellFormedX86` carries the same
    statement for the module set that does not import this one. -/
theorem isPrefixOf_eq_hasPrefix (p s : String) :
    p.isPrefixOf s = VIR.JasminLprogExport.hasPrefix s p := by
  rw [VIR.JasminLprogExport.hasPrefix, String.isPrefixOf, Bool.eq_iff_iff,
    String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

/-- `String.toNat?` of a name's `k`-character-dropped suffix is
    `JasminLprogExport.strDropToNat?`, the character-list parse. -/
theorem toNat?_drop_toString (s : String) (k : Nat) :
    String.toNat? (s.drop k).toString = VIR.JasminLprogExport.strDropToNat? s k := by
  rw [VIR.JasminLprogExport.strDropToNat?, ← VIR.JasminLprogExport.strToNat?_eq,
    VIR.JasminLprogExport.strToNat?]
  congr 1
  simp [String.toList_copy_drop]

/-- The maximum U32-spill index `k.N` referenced in a body (`none` if no spill),
    used to size the frame. The name test and the index parse both run over the
    character list, so a closed application reduces in the kernel;
    `maxSpillIdx_eq_toNat?` states the value against `String.isPrefixOf` and
    `String.toNat?`. -/
def maxSpillIdx (body : VIR.JasminLprogExport.Lcmd) : Option Nat :=
  body.foldl (fun acc i =>
    match i.li_i with
    | .Lopn dsts _ srcs =>
        (dsts ++ srcs).foldl (fun acc' o =>
          match o with
          | .reg nm =>
              if VIR.JasminLprogExport.hasPrefix nm "k." then
                match VIR.JasminLprogExport.strDropToNat? nm 2 with
                | some k => some (max (acc'.getD 0) k)
                | none => acc'
              else acc'
          | _ => acc') acc
    | _ => acc) none

/-- The maximum U32-spill index read with `String.isPrefixOf` and `String.toNat?`. -/
theorem maxSpillIdx_eq_toNat? (body : VIR.JasminLprogExport.Lcmd) :
    maxSpillIdx body
      = body.foldl (fun acc i =>
          match i.li_i with
          | .Lopn dsts _ srcs =>
              (dsts ++ srcs).foldl (fun acc' o =>
                match o with
                | .reg nm =>
                    if "k.".isPrefixOf nm then
                      match String.toNat? (nm.drop 2).toString with
                      | some k => some (max (acc'.getD 0) k)
                      | none => acc'
                    else acc'
                | _ => acc') acc
          | _ => acc) none := by
  simp only [maxSpillIdx, isPrefixOf_eq_hasPrefix, toNat?_drop_toString]

/-- The maximum `kv.N` **vector-spill** slot index used in the body (`none` if the
    body has no vector spills). Mirrors `maxSpillIdx` for the `kv.` class; a
    GP-only / non-spilling body returns `none`, so no vector region is reserved. -/
def maxVecSpillIdx (body : VIR.JasminLprogExport.Lcmd) : Option Nat :=
  body.foldl (fun acc i =>
    match i.li_i with
    | .Lopn dsts _ srcs =>
        (dsts ++ srcs).foldl (fun acc' o =>
          match o with
          | .reg nm =>
              if VIR.JasminLprogExport.hasPrefix nm "kv." then
                match VIR.JasminLprogExport.strDropToNat? nm 3 with
                | some k => some (max (acc'.getD 0) k)
                | none => acc'
              else acc'
          | _ => acc') acc
    | _ => acc) none

/-- The maximum vector-spill index read with `String.isPrefixOf` and
    `String.toNat?`. -/
theorem maxVecSpillIdx_eq_toNat? (body : VIR.JasminLprogExport.Lcmd) :
    maxVecSpillIdx body
      = body.foldl (fun acc i =>
          match i.li_i with
          | .Lopn dsts _ srcs =>
              (dsts ++ srcs).foldl (fun acc' o =>
                match o with
                | .reg nm =>
                    if "kv.".isPrefixOf nm then
                      match String.toNat? (nm.drop 3).toString with
                      | some k => some (max (acc'.getD 0) k)
                      | none => acc'
                    else acc'
                | _ => acc') acc
          | _ => acc) none := by
  simp only [maxVecSpillIdx, isPrefixOf_eq_hasPrefix, toNat?_drop_toString]

/-- Bytes reserved for the vector-spill region: slot `0(%rsp)` is the `%ymm15`
    save cell used by spill legalization, slots `1 … maxVec+1` are the `kv.N`
    cells, so `32·(maxVec+2)`; `0` when the body has no `kv.N` slots. -/
def vecSpillBytes (body : VIR.JasminLprogExport.Lcmd) : Nat :=
  match maxVecSpillIdx body with
  | some m => 32 * (m + 2)
  | none => 0

/-- True iff the body is a U64 kernel (any body mnemonic carries the `:64` tag or
    is `MOVQ`). The spill stride is then 8 bytes, else 4 — kernels are uniform
    width (`comToLfundefPhysAbi` tags every `regArith` op at the source width). -/
def bodyIsU64 (body : VIR.JasminLprogExport.Lcmd) : Bool :=
  body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => hasSuffix opn ":64"
    | _ => false)

/-- An explicit frame-size directive `Lopn [] "FRAME" [.imm F]` (array-ABI
    orchestration). The pointer-passing orchestration around opaque `.stackArr`
    `extCall` leaves needs scratch buffers for each leaf result (G1/G2/GT points,
    96–576 bytes), whose size the spill-index frame sizer cannot see (the body
    holds no `k.N` word spills, only `mem.RSP.<off>` buffer references). The
    producer emits this marker as the body's first instruction stating the exact
    frame `F` it laid its buffers in; `frameSize` reads it and `renderLinstrR`
    drops it (it issues no x86 line). `none` for any body without the marker — the
    spill-index sizer is then used unchanged. -/
def frameDirective (body : VIR.JasminLprogExport.Lcmd) : Option Nat :=
  body.foldl (fun acc i =>
    match acc, i.li_i with
    | some f, _ => some f
    | none, .Lopn [] "FRAME" [.imm f] => some f
    | none, _ => none) none

/-- The additive frame-extension directive `Lopn [] "FRAMEADD" [.imm n]`: the
    bytes a body needs at the BOTTOM of its frame for scratch buffers, on top of
    whatever layout `frameSize` otherwise computes. Summed over every occurrence,
    and `0` for a body carrying none — such a body keeps its computed frame
    exactly.

    Distinct from `FRAME`, which replaces the computed layout rather than
    extending it. A body carrying `FRAMEADD` addresses its buffers as
    `mem.RSP.<off>` with `off` in `[0, n)` (the bottom anchoring `ArrAbiOrch`
    uses), so the offsets are fixed when the body is walked, before register
    allocation settles the spill count. The vector-spill region `kv.N` is
    anchored at the same bottom, so a body carrying both `FRAMEADD` and `kv.N`
    slots would overlap the two. -/
def frameAddDirective (body : VIR.JasminLprogExport.Lcmd) : Nat :=
  body.foldl (fun acc i =>
    match i.li_i with
    | .Lopn [] "FRAMEADD" [.imm n] => acc + n
    | _ => acc) 0

-- Static checks pinning the frame extension against silent change: a body
-- carrying no `FRAMEADD` contributes nothing, so its frame — and every qsave and
-- spill offset computed from that frame — is the one it had before the directive
-- existed. `FRAME` is a distinct directive and contributes nothing here.
#guard frameAddDirective [] = 0
#guard frameAddDirective [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 1]⟩] = 0
#guard frameAddDirective [⟨0, .Lopn [] "FRAME" [.imm 64]⟩] = 0
#guard frameAddDirective [⟨0, .Lopn [] "FRAMEADD" [.imm 96]⟩] = 96

/-- Do a body's bottom-anchored scratch buffers and its vector-spill cells claim
    the same frame region? `FRAMEADD` buffers occupy `[0, n)` from the post-`leaq`
    `%rsp`, and a `kv.idx` cell resolves to `32·(idx+1)(%rsp)` with `0(%rsp)`
    reserved as the spill-legalization scratch — both anchored at the bottom of
    the frame. A body carrying each therefore aliases the two regions.

    `false` for every body carrying no `FRAMEADD`, which is every body that does
    not lay scratch buffers of its own. -/
def frameAddVecOverlap (body : VIR.JasminLprogExport.Lcmd) : Bool :=
  frameAddDirective body != 0 && (maxVecSpillIdx body).isSome

-- The overlap condition is absent from a body with no scratch buffers, and is
-- detected when a body claims the bottom of the frame twice.
#guard frameAddVecOverlap [] = false
#guard frameAddVecOverlap [⟨0, .Lopn [] "FRAMEADD" [.imm 96]⟩] = false
#guard frameAddVecOverlap
  [ ⟨0, .Lopn [] "FRAMEADD" [.imm 96]⟩
  , ⟨0, .Lopn [.reg "kv.0"] "VMOVDQU" [.reg "XMM0"]⟩ ] = true

/-! ### Callee-saved GP park/restore for hand-built bodies

The SysV x86-64 ABI requires a function to preserve `{RBX, RBP, R12, R13, R14,
R15}` across a call. The linear-jasmin owned path (`comToLfundefPhysAbi`) already
parks every callee-saved register it allocates by emitting `MOVQ qsave.X, X` (and
the matching restore) **into the body** via `buildPrologue`/`buildEpilogue`, so
those bodies are ABI-correct without any printer-side help.

A body built **by hand** at the `Lcmd` level (e.g. MAYO's `VerifyEmit`,
which uses `R12`/`R13` as GF(16) scratch) bypasses that prologue and so carries
NO qsave park — without a save it clobbers the C caller's `R12`/`R13` and
SEGFAULTs. `renderLfundef` therefore detects every callee-saved GPR the body
**writes as a bare register destination but does NOT already `qsave`-park**, and
brackets the frame with a `pushq`/`popq` pair for exactly those.

The push count is also what the frame sizer reads for the SysV call-site
alignment correction (`frameSize`), since each push moves `%rsp` by 8 before the
frame `leaq`; the set is therefore defined ahead of the frame layout.

For the linear-jasmin path the wrapping is **inert**: every callee-saved register
those bodies write as a bare destination is also `qsave`-parked (`buildPrologue`
saves all six unconditionally), so `calleeSavedToSave` returns `[]` and no
push/pop is emitted. It is likewise inert for any body that touches no
callee-saved register as scratch. -/

/-- The SysV x86-64 ABI callee-saved GP registers (the caller relies on these
    surviving a call). `RSP` is the stack pointer (handled by the frame), not in
    this set. -/
def calleeSavedRegs : List String := ["RBX", "RBP", "R12", "R13", "R14", "R15"]

/-- True iff some body `Lopn` writes the bare physical register `reg` as a
    destination. Only an exact `.reg reg` destination counts: the `qsave.<reg>`,
    `k.N`, and `mem.<base>.<off>` names are distinct strings, so a spill/save/mem
    target does NOT register as a bare write of `reg`. -/
def bodyWritesBareReg (body : VIR.JasminLprogExport.Lcmd) (reg : String) : Bool :=
  body.any (fun i =>
    match i.li_i with
    | .Lopn dsts _ _ => dsts.any (fun o => match o with
                                            | .reg n => n == reg
                                            | _ => false)
    | _ => false)

/-- True iff the body already `qsave`-parks `reg` (contains an `Lopn` whose
    destination is the bare name `qsave.<reg>`). This is the linear-jasmin path's
    own ABI save (`buildPrologue`); when present, the printer must NOT add a
    second push/pop. -/
def bodyParksQsave (body : VIR.JasminLprogExport.Lcmd) (reg : String) : Bool :=
  let qname := "qsave." ++ reg
  body.any (fun i =>
    match i.li_i with
    | .Lopn dsts _ _ => dsts.any (fun o => match o with
                                            | .reg n => n == qname
                                            | _ => false)
    | _ => false)

/-- The callee-saved GPRs the printer must `pushq`/`popq` around a body: those it
    writes as a bare destination but does NOT already `qsave`-park. Empty for
    every `comToLfundefPhysAbi`-produced body (all six are `qsave`-parked) and for
    any body using no callee-saved scratch — so the push/pop wrapping is inert
    except for hand-built bodies that clobber callee-saved registers. -/
def calleeSavedToSave (body : VIR.JasminLprogExport.Lcmd) : List String :=
  calleeSavedRegs.filter (fun r => bodyWritesBareReg body r && !bodyParksQsave body r)

/-- The allocated frame size `F` (bytes: a 16-aligned layout plus the call-site
    alignment correction) for a body: an explicit `FRAME` directive if present
    (the array-ABI orchestration), else the body's qsave block (`qsaveBytesFor`)
    plus every spill cell (`cell·(maxIdx+1)`, cell = 8 for a U64 body, 4 for
    U32). `frameAddDirective` bytes extend either layout, for a body holding
    bottom-anchored scratch buffers.

    A body that issues a `call` reserves the wider twelve-cell qsave block, so
    its 3rd-through-6th pointer-argument slots sit inside the frame rather than
    in the red zone a `call` overwrites. On the `FRAME` branch the declared size
    is raised by the same difference, which leaves the bottom-anchored buffers
    that directive describes where they were. A call-free body reserves
    `qsaveBytes` on either branch and keeps the frame it had.

    A body that issues a real `call` needs `%rsp ≡ 0 (mod 16)` AT each call
    instruction (SysV). The `%rsp` a call site sees is the entry value (`≡ 8`
    (mod 16), the pushed return address), less 8 per callee-saved register
    `renderLfundef` pushes before the frame (`calleeSavedToSave`), less `F` (the
    `leaq -F(%rsp)`). The correction adds 8 to the 16-aligned layout exactly when
    `8 + 8·npush + F` is `≡ 8 (mod 16)`, on either branch; it is what keeps an
    SSE-using leaf's `movaps` stack spills from faulting. A call-free body takes
    the 16-aligned layout unchanged.

    The correction moves only the frame's top: the `FRAMEADD` scratch buffers and
    the `kv.N` vector-spill cells are anchored at the post-`leaq` `%rsp`, and the
    qsave and `k.N` cells are placed relative to `F` (`qsaveFrameOff`,
    `spillFrameOff`), so both regions keep their layout and stay disjoint. -/
def frameSize (body : VIR.JasminLprogExport.Lcmd) : Nat :=
  let frameAdd := frameAddDirective body
  let f16 :=
    match frameDirective body with
    | some f => (f + frameAdd + (qsaveBytesFor body - qsaveBytes) + 15) / 16 * 16
    | none =>
      let cell := if bodyIsU64 body then 8 else 4
      let spillBytes := match maxSpillIdx body with
                        | some m => cell * (m + 1)
                        | none => 0
      -- The vector-spill region sits at the BOTTOM of the frame (offsets `32·idx`
      -- from `%rsp`); reserving it grows `frame` so the top-anchored qsave and GP
      -- `k.N` cells stay disjoint from it. `0` for a body with no `kv.N` slots, so
      -- every existing (GP-only) kernel's frame keeps this layout.
      let raw := qsaveBytesFor body + spillBytes + vecSpillBytes body + frameAdd
      (raw + 15) / 16 * 16
  if VIR.JasminLprogExport.bodyHasCall body
      && (8 + 8 * (calleeSavedToSave body).length + f16) % 16 != 0 then f16 + 8
  else f16

-- Static checks pinning the call-site alignment correction. A call-free body
-- takes the 16-aligned layout on either branch. A calling body takes the frame
-- for which `8 + 8·npush + F ≡ 0 (mod 16)`, with `npush` the length of
-- `calleeSavedToSave`: a bare `RBX` destination is one such push, a bare `RAX`
-- destination is none (`RAX` is caller-saved).
#guard frameSize [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 1]⟩] = 64
#guard frameSize [⟨0, .Lopn [] "FRAME" [.imm 592]⟩] = 592
#guard frameSize
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 1]⟩, ⟨0, .Lcall none ("f", 0)⟩ ] = 104
#guard frameSize
  [ ⟨0, .Lopn [.reg "RBX"] "MOV:64" [.imm 1]⟩, ⟨0, .Lcall none ("f", 0)⟩ ] = 96
#guard frameSize
  [ ⟨0, .Lopn [] "FRAME" [.imm 592]⟩, ⟨0, .Lcall none ("f", 0)⟩ ] = 632
#guard frameSize
  [ ⟨0, .Lopn [] "FRAME" [.imm 592]⟩
  , ⟨0, .Lopn [.reg "RBX"] "MOV:64" [.imm 1]⟩
  , ⟨0, .Lcall none ("f", 0)⟩ ] = 624

-- The frame size reduces in the kernel, on a body whose names reach no spill
-- parse and on one whose `k.3` name reaches it. The byte encoders compute the
-- frame from the body, so a `frameSize` that only `#eval` evaluates leaves every
-- whole-body byte identity out of the kernel's reach; these are the pins.
example : frameSize [⟨0, .Lopn [.reg "qsave.RDI"] "MOVQ" [.reg "RDI"]⟩,
    ⟨0, .Lopn [.reg "RAX"] "SHR:19:64" [.reg "RBX"]⟩, ⟨0, .Lret⟩] = 64 := by
  decide +kernel

example : frameSize [⟨0, .Lopn [.reg "k.3"] "MOVQ" [.reg "RDI"]⟩, ⟨0, .Lret⟩] = 80 := by
  decide +kernel

/-! ### Pins: the call-dependent qsave block

The block a body reserves, where each slot lands under it, and where the spill
region starts below it. The negative controls are the call-free rows: they fix
the red-zone placement of slots 8-11 and the 64-byte spill base, so a change
that made the wide block unconditional would fail them rather than pass
silently. -/

-- The block is eight cells for a call-free body and twelve for a calling one.
#guard qsaveBytesFor [⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 1]⟩] = 64
#guard qsaveBytesFor
  [ ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 1]⟩, ⟨0, .Lcall none ("f", 0)⟩ ] = 96

-- The eight standard slots are in-frame under either block, at the same offset.
#guard qsaveFrameOff 128 "RDI" = some 120
#guard qsaveFrameOff 128 "RDI" qsaveBytesCall = some 120
#guard qsaveFrameOff 128 "R15" = some 64
#guard qsaveFrameOff 128 "R15" qsaveBytesCall = some 64

-- Slots 8-11 are red-zone under the default block (the leaf-only placement) and
-- in-frame under the call block. The `≠` row is the control: it fails if the two
-- branches ever collapse onto one placement.
#guard qsaveFrameOff 128 "RDX" = some (-8)
#guard qsaveFrameOff 128 "R9" = some (-32)
#guard qsaveFrameOff 128 "RDX" qsaveBytesCall = some 56
#guard qsaveFrameOff 128 "R9" qsaveBytesCall = some 32
#guard qsaveFrameOff 128 "RDX" qsaveBytesCall != qsaveFrameOff 128 "RDX"

-- The spill region starts below whichever block is reserved.
#guard spillFrameOff 128 64 0 = 56
#guard spillFrameOff 128 64 0 qsaveBytesCall = 24
#guard spillFrameOff 128 64 0 qsaveBytesCall != spillFrameOff 128 64 0

/-- Render a whole `Lcmd` body's instruction lines in a frame of size `frame`
    (flattening the per-`Lopn` line lists). The prologue (pointer save + park) and
    epilogue (output stores + callee-save restore) are themselves ordinary
    `Lopn`s `comToLfundefPhysAbi` produced, so they render uniformly here. -/
def renderLcmd (frame spillW : Nat) (body : VIR.JasminLprogExport.Lcmd)
    (lblPfx : String := "") (rvs : Bool := false)
    (qsaveB : Nat := qsaveBytesFor body) : List String :=
  body.flatMap (fun i => renderLinstrR frame spillW i.li_i lblPfx rvs qsaveB)

/-! ## 5. The leaf-function wrapper (trusted ABI scaffolding)

`renderLfundef` wraps the rendered body in a System-V function: label + `.globl`,
an allocated stack frame (`leaq -F(%rsp)`/`leaq F(%rsp)`) holding the qsave block
and spill cells (`frameSize`), the body lines, and a `ret`. The frame is
bracketed by a `pushq`/`popq` of the callee-saved GPRs a **hand-built** body
clobbers without `qsave`-parking (`calleeSavedToSave`) so the SysV callee-saved
contract holds; for a `comToLfundefPhysAbi`-produced body (which `qsave`-parks all
six) the save list is empty and no push/pop is emitted. `%rsp` returns to its
entry value before `ret`, so the function is re-callable. -/

/-- Emit the `.s` text for an owned-RA leaf function `name` whose body is the
    rendered `Lcmd`. We compute the frame `F` from the body's spill footprint,
    open it with `leaq -F(%rsp), %rsp` (jasmin's frame idiom; the qsave/spill
    offsets are shifted `+F` into the positive frame), render the body (which
    already contains the prologue/epilogue `Lopn`s), then close the frame with
    `leaq F(%rsp), %rsp` and `ret`.

    To honour the SysV callee-saved contract for **hand-built** bodies (which do
    not go through `comToLfundefPhysAbi`'s `qsave` park — e.g. MAYO's
    `VerifyEmit`, which uses `R12`/`R13` as GF(16) scratch), the frame is
    bracketed by a `pushq`/`popq` of exactly the callee-saved GPRs the body
    bare-writes without already `qsave`-parking (`calleeSavedToSave`). The pushes
    precede the `leaq -F` and the pops follow the `leaq F` (LIFO), so `%rsp` nests
    correctly and the post-`leaq` frame offsets are unchanged. For any
    `comToLfundefPhysAbi`-produced body the save list is empty and this emits
    byte-identical `.s` to before. -/
def renderLfundef (name : String) (body : VIR.JasminLprogExport.Lcmd)
    (lblPfx : String := "") (rvs : Bool := false) : String :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let saves := calleeSavedToSave body
  let pushes := saves.map (fun r => "\tpushq " ++ gpReg64 r)
  let pops := (saves.reverse).map (fun r => "\tpopq " ++ gpReg64 r)
  -- A body whose bottom-anchored `FRAMEADD` buffers claim the same cells as its
  -- vector spills carries the visible marker the `no UNHANDLED` shape gates
  -- catch, rather than aliasing the two regions silently.
  let overlapMark : List String :=
    if frameAddVecOverlap body then
      [ "\t# UNHANDLED-FRAMEADD-VECSPILL " ++ toString (frameAddDirective body) ]
    else []
  let header :=
    [ "\t.text", "\t.globl " ++ name, "\t.type " ++ name ++ ", @function", name ++ ":" ]
      ++ pushes
      ++ overlapMark
      ++ [ "\tleaq -" ++ toString frame ++ "(%rsp), %rsp" ]
  let footer :=
    ([ "\tleaq " ++ toString frame ++ "(%rsp), %rsp" ] ++ pops)
      ++ [ "\tret", "\t.section .note.GNU-stack,\"\",@progbits" ]
  -- `lblPfx` makes the local `.L<l>` labels function-scoped. gas `.L` labels are
  -- file-scoped, so two functions in one `.s` that both wrap `loopLcmd` (top
  -- label `0`) would emit two `.L0:` and collide. A multi-function emitter
  -- (`renderLprogAtt`, or a driver concatenating several `renderLfundef`) passes
  -- `<name>_` so each function's labels are unique; a standalone single-function
  -- `.s` keeps the default `""` (bare `.L<l>`, no collision possible).
  String.intercalate "\n" (header ++ renderLcmd frame spillW body lblPfx rvs ++ footer) ++ "\n"

/-! ## 6. `.rodata` global constant tables (the NTT twiddle-table seam)

A fully-emitted NTT indexes a precomputed twiddle/root-of-unity table that must
live in the read-only data segment. This section emits a `.section .rodata`
block holding one or more **named u64 tables** as `.quad` lists, so a kernel can
`leaq <name>(%rip), %reg` the base and then index it (`AsmPrinter.JInstr.loadSym`
+ `loadMemIdx`).

A table is a `(name, values)` pair (`String × List Nat`, each value a u64). The
renderer emits, per table, a `.align 8` + `<name>:` label + one `.quad v` line
per value. `renderRodata []` is the empty string (no `.rodata` directive at
all), so a program with no global tables renders byte-identically to before. -/

/-- The byte size (per element) declared for a `.rodata` table; the only width
    the twiddle tables use is 8 (u64), emitted as `.quad`. -/
abbrev RodataTable := String × List Nat

/-- Render one named `.rodata` u64 table: an 8-byte alignment, the label
    `<name>:`, and one `.quad v` line per value. -/
def renderRodataTable (t : RodataTable) : List String :=
  let (name, vals) := t
  ([ "\t.align 8", "\t.type " ++ name ++ ", @object",
     "\t.size " ++ name ++ ", " ++ toString (8 * vals.length), name ++ ":" ])
    ++ vals.map (fun v => "\t.quad " ++ toString v)

/-- Render the whole `.section .rodata` block for a list of named u64 tables.
    **Empty list ⇒ empty string** (no `.rodata` directive emitted), so a program
    with no global tables is byte-identical to the pre-`.rodata` output. -/
def renderRodata (tables : List RodataTable) : String :=
  if tables.isEmpty then ""
  else String.intercalate "\n"
    ("\t.section .rodata" :: tables.flatMap renderRodataTable) ++ "\n"

/-! ### Deriving `.rodata` tables from an `Lprog`'s globals (the back-compat guard)

The `Lprog` carries `lp_globs : List Nat` (Jasmin's flat `seq u8` global blob)
and `lp_glob_names : List (String × Nat × Nat)` (`(var, wsize, value)`). For the
twiddle-table use we read `lp_glob_names` as the named u64 entries and group
consecutive entries of the **same name** into one `.quad` table (preserving
order). The `.rodata` block is emitted **only when `lp_globs` is non-empty** —
the guard `lprogRodata` checks `p.lp_globs ≠ []` and returns `""` otherwise. Every
existing owned emit has `lp_globs = []` (the default) and so renders exactly as
before: the `.rodata` block is appended to *no* current `Lprog`. -/

/-- Group an ordered `(name, value)` list into per-name `.quad` tables, merging
    only runs of the *same* name (the producer lays a table's words contiguously).
    Order within and across tables is preserved. -/
def groupGlobNames (es : List (String × Nat)) : List RodataTable :=
  es.foldl (fun acc (nv : String × Nat) =>
    let (nm, v) := nv
    match acc.reverse with
    | (lastNm, lastVals) :: restRev =>
        if lastNm = nm then (restRev.reverse) ++ [(lastNm, lastVals ++ [v])]
        else acc ++ [(nm, [v])]
    | [] => [(nm, [v])]) []

/-- The `.rodata` block for an `Lprog`, **gated on `lp_globs` non-empty**. When the
    program declares globals (`lp_globs ≠ []`), its `lp_glob_names` `(name, _wsize,
    value)` entries are grouped by name into u64 `.quad` tables and rendered; when
    it declares none (every existing emit), this is the empty string, so the
    appended-`.rodata` `renderLprogAtt` is byte-identical to the old output. -/
def lprogRodata (p : VIR.JasminLprogExport.Lprog) : String :=
  if p.lp_globs.isEmpty then ""
  else renderRodata (groupGlobNames (p.lp_glob_names.map (fun (n, _w, v) => (n, v))))

/-! ## 7. The provenance trailer

A `.ident` directive naming the producer of the render, the counterpart of the
`.ident "Jasmin Compiler <version>"` line jasminc puts at the end of its output.
gas places `.ident` payloads in the `.comment` section, so the trailer survives
assembly into the object file and is ignored by the assembler and the linker.

`provenanceTrailer` is a pure function of a `Provenance` record: it reads no
environment variable, no file, and no clock, and the printer module runs no `IO`.
Every field passes through `sanitizeProvenanceField`, which keeps only
alphanumerics, `.`, `_` and `-`. The excluded characters include `/`, `\`, `~`,
`:`, `@` and whitespace, so no field can render as a filesystem path, a URL, an
email address, or a multi-token string. A revision is a caller-supplied field
that defaults to empty; nothing in this module derives one. -/

/-- The fixed tool marker in the provenance trailer, the string a checker greps
    an assembly file for to decide the file was rendered by this printer. -/
def provenanceMarker : String := "CatCrypt-owned-x86-emit"

/-- The characters a provenance field may contain: alphanumerics, `.`, `_`, `-`.
    `/`, `\`, `~`, `:`, `@` and whitespace are outside this set. -/
def provenanceFieldChar (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '_' || c == '-'

/-- A provenance field with every character outside `provenanceFieldChar`
    dropped. -/
def sanitizeProvenanceField (s : String) : String :=
  String.ofList (s.toList.filter provenanceFieldChar)

/-- The identity of a render: the Lean module that produced it, the front route
    the emitter took, and a source revision. `module` is a repo-relative Lean
    module name. `route` and `rev` are empty unless the caller supplies them. -/
structure Provenance where
  /-- The Lean module that produced the render, as a dotted module name. -/
  module : String
  /-- The front route the emitter took, as a combinator or pipeline name. -/
  route : String := ""
  /-- A source revision, supplied by the caller. -/
  rev : String := ""

/-- One `key=value` fragment of the trailer payload, sanitized, and empty when
    the sanitized value is empty. -/
def provenanceField (key value : String) : String :=
  let v := sanitizeProvenanceField value
  if v.isEmpty then "" else " " ++ key ++ "=" ++ v

/-- The `.ident` line carrying `provenanceMarker` and the sanitized `module`,
    `route` and `rev` fields. -/
def provenanceTrailer (pv : Provenance) : String :=
  "\t.ident\t\"" ++ provenanceMarker
    ++ provenanceField "module" pv.module
    ++ provenanceField "route" pv.route
    ++ provenanceField "rev" pv.rev
    ++ "\"\n"

/-- Render a full owned-RA `Lprog` (one export function) to AT&T `.s` text. This
    is the owned counterpart of `drive_linear` (`read_linear` +
    `compile_lprog_to_asm`): it consumes the SAME `Lprog` the patched jasmin
    encoder consumed, with no encoder dependency.

    A `.section .rodata` block of the program's named u64 global tables is
    appended **after** the functions, emitted **only when `lp_globs` is non-empty**
    (`lprogRodata`); every existing emit has `lp_globs = []`, so the trailing
    `.rodata` string is empty and the output is byte-identical to before.

    `prov` appends the `.ident` provenance trailer (§7). It defaults to `none`,
    which emits no trailer, so a call site that does not pass one renders exactly
    the same text as before. -/
def renderLprogAtt (p : VIR.JasminLprogExport.Lprog)
    (prov : Option Provenance := none) (rvs : Bool := false) : String :=
  -- Multiple functions in one `.s`: pass `<name>_` so each function's local
  -- `.L` labels are unique (gas local labels are file-scoped — two functions
  -- both wrapping `loopLcmd` would otherwise collide on `.L0`).
  let funcs := String.intercalate "\n"
    (p.lp_funcs.map (fun (n, f) => renderLfundef n f.lfd_body (n ++ "_") rvs))
  -- `.rodata` is appended only when the program declares globals (back-compat
  -- guard); for the default `lp_globs = []` this is `""` and `funcs` is returned
  -- unchanged (byte-identical to the pre-`.rodata` renderer).
  funcs ++ lprogRodata p ++ (prov.map provenanceTrailer).getD ""

/-! ### Trailer shape and privacy checks

`sampleProvenance` is a well-formed record and `adversarialProvenance` carries a
home-rooted path, an email address, a hostname and a timestamp in its fields; the
guards below pin the rendered text of the first and the sanitization of the
second. `sampleLprog` is a one-function `Lprog` with an empty body, the smallest
render that exercises the whole `renderLprogAtt` path. -/

/-- A `Provenance` with a module name and a front route, the shape an emitter
    supplies. -/
def sampleProvenance : Provenance :=
  { module := "CatCrypt.Crypto.SecureCompilation.X86Backend.Sample"
  , route := "rolledForLoopNRt" }

/-- A `Provenance` whose fields carry every character class the trailer must
    strip — a path separator, an `@`, a colon, a `+`, and a space — so no field
    can render as a path, an email address, or a timestamp. -/
def adversarialProvenance : Provenance :=
  { module := "seg/seg"
  , route := "a@b c"
  , rev := "1:2+3 ../x" }

/-- A one-function `Lprog` with an empty body. -/
def sampleLprog : VIR.JasminLprogExport.Lprog :=
  { lp_funcs := [("sample_fn", {})] }

-- The trailer of a well-formed record is one `.ident` line carrying the marker
-- and the two supplied fields.
#guard provenanceTrailer sampleProvenance =
  "\t.ident\t\"CatCrypt-owned-x86-emit"
    ++ " module=CatCrypt.Crypto.SecureCompilation.X86Backend.Sample"
    ++ " route=rolledForLoopNRt\"\n"

-- An absent field contributes nothing: `rev` defaults to empty and no `rev=`
-- fragment appears.
#guard ((provenanceTrailer sampleProvenance).splitOn "rev=").length = 1

-- No trailer text, for either record, contains a path separator, a backslash, a
-- tilde, a colon or an `@` — so no field can render as a `/`-rooted path, a
-- Windows path, a home-relative path, a timestamp, or an email address.
#guard ((provenanceTrailer sampleProvenance).toList.any
  (fun c => c = '/' || c = '\\' || c = '~' || c = ':' || c = '@')) = false
#guard ((provenanceTrailer adversarialProvenance).toList.any
  (fun c => c = '/' || c = '\\' || c = '~' || c = ':' || c = '@')) = false

-- Every stripped character class — path separator, `@`, colon, `+`, space — is
-- gone; what survives is a single token per field.
#guard provenanceTrailer adversarialProvenance =
  "\t.ident\t\"CatCrypt-owned-x86-emit"
    ++ " module=segseg"
    ++ " route=abc"
    ++ " rev=123..x\"\n"

-- A whole sample render carrying the adversarial record contains no `/`-rooted
-- path: the render itself has no `/` at all.
#guard ((renderLprogAtt sampleLprog (some adversarialProvenance)).toList.contains '/')
  = false

-- The default render emits no trailer, so a call site that passes no
-- `Provenance` is unchanged.
#guard ((renderLprogAtt sampleLprog).splitOn provenanceMarker).length = 1
#guard renderLprogAtt sampleLprog = renderLprogAtt sampleLprog none

-- The trailer is appended, not interleaved: the render with a `Provenance` is
-- the default render followed by the trailer.
#guard renderLprogAtt sampleLprog (some sampleProvenance)
  = renderLprogAtt sampleLprog ++ provenanceTrailer sampleProvenance

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
