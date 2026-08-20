/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Owned AT&T printer for the linear-jasmin owned-RA `Lcmd` (task #537)

The owned-RA linear path (`JasminLprogExport.Com.toLprogPhysAbi`) emits a
**physical-register, two-address** `Linear.lprog`: every body `Lopn` is already
allocated to a concrete x86 GP register (`RAX … R15`), a stack spill slot
(`k.N`), an ABI save slot (`qsave.X`), or a memory operand (`mem.<base>.<off>`),
and is in destructive two-address form (`MOV dst,src0; OP dst,src1`). Until now
the only consumer of that `Lprog` was the *patched* jasmin `read_linear` +
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
`phys_reg_of_name`); we transcribe it Lean-side so the encoder dependency is
gone. The trusted-but-unverified surface is then exactly `gas` (mnemonic+operands
→ bytes), the same final step every backend trusts.

## Operand-name conventions (transcribed from `patches/jasmin/read_linear.ml`)

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
    neighbouring `uint16_t` element (#656 Frodo seam). -/
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
    (`"v0" → "%zmm0"`). The `VPACK` (#656) packed-add arm names its 512-bit
    ZMM operands through this map. **Limitation (the u512 blocker):** the owned
    GP-linear allocator (`Com.toLprogPhysAbi`) has no vector-register file, so a
    512-bit value cannot be allocated to a ZMM register through that path — it
    keeps producing GP names (`RAX`…). This namer therefore only resolves an
    operand already carrying a `vN` ZMM name (a hand-built or SIMD-RA `Lcmd`); a
    GP name surfaces as an obviously-wrong `%<NOTZMM>` form gas rejects. See the
    module report — VPACK end-to-end needs a vector-RA path, out of this scope. -/
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

/-- The positive frame offset (from the post-`leaq` `%rsp`) of qsave slot `X` in
    a frame of size `frame`: the top 64 bytes hold the eight 8-byte save slots,
    slot `i` at `frame - 8·(i+1)`. -/
def qsaveFrameOff (frame : Nat) (reg : String) : Option Int :=
  (qsaveSlot reg).map (fun i =>
    if i < 8 then
      -- standard 8 callee-save slots: top of the frame (unchanged, keeps every
      -- existing kernel byte-identical).
      Int.ofNat frame - 8 * (Int.ofNat i + 1)
    else
      -- the 2nd+ SysV input-pointer slots (RDX=8 … R9=11) for multi-input array
      -- loops live in the System-V red zone BELOW %rsp (these kernels are leaves,
      -- no calls), so the frame size and the standard slots do not move.
      -(8 * (Int.ofNat i - 7)))

/-- The positive frame offset (from the post-`leaq` `%rsp`) of U32-spill slot
    `k.idx` at op width `w` in a frame of size `frame`: the spill region sits
    BELOW the 64-byte qsave block, slot `idx` at `frame - qsaveBytes -
    cell·(idx+1)` (downward-growing, disjoint from qsave). -/
def spillFrameOff (frame w idx : Nat) : Int :=
  Int.ofNat frame - Int.ofNat qsaveBytes - Int.ofNat (spillCellBytes w * (idx + 1))

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
    MOV. `frame` is the allocated frame size. Recognises, in priority order:
    spill `k.N`, ABI save `qsave.X`, memory `mem.<base>.<off>`, then a GP reg. -/
def resolveName (frame spillW w : Nat) (n : String) : String :=
  if "k.".isPrefixOf n then
    match (String.toNat? (n.drop 2).toString) with
    | some idx => toString (spillFrameOff frame spillW idx) ++ "(%rsp)"
    | none => "<BADSPILL:" ++ n ++ ">"
  else if "qsave.".isPrefixOf n then
    let reg := (n.drop 6).toString
    match qsaveFrameOff frame reg with
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

    A **register-indexed (SIB) element** `arrIdx base idx scale` (#539, the
    runtime-index image of `stackLoad`/`stackStore`) renders as the x86 effective
    address `(%base, %idx, scale)`: `base` and `idx` are physical GP register
    *names* (always addressed as full 64-bit registers in a SIB), and `scale` is
    the compile-time element stride in bytes (1/2/4/8 — the only scales x86 SIB
    encodes). This is the text-path analogue of `LprogBytes`' SIB encoder: a
    `LOADIDX` reads `dst ← (%base,%idx,scale)`, a `STOREIDX` writes
    `(%base,%idx,scale) ← src`. -/
def resolveOperand (frame spillW w : Nat) : LOperand → String
  | .reg n => resolveName frame spillW w n
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

/-- The AT&T text of a **memory-class** operand (spill `k.N`, qsave `X`,
    `mem.<base>.<off>`) at byte offset `+delta` from its base address. Used by
    the imm64-store arm to address the HIGH dword of a 64-bit slot (`+4`): x86
    has no imm64-to-memory encoding, so a ≥ 2³¹ constant stores as two `movl`
    dword writes (lo at `+0`, hi at `+4`). `none` for a non-memory operand or a
    SIB `arrIdx` (the dword split cannot re-scale a SIB stride). -/
def resolveMemPlus (frame spillW delta : Nat) : LOperand → Option String
  | .reg n =>
      if "k.".isPrefixOf n then
        match String.toNat? (n.drop 2).toString with
        | some idx =>
            some (toString (spillFrameOff frame spillW idx + Int.ofNat delta) ++ "(%rsp)")
        | none => none
      else if "qsave.".isPrefixOf n then
        match qsaveFrameOff frame ((n.drop 6).toString) with
        | some off => some (toString (off + Int.ofNat delta) ++ "(%rsp)")
        | none => none
      else if "mem.".isPrefixOf n then
        match ((n.drop 4).toString).splitOn "." with
        | [base, off] =>
            match String.toNat? off with
            | some o =>
                some ((if o + delta = 0 then "" else toString (o + delta))
                  ++ "(" ++ gpReg64 base ++ ")")
            | none => none
        | _ => none
      else none
  | _ => none

/-! ## 3. Mnemonic map: owned-RA body opcode → AT&T mnemonic + size suffix

The body mnemonics are the textual jasmin opcodes from
`JasminLprogExport.binOpName` / `opToLinstrR` (`ADD … SHR`, `MOV`, `MOVQ`,
`LOAD`/`STORE`), optionally carrying a `:64` width tag (`stripWidthTag` peels it).
Each maps to one AT&T mnemonic with the `l` (U32) or `q` (U64) size suffix. The
two-address `MUL` is x86 `IMUL` (signed/unsigned agree on the low word). The
constant-time conditional-move class `CMOVcc` (#581) is the branchless select a
*secret* condition must take (the move is unconditional, only the value is
selected) — the GE-solve pivot-swap primitive for MAYO/UOV/SNOVA sign. -/

/-- The op width (in bits) of a body mnemonic: 64 iff it carries the `:64` tag
    (or is the 64-bit-only `MOVQ`), 16 for `:16`, 8 for `:8`, else 32. The narrow
    tags `:16`/`:8` are carried only by the **ABI load/store** MOV of a narrow
    (`u16`/`u8`) buffer (the Frodo `uint16_t` ABI seam, #656); the body
    *arithmetic* stays at its natural register width (low bits exact). -/
def mnemWidth (opn : String) : Nat :=
  if opn.endsWith ":64" || opn = "MOVQ" then 64
  else if opn.endsWith ":16" then 16
  else if opn.endsWith ":8" then 8
  else 32

/-- Strip the width tag (`:64`, `:16`, `:8`) from a body mnemonic to recover the
    base opcode. The upstream `JasminLprogExport.stripWidthTag` only peels `:64`
    (the only tag the verified two-address legalizer ever sees); the printer also
    needs to recover the base of the narrow ABI MOVs `MOV:16`/`MOV:8` (#656), so
    this printer-local stripper handles all three widths without disturbing the
    legalizer's tag alphabet. -/
def stripAbiTag (opn : String) : String :=
  if opn.endsWith ":16" || opn.endsWith ":8" then
    match opn.splitOn ":" with
    | base :: _ => base
    | [] => opn
  else stripWidthTag opn

/-- The AT&T size suffix for an op width (`q` for U64, `w` for U16, `b` for U8,
    `l` for U32). -/
def sizeSuffix (w : Nat) : String :=
  if w = 64 then "q" else if w = 16 then "w" else if w = 8 then "b" else "l"

/-- The AT&T base mnemonic (no size suffix) for a stripped body opcode. `none`
    for an unmodeled opcode (call), which the renderer surfaces.

    The compare class `CMP`/`TEST` (#538) is the GP-ALU flag-setting head of a
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
  -- Compare class (#538): the flag-setting head of a branch.
  | "CMP" => some "cmp" | "TEST" => some "test"
  -- ADX carry-chain class (#477 / #500). `ADCX dst, src` adds `src + CF` into
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
  -- Constant-time conditional move class (#581). `CMOVcc dst, src` is the
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
  -- Effective-address load `LEA dst, mem` (#656 array-ABI orchestration). The
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

/-! ### Condition-code → Jcc mnemonic map (#538)

A `Lcond cond lbl` is the owned-RA conditional jump: branch to `lbl` when the
public condition `cond` holds. The `cond` operand names the x86 condition code
(`reg "NE"`, `reg "E"`, `reg "L"`, …) the preceding `CMP`/`TEST`/`SUB` set; we
map it to the matching `Jcc` mnemonic. The condition is on a **public** value
(a loop/limb count, a counter-zero test) — the constant-time discipline forbids
a secret-dependent branch (those compile to `CMOVcc`, no PC divergence). See the
`#460` vartime policy and `Cond.lean`'s public-condition note. -/

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

/-- Render one `Lopn dsts opn srcs` (not a carry-out / MULX-hi binding) to its
    AT&T line(s). Handles the three arities the owned-RA body produces:

    * **move** `Lopn [d] MOV/MOVQ/LOAD/STORE [s]` (one source) → `mov<sz> s, d`;
    * **two-address binop/shift** `Lopn [d] OP [d, s]` (two sources, `srcs[0] = d`
      the implicit x86 destination-source) → `op<sz> s, d`;
    * **ADX carry-chain** `Lopn [d] ADCX/ADOX [d, s, cin]` (three sources: the
      dst self-source, the data source, and the `reg 1` carry-in flag) →
      `adcx<sz> s, d` / `adox<sz> s, d`. The dst self-source and the implicit
      flag source are dropped (the x86 op reads CF/OF as a side input, not an
      operand). -/
def renderLopn (frame spillW : Nat) :
    List LOperand → String → List LOperand → List String
  -- `SETcc` (`SETC`, set-on-carry → byte GPR, zero-extended): one destination,
  -- **zero** data sources (the carry-in is the implicit `CF` flag, not a printed
  -- operand). Emits the `setb`/`movzbq` pair that realises the model's `setc` arm
  -- (`d := if CF then 1 else 0`): `setb %d8` sets the low byte from CF, `movzbq
  -- %d8, %d64` zero-extends to the full register. The flag-to-GPR materialisation
  -- the open-coded carry chain (`add; setc cy`) needs to keep the carry across the
  -- loop back-edge (#500/#560). Only the register-direct destination is produced
  -- (the carry GPR); a spill/mem destination would surface as the `<UNKNOWN>`
  -- form gas rejects.
  | [.reg d], opn, [] =>
      if stripWidthTag opn == "SETC" then
        [ "\tsetb " ++ gpReg8 d, "\tmovzbq " ++ gpReg8 d ++ ", " ++ gpReg64 d ]
      else [ "\t# UNHANDLED-OP " ++ opn ]
  | [d], opn, [s] =>
      let base := stripAbiTag opn
      -- **imm64 store** (the fri_proof Merkle u64 mixer constants): x86 has no
      -- imm64-to-memory encoding (`movq $imm, mem` takes a SIGN-EXTENDED imm32,
      -- so gas rejects any value ≥ 2³¹), and no scratch register exists at
      -- render time (R11 is in the RA pool). Store as two `movl` dword writes:
      -- lo at `+0`, hi at `+4` (hi = 0 still written — the imm32 form would
      -- sign-extend). Register destinations stay on the generic arm: gas
      -- selects `movabs` for imm64-to-register itself, keeping every existing
      -- kernel's text byte-identical.
      let imm64Store : Option Nat :=
        match s, attBase base with
        | .imm v, some "mov" =>
            if v > 0x7FFFFFFF && mnemWidth opn == 64 && isMemOperand d then some v
            else none
        | _, _ => none
      if let some v := imm64Store then
        match resolveMemPlus frame spillW 4 d with
        | some hiOp =>
            [ "\tmovl $" ++ toString (v % 4294967296) ++ ", "
                ++ resolveOperand frame spillW 32 d,
              "\tmovl $" ++ toString (v / 4294967296) ++ ", " ++ hiOp ]
        | none => [ "\t# UNHANDLED-IMM64-STORE " ++ opn ]
      else
      -- **Native immediate shift / rotate** (#497/#605/#606): the count is carried
      -- IN the mnemonic (`SHR:n` / `SHL:n` / `SAR:n` / `ROR:n` / `ROL:n`, from
      -- `.shrImm` / … ), not as a source operand. This MUST be checked before the
      -- `mnemWidth`/narrow-ABI-MOV logic below: the count separator `:` collides
      -- with the `:8`/`:16`/`:64` width tags, so a count of 8/16/64 (`SHR:16`) is
      -- otherwise misread as a 16-bit width and rendered as `movw` with the shift
      -- dropped (the Hawk `t1 >> 16` bug). `parseImmShiftMnem` reads the count and
      -- the real width off the raw mnemonic. Render `op<sz> $n, %d` (prepending a
      -- `mov` when the source register differs from the destination).
      if let some (m, n, w) := parseImmShiftMnem opn then
        let dop := resolveOperand frame spillW w d
        let sop := resolveOperand frame spillW w s
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
      -- **LOADIDX / STOREIDX** (#539): the register-indexed (SIB) array element.
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
              [ "\tmovzwl " ++ resolveOperand frame spillW 64 s ++ ", "
                  ++ resolveOperand frame spillW 32 d ]
            else if lw == 8 then
              [ "\tmovzbl " ++ resolveOperand frame spillW 64 s ++ ", "
                  ++ resolveOperand frame spillW 32 d ]
            else
              [ "\tmov" ++ sizeSuffix dstW ++ " "
                  ++ resolveOperand frame spillW 64 s ++ ", "
                  ++ resolveOperand frame spillW dstW d ]
        | _ => [ "\t# UNHANDLED-LOADIDX " ++ opn ]
      -- **ZEROEXT / TRUNC** (#656 cast_demo): a cross-width cast. `ZEROEXT` is the
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
      else if base == "ZEROEXT" || base == "TRUNC" then
        match s, d with
        | .reg sn, .reg dn => [ "\tmovzbl " ++ gpReg8 sn ++ ", " ++ gpReg32 dn ]
        | _, _ => [ "\t# UNHANDLED-CAST " ++ opn ]
      else
      let w := mnemWidth opn
      -- **Narrow ABI MOV** (`MOV:16` / `MOV:8`, #656 Frodo): the load/store of a
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
          [ "\t" ++ zext ++ " " ++ resolveOperand frame spillW w s ++ ", "
              ++ resolveOperand frame spillW 32 d ]
        else if isMemOperand d && !isMemOperand s then
          -- store: width-exact narrow write (no overrun)
          [ "\tmov" ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s ++ ", "
              ++ resolveOperand frame spillW w d ]
        else
          [ "\tmov" ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s ++ ", "
              ++ resolveOperand frame spillW w d ]
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
              let dop := resolveOperand frame spillW w d
              let sop := resolveOperand frame spillW w s
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
                ++ resolveOperand frame spillW w s ++ ", " ++ resolveName frame spillW w "R15",
              "\t" ++ m ++ sizeSuffix w ++ " "
                ++ resolveName frame spillW w "R15" ++ ", " ++ resolveOperand frame spillW w d ]
          else
          [ "\t" ++ m ++ sizeSuffix w ++ " "
              ++ resolveOperand frame spillW w s ++ ", " ++ resolveOperand frame spillW w d ]
      | none => [ "\t# UNHANDLED-OP " ++ opn ]
  -- BMI1 `andn` (`ANDN`): the **non-destructive 3-operand** form. Both sources
  -- are real (neither is a `dst` self-source), and `dst` is written directly:
  -- `Lopn [d] "ANDN" [a, b]` denotes `d := (~a) & b`. AT&T VEX operand order is
  -- `andn<sz> b, a, d` (`andn src2, src1, dst` ⇒ `dst = ~src1 & src2`), so the
  -- two sources are emitted in *reverse* of their IR order (`b` then `a`), unlike
  -- the destructive two-address arm. This must precede the generic two-source arm
  -- (it also has two sources) so the ANDN operand order wins.
  | [d], opn, [a, b] =>
      -- **VPACK** (#656): the AVX-512 ZMM packed-lane add `VPACK8u64:ADD` (8×u64,
      -- `vpaddq`) / `VPACK16u32:ADD` (16×u32, `vpaddd`). 3-operand AVX form
      -- `vpadd{q,d} %zmmB, %zmmA, %zmmD` (`src2, src1, dst`). The operands must be
      -- ZMM names (`vN`) — the owned GP-linear RA cannot allocate a 512-bit value
      -- to a vector register (the u512 blocker), so this arm renders only a
      -- vector-RA / hand-built `Lcmd`; a GP-allocated operand surfaces as the
      -- `%<NOTZMM>` form gas rejects. The lane width selects the suffix: a `u64`
      -- mnemonic → `vpaddq`, a `u32` mnemonic → `vpaddd`.
      if "VPACK".isPrefixOf opn then
        let mn := if (opn.splitOn "u32").length > 1 then "vpaddd" else "vpaddq"
        match a, b, d with
        | .reg an, .reg bn, .reg dn =>
            [ "\t" ++ mn ++ " " ++ zmmReg bn ++ ", " ++ zmmReg an ++ ", " ++ zmmReg dn ]
        | _, _, _ => [ "\t# UNHANDLED-VPACK " ++ opn ]
      else if stripAbiTag opn == "ANDN" then
        let w := mnemWidth opn
        [ "\tandn" ++ sizeSuffix w ++ " "
            ++ resolveOperand frame spillW w b ++ ", "
            ++ resolveOperand frame spillW w a ++ ", "
            ++ resolveOperand frame spillW w d ]
      -- **STOREIDX** (#539): the register-indexed (SIB) array element store. Sources
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
                ++ resolveOperand frame spillW sw b ++ ", "
                ++ resolveOperand frame spillW 64 a ]
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
              ++ resolveOperand frame spillW w b ++ ", "
              ++ resolveOperand frame spillW w a ++ ", "
              ++ resolveOperand frame spillW w d ]
      else
        let w := mnemWidth opn
        let mnBase := stripAbiTag opn
        match attBase mnBase with
        | some m =>
            let bOp := resolveOperand frame spillW w b
            let dOp := resolveOperand frame spillW w d
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
              let scratch := resolveName frame spillW w "R15"
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
      -- before the conditional move reads it). `d`/`cond` are register-allocated
      -- (the export's argument-liveness pin keeps the operands in distinct
      -- registers), as `cmov`/`test` require for the destination and the tested
      -- operand.
      if base == "CMOV" then
        let dOp := resolveOperand frame spillW w d
        let condOp := resolveOperand frame spillW w a
        let tOp := resolveOperand frame spillW w s
        let fOp := resolveOperand frame spillW w cin
        let sz := sizeSuffix w
        if dOp == tOp then
          [ "\ttest" ++ sz ++ " " ++ condOp ++ ", " ++ condOp,
            "\tcmove" ++ sz ++ " " ++ fOp ++ ", " ++ dOp ]
        else
          (if fOp == dOp then [] else [ "\tmov" ++ sz ++ " " ++ fOp ++ ", " ++ dOp ])
            ++ [ "\ttest" ++ sz ++ " " ++ condOp ++ ", " ++ condOp,
                 "\tcmovne" ++ sz ++ " " ++ tOp ++ ", " ++ dOp ]
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
        let dOp := resolveOperand frame spillW w d
        let aOp := resolveOperand frame spillW w a
        if !(isMemOperand d) then
          let movLine := if aOp == dOp then []
                         else [ "\tmov" ++ sizeSuffix w ++ " " ++ aOp ++ ", " ++ dOp ]
          -- FUSED carry-in (`AdxChainFuse`): the `cfCarrySentinel` carry-in means
          -- the CPU carry flag already holds the previous op's carry-out, so the
          -- `bt $0, cin` materialise-round-trip is dead — drop it and let the flag
          -- flow straight into this `adcx`/`adox`.
          let btLine := if cin == LOperand.reg cfCarrySentinel then []
                        else [ "\tbt" ++ sizeSuffix w ++ " $0, " ++ resolveOperand frame spillW w cin ]
          movLine ++ btLine
            ++ [ "\t" ++ mn ++ sizeSuffix w ++ " " ++ resolveOperand frame spillW w s ++ ", " ++ dOp ]
        else
          -- **Spilled destination** (the carry-chain kernels under register
          -- pressure): `adcx`/`adox` require a REGISTER destination (unlike the
          -- classic two-address ALU class, whose memory-destination forms the
          -- generic arm exploits), and no scratch register exists at render time
          -- (all GPs are in the RA pool — the imm64-store precedent).  `push`/
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
          let sOp := resolveOperand frame spillW w s
          let cOp := resolveOperand frame spillW w cin
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
              ++ resolveOperand frame spillW w s ++ ", " ++ resolveOperand frame spillW w d ]
      | none => [ "\t# UNHANDLED-OP " ++ opn ]
  -- BMI2 widening multiply `MULX` (#656 byte-direct field leaves): TWO
  -- destinations `[dstLo, dstHi]` and one explicit source `src2` (the implicit
  -- src1 is `%rdx`, pinned by the kernel allocation — not a printed operand).
  -- AT&T order is `mulx src2, dstLo, dstHi` (reg form, no size suffix — the
  -- operands fix the 64-bit width) / `mulxq off(%base), dstLo, dstHi` (memory
  -- form). Matches `AsmPrinter.renderJInstr`'s `.mulx`/`.mulxMem` lines, so the
  -- text path and the `LprogBytes` byte path agree.
  | [dl, dh], opn, [s] =>
      let base := stripWidthTag opn
      if base == "MULX" || base == "MULXMEM" then
        let rs := resolveOperand frame spillW 64 s
        let rdl := resolveOperand frame spillW 64 dl
        let rdh := resolveOperand frame spillW 64 dh
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

/-- Render one owned-RA `LinstrR` to its AT&T line(s) in a frame of size `frame`.

    Returns `[]` for `Lret`/`Lalign` (the leaf wrapper emits `ret`) and for the
    carry-out / MULX-high *bindings* (the flag / high word is a side effect of
    the matching data op), and a visible sentinel comment for any unexpected
    shape (never a silent drop). -/
def renderLinstrR (frame spillW : Nat) (i : LinstrR) (lblPfx : String := "") : List String :=
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
      -- The `FRAME` directive (#656 array-ABI orchestration) is a frame-size
      -- annotation consumed by `frameSize`; it issues no x86 line (drop before the
      -- arity arms so the empty-dst form doesn't surface as UNHANDLED-LOPN).
      if opn == "FRAME" then [] else
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
      -- `lowerLinstrExtCov` `ADCXHI → setc dst` expansion). The data `ADCX` arm
      -- below leaves CF as the carry-out and only flag-safe moves intervene.
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
              let slot := resolveName frame spillW 64 dn
              [ "\tmovq $0, " ++ slot, "\t" ++ setcc ++ " " ++ slot ]
            else
              [ "\t" ++ setcc ++ " " ++ gpReg8 dn, "\tmovzbq " ++ gpReg8 dn ++ ", " ++ gpReg64 dn ]
        | _ => []
      else
        renderLopn frame spillW dsts opn srcs
  | .Lret => []
  | .Lalign => []
  | .Llabel _ l => [ ".L" ++ lblPfx ++ toString l ++ ":" ]
  -- Control flow (#538). A local internal label `Lgoto ("", l)` (the back-edge
  -- of a bounded loop / a forward skip) renders as `jmp .L<l>`; a remote target
  -- `Lgoto (f, l)` keeps the function symbol. `Lcond (reg cc) l` is the
  -- conditional back-edge / guard: emit `j<cc> .L<l>` mapping the public
  -- condition-code name to its `Jcc` mnemonic. The flag the Jcc reads is set by
  -- the preceding `CMP`/`SUB`/`TEST` body op (the GP-ALU compare class).
  | .Lgoto ("", l) => [ "\tjmp .L" ++ lblPfx ++ toString l ]
  | .Lgoto (f, l) => [ "\tjmp " ++ f ++ "  # .L" ++ lblPfx ++ toString l ]
  | .Lcond (.reg cc) l => [ "\t" ++ attCC cc ++ " .L" ++ lblPfx ++ toString l ]
  | .Lcond c l => [ "\t# UNHANDLED-COND " ++ c.toText ++ " .L" ++ lblPfx ++ toString l ]
  -- Cross-function call (#656). `Lcall ra (f, _)` is a direct near `call` to the
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

/-- The maximum U32-spill index `k.N` referenced in a body (`none` if no spill),
    used to size the frame. -/
def maxSpillIdx (body : VIR.JasminLprogExport.Lcmd) : Option Nat :=
  body.foldl (fun acc i =>
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
    | _ => acc) none

/-- True iff the body is a U64 kernel (any body mnemonic carries the `:64` tag or
    is `MOVQ`). The spill stride is then 8 bytes, else 4 — kernels are uniform
    width (`comToLfundefPhysAbi` tags every `regArith` op at the source width). -/
def bodyIsU64 (body : VIR.JasminLprogExport.Lcmd) : Bool :=
  body.any (fun i =>
    match i.li_i with
    | .Lopn _ opn _ => opn.endsWith ":64"
    | _ => false)

/-- An explicit frame-size directive `Lopn [] "FRAME" [.imm F]` (#656 array-ABI
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

/-- The allocated frame size `F` (bytes, 16-aligned) for a body: an explicit
    `FRAME` directive if present (the array-ABI orchestration), else the 64-byte
    qsave block plus every spill cell (`cell·(maxIdx+1)`, cell = 8 for a U64 body,
    4 for U32). A 16-byte tail pad keeps `%rsp` ABI-aligned after the `leaq -F`. -/
def frameSize (body : VIR.JasminLprogExport.Lcmd) : Nat :=
  match frameDirective body with
  | some f => (f + 15) / 16 * 16
  | none =>
    let cell := if bodyIsU64 body then 8 else 4
    let spillBytes := match maxSpillIdx body with
                      | some m => cell * (m + 1)
                      | none => 0
    let raw := qsaveBytes + spillBytes
    let f16 := (raw + 15) / 16 * 16
    -- A body that issues a real `call` needs `%rsp ≡ 0 (mod 16)` AT each call
    -- instruction (SysV): function entry is `≡ 8` (the pushed return address),
    -- so the frame must be `≡ 8 (mod 16)`. A 16-aligned F leaves every call
    -- site misaligned and an SSE-using C leaf (`movaps` stack spills) faults.
    -- Call-free bodies keep the 16-aligned F (byte-identical).
    if VIR.JasminLprogExport.bodyHasCall body then f16 + 8 else f16

/-- Render a whole `Lcmd` body's instruction lines in a frame of size `frame`
    (flattening the per-`Lopn` line lists). The prologue (pointer save + park) and
    epilogue (output stores + callee-save restore) are themselves ordinary
    `Lopn`s `comToLfundefPhysAbi` produced, so they render uniformly here. -/
def renderLcmd (frame spillW : Nat) (body : VIR.JasminLprogExport.Lcmd)
    (lblPfx : String := "") : List String :=
  body.flatMap (fun i => renderLinstrR frame spillW i.li_i lblPfx)

/-! ### Callee-saved GP park/restore for hand-built bodies (#596)

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

This is **inert** for the linear-jasmin path: every callee-saved register those
bodies write as a bare destination is also `qsave`-parked (`buildPrologue` saves
all six unconditionally), so `calleeSavedToSave` returns `[]` and the emitted
`.s` is byte-identical to before. It is also inert for any body that touches no
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
    second push/pop (that would diverge from the byte-identical baseline). -/
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
    (lblPfx : String := "") : String :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let saves := calleeSavedToSave body
  let pushes := saves.map (fun r => "\tpushq " ++ gpReg64 r)
  let pops := (saves.reverse).map (fun r => "\tpopq " ++ gpReg64 r)
  let header :=
    [ "\t.text", "\t.globl " ++ name, "\t.type " ++ name ++ ", @function", name ++ ":" ]
      ++ pushes
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
  String.intercalate "\n" (header ++ renderLcmd frame spillW body lblPfx ++ footer) ++ "\n"

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
    (prov : Option Provenance := none) : String :=
  -- Multiple functions in one `.s`: pass `<name>_` so each function's local
  -- `.L` labels are unique (gas local labels are file-scoped — two functions
  -- both wrapping `loopLcmd` would otherwise collide on `.L0`).
  let funcs := String.intercalate "\n"
    (p.lp_funcs.map (fun (n, f) => renderLfundef n f.lfd_body (n ++ "_")))
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
