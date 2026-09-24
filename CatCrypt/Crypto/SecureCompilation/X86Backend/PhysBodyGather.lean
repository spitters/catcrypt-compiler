/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-!
# `PhysBodyGather` — does gathering the PHYSICAL body byte-match the Lprog encoder?

This module is an **empirical** probe of whether the `JInstr` gather and the
`Lprog` byte encoder produce identical bytes.
Fed the **virtual** body (`Com.toLprog … |>.lfd_body`), whose operands are the
SSA virtual registers, `JInstrGatherExtended.gatherJBlock2` diverges from the
`Lprog` byte encoder (`LprogBytes.encodeLcmd`): the virtual body is
*non-destructive three-address*, so the gather SSA-splits each two-source
`OP d s0 s1` into `mov d s0 ; OP d s1`, adding a self-`mov` the `Lprog` encoder
never emits.

The hypothesis under test here: `Com.toLprogPhysAbi` produces the **physical**
body, post-register-allocation, in destructive two-address form with physical
registers. Gathering THAT body should add no SSA-split self-`mov`, so its framed
`JInstr` bytes should byte-match `encodeLcmd` of the same physical body.

## The empirical result (see the `#eval`s in `GoldenPathByteIdentityDemo`)

Tested on the real GoldenPath kernel `AsconLinear.asconSigma0Com` (`Σ₀ x`).

**The whole physical body does NOT gather** (`gatherJBlock2 physBody = none`):
the System-V framing instructions — the 8 callee-save `MOVQ qsave.X, X` spills,
the arg-marshal `MOVQ R14, RSI`, and the 8 `MOVQ X, qsave.X` restores — are
outside the `lowerLinstrExtCovL` superset fragment (it covers width-tagged
`regArith` / immediate shifts / ADX / SIB, but not the bare-`MOVQ` qsave
park/restore). That framing is supplied by the prologue/epilogue, not the body
gather, so the meaningful comparison is on the **ALU core** (drop the `MOVQ`
framing and the trailing `Lret`).

**On the ALU core, the byte-compare is `NO`** (`encodeJBlock` = 64 bytes vs
`encodeLcmd` = 24 bytes; first divergence at byte index 2). The physical body
does NOT eliminate the divergence, for two independent structural reasons:

1. **The gather inserts a self-`mov`, here `mov d d`.** Even though the
   physical body's two-source ops are already destructive (`OR:64 [RDX]
   [RDX, RCX]`, i.e. `RDX |= RCX`), `lowerLinstrExtCovL` lowers *every*
   two-source `Lopn [d] op [s0, s1]` into `mov d s0 ; OP d s1` **unconditionally**
   — it does not check `d == s0`. So a destructive `OR:64 [RDX] [RDX, RCX]`
   becomes `mov RDX, RDX` (a redundant self-`mov`, `48 89 D2`) `+ or RDX, RCX`.
   The `Lprog` `encodeLopn` encodes the same `Lopn` directly as a single
   `or %rcx, %rdx` (`48 09 CA`), no self-`mov`. Same divergence as the virtual
   body — the physical body's destructiveness does not help, because the gather
   re-splits regardless.

2. **The count-in-tag immediate shift.**
   `Com.toLprogPhysAbi` (default oracle) emits the shift as `Lopn [RAX]
   "SHR:19:64" [RBX]` — the count `19` is in the **mnemonic tag**, the source is
   a **register**. `lowerLinstrExtCovL` lowers this to `mov RAX, RBX ; shr RAX,
   $19` (7 bytes). The `encTagShift` arm of `LprogBytes.encodeLopn`
   (`BlockBytesAgreeExtended.encodeLopn_shr19_emits`) encodes the
   `Lopn [d] "SHR:n:64" [reg s]` form as the `shr RAX, $19` op (`48 c1 e8 13`),
   so the shift OP agrees with the gather's trailing `shr`; the residual is the
   gather's leading materialise `mov`.

## Bottom line

Gathering the physical body does **not** by itself make the two encoders
byte-identical modulo framing: the divergence is **not** a virtual-vs-physical
artifact. The self-`mov` persists in the non-in-place `gatherJBlock2` because its
two-source lowering is unconditionally SSA-splitting (the `d == s0 ⇒ skip the mov`
peephole that fixes it lives in `GatherInPlace.gatherJBlock3`). For the
count-in-tag shift, `encodeLopn`'s `encTagShift` arm makes the shift OP
byte-agree, leaving only the gather's per-shift materialise `mov` as the shift
residual. Byte identity therefore needs the in-place gather (`gatherJBlock3`)
together with the `encTagShift` encoder arm; the physical body alone does not
suffice.

All goals closed; no axiom, no `native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage

/-! ## 1. The physical-body extraction setup

The kernel-`Com`-specific physical-body defs (`physBody`, `aluCore` on
`AsconLinear.asconSigma0Com`) and their `#eval` byte-compare certificates are
re-homed in `GoldenPathByteIdentityDemo` (above the chain), so this chain file
is GoldenPath-free. The kernel-independent pieces — the `MOVQ` framing predicate
`isMovq` and the identity allocation `physAlloc` — stay here, re-used by the
downstream gather modules and the demo. -/

/-- Whether an `Linstr` is a bare-`MOVQ` qsave park/restore / arg-marshal (the
    framing the prologue/epilogue supplies, not the body gather). -/
def isMovq (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn _ opn _ => opn == "MOVQ"
  | _             => false

/-- An identity allocation mapping each bare-uppercase physical register name
    (`encodeLcmd` reads these via `gpNumU`) to the `%`-prefixed name
    `encodeJBlock` reads via `gpNum`. With this, the two encoders address the
    *same* physical registers, so any byte difference is purely the lowering. -/
def physAlloc : List (String × String) :=
  [("RAX","%rax"),("RCX","%rcx"),("RDX","%rdx"),("RBX","%rbx"),
   ("RSP","%rsp"),("RBP","%rbp"),("RSI","%rsi"),("RDI","%rdi"),
   ("R8","%r8"),("R9","%r9"),("R10","%r10"),("R11","%r11"),
   ("R12","%r12"),("R13","%r13"),("R14","%r14"),("R15","%r15")]

/-! ## 2. The empirical byte-compare

The byte-compare `#eval`s on `asconSigma0`'s physical body (`physBody`/`aluCore`
vs `encodeLcmd`) live in `GoldenPathByteIdentityDemo` so this file is
GoldenPath-free. -/

/-! ## 3. Result

The physical body does NOT by itself remove the self-`mov` divergence:
`lowerLinstrExtCovL` SSA-splits every two-source `Lopn` unconditionally (no
`d == s0` peephole), so a destructive `OR:64 [RDX] [RDX, RCX]` lowers to
`mov RDX, RDX ; or RDX, RCX` whereas the `Lprog` encoder emits the single
`or %rcx, %rdx`. The count-in-tag immediate shift (`SHR:n:64 [d] [reg s]`) has
an arm in `encodeLopn` (the `encTagShift` arm), so the shift OP byte-agrees; the
remaining shift residual is the gather's leading materialise `mov`.
Byte identity therefore needs the in-place gather
(`GatherInPlace.gatherJBlock3`) over the physical body, with the `encTagShift`
encoder arm.

These are `#eval`s, not `rfl`/`decide` theorems, for the same reason
`JInstrGatherExtended` records: `LoweringExtended.parseShiftMnem` dispatches the
immediate-shift arm via `String.startsWith`, which does not kernel-reduce in
Lean 4.29; only the compiled `#eval` evaluator runs it. (The result here is in
any case a *negative* byte-match, so there is no positive equality theorem to
state.) -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
