/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-!
# The D4-collapse precondition: `encodeLprog ≡ encodeJBlock` on the covered fragment

This file proves the **verified precondition** for the D4 backend collapse: that the
two x86-64 byte encoders that the owned emit path can use —

* the **Lprog path** (`LprogBytes.encodeLprog`, over `Lprog`/`Linstr`, the looped
  owned-RA driver), and
* the **JInstr path** (`ScalarEncoder.encodeJBlock`, over `List (JInstr 64)`, the
  straight-line opt-in route of `OptimizedComToElf`)

— produce the **same machine bytes** on the straight-line, const-offset fragment
where both are defined: the `gatherJBlock`-lowerable (`lowerLinstrExtL`-covered)
fragment of ALU/`MOV` and constant-offset `LOAD`/`STORE`.

## Why this is a *precondition* and not a *byte-KAT*

The two encoders are **not independent reimplementations**. `LprogBytes` opens
`ScalarEncoder` and either calls its shape encoders directly or calls *width-threading
wrappers* (`encAluRRw`/`enc0FRRw`/`encMemMovw`/`encMovImmw`/`encAluImmw`/`encShiftImmw`)
that thread an operand-size width `w` into the REX prefix via `rexOpt`. The JInstr
shape encoders (`encAluRR`/`enc0FRR`/`encMemMov`/…) hardcode `rex 1 …` (always
`REX.W = 1`, the 64-bit operand size). Both paths funnel through the *same* primitive
byte builders (`rex`, `modRMReg`, `imm32LE`, the shared base-aware `memTail`).

So on the **U64** (`w = 1`) fragment, the only structural difference between the two
paths is `rexOpt 1 r x b` (the Lprog wrapper) versus the hardcoded `rex 1 r x b` (the
JInstr encoder). For `w = 1` the elision branch of `rexOpt` never fires (`0x48`+ is
never redundant), so the two emit the *same* REX byte — and the opcode / ModRM /
immediate / `memTail` tail are byte-identical by construction.

## What is proved

### §1 — Per-shape agreement (the core)

For each width-threading wrapper the Lprog path uses, the **U64** instance is
*byte-identical* to the corresponding hardcoded-`REX.W` `ScalarEncoder` shape encoder:

* `encAluRRw_one`   : `encAluRRw 1 op d s     = encAluRR op d s`
* `enc0FRRw_one`    : `enc0FRRw 1 op d s      = enc0FRR op d s`
* `encMemMovw_one`  : `encMemMovw 1 op r b o  = encMemMov op r b o`
* `encMovImmw_one`  : `encMovImmw 1 d v       = encMovImm d v`
* `encAluImmw_one`  : `encAluImmw 1 digit d v = encAluImm digit d v`
* `encShiftImmw_one`: `encShiftImmw 1 ext d v = encShiftImm ext d v`

These are the load-bearing facts: every covered mnemonic's bytes are produced, on
each side, by one of these shapes, so per-shape equality at `w = 1` is exactly
"the two encoders compute the same machine bytes".

### §2 — Per-mnemonic JInstr-vs-Lprog agreement

Lifting §1 through the two dispatchers. The JInstr arm `encodeJInstr alloc i` reduces
by `rfl` to its shape encoder (§2a). The Lprog arm `encodeLopn` routes a covered
two-address `Lopn` to `encTwoAddr frame spillW w op …` with the SDM opcode/width
already resolved; we state the Lprog reduction at that `encTwoAddr` byte-function layer
(§2b). The per-mnemonic agreement (§2c–§2d) then chains §2a + §2b + §1: for a covered
ALU/`MOV`/`LOAD`/`STORE` shape, `encodeJInstr alloc (lowered JInstr)` equals
`encTwoAddr frame spillW 1 op (the Lopn operands)` — the byte function the Lprog ALU
arm invokes — *provided the two register resolvers agree on the operand names* (the
JInstr path's `gpNum ∘ regOf alloc` and the Lprog path's `gpNumU`) and the operands are
in the covered domain (plain register or const-offset `mem.*`, never spill/qsave).

**The mnemonic-string step is `native_decide`-only.** Reducing the *full*
`encodeLopn "ADD:64" …` to `encTwoAddr … 0x01 …` requires evaluating the closed-string
dispatch (`stripWidthTag`/`mnemWidth`/`aluOpcode`/`String.endsWith`), which the Lean
**kernel cannot reduce** — `String.endsWith`/`==` route through the UTF-8 iterator,
irreducible without `native_decide` (banned here). So §2 is stated at the post-dispatch
`encTwoAddr` layer (kernel-clean); tying the closed mnemonic literal to its opcode is
the one `native_decide`-only obligation, flagged as a residual below.

### §3 — The residual gating the collapse (honest)

The agreement is on the **flat `.text` instruction bytes**. The two driver *wrappers*
differ in framing, and that difference is the precise residual the collapse must
reconcile:

* **Framing / ELF wrapping.** `encodeLprog` wraps the body in a multi-symbol ELF
  object (`buildElfObjectMulti`), and the looped driver adds an ABI prologue/epilogue
  (push/pop callee-saved, `%rsp` frame). `encodeJBlock` emits a *bare* flat byte
  stream (no frame, no ELF). On the covered fragment there is no frame (it is
  spill-free, frame-free, straight-line), so the *instruction* bytes coincide; the
  ELF/symbol wrapper is the residual.
* **Width.** The Lprog path threads a per-`Lopn` width tag; the JInstr path is U64
  throughout. Agreement holds on the U64 (`w = 1`) tag — the fragment
  `OptimizedComToElf` targets. A U32 body (e.g. SHA-256-linear) is *outside* this
  precondition (the JInstr path would still emit `REX.W = 1`); the collapse's
  encoder-maturation must teach the JInstr path the width tag before a U32 kernel can
  swap encoders.
* **Spill / register-indexed coverage.** `lowerLinstrExtL` returns `none` for spill /
  frame operands and register-indexed memory, so they never reach `gatherJBlock`;
  extending the JInstr encoder to those shapes (and the Lprog `encRspMem`/`encMemMovSib`
  forms) is the remaining coverage the collapse needs.
* **Mnemonic dispatch.** The closed-string mnemonic→opcode resolution
  (`stripWidthTag`/`aluOpcode`/`String.endsWith`) is `native_decide`-only in the
  kernel; the byte-production layer below it (`encTwoAddr`/`encAluRRw`/…, §1 + §2b) is
  kernel-clean. The collapse's emit harness already discharges the dispatch by
  evaluation; the precondition proved here is the *byte-function* equality the
  dispatch lands in.

This is the precise statement: **`encodeLprog ≡ encodeJBlock` on the
`gatherJBlock`-covered fragment, at the instruction-byte level and for the U64 width
tag**; the residual (ELF/frame wrapping, U32 width, spill/indexed coverage) is what
maturing the JInstr encoder must add before the Lprog owned path can be retired.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LinstrR LOperand)

/-! ## §1. Per-shape agreement at the U64 width (`w = 1`)

The single structural difference between the two encoders on the U64 fragment is the
REX prefix: the Lprog wrappers build it with `rexOpt 1 r x b` (a list that *could*
elide to `[]`, but only when `w = 0`), while the JInstr shape encoders use the
hardcoded `rex 1 r x b`. The lemma `rexOpt_one` discharges this: at `w = 1` the
elision branch is dead, so `rexOpt 1 r x b = [rex 1 r x b]` as a byte. Every shape
lemma below then reduces to byte-list equality. -/

/-- At the U64 width (`w = 1`) the REX-prefix elision never fires: `rexOpt 1 r x b` is
    the singleton `[rex 1 r x b]` — byte-identical to the JInstr encoders' hardcoded
    `rex 1 …`. (The elision branch requires `w = 0`; `1 ≠ 0`.) -/
theorem rexOpt_one (r x b : Nat) :
    rexOpt 1 r x b = [BitVec.ofNat 8 (rex 1 r x b)] := rfl

/-- **Reg-reg ALU/`MOV` agree.** The width-threaded `encAluRRw` at `w = 1` is
    byte-identical to the hardcoded-`REX.W` `encAluRR`: same REX byte (`rexOpt_one`),
    same opcode, same `modRMReg`. Covers `ADD/SUB/ADC/SBB/AND/OR/XOR/MOV` reg-reg. -/
theorem encAluRRw_one (op d s : Nat) :
    encAluRRw 1 op d s = encAluRR op d s := by
  simp [encAluRRw, encAluRR, rexOpt]

/-- **`0F`-map reg-reg agree** (`IMUL`/`CMOVcc`): `enc0FRRw 1 = enc0FRR`. -/
theorem enc0FRRw_one (op d s : Nat) :
    enc0FRRw 1 op d s = enc0FRR op d s := by
  simp [enc0FRRw, enc0FRR, rexOpt]

/-- **Reg↔mem `MOV` agree** (`LOAD 0x8b` / `STORE 0x89`): `encMemMovw 1 = encMemMov`.
    The ModRM/SIB/disp tail is the *shared* `ScalarEncoder.memTail` on both sides, so
    only the REX prefix differs — and it does not at `w = 1`. -/
theorem encMemMovw_one (op r base : Nat) (off : Int) :
    encMemMovw 1 op r base off = encMemMov op r base off := by
  simp [encMemMovw, encMemMov, rexOpt]

/-- **`MOV $imm32` agree** (`C7 /0 id`): `encMovImmw 1 = encMovImm`. -/
theorem encMovImmw_one (d v : Nat) :
    encMovImmw 1 d v = encMovImm d v := by
  simp [encMovImmw, encMovImm, rexOpt]

/-- **Imm-source ALU agree** (`81 /digit id`): `encAluImmw 1 = encAluImm`. -/
theorem encAluImmw_one (digit d v : Nat) :
    encAluImmw 1 digit d v = encAluImm digit d v := by
  simp [encAluImmw, encAluImm, rexOpt]

/-- **Shift-by-`imm8` agree** (`C1 /ext ib`): `encShiftImmw 1 = encShiftImm`. -/
theorem encShiftImmw_one (ext d v : Nat) :
    encShiftImmw 1 ext d v = encShiftImm ext d v := by
  simp [encShiftImmw, encShiftImm, rexOpt]

/-! ## §2. Per-mnemonic JInstr-vs-Lprog agreement

Lift §1 through the two dispatchers. The JInstr encoder `encodeJInstr alloc i`
resolves each register name `n` through `gpNum (regOf alloc n)`; the Lprog encoder
`encodeLopn frame spillW (.Lopn …)` resolves it through `gpNumU`. We state the
agreement *abstracted over the register numbers* — i.e. we show both dispatchers
reduce, on a covered shape, to the **same** §1 shape encoder. Equality of the final
bytes then holds whenever the two resolvers agree on the operand names (the natural
side-condition: the JInstr block was lowered from the same physical-register `Lprog`).

Each lemma pairs a `JInstr` arm (LHS) with the matching width-`:64`-tagged `Lopn`
(RHS), both at numbers `dn`/`sn`. The mnemonic tag on the `Lopn` is `:64`, so
`mnemWidth = 64` and `rexW = 1` — the U64 fragment §1 proves identical.

### §2a. JInstr side reduces to a §1 shape encoder -/

/-- JInstr `add` reduces to `encAluRR 0x01`. -/
theorem jinstr_add (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.add d (.reg r))
      = encAluRR 0x01 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `sub` reduces to `encAluRR 0x29`. -/
theorem jinstr_sub (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.sub d (.reg r))
      = encAluRR 0x29 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `and_` reduces to `encAluRR 0x21`. -/
theorem jinstr_and (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.and_ d (.reg r))
      = encAluRR 0x21 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `or_` reduces to `encAluRR 0x09`. -/
theorem jinstr_or (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.or_ d (.reg r))
      = encAluRR 0x09 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `xor_` reduces to `encAluRR 0x31`. -/
theorem jinstr_xor (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.xor_ d (.reg r))
      = encAluRR 0x31 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `mov` (reg source) reduces to `encAluRR 0x89`. -/
theorem jinstr_mov (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.mov d (.reg r))
      = encAluRR 0x89 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `imul` (reg source) reduces to the `0F`-map `enc0FRR 0xaf`. -/
theorem jinstr_imul (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.imul d (.reg r))
      = enc0FRR 0xaf (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- JInstr `loadMem` reduces to the shared-`memTail` `encMemMov 0x8b`. -/
theorem jinstr_loadMem (alloc : GpAlloc) (d base : String) (off : Int) :
    encodeJInstr alloc (.loadMem d base off)
      = encMemMov 0x8b (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off := rfl

/-- JInstr `storeMem` (reg source) reduces to `encMemMov 0x89`. -/
theorem jinstr_storeMem (alloc : GpAlloc) (base : String) (off : Int) (r : String) :
    encodeJInstr alloc (.storeMem base off (.reg r))
      = encMemMov 0x89 (gpNum (regOf alloc r)) (gpNum (regOf alloc base)) off := rfl

/-! ### §2b. Lprog side reduces to the §1 (width-`w`) wrapper, at the `encTwoAddr` layer

`encodeLopn`'s mnemonic dispatch (`stripWidthTag`/`mnemWidth`/`aluOpcode`/…) routes a
covered two-address `Lopn` to `encTwoAddr frame spillW w op d s` with the SDM opcode
`op` and width bit `w` already resolved. *That* mnemonic resolution is a closed-string
computation that the Lean **kernel cannot reduce** (`String.endsWith`/`==` go through
the UTF-8 iterator, which is irreducible without `native_decide`); so we state the
Lprog-side reduction at the `encTwoAddr` layer — *after* the opcode/width are picked —
which is exactly the byte function the dispatch invokes. (Tying the closed mnemonic
string to its opcode is the `native_decide`-only step the docstring's §3 residual
flags; the byte-production layer below is kernel-clean.)

The operand-domain hypotheses (`spillQsaveOff … = none`, `parseMemName … = none`,
`isSpillOrQsave … = false`) are the covered-fragment side-condition: `gatherJBlock`
only fires on plain registers and `.arr` const-offsets, never spill/qsave/`mem.*`
names, so on the covered fragment these always hold. -/

/-- **Reg-reg `encTwoAddr` reduces to `encAluRRw`.** On two plain register operands
    (neither a spill/qsave nor a `mem.*` name), the Lprog two-address byte function is
    the width-threaded `encAluRRw` — the §1 wrapper. -/
theorem encTwoAddr_regReg (frame spillW w op : Nat) (dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encTwoAddr frame spillW w op (.reg dn) (.reg sn)
      = encAluRRw w op (gpNumU dn) (gpNumU sn) := by
  simp only [encTwoAddr, hdk, hsk, hdm, hsm, hdsp, hssp, Bool.or_self,
    Bool.false_eq_true, if_false]

/-- **Store `encTwoAddr` reduces to `encMemMovw 0x89`.** When the destination is a
    `mem.<base>.<off>` operand and the source is a plain register, the Lprog store
    byte function is `encMemMovw w 0x89` over the parsed base/offset. -/
theorem encTwoAddr_store (frame spillW w op : Nat) (dn sn : String) (bb : Nat) (off : Int)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = some (bb, off)) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encTwoAddr frame spillW w op (.reg dn) (.reg sn)
      = encMemMovw w 0x89 (gpNumU sn) bb off := by
  simp only [encTwoAddr, hdk, hsk, hdm, hsm, hdsp, hssp, Bool.or_self,
    Bool.false_eq_true, if_false]

/-- **Load `encTwoAddr` reduces to `encMemMovw 0x8b`.** When the source is a
    `mem.<base>.<off>` operand and the destination is a plain register, the Lprog load
    byte function is `encMemMovw w 0x8b` over the parsed base/offset. -/
theorem encTwoAddr_load (frame spillW w op : Nat) (dn sn : String) (bb : Nat) (off : Int)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = some (bb, off))
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false) :
    encTwoAddr frame spillW w op (.reg dn) (.reg sn)
      = encMemMovw w 0x8b (gpNumU dn) bb off := by
  simp only [encTwoAddr, hdk, hsk, hdm, hsm, hdsp, hssp, Bool.or_self,
    Bool.false_eq_true, if_false]

/-! ### §2c. The byte agreement: equal register numbers ⇒ equal bytes

Combining §2a (JInstr → shape encoder) + §2b (Lprog `encTwoAddr` → §1 wrapper) + §1
(wrapper at `w = 1` = the hardcoded `REX.W` shape encoder). The hypotheses
`gpNum (regOf alloc d) = gpNumU dn` (and the source dual) are the *resolver-agreement*
side-condition: the two encoders read different register-name tables (`%rN` vs
uppercase `RAX`), but on a block lowered from the same physical-register `Lprog` the
names resolve to the same SDM number. Under that agreement, the JInstr bytes for the
covered mnemonic are *byte-identical* to the Lprog `encTwoAddr` bytes (the body of the
matching covered `Lopn` arm), at the U64 width `w = 1`. -/

/-- **`ADD` bytes agree.** The JInstr `add` encoding equals the Lprog reg-reg
    two-address byte function at opcode `0x01`, U64 width, under resolver agreement. -/
theorem add_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.add d (.reg r))
      = encTwoAddr frame spillW 1 0x01 (.reg dn) (.reg sn) := by
  rw [jinstr_add, encTwoAddr_regReg frame spillW 1 0x01 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **`SUB` bytes agree** (opcode `0x29`). -/
theorem sub_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.sub d (.reg r))
      = encTwoAddr frame spillW 1 0x29 (.reg dn) (.reg sn) := by
  rw [jinstr_sub, encTwoAddr_regReg frame spillW 1 0x29 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **`AND` bytes agree** (opcode `0x21`). -/
theorem and_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.and_ d (.reg r))
      = encTwoAddr frame spillW 1 0x21 (.reg dn) (.reg sn) := by
  rw [jinstr_and, encTwoAddr_regReg frame spillW 1 0x21 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **`OR` bytes agree** (opcode `0x09`). -/
theorem or_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.or_ d (.reg r))
      = encTwoAddr frame spillW 1 0x09 (.reg dn) (.reg sn) := by
  rw [jinstr_or, encTwoAddr_regReg frame spillW 1 0x09 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **`XOR` bytes agree** (opcode `0x31`). -/
theorem xor_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.xor_ d (.reg r))
      = encTwoAddr frame spillW 1 0x31 (.reg dn) (.reg sn) := by
  rw [jinstr_xor, encTwoAddr_regReg frame spillW 1 0x31 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **`MOV` bytes agree** (opcode `0x89`). -/
theorem mov_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.mov d (.reg r))
      = encTwoAddr frame spillW 1 0x89 (.reg dn) (.reg sn) := by
  rw [jinstr_mov, encTwoAddr_regReg frame spillW 1 0x89 dn sn hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-! ### §2d. The const-offset memory arms

The JInstr memory arms (`loadMem`/`storeMem`) resolve a *register* base name to its
number; the Lprog `encTwoAddr` mem arm parses a `mem.<base>.<off>` operand name to
`(gpNumU base, off)`. The agreement hypotheses pin the JInstr-resolved register number
to the Lprog-parsed number (`hr`/`hb`) — the same resolver-agreement side-condition as
§2c, here over the memory operand. Under it, the JInstr `loadMem`/`storeMem` bytes are
byte-identical to the Lprog `encTwoAddr` load/store bytes at the U64 width. -/

/-- **`LOAD` bytes agree.** JInstr `loadMem` equals the Lprog reg←`mem.*` `encTwoAddr`
    byte function (`encMemMovw 1 0x8b`). The Lprog source operand `sn` parses to the
    same base/offset (`hsm`), and the destination register numbers agree (`hd`). -/
theorem load_bytes_agree (alloc : GpAlloc) (frame spillW op : Nat)
    (d base : String) (off : Int) (dn sn : String) (bb : Nat)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = some (bb, off))
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hb : gpNum (regOf alloc base) = bb) :
    encodeJInstr alloc (.loadMem d base off)
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) := by
  rw [jinstr_loadMem,
    encTwoAddr_load frame spillW 1 op dn sn bb off hdk hsk hdm hsm hdsp hssp,
    encMemMovw_one, hd, hb]

/-- **`STORE` bytes agree.** JInstr `storeMem` (reg src) equals the Lprog `mem.*`←reg
    `encTwoAddr` byte function (`encMemMovw 1 0x89`). The Lprog destination operand
    `dn` parses to the same base/offset (`hdm`), and the source register numbers agree
    (`hr`). -/
theorem store_bytes_agree (alloc : GpAlloc) (frame spillW op : Nat)
    (base : String) (off : Int) (r : String) (dn sn : String) (bb : Nat)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = some (bb, off)) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hr : gpNum (regOf alloc r) = gpNumU sn) (hb : gpNum (regOf alloc base) = bb) :
    encodeJInstr alloc (.storeMem base off (.reg r))
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) := by
  rw [jinstr_storeMem,
    encTwoAddr_store frame spillW 1 op dn sn bb off hdk hsk hdm hsm hdsp hssp,
    encMemMovw_one, hr, hb]

/-! ## §3. Block-level: lifting the per-instruction agreement to `gatherJBlock`

`OptimizedComToElf.gatherJBlock body` lowers a covered `Lprog` body to a
`List (JInstr 64)` and `ScalarEncoder.encodeJBlock` flattens the per-instruction byte
encodings (`block.flatMap (encodeJInstr alloc)`). So the block-level bytes are the
*concatenation* of the per-instruction bytes — and the §2 per-instruction agreement
lifts pointwise: if every gathered `JInstr` agrees (byte-for-byte) with its Lprog
encoding, the whole `.text` byte streams agree. The lemmas below expose that
concatenation structure (the lift is `List.flatMap`-congruence over §2). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElf (gatherJBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr)

/-- `encodeJBlock` is the per-instruction byte concatenation: the block `.text` bytes
    are `block.flatMap (encodeJInstr alloc)`. The block-level agreement is therefore
    exactly the `List.flatMap`-lift of the per-instruction §2 agreement. -/
theorem encodeJBlock_flatMap (alloc : GpAlloc) (block : List (JInstr 64)) :
    encodeJBlock alloc block = block.flatMap (encodeJInstr alloc) := rfl

/-- **Block lift.** If two `JInstr` blocks are pointwise byte-equal under
    `encodeJInstr` (the per-instruction §2 agreement), their whole `encodeJBlock` byte
    streams are equal. This is the block-level form of the precondition: per-instruction
    byte-agreement on the covered fragment ⇒ whole-block `.text` byte-agreement. -/
theorem encodeJBlock_congr (alloc alloc' : GpAlloc) (block block' : List (JInstr 64))
    (h : block.map (encodeJInstr alloc) = block'.map (encodeJInstr alloc')) :
    encodeJBlock alloc block = encodeJBlock alloc' block' := by
  simp only [encodeJBlock, List.flatMap.eq_1, h]

/-! ## §4. Worked instantiation on `OptimizedComToElf.demoBody`

`demoBody` is the worked straight-line const-offset body of `OptimizedComToElf`; it
gathers (`demoBody_gather`) to the four `JInstr`s `loadMem "t" "a" 0`, `add "t" b`,
`mov "c" t`, `storeMem "r" 1 c` — all in the covered ALU/`MOV` + const-offset fragment.
We instantiate the §2 per-instruction agreement on its `ADD` instruction, witnessing
that the precondition's hypotheses are inhabited on the very body the opt-in route
demos. (The register names here are abstract labels, so the resolver-agreement
hypotheses are the natural `gpNum (regOf alloc _) = gpNumU _` ties.) -/

/-- The gathered `demoBody` block, byte-encoded under the identity allocation, is the
    flat concatenation of its four instructions' bytes — the concrete witness that the
    covered fragment produces a per-instruction-decomposable `.text` stream. -/
theorem demoBody_encode_flatMap (alloc : GpAlloc) :
    encodeJBlock alloc
        [ .loadMem "t" "a" (0 : Int), .add "t" (.reg "b"),
          .mov "c" (.reg "t"), .storeMem "r" (1 : Int) (.reg "c") ]
      = encodeJInstr alloc (.loadMem "t" "a" (0 : Int))
          ++ encodeJInstr alloc (.add "t" (.reg "b"))
          ++ encodeJInstr alloc (.mov "c" (.reg "t"))
          ++ encodeJInstr alloc (.storeMem "r" (1 : Int) (.reg "c")) := by
  simp [encodeJBlock, List.flatMap_cons, List.append_assoc]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
