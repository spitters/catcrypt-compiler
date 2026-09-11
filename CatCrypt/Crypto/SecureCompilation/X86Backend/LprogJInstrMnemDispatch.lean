/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

/-!
# Closing the byte-agreement's mnemonic-dispatch residual (kernel-clean, no `native_decide`)

`LprogJInstrBytesAgree` proves the D4 byte-agreement at the **post-dispatch**
`encTwoAddr` layer: each per-mnemonic lemma (`add_bytes_agree`, …) ties the JInstr
encoding to `encTwoAddr frame spillW w op (.reg dn) (.reg sn)` — the byte function the
Lprog dispatcher *lands in*. Its §2b / §3 docstrings flag the one remaining step as
`native_decide`-only: reducing the **full** `encodeLopn frame spillW (.Lopn … "ADD:64" …)`
down to that `encTwoAddr … 0x01 …` requires evaluating the closed-string mnemonic
dispatch — `isCarryOutBinding`/`isMulHiBinding`, `stripWidthTag`, `mnemWidth`/`rexW`,
the `== "MULX"`/`== "MULXMEM"` guards, `adxPrefix`, and `aluOpcode` — all of which route
through `String.endsWith`/`String.beq`/the UTF-8 iterator and so do **not** reduce by
`rfl`/`simp` in the kernel.

This file closes that residual *without* `native_decide`, using the same observation
that cracked the analogous shift-mnemonic wall in `ShiftMnemSymbolic`: even though
`rfl`/`simp` cannot reduce a `Slice`/UTF-8-backed `String.endsWith`/`==`, **`decide +kernel`
reduces a CLOSED string** through it (the boolean decision procedure forces the iterator
to a concrete value the kernel can check). Every guard in `encodeLopn`'s dispatch, on a
**fixed** mnemonic literal, is a closed-string boolean/`Option` fact, so each is
`decide +kernel`-closable; feeding the resulting equalities to `simp only [encodeLopn, …]`
drives the full dispatch reduction. (No symbolic `sw_iff` is needed here: the byte-agreement
covers a *fixed* mnemonic alphabet — `ADD:64`/…/`LOAD`/`STORE` — so each is closed. The
symbolic `sw_iff` route of `ShiftMnemSymbolic` is reserved for the `SHR:<n>:64` family,
where the count `n` is symbolic.)

## What is proved

### §1 — Per-mnemonic dispatch facts (`encodeLopn → encTwoAddr`)

For each covered mnemonic the byte-agreement uses, the full `encodeLopn` dispatch reduces
to the post-dispatch `encTwoAddr` byte function, at the width tag the mnemonic actually
carries:

* ALU / `MOV` (`ADD:64`/`SUB:64`/`AND:64`/`OR:64`/`XOR:64`/`MOV:64`): `:64` ⇒ `w = 1`,
  `encodeLopn … = encTwoAddr frame spillW 1 op d s` at the SDM opcode `op`. Proved for
  **both** source-list arities the export uses — the one-source form `[s]` and the
  two-source (dst self-source) form `[_, s]`.
* `LOAD`/`STORE` (no width tag): `w = rexW 32 = 0`, `encodeLopn … = encTwoAddr frame spillW 0 op d s`.

These are the dispatch facts §2b of the byte-agreement *stated but did not prove*.

### §2 — The byte-agreement, now `native_decide`-free end-to-end

Chaining §1 with the byte-agreement's existing `*_bytes_agree` lemmas (which are
themselves kernel-clean — `rfl` on the JInstr side + `simp only` on the `encTwoAddr` side):
`encodeJInstr alloc (covered JInstr) = encodeLopn frame spillW (the matching covered Lopn)`,
the **full** Lprog dispatcher, under the same resolver-agreement + covered-domain
hypotheses. The mnemonic→opcode resolution that was the documented `native_decide`-only
obligation is now discharged in the kernel by `decide +kernel`, so the D4 byte-agreement
is `native_decide`-free (and axiom-free) end-to-end.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (isCarryOutBinding isMulHiBinding mnemWidth)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LinstrR LOperand stripWidthTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

/-! ## §1. Per-mnemonic dispatch facts: `encodeLopn` reduces to `encTwoAddr`

Each lemma reduces the full `encodeLopn` mnemonic dispatch on a *fixed* mnemonic literal
to its post-dispatch `encTwoAddr` byte function. The dispatch guards
(`isCarryOutBinding`/`isMulHiBinding`, `stripWidthTag`, `rexW ∘ mnemWidth`,
`== "MULX"`/`== "MULXMEM"`, `adxPrefix`, `aluOpcode`) are closed-string boolean/`Option`
facts on the literal, each discharged by `decide +kernel` — the closed-string route the
kernel *can* reduce even though `rfl`/`simp` cannot. The operands `d`/`s` are passed
straight through the ALU arm (no further string dispatch), so they may stay symbolic. -/

/-- **ALU/`MOV` one-source dispatch.** On the export's one-source ALU/`MOV` form
    `Lopn [.reg dn] "<MNEM>:64" [.reg sn]`, the full `encodeLopn` dispatch reduces to the
    width-`1` reg-reg byte function `encTwoAddr frame spillW 1 op …`, with the SDM opcode
    `op` already resolved by the (closed-string) `aluOpcode` dispatch. -/
theorem dispatch_alu_one
    (frame spillW op : Nat) (mnem base : String) (dn sn : String)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 1)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (halu : aluOpcode base = some op)
    (htag : tagShiftExt base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn])
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, halu, htag,
    Bool.false_eq_true, if_false]

/-- **ALU/`MOV` two-source (dst self-source) dispatch.** The same reduction on the
    two-source export form `Lopn [.reg dn] "<MNEM>:64" [.reg d0, .reg sn]` (`d0` the dst
    self-source). The `[d], [_, s]` arm routes identically to `encTwoAddr`. -/
theorem dispatch_alu_two
    (frame spillW op : Nat) (mnem base : String) (dn d0 sn : String)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 1)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (halu : aluOpcode base = some op)
    (htag : tagShiftExt base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg d0, .reg sn])
      = encTwoAddr frame spillW 1 op (.reg dn) (.reg sn) := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, halu, htag,
    Bool.false_eq_true, if_false]

/-- **`LOAD`/`STORE` dispatch (width-`0`, untagged).** The memory mnemonics carry no
    `:64` tag, so `mnemWidth = 32` and `w = 0`; the dispatch reduces to
    `encTwoAddr frame spillW 0 op …`. -/
theorem dispatch_mem
    (frame spillW op : Nat) (mnem base : String) (dn sn : String)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 0)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (halu : aluOpcode base = some op)
    (htag : tagShiftExt base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn])
      = encTwoAddr frame spillW 0 op (.reg dn) (.reg sn) := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, halu, htag,
    Bool.false_eq_true, if_false]

/-! ### §1a. The concrete dispatch lemmas (closed mnemonics, `decide +kernel` guards)

Instantiate §1 on each covered mnemonic literal. Every hypothesis is a closed-string
boolean/`Option` fact discharged by `decide +kernel` — kernel-clean, no `native_decide`. -/

/-- `ADD:64` (opcode `0x01`) one-source dispatch. -/
theorem encodeLopn_add (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADD:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x01 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x01 "ADD:64" "ADD" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `SUB:64` (opcode `0x29`) one-source dispatch. -/
theorem encodeLopn_sub (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SUB:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x29 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x29 "SUB:64" "SUB" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `AND:64` (opcode `0x21`) one-source dispatch. -/
theorem encodeLopn_and (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "AND:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x21 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x21 "AND:64" "AND" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `OR:64` (opcode `0x09`) one-source dispatch. -/
theorem encodeLopn_or (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "OR:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x09 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x09 "OR:64" "OR" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `XOR:64` (opcode `0x31`) one-source dispatch. -/
theorem encodeLopn_xor (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "XOR:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x31 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x31 "XOR:64" "XOR" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `MOV:64` (opcode `0x89`) one-source dispatch. -/
theorem encodeLopn_mov (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "MOV:64" [.reg sn])
      = encTwoAddr frame spillW 1 0x89 (.reg dn) (.reg sn) :=
  dispatch_alu_one frame spillW 0x89 "MOV:64" "MOV" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `ADD:64` two-source (dst self-source) dispatch. -/
theorem encodeLopn_add₂ (frame spillW : Nat) (dn d0 sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADD:64" [.reg d0, .reg sn])
      = encTwoAddr frame spillW 1 0x01 (.reg dn) (.reg sn) :=
  dispatch_alu_two frame spillW 0x01 "ADD:64" "ADD" dn d0 sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `SUB:64` two-source (dst self-source) dispatch. -/
theorem encodeLopn_sub₂ (frame spillW : Nat) (dn d0 sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SUB:64" [.reg d0, .reg sn])
      = encTwoAddr frame spillW 1 0x29 (.reg dn) (.reg sn) :=
  dispatch_alu_two frame spillW 0x29 "SUB:64" "SUB" dn d0 sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `LOAD` (opcode `0x8b`, untagged ⇒ `w = 0`) dispatch. -/
theorem encodeLopn_load (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "LOAD" [.reg sn])
      = encTwoAddr frame spillW 0 0x8b (.reg dn) (.reg sn) :=
  dispatch_mem frame spillW 0x8b "LOAD" "LOAD" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `STORE` (opcode `0x89`, untagged ⇒ `w = 0`) dispatch. -/
theorem encodeLopn_store (frame spillW : Nat) (dn sn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "STORE" [.reg sn])
      = encTwoAddr frame spillW 0 0x89 (.reg dn) (.reg sn) :=
  dispatch_mem frame spillW 0x89 "STORE" "STORE" dn sn
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ## §2. The byte-agreement, now `native_decide`-free end-to-end

Chain §1 (full `encodeLopn` dispatch → `encTwoAddr`, the formerly `native_decide`-only
step) with the byte-agreement's existing `encTwoAddr`-layer `*_bytes_agree` lemmas. The
result ties `encodeJInstr alloc (covered JInstr)` to the **full** Lprog dispatcher
`encodeLopn frame spillW (matching covered Lopn)` — no `encTwoAddr` intermediate, no
`native_decide`, under the same resolver-agreement + covered-domain hypotheses as the
byte-agreement. -/

/-- **`ADD` end-to-end** (`native_decide`-free): the JInstr `add` encoding equals the
    full Lprog `encodeLopn` dispatch on the `ADD:64` reg-reg `Lopn`. -/
theorem add_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.add d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "ADD:64" [.reg sn]) := by
  rw [add_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_add]

/-- **`SUB` end-to-end** (`native_decide`-free). -/
theorem sub_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.sub d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "SUB:64" [.reg sn]) := by
  rw [sub_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_sub]

/-- **`AND` end-to-end** (`native_decide`-free). -/
theorem and_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.and_ d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "AND:64" [.reg sn]) := by
  rw [and_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_and]

/-- **`OR` end-to-end** (`native_decide`-free). -/
theorem or_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.or_ d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "OR:64" [.reg sn]) := by
  rw [or_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_or]

/-- **`XOR` end-to-end** (`native_decide`-free). -/
theorem xor_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.xor_ d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "XOR:64" [.reg sn]) := by
  rw [xor_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_xor]

/-- **`MOV` end-to-end** (`native_decide`-free). -/
theorem mov_dispatch_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.mov d (.reg r))
      = encodeLopn frame spillW (.Lopn [.reg dn] "MOV:64" [.reg sn]) := by
  rw [mov_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs,
    encodeLopn_mov]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
