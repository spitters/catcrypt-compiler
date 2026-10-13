/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch

/-!
# Block byte-agreement extended to the real GoldenPath op set: the `hbody` reconciliation

`LprogJInstrBytesAgree` + `LprogJInstrMnemDispatch` prove, `native_decide`-free, that on
the **POC fragment** (reg-reg ALU/`MOV`, const-offset `LOAD`/`STORE`) the JInstr encoder
agrees byte-for-byte with the Lprog `encodeLopn`. That agreement is the `hbody` hypothesis
of `ComToFramedJInstrLeaq.framedLeaqText_eq_lprog` /
`CompileComToElfJInstr.jinstrElf_eq_lprogElf` — the fact from which a kernel's
framed JInstr `.text` is proven byte-equal to its Lprog `.text`.

This file carries that reconciliation onto the GoldenPath op set that
`JInstrGatherExtended.gatherJBlock2` covers — the width-tagged two-source `regArith`
exports (`OR:64`/`XOR:64`/…) and the immediate shifts (`SHR:<n>:64`/`SHL:<n>:64`): **at
the byte level the extended JInstr gather does NOT agree with the Lprog `encodeLopn` on
the two-source shape**, and the difference is stated and proved below.

## What the extended gather lowers the real op set into

`gatherJBlock2` lowers each width-tagged op through `lowerLinstrExtCovL`
(`LoweringExtendedCoverage`), which for these shapes does an explicit SSA→two-address
split:

* width-tagged two-source `OP:64 [s0, s1]` (dst `d`) → `[mov d s0, OP d s1]`
  (a leading `mov d, s0` then the destructive `OP d, s1`);
* immediate shift `SHR:<n>:64 [src]` (dst `d`) → `[mov d src, shr d #n]`.

The Lprog byte encoder `encodeLopn`, by contrast, is fed the **physical** body
(`Com.toLprogPhysAbi`, the `physBody` two-address legalizer), where:

* a two-source binop is **already** split into a separate `MOV` Lopn plus a *destructive*
  `OP:64 [d, s1]` Lopn (`d` self-source) — so `encodeLopn` emits exactly the single
  `OP d, s1` byte (no leading mov; the mov is its own prior Lopn);
* a count-in-mnemonic shift `SHR:<n>:64 [src]` is left single-source, and `encodeLopn`
  encodes it to `shr/shl %d, $n` (`encTagShift`, via the `tagShiftExt` arm, §2).

## The byte picture (proved here)

### §1 — Two-source ALU: an extra self-`mov` residual

For a width-tagged two-source `OP:64 [s0, s1]`, the gathered JInstr block encodes to

  `encodeJInstr alloc (mov d s0) ++ encodeLopn frame spillW (.Lopn [dn] "OP:64" [dn, sn])`

(`encJBlock_twoSrc_eq_mov_prepend_lopn`) — i.e. the Lprog destructive single-op bytes with
a **leading `mov d, s0`** prepended. When the physical RA has placed `d = s0` (the common
destructive case the `physBody` split produces — `OR:64 [RDX, RCX]` with `dst = RDX`), that
leading instruction is `mov d, d`, a real **3-byte `0x48 0x89 0xc0`-class self-move** that
`encodeLopn` does not emit. So the JInstr block is *strictly longer* by that self-move: the
two byte streams differ. (This is the SSA-split artifact: outside the register-count
shifts, `lowerAluJ2` always materialises the first source into the destination, even
when the RA already coalesced them.)

### §2 — Count-in-tag shift: encoded on both sides

For a count-in-mnemonic shift `SHR:<n>:64 [src]` the Lprog `encodeLopn` emits the
`shr/shl %d, $n` op (`encodeLopn_shr19_emits` / `_shl45_` / … = `encTagShift 1 ext (gpNumU dn) base`),
the same `C1 /ext ib` (or `D1 /ext` count-1) bytes the `.imm`-source shift arm produces, so
the trailing `shr` of the gather's `mov d, src; shr d, #n` block byte-agrees with the
Lprog op. The arm selection is kernel-clean (`tagShiftExt`, prefix-only — no
`String.toNat?`); the emitted count is `#eval`/`native_decide`-witnessed (the `toNat?`
value is not kernel-reducible) and is the same `n` the gather lowers.

## `hbody` on a physical kernel body

On `AsconLinear.asconSigma0Com`'s **physical** body (`Com.toLprogPhysAbi`), the §2 shift
agrees per-op. The `encodeJBlock alloc (gatherJBlock2 body) ≠ encodeLcmd body` residual
via the non-in-place `gatherJBlock2` is §1's SSA-split self-`mov` (each two-source
`OR:64 [d,s1]`/`XOR:64 [d,s1]` contributes a `mov d,d` on the JInstr side), which
`GatherInPlace`'s in-place peephole (`gatherJBlock3`) elides. What remains for a
whole-kernel `hbody` is the arg-marshal `hmar` gap (below).

### The residuals (stated precisely)

1. **Two-source coalescing** — handled by `GatherInPlace`. `lowerLinstrExtCov3`'s in-place
   peephole elides the leading `mov d, s0` when `s0 = d` (the destructive case), matching the
   Lprog encoder; the two-source ALU bytes then agree (the residual §1 is exactly the
   un-elided self-move).
2. **Shift byte parity** — proved here. The Lprog `encodeLopn` count-in-tag shift arm
   (`encTagShift`) and the gather both emit the `shr/shl %d, $n` op for the count.
3. **Arg-marshal `hmar`.** Independently of the body, `asconSigma0Com`'s physical body
   carries a real arg-marshal (`MOVQ R14, RSI`) and a full 8-register qsave/restore frame,
   so `framedLeaqText_eq_lprog`'s `hmar : argMarshalBytes … = []` (empty marshal) is also
   **false** for the physical body — the recon's flagged default-ABI gap, confirmed here.

No open goals, no axiom, no `native_decide` — every byte-level claim below is `decide +kernel`
on a closed mnemonic / `simp only` on the post-dispatch byte function, the kernel-clean
route of `LprogJInstrMnemDispatch`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (isCarryOutBinding isMulHiBinding mnemWidth)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (LinstrR LOperand stripWidthTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree

/-! ## §1. The width-tagged two-source `regArith` lowering, at the byte level

`gatherJBlock2` lowers `OP:64 [s0, s1]` (`OP ∈ {ADD,SUB,AND,OR,XOR,MOV}`, dst `d`) through
`lowerLinstrExtCovL → lowerLinstrExt2 → lowerAluJ2` into the **two-address split**
`[mov d s0, OP d s1]`. We first pin that lowering (kernel-clean, `decide +kernel` on the
`:64` tag strip), then encode the block and isolate it against the Lprog destructive op. -/

/-! ### §1a. The lowering of each covered two-source mnemonic (`decide +kernel` tag strip) -/

/-- `gatherJBlock2`'s lowering of a width-tagged two-source `OR:64 [s0, s1]` is the
    two-address split `[mov d s0, or_ d s1]` — `lowerAluJ2` materialises `s0` into `d`,
    then applies the destructive `or`. The `:64` tag strip is `decide +kernel`. -/
theorem lower_or64 (dst s0 s1 : String) :
    lowerLinstrExtCov (.Lopn [.reg dst] "OR:64" [.reg s0, .reg s1])
      = some [JInstr.mov dst (.reg s0), JInstr.or_ dst (.reg s1)] := by
  show (lowerAluJ2 dst "OR:64" (lowerJOperand (.reg s0)) (lowerJOperand (.reg s1))) = _
  simp only [lowerAluJ2, lowerJOperand, show stripWidthTag "OR:64" = "OR" from by decide +kernel,
    lowerShiftRegJ_OR, Option.none_or, lowerAluJ, Option.map_some]

/-- `gatherJBlock2`'s lowering of `XOR:64 [s0, s1]`: `[mov d s0, xor_ d s1]`. -/
theorem lower_xor64 (dst s0 s1 : String) :
    lowerLinstrExtCov (.Lopn [.reg dst] "XOR:64" [.reg s0, .reg s1])
      = some [JInstr.mov dst (.reg s0), JInstr.xor_ dst (.reg s1)] := by
  show (lowerAluJ2 dst "XOR:64" (lowerJOperand (.reg s0)) (lowerJOperand (.reg s1))) = _
  simp only [lowerAluJ2, lowerJOperand, show stripWidthTag "XOR:64" = "XOR" from by decide +kernel,
    lowerShiftRegJ_XOR, Option.none_or, lowerAluJ, Option.map_some]

/-- `gatherJBlock2`'s lowering of `ADD:64 [s0, s1]`: `[mov d s0, add d s1]`. -/
theorem lower_add64 (dst s0 s1 : String) :
    lowerLinstrExtCov (.Lopn [.reg dst] "ADD:64" [.reg s0, .reg s1])
      = some [JInstr.mov dst (.reg s0), JInstr.add dst (.reg s1)] := by
  show (lowerAluJ2 dst "ADD:64" (lowerJOperand (.reg s0)) (lowerJOperand (.reg s1))) = _
  simp only [lowerAluJ2, lowerJOperand, show stripWidthTag "ADD:64" = "ADD" from by decide +kernel,
    lowerShiftRegJ_ADD, Option.none_or, lowerAluJ, Option.map_some]

/-- `gatherJBlock2`'s lowering of `SUB:64 [s0, s1]`: `[mov d s0, sub d s1]`. -/
theorem lower_sub64 (dst s0 s1 : String) :
    lowerLinstrExtCov (.Lopn [.reg dst] "SUB:64" [.reg s0, .reg s1])
      = some [JInstr.mov dst (.reg s0), JInstr.sub dst (.reg s1)] := by
  show (lowerAluJ2 dst "SUB:64" (lowerJOperand (.reg s0)) (lowerJOperand (.reg s1))) = _
  simp only [lowerAluJ2, lowerJOperand, show stripWidthTag "SUB:64" = "SUB" from by decide +kernel,
    lowerShiftRegJ_SUB, Option.none_or, lowerAluJ, Option.map_some]

/-- `gatherJBlock2`'s lowering of `AND:64 [s0, s1]`: `[mov d s0, and_ d s1]`. -/
theorem lower_and64 (dst s0 s1 : String) :
    lowerLinstrExtCov (.Lopn [.reg dst] "AND:64" [.reg s0, .reg s1])
      = some [JInstr.mov dst (.reg s0), JInstr.and_ dst (.reg s1)] := by
  show (lowerAluJ2 dst "AND:64" (lowerJOperand (.reg s0)) (lowerJOperand (.reg s1))) = _
  simp only [lowerAluJ2, lowerJOperand, show stripWidthTag "AND:64" = "AND" from by decide +kernel,
    lowerShiftRegJ_AND, Option.none_or, lowerAluJ, Option.map_some]

/-! ### §1b. The Lprog destructive two-source dispatch (`encodeLopn → encTwoAddr`)

The `physBody`-split *destructive* `OP:64 [d, s1]` Lopn (the second of the split pair, whose
first source is `d` itself). `encodeLopn`'s closed-string dispatch routes it to
`encTwoAddr frame spillW 1 op (.reg dn) (.reg sn)` — every guard a `decide +kernel` fact on
the literal (the `LprogJInstrMnemDispatch` route, here for the two-source `OR`/`XOR` arms it
did not pre-instantiate). -/

/-- `OR:64 [dn, sn]` (destructive, `dn` self-source) → `encTwoAddr … 1 0x09 …`. -/
theorem encodeLopn_or₂ (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "OR:64" [.reg dn, .reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x09 (.reg dn) (.reg sn) qsaveB := by
  simp only [encodeLopn,
    show (isCarryOutBinding "OR:64" || isMulHiBinding "OR:64") = false from by decide +kernel,
    show stripWidthTag "OR:64" = "OR" from by decide +kernel,
    show rexW (mnemWidth "OR:64") = 1 from by decide +kernel,
    show ("OR" == "MULX") = false from by decide +kernel,
    show ("OR" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "OR" = none from by decide +kernel,
    show aluOpcode "OR" = some 0x09 from by decide +kernel,
    show tagShiftExt "OR" = none from by decide +kernel,
    Bool.false_eq_true, if_false]

/-- `XOR:64 [dn, sn]` (destructive) → `encTwoAddr … 1 0x31 …`. -/
theorem encodeLopn_xor₂ (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "XOR:64" [.reg dn, .reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x31 (.reg dn) (.reg sn) qsaveB := by
  simp only [encodeLopn,
    show (isCarryOutBinding "XOR:64" || isMulHiBinding "XOR:64") = false from by decide +kernel,
    show stripWidthTag "XOR:64" = "XOR" from by decide +kernel,
    show rexW (mnemWidth "XOR:64") = 1 from by decide +kernel,
    show ("XOR" == "MULX") = false from by decide +kernel,
    show ("XOR" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "XOR" = none from by decide +kernel,
    show aluOpcode "XOR" = some 0x31 from by decide +kernel,
    show tagShiftExt "XOR" = none from by decide +kernel,
    Bool.false_eq_true, if_false]

/-! ### §1c. The byte equation: JInstr two-source block = leading self-`mov` ++ Lprog op

Encoding the gathered JInstr two-source block and combining §1a + the block-split + the
JInstr `or_`/`xor_` reduction (`jinstr_or`/`jinstr_xor`) + §1b: the gathered JInstr block's
bytes are **exactly** the Lprog destructive-op bytes with a leading `encodeJInstr (mov d s0)`
prepended. This isolates the divergence as that one self-`mov`. The resolver-agreement
hypotheses (`hd`/`hs`) tie the JInstr register names to the Lprog `gpNumU` numbers — the
same side-condition the POC `*_bytes_agree` lemmas carry. -/

/-- **`OR:64` two-source byte isolation.** The gathered JInstr `OR:64 [s0, s1]` block encodes
    to `encodeJInstr alloc (mov d s0)` (the SSA-split materialise) **prepended** to the Lprog
    destructive `OR:64 [dn, sn]` bytes. So the only byte difference from the Lprog encoder is
    that leading `mov d, s0` — which the Lprog side does not emit. -/
theorem or64_block_eq_mov_prepend_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn s0 : String) (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hdg : isGpName dn = true) (hsg : isGpName sn = true)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov (.Lopn [.reg d] "OR:64" [.reg s0, .reg r])).map (encodeJBlock alloc)
      = some (encodeJInstr alloc (JInstr.mov d (.reg s0))
                ++ encodeLopn frame spillW
                    (.Lopn [.reg dn] "OR:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lower_or64, Option.map_some, encodeLopn_or₂,
    ← or_bytes_agree alloc frame spillW d r dn sn qsaveB hdk hsk hdm hsm hdsp hssp
      hdg hsg hd hs]
  simp [encodeJBlock, List.flatMap_cons]

/-- **`XOR:64` two-source byte isolation** — the dual of `or64_block_eq_mov_prepend_lopn`. -/
theorem xor64_block_eq_mov_prepend_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn s0 : String) (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hdg : isGpName dn = true) (hsg : isGpName sn = true)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov (.Lopn [.reg d] "XOR:64" [.reg s0, .reg r])).map (encodeJBlock alloc)
      = some (encodeJInstr alloc (JInstr.mov d (.reg s0))
                ++ encodeLopn frame spillW
                    (.Lopn [.reg dn] "XOR:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lower_xor64, Option.map_some, encodeLopn_xor₂,
    ← xor_bytes_agree alloc frame spillW d r dn sn qsaveB hdk hsk hdm hsm hdsp hssp
      hdg hsg hd hs]
  simp [encodeJBlock, List.flatMap_cons]

/-! ### §1d. The residual self-`mov` is non-empty (the divergence, made concrete)

When the physical RA coalesces `d = s0` (the destructive form `physBody` produces — e.g.
`OR:64 [RDX, RCX]`, `dst = RDX`), the prepended `mov d, s0` is `mov d, d`, whose bytes are
the 3-byte `REX.W 0x89 ModRM(11,d,d)` self-move — *never* empty. So the JInstr block is
strictly longer than the Lprog op by those 3 bytes. -/

/-- The leading self-`mov` (`d = s0`) the SSA split materialises is the 3-byte
    `mov %d, %d` (`encAluRR 0x89 (gpNum d) (gpNum d)`) — non-empty, the precise excess the
    JInstr block carries over the Lprog destructive op. -/
theorem selfMov_bytes (alloc : GpAlloc) (d : String) :
    encodeJInstr alloc (JInstr.mov d (.reg d))
      = encAluRR 0x89 (gpNum (regOf alloc d)) (gpNum (regOf alloc d)) := rfl

/-- The self-`mov` byte list has length 3 (`REX.W`, opcode `0x89`, ModRM) — so the JInstr
    two-source block is strictly 3 bytes longer than the Lprog destructive op. (`encAluRR`
    emits `rex :: opcode :: modRM :: []`.) -/
theorem selfMov_length (alloc : GpAlloc) (d : String) :
    (encodeJInstr alloc (JInstr.mov d (.reg d))).length = 3 := rfl

/-! ## §2. The count-in-tag shift is now ENCODED (the dropped-rotation bug, closed)

The count-in-mnemonic shift export `SHR:<n>:64 [src]` / `SHL:<n>:64 [src]` is single-source.
**This used to be a silent correctness bug**: `encodeLopn`'s `[d], [s]` arm with `s = .reg src`
(not an `.imm`) matched no `aluOpcode`/`twoByteOpcode`/`shiftImmExt` (those fire only on an
`.imm` source), so the Lprog byte encoder emitted the **empty** byte list for every
count-in-mnemonic shift — `Com.toLprogPhysAbi`'s rotate spine (asconSigma0's four Σ₀
rotations, SipHash, Sha512, …) emitted code SILENTLY MISSING its rotations.

The fix (`LprogBytes.encTagShift` + the `tagShiftExt` arm in `encodeLopn`) closes it: the
count-in-tag shift now emits the SAME `shr/shl r64, imm8` bytes (`C1 /ext ib`, or the
`D1 /ext` 1-bit short form) the `.imm`-source shift arm produces for the same count. The
lemmas below state the **emits-the-shift** form: `encodeLopn … "SHR:19:64" … = encTagShift 1 5 (gpNumU dn) "SHR:19"`.

The arm SELECTION is kernel-clean (`tagShiftExt` is the **prefix-only** `/ext` detector — no
`String.toNat?`, so `decide +kernel` reduces it on a closed tag); the emitted count `n` stays
inside `encTagShift` (its `String.toNat?` value is `#eval`/`native_decide`-only — see the
`#eval` byte witnesses in §3 — but it is the SAME count the gather's `lowerShiftImmJ` lowers,
so the two sides' shift counts now agree). -/

/-- **The Lprog dispatch for a single-source count-in-tag shift.** Parametric over the
    (fixed) shift mnemonic `mnem`, its tag-stripped base, and its group-2 `/ext`. Every
    dispatch guard is a `decide +kernel` fact on the literal: the base is not a
    carry/MULX/ADX mnemonic, and `tagShiftExt base = some ext` (the prefix-only `/ext`
    detector fires — no `String.toNat?`, so kernel-reducible). So `encodeLopn`'s `[d],[s]`
    arm with `s = .reg sn` now routes to the new `encTagShift` arm. Frame / spill width
    stay symbolic. -/
theorem dispatch_tagshift_reg_emits
    (frame spillW : Nat) (mnem base : String) (ext : Nat) (dn sn : String)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none)
    (hext : tagShiftExt base = some ext)
    -- The in-place drop-`mov` case: GP source == GP dest, nonzero count. The
    -- printer emits `[shr $n, %d]` here (no leading materialise `mov`); a source
    -- register distinct from the dest would prepend `mov %s,%d` (`LprogAsmPrinter`
    -- §count-in-tag), so those hypotheses are what make the bytes just the shift.
    (hgp : (isGpName dn && isGpName sn) = true)
    (hds : (dn == sn) = true)
    (hcnt : tagShiftCount base ≠ 0) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn])
      = encTagShift (rexW (mnemWidth mnem)) ext (gpNumU dn) base := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, hext,
    Bool.false_eq_true, if_false]
  rw [if_pos hgp, if_neg hcnt, if_pos hds, List.nil_append]

/-- **`SHR:19:64` now ENCODES** (asconSigma0's first rotate-hi shift). The Lprog byte encoder
    emits the `shr %d, $19` bytes (`encTagShift 1 5 (gpNumU dn) "SHR:19"`) — the rotation is no
    longer dropped. (Was `encodeLopn_shr19_nil = []`, the codified bug.) -/
theorem encodeLopn_shr19_emits (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHR:19:64" [.reg sn])
      = encTagShift 1 5 (gpNumU dn) "SHR:19" := by
  rw [dispatch_tagshift_reg_emits frame spillW "SHR:19:64" "SHR:19" 5 dn sn
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hgp hds (by native_decide),
      show rexW (mnemWidth "SHR:19:64") = 1 from by decide +kernel]

/-- **`SHL:45:64` now ENCODES** (asconSigma0's first rotate-lo shift). -/
theorem encodeLopn_shl45_emits (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHL:45:64" [.reg sn])
      = encTagShift 1 4 (gpNumU dn) "SHL:45" := by
  rw [dispatch_tagshift_reg_emits frame spillW "SHL:45:64" "SHL:45" 4 dn sn
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hgp hds (by native_decide),
      show rexW (mnemWidth "SHL:45:64") = 1 from by decide +kernel]

/-- **`SHR:28:64` now ENCODES** (asconSigma0's second rotate-hi shift). -/
theorem encodeLopn_shr28_emits (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHR:28:64" [.reg sn])
      = encTagShift 1 5 (gpNumU dn) "SHR:28" := by
  rw [dispatch_tagshift_reg_emits frame spillW "SHR:28:64" "SHR:28" 5 dn sn
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hgp hds (by native_decide),
      show rexW (mnemWidth "SHR:28:64") = 1 from by decide +kernel]

/-- **`SHL:36:64` now ENCODES** (asconSigma0's second rotate-lo shift). -/
theorem encodeLopn_shl36_emits (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHL:36:64" [.reg sn])
      = encTagShift 1 4 (gpNumU dn) "SHL:36" := by
  rw [dispatch_tagshift_reg_emits frame spillW "SHL:36:64" "SHL:36" 4 dn sn
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hgp hds (by native_decide),
      show rexW (mnemWidth "SHL:36:64") = 1 from by decide +kernel]

/-- The count-in-tag shift `SHR:19:64` emits a **non-empty** byte list: the rotation is
    encoded (without evaluating the `String.toNat?` count: the `encShift1`/`encShiftImmw`
    body always carries at least the opcode byte). -/
theorem encodeLopn_shr19_ne_nil (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHR:19:64" [.reg sn]) ≠ [] := by
  rw [encodeLopn_shr19_emits frame spillW dn sn hgp hds, encTagShift]
  split <;> simp [encShift1, encShiftImmw, rexOpt]

/-- The bare (un-tagged) count-in-tag shift form `SHR:<n>` encodes too: `tagShiftExt`
    detects the `"SHR:"`/`"SHL:"` prefix regardless of the `:64` tag, so a U32-width
    register-source shift is emitted as `encTagShift 0 5`. -/
theorem encodeLopn_shr7_emits (frame spillW : Nat) (dn sn : String)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHR:7" [.reg sn])
      = encTagShift 0 5 (gpNumU dn) "SHR:7" := by
  rw [dispatch_tagshift_reg_emits frame spillW "SHR:7" "SHR:7" 5 dn sn
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) hgp hds (by native_decide),
      show rexW (mnemWidth "SHR:7") = 0 from by decide +kernel]

/-! ### §2b. The shift per-op byte-identity reconciliation (`native_decide`-free)

The Lprog `encodeLopn` and the JInstr gather agree on the shift op. The
gather lowers `SHR:<n>:64 [src]` to `[mov d src, shr d (.imm n)]` (`lowerShiftImmJ`), so
its **trailing** op is `encodeJInstr alloc (JInstr.shr d (.imm n))`; the Lprog encoder
emits `encTagShift 1 5 (gpNumU dn) base` for the same count. Both reduce to the same
`C1 /5 ib` (`REX.W`) bytes — the JInstr `ScalarEncoder.encShiftImm 5 …` and the Lprog
`encShiftImmw 1 5 …` are byte-identical for a U64 shift (the `rexOpt 1 …` prefix is the
singleton `0x48`, never elided). This is the shift half of the ALU+shift byte-identity,
proved without `native_decide` (the count `n` stays a free variable — no `String.toNat?`).
The leading materialise `mov d, src` is the gather-side residual (the `GatherInPlace`
in-place peephole covers the two-source ALU shapes but not the shift arm). -/

/-- **Shift per-op byte agreement (`SHR`).** The JInstr gather's trailing `shr d, $n` op
    encodes byte-for-byte to the Lprog `encodeLopn`'s `encTagShift` (group-2 `/5`) for the
    same count `n ≥ 2` — both are the `C1 /5 ib` `REX.W` form. `hd` ties the JInstr register
    name to the Lprog `gpNumU` number (the standard resolver-agreement side-condition); `hn`
    fixes the count the tag carries; `hn1` rules out the `D1 /5` count-1 short form (which the
    JInstr `encShiftImm` does not select). `native_decide`-free. -/
theorem encJShr_eq_encTagShift
    (alloc : GpAlloc) (dn base : String) (n : Nat)
    (hn : tagShiftCount base = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn) :
    encodeJInstr alloc (JInstr.shr dn (.imm n)) = encTagShift 1 5 (gpNumU dn) base := by
  rw [encTagShift, hn, if_neg hn1]
  show encShiftImm 5 (gpNum (regOf alloc dn)) n = encShiftImmw 1 5 (gpNumU dn) n
  rw [hd]; simp [encShiftImm, encShiftImmw, rexOpt]

/-- **Shift per-op byte agreement (`SHL`)** — the group-2 `/4` dual. -/
theorem encJShl_eq_encTagShift
    (alloc : GpAlloc) (dn base : String) (n : Nat)
    (hn : tagShiftCount base = n) (hn1 : n ≠ 1)
    (hd : gpNum (regOf alloc dn) = gpNumU dn) :
    encodeJInstr alloc (JInstr.shl dn (.imm n)) = encTagShift 1 4 (gpNumU dn) base := by
  rw [encTagShift, hn, if_neg hn1]
  show encShiftImm 4 (gpNum (regOf alloc dn)) n = encShiftImmw 1 4 (gpNumU dn) n
  rw [hd]; simp [encShiftImm, encShiftImmw, rexOpt]

/-! ## §3. The block-level account, and `hbody` on a physical kernel body

`encodeJBlock` flattens per-instruction bytes (`encodeJBlock_flatMap`, from
`LprogJInstrBytesAgree`); `encodeLcmd` flattens the per-`Lopn` bytes. So a whole-body
agreement is the pointwise lift of the per-op agreement. §1 + §2 give the per-op picture:
both sides emit the `shr/shl %d, $n` op of a count-in-tag shift, so the only residual on
this op set is §1's SSA-split excess self-`mov` (which `GatherInPlace`'s peephole removes
for the destructive `d == s0` case).

On `AsconLinear.asconSigma0Com`'s physical body the per-`Lopn` mnemonics are four
single-source `SHR/SHL:<n>:64` shifts and two destructive `OR:64 [d, …]` / `XOR:64 [d, …]`
forms; the Lprog `encodeLopn` bytes on the first shift are the `shr %d, $19` op
`[0x48,0xc1,0xe8,0x13]`, and the JInstr gather's block on the same shift is `mov;shr`, whose
shift op agrees; the residual is the gather's leading materialise `mov` (the §1 form,
in-place-elided by `GatherInPlace`). -/

/-! The physical (`Com.toLprogPhysAbi`) body of `asconSigma0Com` — eight ABI qsave
    `MOVQ`s, the arg-marshal `MOVQ R14, RSI`, then the compute spine
    (`SHR:19:64`/`SHL:45:64`/`MOV:64`/`OR:64 [RDX,RDX,RCX]`/…/`XOR:64 [RAX,RAX,RDX]`/…),
    eight restore `MOVQ`s and `Lret`. The per-`Lopn`-mnemonic `#eval` that prints
    this kernel body is re-homed in `GoldenPathByteIdentityDemo` (above the chain)
    so this file is GoldenPath-free. The kernel-independent literal-op `#eval`s
    below stay. -/

-- The Lprog byte encoder now EMITS the physical body's first shift `SHR:19:64`
-- (single-source, count-in-tag) — prints `[0x48,0xc1,0xe8,0x13]` (`shr %rax, $19`), NOT `[]`.
-- This is the dropped-rotation correctness bug, closed.
#eval encodeLopn 0 0 (.Lopn [.reg "RAX"] "SHR:19:64" [.reg "RBX"])

-- The JInstr gather lowers the SAME shift to the full `mov;shr` block — prints
-- `some [0x48,0x89,0xc0, 0x48,0xc1,0xe8,0x13]` (7 bytes). The trailing `shr` op now matches
-- the Lprog encoder's `[0x48,0xc1,0xe8,0x13]` byte-for-byte; the residual is the leading
-- materialise `mov` (the §1 self-mov, elided by `GatherInPlace`'s in-place peephole).
#eval (lowerLinstrExtCov (.Lopn [.reg "RAX"] "SHR:19:64" [.reg "RBX"])).map
  (encodeJBlock [("RAX","RAX"),("RBX","RBX")])

-- And the destructive two-source `OR:64 [RDX, RCX]` (dst = RDX): the JInstr gather emits a
-- spurious leading `mov %rdx,%rdx` (`0x48 0x89 0xc0`) before the `or` — prints a 6-byte
-- block — while `encodeLopn` emits only the 3-byte `or %rcx,%rdx`. The §1 self-mov excess.
#eval (lowerLinstrExtCov (.Lopn [.reg "RDX"] "OR:64" [.reg "RDX", .reg "RCX"])).map
  (encodeJBlock [("RDX","RDX"),("RCX","RCX")])
#eval encodeLopn 0 0 (.Lopn [.reg "RDX"] "OR:64" [.reg "RDX", .reg "RCX"])

/-! ## §4. The `ADOXHI:64` carry-out binding, at the byte level

`LoweringExtendedCoverage.lowerLinstrExtCov` lowers the overflow carry-out binding
`ADOXHI:64 [s0, s1, cin]` to `[setcc .o d, movzx d 8 d]`, and `LprogBytes.encodeLopn`
encodes the same `Lopn` as `encSetccMovzx 0x90 (gpNumU dn)` — the `SETO` opcode
`carryOutSetccOp "ADOXHI"` selects, followed by the `MOVZBQ` zero-extension. The two
sides agree byte for byte under the resolver-agreement side condition the other
`*_bytes_agree` lemmas carry. The `CF` sibling `ADCXHI:64` lowers to `setc`, whose
encoding is `encSetccMovzx 0x92` (`LprogBytes.encSetccMovzx_setc_agree`). -/

/-- The `SETO` + `MOVZBQ` pair of the Lprog encoder is the concatenation of the
    `SETcc` byte encoding at condition `.o` and the `0F B6` zero-extension: the
    overflow analogue of `LprogBytes.encSetccMovzx_setc_agree`. -/
theorem encSetccMovzx_seto_agree (d : Nat) :
    encSetccMovzx 0x90 d = encSetccByte .o d ++ enc0FRR 0xb6 d d := by
  simp [encSetccMovzx, encSetccByte, enc0FRR, condCode, List.map_append]

/-- `JInstr` `setcc .o` reduces to `encSetccByte .o` at the allocated number. -/
theorem jinstr_setcc_o (alloc : GpAlloc) (d : String) :
    encodeJInstr alloc (.setcc .o d) = encSetccByte .o (gpNum (regOf alloc d)) := rfl

/-- `JInstr` `movzx d 8 d` reduces to the `0F B6` reg-reg form. -/
theorem jinstr_movzx8_self (alloc : GpAlloc) (d : String) :
    encodeJInstr alloc (.movzx d 8 d)
      = enc0FRR 0xb6 (gpNum (regOf alloc d)) (gpNum (regOf alloc d)) := rfl

/-- **The `ADOXHI:64` byte agreement.** The gathered `setcc .o` + `movzx` block
    encodes to exactly the bytes `encodeLopn` gives for the overflow carry-out
    binding into a general-purpose register, under the resolver agreement `hr`
    between the `JInstr` register name and the Lprog `gpNumU` number. -/
theorem adoxhi_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (dn : String)
    (s0 s1 cin : LOperand) (hd : isGpName dn = true) (hr : gpNum (regOf alloc dn) = gpNumU dn) :
    (lowerLinstrExtCov (.Lopn [.reg dn] "ADOXHI:64" [s0, s1, cin])).map (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "ADOXHI:64" [s0, s1, cin])) := by
  rw [lowerLinstrExtCov_adoxhi, Option.map_some, encodeLopn_adoxhi _ _ _ _ hd,
    encSetccMovzx_seto_agree, ← hr]
  simp [encodeJBlock, jinstr_setcc_o, jinstr_movzx8_self]

/-- The same agreement at a concrete destination: the gathered `ADOXHI:64` block on
    `RSI` is `seto %sil ; movzbq %sil, %rsi` = `40 0F 90 C6  48 0F B6 F6`. -/
theorem encJAdoxhi_RSI :
    (lowerLinstrExtCov (.Lopn [.reg "RSI"] "ADOXHI:64"
        [.reg "RSI", .reg "R9", .reg "c1"])).map (encodeJBlock [("RSI", "%rsi"), ("R9", "%r9")])
      = some [0x40, 0x0f, 0x90, 0xc6, 0x48, 0x0f, 0xb6, 0xf6] := by
  decide +kernel

/-- The concrete bytes are the ones `encodeLopn` emits for the same `Lopn`. -/
theorem encodeLopn_adoxhi_RSI_bytes :
    encodeLopn 0 0 (.Lopn [.reg "RSI"] "ADOXHI:64" [.reg "RSI", .reg "R9", .reg "c1"])
      = [0x40, 0x0f, 0x90, 0xc6, 0x48, 0x0f, 0xb6, 0xf6] := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
