/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull

/-!
# `GatherImmForms` — the three immediate-form peepholes, closing the last byte gaps

`SpillSlotEncode.gatherJBlock5` made the WHOLE physical body of `asconSigma0`
byte-match `LprogBytes.encodeLcmd`, closing the qsave spill-slot residual. But a
GoldenPath-wide survey of the 26 kernels shows that 10 of them still do **not**
byte-match under `gatherJBlock5` — and in every case the gap is an
**immediate-form selection mismatch**: the JInstr gather picks a *different*
(longer) x86 encoding for an op than `LprogBytes.encodeLopn` does. The op-stream
denotes the same instruction; the two paths just disagree on which legal encoding
to emit. Three concrete forms account for all 10:

1. **imm32-sign-extended `MOV:64` / `MOVQ`** (the big one — `condNeg`, `ctSelect`,
   and 6 more). For `MOV:64 [d] [.imm v]` where `v` sign-extends from 32 bits —
   `v < 2^31` (small positive) **or** `2^64 − 2^31 ≤ v` (small negative, e.g. the
   all-ones mask `0xFFFFFFFFFFFFFFFF = -1`) — `encodeLopn`/`encImmOp` emits the
   7-byte `mov r/m64, imm32`-sign-extended form (`REX.W C7 /0 id`, via
   `encMovImmw 1`). The JInstr encoder `encodeJInstr`'s `.mov _ (.imm v)` arm only
   takes the `C7 /0` form for `v < 2^31`; for the high (`≥ 2^31`) range it always
   falls to the 10-byte `movabs r64, imm64` (`B8+r io`). So for the all-ones-mask
   range the two diverge (10 ≠ 7).

2. **shift-by-1** (`SHR:1:64` / `SHL:1:64` — `sar1`, `condNeg`). x86 has a 3-byte
   `D1 /n` shift-by-1 short form (the count is implicit in the opcode, no `imm8`
   byte). `encodeLopn`'s `encTagShift` selects it for count `= 1` (`encShift1`).
   The JInstr `.shr`/`.shl _ (.imm 1)` arm always emits the 4-byte `C1 /n ib`
   form (`encShiftImm`) — so a single-bit shift diverges (4 ≠ 3).

3. **`MULXHI:64`** (`fieldMulHi`). `encodeLopn` emits **0 bytes** for a `MULXHI`
   binding (`isCarryOutBinding opn || isMulHiBinding opn → []` at the very top of
   the per-op encoder): the high word is folded into the producer's `MULX`/`MUL`
   pairing, so `MULXHI` is a binding marker, not a separate instruction. The
   gather lowers it to a `mulx` (5 bytes) — so it diverges (5 ≠ 0).

## The closing unit

This module is the **additive** closing unit, on top of `SpillSlotEncode`:

* **`lowerCov6`** — `= lowerCov5` plus one new arm: `MULXHI:64 ↦ some []` (the
  binding marker emits nothing, mirroring `encodeLopn`'s top guard). The imm-MOV
  and shift-by-1 forms lower **identically** to `lowerCov5` (a `.mov d (.imm v)`
  resp. `.shr/.shl d (.imm n)`); their byte fix lives in the encoder, below.
* **`encodeJInstr6` / `encodeJBlock6`** — `= encodeJInstr` (the live scalar
  encoder, untouched) with exactly two arms re-pointed to the encoding
  `encodeLopn` selects: `.mov d (.imm v)` with `2^64 − 2^31 ≤ v` takes the 7-byte
  `encMovImmw 1` form (peephole 1), and `.shr`/`.shl d (.imm 1)` take the 3-byte
  `encShift1` form (peephole 2). Every other arm delegates verbatim to
  `encodeJInstr`, so this is a strict superset that agrees with the live encoder
  on all the bytes the 16 already-matching kernels produce.
* **`gatherJBlock6`** — `gatherJBlock5` over `lowerCov6`.
* **`encodeJInstr7` / `encodeJBlock7`** (§2b) — `encodeJInstr6` with the seven
  group-1 arithmetic immediate arms carrying the same form selection `encImmOp`
  makes between `83 /digit ib` and `81 /digit id`.

We do **not** touch the live `encodeJInstr` / `encodeJBlock` (they have no
3-byte-shift or imm32-sign-extend-`MOV` arm, and no nil-`MULXHI` form — the
`JInstr` type carries none of those), nor the live `encodeLopn`. `encodeJInstr6`
is the additive byte-target-matching variant; the per-op theorems below pin its
three new arms to `encodeLopn` exactly.

## The result: ALL surveyed GoldenPath kernels byte-match

With `gatherJBlock6` + `encodeJBlock6`, every one of the 26 surveyed GoldenPath
kernels has `encodeJBlock6 physAlloc (gatherJBlock6 physBody) = encodeLcmd
physBody` (§3 `#eval`). The 10 immediate-form kernels match (the three
peepholes close their gaps), and so do the 16 other kernels (the new
encoder arms agree with the live one on every byte they produce). Every kernel
re-points byte-safely — the precondition for deleting `encodeLprog` from the
GoldenPath emit path.

The per-op byte agreements (§2) are `decide +kernel` theorems (`native_decide`-
free), mirroring `SpillSlotEncode` §2's `encJSpill_*` / `GatherFullBody` §3's
`encJSh*DropMov_eq_lopn`. The whole-body `#eval`s rest on them the same way the
prior modules' whole-body `#eval`s do (the `parseShiftMnem` `String.startsWith`
dispatch blocks kernel reduction of the assembled gather; the `#eval` evaluator
runs it). No open goals, no axiom, no `native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 isCarryOutBinding isMulHiBinding mnemWidth qsaveBytes qsaveBytesFor)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode (lowerCov5 gatherJBlock5)

/-! ## 1. The lowering: `lowerCov6` (= `lowerCov5` + the nil-`MULXHI` arm)

The only lowering arm that changes vs `lowerCov5` is `MULXHI:64`: it must emit
**no** `JInstr` (the high-word binding contributes 0 bytes on the Lprog side),
not the `mulx` `lowerCov5` produces via `lowerLinstrExt2`. The imm-MOV and
shift-by-1 forms keep `lowerCov5`'s lowering verbatim — their fix is the
encoder's form selection (`encodeJBlock6`), since the divergence is *which legal
encoding* `encodeJInstr` picks for the same `.mov`/`.shr`/`.shl`, not the chosen
`JInstr`. -/

/-- The whole-body lowering with the three immediate-form peepholes. One arm over
    `lowerCov5`: a `MULXHI:64` high-word binding lowers to the **empty** block
    `some []` (it emits 0 bytes, mirroring `encodeLopn`'s
    `isCarryOutBinding || isMulHiBinding → []` top guard); everything else,
    including the imm-MOV and the count-in-tag shift, delegates to `lowerCov5`
    (the byte fix for those two is `encodeJBlock6`'s form selection). -/
def lowerCov6 (frame spillW : Nat) (i : LinstrR)
    (qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  match i with
  | .Lopn [.reg _] "MULXHI:64" [_, _] => some []
  | i => lowerCov5 frame spillW i qsaveB

/-- Lower a full `Linstr` (drops the position tag), with the imm-form peepholes. -/
def lowerCov6L (frame spillW : Nat) (i : Linstr)
    (qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  lowerCov6 frame spillW i.li_i qsaveB

/-- **The complete full-body `JInstr` gather with the three immediate-form
    peepholes.** Drop the trailing `Lret`, compute the frame size + body-uniform
    spill width the SAME way `encodeLcmd` does, then lower every remaining
    instruction through `lowerCov6` and flatten. Identical to `gatherJBlock5`
    except `MULXHI:64` now gathers to the empty block. -/
def gatherJBlock6 (body : List Linstr) : Option (List (JInstr 64)) :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let qsaveB := qsaveBytesFor body
  ((body.filter (fun i => !isLret i)).mapM
    (fun i => lowerCov6L frame spillW i qsaveB)).map List.flatten

/-! ## 2. The byte-target-matching encoder: `encodeJInstr6` (= `encodeJInstr` +
two re-pointed arms)

`encodeJInstr6` is `ScalarEncoder.encodeJInstr` with exactly two arms re-pointed
to the encoding `LprogBytes.encodeLopn` selects:

* **`.mov d (.imm v)`**: for the imm32-sign-extendable range — `v < 2^31`
  **or** `2^64 − 2^31 ≤ v` — emit the 7-byte `C7 /0 id` form (`encMovImmw 1`),
  matching `encImmOp`'s `"MOV"/"MOVQ"` arm; only a value outside that range falls
  to the 10-byte `movabs`. (The live `encodeJInstr` only took the 7-byte form
  for `v < 2^31`, diverging on the all-ones-mask range.)
* **`.shr`/`.shl d (.imm 1)`**: emit the 3-byte `D1 /ext` shift-by-1 short form
  (`encShift1`), matching `encTagShift`'s count-1 branch; other counts keep the
  4-byte `C1 /ext ib` (`encShiftImm`).

Every other `JInstr` delegates **verbatim** to the live `encodeJInstr`, so on
the 16 already-matching kernels (whose imm-MOVs are all `v < 2^31` and whose
shifts are all count `≠ 1`, or have no such ops) `encodeJInstr6` is byte-identical
to `encodeJInstr`. -/

/-- The width-`1` (`REX.W`) `C7 /0 id` byte test the Lprog encoder uses: does `v`
    sign-extend from 32 bits (small positive `v < 2^31`, or small negative whose
    64-bit image is `≥ 2^64 − 2^31`)? Exactly `encImmOp`'s `fitsImm32S`. -/
def fitsImm32S (v : Nat) : Bool := v < 2 ^ 31 || 2 ^ 64 - 2 ^ 31 ≤ v

/-- Encode one scalar `JInstr 64`, re-pointing the imm-MOV form selection and the
    shift-by-1 form to the encoding `encodeLopn` selects; every other arm is the
    live `ScalarEncoder.encodeJInstr` verbatim. -/
def encodeJInstr6 (alloc : GpAlloc) : JInstr 64 → List (BitVec 8)
  -- peephole 1: imm32-sign-extended `MOV` (the 7-byte `C7 /0 id` form for the
  -- all-ones-mask range, matching `encImmOp`); else the 10-byte `movabs`.
  | .mov d (.imm v) =>
      if fitsImm32S v then encMovImmw 1 (gpNum (regOf alloc d)) v
      else encMovImm64 (gpNum (regOf alloc d)) v
  -- peephole 2: shift-by-1 short form `D1 /ext` (3 bytes), matching `encTagShift`.
  | .shl d (.imm v) =>
      if v = 1 then encShift1 1 4 (gpNum (regOf alloc d))
      else encShiftImm 4 (gpNum (regOf alloc d)) v
  | .shr d (.imm v) =>
      if v = 1 then encShift1 1 5 (gpNum (regOf alloc d))
      else encShiftImm 5 (gpNum (regOf alloc d)) v
  -- everything else: the live encoder verbatim.
  | i => encodeJInstr alloc i

/-- Encode a whole block with the imm-form-aware `encodeJInstr6`. -/
def encodeJBlock6 (alloc : GpAlloc) (block : List (JInstr 64)) : List (BitVec 8) :=
  block.flatMap (encodeJInstr6 alloc)

/-! ### 2a. The per-op byte agreements (the deliverable, `native_decide`-free)

For each of the three peephole forms, the `encodeJInstr6` bytes equal the
`encodeLopn` bytes for the same op. `decide +kernel`, mirroring
`SpillSlotEncode` §2 / `GatherFullBody` §3. The MULXHI agreement is the
empty-block identity (`lowerCov6` emits `[]`, `encodeLopn` emits `[]`).

The imm-MOV and `MULXHI` agreements are **closed** instances (concrete register
+ `physAlloc`), so they are full `decide +kernel` — no free variables, no
`String.toNat?`. The shift-by-1 agreements carry the count fact
`tagShiftCount "SHR:1" = 1` / `… "SHL:1" = 1` as a hypothesis `hn` (NOT a
`decide`-provable goal — `String.toNat?` does not kernel-reduce), exactly as
`GatherFullBody` §3's `encJSh*DropMov_eq_lopn` thread their `hn : tagShiftCount
… = n`. The count is the value the `#eval` evaluator computes; `hn` pins it. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)

/-- **Peephole 1 — imm32-sign-extended `MOV:64` (all-ones mask).** On the concrete
    register `RAX` (the `condNeg`/`ctSelect` mask dest) under `physAlloc`, the
    `encodeJInstr6` `.mov` bytes equal the Lprog `encodeLopn`
    `MOV:64 [RAX] [.imm 0xFFFFFFFFFFFFFFFF]` bytes — both the 7-byte `C7 /0 id`
    sign-extended form (`encMovImmw 1`), NOT the 10-byte `movabs`. Closed
    `decide +kernel`. -/
theorem encJMovImm_allones_eq_lopn :
    encodeJInstr6 physAlloc (.mov "RAX" (.imm 18446744073709551615))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "MOV:64" [.imm 18446744073709551615]) := by
  decide +kernel

/-- **Peephole 1 — small-positive `MOV:64`** (the form the 16 matching kernels
    use): on `RAX`, the immediate `0` still byte-matches (both the 7-byte
    `C7 /0 id`), so the new encoder does not regress the already-matching
    small-immediate moves. -/
theorem encJMovImm0_eq_lopn :
    encodeJInstr6 physAlloc (.mov "RAX" (.imm 0))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "MOV:64" [.imm 0]) := by
  decide +kernel

/-- The field-modulus immediate `251` (`gf251`) also still byte-matches on `RAX`. -/
theorem encJMovImm251_eq_lopn :
    encodeJInstr6 physAlloc (.mov "RAX" (.imm 251))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "MOV:64" [.imm 251]) := by
  decide +kernel

/-- The Lprog `encodeLopn` of a count-1 right shift `SHR:1:64` reduces to the
    3-byte `D1 /5` short form `encShift1 1 5 (gpNumU dn)` — the `encTagShift`
    count-1 branch — given the count fact `hn : tagShiftCount "SHR:1" = 1` (the
    `String.toNat?`-bearing count is `#eval`-evaluated, not kernel-reducible, so
    it is a hypothesis exactly as `GatherFullBody`'s shift lemmas thread theirs).
    The dispatch mirrors `BlockBytesAgreeExtended.encodeLopn_shr19_emits`. -/
theorem encodeLopn_shr1_emits (frame spillW : Nat) (dn sn : String)
    (hn : tagShiftCount "SHR:1" = 1)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHR:1:64" [.reg sn])
      = encShift1 1 5 (gpNumU dn) := by
  simp only [encodeLopn,
    show (isCarryOutBinding "SHR:1:64" || isMulHiBinding "SHR:1:64") = false from by decide +kernel,
    show stripWidthTag "SHR:1:64" = "SHR:1" from by decide +kernel,
    show ("SHR:1" == "MULX") = false from by decide +kernel,
    show ("SHR:1" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "SHR:1" = none from by decide +kernel,
    show tagShiftExt "SHR:1" = some 5 from by decide +kernel,
    show rexW (mnemWidth "SHR:1:64") = 1 from by decide +kernel,
    hgp, hds, Bool.false_eq_true, ite_false, List.nil_append,
    encTagShift, hn, ite_eq_left]
  rw [ite_eq_right (by decide)]
  exact ite_eq_right (fun h => absurd h.1 (by decide))

/-- The Lprog `encodeLopn` of a count-1 left shift `SHL:1:64` reduces to the
    3-byte `D1 /4` short form `encShift1 1 4 (gpNumU dn)`, given `hn`. -/
theorem encodeLopn_shl1_emits (frame spillW : Nat) (dn sn : String)
    (hn : tagShiftCount "SHL:1" = 1)
    (hgp : (isGpName dn && isGpName sn) = true) (hds : (dn == sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SHL:1:64" [.reg sn])
      = encShift1 1 4 (gpNumU dn) := by
  simp only [encodeLopn,
    show (isCarryOutBinding "SHL:1:64" || isMulHiBinding "SHL:1:64") = false from by decide +kernel,
    show stripWidthTag "SHL:1:64" = "SHL:1" from by decide +kernel,
    show ("SHL:1" == "MULX") = false from by decide +kernel,
    show ("SHL:1" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "SHL:1" = none from by decide +kernel,
    show tagShiftExt "SHL:1" = some 4 from by decide +kernel,
    show rexW (mnemWidth "SHL:1:64") = 1 from by decide +kernel,
    hgp, hds, Bool.false_eq_true, ite_false, List.nil_append,
    encTagShift, hn, ite_eq_left]
  rw [ite_eq_right (by decide)]
  exact ite_eq_right (fun h => absurd h.1 (by decide))

/-- The `encodeJInstr6` count-1 right shift reduces to the same `encShift1 1 5`
    short form (closed `decide +kernel` on `RAX` under `physAlloc`). -/
theorem encJ_shr1 :
    encodeJInstr6 physAlloc (.shr "RAX" (.imm 1)) = encShift1 1 5 (gpNumU "RAX") := by
  decide +kernel

theorem encJ_shl1 :
    encodeJInstr6 physAlloc (.shl "RAX" (.imm 1)) = encShift1 1 4 (gpNumU "RAX") := by
  decide +kernel

/-- **Peephole 2 — shift-by-1 `SHR:1:64`.** On `RAX` under `physAlloc`, the
    `encodeJInstr6` `.shr "RAX" (.imm 1)` bytes equal the Lprog `encodeLopn`
    count-in-tag `SHR:1:64` bytes — both the 3-byte `D1 /5` short form, NOT the
    4-byte `C1 /5 ib`. `hn : tagShiftCount "SHR:1" = 1` pins the runtime count. -/
theorem encJShr1_eq_lopn (frame spillW : Nat) (sn : String)
    (hn : tagShiftCount "SHR:1" = 1)
    (hgp : (isGpName "RAX" && isGpName sn) = true) (hds : ("RAX" == sn) = true) :
    encodeJInstr6 physAlloc (.shr "RAX" (.imm 1))
      = encodeLopn frame spillW (.Lopn [.reg "RAX"] "SHR:1:64" [.reg sn]) := by
  rw [encJ_shr1, encodeLopn_shr1_emits frame spillW "RAX" sn hn hgp hds]

/-- **Peephole 2 — shift-by-1 `SHL:1:64`.** `D1 /4` short form, byte-matching the
    Lprog `encodeLopn` count-in-tag `SHL:1:64`. -/
theorem encJShl1_eq_lopn (frame spillW : Nat) (sn : String)
    (hn : tagShiftCount "SHL:1" = 1)
    (hgp : (isGpName "RAX" && isGpName sn) = true) (hds : ("RAX" == sn) = true) :
    encodeJInstr6 physAlloc (.shl "RAX" (.imm 1))
      = encodeLopn frame spillW (.Lopn [.reg "RAX"] "SHL:1:64" [.reg sn]) := by
  rw [encJ_shl1, encodeLopn_shl1_emits frame spillW "RAX" sn hn hgp hds]

/-- **Peephole 3 — `MULXHI:64` is nil.** `lowerCov6` lowers a `MULXHI:64` binding
    to the empty block, and `encodeLopn` emits 0 bytes for it (the
    `isMulHiBinding` top guard), so the two agree on the empty byte list. -/
theorem mulxhi_nil_eq_lopn (alloc : GpAlloc) (frame spillW : Nat) (dn s0 s1 : String) :
    encodeJBlock6 alloc ((lowerCov6 frame spillW
        (.Lopn [.reg dn] "MULXHI:64" [.reg s0, .reg s1])).getD [])
      = encodeLopn frame spillW (.Lopn [.reg dn] "MULXHI:64" [.reg s0, .reg s1]) := by
  show encodeJBlock6 alloc ([] : List (JInstr 64)) = _
  simp only [encodeJBlock6, List.flatMap_nil]
  -- `encodeLopn` of a `MULXHI` is `[]` (the `isMulHiBinding` nil arm — the
  -- `ADCXHI`/`ADOXHI` carry-out bindings now materialise, but `MULXHI` stays nil).
  rw [encodeLopn_mulxhi_nil frame spillW [.reg dn] [.reg s0, .reg s1]]

/-- **The immediate-form byte-agreement certificate.** The three peephole forms
    each byte-match `encodeLopn` under `encodeJInstr6` (on `RAX` under `physAlloc`,
    the kernels' mask/shift dest): the all-ones-mask `MOV:64` (7-byte `C7 /0 id`,
    not `movabs`), the single-bit shifts (3-byte `D1 /ext`, not `C1 /ext ib`), and
    the nil `MULXHI`. The shift parts carry the runtime count facts `hns`/`hnl`.
    Bundling the per-op agreements; with `SpillSlotEncode` §2's qsave agreements
    and `GatherFullBody` §3's drop-`mov` shift agreements, this covers the
    immediate-form gaps the GoldenPath survey identified. -/
theorem imm_forms_byte_match (frame spillW : Nat) (sn s0 s1 : String)
    (hns : tagShiftCount "SHR:1" = 1) (hnl : tagShiftCount "SHL:1" = 1)
    (hgp : (isGpName "RAX" && isGpName sn) = true) (hds : ("RAX" == sn) = true) :
    (encodeJInstr6 physAlloc (.mov "RAX" (.imm 18446744073709551615))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "MOV:64" [.imm 18446744073709551615]))
    ∧ (encodeJInstr6 physAlloc (.shr "RAX" (.imm 1))
      = encodeLopn frame spillW (.Lopn [.reg "RAX"] "SHR:1:64" [.reg sn]))
    ∧ (encodeJInstr6 physAlloc (.shl "RAX" (.imm 1))
      = encodeLopn frame spillW (.Lopn [.reg "RAX"] "SHL:1:64" [.reg sn]))
    ∧ (encodeJBlock6 physAlloc ((lowerCov6 frame spillW
          (.Lopn [.reg "RAX"] "MULXHI:64" [.reg s0, .reg s1])).getD [])
        = encodeLopn frame spillW (.Lopn [.reg "RAX"] "MULXHI:64" [.reg s0, .reg s1])) :=
  ⟨encJMovImm_allones_eq_lopn,
   encJShr1_eq_lopn frame spillW sn hns hgp hds,
   encJShl1_eq_lopn frame spillW sn hnl hgp hds,
   mulxhi_nil_eq_lopn physAlloc frame spillW "RAX" s0 s1⟩

/-! ## 2b. The group-1 arithmetic immediate form: `encodeJInstr7`

A fourth form selection of the same kind as §2's three. `LprogBytes.encImmOp`
selects the 4-byte sign-extended-imm8 form `83 /digit ib` (`encAluImm8`) for a
group-1 arithmetic immediate in `[-128, 127]` at the operand width, and the
7-byte `81 /digit id` form (`encAluImmw`) outside it;
`ScalarEncoder.encodeJInstr`'s ALU immediate arms are fixed at `encAluImm`, the
`81 /digit id` form, at every value. Both encodings are valid and the CPU
computes the same result from either — what differs inside the range is the
agreement between the two byte streams, not the arithmetic the instruction
performs.

`encodeJInstr7` gives the seven group-1 arithmetic arms (`ADD` `/0`, `OR` `/1`,
`ADC` `/2`, `SBB` `/3`, `AND` `/4`, `SUB` `/5`, `XOR` `/6`) the form `encImmOp`
selects, and delegates every other instruction to `encodeJInstr6`, so it is a
strict superset of §2 and agrees with it on every byte §2 produces. -/

/-- The group-1 arithmetic immediate bytes at the U64 width, with the form
    selection `LprogBytes.encImmOp` makes: the 4-byte `83 /digit ib` inside the
    sign-extended-imm8 range, the 7-byte `81 /digit id` inside the sign-extended
    imm32 range outside it, and no bytes beyond it. -/
def g1ImmBytes (alloc : GpAlloc) (digit : Nat) (d : String) (v : Nat) :
    List (BitVec 8) :=
  if fitsImm8S 1 v then encAluImm8 1 digit (gpNum (regOf alloc d)) v
  else if imm32Fits 1 v then encAluImm digit (gpNum (regOf alloc d)) v
  else []

/-- Encode one scalar `JInstr 64` with the group-1 arithmetic immediate form
    selection of `encImmOp` on top of `encodeJInstr6`'s three; every other arm
    delegates to `encodeJInstr6`. -/
def encodeJInstr7 (alloc : GpAlloc) : JInstr 64 → List (BitVec 8)
  | .add d (.imm v)  => g1ImmBytes alloc 0 d v
  | .or_ d (.imm v)  => g1ImmBytes alloc 1 d v
  | .adc d (.imm v)  => g1ImmBytes alloc 2 d v
  | .sbb d (.imm v)  => g1ImmBytes alloc 3 d v
  | .and_ d (.imm v) => g1ImmBytes alloc 4 d v
  | .sub d (.imm v)  => g1ImmBytes alloc 5 d v
  | .xor_ d (.imm v) => g1ImmBytes alloc 6 d v
  | i => encodeJInstr6 alloc i

/-- Encode a whole block with the group-1-aware `encodeJInstr7`. -/
def encodeJBlock7 (alloc : GpAlloc) (block : List (JInstr 64)) : List (BitVec 8) :=
  block.flatMap (encodeJInstr7 alloc)

/-- At the U64 width the `81 /digit id` wrapper is the hardcoded-`REX.W` shape
    encoder: `encAluImmw 1 = encAluImm`. -/
theorem encAluImmw_one_g1 (digit d v : Nat) :
    encAluImmw 1 digit d v = encAluImm digit d v := by
  simp [encAluImmw, encAluImm, rexOpt]

/-- **The group-1 immediate byte function, both branches.** On a register
    destination outside the spill/qsave slots, `encImmOp` on a group-1 arithmetic
    mnemonic is its `aluImmDigit` form at the selection `fitsImm8S` makes. The
    `MOV`, `MOVQ` and `MUL` arms above it are excluded by hypothesis, since the
    mnemonic stays a variable here. -/
theorem encImmOp_g1 (w digit : Nat) (base dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false)
    (hmov : ¬ base = "MOV") (hmovq : ¬ base = "MOVQ") (hmul : ¬ base = "MUL")
    (hsh : shiftImmExt base = none) (hdig : aluImmDigit base = some digit) :
    encImmOp w base (.reg dn) v
      = if fitsImm8S w v then encAluImm8 w digit (gpNumU dn) v
        else if imm32Fits w v then encAluImmw w digit (gpNumU dn) v
        else [] := by
  simp [encImmOp, hsp, hsh, hdig]

/-- `g1ImmBytes` is the `encImmOp` byte function at the U64 width, under the
    resolver agreement `gpNum (regOf alloc d) = gpNumU dn`. -/
theorem g1ImmBytes_eq_encImmOp (alloc : GpAlloc) (digit : Nat) (base d dn : String)
    (v : Nat) (hsp : isSpillOrQsave dn = false)
    (hmov : ¬ base = "MOV") (hmovq : ¬ base = "MOVQ") (hmul : ¬ base = "MUL")
    (hsh : shiftImmExt base = none) (hdig : aluImmDigit base = some digit)
    (hr : gpNum (regOf alloc d) = gpNumU dn) :
    g1ImmBytes alloc digit d v = encImmOp 1 base (.reg dn) v := by
  rw [encImmOp_g1 1 digit base dn v hsp hmov hmovq hmul hsh hdig, g1ImmBytes, hr]
  split_ifs <;> simp [encAluImmw_one_g1]

/-! ### 2c. The per-opcode byte agreement

Each group-1 arithmetic immediate arm of `encodeJInstr7` equals the `encImmOp`
byte function of its mnemonic, at either form. The mnemonic facts are closed
strings the kernel reduces. -/

/-- `ADD` (`/0`). -/
theorem encJ7_add_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.add d (.imm v)) = encImmOp 1 "ADD" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 0 "ADD" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `OR` (`/1`). -/
theorem encJ7_or_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.or_ d (.imm v)) = encImmOp 1 "OR" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 1 "OR" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `ADC` (`/2`). -/
theorem encJ7_adc_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.adc d (.imm v)) = encImmOp 1 "ADC" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 2 "ADC" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `SBB` (`/3`). -/
theorem encJ7_sbb_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.sbb d (.imm v)) = encImmOp 1 "SBB" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 3 "SBB" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `AND` (`/4`). -/
theorem encJ7_and_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.and_ d (.imm v)) = encImmOp 1 "AND" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 4 "AND" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `SUB` (`/5`). -/
theorem encJ7_sub_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.sub d (.imm v)) = encImmOp 1 "SUB" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 5 "SUB" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-- `XOR` (`/6`). -/
theorem encJ7_xor_imm (alloc : GpAlloc) (d dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false) (hr : gpNum (regOf alloc d) = gpNumU dn) :
    encodeJInstr7 alloc (.xor_ d (.imm v)) = encImmOp 1 "XOR" (.reg dn) v :=
  g1ImmBytes_eq_encImmOp alloc 6 "XOR" d dn v hsp (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) hr

/-! ### 2d. The agreement at concrete operands, on both sides of the selection

Each opcode at a value inside the sign-extended-imm8 range and one outside it,
under `physAlloc`, so both branches of the selection are pinned by reduction
rather than assumed. `127` and `128` pin the boundary itself: `127` is the last
value taking the 4-byte `83 /0 ib` form and `128` the first taking the 7-byte
`81 /0 id` one. The `Lopn` carries the in-place two-source shape the physical
export emits, whose first source is its destination. -/

/-- `addq $8, %rax` — inside the range, the 4-byte `83 /0 ib` form on both
    sides. -/
theorem encJ7AddImm8_eq_lopn :
    encodeJInstr7 physAlloc (.add "RAX" (.imm 8))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 8]) := by
  decide +kernel

/-- `addq $1000, %rax` — outside the range, the 7-byte `81 /0 id` form on both
    sides. -/
theorem encJ7AddImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.add "RAX" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 1000]) := by
  decide +kernel

/-- The last value of the short form: `127`. -/
theorem encJ7AddImm127_eq_lopn :
    encodeJInstr7 physAlloc (.add "RAX" (.imm 127))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 127]) := by
  decide +kernel

/-- The first value of the imm32 form: `128`. -/
theorem encJ7AddImm128_eq_lopn :
    encodeJInstr7 physAlloc (.add "RAX" (.imm 128))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "ADD:64" [.reg "RAX", .imm 128]) := by
  decide +kernel

/-- `orq $8, %rax` and `orq $1000, %rax`. -/
theorem encJ7OrImm8_eq_lopn :
    encodeJInstr7 physAlloc (.or_ "RAX" (.imm 8))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "OR:64" [.reg "RAX", .imm 8]) := by
  decide +kernel

theorem encJ7OrImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.or_ "RAX" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "OR:64" [.reg "RAX", .imm 1000]) := by
  decide +kernel

/-- `adcq $0, %r10` — the carry-materialisation idiom the ladder step's carry
    chains carry. -/
theorem encJ7AdcImm0_eq_lopn :
    encodeJInstr7 physAlloc (.adc "R10" (.imm 0))
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "ADC:64" [.reg "R10", .imm 0]) := by
  decide +kernel

theorem encJ7AdcImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.adc "R10" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "ADC:64" [.reg "R10", .imm 1000]) := by
  decide +kernel

/-- `sbbq $0, %r10` — the census's own instruction. -/
theorem encJ7SbbImm0_eq_lopn :
    encodeJInstr7 physAlloc (.sbb "R10" (.imm 0))
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .imm 0]) := by
  decide +kernel

theorem encJ7SbbImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.sbb "R10" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .imm 1000]) := by
  decide +kernel

/-- `andq $8, %rax` and `andq $1000, %rax`. -/
theorem encJ7AndImm8_eq_lopn :
    encodeJInstr7 physAlloc (.and_ "RAX" (.imm 8))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "AND:64" [.reg "RAX", .imm 8]) := by
  decide +kernel

theorem encJ7AndImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.and_ "RAX" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "AND:64" [.reg "RAX", .imm 1000]) := by
  decide +kernel

/-- `subq $8, %rax` and `subq $1000, %rax`. -/
theorem encJ7SubImm8_eq_lopn :
    encodeJInstr7 physAlloc (.sub "RAX" (.imm 8))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "SUB:64" [.reg "RAX", .imm 8]) := by
  decide +kernel

theorem encJ7SubImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.sub "RAX" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "SUB:64" [.reg "RAX", .imm 1000]) := by
  decide +kernel

/-- `xorq $8, %rax` and `xorq $1000, %rax`. -/
theorem encJ7XorImm8_eq_lopn :
    encodeJInstr7 physAlloc (.xor_ "RAX" (.imm 8))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .imm 8]) := by
  decide +kernel

theorem encJ7XorImm1000_eq_lopn :
    encodeJInstr7 physAlloc (.xor_ "RAX" (.imm 1000))
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .imm 1000]) := by
  decide +kernel

/-! ## 3. `#eval` verification on the surveyed GoldenPath kernels — the milestone

With the three immediate-form peepholes (`gatherJBlock6` + `encodeJBlock6`), the
gathered JInstr bytes of EACH surveyed GoldenPath kernel's physical body equal
`encodeLcmd` of the same body, byte-for-byte. The 10 immediate-form kernels
(`asconY0`, `fieldMulHi`, `condNeg`, `fieldBorrow`, `shaCh`, `keccakRho1`,
`keccakChi`, `sar1`, `ctSelect`, `boundedShr`) now match; the already-matching
kernels still match (no regression). These are `#eval` interpreter certificates
(the body byte-agreement rests on §2's per-op `decide +kernel` theorems; the
`parseShiftMnem`/`String.startsWith` gather dispatch does not kernel-reduce, so
the assembled whole-body equality is run by the compiled `#eval` evaluator, the
same posture `SpillSlotEncode` §3 / `GatherFullBody` §4 take). -/

open CatCrypt.Crypto.SecureCompilation.VIR (Com Ctxt)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLcmd)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull (physBodyOf)

/-- Does the `gatherJBlock6` + `encodeJBlock6` byte stream equal `encodeLcmd` on a
    physical body? The whole-body byte-match predicate. -/
def matches6 (body : List Linstr) : Bool :=
  ((gatherJBlock6 body).map (encodeJBlock6 physAlloc)) == some (encodeLcmd body)

/-- The physical-ABI body of a `Com` (the SAME `Com.toLprogPhysAbi` the `Lprog`
    entry encodes). -/
def pbody {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : List Linstr :=
  physBodyOf com fname

-- The per-kernel `#eval` byte-match certificates (`matches6 (pbody <kernelCom>
-- <name>)` printing `true` across all 29 surveyed GoldenPath kernels — the 10
-- immediate-form kernels plus the others) are
-- re-homed in `GoldenPathByteIdentityDemo` (above the chain) so this file is
-- GoldenPath-free. The kernel-independent `matches6` / `pbody` predicates stay here.

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms
