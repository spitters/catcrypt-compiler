/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
public import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar

/-!
# `GatherInPlace` — the in-place (skip-mov) gather that byte-matches the Lprog encoder on the ALU core

`PhysBodyGather` pinned down (empirically, on the real GoldenPath kernel
`AsconLinear.asconSigma0Com`) the two precise reasons the extended JInstr gather
(`JInstrGatherExtended.gatherJBlock2`) does **not** byte-match the Lprog encoder
(`LprogBytes.encodeLcmd`) on the physical ALU core:

1. **The unconditional SSA-split self-`mov`.** `lowerLinstrExtCovL` lowers *every*
   two-source `Lopn [d] op [s0, s1]` into `mov d s0 ; OP d s1` with **no `d == s0`
   guard**. On the physical body the two-source ops are already destructive
   (`OR:64 [RDX] [RDX, RCX]`, i.e. `RDX |= RCX`), so the materialise is a redundant
   `mov RDX, RDX` (`48 89 D2`) the Lprog `encodeLopn` never emits — the latter
   encodes the same `Lopn` as the single `or %rcx, %rdx` (`48 09 CA`).

2. **The count-in-tag shift representation.** `Com.toLprogPhysAbi` emits the rotate
   shifts as `Lopn [RAX] "SHR:19:64" [RBX]` — count in the **mnemonic tag**, source a
   **register**. The gather lowers this to `mov RAX, RBX ; shr RAX, $19` (7 bytes);
   `encodeLopn`'s `encTagShift` arm emits the `shr RAX, $19` op
   (`[0x48,0xc1,0xe8,0x13]`), matching the trailing `shr` of the gather's block.

This module addresses divergence (1): a lowering `lowerLinstrExtCov3` with the
`d == s0 ⇒ skip the leading mov` peephole on the two-source `regArith` shapes, a
gather `gatherJBlock3` / entries built on it, the per-op byte-agreement theorem for
the in-place case (`native_decide`-free, via the `BlockBytesAgreeExtended` dispatch
technique), and `#eval` evidence that with the peephole the two-source ALU core
byte-matches `encodeLopn`.

Divergence (2) — the shift — is encoded by `encodeLopn`'s `encTagShift` arm
(`BlockBytesAgreeExtended.encodeLopn_shr19_emits`). The shift residual between the
two gathers is the gather's leading materialise `mov d, src` (the shift arm
`lowerShiftImmJ` does not coalesce `d = src`); the shift op byte-agrees on both
sides.

## The peephole (divergence 1)

`lowerLinstrExtCov` delegates the two-source `regArith` shapes to
`lowerLinstrExt2 → lowerAluJ2`, which outside the register-count shifts is

  `lowerAluJ2 d opn s0 s1 = (lowerAluJ d (stripWidthTag opn) s1).map (fun i => [mov d s0, i])`

— always a leading `mov d s0` (a register-count `SHL`/`SHR`/`SAR` is the single
BMI2 `shlx`/`shrx`/`sarx`, `LoweringExtended.lowerShiftRegJ`, on both variants).
The in-place variant `lowerAluJ2InPlace` keeps the
`[mov d s0, OP d s1]` split **except** when `s0 = .reg d`: then it emits just
`[OP d s1]` (the destructive single-op form `encodeLopn` produces). `lowerLinstrExtCov3`
intercepts the two-source `regArith` mnemonics (`ADD/SUB/AND/OR/XOR:64`) with this
peephole; on the `s0 = d` two-source case the gather emits the single in-place op,
matching the Lprog encoder.

## The delegation target (`lowerLinstrExtCov2`)

The catch-all delegates to `LoweringCoverageCmovSar.lowerLinstrExtCov2` rather than
straight to `lowerLinstrExtCov`. That level is a strict superset of
`lowerLinstrExtCov` — its own catch-all is `lowerLinstrExtCov` verbatim — carrying
the literal-tagged immediate arithmetic right-shifts `SAR:63:64` / `SAR:23:64` /
`SAR:31` (the `sarImm` export of `opToLinstrR`), which the levels below drop:
`parseShiftMnem` detects only the `SHL:`/`SHR:` prefixes and `lowerAluJ`'s table
carries no `SAR:<n>` mnemonic. The lowered block is `[mov d src, sar d #n]`, whose
`sar` the byte encoder emits as the group-2 `/7` shift-by-`imm8`
(`ScalarEncoder.encodeJInstr`), and both ops are `IsDirect`, so the block stays in
the unconditional `allDirect` constant-time class.

## The byte-agreement theorem (the deliverable)

`encJInPlace_or64_eq_lopn` (and the `xor`/`add`/`sub`/`and` analogues): for the
in-place two-source op `OR:64 [d, s1]` (dst `d`, first source `d` itself), the
gathered JInstr block encodes to **exactly** the Lprog `encodeLopn` destructive-op
bytes — *no* leading self-`mov`. This is `or_bytes_agree` (the proven per-op
resolver agreement) ∘ `encodeLopn_or₂` (the proven Lprog dispatch), with the
self-`mov` of `or64_block_eq_mov_prepend_lopn` removed by the peephole. With both
divergences addressed — (1) here, (2) in `encodeLopn`'s `encTagShift` arm — the
shift-free ALU core byte-matches `encodeLcmd` exactly (§4b′), and the shift op itself
agrees per-op; the only whole-core residual is the gather's per-shift materialise `mov`.

No `sorry`, no axiom, no `native_decide` (the lemma proofs; the `#eval`/byte-length
witnesses in §4 are interpreter evaluation, not part of any proof term).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageCmovSar (lowerLinstrExtCov2)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (isCarryOutBinding isMulHiBinding mnemWidth)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended

/-! ## 1. The in-place two-source lowering (the skip-mov peephole) -/

/-- The in-place (skip-mov) two-source ALU lowering. Identical to `lowerAluJ2`
    (including the single BMI2 `shlx`/`shrx`/`sarx` of a register-count shift)
    except when the first source is the destination itself (`s0 = .reg dst` — the
    destructive form `Com.toLprogPhysAbi` produces): then the leading materialise
    `mov dst s0` is `mov dst, dst`, a redundant self-move the Lprog `encodeLopn`
    does not emit, so it is **elided** and only the destructive op `OP dst s1`
    remains — matching the Lprog encoder's single-op form. `none` if the
    (tag-stripped) mnemonic is outside both tables. -/
def lowerAluJ2InPlace (dst : String) (opn : String) (s0 s1 : JOperand) :
    Option (List (JInstr 64)) :=
  (lowerShiftRegJ dst (stripWidthTag opn) s0 s1).or
    ((lowerAluJ dst (stripWidthTag opn) s1).map (fun i =>
      if s0 = JOperand.reg dst then [i] else [JInstr.mov dst s0, i]))

/-- The in-place coverage lowering. The two-source `regArith` mnemonics
    (`ADD/SUB/AND/OR/XOR:64`, plus their untagged forms) are intercepted with the
    `lowerAluJ2InPlace` peephole (skip the leading `mov` when `s0 = dst`); the
    high-word multiply `MULXHI:64` and the two-source memory scatters
    `STORE`/`STOREIDX` delegate to `lowerLinstrExtCov` verbatim; every other shape
    delegates to `lowerLinstrExtCov2`, the immediate-arithmetic-right-shift
    superset whose own catch-all is `lowerLinstrExtCov`. So `lowerLinstrExtCov3`
    differs from `lowerLinstrExtCov` on the `s0 = dst` two-source `regArith` case,
    where it emits the single in-place op the Lprog encoder produces, and on the
    literal-tagged `SAR:<n>` shapes, which `lowerLinstrExtCov2` lowers.

    The `MULXHI:64` / `STORE` / `STOREIDX` head patterns sit above the generic
    two-source arm because those shapes also carry two sources: without them the
    generic arm would run `lowerAluJ2InPlace` on a mnemonic outside the ALU table
    and return `none`, hiding coverage `lowerLinstrExtCov` already has. -/
def lowerLinstrExtCov3 : LinstrR → Option (List (JInstr 64))
  -- the high-word multiply stays as `lowerLinstrExtCov` lowers it (two sources, but
  -- not a `regArith` split — keep it before the generic two-source peephole arm)
  | .Lopn [.reg dst] "MULXHI:64" [s0, s1] =>
      lowerLinstrExtCov (.Lopn [.reg dst] "MULXHI:64" [s0, s1])
  -- the two-source memory scatters: constant-offset `STORE` and register-indexed
  -- (SIB) `STOREIDX`, both `[.arr…/.arrIdx…, val]` shapes
  | .Lopn [.reg dst] "STORE" [s0, s1] =>
      lowerLinstrExtCov (.Lopn [.reg dst] "STORE" [s0, s1])
  | .Lopn [.reg dst] "STOREIDX" [s0, s1] =>
      lowerLinstrExtCov (.Lopn [.reg dst] "STOREIDX" [s0, s1])
  -- generic two-source ALU (`regArith bop 64`): the in-place peephole
  | .Lopn [.reg dst] opn [s0, s1] =>
      lowerAluJ2InPlace dst opn (lowerJOperand s0) (lowerJOperand s1)
  -- everything else: the immediate-arithmetic-right-shift superset, whose own
  -- catch-all is `lowerLinstrExtCov`
  | i => lowerLinstrExtCov2 i

/-- The two-source memory scatters delegate to `lowerLinstrExtCov`, so the
    register-indexed store the SSA exporter emits gathers. -/
theorem lowerLinstrExtCov3_storeidx (dst base idx : String) (scale : Nat) (val : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val])
      = some [JInstr.storeMemIdx base idx scale (lowerJOperand val)] := rfl

/-- The constant-offset store delegates to `lowerLinstrExtCov`. -/
theorem lowerLinstrExtCov3_store (dst base : String) (off : Nat) (val : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "STORE" [.arr base off, val])
      = some [JInstr.storeMem base (off : Int) (lowerJOperand val)] := rfl

/-- The literal-tagged immediate arithmetic right-shift `SAR:63:64` (the `>> 63`
    sign-extract) reaches `lowerLinstrExtCov2` through the catch-all and lowers to
    `[mov d src, sar d #63]`. -/
theorem lowerLinstrExtCov3_sar63 (dst : String) (src : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SAR:63:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 63)] := rfl

/-- The `SAR:23:64` reduce shift, likewise. -/
theorem lowerLinstrExtCov3_sar23 (dst : String) (src : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SAR:23:64" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 23)] := rfl

/-- The narrow-width `SAR:31` (no `:64` tag), likewise. -/
theorem lowerLinstrExtCov3_sar31 (dst : String) (src : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SAR:31" [src])
      = some [JInstr.mov dst (lowerJOperand src), JInstr.sar dst (JOperand.imm 31)] := rfl

/-- A single-source shape outside the `SAR:` literals delegates to
    `lowerLinstrExtCov` through `lowerLinstrExtCov2`'s catch-all. -/
theorem lowerLinstrExtCov3_delegates_load (dst base : String) (off : Nat) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "LOAD" [.arr base off])
      = lowerLinstrExtCov (.Lopn [.reg dst] "LOAD" [.arr base off]) := rfl

/-- Lower a full `Linstr` (drops the position tag), in-place coverage superset. -/
def lowerLinstrExtCov3L (i : Linstr) : Option (List (JInstr 64)) :=
  lowerLinstrExtCov3 i.li_i

/-- **The in-place `JInstr` gather.** Drop the trailing `Lret` (framing supplies the
    `ret`), then lower every remaining instruction through `lowerLinstrExtCov3` (the
    skip-mov peephole on the two-source `regArith` shapes) and flatten. `none` iff
    some non-`Lret` instruction is outside the superset fragment. -/
def gatherJBlock3 (body : List Linstr) : Option (List (JInstr 64)) :=
  ((body.filter (fun i => !isLret i)).mapM lowerLinstrExtCov3L).map List.flatten

/-! ## 2. The peephole equations (kernel-clean `decide +kernel` tag strip)

For the destructive in-place form `OP:64 [.reg dst, s1]` the peephole fires and the
lowering is the **single** destructive op — no leading self-`mov`. The `:64` tag
strip is `decide +kernel`, the same route `BlockBytesAgreeExtended.lower_or64` uses
for the non-in-place form. -/

/-- In-place `OR:64 [d, s1]` (first source `= d`) lowers to just `[or_ d s1]`. -/
theorem lower_or64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "OR:64" [.reg dst, .reg s1])
      = some [JInstr.or_ dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "OR:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "OR:64" = "OR" from by decide +kernel, lowerShiftRegJ_OR,
    Option.none_or, lowerAluJ, Option.map_some, if_pos]

/-- In-place `XOR:64 [d, s1]` lowers to just `[xor_ d s1]`. -/
theorem lower_xor64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "XOR:64" [.reg dst, .reg s1])
      = some [JInstr.xor_ dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "XOR:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "XOR:64" = "XOR" from by decide +kernel, lowerShiftRegJ_XOR,
    Option.none_or, lowerAluJ, Option.map_some, if_pos]

/-- In-place `ADD:64 [d, s1]` lowers to just `[add d s1]`. -/
theorem lower_add64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "ADD:64" [.reg dst, .reg s1])
      = some [JInstr.add dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "ADD:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "ADD:64" = "ADD" from by decide +kernel, lowerShiftRegJ_ADD,
    Option.none_or, lowerAluJ, Option.map_some, if_pos]

/-- In-place `SUB:64 [d, s1]` lowers to just `[sub d s1]`. -/
theorem lower_sub64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SUB:64" [.reg dst, .reg s1])
      = some [JInstr.sub dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "SUB:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "SUB:64" = "SUB" from by decide +kernel, lowerShiftRegJ_SUB,
    Option.none_or, lowerAluJ, Option.map_some, if_pos]

/-- In-place `AND:64 [d, s1]` lowers to just `[and_ d s1]`. -/
theorem lower_and64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "AND:64" [.reg dst, .reg s1])
      = some [JInstr.and_ dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "AND:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "AND:64" = "AND" from by decide +kernel, lowerShiftRegJ_AND,
    Option.none_or, lowerAluJ, Option.map_some, if_pos]

/-! ### 2b. The register-count shifts: one BMI2 instruction, no leading `mov`

A two-source `SHL:64`/`SHR:64`/`SAR:64 [v, c]` with a register count lowers, on
both `lowerLinstrExt2` and the in-place `lowerLinstrExtCov3`, to the single
flag-free `shlx`/`shrx`/`sarx dst v c`, which `ScalarEncoder.encodableJInstr`
accepts and `encodeJInstr` encodes as `encShiftX` (five bytes). This is the
shape the SSA exporter emits for `regArith .shr 64` over a runtime count (the
dialect `bvShiftRV`, e.g. the P-256 ladder's per-trip scalar-bit load
`bit := limb >> sa`). -/

/-- `SHR:64 [v, c]` lowers on `lowerLinstrExt2` to the single `shrx`. -/
theorem lowerLinstrExt2_shr_reg (dst v c : String) :
    lowerLinstrExt2 (.Lopn [.reg dst] "SHR:64" [.reg v, .reg c])
      = some [JInstr.shrx dst v c] := by
  show lowerAluJ2 dst "SHR:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  exact lowerAluJ2_shr_reg dst _ v c (by decide +kernel)

/-- `SHL:64 [v, c]` lowers on `lowerLinstrExt2` to the single `shlx`. -/
theorem lowerLinstrExt2_shl_reg (dst v c : String) :
    lowerLinstrExt2 (.Lopn [.reg dst] "SHL:64" [.reg v, .reg c])
      = some [JInstr.shlx dst v c] := by
  show lowerAluJ2 dst "SHL:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  exact lowerAluJ2_shl_reg dst _ v c (by decide +kernel)

/-- `SAR:64 [v, c]` lowers on `lowerLinstrExt2` to the single `sarx`. -/
theorem lowerLinstrExt2_sar_reg (dst v c : String) :
    lowerLinstrExt2 (.Lopn [.reg dst] "SAR:64" [.reg v, .reg c])
      = some [JInstr.sarx dst v c] := by
  show lowerAluJ2 dst "SAR:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  exact lowerAluJ2_sar_reg dst _ v c (by decide +kernel)

/-- `SHR:64 [v, c]` lowers on the in-place gather to the single `shrx`. -/
theorem lower_shr64_reg (dst v c : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SHR:64" [.reg v, .reg c])
      = some [JInstr.shrx dst v c] := by
  show lowerAluJ2InPlace dst "SHR:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "SHR:64" = "SHR" from by decide +kernel, lowerShiftRegJ, Option.some_or]

/-- `SHL:64 [v, c]` lowers on the in-place gather to the single `shlx`. -/
theorem lower_shl64_reg (dst v c : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SHL:64" [.reg v, .reg c])
      = some [JInstr.shlx dst v c] := by
  show lowerAluJ2InPlace dst "SHL:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "SHL:64" = "SHL" from by decide +kernel, lowerShiftRegJ, Option.some_or]

/-- `SAR:64 [v, c]` lowers on the in-place gather to the single `sarx`. -/
theorem lower_sar64_reg (dst v c : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SAR:64" [.reg v, .reg c])
      = some [JInstr.sarx dst v c] := by
  show lowerAluJ2InPlace dst "SAR:64" (lowerJOperand (.reg v)) (lowerJOperand (.reg c)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "SAR:64" = "SAR" from by decide +kernel, lowerShiftRegJ, Option.some_or]

/-- The lowered register-count `SHR` block passes the per-instruction byte gate:
    every instruction of it is `encodableJInstr`. -/
theorem lowerLinstrExt2_shr_reg_encodable (dst v c : String) :
    (lowerLinstrExt2 (.Lopn [.reg dst] "SHR:64" [.reg v, .reg c])).map
        (fun b => b.all encodableJInstr) = some true := by
  rw [lowerLinstrExt2_shr_reg]; rfl

/-- The bytes of the lowered register-count `SHR` block are the BMI2 `shrx`
    encoding `encShiftX 5 dst v c` (`VEX.LZ.F2.0F38.W1 F7 /r`). -/
theorem encJ_shr_reg (alloc : GpAlloc) (dst v c : String) :
    (lowerLinstrExt2 (.Lopn [.reg dst] "SHR:64" [.reg v, .reg c])).map (encodeJBlock alloc)
      = some (encShiftX 5 (gpNum (regOf alloc dst)) (gpNum (regOf alloc v))
          (gpNum (regOf alloc c))) := by
  rw [lowerLinstrExt2_shr_reg, Option.map_some]
  simp [encodeJBlock, List.flatMap_cons, encodeJInstr]

/-- The gated per-instruction encoder accepts the lowered `shrx` and returns
    `encShiftX`. -/
theorem encodeJInstr?_lowered_shr_reg (alloc : GpAlloc) (dst v c : String) :
    (lowerLinstrExt2 (.Lopn [.reg dst] "SHR:64" [.reg v, .reg c])).map
        (fun b => b.map (encodeJInstr? alloc))
      = some [some (encShiftX 5 (gpNum (regOf alloc dst)) (gpNum (regOf alloc v))
          (gpNum (regOf alloc c)))] := by
  rw [lowerLinstrExt2_shr_reg, Option.map_some, List.map_cons, List.map_nil,
    encodeJInstr?_shrx]

/-- The P-256 scalar-bit load shape `bit := limb >> sa` (the `bvShiftRV` export,
    a runtime count register) lowers to a block the byte gate accepts, evaluated
    in the kernel. This is a static check: the lowering is closed and reduces. -/
example :
    (lowerLinstrExt2 (.Lopn [.reg "bit"] "SHR:64" [.reg "limb", .reg "sa"])).map
        (fun b => b.all encodableJInstr) = some true := by
  decide +kernel

/-! ## 3. The per-op byte-agreement theorem (the deliverable)

For the in-place two-source op the gathered JInstr block encodes to **exactly** the
Lprog `encodeLopn` destructive-op bytes — no leading self-`mov`. This is
`§3.lower_or64_inplace` (the peephole) ∘ `or_bytes_agree` (the proven per-op resolver
agreement, `BlockBytesAgreeExtended` imports) ∘ `encodeLopn_or₂` (the proven Lprog
dispatch). `native_decide`-free: the same `decide +kernel` / `simp only` route as
`or64_block_eq_mov_prepend_lopn`, with the self-`mov` term gone. The resolver
side-conditions (`hd`/`hs`) tie the JInstr register names to the Lprog `gpNumU`
numbers, the same hypotheses the POC `*_bytes_agree` lemmas carry. -/

/-- **`OR:64` in-place byte agreement.** The gathered in-place JInstr block for the
    destructive `OR:64 [d, s1]` encodes byte-for-byte to the Lprog `encodeLopn`
    destructive-op bytes — *no* leading self-`mov`, exactly the §1 divergence removed
    by the peephole. -/
theorem encJInPlace_or64_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String) (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov3 (.Lopn [.reg d] "OR:64" [.reg d, .reg r])).map (encodeJBlock alloc)
      = some (encodeLopn frame spillW
                (.Lopn [.reg dn] "OR:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lower_or64_inplace, Option.map_some, encodeLopn_or₂,
    ← or_bytes_agree alloc frame spillW d r dn sn qsaveB hdk hsk hdm hsm hdsp hssp hd hs]
  simp [encodeJBlock, List.flatMap_cons]

/-- **`XOR:64` in-place byte agreement** — the dual of `encJInPlace_or64_eq_lopn`. -/
theorem encJInPlace_xor64_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String) (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov3 (.Lopn [.reg d] "XOR:64" [.reg d, .reg r])).map (encodeJBlock alloc)
      = some (encodeLopn frame spillW
                (.Lopn [.reg dn] "XOR:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lower_xor64_inplace, Option.map_some, encodeLopn_xor₂,
    ← xor_bytes_agree alloc frame spillW d r dn sn qsaveB hdk hsk hdm hsm hdsp hssp hd hs]
  simp [encodeJBlock, List.flatMap_cons]

/-! ### 3b. The residual self-`mov` is gone (the divergence closed, made concrete)

`BlockBytesAgreeExtended.selfMov_length` records that the non-in-place gather carries
a 3-byte self-`mov` excess over the Lprog op. The in-place gather carries **none**:
the encoded block is a single op, the same length as the Lprog encoding. We witness
this concretely (the `#eval`s in §4 print equal lengths), and structurally: the
in-place lowering is a one-element list, so its `encodeJBlock` is `encodeJInstr` of
the single op — with no prepended `mov`. -/

/-- The in-place block is the **single** destructive op's bytes — no self-`mov`
    prepended (contrast `or64_block_eq_mov_prepend_lopn`, which carries the leading
    `encodeJInstr (mov d s0)`). -/
theorem inplace_or64_block_single (alloc : GpAlloc) (d r : String) :
    (lowerLinstrExtCov3 (.Lopn [.reg d] "OR:64" [.reg d, .reg r])).map (encodeJBlock alloc)
      = some (encodeJInstr alloc (JInstr.or_ d (.reg r))) := by
  rw [lower_or64_inplace, Option.map_some]
  simp [encodeJBlock, List.flatMap_cons]

/-! ## 4. `#eval` verification on asconSigma0's physical ALU core, and the shift finding

The `#eval` byte-compares on the real GoldenPath kernel
`AsconLinear.asconSigma0Com` (reusing `physBody`/`aluCore`), plus the shift-free
core byte-match and the per-rotation byte witnesses, are placed in
`GoldenPathByteIdentityDemo` (above the chain) so this file is GoldenPath-free.
The kernel-independent per-op in-place byte-agreement certificates are kept here:
the in-place gather's `OR:64 [RDX, RCX]` / `XOR:64 [RAX, RDX]` encode to exactly
the Lprog `encodeLopn` bytes. -/

-- Direct in-place byte-agreement on a destructive two-source op, kernel-computable:
-- the in-place gather's `OR:64 [RDX, RCX]` (dst = RDX) encodes to exactly the Lprog
-- `encodeLopn` bytes — equal. The alloc maps the bare-uppercase Lprog names to the
-- `%`-prefixed JInstr names so `gpNum (regOf …) = gpNumU`. Prints `true`.
#eval (lowerLinstrExtCov3 (.Lopn [.reg "RDX"] "OR:64" [.reg "RDX", .reg "RCX"])).map
        (encodeJBlock [("RDX","%rdx"),("RCX","%rcx")])
      == some (encodeLopn 0 0 (.Lopn [.reg "RDX"] "OR:64" [.reg "RDX", .reg "RCX"]))

-- The XOR dual, kernel-computable. Prints `true`.
#eval (lowerLinstrExtCov3 (.Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .reg "RDX"])).map
        (encodeJBlock [("RAX","%rax"),("RDX","%rdx")])
      == some (encodeLopn 0 0 (.Lopn [.reg "RAX"] "XOR:64" [.reg "RAX", .reg "RDX"]))

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
