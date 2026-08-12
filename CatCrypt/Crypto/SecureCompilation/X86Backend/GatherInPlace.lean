/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.BlockBytesAgreeExtended
import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather

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

2. **The count-in-tag shift representation mismatch.**
   `Com.toLprogPhysAbi` emits the rotate shifts as `Lopn [RAX] "SHR:19:64" [RBX]` —
   count in the **mnemonic tag**, source a **register**. The gather lowers this to
   `mov RAX, RBX ; shr RAX, $19` (7 bytes), while `encodeLopn` encodes the same `Lopn`
   as the shift op alone, `shr RAX, $19` (`[0x48,0xc1,0xe8,0x13]`), through its
   `encTagShift` arm (the `.imm`-source arm does not match a register-source
   count-in-tag shift). So the shift OP agrees byte-for-byte and the whole divergence
   is the gather's leading materialise `mov`.

This module is the **additive** fix for divergence (1): a new lowering
`lowerLinstrExtCov3` with the `d == s0 ⇒ skip the leading mov` peephole on the
two-source `regArith` shapes, a gather `gatherJBlock3` / entries built on it, the
per-op byte-agreement theorem for the in-place case (`native_decide`-free, via the
`BlockBytesAgreeExtended` dispatch technique), and `#eval` evidence that with the
peephole the two-source ALU core now byte-matches `encodeLopn`.

Divergence (2) — the shift — is handled on the `encodeLopn` side by the `encTagShift`
arm (`BlockBytesAgreeExtended.encodeLopn_shr19_emits`); the byte witnesses on the real
kernel live in `GoldenPathByteIdentityDemo` (every ALU-core `Lopn` encodes to a
non-empty byte list). The remaining shift residual between the two gathers is the
gather's leading materialise `mov d, src` (the shift arm `lowerShiftImmJ` does not
coalesce `d = src`) — the shift OP itself byte-agrees on both sides.

## The peephole (divergence 1)

`lowerLinstrExtCov` delegates the two-source `regArith` shapes to
`lowerLinstrExt2 → lowerAluJ2`, which is

  `lowerAluJ2 d opn s0 s1 = (lowerAluJ d (stripWidthTag opn) s1).map (fun i => [mov d s0, i])`

— always a leading `mov d s0`. The in-place variant `lowerAluJ2InPlace` keeps the
`[mov d s0, OP d s1]` split **except** when `s0 = .reg d`: then it emits just
`[OP d s1]` (the destructive single-op form `encodeLopn` produces). `lowerLinstrExtCov3`
intercepts the two-source `regArith` mnemonics (`ADD/SUB/AND/OR/XOR:64`) with this
peephole and delegates everything else to `lowerLinstrExtCov` verbatim — a strict
behavioural refinement (only the `s0 = d` two-source case changes; the gather now
emits the single in-place op there, matching the Lprog encoder).

## The byte-agreement theorem (the deliverable)

`encJInPlace_or64_eq_lopn` (and the `xor`/`add`/`sub`/`and` analogues): for the
in-place two-source op `OR:64 [d, s1]` (dst `d`, first source `d` itself), the
gathered JInstr block encodes to **exactly** the Lprog `encodeLopn` destructive-op
bytes — *no* leading self-`mov`. This is `or_bytes_agree` (the proven per-op
resolver agreement) ∘ `encodeLopn_or₂` (the proven Lprog dispatch), with the
self-`mov` of `or64_block_eq_mov_prepend_lopn` removed by the peephole. With both
divergences addressed — (1) here, (2) in `encodeLopn`'s `encTagShift` arm — the
shift-free ALU core byte-matches `encodeLcmd` exactly (witnessed on the real kernel in
`GoldenPathByteIdentityDemo`), and the shift op agrees per-op; the only whole-core
residual is the gather's per-shift materialise `mov`.

No `sorry`, no axiom, no `native_decide` (the lemma proofs; the `#eval`/byte-length
witnesses in §4 are interpreter evaluation, not part of any proof term).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtended
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
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
    except when the first source is the destination itself (`s0 = .reg dst` — the
    destructive form `Com.toLprogPhysAbi` produces): then the leading materialise
    `mov dst s0` is `mov dst, dst`, a redundant self-move the Lprog `encodeLopn`
    does not emit, so it is **elided** and only the destructive op `OP dst s1`
    remains — matching the Lprog encoder's single-op form. `none` if the
    (tag-stripped) mnemonic is outside the `lowerAluJ` table. -/
def lowerAluJ2InPlace (dst : String) (opn : String) (s0 s1 : JOperand) :
    Option (List (JInstr 64)) :=
  (lowerAluJ dst (stripWidthTag opn) s1).map (fun i =>
    if s0 = JOperand.reg dst then [i] else [JInstr.mov dst s0, i])

/-- The in-place coverage lowering. The two-source `regArith` mnemonics
    (`ADD/SUB/AND/OR/XOR:64`, plus their untagged forms) are intercepted with the
    `lowerAluJ2InPlace` peephole (skip the leading `mov` when `s0 = dst`); the
    high-word multiply `MULXHI:64`, the two-source memory scatters
    `STORE`/`STOREIDX`, and every other shape delegate to `lowerLinstrExtCov`
    verbatim. So `lowerLinstrExtCov3` differs from `lowerLinstrExtCov` only on the
    `s0 = dst` two-source `regArith` case, where it emits the single in-place op
    the Lprog encoder produces.

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
  -- everything else: the coverage superset verbatim
  | i => lowerLinstrExtCov i

/-- The two-source memory scatters delegate to `lowerLinstrExtCov`, so the
    register-indexed store the SSA exporter emits gathers. -/
theorem lowerLinstrExtCov3_storeidx (dst base idx : String) (scale : Nat) (val : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx scale, val])
      = some [JInstr.storeMemIdx base idx scale (lowerJOperand val)] := rfl

/-- The constant-offset store delegates to `lowerLinstrExtCov`. -/
theorem lowerLinstrExtCov3_store (dst base : String) (off : Nat) (val : LOperand) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "STORE" [.arr base off, val])
      = some [JInstr.storeMem base (off : Int) (lowerJOperand val)] := rfl

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
    show stripWidthTag "OR:64" = "OR" from by decide +kernel, lowerAluJ, Option.map_some,
    if_pos]

/-- In-place `XOR:64 [d, s1]` lowers to just `[xor_ d s1]`. -/
theorem lower_xor64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "XOR:64" [.reg dst, .reg s1])
      = some [JInstr.xor_ dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "XOR:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "XOR:64" = "XOR" from by decide +kernel, lowerAluJ, Option.map_some,
    if_pos]

/-- In-place `ADD:64 [d, s1]` lowers to just `[add d s1]`. -/
theorem lower_add64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "ADD:64" [.reg dst, .reg s1])
      = some [JInstr.add dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "ADD:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "ADD:64" = "ADD" from by decide +kernel, lowerAluJ, Option.map_some,
    if_pos]

/-- In-place `SUB:64 [d, s1]` lowers to just `[sub d s1]`. -/
theorem lower_sub64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "SUB:64" [.reg dst, .reg s1])
      = some [JInstr.sub dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "SUB:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "SUB:64" = "SUB" from by decide +kernel, lowerAluJ, Option.map_some,
    if_pos]

/-- In-place `AND:64 [d, s1]` lowers to just `[and_ d s1]`. -/
theorem lower_and64_inplace (dst s1 : String) :
    lowerLinstrExtCov3 (.Lopn [.reg dst] "AND:64" [.reg dst, .reg s1])
      = some [JInstr.and_ dst (.reg s1)] := by
  show lowerAluJ2InPlace dst "AND:64" (lowerJOperand (.reg dst)) (lowerJOperand (.reg s1)) = _
  simp only [lowerAluJ2InPlace, lowerJOperand,
    show stripWidthTag "AND:64" = "AND" from by decide +kernel, lowerAluJ, Option.map_some,
    if_pos]

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
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov3 (.Lopn [.reg d] "OR:64" [.reg d, .reg r])).map (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "OR:64" [.reg dn, .reg sn])) := by
  rw [lower_or64_inplace, Option.map_some, encodeLopn_or₂,
    ← or_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs]
  simp [encodeJBlock, List.flatMap_cons]

/-- **`XOR:64` in-place byte agreement** — the dual of `encJInPlace_or64_eq_lopn`. -/
theorem encJInPlace_xor64_eq_lopn
    (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (hdk : spillQsaveOff frame spillW dn = none) (hsk : spillQsaveOff frame spillW sn = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    (lowerLinstrExtCov3 (.Lopn [.reg d] "XOR:64" [.reg d, .reg r])).map (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "XOR:64" [.reg dn, .reg sn])) := by
  rw [lower_xor64_inplace, Option.map_some, encodeLopn_xor₂,
    ← xor_bytes_agree alloc frame spillW d r dn sn hdk hsk hdm hsm hdsp hssp hd hs]
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
core byte-match and the dropped-rotation regression witnesses, are re-homed in
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
