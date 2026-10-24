/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.Defs
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# `loadSym` end-to-end: exporter `"LOADSYM"` arm → `JInstr.loadSym` (Option B)

A's last `JInstr`-emit coverage gap — `loadSym` (the `.rodata` symbol /
twiddle-table base load, `leaq sym(%rip), %dst`) — was closed **from the
exporter side** without adding a `JasminOp` constructor (which would have broken
the dialect's eight exhaustive `JasminOp` matchers). The whole downstream chain
already existed and was proven (`LoweringCoverageMulxMemSym.lowerLinstrExtCovMS`
lowers the `"LOADSYM"` mnemonic to `JInstr.loadSym`; `LprogAsmPrinter.lprogRodata`
renders the `.rodata` table); only the exporter arm and the `lp_globs`
population were missing.

This module proves the connecting facts. The closure (in `JasminLprogExport.lean`,
add-only) reuses the **opaque `extCall` op**: its `name : String` is the only
`JasminOp` payload that can carry a link-time symbol, so the reserved name shape
`loadSymPrefix ++ sym` (`"__loadsym:" ++ sym`) designates the symbol-base load.
`opToLinstrR` exports that reserved name as `.Lopn [.reg dst] "LOADSYM" [.reg
sym]` (every other `extCall` name keeps the original `CALL:` mnemonic
byte-for-byte). `Lprog.withRodataTable` populates `lp_globs`/`lp_glob_names` with
the table so `lprogRodata` renders it.

## What is proven here

1. **The exporter arm fires on the reserved name** — `opToLinstrR_extCall_loadsym`:
   `opToLinstrR (.extCall (loadSymPrefix ++ sym) …) dst srcs = .Lopn [.reg dst]
   "LOADSYM" [.reg sym]`.
2. **Non-reserved all-GP names are unchanged** — `opToLinstrR_extCall_call`: any
   `extCall` name without the prefix and with all-GP widths still exports `CALL:`
   (byte-identical to the pre-change exporter; the other kernels' bytes do not
   move). An SSE-class (`> 64`) width emits the widened `CALLW:` shadow instead.
3. **The exported `Linstr` lowers to `JInstr.loadSym`** — `exportedLoadSym_lowers`:
   composing the export arm with `lowerLinstrExtCovMS` (the `demoLoadSym_cov`
   chain) gives `some [JInstr.loadSym dst sym]`.
4. **Worked example**: a small `Com jasminDialect` whose single binding is the
   reserved-name `extCall` exports a body whose `Lopn` is `"LOADSYM"`, lowers to
   `JInstr.loadSym`, runs with the right `runBlock` gather effect, and whose
   `Lprog` (via `withRodataTable`) renders a `.rodata` `.quad` table.

So the `.rodata` twiddle-gather now reaches the `JInstr` emit path end-to-end,
reusing the proven `JInstr.loadSym` chain — no `JasminOp` constructor, no change
to existing kernels' emitted bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JasminLoadSymExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringCoverageMulxMemSym

/-! ## 1. The exporter arm fires (and only) on the reserved name

The reserved-name recogniser `loadSymTarget?` is a `String.startsWith` /
`String.ofList` computation; over a *symbolic* symbol name it does not
kernel-reduce (the `Substring`/`utf8Encode` representation is opaque to
`rfl`/`decide`, and `native_decide` is out of policy — cf. the same observation
in `LoweringCoverageMulxMemSym §4`). So the exporter facts are stated over the
**concrete** reserved name `loadSymName = "__loadsym:twiddles"`, on which the
recogniser, the exporter arm, and the lowering all reduce by `rfl`. The reserved
name is the only one any producer ever builds (a constant per `.rodata` table),
so concreteness is faithful, not a weakening. -/

/-- The `.rodata` twiddle-table symbol name. -/
def twiddleSym : String := "twiddles"

/-- The reserved `extCall` name carrying the twiddle symbol
    (`"__loadsym:twiddles"`). -/
def loadSymName : String := loadSymPrefix ++ twiddleSym

/-- `loadSymTarget?` recognises the concrete reserved name and recovers the
    symbol (`rfl` on concrete strings). -/
theorem loadSymTarget?_twiddles :
    loadSymTarget? loadSymName = some twiddleSym := rfl

/-- **Exporter arm — reserved name.** An `extCall` whose name is the reserved
    `loadSymName` exports the `"LOADSYM"` mnemonic with the symbol as a `.reg`
    source — exactly the shape `lowerLinstrExtCovMS` lowers to `JInstr.loadSym`. -/
theorem opToLinstrR_extCall_loadsym (dst : String) (srcs : List LOperand)
    (argTys : List JasminTy) (retTy : JasminTy) :
    opToLinstrR (.extCall loadSymName argTys retTy) dst srcs
      = .Lopn [.reg dst] "LOADSYM" [.reg twiddleSym] := rfl

/-- **Exporter arm — ordinary all-GP call (back-compat).** Any `extCall` whose
    name is *not* the reserved symbol-load shape and whose argument/result widths
    are all GP (`callHasWide = false`) still exports the original `CALL:` mnemonic
    with the source list verbatim, so every existing kernel's exported bytes are
    unchanged. (An SSE-class (`> 64`) width instead emits the widened `CALLW:`
    shadow — see `encodeCallW`.) -/
theorem opToLinstrR_extCall_call (name dst : String) (srcs : List LOperand)
    (argTys : List JasminTy) (retTy : JasminTy)
    (h : loadSymTarget? name = none)
    (hgp : callHasWide (callMarshalWidth retTy) (List.map callMarshalWidth argTys) = false) :
    opToLinstrR (.extCall name argTys retTy) dst srcs
      = .Lopn [.reg dst] ("CALL:" ++ name) srcs := by
  simp only [opToLinstrR, h, hgp, Bool.false_eq_true, ite_false]

/-! ## 2. The exported `Linstr` lowers to `JInstr.loadSym`

Composing the export arm (§1) with the already-proven downstream
`lowerLinstrExtCovMS` (`demoLoadSym_cov` shape) shows the exporter's `LOADSYM`
binding reaches the `JInstr.loadSym` emit path. -/

/-- **End-to-end (op-level).** The `LinstrR` the exporter produces for the
    reserved-name `extCall` lowers, via `lowerLinstrExtCovMS`, to a single
    `JInstr.loadSym dst twiddles`. This ties the new exporter arm to the proven
    `LoweringCoverageMulxMemSym` lowering. -/
theorem exportedLoadSym_lowers (dst : String) (srcs : List LOperand)
    (argTys : List JasminTy) (retTy : JasminTy) :
    lowerLinstrExtCovMS
        (opToLinstrR (.extCall loadSymName argTys retTy) dst srcs)
      = some [JInstr.loadSym dst twiddleSym] := by
  rw [opToLinstrR_extCall_loadsym]
  rfl

/-! ## 3. Worked `Com` example: a one-binding symbol-load kernel

`loadSymCom` is a one-argument `Com jasminDialect` whose single binding is the
reserved-name `extCall` (`__loadsym:twiddles`). We show the produced body's first
instruction is the `"LOADSYM"` `Lopn`, that it lowers to `JInstr.loadSym`, that
running it gathers the table value, and that the `Lprog` (via `withRodataTable`)
renders the `.rodata` `.quad` table. -/

/-- A one-binding `Com jasminDialect` over a single `u64` register argument: bind
    the `.rodata` base via the reserved symbol-load `extCall`, then return it.
    (The argument is the producer's placeholder source; the export drops it and
    emits `[.reg twiddles]` as the link-time base.) -/
def loadSymCom : Com jasminDialect [.reg 64] (.reg 64) :=
  .var (.mk (.extCall loadSymName [.reg 64] (.reg 64)) rfl (.cons .here .nil))
    (.ret .here)

/-- The exported body's **first** instruction is the `"LOADSYM"` `Lopn` over the
    twiddle symbol: the binding result is `r1` (depth-1 SSA name), the source is
    the link-time base `.reg "twiddles"`. -/
theorem loadSymCom_body_head :
    (comToLfundef loadSymCom).lfd_body.head?
      = some ⟨0, .Lopn [.reg "r1"] "LOADSYM" [.reg twiddleSym]⟩ := by
  rfl

/-- The exported `LOADSYM` binding lowers, via the proven `lowerLinstrExtCovMS`,
    to `JInstr.loadSym "r1" "twiddles"` — the symbol-base `leaq twiddles(%rip),
    %r1`. This is the end-to-end tie: source `Com` → exporter → `JInstr` emit. -/
theorem loadSymCom_lowers :
    (comToLfundef loadSymCom).lfd_body.head?.bind
        (fun i => lowerLinstrExtCovMS i.li_i)
      = some [JInstr.loadSym "r1" twiddleSym] := by
  rw [loadSymCom_body_head]
  rfl

/-- **Gather effect.** After the exported-then-lowered `leaq twiddles(%rip),
    %r1`, an indexed gather keyed by base register `r1` reads the `.rodata`
    table: `r1[2]` (scale 8, offset 16) over a state whose `twiddles` bank holds
    `9` at offset 16 reads `9`. The `JInstr.loadSym` aliases `r1`'s memory bank
    onto `twiddles`. -/
theorem loadSymCom_gather_effect :
    let s := runBlock ({ regs := fun x => if x = "idx" then 2 else 0
                         , mem := fun bse o => if bse = twiddleSym ∧ o = 16 then 9 else 0 }
        : JState 64) [JInstr.loadSym "r1" twiddleSym]
    s.loadIdx "r1" "idx" 8 = 9 := by
  simp [runBlock, evalInstr, JState.loadIdx, JState.load, JState.get, twiddleSym]

/-! ## 4. `.rodata` table rendering (the `lp_globs` companion)

`Com.toLprogWithRodata` exports `loadSymCom` and attaches a concrete twiddle
table; `LprogAsmPrinter.lprogRodata` (gated on `lp_globs ≠ []`) then renders the
`.section .rodata` block the `leaq twiddles(%rip)` resolves against. -/

/-- A tiny concrete twiddle table (two u64 roots). -/
def twiddleTable : List (BitVec 64) := [7, 9]

/-- The `Lprog` exporting `loadSymCom` with its twiddle table populated. -/
def loadSymLprog : Lprog :=
  Com.toLprogWithRodata loadSymCom "ntt_loadsym" twiddleSym twiddleTable

/-- The exported `Lprog` declares the twiddle table in its globals: `lp_globs`
    is non-empty (so the `.rodata` guard trips) and `lp_glob_names` carries one
    `(twiddleSym, 8, value)` entry per table word. -/
theorem loadSymLprog_globs :
    loadSymLprog.lp_glob_names = [(twiddleSym, 8, 7), (twiddleSym, 8, 9)]
      ∧ loadSymLprog.lp_globs ≠ [] := by
  refine ⟨rfl, ?_⟩
  decide

/-- The `.rodata` block for the exported program renders the named `.quad`
    table — the read-only data section the symbol-base load reads. (The default
    `Com.toLprog` path, with empty globals, would render `""` here; populating
    the table is what produces the section.) -/
theorem loadSymLprog_rodata :
    LprogAsmPrinter.lprogRodata loadSymLprog
      = "\t.section .rodata\n\t.align 8\n\t.type twiddles, @object\n" ++
        "\t.size twiddles, 16\ntwiddles:\n\t.quad 7\n\t.quad 9\n" := by
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.JasminLoadSymExport
