/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# `.rodata` constants for the 256-bit `YmmSymInstr` layer

`VIR/YmmAsmPrint` gives a 256-bit kernel the operand form that *references* a
`.rodata` constant (`YmmSymMem`, printed `sym(%rip)`). This module supplies the
other half: the `.rodata` block that *defines* the symbol, and the check pairing
each reference with a definition.

## What is reused

The `.rodata` renderer is `LprogAsmPrinter.renderRodata` — the one the NTT
twiddle-table seam uses (`X86Backend/RodataProbe`). Its table type is a name plus
a list of u64 words emitted as `.quad`s, which covers the 256-bit case directly: a
256-bit constant is four words, a `vpbroadcastq` source is one. The builders here
are the two layouts, not a second renderer.

`renderRodata` declares `.align 8`. Both instruction arms of `YmmSymInstr` read
unaligned (`vmovdqu`, `vpbroadcastq`), so an 8-byte-aligned 256-bit constant is
correct, and 32-byte alignment would only be a store-forwarding/split-load
performance choice. An arm that required natural alignment (`vmovdqa`) would need
a `.align 32` renderer; the 512-bit path uses the constant pool `VIR.RodataPool`, whose
entries carry their own alignment (`.p2align 6` for a 64-byte constant).

## What the reference/definition pairing establishes

`ymmSymRodataViolations` returns the violated conditions: a symbol read with no
defining table, a duplicate label, an empty table.
`ymmSymRefs_subset_of_violations_nil` turns an empty violation list into
inclusion of the read symbols in the defined names.

That is a link-level property. It does not say the constant holds the value the
kernel's specification assumes — the `.quad` list is the definition, and nothing
here or in `YmmOp.denote` (a function on register values) constrains it. The
scalar tier has a value-level counterpart, `RodataProbe.tableGet_value`, which
seeds the symbol's memory bank and runs `runBlock`; the 256-bit instruction layer
has no machine model to seed, so the value of a constant rests on the emitted
`.quad` list and the external byte KAT of the kernel that reads it.

Like `Keccak4WayWholePermVpackZmmEmit.checkWholePerm`, the check is meant to run
in a kernel's emit driver, which refuses to write when it is non-empty:
kernel-reducing a large block list at elaboration time exhausts memory. The
witness block at the end of this module is small enough to `#guard`.

## Main definitions

* `ymmLaneBroadcast`, `ymmBroadcastTable`, `ymmQwordTable`, `ymmRodataDefs`: the
  layout builders over `LprogAsmPrinter.renderRodata`, which composes at 256 bits —
  four u64 words per full-width constant, one per `vpbroadcastq` source. `.align 8`
  suits the two load arms, both of which read unaligned; a `vmovdqa` arm would want
  an `.align 32` sibling
* `ymmSymRodataChecks`, `ymmSymRodataViolations`: the conditions on a symbol table —
  a reference with no defining label, a duplicate label, an empty table

## Main results

* `ymmSymRefs_subset_of_violations_nil`: an empty violation list gives the fact the
  check exists for, that every symbol a block references has a defining label
* `ymmSymsDefined_of_violations_nil`, `ymmSymsDefined_iff`: that inclusion as a
  predicate, and its characterisation
* `ymmLaneBroadcast_length`: a broadcast constant occupies the four lanes

A passing check says the reference resolves, not that the label holds the intended
words. `RodataProbe.tableGet_value` is the value-level statement at the scalar tier;
there is no 256-bit counterpart, so contents rest on the emitted `.quad` list and
the external byte KAT.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Ymm256RodataConst

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (RodataTable renderRodata)

/-! ## 1. The two constant layouts -/

/-- A 256-bit constant whose four 64-bit lanes all hold `v`, as the four `.quad`
    words `renderRodata` emits. This is the layout a `vmovdqu sym(%rip)` load
    reads whole. -/
def ymmLaneBroadcast (v : Nat) : List Nat := List.replicate 4 v

/-- A lane-broadcast constant is 4 words = 32 bytes = one `%ymm`. -/
theorem ymmLaneBroadcast_length (v : Nat) : (ymmLaneBroadcast v).length = 4 := by
  simp [ymmLaneBroadcast]

/-- A `.rodata` table holding the lane-broadcast constant `v` under `name`. -/
def ymmBroadcastTable (name : String) (v : Nat) : RodataTable :=
  (name, ymmLaneBroadcast v)

/-- A `.rodata` table holding the single 64-bit word `v` under `name` — the
    source form of `vpbroadcastq sym(%rip), %ymm`, which replicates it across the
    four lanes at load time. -/
def ymmQwordTable (name : String) (v : Nat) : RodataTable := (name, [v])

/-- The defined label names of a `.rodata` table list. -/
def ymmRodataDefs (tables : List RodataTable) : List String := tables.map Prod.fst

/-! ## 2. Pairing every reference with a definition -/

/-- The conditions a `(block, tables)` pair must satisfy, each with its
    description: every symbol the block reads has a defining table, no label is
    defined twice, and no table is empty. -/
def ymmSymRodataChecks (block : List YmmSymInstr) (tables : List RodataTable) :
    List (String × Bool) :=
  [ ("every symbol read has a defining .rodata table",
      ymmSymsDefined block (ymmRodataDefs tables))
  , ("no .rodata label defined twice",
      (ymmRodataDefs tables).eraseDups.length == (ymmRodataDefs tables).length)
  , ("no empty .rodata table", tables.all (fun t => !t.2.isEmpty)) ]

/-- The violated conditions of `ymmSymRodataChecks` — empty when the pair is well
    formed. An emit driver refuses to write while this is non-empty. -/
def ymmSymRodataViolations (block : List YmmSymInstr) (tables : List RodataTable) :
    List String :=
  ((ymmSymRodataChecks block tables).filter (fun c => !c.2)).map Prod.fst

/-- No violations implies the symbol-definition check passed. -/
theorem ymmSymsDefined_of_violations_nil {block : List YmmSymInstr}
    {tables : List RodataTable} (h : ymmSymRodataViolations block tables = []) :
    ymmSymsDefined block (ymmRodataDefs tables) = true := by
  cases hb : ymmSymsDefined block (ymmRodataDefs tables) with
  | true => rfl
  | false => simp [ymmSymRodataViolations, ymmSymRodataChecks, hb] at h

/-- No violations implies every `.rodata` symbol the block reads is defined by one
    of the tables, so the render links. -/
theorem ymmSymRefs_subset_of_violations_nil {block : List YmmSymInstr}
    {tables : List RodataTable} (h : ymmSymRodataViolations block tables = []) :
    ∀ s ∈ ymmSymRefs block, s ∈ ymmRodataDefs tables :=
  (ymmSymsDefined_iff _ _).mp (ymmSymsDefined_of_violations_nil h)

/-! ## 3. Witness: a block reading two constants, with their definitions

A three-instruction block that loads a lane-broadcast mask whole, broadcasts a
single-qword mask, and ands them into a register, together with the two tables
defining the symbols it reads. Small enough for compile-time `#guard`s on both
the rendered text and the pairing check. -/

/-- The two `.rodata` tables of the witness: a 4-lane `2^26 - 1` mask and a
    single-qword `2^32 - 1` mask. -/
def witnessTables : List RodataTable :=
  [ ymmBroadcastTable "ymm_probe_M26" (2 ^ 26 - 1)
  , ymmQwordTable "ymm_probe_MASK32" (2 ^ 32 - 1) ]

/-- The witness block: load the 256-bit mask, broadcast the qword mask, `vpand`
    them. -/
def witnessBlock : List YmmSymInstr :=
  [ .yloadSym "%ymm1" (ymmSym "ymm_probe_M26")
  , .ybcastqSym "%ymm2" (ymmSym "ymm_probe_MASK32")
  , .plain (.alu .vpand "%ymm3" ["%ymm1", "%ymm2"]) ]

/-- The witness `.s`: the framed function over the symbol layer plus the
    `.rodata` block defining both symbols. -/
def witnessAsm : String :=
  renderYmmSymFundefText "ymm_probe_mask" witnessBlock ++ renderRodata witnessTables

/-- A block reading a symbol no table defines (the negative case for the pairing
    check). -/
def witnessBlockUndefined : List YmmSymInstr :=
  [ .yloadSym "%ymm1" (ymmSym "ymm_probe_M25") ]

/-! ### Pins -/

/- The witness pair is well formed. -/
#guard ymmSymRodataViolations witnessBlock witnessTables == []

/- The check fires on a reference with no defining table. -/
#guard ymmSymRodataViolations witnessBlockUndefined witnessTables
  == ["every symbol read has a defining .rodata table"]

/- The check fires on a label defined twice. -/
#guard ymmSymRodataViolations witnessBlock (witnessTables ++ witnessTables)
  == ["no .rodata label defined twice"]

/- The check fires on an empty table. -/
#guard ymmSymRodataViolations witnessBlock (witnessTables ++ [("ymm_probe_z", [])])
  == ["no empty .rodata table"]

/- The witness reads exactly the two symbols the tables define. -/
#guard ymmSymRefs witnessBlock == ymmRodataDefs witnessTables

/- The three body lines: the two symbol-sourced loads and the register `vpand`. -/
#guard renderYmmSymBlockBody witnessBlock ==
  [ "\tvmovdqu\tymm_probe_M26(%rip), %ymm1"
  , "\tvpbroadcastq\tymm_probe_MASK32(%rip), %ymm2"
  , "\tvpand\t%ymm2, %ymm1, %ymm3" ]

/- The `.rodata` block: the section directive, then per table the alignment, the
    object directives, the label, and the `.quad` words. -/
#guard renderRodata witnessTables ==
  "\t.section .rodata\n\t.align 8\n\t.type ymm_probe_M26, @object\n" ++
  "\t.size ymm_probe_M26, 32\nymm_probe_M26:\n\t.quad 67108863\n\t.quad 67108863\n" ++
  "\t.quad 67108863\n\t.quad 67108863\n\t.align 8\n" ++
  "\t.type ymm_probe_MASK32, @object\n\t.size ymm_probe_MASK32, 8\n" ++
  "ymm_probe_MASK32:\n\t.quad 4294967295\n"

/- The witness `.s` carries the function label and both `.rodata` labels. -/
#guard (witnessAsm.splitOn "ymm_probe_mask:").length == 2
  && (witnessAsm.splitOn "ymm_probe_M26:").length == 2
  && (witnessAsm.splitOn "ymm_probe_MASK32:").length == 2

end CatCrypt.Crypto.SecureCompilation.X86Backend.Ymm256RodataConst
