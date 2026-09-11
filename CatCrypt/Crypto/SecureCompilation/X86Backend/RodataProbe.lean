/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# `.rodata` global table + RIP-relative base load: the NTT-twiddle seam (probe)

A fully-emitted NTT indexes a precomputed twiddle/root-of-unity table that lives
in the read-only data segment. This module exercises the one missing owned-backend
primitive that enables it:

* a **`.rodata` u64 table** emitted as `.section .rodata` + `<name>:` + a `.quad`
  list (`LprogAsmPrinter.renderRodata`), and
* a **RIP-relative base load** `leaq <name>(%rip), %reg`
  (`AsmPrinter.JInstr.loadSym`, semantics `JasminModel.evalInstr`), which puts the
  table base into a register so the existing register-indexed gather
  (`JInstr.loadMemIdx`, `mov (%base,%idx,scale),%dst`, #581) can read `table[i]`.

## The demo kernel `table_get(out, inp)`

SysV ABI: `out → %rdi`, `inp → %rsi` (`extern void table_get(uint64_t *out,
const uint64_t *inp)`). The body, on the fixed table
`rodata_probe_tbl = [10,20,30,40,50,60,70,80]`:

```
  i    := inp[0]                       # loadMem  i, inp, 0
  base := &rodata_probe_tbl            # loadSym  base, "rodata_probe_tbl"
  v    := rodata_probe_tbl[i]          # loadMemIdx v, base, i, 8   (SIB gather)
  out[0] := v                          # storeMem out, 0, v
```

so `out[0] = table[inp[0]]`.

## What is verified in Lean vs trusted to the orchestrator KAT

* **Verified (value, in Lean)** — `tableGet_value`: through the full
  `runBlock`/`evalInstr` chain, on a state seeding `inp[0] = i` and the symbol
  bank `mem "rodata_probe_tbl" (8·k) = table[k]`, the kernel writes
  `out[0] = table[i]` for each `i ∈ {0,…,7}`. The `loadSym` arm aliases the base
  register's memory bank onto the symbol bank, so the indexed gather reads the
  table — a real in-Lean denotation, not a shape check.
* **Verified (printer shape)** — `tableGet_*`: the emitted `.s` carries the
  `table_get` leaf, a `.section .rodata` block, the table label and its eight
  `.quad` values, a `leaq …(%rip), …` RIP-relative base load, the SIB gather
  `(…, …, 8)`, and **no** `UNHANDLED`/`UNALLOCATED` sentinel — all `native_decide`.
* **Trusted to the orchestrator's assemble+run KAT** (`bench/fhe_ntt_compare/
  rodata_probe_kat.c` + `gas`/`gcc`): that `gas`/`ld` resolve `leaq
  rodata_probe_tbl(%rip)` to the address of the `.rodata` `rodata_probe_tbl:`
  block (RIP-relative addressing / PIE/PIC correctness), and that the hardware SIB
  load `(%base,%idx,8)` reads the 8 table words. These are the standard `.rodata`
  + RIP-relative trust the backend's other RIP-relative leaves already carry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RodataProbe

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn allocOverflow)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (RodataTable renderRodata)

/-! ## 1. The fixed `.rodata` table and the kernel body -/

/-- The probe table: eight u64 words `[10, 20, …, 80]`. -/
def probeTable : List Nat := [10, 20, 30, 40, 50, 60, 70, 80]

/-- The `.rodata` symbol name (matches the emitted label and the `loadSym`
    argument). -/
def tableSym : String := "rodata_probe_tbl"

/-- `table_get` body: `i := inp[0]; base := &tbl; v := tbl[i]; out[0] := v`. Uses
    the RIP-relative symbol base load (`loadSym`) and the register-indexed gather
    (`loadMemIdx`, scale 8 = u64). -/
def tableGetBody : List (JInstr 64) :=
  [ .loadMem "i" "inp" 0          -- i := inp[0]
  , .loadSym "base" tableSym      -- base := &rodata_probe_tbl  (leaq sym(%rip))
  , .loadMemIdx "v" "base" "i" 8  -- v := rodata_probe_tbl[i]    (SIB gather)
  , .storeMem "out" 0 (.reg "v")  -- out[0] := v
  ]

/-! ## 2. Value semantics through `runBlock` (the in-Lean KAT)

We seed a machine state with `inp[0] = i` and the symbol memory bank
`mem tableSym (8·k) = table[k]` (what the `.rodata` `.quad` list lays down), run
the body, and read `out[0]`. -/

/-- Seed state for `table_get` on lookup index `i`: `inp[0] = i`, and the symbol
    bank `tableSym` holds the eight table words at byte offsets `0, 8, …, 56`. -/
def seedProbe (i : Nat) : JState 64 :=
  { regs := fun _ => 0
    flags := {}
    mem := fun base off =>
      if base = "inp" then (if off = 0 then BitVec.ofNat 64 i else 0)
      else if base = tableSym then
        (probeTable.zipIdx.foldl
          (fun acc (vk : Nat × Nat) =>
            let (v, k) := vk
            if off = (8 * k : Nat) then BitVec.ofNat 64 v else acc) 0)
      else 0 }

/-- **The in-Lean value KAT.** For each lookup index `i ∈ {0,…,7}`, running the
    `table_get` body on `seedProbe i` writes `out[0] = table[i]` — through the full
    `runBlock`/`evalInstr` chain (`loadMem`, `loadSym` aliasing the base bank onto
    the symbol bank, `loadMemIdx` SIB gather, `storeMem`). -/
theorem tableGet_value :
    (∀ i ∈ [0,1,2,3,4,5,6,7],
      ((runBlock (seedProbe i) tableGetBody).load "out" 0).toNat
        = probeTable.getD i 0) := by
  native_decide

/-! ## 3. AT&T emission (no jasminc): the function body + the `.rodata` block -/

/-- Pin `out → %rdi`, `inp → %rsi` (the SysV argument registers); `i`, `base`, `v`
    take the free pool. -/
def tableGetAlloc : GpAlloc := allocGp [("out", "%rdi"), ("inp", "%rsi")] tableGetBody

/-- The rendered `table_get` body lines under `tableGetAlloc`. -/
def tableGetBodyAsm : List String := renderBlockBody tableGetAlloc tableGetBody

/-- The full `table_get` leaf function (`.text` + label + body + `ret`), with the
    `.rodata` `rodata_probe_tbl` table appended. `out`/`inp` are already in
    `%rdi`/`%rsi` on entry, so there is no argument-load prologue and no
    result-store epilogue beyond `ret` (the body's `storeMem out` writes the
    result). -/
def tableGetAsm : String :=
  renderLeafFn "table_get" [] tableGetBodyAsm []
    ++ renderRodata [(tableSym, probeTable)]

/-! ## 4. Shape checks on the emitted `.s` (native_decide) -/

/-- Substring test (Lean core lacks `String.isInfixOf`). -/
def hasSub (hay needle : String) : Bool :=
  needle.isEmpty || (hay.splitOn needle).length > 1

/-- The free pool covers every non-pinned name (no `<UNALLOCATED>`). -/
theorem tableGet_no_overflow :
    allocOverflow [("out", "%rdi"), ("inp", "%rsi")] tableGetBody = none := by
  native_decide

/- The emitted `.s` carries the `table_get` leaf label. -/
#guard (hasSub tableGetAsm "table_get")

/- The emitted `.s` carries a `.section .rodata` block. -/
#guard (hasSub tableGetAsm ".section .rodata")

/- The emitted `.s` carries the table label `rodata_probe_tbl:`. -/
#guard (hasSub tableGetAsm "rodata_probe_tbl:")

/- The emitted `.s` carries the eight `.quad` table values. -/
#guard (hasSub tableGetAsm "\t.quad 10") && (hasSub tableGetAsm "\t.quad 80")

/- The emitted `.s` carries a RIP-relative base load `leaq …(%rip), …`. -/
#guard (hasSub tableGetAsm "\tleaq rodata_probe_tbl(%rip), ")

/- The emitted `.s` carries the SIB register-indexed gather `(…, …, 8)`. -/
#guard (hasSub tableGetAsm ", 8)")

/- No unhandled-op / unallocated-register sentinel in the emitted `.s`. -/
#guard !(hasSub tableGetAsm "UNHANDLED") && !(hasSub tableGetAsm "UNALLOCATED")

/-! ## 5. Emit driver -/

/-- Write the owned-backend `.s` for the `.rodata`-probe kernel into the
    `bench/fhe_ntt_compare/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/fhe_ntt_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/rodata_probe.s") tableGetAsm
  IO.println "WROTE bench/fhe_ntt_compare/gen/rodata_probe.s"
  IO.println "  (.rodata u64 table + leaq sym(%rip) base load + SIB gather;"
  IO.println "   table_get(out, inp): out[0] = rodata_probe_tbl[inp[0]],"
  IO.println "   rodata_probe_tbl = [10,20,30,40,50,60,70,80]; OWNED x86, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.RodataProbe
