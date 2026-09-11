/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering64

/-!
# GAS RV64 asm printer for the 64-bit bignum `RInst64` (#549)

`RiscvAsmPrinter.lean` prints the scalar 32-bit-word `RInst` block; this is its
**64-bit bignum** counterpart — it prints a `RiscvModel64.RInst64` block
(`add`/`sub`/`sltu`/`and`/`or`/`xor`/`mul`/`mulhu`/`li`/`mv`, ABI register
operands) to GAS RV64 assembly text, to be assembled by `riscv64-linux-gnu-as`.
The 64-bit ops use the **full-register** mnemonics (`add`, not `addw`), and the
M-extension `mul`/`mulhu` (so the assembled object targets `rv64gc`, which
includes `M`).

The trust boundary is identical to the 32-bit printer: the verified artifact is
`ROp64 → runRBlock64` (`lowerRBlock64` + `riscvBlock64_lowering_denote`, down to
the differential-validated `evalRInst64` semantics, including the SLTU
carry-synthesis macros). This printer + `as` is the thin syntactic edge; the
byte-level encoder + `decode(encode)=i` against sail-riscv is in
`RiscvEncoder64.lean`/`SailRiscvDecoder64.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. The (dst, srcs) of a 64-bit instruction and the GP allocator -/

/-- The (dst, srcs) of an `RInst64`. -/
def rinst64DstSrcs : RInst64 → String × List String
  | .add d a b => (d, [a, b])
  | .sub d a b => (d, [a, b])
  | .sltu d a b => (d, [a, b])
  | .and  d a b => (d, [a, b])
  | .or   d a b => (d, [a, b])
  | .xor  d a b => (d, [a, b])
  | .mul  d a b => (d, [a, b])
  | .mulhu d a b => (d, [a, b])
  | .li   d _   => (d, [])
  | .mv   d s   => (d, [s])
  | .srli d a _ => (d, [a])
  | .slli d a _ => (d, [a])

/-- A register assignment (name → ABI register). -/
abbrev GpAlloc64 := List (String × String)

/-- The ABI register a name is assigned. `zero`/`x0` map to `zero`; an unmapped
    name yields the `<UNALLOCATED:n>` sentinel (so an over-budget block is
    rejected by `as`, never silently aliased). -/
def gpOf64 (alloc : GpAlloc64) (n : String) : String :=
  if n = "zero" ∨ n = "x0" then "zero"
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- The index of the last instruction that *reads* `n`, or 0. -/
def gpLastUse64 (block : List RInst64) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (i, idx) =>
    if (rinst64DstSrcs i).2.contains n then idx else acc) 0)

/-- The GP pool we allocate the 64-bit bignum body from: the caller-saved
    `a0..a7`, `t0..t6`, plus the callee-saved `s2..s11` (the bignum body has a
    wider live set than the ChaCha QR, so the saved registers are needed; the
    leaf renderer pushes/pops them as trusted prologue scaffolding). 25 GP
    registers. -/
def gpPool64 : List String :=
  (List.range 8).map (fun i => "a" ++ toString i) ++
  (List.range 7).map (fun i => "t" ++ toString i) ++
  ((List.range 10).map (fun i => "s" ++ toString (i + 2)))

/-- Linear-scan allocation over the 64-bit GP pool with last-use liveness.
    `reserved` names (args/outputs) are pinned to `a0..` and never freed; the rest
    of the pool is recycled by last use. The 64-bit analogue of `allocGp`. -/
def allocGp64 (reserved : List String) (block : List RInst64) : GpAlloc64 :=
  let nres := reserved.length
  let pinned : GpAlloc64 := reserved.zipIdx.map (fun (n, i) => (n, "a" ++ toString i))
  let pool0 : List String := gpPool64.drop nres
  let step : (GpAlloc64 × List String) → (RInst64 × Nat) → (GpAlloc64 × List String) :=
    fun (alloc, free) (instr, idx) =>
      let (dst, _) := rinst64DstSrcs instr
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := (rinst64DstSrcs instr).2.filter (fun s =>
        ¬ reserved.contains s ∧ gpLastUse64 block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool0)
  alloc

/-! ## 2. The GAS mnemonic printer (one line per `RInst64`)

GAS RV64 order is `op rd, rs1, rs2` (dst first); `li rd, imm`; `mv rd, rs`. -/

/-- Print one `RInst64` to its GAS RV64 asm line (ABI registers). -/
def renderRInst64 (alloc : GpAlloc64) : RInst64 → String
  | .add  d a b => "\tadd "  ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .sub  d a b => "\tsub "  ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .sltu d a b => "\tsltu " ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .and  d a b => "\tand "  ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .or   d a b => "\tor "   ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .xor  d a b => "\txor "  ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .mul  d a b => "\tmul "  ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .mulhu d a b => "\tmulhu " ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ gpOf64 alloc b
  | .li   d imm => "\tli "   ++ gpOf64 alloc d ++ ", " ++ toString imm
  | .mv   d s   => "\tmv "   ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc s
  | .srli d a sh => "\tsrli " ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ toString sh
  | .slli d a sh => "\tslli " ++ gpOf64 alloc d ++ ", " ++ gpOf64 alloc a ++ ", " ++ toString sh

/-- Print a whole block's instruction lines (one per `RInst64`). -/
def renderRBlock64Body (alloc : GpAlloc64) (block : List RInst64) : List String :=
  block.map (renderRInst64 alloc)

/-! ## 3. Leaf-function helper: the allocated body lines

The bignum body is rendered register-to-register through `allocGp64`; the emit
file (`bench/riscv_compare`) wraps it in the trusted `ld`/`sd` prologue/epilogue
(reading `x`/`y` into the allocated input registers, writing the result limbs
back), exactly the ARM `addp256` leaf posture. -/

/-- Render the allocated `RInst64` body lines (no prologue) for a fixed
    allocation. -/
def renderAllocBody64 (alloc : GpAlloc64) (block : List RInst64) : List String :=
  renderRBlock64Body alloc block

/-! ## 4. Printer sanity pins -/

/-- `add a2, a0, a1`. -/
example : renderRInst64 [("d","a2"),("a","a0"),("b","a1")] (.add "d" "a" "b")
    = "\tadd a2, a0, a1" := by native_decide

/-- `sltu a3, a2, a0` — the carry-synthesis comparator. -/
example : renderRInst64 [("d","a3"),("a","a2"),("b","a0")] (.sltu "d" "a" "b")
    = "\tsltu a3, a2, a0" := by native_decide

/-- `mulhu a4, a0, a1` — the widening-product high half. -/
example : renderRInst64 [("d","a4"),("a","a0"),("b","a1")] (.mulhu "d" "a" "b")
    = "\tmulhu a4, a0, a1" := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
