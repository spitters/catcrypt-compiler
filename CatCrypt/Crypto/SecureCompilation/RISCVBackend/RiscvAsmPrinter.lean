/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvLowering
public meta import CatCrypt.Crypto.Optimizer.GenericRegAlloc
public import CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-!
# GAS RV64 asm printer for the scalar RISC-V machine instructions

`ARMBackend.ArmAsmPrinter` prints the A64 scalar subset to GAS AArch64 asm; this
is its **RISC-V RV64** counterpart: it prints a `RiscvModel.RInst` block — the
scalar 32-bit-word GP-ALU set of `RiscvModel.lean`, the same set the rotate macro
lowers to via `RiscvLowering.lowerRBlock` / `riscvBlock_lowering_denote` — to
GAS-syntax RV64 assembly text (`addw`/`subw`/`and`/`or`/`xor`/`slliw`/`srliw`/
`mv`, ABI register operands), to be assembled by `riscv64-linux-gnu-as`.

## Where the trust boundary is (precise — identical posture to the x86/ARM printers)

The **verified artifact** is `ROp → runRBlock` (the `RiscvLowering.lowerRBlock`
pass + `riscvBlock_lowering_denote`, down to the differential-validated
`evalRInst` semantics, including the verified rotate macro `rotl_run_denote`).
This printer + `as` is the *thin* trust boundary, because the printer is a
**syntactic** map (one `RInst` arm → one GAS mnemonic line, fixed register
assignment, no instruction selection / scheduling / optimization), and `as`
performs only assembly. So the trusted edge is: (the printer is correct GAS RV64
syntax for each mnemonic) ∧ (`as` encodes each mnemonic per the RISC-V ISA). The
machine-code byte encoder + `decode(encode)=i` against `riscv/sail-riscv` are
`RiscvEncoder` and `SailRiscvDecoder` (the RV64 analogue of `SailX86Decoder`).

## Register allocation

An `RInst` block uses SSA-style string names. `allocGp` (linear-scan with
last-use liveness, the `ARMBackend.allocGp` analogue) assigns each name an RV64
ABI register. The ChaCha quarter-round's live set is the 4 state words + one
rotate scratch, well under the temp pool, so it never spills. `reserved` names
(args/outputs) are pinned to the argument registers `a0..` for the whole
function (matching the RV64 calling convention `a0–a7`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. Register allocation: name → RV64 ABI register -/

/-- The (dst, srcs) of an `RInst` — its written name and read names. -/
def rinstDstSrcs : RInst → String × List String
  | .addw d a b => (d, [a, b])
  | .subw d a b => (d, [a, b])
  | .and  d a b => (d, [a, b])
  | .or   d a b => (d, [a, b])
  | .xor  d a b => (d, [a, b])
  | .slliw d a _ => (d, [a])
  | .srliw d a _ => (d, [a])
  | .roriw d a _ => (d, [a])
  | .mv   d s    => (d, [s])

/-- A register assignment: an association list name → ABI register (e.g.
    `"a"` → `"a0"`). -/
abbrev GpAlloc := List (String × String)

/-- The ABI register a name is assigned. The zero register `zero`/`x0` maps to
    `zero`; an unmapped name yields the explicit `<UNALLOCATED:n>` sentinel (so an
    over-budget block is rejected by `as` rather than silently aliasing — the
    same discipline as the x86/ARM `regOf`). -/
def gpOf (alloc : GpAlloc) (n : String) : String :=
  if n = "zero" ∨ n = "x0" then "zero"
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- The index of the last instruction that *reads* `n` (its last use), or 0:
    `GenericRegAlloc.lastReadIdx` at `rinstDstSrcs`. -/
abbrev gpLastUse (block : List RInst) (n : String) : Nat :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.lastReadIdx rinstDstSrcs block n

/-- The general-purpose register pool we allocate from: the RV64 caller-saved
    argument + temporary registers `a0 … a7`, `t0 … t6` (RISC-V psABI: `a0–a7`
    args/results, `t0–t6` temporaries). 15 registers, ample for a quarter-round
    plus one rotate scratch. -/
def gpPool : List String :=
  (List.range 8).map (fun i => "a" ++ toString i) ++
  (List.range 7).map (fun i => "t" ++ toString i)

/-- Linear-scan allocation over the GP pool. `reserved` names (args/outputs) are
    pinned to `a0..` for the whole function and never freed; the remaining pool
    is recycled by last-use liveness. The RV64 analogue of `ARMBackend.allocGp`: the
    printer scan `GenericRegAlloc.lastReadScan` at `rinstDstSrcs`, with the `reserved`
    names pinned to `a0..` and the pool after them. -/
def allocGp (reserved : List String) (block : List RInst) : GpAlloc :=
  CatCrypt.Crypto.Optimizer.GenericRegAlloc.lastReadScan rinstDstSrcs
    (reserved.zipIdx.map (fun (n, i) => (n, "a" ++ toString i)))
    (gpPool.drop reserved.length) reserved block

/-! ## 2. The GAS mnemonic printer (one line per `RInst`)

GAS RV64 order is `op rd, rs1, rs2` (dst first); the shifts take the immediate
last (`slliw rd, rs1, imm`); `mv rd, rs`. -/

/-- Print one `RInst` to its GAS RV64 asm line (ABI registers). -/
def renderRInst (alloc : GpAlloc) : RInst → String
  | .addw d a b => "\taddw " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .subw d a b => "\tsubw " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .and  d a b => "\tand "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .or   d a b => "\tor "   ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .xor  d a b => "\txor "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .slliw d a imm => "\tslliw " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ toString imm.val
  | .srliw d a imm => "\tsrliw " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ toString imm.val
  | .roriw d a imm => "\troriw " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ toString imm.val
  | .mv   d s     => "\tmv "   ++ gpOf alloc d ++ ", " ++ gpOf alloc s

/-- Print a whole block's instruction lines (one per `RInst`). -/
def renderRBlockBody (alloc : GpAlloc) (block : List RInst) : List String :=
  block.map (renderRInst alloc)

/-! ### 2b. The branch / control-flow printer (the looped-emission lines)

A `RBranch.label` renders as the bare `.L<name>:` line; a `bcc` as the GAS B-type
branch `b<cmp> rs1, rs2, .L<name>` (e.g. `bne ctr, zero, .Ltop`, the counter
back-edge); a `j` as the `j .L<name>` unconditional jump. The RV64 analogue of
`ARMBackend.renderABranch`. -/

/-- The GAS mnemonic for a B-type branch comparison. -/
def renderBCmp : BCmp → String
  | .beq => "beq"
  | .bne => "bne"
  | .blt => "blt"
  | .bge => "bge"
  | .bltu => "bltu"
  | .bgeu => "bgeu"

/-- Print one `RBranch` to its GAS RV64 asm line. A `label` renders as the bare
    `.L<name>:` line; `bcc` as `b<cmp> rs1, rs2, .L<name>`; `j` as `j .L<name>`. -/
def renderRBranch (alloc : GpAlloc) : RBranch → String
  | .label l       => ".L" ++ l ++ ":"
  | .bcc c r1 r2 l => "\t" ++ renderBCmp c ++ " " ++ gpOf alloc r1 ++ ", "
                        ++ gpOf alloc r2 ++ ", .L" ++ l
  | .j l           => "\tj .L" ++ l

/-! ## 3. A leaf-function renderer (GAS RV64)

Wraps the verified straight-line body in a minimal RV64 leaf prologue: the
quarter-round takes its four state words in `a0–a3` (args), runs the body, and
returns the four results in `a0–a3` (the caller reads them back). The body uses
no stack (the live set fits in registers), so the prologue is just the
`.text`/`.globl`/label/`.type` scaffolding and a `ret`. This scaffolding is
*trusted* (outside the verified body), exactly the x86/ARM `renderLeafFn`
posture. -/

/-- Render a complete GAS RV64 leaf function: `.text` directives, label, the
    lowered+rendered body, and `ret`. `name` is the symbol; `reserved` pins the
    arg/result registers; `body` is the source `ROp` block. -/
def renderLeafFn (name : String) (reserved : List ROp → List String)
    (body : List ROp) : String :=
  let lowered := lowerRBlock body
  let resv := reserved body
  let alloc := allocGp resv lowered
  let header :=
    [ "\t.text"
    , "\t.globl " ++ name
    , "\t.type " ++ name ++ ", @function"
    , name ++ ":" ]
  let lines := renderRBlockBody alloc lowered
  String.intercalate "\n" (header ++ lines ++ ["\tret"]) ++ "\n"

/-- The ChaCha quarter-round leaf: state words `a b c d` are the args, pinned to
    `a0–a3`; the rotate scratch `t` and the body are `qrBlk`; results come back in
    the same arg registers. -/
def qrLeafAsm : String :=
  renderLeafFn "chacha_qr_rv64" (fun _ => ["a", "b", "c", "d"])
    (qrBlk "a" "b" "c" "d" "t")

/-! ## 4. Printer sanity pins

The rendered lines match the expected GAS RV64 text for representative ops (the
syntactic half of the trust boundary, audited against `as` mnemonic syntax). -/

/-- `addw a2, a0, a1` ≡ `a2 = a0 + a1` (dst first). -/
example :
    renderRInst [("d","a2"),("a","a0"),("b","a1")] (.addw "d" "a" "b")
      = "\taddw a2, a0, a1" := by native_decide

/-- `xor a2, a0, a1` ≡ `a2 = a0 ^ a1`. -/
example :
    renderRInst [("d","a2"),("a","a0"),("b","a1")] (.xor "d" "a" "b")
      = "\txor a2, a0, a1" := by native_decide

/-- `slliw t0, a0, 16` — the left-shift half of the rotate-left-16 macro. -/
example :
    renderRInst [("t","t0"),("a","a0")] (.slliw "t" "a" 16)
      = "\tslliw t0, a0, 16" := by native_decide

/-- The arg-pinned quarter-round allocates `a b c d` to `a0 a1 a2 a3` and emits
    the first instruction as `addw a0, a0, a1` (`a += b`). -/
example :
    (renderRBlockBody
      (allocGp ["a","b","c","d"] (lowerRBlock (qrBlk "a" "b" "c" "d" "t")))
      (lowerRBlock (qrBlk "a" "b" "c" "d" "t"))).head?
      = some "\taddw a0, a0, a1" := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
