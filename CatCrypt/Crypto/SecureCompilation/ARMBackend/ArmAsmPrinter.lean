/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering

/-!
# GAS AArch64 asm printer for the scalar A64 machine instructions (#533)

`Vec128AsmPrinter.lean` prints the XMM packed-u32 subset to AT&T AVX asm; this is
its **AArch64 scalar** counterpart: it prints an `ArmModel.AInst` block — the
scalar 32-bit-`W` GP-ALU set of `ArmModel.lean`, the same set lowered to the A64
machine model by `ArmLowering.lowerABlock` / `armBlock_lowering_denote` — to
GAS-syntax AArch64 assembly text (`add`/`sub`/`and`/`orr`/`eor`/`lsl`/`lsr`/
`ror`/`mov`, `wN` operands), to be assembled by `as`/`clang`.

## Where the trust boundary is (precise — identical posture to the x86 printer)

The **verified artifact** is `AOp → runABlock` (the `ArmLowering.lowerABlock`
pass + `armBlock_lowering_denote`, down to the differential-validated `evalAInst`
semantics). This printer + `as` is the *thin* trust boundary, because the printer
is a **syntactic** map (one `AInst` arm → one GAS mnemonic line, fixed register
assignment, no instruction selection / scheduling / optimization), and `as`
performs only assembly. So the trusted edge is: (the printer is correct GAS
AArch64 syntax for each mnemonic) ∧ (`as` encodes each mnemonic per the Arm ARM).
The machine-code byte encoder + `decode(encode)=i` against `rems-project/sail-arm`
**landed in sub-2** (`ArmEncoder.lean` + `SailArmDecoder.lean`, the A64 analogue
of `SailX86Decoder`): for the whole emitted GP-ALU subset the encoder's words are
proved to decode back to the same instruction, so this printer + `as` is no longer
the only byte-level trust edge.

## Register allocation

An `AInst` block uses SSA-style string names. `allocGp` (linear-scan with
last-use liveness, the `Vec128.allocXmm` analogue) assigns each name a `wN`
(the 32-bit register view). The ChaCha quarter-round's live set is 4 + a couple
of temps, well under the 18 caller-saved GP registers, so it never spills.
`reserved` names (args/outputs) are pinned to the low registers `w0..` for the
whole function (matching the AAPCS64 argument registers `w0–w7`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. Register allocation: name → wN -/

/-- The (dst, srcs) of an `AInst` — its written name and read names. -/
def ainstDstSrcs : AInst → String × List String
  | .add d a b => (d, [a, b])
  | .sub d a b => (d, [a, b])
  | .and d a b => (d, [a, b])
  | .orr d a b => (d, [a, b])
  | .eor d a b => (d, [a, b])
  | .lsl d a _ => (d, [a])
  | .lsr d a _ => (d, [a])
  | .ror d a _ => (d, [a])
  | .mov d s   => (d, [s])

/-- A register assignment: an association list name → "wN". -/
abbrev GpAlloc := List (String × String)

/-- The `wN` register a name is assigned. The zero register `wzr` maps to itself;
    an unmapped name yields the explicit `<UNALLOCATED:n>` sentinel (so an
    over-budget block is rejected by `as` rather than silently aliasing — the
    same discipline as the x86 `regOf`). -/
def gpOf (alloc : GpAlloc) (n : String) : String :=
  if n = "wzr" then "wzr"
  else if n = "xzr" then "xzr"  -- the 64-bit zero register (bignum path, #547)
  else (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- The index of the last instruction that *reads* `n` (its last use), or 0. -/
def gpLastUse (block : List AInst) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (i, idx) =>
    if (ainstDstSrcs i).2.contains n then idx else acc) 0)

/-- The general-purpose register pool we allocate from: the caller-saved
    AArch64 registers `w0 … w17` (AAPCS64: `w0–w7` args/results, `w8` indirect
    result, `w9–w15` temporaries, `w16/w17` IP0/IP1). 18 registers, ample for a
    quarter-round. -/
def gpPool : List String := (List.range 18).map (fun i => "w" ++ toString i)

/-- Linear-scan allocation over the GP pool. `reserved` names (args/outputs) are
    pinned to `w0..` for the whole function and never freed; the remaining pool
    `w<|reserved|>..w17` is recycled by last-use liveness. The A64 analogue of
    `Vec128.allocXmm`. -/
def allocGp (reserved : List String) (block : List AInst) : GpAlloc :=
  let nres := reserved.length
  let pinned : GpAlloc := reserved.zipIdx.map (fun (n, i) => (n, "w" ++ toString i))
  let pool0 : List String := gpPool.drop nres
  let step : (GpAlloc × List String) → (AInst × Nat) → (GpAlloc × List String) :=
    fun (alloc, free) (instr, idx) =>
      let (dst, _) := ainstDstSrcs instr
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := (ainstDstSrcs instr).2.filter (fun s =>
        ¬ reserved.contains s ∧ gpLastUse block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool0)
  alloc

/-! ## 2. The GAS mnemonic printer (one line per `AInst`)

GAS AArch64 order is `op Wd, Wn, Wm` (dst first); the shifts/rotate take the
immediate last with a `#` (`lsl wd, wn, #imm`); `mov wd, wn`. -/

/-- Print one `AInst` to its GAS AArch64 asm line (`wN` registers). -/
def renderAInst (alloc : GpAlloc) : AInst → String
  | .add d a b => "\tadd "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .sub d a b => "\tsub "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .and d a b => "\tand "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .orr d a b => "\torr "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .eor d a b => "\teor "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .lsl d a imm => "\tlsl "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", #" ++ toString imm
  | .lsr d a imm => "\tlsr "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", #" ++ toString imm
  | .ror d a imm => "\tror "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", #" ++ toString imm
  | .mov d s     => "\tmov "  ++ gpOf alloc d ++ ", " ++ gpOf alloc s

/-- Print a whole block's instruction lines (one per `AInst`). -/
def renderABlockBody (alloc : GpAlloc) (block : List AInst) : List String :=
  block.map (renderAInst alloc)

/-! ### 1b. Branch / control-flow renderer (the looped-emission lines, #551)

GAS AArch64 label syntax is `.L<name>:`; the branches are `b .L<name>`,
`b.<cond> .L<name>`, `cbnz wN, .L<name>` / `cbz wN, .L<name>`. The counter
register a `CBNZ` tests is resolved through the same `gpOf` allocation. -/

/-- Print a `BCond` condition suffix (the `b.<cond>` mnemonic tail). -/
def renderBCond : BCond → String
  | .ne => "ne"
  | .eq => "eq"
  | .cc => "cc"
  | .cs => "cs"

/-- Print one `ABranch` to its GAS AArch64 asm line. A `label` renders as the
    bare `.L<name>:` line; `b`/`b.cond` as the (un)conditional branch; `cbnz`/`cbz`
    as the compare-and-branch on the allocated counter register. -/
def renderABranch (alloc : GpAlloc) : ABranch → String
  | .label l        => ".L" ++ l ++ ":"
  | .b l            => "\tb .L" ++ l
  | .bcond c l      => "\tb." ++ renderBCond c ++ " .L" ++ l
  | .cbnz t l       => "\tcbnz " ++ gpOf alloc t ++ ", .L" ++ l
  | .cbz t l        => "\tcbz " ++ gpOf alloc t ++ ", .L" ++ l

/-! ## 3. A leaf-function renderer (GAS AArch64)

Wraps the verified straight-line body in a minimal AAPCS64 leaf prologue: the
quarter-round takes its four state words in `w0–w3` (args), runs the body, and
returns the four results in `w0–w3` (the caller reads them back). The body uses
no stack (the live set fits in registers), so the prologue is just the
`.global`/label/`.type` scaffolding and a `ret`. This scaffolding is *trusted*
(outside the verified body), exactly the x86 `renderLeafFn` posture. -/

/-- Render a complete GAS AArch64 leaf function: `.text` directives, label,
    the lowered+rendered body, and `ret`. `name` is the symbol; `reserved` pins
    the arg/result registers; `block` is the lowered body. -/
def renderLeafFn (name : String) (reserved : List AOp → List String)
    (body : List AOp) : String :=
  let lowered := lowerABlock body
  let resv := reserved body
  let alloc := allocGp resv lowered
  let header :=
    [ "\t.text"
    , "\t.global " ++ name
    , "\t.type " ++ name ++ ", %function"
    , name ++ ":" ]
  let lines := renderABlockBody alloc lowered
  String.intercalate "\n" (header ++ lines ++ ["\tret"]) ++ "\n"

/-- The ChaCha quarter-round leaf: state words `a b c d` are the args, pinned to
    `w0–w3`; the body is `qrBlk`; results come back in the same registers. -/
def qrLeafAsm : String :=
  renderLeafFn "chacha_qr_a64" (fun _ => ["a", "b", "c", "d"])
    (qrBlk "a" "b" "c" "d")

/-! ## 4. Printer sanity pins

The rendered lines match the expected GAS AArch64 text for representative ops
(the syntactic half of the trust boundary, audited against `as` mnemonic
syntax). -/

/-- `add w2, w0, w1` ≡ `w2 = w0 + w1` (dst first). -/
example :
    renderAInst [("d","w2"),("a","w0"),("b","w1")] (.add "d" "a" "b")
      = "\tadd w2, w0, w1" := by native_decide

/-- `eor w2, w0, w1` ≡ `w2 = w0 ^ w1`. -/
example :
    renderAInst [("d","w2"),("a","w0"),("b","w1")] (.eor "d" "a" "b")
      = "\teor w2, w0, w1" := by native_decide

/-- `ror w2, w0, #16` — the rotate-left-16 realized as rotate-right-16. -/
example :
    renderAInst [("d","w2"),("a","w0")] (.ror "d" "a" 16)
      = "\tror w2, w0, #16" := by native_decide

/-- The arg-pinned quarter-round allocates `a b c d` to `w0 w1 w2 w3` and emits
    the first instruction as `add w0, w0, w1` (`a += b`). -/
example :
    (renderABlockBody
      (allocGp ["a","b","c","d"] (lowerABlock (qrBlk "a" "b" "c" "d")))
      (lowerABlock (qrBlk "a" "b" "c" "d"))).head?
      = some "\tadd w0, w0, w1" := by native_decide

/-! ### 4b. Branch-renderer sanity pins (the looped-emission control-flow lines)

The rendered lines match the GAS AArch64 text the assembler accepts for the loop
back-edge shape (`.L<top>: … ; subs <ctr>,<ctr>,#1 ; cbnz <ctr>,.L<top>`). -/

/-- A label renders as the bare `.L<name>:` line. -/
example : renderABranch [] (.label "loop0") = ".Lloop0:" := by native_decide

/-- An unconditional branch renders as `b .L<name>`. -/
example : renderABranch [] (.b "loop0") = "\tb .Lloop0" := by native_decide

/-- A conditional back-edge renders as `b.ne .L<name>`. -/
example : renderABranch [] (.bcond .ne "loop0") = "\tb.ne .Lloop0" := by native_decide

/-- The counter back-edge `cbnz w9, .L<name>` resolves the counter register
    through the allocation. -/
example : renderABranch [("ctr","w9")] (.cbnz "ctr" "loop0")
    = "\tcbnz w9, .Lloop0" := by native_decide

/-! ## 5. The 64-bit bignum/field GAS printer (#547)

The `BInst` (`X`-register) counterpart of `renderAInst`. GAS order is `op Xd, Xn,
Xm` (dst first); `CSEL` takes the condition last (`csel Xd, Xn, Xm, cc`); `MOVZ`/
`MOVK` take the `#imm` (and `LSL #(16·hw)` for `MOVK`). The register names are
resolved through the same `gpOf` allocation (now an `xN` assignment); `gpOf`
passes the 64-bit zero register `xzr` through. -/

/-- Print the condition suffix of a `CSEL`. -/
def renderACond : ACond → String
  | .cc => "cc"
  | .cs => "cs"

/-- Print one `BInst` to its GAS AArch64 asm line (`xN` registers). -/
def renderBInst (alloc : GpAlloc) : BInst → String
  | .add d a b => "\tadd "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .sub d a b => "\tsub "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .adds d a b => "\tadds " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .adcs d a b => "\tadcs " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .adc d a b => "\tadc "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .subs d a b => "\tsubs " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .sbcs d a b => "\tsbcs " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .sbc d a b => "\tsbc "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .mul d a b => "\tmul "  ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .umulh d a b => "\tumulh " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .and d a b => "\tand " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .orr d a b => "\torr " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .eor d a b => "\teor " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", " ++ gpOf alloc b
  | .csel d a b c => "\tcsel " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", "
                       ++ gpOf alloc b ++ ", " ++ renderACond c
  | .movz d imm16 => "\tmovz " ++ gpOf alloc d ++ ", #" ++ toString imm16
  | .movk d imm16 hw => "\tmovk " ++ gpOf alloc d ++ ", #" ++ toString imm16
                          ++ ", lsl #" ++ toString (hw * 16)
  | .mov d s => "\tmov " ++ gpOf alloc d ++ ", " ++ gpOf alloc s
  | .lsr d a imm => "\tlsr " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", #" ++ toString imm
  | .lsl d a imm => "\tlsl " ++ gpOf alloc d ++ ", " ++ gpOf alloc a ++ ", #" ++ toString imm

/-- Print a whole 64-bit block's instruction lines. -/
def renderBBlockBody (alloc : GpAlloc) (block : List BInst) : List String :=
  block.map (renderBInst alloc)

/-- The (dst, srcs) of a `BInst` — for register allocation of bignum blocks. -/
def binstDstSrcs : BInst → String × List String
  | .add d a b => (d, [a, b])
  | .sub d a b => (d, [a, b])
  | .adds d a b => (d, [a, b])
  | .adcs d a b => (d, [a, b])
  | .adc d a b => (d, [a, b])
  | .subs d a b => (d, [a, b])
  | .sbcs d a b => (d, [a, b])
  | .sbc d a b => (d, [a, b])
  | .mul d a b => (d, [a, b])
  | .umulh d a b => (d, [a, b])
  | .and d a b => (d, [a, b])
  | .orr d a b => (d, [a, b])
  | .eor d a b => (d, [a, b])
  | .csel d a b _ => (d, [a, b])
  | .movz d _ => (d, [])
  | .movk d _ _ => (d, [d])  -- MOVK reads-modifies the destination
  | .mov d s => (d, [s])
  | .lsr d a _ => (d, [a])
  | .lsl d a _ => (d, [a])

/-! ### Printer sanity pins -/

/-- `adds x4, x4, x8` — flag-setting add (carry chain head). -/
example : renderBInst [("d","x4"),("a","x8")] (.adds "d" "d" "a")
    = "\tadds x4, x4, x8" := by native_decide

/-- `csel x4, x4, x8, cc` — the conditional-subtract select. -/
example : renderBInst [("d","x4"),("a","x8")] (.csel "d" "d" "a" .cc)
    = "\tcsel x4, x4, x8, cc" := by native_decide

/-- `umulh x0, x1, x2` — the widening high product. -/
example : renderBInst [("d","x0"),("a","x1"),("b","x2")] (.umulh "d" "a" "b")
    = "\tumulh x0, x1, x2" := by native_decide

/-- `movk x12, #65535, lsl #48` — a reduction-constant lane write. -/
example : renderBInst [("p","x12")] (.movk "p" 0xffff 3)
    = "\tmovk x12, #65535, lsl #48" := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend
