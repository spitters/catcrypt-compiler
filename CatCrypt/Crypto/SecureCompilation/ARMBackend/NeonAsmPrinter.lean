/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonLowering
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonLowering

/-!
# GAS AArch64 ASIMD printer for the packed-u32 NEON machine instructions

The x86 backend prints the XMM packed-u32 subset to AT&T AVX asm; this module is
the **AArch64 NEON/ASIMD** counterpart: it prints a `NeonModel.NInst` block — the
packed-u32 ASIMD set of `NeonModel.lean`, the same set lowered to the NEON model
by `NeonLowering.lowerNBlock` / `neonBlock_lowering_denote` — to GAS-syntax
AArch64 ASIMD assembly text (`add`/`sub`/`mul` `.4s`, `and`/`orr`/`eor` `.16b`,
`shl`/`ushr` `.4s` `#imm`, `mov` `.16b`), to be assembled by
`aarch64-linux-gnu-as`/`clang`.

## Where the trust boundary is (identical posture to the x86 NEON-less printer)

The **verified artifact** is `NOp → runNBlock` (the `NeonLowering.lowerNBlock`
pass + `neonBlock_lowering_denote`, down to the differential-validated
`evalNInst` semantics). This printer + `as` is the *thin* trust boundary, because
the printer is a **syntactic** map (one `NInst` arm → one GAS mnemonic line, fixed
register assignment, no instruction selection / scheduling / optimization), and
`as` performs only assembly. The machine-code byte encoder + `decode(encode)=i`
against `rems-project/sail-arm` lives in `NeonEncoder.lean` + `SailNeonDecoder.lean`,
so this printer + `as` is not the only byte-level trust edge.

## Register allocation

A `NInst` block uses SSA-style string names. `allocV` (linear-scan with last-use
liveness, the scalar `ArmAsmPrinter.allocGp` analogue at `vN` width) assigns each
name a `vN`. The ChaCha quarter-round's live set is 4 + a couple of temps, well
under the 32 NEON registers, so it never spills. `reserved` names (args/outputs)
are pinned to the low registers `v0..` for the whole function.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon

/-! ## 1. Register allocation: name → vN -/

/-- The (dst, srcs) of a `NInst` — its written name and read names. -/
def ninstDstSrcs : NInst → String × List String
  | .add d a b => (d, [a, b])
  | .sub d a b => (d, [a, b])
  | .mul d a b => (d, [a, b])
  | .and d a b => (d, [a, b])
  | .orr d a b => (d, [a, b])
  | .eor d a b => (d, [a, b])
  | .shl d a _ => (d, [a])
  | .ushr d a _ => (d, [a])
  | .mov d s   => (d, [s])

/-- A register assignment: an association list name → "vN". -/
abbrev VAlloc := List (String × String)

/-- The `vN` register a name is assigned. An unmapped name yields the explicit
    `<UNALLOCATED:n>` sentinel (so an over-budget block is rejected by `as` rather
    than silently aliasing — the same discipline as the scalar `gpOf`). -/
def vOf (alloc : VAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- The index of the last instruction that *reads* `n` (its last use), or 0. -/
def vLastUse (block : List NInst) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (i, idx) =>
    if (ninstDstSrcs i).2.contains n then idx else acc) 0)

/-- The NEON register pool we allocate from: `v0 … v31`. NEON has 32 SIMD
    registers; the ChaCha 4-way live set (16 state words + a few temps) fits
    comfortably. -/
def vPool : List String := (List.range 32).map (fun i => "v" ++ toString i)

/-- Linear-scan allocation over the V pool. `reserved` names (args/outputs) are
    pinned to `v0..` for the whole function and never freed; the remaining pool
    `v<|reserved|>..v31` is recycled by last-use liveness. The NEON analogue of
    `ArmAsmPrinter.allocGp`. -/
def allocV (reserved : List String) (block : List NInst) : VAlloc :=
  let nres := reserved.length
  let pinned : VAlloc := reserved.zipIdx.map (fun (n, i) => (n, "v" ++ toString i))
  let pool0 : List String := vPool.drop nres
  let step : (VAlloc × List String) → (NInst × Nat) → (VAlloc × List String) :=
    fun (alloc, free) (instr, idx) =>
      let (dst, _) := ninstDstSrcs instr
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := (ninstDstSrcs instr).2.filter (fun s =>
        ¬ reserved.contains s ∧ vLastUse block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool0)
  alloc

/-! ## 2. The GAS ASIMD mnemonic printer (one line per `NInst`)

GAS AArch64 ASIMD order is `op Vd.T, Vn.T, Vm.T` (dst first); the arithmetic ops
use the `.4s` arrangement, the logical ops `.16b`; the shifts take the immediate
last with a `#` (`shl vd.4s, vn.4s, #imm`); `mov vd.16b, vn.16b`. -/

/-- Append the `.4s` arrangement suffix to a register name. -/
def s4 (r : String) : String := r ++ ".4s"
/-- Append the `.16b` arrangement suffix to a register name. -/
def b16 (r : String) : String := r ++ ".16b"

/-- Print one `NInst` to its GAS AArch64 ASIMD asm line. -/
def renderNInst (alloc : VAlloc) : NInst → String
  | .add d a b => "\tadd "  ++ s4 (vOf alloc d) ++ ", " ++ s4 (vOf alloc a) ++ ", " ++ s4 (vOf alloc b)
  | .sub d a b => "\tsub "  ++ s4 (vOf alloc d) ++ ", " ++ s4 (vOf alloc a) ++ ", " ++ s4 (vOf alloc b)
  | .mul d a b => "\tmul "  ++ s4 (vOf alloc d) ++ ", " ++ s4 (vOf alloc a) ++ ", " ++ s4 (vOf alloc b)
  | .and d a b => "\tand "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a) ++ ", " ++ b16 (vOf alloc b)
  | .orr d a b => "\torr "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a) ++ ", " ++ b16 (vOf alloc b)
  | .eor d a b => "\teor "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc a) ++ ", " ++ b16 (vOf alloc b)
  | .shl d a imm => "\tshl "  ++ s4 (vOf alloc d) ++ ", " ++ s4 (vOf alloc a) ++ ", #" ++ toString imm
  | .ushr d a imm => "\tushr " ++ s4 (vOf alloc d) ++ ", " ++ s4 (vOf alloc a) ++ ", #" ++ toString imm
  | .mov d s     => "\tmov "  ++ b16 (vOf alloc d) ++ ", " ++ b16 (vOf alloc s)

/-- Print a whole block's instruction lines (one per `NInst`). -/
def renderNBlockBody (alloc : VAlloc) (block : List NInst) : List String :=
  block.map (renderNInst alloc)

/-! ## 3. A leaf-function renderer (GAS AArch64 ASIMD)

Wraps the verified straight-line body in a minimal AAPCS64 leaf prologue: the
quarter-round takes its four state vectors in `v0–v3`, runs the body, returns the
four results in `v0–v3`. The body uses no stack (the live set fits in registers),
so the prologue is just the `.global`/label/`.type` scaffolding and a `ret`. This
scaffolding is *trusted* (outside the verified body), exactly the x86
`renderLeafFn` posture. -/

/-- Render a complete GAS AArch64 ASIMD leaf function: `.text` directives, label,
    the lowered+rendered body, and `ret`. -/
def renderLeafFn (name : String) (reserved : List NOp → List String)
    (body : List NOp) : String :=
  let lowered := lowerNBlock body
  let resv := reserved body
  let alloc := allocV resv lowered
  let header :=
    [ "\t.text"
    , "\t.global " ++ name
    , "\t.type " ++ name ++ ", %function"
    , name ++ ":" ]
  let lines := renderNBlockBody alloc lowered
  String.intercalate "\n" (header ++ lines ++ ["\tret"]) ++ "\n"

/-- The ChaCha 4-way quarter-round leaf: state vectors `a b c d` are the args,
    pinned to `v0–v3`; the body is `qrBlk`; results come back in the same
    registers. -/
def qrLeafAsm : String :=
  renderLeafFn "chacha_qr_neon" (fun _ => ["a", "b", "c", "d"])
    (qrBlk "q" "a" "b" "c" "d")

/-! ## 4. Printer sanity pins

The rendered lines match the expected GAS AArch64 ASIMD text for representative
ops (the syntactic half of the trust boundary, audited against `as` mnemonic
syntax). -/

/-- `add v2.4s, v0.4s, v1.4s` ≡ packed `v2 = v0 + v1` (dst first). -/
example :
    renderNInst [("d","v2"),("a","v0"),("b","v1")] (.add "d" "a" "b")
      = "\tadd v2.4s, v0.4s, v1.4s" := by native_decide

/-- `eor v2.16b, v0.16b, v1.16b` ≡ packed `v2 = v0 ^ v1`. -/
example :
    renderNInst [("d","v2"),("a","v0"),("b","v1")] (.eor "d" "a" "b")
      = "\teor v2.16b, v0.16b, v1.16b" := by native_decide

/-- `shl v2.4s, v0.4s, #16` — the rotate's left half. -/
example :
    renderNInst [("d","v2"),("a","v0")] (.shl "d" "a" 16)
      = "\tshl v2.4s, v0.4s, #16" := by native_decide

/-- `ushr v2.4s, v0.4s, #16` — the rotate's right half. -/
example :
    renderNInst [("d","v2"),("a","v0")] (.ushr "d" "a" 16)
      = "\tushr v2.4s, v0.4s, #16" := by native_decide

/-- The arg-pinned quarter-round allocates `a b c d` to `v0 v1 v2 v3` and emits
    the first instruction as `add v0.4s, v0.4s, v1.4s` (`a += b`). -/
example :
    (renderNBlockBody
      (allocV ["a","b","c","d"] (lowerNBlock (qrBlk "q" "a" "b" "c" "d")))
      (lowerNBlock (qrBlk "q" "a" "b" "c" "d"))).head?
      = some "\tadd v0.4s, v0.4s, v1.4s" := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
