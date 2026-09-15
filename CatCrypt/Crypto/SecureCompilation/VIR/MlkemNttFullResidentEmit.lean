/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-!
# Register-resident full 16-lane AVX2 ML-KEM-768 forward NTT

This module emits the complete 7-layer ML-KEM-768 forward NTT with the three
within-vector deep layers (`len = 8, 4, 2`) fused into a single sweep over the 16
`u256` vectors. In the baseline `LatticeNttEmit.renderMlkemNttFull16wayBody` those
three layers are three separate `for v = 0 to 16` loops, so each vector is loaded
from and stored to the polynomial array `r[]` once per layer (three round-trips).
The fused sweep loads each vector once, carries it through the `len = 8 → 4 → 2`
butterfly chain in a `u256` register, and stores it once.

The four vector-pair layers (`len = 128, 64, 32, 16`) are unchanged: each of those
butterflies pairs two of the 16 vectors, so keeping all 16 vectors resident plus
the Montgomery-multiply scratch would need 18 `%ymm`, above the 16-register file.

## Denotation

The deep-layer section of both bodies is given as a `DeepStmt` program:
`separateDeepProg` (three `for v = 0 to 16` loops) renders to the deep-layer lines
of `LatticeNttEmit.renderMlkemNttFull16wayBody`, and `residentDeepProg` (one fused
loop) renders to `residentDeepSweep`. `runStmts` runs such a program on registers,
the polynomial array `r` and the auxiliary array `aux`, with every packed operation
and `vfqmul` interpreted by an arbitrary `DeepOpSem`.
`mlkem_ntt_full_resident_denotation_preserves` states that both bodies are
`residentPairLayers` followed by the rendering of their deep program, and that for
every operation semantics and every entry state the two deep programs leave the
same polynomial array. The pair-layer lines are identical in both bodies. No
theorem relates `DeepOpSem` to x86 instruction semantics or the transform to the
NTT.

## KAT

The emitted `.jazz` is jasminc-lowered and compared with
`PQCLEAN_MLKEM768_CLEAN_ntt` at the bench level on sampled inputs
(`bench/mlkem_compare/mlkem_ntt_avx2_bench.c`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttFullResidentEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNttEmit

/-- The four vector-pair layers (`len = 128, 64, 32, 16`), identical to the
    baseline body: each butterfly pairs two of the 16 `u256` vectors, so the
    working set exceeds the 16-`%ymm` file and the vectors round-trip through the
    polynomial array `r[]`. -/
def residentPairLayers : List String :=
  [ "  reg u256 vq a b t zl zh c d radd rsub bb alow;"
  , "  reg u256 duph4 dupl4 duph2 dupl2;"
  , "  inline int v vv;"
  , ""
  , "  vq  = aux[:u256 0];"
  , ""
  , "  // === len = 128 (zl,zh @ aux 1,2) ==="
  , "  for v = 0 to 8 {"
  , "    zl = aux[:u256 1]; zh = aux[:u256 2];"
  , "    a = r[:u256 v];  b = r[:u256 v + 8];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 8] = d;"
  , "  }"
  , "  // === len = 64 (zl,zh pairs @ aux 3..6) ==="
  , "  for vv = 0 to 2 { for v = 0 to 4 {"
  , "    zl = aux[:u256 3 + 2*vv]; zh = aux[:u256 4 + 2*vv];"
  , "    a = r[:u256 8*vv + v]; b = r[:u256 8*vv + v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8*vv + v] = c; r[:u256 8*vv + v + 4] = d;"
  , "  }}"
  , "  // === len = 32 (zl,zh pairs @ aux 7..14) ==="
  , "  for vv = 0 to 4 { for v = 0 to 2 {"
  , "    zl = aux[:u256 7 + 2*vv]; zh = aux[:u256 8 + 2*vv];"
  , "    a = r[:u256 4*vv + v]; b = r[:u256 4*vv + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 4*vv + v] = c; r[:u256 4*vv + v + 2] = d;"
  , "  }}"
  , "  // === len = 16 (zl,zh pairs @ aux 15..30) ==="
  , "  for vv = 0 to 8 {"
  , "    zl = aux[:u256 15 + 2*vv]; zh = aux[:u256 16 + 2*vv];"
  , "    a = r[:u256 2*vv]; b = r[:u256 2*vv + 1];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 2*vv] = c; r[:u256 2*vv + 1] = d;"
  , "  }" ]

/-- The fused deep-layer sweep: one `for v = 0 to 16` loop that loads vector `v`
    once, runs the `len = 8 → 4 → 2` butterfly chain register-resident, and stores
    it once. Byte-identical to the three separate deep loops of the baseline body
    because those layers are within-vector (each `u256` vector is independent). -/
def residentDeepSweep : List String :=
  [ ""
  , "  duph4 = aux[:u256 127];"
  , "  dupl4 = aux[:u256 128];"
  , "  duph2 = aux[:u256 129];"
  , "  dupl2 = aux[:u256 130];"
  , ""
  , "  // === fused deep layers len = 8, 4, 2 (each vector resident across them) ==="
  , "  for v = 0 to 16 {"
  , "    a = r[:u256 v];"
  , "    // len = 8 (cross-128) zl,zh @ aux 31..62"
  , "    zl = aux[:u256 31 + 2*v]; zh = aux[:u256 32 + 2*v];"
  , "    bb   = #VPERMQ(a, 0xEE);"
  , "    alow = #VPERMQ(a, 0x44);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    a = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "    // len = 4 (within 128) zl,zh @ aux 63..94"
  , "    zl = aux[:u256 63 + 2*v]; zh = aux[:u256 64 + 2*v];"
  , "    bb   = #VPSHUFB_256(a, duph4);"
  , "    alow = #VPSHUFB_256(a, dupl4);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    a = #VPBLEND_16u16(radd, rsub, 0xF0);"
  , "    // len = 2 (within 128) zl,zh @ aux 95..126"
  , "    zl = aux[:u256 95 + 2*v]; zh = aux[:u256 96 + 2*v];"
  , "    bb   = #VPSHUFB_256(a, duph2);"
  , "    alow = #VPSHUFB_256(a, dupl2);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xCC);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- The resident full-NTT body: the four vector-pair layers, then the fused deep
    sweep. -/
def renderMlkemNttFull16wayResidentBody : List String :=
  residentPairLayers ++ residentDeepSweep

/-- Pair layers with loop-invariant zeta/`vq` loads hoisted out of the unrolled
    butterfly loops: within `len = 128` the single group's `(zl,zh)` is constant,
    and within each `len = 64, 32` group the `(zl,zh)` is constant across the inner
    vectors, so the load is issued once per group instead of once per butterfly.
    Byte-identical to the baseline pair layers; removes redundant loads without
    lengthening any dependency chain. -/
def hoistedPairLayers : List String :=
  [ "  reg u256 vq a b t zl zh c d radd rsub bb alow;"
  , "  reg u256 duph4 dupl4 duph2 dupl2;"
  , "  inline int v;"
  , ""
  , "  vq  = aux[:u256 0];"
  , ""
  , "  // === len = 128 (zl,zh @ aux 1,2 hoisted) ==="
  , "  zl = aux[:u256 1]; zh = aux[:u256 2];"
  , "  for v = 0 to 8 {"
  , "    a = r[:u256 v];  b = r[:u256 v + 8];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 8] = d;"
  , "  }"
  , "  // === len = 64 (zl,zh per group hoisted) ==="
  , "  zl = aux[:u256 3]; zh = aux[:u256 4];"
  , "  for v = 0 to 4 {"
  , "    a = r[:u256 v]; b = r[:u256 v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 4] = d;"
  , "  }"
  , "  zl = aux[:u256 5]; zh = aux[:u256 6];"
  , "  for v = 0 to 4 {"
  , "    a = r[:u256 8 + v]; b = r[:u256 8 + v + 4];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8 + v] = c; r[:u256 8 + v + 4] = d;"
  , "  }"
  , "  // === len = 32 (zl,zh per group hoisted) ==="
  , "  zl = aux[:u256 7]; zh = aux[:u256 8];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 v]; b = r[:u256 v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 v] = c; r[:u256 v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 9]; zh = aux[:u256 10];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 4 + v]; b = r[:u256 4 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 4 + v] = c; r[:u256 4 + v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 11]; zh = aux[:u256 12];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 8 + v]; b = r[:u256 8 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 8 + v] = c; r[:u256 8 + v + 2] = d;"
  , "  }"
  , "  zl = aux[:u256 13]; zh = aux[:u256 14];"
  , "  for v = 0 to 2 {"
  , "    a = r[:u256 12 + v]; b = r[:u256 12 + v + 2];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 12 + v] = c; r[:u256 12 + v + 2] = d;"
  , "  }"
  , "  // === len = 16 (distinct zetas per iter; not hoistable) ==="
  , "  for v = 0 to 8 {"
  , "    zl = aux[:u256 15 + 2*v]; zh = aux[:u256 16 + 2*v];"
  , "    a = r[:u256 2*v]; b = r[:u256 2*v + 1];"
  , "    t = vfqmul(b, zl, zh, vq);"
  , "    c = #VPADD_16u16(a, t); d = #VPSUB_16u16(a, t);"
  , "    r[:u256 2*v] = c; r[:u256 2*v + 1] = d;"
  , "  }" ]

/-- The three deep within-vector layers kept as separate loops (baseline shape,
    preserving cross-vector ILP within each layer), each with per-vector `(zl,zh)`
    (distinct per iter, not hoistable). -/
def separateDeepLayers : List String :=
  [ ""
  , "  duph4 = aux[:u256 127];"
  , "  dupl4 = aux[:u256 128];"
  , "  duph2 = aux[:u256 129];"
  , "  dupl2 = aux[:u256 130];"
  , ""
  , "  // === len = 8 (cross-128) ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 31 + 2*v]; zh = aux[:u256 32 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPERMQ(a, 0xEE);"
  , "    alow = #VPERMQ(a, 0x44);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_8u32(radd, rsub, 0xF0);"
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // === len = 4 (within 128) ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 63 + 2*v]; zh = aux[:u256 64 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFB_256(a, duph4);"
  , "    alow = #VPSHUFB_256(a, dupl4);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xF0);"
  , "    r[:u256 v] = c;"
  , "  }"
  , "  // === len = 2 (within 128) ==="
  , "  for v = 0 to 16 {"
  , "    zl = aux[:u256 95 + 2*v]; zh = aux[:u256 96 + 2*v];"
  , "    a = r[:u256 v];"
  , "    bb   = #VPSHUFB_256(a, duph2);"
  , "    alow = #VPSHUFB_256(a, dupl2);"
  , "    t  = vfqmul(bb, zl, zh, vq);"
  , "    radd = #VPADD_16u16(a, t);"
  , "    rsub = #VPSUB_16u16(alow, t);"
  , "    c = #VPBLEND_16u16(radd, rsub, 0xCC);"
  , "    r[:u256 v] = c;"
  , "  }" ]

/-- The hoisted-zeta full-NTT body: hoisted pair layers, then the separate deep
    layers (ILP preserved). -/
def renderMlkemNttFull16wayHoistedBody : List String :=
  hoistedPairLayers ++ separateDeepLayers

/-- Emit the hoisted-zeta full 16-lane AVX2 ML-KEM-768 forward NTT `.jazz`. -/
def emitMlkemNttFull16wayHoistedJazz (name : String) : String :=
  String.intercalate "\n" renderVfqmul ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)\n"
    ++ "    -> reg mut ptr u16[256]\n{\n"
    ++ String.intercalate "\n" renderMlkemNttFull16wayHoistedBody
    ++ "\n\n  return r;\n}"

/-- Emit the resident full 16-lane AVX2 ML-KEM-768 forward NTT `.jazz`. Same ABI
    as `LatticeNttEmit.emitMlkemNttFull16wayJazz`: `reg mut ptr u16[256] r`
    (in-place polynomial), `reg const ptr u16[2112] aux` (q broadcast, per-layer
    `(zl,zh)` expanded-zeta pairs, shuffle controls). -/
def emitMlkemNttFull16wayResidentJazz (name : String) : String :=
  String.intercalate "\n" renderVfqmul ++ "\n\n"
    ++ "export fn " ++ name
    ++ "(reg mut ptr u16[256] r, reg const ptr u16[2112] aux)\n"
    ++ "    -> reg mut ptr u16[256]\n{\n"
    ++ String.intercalate "\n" renderMlkemNttFull16wayResidentBody
    ++ "\n\n  return r;\n}"

/-! ## Semantics of the deep-layer section -/

/-- A packed 256-bit word. -/
abbrev DeepWord := BitVec 256

/-- An argument of a packed operation: a register or an immediate, printed verbatim. -/
inductive DeepArg where
  | reg (r : String)
  | imm (t : String)

/-- The text of a `DeepArg`. -/
def DeepArg.render : DeepArg → String
  | .reg r => r
  | .imm t => t

/-- The strings of a list joined by `sep`. -/
def joinSep (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinSep sep xs

/-- An instruction of a deep-layer loop body, with loop variable `v`. -/
inductive DeepInstr where
  /-- `dst = aux[:u256 base + 2*v];` -/
  | loadAux (dst : String) (base : Nat)
  /-- `dst = r[:u256 v];` -/
  | loadR (dst : String)
  /-- `r[:u256 v] = src;` -/
  | storeR (src : String)
  /-- `dst<pad> = f(args);` -/
  | op (dst pad f : String) (args : List DeepArg)

/-- The text of a `DeepInstr`. -/
def DeepInstr.render : DeepInstr → String
  | .loadAux d b => d ++ " = aux[:u256 " ++ toString b ++ " + 2*v];"
  | .loadR d => d ++ " = r[:u256 v];"
  | .storeR x => "r[:u256 v] = " ++ x ++ ";"
  | .op d pad f args =>
      d ++ pad ++ " = " ++ f ++ "(" ++ joinSep ", " (args.map DeepArg.render) ++ ");"

/-- A line of a loop body: instructions separated by spaces, or a comment. -/
inductive DeepLine where
  | instrs (is : List DeepInstr)
  | comment (t : String)

/-- The text of a `DeepLine`, indented by four spaces. -/
def DeepLine.render : DeepLine → String
  | .instrs is => "    " ++ joinSep " " (is.map DeepInstr.render)
  | .comment t => "    " ++ t

/-- A statement of the deep-layer section. -/
inductive DeepStmt where
  /-- An empty line. -/
  | blank
  /-- A comment line. -/
  | comment (t : String)
  /-- `dst = aux[:u256 k];` -/
  | loadConst (dst : String) (k : Nat)
  /-- `for v = 0 to n { body }` -/
  | loop (n : Nat) (body : List DeepLine)

/-- The lines of a `DeepStmt`, indented by two spaces. -/
def DeepStmt.render : DeepStmt → List String
  | .blank => [""]
  | .comment t => ["  " ++ t]
  | .loadConst d k => ["  " ++ d ++ " = aux[:u256 " ++ toString k ++ "];"]
  | .loop n body =>
      ("  for v = 0 to " ++ toString n ++ " {") :: body.map DeepLine.render ++ ["  }"]

/-- Registers, the polynomial array `r` and the auxiliary array `aux`, by vector
    index. -/
structure DeepState where
  reg : String → DeepWord
  r : Nat → DeepWord
  aux : Nat → DeepWord

/-- Write register `x`. -/
def DeepState.setReg (s : DeepState) (x : String) (w : DeepWord) : DeepState :=
  { s with reg := fun y => if y = x then w else s.reg y }

/-- A semantics for the packed operations and `vfqmul`: the result of operation `f`
    on register values and immediates. -/
abbrev DeepOpSem := String → List (DeepWord ⊕ String) → DeepWord

/-- The value of an argument. -/
def DeepArg.val (s : DeepState) : DeepArg → DeepWord ⊕ String
  | .reg x => .inl (s.reg x)
  | .imm t => .inr t

/-- One instruction step at loop index `v`. -/
def DeepInstr.eval (σ : DeepOpSem) (v : Nat) (s : DeepState) : DeepInstr → DeepState
  | .loadAux d b => s.setReg d (s.aux (b + 2 * v))
  | .loadR d => s.setReg d (s.r v)
  | .storeR x => { s with r := Function.update s.r v (s.reg x) }
  | .op d _ f args => s.setReg d (σ f (args.map (DeepArg.val s)))

/-- One line step at loop index `v`. -/
def DeepLine.eval (σ : DeepOpSem) (v : Nat) (s : DeepState) : DeepLine → DeepState
  | .instrs is => is.foldl (DeepInstr.eval σ v) s
  | .comment _ => s

/-- Run a loop body at loop index `v`. -/
def runLines (σ : DeepOpSem) (v : Nat) (s : DeepState) (ls : List DeepLine) : DeepState :=
  ls.foldl (DeepLine.eval σ v) s

/-- One statement step; a loop runs its body for `v = 0 … n-1`. -/
def DeepStmt.eval (σ : DeepOpSem) (s : DeepState) : DeepStmt → DeepState
  | .blank => s
  | .comment _ => s
  | .loadConst d k => s.setReg d (s.aux k)
  | .loop n body => (List.range n).foldl (fun s v => runLines σ v s body) s

/-- Run a statement list. -/
def runStmts (σ : DeepOpSem) (s : DeepState) (p : List DeepStmt) : DeepState :=
  p.foldl (DeepStmt.eval σ) s

/-- The zeta load `zl = aux[:u256 zb + 2*v]; zh = aux[:u256 zb+1 + 2*v];`. -/
def zetaLine (zb : Nat) : DeepLine := .instrs [.loadAux "zl" zb, .loadAux "zh" (zb + 1)]

/-- The within-vector butterfly on register `a`: partner selection by `f`, `vfqmul`,
    add, subtract, and the blend into `dst`. -/
def butterflyLines (f : String) (bbA alowA : DeepArg) (dst blendF blendImm : String) :
    List DeepLine :=
  [ .instrs [.op "bb" "  " f [.reg "a", bbA]],
    .instrs [.op "alow" "" f [.reg "a", alowA]],
    .instrs [.op "t" " " "vfqmul" [.reg "bb", .reg "zl", .reg "zh", .reg "vq"]],
    .instrs [.op "radd" "" "#VPADD_16u16" [.reg "a", .reg "t"]],
    .instrs [.op "rsub" "" "#VPSUB_16u16" [.reg "alow", .reg "t"]],
    .instrs [.op dst "" blendF [.reg "radd", .reg "rsub", .imm blendImm]] ]

/-- The `len = 8` butterfly (cross-128 `#VPERMQ`). -/
def ops8 (dst : String) : List DeepLine :=
  butterflyLines "#VPERMQ" (.imm "0xEE") (.imm "0x44") dst "#VPBLEND_8u32" "0xF0"

/-- The `len = 4` butterfly (within-128 `#VPSHUFB_256`). -/
def ops4 (dst : String) : List DeepLine :=
  butterflyLines "#VPSHUFB_256" (.reg "duph4") (.reg "dupl4") dst "#VPBLEND_16u16" "0xF0"

/-- The `len = 2` butterfly (within-128 `#VPSHUFB_256`). -/
def ops2 (dst : String) : List DeepLine :=
  butterflyLines "#VPSHUFB_256" (.reg "duph2") (.reg "dupl2") dst "#VPBLEND_16u16" "0xCC"

/-- A separate deep-layer loop body: zeta load, vector load, butterfly into `c`,
    store. -/
def layerBody (zb : Nat) (ops : List DeepLine) : List DeepLine :=
  [zetaLine zb, .instrs [.loadR "a"]] ++ ops ++ [.instrs [.storeR "c"]]

/-- The shuffle-control loads that open both deep-layer sections. -/
def constLoads : List DeepStmt :=
  [ .blank, .loadConst "duph4" 127, .loadConst "dupl4" 128, .loadConst "duph2" 129,
    .loadConst "dupl2" 130, .blank ]

/-- The deep-layer section of `LatticeNttEmit.renderMlkemNttFull16wayBody`: three
    separate loops. -/
def separateDeepProg : List DeepStmt :=
  constLoads ++
  [ .comment "// === len = 8 (cross-128) zl,zh pairs @ aux 31..62 ===",
    .loop 16 (layerBody 31 (ops8 "c")), .blank,
    .comment "// === len = 4 (within 128) zl,zh pairs @ aux 63..94 ===",
    .loop 16 (layerBody 63 (ops4 "c")), .blank,
    .comment "// === len = 2 (within 128) zl,zh pairs @ aux 95..126 ===",
    .loop 16 (layerBody 95 (ops2 "c")) ]

/-- The fused loop body: one vector load, the three butterflies with the first two
    blending back into `a`, one store. -/
def residentBody : List DeepLine :=
  [ .instrs [.loadR "a"], .comment "// len = 8 (cross-128) zl,zh @ aux 31..62", zetaLine 31 ] ++
  ops8 "a" ++
  [ .comment "// len = 4 (within 128) zl,zh @ aux 63..94", zetaLine 63 ] ++ ops4 "a" ++
  [ .comment "// len = 2 (within 128) zl,zh @ aux 95..126", zetaLine 95 ] ++ ops2 "c" ++
  [ .instrs [.storeR "c"] ]

/-- The deep-layer section of the resident body: one fused loop. -/
def residentDeepProg : List DeepStmt :=
  constLoads ++
  [ .comment "// === fused deep layers len = 8, 4, 2 (each vector resident across them) ===",
    .loop 16 residentBody ]

/-- `residentDeepProg` renders to `residentDeepSweep`. -/
theorem residentDeepProg_render :
    residentDeepProg.flatMap DeepStmt.render = residentDeepSweep := by
  decide +kernel

/-- The baseline full-NTT body is `residentPairLayers` followed by the rendering of
    `separateDeepProg`. -/
theorem separateDeepProg_render :
    residentPairLayers ++ separateDeepProg.flatMap DeepStmt.render =
      renderMlkemNttFull16wayBody := by
  decide +kernel

/-- The registers the deep-layer loop bodies read without writing. -/
def deepConsts : List String := ["vq", "duph4", "dupl4", "duph2", "dupl2"]

/-- `s` has auxiliary array `A` and holds `kv c` in each register `c ∈ deepConsts`. -/
def DeepFrame (A : Nat → DeepWord) (kv : String → DeepWord) (s : DeepState) : Prop :=
  s.aux = A ∧ ∀ c ∈ deepConsts, s.reg c = kv c

/-- A loop whose body keeps `DeepFrame A kv` and updates only `r v`, by `G v`, updates
    every `r i` for `i < n` by `G i` and keeps the frame. -/
theorem loop_frame (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord)
    (B : List DeepLine) (G : Nat → DeepWord → DeepWord)
    (hf : ∀ v s, DeepFrame A kv s →
      DeepFrame A kv (runLines σ v s B) ∧
        (runLines σ v s B).r = Function.update s.r v (G v (s.r v))) :
    ∀ (n : Nat) (s : DeepState), DeepFrame A kv s →
      DeepFrame A kv ((List.range n).foldl (fun s v => runLines σ v s B) s) ∧
      ((List.range n).foldl (fun s v => runLines σ v s B) s).r =
        fun i => if i < n then G i (s.r i) else s.r i := by
  intro n
  induction n with
  | zero => intro s hs; exact ⟨hs, by simp⟩
  | succ n ih =>
    intro s hs
    obtain ⟨hF, hr⟩ := ih s hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hF', hr'⟩ := hf n _ hF
    refine ⟨hF', ?_⟩
    rw [hr', hr]
    funext i
    by_cases hi : i = n
    · subst hi; simp
    · rw [Function.update_of_ne hi]
      by_cases hlt : i < n
      · simp [hlt, show i < n + 1 by omega]
      · simp [hlt, show ¬ i < n + 1 by omega]

/-- The state holding `kv` in every register, `x` in every vector, and `aux = A`. -/
def deepCanon (A : Nat → DeepWord) (kv : String → DeepWord) (x : DeepWord) : DeepState :=
  { reg := kv, r := fun _ => x, aux := A }

theorem body8_step (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord) (v : Nat)
    (s : DeepState) (hs : DeepFrame A kv s) :
    DeepFrame A kv (runLines σ v s (layerBody 31 (ops8 "c"))) ∧
    (runLines σ v s (layerBody 31 (ops8 "c"))).r = Function.update s.r v
      ((runLines σ v (deepCanon A kv (s.r v)) (layerBody 31 (ops8 "c"))).r v) := by
  obtain ⟨hA, hK⟩ := hs
  simp only [deepConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hK
  simp [runLines, layerBody, ops8, butterflyLines, zetaLine, DeepLine.eval, DeepInstr.eval,
    DeepState.setReg, DeepArg.val, deepCanon, DeepFrame, deepConsts, hA, hK]

theorem body4_step (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord) (v : Nat)
    (s : DeepState) (hs : DeepFrame A kv s) :
    DeepFrame A kv (runLines σ v s (layerBody 63 (ops4 "c"))) ∧
    (runLines σ v s (layerBody 63 (ops4 "c"))).r = Function.update s.r v
      ((runLines σ v (deepCanon A kv (s.r v)) (layerBody 63 (ops4 "c"))).r v) := by
  obtain ⟨hA, hK⟩ := hs
  simp only [deepConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hK
  simp [runLines, layerBody, ops4, butterflyLines, zetaLine, DeepLine.eval, DeepInstr.eval,
    DeepState.setReg, DeepArg.val, deepCanon, DeepFrame, deepConsts, hA, hK]

theorem body2_step (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord) (v : Nat)
    (s : DeepState) (hs : DeepFrame A kv s) :
    DeepFrame A kv (runLines σ v s (layerBody 95 (ops2 "c"))) ∧
    (runLines σ v s (layerBody 95 (ops2 "c"))).r = Function.update s.r v
      ((runLines σ v (deepCanon A kv (s.r v)) (layerBody 95 (ops2 "c"))).r v) := by
  obtain ⟨hA, hK⟩ := hs
  simp only [deepConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hK
  simp [runLines, layerBody, ops2, butterflyLines, zetaLine, DeepLine.eval, DeepInstr.eval,
    DeepState.setReg, DeepArg.val, deepCanon, DeepFrame, deepConsts, hA, hK]

theorem residentBody_step (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord)
    (v : Nat) (s : DeepState) (hs : DeepFrame A kv s) :
    DeepFrame A kv (runLines σ v s residentBody) ∧
    (runLines σ v s residentBody).r = Function.update s.r v
      ((runLines σ v (deepCanon A kv (s.r v)) residentBody).r v) := by
  obtain ⟨hA, hK⟩ := hs
  simp only [deepConsts, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hK
  simp [runLines, residentBody, ops8, ops4, ops2, butterflyLines, zetaLine, DeepLine.eval,
    DeepInstr.eval, DeepState.setReg, DeepArg.val, deepCanon, DeepFrame, deepConsts, hA, hK]

/-- On one vector, the fused body computes the `len = 2` butterfly of the `len = 4`
    butterfly of the `len = 8` butterfly. -/
theorem residentBody_fuse (σ : DeepOpSem) (A : Nat → DeepWord) (kv : String → DeepWord)
    (v : Nat) (x : DeepWord) :
    (runLines σ v (deepCanon A kv x) residentBody).r v =
      (runLines σ v (deepCanon A kv
        ((runLines σ v (deepCanon A kv
          ((runLines σ v (deepCanon A kv x) (layerBody 31 (ops8 "c"))).r v))
          (layerBody 63 (ops4 "c"))).r v))
        (layerBody 95 (ops2 "c"))).r v := by
  simp [runLines, residentBody, layerBody, ops8, ops4, ops2, butterflyLines, zetaLine,
    DeepLine.eval, DeepInstr.eval, DeepState.setReg, DeepArg.val, deepCanon]

/-- The fused loop and the three separate loops leave the same polynomial array. -/
theorem residentDeepProg_r_eq (σ : DeepOpSem) (s : DeepState) :
    (runStmts σ s residentDeepProg).r = (runStmts σ s separateDeepProg).r := by
  simp only [runStmts, residentDeepProg, separateDeepProg, List.foldl_append, List.foldl_cons,
    List.foldl_nil, DeepStmt.eval]
  generalize constLoads.foldl (DeepStmt.eval σ) s = s1
  have h1 : DeepFrame s1.aux s1.reg s1 := ⟨rfl, fun _ _ => rfl⟩
  obtain ⟨hF2, hr2⟩ := loop_frame σ s1.aux s1.reg _
    (fun v x => (runLines σ v (deepCanon s1.aux s1.reg x) (layerBody 31 (ops8 "c"))).r v)
    (body8_step σ s1.aux s1.reg) 16 s1 h1
  obtain ⟨hF3, hr3⟩ := loop_frame σ s1.aux s1.reg _
    (fun v x => (runLines σ v (deepCanon s1.aux s1.reg x) (layerBody 63 (ops4 "c"))).r v)
    (body4_step σ s1.aux s1.reg) 16 _ hF2
  obtain ⟨-, hr4⟩ := loop_frame σ s1.aux s1.reg _
    (fun v x => (runLines σ v (deepCanon s1.aux s1.reg x) (layerBody 95 (ops2 "c"))).r v)
    (body2_step σ s1.aux s1.reg) 16 _ hF3
  obtain ⟨-, hrF⟩ := loop_frame σ s1.aux s1.reg _
    (fun v x => (runLines σ v (deepCanon s1.aux s1.reg x) residentBody).r v)
    (residentBody_step σ s1.aux s1.reg) 16 s1 h1
  rw [hr4, hr3, hr2, hrF]
  funext i
  by_cases hi : i < 16
  · simp only [hi, ↓reduceIte]
    exact residentBody_fuse σ s1.aux s1.reg i (s1.r i)
  · simp [hi]

/-- **The resident full ML-KEM-768 NTT body agrees with the baseline body.** The
    resident body `renderMlkemNttFull16wayResidentBody` is `residentPairLayers`
    followed by the rendering of `residentDeepProg`, the baseline body
    `renderMlkemNttFull16wayBody` is `residentPairLayers` followed by the rendering
    of `separateDeepProg`, and for every semantics `σ` of the packed operations and
    `vfqmul` and every entry state, the fused loop and the three separate loops
    leave the same polynomial array `r`. -/
theorem mlkem_ntt_full_resident_denotation_preserves :
    renderMlkemNttFull16wayResidentBody =
      residentPairLayers ++ residentDeepProg.flatMap DeepStmt.render ∧
    renderMlkemNttFull16wayBody =
      residentPairLayers ++ separateDeepProg.flatMap DeepStmt.render ∧
    ∀ (σ : DeepOpSem) (s : DeepState),
      (runStmts σ s residentDeepProg).r = (runStmts σ s separateDeepProg).r :=
  ⟨by rw [residentDeepProg_render]; rfl, separateDeepProg_render.symm, residentDeepProg_r_eq⟩

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttFullResidentEmit
