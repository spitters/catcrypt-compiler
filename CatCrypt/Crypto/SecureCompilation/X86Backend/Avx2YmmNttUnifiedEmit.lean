/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint

/-!
# The owned signed ML-DSA-65 forward NTT kernel over the unified `YmmInstr` (`dsa_ntt_proto`)

This module re-authors the complete 8-layer Cooley–Tukey ML-DSA-65 forward NTT —
the signed-Montgomery AVX2 transform of `bench/mldsa_compare/mldsa_ntt_full_8way.s`
— directly over the **unified** dialect-side `YmmAsmPrint.YmmInstr`/`YmmOp`
instruction set, so that the owned AT&T printer
(`YmmAsmPrint.renderYmmFundefText`) emits the `dsa_ntt_proto` `.s` with **no
jasminc** on the path and **no dependency on the bespoke `Avx2YmmModel` /
`Avx2YmmAsmPrinter`**.

It is the dialect-native successor to `X86Backend/Avx2YmmNttEmit.lean`
(which built a `List YInst` over `Avx2YmmModel.YInst`). The translation is
faithful 1:1 — every instruction maps to the SAME rendered AT&T string — so the
emitted artifact is byte-identical to the bespoke kernel's, and the bench driver
can repoint by import only (the `dsaNttProtoAsm` name is kept parallel). The
`renderYmmInstr` rendering is byte-identical to the bespoke `renderYInst` (proven
by the 14 syntax pins in `YmmAsmPrint.lean`), so the structural `take 6` render
pin below IS the byte-identity check for the first 6 emitted lines.

## The transform structure (same recipe, now over `YmmInstr`)

The 256 `int32` coefficients are 32 vectors of 8 lanes. The aux buffer is 256
`u256` slots: slot 0 holds `q` (loaded once into `ymm0`); the remaining slots
hold the per-group `(zl = zeta, zh = (zeta·qinv) mod 2³²)` pairs.

* **Layers `len = 128 … 8` (5 layers)** — vector-pair butterflies: a partner
  vector `b` is loaded from another `r` slot, the signed Montgomery product
  `dmont(b, zl, zh, q)` is formed (the inlined 6-`vpmuldq` core), and the
  butterfly `c = a + t`, `d = a − t` is stored back. The zeta slot runs `1, 3,
  5, …` (odd slots), one pair per group.
* **Layer `len = 4`** — cross-128 (`vpermq $238 / $68`), final blend `$240`.
  Zeta base slot 63.
* **Layer `len = 2`** — within-128 (`vpshufd $238 / $68`), final blend `$204`.
  Zeta base slot 127.
* **Layer `len = 1`** — within-128 adjacent (`vpshufd $245 / $160`), final blend
  `$170`. Zeta base slot 191.

The register assignment is the fixed `%ymm0…%ymm7` allocation of the reference
(`%ymm0` = `q`, scratch `%ymm1…%ymm7`); the 16-register file never spills.

## Honesty anchor

There is no in-Lean *functional* NTT denotation to self-check against (the lane
ops are validated; the transform's correctness is the bench-level KAT). The
integration witness is `bench/mldsa_compare/ntt_avx2_vs_scalar_kat.c`: the
emitted `dsa_ntt_proto(r, aux)` must agree, coefficient-for-coefficient, with the
emitted scalar `mldsa_ntt` (itself KAT'd against PQClean) on the
standard-order/standard-domain contract. This module reproduces the
bench-validated instruction sequence of that transform op-for-op; the §6
`YmmOp.denote` fragment pin checks the Montgomery-mul core denotes as specified.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Avx2YmmUnified

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

-- `DecidableEq` for the memory operand and the instruction type (structural over
-- `YmmOp`/`String`/`YmmMem`). Needed for the `native_decide` operand pins below;
-- `YmmAsmPrint` itself only needs the renderer, so it does not derive these.
deriving instance DecidableEq for YmmMem
deriving instance DecidableEq for YmmInstr

/-! ## 1. Memory-operand helpers (slot → byte displacement) -/

/-- The `r` (coefficients, `%rdi`) memory operand for `u256` slot `k`
    (`disp = 32·k`). Returns a `YmmMem` (the dialect-side twin of `YMem`). -/
def rSlot (k : Nat) : YmmMem := ⟨"%rdi", (32 * k : Nat)⟩

/-- The `aux` (twiddles, `%rsi`) memory operand for `u256` slot `k`
    (`disp = 32·k`). Returns a `YmmMem`. -/
def auxSlot (k : Nat) : YmmMem := ⟨"%rsi", (32 * k : Nat)⟩

/-! ## 2. The two butterfly group shapes

Both shapes inline the signed Montgomery multiply `dmont` (`vmovshdup` of the
odd lanes, 6 `vpmuldq` — `zl·b`, `zl·hodd`, `zh·b`, `zh·hodd`, then `q·`-quotient
twice — two `vpsubq`, recombine with `vmovshdup` + `vpblendd $170`), exactly as
the reference `.s` lays them out. The register names are the reference's fixed
allocation. Each former `YInst` constructor maps to a `YmmInstr` arm: the ALU
ops become `.alu (op : YmmOp) dst srcs`, the memory ops stay `.yload`/`.ystore`. -/

/-- One **vector-pair** butterfly group (layers `len = 128 … 8`): load `zl,zh`
    from `auxSlot zlSlot / zlSlot+1`, `a` from `rSlot aSlot`, partner `b` from
    `rSlot bSlot`; emit `t = dmont(b, zl, zh, q)`, `c = a + t` (store to `aSlot`),
    `d = a − t` (store to `bSlot`). Mirrors reference lines 7–26 (`ymm0` = `q`
    is loaded once in the prologue). -/
def pairGroup (zlSlot aSlot bSlot : Nat) : List YmmInstr :=
  [ .yload "%ymm2" (auxSlot zlSlot)
  , .yload "%ymm3" (auxSlot (zlSlot + 1))
  , .yload "%ymm1" (rSlot aSlot)
  , .yload "%ymm4" (rSlot bSlot)
  , .alu .vmovshdup "%ymm5" ["%ymm4"]            -- hodd = high-dup of b
  , .alu .vpmuldq "%ymm6" ["%ymm2", "%ymm4"]     -- lo_e = zl · b
  , .alu .vpmuldq "%ymm2" ["%ymm2", "%ymm5"]     -- lo_o = zl · hodd
  , .alu .vpmuldq "%ymm4" ["%ymm3", "%ymm4"]     -- m_e  = zh · b
  , .alu .vpmuldq "%ymm3" ["%ymm3", "%ymm5"]     -- m_o  = zh · hodd
  , .alu .vpmuldq "%ymm4" ["%ymm0", "%ymm4"]     -- qm_e = q · m_e
  , .alu .vpmuldq "%ymm3" ["%ymm0", "%ymm3"]     -- qm_o = q · m_o
  , .alu .vpsubq "%ymm6" ["%ymm6", "%ymm4"]      -- lo_e − qm_e
  , .alu .vpsubq "%ymm2" ["%ymm2", "%ymm3"]      -- lo_o − qm_o
  , .alu .vmovshdup "%ymm6" ["%ymm6"]
  , .alu (.vpblendd 170) "%ymm2" ["%ymm6", "%ymm2"] -- t (interleave even/odd hi-words)
  , .alu .vpaddd "%ymm3" ["%ymm1", "%ymm2"]      -- c = a + t
  , .alu .vpsubd "%ymm1" ["%ymm1", "%ymm2"]      -- d = a − t
  , .ystore (rSlot aSlot) "%ymm3"
  , .ystore (rSlot bSlot) "%ymm1" ]

/-- One **within-vector** butterfly group (layers `len = 4, 2, 1`): the partner
    is fetched from the same vector `a = rSlot vSlot` via `part` (`vpermq` for
    `len = 4`, `vpshufd` for `len = 2, 1`) with immediates `hiImm` (the partner
    select) and `loImm` (the kept-lane select); the result halves are recombined
    with `vpblendd finalImm`. Zeta `zl,zh` from `auxSlot zlSlot / zlSlot+1`.
    Mirrors reference lines 1528–1547 (permq), 2168–2187, 2808–2827 (shufd).

    `part` takes `dst src imm` and produces the `YmmInstr` for the permute. -/
def withinGroup (part : String → String → Nat → YmmInstr)
    (hiImm loImm finalImm : Nat) (zlSlot vSlot : Nat) : List YmmInstr :=
  [ .yload "%ymm3" (auxSlot zlSlot)
  , .yload "%ymm4" (auxSlot (zlSlot + 1))
  , .yload "%ymm1" (rSlot vSlot)
  , part "%ymm5" "%ymm1" hiImm            -- bb   = partner lanes
  , part "%ymm2" "%ymm1" loImm            -- alow = kept lanes
  , .alu .vmovshdup "%ymm6" ["%ymm5"]            -- hodd of bb
  , .alu .vpmuldq "%ymm7" ["%ymm3", "%ymm5"]     -- lo_e = zl · bb
  , .alu .vpmuldq "%ymm3" ["%ymm3", "%ymm6"]     -- lo_o = zl · hodd
  , .alu .vpmuldq "%ymm5" ["%ymm4", "%ymm5"]     -- m_e  = zh · bb
  , .alu .vpmuldq "%ymm4" ["%ymm4", "%ymm6"]     -- m_o  = zh · hodd
  , .alu .vpmuldq "%ymm5" ["%ymm0", "%ymm5"]     -- qm_e = q · m_e
  , .alu .vpmuldq "%ymm4" ["%ymm0", "%ymm4"]     -- qm_o = q · m_o
  , .alu .vpsubq "%ymm6" ["%ymm7", "%ymm5"]      -- lo_e − qm_e
  , .alu .vpsubq "%ymm3" ["%ymm3", "%ymm4"]      -- lo_o − qm_o
  , .alu .vmovshdup "%ymm6" ["%ymm6"]
  , .alu (.vpblendd 170) "%ymm3" ["%ymm6", "%ymm3"] -- t
  , .alu .vpaddd "%ymm1" ["%ymm1", "%ymm3"]      -- radd = a + t
  , .alu .vpsubd "%ymm2" ["%ymm2", "%ymm3"]      -- rsub = alow − t
  , .alu (.vpblendd finalImm) "%ymm3" ["%ymm1", "%ymm2"]
  , .ystore (rSlot vSlot) "%ymm3" ]

/-! ## 3. The 8 layers

The vector-pair layers share a single running zeta-slot counter (odd slots
`1, 3, 5, …`), one pair per group, matching the reference's monotone
`32, 96, 160, …(%rsi)` zeta progression. -/

/-- The (a, b) coefficient-slot pairs of a vector-pair layer, **grouped by zeta
    group** `vv` — each inner list shares one zeta pair (constant across its
    butterflies), and the zeta slot advances once per group. `len128`: 1 group of
    16 butterflies `(v, v+16)`; `len64`: 2 groups of 8 `(16vv+v, +8)`; `len32`: 4
    groups of 4 `(8vv+v, +4)`; `len16`: 8 groups of 2 `(4vv+v, +2)`; `len8`: 16
    groups of 1 `(2vv, 2vv+1)`. -/
def pairLayerGroups : Nat → List (List (Nat × Nat))
  | 128 => [(List.range 16).map (fun v => (v, v + 16))]
  | 64  => (List.range 2).map (fun vv => (List.range 8).map (fun v => (16*vv + v, 16*vv + v + 8)))
  | 32  => (List.range 4).map (fun vv => (List.range 4).map (fun v => (8*vv + v, 8*vv + v + 4)))
  | 16  => (List.range 8).map (fun vv => (List.range 2).map (fun v => (4*vv + v, 4*vv + v + 2)))
  | _   => (List.range 16).map (fun vv => [(2*vv, 2*vv + 1)])   -- len = 8

/-- Emit one vector-pair layer, threading the zeta-slot counter `z0`: each zeta
    group reuses one slot pair for all its butterflies, then advances by 2.
    Returns the code and the next free slot. -/
def emitPairLayer (len z0 : Nat) : List YmmInstr × Nat :=
  (pairLayerGroups len).foldl
    (fun (acc : List YmmInstr × Nat) (grp : List (Nat × Nat)) =>
      let (code, z) := acc
      let gcode := grp.flatMap (fun ab => pairGroup z ab.1 ab.2)
      (code ++ gcode, z + 2))
    ([], z0)

/-- Emit all five vector-pair layers (`len = 128, 64, 32, 16, 8`), chaining the
    zeta counter from slot 1. Returns the code and the next free slot (= 63). -/
def emitPairLayers : List YmmInstr × Nat :=
  [128, 64, 32, 16, 8].foldl
    (fun (acc : List YmmInstr × Nat) (len : Nat) =>
      let (code, z) := acc
      let (lcode, z') := emitPairLayer len z
      (code ++ lcode, z'))
    ([], 1)

/-- Emit one within-vector layer over all 32 vectors (`v = 0 … 31`), zeta slot
    `zbase + 2·v`. -/
def emitWithinLayer (part : String → String → Nat → YmmInstr)
    (hiImm loImm finalImm zbase : Nat) : List YmmInstr :=
  (List.range 32).flatMap (fun v => withinGroup part hiImm loImm finalImm (zbase + 2*v) v)

/-! ## 4. The complete kernel -/

/-- The full `dsa_ntt_proto` body as a `List YmmInstr`: the `q` prologue load, the
    five vector-pair layers, then the `len = 4` (`vpermq`) and `len = 2, 1`
    (`vpshufd`) within-vector layers — op-for-op the bench-validated
    `mldsa_ntt_full_8way.s` transform. The `part` closures build the `.alu`
    permute instructions (`vpermq`/`vpshufd` with the immediate baked in). -/
def dsaNttProtoBody : List YmmInstr :=
  [ .yload "%ymm0" (auxSlot 0) ]                                       -- ymm0 = q
  ++ emitPairLayers.1
  ++ emitWithinLayer (fun d a i => .alu (.vpermq i) d [a])  238 68  240 63   -- len = 4
  ++ emitWithinLayer (fun d a i => .alu (.vpshufd i) d [a]) 238 68  204 127  -- len = 2
  ++ emitWithinLayer (fun d a i => .alu (.vpshufd i) d [a]) 245 160 170 191  -- len = 1

/-- The emitted `dsa_ntt_proto` `.s` text (AT&T, 2-pointer ABI). Byte-identical
    to the bespoke `Avx2Ymm.dsaNttProtoAsm`; the bench driver repoints by import. -/
def dsaNttProtoAsm : String :=
  renderYmmFundefText "dsa_ntt_proto" dsaNttProtoBody

/-! ## 5. Structural pins (the emitted stream matches the reference shape)

These reproduce the bespoke kernel's pins with the SAME expected values. The
`take 6` render pin uses the validated reference AT&T strings — its passing is
the byte-identity proof for the first 6 emitted lines. -/

/-- The kernel emits exactly `1 + 19·(16+16+16+16+16) + 20·(32+32+32)` = `1 +
    19·80 + 20·96` = `3441` instructions — the reference `.s` instruction count
    (prologue `ymm0` load + 80 vector-pair groups of 19 + 96 within-vector
    groups of 20). -/
example : dsaNttProtoBody.length = 3441 := by native_decide

/-- The body opens with the `q` prologue load and the first vector-pair group's
    `zl,zh,a,b` loads — byte-identical operands to the reference `.s` head
    (`(%rsi)→ymm0`, `32(%rsi)→ymm2`, `64(%rsi)→ymm3`, `(%rdi)→ymm1`,
    `512(%rdi)→ymm4`). -/
example :
    dsaNttProtoBody.take 5
      = [ .yload "%ymm0" ⟨"%rsi", 0⟩, .yload "%ymm2" ⟨"%rsi", 32⟩
        , .yload "%ymm3" ⟨"%rsi", 64⟩, .yload "%ymm1" ⟨"%rdi", 0⟩
        , .yload "%ymm4" ⟨"%rdi", 512⟩ ] := by native_decide

/-- The first rendered instruction lines match the reference `.s` text exactly
    (the prologue + the first butterfly's `vmovshdup` head). This is the
    byte-identity check: the strings are the validated bespoke `take 6` reference;
    `renderYmmInstr` reproducing them proves the unified printer emits the same
    bytes for the first 6 lines. -/
example :
    (renderYmmBlockBody dsaNttProtoBody).take 6
      = [ "\tvmovdqu\t(%rsi), %ymm0", "\tvmovdqu\t32(%rsi), %ymm2"
        , "\tvmovdqu\t64(%rsi), %ymm3", "\tvmovdqu\t(%rdi), %ymm1"
        , "\tvmovdqu\t512(%rdi), %ymm4", "\tvmovshdup\t%ymm4, %ymm5" ] := by
  native_decide

/-- The last within-vector group (len = 1, `v = 31`, zeta slot `191 + 62 = 253`,
    `r` slot 31 = `992(%rdi)`) closes with the `$170` final blend and the store —
    matching the reference `.s` tail (lines 3431–3447). -/
example :
    dsaNttProtoBody.reverse.take 2
      = [ .ystore ⟨"%rdi", 992⟩ "%ymm3"
        , .alu (.vpblendd 170) "%ymm3" ["%ymm1", "%ymm2"] ] := by native_decide

/-! ## 6. The Montgomery-mul core denotes as specified (`YmmOp.denote` fragment)

The vector-pair group's `dmont` core (the head of `pairGroup`) computes, for
each even 32-bit lane, the signed Montgomery product `lo_e − qm_e` and, for the
odd lanes (via `vmovshdup`), `lo_o − qm_o`. This pin runs the core ops through
`YmmOp.denote` (over `BitVec 256`, NOT `runYBlock`/`YState`) and checks the
signed even-lane product and the odd-dup broadcast — the signed
multiply the NTT relies on. It is the dialect-native restatement of the bespoke
§6 `runYBlock` fragment pin, in the form already cross-checked at the end of
`YmmDialectOps.lean`. -/

/-- Fragment pin (`YmmOp.denote`, signed even-lane `vpmuldq` + odd-dup
    `vmovshdup`). With a NEGATIVE even-lane coefficient (even dword 2 of `a` =
    `0xFFFFFFFF` = `-1`), `vpmuldq` produces the signed products `5·3 = 15` and
    `(-1)·7 = -7`; `vmovshdup b` broadcasts the odd dwords. This is exactly the
    Montgomery-core head the `pairGroup` butterfly emits. -/
example :
    let a := yOfDwordsW ![5, 0, BitVec.ofNat 32 0xFFFFFFFF, 0, 0, 0, 0, 0];
    let b := yOfDwordsW ![3, 11, 7, 22, 0, 0, 0, 0];
    let prod := YmmOp.denote .vpmuldq a b;
    let dup := YmmOp.denote .vmovshdup b 0;
    -- lane 0 = 5 · 3 = 15 (signed, positive)
    (yQwordW prod 0 = (15 : BitVec 64)) ∧
    -- lane 1 = (-1) · 7 = -7 (signed; even dword 2 of a = 0xFFFFFFFF = -1)
    (yQwordW prod 1 = BitVec.ofNat 64 0xFFFFFFFFFFFFFFF9) ∧
    -- vmovshdup of b: odd-dup ⇒ [11,11,22,22,0,0,0,0]
    (yDwordW dup 0 = 11) ∧ (yDwordW dup 1 = 11) ∧
    (yDwordW dup 2 = 22) ∧ (yDwordW dup 3 = 22) := by native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.Avx2YmmUnified
