/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvLowering

/-!
# GAS RV64 RVV printer for the packed-u32 RVV machine instructions (#549 RVV residual)

`ARMBackend/NeonAsmPrinter.lean` prints the AArch64 NEON packed-u32 subset to GAS
ASIMD asm; this is its **RISC-V RVV** counterpart: it prints a `RvvModel.VInst`
block — the packed-u32 OPIVV/OPIVI set of `RvvModel.lean`, lowered to the RVV
model by `RvvLowering.lowerVBlock` / `rvvBlock_lowering_denote` — to GAS-syntax
RV64 RVV assembly text (`vadd.vv`/`vand.vv`/`vor.vv`/`vxor.vv`, `vsll.vi`/`vsrl.vi`
`#imm`, `vmv.v.v`), to be assembled by `riscv64-linux-gnu-as -march=rv64gcv`.

## Where the trust boundary is (identical posture to the NEON printer)

The **verified artifact** is `VOp → runVBlock` (the `RvvLowering.lowerVBlock` pass
+ `rvvBlock_lowering_denote`, down to the differential-validated `evalVInst`
semantics). This printer + `as` is the *thin* trust boundary, because the printer
is a **syntactic** map (one `VInst` arm → one GAS mnemonic line, fixed register
assignment, no instruction selection / scheduling / optimization), and `as`
performs only assembly. The machine-code byte encoder + `decode(encode)=i` against
`riscv/sail-riscv` RVV `encdec` lives in `RvvEncoder.lean` + `SailRvvDecoder.lean`,
so this printer + `as` is not the only byte-level trust edge.

## RVV operand order and the `vsetvli` / load-store prelude

GAS RVV order is `vadd.vv vd, vs2, vs1` (dst first; note `vs2` precedes `vs1`). The
shifts take the immediate last (`vsll.vi vd, vs2, #imm`); `vmv.v.v vd, vs1`. The
leaf function emits a `vsetvli` prelude that pins the fixed config the model
selects (`e32, m1` → `VL = VLEN/32`; the harness sets the AVL to 4), and the
vector arguments are loaded from / stored to the pointer in `a0` with `vle32.v` /
`vse32.v`. The prelude (`vsetvli`, `vle32.v`, `vse32.v`) is **trusted scaffolding**
(outside the verified packed-ALU body), exactly the NEON `renderLeafFn` posture.

## Register allocation

A `VInst` block uses SSA-style string names. `allocV` (linear-scan with last-use
liveness, the NEON `allocV` analogue at RVV `vN` width) assigns each name a `vN`.
The ChaCha quarter-round's live set is 4 + a couple of temps, well under the 32
RVV registers, so it never spills. `reserved` names (args/outputs) are pinned to
the low registers `v0..` for the whole function.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv

/-! ## 1. Register allocation: name → vN -/

/-- The (dst, srcs) of a `VInst` — its written name and read names. -/
def vinstDstSrcs : VInst → String × List String
  | .vadd d a b => (d, [a, b])
  | .vand d a b => (d, [a, b])
  | .vor d a b => (d, [a, b])
  | .vxor d a b => (d, [a, b])
  | .vsll d a _ => (d, [a])
  | .vsrl d a _ => (d, [a])
  | .vmv d s   => (d, [s])

/-- A register assignment: an association list name → "vN". -/
abbrev VAlloc := List (String × String)

/-- The `vN` register a name is assigned. An unmapped name yields the explicit
    `<UNALLOCATED:n>` sentinel (so an over-budget block is rejected by `as` rather
    than silently aliasing — the same discipline as the NEON `vOf`). -/
def vOf (alloc : VAlloc) (n : String) : String :=
  (alloc.lookup n).getD ("<UNALLOCATED:" ++ n ++ ">")

/-- The index of the last instruction that *reads* `n` (its last use), or 0. -/
def vLastUse (block : List VInst) (n : String) : Nat :=
  (block.zipIdx.foldl (fun acc (i, idx) =>
    if (vinstDstSrcs i).2.contains n then idx else acc) 0)

/-- The RVV register pool we allocate from: `v0 … v31`. RVV has 32 vector
    registers; the ChaCha 4-way live set (16 state words + a few temps) fits
    comfortably. -/
def vPool : List String := (List.range 32).map (fun i => "v" ++ toString i)

/-- Linear-scan allocation over the V pool. `reserved` names (args/outputs) are
    pinned to `v0..` for the whole function and never freed; the remaining pool is
    recycled by last-use liveness. The RVV analogue of `Neon.allocV`. -/
def allocV (reserved : List String) (block : List VInst) : VAlloc :=
  let nres := reserved.length
  let pinned : VAlloc := reserved.zipIdx.map (fun (n, i) => (n, "v" ++ toString i))
  let pool0 : List String := vPool.drop nres
  let step : (VAlloc × List String) → (VInst × Nat) → (VAlloc × List String) :=
    fun (alloc, free) (instr, idx) =>
      let (dst, _) := vinstDstSrcs instr
      let (alloc1, free1) :=
        if (alloc.lookup dst).isSome then (alloc, free)
        else match free with
          | [] => (alloc, free)
          | r :: rest => ((dst, r) :: alloc, rest)
      let toFree := (vinstDstSrcs instr).2.filter (fun s =>
        ¬ reserved.contains s ∧ vLastUse block s = idx ∧ s ≠ dst)
      let freedRegs := toFree.filterMap (fun s => alloc1.lookup s)
      (alloc1, free1 ++ freedRegs)
  let (alloc, _) := block.zipIdx.foldl step (pinned, pool0)
  alloc

/-! ## 2. The GAS RVV mnemonic printer (one line per `VInst`)

GAS RVV order is `op vd, vs2, vs1` (dst first). The shifts take the immediate last
with a `#`-less integer literal (`vsll.vi vd, vs2, imm`); `vmv.v.v vd, vs1`. -/

/-- Print one `VInst` to its GAS RV64 RVV asm line. -/
def renderVInst (alloc : VAlloc) : VInst → String
  | .vadd d a b => "\tvadd.vv " ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ vOf alloc b
  | .vand d a b => "\tvand.vv " ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ vOf alloc b
  | .vor d a b  => "\tvor.vv "  ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ vOf alloc b
  | .vxor d a b => "\tvxor.vv " ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ vOf alloc b
  | .vsll d a imm => "\tvsll.vi " ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ toString imm
  | .vsrl d a imm => "\tvsrl.vi " ++ vOf alloc d ++ ", " ++ vOf alloc a ++ ", " ++ toString imm
  | .vmv d s     => "\tvmv.v.v " ++ vOf alloc d ++ ", " ++ vOf alloc s

/-- Print a whole block's instruction lines (one per `VInst`). -/
def renderVBlockBody (alloc : VAlloc) (block : List VInst) : List String :=
  block.map (renderVInst alloc)

/-! ## 3. A leaf-function renderer (GAS RV64 RVV)

Wraps the verified straight-line body in a minimal leaf scaffolding. The 4-way
quarter-round takes its four state vectors packed in memory at the pointer in
`a0` (4 × 4 u32 = 64 bytes); the prologue sets `vsetvli` to `e32, m1` (the model's
fixed config), loads the four vectors with `vle32.v`, runs the verified body, and
stores them back. This `vsetvli` / `vle32.v` / `vse32.v` scaffolding is *trusted*
(outside the verified packed-ALU body), exactly the NEON `renderLeafFn` posture. -/

/-- Render a complete GAS RV64 RVV leaf function: `.text` directives, label, the
    `vsetvli` prelude, the strided `vle32.v` loads of the four state vectors, the
    lowered+rendered verified body, the strided `vse32.v` stores, and `ret`.
    The 16-byte stride steps the pointer between the four SoA word vectors. -/
def renderLeafFn (name : String) (reserved : List VOp → List String)
    (body : List VOp) : String :=
  let lowered := lowerVBlock body
  let resv := reserved body
  let alloc := allocV resv lowered
  let header :=
    [ "\t.text"
    , "\t.global " ++ name
    , "\t.type " ++ name ++ ", @function"
    , name ++ ":"
    -- prelude: pin the fixed e32, m1 config; load the 4 SoA word vectors a/b/c/d
    -- packed contiguously (4 lanes each) at the a0 pointer (16-byte stride).
    , "\tli t0, 4"
    , "\tvsetvli t0, t0, e32, m1, ta, ma"
    , "\tmv t1, a0"
    , "\tvle32.v v0, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvle32.v v1, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvle32.v v2, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvle32.v v3, (t1)" ]
  let lines := renderVBlockBody alloc lowered
  let epilogue :=
    [ "\tmv t1, a0"
    , "\tvse32.v v0, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvse32.v v1, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvse32.v v2, (t1)"
    , "\taddi t1, t1, 16"
    , "\tvse32.v v3, (t1)"
    , "\tret" ]
  String.intercalate "\n" (header ++ lines ++ epilogue) ++ "\n"

/-- The ChaCha 4-way quarter-round leaf: state vectors `a b c d` are the args,
    pinned to `v0–v3`; the body is `qrBlk`; results are stored back to `a0`. -/
def qrLeafAsm : String :=
  renderLeafFn "chacha_qr_rvv" (fun _ => ["a", "b", "c", "d"])
    (qrBlk "q" "a" "b" "c" "d")

/-! ## 4. Printer sanity pins

The rendered lines match the expected GAS RV64 RVV text for representative ops
(the syntactic half of the trust boundary, audited against `as` mnemonic
syntax). -/

/-- `vadd.vv v2, v0, v1` ≡ packed `v2 = v0 + v1` (dst first, `vs2` then `vs1`). -/
example :
    renderVInst [("d","v2"),("a","v0"),("b","v1")] (.vadd "d" "a" "b")
      = "\tvadd.vv v2, v0, v1" := by native_decide

/-- `vxor.vv v2, v0, v1` ≡ packed `v2 = v0 ^ v1`. -/
example :
    renderVInst [("d","v2"),("a","v0"),("b","v1")] (.vxor "d" "a" "b")
      = "\tvxor.vv v2, v0, v1" := by native_decide

/-- `vsll.vi v2, v0, 16` — the rotate's left half. -/
example :
    renderVInst [("d","v2"),("a","v0")] (.vsll "d" "a" 16)
      = "\tvsll.vi v2, v0, 16" := by native_decide

/-- `vsrl.vi v2, v0, 16` — the rotate's right half. -/
example :
    renderVInst [("d","v2"),("a","v0")] (.vsrl "d" "a" 16)
      = "\tvsrl.vi v2, v0, 16" := by native_decide

/-- The arg-pinned quarter-round allocates `a b c d` to `v0 v1 v2 v3` and emits
    the first instruction as `vadd.vv v0, v0, v1` (`a += b`). -/
example :
    (renderVBlockBody
      (allocV ["a","b","c","d"] (lowerVBlock (qrBlk "q" "a" "b" "c" "d")))
      (lowerVBlock (qrBlk "q" "a" "b" "c" "d"))).head?
      = some "\tvadd.vv v0, v0, v1" := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv
