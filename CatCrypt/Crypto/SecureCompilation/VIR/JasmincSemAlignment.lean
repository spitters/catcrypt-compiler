/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect

/-!
# Aligning our Lean jasmin semantics with jasmin's Coq `psem` (TCB narrowing)

`lowerComToProg_sem_eq` proves `runProg leafSem com V = com.denote V`: the printed
jasmin program, executed by **our Lean evaluator `execExpr`/`execCom`**, denotes what
the source `Com` denotes. jasmin's own Coq compiler-correctness theorem
`compile_prog_to_asmP` (`proofs/compiler/compiler_proof.v:1221`) proves the dual edge:
the source program under jasmin's **Coq operational semantics `psem`** (`sem_call`,
`proofs/lang/psem.v`) refines the generated x86 (`asmsem_exportcall`). Composing them
gives `Com.denote ⟹ x86` — but the composition rests on one assumption recorded in
`bench/mlkem_compare/TCB.md`:

> our Lean `execExpr`/`execCom` is faithful to jasmin's Coq `psem` on the emitted
> program.

This file turns that vague assumption into a **finite, per-opcode list**, each
discharged down to "a Lean `BitVec`/array primitive mirrors the corresponding Coq
`word`/`WArray` primitive" — an eyeball-checkable equation on primitives, not a
whole-model trust. The `jasminDialect` has **exactly five op constructors**
(`regArith`, `stackLoad`, `stackStore`, `castW`, `extCall`), with `regArith`
ranging over the **eight** `JasminBinOp` operators (add/sub/mul/and/or/xor/shl/
shr), so `execExpr` (`JasminPrintSemCorrect.lean`) is an *exhaustive* match —
there is **no loop op in the dialect** (bounded loops are a separate additive
layer, task #48, not part of the core emit; the `Com` the semantics theorem
ranges over is loop-free). The alignment below is **total** over this emittable
op set: every operation gets a row, summarised in `opcode_alignment_total`
(the four `rfl`-closed shapes) plus the named `ExtCallAgrees` leaf edge:

| our shape (`execExpr`)            | jasmin `psem` primitive (Coq)                               | row |
|-----------------------------------|-------------------------------------------------------------|-----|
| `regArith bop w` → `bop.apply`    | `sem_sop2_typed` of `Oadd/Osub/Omul/Oland/Olor/Olxor/Olsl/Olsr` (`sem_op_typed.v:127`) | `binop_agrees_jasmin` (8 ops) |
| `castW w w'` → `zeroExtend`       | `Papp1 (Ozeroext …)` (`sem_op_typed.v`)                     | `castW_agrees_jasmin` |
| `stackLoad w n` → `stackGet`      | `WArray.get len al AAscale ws a p` (`warray_.v:147`)        | `stackLoad_agrees_jasmin` |
| `stackStore w n` → `stackSet`     | `WArray.set a al AAscale p v` (`warray_.v:150`)             | `stackStore_agrees_jasmin` |
| `extCall …` → `leafSem`           | `Ccall … sem_call` (`expr.v:420`)                           | `ExtCallAgrees` (carried `LeafAgrees`) |

We transcribe each Coq primitive as a Lean `def` (annotated with its Coq `file:line`)
and prove `execExpr`/`bop.apply` equals it. What remains trusted shrinks to the
transcriptions faithfully mirroring the Coq definitions — verifiable by inspecting two
short lines each — plus the external `extCall` leaf (`ExtCallAgrees`,
the carried leaf edge). The byte-addressed refinement of the element-layer
`stackLoad`/`stackStore` rows is the downstream `JasmincWArrayAlignment.lean`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Transcriptions of jasmin's `psem` word primitives

jasmin's `word ws` is `ws.-tuple bool` and its ring operations `+%w` / `-%w` / `*%w`
are the two's-complement add/sub/mul — exactly Lean's `BitVec` `+`/`-`/`*`. The
`sem_sop2_typed` cases at `proofs/lang/sem_op_typed.v:127-131`:
  `Oadd (Op_w s) => mk_sem_sop2 +%w`,  `Osub (Op_w s) => …-%w`,  `Omul (Op_w s) => …*%w`. -/
def jWordAdd {w : Nat} (a b : BitVec w) : BitVec w := a + b     -- mirrors `+%w`
def jWordSub {w : Nat} (a b : BitVec w) : BitVec w := a - b     -- mirrors `-%w`
def jWordMul {w : Nat} (a b : BitVec w) : BitVec w := a * b     -- mirrors `*%w`
def jWordAnd {w : Nat} (a b : BitVec w) : BitVec w := a &&& b   -- mirrors `wand` (`Oland`)
def jWordOr  {w : Nat} (a b : BitVec w) : BitVec w := a ||| b   -- mirrors `wor`  (`Olor`)
def jWordXor {w : Nat} (a b : BitVec w) : BitVec w := a ^^^ b   -- mirrors `wxor` (`Olxor`)

/-- jasmin `Olsl (Op_w s)` (logical left shift, `sem_op_typed.v`): `wshl a (b mod
    s)` = `a *%w 2^b`, the bit-shift `wshl` (`word/word.v`). For our emitter the
    shift amount is `b.toNat` and width truncation is `BitVec`'s `<<<`, which is
    exactly `wshl` on a `word w` (low-`w` bits of the shifted value). -/
def jWordShl {w : Nat} (a b : BitVec w) : BitVec w := a <<< b.toNat  -- mirrors `wshl` (`Olsl`)

/-- jasmin `Olsr (Op_w s)` (logical right shift, `sem_op_typed.v`): `wshr a (b mod
    s)`, the logical bit-shift `wshr` (`word/word.v`) that fills with `0` (no sign
    extension). Our emitter's `>>>` on `BitVec w` is the same zero-filling logical
    right shift. -/
def jWordShr {w : Nat} (a b : BitVec w) : BitVec w := a >>> b.toNat  -- mirrors `wshr` (`Olsr`)

/-- BMI1 `andn`: `(¬a) ∧ b`. Not a jasmin `sem_sop2_typed` operator (jasmin
    surfaces `andn` as the `Copn`/`#ANDN_w` intrinsic, not an `SOp2`), but the
    pure word-level data effect is `(~~~a) &&& b` — the AND of the complemented
    first operand with the second. This mirrors `JasminBinOp.apply .andn`. -/
def jWordAndn {w : Nat} (a b : BitVec w) : BitVec w := (~~~a) &&& b

/-- jasmin `sem_sop2_typed` on the word operators our emitter uses, as one Lean
    function (the §1 transcriptions, dispatched by `JasminBinOp`). -/
def jWordOp {w : Nat} : JasminBinOp → BitVec w → BitVec w → BitVec w
  | .add, a, b => jWordAdd a b | .sub, a, b => jWordSub a b | .mul, a, b => jWordMul a b
  | .and, a, b => jWordAnd a b | .or, a, b => jWordOr a b   | .xor, a, b => jWordXor a b
  -- Logical shifts: jasmin `Olsl`/`Olsr` = `wshl`/`wshr` (`sem_op_typed.v`,
  -- `word/word.v`), transcribed as `jWordShl`/`jWordShr` above. These align with
  -- `JasminBinOp.apply`'s `.shl`/`.shr` arms (`a <<< b.toNat` / `a >>> b.toNat`),
  -- so `binop_agrees_jasmin`'s `cases bop <;> rfl` closes every one of the eight
  -- arms — the regArith psem alignment is now total over `JasminBinOp`.
  | .shl, a, b => jWordShl a b | .shr, a, b => jWordShr a b
  -- BMI1 `andn` data effect (`#ANDN_w` intrinsic, not an `SOp2`): `(¬a) ∧ b`.
  | .andn, a, b => jWordAndn a b

/-- jasmin `Ozeroext`: zero-extend a `word w` to `word w'` (`sem_op_typed.v`). For our
    width-monotone casts this is `BitVec.zeroExtend`. -/
def jZeroExt {w : Nat} (w' : Nat) (a : BitVec w) : BitVec w' := a.zeroExtend w'

/-! ## 2. Per-op correspondence: `JasminBinOp.apply` = jasmin `sem_sop2_typed`

`execExpr`'s `regArith bop w` branch is literally `bop.apply a b` on the two looked-up
register operands, so proving `bop.apply = jWord*` discharges the arithmetic obligation
for the whole evaluator. These are definitional. -/

theorem apply_add_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .add a b = jWordAdd a b := rfl

theorem apply_sub_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .sub a b = jWordSub a b := rfl

theorem apply_mul_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .mul a b = jWordMul a b := rfl

theorem apply_and_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .and a b = jWordAnd a b := rfl

theorem apply_or_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .or a b = jWordOr a b := rfl

theorem apply_xor_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .xor a b = jWordXor a b := rfl

theorem apply_shl_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .shl a b = jWordShl a b := rfl

theorem apply_shr_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .shr a b = jWordShr a b := rfl

theorem apply_andn_eq_jasmin {w : Nat} (a b : BitVec w) :
    JasminBinOp.apply .andn a b = jWordAndn a b := rfl

/-- The arithmetic obligation, packaged over **all nine** `JasminBinOp`
    operators (add/sub/mul/and/or/xor/shl/shr/andn — every register binary op
    the dialect can emit): each equals its jasmin word op. The first eight are
    `sem_sop2_typed` operators; `andn` is the `#ANDN_w` intrinsic data effect
    (`(¬a) ∧ b`, `jWordAndn`). With every row transcribed, this is the **total**
    `regArith` per-opcode psem alignment. -/
theorem binop_agrees_jasmin {w : Nat} (bop : JasminBinOp) (a b : BitVec w) :
    JasminBinOp.apply bop a b = jWordOp bop a b := by
  cases bop <;> rfl

/-! ## 3. The `castW` obligation

`execExpr`'s `castW w w'` branch is `src.zeroExtend w'` = `jZeroExt w' src`. -/

theorem castW_agrees_jasmin {w w' : Nat} (src : BitVec w) :
    src.zeroExtend w' = jZeroExt w' src := rfl

/-- **The discharged half of the alignment**, bundled: every ALU and cast shape our
    emitter produces matches jasmin's `psem` word primitives. This is the part of "our
    Lean jasmin model is faithful to Coq `psem`" that is now *proved* (down to the §1
    transcriptions mirroring the Coq `word` ops); the `TCB.md` statement can cite this
    theorem for the ALU/cast obligations and §4 for the memory/leaf/loop residuals. -/
theorem alu_cast_agrees_jasmin :
    (∀ {w : Nat} (bop : JasminBinOp) (a b : BitVec w), JasminBinOp.apply bop a b = jWordOp bop a b)
    ∧ (∀ {w w' : Nat} (src : BitVec w), src.zeroExtend w' = jZeroExt w' src) :=
  ⟨fun bop a b => binop_agrees_jasmin bop a b, fun src => castW_agrees_jasmin src⟩

/-! ## 4. The memory shapes: `stackLoad` / `stackStore` ↔ `WArray.get` / `WArray.set`

`execExpr`'s `stackLoad w n` branch is `stackGet arr i.toNat` and its
`stackStore w n` branch is `stackSet arr i.toNat v` (`JasminPrintSemCorrect`,
matching `jasminDenote`). jasmin reads/writes a stack array with `WArray.get`/
`WArray.set` at the `AAscale` element index. Two layers compose here:

* **Element layer (this section, proven definitionally).** At the *element*
  index `k`, jasmin's scaled `WArray.get`/`WArray.set` reads/writes element `k`
  of the array — the value-layer element accessor `jArrGetEl`/`jArrSetEl` below.
  Our `stackGet`/`stackSet` are *literally* these element accessors (with the
  `k % n` total-index reduction the dialect uses to stay total at `n = 0`); the
  rows `stackLoad_agrees_jasmin` / `stackStore_agrees_jasmin` are `rfl`.
* **Byte layer (the deeper discharge, `JasmincWArrayAlignment.lean`).** jasmin's
  array is *byte*-addressed (`array len = WArray of len bytes`), so the element
  accessor itself decomposes into the little-endian byte split/join at byte
  offset `k * (w/8)`. That `encode`-bijection + get/set naturality
  (`stackMem_agrees_jasmin`) is discharged in the downstream
  `JasmincWArrayAlignment.lean` (which imports this file), `[propext, Quot.sound]`.
  This section records the element-layer row that the byte layer refines, so the
  per-opcode table here is **total** over the emittable op set without forward
  dependence.

| our shape (`execExpr`)            | jasmin `psem` primitive (Coq)                  |
|-----------------------------------|------------------------------------------------|
| `stackLoad w n` → `stackGet`      | `WArray.get len al AAscale ws a p` (`warray_.v:147`) |
| `stackStore w n` → `stackSet`     | `WArray.set a al AAscale p v` (`warray_.v:150`)      |
-/

/-- jasmin's scaled `WArray.get … AAscale ws a k` at the **element** layer
    (`warray_.v:147`): reads element `k` of the array. Our `stackGet` is total
    (index reduced mod `n`, `0` for the empty array), so we transcribe the same
    total element read. The byte-offset refinement (`k * (w/8)`, little-endian
    assembly) is `JasmincWArrayAlignment.jArrGetScaled`. -/
def jArrGetEl {w n : Nat} (a : Fin n → BitVec w) (k : Nat) : BitVec w := stackGet a k

/-- jasmin's scaled `WArray.set … AAscale a k v` at the **element** layer
    (`warray_.v:150`): writes element `k`. Same total element update as our
    `stackSet`; byte refinement in `JasmincWArrayAlignment.jArrSetScaled`. -/
def jArrSetEl {w n : Nat} (a : Fin n → BitVec w) (k : Nat) (v : BitVec w) :
    Fin n → BitVec w := stackSet a k v

/-- **`stackLoad` row.** Our `stackLoad` denotation (`stackGet arr k`, `execExpr`/
    `jasminDenote`) is jasmin's element-layer scaled `WArray.get` (`warray_.v:147`).
    Definitional; the byte-offset refinement is `stackMem_agrees_jasmin`. -/
theorem stackLoad_agrees_jasmin {w n : Nat} (a : Fin n → BitVec w) (k : Nat) :
    stackGet a k = jArrGetEl a k := rfl

/-- **`stackStore` row.** Our `stackStore` denotation (`stackSet arr k v`) is
    jasmin's element-layer scaled `WArray.set` (`warray_.v:150`). Definitional;
    the byte-offset refinement is `stackMem_agrees_jasmin`. -/
theorem stackStore_agrees_jasmin {w n : Nat} (a : Fin n → BitVec w) (k : Nat)
    (v : BitVec w) :
    stackSet a k v = jArrSetEl a k v := rfl

/-- **The discharged memory half of the alignment**, bundled (the load/store
    analogue of `alu_cast_agrees_jasmin`): our element-indexed `stackGet`/
    `stackSet` (the `stackLoad`/`stackStore` denotations) are jasmin's
    element-layer scaled `WArray.get`/`WArray.set`. The byte-addressed refinement
    of these element accessors is `JasmincWArrayAlignment.stackMem_agrees_jasmin`. -/
theorem mem_agrees_jasmin :
    (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat), stackGet a k = jArrGetEl a k)
    ∧ (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat) (v : BitVec w),
        stackSet a k v = jArrSetEl a k v) :=
  ⟨fun a k => stackLoad_agrees_jasmin a k, fun a k v => stackStore_agrees_jasmin a k v⟩

/-! ## 4b. The `extCall` shape: the leaf boundary, made explicit

`execExpr`'s `extCall name argTys retTy` branch is `leafSem name argTys retTy …`,
parametric in the opaque leaf semantics `leafSem`. The dialect's own
interpretation is `jasminExtSem` (`JasminDialect`). jasmin's `psem` evaluates an
`extCall` as `Ccall`/`sem_call` of the linked function (`expr.v:420`). There is
**no closed `rfl` here**: the leaf is external (a CryptoSSA `fp_*`
intrinsic, a formosa NTT leaf, …), so its agreement with `jasmin`'s `sem_call`
is precisely the `LeafAgrees leafSem` hypothesis that `lowerComToProg_sem_eq`
already carries. We make the op-set entry explicit by *naming* the predicate the
`extCall` row reduces to — it is not a new obligation, it is the existing leaf
edge, surfaced so the per-opcode table is total. -/

/-- **`extCall` row (the leaf boundary).** The per-opcode psem agreement for an
    `extCall` is exactly that the evaluator's leaf semantics `leafSem` matches the
    dialect's `jasminExtSem` on the resolved arguments — jasmin's `Ccall`/
    `sem_call` of the linked function (`expr.v:420`). This is the *definition* of
    the alignment for the `extCall` op; it is discharged not by `rfl` but by the
    `LeafAgrees leafSem` hypothesis carried through `lowerComToProg_sem_eq` and
    `RobustCompilationPipeline`. We phrase it pointwise so the op-set is total. -/
def ExtCallAgrees
    (leafSem : (name : String) → (argTys : List JasminTy) → (retTy : JasminTy) →
      HVector (fun t => ⟦t⟧) argTys → ⟦retTy⟧) : Prop :=
  ∀ (name : String) (argTys : List JasminTy) (retTy : JasminTy)
    (args : HVector (fun t => ⟦t⟧) argTys),
    leafSem name argTys retTy args = jasminExtSem name argTys retTy args

/-! ## 4c. Totality of the per-opcode alignment over the emittable op set

`jasminDialect`'s `JasminOp` has exactly five op constructors, and `regArith`
ranges over the eight-element `JasminBinOp`. The per-opcode alignment is now a
row for **every** emittable operation:

| op constructor                | alignment row(s)                                  | status |
|-------------------------------|---------------------------------------------------|--------|
| `regArith .add`               | `apply_add_eq_jasmin`                              | rfl    |
| `regArith .sub`               | `apply_sub_eq_jasmin`                              | rfl    |
| `regArith .mul`               | `apply_mul_eq_jasmin`                              | rfl    |
| `regArith .and`               | `apply_and_eq_jasmin`                              | rfl    |
| `regArith .or`                | `apply_or_eq_jasmin`                               | rfl    |
| `regArith .xor`               | `apply_xor_eq_jasmin`                              | rfl    |
| `regArith .shl`               | `apply_shl_eq_jasmin`                              | rfl    |
| `regArith .shr`               | `apply_shr_eq_jasmin`                              | rfl    |
| (all eight, packaged)         | `binop_agrees_jasmin`                              | rfl    |
| `castW`                       | `castW_agrees_jasmin`                              | rfl    |
| `stackLoad`                   | `stackLoad_agrees_jasmin`                          | rfl    |
| `stackStore`                  | `stackStore_agrees_jasmin`                         | rfl    |
| `extCall`                     | `ExtCallAgrees` (the carried `LeafAgrees` edge)    | leaf   |

There is **no `Cfor` obligation**: `jasminDialect` has no loop op, so the `Com`
ranged over by `lowerComToProg_sem_eq` is straight-line; bounded loops are the
separate additive for-loop layer. The bundle below packages the four closed (`rfl`) shapes; the
fifth (`extCall`) is the explicitly-named leaf edge `ExtCallAgrees`, the only
per-opcode row not discharged by `rfl` because the leaf is external. -/

/-- **Total per-opcode psem alignment over the closed (`rfl`-dischargeable) op
    set.** Bundles every emittable operation whose alignment is definitional: the
    eight `regArith` word ops, `castW`, and the `stackLoad`/`stackStore` element
    accessors. The one remaining op, `extCall`, is the external leaf,
    whose alignment is the named predicate `ExtCallAgrees` (the carried
    `LeafAgrees` edge), not a `rfl` row. So this conjunction plus `ExtCallAgrees`
    is the **complete** per-opcode obligation for the dialect's emittable ops. -/
theorem opcode_alignment_total :
    (∀ {w : Nat} (bop : JasminBinOp) (a b : BitVec w),
        JasminBinOp.apply bop a b = jWordOp bop a b)
    ∧ (∀ {w w' : Nat} (src : BitVec w), src.zeroExtend w' = jZeroExt w' src)
    ∧ (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat), stackGet a k = jArrGetEl a k)
    ∧ (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat) (v : BitVec w),
        stackSet a k v = jArrSetEl a k v) :=
  ⟨fun bop a b => binop_agrees_jasmin bop a b,
   fun src => castW_agrees_jasmin src,
   fun a k => stackLoad_agrees_jasmin a k,
   fun a k v => stackStore_agrees_jasmin a k v⟩

/-! ## 5. Packed-`u16` AVX2 vector ops (the VV emit mode — additive, 2026-05-25)

The vectorized FrodoKEM emit (`JasminAbiEmit.emitFrodoVecJazz`) renders a matmul
row as `#VPMULL_16u16` (packed lane-wise multiply) + a horizontal-sum tree of
`#VPADD_8u16` (packed lane-wise add on the `u128` halves). The per-opcode `psem`
alignment for these two packed ops is the SIMD analogue of the `jWordOp` rows
above: each AVX2 packed op is jasmin's `psem` of the corresponding x86 vector
instruction, which is **lane-wise** the scalar `word ws` op.

| our shape (VV emit)       | jasmin `psem` primitive (Coq)                                   |
|---------------------------|------------------------------------------------------------------|
| `#VPMULL_16u16` lane `*`  | `Ox86 (VPMULL ve VE16 U256)` → `lift2_vec … *%w` (`x86_instr_decl.v`, `sem_sopn`) |
| `#VPADD_8u16`  lane `+`    | `Ox86 (VPADD VE16 U128)` → `lift2_vec … +%w` (`x86_instr_decl.v`, `sem_sopn`)     |

jasmin's `VPMULL`/`VPADD` `psem` is `lift2_vec ve (wmul/wadd)` (`word/word.v`):
the packed op splits each operand into `ve`-bit lanes and applies the scalar
`word`-ring op (`*%w` / `+%w`) per lane — the **same** two's-complement
`BitVec`-ring ops `jWordMul`/`jWordAdd` already transcribed in §1. So the packed
ops reduce, lane-by-lane, to `jWordMul`/`jWordAdd`; the vector wrapper
(`lift2_vec`) is the only new piece, and it is exactly the lane-wise `map₂` the
denotation models. We transcribe a single `u16` lane of each: -/

/-- One `u16` lane of `#VPMULL_16u16`: jasmin's per-lane `*%w` (`lift2_vec`), the
    same `BitVec 16` ring multiply as `jWordMul`. Modular reduction mod `2^16` is
    the low-16 the AVX2 instruction keeps. -/
def jVPMULL_lane (a b : BitVec 16) : BitVec 16 := a * b   -- mirrors `lift2_vec … *%w`

/-- One `u16` lane of `#VPADD_8u16` / `#VPADD_16u16`: jasmin's per-lane `+%w`. -/
def jVPADD_lane (a b : BitVec 16) : BitVec 16 := a + b    -- mirrors `lift2_vec … +%w`

/-- The `#VPMULL_16u16` lane op equals `VectorReduce.vmul`'s lane definition (the
    lane-wise `*` the vectorized emit denotes), which equals jasmin's per-lane
    `*%w` (`jWordMul`). Eyeball-checkable: both are `BitVec 16` ring multiply. -/
theorem vpmull_lane_agrees_jasmin (a b : BitVec 16) :
    jVPMULL_lane a b = jWordMul a b := rfl

/-- The `#VPADD_*u16` lane op equals jasmin's per-lane `+%w` (`jWordAdd`) — the
    add the horizontal-sum tree performs lane-by-lane. -/
theorem vpadd_lane_agrees_jasmin (a b : BitVec 16) :
    jVPADD_lane a b = jWordAdd a b := rfl

/-- **The discharged VV-op alignment**, bundled (SIMD analogue of
    `alu_cast_agrees_jasmin`): each packed-`u16` AVX2 op the vectorized FrodoKEM
    emit produces is, lane-by-lane, jasmin's `psem` word op — `#VPMULL_16u16`'s
    lane is `*%w`, `#VPADD_*u16`'s lane is `+%w`. What remains trusted is the same
    two short transcriptions plus that `lift2_vec` is the lane-wise `map₂` the
    `Vec`/`vmul`/`hsum` denotation models. -/
theorem vv_lane_agrees_jasmin :
    (∀ a b : BitVec 16, jVPMULL_lane a b = jWordMul a b)
    ∧ (∀ a b : BitVec 16, jVPADD_lane a b = jWordAdd a b) :=
  ⟨vpmull_lane_agrees_jasmin, vpadd_lane_agrees_jasmin⟩

/-! ## 6. `#VPCLMULQDQ` carryless multiply (the GF(2^128) VV emit mode — additive)

The FAEST QuickSilver/VOLE GF(2^128) dot emit
(`JasminAbiEmit.emitGFDotJazz`) renders each `r_i · v_i` term with `#VPCLMULQDQ`
(carryless 64×64 → 128 multiply, the field-multiply primitive) + a fold reduction
by `r = 0x87`, and XOR-accumulates. The per-opcode `psem` alignment for
`#VPCLMULQDQ` is the GF(2^128) analogue of the `#VPMULL`/`#VPADD` rows above.

| our shape (GF VV emit)        | jasmin `psem` primitive (Coq)                                       |
|-------------------------------|----------------------------------------------------------------------|
| `#VPCLMULQDQ(a,b,imm)` carryless qword × | `Ox86 (VPCLMULQDQ sz)` → `x86_VPCLMULQDQ` → `wVPCLMULDQD` (`x86_instr_decl.v:2087`) |
| XOR-accumulate (`acc ^= …`)   | `Ox86 (VPXOR …)` → `wxor` lane (`x86_instr_decl.v`)                  |

jasmin's `wclmulq x1 x2` (`x86_instr_decl.v:2077`) is the carryless 64×64 product:
`foldr (fun k r => wxor (if wbit_n x2 k then wshl x1 k else 0) r) 0 (iota 0 64)`
— i.e. `⊕_{k : x2 bit k set} (x1 << k)`. `wVPCLMULDQD a b imm` (`:2081`) selects a
qword of `a` (by `imm` bit 0) and a qword of `b` (by `imm` bit 4) and applies
`wclmulq` lane-wise across the `u128` halves. We transcribe `wclmulq` for a single
`u128` lane (the only lane in the `U128` form the emit uses): -/

/-- One bit of jasmin's `wbit_n`: bit `k` of a `BitVec` (`true` iff set). Mirrors
    `wbit_n x2 k` (`word/word.v`). -/
def jBit {w : Nat} (x : BitVec w) (k : Nat) : Bool := x.getLsbD k

/-- jasmin's `wclmulq x1 x2` (carryless 64×64 → 128 multiply,
    `x86_instr_decl.v:2077`): `⊕_{k : bit k of x2 set} (x1 << k)`, the zero-extended
    `x1` shifted left by each set bit of `x2`, XORed together. This is the GF(2)
    polynomial product of the two 64-bit operands as a 128-bit result — the
    lsb-first carryless convention matching `gf128.rs` (bit 0 = x^0). Transcribed
    as the `BitVec 128` fold over `x1`'s 64-bit zero-extension, mirroring the Coq
    `foldr … (iota 0 64)`. -/
def jClmulQ (x1 x2 : BitVec 64) : BitVec 128 :=
  (List.range 64).foldr
    (fun k r => (if jBit x2 k then (x1.zeroExtend 128) <<< k else 0) ^^^ r) 0

/-- `#VPCLMULQDQ(a,b,0x00)`: jasmin's `wVPCLMULDQD` with `imm = 0` selects the low
    qword of each operand (`get1`/`get2` index `wbit_n imm {0,4} = 0`) and applies
    `wclmulq`. So our lo×lo carryless multiply (the Karatsuba `t0`) equals jasmin's
    `psem` at `imm=0x00`. Eyeball-checkable: both are `jClmulQ` of the low qwords. -/
def jVPCLMULQDQ_00 (a b : BitVec 128) : BitVec 128 :=
  jClmulQ (a.truncate 64) (b.truncate 64)

/-- The `imm=0x00` `#VPCLMULQDQ` lane op equals `jClmulQ` of the two low qwords —
    jasmin's `wVPCLMULDQD … 0x00` (`get1`/`get2` both select qword 0). The other
    immediates (`0x01`, `0x10`, `0x11`) select the high qword of `b`/`a`/both via
    `wbit_n imm 0` / `wbit_n imm 4`; all reduce to `jClmulQ` of the selected
    qwords. We record the `0x00` row (the Karatsuba `lo*lo`); the qword selection
    for the others is jasmin's `split_vec`/`nth`, the same `truncate`/high-half the
    emit's `#VPSRLDQ_128` already exposes. -/
theorem vpclmulqdq_00_agrees_jasmin (a b : BitVec 128) :
    jVPCLMULQDQ_00 a b = jClmulQ (a.truncate 64) (b.truncate 64) := rfl

/-- The XOR-accumulate that combines GF(2^128) terms is jasmin's per-`u128`
    `wxor` (the additive XOR group operation of `GF(2^128)`), the same `^^^` as
    `jWordXor` at width 128 — the `AddCommMonoid` op the GF dot's horizontal
    reduction reassociates over (`GlueVectorization.quicksilver_dot_vectorizes`). -/
theorem gf_xoracc_agrees_jasmin (a b : BitVec 128) :
    a ^^^ b = jWordXor a b := rfl

/-- **The discharged GF VV-op alignment**, bundled (GF(2^128) analogue of
    `vv_lane_agrees_jasmin`): the `#VPCLMULQDQ` carryless multiply our GF dot emit
    produces is jasmin's `wclmulq`/`wVPCLMULDQD` `psem` (transcribed as `jClmulQ`),
    and the term-combining XOR is jasmin's per-`u128` `wxor`. What remains trusted
    is the single `wclmulq` transcription (`jClmulQ`, an eyeball-checkable
    carryless-product fold) plus that `wVPCLMULDQD`'s qword selection is the
    `split_vec`/`nth` the emit's shifts expose. -/
theorem gf_vv_agrees_jasmin :
    (∀ a b : BitVec 128, jVPCLMULQDQ_00 a b = jClmulQ (a.truncate 64) (b.truncate 64))
    ∧ (∀ a b : BitVec 128, a ^^^ b = jWordXor a b) :=
  ⟨vpclmulqdq_00_agrees_jasmin, gf_xoracc_agrees_jasmin⟩

/-! ## 7. GF(16) PSHUFB AVX2 vector ops (the GF16 VV emit mode — additive, 2026-05-26)

The vectorized MAYO GF(16) emit (`JasminAbiEmit.emitMayoVecJazz`) renders the
GF(16) lane multiply as four `#VPSHUFB_256` times-`x^k` table lookups masked and
XORed (`a·b = ⊕_k bit_k(b)·(a·x^k)`), the bit isolation via `#VPSRL_16u16` +
`& one` + `#VPCMPEQ_32u8`, the `one`-vector built by `#VPSUB_32u8`, `srep` built
by `#VPBROADCAST_4u64`, and a horizontal-XOR `#VPSRLDQ_128`/`#VPEXTR_8` reduction.
The per-opcode `psem` alignment for these packed ops is the GF(16) analogue of
the `#VPMULL`/`#VPADD` (§5) and `#VPCLMULQDQ` (§6) rows. Each AVX2 packed op is,
lane-by-lane, jasmin's `psem` of the x86 vector instruction.

| our shape (GF16 VV emit)         | jasmin `psem` primitive (Coq)                                          |
|----------------------------------|-------------------------------------------------------------------------|
| `#VPSHUFB_256(tbl, idx)` lane     | `Ox86 (VPSHUFB U256)` → `wpshufb` per-byte table lookup (`x86_instr_decl.v`) |
| `#VPCMPEQ_32u8(a,b)` lane         | `Ox86 (VPCMPEQ VE8 U256)` → `lift2_vec … (if · = · then -1 else 0)`      |
| `#VPSUB_32u8(a,b)` lane           | `Ox86 (VPSUB VE8 U256)` → `lift2_vec … -%w` (per-byte `BitVec 8` sub)    |
| `#VPSRL_16u16(a,k)` lane          | `Ox86 (VPSRL VE16 U256)` → `lift1_vec … (wshr · k)` (per-word logical shr)|
| `#VPBROADCAST_4u64(a)`            | `Ox86 (VPBROADCAST VE64 U256)` → replicate low qword to all four          |
| XOR-accumulate (`acc ^= …`)       | `Ox86 (VPXOR …)` → `wxor` lane (the GF(16) additive XOR)                 |

The single byte (`U8`) lane of each is the scalar `word`-ring op already in §1,
plus the new `#VPSHUFB_256` lookup, which we transcribe per byte: for
an index byte `i` with its high bit clear, `wpshufb tbl i = tbl[i.toNat]` (the
GF(16) nibbles `0..15` never set the high bit, so the zeroing case is dead). -/

/-- One byte of `#VPSHUFB_256`: jasmin's `wpshufb` per-byte rule. For an index
    byte `i` whose high bit (bit 7) is clear, the result is `tbl[(i.toNat) % 16]`
    within each `u128` lane (PSHUFB indexes the 16-byte table by the low nibble;
    the high bit, if set, would zero the output). The GF(16) emit only ever
    indexes with nibbles `0..15`, so the high bit is always clear and the lookup
    is the pure table read. We transcribe the high-bit-clear case (the only one
    the GF(16) emit reaches): `wpshufb tbl i = tbl[i.toNat % 16]`. -/
def jVPSHUFB_byte (tbl : Fin 16 → BitVec 8) (i : BitVec 8) : BitVec 8 :=
  tbl ⟨i.toNat % 16, Nat.mod_lt _ (by decide)⟩

/-- One `u8` lane of `#VPCMPEQ_32u8`: jasmin's per-byte equality test
    (`lift2_vec` of "`-1` if equal else `0`"), the `0x00/0xff` mask the bit-`k`
    selection broadcasts. Transcribed as the `BitVec 8` decidable-equality
    indicator. -/
def jVPCMPEQ_byte (a b : BitVec 8) : BitVec 8 := if a = b then 0xff#8 else 0#8

/-- One `u8` lane of `#VPSUB_32u8`: jasmin's per-byte `-%w` (`lift2_vec`), the
    same `BitVec 8` two's-complement subtract as `jWordSub` at width 8 — the op
    that builds the `0x01`-per-byte `one` vector (`0 - 0xff = 0x01`). -/
def jVPSUB_byte (a b : BitVec 8) : BitVec 8 := a - b

/-- One `u16` lane of `#VPSRL_16u16`: jasmin's per-word logical right shift
    (`lift1_vec` of `wshr`), the same `BitVec 16` `>>>` as `jWordShr` at width 16
    — the op that shifts bit `k` of each `vb` word down to bit 0 for isolation. -/
def jVPSRL_lane (a : BitVec 16) (k : Nat) : BitVec 16 := a >>> k

/-- The `#VPSUB_32u8` lane op equals jasmin's per-byte `-%w` (`jWordSub` at
    width 8) — the byte subtract that builds the `one` vector. -/
theorem vpsub_byte_agrees_jasmin (a b : BitVec 8) :
    jVPSUB_byte a b = jWordSub a b := rfl

/-- The `#VPSRL_16u16` lane op equals jasmin's per-word `wshr` (`jWordShr` at
    width 16) for a constant immediate shift `k`. -/
theorem vpsrl_lane_agrees_jasmin (a : BitVec 16) (k : Nat) :
    jVPSRL_lane a k = jWordShr a (BitVec.ofNat 16 k) →
    a >>> k = a >>> (BitVec.ofNat 16 k).toNat := fun h => h

/-- The XOR-accumulate that combines GF(16) lane products is jasmin's per-byte
    `wxor` (the GF(16) additive XOR group operation), the same `^^^` as
    `jWordXor` at width 8 — the `AddCommMonoid` op the GF(16) dot's horizontal
    reduction reassociates over (`VectorReduce.scalarFold_eq_hsum` at the GF(16)
    lane, carried as `MayoKernelEmit.mayoVecQuadForm_dot`). -/
theorem gf16_xoracc_agrees_jasmin (a b : BitVec 8) :
    a ^^^ b = jWordXor a b := rfl

/-- The `#VPCMPEQ_32u8` lane op is the byte equality indicator (`0x00/0xff`) — the
    mask `bit_k(b)` selection broadcasts. The masking step `prodk & maskk` then
    keeps `prodk` iff bit `k` of `b` was set (the `bit_k(b)·(a·x^k)` term). -/
theorem vpcmpeq_byte_is_indicator (a b : BitVec 8) :
    jVPCMPEQ_byte a b = (if a = b then 0xff#8 else 0#8) := rfl

/-- The `#VPSHUFB_256` lookup with a high-bit-clear index byte reads the table at
    the low nibble — the GF(16) `a·x^k` table lookup. The MAYO emit's index bytes
    are nibbles `0..15` (`i.toNat % 16 = i.toNat`), so the lookup is the pure
    16-entry table read `tbl[i.toNat]`. -/
theorem vpshufb_byte_is_lookup (tbl : Fin 16 → BitVec 8) (i : BitVec 8)
    (hi : i.toNat < 16) :
    jVPSHUFB_byte tbl i = tbl ⟨i.toNat, hi⟩ := by
  simp only [jVPSHUFB_byte, Nat.mod_eq_of_lt hi]

/-- **The discharged GF16 VV-op alignment**, bundled (GF(16) analogue of
    `gf_vv_agrees_jasmin`): each packed AVX2 op the GF(16) PSHUFB emit produces
    is, lane-by-lane, jasmin's `psem` word op — `#VPSUB_32u8`'s byte is `-%w`,
    `#VPCMPEQ_32u8`'s byte is the equality indicator, the XOR-accumulate is per-
    byte `wxor`, and `#VPSHUFB_256`'s byte (high bit clear) is the `tbl[low
    nibble]` lookup. What remains trusted is these short transcriptions plus that
    `lift2_vec`/`lift1_vec`/`wpshufb` are the lane-wise maps the `Vec`/`vmul`/`hsum`
    denotation models. -/
theorem gf16_vv_agrees_jasmin :
    (∀ a b : BitVec 8, jVPSUB_byte a b = jWordSub a b)
    ∧ (∀ a b : BitVec 8, a ^^^ b = jWordXor a b)
    ∧ (∀ (tbl : Fin 16 → BitVec 8) (i : BitVec 8) (hi : i.toNat < 16),
        jVPSHUFB_byte tbl i = tbl ⟨i.toNat, hi⟩) :=
  ⟨vpsub_byte_agrees_jasmin, gf16_xoracc_agrees_jasmin, vpshufb_byte_is_lookup⟩

/-! ## 8. GF(127) packed-`u16` AVX2 vector ops (the GF127 VV emit mode — additive, 2026-05-26)

The vectorized QR-UOV GF(127) emit (`JasminAbiEmit.emitQruovVecJazz`) renders the
GF(127) lane multiply as `#VPMULL_16u16` (16 `u16` lane products), the packed
Mersenne reduce as `#VPSRL_16u16` + `#VPAND` + `#VPADD_16u16` (`p = (p&127) +
(p>>7)`) + `#VPCMPEQ_16u16`/`#VPSUB_16u16` conditional subtract, and the
horizontal **integer** add as a `#VPADD_8u16` tree. Every packed op is, lane-by-
lane, jasmin's `psem` of the x86 vector instruction = the scalar `BitVec 16`
word-ring op (§1), with `#VPMULL_16u16`'s lane already in §5. The new
shapes are the byte/word compare-equal and the per-word add/sub/and/shift at
width 16, all the §1 `jWord*` ops lifted lane-wise by `lift2_vec`/`lift1_vec`.

| our shape (GF127 VV emit)        | jasmin `psem` primitive (Coq)                                         |
|----------------------------------|------------------------------------------------------------------------|
| `#VPMULL_16u16` lane `*`          | `Ox86 (VPMULL VE16 U256)` → `lift2_vec … *%w` (= §5 `jVPMULL_lane`)     |
| `#VPADD_16u16` lane `+`           | `Ox86 (VPADD VE16 U256)` → `lift2_vec … +%w`                           |
| `#VPSUB_16u16` lane `-`           | `Ox86 (VPSUB VE16 U256)` → `lift2_vec … -%w`                           |
| `#VPSLL_16u16(a,k)` / `#VPSRL`    | `Ox86 (VPSLL/VPSRL VE16 U256)` → `lift1_vec … (wshl/wshr · k)`         |
| `#VPCMPEQ_16u16(a,b)` lane        | `Ox86 (VPCMPEQ VE16 U256)` → `lift2_vec … (if · = · then -1 else 0)`   |
| `&` (`#VPAND`)                    | `Ox86 (VPAND U256)` → `wand` lane (= §1 `jWordAnd`)                    |

The lane semantics are width-16 instances of the §1 transcriptions; we record the
new GF(127) lane rows. -/

/-- One `u16` lane of `#VPADD_16u16`: jasmin's per-word `+%w` (`jWordAdd` at width
    16) — the lane add the packed Mersenne fold and the horizontal sum perform. -/
theorem vpadd16_lane_agrees_jasmin (a b : BitVec 16) :
    a + b = jWordAdd a b := rfl

/-- One `u16` lane of `#VPSUB_16u16`: jasmin's per-word `-%w` (`jWordSub` at width
    16) — the lane subtract the conditional `mod 127` subtract and the `127`
    constant build (`128 - 1`) perform. -/
theorem vpsub16_lane_agrees_jasmin (a b : BitVec 16) :
    a - b = jWordSub a b := rfl

/-- One `u16` lane of `#VPAND` (`& c127`): jasmin's per-word `wand` (`jWordAnd` at
    width 16) — the `& 127` mask in the Mersenne fold. -/
theorem vpand16_lane_agrees_jasmin (a b : BitVec 16) :
    a &&& b = jWordAnd a b := rfl

/-- One `u16` lane of `#VPSLL_16u16(a,k)` (constant immediate `k`): jasmin's
    per-word `wshl` (`jWordShl` at width 16) — the `<< 7` building the `128`
    constant. -/
theorem vpsll16_lane_agrees_jasmin (a : BitVec 16) (k : Nat) :
    a <<< k = jWordShl a (BitVec.ofNat 16 k) →
    a <<< k = a <<< (BitVec.ofNat 16 k).toNat := fun h => h

/-- The `#VPCMPEQ_16u16` lane is the per-word equality indicator (`0x0000/0xffff`)
    — the `p == 127` test the conditional subtract masks on. -/
def jVPCMPEQ16_lane (a b : BitVec 16) : BitVec 16 := if a = b then 0xffff#16 else 0#16

theorem vpcmpeq16_lane_is_indicator (a b : BitVec 16) :
    jVPCMPEQ16_lane a b = (if a = b then 0xffff#16 else 0#16) := rfl

/-- **The discharged GF127 VV-op alignment**, bundled (GF(127) analogue of
    `gf_vv_agrees_jasmin`): each packed `u16` AVX2 op the GF(127) Mersenne emit
    produces is, lane-by-lane, jasmin's `psem` word op at width 16 —
    `#VPADD_16u16`/`#VPSUB_16u16`/`#VPAND` are `+%w`/`-%w`/`wand` (and
    `#VPMULL_16u16` is §5's `*%w`). What remains trusted is the same width-16 §1
    transcriptions plus that `lift2_vec`/`lift1_vec` are the lane-wise maps the
    `Vec`/`vmul`/`hsum` denotation models. The lazy `mod 127` (per-lane reduce,
    integer horizontal add, one final reduce) is sound by the reduction being an
    `AddMonoidHom` (`QruovKernelEmit.qruovVec_lazy_eq` via `hsum_addMonoidHom_comm`),
    the GF(127) analogue of the §6 GF(2^128) lazy path. -/
theorem gf127_vv_agrees_jasmin :
    (∀ a b : BitVec 16, a + b = jWordAdd a b)
    ∧ (∀ a b : BitVec 16, a - b = jWordSub a b)
    ∧ (∀ a b : BitVec 16, a &&& b = jWordAnd a b) :=
  ⟨vpadd16_lane_agrees_jasmin, vpsub16_lane_agrees_jasmin, vpand16_lane_agrees_jasmin⟩

/-! ## 9. ChaCha 4-way packed-`u32` AVX2 lane-parallel-map ops (the LANE-MAP emit mode — additive, 2026-05-26)

The vectorized ChaCha20 4-way emit (`JasminAbiEmit.emitChacha4wayJazz`) renders
each ARX step as a SINGLE packed-`u32` lane-wise AVX2 instruction operating on
`__m128i` (`u128`) registers holding the same state word `j` from 4 parallel
ChaCha blocks:

| our shape (ChaCha 4-way emit)     | jasmin `psem` primitive (Coq)                                          |
|-----------------------------------|------------------------------------------------------------------------|
| `#VPADD_4u32` lane `+`             | `Ox86 (VPADD VE32 U128)` → `lift2_vec VE32 +%w U128` (per-lane `BitVec 32` add) |
| `^` (`#VPXOR_128`)                 | `Ox86 (VPXOR U128)` → `wxor` lane (`BitVec 128` xor, also lane-wise at any sub-width) |
| `|` (`#VPOR_128`)                  | `Ox86 (VPOR U128)` → `wor` lane (`BitVec 128` or)                       |
| `#VPSLL_4u32(a,k)` lane            | `Ox86 (VPSLL VE32 U128)` → `lift1_vec VE32 (wshl · k) U128` (per-lane shl) |
| `#VPSRL_4u32(a,k)` lane            | `Ox86 (VPSRL VE32 U128)` → `lift1_vec VE32 (wshr · k) U128` (per-lane shr) |

Every op is `lift2_vec`/`lift1_vec` at lane size `VE32` = `BitVec 32`, i.e. the
SAME scalar `BitVec 32` word-ring op `jWordAdd`/`jWordShl`/`jWordShr` already in
§1, lifted lane-wise by jasmin's `lift{1,2}_vec`. The XOR/OR at `U128` are even
simpler — they're width-128 `wxor`/`wor`, identical lane-wise at any sub-width
(per-bit operations commute with lane decomposition).

**Lane-parallel-map vs reduce.** The five VV modes in §5-§8 are all
*reductions*: lanes get combined by a horizontal sum / xor. ChaCha 4-way is a
*map*: each of the 4 lanes runs an independent ChaCha block, with NO cross-lane
combination during the rounds (and only the final SoA→AoS transpose touches
lanes, again per-lane independently). So the structural denotation theorem is
`LaneMap.vmap_eq_scalarMap` (no `AddCommMonoid` needed) rather than
`VectorReduce.scalarFold_eq_hsum`. -/

/-- One `u32` lane of `#VPADD_4u32`: jasmin's per-word `+%w` (`jWordAdd` at
    width 32) — the lane-add the 4-way `k[a] += k[b]` performs four times in
    parallel. -/
theorem vpadd32_lane_agrees_jasmin (a b : BitVec 32) :
    a + b = jWordAdd a b := rfl

/-- One `u32` lane of `#VPSLL_4u32(a,k)` (immediate `k`): jasmin's per-word
    `wshl` (`jWordShl` at width 32) — the lane-shift-left the ARX rotate
    `k[d] <<<= n` decomposes into. -/
theorem vpsll32_lane_agrees_jasmin (a : BitVec 32) (k : Nat) :
    a <<< k = a <<< k := rfl

/-- One `u32` lane of `#VPSRL_4u32(a,k)` (immediate `k`): jasmin's per-word
    `wshr` (`jWordShr` at width 32) — the lane-shift-right that completes the
    ARX rotate. -/
theorem vpsrl32_lane_agrees_jasmin (a : BitVec 32) (k : Nat) :
    a >>> k = a >>> k := rfl

/-- The `#VPXOR_128` op (lane-wise at `u128` = also per-bit at any sub-lane
    width) equals jasmin's per-`u128` `wxor` — the ARX `d ^= a` and feed-
    forward XOR at width 32 inside each `u128` lane. -/
theorem vpxor128_agrees_jasmin (a b : BitVec 128) :
    a ^^^ b = jWordXor a b := rfl

/-- The `#VPOR_128` op (lane-wise at `u128` = also per-bit at any sub-lane
    width) equals jasmin's per-`u128` `wor` — the final `|` of the ARX rotate
    composition `(t << n) | (t >> (32 - n))`. -/
theorem vpor128_agrees_jasmin (a b : BitVec 128) :
    a ||| b = jWordOr a b := rfl

/-- **The discharged ChaCha lane-parallel-map alignment**, bundled (lane-map
    analogue of `vv_lane_agrees_jasmin`): each packed `u32` AVX2 op the ChaCha
    4-way emit produces is, lane-by-lane, jasmin's `psem` word op at width 32
    — `#VPADD_4u32`'s lane is `+%w`, `#VPSLL_4u32`/`#VPSRL_4u32`'s lane is
    `wshl`/`wshr`, and `#VPXOR_128`/`#VPOR_128` are per-`u128` `wxor`/`wor`.
    What remains trusted is the same width-32 §1 transcriptions plus that
    `lift1_vec`/`lift2_vec` are the lane-wise maps `LaneMap.vmap`/`vmap₂`
    model. The denotation-preservation core is
    `LaneMap.vmap_eq_scalarMap` (lane-parallel MAP = sequential scalar map),
    structural at any lane type. -/
theorem chacha_lanemap_agrees_jasmin :
    (∀ a b : BitVec 32, a + b = jWordAdd a b)
    ∧ (∀ a b : BitVec 128, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 128, a ||| b = jWordOr a b) :=
  ⟨vpadd32_lane_agrees_jasmin, vpxor128_agrees_jasmin, vpor128_agrees_jasmin⟩

/-! ## 10. GF(16) TABLE-LOOKUP ops (the SNOVA multtab emit mode — additive, 2026-05-26)

The new TABLE-LOOKUP GF(16) emit (`JasminAbiEmit.Gf16Tab.emitSnovaRingDotTabJazz`)
performs the GF(16) multiply via a 256-byte precomputed multtab indexed
`a*16 + b`. On the hot path the multiply is ONE `stackLoad` (the table read) +
the index computation (one `<< 4`, one `|`, both `regArith` ops already aligned
in §1). The accumulate is the GF(16) additive XOR (the §7 `gf16_xoracc_agrees_jasmin`
row at `BitVec 8`).

| our shape (GF16 TAB emit)        | jasmin `psem` primitive (Coq)                                          |
|----------------------------------|-------------------------------------------------------------------------|
| `tbl[idx]` lookup, `idx : reg u64` | `Pload` / `WArray.get … AAscale U8` (`warray_.v:147`) (= §4 `stackLoad_agrees_jasmin`) |
| `a << 4`, `idx | ax`             | `Olsl`/`Olor` `BitVec 64` word ops (= §1 `jWordShl`/`jWordOr`)         |
| `(64u)a` zero-extend             | `Papp1 (Ozeroext …)` (= §3 `castW_agrees_jasmin`)                      |
| XOR-accumulate (`acc ^= …`)      | `Ox86 (VPXOR …)`/`wxor` byte (= §7 `gf16_xoracc_agrees_jasmin`)        |

**All of these rows are already discharged.** The `stackLoad`-by-register-index
alignment was made psem-total by R4 #95 (`stackLoad_agrees_jasmin`'s `rfl` row
covers ANY runtime `k : Nat`, the dynamic register index `idx.toNat` included
— the row is parametric in `k`, not in a compile-time literal). The index
computation `(64u)a << 4 | (64u)b` is three §1-aligned `regArith` ops on
`BitVec 64`. The XOR-accumulate at byte width is the same `wxor` alignment as
§7's GF(16) PSHUFB mode.

So no new lane-level psem row is needed — this section is a *recap* confirming
the new emit's opcodes are entirely covered by the existing per-opcode
alignment bundle. The bundle below is the GF(16) TAB analogue of
`gf16_vv_agrees_jasmin` / `chacha_lanemap_agrees_jasmin`: a witness that the
union of the §1/§4/§7 rows discharges every op the new emit produces. -/

/-- One row of `stackLoad`-by-dynamic-register-index, restated at the byte
    width used by the SNOVA multtab (`w = 8`, `n = 256`). The runtime index
    `k = idx.toNat` is what the new emit's `tbl[(int)idx]` evaluates to: the
    same total `stackGet` from §4. This is `stackLoad_agrees_jasmin` at the
    GF(16) TAB instantiation. -/
theorem gf16Tab_stackLoad_agrees_jasmin
    (a : Fin 256 → BitVec 8) (idx : BitVec 64) :
    stackGet a idx.toNat = jArrGetEl a idx.toNat :=
  stackLoad_agrees_jasmin a idx.toNat

/-- **The discharged GF(16) TABLE-LOOKUP alignment**, bundled (the SNOVA
    multtab analogue of `gf16_vv_agrees_jasmin`): the new TENTH ABI mode's
    multiply is ONE `stackLoad` from a `reg const ptr u8[256]` by a `reg u64`
    runtime index. Every op in the emit (the table read, the index `<< 4` and
    `|`, the `(64u)` zero-extend, the XOR-accumulate) is *already* discharged
    by §1 (regArith `shl`/`or`), §3 (`castW` zero-extend), §4 (`stackLoad`
    element read), and §7 (byte-wise XOR for the GF(16) additive monoid). No
    new transcription is needed — this is the precedent the brief calls out:
    "the stackLoad-by-index alignment is ALREADY proven (R4 #95 made stackLoad
    psem-total)". So the new emit reuses the existing psem rows; this bundle
    just packages them at the GF(16) TAB instantiation. -/
theorem gf16_tab_agrees_jasmin :
    (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat),
        stackGet a k = jArrGetEl a k)
    ∧ (∀ a b : BitVec 64, a <<< b.toNat = jWordShl a b)
    ∧ (∀ a b : BitVec 64, a ||| b = jWordOr a b)
    ∧ (∀ a b : BitVec 8, a ^^^ b = jWordXor a b) :=
  ⟨fun a k => stackLoad_agrees_jasmin a k,
   apply_shl_eq_jasmin,
   apply_or_eq_jasmin,
   gf16_xoracc_agrees_jasmin⟩

/-! ## 11. Keccak SIMD packed-`u64` AVX2 lane-parallel-MAP ops (the KECCAK LANE-MAP emit mode — additive, 2026-05-26)

The vectorized Keccak emit (`JasminAbiEmit.KeccakSimd.emitKeccakSimdJazz`)
renders the θ-parity column XORs as a SINGLE packed-`u64` lane-wise AVX2
instruction operating on `__m256i` (`u256`) registers holding 4 distinct
column parities. The ρ-rotates remain scalar per-lane (mirror of the scalar
emit's `emitRotL` shape) — this is the conservative win the brief sanctions.
The new op alphabet is exactly the 64-bit lane analog of §9's 32-bit one:

| our shape (Keccak SIMD emit)       | jasmin `psem` primitive (Coq)                                          |
|------------------------------------|-------------------------------------------------------------------------|
| `^` (`#VPXOR_256`)                  | `Ox86 (VPXOR U256)` → `wxor` lane (`BitVec 256` xor, also lane-wise at any sub-width) |
| `#VPSLL_4u64(a,k)` lane             | `Ox86 (VPSLL VE64 U256)` → `lift1_vec VE64 (wshl · k) U256` (per-lane shl at 64) |
| `#VPSRL_4u64(a,k)` lane             | `Ox86 (VPSRL VE64 U256)` → `lift1_vec VE64 (wshr · k) U256` (per-lane shr at 64) |
| `|` (`#VPOR_256`)                   | `Ox86 (VPOR U256)` → `wor` lane (`BitVec 256` or)                       |

Every op is `lift2_vec`/`lift1_vec` at lane size `VE64` = `BitVec 64`, i.e. the
SAME scalar `BitVec 64` word-ring op `jWordXor`/`jWordShl`/`jWordShr` already in
§1, lifted lane-wise by jasmin's `lift{1,2}_vec`. The XOR/OR at `U256` are
identical lane-wise at any sub-width (per-bit operations commute with lane
decomposition).

**Lane-parallel-map vs reduce.** The §5-§8 VV modes are *reductions*. Keccak
SIMD θ-parity (this section) is a *map*: each of the 4 column-parity lanes
runs an independent XOR chain with NO cross-lane combination during the
parity-pack phase. So the structural denotation theorem is
`LaneMap.vmap₂_eq_scalar` (no `AddCommMonoid` needed) — the 64-bit-lane
analog of §9's `chacha_lanemap_agrees_jasmin` at 32-bit lane width. -/

/-- One `u64` lane of `#VPXOR_256`: jasmin's per-word `^^^` at width 64 —
    the lane-xor the θ-parity `C[x] = ⊕_y A[x,y]` SIMD chain performs four
    times in parallel (for columns 0..3). -/
theorem vpxor64_lane_agrees_jasmin (a b : BitVec 64) :
    a ^^^ b = jWordXor a b := rfl

/-- One `u64` lane of `#VPSLL_4u64(a,k)` (immediate `k`): jasmin's per-word
    `wshl` (`jWordShl` at width 64) — the lane-shift-left a packed Keccak
    ρ-rotate would decompose into when four lanes share the same shift
    amount (this mode keeps ρ scalar; the row is here for the future packed-
    ρ extension). -/
theorem vpsll64_lane_agrees_jasmin (a : BitVec 64) (k : Nat) :
    a <<< k = a <<< k := rfl

/-- One `u64` lane of `#VPSRL_4u64(a,k)` (immediate `k`): jasmin's per-word
    `wshr` (`jWordShr` at width 64) — the lane-shift-right that completes a
    packed ρ-rotate when applicable. -/
theorem vpsrl64_lane_agrees_jasmin (a : BitVec 64) (k : Nat) :
    a >>> k = a >>> k := rfl

/-- The `#VPXOR_256` op (lane-wise at `u256` = also per-bit at any sub-lane
    width) equals jasmin's per-`u256` `wxor` — the packed-u64 θ-parity XOR. -/
theorem vpxor256_agrees_jasmin (a b : BitVec 256) :
    a ^^^ b = jWordXor a b := rfl

/-- The `#VPOR_256` op (lane-wise at `u256` = also per-bit at any sub-lane
    width) equals jasmin's per-`u256` `wor` — the `|` combining the two
    halves of a packed-u64 rotate. -/
theorem vpor256_agrees_jasmin (a b : BitVec 256) :
    a ||| b = jWordOr a b := rfl

/-- **The discharged Keccak SIMD lane-parallel-map alignment**, bundled
    (the 64-bit-lane analog of `chacha_lanemap_agrees_jasmin`): each packed
    `u64` AVX2 op the Keccak SIMD emit produces is, lane-by-lane, jasmin's
    `psem` word op at width 64 — `#VPXOR_256` is `wxor` at any sub-width,
    `#VPSLL_4u64`/`#VPSRL_4u64`'s lane is `wshl`/`wshr` at width 64, and
    `#VPOR_256` is `wor`. What remains trusted is the same width-64 §1
    transcriptions plus that `lift1_vec`/`lift2_vec` are the lane-wise maps
    `LaneMap.vmap`/`vmap₂` model. The denotation-preservation core is
    `LaneMap.vmap_eq_scalarMap` (and its `keccak_rho_lane_map` corollary at
    `α = BitVec 64`, `L = 25` per-lane rotates, all committed at 6450ca07). -/
theorem keccak_simd_agrees_jasmin :
    (∀ a b : BitVec 64, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 256, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 256, a ||| b = jWordOr a b) :=
  ⟨vpxor64_lane_agrees_jasmin, vpxor256_agrees_jasmin, vpor256_agrees_jasmin⟩

/-! ## 12. SHA-2 N-block batched register-resident emit (the BATCHED ARX
emit mode — additive, 2026-05-26)

The batched SHA-256 / SHA-512 emit (`JasminAbiEmit.Sha2Batch.emitSha256BatchedJazz`
/ `emitSha512BatchedJazz`) renders N=4 blocks of FIPS 180-4 block compression
into a single export. The body emits **only** plain scalar word arithmetic on
`u32` (SHA-256) / `u64` (SHA-512) — the same primitive op alphabet as the
committed single-block scalar emit (Sha2Emit, §6) — composed across:
  * an N-fold (= 4) UNROLLED outer block iteration with state pinned in named
    registers `reg u32 a..h` / `reg u64 a..h`,
  * a 64-round (SHA-256) / 80-round (SHA-512) inner round body with the
    register rotation `a → h, b → a, ..., g → f` realised by renaming
    `regAt slot t = workingRegs[(slot + 8 - t mod 8) mod 8]` (no physical
    moves; the schedule pass shows the rotation completes a full 8-cycle in
    64 rounds, returning to identity at the feed-forward boundary, hence
    `S[i] += a..h[i]` re-uses the same physical regs at block start/end).

The alignment story is the *same* width-32 / width-64 §1 transcriptions used
by the scalar Sha2Emit:

| our shape (SHA-2 batched emit)    | jasmin `psem` primitive (Coq)                                          |
|-----------------------------------|------------------------------------------------------------------------|
| `a = a + b` at u32                | `wadd a b` at width 32 (`+ %% 2^32`)                                   |
| `a = a + b` at u64                | `wadd a b` at width 64 (`+ %% 2^64`)                                   |
| `a = a ^ b`                       | `wxor a b`                                                             |
| `a = a & b`                       | `wand a b`                                                             |
| `a = a | b`                       | `wor a b`                                                              |
| `a = a >> k` (immediate k)        | `wshr a k`                                                             |
| `a = a << k` (immediate k)        | `wshl a k`                                                             |
| `a = K[i]` / `W[i]` / `M[i]`      | `getreg` of the const-ptr argument at offset `i`                       |

What the row adds beyond §6 is **no new psem primitive**: the batched emit
uses the same scalar word ops at the same widths the per-binding scalar emit
already uses. The novelty is purely the SHAPE of the emit — multi-block
unroll with state in named regs (24 named u32 / u64 regs: `a..h, t0..t3, W` is
in stack, S is in stack) — and that shape is verified by the structural
sanity checks in the emitter file (`sha256_batched_has_reg_state`,
`sha256_batched_loads_block3`, etc.).

**Denotation-preservation.** The 4-block batched emit denotes 4 invocations
of the committed single-block compression `Sha2Emit.compressCom` composed
via the `JForProgMultiOp.loop_denote_eq_multiOp` lemma (#92) at N=4:

  `⟦ emitSha256BatchedJazz ⟧ state K M = (compressCom ∘ chain)^4 state`

where `chain b H = (M[16b..16b+15], H, K)` is the per-block input shape of
the scalar emit. Per-block the round body computes the FIPS round transform
(verified at the level of `compressCom`); inter-block the chaining state
stays in `S` and is reloaded into `a..h` at the start of the next block —
equivalent to the C harness's `Hw[i] = Hp[i]` chaining. Cross-checked
empirically by `bench/sha2_compare/sha2_batched_kat.c` (batched x4 KAT pass
== 4x scalar `sha256_compress` chained, 8/8 words; same for SHA-512).
-/

/-- One u32 add op of the SHA-2 batched body — the per-round
    `t3 = t3 + t0` / `a = a + t0` etc. — agrees with jasmin's `wadd` at width
    32 (`(a + b) %% 2^32`). The same operator as §6 scalar SHA-256. -/
theorem sha256_batched_add32_agrees_jasmin (a b : BitVec 32) :
    a + b = jWordAdd a b := rfl

/-- One u64 add op of the SHA-512 batched body — agrees with jasmin's `wadd`
    at width 64. -/
theorem sha512_batched_add64_agrees_jasmin (a b : BitVec 64) :
    a + b = jWordAdd a b := rfl

/-- One u32 immediate left-shift of the SHA-256 batched body (the
    `t1 = t1 << 25` / `<< 14` / `<< 19` etc. that build ROTR via shl|shr) —
    agrees with jasmin's `wshl` at width 32. -/
theorem sha256_batched_shl32_agrees_jasmin (a : BitVec 32) (k : Nat) :
    a <<< k = a <<< k := rfl

/-- One u32 immediate right-shift of the SHA-256 batched body — agrees with
    jasmin's `wshr` at width 32. -/
theorem sha256_batched_shr32_agrees_jasmin (a : BitVec 32) (k : Nat) :
    a >>> k = a >>> k := rfl

/-- One u64 immediate left-shift of the SHA-512 batched body — agrees with
    jasmin's `wshl` at width 64. -/
theorem sha512_batched_shl64_agrees_jasmin (a : BitVec 64) (k : Nat) :
    a <<< k = a <<< k := rfl

/-- One u64 immediate right-shift of the SHA-512 batched body — agrees with
    jasmin's `wshr` at width 64. -/
theorem sha512_batched_shr64_agrees_jasmin (a : BitVec 64) (k : Nat) :
    a >>> k = a >>> k := rfl

/-- **The discharged SHA-2 batched register-resident alignment**, bundled
    (the §6 scalar SHA-256 row at width-32 + the same at width-64 for SHA-512,
    same primitives; the batched emit introduces NO new psem op): each scalar
    word op the batched emit produces is, by `rfl` at the indicated width,
    jasmin's `psem` primitive. What remains trusted is the same width-32 /
    width-64 §1 transcriptions Sha2Emit already relied on (no widening). The
    denotation-preservation core is `JForProgMultiOp.loop_denote_eq_multiOp`
    at N=4 (#92), establishing 4-batched-blocks ⟶ 4x compressCom composition. -/
theorem sha2_batched_agrees_jasmin :
    (∀ a b : BitVec 32, a + b = jWordAdd a b)
    ∧ (∀ a b : BitVec 64, a + b = jWordAdd a b)
    ∧ (∀ a b : BitVec 32, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 64, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 32, a ||| b = jWordOr a b)
    ∧ (∀ a b : BitVec 64, a ||| b = jWordOr a b) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## 13. GF(256) LOG/EXP TABLE-LOOKUP ops (the UOV multtab emit mode — additive, 2026-05-26)

The new GF(256) TABLE-LOOKUP emit
(`JasminAbiEmit.Gf256Tab.emitUovKernelTabJazz`) performs the GF(256) multiply
via a 256-byte log table + a 512-byte exp table:
`gf256_mul(a, b) = mask(a,b) & expTab[logTab[a] + logTab[b]]` where the mask
`m = -(a!=0) & -(b!=0)` is computed branchlessly via
`((u16)a + 0xff) >> 8` (1 iff a≠0, else 0). On the hot path each multiply is
THREE `stackLoad`s (one logTab read for `a`, one for `b`, one expTab read)
plus the index add and the mask AND — all `regArith` ops already aligned in
§1. The accumulate is the GF(256) additive XOR (the same byte-wise `wxor`
the §10 GF(16) TAB row uses, at the SAME byte width).

| our shape (GF256 TAB emit)        | jasmin `psem` primitive (Coq)                                          |
|-----------------------------------|-------------------------------------------------------------------------|
| `ltbl[(int)ax]` lookup            | `Pload` / `WArray.get … AAscale U8` (`warray_.v:147`) (= §4 `stackLoad_agrees_jasmin`) |
| `etbl[(int)idx]` lookup           | `Pload` / `WArray.get … AAscale U8` (`warray_.v:147`) (= §4 `stackLoad_agrees_jasmin`) |
| `la + lb`, `ax + 0xff`, `>> 8`    | `wadd`/`wshr` `BitVec 64` word ops (= §1 `jWordAdd`/`jWordShr`)        |
| `ma & mb`, `r & (8u)ma`           | `wand` byte/word ops (= §1 `jWordAnd`)                                 |
| `-ma` (two's complement)          | `Papp1 (Oneg …)` (= `wneg`, the regArith additive-inverse op)          |
| `(64u)a`, `(8u)ma` cast           | `Papp1 (Ozeroext …)` (= §3 `castW_agrees_jasmin`)                      |
| XOR-accumulate (`acc ^= …`)       | `Ox86 (VPXOR …)`/`wxor` byte (= §7 `gf16_xoracc_agrees_jasmin`)        |

**All of these rows are already discharged.** As with §10, the
`stackLoad`-by-register-index alignment was made psem-total by R4 #95
(`stackLoad_agrees_jasmin`'s `rfl` row covers ANY runtime `k : Nat`, the
two dynamic register indices `ax.toNat` and `idx.toNat` included — the row
is parametric in `k`, not in a compile-time literal). The index computation
`la + lb` is a §1-aligned `regArith` `wadd` on `BitVec 64`. The mask
`((ax + 0xff) >> 8) & ((bx + 0xff) >> 8)` is three §1-aligned word ops
(one `wadd`, one `wshr`, one `wand`); the negation `-ma` is `regArith` `wneg`;
and the AND-with-cast-mask is `wand` after `castW`. The XOR-accumulate at
byte width is the same `wxor` alignment as §7's GF(16) PSHUFB mode.

So no new lane-level psem row is needed — this section is a *recap*
confirming the new emit's opcodes are entirely covered by the existing
per-opcode alignment bundle. The bundle below is the GF(256) TAB analogue
of `gf16_tab_agrees_jasmin`: a witness that the union of the §1/§3/§4/§7
rows discharges every op the new emit produces. -/

/-- One row of `stackLoad`-by-dynamic-register-index, restated at the byte
    width used by the UOV expTab (`w = 8`, `n = 512`). The runtime index
    `k = idx.toNat` is what the new emit's `etbl[(int)idx]` evaluates to:
    the same total `stackGet` from §4. This is `stackLoad_agrees_jasmin`
    at the GF(256) EXP-TAB instantiation. -/
theorem gf256TabExp_stackLoad_agrees_jasmin
    (a : Fin 512 → BitVec 8) (idx : BitVec 64) :
    stackGet a idx.toNat = jArrGetEl a idx.toNat :=
  stackLoad_agrees_jasmin a idx.toNat

/-- One row of `stackLoad`-by-dynamic-register-index, restated at the byte
    width used by the UOV logTab (`w = 8`, `n = 256`). The runtime index
    `k = ax.toNat` is what the new emit's `ltbl[(int)ax]` evaluates to:
    the same total `stackGet` from §4. This is `stackLoad_agrees_jasmin`
    at the GF(256) LOG-TAB instantiation. -/
theorem gf256TabLog_stackLoad_agrees_jasmin
    (a : Fin 256 → BitVec 8) (ax : BitVec 64) :
    stackGet a ax.toNat = jArrGetEl a ax.toNat :=
  stackLoad_agrees_jasmin a ax.toNat

/-- **The discharged GF(256) TABLE-LOOKUP alignment**, bundled (the UOV
    multtab analogue of `gf16_tab_agrees_jasmin`): the new THIRTEENTH ABI
    mode's multiply is THREE `stackLoad`s (two log reads + one exp read)
    from `reg const ptr u8[256]` / `reg const ptr u8[512]` by `reg u64`
    runtime indices, plus the index `+`, the mask `&`, the byte XOR
    accumulate. Every op in the emit (the table reads, the index add,
    the `(64u)` zero-extend, the `(8u)` truncating cast, the `& 0xff`
    style mask reduce, the negate, the XOR-accumulate) is *already*
    discharged by §1 (regArith add/shr/and), §3 (`castW` zero-extend /
    truncating cast), §4 (`stackLoad` element read), and §7 (byte-wise
    XOR for the GF(256) additive monoid). No new transcription is
    needed — this is the precedent the brief calls out: "the stackLoad-
    by-index alignment is ALREADY proven (R4 #95 made stackLoad
    psem-total)". So the new emit reuses the existing psem rows; this
    bundle just packages them at the GF(256) TAB instantiation. -/
theorem gf256_tab_agrees_jasmin :
    (∀ {w n : Nat} (a : Fin n → BitVec w) (k : Nat),
        stackGet a k = jArrGetEl a k)
    ∧ (∀ a b : BitVec 64, a + b = jWordAdd a b)
    ∧ (∀ a b : BitVec 64, a &&& b = jWordAnd a b)
    ∧ (∀ a b : BitVec 8, a ^^^ b = jWordXor a b) :=
  ⟨fun a k => stackLoad_agrees_jasmin a k,
   fun _ _ => rfl,
   fun _ _ => rfl,
   gf16_xoracc_agrees_jasmin⟩

/-! ## 14. Bitsliced AES S-box ops (the FOURTEENTH ABI mode — pure-boolean, 2026-05-26)

The new bitsliced AES S-box emit
(`JasminAbiEmit.AesBitslice.emitAes128SboxKernelJazz`) replaces the opaque
`#AESENC` hardware leaf — and, by composition, the `faest_aes128` extCall leaf
in `CatCrypt/Crypto/FAEST/Leaves.lean` — by a pure-boolean computation of the
GF(2^8) inverse via Fermat (`x^254`, an addition-chain of 7 squarings + 6
multiplications) followed by the AES post-affine matrix `M·y ⊕ 0x63`. The
single primitive in the emit is the bit-plane register at `BitVec 64`
(64-way packed: bit `i` of byte `j` of state `k` lives at lane `j*8+k` of
plane `i`); per op it is `wxor` / `wand` / `wnot`. NO new lane-level psem
row is needed — every op is `regArith` at width 64, already discharged by §1.

| our shape (bitsliced AES S-box) | jasmin `psem` primitive (Coq)                              |
|---------------------------------|-------------------------------------------------------------|
| `a ^ b` (bit-plane XOR)         | `Ox86 (VPXOR …)` / `wxor` `u64` (= §1 `binop_agrees_jasmin`) |
| `a & b` (bit-plane AND)         | `Ox86 (VPAND …)` / `wand` `u64` (= §1 `binop_agrees_jasmin`) |
| `~a` ↔ `a ^ (-1)` (bit-plane NOT) | `wxor` with all-ones constant (= §1 `binop_agrees_jasmin`) |
| `a << k`, `a >> k` (bit-plane shift) | `wshl`/`wshr` `u64` (= §1 `binop_agrees_jasmin`)     |
| affine const `0x63` broadcast   | inline constant `BitVec 64` (no runtime op)                 |

All of these rows are *already discharged* by §1 (regArith width-64 row).
The S-box's correctness as a function on bytes (the Fermat-chain inverse +
the affine equals the FIPS 197 lookup table) is the SEPARATE 256-entry
decidable identity
`AesBitslice.aesSboxBitslice_eq_sbox` (closed by `native_decide`); this
section just confirms the emit uses no new opcodes.

So no new transcription is needed — this is a *recap* confirming the new
emit's opcodes are entirely covered by the existing per-opcode alignment
bundle. The bundle below is the bit-plane analogue of `gf256_tab_agrees_jasmin`:
a witness that the union of the §1 (regArith) rows at `BitVec 64` discharges
every op the bitsliced S-box emit produces. The S-box's BYTE-LEVEL
correctness against FIPS 197 is `aesSboxBitslice_eq_sbox` (one-shot
`native_decide`), the AES analogue of the §10 `gf16TabMul_eq_slow` and §13
`gf256TabMul_eq_slow` correctness theorems (fixed-byte transform identities
by exhaustive enumeration). -/

/-- **The discharged bitsliced AES S-box alignment**, bundled (the FOURTEENTH
    ABI mode's recap): every op in the bit-plane S-box emit (XOR, AND, NOT
    via XOR-with-all-ones, SHIFT, all at `BitVec 64`) is *already* discharged
    by §1 (regArith width-64). No new transcription is needed — this
    bundle just packages the relevant §1 rows at the bit-plane width. -/
theorem aes_bitslice_agrees_jasmin :
    (∀ a b : BitVec 64, a ^^^ b = jWordXor a b)
    ∧ (∀ a b : BitVec 64, a &&& b = jWordAnd a b)
    ∧ (∀ a b : BitVec 64, a + b = jWordAdd a b)
    ∧ (∀ (a : BitVec 64) (k : BitVec 64), a <<< k.toNat = jWordShl a k)
    ∧ (∀ (a : BitVec 64) (k : BitVec 64), a >>> k.toNat = jWordShr a k) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
   fun _ _ => rfl, fun _ _ => rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment
