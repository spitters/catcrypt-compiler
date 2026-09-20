/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockTie

/-!
# The straight-line multi-op `Com jasminDialect` ↔ `runBlock` tie

`JasminComRunBlockTie` ties a **single** register-arithmetic op's dialect
denotation (`Com jasminDialect`) to the register-machine (`runBlock` of the
lowered `JInstr`). This module **composes that single-op tie over a whole
straight-line block**: a sequence of scalar binder ops threaded through a growing
SSA context lowers to the concatenation of the per-op lowerings, and after
`runBlock` of the whole lowered block, the block's output register holds exactly
the value the multi-op `Com jasminDialect` program denotes.

## Model — a dependently-typed straight-line block (`ArithBlock`)

`ArithBlock Γ` is the covered straight-line sublanguage: a chain of binders, each
binding a fresh `reg 64` slot in the growing De Bruijn context, terminated by
returning one variable. Four binder shapes are covered — a scalar `regArith`
(`.op`), a register copy or an immediate shift (`.un`, over `ArithUn`), and a
compile-time constant (`.cnst`), the dialect images of `regArith bop 64`,
`shlImm 64 k` / `shrImm 64 k` and `regConst 64 n`. Every `ArithBlock` compiles to
a `Com jasminDialect Γ (.reg 64)` (`ArithBlock.toCom`), so the tie below is a
statement about `Com.denote`, with no separate source semantics. This is the
`Com`-valuation analogue (Framing A) of `LowCTToJInstrCT.lowerSeq_denote`, with
the growing dependent context handled by structural induction on `ArithBlock`
(no casing on arbitrary `Expr.op`, so no dependent-op pain).

## What is proved

* `lowerArith2_get_dst` / `lowerArith2_get_other` — the per-op building blocks
  over **explicit** registers (decoupled from the fixed `Γ2`/`jasminSingleOp`):
  the lowered `mov dst ra; op dst rb` writes `bop.apply (s.get ra) (s.get rb)`
  to `dst` and leaves every other register untouched.
* `lowerUn_get_dst` / `lowerUn_get_other` and `lowerConst_get_dst` /
  `lowerConst_get_other` — the same value-and-frame pair for the one-input and
  constant lowerings. The shift value lemmas hold for an immediate below the word
  width, which is the range on which the machine shift's `mod 64` count mask is
  the identity (`shiftCount_imm`); `IsScalarUn` carries that side condition.
* `FreshFor` — the register-allocation freshness invariant: the fresh-name
  stream is injective and disjoint from the live register map's range. Preserved
  as the context grows (`FreshFor_extend`).
* `lowerBlock_tie` — the block tie: for every straight-line `ArithBlock`,
  under a `JStateInterpG` state correspondence and a `FreshFor` allocation,
  `(runBlock s (lowerBlock block ρ g)).get (outReg block ρ g)
     = block.toCom.denote V`. The left side is a machine register read after
  `runBlock` of the whole lowered block, the right side the `Com jasminDialect`
  denotation folding `bop.apply` over the valuation.

## Register reuse

`lowerBlock_tie` uses a **fresh** (injective, range-disjoint) allocation.
Register *reuse* (dead-slot reallocation) is proved separately by
`Optimizer.RandomizedRegAlloc.regalloc_runBlock_sound` (cited in
`JasminComRunBlockTie.regalloc_composition_note`); it composes on top of this
block tie to add reuse. This file does not re-prove allocation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. `runBlock` over a concatenation (local structural helper) -/

/-- `runBlock` over a concatenation: run the first block, then the second from
    the resulting state. (Local copy; the same lemma lives elsewhere in the
    backend, not imported here.) -/
theorem runBlock_append {w : Nat} (s : JState w) (l₁ l₂ : List (JInstr w)) :
    runBlock s (l₁ ++ l₂) = runBlock (runBlock s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons, ih]

/-! ## 2. The per-op lowering over explicit registers

Decoupled from the fixed `Γ2`/`jasminSingleOp` of `JasminComRunBlockTie`: the
same `mov dst ra; op dst rb` shape, but with the operand/destination registers
given explicitly, so it can be threaded through a growing context. -/

/-- The per-op machine block `mov dst ra; op dst rb`, with explicit operand
    registers. Equal in shape to `JasminComRunBlockTie.lowerJasminArith`, but the
    two source registers and destination are supplied directly. -/
def lowerArith2 (bop : JasminBinOp) (ra rb dst : String) : List (JInstr 64) :=
  [ .mov dst (.reg ra)
  , bopToJInstr bop dst (.reg rb) ]

/-- **Per-op value agreement (explicit registers).** Running the lowered per-op
    block and reading `dst` yields `bop.apply (s.get ra) (s.get rb)` — the same
    `BitVec 64` op the dialect's `regArith bop` denotes. Needs `dst ≠ rb` so the
    priming `mov dst ra` does not clobber the `b` read. -/
theorem lowerArith2_get_dst (bop : JasminBinOp) (hbop : IsScalarBop bop)
    (ra rb dst : String) (hne : dst ≠ rb) (s : JState 64) :
    (runBlock s (lowerArith2 bop ra rb dst)).get dst
      = bop.apply (s.get ra) (s.get rb) := by
  simp only [lowerArith2, runBlock_cons, runBlock_nil]
  rw [jasminBop_eq_machine bop hbop]
  have hmov_dst : (evalInstr s (.mov dst (.reg ra))).get dst = s.get ra := by
    simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.get]
  have hmov_rb : (evalInstr s (.mov dst (.reg ra))).get rb = s.get rb := by
    have hrb : rb ≠ dst := fun h => hne h.symm
    simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.get, hrb]
  rw [hmov_dst, hmov_rb]

/-- **Per-op frame (explicit registers).** The lowered per-op block writes only
    `dst`; reading any other register `r ≠ dst` falls through unchanged. -/
theorem lowerArith2_get_other (bop : JasminBinOp) (hbop : IsScalarBop bop)
    (ra rb dst r : String) (hr : r ≠ dst) (s : JState 64) :
    (runBlock s (lowerArith2 bop ra rb dst)).get r = s.get r := by
  simp only [lowerArith2, runBlock_cons, runBlock_nil]
  rw [bopToJInstr_get_other bop hbop dst rb r _ hr]
  simp [evalInstr, x86_MOV, JOperand.eval, JState.setReg, JState.get, hr]

/-! ## 2b. The one-input operations and the constant

`shlImm 64 k`, `shrImm 64 k` and `regConst 64 n` are the three single-binder
dialect ops the block language covers beside `regArith`. The first two share the
one-input shape and are collected in `ArithUn`; the constant has no operand and
gets its own lowering. -/

/-- **The one-input register operations of the block language.** A register copy
    and the two logical shifts by a compile-time immediate. -/
inductive ArithUn where
  /-- Copy the operand register. -/
  | copy
  /-- Logical left shift by the immediate `k`. -/
  | shl (k : Nat)
  /-- Logical right shift by the immediate `k`. -/
  | shr (k : Nat)
  deriving DecidableEq, Repr

/-- The `BitVec 64` value a one-input operation computes, matching the dialect
    denotation of `shlImm 64` / `shrImm 64`. -/
def ArithUn.apply : ArithUn → BitVec 64 → BitVec 64
  | .copy, a => a
  | .shl k, a => a <<< k
  | .shr k, a => a >>> k

/-- **The covered one-input operations.** A copy is always covered; a shift is
    covered when the immediate is below the word width, which is where the
    machine shift's `mod 64` count mask is the identity. -/
def IsScalarUn : ArithUn → Prop
  | .copy => True
  | .shl k => k < 64
  | .shr k => k < 64

/-- The decidable form of `IsScalarUn`. -/
def isScalarUnB : ArithUn → Bool
  | .copy => true
  | .shl k => decide (k < 64)
  | .shr k => decide (k < 64)

/-- `isScalarUnB` implies the `Prop`-valued `IsScalarUn` that `ArithBlock.un`
    carries. -/
theorem IsScalarUn_of_isScalarUnB {uop : ArithUn} (h : isScalarUnB uop = true) :
    IsScalarUn uop := by
  cases uop <;> simp_all [isScalarUnB, IsScalarUn]

/-- **The machine instructions of a one-input operation.** A copy is the register
    `mov`; a shift is the register `mov` followed by the two-address shift with an
    immediate count. -/
def ArithUn.toJInstr : ArithUn → String → String → List (JInstr 64)
  | .copy, dst, a => [ .mov dst (.reg a) ]
  | .shl k, dst, a => [ .mov dst (.reg a), .shl dst (.imm k) ]
  | .shr k, dst, a => [ .mov dst (.reg a), .shr dst (.imm k) ]

/-- The machine instructions of a constant: the immediate `mov`. -/
def lowerConst (n : Nat) (dst : String) : List (JInstr 64) :=
  [ .mov dst (.imm n) ]

/-- The machine shift count of an immediate below the word width is the immediate
    itself: the `mod 64` mask of `shiftCount` is the identity there. -/
theorem shiftCount_imm {k : Nat} (hk : k < 64) :
    shiftCount (BitVec.ofNat 64 k) = k := by
  have hlt : k < 2 ^ 64 := Nat.lt_of_lt_of_le hk (by decide)
  simp [shiftCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hk]

/-- The word the machine left shift writes for an immediate count below the word
    width is `v <<< k` — the value the dialect's `shlImm 64 k` denotes. -/
theorem x86_SHL_imm_word {k : Nat} (hk : k < 64) (v : BitVec 64) :
    (x86_SHL v (BitVec.ofNat 64 k)).word = v <<< k := by
  rw [x86_SHL]
  simp only [shiftCount_imm hk]
  split
  · rename_i h0
    simp [rflags_None, h0]
  · simp [rflags_OF, wshl, Nat.min_eq_right (Nat.le_of_lt hk)]

/-- The word the machine logical right shift writes for an immediate count below
    the word width is `v >>> k` — the value the dialect's `shrImm 64 k`
    denotes. -/
theorem x86_SHR_imm_word {k : Nat} (hk : k < 64) (v : BitVec 64) :
    (x86_SHR v (BitVec.ofNat 64 k)).word = v >>> k := by
  rw [x86_SHR]
  simp only [shiftCount_imm hk]
  split
  · rename_i h0
    simp [rflags_None, h0]
  · simp [rflags_OF, wshr, Nat.min_eq_right (Nat.le_of_lt hk)]

/-- **Per-operation value agreement (one input).** Running the lowered one-input
    block and reading `dst` yields `uop.apply (s.get a)` — the same `BitVec 64`
    value the dialect's `shlImm`/`shrImm` denotes. -/
theorem lowerUn_get_dst (uop : ArithUn) (huop : IsScalarUn uop) (ra dst : String)
    (s : JState 64) :
    (runBlock s (uop.toJInstr dst ra)).get dst = uop.apply (s.get ra) := by
  cases uop with
  | copy =>
      simp [ArithUn.toJInstr, ArithUn.apply, runBlock_cons, runBlock_nil, evalInstr,
        x86_MOV, JOperand.eval, JState.setReg, JState.get]
  | shl k =>
      have hk : k < 64 := huop
      simp [ArithUn.toJInstr, ArithUn.apply, runBlock_cons, runBlock_nil, evalInstr,
        x86_MOV, JOperand.eval, JState.setReg, JState.writeB5W, JState.get,
        x86_SHL_imm_word hk]
  | shr k =>
      have hk : k < 64 := huop
      simp [ArithUn.toJInstr, ArithUn.apply, runBlock_cons, runBlock_nil, evalInstr,
        x86_MOV, JOperand.eval, JState.setReg, JState.writeB5W, JState.get,
        x86_SHR_imm_word hk]

/-- **Per-operation frame (one input).** The lowered one-input block writes only
    `dst`; reading any other register `r ≠ dst` falls through unchanged. -/
theorem lowerUn_get_other (uop : ArithUn) (ra dst r : String) (hr : r ≠ dst)
    (s : JState 64) :
    (runBlock s (uop.toJInstr dst ra)).get r = s.get r := by
  cases uop <;>
    simp [ArithUn.toJInstr, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
      JOperand.eval, JState.setReg, JState.writeB5W, JState.get, hr]

/-- **Constant value agreement.** Running the lowered constant and reading `dst`
    yields `BitVec.ofNat 64 n` — the value the dialect's `regConst 64 n`
    denotes. -/
theorem lowerConst_get_dst (n : Nat) (dst : String) (s : JState 64) :
    (runBlock s (lowerConst n dst)).get dst = BitVec.ofNat 64 n := by
  simp [lowerConst, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval,
    JState.setReg, JState.get]

/-- **Constant frame.** The lowered constant writes only `dst`. -/
theorem lowerConst_get_other (n : Nat) (dst r : String) (hr : r ≠ dst)
    (s : JState 64) :
    (runBlock s (lowerConst n dst)).get r = s.get r := by
  simp [lowerConst, runBlock_cons, runBlock_nil, evalInstr, x86_MOV, JOperand.eval,
    JState.setReg, JState.get, hr]

/-! ## 3. The straight-line block model `ArithBlock` -/

/-- **The covered straight-line arithmetic sublanguage.** A chain of scalar
    `regArith` ops, each binding a fresh `reg 64` slot in the growing De Bruijn
    context `Γ`, terminated by returning a single variable. Every op carries its
    `IsScalarBop` proof (the arms whose machine ALU step matches `apply`). -/
inductive ArithBlock : Ctxt jasminDialect → Type where
  /-- Return one `reg 64` variable — the block's output. -/
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 64)) : ArithBlock Γ
  /-- One scalar op `d := a ⟨bop⟩ b`, binding a fresh slot, then continue. -/
  | op {Γ : Ctxt jasminDialect} (bop : JasminBinOp) (hbop : IsScalarBop bop)
      (a b : Ctxt.Var Γ (.reg 64)) (rest : ArithBlock (.reg 64 :: Γ)) :
      ArithBlock Γ
  /-- One one-input op `d := ⟨uop⟩ a`, binding a fresh slot, then continue. -/
  | un {Γ : Ctxt jasminDialect} (uop : ArithUn) (huop : IsScalarUn uop)
      (a : Ctxt.Var Γ (.reg 64)) (rest : ArithBlock (.reg 64 :: Γ)) :
      ArithBlock Γ
  /-- One constant `d := n`, binding a fresh slot, then continue. -/
  | cnst {Γ : Ctxt jasminDialect} (n : Nat) (rest : ArithBlock (.reg 64 :: Γ)) :
      ArithBlock Γ

/-- The `regArith bop` expression on two `reg 64` variables, at width 64. Built
    exactly like `jasminSingleOp`'s op. -/
def arithExpr {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.reg 64) :=
  .mk (.regArith bop 64) rfl (.cons a (.cons b .nil))

/-- The `regArith` expression denotes to `bop.apply (a.lookup V) (b.lookup V)`,
    a two-operand value read from the valuation. -/
theorem arithExpr_denote {Γ : Ctxt jasminDialect} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg 64)) (V : Ctxt.Valuation Γ) :
    (arithExpr bop a b).denote V = bop.apply (a.lookup V) (b.lookup V) := rfl

/-- The dialect expression of a one-input operation on one `reg 64` variable, at
    width 64: `shlImm` for a copy or a left shift, `shrImm` for a right shift. -/
def unExpr {Γ : Ctxt jasminDialect} : ArithUn → Ctxt.Var Γ (.reg 64) →
    Expr jasminDialect Γ (.reg 64)
  | .copy, a => .mk (.shlImm 64 0) rfl (.cons a .nil)
  | .shl k, a => .mk (.shlImm 64 k) rfl (.cons a .nil)
  | .shr k, a => .mk (.shrImm 64 k) rfl (.cons a .nil)

/-- The one-input expression denotes to `uop.apply (a.lookup V)`, a value read
    from the valuation. -/
theorem unExpr_denote {Γ : Ctxt jasminDialect} (uop : ArithUn)
    (a : Ctxt.Var Γ (.reg 64)) (V : Ctxt.Valuation Γ) :
    (unExpr uop a).denote V = uop.apply (a.lookup V) := by
  cases uop with
  | copy => exact BitVec.shiftLeft_zero (a.lookup V)
  | shl k => rfl
  | shr k => rfl

/-- The `regConst n` expression at width 64, taking no operands. -/
def constExpr {Γ : Ctxt jasminDialect} (n : Nat) : Expr jasminDialect Γ (.reg 64) :=
  .mk (.regConst 64 n) rfl .nil

/-- The constant expression denotes to `BitVec.ofNat 64 n`. -/
theorem constExpr_denote {Γ : Ctxt jasminDialect} (n : Nat) (V : Ctxt.Valuation Γ) :
    (constExpr (Γ := Γ) n).denote V = BitVec.ofNat 64 n := rfl

/-- The one-input operation a `shlImm 64 k` binder carries: a copy at count zero,
    the left shift otherwise. -/
def unOfShl : Nat → ArithUn
  | 0 => .copy
  | k + 1 => .shl (k + 1)

/-- The operation of a `shlImm 64 k` binder computes `a <<< k`. -/
theorem unOfShl_apply (k : Nat) (a : BitVec 64) : (unOfShl k).apply a = a <<< k := by
  cases k with
  | zero => simp [unOfShl, ArithUn.apply]
  | succ k => rfl

/-- The operation of a `shlImm 64 k` binder is covered when `k` is below the word
    width. -/
theorem IsScalarUn_unOfShl {k : Nat} (hk : k < 64) : IsScalarUn (unOfShl k) := by
  cases k with
  | zero => exact trivial
  | succ k => exact hk

/-- The expression of a `shlImm 64 k` binder's operation is that binder's own
    expression. -/
theorem unExpr_unOfShl {Γ : Ctxt jasminDialect} (k : Nat) (a : Ctxt.Var Γ (.reg 64)) :
    unExpr (unOfShl k) a = .mk (.shlImm 64 k) rfl (.cons a .nil) := by
  cases k <;> rfl

/-- **Compile an `ArithBlock` to a `Com jasminDialect`.** The `.ret`
    becomes `Com.ret`; each `.op` becomes a `Com.var` binding `arithExpr`. The
    tie below is stated over this program's `Com.denote`. -/
def ArithBlock.toCom : {Γ : Ctxt jasminDialect} → ArithBlock Γ →
    Com jasminDialect Γ (.reg 64)
  | _, .ret v => .ret v
  | _, .op bop _ a b rest => .var (arithExpr bop a b) rest.toCom
  | _, .un uop _ a rest => .var (unExpr uop a) rest.toCom
  | _, .cnst n rest => .var (constExpr n) rest.toCom

/-! ## 4. The register map and its extension -/

/-- The per-context register map: each live `reg 64` SSA variable to a machine
    register name. -/
abbrev RegMapG (Γ : Ctxt jasminDialect) := Ctxt.Var Γ (.reg 64) → String

/-- Extend a register map with a fresh binding `d` for the new slot `.here`;
    old variables `.there w` keep their register `ρ w`. Mirrors
    `Ctxt.Valuation.extend` on the register side. -/
def RegMapG.extend {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ) (d : String) :
    RegMapG (.reg 64 :: Γ) :=
  fun w =>
    match w with
    | .here => d
    | .there w0 => ρ w0

/-! ## 5. The state correspondence and fresh-allocation invariant -/

/-- **The state correspondence for a general context `Γ`.** The machine register
    `ρ v` holds the SSA valuation's value `v.lookup V`, for every `reg 64`
    variable `v`. The `Γ`-general analogue of
    `JasminComRunBlockTie.JStateInterp`. -/
def JStateInterpG {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ)
    (V : Ctxt.Valuation Γ) (s : JState 64) : Prop :=
  ∀ v : Ctxt.Var Γ (.reg 64), s.get (ρ v) = v.lookup V

/-- **The fresh-allocation invariant.** The fresh-name stream `g` is injective
    and disjoint from the live register map `ρ`'s range: every op's freshly
    allocated destination is a physical register not yet in use. This is the
    fresh-allocation leg (register *reuse* is added by `regalloc_runBlock_sound`,
    see the module docstring). -/
def FreshFor {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ) (g : Nat → String) : Prop :=
  (∀ i j, i ≠ j → g i ≠ g j) ∧ (∀ i (v : Ctxt.Var Γ (.reg 64)), g i ≠ ρ v)

/-- The fresh invariant is preserved as the context grows: after allocating the
    head `g 0` to the new slot and shifting the stream, the shifted stream stays
    injective and disjoint from the extended register map's range. -/
theorem FreshFor_extend {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ) (g : Nat → String)
    (hfresh : FreshFor ρ g) :
    FreshFor (ρ.extend (g 0)) (fun k => g (k + 1)) := by
  obtain ⟨hinj, hdisj⟩ := hfresh
  refine ⟨fun i j hij => hinj (i + 1) (j + 1) (by omega), ?_⟩
  intro i v
  match v with
  | .here => exact hinj (i + 1) 0 (by omega)
  | .there w0 => exact hdisj (i + 1) w0

/-! ## 6. The lowering of a whole block and its output register -/

/-- **The whole-block lowering.** A straight-line `ArithBlock` lowers to the
    concatenation of the per-op lowerings, each op's destination taken from the
    fresh stream (`g 0`), then recurse with the extended register map and the
    shifted stream. The `.ret` emits nothing — the output already sits in its
    register. -/
def lowerBlock : {Γ : Ctxt jasminDialect} → ArithBlock Γ → RegMapG Γ →
    (Nat → String) → List (JInstr 64)
  | _, .ret _, _, _ => []
  | _, .op bop _ a b rest, ρ, g =>
      lowerArith2 bop (ρ a) (ρ b) (g 0)
        ++ lowerBlock rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .un uop _ a rest, ρ, g =>
      uop.toJInstr (g 0) (ρ a)
        ++ lowerBlock rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .cnst n rest, ρ, g =>
      lowerConst n (g 0)
        ++ lowerBlock rest (ρ.extend (g 0)) (fun k => g (k + 1))

/-- **The block's output register.** The machine register holding the block's
    result after `runBlock` — the register of the finally-returned variable
    under the accumulated register map. -/
def outReg : {Γ : Ctxt jasminDialect} → ArithBlock Γ → RegMapG Γ →
    (Nat → String) → String
  | _, .ret v, ρ, _ => ρ v
  | _, .op _ _ _ _ rest, ρ, g =>
      outReg rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .un _ _ _ rest, ρ, g =>
      outReg rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .cnst _ rest, ρ, g =>
      outReg rest (ρ.extend (g 0)) (fun k => g (k + 1))

/-! ## 7. The block tie: the single-op tie composes over the block -/

/-- **The straight-line multi-op `.denote ↔ runBlock` tie.**
    For every straight-line `ArithBlock`, under the state correspondence
    `JStateInterpG ρ V s` and a fresh (injective, range-disjoint) allocation
    `FreshFor ρ g`, reading the block's output register after `runBlock` of the
    whole lowered block equals the multi-op `Com jasminDialect` program's
    denotation on `V`.

    Proven by structural induction on `ArithBlock`, composing the single-op tie
    (`lowerArith2_get_dst`) with its frame (`lowerArith2_get_other`): each op
    extends `JStateInterpG` to the grown context (new slot holds the op's value,
    every old register survives by the frame + freshness), and `FreshFor` is
    preserved by `FreshFor_extend`. The left side is a `runBlock` register read,
    the right side a `Com.denote` fold of `bop.apply`. -/
theorem lowerBlock_tie : {Γ : Ctxt jasminDialect} → (block : ArithBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    (V : Ctxt.Valuation Γ) → JStateInterpG ρ V s → FreshFor ρ g →
    (runBlock s (lowerBlock block ρ g)).get (outReg block ρ g)
      = block.toCom.denote V
  | _, .ret v, ρ, g, s, V, hinterp, _ => by
      simp only [lowerBlock, outReg, runBlock_nil, ArithBlock.toCom, Com.denote]
      exact hinterp v
  | _, .op bop hbop a b rest, ρ, g, s, V, hinterp, hfresh => by
      -- The op's freshly allocated destination `g 0` differs from every old register.
      have hdisj := hfresh.2 0
      -- `JStateInterpG` extends to the grown context on the post-op state.
      have hinterp' : JStateInterpG (ρ.extend (g 0))
          (V.extend ((arithExpr bop a b).denote V))
          (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))) := by
        intro w
        match w with
        | .here =>
            -- new slot: post-op `g 0` holds `bop.apply (V a) (V b)` = the op's denotation
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (g 0)
                = bop.apply (a.lookup V) (b.lookup V)
            rw [lowerArith2_get_dst bop hbop (ρ a) (ρ b) (g 0) (hdisj b) s,
              hinterp a, hinterp b]
        | .there w0 =>
            -- old slot survives: frame (op writes only `g 0`) + freshness `g 0 ≠ ρ w0`
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (ρ w0)
                = w0.lookup V
            rw [lowerArith2_get_other bop hbop (ρ a) (ρ b) (g 0) (ρ w0)
              (fun h => (hdisj w0) h.symm) s]
            exact hinterp w0
      -- `FreshFor` is preserved for the recursion.
      have hfresh' : FreshFor (ρ.extend (g 0)) (fun k => g (k + 1)) :=
        FreshFor_extend ρ g hfresh
      -- Recurse on `rest` from the post-op state, then match the split run.
      have key := lowerBlock_tie rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0)))
        (V.extend ((arithExpr bop a b).denote V)) hinterp' hfresh'
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .un uop huop a rest, ρ, g, s, V, hinterp, hfresh => by
      have hdisj := hfresh.2 0
      have hinterp' : JStateInterpG (ρ.extend (g 0))
          (V.extend ((unExpr uop a).denote V))
          (runBlock s (uop.toJInstr (g 0) (ρ a))) := by
        intro w
        match w with
        | .here =>
            show (runBlock s (uop.toJInstr (g 0) (ρ a))).get (g 0)
                = (unExpr uop a).denote V
            rw [lowerUn_get_dst uop huop (ρ a) (g 0) s, hinterp a, unExpr_denote]
        | .there w0 =>
            show (runBlock s (uop.toJInstr (g 0) (ρ a))).get (ρ w0) = w0.lookup V
            rw [lowerUn_get_other uop (ρ a) (g 0) (ρ w0)
              (fun h => (hdisj w0) h.symm) s]
            exact hinterp w0
      have hfresh' : FreshFor (ρ.extend (g 0)) (fun k => g (k + 1)) :=
        FreshFor_extend ρ g hfresh
      have key := lowerBlock_tie rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (uop.toJInstr (g 0) (ρ a)))
        (V.extend ((unExpr uop a).denote V)) hinterp' hfresh'
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .cnst n rest, ρ, g, s, V, hinterp, hfresh => by
      have hdisj := hfresh.2 0
      have hinterp' : JStateInterpG (ρ.extend (g 0))
          (V.extend ((constExpr n).denote V))
          (runBlock s (lowerConst n (g 0))) := by
        intro w
        match w with
        | .here =>
            show (runBlock s (lowerConst n (g 0))).get (g 0) = (constExpr n).denote V
            rw [lowerConst_get_dst n (g 0) s, constExpr_denote]
        | .there w0 =>
            show (runBlock s (lowerConst n (g 0))).get (ρ w0) = w0.lookup V
            rw [lowerConst_get_other n (g 0) (ρ w0) (fun h => (hdisj w0) h.symm) s]
            exact hinterp w0
      have hfresh' : FreshFor (ρ.extend (g 0)) (fun k => g (k + 1)) :=
        FreshFor_extend ρ g hfresh
      have key := lowerBlock_tie rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerConst n (g 0)))
        (V.extend ((constExpr n).denote V)) hinterp' hfresh'
      simpa only [lowerBlock, outReg, ArithBlock.toCom, Com.denote, runBlock_append]
        using key

/-! ## 8. Non-vacuity — a symbolic 2-op block

A concrete two-op straight-line block over inputs `⟨a, b⟩` computing
`(a + b) * a`. The dialect side folds two `bop.apply` calls over a symbolic
valuation (by `rfl`), and the tie follows from `lowerBlock_tie`. -/

/-- The two-input context `[reg 64, reg 64]`. -/
abbrev Δ2 : Ctxt jasminDialect := [.reg 64, .reg 64]

/-- Input `a` (de Bruijn 0) in `Δ2`. -/
abbrev dA : Ctxt.Var Δ2 (.reg 64) := .here

/-- Input `b` (de Bruijn 1) in `Δ2`. -/
abbrev dB : Ctxt.Var Δ2 (.reg 64) := .there .here

/-- **A 2-op block**: `s1 := a + b ; s2 := s1 * a ; ret s2`.
    After op 1 the context is `reg 64 :: Δ2`; `s1 = .here`, `a` shifts to
    `.there .here`. After op 2, `s2 = .here`. -/
def block2 : ArithBlock Δ2 :=
  .op .add trivial dA dB
    (.op .mul trivial (.here) (.there .here)
      (.ret .here))

/-- **The 2-op denotation is a two-`bop` fold** over a symbolic valuation:
    `block2` denotes to `mul (add a b) a`, a nested composition of
    `JasminBinOp.apply`. -/
theorem block2_denote (V : Ctxt.Valuation Δ2) :
    block2.toCom.denote V
      = JasminBinOp.mul.apply
          (JasminBinOp.add.apply (dA.lookup V) (dB.lookup V)) (dA.lookup V) := by
  rfl

/-- **The block tie instantiated on the 2-op block.** Under any state
    correspondence and fresh allocation, the machine `runBlock` of the whole
    lowered 2-op block reads exactly `(a + b) * a`, the composed dialect
    denotation of `block2_denote`. -/
theorem block2_tie (ρ : RegMapG Δ2) (g : Nat → String) (s : JState 64)
    (V : Ctxt.Valuation Δ2) (hinterp : JStateInterpG ρ V s) (hfresh : FreshFor ρ g) :
    (runBlock s (lowerBlock block2 ρ g)).get (outReg block2 ρ g)
      = JasminBinOp.mul.apply
          (JasminBinOp.add.apply (dA.lookup V) (dB.lookup V)) (dA.lookup V) := by
  rw [lowerBlock_tie block2 ρ g s V hinterp hfresh, block2_denote]

/-! ## 9. Non-vacuity — a block mixing a constant, a copy, shifts and an op

A five-binder block over the same two inputs, led by a constant:
`c := 5 ; t1 := a ; t2 := t1 <<< 3 ; t3 := b >>> 2 ; t4 := t2 ^^^ t3 ; ret t4`.
All four block arms occur. -/

/-- **A 5-binder mixed block**: a constant, a copy, a left shift, a right shift
    and a binary op. -/
def block3 : ArithBlock Δ2 :=
  .cnst 5
    (.un .copy trivial (.there .here)
      (.un (.shl 3) (show (3 : Nat) < 64 by omega) .here
        (.un (.shr 2) (show (2 : Nat) < 64 by omega)
            (.there (.there (.there (.there .here))))
          (.op .xor trivial (.there .here) .here (.ret .here)))))

/-- The mixed block denotes to `(a <<< 3) ^^^ (b >>> 2)` over a symbolic
    valuation: the constant and the copy carry through the fold. -/
theorem block3_denote (V : Ctxt.Valuation Δ2) :
    block3.toCom.denote V
      = JasminBinOp.xor.apply ((ArithUn.shl 3).apply (dA.lookup V))
          ((ArithUn.shr 2).apply (dB.lookup V)) := by
  have hz : ∀ x : BitVec 64, (ArithUn.shl 0).apply x = x :=
    fun x => BitVec.shiftLeft_zero x
  show JasminBinOp.xor.apply
      ((ArithUn.shl 3).apply ((ArithUn.shl 0).apply (dA.lookup V)))
      ((ArithUn.shr 2).apply (dB.lookup V)) = _
  rw [hz]

/-- **The block tie instantiated on the mixed block.** Under any state
    correspondence and fresh allocation, the machine `runBlock` of the whole
    lowered mixed block reads `(a <<< 3) ^^^ (b >>> 2)`. -/
theorem block3_tie (ρ : RegMapG Δ2) (g : Nat → String) (s : JState 64)
    (V : Ctxt.Valuation Δ2) (hinterp : JStateInterpG ρ V s) (hfresh : FreshFor ρ g) :
    (runBlock s (lowerBlock block3 ρ g)).get (outReg block3 ρ g)
      = JasminBinOp.xor.apply ((ArithUn.shl 3).apply (dA.lookup V))
          ((ArithUn.shr 2).apply (dB.lookup V)) := by
  rw [lowerBlock_tie block3 ρ g s V hinterp hfresh, block3_denote]

end CatCrypt.Crypto.SecureCompilation.Ascent
