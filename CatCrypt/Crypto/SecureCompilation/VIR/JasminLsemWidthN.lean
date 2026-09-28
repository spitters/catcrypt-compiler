/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

/-!
# A non-uniform-width linear machine and the widened `correct ∧ robust`
# simulation — increment 5 of porting jasmin's `lsem`

Increments 1–4 (`JasminLsem`/`JasminLsemSimulation`/`JasminLsemRobust`/
`JasminLsemScalar`) built the straight-line linear machine **at a single uniform
word width** (`Lstate w`, `lvm : String → BitVec w`) and proved, unconditionally,
a functional ∧ constant-time simulation for the uniform-width scalar fragment
(`owned_lsem_correct_and_robust_scalar`, over `regArith ∪ regConst`). The single
remaining coverage axis the uniform machine *cannot* express is **width
mixing**: a binding whose operands or result live at different widths. Increment
4's deferral list names exactly these — `select` (cond `.reg 1`, data `.reg w`),
the stack array ops, `castW`, the carry/widening trio — and notes that they
"break the single-width store, so they need the *next* (multi-width) increment".

This module is **increment 5**: a **non-uniform-width** linear state `LstateN`
(a width-tagged store, `lvm : String → Σ w, BitVec w`), a faithful step
`lsemStepN` over it, and the widened functional ∧ CT simulation + unconditional
capstone over a width-mixed source fragment that includes the first
width-mixing op, `select`. Increments 1–4 are left intact (additive: new file,
new names).

## What is in scope (and why), at non-uniform width

`LstateN` tags each register with the width of the value it holds (`Σ w, BitVec
w`), so a `BitVec 1` condition and a `BitVec w` datum can coexist in the same
store. The widened source fragment `ScalarArithN` covers, over a (per-register,
possibly non-uniform) context:

* **`regArith bop w`** — `[reg w, reg w] → reg w`. As in increments 2–4, but now
  the two source registers are read out of the width-tagged store *at their
  stored width* (which the agreement invariant pins to `w`). The result width
  `w` is recovered from the data source's store tag (not from a wire-format
  annotation), so the same arm serves every `w` in a width-mixed program.
* **`select w`** — `[reg 1, reg w, reg w] → reg w`, **the first width-mixing
  op**. Its condition operand is a 1-bit register, its two data operands and its
  result are width `w`. `opToLinstrR` lowers it to
  `Lopn [.reg dst] (CMOV-tagged) [cond, a, b]` with three `.reg` sources.
  `lsemStepN` reads `cond` at width 1 and `a`, `b` at width `w` out of the
  width-tagged store and writes `selectW cond a b = (select w).denote …`.
  Constant-time: `linstrLeak` leaks the cond register **name** (`regShape`),
  never its 1-bit value — exactly the CT story the task wants for a branch-free
  cmov.

This is a *width-mixing* widening of the unconditional simulation: the
first op whose operands do not all share one width brought into the functional ∧
constant-time `lsem` simulation, with no new hypothesis and no `jasminc`/IR→x86
edge. The uniform-width `regArith` fragment of increments 2–4 is recovered as a
special case of the non-uniform `regArith` arm (the uniform context is a
non-uniform context all of whose registers happen to share `w`).

## Deferred ops, with the technical reason for each

The remaining width-mixed `JasminOp`s are **not faked**; each is deferred with
the concrete obstruction it hits against `LstateN` *given the frozen
`opToLinstrR` wire format* (the task forbids changing it, as it ripples into the
byte-KATs):

* **`regConst w n`** — lowers to `Lopn [.reg dst] (withWidthTag w "MOV")
  [.imm n]`. Its only source is the public `.imm n` (no register to read), so —
  unlike `regArith`/`select` — `lsemStepN` has no store tag to recover the result
  width `w` from. The bare mnemonic carries `w` only as the `:64` tag
  (`withWidthTag` appends `:64` *only* when `w = 64`), so for `w ≠ 64` the result
  width is **not** recoverable from the wire. In increment 4 this was fine
  because the store was uniform width `w` (a typeclass parameter pinned `w`); in
  the width-tagged store there is no such global `w`. Recovering it needs a
  width-carrying constant mnemonic — a wire-format change — so `regConst` is
  deferred here by the same frozen-wire constraint as `castW`, *not* by a missing
  proof. (The increment-4 uniform-width capstone still covers `regConst` at any
  fixed `w`; this increment covers the orthogonal width-mixing axis.)
* **`castW w w'` (`w ≠ w'`)** — lowers to `Lopn [.reg dst] ("ZEROEXT"/"TRUNC")
  [src]`. The **output width `w'` is not recoverable** from the emitted
  `LinstrR`: the mnemonic carries no width tag (`opToLinstrR` does *not* apply
  `withWidthTag` to the cast), and the store only tells the step the *input*
  width `w` (from `src`'s stored tag), never the target `w'`. A faithful
  `lsemStepN` operating on the wire format therefore cannot decide whether to
  zero-extend or truncate, nor to what width. (Contrast `select`, whose output
  width *equals* its data-operand width, which the store provides.) Closing this
  needs a width-carrying cast mnemonic — i.e. a wire-format change — so it is
  out of scope here by the frozen-wire constraint, not by a missing proof.
* **`stackLoad w n` / `stackStore w n`** — operate on a `.stackArr w n` (an
  array cell family, not a single `BitVec`) with a `.reg 64` index, and
  `stackStore` *returns* a `.stackArr w n`. `LstateN` tags each register with a
  single `BitVec w`; it has no array-cell carrier, and the runtime index lives at
  width 64 ≠ w. A faithful model needs the memory/array carrier added to the
  state (a second, separately-sized store dimension), which is an orthogonal
  state extension (the memory axis), not the width-mixing axis this increment
  closes. Deferred to the memory increment.
* **`mulhi w`** — `[reg w, reg w] → reg w`: uniform width, *already* expressible
  in the increment-4 single-width store; its obstruction is not width (it would
  belong in a `mulHiW`-arm widening of `applyOpn`, an op-set step at fixed
  width, orthogonal to this increment). Modeling it here adds nothing to the
  width-mixing story, so it is left to an op-set increment.
* **`addCarryLo w` / `addCarryHi w`** — carry-coupled: the carry-in is `.reg 1`
  and `addCarryHi` *returns* `.reg 1`. The carry datum lives at width 1
  while the data words live at width `w`, so these are width-mixing in the same
  way `select` is, and `LstateN` *can* carry them. They are deferred only to keep
  this increment to one representative width-mixing op (`select`); the same
  `LstateN` + `lsemStepN` machinery extends to them (read two `.reg w` and one
  `.reg 1`, write `addCarryWord`/`carryOutBit`). Deferred: machinery
  present, arm not added.

## Fidelity (trust-critical)

* `regArith`/`regConst` arms of `lsemStepN` are the increment-1/4 arms lifted to
  read/write the width-tagged store; their denotational agreement is the
  width-tagged analogue of `applyOpn_binOpName` / `lsemStep_const`.
* `select`'s arm reads `cond : BitVec 1`, `a b : BitVec w` from the store and
  writes `selectW cond a b`, which is *definitionally* `(select w).denote`'s
  value. Faithful to Coq `eval_instr`'s `Lopn` (evaluate sources, run the
  cmov `exec_sopn`, write the destination, advance the pc).
* `linstrLeak` is increment 3's, unchanged — it reads only the `LinstrR` syntax
  (opcode + operand *register names / immediates*), never a stored value. For
  `select` this means the cond's **register name** leaks, never the 1-bit secret
  it holds: the branch-free CT property the task requires.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust

/-! ## 1. `LstateN`: the non-uniform-width linear state

Mirror of Coq `lstate`'s straight-line fields, but with the variable map
width-tagged: each register holds a value of its *own* width
(`Σ w, BitVec w`), so a `BitVec 1` condition and a `BitVec w` datum coexist.
Generalises increment 1's `Lstate w` (`lvm : String → BitVec w`), recovered by
tagging every register with the same `w`. -/

/-- The non-uniform-width linear-machine state for the straight-line fragment.
    `lvm` width-tags each register (`Σ w, BitVec w`): the register may hold a
    value of any width, recoverable from its tag. This generalises increment 1's
    single-width `Lstate w` (`String → BitVec w`) to the width-mixing fragment. -/
structure LstateN where
  /-- The width-tagged variable/register map: each name maps to a value together
      with its width. Untouched names default to the 0-width zero `⟨0, 0#0⟩`. -/
  lvm : String → Σ w, BitVec w := fun _ => ⟨0, 0#0⟩
  /-- `lpc : nat` — the program counter. -/
  lpc : Nat := 0

/-- Read a register **at an expected width** `w`: `some v` iff the stored tag is
    `w` (then `v` is the stored value), `none` on a width mismatch. The
    width-tagged analogue of `Lstate.get`. -/
def LstateN.getW (s : LstateN) (r : String) (w : Nat) : Option (BitVec w) :=
  if hw : (s.lvm r).fst = w then some (hw ▸ (s.lvm r).snd) else none

/-- Write a register `r` with a width-`w` value, leaving the pc unchanged.
    The `lvm`-update of `lset_estate'` restricted to a single (width-tagged) var
    write. -/
def LstateN.setReg (s : LstateN) (r : String) {w : Nat} (v : BitVec w) : LstateN :=
  { s with lvm := fun r' => if r' = r then ⟨w, v⟩ else s.lvm r' }

/-- `lnext_pc`: advance the pc by one, leaving the store unchanged. -/
def LstateN.nextPc (s : LstateN) : LstateN := { s with lpc := s.lpc + 1 }

@[simp] theorem LstateN.lvm_setReg (s : LstateN) (r : String) {w : Nat} (v : BitVec w) :
    (s.setReg r v).lvm = (fun r' => if r' = r then ⟨w, v⟩ else s.lvm r') := rfl

@[simp] theorem LstateN.lpc_setReg (s : LstateN) (r : String) {w : Nat} (v : BitVec w) :
    (s.setReg r v).lpc = s.lpc := rfl

@[simp] theorem LstateN.lpc_nextPc (s : LstateN) : s.nextPc.lpc = s.lpc + 1 := rfl

@[simp] theorem LstateN.lvm_nextPc (s : LstateN) : s.nextPc.lvm = s.lvm := rfl

@[simp] theorem LstateN.getW_setReg_same (s : LstateN) (r : String) {w : Nat}
    (v : BitVec w) : (s.setReg r v).getW r w = some v := by
  have h : (s.setReg r v).lvm r = ⟨w, v⟩ := by simp [LstateN.setReg]
  unfold LstateN.getW
  rw [h]
  simp

@[simp] theorem LstateN.getW_setReg_other (s : LstateN) (r r' : String) {w : Nat}
    (v : BitVec w) (w' : Nat) (h : r' ≠ r) :
    (s.setReg r v).getW r' w' = s.getW r' w' := by
  have hlvm : (s.setReg r v).lvm r' = s.lvm r' := by simp [LstateN.setReg, if_neg h]
  unfold LstateN.getW
  rw [hlvm]

@[simp] theorem LstateN.getW_nextPc (s : LstateN) (r : String) (w : Nat) :
    s.nextPc.getW r w = s.getW r w := by
  simp only [LstateN.getW, LstateN.nextPc]
  exact rfl

/-! ## 2. Width-aware operand evaluation

A source operand is evaluated *at an expected width* `w`: a register read
consults the tag (`getW`), an immediate is the literal at width `w`. The
width-tagged analogue of increment 1's `evalOperand` (which was width-uniform).
Array operands are out of scope (the memory increment), so they fail at any
expected width. -/

/-- Evaluate a source operand at expected width `w`. A register reads `lvm` and
    succeeds iff its stored tag is `w`; an immediate is the literal at width `w`.
    Array / SIB operands are out of scope (deferred memory increment), so they
    yield `none`. Faithful to `sem_rexpr` on the `Pvar`/`Pconst` cases the
    in-scope ops emit. -/
def evalOperandN (s : LstateN) (w : Nat) : LOperand → Option (BitVec w)
  | .reg r => s.getW r w
  | .imm v => some (BitVec.ofNat w v)
  | .arr _ _ => none
  | .arrIdx _ _ _ => none

@[simp] theorem evalOperandN_nextPc (s : LstateN) (w : Nat) (o : LOperand) :
    evalOperandN s.nextPc w o = evalOperandN s w o := by
  cases o <;> simp [evalOperandN, LstateN.getW, LstateN.nextPc]
  exact rfl

/-! ## 3. `lsemStepN`: the width-aware single-instruction step

Mirror of Coq `eval_instr` on the straight-line cases, over the width-tagged
store. Each in-scope arm reads its sources at their (op-determined) widths,
applies the op, writes the (op-determined-width) destination, and advances the
pc. The width of each source/result is determined by the *opcode mnemonic*
(plus the agreement invariant), exactly as `exec_sopn`'s descriptor does in Coq.

The arms covered here are `regArith` (via the tagged `applyOpn`), `regConst`
(immediate MOV), and `select` (CMOV: cond `.reg 1`, data `.reg w`). The bare
mnemonics the in-scope ops emit are: `withWidthTag w (binOpName bop)`,
`withWidthTag w "MOV"`, and `withWidthTag w "CMOV"`. We strip the width tag and
dispatch on the base mnemonic. -/

/-- Apply the width-`w` register-arithmetic / MOV fragment of `exec_sopn` over a
    homogeneous list of width-`w` source words. The width-tagged analogue of
    increment 1's `applyOpn` (here every input/output is the same `w`; the
    width-*mixing* `select` is a separate arm of `lsemStepN`, not of this
    function). -/
def applyOpnN (w : Nat) : String → List (BitVec w) → Option (BitVec w)
  | "ADD", [a, b] => some (a + b)
  | "SUB", [a, b] => some (a - b)
  | "MUL", [a, b] => some (a * b)
  | "AND", [a, b] => some (a &&& b)
  | "OR",  [a, b] => some (a ||| b)
  | "XOR", [a, b] => some (a ^^^ b)
  | "SHL", [a, b] => some (a <<< b.toNat)
  | "SHR", [a, b] => some (a >>> b.toNat)
  | "ANDN", [a, b] => some ((~~~a) &&& b)
  | "MOV", [a] => some a
  | "NEG", [a] => some (0 - a)
  | _, _ => none

/-- `applyOpnN` agrees with `JasminBinOp.apply` on the binary register-arithmetic
    opcodes `binOpName` produces — the width-tagged analogue of
    `applyOpn_binOpName`. -/
theorem applyOpnN_binOpName {w : Nat} (bop : JasminBinOp) (a b : BitVec w) :
    applyOpnN w (binOpName bop) [a, b] = some (bop.apply a b) := by
  cases bop <;> rfl

/-- The `applyOpnN` value of the one-source `"NEG"` opcode: two's-complement
    negation, the data word `x86_NEG` writes. -/
theorem applyOpnN_NEG {w : Nat} (a : BitVec w) :
    applyOpnN w "NEG" [a] = some (0 - a) := rfl

/-- The `applyOpnN` value of the one-source `"MOV"` opcode: the read word itself,
    the data a register-to-register `MOV dst, src` copies. -/
theorem applyOpnN_MOV {w : Nat} (a : BitVec w) :
    applyOpnN w "MOV" [a] = some a := rfl

/-- The width tag round-trips on every binary register-arithmetic mnemonic:
    `stripWidthTag` recovers `binOpName bop` from the tagged form. Quantifying
    over `JasminBinOp` discharges the per-opcode kernel evaluation once, so a
    consumer cites this instead of re-deciding the tag at each use site. -/
theorem stripWidthTag_withWidthTag_binOpName' (w : Nat) (bop : JasminBinOp) :
    stripWidthTag (withWidthTag w (binOpName bop)) = binOpName bop := by
  unfold withWidthTag
  split <;> cases bop <;> decide +kernel

/-- The register name carried by an operand (the empty string for a
    non-register operand — never reached for the in-scope `.reg`-resolved
    operands). -/
def operandName : LOperand → String
  | .reg r => r
  | _ => ""

/-- Read a `.reg` operand's *width-tagged* value out of the store
    (`some ⟨w, v⟩`); `none` for a non-register operand (in-scope ops resolve
    every data source to a `.reg`). The width is recovered from the store tag —
    this is how `lsemStepN` learns the op's data width without a wire-format
    width annotation. -/
def readReg (s : LstateN) : LOperand → Option (Σ w, BitVec w)
  | .reg r => some (s.lvm r)
  | _ => none

/-- Recover the data width a body mnemonic's `withWidthTag` commits to: `64` for a
    `":64"`-tagged mnemonic, `32` for an untagged one. This is the width
    `read_linear` materialises the instruction at — the tagged ops at `U64`, the
    untagged ops at the reader's `default_ws = U32` — so it is the exact data width
    on the two widths the wire format distinguishes (`{32, 64}`). For the nullary
    `regConst` image `withWidthTag w "MOV" [.imm n]` (which carries no source
    register to read a width from), this is the only width information on the wire. -/
def widthFromTag (opn : String) : Nat :=
  if JasminLprogExport.hasSuffix opn ":64" then 64 else 32

/-- The width tag recovers the data width on the two wire-distinguished widths
    `{64, 32}`: `widthFromTag (withWidthTag w "MOV") = w` when `w` is `64` or `32`
    (the `U64`-tagged path and the reader's `default_ws = U32` path). The exact
    width of a `regConst w n` immediate-MOV is therefore on the wire for those
    widths. -/
theorem widthFromTag_withWidthTag_MOV {w : Nat} (hw : w = 64 ∨ w = 32) :
    widthFromTag (JasminLprogExport.withWidthTag w "MOV") = w := by
  unfold widthFromTag JasminLprogExport.withWidthTag
  rcases hw with hw | hw <;> subst hw <;> decide +kernel

/-- The single one-source negate linear instruction writing `dst` from source
    operand `src` at width `w`: `Lopn [.reg dst] (withWidthTag w "NEG") [src]`.
    The jasmin `Ox86 (NEG ws)` arity — one source, one destination. -/
def negLinstr (w : Nat) (dst : String) (src : LOperand) : LinstrR :=
  .Lopn [.reg dst] (JasminLprogExport.withWidthTag w "NEG") [src]

/-- The conditional-move linear instruction writing `dst` at width `w`:
    `Lopn [.reg dst] (withWidthTag w "CMOV") srcs`, whose sources are the
    condition register followed by the two data operands. The jasmin
    `Ox86 (CMOVcc ws)` arity — three sources, one destination. -/
def cmovLinstr (w : Nat) (dst : String) (srcs : List LOperand) : LinstrR :=
  .Lopn [.reg dst] (JasminLprogExport.withWidthTag w "CMOV") srcs

/-- The zero-extend linear instruction writing `dst` from the width-1 source
    register `src`: `Lopn [.reg dst] "ZEROEXT" [.reg src]`. The mnemonic carries
    no width tag; the destination width travels in the instruction's `MemTag`. -/
def zeroextLinstr (dst src : String) : LinstrR :=
  .Lopn [.reg dst] "ZEROEXT" [.reg src]

/-- The immediate-move linear instruction writing the literal `n` to `dst` at
    width `w`: `Lopn [.reg dst] (withWidthTag w "MOV") [.imm n]`. The nullary
    `regConst` form — no source register, so the width tag is the only width
    information on the wire. -/
def movImmLinstr (w : Nat) (dst : String) (n : Nat) : LinstrR :=
  .Lopn [.reg dst] (JasminLprogExport.withWidthTag w "MOV") [.imm n]

/-- The width-`w` word an immediate shift with base mnemonic `m` (`"SHL"`,
    `"SHR"` or `"SAR"`) and compile-time count `k` writes. `"SHL"` and `"SHR"`
    are the `applyOpnN` shifts at the count materialised as a width-`w` word;
    `"SAR"` is the arithmetic right shift, which `applyOpnN` does not carry. Any
    other mnemonic is `none`. -/
def applyImmShiftN (w : Nat) (m : String) (k : Nat) (a : BitVec w) : Option (BitVec w) :=
  if m = "SAR" then some (BitVec.sshiftRight a k)
  else if m = "SHL" || m = "SHR" then applyOpnN w m [a, BitVec.ofNat w k]
  else none

/-- The base mnemonic `"NEG"` round-trips through
    `stripWidthTag ∘ withWidthTag`. -/
theorem stripWidthTag_withWidthTag_NEG (w : Nat) :
    JasminLprogExport.stripWidthTag (JasminLprogExport.withWidthTag w "NEG") = "NEG" := by
  unfold JasminLprogExport.withWidthTag; split <;> decide +kernel

/-- Width-aware single-step linear semantics, faithful to Coq `eval_instr` on the
    in-scope straight-line cases:

    * `Lopn [.reg dst] opn [a, b]` with `stripWidthTag opn ∈ {ADD,…,ANDN}` —
      read the data width `wₐ` from `a`'s store tag, evaluate `b` at `wₐ`, apply
      the binop, write `dst` at width `wₐ`, advance pc. (`regArith`.)
    * `Lopn [.reg dst] opn [c, a, b]` with `stripWidthTag opn = "CMOV"` —
      read the cond at width 1 from `c`, the data width `wₐ` from `a`'s store
      tag, evaluate `b` at `wₐ`, write `selectW cond a b` to `dst` at width `wₐ`,
      advance pc. (`select` — **the width-mixing arm**: cond `BitVec 1`, data
      `BitVec wₐ`.)
    * `Lopn [.reg dst] opn [.imm n]` with `stripWidthTag opn = "MOV"` — the
      immediate-MOV: write `BitVec.ofNat (widthFromTag opn) n` to `dst` (the data
      width recovered from the width tag — the only width the nullary const carries
      on the wire, exact on `w ∈ {64, 32}`), advance pc. (`regConst`.)
    * `Lopn [.reg dst] opn [.reg a]` with `stripWidthTag opn = "NEG"` — the
      one-source negate: read the data width `wₐ` from `a`'s store tag, apply
      `applyOpnN wₐ "NEG"`, write `dst` at width `wₐ`, advance pc. (`regUn`.)
    * `Lopn [.reg dst] opn [.reg a]` with `stripWidthTag opn = "MOV"` — the
      register-to-register move: read the data width `wₐ` from `a`'s store tag,
      apply `applyOpnN wₐ "MOV"` (the identity on the read word), write `dst` at
      width `wₐ`, advance pc. This is the register-source counterpart of the
      nullary immediate `MOV` arm above (`[.imm n]`), and models the `MOV dst, src`
      copy the schoolbook column emits to route a materialised carry word.
    * `Lopn [.reg dst] opn [.reg a]` with `immShiftMnem? opn = some (m, k)` — the
      count-in-mnemonic immediate shift `opToLinstrR` emits for
      `shrImm`/`shlImm`/`sarImm`: read the data width `wₐ` from `a`'s store tag,
      apply `applyImmShiftN wₐ m k`, write `dst` at width `wₐ`, advance pc.
      A one-source `Lopn` under any other mnemonic returns `none`.

    The CMOV arm is matched *before* the generic binop arm (`select`'s mnemonic
    `CMOV` is not a binop name, but matching CMOV explicitly keeps the arms
    disjoint and the proofs case-split-free). All other instructions (control
    flow, out-of-scope ops, ill-shaped operand lists, and — by the frozen-wire
    deferral — `castW`/stack/carry) return `none`: partiality, never a
    fabricated step. -/
def lsemStepN (i : LinstrR) (s : LstateN) : Option LstateN :=
  match i with
  | .Lopn [.reg dst] opn [c, a, b] =>
      if stripWidthTag opn = "CMOV" then
        -- `select` image: cond at width 1, data at the data width `wₐ` from `a`.
        match s.getW (operandName c) 1, readReg s a with
        | some cond, some ⟨wₐ, va⟩ =>
            match evalOperandN s wₐ b with
            | some vb => some ((s.setReg dst (selectW cond va vb)).nextPc)
            | none => none
        | _, _ => none
      else none
  | .Lopn [.reg dst] opn [a, b] =>
      -- `regArith` image: both sources at the common width `wₐ` from `a`.
      match readReg s a with
      | some ⟨wₐ, va⟩ =>
          match evalOperandN s wₐ b with
          | some vb =>
              match applyOpnN wₐ (stripWidthTag opn) [va, vb] with
              | some v => some ((s.setReg dst v).nextPc)
              | none => none
          | none => none
      | none => none
  | .Lopn [.reg dst] opn [.imm n] =>
      -- `regConst` image: the immediate-MOV. The data width is recovered from the
      -- width tag (`widthFromTag`), the only width information the nullary const
      -- carries on the wire; the value is the literal at that width.
      if stripWidthTag opn = "MOV" then
        some ((s.setReg dst (BitVec.ofNat (widthFromTag opn) n)).nextPc)
      else none
  | .Lopn [.reg dst] opn [.reg a] =>
      -- `regUn` image (`NEG`) and the register-source `MOV`: the single source at
      -- the data width `wₐ` from `a`'s store tag. Gated on the mnemonic, as the
      -- `CMOV` arm is, so every other one-source `Lopn` keeps its `none`.
      if stripWidthTag opn = "NEG" then
        match readReg s (.reg a) with
        | some ⟨wₐ, va⟩ =>
            match applyOpnN wₐ "NEG" [va] with
            | some v => some ((s.setReg dst v).nextPc)
            | none => none
        | none => none
      else if stripWidthTag opn = "MOV" then
        match readReg s (.reg a) with
        | some ⟨wₐ, va⟩ =>
            match applyOpnN wₐ "MOV" [va] with
            | some v => some ((s.setReg dst v).nextPc)
            | none => none
        | none => none
      else
        match JasminImmShiftMnem.immShiftMnem? opn with
        | some (m, k) =>
            match readReg s (.reg a) with
            | some ⟨wₐ, va⟩ =>
                match applyImmShiftN wₐ m k va with
                | some v => some ((s.setReg dst v).nextPc)
                | none => none
            | none => none
        | none => none
  | .Lopn _ _ _ => none
  | .Lalign => some s.nextPc
  | .Llabel _ _ => some s.nextPc
  | .Lgoto _ => none
  | .Lcond _ _ => none
  | .Ligoto _ => none
  | .Lcall _ _ => none
  | .Lret => none
  | .LstoreLabel _ _ => none
  | .Lsyscall _ => none

/-- `getW r w = some v` exactly pins the store tag at `r` to `⟨w, v⟩`. The bridge
    between the expected-width read `getW` and the raw width-tagged cell, used to
    recover the data width in the simulation. -/
theorem getW_eq_some_iff {s : LstateN} {r : String} {w : Nat} {v : BitVec w} :
    s.getW r w = some v ↔ s.lvm r = ⟨w, v⟩ := by
  unfold LstateN.getW
  generalize hcell : s.lvm r = cell
  obtain ⟨w', v'⟩ := cell
  constructor
  · intro h
    by_cases hw : w' = w
    · subst hw
      rw [dif_pos rfl] at h
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · rw [dif_neg hw] at h; exact absurd h (by simp)
  · intro h
    rw [Sigma.mk.injEq] at h
    obtain ⟨hfst, hsnd⟩ := h
    subst hfst
    simp at hsnd
    subst hsnd
    rw [dif_pos rfl]

/-- `readReg` recovers the width-tagged value of a `.reg` operand from a
    `getW`-agreement: if `getW r w = some v` then `readReg` reads `⟨w, v⟩`. -/
theorem readReg_of_getW {s : LstateN} {r : String} {w : Nat} {v : BitVec w}
    (h : s.getW r w = some v) : readReg s (.reg r) = some ⟨w, v⟩ := by
  simp only [readReg, (getW_eq_some_iff).1 h]

/-! ## 4. `lsem1N` / determinism and `lsemStraightN`

The width-aware analogues of increment 1's `lsem1`/`lsemStraight` and the
composition law `lsemStraight_append`. Identical shape, over `LstateN`. -/

/-- The single-instruction step as a relation (Coq `lsem1`), here over the
    width-tagged state. -/
def lsem1N (i : LinstrR) (s1 s2 : LstateN) : Prop := lsemStepN i s1 = some s2

/-- `lsem1N` is deterministic (Coq `lsem1_fun`). -/
theorem lsem1N_deterministic (i : LinstrR) (s1 s2 s3 : LstateN)
    (h12 : lsem1N i s1 s2) (h13 : lsem1N i s1 s3) : s2 = s3 := by
  rw [lsem1N] at h12 h13; rw [h12] at h13; exact Option.some.inj h13

/-- Width-aware straight-line execution: the sequential fold of `lsemStepN`,
    short-circuiting at the first unmodeled / erroring instruction. The
    reflexive-transitive closure `lsem` restricted to straight-line code over the
    width-tagged state. -/
def lsemStraightN : List LinstrR → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepN i s with
      | some s' => lsemStraightN is s'
      | none => none

@[simp] theorem lsemStraightN_nil (s : LstateN) : lsemStraightN [] s = some s := rfl

@[simp] theorem lsemStraightN_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemStraightN (i :: is) s =
      (match lsemStepN i s with
        | some s' => lsemStraightN is s'
        | none => none) := rfl

/-- **Sequential composition**, width-aware: the Kleisli composite of the two
    halves (the increment-1 `lsemStraight_append` over `LstateN`). -/
theorem lsemStraightN_append (xs ys : List LinstrR) (s : LstateN) :
    lsemStraightN (xs ++ ys) s = (lsemStraightN xs s).bind (lsemStraightN ys) := by
  induction xs generalizing s with
  | nil => simp
  | cons i is ih =>
      simp only [List.cons_append, lsemStraightN]
      cases lsemStepN i s with
      | none => rfl
      | some s' => exact ih s'

/-! ## 5. The width-mixed source fragment `ScalarArithN`

Every binding is either a binary `regArith bop w` or a width-mixing `select w`,
over a (possibly non-uniform) context. Generalises `UniformRegArith`: a uniform
`regArith` program is a `ScalarArithN` program (`ScalarArithN.of_regArith`). The
context is *not* required uniform — `select`'s cond operand is `.reg 1`. -/

/-- The straight-line **width-mixed scalar** fragment: every binding is either a
    binary `regArith bop w` or a width-mixing `select w`, and the program returns
    a register `.reg t`. The context `Γ` is arbitrary (non-uniform); `select`
    reads a `.reg 1` cond and two `.reg w` data operands. -/
inductive ScalarArithN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarArithN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarArithN body) :
      ScalarArithN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarArithN body) :
      ScalarArithN (.var ⟨JasminOp.select w, heq, args⟩ body)

/-- `ScalarArithN` subsumes `UniformRegArith`: every uniform `regArith`-only
    straight-line program is in the width-mixed fragment. So the increment-2/3
    `regArith` results are special cases of the increment-5 results below. -/
theorem ScalarArithN.of_regArith {w : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : UniformRegArith w com) : ScalarArithN com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih

/-- A `ScalarArithN` program returns a register: its result type is `.reg w` for
    some `w`. -/
theorem ScalarArithN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) : ∃ w, t = .reg w := by
  induction hcom with
  | ret v => exact ⟨_, rfl⟩
  | var _ _ _ _ ih => exact ih
  | sel _ _ _ ih => exact ih

/-- With the trivial immediate-slot map (`fun _ => none`), `resolveVar` always
    produces a register operand. So every in-scope data source is a `.reg`, which
    `readReg`/`evalOperandN` read by name. -/
theorem resolveVar_isReg {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    resolveVar curDepth nArgs argName (fun _ => none) v
      = .reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) := by
  simp only [resolveVar]
  split <;> rfl

/-! ## 6. The width-tagged store-agreement invariant

`StoreAgreesN nArgs curDepth s V` says the width-tagged store `s` reproduces the
valuation `V` through the linearizer's `resolveVar` naming: every variable `v` of
type `.reg w'` reads, from `s` *at its own width `w'`*, the value `V` assigns it.
The non-uniform-width analogue of increment 2's `StoreAgrees` (which fixed one
`w`); here each variable carries its own `w'`. -/

/-- The width-tagged store `s` agrees with valuation `V` at SSA depth `curDepth`:
    every in-scope variable `v : Var Γ (.reg w')`, resolved through the
    linearizer's `resolveVar` naming, reads its `V`-value out of `s` **at width
    `w'`** (`evalOperandN … w'` succeeds and returns it). -/
def StoreAgreesN (nArgs curDepth : Nat) {Γ : Ctxt jasminDialect}
    (s : LstateN) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ {w' : Nat} (v : Ctxt.Var Γ (.reg w')),
    evalOperandN s w' (resolveVar curDepth nArgs argName (fun _ => none) v) =
      some (v.lookup V)

/-- Writing the fresh register `regName curDepth` (at width `w`) does not change
    how an earlier variable (resolved slot `< curDepth`) reads from the store:
    the destination name differs from every earlier register/argument name.
    Width-tagged analogue of `evalOperand_setReg_resolveVar`. -/
theorem evalOperandN_setReg_resolveVar {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {w' : Nat} (v : Ctxt.Var Γ (.reg w')) (s : LstateN) {w : Nat} (val : BitVec w)
    (hlt : varIndex v < curDepth) :
    evalOperandN (s.setReg (regName curDepth) val) w'
        (resolveVar curDepth nArgs argName (fun _ => none) v) =
      evalOperandN s w' (resolveVar curDepth nArgs argName (fun _ => none) v) := by
  simp only [resolveVar]
  set slot := curDepth - 1 - varIndex v with hslot
  have hslt : slot < curDepth := by omega
  by_cases hsa : slot < nArgs
  · simp only [hsa, if_true, evalOperandN]
    rw [LstateN.getW_setReg_other]
    exact fun he => (JasminLsemSimulation.regName_ne_argName curDepth slot) he.symm
  · simp only [hsa, if_false, evalOperandN]
    rw [LstateN.getW_setReg_other]
    exact fun he => (JasminLsemSimulation.regName_ne (by omega)) he.symm

/-- **Invariant preservation.** Writing the new binding's value `val` (a `.reg w`
    word) to `regName curDepth` and advancing the pc preserves `StoreAgreesN`,
    extending the valuation with `val` at depth `curDepth + 1`. Width-tagged
    analogue of increment 2's `StoreAgrees.step`. -/
theorem StoreAgreesN.step {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateN} {V : Ctxt.Valuation Γ} {w : Nat} (val : BitVec w)
    (hlen : Γ.length = curDepth) (harg : nArgs ≤ curDepth)
    (hagree : StoreAgreesN nArgs curDepth s V) :
    StoreAgreesN nArgs (curDepth + 1)
      ((s.setReg (regName curDepth) val).nextPc)
      (V.extend (Γ := Γ) (t := .reg w) val) := by
  intro w' v
  cases v with
  | here =>
      simp only [resolveVar, varIndex, evalOperandN_nextPc]
      have hslot : curDepth + 1 - 1 - 0 = curDepth := by omega
      simp only [hslot]
      have hsa : ¬ curDepth < nArgs := by omega
      simp only [hsa, if_false, evalOperandN]
      -- `.here : Var (.reg w :: Γ) (.reg w')` forces `w' = w`; reads `val`.
      rw [LstateN.getW_setReg_same]
      rfl
  | there v' =>
      rw [JasminLsemSimulation.resolveVar_there, evalOperandN_nextPc]
      have hlt : varIndex v' < curDepth := by
        have := JasminLsemSimulation.varIndex_lt v'; omega
      rw [evalOperandN_setReg_resolveVar v' s val hlt]
      exact hagree v'

/-- Evaluating a `resolveVar` operand at width `w` is reading its register name
    at width `w`: `evalOperandN s w (resolveVar … v) = s.getW (operandName …) w`.
    The single rewrite that turns an `evalOperandN` into a `getW` (no recursive
    blow-up, unlike folding `resolveVar_isReg` into simp). -/
theorem evalOperandN_resolveVar {curDepth nArgs : Nat} {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (s : LstateN) (w : Nat) (v : Ctxt.Var Γ τ) :
    evalOperandN s w (resolveVar curDepth nArgs argName (fun _ => none) v) =
      s.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) v)) w := by
  simp only [resolveVar, operandName]
  split <;> rfl

/-- From a `StoreAgreesN` agreement, `readReg` reads a data source `v : Var Γ
    (.reg w')` as `⟨w', v.lookup V⟩`: the width is recovered as `w'` and the value
    matches the valuation. The bridge that lets `lsemStepN` learn the data width
    from the store. -/
theorem readReg_resolveVar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateN} {V : Ctxt.Valuation Γ} {w' : Nat} (v : Ctxt.Var Γ (.reg w'))
    (hagree : StoreAgreesN nArgs curDepth s V) :
    readReg s (resolveVar curDepth nArgs argName (fun _ => none) v)
      = some ⟨w', v.lookup V⟩ := by
  have hget := hagree v
  rw [resolveVar_isReg v] at hget ⊢
  simp only [evalOperandN] at hget
  exact readReg_of_getW hget

/-! ## 7. Per-op agreement: the `regArith` and `select` bindings step faithfully

Each binding `lsemStepN`s, from a store agreeing with `V`, to the state that
writes the binding's `Com`-denotation to `regName curDepth` and advances the pc.
`regArith` reuses the increment-2 shape (now reading at the recovered width);
`select` is the new width-mixing arm (cond at width 1, data at width `w`). -/

/-- The width tag round-trips on the `CMOV` mnemonic (kernel evaluation per width
    branch, as for `MOV`/binops). -/
theorem stripWidthTag_withWidthTag_CMOV (w : Nat) :
    stripWidthTag (withWidthTag w "CMOV") = "CMOV" := by
  unfold withWidthTag
  split <;> decide +kernel

/-- The width tag round-trips on a binop mnemonic that is **not** `CMOV`: needed
    to know the `regArith` arm is taken (the `[a,b]` list never matches the
    `[c,a,b]` CMOV arm, so this is only a sanity fact, kept explicit). -/
theorem binOpName_ne_CMOV (bop : JasminBinOp) : binOpName bop ≠ "CMOV" := by
  cases bop <;> decide

/-- **`regArith` per-binding step (width-aware).** From a store agreeing with `V`
    at depth `curDepth`, a `regArith bop w` binding `lsemStepN`s to the state that
    writes `e.denote V` to `regName curDepth` and advances the pc. The data width
    `w` is recovered from the first source's store tag (`readReg_resolveVar`).
    Faithful to `eval_instr`'s `Lopn` arm. -/
theorem lsemStepN_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepN
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons a0 (.cons a1 .nil) =>
    have hargs : exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ : Expr jasminDialect Γ (.reg w))
        = [resolveVar curDepth nArgs argName (fun _ => none) a0,
           resolveVar curDepth nArgs argName (fun _ => none) a1] := rfl
    simp only [opToLinstrR, lsemStepN, hargs,
      readReg_resolveVar a0 hagree, hagree a1,
      stripWidthTag_withWidthTag_binOpName, applyOpnN_binOpName]
    rfl

/-- **`select` per-binding step (width-mixing).** From a store agreeing with `V`,
    a `select w` binding `lsemStepN`s to the state that writes
    `selectW cond a b = e.denote V` to `regName curDepth` and advances the pc. The
    cond is read at width 1, the data operands at the data width `w` (recovered
    from `a`'s store tag). This is the first **width-mixing** step (cond `BitVec
    1`, data `BitVec w` in one instruction). -/
theorem lsemStepN_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepN
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons c (.cons a (.cons b .nil)) =>
    have hargs : exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.select w, heq, .cons c (.cons a (.cons b .nil))⟩ :
          Expr jasminDialect Γ (.reg w))
        = [resolveVar curDepth nArgs argName (fun _ => none) c,
           resolveVar curDepth nArgs argName (fun _ => none) a,
           resolveVar curDepth nArgs argName (fun _ => none) b] := rfl
    -- the cond read: at width 1, by name; the `b` read: at the data width `w`
    have hc := hagree c
    rw [evalOperandN_resolveVar] at hc
    simp only [opToLinstrR, lsemStepN, hargs, stripWidthTag_withWidthTag_CMOV,
      if_true, hc, readReg_resolveVar a hagree, hagree b]
    rfl

/-- **`regConst` per-binding step (width-aware).** From any store, a `regConst w n`
    binding `lsemStepN`s to the state that writes `e.denote V = BitVec.ofNat w n`
    to `regName curDepth` and advances the pc. The data width `w` is the only width
    information the nullary const carries on the wire — recovered from the
    immediate-MOV's width tag (`widthFromTag_withWidthTag_MOV`), which pins it on the
    two wire-distinguished widths `w ∈ {64, 32}` (the `hwn` hypothesis). No
    `StoreAgreesN` is needed: a nullary const reads no operand register. Faithful to
    `eval_instr`'s `Lopn` computing the constant. -/
theorem lsemStepN_const {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n))) :
    lsemStepN
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  simp only [opToLinstrR, lsemStepN,
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV, if_pos]
  rw [widthFromTag_withWidthTag_MOV hwn]
  rfl

/-! ## 8. The core width-mixed straight-line simulation

Same induction skeleton as increment 2's `lsemStraight_straightOps`, with the new
`sel` arm closed by `lsemStepN_sel` + `StoreAgreesN.step`. The return type is
`.reg w` for the (existential) width `w` of `ScalarArithN.ret_reg`; the final
register reads `Com.denote com V` at that width. -/

/-- **Core simulation (parametrized by an agreeing start state), width-mixed.**
    From any width-tagged store `st` agreeing with `V` at depth `curDepth`
    (`Γ.length = curDepth`, `nArgs ≤ curDepth`), running the width-mixed
    `.var`-chain `straightOps` succeeds, lands in a store agreeing with the
    binding-extended valuation, and reads `Com.denote com V` (transported to its
    return width) at the return register. -/
theorem lsemStraightN_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightN (straightOps nArgs com curDepth) st = some st' ∧
        evalOperandN st' w (.reg (comRetReg nArgs argName com curDepth)) =
          some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V w hw hlen harg hagree
      cases hw
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]
      exact hagree v
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepN_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ :=
        ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · simp only [straightOps, lsemStraightN_cons, hstep]
        exact hrun
      · simp only [comRetReg]
        exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepN_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ :=
        ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · simp only [straightOps, lsemStraightN_cons, hstep]
        exact hrun
      · simp only [comRetReg]
        exact hret

/-! ## 9. `encodeN`/`decodeN` and the top-level faithfulness statement

`encodeN` places the argument valuation into the width-tagged store under the
linearizer's `argName` naming, each value at *its own width*. Unlike increment
2's `encode` (which required a uniform context `UniformCtxt`), `encodeN` handles a
non-uniform context directly — every `JasminTy` head is tagged with its own
width; only register heads matter (the in-scope fragment's context is all
registers, but the encoder is total). -/

/-- Encode a valuation into a width-tagged store, placing the value at de Bruijn
    index `i` (from the head of `Γ`) at `argName (Γ.length - 1 - i)`, *tagged with
    its own width*. Register heads write a width-`w'` cell; non-register heads
    (never in-scope) are skipped — they are irrelevant to the in-scope `.reg`
    reads. -/
def encodeAuxN : {Γ : Ctxt jasminDialect} → Ctxt.Valuation Γ → LstateN → LstateN
  | [], _, st => st
  | (.reg w') :: rest, .cons hd tl, st =>
      (encodeAuxN tl st).setReg (argName rest.length) (hd : BitVec w')
  | _ :: _, .cons _ tl, st => encodeAuxN tl st

/-- The canonical encoding of an argument valuation into a fresh width-tagged
    store: `argName j ↦ V[j]` at `V[j]`'s own width, `⟨0, 0#0⟩` elsewhere. -/
def encodeN {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) : LstateN :=
  encodeAuxN V {}

/-- Decode a register from a width-tagged store at width `w`: read it back via
    `getW`. Paired with `comRetReg`, this reads the result the body computed. -/
def decodeN (st : LstateN) (obsName : String) (w : Nat) : Option (BitVec w) :=
  st.getW obsName w

/-- `encodeAuxN` reads back each register variable at its `argName` slot, at its
    own width: the value at de Bruijn index `varIndex v` (type `.reg w'`) is
    stored at `argName (Γ.length - 1 - varIndex v)` with tag `w'`. -/
theorem encodeAuxN_lookup {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    (st : LstateN) {τ : JasminTy} (v : Ctxt.Var Γ τ) {w' : Nat} (h : τ = .reg w') :
    (encodeAuxN V st).getW (argName (Γ.length - 1 - varIndex v)) w' =
      some (h ▸ v.lookup V : ⟦(JasminTy.reg w')⟧) := by
  induction v with
  | here =>
      rename_i Γ' σ
      subst h
      -- `Γ = .reg w' :: Γ'`; `varIndex = 0`, target slot `argName Γ'.length`.
      cases V with
      | cons hd tl =>
        show ((encodeAuxN tl st).setReg (argName (List.length Γ')) (hd : BitVec w')).getW
              (argName (List.length Γ' + 1 - 1 - 0)) w' = some hd
        have hslot : List.length Γ' + 1 - 1 - 0 = List.length Γ' := by omega
        rw [hslot, LstateN.getW_setReg_same]
  | there v' ih =>
      rename_i Γ' tt σ
      subst h
      have heq2 : List.length Γ' + 1 - 1 - (varIndex v' + 1)
          = List.length Γ' - 1 - varIndex v' := by omega
      cases V with
      | cons hd tl =>
        have hlt : varIndex v' < List.length Γ' := JasminLsemSimulation.varIndex_lt v'
        cases σ with
        | reg wσ =>
            show ((encodeAuxN tl st).setReg (argName (List.length Γ')) (hd : BitVec wσ)).getW
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' = some (v'.lookup tl)
            rw [LstateN.getW_setReg_other _ _ _ _ _
              (JasminLsemSimulation.argName_ne (by omega)), heq2]
            exact ih tl rfl
        | stackArr wσ nσ =>
            show (encodeAuxN tl st).getW
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl
        | inlineInt =>
            show (encodeAuxN tl st).getW
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl
        | bool =>
            show (encodeAuxN tl st).getW
                  (argName (List.length Γ' + 1 - 1 - (varIndex v' + 1))) w' = some (v'.lookup tl)
            rw [heq2]; exact ih tl rfl

/-- **`encodeN` establishes the start-state agreement.** The encoded store agrees
    with the valuation at the start depth `curDepth = nArgs = Γ.length`. The base
    case of the simulation induction. -/
theorem encodeN_StoreAgreesN {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    StoreAgreesN Γ.length Γ.length (encodeN V) V := by
  intro w' v
  have hslot : Γ.length - 1 - varIndex v < Γ.length := by
    have := JasminLsemSimulation.varIndex_lt v; omega
  simp only [resolveVar, hslot, if_true, evalOperandN, encodeN]
  exact encodeAuxN_lookup V _ v rfl

/-! ## 10. The width-mixed straight-line faithfulness theorem -/

/-- **Straight-line linearizer simulation, width-mixed.** For a width-mixed
    scalar straight-line `Com` whose return type is `.reg w`, running the
    linearizer-emitted `.var`-chain `straightOps` from the encoded argument
    valuation and decoding the result register at width `w` equals the source
    program's `Com.denote`. This is the non-uniform-width counterpart of
    `comToLprog_lsem_straightline`, now covering the width-mixing `select`. -/
theorem comToLprog_lsemN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightN (straightOps Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightN_straightOps hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), width-mixed.** The width-mixed straight-line body,
    run on the encoded inputs and decoded at the result register, equals the
    source denotation. -/
theorem comToLprog_faithful_widthN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightN (straightOps Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemN hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-! ## 11. The width-mixed leak model and state-independence

The per-instruction leak `linstrLeak` (increment 3) reads only the `LinstrR`
syntax, so it is reused verbatim — for `select`'s `CMOV` it emits a single
`LLeak.opn "CMOV" [regShape dst] [regShape cond, regShape a, regShape b]`: the
condition's **register name** leaks, never its 1-bit value. `lsemLeakN` threads
the width-tagged state through `lsemStepN` (same shape as increment 3's
`lsemLeak`), but each contribution is state-blind, so the trace is
state-independent for the branch-free width-mixed fragment. -/

/-- `lsemLeakN is s`: the linear-IR leakage trace of running `is` from the
    width-tagged state `s`. The width-tagged analogue of increment 3's
    `lsemLeak`; `linstrLeak` (reused) reads only the instruction syntax. -/
def lsemLeakN : List LinstrR → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepN i s with
          | some s' => lsemLeakN is s'
          | none => [])

@[simp] theorem lsemLeakN_nil (s : LstateN) : lsemLeakN [] s = [] := rfl

@[simp] theorem lsemLeakN_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemLeakN (i :: is) s =
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepN i s with
          | some s' => lsemLeakN is s'
          | none => []) := rfl

/-- A `regArith` head always `lsemStepN`s successfully, from **any** width-tagged
    state in which its sources agree (the data width is recovered from the store).
    The width-aware analogue of `lsemStep_regArith_succeeds`. -/
theorem lsemStepN_var_succeeds {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    ∃ st', lsemStepN (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))) st
      = some st' :=
  ⟨_, lsemStepN_var bop heq args hagree⟩

/-- A `select` head always `lsemStepN`s successfully, from **any** width-tagged
    state in which its sources agree. -/
theorem lsemStepN_sel_succeeds {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    ∃ st', lsemStepN (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))) st
      = some st' :=
  ⟨_, lsemStepN_sel heq args hagree⟩

/-- **Robustness / constant-time capstone (unconditional), width-mixed.** The
    linear-IR leakage trace of the width-mixed linearizer-emitted `.var`-chain
    `straightOps` is the **same from any two initial states that agree with the
    same valuation** — every head (`regArith` or the width-mixing `select`) has a
    `linstrLeak` that reads only syntax (the cond's **name**, never its value) and
    `lsemStepN`s successfully, so both states take the `some` branch and the
    (possibly diverged) tails — each still agreeing with the extended valuation —
    are run on the same instruction list, closed by the IH.

    The agreement hypotheses are present because the width-mixed step recovers the
    data width *from the store*: to know that the step *succeeds* (and the leak's
    `some` branch is taken) we need the sources present at the expected widths,
    which is exactly `StoreAgreesN`. For an attacker, the conclusion is the CT
    guarantee: the leak is a function of the emitted instruction list, not of any
    register value. -/
theorem lsemLeakN_straightOps_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakN (straightOps nArgs com curDepth) s₁ =
        lsemLeakN (straightOps nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _
      rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepN_var (V := V₁) bop heq args hag1
      have hstep2 := lsemStepN_var (V := V₂) bop heq args hag2
      simp only [straightOps, lsemLeakN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepN_sel (V := V₁) heq args hag1
      have hstep2 := lsemStepN_sel (V := V₂) heq args hag2
      simp only [straightOps, lsemLeakN_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 12. The unconditional width-mixed capstone: `correct ∧ robust` -/

/-- **Unconditional `correct ∧ robust` for the width-mixed scalar fragment
    (`regArith ∪ select`).** For a width-mixed scalar straight-line `Com` with
    return type `.reg w`:

    1. *(correct, §10)* running the linearizer-emitted `.var`-chain `straightOps`
       on the encoded argument valuation and decoding the result register at width
       `w` yields exactly `com.denote V`; and
    2. *(robust, syntactic leak model, §11)* the linear-IR leakage trace
       `lsemLeakN (straightOps …)` is the **same from the encodings of any two
       input valuations** — the attacker's control-flow + operand-structure view
       (including, for `select`, the cond's register *name*) is a function of the
       emitted instruction list alone, never of a register value.

    This is **unconditional**: no IR→x86 faithfulness hypothesis, no
    `jasminc_preserves_ct`. Both conjuncts concern one and the same object — the
    width-mixed linearizer-emitted straight-line body run by `lsemStraightN`
    (functional) and observed by `lsemLeakN` (CT). The `lsem→bytes` encoder and
    Sail tables remain the declared trusted base. The first capstone covering a
    **width-mixing** op (`select`: cond `BitVec 1`, data `BitVec w`).

    The leak function reads no register value (an indexed access leaks the index
    register's name, not its value), so conjunct 2 holds for every program of the
    fragment and is not constant-time evidence. Constant-time evidence for emitted
    code is `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` (straight-line
    gathered blocks) and the per-kernel `blockLeak` theorems. -/
theorem owned_lsem_correct_and_robust_widthN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarArithN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§10)
    ((lsemStraightN (straightOps Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§11)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakN (straightOps Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakN (straightOps Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_widthN hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakN_straightOps_state_independent hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 13. Tie-back: the uniform-width `regArith` fragment is subsumed

`ScalarArithN.of_regArith` already shows every `UniformRegArith` program is a
`ScalarArithN` program, so the increment-2/3 *functional* `regArith` simulation
is the `regArith`-only restriction of the width-mixed one. The increment-4
uniform capstone additionally covers `regConst` (at one fixed `w`, where the
uniform store pins the width); the width-mixed capstone covers the *orthogonal*
width-mixing axis (`select`). The two are complementary specialisations of the
same straight-line `lsem` foundation, not nested. -/

/-- Every uniform-`regArith` straight-line program is in the width-mixed
    fragment, with return width the uniform `w`. The bridge that makes the
    increment-2/3 `regArith` results special cases of the increment-5 ones. -/
theorem owned_lsem_correct_and_robust_widthN_of_regArith {w : Nat}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    (hcom : UniformRegArith w com) (V : Ctxt.Valuation Γ) :
    ((lsemStraightN (straightOps Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hcom.ret_ty ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakN (straightOps Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakN (straightOps Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_widthN (ScalarArithN.of_regArith hcom) hcom.ret_ty V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
