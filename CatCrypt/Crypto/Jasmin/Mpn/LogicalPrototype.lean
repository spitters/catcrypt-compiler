/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

@[expose] public section

set_option autoImplicit false

/-!
# FEASIBILITY PROTOTYPE — verified variable-length bitwise mpn kernels

**EXPERIMENTAL FILE.**  This is a feasibility prototype for the three
*simplest* GMP bitwise-logical kernels — `mpn_and_n`, `mpn_ior_n`,
`mpn_xor_n`: a per-limb binary bit operation (`AND` / `OR` / `XOR`) on two
equal-length limb arrays, with **no carry**.  Because there is no carry
register to thread across iterations, the emitted `while (n != 0)` loop is
strictly simpler than the `mpn_add_n` loop of `MpnAddPrototype`: each
iteration loads `a[i]`, `b[i]`, computes `a[i] OP b[i]`, stores it, and
advances the three pointers + decrements `n`.

This file reuses, verbatim, all of `MpnAddPrototype`'s plumbing:

* the little-endian denotation `toNat`,
* the `reg u64` helpers `vr`, `pv`, `loadAt0`, `storeAt0`, `binImm`,
* the byte-memory algebra (`load64Mem_store64_same`,
  `load64Mem_store64_disjoint`, `memHoldsLimbs`,
  `memHoldsLimbs_store64_frame`, …),
* the pointer arithmetic (`regAddr`, `regAddr_advance`, `bv_uint_roundtrip`),
* the `Cwhile` fuel rule (`bignumExecFuel_loop_step`,
  `bignumExecFuel_loop_exit`) and the loop-guard evaluators
  (`evalPExpr_loopCond_true/false`),
* the counter lemmas (`ofNat64_succ_ne_zero`, `ofNat64_succ_sub_one`,
  `disjoint_range_lt`, `range_op_head_tail_disjoint`, …).

## What this prototype delivers

1. Three Jasmin `FunDecl`s `mpnAndNFd` / `mpnIorNFd` / `mpnXorNFd`, each a
   pointer-advancing `while (n != 0)` loop built from emitter-supported
   instruction shapes only (constant-offset `Pload`/`Lmem`, the `Papp2`
   bitwise ops `Oland`/`Olor`/`Olxor` over `U64`, and `+=`/`-=`).

2. Pure functional references `mpnAnd` / `mpnIor` / `mpnXor :
   List (BitVec 64) → List (BitVec 64) → List (BitVec 64)`, limb-wise
   `BitVec.and` / `.or` / `.xor`.

3. The functional spec at the `Nat` denotation level:
   `toNat (mpnAnd a b) = toNat a &&& toNat b` (and `|||` / `^^^` for ior /
   xor), for **equal-length** inputs.  This is the genuinely new obligation:
   that a limb-wise bit operation denotes the corresponding `Nat` bit
   operation.  Proved via the bit-parallel correspondence — each output bit
   is a function of the two same-position input bits, and the little-endian
   `2^64`-block decomposition of `toNat` lines those bits up exactly.

4. The bridges `MpnAndJasminRefines` / `MpnIorJasminRefines` /
   `MpnXorJasminRefines`: the emitted `while (n != 0)` loop refines the pure
   reference over byte memory.  These reuse the `MpnAddPrototype` `Cwhile`
   loop-invariant rule + memory frame; the per-iteration step is simpler
   than add_n's (no `#ADC_64`, no carry flag — just a `Papp2` and a store).

## Honest status

* The bit-correspondence spec (point 3) is the only genuinely new proof.
  It rests on `Nat.testBit_two_pow_mul_add` (the little-endian block split)
  + `Nat.testBit_and`/`_or`/`_xor` (per-bit op), assembled by induction on
  the limb list.  See `mpnBitwise_spec` / `mpnAnd_spec` etc.
* The Jasmin bridges (point 4) are fully proved (no `sorry`), reusing the
  `MpnAddPrototype` machinery; the one-iteration step lemma
  (`bignumExec_logBody_step`) is the bitwise analogue of
  `bignumExec_loopBody_step`.

## Equal-length vs. unequal length

The spec is stated for **equal-length** inputs `a.length = b.length`, which
is exactly the GMP `mpn_{and,ior,xor}_n` contract (the `_n` suffix means
both operands have the common limb count `n`).  Unequal lengths behave
differently per op and are a deliberate follow-on:

* `AND` truncates to the *shorter* operand (`Nat.land a b` has no bits above
  `min (bitlen a) (bitlen b)`), so the natural reference would drop the
  longer tail — GMP exposes this as `mpn_and_n` over the common prefix only.
* `IOR` / `XOR` keep the *longer* tail verbatim (the missing limbs of the
  shorter operand act as `0`), so the reference would copy the tail through.

The pure references here recurse in lockstep and stop at the first `nil`
(matching `mpnAddN`); for equal-length inputs the two `nil` branches never
disagree, so the equal-length spec is unaffected.  Extending the references
+ specs to the unequal-length truncate/copy behavior is left as a follow-on.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.LogicalPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype

/-! ## §1  The Jasmin bitwise-kernel bodies — runtime `Cwhile` loop

`MpnAddPrototype`'s `vr` / `pv` / `loadAt0` / `storeAt0` / `binImm` register
helpers are `private`, so we re-declare identical local copies here (the
definitions are character-for-character the same as in `MpnAddPrototype`).
The only new ingredient is the per-limb assignment `r := t OP s`, where
`OP ∈ {Oland, Olor, Olxor}` over `U64`. -/

/-- `reg u64` variable (local copy of `Mpn.AddPrototype.vr`). -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s` (local copy of `Mpn.AddPrototype.pv`). -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- Memory load `x := [:u64 base + 0]` (local copy of `Mpn.AddPrototype.loadAt0`). -/
def loadAt0 (x base : String) : InstrR :=
  .Cassgn (.Lvar { var := vr x }) .AT_none (.sword .U64)
    (.Pload .U64 { var := vr base } (.Pconst 0))

/-- Memory store `[:u64 base + 0] := src` (local copy of `Mpn.AddPrototype.storeAt0`). -/
def storeAt0 (base src : String) : InstrR :=
  .Cassgn (.Lmem .U64 { var := vr base } (.Pconst 0)) .AT_none (.sword .U64)
    (.Pvar { gv := { var := vr src }, gs := false })

/-- `r += k` / `r -= k` scalar update (local copy of `Mpn.AddPrototype.binImm`). -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `r := t OP s` for a binary `Papp2` op (`Oland`/`Olor`/`Olxor`). -/
def binOp (r t s : String) (op : SOp2) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv t) (pv s))

/-- One loop-iteration body for a bitwise kernel:
    ```
    t = [:u64 ap + 0];
    s = [:u64 bp + 0];
    r = t OP s;
    [:u64 op + 0] = r;
    ap += 8; bp += 8; op += 8;
    n  -= 1;
    ```
    Compared with `Mpn.AddPrototype.loopBody` this drops the `#ADC_64` bundle
    (and the carry register entirely) for a single `Papp2` assignment. -/
def logBody (op : SOp2) : List InstrR :=
  [ loadAt0 "t" "ap"
  , loadAt0 "s" "bp"
  , binOp "r" "t" "s" op
  , storeAt0 "op" "r"
  , binImm "ap" (.Oadd .U64) 8
  , binImm "bp" (.Oadd .U64) 8
  , binImm "op" (.Oadd .U64) 8
  , binImm "n"  (.Osub .U64) 1 ]

/-- Full body of a bitwise kernel: just the loop (no carry-register
    prelude — there is no carry).
    ```
    while (n != 0) { <logBody op> }
    ``` -/
def logFullBody (op : SOp2) : List InstrR :=
  [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) (logBody op) ]

/-- `mpn_and_n(op, ap, bp, n)` as a Jasmin `FunDecl` (void; output via
    `*op`).  SysV ABI `rdi=op, rsi=ap, rdx=bp, rcx=n`. -/
def mpnAndNFd : FunDecl where
  name := { name := "mpn_and_n" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := logFullBody (.Oland .U64)
  results := []

/-- `mpn_ior_n` Jasmin `FunDecl`. -/
def mpnIorNFd : FunDecl where
  name := { name := "mpn_ior_n" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := logFullBody (.Olor .U64)
  results := []

/-- `mpn_xor_n` Jasmin `FunDecl`. -/
def mpnXorNFd : FunDecl where
  name := { name := "mpn_xor_n" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := logFullBody (.Olxor .U64)
  results := []

/-- Each kernel is constant-time-*shaped*: the loop condition `n != 0`
    depends only on the public length `n`, never on a secret limb. -/
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody (.Oland .U64)) = true := by decide
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody (.Olor .U64)) = true := by decide
example : CatCrypt.Crypto.Jasmin.isCT_Cmd (logFullBody (.Olxor .U64)) = true := by decide

-- Emit the real `.jazz` source.  `#eval` to read the emitted loops.
#eval match emitFunDecl mpnAndNFd with | some s => s | none => "EMIT FAILED"
#eval match emitFunDecl mpnIorNFd with | some s => s | none => "EMIT FAILED"
#eval match emitFunDecl mpnXorNFd with | some s => s | none => "EMIT FAILED"

/-! ## §2  Pure functional references (limb-wise bit op) -/

/-- Pure reference for `mpn_and_n`: limb-wise `BitVec.and`, recursing in
    lockstep.  Stops at the first `nil` (equal-length contract; see the
    module docstring on unequal-length behavior). -/
def mpnAnd : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | a :: as, b :: bs => (a &&& b) :: mpnAnd as bs
  | _, _ => []

/-- Pure reference for `mpn_ior_n`: limb-wise `BitVec.or`. -/
def mpnIor : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | a :: as, b :: bs => (a ||| b) :: mpnIor as bs
  | _, _ => []

/-- Pure reference for `mpn_xor_n`: limb-wise `BitVec.xor`. -/
def mpnXor : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | a :: as, b :: bs => (a ^^^ b) :: mpnXor as bs
  | _, _ => []

/-! ### Concrete sanity checks (decidable `#eval`/`native_decide`) -/

example : mpnAnd [0xF0, 0xFF] [0x0F, 0x0F] = [0x00, 0x0F] := by native_decide
example : mpnIor [0xF0, 0x00] [0x0F, 0x10] = [0xFF, 0x10] := by native_decide
example : mpnXor [0xFF, 0x0F] [0x0F, 0xFF] = [0xF0, 0xF0] := by native_decide

/-! ## §3  Functional spec: limb-wise bit op denotes the `Nat` bit op

This is the genuinely new obligation of this file.  The little-endian
denotation `toNat (w :: ws) = w.toNat + 2^64 · toNat ws` packs each limb
into its own 64-bit window.  A bitwise op acts pointwise on bits, so it
respects that windowing exactly: bit `j` of the output depends only on bit
`j` of the two inputs.  Formally we use `Nat.testBit_two_pow_mul_add` (the
window split) and `Nat.testBit_{and,or,xor}` (the per-bit op).

We first prove a single *block-split* identity for an arbitrary pointwise
bit op, then instantiate it for `&&&` / `|||` / `^^^`, and finally lift to
the limb list by induction. -/

/-- **Block split for `Nat.land`.**  When the low words `x, y` fit in
    `2^64`, `&&&` distributes over the little-endian `2^64`-window split:
    `(x + 2^64·X) &&& (y + 2^64·Y) = (x &&& y) + 2^64·(X &&& Y)`.
    Proved bit-by-bit: `Nat.testBit_two_pow_mul_add` splits each side at
    bit 64, and `Nat.testBit_and` shows the per-bit op matches in both the
    low window (`j < 64`) and the high window (`j ≥ 64`). -/
theorem land_block_split (x X y Y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (x + 2 ^ 64 * X) &&& (y + 2 ^ 64 * Y) = (x &&& y) + 2 ^ 64 * (X &&& Y) := by
  have hxy : x &&& y < 2 ^ 64 := lt_of_le_of_lt (Nat.and_le_left) hx
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show x + 2 ^ 64 * X = 2 ^ 64 * X + x from by ring,
      show y + 2 ^ 64 * Y = 2 ^ 64 * Y + y from by ring,
      show (x &&& y) + 2 ^ 64 * (X &&& Y) = 2 ^ 64 * (X &&& Y) + (x &&& y) from by ring]
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add X hx j,
      Nat.testBit_two_pow_mul_add Y hy j,
      Nat.testBit_two_pow_mul_add (X &&& Y) hxy j, Nat.testBit_and, Nat.testBit_and]
  by_cases hj : j < 64 <;> simp [hj]

/-- **Block split for `Nat.lor`.** -/
theorem lor_block_split (x X y Y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (x + 2 ^ 64 * X) ||| (y + 2 ^ 64 * Y) = (x ||| y) + 2 ^ 64 * (X ||| Y) := by
  have hxy : x ||| y < 2 ^ 64 := Nat.or_lt_two_pow hx hy
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show x + 2 ^ 64 * X = 2 ^ 64 * X + x from by ring,
      show y + 2 ^ 64 * Y = 2 ^ 64 * Y + y from by ring,
      show (x ||| y) + 2 ^ 64 * (X ||| Y) = 2 ^ 64 * (X ||| Y) + (x ||| y) from by ring]
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add X hx j,
      Nat.testBit_two_pow_mul_add Y hy j,
      Nat.testBit_two_pow_mul_add (X ||| Y) hxy j, Nat.testBit_or, Nat.testBit_or]
  by_cases hj : j < 64 <;> simp [hj]

/-- **Block split for `Nat.xor`.** -/
theorem xor_block_split (x X y Y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (x + 2 ^ 64 * X) ^^^ (y + 2 ^ 64 * Y) = (x ^^^ y) + 2 ^ 64 * (X ^^^ Y) := by
  have hxy : x ^^^ y < 2 ^ 64 := Nat.xor_lt_two_pow hx hy
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show x + 2 ^ 64 * X = 2 ^ 64 * X + x from by ring,
      show y + 2 ^ 64 * Y = 2 ^ 64 * Y + y from by ring,
      show (x ^^^ y) + 2 ^ 64 * (X ^^^ Y) = 2 ^ 64 * (X ^^^ Y) + (x ^^^ y) from by ring]
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add X hx j,
      Nat.testBit_two_pow_mul_add Y hy j,
      Nat.testBit_two_pow_mul_add (X ^^^ Y) hxy j, Nat.testBit_xor, Nat.testBit_xor]
  by_cases hj : j < 64 <;> simp [hj]

/-- The single-limb bridge for `&&&`: `(a &&& b).toNat = a.toNat &&& b.toNat`
    on `BitVec 64`.  (This is `BitVec.toNat_and`, restated for readability.) -/
theorem bvAnd_toNat (a b : BitVec 64) : (a &&& b).toNat = a.toNat &&& b.toNat :=
  BitVec.toNat_and a b

theorem bvOr_toNat (a b : BitVec 64) : (a ||| b).toNat = a.toNat ||| b.toNat :=
  BitVec.toNat_or a b

theorem bvXor_toNat (a b : BitVec 64) : (a ^^^ b).toNat = a.toNat ^^^ b.toNat :=
  BitVec.toNat_xor a b

/-- **Main functional spec for `mpn_and_n` — by induction on the limb list.**
    For equal-length limb lists, the limb-wise `BitVec.and` reference
    denotes the `Nat` `&&&` of the two denotations.  The inductive step
    peels the head limb (`bvAnd_toNat` gives `(a &&& b).toNat = a.toNat &&&
    b.toNat`, both `< 2^64`) and re-blocks the tail via `land_block_split`,
    with the IH supplying `toNat (mpnAnd as bs) = toNat as &&& toNat bs`. -/
theorem mpnAnd_spec :
    ∀ (a b : List (BitVec 64)), a.length = b.length →
      toNat (mpnAnd a b) = toNat a &&& toNat b := by
  intro a
  induction a with
  | nil =>
    intro b hlen
    cases b with
    | nil => simp [mpnAnd, toNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnAnd, toNat]
      rw [ih bs hlen', bvAnd_toNat]
      exact (land_block_split a.toNat (toNat as) b.toNat (toNat bs) a.isLt b.isLt).symm

/-- **Main functional spec for `mpn_ior_n`.** -/
theorem mpnIor_spec :
    ∀ (a b : List (BitVec 64)), a.length = b.length →
      toNat (mpnIor a b) = toNat a ||| toNat b := by
  intro a
  induction a with
  | nil =>
    intro b hlen
    cases b with
    | nil => simp [mpnIor, toNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnIor, toNat]
      rw [ih bs hlen', bvOr_toNat]
      exact (lor_block_split a.toNat (toNat as) b.toNat (toNat bs) a.isLt b.isLt).symm

/-- **Main functional spec for `mpn_xor_n`.** -/
theorem mpnXor_spec :
    ∀ (a b : List (BitVec 64)), a.length = b.length →
      toNat (mpnXor a b) = toNat a ^^^ toNat b := by
  intro a
  induction a with
  | nil =>
    intro b hlen
    cases b with
    | nil => simp [mpnXor, toNat]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnXor, toNat]
      rw [ih bs hlen', bvXor_toNat]
      exact (xor_block_split a.toNat (toNat as) b.toNat (toNat bs) a.isLt b.isLt).symm

/-! ## §4  Length lemmas (output length = input length) -/

theorem mpnAnd_length :
    ∀ (a b : List (BitVec 64)), a.length = b.length → (mpnAnd a b).length = a.length := by
  intro a
  induction a with
  | nil => intro b _; rfl
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnAnd, List.length_cons, ih bs hlen']

theorem mpnIor_length :
    ∀ (a b : List (BitVec 64)), a.length = b.length → (mpnIor a b).length = a.length := by
  intro a
  induction a with
  | nil => intro b _; rfl
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnIor, List.length_cons, ih bs hlen']

theorem mpnXor_length :
    ∀ (a b : List (BitVec 64)), a.length = b.length → (mpnXor a b).length = a.length := by
  intro a
  induction a with
  | nil => intro b _; rfl
  | cons a as ih =>
    intro b hlen
    cases b with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [mpnXor, List.length_cons, ih bs hlen']

/-! ## §5  One loop iteration as an explicit state update

`logBody op` is straight-line, so it runs via `bignumExec`.  Given a state
whose memory holds limb `a` at `ap` and `b` at `bp`, one iteration loads
`a`, `b`; computes `a OP b` (`evalLimbOp`); stores it at `op`; and advances
the three pointers + decrements `n`.  This is the bitwise analogue of
`Mpn.AddPrototype.bignumExec_loopBody_step` (with no carry register). -/

/-- The `BitVec 64` value the per-limb assignment `r := t OP s` computes,
    for the three supported ops. -/
def evalLimbOp (op : SOp2) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .Oland _ => a &&& b
  | .Olor _ => a ||| b
  | .Olxor _ => a ^^^ b
  | _ => 0

/-- For the three bitwise ops, evaluating `Papp2 op (Pvar t) (Pvar s)` in a
    state where `t = a` and `s = b` returns `evalLimbOp op a b`. -/
theorem evalPExpr_binOp (s : BignumState) (op : SOp2) (a b : BitVec 64)
    (ht : s.regs "t" = a) (hs : s.regs "s" = b)
    (hop : op = .Oland .U64 ∨ op = .Olor .U64 ∨ op = .Olxor .U64) :
    evalPExpr s (.Papp2 op (pv "t") (pv "s")) = some (evalLimbOp op a b) := by
  rcases hop with h | h | h <;>
    subst h <;>
    simp only [pv, evalPExpr, vr, evalLimbOp, bind, Option.bind, ht, hs]

/-- The emitted loop guard `n != 0` evaluates to `1` when register `n`
    holds a nonzero value (local-`pv` analogue of
    `Mpn.AddPrototype.evalPExpr_loopCond_true`). -/
theorem evalPExpr_logCond_true (s : BignumState) (hn : s.regs "n" ≠ 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 1 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_neg hn]

/-- The emitted loop guard `n != 0` evaluates to `0` when register `n`
    holds `0` (the loop exit). -/
theorem evalPExpr_logCond_false (s : BignumState) (hn : s.regs "n" = 0) :
    evalPExpr s (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) = some 0 := by
  rw [pv, evalPExpr]
  simp only [evalPExpr, vr, bind, Option.bind,
    show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
  rw [if_pos hn]

/-- One iteration of `logBody op` (run via the straight-line interpreter
    `bignumExec`), assuming memory holds limb `a` at `ap` and `b` at `bp`.
    The result state is described entirely by its `ap`/`bp`/`op`/`n`
    registers and a single `store64` at `op` of `evalLimbOp op a b`. -/
theorem bignumExec_logBody_step (s : BignumState) (op : SOp2) (a b : BitVec 64)
    (hop : op = .Oland .U64 ∨ op = .Olor .U64 ∨ op = .Olxor .U64)
    (ha : load64Mem s.mem (regAddr s "ap") = some (UInt64.ofNat a.toNat))
    (hb : load64Mem s.mem (regAddr s "bp") = some (UInt64.ofNat b.toNat)) :
    ∃ s', bignumExec (logBody op) s = some s' ∧
      s'.mem = s.mem.store64 (regAddr s "op")
        (UInt64.ofNat (evalLimbOp op a b).toNat) ∧
      s'.regs "ap" = s.regs "ap" + 8 ∧
      s'.regs "bp" = s.regs "bp" + 8 ∧
      s'.regs "op" = s.regs "op" + 8 ∧
      s'.regs "n" = s.regs "n" - 1 := by
  -- Case-split on the op so `evalPExpr (Papp2 op …)` and `evalLimbOp op`
  -- both reduce to a concrete arm; the three branches are then identical
  -- straight-line unfolds (load `a`, load `b`, bit-op, store, 4 advances).
  rcases hop with h | h | h <;> subst h <;>
  · -- Unfold the straight-line body, resolving the two loads (round-trip via
    -- `ha`/`hb`), the concrete `Papp2` op, the store, and the four advances.
    simp only [logBody, loadAt0, binOp, storeAt0, binImm, evalLimbOp,
               bignumExec, execInstr, evalPExpr, pv, vr,
               setReg_mem, setReg_regs, storeMem_mem, storeMem_regs,
               Option.bind_some, bind, Option.bind]
    simp only [regAddr, resolveAddr, reduceIte, String.reduceEq, if_true, if_false,
               ↓reduceIte, setReg_regs, storeMem_regs, storeMem_mem,
               show BitVec.ofInt 64 0 = 0 from rfl, BitVec.add_zero,
               ha, hb, bv_uint_roundtrip, Option.bind_some, bind, Option.bind] at *
    -- Fire the first load (`ap + 0` reduces to `ap`).
    rw [show s.regs "ap" + 0 = s.regs "ap" from by bv_decide]
    rw [ha]
    simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
    -- Fire the second load (`bp + 0` in the `t := a` state).
    rw [show (setReg s "t" a).regs "bp" + 0 = s.regs "bp" from by
          simp only [setReg_regs]; bv_decide, setReg_mem, hb]
    simp only [bv_uint_roundtrip, Option.bind_some, bind, Option.bind]
    -- The op evaluates: `t`/`s` hold `a`/`b`; read off store + 4 advances.
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [setReg_regs, setReg_mem, storeMem_mem, storeMem_regs, regAddr,
                 String.reduceEq, ↓reduceIte, reduceIte,
                 show s.regs "op" + 0 = s.regs "op" from by bv_decide,
                 show BitVec.ofInt 64 8 = (8 : BitVec 64) from rfl,
                 show BitVec.ofInt 64 1 = (1 : BitVec 64) from rfl]

/-- `logBody op` consists only of `Cassgn` — it is straight-line. -/
theorem logBody_straightLine (op : SOp2) : InstrR.bodyIsStraightLine (logBody op) := by
  simp only [logBody, loadAt0, binOp, storeAt0, binImm, InstrR.bodyIsStraightLine,
             InstrR.isStraightLine, and_self]

/-- Every instruction of `logBody op` is non-control. -/
theorem logBody_nonControl (op : SOp2) : ∀ i ∈ logBody op, i.isNonControl := by
  intro i hi
  simp only [logBody, loadAt0, binOp, storeAt0, binImm, List.mem_cons,
             List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h <;> (subst h; exact True.intro)

/-- **Forward one-iteration rule for `logBody op`.**  The exact analogue of
    `Mpn.AddPrototype.bignumExecFuel_loop_step`, re-proved here because that
    lemma is hardcoded to `loopBody`.  It rests only on the *public*
    `BignumExec` primitives `bignumExecFuel_eq_bignumExec_of_straightLine`
    (logBody is straight-line) and `bignumExecFuel_append_join` (logBody is
    non-control). -/
theorem bignumExecFuel_logBody_step (op : SOp2) (reg : BignumRegistry) (f : Nat)
    (cond : PExpr) (s s_mid s' : BignumState)
    (hcond : evalPExpr s cond = some 1)
    (hbody : bignumExec (logBody op) s = some s_mid)
    (hrec : bignumExecFuel reg (f + 1) [.Cwhile [] cond (logBody op)] s_mid = some s') :
    bignumExecFuel reg (f + 3) [.Cwhile [] cond (logBody op)] s = some s' := by
  have hsl : bignumExecFuel reg (f + 1) (logBody op) s = some s_mid := by
    rw [bignumExecFuel_eq_bignumExec_of_straightLine reg f (logBody op) s
          (logBody_straightLine op)]
    exact hbody
  conv_lhs => rw [show f + 3 = (f + 2) + 1 from rfl, bignumExecFuel]
  simp only [List.nil_append, List.append_nil, bignumExecFuel, hcond, bne_iff_ne, ne_eq,
             show ((1 : BitVec 64) ≠ 0) from by decide, not_false_eq_true, if_true]
  rw [bignumExecFuel_append_join reg (f + 1) (logBody op) [.Cwhile [] cond (logBody op)]
        (logBody_nonControl op) s s_mid s' hsl hrec]

/-! ## §6  The loop, by induction on the limb list

The bitwise analogue of `Mpn.AddPrototype.mpnAddN_loop`: it threads the
`Cwhile` fuel rule (`bignumExecFuel_loop_step` / `_loop_exit`, reused from
`MpnAddPrototype`), peels one limb per iteration via
`bignumExec_logBody_step`, and frames the unread `ap`/`bp` suffixes across
the per-iteration `op[i]` store with `load64Mem_store64_disjoint` /
`memHoldsLimbs_store64_frame`.  No carry register is threaded.

We state it once over a generic `(op, ref)` pair where `ref` is the pure
reference, abstracting the per-limb head/tail equations as hypotheses, then
discharge those for each of the three concrete ops. -/

/-- Generic loop lemma, parametric over the op and its pure reference.
    Hypotheses `hop`, `href_nil`, and `href_cons` pin `ref` to the limb-wise
    `evalLimbOp op` reference; the body is then a straightforward induction
    reusing the `MpnAddPrototype` loop infrastructure. -/
theorem log_loop (op : SOp2) (ref : List (BitVec 64) → List (BitVec 64) → List (BitVec 64))
    (hop : op = .Oland .U64 ∨ op = .Olor .U64 ∨ op = .Olxor .U64)
    (href_nil : ∀ a b, a = [] ∨ b = [] → ref a b = [])
    (href_cons : ∀ a as b bs, ref (a :: as) (b :: bs) = evalLimbOp op a b :: ref as bs) :
    ∀ (as bs : List (BitVec 64)) (s : BignumState) (extra : Nat),
      as.length = bs.length →
      s.regs "n" = BitVec.ofNat 64 as.length →
      memHoldsLimbs s.mem (regAddr s "ap") as →
      memHoldsLimbs s.mem (regAddr s "bp") bs →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "ap") (8 * as.length)) →
      MemoryModel.Disjoint (range (regAddr s "op") (8 * as.length))
        (range (regAddr s "bp") (8 * as.length)) →
      ∃ s', bignumExecFuel emptyRegistry (2 * as.length + 3 + extra)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) (logBody op)] s
              = some s' ∧
        memHoldsLimbs s'.mem (regAddr s "op") (ref as bs) ∧
        (∀ b, MemoryModel.Disjoint (range b 8)
              (range (regAddr s "op") (8 * as.length)) →
            load64Mem s'.mem b = load64Mem s.mem b) := by
  intro as
  induction as with
  | nil =>
    intro bs s extra _ hn _ _ _ _
    have hn0 : s.regs "n" = 0 := by simpa using hn
    refine ⟨s, ?_, ?_, ?_⟩
    · have : 2 * ([] : List (BitVec 64)).length + 3 + extra = extra + 3 := by
        simp only [List.length_nil]; omega
      rw [this]
      exact bignumExecFuel_loop_exit emptyRegistry extra _ (logBody op) s
        (evalPExpr_logCond_false s hn0)
    · rw [href_nil [] bs (Or.inl rfl)]; exact True.intro
    · intro b _; rfl
  | cons a as ih =>
    intro bs s extra hlen hn hap hbp hdoa hdob
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hsize : 8 * (as.length + 1) < 2 ^ 64 := by
        simpa [List.length_cons] using
          disjoint_range_lt (regAddr s "op") (regAddr s "ap")
            (8 * (a :: as).length) (by simp only [List.length_cons]; omega)
            (by simpa using hdoa)
      have hLsucc : as.length + 1 < 2 ^ 64 := by omega
      have hn_ne : s.regs "n" ≠ 0 := by
        rw [hn]; simpa [List.length_cons] using ofNat64_succ_ne_zero as.length hLsucc
      obtain ⟨hap_head, hap_tail⟩ := hap
      obtain ⟨hbp_head, hbp_tail⟩ := hbp
      -- Run one iteration.
      obtain ⟨s1, hs1, hs1_mem, hs1_ap, hs1_bp, hs1_op, hs1_n⟩ :=
        bignumExec_logBody_step s op a b hop hap_head hbp_head
      set op0 : UInt64 := regAddr s "op" with hop0
      have hra_ap : regAddr s1 "ap" = regAddr s "ap" + 8 := by
        simp only [regAddr, hs1_ap]; exact regAddr_advance _
      have hra_bp : regAddr s1 "bp" = regAddr s "bp" + 8 := by
        simp only [regAddr, hs1_bp]; exact regAddr_advance _
      have hra_op : regAddr s1 "op" = op0 + 8 := by
        simp only [regAddr, hs1_op, hop0]; exact regAddr_advance _
      have hmem1 : s1.mem = s.mem.store64 op0 (UInt64.ofNat (evalLimbOp op a b).toNat) := by
        simpa [hop0, regAddr] using hs1_mem
      -- Frame the tails of `ap`/`bp` across the head store.
      have hdoa_store_aptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "ap" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob_store_bptail :
          MemoryModel.Disjoint (range op0 8) (range (regAddr s "bp" + 8) (8 * as.length)) := by
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_head_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hap1 : memHoldsLimbs s1.mem (regAddr s1 "ap") as := by
        rw [hra_ap, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "ap" + 8) op0 _ as
          hdoa_store_aptail hap_tail
      have hbp1 : memHoldsLimbs s1.mem (regAddr s1 "bp") bs := by
        rw [hra_bp, hmem1]
        exact memHoldsLimbs_store64_frame s.mem (regAddr s "bp" + 8) op0 _ bs
          (by rw [hlen'] at hdob_store_bptail; exact hdob_store_bptail) hbp_tail
      have hdoa1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "ap") (8 * as.length)) := by
        rw [hra_op, hra_ap]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdoa
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "ap") as.length x
            (by simpa [List.length_cons] using h)
      have hdob1 : MemoryModel.Disjoint (range (regAddr s1 "op") (8 * as.length))
          (range (regAddr s1 "bp") (8 * as.length)) := by
        rw [hra_op, hra_bp]
        refine disjoint_mono (fun x h => ?_) (fun x h => ?_) hdob
        · exact range_shift_subset op0 as.length x (by simpa [List.length_cons] using h)
        · exact range_shift_subset (regAddr s "bp") as.length x
            (by simpa [List.length_cons] using h)
      have hn1 : s1.regs "n" = BitVec.ofNat 64 as.length := by
        rw [hs1_n, hn]
        simpa [List.length_cons] using ofNat64_succ_sub_one as.length hLsucc
      -- Apply the IH on the tail.
      obtain ⟨s', hs', hs'_mem, hs'_frame⟩ :=
        ih bs s1 extra hlen' hn1 hap1 hbp1 hdoa1 hdob1
      refine ⟨s', ?_, ?_, ?_⟩
      · have hfuel : 2 * (a :: as).length + 3 + extra
            = (2 * as.length + 2 + extra) + 3 := by
          simp only [List.length_cons]; ring
        rw [hfuel]
        refine bignumExecFuel_logBody_step op emptyRegistry (2 * as.length + 2 + extra) _ s s1 s'
          (evalPExpr_logCond_true s hn_ne) hs1 ?_
        simpa [show 2 * as.length + 2 + extra + 1 = 2 * as.length + 3 + extra
                from by omega] using hs'
      · rw [hmem1] at hs'_frame
        have hsep : MemoryModel.Disjoint (range op0 8) (range (op0 + 8) (8 * as.length)) :=
          range_op_head_tail_disjoint op0 as.length (by omega)
        rw [href_cons a as b bs]
        refine ⟨?_, ?_⟩
        · rw [hs'_frame op0 (by rw [hra_op]; exact hsep)]
          have hread := load64Mem_store64_same s.mem op0 (UInt64.ofNat (evalLimbOp op a b).toNat)
          rw [hread]
        · have hthis := hs'_mem
          rw [hra_op] at hthis
          exact hthis
      · intro bb hbb
        rw [hmem1] at hs'_frame
        have hbb_tail : MemoryModel.Disjoint (range bb 8)
            (range (regAddr s1 "op") (8 * as.length)) := by
          rw [hra_op]
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_shift_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [hs'_frame bb hbb_tail]
        have hbb_head : MemoryModel.Disjoint (range bb 8) (range (regAddr s "op") 8) := by
          refine disjoint_mono (fun x h => h) (fun x h => ?_) hbb
          exact range_head_subset (regAddr s "op") as.length x
            (by simpa [List.length_cons] using h)
        rw [load64Mem_store64_disjoint s.mem bb (regAddr s "op") _ hbb_head]

/-! ## §7  Bridge statements + assembly

The bridge says: starting from a state whose memory holds `as` at `ap`,
`bs` at `bp`, with `n = |as|`, running the kernel body lands in a state
whose memory at `op` holds the limb-wise reference.  The `op`-vs-`ap` and
`op`-vs-`bp` `Disjoint` hypotheses keep the per-iteration store from
clobbering unread source limbs (both inputs are read every iteration, as in
add_n).  The body here *is* the loop (no carry prelude), so the bridge is
`log_loop` instantiated for each op (with `extra = fuel - (2|as|+3)`). -/

/-- Shared bridge-statement shape for a bitwise kernel body `bdy` against
    reference `ref`. -/
def LogRefinesStmt (bdy : List InstrR) (ref : List (BitVec 64) → List (BitVec 64) → List (BitVec 64)) : Prop :=
  ∀ (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat),
    as.length = bs.length →
    s.regs "n" = BitVec.ofNat 64 as.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)) →
    fuel > 2 * as.length + 2 →
    ∃ s', bignumExecFuel emptyRegistry fuel bdy s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (ref as bs)

/-- Generic bridge assembly: `log_loop` packaged into `LogRefinesStmt`. -/
theorem log_refines (op : SOp2) (ref : List (BitVec 64) → List (BitVec 64) → List (BitVec 64))
    (hop : op = .Oland .U64 ∨ op = .Olor .U64 ∨ op = .Olxor .U64)
    (href_nil : ∀ a b, a = [] ∨ b = [] → ref a b = [])
    (href_cons : ∀ a as b bs, ref (a :: as) (b :: bs) = evalLimbOp op a b :: ref as bs) :
    LogRefinesStmt (logFullBody op) ref := by
  intro s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, _⟩ :=
    log_loop op ref hop href_nil href_cons as bs s extra hlen hn hap hbp hdoa hdob
  refine ⟨s', ?_, ?_⟩
  · rw [hextra]; simpa [logFullBody, regAddr] using hs'
  · simpa [regAddr] using hs'_mem

/-! ### Per-op reference equations -/

theorem mpnAnd_nil (a b : List (BitVec 64)) (h : a = [] ∨ b = []) : mpnAnd a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

theorem mpnIor_nil (a b : List (BitVec 64)) (h : a = [] ∨ b = []) : mpnIor a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

theorem mpnXor_nil (a b : List (BitVec 64)) (h : a = [] ∨ b = []) : mpnXor a b = [] := by
  rcases h with h | h
  · subst h; rfl
  · subst h; cases a <;> rfl

theorem mpnAnd_cons (a : BitVec 64) (as : List (BitVec 64)) (b : BitVec 64)
    (bs : List (BitVec 64)) :
    mpnAnd (a :: as) (b :: bs) = evalLimbOp (.Oland .U64) a b :: mpnAnd as bs := rfl

theorem mpnIor_cons (a : BitVec 64) (as : List (BitVec 64)) (b : BitVec 64)
    (bs : List (BitVec 64)) :
    mpnIor (a :: as) (b :: bs) = evalLimbOp (.Olor .U64) a b :: mpnIor as bs := rfl

theorem mpnXor_cons (a : BitVec 64) (as : List (BitVec 64)) (b : BitVec 64)
    (bs : List (BitVec 64)) :
    mpnXor (a :: as) (b :: bs) = evalLimbOp (.Olxor .U64) a b :: mpnXor as bs := rfl

/-! ### The three concrete bridges -/

/-- **`mpn_and_n` bridge, fully proved.**  The emitted
    `while (n != 0) { t = [ap]; s = [bp]; r = t & s; [op] = r; … }` refines
    the limb-wise `BitVec.and` reference `mpnAnd` over byte memory.  Combined
    with `mpnAnd_spec`, the memory at `op` denotes `toNat as &&& toNat bs`. -/
theorem MpnAndJasminRefines : LogRefinesStmt (logFullBody (.Oland .U64)) mpnAnd :=
  log_refines (.Oland .U64) mpnAnd (Or.inl rfl) mpnAnd_nil mpnAnd_cons

/-- **`mpn_ior_n` bridge, fully proved.** -/
theorem MpnIorJasminRefines : LogRefinesStmt (logFullBody (.Olor .U64)) mpnIor :=
  log_refines (.Olor .U64) mpnIor (Or.inr (Or.inl rfl)) mpnIor_nil mpnIor_cons

/-- **`mpn_xor_n` bridge, fully proved.** -/
theorem MpnXorJasminRefines : LogRefinesStmt (logFullBody (.Olxor .U64)) mpnXor :=
  log_refines (.Olxor .U64) mpnXor (Or.inr (Or.inr rfl)) mpnXor_nil mpnXor_cons

/-! ## §8  Corollaries: the bridge memory denotes the `Nat` bit op

Combining the bridge (`Mpn*JasminRefines`) with the functional spec
(`mpn*_spec`) gives the end-to-end statement: after the emitted loop, the
memory at `op` holds a limb list whose denotation is the `Nat` bitwise op of
the two input denotations. -/

/-- End-to-end for `mpn_and_n`: the output memory denotes `toNat as &&& toNat bs`. -/
theorem MpnAndJasminRefines_toNat
    (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat)
    (hlen : as.length = bs.length)
    (hn : s.regs "n" = BitVec.ofNat 64 as.length)
    (hap : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as)
    (hbp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)))
    (hdob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)))
    (hfuel : fuel > 2 * as.length + 2) :
    ∃ s', bignumExecFuel emptyRegistry fuel (logFullBody (.Oland .U64)) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAnd as bs) ∧
      toNat (mpnAnd as bs) = toNat as &&& toNat bs := by
  obtain ⟨s', hs', hmem⟩ :=
    MpnAndJasminRefines s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  exact ⟨s', hs', hmem, mpnAnd_spec as bs hlen⟩

/-- End-to-end for `mpn_ior_n`. -/
theorem MpnIorJasminRefines_toNat
    (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat)
    (hlen : as.length = bs.length)
    (hn : s.regs "n" = BitVec.ofNat 64 as.length)
    (hap : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as)
    (hbp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)))
    (hdob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)))
    (hfuel : fuel > 2 * as.length + 2) :
    ∃ s', bignumExecFuel emptyRegistry fuel (logFullBody (.Olor .U64)) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnIor as bs) ∧
      toNat (mpnIor as bs) = toNat as ||| toNat bs := by
  obtain ⟨s', hs', hmem⟩ :=
    MpnIorJasminRefines s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  exact ⟨s', hs', hmem, mpnIor_spec as bs hlen⟩

/-- End-to-end for `mpn_xor_n`. -/
theorem MpnXorJasminRefines_toNat
    (s : BignumState) (as bs : List (BitVec 64)) (fuel : Nat)
    (hlen : as.length = bs.length)
    (hn : s.regs "n" = BitVec.ofNat 64 as.length)
    (hap : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as)
    (hbp : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) bs)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * as.length)))
    (hdob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * as.length)))
    (hfuel : fuel > 2 * as.length + 2) :
    ∃ s', bignumExecFuel emptyRegistry fuel (logFullBody (.Olxor .U64)) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnXor as bs) ∧
      toNat (mpnXor as bs) = toNat as ^^^ toNat bs := by
  obtain ⟨s', hs', hmem⟩ :=
    MpnXorJasminRefines s as bs fuel hlen hn hap hbp hdoa hdob hfuel
  exact ⟨s', hs', hmem, mpnXor_spec as bs hlen⟩

end CatCrypt.Crypto.Jasmin.Mpn.LogicalPrototype
