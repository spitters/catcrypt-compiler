/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# C4 fan-out: the verified compiler emits the Ascon permutation round from extracted source

This module extends the **C4** step of the verified-compiler plan to a **fourth**
primitive family: **Ascon** (NIST SP 800-232 / Ascon v1.2 lightweight AEAD). The
earlier C4 leaves drove `compileFromHax` *emitting* a crypto leaf from
hax-extracted source for SHA-256 (`CompileFromHaxLeaves`, the big and small sigma
plus majority leaves), Keccak χ (`CompileFromHaxKeccak`), and BLAKE2s ARX
(`CompileFromHaxBlake2`). Here we do the same for the **Ascon permutation round**,
whose state-update is pure bit-ops over five 64-bit lanes `x0 … x4`:

* **round-constant add** — XOR a fixed `u64` round constant into `x2`;
* **substitution layer** — the bit-sliced χ-style 5-bit S-box: a chain of
  `xor` / `and` / bit-`not` over the five lanes (the canonical Ascon reference
  S-box, `~` recognised by the verified front's `Not`/`BitNot` head);
* **linear diffusion** — per-lane `xi ^= rotr(xi, r1) ^ rotr(xi, r2)` with the
  Ascon rotation pairs `{(19,28),(61,39),(1,6),(10,17),(7,41)}`.

Each of the **five output lanes** `x0' … x4'` is derived as a single-output leaf
(`w = 64`, `nIn = 5`): `compileFromHax src = some c ∧ c.denote = <closed form>`,
routed through the C3 per-primitive obligation `compileFromHax_meets_spec`. No
front change is required — every head (`wrapping_add` is unused here; `BitXor`,
`BitAnd`, `Not`, `rotate_right`) is already recognised by `recogBin`/`recogShift`/
`recogNot`. The round-constant is the round-6 (Ascon-128 `p^b` first round)
value `0x96 = 150`, mirroring `AsconEmit.roundConst 6`.

## The canonical Ascon S-box (NIST SP 800-232, reference `round.h`)

On the lanes `(x0, x1, x2c, x3, x4)` where `x2c = x2 ⊕ RC`:

```
a0 = x0 ^ x4;  a4 = x4 ^ x3;  a2 = x2c ^ x1;   (a1 = x1, a3 = x3)
t0 = ~a0 & a1; t1 = ~a1 & a2; t2 = ~a2 & a3; t3 = ~a3 & a4; t4 = ~a4 & a0;
b0 = a0 ^ t1;  b1 = a1 ^ t2;  b2 = a2 ^ t3;  b3 = a3 ^ t4;  b4 = a4 ^ t0;
c1 = b1 ^ b0;  c0 = b0 ^ b4;  c3 = b3 ^ b2;  c2 = ~b2;       c4 = b4;
```

then the linear layer `xi' = ci ^ rotr(ci, r1_i) ^ rotr(ci, r2_i)`.

## Method (mirrors `CompileFromHaxBlake2.blake2G_compiles`)

Each lane's source is a fully let-normalized `ImpExpr` (one operator per
`letBind`, all arguments atoms or earlier locals); `*_src_denoteScalar = spec`
closes by `rfl`; `*_isSome` by `native_decide`; `*_compiles` routes the
source-spec through `compileFromHax_meets_spec`. The five-input valuation is
`![x0, x1, x2, x3, x4]`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxAscon

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect)

/-! ## §0  The round constant and the shared S-box closed form

The round constant is the Ascon-128 `p^b` first round value (`AsconEmit.roundConst 6`).
The S-box and linear-layer closed forms are stated once as plain `def`s so the
five per-lane specs are explicit and auditable. -/

/-- The round-6 Ascon round constant `0x96 = 150` (mirrors `AsconEmit.roundConst 6`). -/
abbrev RC : BitVec 64 := BitVec.ofNat 64 150

/-- The width-64 all-ones mask. Bitwise complement is `x ^^^ ONES = ~~~x`
    (`BitVec.xor_allOnes`, since `ONES = BitVec.allOnes 64`); the spec is written
    in the XOR-all-ones form the desugared `Not` produces, so the source
    denotation matches definitionally. -/
abbrev ONES : BitVec 64 := BitVec.ofNat 64 18446744073709551615

/-- The post-S-box lane `c0 … c4` closed forms on the round-entry lanes
    `(x0, x1, x2, x3, x4)`, with the round constant XORed into `x2` first. This is
    the canonical NIST SP 800-232 reference S-box. Bitwise complement is written
    `· ^^^ ONES` (= `~~~·`, `BitVec.xor_allOnes`). -/
def sboxC (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let x2c := x2 ^^^ RC
  let a0 := x0 ^^^ x4
  let a1 := x1
  let a2 := x2c ^^^ x1
  let a3 := x3
  let a4 := x4 ^^^ x3
  let t0 := (a0 ^^^ ONES) &&& a1
  let t1 := (a1 ^^^ ONES) &&& a2
  let t2 := (a2 ^^^ ONES) &&& a3
  let t3 := (a3 ^^^ ONES) &&& a4
  let t4 := (a4 ^^^ ONES) &&& a0
  let b0 := a0 ^^^ t1
  let b1 := a1 ^^^ t2
  let b2 := a2 ^^^ t3
  let b3 := a3 ^^^ t4
  let b4 := a4 ^^^ t0
  let c0 := b0 ^^^ b4
  let c1 := b1 ^^^ b0
  let c2 := b2 ^^^ ONES
  let c3 := b3 ^^^ b2
  let c4 := b4
  (c0, c1, c2, c3, c4)

/-- The bit-complement equation `x ^^^ ONES = ~~~x` at width 64, making the
    `· ^^^ ONES` form in `sboxC` the genuine bitwise NOT of the canonical S-box. -/
theorem xor_ONES (x : BitVec 64) : x ^^^ ONES = ~~~x := by
  rw [show ONES = BitVec.allOnes 64 from by native_decide, BitVec.xor_allOnes]

/-- The linear-diffusion mix `c ^ rotr(c, r1) ^ rotr(c, r2)`. -/
def lin (c : BitVec 64) (r1 r2 : Nat) : BitVec 64 :=
  c ^^^ c.rotateRight r1 ^^^ c.rotateRight r2

/-- Output lane `x0'`. -/
def asconLane0Spec (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 :=
  lin (sboxC x0 x1 x2 x3 x4).1 19 28

/-- Output lane `x1'`. -/
def asconLane1Spec (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 :=
  lin (sboxC x0 x1 x2 x3 x4).2.1 61 39

/-- Output lane `x2'`. -/
def asconLane2Spec (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 :=
  lin (sboxC x0 x1 x2 x3 x4).2.2.1 1 6

/-- Output lane `x3'`. -/
def asconLane3Spec (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 :=
  lin (sboxC x0 x1 x2 x3 x4).2.2.2.1 10 17

/-- Output lane `x4'`. -/
def asconLane4Spec (x0 x1 x2 x3 x4 : BitVec 64) : BitVec 64 :=
  lin (sboxC x0 x1 x2 x3 x4).2.2.2.2 7 41

/-! ## §1  The shared let-normalized S-box prefix

The S-box body computes `c0 … c4` from the five lane parameters; each lane's
source threads this prefix and finishes with its own two-rotate-XOR linear mix.
We factor the prefix as a continuation-taking `ImpExpr` builder so the five
sources share it verbatim. Parameters are `["x0","x1","x2","x3","x4"]`
(`nIn = 5`). -/

/-- The S-box prefix as a let-normalized `ImpExpr`, binding `c0 … c4`, then
    continuing with `cont` (which reads whichever `cI` the lane needs). -/
def sboxPrefix (cont : ImpExpr) : ImpExpr :=
  -- ones = 0xFFFFFFFFFFFFFFFF (the width-64 all-ones literal materialised into a
  -- register; bit-`not` is desugared as `x ^ ones`, which the translator's BitXor
  -- recogniser accepts — there is no standalone `Not` RHS in the front).
  .letBind "ones" (.lit (.int 18446744073709551615))
  -- rc = 0x96 = 150 (round-6 constant), materialised into a register so it can be
  -- a BitXor operand (the front rejects a bare literal as a binary-op operand).
  (.letBind "rc" (.lit (.int 150))
  -- x2c = x2 ^ RC
  (.letBind "x2c" (.app "BitXor" [.var "x2", .var "rc"])
  -- a0 = x0 ^ x4;  a2 = x2c ^ x1;  a4 = x4 ^ x3   (a1 = x1, a3 = x3 reuse params)
  (.letBind "a0" (.app "BitXor" [.var "x0", .var "x4"])
  (.letBind "a2" (.app "BitXor" [.var "x2c", .var "x1"])
  (.letBind "a4" (.app "BitXor" [.var "x4", .var "x3"])
  -- t0 = ~a0 & x1
  (.letBind "n0" (.app "BitXor" [.var "a0", .var "ones"])
  (.letBind "t0" (.app "BitAnd" [.var "n0", .var "x1"])
  -- t1 = ~x1 & a2
  (.letBind "n1" (.app "BitXor" [.var "x1", .var "ones"])
  (.letBind "t1" (.app "BitAnd" [.var "n1", .var "a2"])
  -- t2 = ~a2 & x3
  (.letBind "n2" (.app "BitXor" [.var "a2", .var "ones"])
  (.letBind "t2" (.app "BitAnd" [.var "n2", .var "x3"])
  -- t3 = ~x3 & a4
  (.letBind "n3" (.app "BitXor" [.var "x3", .var "ones"])
  (.letBind "t3" (.app "BitAnd" [.var "n3", .var "a4"])
  -- t4 = ~a4 & a0
  (.letBind "n4" (.app "BitXor" [.var "a4", .var "ones"])
  (.letBind "t4" (.app "BitAnd" [.var "n4", .var "a0"])
  -- b0 = a0 ^ t1;  b1 = x1 ^ t2;  b2 = a2 ^ t3;  b3 = x3 ^ t4;  b4 = a4 ^ t0
  (.letBind "b0" (.app "BitXor" [.var "a0", .var "t1"])
  (.letBind "b1" (.app "BitXor" [.var "x1", .var "t2"])
  (.letBind "b2" (.app "BitXor" [.var "a2", .var "t3"])
  (.letBind "b3" (.app "BitXor" [.var "x3", .var "t4"])
  (.letBind "b4" (.app "BitXor" [.var "a4", .var "t0"])
  -- c0 = b0 ^ b4;  c1 = b1 ^ b0;  c2 = ~b2;  c3 = b3 ^ b2;  c4 = b4
  (.letBind "c0" (.app "BitXor" [.var "b0", .var "b4"])
  (.letBind "c1" (.app "BitXor" [.var "b1", .var "b0"])
  (.letBind "c2" (.app "BitXor" [.var "b2", .var "ones"])
  (.letBind "c3" (.app "BitXor" [.var "b3", .var "b2"])
   cont))))))))))))))))))))))))

/-- The linear-mix tail for a lane: read local `cName`, rotate by `r1`/`r2`, XOR
    all three, return. -/
def linTail (cName : String) (r1 r2 : Nat) : ImpExpr :=
  .letBind "s1" (.app "rotate_right" [.var cName, .lit (.int r1)])
  (.letBind "s2" (.app "rotate_right" [.var cName, .lit (.int r2)])
  (.letBind "m1" (.app "BitXor" [.var cName, .var "s1"])
  (.letBind "out" (.app "BitXor" [.var "m1", .var "s2"])
   (.var "out"))))

/-! ## §2  The five lane sources -/

/-- Source for output lane `x0'` (`c0`, rotates `(19, 28)`). -/
def asconLane0Src : ImpExpr := sboxPrefix (linTail "c0" 19 28)
/-- Source for output lane `x1'` (`c1`, rotates `(61, 39)`). -/
def asconLane1Src : ImpExpr := sboxPrefix (linTail "c1" 61 39)
/-- Source for output lane `x2'` (`c2`, rotates `(1, 6)`). -/
def asconLane2Src : ImpExpr := sboxPrefix (linTail "c2" 1 6)
/-- Source for output lane `x3'` (`c3`, rotates `(10, 17)`). -/
def asconLane3Src : ImpExpr := sboxPrefix (linTail "c3" 10 17)
/-- Source for output lane `x4'` (`c4 = b4`, rotates `(7, 41)`). -/
def asconLane4Src : ImpExpr := sboxPrefix (linTail "b4" 7 41)

/-- The parameter list shared by all five lanes. -/
abbrev asconParams : List String := ["x0", "x1", "x2", "x3", "x4"]

/-! ## §3  Source-spec agreement (each lane's source denotes to its closed form) -/

/- The source for lane `x0'` denotes (under `denoteScalar`, parameters
   `asconParams`) to its closed form. The let-normalized body and `sboxC`/`lin`
   both reduce definitionally — the `· ^^^ ONES` complement form in `sboxC`
   matches the desugared `BitXor[·, ones]` the source emits — so the source-spec
   is `rfl` (the deep S-box tree needs the raised heartbeat budget). -/
set_option maxHeartbeats 4000000 in
theorem asconLane0Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar asconParams I asconLane0Src (fun _ => none)
      = some (asconLane0Spec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3) (inpGet I 4)) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem asconLane1Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar asconParams I asconLane1Src (fun _ => none)
      = some (asconLane1Spec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3) (inpGet I 4)) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem asconLane2Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar asconParams I asconLane2Src (fun _ => none)
      = some (asconLane2Spec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3) (inpGet I 4)) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem asconLane3Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar asconParams I asconLane3Src (fun _ => none)
      = some (asconLane3Spec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3) (inpGet I 4)) := by
  rfl

set_option maxHeartbeats 4000000 in
theorem asconLane4Src_denoteScalar {nIn : Nat} (I : Fin nIn → BitVec 64) :
    ImpExpr.denoteScalar asconParams I asconLane4Src (fun _ => none)
      = some (asconLane4Spec (inpGet I 0) (inpGet I 1) (inpGet I 2) (inpGet I 3) (inpGet I 4)) := by
  rfl

/-! ## §4  Compilation succeeds (`native_decide`) -/

theorem asconLane0_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) asconParams asconLane0Src).isSome := by native_decide
theorem asconLane1_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) asconParams asconLane1Src).isSome := by native_decide
theorem asconLane2_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) asconParams asconLane2Src).isSome := by native_decide
theorem asconLane3_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) asconParams asconLane3Src).isSome := by native_decide
theorem asconLane4_compileFromHax_isSome :
    (compileFromHax (w := 64) (nIn := 5) asconParams asconLane4Src).isSome := by native_decide

/-! ## §5  The five lanes emitted by the verified compiler -/

/-- **Ascon round output lane `x0'` emitted by the verified compiler.** Routed
    through the C3 per-primitive obligation `compileFromHax_meets_spec`. -/
theorem asconLane0_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) asconParams asconLane0Src = some prog ∧
      ∀ (x0 x1 x2 x3 x4 : BitVec 64),
        prog.denote (inputValuation 64 5 ![x0, x1, x2, x3, x4])
          = asconLane0Spec x0 x1 x2 x3 x4 := by
  set prog := (compileFromHax (w := 64) (nIn := 5) asconParams asconLane0Src).get
    asconLane0_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 5) asconParams asconLane0Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x0 x1 x2 x3 x4
  have hspec : ImpExpr.denoteScalar asconParams ![x0, x1, x2, x3, x4]
      asconLane0Src (fun _ => none) = some (asconLane0Spec x0 x1 x2 x3 x4) := by
    have h := asconLane0Src_denoteScalar (nIn := 5) ![x0, x1, x2, x3, x4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) asconParams
    ![x0, x1, x2, x3, x4] asconLane0Src _ hc hspec

/-- **Ascon round output lane `x1'` emitted by the verified compiler.** -/
theorem asconLane1_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) asconParams asconLane1Src = some prog ∧
      ∀ (x0 x1 x2 x3 x4 : BitVec 64),
        prog.denote (inputValuation 64 5 ![x0, x1, x2, x3, x4])
          = asconLane1Spec x0 x1 x2 x3 x4 := by
  set prog := (compileFromHax (w := 64) (nIn := 5) asconParams asconLane1Src).get
    asconLane1_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 5) asconParams asconLane1Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x0 x1 x2 x3 x4
  have hspec : ImpExpr.denoteScalar asconParams ![x0, x1, x2, x3, x4]
      asconLane1Src (fun _ => none) = some (asconLane1Spec x0 x1 x2 x3 x4) := by
    have h := asconLane1Src_denoteScalar (nIn := 5) ![x0, x1, x2, x3, x4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) asconParams
    ![x0, x1, x2, x3, x4] asconLane1Src _ hc hspec

/-- **Ascon round output lane `x2'` emitted by the verified compiler.** -/
theorem asconLane2_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) asconParams asconLane2Src = some prog ∧
      ∀ (x0 x1 x2 x3 x4 : BitVec 64),
        prog.denote (inputValuation 64 5 ![x0, x1, x2, x3, x4])
          = asconLane2Spec x0 x1 x2 x3 x4 := by
  set prog := (compileFromHax (w := 64) (nIn := 5) asconParams asconLane2Src).get
    asconLane2_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 5) asconParams asconLane2Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x0 x1 x2 x3 x4
  have hspec : ImpExpr.denoteScalar asconParams ![x0, x1, x2, x3, x4]
      asconLane2Src (fun _ => none) = some (asconLane2Spec x0 x1 x2 x3 x4) := by
    have h := asconLane2Src_denoteScalar (nIn := 5) ![x0, x1, x2, x3, x4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) asconParams
    ![x0, x1, x2, x3, x4] asconLane2Src _ hc hspec

/-- **Ascon round output lane `x3'` emitted by the verified compiler.** -/
theorem asconLane3_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) asconParams asconLane3Src = some prog ∧
      ∀ (x0 x1 x2 x3 x4 : BitVec 64),
        prog.denote (inputValuation 64 5 ![x0, x1, x2, x3, x4])
          = asconLane3Spec x0 x1 x2 x3 x4 := by
  set prog := (compileFromHax (w := 64) (nIn := 5) asconParams asconLane3Src).get
    asconLane3_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 5) asconParams asconLane3Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x0 x1 x2 x3 x4
  have hspec : ImpExpr.denoteScalar asconParams ![x0, x1, x2, x3, x4]
      asconLane3Src (fun _ => none) = some (asconLane3Spec x0 x1 x2 x3 x4) := by
    have h := asconLane3Src_denoteScalar (nIn := 5) ![x0, x1, x2, x3, x4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) asconParams
    ![x0, x1, x2, x3, x4] asconLane3Src _ hc hspec

/-- **Ascon round output lane `x4'` emitted by the verified compiler.** -/
theorem asconLane4_compiles :
    ∃ (prog : Com jasminDialect (frontCtxt 64 5 []) (rW 64)),
      compileFromHax (w := 64) (nIn := 5) asconParams asconLane4Src = some prog ∧
      ∀ (x0 x1 x2 x3 x4 : BitVec 64),
        prog.denote (inputValuation 64 5 ![x0, x1, x2, x3, x4])
          = asconLane4Spec x0 x1 x2 x3 x4 := by
  set prog := (compileFromHax (w := 64) (nIn := 5) asconParams asconLane4Src).get
    asconLane4_compileFromHax_isSome with hprog_def
  have hc : compileFromHax (w := 64) (nIn := 5) asconParams asconLane4Src = some prog :=
    (Option.some_get _).symm
  refine ⟨prog, hc, ?_⟩
  intro x0 x1 x2 x3 x4
  have hspec : ImpExpr.denoteScalar asconParams ![x0, x1, x2, x3, x4]
      asconLane4Src (fun _ => none) = some (asconLane4Spec x0 x1 x2 x3 x4) := by
    have h := asconLane4Src_denoteScalar (nIn := 5) ![x0, x1, x2, x3, x4]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using h
  exact compileFromHax_meets_spec (w := 64) (nIn := 5) asconParams
    ![x0, x1, x2, x3, x4] asconLane4Src _ hc hspec

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxAscon
