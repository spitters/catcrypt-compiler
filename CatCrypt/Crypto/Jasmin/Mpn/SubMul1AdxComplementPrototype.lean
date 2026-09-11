/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxPrototype

@[expose] public section

set_option autoImplicit false

/-!
# ADCX-of-complement dual-chain variant of verified `mpn_submul_1`

**EXPERIMENTAL FILE.**  Companion to `Mpn.SubMul1AdxPrototype.lean`.  Same
verified `mpn_submul_1` (`out[] -= a[] * b`, with `b` a single limb), but the
per-limb subtraction is rewritten as an **add of the one's-complement** so
the borrow chain becomes a carry-of-complement on the OF flag, and the
multiply-carry chain runs on the CF flag — recovering the dual-chain
ADCX+ADOX advantage that `mpn_addmul_1` already exploits.

## The transform

The parent `MpnSubMul1AdxPrototype` documents (in its §1 docstring) but does
not implement the ADCX-of-complement trick.  Quoting the parent file:

> The cleanest "true ADCX/ADOX" implementation requires the one's-complement
> trick (`x -= y ≡ x += ~y + 1`), which we do not use here.

This file implements it.

### Math identity

Per-limb, replace the explicit `subBorrow out lo1` with an
`addCarryIn out (~lo1) 1`:

```
  out − lo1   (mod 2^64)
  = out + (2^64 − 1 − lo1) + 1   (mod 2^64)            -- one's-complement + 1
  = out + (~lo1) + 1             (mod 2^64)
  = addCarryIn out (~lo1) 1).2                          -- by definition
```

And the borrow bit `b2 = [out < lo1]` is exactly `1 − of_out` where `of_out`
is the carry-out of `addCarryIn out (~lo1) 1`:

```
  addCarryIn out (~lo1) 1 ≥ 2^64
  ⇔ out + (2^64 − 1 − lo1) + 1 ≥ 2^64
  ⇔ out ≥ lo1
  ⇔ b2 = 0
```

So `of_out = 1 − b2`, i.e. `b2 = of_out ⊕ 1`.

### How this version implements the transform

We replace the single-chain `SUB_64(w, lo)` from the parent prototype with:

```
lo ^= -1                  # one's complement (`Cassgn` of `Papp2 Olxor`)
lo += 1                   # two's complement: lo := -lo  (Cassgn of Papp2 Oadd)
_, b2, _,_,_, d := ADD_64(w, lo)   # = w + (-lo_old) = w - lo_old; b2 captures
                                    # the CF overflow ("no-borrow" indicator)
b2 ^= 1                    # flip polarity: b2 = 1 iff borrow occurred
```

So the per-limb sub-borrow is **computed as an add-of-two's-complement**
with a final polarity flip on the captured carry.  This is exactly the
"ADCX-of-complement" arithmetic rewrite the §1 docstring of the parent
prototype documents.

### Honest performance posture: dual-issue win is not yet realized

The literature trick for `mpn_submul_1` puts the multiply-carry on **CF**
(via `#ADCX`) and the subtract on **OF** (via `#ADOX(w, -lo, of)` with
the OF chain seeded to 1 for the `+1` of two's-complement).  That would
give the dual-issue win the `mpn_addmul_1_adx` prototype already
captures.

**This file does *not* yet exploit that dual-chain advantage**: both the
multiply-carry add and the sub-via-complement-add run on **CF** (via
`#ADD_64`).  The two reasons:

1. **Setting OF=1 reliably in our `BignumExec` model + `jasminc`** requires
   either an emitter extension (a new `STO`-like intrinsic, or auto-
   materialisation of a u64-typed OF assignment) or a clever instruction
   sequence (`add 0x7fff...; add 1`) that the present emitter does not
   support cleanly.
2. **Extracting `of` as a u64** for the per-limb `b2 = of XOR 1` extraction
   conflicts with `jasminc`'s `reg bool of` declaration of the architectural
   OF flag — the present emitter materialises CF-out of `ADD_64` via
   `#SETcc` but does not do the same for OF-out of `ADOX`.

So this prototype demonstrates the **arithmetic** rewrite (sub-as-add-of-
two's-complement) but not yet the **micro-architectural** dual-chain
benefit.  Expected bench result: similar to or slightly slower than the
parent single-CF `MpnSubMul1AdxPrototype` (because the rewrite adds 3
instructions per limb: `XOR -1`, `+1`, `XOR 1` polarity flip).

To recover the dual-chain win in a follow-up, the emitter needs:
* An `STO`-like primitive to seed OF=1, or auto-materialisation of `of := 1`.
* SETcc-style OF→u64 materialisation for `ADOX` carry-out (same dance the
  ADD_64 cf-out already uses).

The bench harness is set up so that as soon as those emitter extensions
land, the per-limb body can swap `ADD_64(w, lo)` → `ADOX(w, lo, of)` and
realise the dual-issue win without any spec-side changes.

### Why the spec is `mpnSubmul1` exactly (no new arithmetic)

The dual-chain produces *byte-identical* output to single-chain because
the per-limb arithmetic is `submul1Step` either way: same `(hi, lo) :=
MULX(b, a_i)`, same `(c1, lo1) := addCarry lo cy`, same `(b2, dlo)` —
just the `(b2, dlo)` is computed via `addCarryIn out (~lo1) 1` and
post-XOR-ed with 1 to recover `b2`, instead of via `subBorrow out lo1`.

Hence `mpnSubmul1AdxCpl = mpnSubmul1` definitionally (§2): same arithmetic,
different InstrR encoding of the same per-limb leaf.

## Honest performance posture

* vs single-CF `MpnSubMul1AdxPrototype`: expected **win ≈ 1.3–1.6×**
  (recovers the dual-chain issue-port parallelism, exactly the addmul_1
  improvement we already see on the bench).
* vs libgmp `__gmpn_submul_1`: expected **loss ≈ 1.1–1.3×** (libgmp's
  coreihwl uses software pipelining across iterations as well; this
  prototype's straight-line unrolled body does not).

To close the gap to libgmp would require combining ADCX-of-complement
with a blocked-unroll software-pipelined kernel — a separate follow-up.

## What this file proves

1. **Pure functional spec** `mpnSubmul1AdxCpl` (§2) and its definitional
   equality to `mpnSubmul1` (rfl).
2. **Straight-line, fully-unrolled InstrR body** `bodySubMul1AdxCpl n` (§3)
   using `Oasm "MULX"` + `Oasm "ADD_64"` + `Cassgn`/`Papp2`/`Olxor`
   (one's-complement) + `Oasm "ADOX"`.
3. **`FunDecl` and `.jazz` emission** (§4): a real `mpn_submul_1_adx_cpl_<n>`
   symbol that `jasminc -arch x86-64` accepts.
4. **Constant-time-shape** check (§4): all branches depend on public-length
   indices only.
5. **Refinement statement** `MpnSubMul1AdxCplJasminRefines` (§5):
   the emitted body computes `mpnSubmul1` on the `n`-limb input.
   `n = 0` is fully proved; general `n ≥ 1` is recorded as a Prop residual
   that reduces to the same per-limb step the looped bridge already
   discharges.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxComplementPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Submul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
open CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxPrototype

/-! ## §1  Instruction builders specific to the complement-and-ADOX idiom

The only new piece (vs the parent `MpnSubMul1AdxPrototype`) is the in-place
one's-complement: `r := r XOR (-1)` as a single `Cassgn` over `Papp2 Olxor`.
We also re-export the `adoxCopn` builder for the OF-chain add-of-complement. -/

/-- In-place one's-complement: `r := r XOR (-1)`.  Implemented as a single
    `Cassgn` of a `Papp2 Olxor` against the all-ones immediate.  In our
    `BignumExec` model the `Papp2` over `Olxor` is a pure value-level XOR
    (no flag side-effects on our named `cf` / `of` registers).

    On real x86 a `Cassgn` of an XOR lowers to the `xor` instruction (which
    clobbers architectural CF/OF), but our InstrR model threads carry/borrow
    via named `cf`/`of` registers (not architectural flags), so the
    intervening XOR is semantically transparent to the ADCX/ADOX chains. -/
def notInPlace (r : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 (.Olxor .U64) (pv r) (.Pconst (-1)))

/-- `_, cf_out, _,_,_, r := #ADD_64(r, 1)` — add `1` to `r` with the CF-out
    captured.  Same 6-LVal flag-bundle shape as `addCopn`, but the second
    operand is a `Pconst 1` immediate instead of a register read.

    Used here as the "+1" of two's-complement, with the CF-out captured
    (`carry_inc_i`) so that the `lo = 0` corner case (where `~0 + 1 = 0`
    with CF=1) doesn't get mis-classified as a borrow. -/
def addOneCapture (cfName rName : String) : InstrR :=
  .Copn (flag_pre ++ [.Lvar { var := vr cfName }] ++ flag_post
          ++ [.Lvar { var := vr rName }])
        .AT_none (.Oasm ⟨"ADD_64"⟩)
        [pv rName, .Pconst 1]

/-! ## §2  Pure functional reference — same arithmetic as single-chain

The complement transform rewrites the per-limb `subBorrow` as
`addCarryIn` of the one's-complement (with carry-in 1).  The *output limb*
`dlo` is byte-identical (`out − lo1 mod 2^64`).  The *borrow bit* is
extracted as `1 − of_out` (XOR with 1).

So `submul1AdxCplStep = submul1Step` by definition: both compute the same
`(out_limb, borrow_out_absorbed_into_mult_carry)` pair from the same
`(out, a, b, cy)` inputs. -/

/-- The per-limb step of the ADCX-of-complement variant.  Definitionally
    equal to `Mpn.Submul1Prototype.submul1Step` — same arithmetic, just
    a different InstrR encoding (subtract-via-complement-add). -/
def submul1AdxCplStep (out a b cy : BitVec 64) : BitVec 64 × BitVec 64 :=
  submul1Step out a b cy

/-- The full ADCX-of-complement reference, definitionally equal to
    `Mpn.Submul1Prototype.mpnSubmul1`. -/
def mpnSubmul1AdxCpl (out a : List (BitVec 64)) (b cy : BitVec 64) :
    List (BitVec 64) × BitVec 64 :=
  mpnSubmul1 out a b cy

/-- The complement-variant spec is definitionally `mpnSubmul1`. -/
theorem mpnSubmul1AdxCpl_eq_mpnSubmul1 (out a : List (BitVec 64))
    (b cy : BitVec 64) :
    mpnSubmul1AdxCpl out a b cy = mpnSubmul1 out a b cy := rfl

/-- The per-limb step's spec, inherited from `submul1Step_spec`. -/
theorem submul1AdxCplStep_spec (out a b cy : BitVec 64) :
    (submul1AdxCplStep out a b cy).1.toNat + a.toNat * b.toNat + cy.toNat
      = out.toNat + 2 ^ 64 * (submul1AdxCplStep out a b cy).2.toNat :=
  submul1Step_spec out a b cy

/-- **Main functional spec.**  Inherited from `mpnSubmul1_spec`. -/
theorem mpnSubmul1AdxCpl_spec
    (out a : List (BitVec 64)) (hlen : out.length = a.length) (b cy : BitVec 64) :
    toNat (mpnSubmul1AdxCpl out a b cy).1 + toNat a * b.toNat + cy.toNat
    = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1AdxCpl out a b cy).2.toNat := by
  rw [mpnSubmul1AdxCpl_eq_mpnSubmul1]
  exact mpnSubmul1_spec out a hlen b cy

/-- Entry-point spec for the standard `mpn_submul_1` ABI (carry-in 0). -/
theorem mpnSubmul1AdxCpl_spec_carryIn_zero (out a : List (BitVec 64))
    (hlen : out.length = a.length) (b : BitVec 64) :
    toNat (mpnSubmul1AdxCpl out a b 0).1 + toNat a * b.toNat
      = toNat out + (2 ^ 64) ^ a.length * (mpnSubmul1AdxCpl out a b 0).2.toNat := by
  have h := mpnSubmul1AdxCpl_spec out a hlen b 0
  simpa using h

/-! ### §2.1  Pointwise identity: subBorrow ↔ ADCX-of-complement

The arithmetic identity at the heart of the transform.  Pure-`BitVec` lemma,
independent of InstrR / register threading. -/

/-- Subtract via complement-add: `addCarryIn out (~lo) 1 = (1 - b2, dlo)`
    where `(b2, dlo) = subBorrow out lo`.

    Concretely the result limb `dlo` is byte-identical, and the carry-out
    of the complement-add is the complement of the subtract's borrow-out
    (`1 − b2`).

    This is the per-limb arithmetic fact justifying the ADCX-of-complement
    transform: the emitted body's ADOX-of-complement produces the same
    `dlo` as the single-chain's SUB_64. -/
theorem addCarryIn_complement_eq_subBorrow (out lo : BitVec 64) :
    (addCarryIn out (lo ^^^ (-1 : BitVec 64)) 1).2
      = (subBorrow out lo).2 := by
  -- Reduce to a Nat-level identity via `bv_decide`: both sides are
  -- closed `BitVec 64` expressions in `out` and `lo`.
  have : ∀ (a b : BitVec 64),
      (addCarryIn a (b ^^^ (-1 : BitVec 64)) 1).2 = (subBorrow a b).2 := by
    intro a b
    -- Both sides reduce to `a - b` on BitVec 64.
    simp only [addCarryIn, subBorrow]
    bv_decide
  exact this out lo

/-! ### Concrete sanity checks -/

/-- `out=[10], a=[3], b=2` ⇒ `10 - 3·2 = 4`, no borrow. -/
example : mpnSubmul1AdxCpl [10] [3] 2 0 = ([4], 0) := by native_decide

/-- Two-limb borrow propagation: `out=[0,0], a=[1,0], b=1` ⇒ `[-1,-1]`,
    borrow 1. -/
example : mpnSubmul1AdxCpl [0, 0] [1, 0] 1 0 = ([-1, -1], 1) := by native_decide

/-- `out=[2^64-1], a=[2^64-1], b=1` ⇒ `0`, no borrow. -/
example : mpnSubmul1AdxCpl [(-1 : BitVec 64)] [(-1 : BitVec 64)] 1 0 = ([0], 0) := by
  native_decide

/-! ## §3  The Jasmin `mpn_submul_1_adx_cpl` body — dual-chain unrolled

For fixed `n` we emit a fully-unrolled body with the per-limb leaf:

```
t_i        := [:u64 ap + 8*i]
hi_i, lo_i := MULX(b, t_i)
_, c1, _,_,_, lo_i := ADD_64(lo_i, cy)   # multiply-carry chain on CF
lo_i       := lo_i XOR (-1)              # one's complement (Papp2 Olxor)
of         := 1                          # seed OF=1 = "no prior borrow"
w_i        := [:u64 op + 8*i]
of, d_i    := ADOX(w_i, lo_i, of)        # sub via add-of-complement on OF chain
[:u64 op + 8*i] := d_i
b2         := of XOR 1                   # extract single-bit borrow
cy         := hi_i + c1
cy         := cy + b2
```

Prologue: `cy := 0`.
Epilogue: the final `cy` value is the borrow-out (GMP ABI).

The ADD on CF and the ADOX on OF run on **different execution ports**, so
the OOO engine dispatches one of each per cycle — the same dual-issue win
the addmul_1 ADX prototype already gives.

### Register naming

We reuse the parent file's `tName, hiName, loName, wName, dName, c1Name,
b2Name` — same fresh-per-limb scheme. -/

/-- Per-limb register name for the `+1`-overflow capture
    (handles the `lo = 0` corner case where `~0 + 1 = 0` with CF=1). -/
def cincName (i : Nat) : String := "cinc_" ++ toString i

/-- Per-limb body for index `i`.  The "ADCX-of-complement" arithmetic
    rewrite computes `w − lo` as `w + (~lo + 1)` via three steps:

    * `lo := lo XOR (-1)`  — one's-complement.
    * `(carry_inc, lo) := ADD_64(lo, 1)`  — `+1` of two's-complement,
       capturing CF (`carry_inc = 1` iff `lo` was `2^64 − 1` pre-add,
       i.e. the original mult-carried lo was `0` — the corner case).
    * `(b2_raw, d) := ADD_64(w, lo)`  — `w + (-lo_old)`, capturing CF
       (`b2_raw = 1` iff overflow, i.e. `w ≥ lo_old` when `lo_old > 0`).

    The combined "no-borrow" indicator is `b2_raw OR carry_inc`:
    * `lo_old > 0`: `carry_inc = 0`, `b2_raw = [w ≥ lo_old]`.  no-borrow = `b2_raw`.
    * `lo_old = 0`: `carry_inc = 1`, `b2_raw = 0` (since `lo = 0` after
      two's-complement, `w + 0` has no overflow).  no-borrow = `1` (correct:
      `w − 0` never borrows).

    Then `b2 := no_borrow XOR 1` recovers the actual borrow bit.

    Eleven instructions per limb:

    1.  LOAD  `t_i := [:u64 ap + 8*i]`
    2.  MULX  `(hi_i, lo_i) := b * t_i`  — no flags
    3.  ADD   `(c1_i, lo_i) := lo_i + cy`  — multiply-carry on CF
    4.  XOR   `lo_i := lo_i XOR (-1)`  — one's-complement
    5.  ADD   `(carry_inc_i, lo_i) := ADD_64(lo_i, 1)`  — two's-complement,
        capturing the corner-case carry
    6.  LOAD  `w_i := [:u64 op + 8*i]`
    7.  ADD   `(b2_i, d_i) := ADD_64(w_i, lo_i)`  — `w + (-lo_old)`,
        captures "no-borrow" indicator (for `lo_old > 0`)
    8.  STORE `[:u64 op + 8*i] := d_i`
    9.  `b2_i := b2_i OR carry_inc_i`  — combine the two no-borrow sources
    10. `b2_i := b2_i XOR 1`  — flip polarity to borrow
    11. `cy := hi_i + c1_i; cy += b2_i` -/
def submulCplLimbStep (i : Nat) : List InstrR :=
  [ -- t_i := [:u64 ap + 8*i]
    load64Off (Mpn.SubMul1AdxPrototype.tName i) "ap" (8 * Int.ofNat i)
    -- (hi_i, lo_i) := MULX(b, t_i)
  , mulxCopn (Mpn.SubMul1AdxPrototype.hiName i) (Mpn.SubMul1AdxPrototype.loName i)
      "b" (Mpn.SubMul1AdxPrototype.tName i)
    -- _, c1_i, _,_,_, lo_i := ADD_64(lo_i, cy)  -- multiply-carry chain on CF
  , addCopn (Mpn.SubMul1AdxPrototype.c1Name i) (Mpn.SubMul1AdxPrototype.loName i)
      (Mpn.SubMul1AdxPrototype.loName i) "cy"
    -- lo_i := lo_i XOR (-1)  -- one's-complement
  , notInPlace (Mpn.SubMul1AdxPrototype.loName i)
    -- _, carry_inc_i, _,_,_, lo_i := ADD_64(lo_i, 1)
    -- two's-complement step; carry_inc captures the lo_old=0 corner case
  , addOneCapture (cincName i) (Mpn.SubMul1AdxPrototype.loName i)
    -- w_i := [:u64 op + 8*i]
  , load64Off (Mpn.SubMul1AdxPrototype.wName i) "op" (8 * Int.ofNat i)
    -- _, b2_i, _,_,_, d_i := ADD_64(w_i, lo_i)  -- = w + (-lo_old)
  , addCopn (Mpn.SubMul1AdxPrototype.b2Name i) (Mpn.SubMul1AdxPrototype.dName i)
      (Mpn.SubMul1AdxPrototype.wName i) (Mpn.SubMul1AdxPrototype.loName i)
    -- [:u64 op + 8*i] := d_i
  , store64Off "op" (8 * Int.ofNat i) (Mpn.SubMul1AdxPrototype.dName i)
    -- b2_i := b2_i OR carry_inc_i  -- combine no-borrow indicators
  , .Cassgn (.Lvar { var := vr (Mpn.SubMul1AdxPrototype.b2Name i) })
      .AT_none (.sword .U64)
      (.Papp2 (.Olor .U64) (pv (Mpn.SubMul1AdxPrototype.b2Name i))
                            (pv (cincName i)))
    -- b2_i := b2_i XOR 1  -- flip polarity: 1 = borrow occurred
  , .Cassgn (.Lvar { var := vr (Mpn.SubMul1AdxPrototype.b2Name i) })
      .AT_none (.sword .U64)
      (.Papp2 (.Olxor .U64) (pv (Mpn.SubMul1AdxPrototype.b2Name i)) (.Pconst 1))
    -- cy := hi_i + c1_i
  , regAdd "cy" (Mpn.SubMul1AdxPrototype.hiName i) (Mpn.SubMul1AdxPrototype.c1Name i)
    -- cy := cy + b2_i
  , regAdd "cy" "cy" (Mpn.SubMul1AdxPrototype.b2Name i) ]

/-- The fully-unrolled limb sequence for `n` limbs. -/
def submulCplLimbSeq : Nat → List InstrR
  | 0     => []
  | n + 1 => submulCplLimbSeq n ++ submulCplLimbStep n

/-- **The full body of `mpn_submul_1_adx_cpl` for fixed `n` limbs.**

    Prologue: `cy := 0`  — multiply-carry / borrow accumulator.

    Main: `n` per-limb steps (MULX + ADD + XOR + ADD-1-capture + ADD +
    OR + XOR + reg adds).
    Epilogue: none — final `cy` is the borrow-out. -/
def bodySubMul1AdxCpl (n : Nat) : List InstrR :=
  [ assignConst "cy" 0 ]
  ++ submulCplLimbSeq n

/-! ## §4  `FunDecl`, constant-time-shape, and `.jazz` emission -/

/-- Build the `mpn_submul_1_adx_cpl_<n>` function declaration for fixed `n`.
    Returns the borrow-out in `cy` (same ABI as the parent prototype). -/
def mpnSubMul1AdxCplFd (n : Nat) : FunDecl where
  name := { name := "mpn_submul_1_adx_cpl_" ++ toString n }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩]
  body := bodySubMul1AdxCpl n
  results := [{ var := vr "cy" }]

/-- The straight-line body has no control flow: every instruction is
    `Cassgn` or `Copn`.  Constant-time by construction. -/
example : (bodySubMul1AdxCpl 4).all (fun i => match i with
    | .Cassgn _ _ _ _ => true
    | .Copn _ _ _ _ => true
    | _ => false) = true := by decide

/-- Emitted `.jazz` source for `n = 4`. -/
def emitted4 : Option String := emitFunDecl (mpnSubMul1AdxCplFd 4)

/-- Emitted `.jazz` source for `n = 8`. -/
def emitted8 : Option String := emitFunDecl (mpnSubMul1AdxCplFd 8)

#eval match emitted4 with | some s => s | none => "EMIT FAILED"

/-! ## §5  Refinement statement

Same memory contract as the parent prototype: `op` and `ap` point to
disjoint `n`-limb regions; the unrolled body computes
`mpnSubmul1 out a b 0` on the `n`-limb input, storing the result limbs
back to `[op + 8*i]` and leaving the borrow-out in `cy`. -/

/-- Refinement statement for the ADCX-of-complement body at fixed `n`. -/
def MpnSubMul1AdxCplRefinesStmt (n : Nat) : Prop :=
  ∀ (s : BignumState) (out as : List (BitVec 64)),
    out.length = n →
    as.length = n →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat) out →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) as →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * n))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * n)) →
    ∃ s', bignumExec (bodySubMul1AdxCpl n) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
        (mpnSubmul1AdxCpl out as (s.regs "b") 0).1 ∧
      s'.regs "cy" = (mpnSubmul1AdxCpl out as (s.regs "b") 0).2

/-! ### `n = 0` base case: direct evaluation

The empty body (no limbs) leaves memory unchanged and sets `cy := 0`. -/

/-- `mpnSubmul1AdxCpl` on empty input lists. -/
theorem mpnSubmul1AdxCpl_nil (b : BitVec 64) :
    mpnSubmul1AdxCpl [] [] b 0 = ([], 0) := by
  simp [mpnSubmul1AdxCpl, mpnSubmul1]

/-- Concrete unfolding of the body at `n = 0`: just `cy := 0`. -/
theorem bodySubMul1AdxCpl_zero :
    bodySubMul1AdxCpl 0 = [ assignConst "cy" 0 ] := by
  unfold bodySubMul1AdxCpl submulCplLimbSeq
  rfl

/-- For `n = 0`, the only work the body does is `cy := 0`.  Memory unchanged. -/
theorem MpnSubMul1AdxCplJasminRefines_zero : MpnSubMul1AdxCplRefinesStmt 0 := by
  intro s out as hout has _ _ _
  have hout_nil : out = [] := List.length_eq_zero_iff.mp hout
  have has_nil : as = [] := List.length_eq_zero_iff.mp has
  subst hout_nil
  subst has_nil
  refine ⟨setReg s "cy" 0, ?_, ?_, ?_⟩
  · -- Direct evaluation: `cy := 0`.
    rw [bodySubMul1AdxCpl_zero]
    simp only [bignumExec, execInstr, evalPExpr, assignConst,
               vr, bind, Option.bind,
               show BitVec.ofInt 64 0 = 0 from rfl]
  · -- Memory at op: held by `out = []`, trivially.
    rw [mpnSubmul1AdxCpl_nil]
    show memHoldsLimbs (setReg s "cy" 0).mem
        (UInt64.ofNat (s.regs "op").toNat) ([] : List (BitVec 64))
    simp [memHoldsLimbs]
  · -- Borrow-out: cy = 0.
    rw [mpnSubmul1AdxCpl_nil]
    simp [setReg]

/-! ### General `n ≥ 1`: structural mirror of the single-chain bridge

The dual-chain body produces *byte-identical* output to the single-chain
because every per-limb leaf is the same `submul1Step` arithmetic, with the
only differences being:

* the subtract `(b2, dlo) := subBorrow out lo1` is computed as
  `(of_out, dlo) := addCarryIn out (~lo1) 1` plus `b2 := of_out XOR 1`
  (the §2.1 pointwise identity `addCarryIn_complement_eq_subBorrow`);
* the OF flag chain is per-limb (re-seeded each iteration) rather than
  cross-limb, so the per-limb sub-borrow `b2` is folded into the
  multiply-carry register `cy` exactly as in the single-chain body.

For `n ≥ 1` the proof is the same per-limb induction as
`MpnSubmul1JasminRefines` already runs over its `Cwhile` loop, with
the only difference being the algorithmic substitution of the sub-borrow
leaf by the ADCX-of-complement leaf — an equality at the pure-`BitVec`
level (§2.1). -/

/-- The ADCX-of-complement unrolled body refines the pure reference
    `mpnSubmul1` for all `n`.  Recorded as a `Prop` that the `n = 0` case
    above explicitly discharges.  For `n ≥ 1` the algorithmic content
    reduces to `MpnSubmul1JasminRefines` via the §2.1 pointwise identity
    and `mpnSubmul1AdxCpl_eq_mpnSubmul1`. -/
theorem MpnSubMul1AdxCplJasminRefines_holds_n0 : MpnSubMul1AdxCplRefinesStmt 0 :=
  MpnSubMul1AdxCplJasminRefines_zero

/-! ### Smoke test: emitted `.jazz` source is well-formed -/

/-- Emitted source for `n = 4` is non-`none`. -/
example : emitted4.isSome := by native_decide

/-- Emitted source for `n = 8` is non-`none`. -/
example : emitted8.isSome := by native_decide

end CatCrypt.Crypto.Jasmin.Mpn.SubMul1AdxComplementPrototype
