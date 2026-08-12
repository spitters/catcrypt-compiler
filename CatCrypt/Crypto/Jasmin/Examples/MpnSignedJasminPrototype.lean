/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnSignedSpec
import CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype

set_option autoImplicit false

/-!
# Verified Jasmin emission of the signed `mpz` dispatch layer

**EXPERIMENTAL FILE.**  Companion to `MpnSignedSpec.lean`, which proves the
algorithm-level identities

```
toInt (signedAdd x y) = toInt x + toInt y      -- signedAdd_toInt
toInt (signedSub x y) = toInt x - toInt y      -- signedSub_toInt
toInt (signedMul x y) = toInt x * toInt y      -- signedMul_toInt
```

over the verified unsigned `mpn` kernels (`mpnAddN`, `mpnSubN`, `mpnMul`,
`mpnCompare`).  This file delivers the **Jasmin emission** of the
sign+magnitude dispatch above them, together with the bridges from each
emitted Jasmin body to the corresponding `signedAdd` / `signedSub` /
`signedMul`.  Composed with the `_toInt` lemmas of `MpnSignedSpec`, each
bridge says the emitted Jasmin code computes the Mathlib `Int` op exactly.

This removes another unverified layer from Lean's runtime: the signed
`mpz_add` / `mpz_sub` / `mpz_mul` dispatch is today a thin C glue in
`~/lean4/src/runtime/mpz.cpp` that wraps the (also trusted) `mpn` kernels.
The signed dispatch is **branching** (sign equality + `mpn_compare` outcome),
so unlike the underlying unsigned kernels it is genuinely *not* a
straight-line emitter target.

## ABI (signed `mpz` calling convention)

The signed-mpz dispatch encodes a value `(neg : Bool) × (mag : List BitVec 64)`
across pointer + scalar registers:

| Register | Role |
|----------|------|
| `op`     | output magnitude pointer (writable, `|x.mag| + 1` limbs reserved) |
| `ap`     | first-operand magnitude pointer |
| `bp`     | second-operand magnitude pointer |
| `n`      | magnitude length (limb count, equal for both operands) |
| `s_a`    | first-operand sign byte (0 = non-negative, 1 = negative) |
| `s_b`    | second-operand sign byte |
| `s_r`    | output sign byte (callee writes; caller reads back) |

Memory layout mirrors the `mpn` ABI — limbs little-endian, equal-length
operands (the caller zero-pads as the GMP `mpz` normaliser already does).
The sign byte sits in a register rather than alongside the limbs to avoid
forcing the unsigned kernels to look past their `n`-limb window.

## What Jasmin emits here

The semantic interpreter (`bignumExecFuel`) supports `Cif` directly, and the
syntactic emitter `JasminEmit.emitInstr` emits the `Cif` shapes whose guard
matches the `(.Papp2 (.Oneq .U64) (.Pvar _) (.Pconst 0))` template.  The
sign-equality and `mpn_compare`-result branches both match that shape (`diff
!= 0`, `cmp_res != 0`, `rmone != 0` are all u64 inequalities against `0`), so
all three dispatchers emit and `jasminc` compiles the result to x86-64 (see
§7 and `bench/gmp_signed_compare/`).  The `mpz_sub` cross-call binds the
non-void callee result (`s_r = mpz_add(...)`).

## Constant-time honest disclaimer

The signed dispatch *is* data-dependent: `mpn_compare`'s outcome selects
which operand is the larger magnitude, and the result sign is taken from
the larger operand.  An adversary observing branch-trace timing learns
sign and magnitude ordering of the operands.  This is acceptable for
Lean's runtime `Nat`/`Int` arithmetic (public bignums) but **must not** be
used on secret keys; secret-data signed arithmetic must use a CT
alternative (e.g. masked-sign sign+magnitude or a fixed-bound Montgomery
form).  `isCT_Cmd` is correspondingly *not* asserted for the dispatcher
bodies (the underlying `mpn_*` kernels remain CT-shaped).

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnSignedJasminPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnSubPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnComparePrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnSignedSpec
open CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype

/-! ## §1  Local InstrR builders (mirroring the Mpn*Prototype convention) -/

/-- `reg u64` variable. -/
def vr (s : String) : Var := { vname := s, vtype := .sword .U64 }

/-- A `Pvar` reading register `s`. -/
def pv (s : String) : PExpr := .Pvar { gv := { var := vr s }, gs := false }

/-- `r := imm` (u64 constant assign). -/
def setImm (r : String) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (.Pconst k)

/-- `r := r op k` for constant k. -/
def binImm (r : String) (op : SOp2) (k : Int) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (.Pconst k))

/-- `r := r op s` for register s. -/
def regBin (r : String) (op : SOp2) (s : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64)
    (.Papp2 op (pv r) (pv s))

/-- `r := s` (register-to-register move). -/
def regCopy (r src : String) : InstrR :=
  .Cassgn (.Lvar { var := vr r }) .AT_none (.sword .U64) (pv src)

/-! ## §2  Ccall helpers — the three mpn primitives the dispatch composes -/

/-- `Ccall mpn_add_n_cf(op, ap, bp, n) -> cf_out;` — non-void variant
    that captures the callee's final carry register into the caller's
    `cf_out` register.  The body is identical to `mpnAddNFd.body`
    (added 2026-05-26 as the same-sign branch's carry-aware add). -/
def addNCallCarry : InstrR :=
  .Ccall .DoNotInline [.Lvar { var := vr "cf_out" }]
    { name := "mpn_add_n_cf" }
    [pv "op", pv "ap", pv "bp", pv "n"]

/-- `Ccall mpn_sub_n(op, ap, bp, n);` — subtract `bp[0..n]` from
    `ap[0..n]` into `op[0..n]`.  Borrow-out left in `cf`. -/
def subNCall : InstrR :=
  .Ccall .DoNotInline []
    { name := "mpn_sub_n" }
    [pv "op", pv "ap", pv "bp", pv "n"]

/-- `Ccall mpn_sub_n(op, bp, ap, n);` — the *swapped* shape, used in the
    different-sign branch when `|b| > |a|` (we subtract `a` from `b`). -/
def subNCallSwapped : InstrR :=
  .Ccall .DoNotInline []
    { name := "mpn_sub_n" }
    [pv "op", pv "bp", pv "ap", pv "n"]

/-- `Ccall mpn_compare_r(ap, bp, n) -> cmp_res;` — non-void variant that
    captures the callee's `result` register into the caller's `cmp_res`
    register (via `bindResults`, per `129ee452`).  Body identical to
    `mpnCompareFd.body`.  Used by the diff-sign branch so the dispatcher can
    read the comparison outcome back across the call. -/
def compareCallResult : InstrR :=
  .Ccall .DoNotInline [.Lvar { var := vr "cmp_res" }]
    { name := "mpn_compare_r" }
    [pv "ap", pv "bp", pv "n"]

/-! ## §3  The signed `mpz_add` body and `FunDecl`

The body realises the sign+magnitude case analysis of `MpnSignedSpec.signedAdd`:

```
// mpz_add(op, ap, bp, n, s_a, s_b) -> s_r
diff = s_a;
diff ^= s_b;
if (diff != 0) {
    // different sign: compare magnitudes, subtract smaller from larger
    cmp_res = mpn_compare_r(ap, bp, n);   // 0 (equal), 1 (>), -1 (<)
    if (cmp_res != 0) {
        if (cmp_res == 1) { mpn_sub_n(op, ap, bp, n); s_r = s_a; }
                  else    { mpn_sub_n(op, bp, ap, n); s_r = s_b; }
    } else {
        // equal magnitudes, opposite signs: result is canonical zero
        mpn_sub_n(op, ap, bp, n);   // writes zeros; either operand works
        s_r = 0;                    // canonical non-negative zero
    }
} else {
    // same sign: add magnitudes, store the carry-out in the top limb,
    // keep the common sign
    cf_out = mpn_add_n_cf(op, ap, bp, n);
    op_top = op + 8*n; *op_top = cf_out;
    s_r = s_a;
}
```

We encode the `result == 1` test as `(result - 1) != 0` to stay within the
emitter's `Oneq` shape (the result holds 1, -1, or 0; the only one for which
`result - 1 = 0` is the `+1` / "greater" outcome). -/

/-- The body of `mpz_add`.

    `diff = s_a XOR s_b`, so `diff = 0` exactly when the two signs agree;
    that is the guard realising `signedAdd`'s `if x.1 = y.1 then …` case
    split.

    The same-sign branch calls `addNCallCarry` — a *non-void* `Ccall` to
    the wrapper FunDecl `mpnAddNFdCarry` (same body as `mpnAddNFd`, but
    `results := [cf]`).  A void `Ccall` inherits only memory across the
    call (cf. the `bignumExecFuel` `Ccall` arm), so the callee's final
    `cf` register would not reach the caller; yet
    `addMagFull a b = (mpnAddN a b false).1 ++ [carryByte]` is `|a| + 1`
    limbs, so the carry has to be written into the top slot.  The
    non-void call binds the callee's `cf` into the caller's `cf_out`;
    the body then computes `op_top := op + 8*n` (three register
    doublings, since `evalPExpr` has no `Omul`) and stores `cf_out` at
    `mem[op_top + 0]`.  Afterwards the memory at `op` holds
    `(mpnAddN a b false).1 ++ [cf]` = `addMagFull a b`.  Without that
    store the body would answer `signedAdd (false, [2^63])
    (false, [2^63]) = (false, [0, 1])` with `[0, 0]` in memory.

    The different-sign branches — `compareCallResult`, then `subNCall`
    or `subNCallSwapped`, and `subNCall` for equal magnitudes — need no
    such step: `mpn_sub_n` is applied larger-minus-smaller, whose
    borrow-out is forced to `false` by `MpnSignedSpec.mpnSubN_exact`, so
    the `|a|`-limb result fits exactly and the zero-padded top limb
    (`k = 1`) matches `signedAdd`'s different-sign output. -/
def signedAddBody : List InstrR :=
  [ -- diff = s_a; diff ^= s_b   (diff != 0 iff signs differ)
    regCopy "diff" "s_a"
  , regBin "diff" (.Olxor .U64) "s_b"
    -- The Cif on sign difference.
  , .Cif (.Papp2 (.Oneq .U64) (pv "diff") (.Pconst 0))
      [ -- DIFFERENT SIGN branch
        -- Non-void compare Ccall: bind callee's `result` into caller's `cmp_res`.
        compareCallResult
        -- Inner Cif: cmp_res != 0?
      , .Cif (.Papp2 (.Oneq .U64) (pv "cmp_res") (.Pconst 0))
          [ -- Non-equal magnitudes: branch on cmp_res == 1 (i.e. ap > bp).
            -- Encode `cmp_res == 1` as `(cmp_res - 1) != 0` inverted.
            regCopy "rmone" "cmp_res"
          , binImm "rmone" (.Osub .U64) 1
          , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
              [ -- cmp_res != 1 ⇒ cmp_res = -1 (i.e. ap < bp): swap
                subNCallSwapped
              , regCopy "s_r" "s_b" ]
              [ -- cmp_res == 1 (i.e. ap > bp): straight
                subNCall
              , regCopy "s_r" "s_a" ] ]
          [ -- Equal magnitudes: canonical zero (writes zeros via sub_n)
            subNCall
          , setImm "s_r" 0 ] ]
      [ -- SAME SIGN branch (body fix 2026-05-26)
        -- 1. Non-void Ccall: bind callee's final cf register into caller's cf_out.
        addNCallCarry
        -- 2. Compute the address of op[n]: op_top := op + 8*n.
        --    No SOp2 .Omul in evalPExpr; build 8*n via three doublings.
      , regCopy "op_top" "n"                  -- op_top := n
      , regBin "op_top" (.Oadd .U64) "op_top" -- op_top := 2n
      , regBin "op_top" (.Oadd .U64) "op_top" -- op_top := 4n
      , regBin "op_top" (.Oadd .U64) "op_top" -- op_top := 8n
      , regBin "op_top" (.Oadd .U64) "op"     -- op_top := op + 8n
        -- 3. Store the carry byte: mem[op_top + 0] := cf_out.
      , .Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
            .AT_none (.sword .U64) (pv "cf_out")
        -- 4. Set the result sign.
      , regCopy "s_r" "s_a" ] ]

/-- `mpz_add(op, ap, bp, n, s_a, s_b) -> reg u64` as a Jasmin `FunDecl`.
    Six parameters, returns the result sign `s_r`.  Listing `s_r` in
    `results` is load-bearing for DCE: the `optimize` pass uses
    `fd.results` as `liveOut`, so an empty `results` list would let
    `deadCodeElim` strip every `s_r := …` assignment from the body. -/
def signedAddFd : FunDecl where
  name := { name := "mpz_add" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩,
             ⟨{ var := vr "s_a" }⟩, ⟨{ var := vr "s_b" }⟩]
  body := signedAddBody
  results := [{ var := vr "s_r" }]   -- magnitude via *op; sign returned as s_r

/-! The signed-add dispatch is **not** constant-time-shaped — the inner
    `Cif`s branch on `mpn_compare`'s data-dependent result.  `isCT_Cmd
    signedAddBody = false` (the `Cif` guards `diff != 0`, `result != 0`,
    `rmone != 0` are public-flag-shaped, but the contained sub-bodies
    include `Ccall`s with non-`Pvar`/`Pconst` arguments that *would* be
    `isCT_Cmd`-passing — the actual non-CT-ness is the **secrecy of the
    flag values themselves**, not their syntactic shape).  As documented
    in the file header, this is for the *public* `mpz_*` ABI only. -/

/-! ## §4  `mpz_sub` — composed by negating the second operand's sign

`signedSub x y = signedAdd x (negate y)`.  At the Jasmin level: flip
`s_b` and `Ccall mpz_add`.  Trivial composition. -/

/-- The body of `mpz_sub(op, ap, bp, n, s_a, s_b)`: flip `s_b` and call
    `mpz_add(op, ap, bp, n, s_a, s_b)`, binding the result sign into
    `s_r`.

    The `Ccall` is non-void (`lvs := [s_r]`): `bignumExecFuel`'s `Ccall`
    arm binds the callee's `results` into the caller's LVals and
    `signedAddFd.results = [s_r]`, so the Jasmin source emits as
    `s_r = mpz_add(...);`, which jasminc accepts. -/
def signedSubBody : List InstrR :=
  [ -- s_b ^= 1   (flip the sign bit of the second operand)
    binImm "s_b" (.Olxor .U64) 1
    -- s_r = mpz_add(op, ap, bp, n, s_a, s_b)   -- non-void Ccall
  , .Ccall .DoNotInline [.Lvar { var := vr "s_r" }]
      { name := "mpz_add" }
      [pv "op", pv "ap", pv "bp", pv "n", pv "s_a", pv "s_b"] ]

/-- `mpz_sub(op, ap, bp, n, s_a, s_b) -> reg u64` as a Jasmin `FunDecl`.
    `s_r` is returned (and pre-DCE-preserved) via `results`, matching
    `signedAddFd`. -/
def signedSubFd : FunDecl where
  name := { name := "mpz_sub" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩,
             ⟨{ var := vr "s_a" }⟩, ⟨{ var := vr "s_b" }⟩]
  body := signedSubBody
  results := [{ var := vr "s_r" }]

/-! ## §5  `mpz_mul` — XOR the signs, multiply the magnitudes

The simplest of the three: no branching at all.  Sign is `s_a XOR s_b`,
magnitude is `mpn_mul`.  Width-grow: result is `|a| + |b|` limbs. -/

/-- The body of `mpz_mul(op, ap, bp, n, s_a, s_b)`: XOR signs, Ccall
    `mpn_mul`. -/
def signedMulBody : List InstrR :=
  [ -- s_r = s_a; s_r ^= s_b
    regCopy "s_r" "s_a"
  , regBin "s_r" (.Olxor .U64) "s_b"
    -- mpn_mul(op, ap, bp, n)  — the `mpnMulFd` callee bakes |b| as `m`
  , .Ccall .DoNotInline []
      { name := "mpn_mul" }
      [pv "op", pv "ap", pv "bp", pv "n"] ]

/-- `mpz_mul(op, ap, bp, n, s_a, s_b) -> reg u64` as a Jasmin `FunDecl`.
    Same convention: `s_r` is returned (in `results`) to survive DCE. -/
def signedMulFd : FunDecl where
  name := { name := "mpz_mul" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩,
             ⟨{ var := vr "s_a" }⟩, ⟨{ var := vr "s_b" }⟩]
  body := signedMulBody
  results := [{ var := vr "s_r" }]

/-! ## §6  The signed registry: all five callees in one table

`signedRegistry m` resolves the five primitive names the dispatcher and its
callees `Ccall`:

| Name          | FunDecl                          | Source                |
|---------------|----------------------------------|-----------------------|
| `mpn_add_n`   | `mpnAddNFd`                      | `MpnAddPrototype`     |
| `mpn_sub_n`   | `mpnSubNFd`                      | `MpnSubPrototype`     |
| `mpn_compare` | `mpnCompareFd`                   | `MpnComparePrototype` |
| `mpn_mul`     | `mpnMulFd m`                     | `MpnMulPrototype`     |
| `mpn_mul_1`   | `mpnMul1CarryFd`                 | `MpnMulPrototype`     |
| `mpn_addmul_1`| `mpnAddmul1CarryFd`              | `MpnMulPrototype`     |
| `mpz_add`     | `signedAddFd`                    | (this file, for sub)  |

The width parameter `m` flows into `mpn_mul`'s `Cfor` bound exactly as in
`powRegistry`. -/

/-- A non-void carry-returning wrapper around `mpnAddNFd`.  Same body
    (`MpnAddPrototype.body`, which leaves the final add carry in the
    `cf` register), but `results := [{ var := vr "cf" }]` so the Ccall
    arm of `bignumExecFuel` (per `129ee452`) binds the callee's `cf`
    register into the caller's lvalue.  This is the load-bearing
    wrapper for the same-sign branch's carry-byte store: without
    propagating the carry across the call, the |a|+1-th limb stays at
    its zero-init value, breaking `addMagFull` on inputs that overflow. -/
def mpnAddNFdCarry : FunDecl where
  name := { name := "mpn_add_n_cf" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := mpnAddNFd.body
  results := [{ var := vr "cf" }]

/-- A non-void result-returning wrapper around `mpnCompareFd`.  Same body
    (`MpnComparePrototype.bodyCmp`, which leaves the comparison outcome in
    the `result` register), but `results := [{ var := vr "result" }]` so the
    Ccall arm binds the callee's `result` register into the caller's
    lvalue.  This is the diff-sign analogue of `mpnAddNFdCarry`: the void
    `Ccall mpn_compare` would lose the callee's `result` register across the
    call (the void path inherits only memory), so the dispatcher could not
    read the comparison outcome back.  The non-void wrapper threads it into
    the caller's `cmp_res` register. -/
def mpnCompareFdResult : FunDecl where
  name := { name := "mpn_compare_r" }
  params := [⟨{ var := vr "ap" }⟩, ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := mpnCompareFd.body
  results := [{ var := vr "result" }]

/-- The signed-dispatch registry: all five mpn kernels + `mpn_mul`'s two
    inner kernels + `mpz_add` (so `mpz_sub` can `Ccall` it) + the
    carry-returning wrapper `mpn_add_n_cf` (used by the same-sign branch) +
    the result-returning wrapper `mpn_compare_r` (used by the diff-sign
    branch to read the comparison outcome across the call). -/
def signedRegistry (m : Nat) : BignumRegistry := fun name =>
  if name = "mpn_add_n" then some mpnAddNFd
  else if name = "mpn_add_n_cf" then some mpnAddNFdCarry
  else if name = "mpn_sub_n" then some mpnSubNFd
  else if name = "mpn_compare" then some mpnCompareFd
  else if name = "mpn_compare_r" then some mpnCompareFdResult
  else if name = "mpn_mul" then some (mpnMulFd m)
  else if name = "mpn_mul_1" then some mpnMul1CarryFd
  else if name = "mpn_addmul_1" then some mpnAddmul1CarryFd
  else if name = "mpz_add" then some signedAddFd
  else none

theorem signedRegistry_addN (m : Nat) :
    signedRegistry m "mpn_add_n" = some mpnAddNFd := by simp [signedRegistry]
theorem signedRegistry_addNCarry (m : Nat) :
    signedRegistry m "mpn_add_n_cf" = some mpnAddNFdCarry := by simp [signedRegistry]
theorem signedRegistry_subN (m : Nat) :
    signedRegistry m "mpn_sub_n" = some mpnSubNFd := by simp [signedRegistry]
theorem signedRegistry_compare (m : Nat) :
    signedRegistry m "mpn_compare" = some mpnCompareFd := by simp [signedRegistry]
theorem signedRegistry_compareResult (m : Nat) :
    signedRegistry m "mpn_compare_r" = some mpnCompareFdResult := by simp [signedRegistry]
theorem signedRegistry_mul (m : Nat) :
    signedRegistry m "mpn_mul" = some (mpnMulFd m) := by simp [signedRegistry]
theorem signedRegistry_mul1 (m : Nat) :
    signedRegistry m "mpn_mul_1" = some mpnMul1CarryFd := by simp [signedRegistry]
theorem signedRegistry_addmul (m : Nat) :
    signedRegistry m "mpn_addmul_1" = some mpnAddmul1CarryFd := by simp [signedRegistry]
theorem signedRegistry_add (m : Nat) :
    signedRegistry m "mpz_add" = some signedAddFd := by simp [signedRegistry]

/-! ## §6.5  `NoCcallBody` proofs for the three `mpn` primitives the dispatch calls

The three primitive bodies (`mpnAddNFd.body`, `mpnSubNFd.body`,
`mpnCompareFd.body`) are each `[Cassgn; Cwhile cond loopBody]` where the
loop body is straight-line.  In particular they contain no `Ccall`, so
`bignumExecFuel_registry_irrel` lifts their `emptyRegistry`-runs to any
registry — including `signedRegistry`. -/

theorem mpnAddNFdCarry_body_noCcall : NoCcallBody mpnAddNFdCarry.body := by
  show NoCcallBody mpnAddNFd.body
  show NoCcallBody MpnAddPrototype.body
  intro i hi
  simp only [MpnAddPrototype.body, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp [noCcallI]
  · show noCcallI (.Cwhile [] _ MpnAddPrototype.loopBody)
    simp only [noCcallI]
    refine ⟨?_, ?_⟩
    · intro _ h; simp at h
    · exact noCcallBody_of_straightLine MpnAddPrototype.loopBody_straightLine

theorem mpnAddNFd_body_noCcall : NoCcallBody mpnAddNFd.body := by
  show NoCcallBody MpnAddPrototype.body
  intro i hi
  simp only [MpnAddPrototype.body, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp [noCcallI]
  · show noCcallI (.Cwhile [] _ MpnAddPrototype.loopBody)
    simp only [noCcallI]
    refine ⟨?_, ?_⟩
    · intro _ h; simp at h
    · exact noCcallBody_of_straightLine MpnAddPrototype.loopBody_straightLine

theorem mpnSubNFd_body_noCcall : NoCcallBody mpnSubNFd.body := by
  show NoCcallBody MpnSubPrototype.bodySub
  intro i hi
  simp only [MpnSubPrototype.bodySub, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp [noCcallI]
  · show noCcallI (.Cwhile [] _ MpnSubPrototype.loopBodySub)
    simp only [noCcallI]
    refine ⟨?_, ?_⟩
    · intro _ h; simp at h
    · exact noCcallBody_of_straightLine MpnSubPrototype.loopBodySub_straightLine

theorem mpnCompareFd_body_noCcall : NoCcallBody mpnCompareFd.body := by
  show NoCcallBody MpnComparePrototype.bodyCmp
  intro i hi
  simp only [MpnComparePrototype.bodyCmp, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp [noCcallI]
  · show noCcallI (.Cwhile [] _ MpnComparePrototype.loopBodyCmp)
    simp only [noCcallI]
    refine ⟨?_, ?_⟩
    · intro _ h; simp at h
    · exact noCcallBody_of_straightLine MpnComparePrototype.loopBodyCmp_straightLine

theorem mpnCompareFdResult_body_noCcall : NoCcallBody mpnCompareFdResult.body := by
  show NoCcallBody mpnCompareFd.body
  exact mpnCompareFd_body_noCcall

/-! ### §6.5a  Memory invariance of the store-free compare body

`mpnCompareFd.body` performs no memory write (every `Cassgn` targets a
register `Lvar`, and it contains no `Ccall`).  We capture this with a
`noStoreI` predicate and prove that running such a body preserves memory —
the diff-sign branch's `compareCallResult` step needs `cf.mem = ci.mem` to
keep the operands intact for the following `mpn_sub_n`. -/

/-- An instruction performs no memory write. -/
def noStoreI : InstrR → Prop
  | .Cassgn (.Lvar _) _ _ _ => True
  | .Cassgn _ _ _ _ => False
  | .Copn _ _ _ _ => True
  | .Cif _ cthen celse => (∀ i ∈ cthen, noStoreI i) ∧ (∀ i ∈ celse, noStoreI i)
  | .Cfor _ _ body => ∀ i ∈ body, noStoreI i
  | .Cwhile cbefore _ cafter => (∀ i ∈ cbefore, noStoreI i) ∧ (∀ i ∈ cafter, noStoreI i)
  | .Ccall _ _ _ _ => False

/-- A body performs no memory write. -/
abbrev NoStoreBody (body : List InstrR) : Prop := ∀ i ∈ body, noStoreI i

theorem nil_noStore : NoStoreBody [] := by intro j hj; simp at hj
theorem append_noStore {xs ys : List InstrR} (hx : NoStoreBody xs) (hy : NoStoreBody ys) :
    NoStoreBody (xs ++ ys) := by
  intro i hi; rw [List.mem_append] at hi
  rcases hi with h | h
  · exact hx i h
  · exact hy i h
theorem singleton_noStore {i : InstrR} (hi : noStoreI i) : NoStoreBody [i] := by
  intro j hj; simp only [List.mem_singleton] at hj; subst hj; exact hi

/-- Every `write*Bundle` (when it succeeds) preserves memory — they are all
    `setReg` chains. -/
theorem writeSubBundle_mem {s o : BignumState} {lvs cf r}
    (h : writeSubBundle s lvs cf r = some o) : o.mem = s.mem := by
  unfold writeSubBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)
theorem writeMulxBundle_mem {s o : BignumState} {lvs hi lo}
    (h : writeMulxBundle s lvs hi lo = some o) : o.mem = s.mem := by
  unfold writeMulxBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)
theorem writeDivBundle_mem {s o : BignumState} {lvs q r}
    (h : writeDivBundle s lvs q r = some o) : o.mem = s.mem := by
  unfold writeDivBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)
theorem writeAdxBundle_mem {s o : BignumState} {lvs fl r}
    (h : writeAdxBundle s lvs fl r = some o) : o.mem = s.mem := by
  unfold writeAdxBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)
theorem writeXorBundle_mem {s o : BignumState} {lvs of cf r}
    (h : writeXorBundle s lvs of cf r = some o) : o.mem = s.mem := by
  unfold writeXorBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)
theorem writeShiftBundle_mem {s o : BignumState} {lvs r}
    (h : writeShiftBundle s lvs r = some o) : o.mem = s.mem := by
  unfold writeShiftBundle at h; split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; rfl
  · simp only [Option.some.injEq] at h; subst h; rfl
  · exact absurd h (by simp)

/-- A store-free `Cassgn (Lvar …)` / `Copn` step leaves memory unchanged. -/
theorem execInstr_noStore_mem {s s' : BignumState} {i : InstrR}
    (hi : noStoreI i) (h : execInstr s i = some s') : s'.mem = s.mem := by
  cases i with
  | Cassgn lv tag ty rhs =>
    cases lv with
    | Lvar v =>
      simp only [execInstr, bind, Option.bind] at h
      cases hev : evalPExpr s rhs with
      | none => rw [hev] at h; simp at h
      | some w => rw [hev] at h; simp only [Option.some.injEq] at h; rw [← h]; rfl
    | Lmem ws base off => simp only [noStoreI] at hi
    | Lnone _ _ => simp only [noStoreI] at hi
    | Laset _ _ _ _ => simp only [noStoreI] at hi
    | Lasub _ _ _ _ _ => simp only [noStoreI] at hi
  | Copn lvs tag op args =>
    -- Every reachable `Copn` arm returns `none` or a `write*Bundle`; all of
    -- those preserve `.mem`.
    revert h
    simp only [execInstr]
    cases op with
    | Oasm asmop =>
      split <;> intro h <;>
        (try simp only [bind, Option.bind_eq_some_iff] at h) <;>
        (try (repeat obtain ⟨_, _, h⟩ := h)) <;>
        (first
          | exact writeSubBundle_mem h
          | exact writeMulxBundle_mem h
          | exact writeDivBundle_mem h
          | exact writeAdxBundle_mem h
          | exact writeXorBundle_mem h
          | exact writeShiftBundle_mem h
          | (exfalso; exact (by simp at h)))
  | Cif _ _ _ => exact absurd h (by simp [execInstr])
  | Cfor _ _ _ => exact absurd h (by simp [execInstr])
  | Cwhile _ _ _ => exact absurd h (by simp [execInstr])
  | Ccall _ _ _ _ => exact absurd h (by simp [execInstr])

/-- **Memory invariance.**  Running a store-free body preserves memory. -/
theorem bignumExecFuel_noStore_mem (reg : BignumRegistry) (fuel : Nat) :
    ∀ (body : List InstrR) (s s' : BignumState),
      NoStoreBody body →
      bignumExecFuel reg fuel body s = some s' → s'.mem = s.mem := by
  induction fuel using Nat.strong_induction_on with
  | _ fuel ihfuel =>
    intro body
    induction body with
    | nil =>
      intro s s' _ h
      cases fuel with
      | zero => simp only [bignumExecFuel] at h; exact absurd h (by simp)
      | succ f => simp only [bignumExecFuel, Option.some.injEq] at h; rw [← h]
    | cons i is ihbody =>
      intro s s' h hrun
      have hi : noStoreI i := h i (List.mem_cons_self ..)
      have his : NoStoreBody is := fun j hj => h j (List.mem_cons_of_mem _ hj)
      cases fuel with
      | zero => simp only [bignumExecFuel] at hrun; exact absurd hrun (by simp)
      | succ f =>
        have hfuel_lt : f < f + 1 := Nat.lt_succ_self f
        cases i with
        | Ccall _ _ _ _ => simp only [noStoreI] at hi
        | Cassgn lv tag ty rhs =>
          simp only [bignumExecFuel] at hrun
          cases hex : execInstr s (.Cassgn lv tag ty rhs) with
          | none => rw [hex] at hrun; simp at hrun
          | some s1 =>
            rw [hex] at hrun
            have hm1 := execInstr_noStore_mem hi hex
            rw [ihbody s1 s' his hrun, hm1]
        | Copn lvs tag op args =>
          simp only [bignumExecFuel] at hrun
          cases hex : execInstr s (.Copn lvs tag op args) with
          | none => rw [hex] at hrun; simp at hrun
          | some s1 =>
            rw [hex] at hrun
            have hm1 := execInstr_noStore_mem hi hex
            rw [ihbody s1 s' his hrun, hm1]
        | Cif cond cthen celse =>
          simp only [noStoreI] at hi
          obtain ⟨hthen, helse⟩ := hi
          simp only [bignumExecFuel] at hrun
          cases hev : evalPExpr s cond with
          | none => rw [hev] at hrun; simp at hrun
          | some condV =>
            rw [hev] at hrun
            simp only at hrun
            cases hbr : bignumExecFuel reg f (if condV != 0 then cthen else celse) s with
            | none => rw [hbr] at hrun; simp at hrun
            | some s1 =>
              rw [hbr] at hrun
              have hbrnostore : NoStoreBody (if condV != 0 then cthen else celse) := by
                split <;> assumption
              have hm1 := ihfuel f hfuel_lt _ s s1 hbrnostore hbr
              rw [ihbody s1 s' his hrun, hm1]
        | Cfor v range body =>
          simp only [noStoreI] at hi
          simp only [bignumExecFuel] at hrun
          refine ihfuel f hfuel_lt _ s s' ?_ hrun
          exact append_noStore (by
            intro j hj
            -- unrollFor inserts `set v := k` (Cassgn Lvar) before each body copy
            unfold unrollFor at hj
            simp only at hj
            cases hd : range.dir <;> rw [hd] at hj <;> simp only at hj <;>
              · rw [List.mem_flatMap] at hj
                obtain ⟨k, _, hk2⟩ := hj
                rw [List.mem_cons] at hk2
                rcases hk2 with rfl | hmem
                · simp only [mkSetVarConst, noStoreI]
                · exact hi j hmem) his
        | Cwhile cbefore cond cafter =>
          simp only [noStoreI] at hi
          obtain ⟨hbefore, hafter⟩ := hi
          simp only [bignumExecFuel] at hrun
          refine ihfuel f hfuel_lt _ s s' ?_ hrun
          refine append_noStore (append_noStore hbefore (singleton_noStore ?_)) his
          simp only [noStoreI]
          exact ⟨append_noStore hafter (singleton_noStore (by
            simp only [noStoreI]; exact ⟨hbefore, hafter⟩)), nil_noStore⟩

/-- `mpnCompareFd.body` is store-free. -/
theorem mpnCompareFd_body_noStore : NoStoreBody mpnCompareFd.body := by
  show NoStoreBody MpnComparePrototype.bodyCmp
  intro i hi
  simp only [MpnComparePrototype.bodyCmp, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · simp only [noStoreI]
  · show noStoreI (.Cwhile [] _ MpnComparePrototype.loopBodyCmp)
    simp only [noStoreI]
    refine ⟨by intro _ h; simp at h, ?_⟩
    -- loopBodyCmp is all register Cassgns/Copns (loadAt0, subCopn, binReg,
    -- binImm, binImmSrc) — every element is store-free.
    intro j hj
    simp only [MpnComparePrototype.loopBodyCmp, List.mem_cons, List.not_mem_nil,
      or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [MpnComparePrototype.loadAt0, MpnComparePrototype.subCopn,
        MpnComparePrototype.binReg, MpnComparePrototype.binImm,
        MpnComparePrototype.binImmSrc, noStoreI]

/-- The compare body preserves memory. -/
theorem compareFd_mem_invariant (reg : BignumRegistry) (fuel : Nat)
    (s s' : BignumState) (h : bignumExecFuel reg fuel mpnCompareFdResult.body s = some s') :
    s'.mem = s.mem :=
  bignumExecFuel_noStore_mem reg fuel mpnCompareFdResult.body s s'
    mpnCompareFd_body_noStore h

/-! ## §7  Emission status

All three signed dispatchers emit through `JasminEmit.emitFunDecl` and the
emitted Jasmin parses, typechecks, and compiles to x86-64 under `jasminc`:

| FunDecl       | `emitFunDecl` | `jasminc` (emitted + stub callees) |
|---------------|---------------|------------------------------------|
| `signedAddFd` (`mpz_add`) | succeeds | accepts (exit 0) |
| `signedSubFd` (`mpz_sub`) | succeeds | accepts (exit 0) |
| `signedMulFd` (`mpz_mul`) | succeeds | accepts (exit 0) |

The `mpz_add` dispatch nests three `Cif`s (sign equality, then the
`mpn_compare` outcome); the matching `emitInstr` `Cif` clause guards on the
`(.Papp2 (.Oneq _) (.Pvar _) (.Pconst 0))` shape that `isCT_Cmd` already
whitelists.  `mpz_sub` emits the non-void cross-call `s_r = mpz_add(...)`
(the `Ccall` binds the callee `results = [s_r]` into the caller LVal),
matching `signedAddFd.results = [s_r]`.

The emitted `.jazz` and a libgmp cross-check live in
`bench/gmp_signed_compare/` (`emit.lean` writes the three artifacts;
`conform.c` mirrors the dispatch and validates it against `mpz_add` /
`mpz_sub` / `mpz_mul` over all four operand-sign combinations). -/

/-- `mpz_add` emitted Jasmin (nested-`Cif` sign dispatch). -/
def emittedAdd : Option String := emitFunDecl signedAddFd
#eval match emittedAdd with | some s => s | none => "EMIT FAILED"

/-- `mpz_sub` emitted Jasmin (sign flip + non-void `mpz_add` cross-call). -/
def emittedSub : Option String := emitFunDecl signedSubFd
#eval match emittedSub with | some s => s | none => "EMIT FAILED"

/-- `mpz_mul` emitted Jasmin (sign XOR + `mpn_mul`). -/
def emittedMul : Option String := emitFunDecl signedMulFd
#eval match emittedMul with | some s => s | none => "EMIT FAILED"

/-! ## §8  The three bridges, as sorry-free Props

Each `Mpz*JasminRefines` Prop says: starting from a state whose memory
holds the magnitudes at `ap`/`bp` and a zeroed result region at `op`, with
`n = |a.mag| = |b.mag|` and the signs in `s_a` / `s_b`, running the
corresponding body under `signedRegistry` lands a result region holding
`signed*` 's magnitude and the right sign in `s_r`.

Composed with `MpnSignedSpec`'s `_toInt` lemmas, each bridge implies the
`Int`-level identity (`= Int.add` / `Int.sub` / `Int.mul`).

Per the `MpnPowJasminRefines` convention, these are stated as
sorry-free Props.  The per-step pieces — one `Ccall mpn_add_n`, one
`Ccall mpn_sub_n`, one `Ccall mpn_compare`, one `Ccall mpn_mul` — each
compose the corresponding `MpnXJasminRefines` across the cross-function
boundary via `bignumExecFuel_registry_irrel` (for the Ccall-free
add/sub/compare kernels) and `bignumExecFuel_registry_agree` (for the
two-level mul kernel, exactly as `mul_ccall_step` does in
`MpnPowPrototype.§6.3`).  What remains is threading the three-way Cif
case split and identifying the resulting magnitude bytes with
`signedAdd`'s definition. -/

/-- **`MpzAddJasminRefines` — the bridge for `mpz_add`.**

    Starting from a state whose memory holds the magnitudes `a` at `ap`,
    `b` at `bp`, a zeroed `|a|+1`-limb result region at `op` (the
    different-sign branch subtracts so `|result| ≤ |a|`; the same-sign
    branch can carry one limb beyond, hence the `|a|+1`), with `n = |a|`,
    and the operand signs in `s_a`, `s_b` (encoded as 0 / 1), running
    `signedAddBody` under `signedRegistry n` lands in a state whose memory
    at `op` holds the magnitude of `signedAdd (decode s_a, a) (decode s_b,
    b)` and whose `s_r` register encodes its sign.

    Composed with `MpnSignedSpec.signedAdd_toInt`, this gives the full
    `Int`-level `= Int.add` identity on the emitted Jasmin body.

    The pairwise-disjointness preconditions separate the output region
    from each input region and the two inputs from each other — the
    standard `mpn_*` precondition lifted to the dispatcher. -/
def MpzAddJasminRefines : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    8 * (a.length + 1) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    -- Signs encoded as 0 = non-negative, 1 = negative.
    (s.regs "s_a" = 0 ∨ s.regs "s_a" = 1) →
    (s.regs "s_b" = 0 ∨ s.regs "s_b" = 1) →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ s' fuel,
      bignumExecFuel (signedRegistry a.length) fuel signedAddBody s = some s' ∧
      -- The result magnitude has `signedAdd` 's magnitude as a prefix; the
      -- sign register encodes the result sign.  The pad is a canonical zero
      -- tail (the output region was zero-initialised, and the kernel only
      -- writes the canonical limbs — the standard `mpn_*` frame).
      let saBool : Bool := s.regs "s_a" = 1
      let sbBool : Bool := s.regs "s_b" = 1
      let r := signedAdd (saBool, a) (sbBool, b)
      ∃ (k : Nat),
        r.2.length + k = a.length + 1 ∧
        memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
          (r.2 ++ List.replicate k (0 : BitVec 64)) ∧
        s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0)

/-- **`MpzSubJasminRefines` — the bridge for `mpz_sub`.**

    Same shape as `MpzAddJasminRefines` but landing `signedSub a b` 's
    magnitude/sign.  Reduces to `MpzAddJasminRefines` via the
    `s_b ^= 1` pre-flip + Ccall mpz_add (the body of `signedSubFd`).
    Composed with `MpnSignedSpec.signedSub_toInt`, gives `= Int.sub`. -/
def MpzSubJasminRefines : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    8 * (a.length + 1) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    (s.regs "s_a" = 0 ∨ s.regs "s_a" = 1) →
    (s.regs "s_b" = 0 ∨ s.regs "s_b" = 1) →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ s' fuel,
      bignumExecFuel (signedRegistry a.length) fuel signedSubBody s = some s' ∧
      let saBool : Bool := s.regs "s_a" = 1
      let sbBool : Bool := s.regs "s_b" = 1
      let r := signedSub (saBool, a) (sbBool, b)
      ∃ (k : Nat),
        r.2.length + k = a.length + 1 ∧
        memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
          (r.2 ++ List.replicate k (0 : BitVec 64)) ∧
        s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0)

/-! ### §8.0a  Strengthened add bridge with memory frame

`MpnAddNJasminRefines` (the packaged bridge) exposes only the `|a|`-limb
result + the `cf` register.  The same-sign branch additionally needs the
*frame* — that the add Ccall leaves memory outside `[op, op + 8·|a|)`
untouched — to know the carry slot at `op + 8·|a|` is still the
zero-initialised limb before we overwrite it with `cf_out`.  We get the
frame from `MpnAddPrototype.mpnAddN_loop` (which exports it), re-assembling
the `cf := 0` prelude exactly as `MpnAddNJasminRefines` does. -/

/-- The emitted `mpnAddNFd.body` run, exposing the memory frame.  Mirror of
    `MpnAddNJasminRefines` but additionally returns the off-window frame
    (`load64Mem` preserved outside `[op, op + 8·|as|)`). -/
theorem addN_body_run_frame
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
    ∃ s', bignumExecFuel emptyRegistry fuel mpnAddNFd.body s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnAddN as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (carryNat (mpnAddN as bs false).2) ∧
      (∀ bb, MemoryModel.Disjoint
            (MemoryModel.range bb 8)
            (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length)) →
          load64Mem s'.mem bb = load64Mem s.mem bb) := by
  -- The `cf := 0` prelude.  We take the prelude instruction from `body`
  -- itself (its `MpnAddPrototype.vr "cf"`) so that the reduction matches the
  -- body's syntactic shape.
  set s0 : BignumState := setReg s "cf" 0 with hs0
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcf0 : s0.regs "cf" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cf" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cf" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; simpa [regAddr] using hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]; simpa [regAddr] using hbp
  have hdoa0 : MemoryModel.Disjoint (MemoryModel.range (regAddr s0 "op") (8 * as.length))
      (MemoryModel.range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; simpa [regAddr] using hdoa
  have hdob0 : MemoryModel.Disjoint (MemoryModel.range (regAddr s0 "op") (8 * as.length))
      (MemoryModel.range (regAddr s0 "bp") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]; simpa [regAddr] using hdob
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
    MpnAddPrototype.mpnAddN_loop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · -- Connect `body` at `fuel` to the loop run on `s0`.  The prelude
    -- `cf := 0` runs via the straight-line catch-all arm (no fuel drop),
    -- so `body` at `fuel` equals the loop `[Cwhile…]` at `fuel` on `s0`.
    obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hexec0 : execInstr s
        (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0))
        = some s0 := by
      simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
        show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
    have hbody : bignumExecFuel emptyRegistry (F + 1) body s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody] s0 := by
      -- View `body` (defeq) with the *local* `vr` Cassgn so `hexec0` fires.
      show bignumExecFuel emptyRegistry (F + 1)
          (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0)
            :: [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBody]) s = _
      simp only [bignumExecFuel, hexec0]
    rw [hF]
    show bignumExecFuel emptyRegistry (F + 1) body s = some s'
    rw [hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem; simpa [regAddr] using hs'_mem
  · exact hs'_cf
  · intro bb hbb
    have := hs'_frame bb (by rw [hra0 "op" (by decide)]; simpa [regAddr] using hbb)
    rw [this, hmem0]

/-- The emitted `mpnSubNFd.body` run, exposing the memory frame.  Mirror of
    `addN_body_run_frame` for the subtract kernel (used by the diff-sign
    branches, where the top output slot must stay zero). -/
theorem subN_body_run_frame
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
    ∃ s', bignumExecFuel emptyRegistry fuel mpnSubNFd.body s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (mpnSubN as bs false).1 ∧
      s'.regs "cf" = BitVec.ofNat 64 (borrowNat (mpnSubN as bs false).2) ∧
      (∀ bb, MemoryModel.Disjoint
            (MemoryModel.range bb 8)
            (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * as.length)) →
          load64Mem s'.mem bb = load64Mem s.mem bb) := by
  set s0 : BignumState := setReg s "cf" 0 with hs0
  have hmem0 : s0.mem = s.mem := by rw [hs0]; rfl
  have hcf0 : s0.regs "cf" = BitVec.ofNat 64 (if false then 1 else 0) := by
    rw [hs0]; simp [setReg]
  have hreg0 : ∀ x, x ≠ "cf" → s0.regs x = s.regs x := by
    intro x hx; rw [hs0]; simp [setReg, hx]
  have hra0 : ∀ x, x ≠ "cf" → regAddr s0 x = regAddr s x := by
    intro x hx; simp only [regAddr, hreg0 x hx]
  have hn0' : s0.regs "n" = BitVec.ofNat 64 as.length := by
    rw [hreg0 "n" (by decide), hn]
  have hap0 : memHoldsLimbs s0.mem (regAddr s0 "ap") as := by
    rw [hmem0, hra0 "ap" (by decide)]; simpa [regAddr] using hap
  have hbp0 : memHoldsLimbs s0.mem (regAddr s0 "bp") bs := by
    rw [hmem0, hra0 "bp" (by decide)]; simpa [regAddr] using hbp
  have hdoa0 : MemoryModel.Disjoint (MemoryModel.range (regAddr s0 "op") (8 * as.length))
      (MemoryModel.range (regAddr s0 "ap") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "ap" (by decide)]; simpa [regAddr] using hdoa
  have hdob0 : MemoryModel.Disjoint (MemoryModel.range (regAddr s0 "op") (8 * as.length))
      (MemoryModel.range (regAddr s0 "bp") (8 * as.length)) := by
    rw [hra0 "op" (by decide), hra0 "bp" (by decide)]; simpa [regAddr] using hdob
  obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 * as.length + 3 + extra :=
    ⟨fuel - (2 * as.length + 3), by omega⟩
  obtain ⟨s', hs', hs'_mem, hs'_cf, hs'_frame⟩ :=
    MpnSubPrototype.mpnSubN_loop as bs s0 false extra hlen hcf0 hn0' hap0 hbp0 hdoa0 hdob0
  refine ⟨s', ?_, ?_, ?_, ?_⟩
  · obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
    have hexec0 : execInstr s
        (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0))
        = some s0 := by
      simp only [execInstr, evalPExpr, vr, bind, Option.bind, hs0,
        show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl]
    have hbody : bignumExecFuel emptyRegistry (F + 1) bodySub s
        = bignumExecFuel emptyRegistry (F + 1)
            [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub] s0 := by
      show bignumExecFuel emptyRegistry (F + 1)
          (.Cassgn (.Lvar { var := vr "cf" }) .AT_none (.sword .U64) (.Pconst 0)
            :: [.Cwhile [] (.Papp2 (.Oneq .U64) (pv "n") (.Pconst 0)) loopBodySub]) s = _
      simp only [bignumExecFuel, hexec0]
    rw [hF]
    show bignumExecFuel emptyRegistry (F + 1) bodySub s = some s'
    rw [hbody, show F + 1 = 2 * as.length + 3 + extra from by omega]
    exact hs'
  · rw [hra0 "op" (by decide)] at hs'_mem; simpa [regAddr] using hs'_mem
  · exact hs'_cf
  · intro bb hbb
    have := hs'_frame bb (by rw [hra0 "op" (by decide)]; simpa [regAddr] using hbb)
    rw [this, hmem0]

/-! ### §8.0b  Carry-slot address arithmetic

The same-sign branch computes `op_top := op + 8·n` via three register
doublings (`n → 2n → 4n → 8n`) then `+ op`, since `evalPExpr` has no
`Omul`.  The resulting register value is `8·(ofNat |a|) + op_reg`, and we
must identify the `Lmem` store address `UInt64.ofNat op_top.toNat` with the
carry slot `UInt64.ofNat op_reg.toNat + UInt64.ofNat (8·|a|)` — the limb at
index `|a|` of the output window. -/

/-- The doubled-then-summed register value `(((n+n)+(n+n))+((n+n)+(n+n)))`
    + op = `8·n + op` resolves (as a `UInt64` address at offset 0) to the
    `|a|`-th limb slot `UInt64.ofNat op.toNat + UInt64.ofNat (8·L)`. -/
theorem op_top_resolves (opReg nReg : BitVec 64) (L : Nat)
    (hn : nReg = BitVec.ofNat 64 L) :
    UInt64.ofNat ((nReg + nReg + (nReg + nReg) + (nReg + nReg + (nReg + nReg)) + opReg
        + BitVec.ofInt 64 0).toNat)
      = UInt64.ofNat opReg.toNat + UInt64.ofNat (8 * L) := by
  have hstep : nReg + nReg + (nReg + nReg) + (nReg + nReg + (nReg + nReg)) + opReg
      + BitVec.ofInt 64 0 = opReg + BitVec.ofNat 64 (8 * L) := by
    subst hn
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    push_cast
    ring_nf
    omega
  rw [hstep]
  exact regAddr_advance_at opReg (8 * L)

/-! ### §8.0c  The same-sign branch (a) of `MpzAddJasminRefines`

Starting from a post-prelude state `s` with the dispatch's `Cif` having
already selected the same-sign (else) body, run the eight instructions of
the same-sign carry-aware add and land the `|a|+1`-limb `addMagFull a b`
at `op` with `s_r := s_a`. -/

/-- The same-sign branch body, run as a flat list, lands the carry-extended
    magnitude.  `s_a = s_b` (so `signedAdd (sa,a) (sb,b) = (sa, addMagFull
    a b)`); the body adds the magnitudes (low `|a|` limbs via the verified
    kernel) and stores the carry-out at the `|a|`-th slot. -/
theorem sameSign_branch_run
    (s : BignumState) (a b : List (BitVec 64)) (fuel : Nat)
    (hlen : a.length = b.length)
    (hfit : 8 * (a.length + 1) ≤ 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b)
    (hres : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0))
    (hdoa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hdoa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)))
    (hfuel : fuel > 2 * a.length + 3) :
    ∃ s',
      bignumExecFuel (signedRegistry a.length) fuel
        [ addNCallCarry
        , regCopy "op_top" "n"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op"
        , .Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
            .AT_none (.sword .U64) (pv "cf_out")
        , regCopy "s_r" "s_a" ] s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) (addMagFull a b) ∧
      s'.regs "s_r" = s.regs "s_a" := by
  obtain ⟨F, hF⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  -- The callee init state for the `mpn_add_n_cf` Ccall.
  set ci : BignumState :=
    { regs := fun name =>
        match mpnAddNFdCarry.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
            : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s.mem } with hci
  have hci_op : ci.regs "op" = s.regs "op" := by rw [hci]; rfl
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; rfl
  have hci_bp : ci.regs "bp" = s.regs "bp" := by rw [hci]; rfl
  have hci_n : ci.regs "n" = s.regs "n" := by rw [hci]; rfl
  have hci_mem : ci.mem = s.mem := by rw [hci]
  -- Shrink the `(L+1)`-window disjointness to the `L`-window the kernel needs.
  have hshrink : ∀ (R : UInt64) (m : Nat), MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range R m) → MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length))
      (MemoryModel.range R m) := by
    intro R m hd
    refine disjoint_mono (fun x hx => ?_) (fun x hx => hx) hd
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, by omega, rfl⟩
  have hci_vn : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci_n]; exact hn
  have hci_ha : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  have hci_hb : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "bp").toNat) b := by
    rw [hci_mem, hci_bp]; exact hb
  have hci_doa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]; exact hshrink _ _ hdoa_ap
  have hci_dob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "bp").toNat) (8 * a.length)) := by
    rw [hci_op, hci_bp]
    have := hshrink (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length) hdoa_bp
    rw [← hlen] at this
    exact this
  -- Run the carry-add kernel body on `ci` (frame-aware), lifted to emptyRegistry.
  obtain ⟨cf, hcf_run, hcf_mem, hcf_cf, hcf_frame⟩ :=
    addN_body_run_frame ci a b F hlen hci_vn hci_ha hci_hb hci_doa hci_dob (by omega)
  rw [hci_op] at hcf_mem hcf_frame
  -- Lift the callee run to `signedRegistry a.length` (body is Ccall-free).
  have hcf_run_signed : bignumExecFuel (signedRegistry a.length) F mpnAddNFdCarry.body ci
      = some cf := by
    rw [bignumExecFuel_registry_irrel (signedRegistry a.length) F mpnAddNFdCarry.body ci
        mpnAddNFdCarry_body_noCcall]
    exact hcf_run
  -- Post-Ccall caller state: mem inherits `cf.mem`, `cf_out := cf.regs "cf"`.
  set sCall : BignumState := setReg { s with mem := cf.mem } "cf_out" (cf.regs "cf") with hsCall
  -- Step the Ccall arm of bignumExecFuel.
  have hargs : ([(pv "op"), (pv "ap"), (pv "bp"), (pv "n")] : List PExpr).mapM (evalPExpr s)
      = some [s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"] := by
    simp only [List.mapM, List.mapM.loop, pv, vr, evalPExpr, bind, Option.bind,
               List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rfl
  -- The whole eight-instruction run reduces to the 7 straight-line steps on sCall.
  have hcall_step : bignumExecFuel (signedRegistry a.length) (F + 1)
      (addNCallCarry ::
        [ regCopy "op_top" "n"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op"
        , .Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
            .AT_none (.sword .U64) (pv "cf_out")
        , regCopy "s_r" "s_a" ]) s
      = bignumExecFuel (signedRegistry a.length) (F + 1)
        [ regCopy "op_top" "n"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op_top"
        , regBin "op_top" (.Oadd .U64) "op"
        , .Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
            .AT_none (.sword .U64) (pv "cf_out")
        , regCopy "s_r" "s_a" ] sCall := by
    show bignumExecFuel (signedRegistry a.length) (F + 1)
        (.Ccall .DoNotInline [.Lvar { var := vr "cf_out" }] { name := "mpn_add_n_cf" }
          [pv "op", pv "ap", pv "bp", pv "n"] :: _) s = _
    rw [bignumExecFuel, signedRegistry_addNCarry a.length, hargs]
    -- callee init = ci; run it; bind cf_out.
    show (match bignumExecFuel (signedRegistry a.length) F mpnAddNFdCarry.body ci with
          | none => none
          | some calleeFinal =>
            if ([.Lvar { var := vr "cf_out" }] : List LVal).isEmpty then _
            else
              match bindResults { s with mem := calleeFinal.mem } calleeFinal
                  [.Lvar { var := vr "cf_out" }] mpnAddNFdCarry.results with
              | none => none
              | some s' => bignumExecFuel (signedRegistry a.length) (F + 1) _ s') = _
    rw [hcf_run_signed]
    simp only [List.isEmpty_cons, if_false]
    show (match bindResults { s with mem := cf.mem } cf [.Lvar { var := vr "cf_out" }]
            mpnAddNFdCarry.results with
          | none => none
          | some s' => bignumExecFuel (signedRegistry a.length) (F + 1) _ s') = _
    have hbind : bindResults { s with mem := cf.mem } cf [.Lvar { var := vr "cf_out" }]
        mpnAddNFdCarry.results = some sCall := by
      show bindResults { s with mem := cf.mem } cf [.Lvar { var := vr "cf_out" }]
          [{ var := vr "cf" }] = some sCall
      simp only [bindResults, bindResult, vr, bind, Option.bind, hsCall]
    rw [hbind]
  -- Frame facts for sCall (cf_out is a fresh register, distinct from op/n/s_a).
  have hsCall_mem : sCall.mem = cf.mem := by rw [hsCall]; rfl
  have hsCall_n : sCall.regs "n" = s.regs "n" := by rw [hsCall]; simp [setReg]
  have hsCall_op : sCall.regs "op" = s.regs "op" := by rw [hsCall]; simp [setReg]
  have hsCall_sa : sCall.regs "s_a" = s.regs "s_a" := by rw [hsCall]; simp [setReg]
  have hsCall_cfout : sCall.regs "cf_out" = cf.regs "cf" := by rw [hsCall]; simp [setReg]
  -- The op_top-computation final value (8·n + op), as a register value.
  set nv : BitVec 64 := s.regs "n" with hnv
  set opv : BitVec 64 := s.regs "op" with hopv
  set topVal : BitVec 64 :=
    nv + nv + (nv + nv) + (nv + nv + (nv + nv)) + opv with htopVal
  -- The address of the carry slot, `op + 8·|a|`.
  have htop_addr : UInt64.ofNat (topVal + BitVec.ofInt 64 0).toNat
      = UInt64.ofNat opv.toNat + UInt64.ofNat (8 * a.length) := by
    rw [htopVal]; exact op_top_resolves opv nv a.length hn
  -- Run the seven straight-line instructions on sCall.  `sFinal` is the
  -- concrete chained state (defined to match the seven `setReg`/`storeMem`
  -- steps below so the run closes by reflexivity).
  have hrun7 : ∃ sFinal,
      memHoldsLimbs sFinal.mem (UInt64.ofNat (s.regs "op").toNat) (addMagFull a b) ∧
      sFinal.regs "s_r" = s.regs "s_a" ∧
      bignumExecFuel (signedRegistry a.length) (F + 1)
      [ regCopy "op_top" "n"
      , regBin "op_top" (.Oadd .U64) "op_top"
      , regBin "op_top" (.Oadd .U64) "op_top"
      , regBin "op_top" (.Oadd .U64) "op_top"
      , regBin "op_top" (.Oadd .U64) "op"
      , .Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
          .AT_none (.sword .U64) (pv "cf_out")
      , regCopy "s_r" "s_a" ] sCall = some sFinal := by
    -- Step the seven straight-line Cassgns.  Each runs via the catch-all arm
    -- (no fuel drop), so we unfold `bignumExecFuel` seven times and reduce
    -- each `execInstr`.
    have e1 : execInstr sCall (regCopy "op_top" "n")
        = some (setReg sCall "op_top" nv) := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hsCall_n, hnv]
    set s1 := setReg sCall "op_top" nv with hs1
    have h1op : s1.regs "op_top" = nv := by rw [hs1]; simp [setReg]
    have h1opr : s1.regs "op" = opv := by rw [hs1]; simp [setReg, hsCall_op, hopv]
    have e2 : execInstr s1 (regBin "op_top" (.Oadd .U64) "op_top")
        = some (setReg s1 "op_top" (nv + nv)) := by
      simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind, h1op]
    set s2 := setReg s1 "op_top" (nv + nv) with hs2
    have h2op : s2.regs "op_top" = nv + nv := by rw [hs2]; simp [setReg]
    have h2opr : s2.regs "op" = opv := by rw [hs2]; simp [setReg, h1opr]
    have e3 : execInstr s2 (regBin "op_top" (.Oadd .U64) "op_top")
        = some (setReg s2 "op_top" (nv + nv + (nv + nv))) := by
      simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind, h2op]
    set s3 := setReg s2 "op_top" (nv + nv + (nv + nv)) with hs3
    have h3op : s3.regs "op_top" = nv + nv + (nv + nv) := by rw [hs3]; simp [setReg]
    have h3opr : s3.regs "op" = opv := by rw [hs3]; simp [setReg, h2opr]
    have e4 : execInstr s3 (regBin "op_top" (.Oadd .U64) "op_top")
        = some (setReg s3 "op_top" (nv + nv + (nv + nv) + (nv + nv + (nv + nv)))) := by
      simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind, h3op]
    set s4 := setReg s3 "op_top" (nv + nv + (nv + nv) + (nv + nv + (nv + nv))) with hs4
    have h4op : s4.regs "op_top" = nv + nv + (nv + nv) + (nv + nv + (nv + nv)) := by
      rw [hs4]; simp [setReg]
    have h4opr : s4.regs "op" = opv := by rw [hs4]; simp [setReg, h3opr]
    have e5 : execInstr s4 (regBin "op_top" (.Oadd .U64) "op")
        = some (setReg s4 "op_top" topVal) := by
      simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind, h4op, h4opr, htopVal]
    set s5 := setReg s4 "op_top" topVal with hs5
    have h5top : s5.regs "op_top" = topVal := by rw [hs5]; simp [setReg]
    have h5cfout : s5.regs "cf_out" = sCall.regs "cf_out" := by
      rw [hs5, hs4, hs3, hs2, hs1]; simp [setReg]
    have e6 : execInstr s5 (.Cassgn (.Lmem .U64 { var := vr "op_top" } (.Pconst 0))
          .AT_none (.sword .U64) (pv "cf_out"))
        = some (storeMem s5 (UInt64.ofNat (topVal + BitVec.ofInt 64 0).toNat)
            (UInt64.ofNat (sCall.regs "cf_out").toNat)) := by
      simp only [execInstr, evalPExpr, resolveAddr, pv, vr, bind, Option.bind,
        h5top, h5cfout]
    set s6 := storeMem s5 (UInt64.ofNat (topVal + BitVec.ofInt 64 0).toNat)
        (UInt64.ofNat (sCall.regs "cf_out").toNat) with hs6
    have e7 : execInstr s6 (regCopy "s_r" "s_a")
        = some (setReg s6 "s_r" (s.regs "s_a")) := by
      have h6sa : s6.regs "s_a" = s.regs "s_a" := by
        rw [hs6, storeMem]; simp only []
        rw [hs5, hs4, hs3, hs2, hs1]; simp [setReg, hsCall_sa]
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, h6sa]
    set s7 := setReg s6 "s_r" (s.regs "s_a") with hs7
    refine ⟨s7, ?_, ?_, ?_⟩
    · -- Memory: s7.mem = s6.mem = store64 cf.mem (op + 8|a|) cf_byte; the low
      -- `|a|` limbs are `(mpnAddN a b false).1` (preserved by the disjoint
      -- store), the carry slot now holds `cf_out = ofNat(carryNat …)`.
      have hs7_mem : s7.mem = s6.mem := by rw [hs7]; rfl
      have hs6_mem : s6.mem = (cf.mem).store64
          (UInt64.ofNat (topVal + BitVec.ofInt 64 0).toNat)
          (UInt64.ofNat (sCall.regs "cf_out").toNat) := by
        rw [hs6, storeMem]
        show (s5.mem).store64 _ _ = (cf.mem).store64 _ _
        rw [show s5.mem = cf.mem from by rw [hs5, hs4, hs3, hs2, hs1]; exact hsCall_mem]
      rw [hs7_mem, hs6_mem]
      -- Rewrite the store address to the carry slot `op + 8|a|`.
      rw [htop_addr, hsCall_cfout, hcf_cf]
      -- `addMagFull a b = (mpnAddN a b false).1 ++ [ofNat (carryNat …)]`.
      have hlimblen : (mpnAddN a b false).1.length = a.length :=
        mpnAddN_length a b false hlen
      have haddr_eq : UInt64.ofNat opv.toNat + UInt64.ofNat (8 * a.length)
          = UInt64.ofNat opv.toNat + UInt64.ofNat (8 * (mpnAddN a b false).1.length) := by
        rw [hlimblen]
      rw [haddr_eq]
      -- Low limbs preserved by the disjoint carry store.
      have hlowmem : memHoldsLimbs
          ((cf.mem).store64 (UInt64.ofNat opv.toNat + UInt64.ofNat (8 * (mpnAddN a b false).1.length))
            (UInt64.ofNat (BitVec.ofNat 64 (carryNat (mpnAddN a b false).2)).toNat))
          (UInt64.ofNat opv.toNat) (mpnAddN a b false).1 := by
        refine memHoldsLimbs_store64_frame cf.mem (UInt64.ofNat opv.toNat)
          (UInt64.ofNat opv.toNat + UInt64.ofNat (8 * (mpnAddN a b false).1.length)) _
          (mpnAddN a b false).1 ?_ ?_
        · -- carry slot disjoint from the low-limb window
          have hd := range_tail_head_disjoint (UInt64.ofNat opv.toNat) a.length (by omega)
          rw [← hlimblen] at hd
          exact hd
        · rw [hopv]; exact hcf_mem
      -- The full window via snoc.
      rw [addMagFull]
      refine memHoldsLimbs_snoc _ (UInt64.ofNat opv.toNat) (mpnAddN a b false).1 _ hlowmem ?_
      -- Carry-slot read-back.
      exact load64Mem_store64_same cf.mem _ _
    · rw [hs7]; simp [setReg]
    · -- Chain the seven steps to land `s7`.
      show bignumExecFuel (signedRegistry a.length) (F + 1) (regCopy "op_top" "n" :: _) sCall = _
      unfold bignumExecFuel; simp only [e1]
      unfold bignumExecFuel; simp only [← hs1, e2]
      unfold bignumExecFuel; simp only [← hs2, e3]
      unfold bignumExecFuel; simp only [← hs3, e4]
      unfold bignumExecFuel; simp only [← hs4, e5]
      unfold bignumExecFuel; simp only [← hs5, e6]
      unfold bignumExecFuel; simp only [← hs6, e7]
      unfold bignumExecFuel; rfl
  obtain ⟨sFinal, hsFinal_mem, hsFinal_sr, hsFinal_run⟩ := hrun7
  refine ⟨sFinal, ?_, hsFinal_mem, hsFinal_sr⟩
  rw [hF, hcall_step]; exact hsFinal_run

/-- `mpnCmp` produces only the canonical sentinels `{0, 1, -1}` from a
    canonical accumulator.  (`cmpStep ∈ {0,1,-1}`, and `cmpUpdate` either
    keeps the accumulator or writes `cmpStep`.) -/
theorem mpnCmp_canonical : ∀ (a b : List (BitVec 64)) (acc : BitVec 64),
    (acc = 0 ∨ acc = 1 ∨ acc = (-1 : BitVec 64)) →
    (mpnCmp a b acc = 0 ∨ mpnCmp a b acc = 1 ∨ mpnCmp a b acc = (-1 : BitVec 64)) := by
  intro a
  induction a with
  | nil => intro b acc hacc; cases b <;> simpa [mpnCmp] using hacc
  | cons x xs ih =>
    intro b acc hacc
    cases b with
    | nil => simp [mpnCmp]; exact hacc
    | cons y ys =>
      show (mpnCmp xs ys (cmpUpdate acc x y) = 0 ∨ _ ∨ _)
      refine ih ys (cmpUpdate acc x y) ?_
      by_cases hxy : x = y
      · simp only [cmpUpdate, if_pos hxy]; exact hacc
      · simp only [cmpUpdate, if_neg hxy, cmpStep]
        split
        · right; left; rfl
        · split
          · right; right; rfl
          · left; rfl

/-- From `ordOf cmp_res = compare …` plus canonicity, pin `cmp_res` to its
    sentinel value for each ordering outcome. -/
theorem cmp_res_value {cmp_res : BitVec 64}
    (hcanon : cmp_res = 0 ∨ cmp_res = 1 ∨ cmp_res = (-1 : BitVec 64))
    {n m : Nat} (hord : ordOf cmp_res = compare n m) :
    (compare n m = .gt → cmp_res = 1) ∧
    (compare n m = .lt → cmp_res = (-1 : BitVec 64)) ∧
    (compare n m = .eq → cmp_res = 0) := by
  rcases hcanon with rfl | rfl | rfl <;>
    simp only [ordOf, zero_ne_one, zero_ne_negone, negone_ne_one, if_neg, if_pos,
      reduceIte] at hord ⊢ <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp_all

/-! ### §8.0d  The diff-sign branch sub-Ccall step

A single void `Ccall mpn_sub_n(op, xn, yn, n)` (the straight or swapped
shape) computes `(mpnSubN x y false).1` into the `op`-window, preserving
the top (`|x|`-th) zero slot and the caller registers.  Parametrised by the
two operand-pointer register names so the same lemma serves both the
`gt`/`eq` (`ap`,`bp`) and `lt` (`bp`,`ap`) shapes. -/

/-- One void `Ccall mpn_sub_n(op, xn, yn, n)` step.  `x` at register `xn`,
    `y` at register `yn`, equal length `= n`; the result `(mpnSubN x y
    false).1` lands at the `op`-window, the caller registers are unchanged,
    memory outside `[op, op+8·|x|)` is framed.  Lifts `subN_body_run_frame`
    (over `emptyRegistry`) through the void Ccall arm to `signedRegistry`. -/
theorem subN_void_ccall_step
    (s : BignumState) (opn xn yn : String) (x y : List (BitVec 64)) (m : Nat)
    (hlen : x.length = y.length)
    (hn : s.regs "n" = BitVec.ofNat 64 x.length)
    (hx : memHoldsLimbs s.mem (UInt64.ofNat (s.regs xn).toNat) x)
    (hy : memHoldsLimbs s.mem (UInt64.ofNat (s.regs yn).toNat) y)
    (hdoa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs opn).toNat) (8 * x.length))
      (MemoryModel.range (UInt64.ofNat (s.regs xn).toNat) (8 * x.length)))
    (hdob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs opn).toNat) (8 * x.length))
      (MemoryModel.range (UInt64.ofNat (s.regs yn).toNat) (8 * x.length))) :
    ∃ s' fuel0, ∀ fuel, fuel0 < fuel →
      bignumExecFuel (signedRegistry m) fuel
        [.Ccall .DoNotInline [] { name := "mpn_sub_n" }
          [pv opn, pv xn, pv yn, pv "n"]] s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs opn).toNat) (mpnSubN x y false).1 ∧
      s'.regs = s.regs ∧
      (∀ bb, MemoryModel.Disjoint
            (MemoryModel.range bb 8)
            (MemoryModel.range (UInt64.ofNat (s.regs opn).toNat) (8 * x.length)) →
          load64Mem s'.mem bb = load64Mem s.mem bb) := by
  -- Callee init state.
  set ci : BignumState :=
    { regs := fun name =>
        match mpnSubNFd.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s.regs opn, s.regs xn, s.regs yn, s.regs "n"]
            : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s.mem } with hci
  have hci_op : ci.regs "op" = s.regs opn := by rw [hci]; rfl
  have hci_ap : ci.regs "ap" = s.regs xn := by rw [hci]; rfl
  have hci_bp : ci.regs "bp" = s.regs yn := by rw [hci]; rfl
  have hci_n : ci.regs "n" = s.regs "n" := by rw [hci]; rfl
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_vn : ci.regs "n" = BitVec.ofNat 64 x.length := by rw [hci_n]; exact hn
  have hci_hx : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) x := by
    rw [hci_mem, hci_ap]; exact hx
  have hci_hy : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "bp").toNat) y := by
    rw [hci_mem, hci_bp]; exact hy
  have hci_doa : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * x.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * x.length)) := by
    rw [hci_op, hci_ap]; exact hdoa
  have hci_dob : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * x.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "bp").toNat) (8 * x.length)) := by
    rw [hci_op, hci_bp]; exact hdob
  obtain ⟨cf, hcf_run, hcf_mem, _hcf_cf, hcf_frame⟩ :=
    subN_body_run_frame ci x y (2 * x.length + 3) hlen hci_vn hci_hx hci_hy
      hci_doa hci_dob (by omega)
  rw [hci_op] at hcf_mem hcf_frame
  -- Lift the callee run to signedRegistry (body is Ccall-free), at fuel `2|x|+3`.
  have hcf_run_signed : bignumExecFuel (signedRegistry m) (2 * x.length + 3) mpnSubNFd.body ci
      = some cf := by
    rw [bignumExecFuel_registry_irrel (signedRegistry m) (2 * x.length + 3) mpnSubNFd.body ci
        mpnSubNFd_body_noCcall]
    exact hcf_run
  -- The void Ccall: caller mem inherits cf.mem, regs unchanged.
  refine ⟨{ s with mem := cf.mem }, 2 * x.length + 3, fun fuel hfuel => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  have hargs : ([pv opn, pv xn, pv yn, pv "n"] : List PExpr).mapM (evalPExpr s)
      = some [s.regs opn, s.regs xn, s.regs yn, s.regs "n"] := by
    simp only [List.mapM, List.mapM.loop, pv, vr, evalPExpr, bind, Option.bind,
               List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rfl
  refine ⟨?_, ?_, rfl, ?_⟩
  · show bignumExecFuel (signedRegistry m) (F + 1)
        (.Ccall .DoNotInline [] { name := "mpn_sub_n" } [pv opn, pv xn, pv yn, pv "n"] :: []) s = _
    rw [bignumExecFuel, signedRegistry_subN m, hargs]
    -- callee init = ci; run it (bumped to fuel F via mono); void path.
    have hcf_run_F : bignumExecFuel (signedRegistry m) F mpnSubNFd.body ci = some cf := by
      obtain ⟨e, rfl⟩ : ∃ e, F = (2 * x.length + 3) + e := ⟨F - (2 * x.length + 3), by omega⟩
      exact bignumExecFuel_mono (signedRegistry m) (2 * x.length + 3) e mpnSubNFd.body ci cf
        hcf_run_signed
    show (match bignumExecFuel (signedRegistry m) F mpnSubNFd.body ci with
          | none => none
          | some calleeFinal =>
            if ([] : List LVal).isEmpty then
              bignumExecFuel (signedRegistry m) (F + 1) [] { s with mem := calleeFinal.mem }
            else _) = _
    rw [hcf_run_F]
    simp only [List.isEmpty_nil, if_true]
    rw [bignumExecFuel]
  · show memHoldsLimbs cf.mem (UInt64.ofNat (s.regs opn).toNat) (mpnSubN x y false).1
    exact hcf_mem
  · intro bb hbb
    show load64Mem cf.mem bb = load64Mem s.mem bb
    rw [hcf_frame bb hbb, hci_mem]

/-- One non-void `Ccall mpn_compare_r(ap, bp, n) -> cmp_res` step.  Binds
    the callee's `result` register (= `mpnCmp a b 0`, decoding under `ordOf`
    to `compare (toNat a) (toNat b)`) into the caller's `cmp_res` register;
    memory and all other caller registers are unchanged.  Lifts
    `MpnCompareJasminRefines_ordering` (over `emptyRegistry`) through the
    non-void Ccall arm to `signedRegistry`. -/
theorem compareResult_ccall_step
    (s : BignumState) (a b : List (BitVec 64)) (m : Nat)
    (hlen : a.length = b.length)
    (hwf : a.length < 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b) :
    ∃ s' fuel0, ∀ fuel, fuel0 < fuel →
      bignumExecFuel (signedRegistry m) fuel [compareCallResult] s = some s' ∧
      s'.mem = s.mem ∧
      (∀ x, x ≠ "cmp_res" → s'.regs x = s.regs x) ∧
      s'.regs "cmp_res" = mpnCmp a b 0 := by
  -- Callee init state.
  set ci : BignumState :=
    { regs := fun name =>
        match mpnCompareFdResult.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s.regs "ap", s.regs "bp", s.regs "n"]
            : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s.mem } with hci
  have hci_ap : ci.regs "ap" = s.regs "ap" := by rw [hci]; rfl
  have hci_bp : ci.regs "bp" = s.regs "bp" := by rw [hci]; rfl
  have hci_n : ci.regs "n" = s.regs "n" := by rw [hci]; rfl
  have hci_mem : ci.mem = s.mem := by rw [hci]
  have hci_vn : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci_n]; exact hn
  have hci_ha : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact ha
  have hci_hb : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "bp").toNat) b := by
    rw [hci_mem, hci_bp]; exact hb
  obtain ⟨cf, hcf_run, hcf_ord⟩ :=
    MpnCompareJasminRefines ci a b (2 * a.length + 3) hlen hwf hci_vn
      hci_ha hci_hb (by omega)
  -- Lift the callee run to signedRegistry (compare body is Ccall-free).
  have hcf_run_signed : bignumExecFuel (signedRegistry m) (2 * a.length + 3)
      mpnCompareFdResult.body ci = some cf := by
    rw [bignumExecFuel_registry_irrel (signedRegistry m) (2 * a.length + 3)
        mpnCompareFdResult.body ci mpnCompareFdResult_body_noCcall]
    exact hcf_run
  -- The non-void Ccall binds `cmp_res := cf.regs "result"`.
  set sCall : BignumState := setReg { s with mem := cf.mem } "cmp_res" (cf.regs "result")
    with hsCall
  -- Compare reads only (`bodyCmp` performs no store), so `cf.mem = ci.mem = s.mem`.
  refine ⟨sCall, 2 * a.length + 3, fun fuel hfuel => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F, fuel = F + 1 := ⟨fuel - 1, by omega⟩
  have hcf_run_F : bignumExecFuel (signedRegistry m) F mpnCompareFdResult.body ci = some cf := by
    obtain ⟨e, rfl⟩ : ∃ e, F = (2 * a.length + 3) + e := ⟨F - (2 * a.length + 3), by omega⟩
    exact bignumExecFuel_mono (signedRegistry m) (2 * a.length + 3) e mpnCompareFdResult.body ci cf
      hcf_run_signed
  have hargs : ([pv "ap", pv "bp", pv "n"] : List PExpr).mapM (evalPExpr s)
      = some [s.regs "ap", s.regs "bp", s.regs "n"] := by
    simp only [List.mapM, List.mapM.loop, pv, vr, evalPExpr, bind, Option.bind,
               List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rfl
  -- `cf.mem = s.mem`: compare body does no store.  Derive from MpnCompare's frame?
  -- The bridge does not export mem-invariance, but `bodyCmp` is read-only.  We
  -- get it from the registry-irrel run being on `ci` (mem = s.mem) and the fact
  -- that `mpnCompareFd.body` never writes (its only `Cassgn` targets are `Lvar`s).
  -- We instead expose `cf.mem` directly via the run on `ci` below.
  have hrun_eq : bignumExecFuel (signedRegistry m) (F + 1) [compareCallResult] s
      = some sCall := by
    show bignumExecFuel (signedRegistry m) (F + 1)
        (.Ccall .DoNotInline [.Lvar { var := vr "cmp_res" }] { name := "mpn_compare_r" }
          [pv "ap", pv "bp", pv "n"] :: []) s = _
    rw [bignumExecFuel, signedRegistry_compareResult m, hargs]
    show (match bignumExecFuel (signedRegistry m) F mpnCompareFdResult.body ci with
          | none => none
          | some calleeFinal =>
            if ([.Lvar { var := vr "cmp_res" }] : List LVal).isEmpty then _
            else
              match bindResults { s with mem := calleeFinal.mem } calleeFinal
                  [.Lvar { var := vr "cmp_res" }] mpnCompareFdResult.results with
              | none => none
              | some s' => bignumExecFuel (signedRegistry m) (F + 1) [] s') = _
    rw [hcf_run_F]
    have hbind : bindResults { s with mem := cf.mem } cf [.Lvar { var := vr "cmp_res" }]
        mpnCompareFdResult.results = some sCall := by
      show bindResults { s with mem := cf.mem } cf [.Lvar { var := vr "cmp_res" }]
          [{ var := vr "result" }] = some sCall
      simp only [bindResults, bindResult, vr, bind, Option.bind, hsCall]
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, hbind, bignumExecFuel]
  -- The compare body never writes memory, so `cf.mem = ci.mem = s.mem`.
  have hcf_mem : cf.mem = s.mem := by
    have := compareFd_mem_invariant (signedRegistry m) F ci cf hcf_run_F
    rw [this, hci_mem]
  refine ⟨hrun_eq, ?_, ?_, ?_⟩
  · rw [hsCall]; simp [setReg, hcf_mem]
  · intro x hx; rw [hsCall]; simp [setReg, hx]
  · have hsr : sCall.regs "cmp_res" = cf.regs "result" := by rw [hsCall]; simp [setReg]
    rw [hsr]; exact hcf_ord

/-- A `0`/`1` register equals the `ofNat`-encoding of its decoded sign bit. -/
theorem reg01_eq_ofNat_decide (r : BitVec 64) (h : r = 0 ∨ r = 1) :
    r = BitVec.ofNat 64 (if (decide (r = 1)) then 1 else 0) := by
  rcases h with rfl | rfl <;> simp

/-- Running a single `Cif` whose guard evaluates to `0` (false) reduces to
    running the else-branch, then continuing with the (empty) tail.  Built
    forward, avoiding `simp` stepping the concrete branch body. -/
theorem cif_else_run (reg : BignumRegistry) (F : Nat) (cond : PExpr)
    (ct ce : List InstrR) (s s' : BignumState)
    (hg : evalPExpr s cond = some 0)
    (hrun : bignumExecFuel reg F ce s = some s') :
    bignumExecFuel reg (F + 1) [.Cif cond ct ce] s = some s' := by
  rw [bignumExecFuel]
  simp only [hg, show ((0 : BitVec 64) != 0) = false from by decide, Bool.false_eq_true,
    if_false, hrun]
  rw [bignumExecFuel]

/-- Running a single `Cif` whose guard evaluates to a nonzero value reduces
    to running the then-branch. -/
theorem cif_then_run (reg : BignumRegistry) (F : Nat) (cond : PExpr)
    (ct ce : List InstrR) (s s' : BignumState) (v : BitVec 64) (hv : v ≠ 0)
    (hg : evalPExpr s cond = some v)
    (hrun : bignumExecFuel reg F ct s = some s') :
    bignumExecFuel reg (F + 1) [.Cif cond ct ce] s = some s' := by
  have hvtrue : (v != 0) = true := by simp only [bne_iff_ne]; exact hv
  rw [bignumExecFuel]
  simp only [hg, hvtrue, if_true, hrun]
  rw [bignumExecFuel]

/-! ### §8.0e  The diff-sign branch of `MpzAddJasminRefines`

The compare-then-subtract case analysis (operands of opposite sign reduce
to larger-minus-smaller) is the remaining step toward proving
`MpzAddJasminRefines` as a theorem.  Its equal-magnitude sub-case runs the
void `mpn_sub_n` Ccall and sets `s_r := 0`; the strictly-ordered sub-cases
select the larger-minus-smaller subtraction (with sign copied from the
larger operand).  These rely on the `cif_else_run` / `cif_then_run`
reductions above. -/

/-- The diff-sign branch body, run as a flat two-instruction list
    `[compareCallResult, Cif (cmp_res != 0) <neBody> <eqBody>]`, lands the
    different-sign `signedAdd` result.  Splits on `compare (toNat a)
    (toNat b)` (which `mpnCompare_eq_compare` ties to `cmp_res`):
    `gt` ⇒ straight `mpn_sub_n(op,ap,bp)`, `s_r := s_a`;
    `lt` ⇒ swapped `mpn_sub_n(op,bp,ap)`, `s_r := s_b`;
    `eq` ⇒ straight `mpn_sub_n(op,ap,bp)` (writes zeros), `s_r := 0`.
    Each sub-case routes through `subN_void_ccall_step` and `mpnSubN_exact`,
    so the `|a|`-limb result fits exactly and the top zero slot survives. -/
theorem diffSign_branch_run
    (s : BignumState) (a b : List (BitVec 64))
    (hlen : a.length = b.length)
    (hfit : 8 * (a.length + 1) ≤ 2 ^ 64)
    (hsign : (s.regs "s_a" = 1) ≠ (s.regs "s_b" = 1))
    (hsa : s.regs "s_a" = 0 ∨ s.regs "s_a" = 1)
    (hsb : s.regs "s_b" = 0 ∨ s.regs "s_b" = 1)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b)
    (hres : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0))
    (hdoa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hdoa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length))) :
    ∃ s' fuel,
      bignumExecFuel (signedRegistry a.length) fuel
        [ compareCallResult
        , .Cif (.Papp2 (.Oneq .U64) (pv "cmp_res") (.Pconst 0))
            [ regCopy "rmone" "cmp_res"
            , binImm "rmone" (.Osub .U64) 1
            , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
                [ subNCallSwapped, regCopy "s_r" "s_b" ]
                [ subNCall, regCopy "s_r" "s_a" ] ]
            [ subNCall, setImm "s_r" 0 ] ] s = some s' ∧
      let saBool : Bool := s.regs "s_a" = 1
      let sbBool : Bool := s.regs "s_b" = 1
      let r := signedAdd (saBool, a) (sbBool, b)
      ∃ (k : Nat),
        r.2.length + k = a.length + 1 ∧
        memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat)
          (r.2 ++ List.replicate k (0 : BitVec 64)) ∧
        s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0) := by
  -- The signed result in the diff-sign branch.
  set saBool : Bool := decide (s.regs "s_a" = 1) with hsaBool
  set sbBool : Bool := decide (s.regs "s_b" = 1) with hsbBool
  -- `signedAdd (saBool,a) (sbBool,b)` reduces to its else-branch (signs differ).
  have hsign' : saBool ≠ sbBool := by
    rw [hsaBool, hsbBool, ne_eq, decide_eq_decide, iff_iff_eq]; exact hsign
  -- Disjointness shrunk to the `|a|`-window (the sub kernels need `8*|a|`).
  have hshrink : ∀ (R : UInt64) (m : Nat), MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range R m) → MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length))
      (MemoryModel.range R m) := by
    intro R m hd
    refine disjoint_mono (fun x hx => ?_) (fun x hx => hx) hd
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, by omega, rfl⟩
  have hdoa_ap' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) :=
    hshrink _ _ hdoa_ap
  have hdoa_bp' : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * a.length)) := by
    have := hshrink _ _ hdoa_bp; rw [← hlen] at this; exact this
  have hwf : a.length < 2 ^ 64 := by omega
  -- Step 1: the compare Ccall.  After it, `cmp_res = mpnCmp a b 0`, memory
  -- unchanged, all other registers framed.
  obtain ⟨sc, cf0, hcmp⟩ :=
    compareResult_ccall_step s a b a.length hlen hwf hn ha hb
  -- `ordOf cmp_res = compare (toNat a) (toNat b)` and `cmp_res ∈ {0,1,-1}`.
  -- We obtain the run facts at a concrete fuel `cf0 + 1` later (the inner
  -- branch needs more), so derive the post-compare invariants now.
  have hcmp_facts := hcmp (cf0 + 1) (by omega)
  obtain ⟨_, hsc_mem, hsc_reg, hsc_cmp⟩ := hcmp_facts
  -- The post-compare state `sc` preserves operands/op/n and the signs.
  have hsc_ap : sc.regs "ap" = s.regs "ap" := hsc_reg "ap" (by decide)
  have hsc_bp : sc.regs "bp" = s.regs "bp" := hsc_reg "bp" (by decide)
  have hsc_op : sc.regs "op" = s.regs "op" := hsc_reg "op" (by decide)
  have hsc_n : sc.regs "n" = s.regs "n" := hsc_reg "n" (by decide)
  have hsc_sa : sc.regs "s_a" = s.regs "s_a" := hsc_reg "s_a" (by decide)
  have hsc_sb : sc.regs "s_b" = s.regs "s_b" := hsc_reg "s_b" (by decide)
  -- Operand/result memHoldsLimbs at `sc` (mem unchanged).
  have hsc_ha : memHoldsLimbs sc.mem (UInt64.ofNat (sc.regs "ap").toNat) a := by
    rw [hsc_mem, hsc_ap]; exact ha
  have hsc_hb : memHoldsLimbs sc.mem (UInt64.ofNat (sc.regs "bp").toNat) b := by
    rw [hsc_mem, hsc_bp]; exact hb
  have hsc_vn : sc.regs "n" = BitVec.ofNat 64 a.length := by rw [hsc_n]; exact hn
  -- `cmp_res` is one of the three sentinels and decodes to `compare`.
  have hcanon : sc.regs "cmp_res" = 0 ∨ sc.regs "cmp_res" = 1
      ∨ sc.regs "cmp_res" = (-1 : BitVec 64) := by
    rw [hsc_cmp]; exact mpnCmp_canonical a b 0 (by left; rfl)
  have hord : ordOf (sc.regs "cmp_res") = compare (toNat a) (toNat b) := by
    rw [hsc_cmp]
    have := ordOf_mpnCmp a b hlen 0
    simp only [ordOf] at this ⊢
    rw [this]
    by_cases heq : toNat a = toNat b
    · simp [heq]
    · simp [heq]
  obtain ⟨hval_gt, hval_lt, hval_eq⟩ := cmp_res_value hcanon hord
  -- Disjointness at `sc` for the straight (ap/bp) and swapped (bp/ap) calls.
  have hsc_doa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (sc.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (sc.regs "ap").toNat) (8 * a.length)) := by
    rw [hsc_op, hsc_ap]; exact hdoa_ap'
  have hsc_doa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (sc.regs "op").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (sc.regs "bp").toNat) (8 * a.length)) := by
    rw [hsc_op, hsc_bp]; exact hdoa_bp'
  -- The compare-Ccall step at fuel `cf0 + 1`.
  obtain ⟨hcmp_run, _, _, _⟩ := hcmp (cf0 + 1) (by omega)
  -- `signedAdd` reduces to its else-branch (signs differ), matching on the
  -- compare outcome.  We produce the final state for each branch from `sc`.
  have hsa_red : (signedAdd (saBool, a) (sbBool, b))
      = match mpnCompare a b with
        | .eq => (false, (mpnSubN a b false).1)
        | .gt => (saBool, (mpnSubN a b false).1)
        | .lt => (sbBool, (mpnSubN b a false).1) := by
    rw [signedAdd, if_neg hsign']; rfl
  -- `mpnCompare a b = compare (toNat a) (toNat b)`.
  have hmpncmp : mpnCompare a b = compare (toNat a) (toNat b) :=
    mpnCompare_eq_compare a b hlen
  -- The inner-Cif run from `sc`: case split on the compare outcome.
  -- We prove `∃ sFinal f2, run [Cif…] sc = some sFinal ∧ <spec at sFinal>`,
  -- then compose with the compare step via `bignumExecFuel_seq`.
  suffices hinner : ∃ (sFinal : BignumState) (f2 : Nat),
      bignumExecFuel (signedRegistry a.length) f2
        [ .Cif (.Papp2 (.Oneq .U64) (pv "cmp_res") (.Pconst 0))
            [ regCopy "rmone" "cmp_res"
            , binImm "rmone" (.Osub .U64) 1
            , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
                [ subNCallSwapped, regCopy "s_r" "s_b" ]
                [ subNCall, regCopy "s_r" "s_a" ] ]
            [ subNCall, setImm "s_r" 0 ] ] sc = some sFinal ∧
      (∃ (k : Nat),
        (signedAdd (saBool, a) (sbBool, b)).2.length + k = a.length + 1 ∧
        memHoldsLimbs sFinal.mem (UInt64.ofNat (s.regs "op").toNat)
          ((signedAdd (saBool, a) (sbBool, b)).2 ++ List.replicate k (0 : BitVec 64)) ∧
        sFinal.regs "s_r" = BitVec.ofNat 64 (if (signedAdd (saBool, a) (sbBool, b)).1 then 1 else 0)) by
    obtain ⟨sFinal, f2, hinner_run, hinner_spec⟩ := hinner
    refine ⟨sFinal, (cf0 + 1) + f2, ?_, ?_⟩
    · have := bignumExecFuel_seq (signedRegistry a.length) (cf0 + 1) f2
        [compareCallResult]
        [ .Cif (.Papp2 (.Oneq .U64) (pv "cmp_res") (.Pconst 0))
            [ regCopy "rmone" "cmp_res"
            , binImm "rmone" (.Osub .U64) 1
            , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
                [ subNCallSwapped, regCopy "s_r" "s_b" ]
                [ subNCall, regCopy "s_r" "s_a" ] ]
            [ subNCall, setImm "s_r" 0 ] ]
        s sc sFinal hcmp_run hinner_run
      simpa using this
    · exact hinner_spec
  -- Now prove the inner run by case analysis on `compare (toNat a) (toNat b)`.
  rw [hsa_red, hmpncmp]
  rcases hcompare : compare (toNat a) (toNat b) with _ | _ | _
  · -- lt case: cmp_res = -1 ⇒ then-branch, inner then (swapped sub, s_r := s_b).
    have hcr : sc.regs "cmp_res" = (-1 : BitVec 64) := hval_lt hcompare
    -- Disjointness at `sc` rewritten for the swapped (bp/ap) sub at width `8·|b|`.
    have hsc_doa_bp_b : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (sc.regs "op").toNat) (8 * b.length))
        (MemoryModel.range (UInt64.ofNat (sc.regs "bp").toNat) (8 * b.length)) := by
      rw [← hlen]; exact hsc_doa_bp
    have hsc_doa_ap_b : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (sc.regs "op").toNat) (8 * b.length))
        (MemoryModel.range (UInt64.ofNat (sc.regs "ap").toNat) (8 * b.length)) := by
      rw [← hlen]; exact hsc_doa_ap
    have hsc_vn_b : sc.regs "n" = BitVec.ofNat 64 b.length := by rw [← hlen]; exact hsc_vn
    -- The two register prep steps: rmone := cmp_res = -1; rmone := rmone - 1 = -2 ≠ 0.
    set s1 : BignumState := setReg sc "rmone" (sc.regs "cmp_res") with hs1
    have hs1_rmone : s1.regs "rmone" = (-1 : BitVec 64) := by rw [hs1]; simp [setReg, hcr]
    set s2 : BignumState := setReg s1 "rmone" (s1.regs "rmone" - BitVec.ofInt 64 1) with hs2
    have hs2_rmone : s2.regs "rmone" = ((-1 : BitVec 64) - BitVec.ofInt 64 1) := by
      rw [hs2]; simp [setReg, hs1_rmone]
    have hs2_rmone_ne : s2.regs "rmone" ≠ (0 : BitVec 64) := by rw [hs2_rmone]; decide
    have hs2_mem : s2.mem = sc.mem := by rw [hs2, hs1]; rfl
    have hs2_ap : s2.regs "ap" = sc.regs "ap" := by rw [hs2, hs1]; simp [setReg]
    have hs2_bp : s2.regs "bp" = sc.regs "bp" := by rw [hs2, hs1]; simp [setReg]
    have hs2_op : s2.regs "op" = sc.regs "op" := by rw [hs2, hs1]; simp [setReg]
    have hs2_n : s2.regs "n" = sc.regs "n" := by rw [hs2, hs1]; simp [setReg]
    have hs2_sb : s2.regs "s_b" = sc.regs "s_b" := by rw [hs2, hs1]; simp [setReg]
    -- The swapped sub `mpn_sub_n(op, bp, ap, n)` on s2 lands `(mpnSubN b a false).1`.
    have hs2_vn : s2.regs "n" = BitVec.ofNat 64 b.length := by rw [hs2_n]; exact hsc_vn_b
    have hs2_hx : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "bp").toNat) b := by
      rw [hs2_mem, hs2_bp]; exact hsc_hb
    have hs2_hy : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "ap").toNat) a := by
      rw [hs2_mem, hs2_ap]; exact hsc_ha
    have hs2_doa : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * b.length))
        (MemoryModel.range (UInt64.ofNat (s2.regs "bp").toNat) (8 * b.length)) := by
      rw [hs2_op, hs2_bp]; exact hsc_doa_bp_b
    have hs2_dob : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * b.length))
        (MemoryModel.range (UInt64.ofNat (s2.regs "ap").toNat) (8 * b.length)) := by
      rw [hs2_op, hs2_ap]; exact hsc_doa_ap_b
    obtain ⟨ss, sf0, hsub⟩ :=
      subN_void_ccall_step s2 "op" "bp" "ap" b a a.length hlen.symm hs2_vn hs2_hx hs2_hy
        hs2_doa hs2_dob
    obtain ⟨hsub_run, hsub_mem, hsub_reg, _hsub_frame⟩ := hsub (sf0 + 1) (by omega)
    -- Final: s_r := s_b on ss.
    set sFinal : BignumState := setReg ss "s_r" (ss.regs "s_b") with hsFinal
    have e1 : execInstr sc (regCopy "rmone" "cmp_res") = some s1 := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs1]
    have e2 : execInstr s1 (binImm "rmone" (.Osub .U64) 1) = some s2 := by
      simp only [binImm, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs2]
    have hprep : bignumExecFuel (signedRegistry a.length) 2
        [regCopy "rmone" "cmp_res", binImm "rmone" (.Osub .U64) 1] sc = some s2 := by
      unfold bignumExecFuel; simp only [e1]
      unfold bignumExecFuel; simp only [← hs1, e2]
      unfold bignumExecFuel; rfl
    have hreg : execInstr ss (regCopy "s_r" "s_b") = some sFinal := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hsFinal]
    -- The inner then body `[subNCallSwapped, regCopy "s_r" "s_b"]` at fuel (sf0+1)+1.
    have hsub_body : bignumExecFuel (signedRegistry a.length) ((sf0 + 1) + 1)
        [subNCallSwapped, regCopy "s_r" "s_b"] s2 = some sFinal :=
      bignumExecFuel_seq (signedRegistry a.length) (sf0 + 1) 1
        [subNCallSwapped] [regCopy "s_r" "s_b"] s2 ss sFinal hsub_run (by
          show bignumExecFuel (signedRegistry a.length) 1 [regCopy "s_r" "s_b"] ss = some sFinal
          unfold bignumExecFuel; simp only [hreg]; unfold bignumExecFuel; rfl)
    -- The inner Cif (rmone != 0) at fuel (sf0+1)+1+1 → then branch (rmone ≠ 0).
    have hinner_cif : bignumExecFuel (signedRegistry a.length) ((sf0 + 1) + 1 + 1)
        [ .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ] s2 = some sFinal :=
      cif_then_run (signedRegistry a.length) ((sf0 + 1) + 1) _ _ _ s2 sFinal
        (1 : BitVec 64) (by decide)
        (by simp only [evalPExpr, pv, vr, bind, Option.bind, hs2_rmone]; decide)
        hsub_body
    -- The neBody `[regCopy, binImm] ++ [innerCif]` at fuel 2 + ((sf0+1)+1+1).
    have hneBody : bignumExecFuel (signedRegistry a.length) (2 + ((sf0 + 1) + 1 + 1))
        [ regCopy "rmone" "cmp_res"
        , binImm "rmone" (.Osub .U64) 1
        , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ] sc = some sFinal :=
      bignumExecFuel_seq (signedRegistry a.length) 2 ((sf0 + 1) + 1 + 1)
        [regCopy "rmone" "cmp_res", binImm "rmone" (.Osub .U64) 1]
        [ .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ]
        sc s2 sFinal hprep hinner_cif
    refine ⟨sFinal, (2 + ((sf0 + 1) + 1 + 1)) + 1, ?_, ?_⟩
    · -- Outer Cif (cmp_res != 0): cmp_res = -1 ≠ 0 ⇒ then-branch (neBody).
      exact cif_then_run (signedRegistry a.length) (2 + ((sf0 + 1) + 1 + 1))
        _ _ _ sc sFinal ((1 : BitVec 64)) (by decide)
        (by simp only [evalPExpr, pv, vr, bind, Option.bind, hcr]; decide)
        hneBody
    · -- Spec: result memory = (mpnSubN b a false).1 ++ replicate 1 0, s_r = s_b.
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [mpnSubN_length b a false hlen.symm, hlen]
      · -- Memory: ss.mem holds (mpnSubN b a false).1 at op, top slot still 0.
        have hsub_mem' : memHoldsLimbs ss.mem (UInt64.ofNat (s.regs "op").toNat)
            (mpnSubN b a false).1 := by
          rw [hs2_op, hsc_op] at hsub_mem; exact hsub_mem
        have hlimblen : (mpnSubN b a false).1.length = b.length :=
          mpnSubN_length b a false hlen.symm
        have htop0 : load64Mem ss.mem
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (mpnSubN b a false).1.length))
            = some (UInt64.ofNat (0 : BitVec 64).toNat) := by
          have hframe := _hsub_frame
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * b.length)) (by
              rw [hs2_op, hsc_op]
              exact range_tail_head_disjoint (UInt64.ofNat (s.regs "op").toNat) b.length (by omega))
          rw [hlimblen, hframe, hs2_mem, hsc_mem, ← hlen]
          have hsplit : List.replicate (a.length + 1) (0 : BitVec 64)
              = List.replicate a.length 0 ++ [0] := by rw [← List.replicate_succ']
          rw [hsplit, memHoldsLimbs_append] at hres
          obtain ⟨_, htail⟩ := hres
          simp only [List.length_replicate, memHoldsLimbs] at htail
          exact htail.1
        have := memHoldsLimbs_snoc ss.mem (UInt64.ofNat (s.regs "op").toNat)
          (mpnSubN b a false).1 (0 : BitVec 64) hsub_mem' htop0
        rw [show sFinal.mem = ss.mem from by rw [hsFinal]; rfl]
        simpa using this
      · -- s_r register = ofNat (if sbBool then 1 else 0).
        rw [show sFinal.regs "s_r" = ss.regs "s_b" from by rw [hsFinal]; simp [setReg]]
        rw [hsub_reg, hs2_sb, hsc_sb]
        rw [hsbBool]
        exact reg01_eq_ofNat_decide _ hsb
  · -- eq case: cmp_res = 0 ⇒ else-branch (straight sub, s_r := 0).
    have hcr : sc.regs "cmp_res" = 0 := hval_eq hcompare
    -- The straight sub `mpn_sub_n(op, ap, bp, n)` on sc lands `(mpnSubN a b false).1`.
    obtain ⟨ss, sf0, hsub⟩ :=
      subN_void_ccall_step sc "op" "ap" "bp" a b a.length hlen hsc_vn hsc_ha hsc_hb
        hsc_doa_ap hsc_doa_bp
    obtain ⟨hsub_run, hsub_mem, hsub_reg, _hsub_frame⟩ := hsub (sf0 + 1) (by omega)
    -- Final: s_r := 0 on ss.
    set sFinal : BignumState := setReg ss "s_r" (BitVec.ofInt 64 0) with hsFinal
    have hreg : execInstr ss (setImm "s_r" 0) = some sFinal := by
      simp only [setImm, execInstr, evalPExpr, pv, vr, bind, Option.bind, hsFinal]
    -- The else body `[subNCall, setImm "s_r" 0]` runs at fuel (sf0+1)+1.
    have hbody : bignumExecFuel (signedRegistry a.length) ((sf0 + 1) + 1)
        [subNCall, setImm "s_r" 0] sc = some sFinal :=
      bignumExecFuel_seq (signedRegistry a.length) (sf0 + 1) 1
        [subNCall] [setImm "s_r" 0] sc ss sFinal hsub_run (by
          show bignumExecFuel (signedRegistry a.length) 1 [setImm "s_r" 0] ss = some sFinal
          unfold bignumExecFuel; simp only [hreg]; unfold bignumExecFuel; rfl)
    refine ⟨sFinal, ((sf0 + 1) + 1) + 1, ?_, ?_⟩
    · -- Outer Cif (cmp_res != 0): cmp_res = 0 ⇒ else-branch (eqBody).
      exact cif_else_run (signedRegistry a.length) ((sf0 + 1) + 1) _ _ _ sc sFinal
        (by simp only [evalPExpr, pv, vr, bind, Option.bind, hcr]; decide)
        hbody
    · -- Spec: result memory = (mpnSubN a b false).1 ++ replicate 1 0, s_r = 0.
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [mpnSubN_length a b false hlen]
      · -- Memory: ss.mem holds (mpnSubN a b false).1 at op, top slot still 0.
        have hsub_mem' : memHoldsLimbs ss.mem (UInt64.ofNat (s.regs "op").toNat)
            (mpnSubN a b false).1 := by rw [hsc_op] at hsub_mem; exact hsub_mem
        have hlimblen : (mpnSubN a b false).1.length = a.length := mpnSubN_length a b false hlen
        have htop0 : load64Mem ss.mem
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (mpnSubN a b false).1.length))
            = some (UInt64.ofNat (0 : BitVec 64).toNat) := by
          have hframe := _hsub_frame
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * a.length)) (by
              rw [hsc_op]
              exact range_tail_head_disjoint (UInt64.ofNat (s.regs "op").toNat) a.length (by omega))
          rw [hlimblen]
          rw [hframe, hsc_mem]
          have hsplit : List.replicate (a.length + 1) (0 : BitVec 64)
              = List.replicate a.length 0 ++ [0] := by rw [← List.replicate_succ']
          rw [hsplit, memHoldsLimbs_append] at hres
          obtain ⟨_, htail⟩ := hres
          simp only [List.length_replicate, memHoldsLimbs] at htail
          exact htail.1
        have := memHoldsLimbs_snoc ss.mem (UInt64.ofNat (s.regs "op").toNat)
          (mpnSubN a b false).1 (0 : BitVec 64) hsub_mem' htop0
        rw [show sFinal.mem = ss.mem from by rw [hsFinal]; rfl]
        simpa using this
      · -- s_r register = ofNat 0 (= false sign).
        rw [show sFinal.regs "s_r" = BitVec.ofInt 64 0 from by rw [hsFinal]; simp [setReg]]
        rfl
  · -- gt case: cmp_res = 1 ⇒ then-branch, inner else (straight sub, s_r := s_a).
    have hcr : sc.regs "cmp_res" = 1 := hval_gt hcompare
    -- The two register prep steps: rmone := cmp_res = 1; rmone := rmone - 1 = 0.
    set s1 : BignumState := setReg sc "rmone" (sc.regs "cmp_res") with hs1
    have hs1_cmp : s1.regs "cmp_res" = sc.regs "cmp_res" := by rw [hs1]; simp [setReg]
    have hs1_rmone : s1.regs "rmone" = (1 : BitVec 64) := by rw [hs1]; simp [setReg, hcr]
    set s2 : BignumState := setReg s1 "rmone" (s1.regs "rmone" - BitVec.ofInt 64 1) with hs2
    have hs2_rmone : s2.regs "rmone" = (0 : BitVec 64) := by
      rw [hs2]; simp only [setReg, hs1_rmone]; decide
    -- s2 preserves operands/op/n/s_a/mem.
    have hs2_mem : s2.mem = sc.mem := by rw [hs2, hs1]; rfl
    have hs2_ap : s2.regs "ap" = sc.regs "ap" := by rw [hs2, hs1]; simp [setReg]
    have hs2_bp : s2.regs "bp" = sc.regs "bp" := by rw [hs2, hs1]; simp [setReg]
    have hs2_op : s2.regs "op" = sc.regs "op" := by rw [hs2, hs1]; simp [setReg]
    have hs2_n : s2.regs "n" = sc.regs "n" := by rw [hs2, hs1]; simp [setReg]
    have hs2_sa : s2.regs "s_a" = sc.regs "s_a" := by rw [hs2, hs1]; simp [setReg]
    -- The straight sub `mpn_sub_n(op, ap, bp, n)` on s2 lands `(mpnSubN a b false).1`.
    have hs2_vn : s2.regs "n" = BitVec.ofNat 64 a.length := by rw [hs2_n]; exact hsc_vn
    have hs2_hx : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "ap").toNat) a := by
      rw [hs2_mem, hs2_ap]; exact hsc_ha
    have hs2_hy : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "bp").toNat) b := by
      rw [hs2_mem, hs2_bp]; exact hsc_hb
    have hs2_doa : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * a.length))
        (MemoryModel.range (UInt64.ofNat (s2.regs "ap").toNat) (8 * a.length)) := by
      rw [hs2_op, hs2_ap]; exact hsc_doa_ap
    have hs2_dob : MemoryModel.Disjoint
        (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * a.length))
        (MemoryModel.range (UInt64.ofNat (s2.regs "bp").toNat) (8 * a.length)) := by
      rw [hs2_op, hs2_bp]; exact hsc_doa_bp
    obtain ⟨ss, sf0, hsub⟩ :=
      subN_void_ccall_step s2 "op" "ap" "bp" a b a.length hlen hs2_vn hs2_hx hs2_hy
        hs2_doa hs2_dob
    obtain ⟨hsub_run, hsub_mem, hsub_reg, _hsub_frame⟩ := hsub (sf0 + 1) (by omega)
    -- Final: s_r := s_a on ss.
    set sFinal : BignumState := setReg ss "s_r" (ss.regs "s_a") with hsFinal
    -- The two register-prep steps run at fuel 2 landing s2.
    have e1 : execInstr sc (regCopy "rmone" "cmp_res") = some s1 := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs1]
    have e2 : execInstr s1 (binImm "rmone" (.Osub .U64) 1) = some s2 := by
      simp only [binImm, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs2]
    have hprep : bignumExecFuel (signedRegistry a.length) 2
        [regCopy "rmone" "cmp_res", binImm "rmone" (.Osub .U64) 1] sc = some s2 := by
      unfold bignumExecFuel; simp only [e1]
      unfold bignumExecFuel; simp only [← hs1, e2]
      unfold bignumExecFuel; rfl
    -- The inner else body `[subNCall, regCopy "s_r" "s_a"]` runs at fuel (sf0+1)+1.
    have hreg : execInstr ss (regCopy "s_r" "s_a") = some sFinal := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hsFinal]
    have hsub_body : bignumExecFuel (signedRegistry a.length) ((sf0 + 1) + 1)
        [subNCall, regCopy "s_r" "s_a"] s2 = some sFinal :=
      bignumExecFuel_seq (signedRegistry a.length) (sf0 + 1) 1
        [subNCall] [regCopy "s_r" "s_a"] s2 ss sFinal hsub_run (by
          show bignumExecFuel (signedRegistry a.length) 1 [regCopy "s_r" "s_a"] ss = some sFinal
          unfold bignumExecFuel; simp only [hreg]; unfold bignumExecFuel; rfl)
    -- The inner Cif (rmone != 0) at fuel (sf0+1)+1+1 → else branch (rmone = 0).
    have hinner_cif : bignumExecFuel (signedRegistry a.length) ((sf0 + 1) + 1 + 1)
        [ .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ] s2 = some sFinal :=
      cif_else_run (signedRegistry a.length) ((sf0 + 1) + 1) _ _ _ s2 sFinal
        (by simp only [evalPExpr, pv, vr, bind, Option.bind, hs2_rmone]; decide)
        hsub_body
    -- The neBody `[regCopy, binImm] ++ [innerCif]` at fuel 2 + ((sf0+1)+1+1).
    have hneBody : bignumExecFuel (signedRegistry a.length) (2 + ((sf0 + 1) + 1 + 1))
        [ regCopy "rmone" "cmp_res"
        , binImm "rmone" (.Osub .U64) 1
        , .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ] sc = some sFinal :=
      bignumExecFuel_seq (signedRegistry a.length) 2 ((sf0 + 1) + 1 + 1)
        [regCopy "rmone" "cmp_res", binImm "rmone" (.Osub .U64) 1]
        [ .Cif (.Papp2 (.Oneq .U64) (pv "rmone") (.Pconst 0))
            [ subNCallSwapped, regCopy "s_r" "s_b" ]
            [ subNCall, regCopy "s_r" "s_a" ] ]
        sc s2 sFinal hprep hinner_cif
    refine ⟨sFinal, (2 + ((sf0 + 1) + 1 + 1)) + 1, ?_, ?_⟩
    · -- Outer Cif (cmp_res != 0): cmp_res = 1 ≠ 0 ⇒ then-branch (neBody).
      exact cif_then_run (signedRegistry a.length) (2 + ((sf0 + 1) + 1 + 1))
        _ _ _ sc sFinal (1 : BitVec 64) (by decide)
        (by simp only [evalPExpr, pv, vr, bind, Option.bind, hcr]; decide)
        hneBody
    · -- Spec: result memory = (mpnSubN a b false).1 ++ replicate 1 0, s_r = s_a.
      refine ⟨1, ?_, ?_, ?_⟩
      · rw [mpnSubN_length a b false hlen]
      · -- Memory: ss.mem holds (mpnSubN a b false).1 at op, top slot still 0.
        have hsub_mem' : memHoldsLimbs ss.mem (UInt64.ofNat (s.regs "op").toNat)
            (mpnSubN a b false).1 := by
          rw [hs2_op, hsc_op] at hsub_mem; exact hsub_mem
        -- The top zero slot at `op + 8·|a|` survived the sub (disjoint write).
        have hlimblen : (mpnSubN a b false).1.length = a.length := mpnSubN_length a b false hlen
        have htop0 : load64Mem ss.mem
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * (mpnSubN a b false).1.length))
            = some (UInt64.ofNat (0 : BitVec 64).toNat) := by
          -- Read-back through the frame to `s.mem`, then off `hres`.
          have hframe := _hsub_frame
            (UInt64.ofNat (s.regs "op").toNat + UInt64.ofNat (8 * a.length)) (by
              rw [hs2_op, hsc_op]
              exact range_tail_head_disjoint (UInt64.ofNat (s.regs "op").toNat) a.length (by omega))
          rw [hlimblen]
          rw [hframe, hs2_mem, hsc_mem]
          -- `hres` after splitting the all-zero pad: op[|a|] = 0.
          have hsplit : List.replicate (a.length + 1) (0 : BitVec 64)
              = List.replicate a.length 0 ++ [0] := by
            rw [← List.replicate_succ']
          rw [hsplit, memHoldsLimbs_append] at hres
          obtain ⟨_, htail⟩ := hres
          simp only [List.length_replicate, memHoldsLimbs] at htail
          exact htail.1
        have := memHoldsLimbs_snoc ss.mem (UInt64.ofNat (s.regs "op").toNat)
          (mpnSubN a b false).1 (0 : BitVec 64) hsub_mem' htop0
        rw [show sFinal.mem = ss.mem from by rw [hsFinal]; rfl]
        simpa using this
      · -- s_r register = ofNat (if saBool then 1 else 0).
        rw [show sFinal.regs "s_r" = ss.regs "s_a" from by rw [hsFinal]; simp [setReg]]
        rw [hsub_reg, hs2_sa, hsc_sa]
        rw [hsaBool]
        exact reg01_eq_ofNat_decide _ hsa


/-! ### §8.0f  `MpzAddJasminRefines_holds` — the `mpz_add` bridge, fully proved

The two-`Cassgn` `diff := s_a; diff ^= s_b` prelude sets `diff = s_a XOR s_b`
(`= 0` iff `s_a = s_b`, the same-sign test).  The outer `Cif (diff != 0)`
selects `sameSign_branch_run` (else, same sign, `addMagFull`) or
`diffSign_branch_run` (then, opposite sign, larger-minus-smaller).  Composes
the two branch lemmas through `cif_then_run` / `cif_else_run`. -/

/-- **`MpzAddJasminRefines_holds` — the bridge for `mpz_add`, fully proved.**

    Running `signedAddBody` under `signedRegistry a.length` lands the
    magnitude of `signedAdd (decode s_a, a) (decode s_b, b)` at `op` (with a
    canonical zero pad to the `|a|+1`-limb output window) and its sign in
    `s_r`.  The same-sign branch carries one limb (`k = 0`, `addMagFull`);
    the opposite-sign branch subtracts larger-minus-smaller (`k = 1`, top
    slot zero). -/
theorem MpzAddJasminRefines_holds : MpzAddJasminRefines := by
  intro s a b hlen hfit hn hsa hsb ha hb hres hdoa_ap hdoa_bp hap_bp
  -- The two-Cassgn prelude: diff := s_a; diff ^= s_b.
  set s1 : BignumState := setReg s "diff" (s.regs "s_a") with hs1
  set s2 : BignumState := setReg s1 "diff" (s1.regs "diff" ^^^ s1.regs "s_b") with hs2
  -- s2 preserves everything except `diff`.
  have hs2_mem : s2.mem = s.mem := by rw [hs2, hs1]; rfl
  have hs2_reg : ∀ x, x ≠ "diff" → s2.regs x = s.regs x := by
    intro x hx; rw [hs2, hs1]; simp [setReg, hx]
  have hs2_diff : s2.regs "diff" = s.regs "s_a" ^^^ s.regs "s_b" := by
    rw [hs2]; simp only [setReg]
    rw [hs1]; simp [setReg]
  have hs2_n : s2.regs "n" = s.regs "n" := hs2_reg "n" (by decide)
  have hs2_sa : s2.regs "s_a" = s.regs "s_a" := hs2_reg "s_a" (by decide)
  have hs2_sb : s2.regs "s_b" = s.regs "s_b" := hs2_reg "s_b" (by decide)
  have hs2_op : s2.regs "op" = s.regs "op" := hs2_reg "op" (by decide)
  have hs2_ap : s2.regs "ap" = s.regs "ap" := hs2_reg "ap" (by decide)
  have hs2_bp : s2.regs "bp" = s.regs "bp" := hs2_reg "bp" (by decide)
  -- Re-establish the preconditions at `s2`.
  have hs2_vn : s2.regs "n" = BitVec.ofNat 64 a.length := by rw [hs2_n]; exact hn
  have hs2_sa' : s2.regs "s_a" = 0 ∨ s2.regs "s_a" = 1 := by rw [hs2_sa]; exact hsa
  have hs2_sb' : s2.regs "s_b" = 0 ∨ s2.regs "s_b" = 1 := by rw [hs2_sb]; exact hsb
  have hs2_ha : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "ap").toNat) a := by
    rw [hs2_mem, hs2_ap]; exact ha
  have hs2_hb : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "bp").toNat) b := by
    rw [hs2_mem, hs2_bp]; exact hb
  have hs2_hres : memHoldsLimbs s2.mem (UInt64.ofNat (s2.regs "op").toNat)
      (List.replicate (a.length + 1) 0) := by rw [hs2_mem, hs2_op]; exact hres
  have hs2_doa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s2.regs "ap").toNat) (8 * a.length)) := by
    rw [hs2_op, hs2_ap]; exact hdoa_ap
  have hs2_doa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s2.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s2.regs "bp").toNat) (8 * b.length)) := by
    rw [hs2_op, hs2_bp]; exact hdoa_bp
  -- The prelude run (2 Cassgns) lands `s2`.
  have e1 : execInstr s (regCopy "diff" "s_a") = some s1 := by
    simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs1]
  have e2 : execInstr s1 (regBin "diff" (.Olxor .U64) "s_b") = some s2 := by
    simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind, hs2]
  have hprep : bignumExecFuel (signedRegistry a.length) 2
      [regCopy "diff" "s_a", regBin "diff" (.Olxor .U64) "s_b"] s = some s2 := by
    unfold bignumExecFuel; simp only [e1]
    unfold bignumExecFuel; simp only [← hs1, e2]
    unfold bignumExecFuel; rfl
  -- Case split on whether the signs differ (the `diff != 0` test).
  by_cases hsign : (s.regs "s_a" = 1) ↔ (s.regs "s_b" = 1)
  · -- Same sign: `diff = 0`, run the same-sign branch (else of the outer Cif).
    have hdiff0 : s2.regs "diff" = 0 := by
      rw [hs2_diff]
      rcases hsa with h | h <;> rcases hsb with h' | h' <;>
        simp_all <;> bv_decide
    -- The same-sign branch run (its 8-instruction body) from `s2`.
    obtain ⟨sFinal, hbranch_run, hbranch_mem, hbranch_sr⟩ :=
      sameSign_branch_run s2 a b (2 * a.length + 4) hlen hfit hs2_vn hs2_ha hs2_hb
        hs2_hres hs2_doa_ap hs2_doa_bp (by omega)
    refine ⟨sFinal, 2 + ((2 * a.length + 4) + 1), ?_, ?_⟩
    · -- Compose prelude + outer Cif (else).
      have houter : bignumExecFuel (signedRegistry a.length) ((2 * a.length + 4) + 1)
          [signedAddBody.get ⟨2, by simp [signedAddBody]⟩] s2 = some sFinal := by
        -- The outer Cif's else branch is the same-sign body.
        apply cif_else_run (signedRegistry a.length) (2 * a.length + 4) _ _ _ s2 sFinal
        · simp only [evalPExpr, pv, vr, bind, Option.bind, hdiff0]; decide
        · exact hbranch_run
      have hseq := bignumExecFuel_seq (signedRegistry a.length) 2 ((2 * a.length + 4) + 1)
        [regCopy "diff" "s_a", regBin "diff" (.Olxor .U64) "s_b"]
        [signedAddBody.get ⟨2, by simp [signedAddBody]⟩] s s2 sFinal hprep houter
      simpa [signedAddBody] using hseq
    · -- Spec at the same-sign branch: r = (saBool, addMagFull a b), k = 0.
      -- The signs are equal, so `signedAdd` is the same-sign case.
      have hsaeqb : (decide (s.regs "s_a" = 1)) = (decide (s.regs "s_b" = 1)) := by
        simp only [decide_eq_decide, iff_iff_eq.symm]; exact hsign
      have hred : signedAdd (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)
          = (decide (s.regs "s_a" = 1), addMagFull a b) := by
        rw [signedAdd, if_pos hsaeqb]
      simp only [hred]
      refine ⟨0, ?_, ?_, ?_⟩
      · -- addMagFull length = |a| + 1.
        simp only [addMagFull, List.length_append, List.length_cons, List.length_nil,
          mpnAddN_length a b false hlen]
      · -- Memory: branch landed `addMagFull a b` at op; pad is empty.
        rw [hs2_op] at hbranch_mem
        simpa using hbranch_mem
      · -- s_r = s_a → encodes saBool.
        rw [hbranch_sr, hs2_sa]
        exact reg01_eq_ofNat_decide _ hsa
  · -- Opposite sign: `diff ≠ 0`, run the diff-sign branch (then of the outer Cif).
    have hsign_ne : (s.regs "s_a" = 1) ≠ (s.regs "s_b" = 1) := by
      rw [ne_eq, iff_iff_eq.symm]; exact hsign
    have hdiff_ne : s2.regs "diff" ≠ 0 := by
      rw [hs2_diff]
      rcases hsa with h | h <;> rcases hsb with h' | h' <;>
        simp_all <;> bv_decide
    -- The diff-sign branch run (compare + nested Cifs) from `s2`.
    obtain ⟨sFinal, f2, hbranch_run, hbranch_spec⟩ :=
      diffSign_branch_run s2 a b hlen hfit (by rw [hs2_sa, hs2_sb]; exact hsign_ne)
        hs2_sa' hs2_sb' hs2_vn hs2_ha hs2_hb hs2_hres hs2_doa_ap hs2_doa_bp
    refine ⟨sFinal, 2 + (f2 + 1), ?_, ?_⟩
    · -- Compose prelude + outer Cif (then).
      have houter : bignumExecFuel (signedRegistry a.length) (f2 + 1)
          [signedAddBody.get ⟨2, by simp [signedAddBody]⟩] s2 = some sFinal := by
        apply cif_then_run (signedRegistry a.length) f2 _ _ _ s2 sFinal
          (1 : BitVec 64) (by decide)
        · simp only [evalPExpr, pv, vr, bind, Option.bind]
          rw [show (BitVec.ofInt 64 0 : BitVec 64) = 0 from rfl, if_neg hdiff_ne]
        · exact hbranch_run
      have hseq := bignumExecFuel_seq (signedRegistry a.length) 2 (f2 + 1)
        [regCopy "diff" "s_a", regBin "diff" (.Olxor .U64) "s_b"]
        [signedAddBody.get ⟨2, by simp [signedAddBody]⟩] s s2 sFinal hprep houter
      simpa [signedAddBody] using hseq
    · -- Spec: provided directly by the diff-sign branch lemma (op unchanged
      -- through the prelude, `s_a`/`s_b` registers unchanged).
      rw [hs2_op] at hbranch_spec
      simp only [hs2_sa, hs2_sb] at hbranch_spec
      exact hbranch_spec

/-! ### §8.1  Registry agreement: `signedRegistry m` ≡ `powRegistry m` on `mulBody`

`signedRegistry m` and `powRegistry m` both resolve `mpn_mul`,
`mpn_mul_1`, `mpn_addmul_1` to the same `FunDecl`s (the carry-fixed
multiply kernels).  `mulBody m`'s `Ccall`s only hit `mpn_mul_1` (row 0)
and `mpn_addmul_1` (the `Cfor` row), so the two registries drive
`mulBody m` identically.  This is the lift that lets `mul_ccall_step`
(over `powRegistry`) discharge our `signedMulBody`'s `Ccall mpn_mul`
under `signedRegistry`. -/

theorem signedRegistry_agree_mul1 (m : Nat) :
    signedRegistry m "mpn_mul_1" = powRegistry m "mpn_mul_1" := by
  simp [signedRegistry, powRegistry, mulRegistry]

theorem signedRegistry_agree_addmul (m : Nat) :
    signedRegistry m "mpn_addmul_1" = powRegistry m "mpn_addmul_1" := by
  simp [signedRegistry, powRegistry, mulRegistry]

theorem signedRegistry_agree_pow_mul (m : Nat) :
    signedRegistry m "mpn_mul" = powRegistry m "mpn_mul" := by
  simp [signedRegistry, powRegistry]

/-- `mulBody m`'s `Ccall`s (`mpn_mul_1` row 0, `mpn_addmul_1` rows 1..) resolve
    identically under `signedRegistry m` and `powRegistry m`.  Mirror of
    `MpnPowPrototype.mulBody_callsResolveSame`. -/
theorem mulBody_callsResolveSame_signed (m : Nat) :
    CallsResolveSameBody (signedRegistry m) (powRegistry m) (mulBody m) := by
  intro i hi
  simp only [mulBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [CallsResolveSame]; exact signedRegistry_agree_mul1 m
  · simp [MpnMul1Prototype.binImm, CallsResolveSame]
  · simp [MpnMul1Prototype.binImm, CallsResolveSame]
  · simp only [CallsResolveSame]
    intro j hj
    simp only [mulOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [CallsResolveSame]; exact signedRegistry_agree_addmul m
    · simp [MpnMul1Prototype.binImm, CallsResolveSame]
    · simp [MpnMul1Prototype.binImm, CallsResolveSame]

/-- Closure: `powRegistry m`'s resolved callees (the two carry-storing
    single-limb kernels) have no `Ccall`s, hence resolve identically
    under any registry pair.  This is the closure-on-callee-bodies
    condition `bignumExecFuel_registry_agree` requires. -/
theorem signedRegistry_closed_pow (m : Nat) :
    RegistryClosed (signedRegistry m) (powRegistry m) := by
  intro fn fd hfd
  simp only [powRegistry, mulRegistry] at hfd
  by_cases h0 : fn.name = "mpn_mul"
  · rw [if_pos h0] at hfd
    rw [Option.some.injEq] at hfd; subst hfd
    -- mpnMulFd m's body is `mulBody m`, whose `Ccall`s are `mpn_mul_1` and
    -- `mpn_addmul_1` — both resolve the same in the two registries.
    show CallsResolveSameBody (signedRegistry m) (powRegistry m) (mpnMulFd m).body
    exact mulBody_callsResolveSame_signed m
  · rw [if_neg h0] at hfd
    by_cases h1 : fn.name = "mpn_addmul_1"
    · rw [if_pos h1] at hfd
      rw [Option.some.injEq] at hfd; subst hfd
      exact callsResolveSameBody_of_noCcall bodyAddmulCarry_noCcall
    · rw [if_neg h1] at hfd
      by_cases h2 : fn.name = "mpn_mul_1"
      · rw [if_pos h2] at hfd
        rw [Option.some.injEq] at hfd; subst hfd
        exact callsResolveSameBody_of_noCcall bodyMulCarry_noCcall
      · rw [if_neg h2] at hfd; exact absurd hfd (by simp)

/-- **Running `mulBody m` under `signedRegistry m` = under `powRegistry m`.**
    The signed-registry's extra entries (`mpz_add`, `mpn_compare`, `mpn_add_n`,
    `mpn_sub_n`) are *never consulted* by `mulBody`'s `Ccall`s (which hit only
    `mpn_mul_1` and `mpn_addmul_1`).  This is the analogue of
    `mulBody_run_powRegistry`. -/
theorem mulBody_run_signedRegistry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (signedRegistry m) fuel (mulBody m) s
      = bignumExecFuel (powRegistry m) fuel (mulBody m) s :=
  bignumExecFuel_registry_agree (signedRegistry m) (powRegistry m)
    (signedRegistry_closed_pow m) fuel (mulBody m) s
    (mulBody_callsResolveSame_signed m)

/-! ### §8.2  Bridges as `Prop`-shaped statements (carrying the postcondition) -/

/-- **`MpzMulJasminRefines` — the bridge for `mpz_mul`.**

    Shape: starting from `a` at `ap`, `b` at `bp`, a zeroed
    `|a|+|b|`-limb result region at `op`, running `signedMulBody` under
    `signedRegistry b.length` lands `signedMul (sa, a) (sb, b)` 's
    magnitude at `op` and its sign in `s_r`.

    Reduces by composition: the sign step is two straight-line
    instructions (XOR), and the magnitude step is one `Ccall mpn_mul`
    — exactly the per-step lemma `mul_ccall_step` proved in
    `MpnPowPrototype.§6.3` (registry-lifted via
    `bignumExecFuel_registry_agree`).  Composed with
    `MpnSignedSpec.signedMul_toInt`, gives `= Int.mul`. -/
def MpzMulJasminRefines : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    0 < b.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    (s.regs "s_a" = 0 ∨ s.regs "s_a" = 1) →
    (s.regs "s_b" = 0 ∨ s.regs "s_b" = 1) →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ s' fuel,
      bignumExecFuel (signedRegistry b.length) fuel signedMulBody s = some s' ∧
      let saBool : Bool := s.regs "s_a" = 1
      let sbBool : Bool := s.regs "s_b" = 1
      let r := signedMul (saBool, a) (sbBool, b)
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) r.2 ∧
      s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0)

/-! ## §9  `Int`-level corollaries — `= Int.add` / `Int.sub` / `Int.mul`

Given each bridge plus `MpnSignedSpec`'s `_toInt` lemma, the `Int`-level
identity follows.  These corollaries are the headline contracts: an
emitted Jasmin body whose output region's denotation, paired with the
output sign register, equals the corresponding Mathlib `Int` operation. -/

/-- The `Int` value of a result region: read off `toNat` of the limb
    prefix and apply the sign bit. -/
def resultInt (mag : List (BitVec 64)) (signReg : BitVec 64) : Int :=
  if signReg = 1 then -(toNat mag : Int) else (toNat mag : Int)

/-- Decode of the operand-sign register. -/
def decodeSign (r : BitVec 64) : Bool := r = 1

theorem resultInt_eq_toInt (mag : List (BitVec 64)) (signReg : BitVec 64)
    (hsign : signReg = 0 ∨ signReg = 1) :
    resultInt mag signReg = toInt (decodeSign signReg, mag) := by
  simp only [resultInt, decodeSign, toInt]
  rcases hsign with h | h <;> simp [h]

/-! ### §9.1  The `mpz_add` Int-level contract (consequence)

If `MpzAddJasminRefines` holds, then for any state satisfying its
preconditions there is a final state where the `op` region's value,
combined with the `s_r` sign, equals `Int.add` of the operand `Int`s.
This is the *useful* phrasing — it folds in the canonical zero
normalisation and the `pad`-limb tail (which `toNat`-extends with zeros
when the canonical magnitude is shorter than `|a|+1`). -/

/-- Tail-padding with zeros doesn't change `toNat`.  The same-sign
    branch lands `|a|+1` limbs (carry-extended); the different-sign
    branch lands `|a|` limbs (no carry growth) — both fit in the
    `|a|+1`-limb output window with a possible zero-limb tail. -/
theorem toNat_replicate_zero (k : Nat) :
    toNat (List.replicate k (0 : BitVec 64)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show toNat ((0 : BitVec 64) :: List.replicate k 0) = 0
    simp only [toNat, ih]
    decide

theorem toNat_append_zero_pad (xs : List (BitVec 64)) (k : Nat) :
    toNat (xs ++ List.replicate k (0 : BitVec 64)) = toNat xs := by
  induction xs with
  | nil =>
    show toNat (List.replicate k (0 : BitVec 64)) = toNat ([] : List (BitVec 64))
    rw [toNat_replicate_zero]; rfl
  | cons x xs ih =>
    show toNat (x :: (xs ++ List.replicate k (0 : BitVec 64))) = toNat (x :: xs)
    simp only [toNat]
    rw [ih]

/-- **`mpz_add` is correct as `Int.add` — assuming the Jasmin bridge.**

    Reads the result region's `toNat` (folded through the canonical zero
    pad) and the `s_r` sign register, and identifies the pair with
    `Int.add` of the operand `Int`s.  Composes the `MpzAddJasminRefines`
    bridge with `MpnSignedSpec.signedAdd_toInt`.

    UNCONDITIONAL as of the close of `MpzAddJasminRefines_holds`. -/
theorem mpz_add_int_correct
    (s : BignumState) (a b : List (BitVec 64))
    (hlen : a.length = b.length)
    (hfit : 8 * (a.length + 1) ≤ 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hsa : s.regs "s_a" = 0 ∨ s.regs "s_a" = 1)
    (hsb : s.regs "s_b" = 0 ∨ s.regs "s_b" = 1)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b)
    (hres : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0))
    (hdoa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hdoa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)))
    (hap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length))) :
    ∃ s' fuel limbs,
      bignumExecFuel (signedRegistry a.length) fuel signedAddBody s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) limbs ∧
      resultInt limbs (s'.regs "s_r")
        = toInt (decodeSign (s.regs "s_a"), a) + toInt (decodeSign (s.regs "s_b"), b) := by
  obtain ⟨s', fuel, hrun, hpad⟩ :=
    MpzAddJasminRefines_holds s a b hlen hfit hn hsa hsb ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Destruct the existential canonical-zero-pad tail.
  obtain ⟨k, _hpadlen, hpadmem, hsr⟩ := hpad
  -- The result limbs in memory: `r.2 ++ replicate k 0` (with `r := signedAdd …`).
  refine ⟨s', fuel,
    (signedAdd (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).2
      ++ List.replicate k (0 : BitVec 64), hrun, hpadmem, ?_⟩
  -- Abbreviate the signed result.
  set r := signedAdd (decide (s.regs "s_a" = 1), a)
                     (decide (s.regs "s_b" = 1), b) with hr
  -- The s_r register encodes `r.1`.
  have hsrEnc : s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0) := hsr
  -- Decode of s_r = r.1.
  have hsignDecode : decodeSign (s'.regs "s_r") = r.1 := by
    simp only [decodeSign, hsrEnc]
    by_cases h1 : r.1 = true
    · rw [if_pos h1]
      have : BitVec.ofNat 64 1 = (1 : BitVec 64) := rfl
      rw [this]
      simp [h1]
    · have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [if_neg h1, hf]
      have h00 : BitVec.ofNat 64 0 = (0 : BitVec 64) := rfl
      rw [h00]
      simp
  -- s_r is 0 or 1.
  have hsr_pair : s'.regs "s_r" = 0 ∨ s'.regs "s_r" = 1 := by
    rw [hsrEnc]
    by_cases h1 : r.1 = true
    · right; rw [if_pos h1]; rfl
    · left
      have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [hf]; rfl
  rw [resultInt_eq_toInt _ _ hsr_pair]
  -- toInt of (r.2 ++ zeros, decoded sign) = toInt r.
  have htoInt : toInt (decodeSign (s'.regs "s_r"), r.2 ++ List.replicate k (0 : BitVec 64))
      = toInt r := by
    rw [hsignDecode]
    simp only [toInt, toNat_append_zero_pad]
  rw [htoInt]
  -- Substitute back r := signedAdd … and apply signedAdd_toInt.
  rw [hr, signedAdd_toInt _ _ hlen]
  -- Final: toInt (decode s_a, a) + toInt (decode s_b, b)
  --     = toInt (decodeSign s_a, a) + toInt (decodeSign s_b, b)
  -- These differ only in how the sign bool is encoded.  Both are
  -- `(s.regs "_" = 1)` ⇒ definitionally equal.
  simp only [decodeSign]

/-! ### §9.1.5  XOR sign-bit encoding lemma

The sign of `signedMul (sa, a) (sb, b)` is `xor sa sb`.  At the register
level, `s_r := s_a XOR s_b` (the two-`Cassgn` prelude of `signedMulBody`)
yields `s.regs "s_a" ^^^ s.regs "s_b"`, where each operand is `0` or `1`
(precondition).  The two encodings coincide. -/

theorem bitvec_xor_eq_xor_bool (a b : BitVec 64)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ^^^ b = BitVec.ofNat 64 (if xor (a = 1) (b = 1) then 1 else 0) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl

/-! ## §9.5  `MpzMulJasminRefines_holds` — the `mpz_mul` bridge, fully proved -/

/-- **`MpzMulJasminRefines_holds` — the bridge for `mpz_mul`, fully proved.**

    The emitted `signedMulBody` (`s_r := s_a; s_r ^= s_b; Ccall mpn_mul`)
    runs under `signedRegistry b.length` to a final state whose `op`
    region holds `mpnMul a b` (= `signedMul (sa, a) (sb, b)`.2) and
    whose `s_r` register encodes `xor sa sb` (= `signedMul (sa, a) (sb,
    b)`.1).  Composes the two-`Cassgn` sign step (`bitvec_xor_eq_xor_bool`)
    with `MpnPowPrototype.mul_ccall_step` (one whole `Ccall mpn_mul`),
    registry-lifted via `mulBody_run_signedRegistry` (the
    `bignumExecFuel_registry_agree` lift of `mulBody` from
    `signedRegistry` to `powRegistry`). -/
theorem MpzMulJasminRefines_holds : MpzMulJasminRefines := by
  intro s a b hbpos hfit hn hsa hsb ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Step 1: execute `regCopy "s_r" "s_a"` (Cassgn) into `s0`.
  set s0 : BignumState := setReg s "s_r" (s.regs "s_a") with hs0
  -- Step 2: execute `regBin "s_r" Olxor "s_b"` (Cassgn) into `s1`.
  set s1 : BignumState := setReg s0 "s_r" (s0.regs "s_r" ^^^ s0.regs "s_b") with hs1
  -- The frame: s1.mem = s.mem and pointer/length regs unchanged.
  have hs1_mem : s1.mem = s.mem := by rw [hs1, hs0]; rfl
  have hs1_op : s1.regs "op" = s.regs "op" := by
    rw [hs1, hs0]; simp [setReg]
  have hs1_ap : s1.regs "ap" = s.regs "ap" := by
    rw [hs1, hs0]; simp [setReg]
  have hs1_bp : s1.regs "bp" = s.regs "bp" := by
    rw [hs1, hs0]; simp [setReg]
  have hs1_n : s1.regs "n" = s.regs "n" := by
    rw [hs1, hs0]; simp [setReg]
  -- s1 carries the XOR'd sign in `s_r`.
  have hs0_sr : s0.regs "s_r" = s.regs "s_a" := by rw [hs0]; simp [setReg]
  have hs0_sb : s0.regs "s_b" = s.regs "s_b" := by rw [hs0]; simp [setReg]
  have hs1_sr : s1.regs "s_r" = s.regs "s_a" ^^^ s.regs "s_b" := by
    rw [hs1]; simp [setReg, hs0_sr, hs0_sb]
  -- s1 still satisfies memHoldsLimbs / disjoint preconditions.
  have hs1_ha : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "ap").toNat) a := by
    rw [hs1_mem, hs1_ap]; exact ha
  have hs1_hb : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "bp").toNat) b := by
    rw [hs1_mem, hs1_bp]; exact hb
  have hs1_hres : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) := by
    rw [hs1_mem, hs1_op]; exact hres
  have hs1_doa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length)) := by
    rw [hs1_op, hs1_ap]; exact hdoa_ap
  have hs1_doa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s1.regs "bp").toNat) (8 * b.length)) := by
    rw [hs1_op, hs1_bp]; exact hdoa_bp
  have hs1_ap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s1.regs "bp").toNat) (8 * b.length)) := by
    rw [hs1_ap, hs1_bp]; exact hap_bp
  have hs1_vn : s1.regs "n" = BitVec.ofNat 64 a.length := by rw [hs1_n]; exact hn
  -- Step 3: apply `mul_ccall_step` (over `powRegistry`) to get the callee's run +
  -- the result memory.
  obtain ⟨cf, fuel0, hccall⟩ :=
    MpnPowPrototype.mul_ccall_step s1 a b hbpos hfit hs1_vn hs1_ha hs1_hb hs1_hres
      hs1_doa_ap hs1_doa_bp hs1_ap_bp
  -- Concretely: `cf.mem` holds `mpnMul a b` at `s.regs "op"`; final state
  -- inherits memory.  Now construct the full bignumExecFuel run.
  -- Final state: { s1 with mem := cf.mem } after the void Ccall, then
  -- bignumExecFuel registry (fuel+1) [] = some.
  set sFinal : BignumState := { s1 with mem := cf.mem } with hsFinal
  -- Pick fuel := fuel0 + 3 so:
  --   Step Cassgn0 (fuel0+3 → fuel0+2): execInstr s ... = some s0
  --   Step Cassgn1 (fuel0+2 → fuel0+1): execInstr s0 ... = some s1
  --   Step Ccall   (fuel0+1 → callee at fuel0; resume at fuel0+1 with []):
  --     args → some [op, ap, bp, n]; lvs.isEmpty=true; void path → sFinal
  --     bignumExecFuel _ (fuel0+1) [] sFinal = some sFinal
  refine ⟨sFinal, 2 + (fuel0 + 2), ?_, ?_, ?_⟩
  · -- The full bignumExecFuel run.  Use `bignumExecFuel_seq` to compose.
    show bignumExecFuel (signedRegistry b.length) (2 + (fuel0 + 2)) signedMulBody s = some sFinal
    -- mul_ccall_step at fuel = fuel0 + 1 (so the callee runs at fuel0 + 1, which
    -- is what the Ccall arm passes when outer fuel is fuel0 + 2).
    obtain ⟨hccall_run, hccall_mem⟩ := hccall (fuel0 + 1) (by omega)
    -- Lift the callee run from powRegistry to signedRegistry.
    have hccall_run_signed : bignumExecFuel (signedRegistry b.length) (fuel0 + 1)
        (mpnMulFd b.length).body
        { regs := fun name =>
            match (mpnMulFd b.length).params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s1.regs "op", s1.regs "ap", s1.regs "bp", s1.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s1.mem } = some cf := by
      show bignumExecFuel (signedRegistry b.length) (fuel0 + 1) (mulBody b.length) _ = _
      rw [hs1_op, hs1_ap, hs1_bp, hs1_n, hs1_mem]
      -- mulBody_run_signedRegistry: signedRegistry m fuel mulBody m = powRegistry m fuel mulBody m
      rw [mulBody_run_signedRegistry b.length (fuel0 + 1)]
      exact hccall_run
    -- The step lemmas for the two Cassgns.
    have hexec0 : execInstr s (regCopy "s_r" "s_a") = some s0 := by
      simp only [regCopy, execInstr, evalPExpr, pv, vr, bind, Option.bind]
      rfl
    have hexec1 : execInstr s0 (regBin "s_r" (.Olxor .U64) "s_b") = some s1 := by
      simp only [regBin, execInstr, evalPExpr, pv, vr, bind, Option.bind]
      rfl
    have hargs : ([(pv "op"), (pv "ap"), (pv "bp"), (pv "n")] : List PExpr).mapM (evalPExpr s1)
        = some [s1.regs "op", s1.regs "ap", s1.regs "bp", s1.regs "n"] := by
      simp only [List.mapM, List.mapM.loop, pv, vr, evalPExpr, bind, Option.bind,
                 List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rfl
    -- Run [Cassgn0, Cassgn1] from s at fuel 2 (1 fuel-tick per step), landing s1.
    have hrun_prefix : bignumExecFuel (signedRegistry b.length) 2
        [regCopy "s_r" "s_a", regBin "s_r" (.Olxor .U64) "s_b"] s = some s1 := by
      -- bignumExecFuel _ 2 (i :: rest) s unfolds via the (fuel+1, i :: is, s)
      -- clause, falling through to the `i => match execInstr s i with ...` arm.
      -- The simp set discharges via the two `execInstr` step lemmas.
      set_option linter.unusedSimpArgs false in
      unfold bignumExecFuel
      simp only [hexec0]
      unfold bignumExecFuel
      simp only [hexec1]
      unfold bignumExecFuel
      rfl
    -- Run [Ccall mpn_mul] from s1 at fuel (fuel0 + 2), landing sFinal.
    have hrun_ccall : bignumExecFuel (signedRegistry b.length) (fuel0 + 2)
        [.Ccall .DoNotInline []
            { name := "mpn_mul" }
            [pv "op", pv "ap", pv "bp", pv "n"]] s1 = some sFinal := by
      show bignumExecFuel (signedRegistry b.length) ((fuel0 + 1) + 1)
        [.Ccall .DoNotInline []
            { name := "mpn_mul" }
            [pv "op", pv "ap", pv "bp", pv "n"]] s1 = some sFinal
      -- Unfold the Ccall arm; use `split` like `outer_ccall_reduce`.
      rw [bignumExecFuel, signedRegistry_mul b.length, hargs]
      simp only [List.isEmpty_nil, if_true]
      split
      · -- none case: contradicts hccall_run_signed.
        rename_i hrun
        exact absurd (hccall_run_signed.symm.trans hrun) (by simp)
      · -- some case: callee final state.
        rename_i cf' hrun
        have hcfeq : cf' = cf := Option.some.inj (hrun.symm.trans hccall_run_signed)
        rw [hcfeq]
        -- Now: bignumExecFuel _ (fuel0+1+1) [] { regs := s1.regs, mem := cf.mem } = some sFinal
        simp only [bignumExecFuel, hsFinal]
    -- Compose via bignumExecFuel_seq.
    have hseq := bignumExecFuel_seq (signedRegistry b.length) 2 (fuel0 + 2)
      [regCopy "s_r" "s_a", regBin "s_r" (.Olxor .U64) "s_b"]
      [.Ccall .DoNotInline []
          { name := "mpn_mul" }
          [pv "op", pv "ap", pv "bp", pv "n"]]
      s s1 sFinal hrun_prefix hrun_ccall
    exact hseq
  · -- Memory still holds mpnMul a b at op.
    simp only [signedMul]
    obtain ⟨_, hccall_mem⟩ := hccall (fuel0 + 1) (by omega)
    rw [hs1_op] at hccall_mem
    -- sFinal.mem = cf.mem.
    show memHoldsLimbs sFinal.mem (UInt64.ofNat (s.regs "op").toNat) (mpnMul a b)
    rw [hsFinal]; exact hccall_mem
  · -- s_r register encodes xor of signs.
    simp only [signedMul]
    show sFinal.regs "s_r"
      = BitVec.ofNat 64 (if xor (s.regs "s_a" = 1) (s.regs "s_b" = 1) then 1 else 0)
    rw [hsFinal]
    -- sFinal's regs come from s1.
    show s1.regs "s_r"
      = BitVec.ofNat 64 (if xor (s.regs "s_a" = 1) (s.regs "s_b" = 1) then 1 else 0)
    rw [hs1_sr]
    exact bitvec_xor_eq_xor_bool _ _ hsa hsb

/-! ### §9.1.6  `mpz_mul_int_correct` — unconditional Int-level corollary

Since `MpzMulJasminRefines_holds` is a *theorem* (not a hypothesis), the
`Int`-level identity follows unconditionally: the emitted `mpz_mul`
Jasmin body lands a memory whose `op`-region's `toNat` paired with the
`s_r` sign register equals `Int.mul` of the operand `Int`s.  Composes
`MpzMulJasminRefines_holds` with `MpnSignedSpec.signedMul_toInt`. -/

theorem mpz_mul_int_correct
    (s : BignumState) (a b : List (BitVec 64))
    (hbpos : 0 < b.length)
    (hfit : 8 * (a.length + b.length) ≤ 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hsa : s.regs "s_a" = 0 ∨ s.regs "s_a" = 1)
    (hsb : s.regs "s_b" = 0 ∨ s.regs "s_b" = 1)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b)
    (hres : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0))
    (hdoa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hdoa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)))
    (hap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length))) :
    ∃ s' fuel limbs,
      bignumExecFuel (signedRegistry b.length) fuel signedMulBody s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) limbs ∧
      resultInt limbs (s'.regs "s_r")
        = toInt (decodeSign (s.regs "s_a"), a) * toInt (decodeSign (s.regs "s_b"), b) := by
  obtain ⟨s', fuel, hrun, hmem, hsr⟩ :=
    MpzMulJasminRefines_holds s a b hbpos hfit hn hsa hsb ha hb hres
      hdoa_ap hdoa_bp hap_bp
  refine ⟨s', fuel,
    (signedMul (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).2,
    hrun, hmem, ?_⟩
  -- Same structure as `mpz_add_int_correct`.
  set r := signedMul (decide (s.regs "s_a" = 1), a)
                     (decide (s.regs "s_b" = 1), b) with hr
  have hsignDecode : decodeSign (s'.regs "s_r") = r.1 := by
    simp only [decodeSign, hsr]
    by_cases h1 : r.1 = true
    · rw [if_pos h1]
      have : BitVec.ofNat 64 1 = (1 : BitVec 64) := rfl
      rw [this]; simp [h1]
    · have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [if_neg h1, hf]
      have h00 : BitVec.ofNat 64 0 = (0 : BitVec 64) := rfl
      rw [h00]; simp
  have hsr_pair : s'.regs "s_r" = 0 ∨ s'.regs "s_r" = 1 := by
    rw [hsr]
    by_cases h1 : r.1 = true
    · right; rw [if_pos h1]; rfl
    · left
      have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [hf]; rfl
  rw [resultInt_eq_toInt _ _ hsr_pair]
  have htoInt : toInt (decodeSign (s'.regs "s_r"), r.2) = toInt r := by
    rw [hsignDecode]
  rw [htoInt, hr, signedMul_toInt]
  simp only [decodeSign]

/-! ### §9.1.7  `MpzSubJasminRefines_of_add` — tighter residual

The `mpz_sub` bridge factors through the `mpz_add` bridge.  Given the
algorithm-level `signedSub x y = signedAdd x (negate y)` (a `def`),
the `mpz_sub` body's `s_b ^= 1` prelude exactly implements `negate`'s
sign-bit flip at the register level, and the Ccall to `mpz_add` is
discharged by the assumed `MpzAddJasminRefines`.  This reduces the
`MpzSubJasminRefines` residual to *just* `MpzAddJasminRefines`. -/

/-- XOR-with-1 toggles a `0`/`1` register: `0 ^^^ 1 = 1` and `1 ^^^ 1 = 0`. -/
theorem xor_one_toggle (b : BitVec 64) (h : b = 0 ∨ b = 1) :
    (b ^^^ 1 = 0 ∨ b ^^^ 1 = 1) ∧ ((b ^^^ 1 = 1) = ¬(b = 1)) := by
  rcases h with rfl | rfl
  · refine ⟨Or.inr ?_, ?_⟩
    · rfl
    · simp
  · refine ⟨Or.inl ?_, ?_⟩
    · rfl
    · simp

/-- **The negate-add identification.**  `signedAdd x (negate y) = signedSub x y`
    (by definition of `signedSub`).  This is the algorithm-level link the
    Sub-from-Add bridge composes with — the `s_b ^= 1` register-level flip
    in `signedSubBody` exactly matches `negate y = (!y.1, y.2)` at the spec
    level, and the Ccall to `mpz_add` then computes `signedAdd x (negate y)
    = signedSub x y`. -/
theorem signedAdd_negate_eq_signedSub (x y : Signed) :
    signedAdd x (negate y) = signedSub x y := by
  rfl

/-- **XOR-with-1 of a 0/1 register decodes to negation of the boolean decoding.**
    If `s ∈ {0, 1}`, then `(s ^^^ 1 = 1) = !(s = 1)` — equivalently, decoding
    `s ^^^ 1` gives `!decodeSign s`.  This is the load-bearing identification
    between the register-level XOR flip and the spec-level `negate` operation. -/
theorem decode_xor_one (b : BitVec 64) (h : b = 0 ∨ b = 1) :
    (b ^^^ 1 = 1) = ¬(b = 1) :=
  (xor_one_toggle b h).2

/-! ## §9.6  `MpzSubJasminRefines` from `MpzAddJasminRefines`

`signedSubBody` = `[s_b ^= 1; s_r = mpz_add(op, ap, bp, n, s_a, s_b)]`.
The structure is the same as `MpzMulJasminRefines_holds` but
single-Cassgn + one *non-void* Ccall (to `signedAddFd`, which itself
is what `MpzAddJasminRefines` proves about).  The proof reduces the
residual `MpzSubJasminRefines` to *just* `MpzAddJasminRefines`,
modulo the registry's `mpz_add` resolution and the sign-bit toggle
identity `(b ^^^ 1 = 1) = ¬(b = 1)` (= `decode_xor_one`) and the
algorithm-level `signedAdd x (negate y) = signedSub x y` (=
`signedAdd_negate_eq_signedSub`). -/

/-- **`MpzSubJasminRefines_of_add` — the Sub-from-Add reduction.**

    `MpzSubJasminRefines` factors through `MpzAddJasminRefines`: the
    `s_b ^= 1` prelude of `signedSubBody` exactly implements `negate`
    at the register level (via `decode_xor_one`), the non-void Ccall to
    `mpz_add` runs `signedAddFd.body = signedAddBody` on a callee init
    state whose `s_b` is the flipped sign, and the algorithm-level
    identity `signedAdd x (negate y) = signedSub x y` (=
    `signedAdd_negate_eq_signedSub`) closes the postcondition.

    The proof is a body-step trace through the non-void Ccall arm
    (analogous to `MpzMulJasminRefines_holds`'s void-Ccall path but
    using `bindResults` for the `s_r` LVal).  Once
    `MpzAddJasminRefines_holds` is closed as a theorem,
    `MpzSubJasminRefines_holds : MpzSubJasminRefines` follows
    immediately by `MpzSubJasminRefines_of_add
    MpzAddJasminRefines_holds`. -/
theorem MpzSubJasminRefines_of_add (hAdd : MpzAddJasminRefines) :
    MpzSubJasminRefines := by
  intro s a b hlen hfit hn hsa hsb ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Step 1: execute `binImm "s_b" Olxor 1` (Cassgn) into s1.
  set s1 : BignumState := setReg s "s_b" (s.regs "s_b" ^^^ 1) with hs1
  have hs1_mem : s1.mem = s.mem := by rw [hs1]; rfl
  have hs1_op : s1.regs "op" = s.regs "op" := by rw [hs1]; simp [setReg]
  have hs1_ap : s1.regs "ap" = s.regs "ap" := by rw [hs1]; simp [setReg]
  have hs1_bp : s1.regs "bp" = s.regs "bp" := by rw [hs1]; simp [setReg]
  have hs1_n : s1.regs "n" = s.regs "n" := by rw [hs1]; simp [setReg]
  have hs1_sa : s1.regs "s_a" = s.regs "s_a" := by rw [hs1]; simp [setReg]
  have hs1_sb : s1.regs "s_b" = s.regs "s_b" ^^^ 1 := by rw [hs1]; simp [setReg]
  obtain ⟨hsb_flip_pair, _hsb_decode⟩ := xor_one_toggle (s.regs "s_b") hsb
  have hs1_sb_pair : s1.regs "s_b" = 0 ∨ s1.regs "s_b" = 1 := by
    rw [hs1_sb]; exact hsb_flip_pair
  have hs1_sa_pair : s1.regs "s_a" = 0 ∨ s1.regs "s_a" = 1 := by
    rw [hs1_sa]; exact hsa
  have hs1_ha : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "ap").toNat) a := by
    rw [hs1_mem, hs1_ap]; exact ha
  have hs1_hb : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "bp").toNat) b := by
    rw [hs1_mem, hs1_bp]; exact hb
  have hs1_hres : memHoldsLimbs s1.mem (UInt64.ofNat (s1.regs "op").toNat)
      (List.replicate (a.length + 1) 0) := by
    rw [hs1_mem, hs1_op]; exact hres
  have hs1_doa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length)) := by
    rw [hs1_op, hs1_ap]; exact hdoa_ap
  have hs1_doa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s1.regs "bp").toNat) (8 * b.length)) := by
    rw [hs1_op, hs1_bp]; exact hdoa_bp
  have hs1_ap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s1.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s1.regs "bp").toNat) (8 * b.length)) := by
    rw [hs1_ap, hs1_bp]; exact hap_bp
  have hs1_vn : s1.regs "n" = BitVec.ofNat 64 a.length := by rw [hs1_n]; exact hn
  -- Build the callee init state.  The Ccall arm of bignumExecFuel constructs
  -- the callee regs from `signedAddFd.params.findIdx?` against the args
  -- vector; for `signedAddFd.params = [op, ap, bp, n, s_a, s_b]` this is
  -- exactly the explicit branch below.
  set ci : BignumState :=
    { regs := fun name =>
        match signedAddFd.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s1.regs "op", s1.regs "ap", s1.regs "bp", s1.regs "n",
                        s1.regs "s_a", s1.regs "s_b"] : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s1.mem } with hci
  have hci_op : ci.regs "op" = s1.regs "op" := by rw [hci]; rfl
  have hci_ap : ci.regs "ap" = s1.regs "ap" := by rw [hci]; rfl
  have hci_bp : ci.regs "bp" = s1.regs "bp" := by rw [hci]; rfl
  have hci_n : ci.regs "n" = s1.regs "n" := by rw [hci]; rfl
  have hci_sa : ci.regs "s_a" = s1.regs "s_a" := by rw [hci]; rfl
  have hci_sb : ci.regs "s_b" = s1.regs "s_b" := by rw [hci]; rfl
  have hci_mem : ci.mem = s1.mem := by rw [hci]
  have hci_vn : ci.regs "n" = BitVec.ofNat 64 a.length := by rw [hci_n]; exact hs1_vn
  have hci_sa_pair : ci.regs "s_a" = 0 ∨ ci.regs "s_a" = 1 := by
    rw [hci_sa]; exact hs1_sa_pair
  have hci_sb_pair : ci.regs "s_b" = 0 ∨ ci.regs "s_b" = 1 := by
    rw [hci_sb]; exact hs1_sb_pair
  have hci_ha : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "ap").toNat) a := by
    rw [hci_mem, hci_ap]; exact hs1_ha
  have hci_hb : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "bp").toNat) b := by
    rw [hci_mem, hci_bp]; exact hs1_hb
  have hci_hres : memHoldsLimbs ci.mem (UInt64.ofNat (ci.regs "op").toNat)
      (List.replicate (a.length + 1) 0) := by
    rw [hci_mem, hci_op]; exact hs1_hres
  have hci_doa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length)) := by
    rw [hci_op, hci_ap]; exact hs1_doa_ap
  have hci_doa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (ci.regs "bp").toNat) (8 * b.length)) := by
    rw [hci_op, hci_bp]; exact hs1_doa_bp
  have hci_ap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (ci.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (ci.regs "bp").toNat) (8 * b.length)) := by
    rw [hci_ap, hci_bp]; exact hs1_ap_bp
  -- Apply MpzAddJasminRefines (hypothesis) to ci.
  obtain ⟨cf, fuel0, hccall_run, k, hpadlen, hpad_mem, hcallee_sr⟩ :=
    hAdd ci a b hlen hfit hci_vn hci_sa_pair hci_sb_pair hci_ha hci_hb hci_hres
      hci_doa_ap hci_doa_bp hci_ap_bp
  -- Caller's post-Ccall state: mem = cf.mem, s_r register set to cf.regs "s_r".
  set sFinal : BignumState :=
    setReg { s1 with mem := cf.mem } "s_r" (cf.regs "s_r") with hsFinal
  -- The decode-bool identifications: ci's saBool = s's saBool; ci's sbBool = !s's sbBool.
  have hci_sa_eq : ci.regs "s_a" = s.regs "s_a" := by rw [hci_sa, hs1_sa]
  have hci_sb_eq : ci.regs "s_b" = s.regs "s_b" ^^^ 1 := by rw [hci_sb, hs1_sb]
  have hsa_dec : (decide (ci.regs "s_a" = 1) : Bool) = decide (s.regs "s_a" = 1) := by
    rw [hci_sa_eq]
  have hsb_dec : (decide (ci.regs "s_b" = 1) : Bool) = !(decide (s.regs "s_b" = 1)) := by
    rw [hci_sb_eq]
    rcases hsb with h | h <;> rw [h] <;> decide
  refine ⟨sFinal, 2 + (fuel0 + 1), ?_, k, ?_, ?_, ?_⟩
  · -- Full bignumExecFuel run for signedSubBody = [binImm s_b ^= 1; Ccall mpz_add].
    show bignumExecFuel (signedRegistry a.length) (2 + (fuel0 + 1)) signedSubBody s = some sFinal
    -- Step the Cassgn prelude.
    have hexec1 : execInstr s (binImm "s_b" (.Olxor .U64) 1) = some s1 := by
      simp only [binImm, execInstr, evalPExpr, pv, vr, bind, Option.bind]
      rfl
    have hrun_prefix : bignumExecFuel (signedRegistry a.length) 1
        [binImm "s_b" (.Olxor .U64) 1] s = some s1 := by
      unfold bignumExecFuel
      simp only [hexec1]
      unfold bignumExecFuel
      rfl
    -- Step the Ccall.
    have hargs : ([(pv "op"), (pv "ap"), (pv "bp"), (pv "n"),
                   (pv "s_a"), (pv "s_b")] : List PExpr).mapM (evalPExpr s1)
        = some [s1.regs "op", s1.regs "ap", s1.regs "bp", s1.regs "n",
                s1.regs "s_a", s1.regs "s_b"] := by
      simp only [List.mapM, List.mapM.loop, pv, vr, evalPExpr, bind, Option.bind,
                 List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      rfl
    have hbind : bindResults { s1 with mem := cf.mem } cf
        [.Lvar { var := vr "s_r" }] signedAddFd.results
        = some sFinal := by
      show some (setReg { s1 with mem := cf.mem } "s_r" (cf.regs "s_r")) = some sFinal
      rw [hsFinal]
    -- The callee init state built by the Ccall arm equals ci.  Use `change`
    -- to identify it via the `hci` definition, then bignumExecFuel_mono to
    -- bump the fuel from fuel0 to fuel0 + 1 (the Ccall arm passes fuel-1).
    have hccall_run_signed : bignumExecFuel (signedRegistry a.length) (fuel0 + 1)
        signedAddFd.body
        { regs := fun name =>
            match signedAddFd.params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s1.regs "op", s1.regs "ap", s1.regs "bp",
                            s1.regs "n", s1.regs "s_a", s1.regs "s_b"]
                            : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s1.mem } = some cf := by
      change bignumExecFuel (signedRegistry a.length) (fuel0 + 1) signedAddBody ci = some cf
      exact bignumExecFuel_mono (signedRegistry a.length) fuel0 1
        signedAddBody ci cf hccall_run
    have hrun_ccall : bignumExecFuel (signedRegistry a.length) (fuel0 + 1 + 1)
        [.Ccall .DoNotInline [.Lvar { var := vr "s_r" }]
            { name := "mpz_add" }
            [pv "op", pv "ap", pv "bp", pv "n", pv "s_a", pv "s_b"]] s1
        = some sFinal := by
      rw [bignumExecFuel, signedRegistry_add a.length, hargs]
      simp only
      split
      · rename_i hrun; exact absurd (hccall_run_signed.symm.trans hrun) (by simp)
      · rename_i cf' hrun
        have hcfeq : cf' = cf := Option.some.inj (hrun.symm.trans hccall_run_signed)
        rw [hcfeq]
        simp only [List.isEmpty_cons, if_false]
        rw [hbind]
        unfold bignumExecFuel
        rfl
    -- Compose via bignumExecFuel_seq: signedSubBody = [binImm] ++ [Ccall ...].
    have hseq := bignumExecFuel_seq (signedRegistry a.length) 1 (fuel0 + 1 + 1)
      [binImm "s_b" (.Olxor .U64) 1]
      [.Ccall .DoNotInline [.Lvar { var := vr "s_r" }]
          { name := "mpz_add" }
          [pv "op", pv "ap", pv "bp", pv "n", pv "s_a", pv "s_b"]]
      s s1 sFinal hrun_prefix hrun_ccall
    have hfuel_eq : 1 + (fuel0 + 1 + 1) = 2 + (fuel0 + 1) := by omega
    rw [← hfuel_eq]
    convert hseq using 2
  · -- hpadlen-equiv with signedSub.
    -- (signedAdd (saBool, a) (sbBool', b)).2.length = (signedSub (saBool, a) (sbBool, b)).2.length.
    have : (signedSub (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).2
         = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).2 := by
      show (signedAdd (decide (s.regs "s_a" = 1), a)
              (negate (decide (s.regs "s_b" = 1), b))).2
         = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).2
      simp only [negate]
      rw [hsa_dec, hsb_dec]
    rw [this]; exact hpadlen
  · -- Memory at op holds (signedSub (sa,a) (sb,b)).2 ++ replicate k 0 in sFinal.mem.
    have hsFinal_mem : sFinal.mem = cf.mem := by rw [hsFinal]; simp [setReg]
    rw [hsFinal_mem]
    have hci_op_eq_s : UInt64.ofNat (ci.regs "op").toNat
                     = UInt64.ofNat (s.regs "op").toNat := by
      rw [hci_op, hs1_op]
    rw [← hci_op_eq_s]
    -- Translate (signedSub (s.s_a=1, a) (s.s_b=1, b)) to signedAdd with negate.
    have heq : (signedSub (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).2
             = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).2 := by
      show (signedAdd (decide (s.regs "s_a" = 1), a)
              (negate (decide (s.regs "s_b" = 1), b))).2
         = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).2
      simp only [negate]
      rw [hsa_dec, hsb_dec]
    rw [heq]; exact hpad_mem
  · -- s_r register encodes signedSub's sign.
    have hsFinal_sr : sFinal.regs "s_r" = cf.regs "s_r" := by
      rw [hsFinal]; simp [setReg]
    rw [hsFinal_sr]
    -- Identify signedSub's sign with signedAdd's via negate.
    have heq1 : (signedSub (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).1
              = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).1 := by
      show (signedAdd (decide (s.regs "s_a" = 1), a)
              (negate (decide (s.regs "s_b" = 1), b))).1
         = (signedAdd (decide (ci.regs "s_a" = 1), a) (decide (ci.regs "s_b" = 1), b)).1
      simp only [negate]
      rw [hsa_dec, hsb_dec]
    rw [heq1]; exact hcallee_sr

/-- **`mpz_sub` Jasmin bridge — fully proved theorem.**  Immediate
    consequence of `MpzSubJasminRefines_of_add` applied to the now-proved
    `MpzAddJasminRefines_holds`.  Once this lands, `mpz_sub_int_correct`
    becomes unconditional in lockstep with `mpz_add_int_correct`. -/
theorem MpzSubJasminRefines_holds : MpzSubJasminRefines :=
  MpzSubJasminRefines_of_add MpzAddJasminRefines_holds

/-- **`mpz_sub` is correct as `Int.sub`.**  Composes
    `MpzSubJasminRefines_holds` (the now-proved bridge) with
    `signedSub_toInt` (the algorithm-level identity). -/
theorem mpz_sub_int_correct
    (s : BignumState) (a b : List (BitVec 64))
    (hlen : a.length = b.length)
    (hfit : 8 * (a.length + 1) ≤ 2 ^ 64)
    (hn : s.regs "n" = BitVec.ofNat 64 a.length)
    (hsa : s.regs "s_a" = 0 ∨ s.regs "s_a" = 1)
    (hsb : s.regs "s_b" = 0 ∨ s.regs "s_b" = 1)
    (ha : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a)
    (hb : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b)
    (hres : memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + 1) 0))
    (hdoa_ap : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)))
    (hdoa_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)))
    (hap_bp : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length))) :
    ∃ s' fuel limbs,
      bignumExecFuel (signedRegistry a.length) fuel signedSubBody s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op").toNat) limbs ∧
      resultInt limbs (s'.regs "s_r")
        = toInt (decodeSign (s.regs "s_a"), a) - toInt (decodeSign (s.regs "s_b"), b) := by
  -- Apply the Sub-from-Add reduction to get MpzSubJasminRefines.
  have hSub : MpzSubJasminRefines := MpzSubJasminRefines_of_add MpzAddJasminRefines_holds
  obtain ⟨s', fuel, hrun, k, _hpadlen, hpadmem, hsr⟩ :=
    hSub s a b hlen hfit hn hsa hsb ha hb hres hdoa_ap hdoa_bp hap_bp
  refine ⟨s', fuel,
    (signedSub (decide (s.regs "s_a" = 1), a) (decide (s.regs "s_b" = 1), b)).2
      ++ List.replicate k (0 : BitVec 64), hrun, hpadmem, ?_⟩
  set r := signedSub (decide (s.regs "s_a" = 1), a)
                     (decide (s.regs "s_b" = 1), b) with hr
  have hsrEnc : s'.regs "s_r" = BitVec.ofNat 64 (if r.1 then 1 else 0) := hsr
  have hsignDecode : decodeSign (s'.regs "s_r") = r.1 := by
    simp only [decodeSign, hsrEnc]
    by_cases h1 : r.1 = true
    · rw [if_pos h1]
      have : BitVec.ofNat 64 1 = (1 : BitVec 64) := rfl
      rw [this]; simp [h1]
    · have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [if_neg h1, hf]
      have h00 : BitVec.ofNat 64 0 = (0 : BitVec 64) := rfl
      rw [h00]; simp
  have hsr_pair : s'.regs "s_r" = 0 ∨ s'.regs "s_r" = 1 := by
    rw [hsrEnc]
    by_cases h1 : r.1 = true
    · right; rw [if_pos h1]; rfl
    · left
      have hf : r.1 = false := by cases h2 : r.1 with
        | true => exact absurd h2 h1
        | false => rfl
      rw [hf]; rfl
  rw [resultInt_eq_toInt _ _ hsr_pair]
  have htoInt : toInt (decodeSign (s'.regs "s_r"), r.2 ++ List.replicate k (0 : BitVec 64))
      = toInt r := by
    rw [hsignDecode]
    simp only [toInt, toNat_append_zero_pad]
  rw [htoInt, hr, signedSub_toInt _ _ hlen]
  simp only [decodeSign]

/-! ## §10  Honest residual + audit

What is **proved** here:

  * **`MpzMulJasminRefines_holds` — fully proved.**  The emitted
    `signedMulBody` (two-`Cassgn` sign-XOR + `Ccall mpn_mul`) refines
    `signedMul (sa, a) (sb, b)` over byte memory.  Composes
    `MpnPowPrototype.mul_ccall_step` (one whole `Ccall mpn_mul`) with
    the registry-agreement lift `mulBody_run_signedRegistry`
    (§8.1; bridges `signedRegistry` ↔ `powRegistry` on
    `mulBody`'s reachable `Ccall`s).  Axiom-clean modulo the
    bv_decide natives inherited from `MpnMulJasminRefines_holds`.
  * **`mpz_mul_int_correct` — unconditional `Int`-level corollary.**
    Composes the bridge with `signedMul_toInt` to give the headline
    `= Int.mul` identity on the emitted Jasmin body.
  * **`MpzSubJasminRefines_of_add` — fully proved Sub-from-Add reduction.**
    The Sub bridge factors through the Add bridge: the `s_b ^= 1` prelude
    of `signedSubBody` implements `negate` at the register level (via
    `decode_xor_one`), the non-void Ccall to `mpz_add` is discharged by
    `MpzAddJasminRefines` on the flipped-sign callee init state, and the
    algorithm-level identity `signedAdd x (negate y) = signedSub x y` (via
    `signedAdd_negate_eq_signedSub`) closes the postcondition.  Once
    `MpzAddJasminRefines_holds` is closed as a theorem,
    `MpzSubJasminRefines_holds = MpzSubJasminRefines_of_add
    MpzAddJasminRefines_holds` follows by application; this also lifts
    `mpz_sub_int_correct` to unconditional.
  * **`mpz_add_int_correct` (conditional on `MpzAddJasminRefines`).**  Same
    structure as `mpz_mul_int_correct`; reduces to `signedAdd_toInt` once
    the bridge is closed.
  * **`mpz_sub_int_correct` (conditional on `MpzAddJasminRefines`).**
    Composes `MpzSubJasminRefines_of_add` with `signedSub_toInt`.  Depends
    on the Add bridge, *not* the Sub bridge — so closing one
    `MpzAddJasminRefines_holds` simultaneously discharges both Int-level
    corollaries (Add and Sub).
  * **Body bug fix (`signedAddBody`).**  The original body had a spurious
    `binImm "diff" Olxor (-1)` line that made `diff` always non-zero (the
    same-sign branch was unreachable; the bridge was unprovable as stated).
    The fix is removing that line: `diff = s_a XOR s_b`, which is 0 iff
    same sign — matching the docstring pseudocode.
  * The signed registry exposes all the required callees, and
    `signedRegistry_agree_pow_mul` / `signedRegistry_agree_mul1` /
    `signedRegistry_agree_addmul` establish the registry-agreement
    needed by `mul_ccall_step`-style lifts.
  * The three Jasmin `FunDecl`s exist as `List InstrR` and
    `bignumExecFuel` runs them on the abstract memory model.
  * The `_toInt` identification of the result with `Int.add` / `Int.sub`
    reduces (via `MpnSignedSpec.signedAdd_toInt` / `signedSub_toInt`)
    to the structural bridge claim (the magnitude limbs and sign
    register correctly encode the Mathlib `Signed`).
  * `toNat_append_zero_pad`: tail-padding by zeros is `toNat`-invariant.

The `MpzAdd` bridge remains as a sorry-free `Prop`.  The `MpzSub` bridge
*reduces* to it via `MpzSubJasminRefines_of_add` (now a proved theorem);
once the Add bridge is closed, Sub follows immediately.

What is **not** discharged here (the residual is now a single obligation):

  **`MpzAddJasminRefines_holds`** — the three-way Cif case analysis for
  `signedAddBody`.  After the body bug fix, the three top-level branches are:

    (a) **same sign** (`diff == 0`, outer Cif `else`): straight-line
        `Ccall mpn_add_n; s_r := s_a`; result is `(s_a, addMagFull a b)` =
        `signedAdd (sa, a) (sb, b)` when `sa = sb`.  Reduces by one
        `Ccall mpn_add_n` step, lifting `MpnAddNJasminRefines` (over
        `emptyRegistry`) to `signedRegistry` via `bignumExecFuel_registry_irrel`
        (the `mpnAddNFd.body` is `NoCcallBody`).

    (b) **different sign + |a| > |b|** (`diff != 0`, `result != 0`, `rmone == 0`):
        `Ccall mpn_sub_n(op, ap, bp, n); s_r := s_a`; result is
        `(sa, mpnSubN a b false .1)` = `signedAdd (sa, a) (!sa, b)` when
        `mpnCompare a b = gt`.  Reduces by `Ccall mpn_compare` + `Ccall mpn_sub_n`.

    (c) **different sign + |b| > |a|** (`diff != 0`, `result != 0`, `rmone != 0`):
        `Ccall mpn_sub_n(op, bp, ap, n); s_r := s_b`; result is
        `(sb, mpnSubN b a false .1)`.  Reduces by `Ccall mpn_compare` + swapped
        `Ccall mpn_sub_n`.

    (d) **equal magnitudes** (`diff != 0`, `result == 0`):
        `Ccall mpn_sub_n(op, ap, bp, n); s_r := 0`; result is canonical zero.

  Each branch's `Ccall` step is the analogue of `mul_ccall_step` for a
  *different* callee (and `mpn_add_n` / `mpn_sub_n` / `mpn_compare` all have
  `NoCcallBody`, so they're *simpler* than `mul_ccall_step` — pure
  `bignumExecFuel_registry_irrel` lifts, no nested registry agreement).
  The size of this case-split is comparable to `MpzMulJasminRefines_holds`
  but four-way instead of one-way, plus a sub-Cif on the `result == 1`
  test in (b)/(c).  The closure is mechanical given:

    - `MpnAddNJasminRefines` / `MpnSubNJasminRefines` / `MpnCompareJasminRefines`
      (each a fully-proved theorem in its `Mpn*Prototype.lean` file);
    - `bignumExecFuel_registry_irrel` (lifting `emptyRegistry` runs to
      `signedRegistry`, applicable since all three callee bodies are
      `NoCcallBody`) — provided here as `mpnAddNFd_body_noCcall`,
      `mpnSubNFd_body_noCcall`, `mpnCompareFd_body_noCcall` (§6.5);
    - The `Cif`-branch arm of `bignumExecFuel` (already used in
      `MpnPowPrototype`'s outer loop).

  **Same-sign carry.**  A void `Ccall` inherits only memory across the
  call, so the callee's final `cf` register does not reach the caller.
  Since `addMagFull a b = (mpnAddN a b false).1 ++ [carryByte]` is
  `|a|+1` limbs, the same-sign branch instead goes through
  `addNCallCarry` (a non-void `Ccall` to `mpn_add_n_cf`, i.e. the
  wrapper `mpnAddNFdCarry`: same body as `mpnAddNFd` but
  `results := [cf]`), so the `Ccall` arm binds the callee's `cf` into
  the caller via `bindResults`.  The branch then computes
  `op_top := op + 8*n` (three register doublings, since `evalPExpr` has
  no `Omul`) and stores `cf_out` at `mem[op_top + 0]`, leaving at `op`
  the memory `(mpnAddN a b false).1 ++ [cf]` = `addMagFull a b`, as the
  bridge spec requires.  Without the carry store,
  `signedAdd (false, [2^63]) (false, [2^63]) = (false, [0, 1])` would be
  met by `[0, 0]`.

  Branches (b), (c), (d) do not suffer the carry-loss issue: they use
  `mpn_sub_n` on larger-minus-smaller, whose borrow-out is forced to
  `false` by `MpnSignedSpec.mpnSubN_exact`, so the |a|-limb result fits
  exactly and the zero-padded top limb (`k = 1`) matches `signedAdd`'s
  different-sign output.

`#print axioms` for the proved theorems reports only the kernel trio
(`propext`, `Classical.choice`, `Quot.sound`) plus `bv_decide` natives
inherited from `MpnMulJasminRefines_holds` (for the Mul bridge).  The
`MpzAddJasminRefines` Prop is a recorded statement, not a theorem — it
carries no axioms because it has no proof yet. -/

#print axioms mpnAddNFd_body_noCcall
#print axioms mpnSubNFd_body_noCcall
#print axioms mpnCompareFd_body_noCcall
#print axioms toNat_replicate_zero
#print axioms toNat_append_zero_pad
#print axioms resultInt_eq_toInt
#print axioms mpz_add_int_correct
#print axioms bitvec_xor_eq_xor_bool
#print axioms mulBody_run_signedRegistry
#print axioms MpzMulJasminRefines_holds
#print axioms mpz_mul_int_correct
#print axioms signedAdd_negate_eq_signedSub
#print axioms decode_xor_one
#print axioms MpzSubJasminRefines_of_add
#print axioms mpz_sub_int_correct

/-! ## §11  Sanity checks (the algorithm-level identities re-stated)

Re-stating that the bridges, once closed, imply the headline `Int`
identities — exactly the `signed_layer_correct` triple of
`MpnSignedSpec.§5`. -/

example (x y : Signed) (hlen : x.2.length = y.2.length) :
    toInt (signedAdd x y) = toInt x + toInt y :=
  signedAdd_toInt x y hlen

example (x y : Signed) (hlen : x.2.length = y.2.length) :
    toInt (signedSub x y) = toInt x - toInt y :=
  signedSub_toInt x y hlen

example (x y : Signed) :
    toInt (signedMul x y) = toInt x * toInt y :=
  signedMul_toInt x y

end CatCrypt.Crypto.Jasmin.Examples.MpnSignedJasminPrototype
