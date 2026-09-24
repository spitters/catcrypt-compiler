/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCT


@[expose] public section
set_option autoImplicit false

/-!
# PROTOTYPE — MLIR/`scf` backend for the `mpn_add_n` runtime-length loop

**EXPERIMENTAL, EMIT-ONLY, NOT VERIFIED.**  This file is the MLIR-path
counterpart of the Jasmin-path prototype
`CatCrypt/Crypto/Jasmin/Mpn/AddPrototype.lean`.  Where that file
chose the Jasmin `Cwhile` route (option (b)) because the emitter, a
validated example, and a loop-aware interpreter already existed, this
file prototypes option (a): emit a real
runtime-length loop as MLIR `scf.while` so the kernel can flow
`MLIR → LLVM → {x86_64, AArch64}`.  That is the backend that earns the
Lean-TCB claim across architectures (the Jasmin backend is x86-64 only).

## Scope

* **(A) A textual MLIR `scf.while` emitter** (`emitMpnAddNScfWhile`) that
  produces the runtime loop analogue of the committed Jasmin
  `while (n != 0) { load a,b; adc; store; ptr += 8; n -= 1 }`.  The text
  it produces was confirmed to parse and verify with `mlir-opt-20`
  (LLVM 20.1.2, fully-registered `scf`/`memref`/`arith`/`func`
  dialects — no `--allow-unregistered-dialect` needed) and to lower
  end-to-end to the LLVM dialect via
  `--convert-scf-to-cf --convert-cf-to-llvm --finalize-memref-to-llvm
   --convert-arith-to-llvm --convert-func-to-llvm
   --reconcile-unrealized-casts`.  See `expectedMpnAddNScfWhile` for the
  exact captured text.

* **(B)+(C) Scoping + verified-lowering path**: in the prose below and in
  the report this file ships with.  No proof is claimed.

## This is a *text formatter*, not a verified lowering

Exactly like `LowCTToMLIR.lean`, the emitter here is an unverified
`String` formatter.  It is NOT routed through the verified
`LowCT → Com catCryptDialect → Veir/MLIR` chain, and it CANNOT be: that
chain's IR (`Com`, in
`CatCrypt/Crypto/SecureCompilation/VIR/Core.lean`) is, by its own
docstring, *"A program in A-normal form … and no regions."*  `scf.while`
*is* a region-carrying op.  Emitting it verified would require a
region-carrying loop construct in the in-tree VIR `Com` plus a denoting
loop op in a dialect — neither exists in the IR (see §"Dynamic-memref +
loop scoping" below).

`Examples/` is never imported by `Crypto`, so nothing security-relevant
depends on this file.

## Why `scf.while` (not `scf.for`)

`scf.for` has a statically-shaped trip count `(lo, hi, step)` and is the
natural target when the limb count `n` is an `index` SSA value (it is,
in the GMP ABI).  Both are emittable.  We emit `scf.while` here because
it most directly mirrors the Jasmin `while (n != 0)` guard and threads
the carry as an explicit loop-carried (iter) value, making the
denotation obligation (§) line up one-to-one with the Jasmin
`bignumExecFuel_loop_step` rule that the Jasmin prototype already proved.
A `scf.for` variant would carry `cf` via `iter_args` identically; the
verified-lowering obligation is the same shape.

## Dynamic-memref + loop scoping (deliverable B)

The committed `MlirMemrefDialect` (`MlirMemrefOp`) is **fixed-size**:

* `allocaZero (n : Nat)` carries a *static* element count `n`;
* `store (n : Nat) (i : Fin n)` / `load (n : Nat) (i : Fin n)` carry a
  *static, in-bounds* index `i : Fin n`;
* the denotation model is the pure function `Fin n → BitVec 64` (= the
  denotation of `CryptoTy.memref n`).

`mpn_add_n` over `memref<?xi64>` needs the runtime analogue:

* element count is a runtime `index` value, not a static `Nat`;
* the access index is a runtime `index` value, not a static `Fin n`;
* the natural denotation model becomes a *partial* dependent function or
  a length-tagged array: `Σ (len : Nat), Fin len → BitVec 64`, with an
  out-of-bounds policy (MLIR `memref.load` is UB on OOB — so the
  denotation would carry a side condition `i < len`, discharged from the
  loop invariant `0 ≤ i < n`).

So a `MlirMemrefDynOp` would look like (sketch, NOT added here):

```
inductive MlirMemrefDynOp where
  | allocaDyn                       -- memref.alloca(%len) : memref<?xi64>
  | storeDyn                        -- args: arr, v, idx ; ret: arr'
  | loadDyn                         -- args: arr, idx     ; ret: i64
```

with signatures taking the index as an *operand* (a `.sword 64`/`index`
SSA value) rather than an op parameter, and denotations
`loadDyn : (arr, i) ↦ if h : i.toNat < len then arr ⟨i.toNat, h⟩ else 0`.
The `agree_*`-style lemma cannot close by `rfl`: the source op
(`CatCryptOp.memrefGet n (i : Fin n)`) carries the bound *statically*,
the dynamic op carries it as a runtime value, so the agreement lemma must
assume `i.toNat < n` and rewrite the static `Fin n` access to the dynamic
one under that hypothesis.  **This is the first place the memref `agree`
proof stops being definitional.**

## What an `scf.while` `agree`/denotation lemma must state

The in-tree `Com` has no loop op, so before any lemma can be written the
framework needs a region-carrying construct.  The smallest believable
shape is a *bounded* loop op `forN` (mirroring the AST-level `LowCT.RFor
x (n : Nat) body`, which is structurally terminating — no fuel needed):

```
-- in a dialect that has regions (NOT today's Com):
forN (n : Nat) : region(carry → carry) → (carry → carry)
denote: forN n body init = Nat.rec init (fun k acc => body k acc) n
```

The denotation-preservation lemma the lowering must then prove is:

```
theorem agree_forN
    (body_src : ...catCryptDialect region...)
    (body_tgt : ...scf region...)
    (hbody : ∀ k acc, denote_src body_src k acc = denote_tgt body_tgt k acc) :
  denote_src (forN n body_src) init = denote_tgt (scf.for 0 n 1 body_tgt) init
```

i.e. *if the loop bodies agree pointwise on every iteration index and
accumulator, the whole loops agree* — proved by `Nat.rec` on the trip
count `n`.  This is exactly the structure of the Jasmin-side
`bignumExecFuel_loop_step` (one-iteration rule) + induction on the limb
list (`mpnAddN_loop` in `Mpn.AddPrototype.lean`). The **central
obligation** is the per-iteration body agreement `hbody` *plus* the
memref dynamic-index `agree` lemma (which, per above, is conditional on
`i < n` from the loop invariant).

## Smallest first verified milestone

NOT the full kernel.  The honest first milestone is:

  **A denoting bounded-loop op `forN` in a fresh region-carrying toy
  dialect, with `agree_forN` proved by `Nat.rec`, for a body that does
  ONE `loadDyn`/`storeDyn`/`addi` (no carry, no aliasing).**

That isolates the two new proof obligations (regions in the IR;
conditional dynamic-memref agreement) from the bignum-specific carry
chain (already proved on the Jasmin side, reusable verbatim).
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.MLIRBackend

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The `LowCT` runtime-loop term (AST level, existing constructors)

`mpn_add_n` expressed with the *existing* `LowCT` loop constructor
`RFor x n body` (structurally terminating, mirrors Bedrock2's bounded
`for`) plus the existing array element load/store (`RArrLoad`/`RArrStore`)
and multi-output call (`RCallN` for ADC).  No new AST constructor is
introduced.  This is the source the (future) verified MLIR `scf` emitter
would consume; today's `LowCTToMLIR.emitCmd` emits `// <RFor: not
emitted>` for it. -/

/-- A `u64`-typed scalar slot. -/
def u64 (s : String) : Located := { locVar := s, locSrc := .TU64 }

/-- A dynamic limb-array slot `memref<?xi64>`, modelled at the AST level as
    `TArr n .TU64` for a symbolic length `n` (the AST carries a `Nat`; the
    runtime-`?` nature shows up only at MLIR-emit time as `memref<?xi64>`). -/
def arr (s : String) (n : Nat) : Located := { locVar := s, locSrc := .TArr n .TU64 }

/-- One iteration body of `mpn_add_n`, indexed by the `RFor` loop variable
    `i`:  `a := ap[i]; b := bp[i]; (cf, sum) := adc(a, b, cf); op[i] := sum`.
    Pointer advancement is implicit in array indexing by `i` (the MLIR
    `scf.for`/`scf.while` analogue of the Jasmin pointer `+= 8`). -/
def loopBody (n : Nat) : LowCT :=
  .RSeq (.RArrLoad (u64 "a") (arr "ap" n) "i")
  (.RSeq (.RArrLoad (u64 "b") (arr "bp" n) "i")
  (.RSeq (.RCallN "adc" [u64 "cf", u64 "sum"] [u64 "a", u64 "b", u64 "cf"])
         (.RArrStore (arr "op" n) "i" (u64 "sum"))))

/-- Full `mpn_add_n` body at the AST level: zero the carry, then a bounded
    `RFor` over the `n` limbs. -/
def mpnAddNCmd (n : Nat) : LowCT :=
  .RSeq (.RLetU64Zero "cf" .RSkip)
        (.RFor "i" n (loopBody n))

/-! ## §2  Textual MLIR `scf.while` emitter (EMIT-ONLY)

A direct `String` writer for the runtime loop.  Parameterised only by the
function name; the limb count is the runtime `index` argument `%n` so the
emitted text is length-generic (`memref<?xi64>`), unlike the
unrolled X25519 path.  This text was validated with `mlir-opt-20`. -/

/-- Emit `mpn_add_n` as MLIR `scf.while` over `memref<?xi64>`.  Loop-carried
    values: the limb index `%i : index` and the carry `%cf : i64` (in
    `{0,1}`).  The ADC is open-coded as
    `sum0 = a+b; c1 = sum0 <u a; sum = sum0+cf; c2 = sum <u sum0;
     cf' = zext(c1 | c2)` — the standard two-add carry idiom (no `i65`
     widening, so it stays in the `arith`/`memref` core dialects). -/
def emitMpnAddNScfWhile (fname : String) : String :=
  let hdr :=
    "func.func @" ++ fname ++
    "(%op: memref<?xi64>, %ap: memref<?xi64>, %bp: memref<?xi64>, %n: index) {"
  String.intercalate "\n"
    [ hdr
    , "  %c0 = arith.constant 0 : index"
    , "  %c1 = arith.constant 1 : index"
    , "  %cf0 = arith.constant 0 : i64"
    , "  %res:2 = scf.while (%i = %c0, %cf = %cf0) : (index, i64) -> (index, i64) {"
    , "    %cond = arith.cmpi ne, %i, %n : index"
    , "    scf.condition(%cond) %i, %cf : index, i64"
    , "  } do {"
    , "  ^bb0(%i: index, %cf: i64):"
    , "    %a = memref.load %ap[%i] : memref<?xi64>"
    , "    %b = memref.load %bp[%i] : memref<?xi64>"
    , "    %sum0 = arith.addi %a, %b : i64"
    , "    %carry1 = arith.cmpi ult, %sum0, %a : i64"
    , "    %sum = arith.addi %sum0, %cf : i64"
    , "    %carry2 = arith.cmpi ult, %sum, %sum0 : i64"
    , "    %cor = arith.ori %carry1, %carry2 : i1"
    , "    %cfn = arith.extui %cor : i1 to i64"
    , "    memref.store %sum, %op[%i] : memref<?xi64>"
    , "    %inext = arith.addi %i, %c1 : index"
    , "    scf.yield %inext, %cfn : index, i64"
    , "  }"
    , "  return"
    , "}" ]

/-- The exact text `emitMpnAddNScfWhile "mpn_add_n"` produces, captured so a
    `#eval` / CI check can diff against it.  This string was confirmed to
    `mlir-opt-20`-parse, verify, and lower to the LLVM dialect. -/
def expectedMpnAddNScfWhile : String :=
"func.func @mpn_add_n(%op: memref<?xi64>, %ap: memref<?xi64>, %bp: memref<?xi64>, %n: index) {
  %c0 = arith.constant 0 : index
  %c1 = arith.constant 1 : index
  %cf0 = arith.constant 0 : i64
  %res:2 = scf.while (%i = %c0, %cf = %cf0) : (index, i64) -> (index, i64) {
    %cond = arith.cmpi ne, %i, %n : index
    scf.condition(%cond) %i, %cf : index, i64
  } do {
  ^bb0(%i: index, %cf: i64):
    %a = memref.load %ap[%i] : memref<?xi64>
    %b = memref.load %bp[%i] : memref<?xi64>
    %sum0 = arith.addi %a, %b : i64
    %carry1 = arith.cmpi ult, %sum0, %a : i64
    %sum = arith.addi %sum0, %cf : i64
    %carry2 = arith.cmpi ult, %sum, %sum0 : i64
    %cor = arith.ori %carry1, %carry2 : i1
    %cfn = arith.extui %cor : i1 to i64
    memref.store %sum, %op[%i] : memref<?xi64>
    %inext = arith.addi %i, %c1 : index
    scf.yield %inext, %cfn : index, i64
  }
  return
}"

/-- The emitter agrees with the captured expected text — a `decide`-level
    sanity check that the writer wasn't accidentally edited.  (This is a
    text-equality check, NOT a semantic correctness claim.) -/
theorem emit_eq_expected :
    emitMpnAddNScfWhile "mpn_add_n" = expectedMpnAddNScfWhile := by
  native_decide

/-! ## §3  Emission demos (`#eval`) -/

-- The real MLIR text.  Copy out of the info view and feed to `mlir-opt-20`.
#eval IO.println (emitMpnAddNScfWhile "mpn_add_n")

-- The AST source the verified emitter would (in future) consume; today's
-- `LowCTToMLIR.emitCmd` renders the `RFor` as `// <RFor: not emitted>`.
#eval (reprStr (mpnAddNCmd 4))

end CatCrypt.Crypto.Jasmin.Mpn.MLIRBackend
