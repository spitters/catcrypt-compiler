/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialect
public import CatCrypt.Crypto.SecureCompilation.Jasmin.JasminToSSADialectNative
public import CatCrypt.Crypto.Jasmin.S2NBignumRefSem

/-!
# s2n-bignum SSA reference results transported onto `catCryptDialect`

This is the batch of s2n-bignum SSA reference results transported off the
`CProg` inductive onto `catCryptDialect`, replicating the `Simple` template.
Each transported kernel is one more bignum reference result that no longer
rests on `CProg` — progress toward deleting `CProg`. After the full
single-input and two-input ALU-spine reference set transports (the
`cryptoSSA_denote` corollaries: `Simple`, `WordAvg`, `ByteReverse`,
`NegModInv`), only the
SSA-bridge re-point and the front-orphan trim remain before `CProg` can go.

This file is the keystone demonstration for **re-founding the s2n-bignum SSA
reference layer (`S2NBignumSSA`) on `catCryptDialect`**, the path to retiring
the `CProg` inductive.

It takes one concrete `S2NBignumSSA` reference result — the `simple.s` Atlas
tutorial port, whose CProg-side reference theorem is
`S2NBignumSSA.Simple.cryptoSSA_denote` (stated over `CProg.denote`, proved via
`translateMonoFun2_correct`) — and produces its `catCryptDialect` twin
`Simple.dialect_denote`, stated over `Com.denoteSP (translateMonoCmdD …)` (the
**dialect** SSA form). The twin proves the *same* bignum semantics
(`Simple.refSem`, hence the `SIMPLE_SPEC` post-condition `r = a`) lives on the
dialect, no longer resting on `CProg`.

## How the transport works (CProg-free, sorry-free)

The kernels are discharged by the **native** dialect-translator correctness
`translateMonoCmdD_denoteSP_native` (in `JasminToSSADialectNative`):

```
Com.denoteSP (translateMonoCmdD m r cmd) (toVIRVal V)
  = SPComp.pure (pureEvalMonoCmd n env r cmd)
```

under the simulation invariant `monoAgrees m V env`. `translateMonoCmdD` emits
`Com catCryptDialect` ops directly from the Jasmin AST, and that lemma is proved
**directly by induction on the command**, computing `Com.denoteSP` through each
translated arm's dialect-op denotation — it never mentions the `CProg`/`CExpr`
inductives or the `CExpr→dialect` translators `toVIRExprT`/`toVIRComT`.
`#print axioms`/`lean_verify` on each `dialect_denote` reports only
`[propext, Classical.choice, Quot.sound]` — sorry-free.

So all this file does at the kernel level is **instantiate**
`translateMonoCmdD_denoteSP_native` at the `simple.s` body, with the same
two-input `monoAgrees` witness that `translateMonoFun2_correct` builds
internally. The kernel's reference semantics now sits on the dialect, with no
`CProg` dependency.

## How far the transport reaches (honest)

* **Reaches**: the full `translateMonoCmdD` reference layer — the dialect
  denotation `Com.denoteSP` of the translated program equals
  `pureEvalMonoCmd`, hence (composing the existing `Simple.spec`) the ARM
  `SIMPLE_SPEC` post-condition `r = a`. The pure ALU spine
  (copy/add/sub/mul/and/xor/or/not/shift/const/ret) plus the `ADD_64`/`ADC_64`
  carry intrinsics — everything every `S2NBignumSSA` port in this kernel uses —
  is the fragment `translateMonoCmdD` fully covers and that the native lemma
  proves sorry-free.
* **`CProg`-specific layer that remains**: none for these reference theorems.
  Their statements and proofs mention only `Com.denoteSP` over the dialect, the
  native translator, and the `monoAgrees` witness. (The pre-existing
  `cryptoSSA_denote` corollaries on the `CProg` side still exist in
  `S2NBignumSSA`, but this file no longer depends on them.)

  Where a `CProg`-specific layer *would* remain is the `BignumStep` /
  `bignumExecM` symbolic-execution Hoare machinery used by the wider multi-limb
  bignum files — that has no dialect analogue yet, so those files' Hoare-level
  obligations would not transport by this route. The `simple.s`-class reference
  theorems do.

The remaining ~13 `S2NBignumSSA` `cryptoSSA_denote`-style results (NegModInv,
ByteReverse, WordAvg, …) follow this exact pattern: instantiate
`translateMonoCmdD_denoteSP_native` at their body with their input-arity
`monoAgrees` witness.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.S2NBignumSSADialect

open CatCrypt.Core (SPComp)
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.ToSSA
open CatCrypt.Crypto.Jasmin.ToSSADialect
open CatCrypt.Crypto.Jasmin.S2NBignumSSA (v)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP

set_option autoImplicit false

noncomputable section

/-! ## The `simple.s` port, transported onto `catCryptDialect`

`S2NBignumSSA.Simple` ports the Atlas tutorial `simple.s`:

```
t := x1 + x0
r := t  - x1     -- result r = x0
```

The CProg-side reference theorem is `S2NBignumSSA.Simple.cryptoSSA_denote`
(`prog.denote V = SPComp.pure (refSem a b)`). We rebuild the same body on the
dialect translator and transport that semantics via the CProg-free native
correctness `translateMonoCmdD_denoteSP_native`. -/

namespace Simple

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.Simple (body refSem spec)

/-- The two-input variable map, identical to the one `translateMonoFun2`
    uses for the `simple.s` port: `x0 ↦ .here`, `x1 ↦ .there .here`. -/
def m1 : MonoVarMap [.sword 64, .sword 64] 64 :=
  (MonoVarMap.extend (n := 64) (MonoVarMap.extend MonoVarMap.empty (v "x1")) (v "x0"))

/-- The **dialect** SSA program for `simple.s`, produced by the
    dialect-targeting translator `translateMonoCmdD` (the `catCryptDialect`
    twin of `translateMonoFun2`'s `translateMonoCmd`). -/
def dprog : Option (Com catCryptDialect [.sword 64, .sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "r") body

/-- The reference environment used by `Simple.refSem`. -/
def env (a b : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "x0" then a else if w = v "x1" then b else 0

/-- `m1` agrees with the input valuation under `env`. This is the same
    `monoAgrees` witness that `translateMonoFun2_correct` constructs internally
    for the `simple.s` port. -/
theorem agrees (a b : BitVec 64) :
    monoAgrees m1 (.cons a (.cons b .nil)) (env a b) := by
  intro w cv h_lookup
  simp only [m1, MonoVarMap.extend, MonoVarMap.empty, Option.map] at h_lookup
  simp only [env]
  split at h_lookup
  · rename_i h_eq
    simp only [Option.some.injEq] at h_lookup
    subst h_lookup
    simp [CVar.lookup, h_eq]
  · rename_i h_ne1
    split at h_lookup
    · rename_i cv' h_inner
      simp only [Option.some.injEq] at h_lookup
      subst h_lookup
      split at h_inner
      · rename_i h_eq2
        simp only [Option.some.injEq] at h_inner
        subst h_inner
        subst h_eq2
        simp [CVar.lookup, v]
      · exact absurd h_inner (by simp)
    · exact absurd h_lookup (by simp)

/-- **Transported reference semantics (dialect twin of
    `S2NBignumSSA.Simple.cryptoSSA_denote`).** Whenever the `CProg` translation
    succeeds (`S2NBignumSSA.Simple.prog = some prog`) and the dialect
    translation succeeds (`dprog = some dp`), the dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a b)` — the
    *same* bignum semantics the `CProg`-side `cryptoSSA_denote` gives, now
    stated over `Com.denoteSP` on `catCryptDialect` rather than over
    `CProg.denote`. **CProg-free**: routed through the native translator
    correctness `translateMonoCmdD_denoteSP_native`, so this statement no longer
    mentions the `CProg` inductive at all.

    Proof: instantiate `translateMonoCmdD_denoteSP_native` at the `simple.s` body
    with the `monoAgrees` witness `agrees`; `refSem` is `pureEvalMonoCmd … body`
    by definition. -/
theorem dialect_denote
    (dp : Com catCryptDialect [.sword 64, .sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a b : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a (.cons b .nil))) =
      SPComp.pure (refSem a b) := by
  -- `dprog` is the dialect twin over `m1`; unfold to the underlying
  -- `translateMonoCmdD …` and discharge via the **CProg-free** native
  -- translator correctness (no `prog`/`CProg` detour, sorry-free).
  have h_dprog' : translateMonoCmdD m1 (v "r") body = some dp := h_dprog
  have h := translateMonoCmdD_denoteSP_native m1 (.cons a (.cons b .nil)) (env a b)
    (v "r") body dp (agrees a b) h_dprog'
  -- `refSem a b = pureEvalMonoCmd 64 (env a b) (v "r") body` by definition.
  exact h

/-- **End-to-end on the dialect (twin of `S2NBignumSSA.Simple.cryptoSSA_eq_input`).**
    The dialect SSA program denotes `SPComp.pure a` — the `SIMPLE_SPEC`
    post-condition `r = a`, now living on `catCryptDialect`. -/
theorem dialect_eq_input
    (dp : Com catCryptDialect [.sword 64, .sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a b : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a (.cons b .nil))) = SPComp.pure a := by
  rw [dialect_denote dp h_dprog a b, spec a b]

end Simple

/-! ## Batch of further s2n-bignum SSA reference results transported

The kernels below replicate the `Simple` template exactly: each is one
`S2NBignumSSA` `cryptoSSA_denote`-style reference theorem moved off the
`CProg` inductive onto `catCryptDialect`, by instantiating the CProg-free
native correctness `translateMonoCmdD_denoteSP_native` with the kernel's
input-arity `monoAgrees` witness (mirroring `Simple.agrees`).

Covered here (the `S2NBignumSSA` ports that carry an explicit
`cryptoSSA_denote` corollary of `translateMonoFun{,2}_correct`, i.e. the pure
ALU-spine kernels `translateMonoCmdD` fully covers):

* `WordAvg`   — 2-input bitwise average `(a&b) + ((a^b)>>1)`;
* `ByteReverse` — 1-input 64-bit byte reversal (mask/ror/or spine);
* `NegModInv` — 1-input Newton negated modular inverse (mul/add/xor/shl spine).

The wider multi-limb bignum ports (`BignumAdd4`, `BignumMul4`, `BignumSqr4`,
`BignumModP25519_4`, …) define `body`/`refSem` but carry **no**
`cryptoSSA_denote` corollary — their reference layer rests on the
`BignumStep`/`bignumExecM` symbolic-execution Hoare machinery, which has no
dialect analogue, so they are out-of-template for this `translateMonoCmdD`
route (reported below, not a failure). -/

/-! ### `word_avg` port, transported onto `catCryptDialect`

`S2NBignumSSA.WordAvg` ports the bitwise average: `(a&b) + ((a^b)>>1)`. The
CProg-side reference theorem is `S2NBignumSSA.WordAvg.cryptoSSA_denote`. -/

namespace WordAvg

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.WordAvg (body refSem)

/-- Two-input variable map, identical to `translateMonoFun2`'s for `word_avg`:
    `a ↦ .here`, `b ↦ .there .here`. -/
def m1 : MonoVarMap [.sword 64, .sword 64] 64 :=
  (MonoVarMap.extend (n := 64) (MonoVarMap.extend MonoVarMap.empty (v "b")) (v "a"))

/-- The dialect SSA program for `word_avg`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64, .sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `WordAvg.refSem`. -/
def env (a b : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else if w = v "b" then b else 0

/-- `m1` agrees with the input valuation under `env` — the same `monoAgrees`
    witness `translateMonoFun2_correct` builds internally. -/
theorem agrees (a b : BitVec 64) :
    monoAgrees m1 (.cons a (.cons b .nil)) (env a b) := by
  intro w cv h_lookup
  simp only [m1, MonoVarMap.extend, MonoVarMap.empty, Option.map] at h_lookup
  simp only [env]
  split at h_lookup
  · rename_i h_eq
    simp only [Option.some.injEq] at h_lookup
    subst h_lookup
    simp [CVar.lookup, h_eq]
  · rename_i h_ne1
    split at h_lookup
    · rename_i cv' h_inner
      simp only [Option.some.injEq] at h_lookup
      subst h_lookup
      split at h_inner
      · rename_i h_eq2
        simp only [Option.some.injEq] at h_inner
        subst h_inner
        subst h_eq2
        simp [CVar.lookup, v]
      · exact absurd h_inner (by simp)
    · exact absurd h_lookup (by simp)

/-- **Transported reference semantics (dialect twin of
    `S2NBignumSSA.WordAvg.cryptoSSA_denote`).** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a b)` —
    the bitwise-average semantics, now on `catCryptDialect`. **CProg-free**:
    routed through `translateMonoCmdD_denoteSP_native`. -/
theorem dialect_denote
    (dp : Com catCryptDialect [.sword 64, .sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a b : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a (.cons b .nil))) =
      SPComp.pure (refSem a b) := by
  have h_dprog' : translateMonoCmdD m1 (v "ret") body = some dp := h_dprog
  have h := translateMonoCmdD_denoteSP_native m1 (.cons a (.cons b .nil)) (env a b)
    (v "ret") body dp (agrees a b) h_dprog'
  -- `refSem a b = pureEvalMonoCmd 64 (env a b) (v "ret") body` definitionally.
  exact h

end WordAvg

/-! ### `word_bytereverse` port, transported onto `catCryptDialect`

`S2NBignumSSA.ByteReverse` ports the 64-bit byte reversal. The CProg-side
reference theorem is `S2NBignumSSA.ByteReverse.cryptoSSA_denote`. One input. -/

namespace ByteReverse

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.ByteReverse (body refSem)

/-- One-input variable map, identical to `translateMonoFun`'s for the port:
    `a ↦ .here`. -/
def m1 : MonoVarMap [.sword 64] 64 :=
  MonoVarMap.extend MonoVarMap.empty (v "a")

/-- The dialect SSA program for `word_bytereverse`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `ByteReverse.refSem`. -/
def env (a : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else 0

/-- `m1` agrees with the input valuation under `env` — the same `monoAgrees`
    witness `translateMonoFun_correct` builds internally (one input). -/
theorem agrees (a : BitVec 64) :
    monoAgrees m1 (.cons a .nil) (env a) := by
  intro w cv h_lookup
  simp only [m1, MonoVarMap.extend, MonoVarMap.empty] at h_lookup
  simp only [env]
  split at h_lookup
  · rename_i h_eq
    simp only [Option.some.injEq] at h_lookup
    subst h_lookup
    simp [CVar.lookup, h_eq]
  · exact absurd h_lookup (by simp)

/-- **Transported reference semantics (dialect twin of
    `S2NBignumSSA.ByteReverse.cryptoSSA_denote`).** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a)` — the
    64-bit byte-reversal semantics, now on `catCryptDialect`. **CProg-free**:
    routed through `translateMonoCmdD_denoteSP_native`. -/
theorem dialect_denote
    (dp : Com catCryptDialect [.sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a .nil)) =
      SPComp.pure (refSem a) := by
  have h_dprog' : translateMonoCmdD m1 (v "ret") body = some dp := h_dprog
  have h := translateMonoCmdD_denoteSP_native m1 (.cons a .nil) (env a)
    (v "ret") body dp (agrees a) h_dprog'
  -- `refSem a = pureEvalMonoCmd 64 (env a) (v "ret") body` definitionally.
  exact h

end ByteReverse

/-! ### `word_negmodinv` port, transported onto `catCryptDialect`

`S2NBignumSSA.NegModInv` ports the Newton negated modular inverse. The
CProg-side reference theorem is `S2NBignumSSA.NegModInv.cryptoSSA_denote`.
One input. We additionally transport the Newton correctness spec
(`word_negmodinv_correct`) onto the dialect for odd inputs. -/

namespace NegModInv

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.NegModInv (body refSem word_negmodinv_correct)

/-- One-input variable map, identical to `translateMonoFun`'s for the port:
    `a ↦ .here`. -/
def m1 : MonoVarMap [.sword 64] 64 :=
  MonoVarMap.extend MonoVarMap.empty (v "a")

/-- The dialect SSA program for `word_negmodinv`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `NegModInv.refSem`. -/
def env (a : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else 0

/-- `m1` agrees with the input valuation under `env` — the same `monoAgrees`
    witness `translateMonoFun_correct` builds internally (one input). -/
theorem agrees (a : BitVec 64) :
    monoAgrees m1 (.cons a .nil) (env a) := by
  intro w cv h_lookup
  simp only [m1, MonoVarMap.extend, MonoVarMap.empty] at h_lookup
  simp only [env]
  split at h_lookup
  · rename_i h_eq
    simp only [Option.some.injEq] at h_lookup
    subst h_lookup
    simp [CVar.lookup, h_eq]
  · exact absurd h_lookup (by simp)

/-- **Transported reference semantics (dialect twin of
    `S2NBignumSSA.NegModInv.cryptoSSA_denote`).** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a)` — the
    Newton negated-modular-inverse semantics, now on `catCryptDialect`.
    **CProg-free**: routed through `translateMonoCmdD_denoteSP_native`. -/
theorem dialect_denote
    (dp : Com catCryptDialect [.sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a .nil)) =
      SPComp.pure (refSem a) := by
  have h_dprog' : translateMonoCmdD m1 (v "ret") body = some dp := h_dprog
  have h := translateMonoCmdD_denoteSP_native m1 (.cons a .nil) (env a)
    (v "ret") body dp (agrees a) h_dprog'
  -- `refSem a = pureEvalMonoCmd 64 (env a) (v "ret") body` definitionally.
  exact h

/-- **End-to-end Newton correctness on the dialect (twin of
    `S2NBignumSSA.NegModInv.word_negmodinv_correct`).** For every odd `a`,
    the dialect SSA program denotes `SPComp.pure (refSem a)` where
    `a · refSem a + 1 = 0` — the negated-modular-inverse post-condition,
    now living on `catCryptDialect`. -/
theorem dialect_correct
    (dp : Com catCryptDialect [.sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a : BitVec 64) (h_odd : a &&& 1 = 1) :
    Com.denoteSP dp (toVIRVal (.cons a .nil)) = SPComp.pure (refSem a)
      ∧ a * refSem a + 1 = 0 :=
  ⟨dialect_denote dp h_dprog a, word_negmodinv_correct a h_odd⟩

end NegModInv

end

end CatCrypt.Crypto.Jasmin.S2NBignumSSADialect
