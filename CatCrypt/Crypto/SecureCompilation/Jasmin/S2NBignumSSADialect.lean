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

This module states the s2n-bignum SSA reference results (`S2NBignumSSA`) on
`catCryptDialect`: for each of the single-input and two-input ALU-spine ports
`Simple`, `WordAvg`, `ByteReverse` and `NegModInv`, the dialect SSA program
produced by `translateMonoCmdD` denotes the port's reference semantics `refSem`.

For the `simple.s` Atlas tutorial port, `Simple.dialect_denote` is stated over
`Com.denoteSP (translateMonoCmdD …)` (the dialect SSA form) and proves the
bignum semantics `Simple.refSem`, hence the `SIMPLE_SPEC` post-condition
`r = a`.

## How the transport works

The kernels are discharged by the **native** dialect-translator correctness
`translateMonoCmdD_denoteSP_native` (in `JasminToSSADialectNative`):

```
Com.denoteSP (translateMonoCmdD m r cmd) (toVIRVal V)
  = SPComp.pure (pureEvalMonoCmd n env r cmd)
```

under the simulation invariant `monoAgrees m V env`. `translateMonoCmdD` emits
`Com catCryptDialect` ops directly from the Jasmin AST, and that lemma is proved
**directly by induction on the command**, computing `Com.denoteSP` through each
translated arm's dialect-op denotation.
`#print axioms` on each `dialect_denote` reports only
`[propext, Classical.choice, Quot.sound]`.

At the kernel level this module instantiates
`translateMonoCmdD_denoteSP_native` at each port's body, with a `monoAgrees`
witness of the port's input arity.

## Scope

* **Reaches**: the full `translateMonoCmdD` reference layer — the dialect
  denotation `Com.denoteSP` of the translated program equals
  `pureEvalMonoCmd`, hence (composing the existing `Simple.spec`) the ARM
  `SIMPLE_SPEC` post-condition `r = a`. The pure ALU spine
  (copy/add/sub/mul/and/xor/or/not/shift/const/ret) plus the `ADD_64`/`ADC_64`
  carry intrinsics — everything every `S2NBignumSSA` port in this kernel uses —
  is the fragment `translateMonoCmdD` fully covers and that the native lemma
  proves.
* The statements and proofs mention only `Com.denoteSP` over the dialect, the
  native translator, and the `monoAgrees` witness.
* The `bignumExecM` symbolic-execution Hoare machinery used by the multi-limb
  bignum files has no dialect analogue, so their Hoare-level obligations are
  outside the scope of this route.
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

The body is translated by the dialect translator and its reference semantics
`refSem a b` follows from the native correctness
`translateMonoCmdD_denoteSP_native`. -/

namespace Simple

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.Simple (body refSem spec)

/-- The two-input variable map for the `simple.s` port:
    `x0 ↦ .here`, `x1 ↦ .there .here`. -/
def m1 : MonoVarMap [.sword 64, .sword 64] 64 :=
  (MonoVarMap.extend (n := 64) (MonoVarMap.extend MonoVarMap.empty (v "x1")) (v "x0"))

/-- The **dialect** SSA program for `simple.s`, produced by the
    dialect-targeting translator `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64, .sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "r") body

/-- The reference environment used by `Simple.refSem`. -/
def env (a b : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "x0" then a else if w = v "x1" then b else 0

/-- `m1` agrees with the input valuation under `env`. -/
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

/-- **Reference semantics on the dialect.** Whenever the dialect translation
    succeeds (`dprog = some dp`), the dialect SSA program's `SPComp`-valued
    security denotation `Com.denoteSP` equals `SPComp.pure (refSem a b)`.

    Proof: instantiate `translateMonoCmdD_denoteSP_native` at the `simple.s` body
    with the `monoAgrees` witness `agrees`; `refSem` is `pureEvalMonoCmd … body`
    by definition. -/
theorem dialect_denote
    (dp : Com catCryptDialect [.sword 64, .sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a b : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a (.cons b .nil))) =
      SPComp.pure (refSem a b) := by
  -- `dprog` is the dialect program over `m1`; unfold to the underlying
  -- `translateMonoCmdD …` and discharge via the native translator correctness.
  have h_dprog' : translateMonoCmdD m1 (v "r") body = some dp := h_dprog
  have h := translateMonoCmdD_denoteSP_native m1 (.cons a (.cons b .nil)) (env a b)
    (v "r") body dp (agrees a b) h_dprog'
  -- `refSem a b = pureEvalMonoCmd 64 (env a b) (v "r") body` by definition.
  exact h

/-- **End-to-end on the dialect.** The dialect SSA program denotes
    `SPComp.pure a`, the `SIMPLE_SPEC` post-condition `r = a`. -/
theorem dialect_eq_input
    (dp : Com catCryptDialect [.sword 64, .sword 64] (.sword 64))
    (h_dprog : dprog = some dp)
    (a b : BitVec 64) :
    Com.denoteSP dp (toVIRVal (.cons a (.cons b .nil))) = SPComp.pure a := by
  rw [dialect_denote dp h_dprog a b, spec a b]

end Simple

/-! ## Further s2n-bignum SSA reference results on the dialect

The kernels below follow the `Simple` template: each reference theorem is
obtained by instantiating the native correctness
`translateMonoCmdD_denoteSP_native` with the kernel's input-arity
`monoAgrees` witness (as in `Simple.agrees`). They are the pure ALU-spine
kernels that `translateMonoCmdD` fully covers:

* `WordAvg`   — 2-input bitwise average `(a&b) + ((a^b)>>1)`;
* `ByteReverse` — 1-input 64-bit byte reversal (mask/ror/or spine);
* `NegModInv` — 1-input Newton negated modular inverse (mul/add/xor/shl spine).

Multi-limb bignum kernels rest on the `bignumExecM` symbolic-execution Hoare
machinery, which has no dialect analogue, and are outside the scope of this
`translateMonoCmdD` route. -/

/-! ### `word_avg` port on `catCryptDialect`

`S2NBignumSSA.WordAvg` ports the bitwise average: `(a&b) + ((a^b)>>1)`. -/

namespace WordAvg

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.WordAvg (body refSem)

/-- Two-input variable map for `word_avg`: `a ↦ .here`, `b ↦ .there .here`. -/
def m1 : MonoVarMap [.sword 64, .sword 64] 64 :=
  (MonoVarMap.extend (n := 64) (MonoVarMap.extend MonoVarMap.empty (v "b")) (v "a"))

/-- The dialect SSA program for `word_avg`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64, .sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `WordAvg.refSem`. -/
def env (a b : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else if w = v "b" then b else 0

/-- `m1` agrees with the input valuation under `env`. -/
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

/-- **Reference semantics on the dialect.** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a b)`,
    the bitwise-average semantics; proved through
    `translateMonoCmdD_denoteSP_native`. -/
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

/-! ### `word_bytereverse` port on `catCryptDialect`

`S2NBignumSSA.ByteReverse` ports the 64-bit byte reversal. One input. -/

namespace ByteReverse

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.ByteReverse (body refSem)

/-- One-input variable map for the port: `a ↦ .here`. -/
def m1 : MonoVarMap [.sword 64] 64 :=
  MonoVarMap.extend MonoVarMap.empty (v "a")

/-- The dialect SSA program for `word_bytereverse`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `ByteReverse.refSem`. -/
def env (a : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else 0

/-- `m1` agrees with the one-input valuation under `env`. -/
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

/-- **Reference semantics on the dialect.** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a)`, the
    64-bit byte-reversal semantics; proved through
    `translateMonoCmdD_denoteSP_native`. -/
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

/-! ### `word_negmodinv` port on `catCryptDialect`

`S2NBignumSSA.NegModInv` ports the Newton negated modular inverse. One input.
The Newton correctness spec (`word_negmodinv_correct`) is also stated on the
dialect for odd inputs. -/

namespace NegModInv

open CatCrypt.Crypto.Jasmin.S2NBignumSSA.NegModInv (body refSem word_negmodinv_correct)

/-- One-input variable map for the port: `a ↦ .here`. -/
def m1 : MonoVarMap [.sword 64] 64 :=
  MonoVarMap.extend MonoVarMap.empty (v "a")

/-- The dialect SSA program for `word_negmodinv`, via `translateMonoCmdD`. -/
def dprog : Option (Com catCryptDialect [.sword 64] (.sword 64)) :=
  translateMonoCmdD m1 (v "ret") body

/-- The reference environment used by `NegModInv.refSem`. -/
def env (a : BitVec 64) : Var → BitVec 64 :=
  fun w => if w = v "a" then a else 0

/-- `m1` agrees with the one-input valuation under `env`. -/
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

/-- **Reference semantics on the dialect.** The dialect SSA program's
    `SPComp`-valued security denotation equals `SPComp.pure (refSem a)`, the
    Newton negated-modular-inverse semantics; proved through
    `translateMonoCmdD_denoteSP_native`. -/
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

/-- **End-to-end Newton correctness on the dialect** (with
    `S2NBignumSSA.NegModInv.word_negmodinv_correct`). For every odd `a`,
    the dialect SSA program denotes `SPComp.pure (refSem a)` where
    `a · refSem a + 1 = 0`, the negated-modular-inverse post-condition. -/
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
