/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresBridge
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-!
# The value-level middle tie for the scalar-arith fragment (Route B)

`corresJ_forget_to_corres` (`CorresBridge.lean`) transports a `CorresJ` over the
flag-carrying machine `runBlock` down to a `Corres` over the flag-free scalar
machine `semScalar`, but only under the hypothesis

```
hmirror : ∀ st, semScalar c_s (regEnv st) = some (regEnv (runBlock st c_J))
```

that the scalar program `c_s` *mirrors* the JInstr block `c_J`'s register effect
through the forgetful register view `regEnv`.  This module discharges the
**value-level core** of `hmirror` for the arithmetic-source fragment `ArithSrc`
(`x := a ⟨op⟩ b`, `LowCTToJInstrCT.lean`): reading only the **output** name
`dst`, the value `semScalar` assigns there equals the register `runBlock` of the
lowered JInstr leaves holds there.

## Why the read is restricted to `dst`

The whole-environment equality `hmirror` demands is genuinely **false** for
`ArithSrc`: `semScalar`'s `RScalarSetExpr` arm evaluates the source `SExpr` by
threading a chain of *fresh temporaries* (`semLowerSExpr`, the `__sx` namespace)
into the environment, and those temporary slots have no counterpart in the
machine run.  The environments therefore differ off `dst`.  Restricting the read
to the output name `dst` **quotients the temporaries out** — and `dst` is the
only slot the correspondence actually observes.

## The crux (`arith_middle_tie_at_dst`)

Both the scalar output value
`SExpr.evalBV (envReader (regEnv st)) p.toSExpr` and the machine output register
`(runBlock st (lowerArith id p)).regs p.dst` reduce to the **same** `BitVec 64`
operation (`+`/`&&&`/`^^^`/`*`) applied to `st.regs p.a` and `st.regs p.b`:

* on the scalar side, through `envReader_regEnv` (`envReader (regEnv st) =
  st.regs`) and `SExpr.evalBV`'s per-node homomorphism;
* on the machine side, through `ArithOp.toJInstr_word` on the `mov; op`
  two-instruction schedule (the `mov` primes `dst` with `a`, the op reads the
  now-`a` `dst` and the untouched `b`, needing `p.b ≠ p.dst`).

`semScalar` *succeeds* on the real `LowCT` node here because `regEnv st` binds
**every** name at `.sword 64`, so `semLowerSExpr`'s per-leaf `envReadU64` lookup
never fails — the success is proved by computation, not assumed.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LowCTToJInstrCT

/-- **The forgetful register view is the identity word-reader.**  Reading the
    `.sword 64` slot of `regEnv st` at every name recovers exactly the register
    file `st.regs`.  This is the bridge between the scalar `SExpr` word evaluator
    (`SExpr.evalBV`, which reads its `SVar` leaves through `envReader`) and the
    machine register file. -/
theorem envReader_regEnv (st : JState 64) : envReader (regEnv st) = st.regs := by
  funext r; simp [envReader, regEnv]

/-- Every name is bound at `.sword 64` in `regEnv st`, so the partial word-lookup
    `envReadU64` always succeeds — the fact that makes `semLowerSExpr` total on
    the register view (no fresh-temp lookup can fail). -/
theorem envReadU64_regEnv (st : JState 64) (x : String) :
    envReadU64 (regEnv st) x = some (st.regs x) := by
  simp [envReadU64, regEnv]

/-- **The machine output register of the lowered scalar-arith block.**  Running
    `lowerArith id p` (the identity register map: `regEnv` is the identity
    register-view, so `ρ = id`) from `st` leaves the destination register `dst`
    holding the `BitVec 64` op of the two source reads `st.regs a`, `st.regs b`.
    The `mov` primes `dst` with `a`; the op then reads the now-`a` `dst` and the
    untouched `b` (needing `p.b ≠ p.dst`). -/
theorem runBlock_lowerArith_id_dst (dst a b : String) (op : ArithOp)
    (st : JState 64) (hb : b ≠ dst) :
    (runBlock st (lowerArith id ⟨dst, a, op, b⟩)).regs dst =
      (match op with
       | .add  => st.regs a + st.regs b
       | .and_ => st.regs a &&& st.regs b
       | .xor_ => st.regs a ^^^ st.regs b
       | .mul_ => st.regs a * st.regs b) := by
  have hrun : runBlock st (lowerArith id ⟨dst, a, op, b⟩)
      = evalInstr (st.setReg dst (st.get a)) (op.toJInstr dst (.reg b)) := by
    simp only [lowerArith, id_eq, runBlock_cons, runBlock_nil, evalInstr, x86_MOV,
      JOperand.eval]
  have hword := ArithOp.toJInstr_word op dst b (st.setReg dst (st.get a))
  calc (runBlock st (lowerArith id ⟨dst, a, op, b⟩)).regs dst
      = (evalInstr (st.setReg dst (st.get a)) (op.toJInstr dst (.reg b))).get dst := by
        rw [hrun]; rfl
    _ = _ := by
        rw [hword]
        cases op <;> simp [JState.setReg, JState.get, hb]

/-- **The value-level middle tie for `ArithSrc`.**  `semScalar` succeeds on the
    real `LowCT` node `ArithSrc.toLowCT p = RScalarSetExpr p.dst p.toSExpr` over
    the forgetful register view `regEnv st`, and the value it writes at the
    **output** slot `p.dst` is exactly the machine's output register
    `(runBlock st (lowerArith id p)).regs p.dst`.

    Reading only `p.dst` quotients out `semLowerSExpr`'s fresh temporaries (the
    whole-environment equality is false — the temporary slots have no machine
    counterpart).  This is the Route-B increment toward making
    `corresJ_forget_to_corres`'s `hmirror` hypothesis a theorem. -/
theorem arith_middle_tie_at_dst (p : ArithSrc) (st : JState 64) (hb : p.b ≠ p.dst) :
    (∃ env', semScalar (ArithSrc.toLowCT p) (regEnv st) = some env'
      ∧ env' p.dst = some ⟨.sword 64, (runBlock st (lowerArith id p)).regs p.dst⟩) := by
  cases p with
  | mk dst a op b =>
    have hbv : b ≠ dst := hb
    rw [runBlock_lowerArith_id_dst dst a b op st hbv]
    cases op <;>
      · simp only [ArithSrc.toLowCT, ArithSrc.toSExpr, semScalar, semLowerSExpr,
          envReadU64, regEnv, binNode]
        refine ⟨_, rfl, ?_⟩
        simp [SEnvScalar.upd, envReader, regEnv, SExpr.evalBV]

end CatCrypt.Crypto.SecureCompilation.Ascent
