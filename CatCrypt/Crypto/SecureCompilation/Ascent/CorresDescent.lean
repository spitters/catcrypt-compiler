/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh

/-!
# The descent's contract in the ascent weld's shape

The relational compiler lowers a Lean field computation to a `Com fieldDialect`
fragment and certifies it with `FRefines spec frag`: for every continuation `k`
and every view `V`, `(frag k).denote V = k.denote (spec V)`. The ascent leg's
weld `corresScalar_frontDenote` concludes, for the program it reads off a
`LowCT`, `com.denote V = fa a dst`: the lowered program's denotation is the
abstract transformer's output at the destination.

`frefines_ret` is `FRefines` at the returning continuation `Com.ret v`, and
states the descent's contract in that same shape: the fragment closed with a
return denotes to the abstract step's output at `v`. Each leg concludes a
denotation equality, so for one program reached by both they would compose by
transitivity.

No such program is stated here, and the dialects differ: `frefines_ret` is over
`Com fieldDialect`, while `corresScalar_frontDenote` concludes over
`Com catCryptDialect`, and the package contains no program to which both apply.
The descent builds its `Com` from the Lean source; the ascent reads a `Com` off a
`LowCT` through `translateDialectControl`. At the `LowCT` level, `LegWeld.legWeld`
states the identity for any straight-line word kernel: the descent's `RRefines`,
the front's translation and the ascent's `Corres` are indexed by one term, and the
two semantics of that term are reconciled by `LegWeld.agreeRun`. At the x86 machine,
`XrunRunBlockTie.corres_of_refines_x86_runBlock` states a descent result as a
correspondence over the same `runBlock` blocks the ascent's x86 solver refines.
`PipelineWeld.feSub_raw_source_to_bytes` conjoins the feSub capstone with a statement
about a raw hax `ImpExpr` through its output word.

## Main definitions

* `frefines_ret` — `FRefines` at the returning continuation
* `dotFrag_ret` — the instance on the relational compiler's dot product
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
open CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh.Demo

/-- A fragment closed with `Com.ret v` denotes to the abstract step's output at
    `v`. -/
theorem frefines_ret {Γ Δ : Ctxt fieldDialect}
    {spec : FStateStep Γ Δ} {frag : FFrag Γ Δ} (h : FRefines spec frag)
    {s : FieldTy} (V : FView Γ) (v : Ctxt.Var Δ s) :
    (frag (Com.ret v)).denote V = v.lookup (spec V) :=
  h V (Com.ret v)

/-- The relational compiler's dot product, closed with a return, denotes to
    `dotStep` at that variable. -/
theorem dotFrag_ret (p : Nat) {s : FieldTy} (V : FView (Γ₀ p))
    (v : Ctxt.Var (Δout p) s) :
    (dotFrag p (Com.ret v)).denote V = v.lookup (dotStep p V) :=
  frefines_ret (dotFrag_refines p) V v

end CatCrypt.Crypto.SecureCompilation.Ascent
