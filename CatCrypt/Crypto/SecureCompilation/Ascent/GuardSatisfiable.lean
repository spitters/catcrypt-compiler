/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

/-!
# The guard-satisfiability obligation for `CorresJ` and `BytesCorresJ`

`CorresJ SR P fa c := ∀ st a, SR st a → P a → SR (runBlock st c) (fa a)` holds of
every block `c` whenever the state relation `SR` and the guard `P` share no
witness: the hypothesis `SR st a` is then never available together with `P a`, so
the conclusion is never exercised and the theorem says nothing about `c`.
`scripts/ascent-nonvacuity-ratchet.sh` already forces a satisfiability witness for
the named state relation `SR`, but not for the guard `P`, which in this tree is
almost always an inline lambda (`fun a => a.stage = 0 ∧ a.x < 2 ^ 384`); a
line-oriented script cannot name an inline lambda, let alone check it against the
state relation it is paired with.

`corresJ_guardSat` and `bytesCorresJ_guardSat` close that gap without any script
heuristic or source-text parsing. Each is the identity on a joint witness
`∃ st a, SR st a ∧ P a`, but its `SR`/`P` are *implicit*, so at a call site
`corresJ_guardSat foo_corresJ w` Lean's own unifier reads them off `foo_corresJ`'s
*elaborated* type — exactly the state relation and guard that theorem uses,
lambda and all — and then checks `w` against that pair. A mismatched or
insufficient witness is an ordinary type error, not a missed grep. The obligation
this turns into is a ordinary declaration in the library: for a concrete,
hypothesis-free `foo_corresJ : CorresJ SR P fa c`, a module states

```
theorem foo_corresJ_guardSat : ∃ st a, SR st a ∧ P a :=
  corresJ_guardSat foo_corresJ w
```

with the *same* `SR`/`P` written out (Lean checks the match), and `w` any term
of that type. `scripts/ascent-nonvacuity-ratchet.sh` is extended to require such a
declaration exist for every concrete `CorresJ`/`BytesCorresJ` theorem it can name
syntactically (see its header for what "concrete" and "name" mean there).

## Main results

* `corresJ_guardSat` — the `CorresJ` case.
* `bytesCorresJ_guardSat` — the `BytesCorresJ` case.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodedBlockCorres

/-- The state relation `SR` and the guard `P` of a `CorresJ SR P fa c` theorem `h`
    have a common witness, given one: `w`. Stated with `SR`/`P` implicit so that a
    call `corresJ_guardSat h w` reads them off `h`'s own elaborated type, not off
    a re-typed copy — a guard `h` states as an inline lambda is exactly the `P`
    this obligation is checked against. -/
theorem corresJ_guardSat {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {c : List (JInstr 64)}
    (_h : CorresJ SR P fa c) (w : ∃ st a, SR st a ∧ P a) :
    ∃ st a, SR st a ∧ P a :=
  w

/-- The `BytesCorresJ` counterpart of `corresJ_guardSat`: the state relation and
    guard of a `BytesCorresJ SR P fa n bs` theorem `h` have a common witness `w`,
    read off `h`'s own elaborated type. -/
theorem bytesCorresJ_guardSat {AState : Type} {SR : JState 64 → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {n : Nat} {bs : List (BitVec 8)}
    (_h : BytesCorresJ SR P fa n bs) (w : ∃ st a, SR st a ∧ P a) :
    ∃ st a, SR st a ∧ P a :=
  w

end CatCrypt.Crypto.SecureCompilation.Ascent
