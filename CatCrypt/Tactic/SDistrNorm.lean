/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SDist

/-!
# `sdistr_norm`: normalization of `SDistr` do-block goals

`do`-notation over `SDistr` elaborates to the typeclass heads `Bind.bind` /
`Pure.pure`, while the `SDistr` lemma library (`SDistr.bind_assoc`,
`SDistr.pure_bind`, `SDistr.uniform_bind_const`, game definitions written with
explicit `SDistr.bind`/`SDistr.pure`) is stated on the method heads. Neither
form's rewrite lemmas fire on the other's terms, so distribution-equality
proofs between a `do`-block game and a method-form game each carry local
`rfl`-bridge hypotheses. `sdistr_norm` packages the bridge and the monad-law
normalization in the working order: user-supplied definitional unfolds first
(so collapse lemmas whose left-hand side mentions `SDistr.pure` fire before the
bridge renames it), then the method→typeclass bridge, then the lawful-monad
normal form.

## Main definitions

* `SDistr.method_bind_eq`, `SDistr.method_pure_eq`: the `rfl` bridges from the
  method heads to the typeclass heads.
* `sdistr_norm`: normalize an `SDistr` goal to the typeclass heads in monad
  normal form.
* `sdistr_norm [defs]`: unfold `defs` first, then normalize.
* `absdiff_hop h`: close `a ≤ b + ε` from `h : absDiff a b ≤ ε` (or the
  commuted form), the distinguisher-hop calc step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Prob.SDistr

universe u v

variable {α : Type u} {β : Type u}

/-- The method-form bind is the typeclass bind. Oriented method → typeclass so
    that after rewriting, the lawful-monad lemmas (`bind_assoc`, `pure_bind`,
    `bind_pure`) apply to every bind in the goal. -/
theorem method_bind_eq (d : SDistr α) (f : α → SDistr β) :
    d.bind f = Bind.bind d f := rfl

/-- The method-form pure is the typeclass pure. Stated with `Pure.pure`
    explicitly: inside the `SDistr` namespace a bare `pure` resolves to
    `SDistr.pure` itself, which would make the bridge trivial. -/
theorem method_pure_eq (b : α) : (SDistr.pure b : SDistr α) = Pure.pure b := rfl

end CatCrypt.Prob.SDistr

namespace CatCrypt.Tactic

open CatCrypt.Prob

/-- Normalize an `SDistr` goal: rewrite the method heads `SDistr.bind` /
    `SDistr.pure` to the typeclass heads, then apply the lawful-monad laws.
    After `sdistr_norm`, both sides of a `do`-block-vs-method-form equality
    share the typeclass heads in monad normal form, so `SDistr.bind_comm` /
    `SDistr.uniform_bind_const` steps can be stated as `>>=`-form local
    `have`s (they typecheck by defeq) and rewritten directly. -/
macro "sdistr_norm" : tactic =>
  `(tactic| simp only [SDistr.method_bind_eq, SDistr.method_pure_eq,
      bind_assoc, pure_bind, bind_pure])

/-- `sdistr_norm [d₁, d₂, …]` unfolds the given definitions and collapse
    lemmas first — before the bridge renames `SDistr.pure`/`SDistr.bind`, so
    lemmas whose left-hand side mentions the method heads still fire — then
    normalizes. -/
macro "sdistr_norm" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (simp only [$args,*]
     try simp only [SDistr.method_bind_eq, SDistr.method_pure_eq,
       bind_assoc, pure_bind, bind_pure]))

/-- `absdiff_hop h` closes a goal `a ≤ b + ε` from `h : absDiff a b ≤ ε`,
    trying the commuted orientation as well — the distinguisher-hop calc step
    (`Real ≤ Ideal + ε` from a `*Secure` advantage bound, in either
    direction). -/
macro "absdiff_hop" h:term : tactic =>
  `(tactic| first
    | exact CatCrypt.Crypto.le_add_of_absDiff_le $h
    | exact CatCrypt.Crypto.le_add_of_absDiff_le
        (by rw [CatCrypt.Crypto.absDiff_comm]; exact $h))

end CatCrypt.Tactic
