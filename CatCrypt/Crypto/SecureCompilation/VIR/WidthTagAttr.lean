/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The `width_tag` simp set

`width_tag` is the simp set that reads a width-tagged mnemonic (`withWidthTag`) through
`untagCaret` and `stripWidthTag`, and evaluates `untagCaret` on the literal mnemonics the
address machine compares against. A simp attribute cannot be used in the module that
registers it; the members are tagged in `VIR.WidthTagSimp` and in the modules above it.
-/

@[expose] public section

/-- Simp set for width-tagged mnemonics: `untagCaret` and `stripWidthTag` on a `withWidthTag`
    form and on the literal mnemonics of the address machine. -/
register_simp_attr width_tag
