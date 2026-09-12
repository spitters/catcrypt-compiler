/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.BindAlign

/-!
# `bind_align` — re-export of the canonical CatCryptCore tactic

The `bind_align` / `bind_step` tactics (peel matching `SPComp.bind` layers from a
goal equality) live canonically in `CatCryptCore/Tactics/BindAlign.lean`, under the
same `CatCrypt.Tactic` namespace. This module used to define its own identical copy;
importing both into one environment (e.g. the `CryptoBridgesAll` aggregate) clashed —
both packages declared `CatCrypt.Tactic.tacticBind_step`. It now simply re-exports the
core definition, so existing `import CatCrypt.Tactic.BindAlign` sites keep working with
a single source of truth.
-/

@[expose] public section
