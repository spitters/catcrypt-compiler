/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTTypes

/-!
# Source-declared secrecy and its level table

`SourceSecrecy` records the per-binding secrecy a source secret-integer discipline
declares: the bindings whose source type is a secret integer, and the bindings
produced by an explicit `declassify()` downgrade. `SourceSecrecy.toLevelTable` is the
`LevelTable` it induces, in which a declassified binding is `Public`.

## Main definitions

* `SourceSecrecy` — the source secrecy record
* `SourceSecrecy.toLevelTable` — its level table
* `SourceSecrecy.declassify` — the source-level downgrade of one binding
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer

open CatCrypt.Crypto.Jasmin.LowCT

set_option autoImplicit false

/-- The per-binding secrecy a source secret-integer discipline declares, as
    carried out of extraction. `secret` lists the bindings whose *source* type is
    a secret integer; `declassified` lists the bindings produced by an explicit
    `declassify()` downgrade, the audit surface. Any binding in neither list is
    `Public` (the default). -/
structure SourceSecrecy where
  /-- Bindings whose source type is a secret integer. -/
  secret : List String
  /-- Bindings produced by an explicit `declassify()`, the trusted-downgrade
      audit surface. Overrides `secret`. -/
  declassified : List String

/-- The `LevelTable` a `SourceSecrecy` induces: `Public` unless the binding is a
    non-declassified secret. `declassify` wins over `secret` (a downgraded value
    is public). This is the table `cmdCT` consumes. -/
def SourceSecrecy.toLevelTable (s : SourceSecrecy) : LevelTable :=
  fun v =>
    if s.declassified.contains v then .Public
    else if s.secret.contains v then .Secret
    else .Public

/-- The source-level `declassify(v)`: mark binding `v` as downgraded to `Public`.
    This is the only Secret → Public transition, and the site is recorded in
    `declassified` for the audit. -/
def SourceSecrecy.declassify (s : SourceSecrecy) (v : String) : SourceSecrecy :=
  { s with declassified := v :: s.declassified }

end CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer
