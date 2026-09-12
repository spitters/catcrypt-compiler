/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefEmit

/-!
# Rendered-text checks on the owned whole-block ChaCha20 `.s`, as a program

Named Boolean checks on `Chacha20BlockFullMemrefEmit.chachaAtt`, the owned-backend
AT&T text of the whole ChaCha20 block, evaluated by running a compiled program
rather than at elaboration:

```
lake exe chacha20-block-full-memref-text-kat
```

## Main definitions

* `textChecks`: the checks, each paired with its name; the render is computed
  when the function is applied, after module initialisation.
* `main`: evaluates `textChecks`, exiting non-zero at the first failing check and
  naming it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefTextKat

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The rendered-text checks of `Chacha20BlockFullMemrefEmit.chachaAtt`: the
    export label `chacha20_block_owned` occurs, and the printer's `UNHANDLED`
    marker does not. -/
def textChecks (_ : Unit) : List (String × Bool) :=
  let att := Chacha20BlockFullMemrefEmit.chachaAtt
  [ ("chachaAtt contains chacha20_block_owned", strContains att "chacha20_block_owned")
  , ("chachaAtt lacks UNHANDLED", !strContains att "UNHANDLED") ]

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefTextKat

open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockFullMemrefTextKat in
def main : IO UInt32 := do
  let checks := textChecks ()
  for (nm, ok) in checks do
    unless ok do
      IO.eprintln s!"chacha20-block-full-memref-text-kat: check FAILED: {nm}"
      return 1
  IO.println s!"chacha20-block-full-memref-text-kat: {checks.length} text checks hold"
  return 0
