/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSL
import CatCrypt.Crypto.Jasmin.RustEmit

/-!
# Safe-Rust emit of the X25519 ladder

Emits two Lean → safe-Rust functions:

  * `x25519_ladder255`     — the full 255-iter unrolled ladder.
                             Available but not currently consumed by
                             signal-wasm because the in-tree
                             `scalar_bit` leaf has no clean way to
                             receive its iteration index.
  * `x25519_ladder_step`   — one iteration of the ladder body.  The
                             Rust glue in
                             `signal-wasm/component/src/x25519.rs`
                             calls this 255 times.

Run via:

    lake env lean --run \
      CatCrypt/Crypto/Jasmin/Examples/X25519LadderDSLEmit.lean
-/

namespace CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSLEmit

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSL
open TowerType

def ladder255_params : List Located :=
  [ { locVar := "k",  locSrc := TFp25519 }
  , { locVar := "x1", locSrc := TFp25519 } ]

def ladder255_results : List Located :=
  [ { locVar := "out", locSrc := TFp25519 } ]

def emit_ladder255 : String :=
  ppRustFunction "x25519_ladder255" ladder255_params ladder255_results ladder255

/-- Per-iteration entry point. Inputs are `x1` (u-coord) and `swap`
    (current swap mask, broadcast as Fp25519 by the Rust glue);
    outputs are the four state-element refs `x2/z2/x3/z3`. -/
def step_params : List Located :=
  [ { locVar := "x1",   locSrc := TFp25519 }
  , { locVar := "swap", locSrc := TFp25519 } ]

def step_results : List Located :=
  [ { locVar := "x2", locSrc := TFp25519 }
  , { locVar := "z2", locSrc := TFp25519 }
  , { locVar := "x3", locSrc := TFp25519 }
  , { locVar := "z3", locSrc := TFp25519 } ]

def emit_ladder_step : String :=
  ppRustFunction "x25519_ladder_step" step_params step_results ladder_step_call

end CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSLEmit

/-- `lake env lean --run` entry point: write the per-step ladder body
    (the consumed artefact for signal-wasm/component) plus the full
    255-iter ladder for documentation.  Files go to a fixed path so
    `signal-wasm/component/build.rs` (or a manual copy step) can pick
    them up. -/
private def main : IO Unit := do
  let step_path := "/tmp/x25519_ladder_step.rs"
  let full_path := "/tmp/x25519_ladder255.rs"
  IO.FS.writeFile step_path
    CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSLEmit.emit_ladder_step
  IO.FS.writeFile full_path
    CatCrypt.Crypto.Jasmin.Examples.X25519LadderDSLEmit.emit_ladder255
  IO.println s!"wrote {step_path}"
  IO.println s!"wrote {full_path}"
