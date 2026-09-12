/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SecureCompileChain

/-!
# The secure-compilation capstone, exhibited (non-vacuity)

`SecureCompileChain` states the capstone abstractly. This file pins it on
concrete inputs so it is demonstrably **non-vacuous**:

* a constant-time source (`demoSrc`) compiled with a straight-line lowering
  reaches `.ok` with a `CompilableCT` (direct-addressing) block, and
  `secureCompile_constant_time` then yields a real constant-time guarantee on it;
* a secret-branching source (`secretSrc`) is **rejected** by the front gate —
  `secureCompile` returns `.error`, so the secure compiler refuses to emit it.

These are the positive/negative ends of "the compiler emits a CT block, or
refuses." The lowering used here is a trivial straight-line stand-in; the real
`ImpExpr → machine block` lowering (the regalloc/loop/conditional workstream)
plugs into the same `secureCompile` entry.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SecureCompileChainDemo

open CatCrypt.Crypto.SecureCompilation.SecureCompileChain
open CatCrypt.Crypto.SecureCompilation.ImpCTGate
open CatCrypt.Crypto.Optimizer.SecretType
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open _root_.Hax

/-! ## 1. A constant-time block + a straight-line lowering -/

/-- A tiny direct-addressing (hence `CompilableCT`) block: `mov a, 5; add a, 8`. -/
def demoBlock : List (JInstr 64) := [.mov "a" (.imm 5), .add "a" (.imm 8)]

/-- A constant-time source: a literal — no control flow at all. -/
def demoSrc : ImpExpr := .lit (.int 5)

/-- A straight-line stand-in lowering (always emits `demoBlock`). The real
    `ImpExpr → machine block` lowering plugs in here. -/
def demoLower : ImpExpr → Option (List (JInstr 64)) := fun _ => some demoBlock

/-! ## 2. Positive: the source compiles to a verified-CT block -/

/-- `secureCompile` accepts the CT source and returns the CT block. -/
theorem demo_ok :
    secureCompile SecEnv.pub demoLower demoSrc = .ok demoBlock := by
  rfl

/-- **The constant-time guarantee, concretely.** The emitted block's leakage
    trace is the same from any two states — a non-vacuous instance of
    `secureCompile_constant_time`. -/
theorem demo_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ demoBlock = blockLeak s₂ demoBlock :=
  secureCompile_constant_time demo_ok s₁ s₂

/-! ## 3. Negative: a secret-branching source is rejected -/

/-- The environment marking `k` secret. -/
def secEnv : SecEnv := SecEnv.set SecEnv.pub "k" SecretLevel.sec

/-- A source that branches on the secret `k` — outside the CT subset. -/
def secretSrc : ImpExpr :=
  .ifThenElse (.var "k") (.lit (.int 1)) (.lit (.int 0))

/-- The front gate rejects the secret branch: `impCTSafe` is `false`. -/
theorem secret_gate_rejects : impCTSafe secEnv secretSrc = false := by
  decide

/-- **The secure compiler refuses to emit the secret-branching source.**
    `secureCompile` returns `.error` (it never reaches `.ok`). -/
theorem secret_src_rejected :
    ∃ msg, secureCompile secEnv demoLower secretSrc = .error msg :=
  ⟨_, rfl⟩

end CatCrypt.Crypto.SecureCompilation.SecureCompileChainDemo
