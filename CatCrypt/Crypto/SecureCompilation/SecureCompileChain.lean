/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ImpCTGate
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT

/-!
# The secure-compilation capstone

This module composes the secure-compiler chain into one statement: **a source
program that passes the constant-time gate compiles to a constant-time machine
block.** It ties together

* the **front gate** — `ImpCTGate.impCTSafe` rejects any secret-dependent control
  surface, with `impCTSafe_NoSecretControl` proving the structural invariant
  (mine);
* the **machine guarantee** — `CompilableCT.constant_time`: a direct-addressing
  leaf has a state-independent (public-determined) leakage trace, the Phase-0
  target (mine);
* the **middle** — that the source→machine lowering carries the source's
  no-secret-control property to a `CompilableCT` machine block. This is the
  register-allocator / loop-unroll / conditional-lowering CT-preservation work
  (`Optimizer/RegAllocLeakTrace`, `X86Backend/{LoopUnroll,Cond,RejectLoop}`)
  proved on the other workstream; here it is the **named interface**
  `LoweringCTPreserving` the capstone consumes.

The two ends are proved here; the middle is an explicit hypothesis, so the
capstone is honest about exactly what the other workstream must deliver.

`secureCompile` is the consumable entry: it gates the source, lowers it, and
**re-checks `CompilableCT` at the machine level** — so `secureCompile_constant_time`
guarantees constant-time output *even if the lowering is untrusted* (defense in
depth: the front gate rejects bad sources early with a clear reason, and the
machine re-check is the backstop that the emitted block actually is CT).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SecureCompileChain

open CatCrypt.Crypto.SecureCompilation.ImpCTGate
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Hax (ImpExpr)

/-! ## 1. The middle interface (the other workstream's obligation) -/

/-- **The lowering CT-preservation interface.** A source→machine lowering `lower`
    is CT-preserving (under the secret environment `env`) when it carries a
    `NoSecretControl` source to a `CompilableCT` machine block. This is the
    contract the register-allocator / loop-unroll / conditional-lowering work
    discharges (their leakage-trace preservation across rename/spill + the
    public-bounded unrolling and public-conditioned `cmov` lowering). -/
def LoweringCTPreserving (env : SecEnv)
    (lower : ImpExpr → Option (List (JInstr 64))) : Prop :=
  ∀ (e : ImpExpr) (b : List (JInstr 64)),
    NoSecretControl env e → lower e = some b → CompilableCT b

/-! ## 2. The capstone: front gate + CT-preserving lowering ⇒ constant-time -/

/-- **Secure compilation.** If the source `e` passes the CT gate (`impCTSafe`) and
    the lowering is CT-preserving, the emitted machine block `b` has a
    state-independent leakage trace from any two initial states — it is
    constant-time. The front gate's structural invariant
    (`impCTSafe_NoSecretControl`) feeds the lowering interface, whose output
    `CompilableCT` discharges the machine guarantee (`CompilableCT.constant_time`,
    the Phase-0 keystone). -/
theorem secure_compile_constant_time {env : SecEnv}
    {lower : ImpExpr → Option (List (JInstr 64))}
    (hpre : LoweringCTPreserving env lower)
    {e : ImpExpr} {b : List (JInstr 64)}
    (hgate : impCTSafe env e = true) (hlower : lower e = some b)
    (s₁ s₂ : JState 64) :
    blockLeak s₁ b = blockLeak s₂ b :=
  CompilableCT.constant_time
    (hpre e b (impCTSafe_NoSecretControl env e hgate) hlower) s₁ s₂

/-! ## 3. The consumable entry (defense-in-depth) -/

/-- **The secure-compiler entry.** Gate the source, lower it, and re-check
    `CompilableCT` at the machine level:

    * secret-dependent control flow ⇒ rejected at the source (clear reason);
    * out of the translatable subset (`lower` returns `none`) ⇒ rejected;
    * a lowering that (somehow) produced a non-CT block ⇒ rejected by the machine
      re-check — so a *trusted* `lower` is not required for the CT guarantee.

    Returns the verified-CT block, or an error naming the violation. -/
def secureCompile (env : SecEnv)
    (lower : ImpExpr → Option (List (JInstr 64))) (e : ImpExpr) :
    Except String (List (JInstr 64)) :=
  if impCTSafe env e then
    match lower e with
    | some b =>
        if compilableCT? b then .ok b
        else .error "secure-compile: lowering produced a non-CT block \
          (register-indexed memory or a data-dependent branch)"
    | none => .error "secure-compile: source outside the translatable subset"
  else .error "secure-compile: source has secret-dependent control flow \
    (rejected by the constant-time gate)"

/-- **The entry's guarantee.** Whenever `secureCompile` returns a block, that
    block is constant-time — independent of whether `lower` is trusted, because
    the `.ok` branch is reached only when the machine-level `compilableCT?` check
    passes. -/
theorem secureCompile_constant_time {env : SecEnv}
    {lower : ImpExpr → Option (List (JInstr 64))} {e : ImpExpr}
    {b : List (JInstr 64)}
    (h : secureCompile env lower e = .ok b) (s₁ s₂ : JState 64) :
    blockLeak s₁ b = blockLeak s₂ b := by
  unfold secureCompile at h
  split at h
  · rename_i _hgate
    split at h
    · rename_i b' hlower
      split at h
      · rename_i hct
        -- `.ok b' = .ok b` ⇒ b' = b; the guard gave `compilableCT? b' = true`.
        have hbb : b' = b := by simpa using h
        rw [hbb] at hct
        exact CompilableCT.constant_time (compilableCT?_eq_true_iff b |>.mp hct) s₁ s₂
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The entry also takes no conditional branch (the branch half of CT). -/
theorem secureCompile_no_branch {env : SecEnv}
    {lower : ImpExpr → Option (List (JInstr 64))} {e : ImpExpr}
    {b : List (JInstr 64)}
    (h : secureCompile env lower e = .ok b) (s : JState 64) :
    (blockLeak s b).filter MLeak.isBranch = [] := by
  unfold secureCompile at h
  split at h
  · split at h
    · rename_i b' hlower
      split at h
      · rename_i hct
        have hbb : b' = b := by simpa using h
        rw [hbb] at hct
        exact CompilableCT.no_branch (compilableCT?_eq_true_iff b |>.mp hct) s
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

end CatCrypt.Crypto.SecureCompilation.SecureCompileChain
