/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ScalarLin

/-!
# Backend-neutral `RegProg` semantics — so the de-Bruijn proof is proved ONCE

The `Com → RegProg` de-Bruijn/`HVector` faithfulness proof is the expensive part.
This module makes it provable **once, against a backend-neutral register
semantics**, so every backend inherits it rather than re-proving it per ISA.

The three layers:

1. **`evalRegStmtPure` / `RegProg.denotePure`** — the canonical `RegProg`
   semantics over a plain register environment `Env = String → BitVec 64`, using
   the dialect op functions. The de-Bruijn proof targets *this* (it mentions no
   backend).
2. **`ScalarTarget.compile_denote_pure`** (this file, generic) — for ANY backend
   with a register projection `proj : St → Env` whose `step` agrees with
   `evalRegStmtPure` on the projection, the machine run projected to `Env`
   computes `denotePure`. Proved once, over an abstract `ScalarTarget`.
3. Each backend supplies only `proj` + a one-line `cases <;> rfl` agreement.

So: prove the de-Bruijn lemma once against `denotePure`; compose with
`compile_denote_pure` (already generic) to get `Com → AArch64`, `Com → RISC-V`,
`Com → x86`, `Com → GPU` faithfulness — no per-backend de-Bruijn proof.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. The neutral register environment + semantics -/

/-- A backend-neutral 64-bit register environment. -/
abbrev Env := String → BitVec 64

namespace Env

/-- Read a register (`xzr` reads `0`). -/
def get (e : Env) (r : String) : BitVec 64 := if r = "xzr" then 0 else e r

/-- Write a register (`xzr` writes are discarded). -/
def set (e : Env) (r : String) (v : BitVec 64) : Env :=
  if r = "xzr" then e else (fun r' => if r' = r then v else e r')

/-- Reading back a just-written non-`xzr` register yields the written value. -/
theorem set_self (e : Env) (r : String) (v : BitVec 64) (h : r ≠ "xzr") :
    (Env.set e r v) r = v := by
  simp [Env.set, h]

/-- Writing one register does not change a different register. -/
theorem set_other (e : Env) (r r' : String) (v : BitVec 64) (h : r' ≠ r) :
    (Env.set e r v) r' = e r' := by
  by_cases hx : r = "xzr" <;> simp [Env.set, hx, h]

end Env

/-- The canonical, backend-neutral effect of one statement on the environment —
    the dialect op functions inlined (matching every backend's `op*`/`evalBInst`
    arms, which all compute these same `BitVec` operations). -/
def evalRegStmtPure (e : Env) : RegStmt → Env
  | .add d a b => e.set d (e.get a + e.get b)
  | .sub d a b => e.set d (e.get a - e.get b)
  | .mul d a b => e.set d (e.get a * e.get b)
  | .and d a b => e.set d (e.get a &&& e.get b)
  | .orr d a b => e.set d (e.get a ||| e.get b)
  | .eor d a b => e.set d (e.get a ^^^ e.get b)
  | .umulh d a b => e.set d (BitVec.ofNat 64 (((e.get a).toNat * (e.get b).toNat) >>> 64))
  | .shrI d a i => e.set d (e.get a >>> i)
  | .shlI d a i => e.set d (e.get a <<< i)
  | .mov d a => e.set d (e.get a)
  | .movz d i => e.set d (BitVec.ofNat 64 (i % 0x10000))
  | .movk d i h =>
      let lo := h * 16
      let mask : BitVec 64 := BitVec.ofNat 64 (0xffff <<< lo)
      e.set d ((e.get d &&& ~~~ mask) ||| (BitVec.ofNat 64 ((i % 0x10000) <<< lo)))
  | .loadImm d n => e.set d (BitVec.ofNat 64 n)

/-- The canonical denotation of a whole program. -/
def RegProg.denotePure (p : RegProg) (e : Env) : Env := p.foldl evalRegStmtPure e

@[simp] theorem RegProg.denotePure_nil (e : Env) : RegProg.denotePure [] e = e := rfl

@[simp] theorem RegProg.denotePure_cons (x : RegStmt) (xs : RegProg) (e : Env) :
    RegProg.denotePure (x :: xs) e = RegProg.denotePure xs (evalRegStmtPure e x) := rfl

/-- **`denotePure` runs a concatenation left-to-right** — the sequencing law the
    `.var e body` case of the de-Bruijn induction needs (run the binding's
    statements, then the rest). -/
theorem RegProg.denotePure_append (p q : RegProg) (e : Env) :
    RegProg.denotePure (p ++ q) e = RegProg.denotePure q (RegProg.denotePure p e) := by
  simp only [RegProg.denotePure, List.foldl_append]

/-! ## 2. The generic backend lift (proved once over an abstract `ScalarTarget`)

A backend "refines" the neutral semantics if it has a register projection
`proj : St → Env` whose `step` agrees with `evalRegStmtPure` after projection.
Then its machine run, projected, computes `denotePure`. -/

namespace ScalarTarget

/-- **The neutral lift.** For any backend with a projection whose `step` agrees
    with `evalRegStmtPure`, the projected machine run computes `denotePure` — the
    backend's whole machine semantics reduced to the canonical one, generically. -/
theorem compile_denote_pure (T : ScalarTarget) (proj : T.St → Env)
    (hstep : ∀ (s : T.St) (stmt : RegStmt),
      proj (T.step s stmt) = evalRegStmtPure (proj s) stmt)
    (p : RegProg) (s : T.St) :
    proj (T.runOps s (T.compile p)) = RegProg.denotePure p (proj s) := by
  rw [T.compile_denote]
  show proj (p.foldl T.step s) = p.foldl evalRegStmtPure (proj s)
  induction p generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← hstep]
      exact ih (T.step s x)

/-- **The restricted lift.** A backend whose `step` agrees with `evalRegStmtPure`
    on every statement satisfying `P` still computes `denotePure p` whenever every
    statement of `p` satisfies `P` — needed for backends faithful on the
    compiler-emitted op subset but not on the whole `RegStmt` alphabet (e.g. RISC-V,
    which does not realise the ARM-specific `movk`, an op the front never emits). -/
theorem compile_denote_pure_on (T : ScalarTarget) (proj : T.St → Env)
    (P : RegStmt → Prop)
    (hstep : ∀ (s : T.St) (stmt : RegStmt), P stmt →
      proj (T.step s stmt) = evalRegStmtPure (proj s) stmt)
    (p : RegProg) (hp : ∀ stmt ∈ p, P stmt) (s : T.St) :
    proj (T.runOps s (T.compile p)) = RegProg.denotePure p (proj s) := by
  rw [T.compile_denote]
  show proj (p.foldl T.step s) = p.foldl evalRegStmtPure (proj s)
  induction p generalizing s with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [← hstep s x (hp x (List.mem_cons.mpr (Or.inl rfl)))]
      exact ih (fun stmt h => hp stmt (List.mem_cons.mpr (Or.inr h))) (T.step s x)

end ScalarTarget

end CatCrypt.Crypto.SecureCompilation.ScalarLin
