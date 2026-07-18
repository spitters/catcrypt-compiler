/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.Jasmin.JasminCT

/-!
# Syntactic constant-time predicate on `LowCT`

This file is the **Track C3 starting point** for constant-time (CT) on
pipeline (1)'s authoring AST. It mirrors the role of
`Crypto/Jasmin/JasminCT.lean`'s `isCT_Cmd` for pipeline (2): a syntactic,
decidable, structural whitelist over the AST that a downstream
preservation theorem can carry through to the CryptoSSA denotation.

## Design choice for this starting point

`LowCT` does **not currently carry secret/public tagging** on
variables. The two control-flow constructors that can leak —
`RIfNz` (branch on a scalar variable's value) and `RWhileNz` (loop while
a scalar variable is non-zero) — both inspect a `String`-named scalar
without any type-level information about whether that scalar is secret.

Three plausible designs:

1. **Reject all `RIfNz` / `RWhileNz`** — over-strict, but trivially
   sound: a program with no data-dependent control flow is constant-time
   at the AST level (modulo the leaf-call whitelist).
2. **Parameterise by a `Set String` of secret-named locals** — admits
   `RIfNz x t f` when `x` is *not* in the secret set. Still
   simple-minded (taint is name-level, no propagation analysis), but
   captures the common case where loop counters and length parameters
   live in distinct names from secret keys / scalars.
3. **Add a per-construct CT annotation** to `LowCT` itself — most
   expressive, but requires editing the AST in `Crypto/Jasmin/`, which
   is out of scope for this file (claimed by the active Lean terminal).

This file ships **Design 1** as the starting point — the over-strict but
unambiguously correct rule. Design 2 is left as a documented follow-up
(C3.1) below: it is a small additive refinement that doesn't touch the
AST.

A leaf-call whitelist is also part of the predicate: an `RCall` is CT
only when its function name is in a user-provided `Set String` of
"CT-cleared leaves" (analogous to `JasminCT.ct_intrinsic`). This matches
the pipeline (2) shape, where `Copn` is CT only for whitelisted
intrinsics.

## What this is *not*

This file is the **syntactic** half. The semantic bridge — proving
that `isCT_LowCT c` implies the CryptoSSA denotation of `translate c`
satisfies `ct_spComp` — is C3.2 (see follow-up notes). That requires
threading through `LowCTToCryptoSSA.lean` (which already produces
`none` on `RIfNz` / `RWhileNz` in the general case), so it composes
naturally with the over-strict rule here.

## Decidability

`isCT_LowCT` is `Bool`-valued, so `decide` discharges all ground
instances and `decide`-style smoke tests close. No separate
`DecidablePred` instance is needed (Lean infers it from the `Bool`
shape).
-/

namespace CatCrypt.Crypto.SecureCompilation.LowCTCT

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Syntactic CT predicate -/

/-- A "CT-cleared leaves" whitelist: names of `RCall` targets that the
caller has audited as constant-time leaves.

For the over-strict starting point this is just a `String → Bool`. A
follow-up can lift this to a typeclass-driven registry. -/
abbrev CTLeaves := String → Bool

/-- Syntactic constant-time predicate on `LowCT`.

**Over-strict rule (C3 starting point).** Rejects all data-dependent
control flow at the AST level:

* `RSkip`, `RSeq`, `RLetZero`, `RLetU64Zero`, `RScalarSet`,
  `RLimbStore` — always CT (no control-flow effect).
* `RCall f _ _` — CT iff `leaves f` (the leaf is on the audited list).
* `RCloneCall _ _ _ f _ _` — CT iff `leaves f` (the inner call's leaf
  is on the audited list); the clone itself is a `memcpy`-shape and
  CT.
* `RIfNz _ _ _` — **rejected**.
* `RWhileNz _ _` — **rejected**.

This is the safe lower bound. The follow-up C3.1 relaxes the `RIfNz` /
`RWhileNz` cases to allow branching on scalars that are not in a
"secrets" set; see the documented follow-ups at the bottom of this
file. -/
def isCT_LowCT (leaves : CTLeaves) : LowCT → Bool
  | .RSkip                           => true
  | .RSeq c1 c2                      => isCT_LowCT leaves c1
                                          && isCT_LowCT leaves c2
  | .RLetZero _ _ body               => isCT_LowCT leaves body
  | .RLetU64Zero _ body              => isCT_LowCT leaves body
  | .RScalarSet _ _                  => true
  | .RCall f _ _                     => leaves f
  | .RCloneCall _ _ _ innerF _ _     => leaves innerF
  | .RIfNz _ _ _                     => false   -- C3.1 follow-up: allow on non-secret guard
  | .RWhileNz _ _                    => false   -- C3.1 follow-up: allow on non-secret guard
  | .RFor _ _ body                   => isCT_LowCT leaves body
  | .RForRuntime _ _ body            => isCT_LowCT leaves body
  | .RLimbStore _ _ _                => true
  | .RLimbStoreExpr _ _ _            => true
  -- Phase F/G/H/L/M (2026-05-03): the new constructors are admitted
  -- by the over-strict CT predicate exactly when the corresponding
  -- leaf calls are; structural-only forms are accepted unconditionally.
  | .RCallSwap f _ _ _               => leaves f
  -- An inline asm op is CT iff its opcode is on the vendor DOIT∩DIT list
  -- (`ct_intrinsic` — CT_INSTRUCTION_REFERENCES.md §"Arithmetic/logic Copn").
  -- This **rejects** `DIV`/`IDIV`/`BSF`/`BSR`/FP/variable-latency opcodes,
  -- which are NOT on the list and would otherwise leak through timing.  It
  -- matches the back-end `isCT_InstrR` `Copn` clause, which gates the emitted
  -- `Copn (Oasm name)` on the same `ct_intrinsic name`, so the two predicates
  -- agree on `RAsmOp`.
  | .RAsmOp name _ _                 => CatCrypt.Crypto.Jasmin.ct_intrinsic name
  | .RCallN f _ _                    => leaves f
  | .RSelect _ _ _ _                 => true
  | .RAssert _                       => true
  | .RBlock body                     => isCT_LowCT leaves body
  | .RFnDef _ _ _ body cont          =>
      isCT_LowCT leaves body && isCT_LowCT leaves cont
  | .RFnCall f _ _                   => leaves f
  -- Phase I (2026-05-03): tuple component store/load is structural.
  | .RTupleStore _ _ _               => true
  | .RTupleLoad _ _ _                => true
  -- Phase Ext / Ext2 (2026-05-12, 2026-05-13): pure data-movement
  -- constructors landed in commits `022da829` and `425ef76a`.  None
  -- of these carry data-dependent control flow, so they're CT
  -- unconditionally — the leak trace for each is `[]` (see
  -- `LowCTLeakTrace.lean`).
  | .RArrStore _ _ _                 => true
  | .RArrLoad _ _ _                  => true
  | .RScalarSetExpr _ _              => true
  | .RBytesSlice _ _ _ _             => true
  -- Phase DD (2026-05-28): literal-index array access is pure
  -- data-movement (no data-dependent control flow), CT unconditionally.
  | .RArrStoreLit _ _ _              => true
  | .RArrLoadLit _ _ _               => true
  -- Phase E2 (2026-05-29): dst-threaded leaf call is CT iff the leaf is
  -- (same as `RCall`).
  | .RCallDstThreaded f _ _          => leaves f

/-! ## §2  Trivial structural lemmas -/

/-- `RSkip` is always CT. -/
@[simp] theorem isCT_RSkip (leaves : CTLeaves) :
    isCT_LowCT leaves .RSkip = true := rfl

/-- `RSeq` is CT iff both components are. (This is the **structural
preservation lemma** for the obvious composition case: a sequence is
CT iff each piece is, so a verified pass that preserves CT
componentwise preserves it on the sequence.) -/
@[simp] theorem isCT_RSeq (leaves : CTLeaves) (c1 c2 : LowCT) :
    isCT_LowCT leaves (.RSeq c1 c2)
      = (isCT_LowCT leaves c1 && isCT_LowCT leaves c2) := rfl

/-- `RLetZero` is CT iff its body is. -/
@[simp] theorem isCT_RLetZero (leaves : CTLeaves)
    (x : String) (t : TowerType) (body : LowCT) :
    isCT_LowCT leaves (.RLetZero x t body)
      = isCT_LowCT leaves body := rfl

/-- `RLetU64Zero` is CT iff its body is. -/
@[simp] theorem isCT_RLetU64Zero (leaves : CTLeaves)
    (x : String) (body : LowCT) :
    isCT_LowCT leaves (.RLetU64Zero x body)
      = isCT_LowCT leaves body := rfl

/-- `RScalarSet` is always CT (it sets a scalar to a literal). -/
@[simp] theorem isCT_RScalarSet (leaves : CTLeaves)
    (x : String) (v : Nat) :
    isCT_LowCT leaves (.RScalarSet x v) = true := rfl

/-- `RLimbStore` is always CT (it writes a literal to a known limb
index). -/
@[simp] theorem isCT_RLimbStore (leaves : CTLeaves)
    (loc : Located) (idx : Nat) (v : BitVec 64) :
    isCT_LowCT leaves (.RLimbStore loc idx v) = true := rfl

/-- `RIfNz` is rejected by the over-strict rule. -/
@[simp] theorem isCT_RIfNz_false (leaves : CTLeaves)
    (e : String) (ct cf : LowCT) :
    isCT_LowCT leaves (.RIfNz e ct cf) = false := rfl

/-- `RWhileNz` is rejected by the over-strict rule. -/
@[simp] theorem isCT_RWhileNz_false (leaves : CTLeaves)
    (e : String) (body : LowCT) :
    isCT_LowCT leaves (.RWhileNz e body) = false := rfl

/-! ### Sub-program closure

Reading `isCT_LowCT c = true` constructively: the `&&` in the `RSeq`
case factors out the two components. Below we extract each leaf as a
separate lemma so downstream proofs can `apply isCT_seq_left` /
`apply isCT_seq_right` without unfolding the predicate. -/

/-- If `RSeq c1 c2` is CT then so is `c1`. -/
theorem isCT_seq_left {leaves : CTLeaves} {c1 c2 : LowCT}
    (h : isCT_LowCT leaves (.RSeq c1 c2) = true) :
    isCT_LowCT leaves c1 = true := by
  have := h
  rw [isCT_RSeq] at this
  exact (Bool.and_eq_true _ _).mp this |>.1

/-- If `RSeq c1 c2` is CT then so is `c2`. -/
theorem isCT_seq_right {leaves : CTLeaves} {c1 c2 : LowCT}
    (h : isCT_LowCT leaves (.RSeq c1 c2) = true) :
    isCT_LowCT leaves c2 = true := by
  have := h
  rw [isCT_RSeq] at this
  exact (Bool.and_eq_true _ _).mp this |>.2

/-- Build `RSeq` CT-ness from componentwise CT-ness — the converse of
`isCT_seq_left`/`isCT_seq_right`. -/
theorem isCT_seq_intro {leaves : CTLeaves} {c1 c2 : LowCT}
    (h1 : isCT_LowCT leaves c1 = true)
    (h2 : isCT_LowCT leaves c2 = true) :
    isCT_LowCT leaves (.RSeq c1 c2) = true := by
  rw [isCT_RSeq, h1, h2]; rfl

/-- Body of `RLetZero` inherits CT from the whole. -/
theorem isCT_letZero_body {leaves : CTLeaves}
    {x : String} {t : TowerType} {body : LowCT}
    (h : isCT_LowCT leaves (.RLetZero x t body) = true) :
    isCT_LowCT leaves body = true := by
  rw [isCT_RLetZero] at h; exact h

/-- Body of `RLetU64Zero` inherits CT from the whole. -/
theorem isCT_letU64Zero_body {leaves : CTLeaves}
    {x : String} {body : LowCT}
    (h : isCT_LowCT leaves (.RLetU64Zero x body) = true) :
    isCT_LowCT leaves body = true := by
  rw [isCT_RLetU64Zero] at h; exact h

/-! ## §3  Leaf-whitelist monotonicity

If you enlarge the CT-cleared leaf set, anything previously CT remains
CT. This is the natural monotonicity for the predicate: predicate
sound for a small whitelist transfers to any larger one. -/

/-- Pointwise leaf-whitelist subsumption. -/
def CTLeavesSubsumes (a b : CTLeaves) : Prop :=
  ∀ s, a s = true → b s = true

/-- Monotonicity: enlarging the CT-cleared leaf whitelist preserves
`isCT_LowCT`. -/
theorem isCT_LowCT_mono {a b : CTLeaves}
    (hab : CTLeavesSubsumes a b) :
    ∀ c : LowCT, isCT_LowCT a c = true → isCT_LowCT b c = true := by
  intro c
  induction c with
  | RSkip => intro _; rfl
  | RSeq c1 c2 ih1 ih2 =>
      intro h
      rw [isCT_RSeq] at h ⊢
      have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      rw [ih1 h1, ih2 h2]; rfl
  | RLetZero _ _ body ih =>
      intro h
      rw [isCT_RLetZero] at h ⊢
      exact ih h
  | RLetU64Zero _ body ih =>
      intro h
      rw [isCT_RLetU64Zero] at h ⊢
      exact ih h
  | RScalarSet _ _ => intro _; rfl
  | RCall f _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab f h
  | RCloneCall _ _ _ innerF _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab innerF h
  | RIfNz _ _ _ _ _ =>
      intro h; simp only [isCT_LowCT] at h; cases h
  | RWhileNz _ _ _ =>
      intro h; simp only [isCT_LowCT] at h; cases h
  | RFor _ _ body ih =>
      intro h; simp only [isCT_LowCT] at h ⊢
      exact ih h
  | RForRuntime _ _ body ih =>
      intro h; simp only [isCT_LowCT] at h ⊢
      exact ih h
  | RLimbStore _ _ _ => intro _; rfl
  | RLimbStoreExpr _ _ _ => intro _; rfl
  -- Phase F/G/H/L/M (2026-05-03): mirror the existing patterns.
  | RCallSwap f _ _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab f h
  -- `RAsmOp` is gated on `ct_intrinsic name` (no `leaves` dependence), so
  -- the implication is the identity on `ct_intrinsic name = true`.
  | RAsmOp _ _ _ => intro h; exact h
  | RCallN f _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab f h
  | RSelect _ _ _ _ => intro _; rfl
  | RAssert _ => intro _; rfl
  | RBlock body ih =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact ih h
  -- Phase C: helper definition is the conjunction of its body+cont;
  -- helper call is treated like a leaf call.
  | RFnDef _ _ _ _ _ ih_body ih_cont =>
      intro h
      simp only [isCT_LowCT, Bool.and_eq_true] at h ⊢
      exact ⟨ih_body h.1, ih_cont h.2⟩
  | RFnCall f _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab f h
  | RTupleStore _ _ _ => intro _; rfl
  | RTupleLoad _ _ _ => intro _; rfl
  -- Phase Ext / Ext2 (2026-05-12, 2026-05-13): structural data-movement
  -- constructors — `isCT_LowCT` returns the constant `true`, so
  -- monotonicity is immediate.
  | RArrStore _ _ _ => intro _; rfl
  | RArrLoad _ _ _ => intro _; rfl
  | RScalarSetExpr _ _ => intro _; rfl
  | RBytesSlice _ _ _ _ => intro _; rfl
  -- Phase DD (2026-05-28): literal-index access is structurally `true`.
  | RArrStoreLit _ _ _ => intro _; rfl
  | RArrLoadLit _ _ _ => intro _; rfl
  -- Phase E2 (2026-05-29): dst-threaded leaf call, monotone like `RCall`.
  | RCallDstThreaded f _ _ =>
      intro h
      simp only [isCT_LowCT] at h ⊢
      exact hab f h

/-! ## §3.5  Relaxed predicate (C3.1): admit non-secret guards

The over-strict `isCT_LowCT` rejects every `RIfNz` / `RWhileNz`. In
practice, much real code branches on quantities that are themselves
public — loop counters, length parameters, table indices. The relaxed
predicate `isCT_LowCT'` takes an additional `secrets : SecretSet`
parameter (a `String → Bool` indicating which scalar names hold secret
values) and admits an `RIfNz` / `RWhileNz` whose guard is **not** in
that set, recursively checking the body / branches.

### Soundness sketch

Under leakage non-interference (NI), a program is constant-time when
its leakage trace is a function of the *public* inputs only, with no
dependence on the secrets. Branching on a value that is itself
publicly observable (i.e. derived from public inputs and not in
`secrets`) leaks only public information — by the definition of NI,
this does not violate the secret-input non-interference condition.

The CryptoSSA-side analogue is `SSALeakage.all_cprog_ct`: there,
because the CryptoSSA AST simply has no data-dependent branching
constructor at all, every program is CT by construction. On the
`LowCT` side we *do* have `RIfNz` / `RWhileNz` constructors, so the
syntactic predicate must rule out branches whose guard could depend on
the secret context entry — which is exactly what `secrets x = false`
encodes at the name level. Propagating that name-level information
through to a semantic NI proof is C3.2 (the syntactic-to-semantic
bridge); see §5.

This relaxation is purely additive: `isCT_LowCT leaves c` is exactly
`isCT_LowCT' leaves emptySecrets c`, as proved in
`isCT_LowCT_eq_relaxed_emptySecrets` below. -/

/-- A "secrets" set: scalar names whose value is treated as secret. -/
abbrev SecretSet := String → Bool

/-- The empty secret set: no scalar name is treated as secret. With
this set, `isCT_LowCT'` admits every public-guarded conditional, and
collapses to a leaf-whitelist + branch-recursion check. -/
def emptySecrets : SecretSet := fun _ => false

/-- Relaxed syntactic constant-time predicate (C3.1).

Identical to `isCT_LowCT` on the original constructors, but admits
`.RIfNz x t f` and `.RWhileNz x body` when `secrets x = false`,
recursively checking the inner programs.

The `Bool` shape preserves decidability, so `decide`-style smoke tests
still close. -/
def isCT_LowCT' (leaves : CTLeaves) (secrets : SecretSet) : LowCT → Bool
  | .RSkip                           => true
  | .RSeq c1 c2                      => isCT_LowCT' leaves secrets c1
                                          && isCT_LowCT' leaves secrets c2
  | .RLetZero _ _ body               => isCT_LowCT' leaves secrets body
  | .RLetU64Zero _ body              => isCT_LowCT' leaves secrets body
  | .RScalarSet _ _                  => true
  | .RCall f _ _                     => leaves f
  | .RCloneCall _ _ _ innerF _ _     => leaves innerF
  | .RIfNz x t f                     => !(secrets x)
                                          && isCT_LowCT' leaves secrets t
                                          && isCT_LowCT' leaves secrets f
  | .RWhileNz x body                 => !(secrets x)
                                          && isCT_LowCT' leaves secrets body
  | .RFor _ _ body                   => isCT_LowCT' leaves secrets body
  | .RForRuntime _ _ body            => isCT_LowCT' leaves secrets body
  | .RLimbStore _ _ _                => true
  | .RLimbStoreExpr _ _ _            => true
  -- Phase F/G/H/L/M (2026-05-03): mirror the strict predicate.
  | .RCallSwap f _ _ _               => leaves f
  -- Tightened (#235): gate the inline-asm opcode on the vendor DOIT∩DIT
  -- whitelist `ct_intrinsic`, rejecting `DIV`/`IDIV`/`BSF`/`BSR`/FP/
  -- variable-latency opcodes.  Was `true` (accepted *any* opcode name,
  -- including non-CT ones) — a CT soundness gap closed here; mirrors the
  -- back-end `isCT_InstrR` `Copn` clause.  See
  -- CT_INSTRUCTION_REFERENCES.md §"Arithmetic/logic Copn".
  | .RAsmOp name _ _                 => CatCrypt.Crypto.Jasmin.ct_intrinsic name
  | .RCallN f _ _                    => leaves f
  | .RSelect _ _ _ _                 => true
  | .RAssert _                       => true
  | .RBlock body                     => isCT_LowCT' leaves secrets body
  | .RFnDef _ _ _ body cont          =>
      isCT_LowCT' leaves secrets body && isCT_LowCT' leaves secrets cont
  | .RFnCall f _ _                   => leaves f
  -- Phase I (2026-05-03): tuple component store/load is structural.
  | .RTupleStore _ _ _               => true
  | .RTupleLoad _ _ _                => true
  -- Phase Ext / Ext2 (2026-05-12, 2026-05-13): mirror the strict predicate.
  | .RArrStore _ _ _                 => true
  | .RArrLoad _ _ _                  => true
  | .RScalarSetExpr _ _              => true
  | .RBytesSlice _ _ _ _             => true
  -- Phase DD (2026-05-28) / E2 (2026-05-29): mirror the strict predicate.
  | .RArrStoreLit _ _ _              => true
  | .RArrLoadLit _ _ _               => true
  | .RCallDstThreaded f _ _          => leaves f

/-- The relaxed predicate with the empty secret set agrees with the
over-strict one on the no-control-flow constructors and with `false`
on `RIfNz` / `RWhileNz` — but the right-hand side under `emptySecrets`
*also* admits non-secret-guarded branches whose bodies are CT. The two
predicates therefore disagree exactly on programs whose only obstacle
to CT is a (now-admissible) branch.

The strict-implies-relaxed direction is the genuinely useful
compatibility statement: anything the over-strict predicate accepts,
the relaxed predicate also accepts under `emptySecrets`. -/
theorem isCT_LowCT_imp_relaxed_emptySecrets
    (leaves : CTLeaves) (c : LowCT)
    (h : isCT_LowCT leaves c = true) :
    isCT_LowCT' leaves emptySecrets c = true := by
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
      rw [isCT_RSeq] at h
      have ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      simp only [isCT_LowCT', ih1 h1, ih2 h2, Bool.and_self]
  | RLetZero _ _ body ih =>
      rw [isCT_RLetZero] at h
      simp only [isCT_LowCT', ih h]
  | RLetU64Zero _ body ih =>
      rw [isCT_RLetU64Zero] at h
      simp only [isCT_LowCT', ih h]
  | RScalarSet _ _ => rfl
  | RCall f _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]
  | RCloneCall _ _ _ innerF _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]
  | RIfNz _ _ _ _ _ =>
      simp only [isCT_LowCT] at h; cases h
  | RWhileNz _ _ _ =>
      simp only [isCT_LowCT] at h; cases h
  | RFor _ _ body ih =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', ih h]
  | RForRuntime _ _ body ih =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', ih h]
  | RLimbStore _ _ _ => rfl
  | RLimbStoreExpr _ _ _ => rfl
  -- Phase F/G/H/L/M (2026-05-03): mirror the patterns.
  | RCallSwap f _ _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]
  -- Both predicates gate `RAsmOp name` on the same `ct_intrinsic name`.
  | RAsmOp _ _ _ => simpa only [isCT_LowCT, isCT_LowCT'] using h
  | RCallN f _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]
  | RSelect _ _ _ _ => rfl
  | RAssert _ => rfl
  | RBlock body ih =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', ih h]
  -- Phase C: helper definition forwards CT to body+cont; helper call
  -- forwards CT through the leaf-name whitelist.
  | RFnDef _ _ _ _ _ ih_body ih_cont =>
      simp only [isCT_LowCT, Bool.and_eq_true] at h
      simp only [isCT_LowCT', ih_body h.1, ih_cont h.2, Bool.and_self]
  | RFnCall f _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]
  | RTupleStore _ _ _ => rfl
  | RTupleLoad _ _ _ => rfl
  -- Phase Ext / Ext2 (2026-05-12, 2026-05-13): both sides constantly
  -- return `true`, so reflexivity suffices.
  | RArrStore _ _ _ => rfl
  | RArrLoad _ _ _ => rfl
  | RScalarSetExpr _ _ => rfl
  | RBytesSlice _ _ _ _ => rfl
  -- Phase DD (2026-05-28): both sides constantly `true`.
  | RArrStoreLit _ _ _ => rfl
  | RArrLoadLit _ _ _ => rfl
  -- Phase E2 (2026-05-29): dst-threaded leaf call, forwarded like `RCall`.
  | RCallDstThreaded f _ _ =>
      simp only [isCT_LowCT] at h
      simp only [isCT_LowCT', h]

/-! ## §4  Smoke tests

Hand-written CT and non-CT programs, closed by `decide`. -/

/-- A trivial CT-leaf whitelist: accept the names "leafA" and "leafB"
only. Used in smoke tests below. -/
def smokeLeaves : CTLeaves := fun
  | "leafA" => true
  | "leafB" => true
  | _       => false

/-- A hand-written CT program: a sequence of `RScalarSet` and
`RLimbStore`. -/
def smokeCT : LowCT :=
  .RSeq (.RScalarSet "i" 0)
        (.RLimbStore { locVar := "x"
                     , locSrc := .TFp } 0 0)

/-- Smoke test: the hand-written CT program closes the predicate. -/
theorem smokeCT_isCT : isCT_LowCT smokeLeaves smokeCT = true := by decide

/-- A hand-written CT program using an `RCall` to a whitelisted leaf. -/
def smokeCallCT : LowCT :=
  .RCall "leafA"
    { locVar := "out", locSrc := .TFp }
    [{ locVar := "in", locSrc := .TFp }]

/-- Smoke test: a single whitelisted call closes the predicate. -/
theorem smokeCallCT_isCT : isCT_LowCT smokeLeaves smokeCallCT = true := by
  decide

/-- A hand-written non-CT program: an `RCall` to an un-whitelisted leaf
("notVetted"). -/
def smokeBadCall : LowCT :=
  .RCall "notVetted"
    { locVar := "out", locSrc := .TFp }
    []

/-- Smoke test: a non-whitelisted call is rejected. -/
theorem smokeBadCall_notCT :
    isCT_LowCT smokeLeaves smokeBadCall = false := by decide

/-- A hand-written program containing `RIfNz`: rejected unconditionally
by the over-strict rule. -/
def smokeIf : LowCT :=
  .RIfNz "guard" .RSkip .RSkip

/-- Smoke test: any `RIfNz` is rejected. -/
theorem smokeIf_notCT : isCT_LowCT smokeLeaves smokeIf = false := by decide

/-- A hand-written program containing `RWhileNz`: rejected
unconditionally by the over-strict rule. -/
def smokeWhile : LowCT :=
  .RWhileNz "ctr" .RSkip

/-- Smoke test: any `RWhileNz` is rejected. -/
theorem smokeWhile_notCT :
    isCT_LowCT smokeLeaves smokeWhile = false := by decide

/-! ### Smoke tests for the relaxed predicate (C3.1) -/

/-- A non-secret-guarded `RIfNz`. With an empty secret set the
relaxed predicate admits this program. -/
def smokeIfPublic : LowCT :=
  .RIfNz "publicGuard" (.RScalarSet "x" 7) (.RScalarSet "x" 11)

/-- Smoke test (C3.1): a public-guarded `RIfNz` closes the relaxed
predicate under `emptySecrets`. -/
theorem smokeIfPublic_isCT' :
    isCT_LowCT' smokeLeaves emptySecrets smokeIfPublic = true := by decide

/-- Smoke test (C3.1): the same program is still rejected when the
guard is in the secrets set. -/
theorem smokeIfPublic_secret_notCT' :
    isCT_LowCT' smokeLeaves (fun n => decide (n = "publicGuard")) smokeIfPublic
      = false := by decide

/-- Smoke test (C3.1): the over-strict predicate still rejects every
`RIfNz`, including this public-guarded one — the strict rule has no
way to inspect the guard. -/
theorem smokeIfPublic_strict_notCT :
    isCT_LowCT smokeLeaves smokeIfPublic = false := by decide

/-- A public-guarded `RWhileNz` whose body is CT. With an empty
secret set the relaxed predicate admits this program. -/
def smokeWhilePublic : LowCT :=
  .RWhileNz "ctr" (.RScalarSet "tmp" 0)

/-- Smoke test (C3.1): a public-guarded `RWhileNz` closes the relaxed
predicate under `emptySecrets`. -/
theorem smokeWhilePublic_isCT' :
    isCT_LowCT' smokeLeaves emptySecrets smokeWhilePublic = true := by decide

/-- Smoke test (C3.1): the same loop is rejected when its guard name
is in the secret set. -/
theorem smokeWhilePublic_secret_notCT' :
    isCT_LowCT' smokeLeaves (fun n => decide (n = "ctr")) smokeWhilePublic
      = false := by decide

/-- Smoke test (C3.1): a `RIfNz` whose body contains a non-CT call
remains rejected even when its guard is public — the inner-CT
check still fires. -/
def smokeIfPublicBadBody : LowCT :=
  .RIfNz "publicGuard"
    (.RCall "notVetted" { locVar := "out", locSrc := .TFp } [])
    .RSkip

theorem smokeIfPublicBadBody_notCT' :
    isCT_LowCT' smokeLeaves emptySecrets smokeIfPublicBadBody = false := by
  decide

/-! ## §5  Documented follow-ups

* **C3.1 — relax `RIfNz` / `RWhileNz`. [DONE].** Landed in §3.5 above
  as the additive predicate `isCT_LowCT' (leaves : CTLeaves)
  (secrets : SecretSet)`, which admits `.RIfNz x t f` and
  `.RWhileNz x body` when `secrets x = false`, recursively checking
  the inner programs. The `Bool` shape stays decidable. Backwards
  compatibility with the over-strict starting point is given by
  `isCT_LowCT_imp_relaxed_emptySecrets`. Smoke tests
  `smokeIfPublic_isCT'`, `smokeIfPublic_secret_notCT'`,
  `smokeWhilePublic_isCT'`, `smokeWhilePublic_secret_notCT'`, and
  `smokeIfPublicBadBody_notCT'` exercise both directions. A future
  micro-refinement could extend the §3 monotonicity statement jointly
  to leaf-whitelist *enlargement* and secret-set *shrinkage*; not
  needed by the C3.2 bridge as currently shaped.

* **C3.2 — syntactic-to-semantic bridge.** Prove that
  `isCT_LowCT leaves c = true` implies the CryptoSSA denotation of
  `LowCTToCryptoSSA.translate c = some prog` satisfies `ct_spComp`
  (matching pipeline (2)'s `translateMonoFun_denote_is_ct`).
  Compositionally, the `RIfNz` / `RWhileNz` rejection in §1 means the
  translate function — which already returns `none` on most uses of
  those constructors — never has to reason about secret-dependent
  branching at all under this predicate.

* **C3.3 — joint preservation in `JasminCompilerBridge`.** Compose
  with `JasminCompilerBridge.compiler_preserves_ct` to extend the
  pipeline (1) preservation guarantee through the back-end. -/

end CatCrypt.Crypto.SecureCompilation.LowCTCT
