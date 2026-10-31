/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideDecl
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToMulti
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak

/-!
# The events of the wide template blocks

A body `wideBlockOf W m` of a wide tagged field call loads the limbs of its argument arrays
at constant indices, runs the Montgomery limb blocks on the loaded registers, and stores
the result limbs at constant indices. At leakage parameters of `jasminDialect` with no
variable-time operation its events are therefore the same at every argument vector.

The proof is structural. `jMemFree` marks the operations other than the stack accesses, the
fresh zero arrays and the leaf calls; at such parameters they emit no event. A predicate on multi-result programs
is closed under a memory-free prefix (`PrefixClosed`) when a binding of a memory-free
operation in front of a program of the predicate keeps it. Every limb generator of the
Montgomery blocks (`Curve25519.adcR` to `Mont.mulMK` and `Mont.ciosMK`) passes a
prefix-closed predicate from its continuation to its result; the blocks themselves bind
memory-free operations only (`MemFree`). The predicate `EvFix` (the events are the same at
every two valuations) is prefix-closed, and the constant-index loads and stores keep it.

## Main definitions

* `jMemFree` — the operations of `jasminDialect` other than stack accesses, fresh zero
  arrays and leaf calls.
* `MemFree` — a multi-result program binds memory-free operations only.
* `PrefixClosed` — a predicate closed under a memory-free binding in front.
* `EvFix` — the events of a multi-result program are the same at every two valuations.

## Main results

* `lowerOpL_memFree` — the Montgomery limb block of an operation of `ArithAt` binds
  memory-free operations only.
* `fieldBodyOf_evFix` — the lowered field program over word arrays has fixed events when
  its blocks are memory-free.
* `wideTemplateOf_evFix` — the blocks of a registered wide template have fixed events.
* `canonRegBlock_evFix` — the register block of the canonical Montgomery template has fixed
  events.
* `wideBlockOf_leakRunMC`, `montWordBlockOf_leakRunMC`, `wideBody_leakRunMC` — the body of
  a tagged call at a wide template or a one-limb record runs at a fixed list of events.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC eBin eConst eBit eMulhi eAdc eCarry eSel bindK adcR rowR selR xorR constsK addK
    mulRowK accK)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open Ctxt (Var Valuation)

/-! ## 1. Memory-free operations and prefix-closed predicates -/

/-- The operations of `jasminDialect` other than the stack accesses (at a register or a
    constant index), the fresh zero arrays and the leaf calls. -/
def jMemFree : JasminOp → Bool
  | .stackLoad _ _ | .stackStore _ _ | .stackStoreImm _ _ _ | .stackZero _ _
  | .extCall _ _ _ => false
  | _ => true

/-- **A predicate on multi-result programs closed under a memory-free prefix**: a binding
    of a memory-free operation in front of a program of the predicate gives a program of
    the predicate. -/
def PrefixClosed (Q : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}, MC Γ ts → Prop) :
    Prop :=
  ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : MC (t :: Γ) ts), jMemFree e.op = true → Q k →
      Q (.var e k)

/-- A multi-result program binds memory-free operations only. -/
def MemFree : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → MC Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var e k => jMemFree e.op = true ∧ MemFree k

theorem memFree_prefixClosed : PrefixClosed @MemFree := fun _ _ he hk => ⟨he, hk⟩

section Gen

variable {Q : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}, MC Γ ts → Prop}
  (hQ : PrefixClosed @Q)
include hQ

/-- A binding of a memory-free expression keeps a prefix-closed predicate of every
    continuation. -/
theorem bindK_q {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (x : Var Δ t), Q (k r x)) :
    Q (bindK e k) :=
  hQ e _ he (hk _ _)

theorem adcR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs ys : List (Var Γ w64)) (c : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out c', Q (k r out c')) →
      Q (adcR ren xs ys c k)
  | _, _, _, _, _ :: xs, _ :: ys, _, _, hk => by
      rw [adcR]
      exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        adcR_q _ xs ys _ fun _ _ _ => hk _ _ _
  | _, _, _, _, [], _, _, _, hk => by rw [adcR]; exact hk _ _ _
  | _, _, _, _, _ :: _, [], _, _, hk => by rw [adcR]; exact hk _ _ _

theorem rowR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs : List (Var Γ w64)) (w z h : Var Δ w64) (c : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (rowR ren xs w z h c k)
  | _, _, _, _, [], _, _, _, _, _, hk => by
      rw [rowR]
      exact bindK_q hQ _ rfl fun _ _ => hk _ _
  | _, _, _, _, _ :: xs, _, _, _, _, _, hk => by
      rw [rowR]
      exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        rowR_q _ xs _ _ _ _ fun _ _ => hk _ _

theorem selR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (c : Var Δ w1) (xs ys : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (selR ren c xs ys k)
  | _, _, _, _, _, _ :: xs, _ :: ys, _, hk => by
      rw [selR]
      exact bindK_q hQ _ rfl fun _ _ => selR_q _ _ xs ys fun _ _ => hk _ _
  | _, _, _, _, _, [], _, _, hk => by rw [selR]; exact hk _ _
  | _, _, _, _, _, _ :: _, [], _, hk => by rw [selR]; exact hk _ _

theorem xorR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (m : Var Δ w64) (xs : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (xorR ren m xs k)
  | _, _, _, _, _, _ :: xs, _, hk => by
      rw [xorR]
      exact bindK_q hQ _ rfl fun _ _ => xorR_q _ _ xs fun _ _ => hk _ _
  | _, _, _, _, _, [], _, hk => by rw [xorR]; exact hk _ _

theorem constsK_q : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ns : List Nat)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts},
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) → Q (constsK ns k)
  | _, _, [], _, hk => by rw [constsK]; exact hk _ _
  | _, _, _ :: ns, _, hk => by
      rw [constsK]
      exact bindK_q hQ _ rfl fun _ _ => constsK_q ns fun _ _ => hk _ _

theorem addK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → Var Δ w1 → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out c, Q (k r out c)) :
    Q (addK xs ys k) := by
  rw [addK]
  exact bindK_q hQ _ rfl fun _ _ => adcR_q hQ _ _ _ _ fun _ _ _ => hk _ _ _

theorem mulRowK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (w : Var Γ w64) {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (mulRowK xs w k) := by
  rw [mulRowK]
  exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    rowR_q hQ _ _ _ _ _ _ fun _ _ => hk _ _

theorem accK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (i : Nat) (xs : List (Var Γ w64))
    (y : Var Γ w64) (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (accK i xs y acc k) := by
  rw [accK]
  exact mulRowK_q hQ _ _ fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    addK_q hQ _ _ fun _ _ _ => hk _ _

variable {n : Nat} (P : LimbParams n)

theorem csubPCK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.csubPCK P xs k) := by
  rw [Mont.csubPCK]
  exact constsK_q hQ _ fun _ _ => addK_q hQ _ _ fun _ _ _ =>
    selR_q hQ _ _ _ _ fun _ _ => hk _ _

theorem addMK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.addMK P xs ys k) := by
  rw [Mont.addMK]
  exact bindK_q hQ _ rfl fun _ _ => addK_q hQ _ _ fun _ _ _ =>
    csubPCK_q hQ P _ fun _ _ => hk _ _

theorem subMK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.subMK P xs ys k) := by
  rw [Mont.subMK]
  exact bindK_q hQ _ rfl fun _ _ => xorR_q hQ _ _ _ fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    adcR_q hQ _ _ _ _ fun _ _ _ => constsK_q hQ _ fun _ _ => addK_q hQ _ _ fun _ _ _ =>
    selR_q hQ _ _ _ _ fun _ _ => hk _ _

theorem prodAccK_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (i : Nat) (xs : List (Var Δ w64)) (ys : List (Var Γ w64)) (acc : List (Var Δ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (Mont.prodAccK ren i xs ys acc k)
  | _, _, _, _, _, _, [], _, _, hk => by rw [Mont.prodAccK]; exact hk _ _
  | _, _, _, _, _, _, _ :: ys, _, _, hk => by
      rw [Mont.prodAccK]
      exact accK_q hQ _ _ _ _ fun _ _ => prodAccK_q _ _ _ ys _ fun _ _ => hk _ _

theorem prodNK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.prodNK xs ys k) := by
  cases ys with
  | nil => rw [Mont.prodNK]; exact hk _ _
  | cons y ys =>
      rw [Mont.prodNK]
      exact mulRowK_q hQ _ _ fun _ _ => prodAccK_q hQ _ _ _ _ _ fun _ _ => hk _ _

theorem redcStepK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.redcStepK P acc k) := by
  rw [Mont.redcStepK]
  exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    constsK_q hQ _ fun _ _ => mulRowK_q hQ _ _ fun _ _ => addK_q hQ _ _ fun _ _ _ => hk _ _

theorem redcChainK_q : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (s : Nat)
    (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts},
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) →
      Q (Mont.redcChainK P s acc k)
  | _, _, 0, _, _, hk => by rw [Mont.redcChainK]; exact hk _ _
  | _, _, s + 1, _, _, hk => by
      rw [Mont.redcChainK]
      exact redcStepK_q hQ P _ fun _ _ => redcChainK_q s _ fun _ _ => hk _ _

theorem mulMK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.mulMK P xs ys k) := by
  rw [Mont.mulMK]
  exact prodNK_q hQ _ _ fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    redcChainK_q hQ P _ _ fun _ _ => csubPCK_q hQ P _ fun _ _ => hk _ _

theorem opK_q {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (y : Var Γ w64 ⊕ Nat)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' w64 → MC Δ' ts}
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') v, Q (k r v)) :
    Q (Mont.opK ren y k) := by
  cases y with
  | inl v => exact hk _ _
  | inr d => exact bindK_q hQ _ rfl fun _ _ => hk _ _

theorem fmaR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (ys : List (Var Γ w64 ⊕ Nat)) (acc : List (Var Γ w64)) (x z h : Var Δ w64)
    (cA cB : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 →
      Var Δ' w1 → Var Δ' w64 → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out cA' cB' h', Q (k r out cA' cB' h')) →
      Q (Mont.fmaR ren ys acc x z h cA cB k)
  | _, _, _, _, _ :: ys, _ :: acc, _, _, _, _, _, _, hk => by
      rw [Mont.fmaR]
      exact opK_q hQ _ _ fun _ _ => bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        bindK_q hQ _ rfl fun _ _ => fmaR_q _ ys acc _ _ _ _ _ fun _ _ _ _ _ => hk _ _ _ _ _
  | _, _, _, _, [], _ :: acc, _, _, _, _, _, _, hk => by
      rw [Mont.fmaR]
      exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        fmaR_q _ [] acc _ _ _ _ _ fun _ _ _ _ _ => hk _ _ _ _ _
  | _, _, _, _, [], [], _, _, _, _, _, _, hk => by rw [Mont.fmaR]; exact hk _ _ _ _ _
  | _, _, _, _, _ :: _, [], _, _, _, _, _, _, hk => by rw [Mont.fmaR]; exact hk _ _ _ _ _

theorem ciosAddK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x z : Var Γ w64) (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.ciosAddK ys x z acc k) := by
  rw [Mont.ciosAddK]
  exact bindK_q hQ _ rfl fun _ _ => fmaR_q hQ _ _ _ _ _ _ _ _ fun _ _ _ _ _ => hk _ _

theorem ciosRedK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (S : List (Var Γ w64))
    (ni z : Var Γ w64)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.ciosRedK P S ni z k) := by
  rw [Mont.ciosRedK]
  exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    fmaR_q hQ _ _ _ _ _ _ _ _ fun _ _ _ _ _ => hk _ _

theorem ciosRowsK_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (ys : List (Var Δ w64)) (ni z : Var Δ w64) (xs : List (Var Γ w64))
    (acc : List (Var Δ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (Mont.ciosRowsK P ren ys ni z xs acc k)
  | _, _, _, _, _, _, _, [], _, _, hk => by rw [Mont.ciosRowsK]; exact hk _ _
  | _, _, _, _, _, _, _, _ :: xs, _, _, hk => by
      rw [Mont.ciosRowsK]
      exact ciosAddK_q hQ _ _ _ _ fun _ _ => ciosRedK_q hQ P _ _ _ fun _ _ =>
        ciosRowsK_q _ _ _ _ xs _ fun _ _ => hk _ _

theorem ciosMK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (k r out)) :
    Q (Mont.ciosMK P xs ys k) := by
  cases xs with
  | nil => rw [Mont.ciosMK]; exact hk _ _
  | cons x xs =>
      rw [Mont.ciosMK]
      exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        mulRowK_q hQ _ _ fun _ _ => ciosRedK_q hQ P _ _ _ fun _ _ =>
        ciosRowsK_q hQ P _ _ _ _ _ _ fun _ _ => csubPCK_q hQ P _ fun _ _ => hk _ _

theorem shrR_q : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (sa sb : Var Δ w64) (xs : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out, Q (k r out)) →
      Q (Solinas.shrR ren sa sb xs k)
  | _, _, _, _, _, _, [], _, hk => by rw [Solinas.shrR]; exact hk _ _
  | _, _, _, _, _, _, [_], _, hk => by
      rw [Solinas.shrR]
      exact bindK_q hQ _ rfl fun _ _ => hk _ _
  | _, _, _, _, _, _, _ :: y :: ys, _, hk => by
      rw [Solinas.shrR]
      exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
        bindK_q hQ _ rfl fun _ _ => shrR_q _ _ _ (y :: ys) fun _ _ => hk _ _

theorem splitK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k : Nat)
    (xs : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → List (Var Δ w64) →
      MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) hi lo, Q (K r hi lo)) :
    Q (Solinas.splitK k xs K) := by
  rw [Solinas.splitK]
  split
  · exact hK _ _ _
  · exact bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
      bindK_q hQ _ rfl fun _ _ => bindK_q hQ _ rfl fun _ _ =>
      shrR_q hQ _ _ _ _ fun _ _ => hK _ _ _

theorem foldK_q {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k c m : Nat)
    (xs : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (K r out)) :
    Q (Solinas.foldK k c m xs K) := by
  rw [Solinas.foldK]
  exact splitK_q hQ _ _ fun _ _ _ => bindK_q hQ _ rfl fun _ _ =>
    mulRowK_q hQ _ _ fun _ _ => bindK_q hQ _ rfl fun _ _ =>
    addK_q hQ _ _ fun _ _ _ => hK _ _

theorem mulSK_q {n : Nat} (S : Solinas.SolinasParams n) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out, Q (K r out)) :
    Q (Solinas.mulSK S xs ys K) := by
  rw [Solinas.mulSK]
  exact prodNK_q hQ _ _ fun _ _ => foldK_q hQ _ _ _ _ fun _ _ =>
    foldK_q hQ _ _ _ _ fun _ _ => csubPCK_q hQ (Solinas.lp S) _ fun _ _ => hK _ _

end Gen

/-! ## 2. The Montgomery limb blocks bind memory-free operations -/

section Blocks

variable {n : Nat} (P : LimbParams n) {Γ : Ctxt jasminDialect}

theorem retN_memFree (k : Nat) (xs : List (Var Γ w64)) : MemFree (Mont.retN k xs) := by
  cases xs with
  | nil => exact ⟨rfl, trivial⟩
  | cons a as => trivial

theorem constBlk_memFree (k v : Nat) : MemFree (Mont.constBlk (Γ := Γ) k v) := by
  rw [Mont.constBlk]
  exact constsK_q memFree_prefixClosed _ fun _ _ => retN_memFree _ _

theorem addBlk_memFree (xs ys : List (Var Γ w64)) : MemFree (Mont.addBlk P xs ys) := by
  rw [Mont.addBlk]
  exact addMK_q memFree_prefixClosed P _ _ fun _ _ => retN_memFree _ _

theorem subBlk_memFree (xs ys : List (Var Γ w64)) : MemFree (Mont.subBlk P xs ys) := by
  rw [Mont.subBlk]
  exact subMK_q memFree_prefixClosed P _ _ fun _ _ => retN_memFree _ _

theorem negBlk_memFree (xs : List (Var Γ w64)) : MemFree (Mont.negBlk P xs) := by
  rw [Mont.negBlk]
  exact constsK_q memFree_prefixClosed _ fun _ _ => subBlk_memFree P _ _

theorem mulBlkRoute_memFree (xs ys : List (Var Γ w64)) :
    MemFree (Mont.mulBlkRoute P xs ys) := by
  rw [Mont.mulBlkRoute]
  split
  · rw [Mont.mulBlkI]
    exact ciosMK_q memFree_prefixClosed P _ _ fun _ _ => retN_memFree _ _
  · rw [Mont.mulBlk]
    exact mulMK_q memFree_prefixClosed P _ _ fun _ _ => retN_memFree _ _

/-- **The Montgomery limb block of an operation of `arithOpB P.p` binds memory-free
    operations only.** -/
theorem lowerOpL_memFree (op : FieldDialect.FieldOp)
    (hop : FieldLower.arithOpB P.p op = true) :
    MemFree (FieldToJasminLimbs.lowerOpL P op) := by
  cases op <;> simp only [FieldLower.arithOpB, beq_iff_eq, Bool.false_eq_true] at hop <;>
    subst hop <;> rw [FieldToJasminLimbs.lowerOpL] <;> simp only [ite_true, dite_eq_left]
  · exact addBlk_memFree P _ _
  · exact subBlk_memFree P _ _
  · exact negBlk_memFree P _
  · exact mulBlkRoute_memFree P _ _
  · exact constBlk_memFree _ _

/-- **The Solinas limb block of an operation of `arithOpB (Solinas.p S)` binds memory-free
    operations only.** -/
theorem solinasLowerOpL_memFree (S : Solinas.SolinasParams n) (op : FieldDialect.FieldOp)
    (hop : FieldLower.arithOpB (Solinas.p S) op = true) :
    MemFree (FieldToJasminLimbsSolinas.lowerOpL S op) := by
  cases op <;> simp only [FieldLower.arithOpB, beq_iff_eq, Bool.false_eq_true] at hop <;>
    subst hop <;> rw [FieldToJasminLimbsSolinas.lowerOpL] <;> simp only [ite_true, dite_eq_left]
  · rw [Solinas.addBlk]
    exact addMK_q memFree_prefixClosed (Solinas.lp S) _ _ fun _ _ => retN_memFree _ _
  · exact subBlk_memFree (Solinas.lp S) _ _
  · exact negBlk_memFree (Solinas.lp S) _
  · rw [Solinas.mulBlk]
    exact mulSK_q memFree_prefixClosed S _ _ fun _ _ => retN_memFree _ _
  · exact constBlk_memFree _ _

end Blocks

/-! ## 3. Renaming, splicing and the lowering -/

section Lower

open MultiBlockLowering (spliceMultiK MultiBlockLoweringData)

/-- A renamed memory-free program is memory-free. -/
theorem rename_memFree {Γ Γ' : Ctxt jasminDialect} {ts : List JasminTy}
    (h : Ctxt.Hom Γ Γ') (m : MC Γ ts) (hm : MemFree m) :
    MemFree (MultiReturnCom.rename h m) := by
  induction m generalizing Γ' with
  | ret => trivial
  | var e body ih =>
      obtain ⟨op, rfl, args⟩ := e
      exact ⟨hm.1, ih h.lift hm.2⟩

variable {Q : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy}, MC Γ ts → Prop}
  (hQ : PrefixClosed @Q)
include hQ

/-- The splice of a memory-free block keeps a prefix-closed predicate of every
    continuation. -/
theorem spliceMultiK_q : ∀ {Γ : Ctxt jasminDialect} {ts bs : List JasminTy} (blk : MC Γ ts)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts → MC Δ bs},
    MemFree blk → (∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) res, Q (k ren res)) →
      Q (spliceMultiK blk k)
  | _, _, _, .ret _, _, _, hk => hk _ _
  | _, _, _, .var e blk, _, hb, hk =>
      hQ e _ hb.1 (spliceMultiK_q blk hb.2 fun _ _ => hk _ _)

/-- **The lowering of a covered program keeps a prefix-closed predicate of every
    continuation**, when the block of every covered expression is memory-free. -/
theorem lowerR_q {d : Dialect} [DialectSignature d]
    (L : MultiBlockLoweringData d jasminDialect)
    {Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop}
    (hB : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e → MemFree (L.exprBlock e)) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt jasminDialect} {bs : List JasminTy}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (c : Com d Γ t)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        HVector (fun u => Var Δ' u) (L.mapTys t) → MC Δ' bs},
      BlockLoweringCPS.CoveredCom Good c →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') vs, Q (k r vs)) → Q (L.lowerR ren c k)
  | _, _, _, _, _, .ret _, _, _, hk => by rw [MultiBlockLoweringData.lowerR]; exact hk _ _
  | _, _, _, _, ren, .var e body, _, hc, hk => by
      rw [MultiBlockLoweringData.lowerR, MultiBlockLoweringData.lowerBind]
      exact spliceMultiK_q hQ _ (rename_memFree _ _ (hB e hc.1)) fun _ _ =>
        lowerR_q L hB _ body hc.2 fun _ _ => hk _ _

end Lower

/-! ## 4. Fixed events -/

section Ev

open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel jKind)

variable {Pj : JLeakParams}

/-- A memory-free operation is quiet at leakage parameters with no variable-time
    operation. -/
theorem kind_quiet_of_memFree (hV : ∀ op, Pj.opVT op = none) (op : JasminOp)
    (h : jMemFree op = true) : (jLeakModel Pj).kind op = .quiet := by
  cases op <;> simp_all [jMemFree, jLeakModel, jKind]

/-- **The events of a multi-result program are the same at every two valuations.** -/
def EvFix (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (c : MC Γ ts) : Prop :=
  ∀ V₁ V₂ : Valuation Γ, MultiReturnCom.ctLeak M c V₁ = MultiReturnCom.ctLeak M c V₂

/-- Fixed events are closed under a memory-free prefix at leakage parameters with no
    variable-time operation. -/
theorem evFix_prefixClosed (hV : ∀ op, Pj.opVT op = none) :
    PrefixClosed (EvFix (jLeakModel Pj)) := by
  intro Γ t ts e k he hk V₁ V₂
  simp only [MultiReturnCom.ctLeak, ComLevelCheck.Expr.ctLeak, ComLevelCheck.opLeak,
    kind_quiet_of_memFree hV _ he, List.nil_append]
  exact hk _ _

variable {n : Nat}

open FieldToJasminLimbs (arrTy loadLimbs loadArgs storeLimbs eLoad eStore)

/-- **The loads of limbs at constant indices keep fixed events of every continuation.** -/
theorem loadLimbs_evFix (hV : ∀ op, Pj.opVT op = none) {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, EvFix (jLeakModel Pj) (k r h)) →
      EvFix (jLeakModel Pj) (loadLimbs m j a k)
  | _, 0, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hk => by
      rw [loadLimbs]
      intro V₁ V₂
      rw [bindK, bindK]
      simp only [MultiReturnCom.ctLeak, ComLevelCheck.Expr.ctLeak, ComLevelCheck.opLeak]
      rw [kind_quiet_of_memFree hV _ rfl,
        show (jLeakModel Pj).kind (eLoad (n := n) a.there Var.here).op = .addrAt 1 from rfl]
      simp only [List.nil_append]
      congr 1
      exact loadLimbs_evFix hV m (j + 1) _ (fun _ _ => hk _ _) _ _

/-- The loads of the limbs of every array keep fixed events of every continuation. -/
theorem loadArgs_evFix (hV : ∀ op, Pj.opVT op = none) {bs : List JasminTy} :
    ∀ (Γ : Ctxt FieldDialect.fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h, EvFix (jLeakModel Pj) (k r h)) →
      EvFix (jLeakModel Pj) (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_evFix hV _ _ _ fun _ _ => loadArgs_evFix hV Γ _ fun _ _ => hk _ _

/-- The stores of limbs at constant indices have fixed events. -/
theorem storeLimbs_evFix (hV : ∀ op, Pj.opVT op = none) :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn m) Δ), EvFix (jLeakModel Pj) (storeLimbs m j o h)
  | _, 0, _, _, _ => by rw [storeLimbs]; intro _ _; rfl
  | _, m + 1, j, o, h => by
      rw [storeLimbs]
      intro V₁ V₂
      rw [bindK, bindK]
      simp only [MultiReturnCom.ctLeak, ComLevelCheck.Expr.ctLeak, ComLevelCheck.opLeak]
      rw [kind_quiet_of_memFree hV _ rfl,
        show (jLeakModel Pj).kind (eStore (n := n) o.there Var.here (h Var.here).there).op =
          .addrAt 1 from rfl]
      simp only [List.nil_append]
      congr 1
      exact storeLimbs_evFix hV m (j + 1) _ _ _ _

/-- **The lowered field program over word arrays has fixed events** at leakage parameters
    with no variable-time operation, for a covered program whose blocks are memory-free: its
    loads and stores are at constant indices and its lowered blocks emit no event. -/
theorem fieldBodyOf_evFix (hV : ∀ op, Pj.opVT op = none)
    (lo : FieldToJasminLimbs.LimbBlocks n)
    {Good : ∀ {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy},
      Expr FieldDialect.fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy}
      (e : Expr FieldDialect.fieldDialect Γ t), Good e →
        MemFree ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy}
    (c : Com FieldDialect.fieldDialect Γ t) (hc : BlockLoweringCPS.CoveredCom Good c) :
    EvFix (jLeakModel Pj) (FieldToJasminLimbs.fieldBodyOf lo c) := by
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_evFix hV Γ _ fun _ _ =>
    lowerR_q (evFix_prefixClosed hV) _ hB _ c hc fun _ _ => storeLimbs_evFix hV _ _ _ _

end Ev

/-- The single-result projection of a multi-result program emits its events. -/
theorem ctLeak_toComHead {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [DialectDenote d] (M : ComLevelCheck.LeakModel d) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty} (m : MultiReturnCom d Γ (t :: ts))
      (V : Valuation Γ), ComLevelCheck.Com.ctLeak M m.toComHead V = MultiReturnCom.ctLeak M m V
  | _, _, _, .ret (.cons _ _), _ => by
      simp only [MultiReturnCom.toComHead, ComLevelCheck.Com.ctLeak, MultiReturnCom.ctLeak]
  | _, _, _, .var e body, V => by
      simp only [MultiReturnCom.toComHead, ComLevelCheck.Com.ctLeak, MultiReturnCom.ctLeak,
        ctLeak_toComHead M body]

/-- The embedding of a straight-line program runs, at every call environment, to its
    denotation and to its events. -/
theorem leakRunMC_ofCom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] [DialectDenote d] (M : ComLevelCheck.LeakModel d)
    (E : CallEnv d) (fuel : Nat) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRunMC M E fuel (NFProg.ofCom c) V =
      some (.cons (c.denote V) .nil, ComLevelCheck.Com.ctLeak M c V) := by
  induction c with
  | ret v => rfl
  | var e k ih =>
      simp only [NFProg.ofCom, Dialects.NFLeak.NFProg.leakRunMC,
        Expr.denoteM_option_eq_some, Option.bind_some, ih, Option.map_some,
        ComLevelCheck.Com.ctLeak]
      rfl

/-! ## 5. The wide templates -/

section Wide

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs (ArithAt montBlocks)
open FieldWideInline

variable {n : Nat} (P : LimbParams n)

/-- The Montgomery limb block of an expression of `ArithAt P.p` binds memory-free operations
    only. -/
theorem exprBlock_memFree {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t)
    (he : ArithAt P.p e) :
    MemFree ((FieldToJasminLimbs.loweringOf (FieldToJasminLimbs.lowerOpL P)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  refine lowerOpL_memFree P op ?_
  rcases he with h | h | h | h | ⟨c, h⟩ <;> (simp only at h; subst h; simp [FieldLower.arithOpB])

/-- The twisted program of an operation of `arithOpB P.p` is covered by `ArithAt P.p`. -/
theorem twistOp_coveredArith (op : fieldDialect.Op) (hg : FieldLower.arithOpB P.p op = true) :
    BlockLoweringCPS.CoveredCom (ArithAt P.p) (twistOp n op) := by
  cases op <;> simp only [FieldLower.arithOpB, beq_iff_eq, Bool.false_eq_true] at hg <;> subst hg
  · exact FieldLower.coveredCom_opCom (fun h => h) _ (by simp [FieldLower.arithOpB])
  · exact FieldLower.coveredCom_opCom (fun h => h) _ (by simp [FieldLower.arithOpB])
  · exact FieldLower.coveredCom_opCom (fun h => h) _ (by simp [FieldLower.arithOpB])
  · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), trivial⟩
  · exact FieldLower.coveredCom_opCom (fun h => h) _ (by simp [FieldLower.arithOpB])

variable {Pj : JLeakParams}

/-- **The blocks of a wide template have fixed events** at the leakage model `M`: the block
    of every operation of `arithOpB p` emits the same events at every two valuations. -/
def WideEvFix (M : ComLevelCheck.LeakModel jasminDialect) {p m : Nat}
    (W : WideTemplate p m) : Prop :=
  ∀ op : fieldDialect.Op, FieldLower.arithOpB p op = true →
    ∀ V₁ V₂ : Valuation (FieldToJasminLimbs.arrCtx m (DialectSignature.sig op) ++
        [FieldToJasminLimbs.arrTy m]),
      ComLevelCheck.Com.ctLeak M (@FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op) V₁ =
        ComLevelCheck.Com.ctLeak M (@FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op) V₂

/-- The canonical Montgomery template of a record has fixed events. -/
theorem ofMont_evFix (hV : ∀ op, Pj.opVT op = none) (hn : n < 2 ^ 64) :
    WideEvFix (jLeakModel Pj) (WideTemplate.ofMont P hn) := by
  intro op hop V₁ V₂
  change ComLevelCheck.Com.ctLeak _
      (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op)) V₁ =
    ComLevelCheck.Com.ctLeak _
      (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op)) V₂
  rw [FieldToJasminLimbs.fieldComOf, ctLeak_toComHead, ctLeak_toComHead]
  exact fieldBodyOf_evFix hV _ (exprBlock_memFree P) _ (twistOp_coveredArith P op hop) V₁ V₂

theorem castN_evFix {M : ComLevelCheck.LeakModel jasminDialect} {p m : Nat} (h : n = m)
    {W : WideTemplate p n} (hW : WideEvFix M W) : WideEvFix M (W.castN h) := by
  subst h
  exact hW

theorem castP_evFix {M : ComLevelCheck.LeakModel jasminDialect} {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideEvFix M W) :
    WideEvFix M (W.castP h) := by
  subst h
  exact hW

/-- The Solinas limb block of an expression of `ArithAt (Solinas.p S)` binds memory-free
    operations only. -/
theorem solinasExprBlock_memFree (S : Solinas.SolinasParams n) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (e : Expr fieldDialect Γ t) (he : ArithAt (Solinas.p S) e) :
    MemFree ((FieldToJasminLimbs.loweringOf
      (FieldToJasminLimbsSolinas.lowerOpL S)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  refine solinasLowerOpL_memFree S op ?_
  rcases he with h | h | h | h | ⟨c, h⟩ <;> (simp only at h; subst h; simp [FieldLower.arithOpB])

/-- **The Solinas template of a record has fixed events** at leakage parameters with no
    variable-time operation. -/
theorem ofSolinasAt_evFix (hV : ∀ op, Pj.opVT op = none) (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideEvFix (jLeakModel Pj) (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_evFix hn ?_
  intro op hop V₁ V₂
  change ComLevelCheck.Com.ctLeak _
      (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S)
        (FieldLower.opCom op)) V₁ =
    ComLevelCheck.Com.ctLeak _
      (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S)
        (FieldLower.opCom op)) V₂
  rw [FieldToJasminLimbs.fieldComOf, ctLeak_toComHead, ctLeak_toComHead]
  exact fieldBodyOf_evFix hV _ (solinasExprBlock_memFree S) _
    (FieldLower.coveredCom_opCom (fun h => h) op hop) V₁ V₂

/-- **The blocks of a registered wide template have fixed events** at leakage parameters with
    no variable-time operation. -/
theorem wideTemplateOf_evFix (hV : ∀ op, Pj.opVT op = none) {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W) :
    WideEvFix (jLeakModel Pj) W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp, rfl⟩ | ⟨_, _, _, rfl⟩
  · exact castP_evFix hp (ofSolinasAt_evFix hV S hn h64)
  · exact ofMont_evFix _ hV _

/-- **The body of a wide tagged call runs at a fixed list of events**: at a registered wide
    template and leakage parameters with no variable-time operation, the leakage run of
    `wideBlockOf W m` at every call environment and fuel succeeds, from every argument
    vector, with the same events. -/
theorem wideBlockOf_leakRunMC (hV : ∀ op, Pj.opVT op = none) {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) :
    ∃ ev, ∀ (E : CallEnv jasminDialect) (fuel : Nat)
      (x : Valuation (d := jasminDialect) (wideSig (_root_.Hax.FieldTag.fieldLimbs p) m)),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel (wideBlockOf W m) x).map
        Prod.snd = some ev := by
  have key : ∀ (E : CallEnv jasminDialect) (fuel : Nat) (x : Valuation (d := jasminDialect)
      (wideSig (_root_.Hax.FieldTag.fieldLimbs p) m)),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel (wideBlockOf W m) x).map
        Prod.snd = some (ComLevelCheck.Com.ctLeak (jLeakModel Pj)
          (templateCall W.P (fieldOpOf m p) (wideArgs p m) (wideFirst m)) x) := by
    intro E fuel x
    rw [wideBlockOf, leakRunMC_ofCom, Option.map_some]
  by_cases hx : Nonempty (Valuation (d := jasminDialect)
    (wideSig (_root_.Hax.FieldTag.fieldLimbs p) m))
  · obtain ⟨x₀⟩ := hx
    refine ⟨ComLevelCheck.Com.ctLeak (jLeakModel Pj)
      (templateCall W.P (fieldOpOf m p) (wideArgs p m) (wideFirst m)) x₀, fun E fuel x => ?_⟩
    rw [key, templateCall, NFProg.Com.ctLeak_rename_pullV, NFProg.Com.ctLeak_rename_pullV,
      wideTemplateOf_evFix hV h _ (arithOpB_fieldOpOf m p)]
  · exact ⟨[], fun _ _ x => absurd ⟨x⟩ hx⟩

/-- **The register block of the canonical Montgomery template has fixed events** at leakage
    parameters with no variable-time operation, for an operation of `arithOpB P.p`. -/
theorem canonRegBlock_evFix (hV : ∀ op, Pj.opVT op = none) (op : fieldDialect.Op)
    (hg : FieldLower.arithOpB P.p op = true) :
    EvFix (jLeakModel Pj) (canonRegBlock P op) := by
  unfold canonRegBlock MultiBlockLowering.MultiBlockLoweringData.lowerMulti
  exact lowerR_q (evFix_prefixClosed hV) _ (exprBlock_memFree P) _ _
    (twistOp_coveredArith P op hg) fun _ _ _ _ => rfl

/-- **The body of a call over one limb runs at a fixed list of events**: for a one-limb
    record and leakage parameters with no variable-time operation, the leakage run of
    `montWordBlockOf P m` at every call environment and fuel succeeds, from every argument
    vector, with the same events. -/
theorem montWordBlockOf_leakRunMC (hV : ∀ op, Pj.opVT op = none) (P : LimbParams 1)
    (m : _root_.Hax.FieldTag.FieldMethod) :
    ∃ ev, ∀ (E : CallEnv jasminDialect) (fuel : Nat)
      (x : Valuation (d := jasminDialect) (wordSig m)),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel (montWordBlockOf P m) x).map
        Prod.snd = some ev := by
  have hfix := canonRegBlock_evFix P hV _ (arithOpB_fieldOpOf m P.p)
  let c := Com.rename (MultiBlockLowering.hvToHom (wordArgs P.p m))
    (canonRegBlock P (fieldOpOf m P.p)).toComHead
  have key : ∀ (E : CallEnv jasminDialect) (fuel : Nat)
      (x : Valuation (d := jasminDialect) (wordSig m)),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel (montWordBlockOf P m) x).map
        Prod.snd = some (ComLevelCheck.Com.ctLeak (jLeakModel Pj) c x) := by
    intro E fuel x
    rw [montWordBlockOf, leakRunMC_ofCom, Option.map_some]
  by_cases hx : Nonempty (Valuation (d := jasminDialect) (wordSig m))
  · obtain ⟨x₀⟩ := hx
    refine ⟨ComLevelCheck.Com.ctLeak (jLeakModel Pj) c x₀, fun E fuel x => ?_⟩
    rw [key, NFProg.Com.ctLeak_rename_pullV, NFProg.Com.ctLeak_rename_pullV,
      ctLeak_toComHead, ctLeak_toComHead, hfix]
  · exact ⟨[], fun _ _ x => absurd ⟨x⟩ hx⟩

open FieldWideDecl (wideBody) in
/-- **A body of a wide tagged head runs at a fixed list of events**: at leakage parameters of
    `jasminDialect` with no variable-time operation, there is one list of events at which
    every body of `wideBody f as rs` runs, at every call environment, fuel and argument
    vector (`wideBlockOf_leakRunMC`, `montWordBlockOf_leakRunMC`). -/
theorem wideBody_leakRunMC (hV : ∀ op, Pj.opVT op = none) (f : String)
    (as rs : List JasminTy) :
    ∃ ev, ∀ b, wideBody f as rs = some b → ∀ (E : CallEnv jasminDialect) (fuel : Nat)
      (x : Valuation (d := jasminDialect) as),
      (Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) E fuel b x).map Prod.snd =
        some ev := by
  unfold wideBody
  split
  · rename_i m p _
    split
    · rename_i W hW
      split
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        obtain ⟨ev, hev⟩ := wideBlockOf_leakRunMC hV hW m
        exact ⟨ev, fun b hb => by cases hb; exact hev⟩
      · exact ⟨[], fun _ hb => by cases hb⟩
    · split
      · rename_i P _
        split
        · rename_i hs
          obtain ⟨rfl, rfl⟩ := hs
          obtain ⟨ev, hev⟩ := montWordBlockOf_leakRunMC hV P m
          exact ⟨ev, fun b hb => by cases hb; exact hev⟩
        · exact ⟨[], fun _ hb => by cases hb⟩
      · exact ⟨[], fun _ hb => by cases hb⟩
  · exact ⟨[], fun _ hb => by cases hb⟩

end Wide

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak
