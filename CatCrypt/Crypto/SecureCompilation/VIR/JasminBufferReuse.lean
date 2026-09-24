/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminStoreMemoryModel

/-!
# Dead-buffer reuse for the Jasmin dialect

`JasminStoreMemoryModel.lean` builds the non-aliasing memory model: distinct
`stackArr` SSA variables hold independent arrays, a `stackStore` binds the
updated array as a fresh `here` slot, and a later load from a *distinct* buffer
reads through `.there` (so the store is invisible to it). It closes the
`WellFormedStores` fragment — a relaxation of `StraightLine` that admits
non-aliasing `stackStore` binders — and `WellFormedStores.of_straightLine`.

This file is the next milestone toward a verified **dead-buffer-reuse** pass —
the foundation for reusing dead orchestration buffers. A buffer is *dead after*
a program point when no later `stackLoad` reads it; overwriting a dead buffer
(reusing its storage) is then sound: it cannot change what the program computes.

It contributes four pieces:

1. **`BufferDeadAfter`** — a buffer `B : Var Γ (stackArr w n)` is *dead after*
   the body `Com Γ t` when no later `stackLoad` reads it. Defined directly as
   the existing `LaterLoadsDisjoint B body` from the memory model (every later
   load's source is `ShapeDisjoint` from `B`, i.e. — at matching shape — a
   *distinct* buffer). So `BufferDeadAfter` reuses the `LaterLoadsDisjoint` /
   `LoadDisjointFrom` / `ExprStoresInto` machinery rather than reinventing it.

2. **Reuse-soundness** (`deadBuffer_denote_irrelevant`, the key lemma, all goals
   closed): if the `here` slot is dead after `body`, then `body.denote` does not
   depend on the value bound there — `body.denote (V.extend a) = body.denote
   (V.extend b)` for *any* arrays `a b`. Corollary `stackStore_dead_denote`:
   inserting a `stackStore` whose result buffer is dead does not change the
   denotation; the stored value is irrelevant. This is "storing into a buffer
   that is dead-after-this-point does not change the Com's denotation".

3. **Worked two-buffer reuse example** (`reuseDeadBuffer_denote`, all goals
   closed): a concrete straight-line `Com` over two buffers in which one dead
   buffer is overwritten by an arbitrary value, and the denotation is unchanged.

4. **`lowerComToProg_sem_eq_wf`** — the semantic-half theorem
   `lowerComToProg_sem_eq` extended from `StraightLine` to a fragment with
   non-aliasing `stackStore` binders, via a live-variable agreement argument. The
   `Com.denote` side (`denote_agreeOff_all` over the full-deadness predicate
   `BodyAvoidsBuffer`, the `valUpdate`/`storeVal` valuation surgery) and the
   store side (`execCom_storeVal`, a store-faithful evaluator induction) are both
   closed. A precise finding falls out of this work (see §4): `WellFormedStores`
   alone — which disjoints only later *loads* from a store target — is **not**
   sufficient for denotation preservation, because the in-place store's stale
   pre-store value is still observable by returning the target or by using it as
   a later store's source. The sufficient per-store condition is full
   deadness, threaded as `StoreSafe` (unique source naming + `BodyAvoidsBuffer`).

All lemmas have all goals closed; the only axioms are the standard
`propext` / `Classical.choice` / `Quot.sound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminBufferReuse

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminStoreMemoryModel

/-! ## 1. `BufferDeadAfter`

A buffer is *dead after* a program point when nothing downstream reads it. In
the memory model, "no later load reads `B`" is exactly `LaterLoadsDisjoint B`:
that predicate walks the body and, for each `stackLoad`, requires its source to
be `ShapeDisjoint` from the (appropriately shifted) `B` — which at matching
shape is `BufDisjoint`, i.e. a *distinct* SSA variable. A buffer that no load
reads is therefore disjoint from every load source, so `BufferDeadAfter` is a
definitional alias of `LaterLoadsDisjoint`. We give it its own name to mark the
intent (liveness, for the reuse pass) and to carry the convenience lemmas. -/

/-- A stack buffer `B : Var Γ (stackArr w n)` is **dead after** the body
    `body : Com jasminDialect Γ t` when no later `stackLoad` reads it: every
    `stackLoad` reachable in `body` has a source `ShapeDisjoint` from the
    (shifted) `B`. This is exactly the memory model's `LaterLoadsDisjoint`. -/
def BufferDeadAfter {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : jasminDialect.Ty}
    (body : Com jasminDialect Γ t) : Prop :=
  LaterLoadsDisjoint B body

/-- `BufferDeadAfter` is, by definition, `LaterLoadsDisjoint`. -/
theorem BufferDeadAfter_iff {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : jasminDialect.Ty}
    (body : Com jasminDialect Γ t) :
    BufferDeadAfter B body ↔ LaterLoadsDisjoint B body := Iff.rfl

/-- Nothing is read after a bare `ret`, so every buffer is dead after it. -/
theorem BufferDeadAfter.ret {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : jasminDialect.Ty}
    (v : Ctxt.Var Γ t) : BufferDeadAfter B (Com.ret v) := trivial

/-! ## 2. Reuse-soundness: the value at a dead slot is irrelevant

The reuse pass overwrites a dead buffer's storage with an arbitrary value. At
the `Com.denote` level a `stackStore` binds the updated array as a fresh `here`
slot, so the reused storage is exactly that head slot. Reuse-soundness is then:
if the head slot is dead after `body`, `body.denote` does not depend on the
value bound there — `body.denote (V.extend a) = body.denote (V.extend b)`.

We prove this by induction on `body`, generalised over an arbitrary dead buffer
variable `B` (not only `here`) and two valuations that **agree off `B`**: equal
at every variable except possibly `B`. The structural reason `B` is unobserved
is that no expression reads it; in the realistic emitted fragment the only op
reading a `stackArr` source is `stackLoad` (`regArith`/`castW` take only
registers, and the fragment carries no buffer-reading `stackStore`/`extCall`),
so `BufferDeadAfter B` (= `LaterLoadsDisjoint B`, every load `ShapeDisjoint` from
`B`) is deadness. We make the "only loads read buffers" side-condition
explicit as `OnlyLoadsReadBuffers`, and conclude the irrelevance lemma. -/

/-- `v` is **not the buffer `B`**, allowing for a type mismatch: either `v`'s
    type is not `stackArr wB nB` at all (then it cannot be `B`), or it is and the
    (cast) variable differs from `B`. Phrased so that a same-typed `v` reduces to
    plain `v ≠ B`, while a different-typed `v` is vacuously not `B`. -/
def NotBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : jasminDialect.Ty}
    (v : Ctxt.Var Γ t) : Prop :=
  ∀ (h : t = JasminTy.stackArr wB nB), h ▸ v ≠ B

/-- **Two valuations agree off the buffer `B`.** They are equal at every variable
    that is `NotBuffer B` — i.e. everywhere except possibly `B` itself. This is
    the induction-carrying relation for the irrelevance lemma: a write that only
    touches `B` relates the pre- and post-write valuations. -/
def AgreeOff {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) (V₁ V₂ : Ctxt.Valuation Γ) : Prop :=
  ∀ {t : jasminDialect.Ty} (v : Ctxt.Var Γ t), NotBuffer B v →
    v.lookup V₁ = v.lookup V₂

/-- **Structural restriction to load-only buffer reads.** Every binder's op is a
    `regArith`/`castW`/`stackLoad` — never a buffer-reading `stackStore` or
    `extCall`. This is the emitted-code fragment in which a `stackLoad` is the
    *only* way a `stackArr` flows into a computation, so a buffer disjoint from
    every later load source is unread. Threaded through the body. -/
def OnlyLoadsReadBuffers {Γ : Ctxt jasminDialect} :
    {t : jasminDialect.Ty} → Com jasminDialect Γ t → Prop
  | _, .ret _ => True
  | _, .var e body =>
      (∀ (w n : Nat), e.op ≠ .stackStore w n) ∧
      (∀ (name : String) (argTys : List jasminDialect.Ty) (retTy : jasminDialect.Ty),
        e.op ≠ .extCall name argTys retTy) ∧
      OnlyLoadsReadBuffers body

/-- The operand-independence of `callN` under the default `jasminDenote`, which is
    what lets `OnlyLoadsReadBuffers` omit `callN` from the exclusion list above:
    a `callN` denotes the constant `callNDefaults`, so it reads nothing, while
    `stackStore` and `extCall` must be excluded because they write and read the
    buffer respectively.

    The scope is the default instance. `jasminDenoteWithN` takes a `callNSem`
    parameter, and under an instance supplying a semantics that consults its
    arguments this equation is false — so `OnlyLoadsReadBuffers`,
    `expr_denote_agreeOff`'s `callN` arm, and `deadBuffer_denote_irrelevant`
    hold for `jasminDenote` and would need a `callN` exclusion to transport to
    `jasminDenoteWithN`. -/
theorem callN_denote_const (name : String) (argTys retTys : List JasminTy)
    (args args' : HVector (fun t => ⟦t⟧) argTys) :
    jasminDenote.denote (.callN name argTys retTys) args
      = jasminDenote.denote (.callN name argTys retTys) args' := rfl

/-- **The buffer `B` is never the returned value.** Walks the body, shifting `B`
    under each binder, and requires every `ret` to return a variable distinct
    from the (shifted) `B`. Together with deadness for loads, this rules out the
    other way `B`'s value would be observed: returning it directly. -/
def ReturnsNotBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {t : jasminDialect.Ty} → Com jasminDialect Γ t → Prop
  | _, .ret v => NotBuffer B v
  | _, .var (t := tEx) _ body => ReturnsNotBuffer (Ctxt.Var.there (s := tEx) B) body

/-- A variable of a type other than `stackArr wB nB` is never the buffer `B`. -/
theorem NotBuffer.of_ne_ty {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) {t : jasminDialect.Ty}
    (v : Ctxt.Var Γ t) (ht : t ≠ JasminTy.stackArr wB nB) : NotBuffer B v :=
  fun h => absurd h ht

/-- `ShapeDisjoint B src` (the memory model's cross-shape disjointness) implies
    the load source `src` is `NotBuffer B`: at matching shape it is `BufDisjoint`
    (`src ≠ B`); at differing shape the types differ, so `src` is vacuously not
    `B`. -/
theorem NotBuffer.of_shapeDisjoint {Γ : Ctxt jasminDialect} {wB nB w n : Nat}
    {B : Ctxt.Var Γ (.stackArr wB nB)} {src : Ctxt.Var Γ (.stackArr w n)}
    (h : ShapeDisjoint B src) : NotBuffer B src := by
  intro hty
  -- `hty : stackArr w n = stackArr wB nB`, so `w = wB`, `n = nB`.
  obtain ⟨rfl, rfl⟩ : w = wB ∧ n = nB := by
    cases hty; exact ⟨rfl, rfl⟩
  -- Now `ShapeDisjoint` at equal shape is `BufDisjoint B src`, i.e. `B ≠ src`.
  unfold ShapeDisjoint at h
  rw [dif_pos (And.intro (rfl : w = w) (rfl : n = n))] at h
  -- The casts are refls; `h : BufDisjoint B src`, target: `(rfl ▸ src) ≠ B`.
  simpa using fun (he : src = B) => h he.symm

/-- **Args-level non-buffer.** Every variable in an argument vector is
    `NotBuffer B`. For the emitted shapes only the `stackArr`-typed arguments can
    fail this (register/index/value args are `NotBuffer B` by type), so it bites
    exactly on buffer reads. -/
def ArgsNotBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {tys : List jasminDialect.Ty} → HVector (fun ty => Ctxt.Var Γ ty) tys → Prop
  | [], .nil => True
  | _ :: _, .cons v rest => NotBuffer B v ∧ ArgsNotBuffer B rest

/-- If two valuations agree off `B` and every argument is `NotBuffer B`, the
    looked-up argument vectors coincide. -/
theorem lookupArgs_agreeOff {Γ : Ctxt jasminDialect} {wB nB : Nat}
    {B : Ctxt.Var Γ (.stackArr wB nB)} {V₁ V₂ : Ctxt.Valuation Γ}
    (hag : AgreeOff B V₁ V₂) :
    {tys : List jasminDialect.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    ArgsNotBuffer B args → Expr.lookupArgs args V₁ = Expr.lookupArgs args V₂
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, h => by
      obtain ⟨hv, hrest⟩ := h
      show HVector.cons (v.lookup V₁) (Expr.lookupArgs rest V₁)
        = HVector.cons (v.lookup V₂) (Expr.lookupArgs rest V₂)
      rw [hag v hv, lookupArgs_agreeOff hag rest hrest]

/-- **Any-op expression irrelevance.** `Expr.denote` is a function of the looked-up
    arguments only (true for every op, including `stackStore`/`extCall`), so if
    all arguments are `NotBuffer B` then the expression denotes equally under any
    two valuations agreeing off `B`. This generalises `expr_denote_agreeOff` past
    the load-only fragment. -/
theorem expr_denote_argsNotBuffer {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    {wB nB : Nat} {B : Ctxt.Var Γ (.stackArr wB nB)}
    {V₁ V₂ : Ctxt.Valuation Γ} (hag : AgreeOff B V₁ V₂)
    (e : Expr jasminDialect Γ t) (h : ArgsNotBuffer B e.args) :
    e.denote V₁ = e.denote V₂ := by
  show e.retTy_eq ▸ DialectDenote.denote e.op (Expr.lookupArgs e.args V₁)
    = e.retTy_eq ▸ DialectDenote.denote e.op (Expr.lookupArgs e.args V₂)
  rw [lookupArgs_agreeOff hag e.args h]

/-- An argument vector none of whose types is the buffer's `stackArr wB nB` is
    `ArgsNotBuffer B`: each entry is `NotBuffer B` by type. -/
theorem argsNotBuffer_of_tys {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {tys : List jasminDialect.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (∀ ty ∈ tys, ty ≠ JasminTy.stackArr wB nB) → ArgsNotBuffer B args
  | [], .nil, _ => trivial
  | ty :: _, .cons v rest, h =>
      ⟨NotBuffer.of_ne_ty B v (h ty (by simp)),
       argsNotBuffer_of_tys B rest (fun t ht => h t (by simp [ht]))⟩

/-- An expression whose operand types are all distinct from the buffer's
    `stackArr wB nB` denotes identically under two valuations that agree off `B`:
    no operand can be `B`, so `expr_denote_argsNotBuffer` applies. -/
theorem expr_denote_of_argTys {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    {wB nB : Nat} {B : Ctxt.Var Γ (.stackArr wB nB)}
    {V₁ V₂ : Ctxt.Valuation Γ} (hag : AgreeOff B V₁ V₂)
    (e : Expr jasminDialect Γ t)
    (h : ∀ ty ∈ DialectSignature.sig (d := jasminDialect) e.op,
      ty ≠ JasminTy.stackArr wB nB) :
    e.denote V₁ = e.denote V₂ :=
  expr_denote_argsNotBuffer hag e (argsNotBuffer_of_tys B e.args h)

/-- A `regArith`/`castW`/`stackLoad` argument vector resolves identically under
    two valuations that `AgreeOff B`, provided (for the `stackLoad`) its source
    is disjoint from `B` (`LoadDisjointFrom B e`): the only non-register arg is
    the load source, which `NotBuffer.of_shapeDisjoint` shows is not `B`, and
    every register arg is `NotBuffer B` by type. Hence the expression's
    denotation is the same. -/
theorem expr_denote_agreeOff {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    {wB nB : Nat} {B : Ctxt.Var Γ (.stackArr wB nB)}
    {V₁ V₂ : Ctxt.Valuation Γ} (hag : AgreeOff B V₁ V₂)
    (e : Expr jasminDialect Γ t)
    (hNS : ∀ (w n : Nat), e.op ≠ .stackStore w n)
    (hNE : ∀ (name : String) (argTys : List jasminDialect.Ty)
      (retTy : jasminDialect.Ty), e.op ≠ .extCall name argTys retTy)
    (hLD : LoadDisjointFrom B e) :
    e.denote V₁ = e.denote V₂ := by
  obtain ⟨op, hret, args⟩ := e
  cases op with
  | regArith bop w =>
      -- args : [reg w, reg w]; both register, both NotBuffer B.
      match args with
      | .cons a (.cons b .nil) =>
          have ha := hag a (NotBuffer.of_ne_ty B a (by simp))
          have hb := hag b (NotBuffer.of_ne_ty B b (by simp))
          simp only [Expr.denote]
          congr 2
          show HVector.cons (a.lookup V₁) (HVector.cons (b.lookup V₁) .nil)
            = HVector.cons (a.lookup V₂) (HVector.cons (b.lookup V₂) .nil)
          rw [ha, hb]
  | stackLoad w n =>
      -- args : [stackArr w n, reg 64]; source from LoadDisjointFrom, idx reg.
      match args with
      | .cons src (.cons idx .nil) =>
          have hsrc : NotBuffer B src := by
            have : ShapeDisjoint B src := hLD
            exact NotBuffer.of_shapeDisjoint this
          have hs := hag src hsrc
          have hi := hag idx (NotBuffer.of_ne_ty B idx (by simp))
          simp only [Expr.denote]
          congr 2
          show HVector.cons (src.lookup V₁) (HVector.cons (idx.lookup V₁) .nil)
            = HVector.cons (src.lookup V₂) (HVector.cons (idx.lookup V₂) .nil)
          rw [hs, hi]
  | castW w w' =>
      match args with
      | .cons a .nil =>
          have ha := hag a (NotBuffer.of_ne_ty B a (by simp))
          simp only [Expr.denote]
          congr 2
          show HVector.cons (a.lookup V₁) .nil = HVector.cons (a.lookup V₂) .nil
          rw [ha]
  | stackStore w n => exact absurd rfl (hNS w n)
  | extCall name argTys retTy => exact absurd rfl (hNE name argTys retTy)
  | regConst w n =>
      -- Nullary constant: no arguments, denotation is `BitVec.ofNat w n`,
      -- independent of valuations.
      match args with
      | .nil => rfl
  -- The vector / carry-chain / immediate-shift / select ops take only `reg _`
  -- operands, so no operand can be the `stackArr` buffer `B`.
  | vpackZMM bop => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | vpackZMMd bop => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | vprordZMM n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | vpslldq n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | vpsrldq n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | vsimd sop =>
      exact expr_denote_of_argTys hag _
        (by cases sop <;> simp [DialectSignature.sig, SimdOp.argTys])
  | vymm op =>
      exact expr_denote_of_argTys hag _
        (by by_cases h : op.isBinary <;> simp [DialectSignature.sig, h])
  | mulhi w => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | addCarryLo w => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | addCarryHi w => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | rorImm w n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | shrImm w n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | sarImm w n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | shlImm w n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | select w => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | cmp c w => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | cmpImm c w n => exact expr_denote_of_argTys hag _ (by simp [DialectSignature.sig])
  | callN name argTys retTys =>
      -- Multi-result opaque call: under `jasminDenote` its denotation is the
      -- constant `callNDefaults` tuple projected to the head slot, so it does not
      -- read its operands. `callN_denote_const` states that dependence and records
      -- that it fails under a `jasminDenoteWithN` instance with an argument-reading
      -- `callNSem`.
      rfl

/-- If `.there v` (a shifted variable) is `NotBuffer (.there B)`, then `v` is
    `NotBuffer B`: `.there` is injective, so `v = B` would force `.there v = .there B`. -/
theorem NotBuffer.of_there {Γ : Ctxt jasminDialect} {wB nB : Nat}
    {B : Ctxt.Var Γ (.stackArr wB nB)} {tEx t : jasminDialect.Ty}
    {v : Ctxt.Var Γ t}
    (h : NotBuffer (Ctxt.Var.there (s := tEx) B) (Ctxt.Var.there (s := tEx) v)) :
    NotBuffer B v := by
  intro hty
  subst hty
  intro he
  exact h rfl (congrArg Ctxt.Var.there he)

/-- **`AgreeOff` is preserved by extending with equal values.** If `V₁`, `V₂`
    agree off `B` and the new head values coincide, then the extended valuations
    agree off the shifted buffer `.there B`. The new `here` slot matches by the
    equal head values; an old slot `.there v'` matches by `AgreeOff` applied to
    `v'` (whose `NotBuffer B` follows from `NotBuffer (.there B) (.there v')`). -/
theorem AgreeOff.extend {Γ : Ctxt jasminDialect} {wB nB : Nat}
    {B : Ctxt.Var Γ (.stackArr wB nB)} {V₁ V₂ : Ctxt.Valuation Γ}
    {tEx : jasminDialect.Ty} {x₁ x₂ : ⟦tEx⟧}
    (hag : AgreeOff B V₁ V₂) (hx : x₁ = x₂) :
    AgreeOff (Ctxt.Var.there (s := tEx) B) (V₁.extend x₁) (V₂.extend x₂) := by
  intro t v hv
  cases v with
  | here =>
      show x₁ = x₂
      exact hx
  | there v' =>
      show v'.lookup V₁ = v'.lookup V₂
      exact hag v' (NotBuffer.of_there hv)

/-- **Denotation depends only off the dead buffer (induction core).** If the
    buffer `B` is dead after `body` (`LaterLoadsDisjoint B body`, no later load
    reads it), `body` reads buffers only via `stackLoad` (`OnlyLoadsReadBuffers`,
    the emitted fragment), and `body` never returns `B` (`ReturnsNotBuffer`),
    then `body.denote` is identical on any two valuations that agree off `B`. By
    structural induction on `body`: the `ret` case uses `ReturnsNotBuffer` +
    `AgreeOff`; the `var` case uses `expr_denote_agreeOff` (the bound expression
    can't read `B`) to keep the extended valuations agreeing off `.there B`, then
    the IH. -/
theorem denote_agreeOff {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {t : jasminDialect.Ty} → (body : Com jasminDialect Γ t) →
    OnlyLoadsReadBuffers body → LaterLoadsDisjoint B body →
    ReturnsNotBuffer B body →
    {V₁ V₂ : Ctxt.Valuation Γ} → AgreeOff B V₁ V₂ →
    body.denote V₁ = body.denote V₂
  | _, .ret v, _, _, hRet, V₁, V₂, hag => by
      show v.lookup V₁ = v.lookup V₂
      exact hag v hRet
  | _, .var (t := tEx) e body, hOnly, hLLD, hRet, V₁, V₂, hag => by
      obtain ⟨hNS, hNE, hOnlyBody⟩ := hOnly
      obtain ⟨hLD, hLLDbody⟩ := hLLD
      -- The bound expression cannot read `B`, so it denotes equally under V₁/V₂.
      have he : e.denote V₁ = e.denote V₂ :=
        expr_denote_agreeOff hag e hNS hNE hLD
      -- Step `Com.denote`; the extended valuations agree off `.there B`.
      show body.denote (V₁.extend (e.denote V₁)) = body.denote (V₂.extend (e.denote V₂))
      exact denote_agreeOff (Ctxt.Var.there (s := tEx) B) body hOnlyBody hLLDbody hRet
        (hag.extend he)

/-- Two valuations that differ only in the **head** slot agree off `here`: every
    `NotBuffer here` variable is a `.there v'`, which reads the shared tail. -/
theorem agreeOff_here_extend {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (V : Ctxt.Valuation Γ) (a b : ⟦JasminTy.stackArr wB nB⟧) :
    AgreeOff (Γ := JasminTy.stackArr wB nB :: Γ) Ctxt.Var.here
      (V.extend a) (V.extend b) := by
  intro t v hv
  cases v with
  | here =>
      -- `here` is *not* `NotBuffer here`: `hv rfl rfl` is a contradiction.
      exact absurd (hv rfl) (by simp)
  | there v' =>
      show v'.lookup V = v'.lookup V
      rfl

/-! ### The reuse-soundness lemmas -/

/-- **Reuse-soundness (head form).** If the freshly-bound head buffer is dead
    after `body` — read by no later load (`LaterLoadsDisjoint here body`), in the
    load-only fragment (`OnlyLoadsReadBuffers body`), and never returned
    (`ReturnsNotBuffer here body`) — then `body.denote` does not depend on the
    value bound at that slot. Storing *any* array there is invisible. -/
theorem deadBuffer_denote_irrelevant {Γ : Ctxt jasminDialect} {wB nB : Nat}
    {t : jasminDialect.Ty}
    (body : Com jasminDialect (JasminTy.stackArr wB nB :: Γ) t)
    (hOnly : OnlyLoadsReadBuffers body)
    (hDead : BufferDeadAfter (Ctxt.Var.here (Γ := Γ) (t := .stackArr wB nB)) body)
    (hRet : ReturnsNotBuffer (Ctxt.Var.here (Γ := Γ) (t := .stackArr wB nB)) body)
    (V : Ctxt.Valuation Γ) (a b : ⟦JasminTy.stackArr wB nB⟧) :
    body.denote (V.extend a) = body.denote (V.extend b) :=
  denote_agreeOff Ctxt.Var.here body hOnly hDead hRet (agreeOff_here_extend V a b)

/-- **Reuse-soundness (`stackStore` form, the milestone's step 2).** Inserting a
    `stackStore` into buffer `X` ahead of `body` does **not** change the
    denotation when the store's freshly-bound result buffer is dead after `body`
    (load-only fragment, never returned): the program denotes to `body` run on
    *any* array in that slot — in particular the stored value `v`, the index `i`,
    and the prior contents of `X` are all irrelevant. This is "storing an
    arbitrary value into a buffer that is dead-after-this-point does not change
    the Com's denotation", proved on top of the `stackStore` denotation
    (`stackStore_denote` binds the head slot) and `deadBuffer_denote_irrelevant`. -/
theorem stackStore_dead_denote {Γ : Ctxt jasminDialect} {wX nX : Nat}
    {t : jasminDialect.Ty}
    (X : Ctxt.Var Γ (.stackArr wX nX)) (i : Ctxt.Var Γ (.reg 64))
    (v : Ctxt.Var Γ (.reg wX))
    (body : Com jasminDialect (JasminTy.stackArr wX nX :: Γ) t)
    (hOnly : OnlyLoadsReadBuffers body)
    (hDead : BufferDeadAfter (Ctxt.Var.here (Γ := Γ) (t := .stackArr wX nX)) body)
    (hRet : ReturnsNotBuffer (Ctxt.Var.here (Γ := Γ) (t := .stackArr wX nX)) body)
    (V : Ctxt.Valuation Γ) (arbitrary : ⟦JasminTy.stackArr wX nX⟧) :
    (Com.var
        (Expr.mk (JasminOp.stackStore wX nX) rfl
          (.cons X (.cons i (.cons v .nil)))) body).denote V
      = body.denote (V.extend arbitrary) := by
  -- The store binds the head slot with `stackSet …`; deadness makes that value
  -- irrelevant, so it equals running `body` on any array.
  show body.denote (V.extend (stackSet (X.lookup V) (i.lookup V).toNat (v.lookup V)))
    = body.denote (V.extend arbitrary)
  exact deadBuffer_denote_irrelevant body hOnly hDead hRet V _ _

/-! ## 3. Worked two-buffer reuse example

A concrete straight-line program over **two** distinct stack buffers `Y`
(`stackArr 16 4`) and the freshly stored buffer `X` (also `stackArr 16 4`),
sharing a `reg 64` index. The first binder is a `stackStore` into the head
buffer `X`; the body then loads from the *distinct* buffer `Y` and returns the
loaded element. Buffer `X` is dead after the store — nothing downstream reads it
(the only load reads `Y`, the only return is the `reg 16` load result), so
overwriting `X` with an arbitrary value leaves the denotation unchanged.

We work in the context `Γ₀ = [stackArr 16 4, reg 64]`, so within the program:

* `Y      = .here`         (the loaded buffer),
* `idx    = .there .here`  (the shared index register),

and the head `stackStore` binds the dead buffer at the new `.here`; in the body
`Y` and `idx` are reached as `.there Y` / `.there idx`. -/

/-- Context of the worked example: one stack buffer `Y` and one index register. -/
abbrev twoBufCtxt : Ctxt jasminDialect := [JasminTy.stackArr 16 4, JasminTy.reg 64]

/-- The body that runs after the dead-buffer store: load element `idx` of the
    distinct buffer `Y` (both reached via `.there`, since they were in scope
    before the store) and return it. -/
def reuseBody :
    Com jasminDialect (JasminTy.stackArr 16 4 :: twoBufCtxt) (.reg 16) :=
  Com.var
    (Expr.mk (JasminOp.stackLoad 16 4) rfl
      (.cons (Ctxt.Var.there Ctxt.Var.here)
        (.cons (Ctxt.Var.there (Ctxt.Var.there Ctxt.Var.here)) .nil)))
    (Com.ret Ctxt.Var.here)

/-- `reuseBody` reads buffers only through its single `stackLoad`. -/
theorem reuseBody_onlyLoads : OnlyLoadsReadBuffers reuseBody := by
  refine ⟨?_, ?_, trivial⟩
  · intro w n h; exact absurd h (by simp)
  · intro name argTys retTy h; exact absurd h (by simp)

/-- The head (stored) buffer is **dead after** `reuseBody`: under the load
    binder the dead buffer (the new `.here`) becomes `.there .here`, while the
    loaded buffer `Y` becomes `.there (.there .here)`. These are distinct SSA
    variables, so the only load is `ShapeDisjoint` from the dead buffer. -/
theorem reuseBody_dead :
    BufferDeadAfter
      (Ctxt.Var.here (Γ := twoBufCtxt) (t := .stackArr 16 4)) reuseBody := by
  refine ⟨?_, trivial⟩
  -- LoadDisjointFrom here load: the dead buffer `here` vs the load source
  -- `there here` (the loaded buffer `Y`, shifted under the store binder).
  show ShapeDisjoint Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here)
  -- Same shape (16,4): reduces to `here ≠ there here`.
  unfold ShapeDisjoint
  rw [dif_pos (And.intro (rfl : (16 : Nat) = 16) (rfl : (4 : Nat) = 4))]
  show BufDisjoint Ctxt.Var.here (Ctxt.Var.there Ctxt.Var.here)
  intro h
  exact absurd h (by simp)

/-- `reuseBody` returns the `reg 16` load result, not the stored buffer (the
    return type differs from `stackArr 16 4`). -/
theorem reuseBody_returnsNotBuffer :
    ReturnsNotBuffer
      (Ctxt.Var.here (Γ := twoBufCtxt) (t := .stackArr 16 4)) reuseBody := by
  -- Body's `ret` returns a `reg 16` variable; its type ≠ `stackArr 16 4`.
  show NotBuffer _ (Ctxt.Var.here)
  exact NotBuffer.of_ne_ty _ _ (by simp)

/-- **Worked two-buffer reuse (the milestone's step 3).** Overwriting the dead
    buffer `X` (the head slot) with an *arbitrary* array via a `stackStore` does
    not change what the program computes: it still returns element `idx` of the
    distinct, live buffer `Y`. The stored value `v`, the index `i`, and the prior
    contents of `X` are all invisible. -/
theorem reuseDeadBuffer_denote
    (X : Ctxt.Var twoBufCtxt (.stackArr 16 4)) (i : Ctxt.Var twoBufCtxt (.reg 64))
    (v : Ctxt.Var twoBufCtxt (.reg 16))
    (V : Ctxt.Valuation twoBufCtxt) (arbitrary : ⟦JasminTy.stackArr 16 4⟧) :
    (Com.var
        (Expr.mk (JasminOp.stackStore 16 4) rfl
          (.cons X (.cons i (.cons v .nil)))) reuseBody).denote V
      = reuseBody.denote (V.extend arbitrary) :=
  stackStore_dead_denote X i v reuseBody
    reuseBody_onlyLoads reuseBody_dead reuseBody_returnsNotBuffer V arbitrary

/-! ## 4. The live-variable agreement machinery (`Com.denote` side)

`lowerComToProg_sem_eq` (in `JasminPrintSemCorrect`) proves the lowering is
denotation-preserving on `StraightLine`. The goal of this section is to extend it
to the wider `WellFormedStores` fragment — the one that admits non-aliasing
`stackStore` binders. We build the `Com.denote`-side half of the live-variable
argument the milestone needs, generalising §2's `denote_agreeOff` past the
load-only fragment.

### `WellFormedStores` is *not* sufficient for denotation preservation

`WellFormedStores` requires only that each `stackStore` target is disjoint, in
the post-store context, from every later **load** source (`LaterLoadsDisjoint`).
That is too weak for denotation preservation. The reason is the
in-place aliasing recorded in `stackStore_aliases_source`: a `stackStore` writes
its result to the source array's own SSA name, so after the binder the fresh
`.here` (post-store array) and the in-scope `.there X` (pre-store array) collapse
to one store slot holding the post-store array, while `Com.denote` keeps
`.there X` at its pre-store value. `LaterLoadsDisjoint` forbids a later *load*
from observing the stale `.there X`, but it does **not** forbid:

* **returning it** — `ret (.there X)` reads the stale value directly; or
* **a later store using it as its source** — `stackStore`'s denotation is
  `stackSet (src.lookup V) …`, so a store whose source is the stale `.there X`
  threads the stale value into a fresh array.

Both are admitted by `WellFormedStores`, and both break the equality
`runProg = Com.denote`. Concretely, over `Γ = [stackArr 8 1, reg 64, reg 8]`,
the program `var (stackStore into .here) (ret (.there .here))` *is*
`WellFormedStores` (the trailing `ret` carries no load obligation), yet on the
input where `X` is the all-`1` array and the stored value is `5` at index `0`,
`Com.denote` returns the pre-store array (a `1` at index 0) while `runProg`
returns the post-store array (a `5` at index 0). They differ. So the literal
`WellFormedStores`-only statement is false; preservation needs the store target
to be **fully dead** after the store — read by no later load, *no later store
source*, and not returned.

### What this section provides, and the precisely-scoped residual

The full-deadness condition is exactly `BodyAvoidsBuffer (.there target) body`:
every later expression's arguments and every later `ret` are `NotBuffer`
(`ShapeDisjoint`) from the (shifted) target. We generalise §2's
load-only `denote_agreeOff` to `denote_agreeOff_all` over *this* condition (it
tolerates `stackStore`/`extCall` binders in the body), and build the
`valUpdate` valuation surgery that the store-side bridge needs. These are the
`Com.denote`-side half, fully closed.

The store-side (`execCom`) half — re-running the evaluator induction so that the
in-place write's stale aliases are absorbed by full deadness — is carried as the
single explicit hypothesis `hExec` of the theorem below. It is a precisely-stated
side condition on the named evaluator (not an admitted proof): the residual store-level
agreement under full per-store deadness, which any caller discharges from the
`execCom` semantics. Everything else — the `runProg`/seed-store wrapper, the
`StraightLine` reduction to `lowerComToProg_sem_eq`, and all the denote-side
machinery — is closed unconditionally. -/

/-- **Body avoids the buffer `B` (full deadness).** Every binder's expression has
    all arguments `NotBuffer B` and every `ret` is `NotBuffer B`, with `B` shifted
    under each binder. This is the deadness condition that preservation
    needs: it forbids a later load, a later store *source*, an `extCall`
    argument, and a return from observing `B` — unlike `LaterLoadsDisjoint`, which
    constrains loads only. -/
def BodyAvoidsBuffer {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {t : jasminDialect.Ty} → Com jasminDialect Γ t → Prop
  | _, .ret v => NotBuffer B v
  | _, .var (t := tEx) e body =>
      ArgsNotBuffer B e.args ∧ BodyAvoidsBuffer (Ctxt.Var.there (s := tEx) B) body

/-- **Denotation depends only off a fully-dead buffer (any-op induction core).**
    If `B` is fully dead after `body` (`BodyAvoidsBuffer`, no later expression
    argument or `ret` reads it), then `body.denote` is identical on any two
    valuations that agree off `B`. By structural induction: the `ret` case uses
    the avoided return; the `var` case uses `expr_denote_argsNotBuffer` (the bound
    expression's value is unchanged) to keep the extended valuations agreeing off
    `.there B`, then the IH. This is the `Com.denote`-side half of the
    live-variable argument, valid even when `body` itself contains stores. -/
theorem denote_agreeOff_all {Γ : Ctxt jasminDialect} {wB nB : Nat}
    (B : Ctxt.Var Γ (.stackArr wB nB)) :
    {t : jasminDialect.Ty} → (body : Com jasminDialect Γ t) →
    BodyAvoidsBuffer B body →
    {V₁ V₂ : Ctxt.Valuation Γ} → AgreeOff B V₁ V₂ →
    body.denote V₁ = body.denote V₂
  | _, .ret v, hRet, V₁, V₂, hag => by
      show v.lookup V₁ = v.lookup V₂
      exact hag v hRet
  | _, .var (t := tEx) e body, hAvoid, V₁, V₂, hag => by
      obtain ⟨hArgs, hBody⟩ := hAvoid
      have he : e.denote V₁ = e.denote V₂ := expr_denote_argsNotBuffer hag e hArgs
      show body.denote (V₁.extend (e.denote V₁)) = body.denote (V₂.extend (e.denote V₂))
      exact denote_agreeOff_all (Ctxt.Var.there (s := tEx) B) body hBody (hag.extend he)

/-! ### Valuation surgery for the store-side bridge

A `stackStore` step writes the post-store array to the source buffer's slot. The
bridging valuation that the named evaluator actually computes against differs
from the functional `Com.denote` valuation only at the (now-dead) source slot.
`valUpdate` performs exactly that one-slot replacement; its two lookup laws say
the updated slot reads the new value and every `NotBuffer`-distinct slot is
untouched. The bridged and functional valuations then `AgreeOff` the source
buffer, so `denote_agreeOff_all` closes the gap. -/

/-- Replace the value at the variable `u` in a valuation. -/
def valUpdate {Γ : Ctxt jasminDialect} {tU : jasminDialect.Ty} :
    (V : Ctxt.Valuation Γ) → (u : Ctxt.Var Γ tU) → ⟦tU⟧ → Ctxt.Valuation Γ
  | .cons _ tl, .here, x => .cons x tl
  | .cons hd tl, .there u', x => .cons hd (valUpdate tl u' x)

/-- The updated slot reads back the new value. -/
theorem valUpdate_lookup_self {Γ : Ctxt jasminDialect} {tU : jasminDialect.Ty} :
    (V : Ctxt.Valuation Γ) → (u : Ctxt.Var Γ tU) → (x : ⟦tU⟧) →
    Ctxt.Var.lookup u (valUpdate V u x) = x
  | .cons _ _, .here, _ => rfl
  | .cons _ tl, .there u', x => valUpdate_lookup_self tl u' x

/-- A slot `NotBuffer`-distinct from the updated buffer is untouched. -/
theorem valUpdate_lookup_other {Γ : Ctxt jasminDialect} {wB nB : Nat}
    {t' : jasminDialect.Ty} :
    (V : Ctxt.Valuation Γ) → (B : Ctxt.Var Γ (.stackArr wB nB)) →
    (u' : Ctxt.Var Γ t') → NotBuffer B u' → (x : ⟦JasminTy.stackArr wB nB⟧) →
    Ctxt.Var.lookup u' (valUpdate V B x) = u'.lookup V
  | .cons _ _, .here, .here, hnb, _ => absurd (hnb rfl) (by simp)
  | .cons _ _, .here, .there _, _, _ => rfl
  | .cons _ _, .there _, .here, _, _ => rfl
  | .cons _ tl, .there B0, .there w, hnb, x => by
      show Ctxt.Var.lookup w (valUpdate tl B0 x) = w.lookup tl
      exact valUpdate_lookup_other tl B0 w (NotBuffer.of_there hnb) x

/-- The valuation read off the store under `vm`: every variable reads its lowered
    name. `StoreAgrees vm (storeVal vm s) s` holds reflexively. -/
def storeVal {Γ : Ctxt jasminDialect} (vm : VarMap Γ) :
    Store → Ctxt.Valuation Γ
  | s => match Γ, vm with
    | [], _ => .nil
    | _ :: _, vm =>
        .cons (s.get (vm _ Ctxt.Var.here) _)
          (storeVal (fun t v => vm t (.there v)) s)

/-- `storeVal` reads each variable's lowered name from the store. -/
theorem storeVal_lookup {Γ : Ctxt jasminDialect} :
    (vm : VarMap Γ) → (s : Store) → {t : jasminDialect.Ty} → (v : Ctxt.Var Γ t) →
    Ctxt.Var.lookup v (storeVal vm s) = s.get (vm t v) t
  | vm, s, _, .here => rfl
  | vm, s, _, .there v' => by
      show Ctxt.Var.lookup v' (storeVal (fun t v => vm t (.there v)) s)
        = s.get (vm _ (.there v')) _
      exact storeVal_lookup (fun t v => vm t (.there v)) s v'

/-- The store-derived valuation agrees with the store reflexively. -/
theorem storeAgrees_storeVal {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (s : Store) :
    StoreAgrees vm (storeVal vm s) s :=
  fun _t v => (storeVal_lookup vm s v).symm

/-- If two valuations agree at every variable, every argument vector resolves
    identically under them. -/
theorem lookupArgs_eq_of_lookup_eq {Γ : Ctxt jasminDialect} {V₁ V₂ : Ctxt.Valuation Γ}
    (hag : ∀ {t : jasminDialect.Ty} (v : Ctxt.Var Γ t), v.lookup V₁ = v.lookup V₂) :
    {tys : List jasminDialect.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    Expr.lookupArgs args V₁ = Expr.lookupArgs args V₂
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons (v.lookup V₁) (Expr.lookupArgs rest V₁)
        = HVector.cons (v.lookup V₂) (Expr.lookupArgs rest V₂)
      rw [hag v, lookupArgs_eq_of_lookup_eq hag rest]

/-- Two valuations that agree at every variable denote any program equally. The
    `.ret` case is the agreement at the returned variable; the `.var` case
    extends agreement by the (then-equal) bound value and recurses. -/
theorem denote_eq_of_lookup_eq {Γ : Ctxt jasminDialect} {V₁ V₂ : Ctxt.Valuation Γ}
    (hag : ∀ {t : jasminDialect.Ty} (v : Ctxt.Var Γ t), v.lookup V₁ = v.lookup V₂) :
    {t : jasminDialect.Ty} → (body : Com jasminDialect Γ t) →
    body.denote V₁ = body.denote V₂
  | _, .ret v => hag v
  | _, .var (t := tEx) e body => by
      have he : e.denote V₁ = e.denote V₂ := by
        show e.retTy_eq ▸ DialectDenote.denote e.op (Expr.lookupArgs e.args V₁)
          = e.retTy_eq ▸ DialectDenote.denote e.op (Expr.lookupArgs e.args V₂)
        rw [lookupArgs_eq_of_lookup_eq hag e.args]
      show body.denote (V₁.extend (e.denote V₁)) = body.denote (V₂.extend (e.denote V₂))
      refine denote_eq_of_lookup_eq (fun {t'} v => ?_) body
      cases v with
      | here => show e.denote V₁ = e.denote V₂; exact he
      | there v' => show v'.lookup V₁ = v'.lookup V₂; exact hag v'

/-! ## 5. The store-side `execCom` induction over `WellFormedStores`

We now run the named-evaluator induction. The conclusion is *store-faithful*:
`(execCom … s com).2 = com.denote (storeVal vm s)`, i.e. the evaluator computes
the program's denotation **on the valuation read off the store**. Because
`StoreAgrees vm (storeVal vm s) s` holds reflexively, the bound expression's
value `execExpr e s` is exactly `e.denote (storeVal vm s)` (`execExpr_eq`), so
each step lines up.

The single non-aliasing side condition the in-place `stackStore` step needs is
threaded as `StoreSafe`: at every `stackStore` binder, (i) the **source buffer's
name is held by no other in-scope variable** (so the in-place write clobbers no
live distinct slot — the bound name is *uniquely* the source's), and (ii) the
shifted source buffer is **fully dead** after the binder (`BodyAvoidsBuffer`, no
later argument or `ret` reads it). Under (i)–(ii) the post-store store-valuation
agrees with the functional `Com.denote` valuation *off* the dead source slot, and
`denote_agreeOff_all` bridges the two. `StoreSafe` is exactly the gap between
`WellFormedStores` (loads only) and denotation preservation; it is the precise
residual identified in §4 (and witnessed false for `WellFormedStores` alone by
the `store; ret stale` counterexample). -/

/-- **Per-store non-aliasing + full-deadness side condition**, threaded with the
    resolver and fresh counter exactly as `execCom` threads them. Empty after a
    `ret`. At a `stackStore` binder it requires the source buffer to be uniquely
    named among in-scope variables and fully dead after the binder; for any binder
    it recurses with the resolver extended by the binder's bound name. -/
def StoreSafe {Γ : Ctxt jasminDialect} (vm : VarMap Γ) (next : Nat) :
    {t : jasminDialect.Ty} → Com jasminDialect Γ t → Prop
  | _, .ret _ => True
  | _, .var (t := tEx) e body =>
      (∀ (w n : Nat) (source : Ctxt.Var Γ (.stackArr w n)),
        e.op = .stackStore w n → argName vm e.args 0 = vm _ source →
        -- (i) the source buffer's name is held by no other in-scope variable;
        (∀ (t' : jasminDialect.Ty) (u' : Ctxt.Var Γ t'),
            vm t' u' = vm _ source → (∃ h : t' = JasminTy.stackArr w n, h ▸ u' = source)) ∧
        -- (ii) the (shifted) source buffer is fully dead after the binder.
        BodyAvoidsBuffer (Ctxt.Var.there (s := tEx) source) body) ∧
      StoreSafe (vm.extend (t := tEx) (resultName vm e (freshName next))) (next + 1) body

/-- A `stackStore` expression has a definite source buffer (its 0-th argument),
    and every resolver names the 0-th argument by that buffer. -/
theorem stackStore_source_exists {Γ : Ctxt jasminDialect} {tEx : jasminDialect.Ty}
    (e : Expr jasminDialect Γ tEx) (w n : Nat) (hop : e.op = .stackStore w n) :
    ∃ (source : Ctxt.Var Γ (.stackArr w n)),
      ∀ (vm : VarMap Γ), argName vm e.args 0 = vm _ source := by
  rcases e with ⟨op, hret, args⟩
  subst hop
  cases args with
  | cons src rest => exact ⟨src, fun vm => rfl⟩

/-- For a `stackStore` binder (cast-free in the result type), `resultName` reuses
    the source array's name. The typed `stackStore_aliases_source` needs the
    return type to be syntactically `stackArr w n`; here we only know `e.op`. -/
theorem resultName_stackStore' {Γ : Ctxt jasminDialect} {tEx : jasminDialect.Ty}
    {vm : VarMap Γ} (e : Expr jasminDialect Γ tEx) {w n : Nat}
    (hop : e.op = .stackStore w n) (fresh : String) :
    resultName vm e fresh = argName vm e.args 0 := by
  unfold resultName
  split <;> rename_i heq
  · rfl
  · rw [hop] at heq; exact absurd heq (by simp)

/-- **`execCom` is store-faithful on `WellFormedStores`** under `StoreSafe`,
    fresh-name injectivity, and resolver freshness. The result the evaluator reads
    from the threaded store equals the program's denotation on the store-derived
    valuation. By induction on the program:

    * `.ret v`: both sides read `v`'s lowered name (`storeVal_lookup`).
    * a **non-`stackStore`** binder: `resultName` is the fresh `freshName next`,
      which freshness keeps distinct from every in-scope name, so the stepped
      store-valuation equals the functional extension at *every* variable
      (`denote_eq_of_lookup_eq`); apply the IH.
    * a **`stackStore`** binder: `resultName` is the source's own name. The
      stepped store-valuation agrees with the functional extension *off* the dead
      source slot — at `.here` by `get_set_same`, at a distinct `.there u'`
      because `StoreSafe`'s unique-naming forbids `u'` from sharing the source
      name. `denote_agreeOff_all` over the dead (`BodyAvoidsBuffer`) source slot
      bridges them; apply the IH. -/
theorem execCom_storeVal {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    (com : Com jasminDialect Γ t) →
    {vm : VarMap Γ} → {s : Store} → {next : Nat} →
    FreshFor vm next → StoreSafe vm next com →
    (execCom leafSem vm next s com).2 = com.denote (storeVal vm s)
  | .ret v, vm, s, _next, _hF, _hSafe => by
      show s.get (vm t v) t = v.lookup (storeVal vm s)
      rw [storeVal_lookup vm s v]
  | .var (t := tEx) e body, vm, s, next, hF, hSafe => by
      obtain ⟨hStore, hSafeBody⟩ := hSafe
      -- One step of `execCom`/`Com.denote`.
      have hStepExec : (execCom leafSem vm next s (.var e body)).2
          = (execCom leafSem (vm.extend (resultName vm e (freshName next))) (next + 1)
              (s.set (resultName vm e (freshName next)) (execExpr leafSem vm e s)) body).2 := rfl
      rw [hStepExec]
      set bound := resultName vm e (freshName next) with hboundDef
      set s' := s.set bound (t := tEx) (execExpr leafSem vm e s) with hs'Def
      set vm' := vm.extend (t := tEx) bound with hvm'Def
      -- Reflexive store-agreement, so `execExpr` is the denotation on `storeVal`.
      have hSA : StoreAgrees vm (storeVal vm s) s := storeAgrees_storeVal vm s
      have hExec : execExpr leafSem vm e s = e.denote (storeVal vm s) :=
        execExpr_eq hLeaf hSA e
      -- IH on the body, in the stepped state.
      have hF' : FreshFor vm' (next + 1) := by
        -- Freshness of the extension. For a non-store bound this is the fresh
        -- name; for a store it is an in-scope name, but freshness of the *tail*
        -- only requires the extension to avoid `freshName k`, `k ≥ next+1`.
        intro k t' v hk
        cases v with
        | here =>
            show bound ≠ freshName k
            by_cases hns : ∃ w n, e.op = .stackStore w n
            · -- store: bound = vm source (an in-scope name), fresh by `hF`.
              obtain ⟨w, n, hop⟩ := hns
              obtain ⟨source, hsrc⟩ := stackStore_source_exists e w n hop
              have hb : bound = vm _ source := by
                rw [hboundDef, resultName_stackStore' e hop (freshName next), hsrc vm]
              rw [hb]; exact hF k _ source (by omega)
            · -- non-store: bound = freshName next, distinct from freshName k.
              have hbf : bound = freshName next := by
                rw [hboundDef]
                exact resultName_of_notStackStore (fun w n hh => hns ⟨w, n, hh⟩) _
              rw [hbf]; intro heq; exact absurd (hInj heq) (by omega)
        | there v' =>
            show vm t' v' ≠ freshName k
            exact hF k t' v' (by omega)
      have ih := execCom_storeVal hLeaf hInj body hF' hSafeBody
        (vm := vm') (s := s')
      rw [ih]
      -- Reduce the RHS step and bridge the two body-valuations.
      show body.denote (storeVal vm' s')
        = body.denote ((storeVal vm s).extend (e.denote (storeVal vm s)))
      -- The bound name's value is `e.denote (storeVal vm s)` (`get_set_same`).
      have hHere : Ctxt.Var.lookup (Ctxt.Var.here) (storeVal vm' s')
          = e.denote (storeVal vm s) := by
        rw [storeVal_lookup vm' s' Ctxt.Var.here]
        show s'.get bound tEx = e.denote (storeVal vm s)
        rw [hs'Def, Store.get_set_same, hExec]
      by_cases hns : ∃ w n, e.op = .stackStore w n
      · -- `stackStore` binder: bridge off the dead source slot.
        obtain ⟨w, n, hop⟩ := hns
        obtain ⟨source, hsrc⟩ := stackStore_source_exists e w n hop
        -- `bound` is the source's name.
        have hb : bound = vm _ source := by
          rw [hboundDef, resultName_stackStore' e hop (freshName next), hsrc vm]
        obtain ⟨hUniq, hDead⟩ := hStore w n source hop (hsrc vm)
        -- Bridge across the dead source slot (shifted under the binder).
        refine denote_agreeOff_all (Ctxt.Var.there (s := tEx) source) body hDead ?_
        intro t' u hu
        cases u with
        | here =>
            show Ctxt.Var.lookup (Ctxt.Var.here) (storeVal vm' s')
              = Ctxt.Var.lookup (Ctxt.Var.here)
                  ((storeVal vm s).extend (e.denote (storeVal vm s)))
            rw [hHere]; rfl
        | there u' =>
            -- `hu : NotBuffer (.there source) (.there u')`, so `NotBuffer source u'`.
            have hNB : NotBuffer source u' := NotBuffer.of_there hu
            show Ctxt.Var.lookup (Ctxt.Var.there u') (storeVal vm' s')
              = Ctxt.Var.lookup (Ctxt.Var.there u')
                  ((storeVal vm s).extend (e.denote (storeVal vm s)))
            rw [storeVal_lookup vm' s' (Ctxt.Var.there u')]
            show s'.get (vm t' u') t' = Ctxt.Var.lookup u' (storeVal vm s)
            rw [storeVal_lookup vm s u']
            show s'.get (vm t' u') t' = s.get (vm t' u') t'
            -- `vm u' ≠ bound = vm source`: else unique-naming forces `u' = source`,
            -- contradicting `NotBuffer source u'`.
            have hne : vm t' u' ≠ bound := by
              rw [hb]
              intro heq
              obtain ⟨hh, hv⟩ := hUniq t' u' heq
              subst hh
              exact hNB rfl hv
            rw [hs'Def, Store.get_set_other s hne]
      · -- non-`stackStore` binder: store-valuations agree at every variable.
        have hbf : bound = freshName next := by
          rw [hboundDef]
          exact resultName_of_notStackStore (fun w n hh => hns ⟨w, n, hh⟩) _
        refine denote_eq_of_lookup_eq (fun {t'} u => ?_) body
        cases u with
        | here =>
            show Ctxt.Var.lookup (Ctxt.Var.here) (storeVal vm' s')
              = Ctxt.Var.lookup (Ctxt.Var.here)
                  ((storeVal vm s).extend (e.denote (storeVal vm s)))
            rw [hHere]; rfl
        | there u' =>
            show Ctxt.Var.lookup (Ctxt.Var.there u') (storeVal vm' s')
              = Ctxt.Var.lookup (Ctxt.Var.there u')
                  ((storeVal vm s).extend (e.denote (storeVal vm s)))
            rw [storeVal_lookup vm' s' (Ctxt.Var.there u')]
            show s'.get (vm t' u') t' = Ctxt.Var.lookup u' (storeVal vm s)
            rw [storeVal_lookup vm s u']
            show s'.get (vm t' u') t' = s.get (vm t' u') t'
            have hne : vm t' u' ≠ bound := by
              rw [hbf]; exact hF next t' u' (Nat.le_refl next)
            rw [hs'Def, Store.get_set_other s hne]

/-! ## 6. `lowerComToProg` on `WellFormedStores`

Assembling the wrapper. `runProg` seeds the parameter store from `V`; that seed
agrees with `V` (`seedStore_agrees`, via the parameter resolver injectivity
`hPinj`), so `storeVal (paramsAndMap Γ).2 (seedStore …) = V` at every variable
and `execCom_storeVal` computes `com.denote V`. The parameter resolver's
freshness is `paramsAndMap_FreshFor`; the per-store non-aliasing / deadness side
condition is `StoreSafe`. -/

set_option linter.unusedVariables false in
/-- **`lowerComToProg` is denotation-preserving on `WellFormedStores`.**

    Same conclusion as `lowerComToProg_sem_eq`, over the wider fragment that
    admits non-aliasing `stackStore` binders. As established in §4,
    `WellFormedStores` alone is **not** sufficient — a store target may still be
    returned or used as a later store's source, both of which expose the stale
    pre-store value (witnessed by the `store; ret stale` counterexample). The
    sufficient side condition is `StoreSafe`: at each `stackStore`, the
    source buffer is uniquely named among in-scope variables and fully dead after
    the binder. Under it the result follows from the store-faithful induction
    `execCom_storeVal` (the `Com.denote` half being the `denote_agreeOff_all` /
    `valUpdate` machinery of §4) and the `runProg`/seed-store wrapper.

    `hWF` (`WellFormedStores com`) is retained in the interface — it is the
    fragment marker — even though `StoreSafe` strictly subsumes its load
    obligations. -/
theorem lowerComToProg_sem_eq_wf {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    (hInj : Function.Injective freshName)
    {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty}
    (com : Com jasminDialect Γ t) (hWF : WellFormedStores com)
    (hPinj : ∀ (t t' : jasminDialect.Ty) (v : Ctxt.Var Γ t)
                (v' : Ctxt.Var Γ t'), (paramsAndMap Γ).2 t v = (paramsAndMap Γ).2 t' v' →
                (∃ h : t = t', h ▸ v = v'))
    (hSafe : StoreSafe (paramsAndMap Γ).2 0 com)
    (V : Ctxt.Valuation Γ) :
    runProg leafSem com V = com.denote V := by
  unfold runProg
  -- The seed store agrees with `V`, so its store-valuation is `V` everywhere.
  have hSeed : StoreAgrees (paramsAndMap Γ).2 V (seedStore (paramsAndMap Γ).2 V) :=
    seedStore_agrees hPinj
  rw [execCom_storeVal hLeaf hInj com paramsAndMap_FreshFor hSafe]
  -- `storeVal (paramsAndMap Γ).2 (seedStore …)` agrees with `V` at every variable.
  exact denote_eq_of_lookup_eq
    (fun {t'} v => by rw [storeVal_lookup _ _ v]; exact hSeed t' v) com

end CatCrypt.Crypto.SecureCompilation.VIR.JasminBufferReuse
