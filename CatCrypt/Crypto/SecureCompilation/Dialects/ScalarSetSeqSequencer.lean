/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

set_option autoImplicit false

/-!
# Width-parametric scalar-statement SEQUENCER (the whole-kernel keystone)

`ScalarSExprWidth32Prototype.lowerSExprW` front-sources a SINGLE `.sword w`
`SExpr` to a `Com catCryptDialect`, and the `FrontSourced` namespaces
(`Sha256RoundWidth32Front`, `ChaChaEmit`, …) prove single-expression provenance
`(progOf …).isSome := by rfl` (axiom-clean). But a WHOLE crypto kernel is a
SEQUENCE of `RScalarSetExpr`-style statements `dst := e` (≈64 SHA rounds ⇒ ~4000
named-intermediate bindings). `translateDialectControlTop` over that sequence does
NOT reduce by `rfl`, and a single `native_decide` over its `isSome` OOMs — it must
build/normalise the whole ~4000-node `Com` term at once.

This module supplies the missing combinator: a statement SEQUENCER
`lowerScalarSetSeqW` that folds `lowerSExprW` over a `List (String × SExpr)`
(each statement lowers its RHS `SExpr`, then aliases the destination name to the
result slot), and — the keystone — a `.isSome` theorem proved BY INDUCTION over
the statement list (`lowerScalarSetSeqW_isSome`), composing per-statement
`lowerSExprW`-`isSome` facts. Each per-statement fact is `rfl`-checkable at the
size of ONE statement; the induction glues them WITHOUT ever normalising the
whole-kernel `Com`. This is the "induct over the BUILDER, not the output" pattern.

The jasmin side (`cryptoDialectToJasminCom` reaching owned x86 for the WHOLE
sequence) is proved by the same structural composition
(`comContJasminChain_isSome`): the sequencer's `ComCont` is a right-nested chain
of `varBind` nodes, and `cryptoDialectToJasminCom` succeeds node-by-node as long
as every emitted op is in `toJExprD`'s covered set — which the covered `SExpr`
alphabet guarantees.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. Aliasing a destination name to a result slot

After lowering a statement's RHS `SExpr`, the result is bound under a fresh
`__sx` temp name (`resName`). The statement `dst := e` additionally makes `dst`
name the SAME De-Bruijn slot — a VarMap-level alias, no new `Com` node. -/

/-- Rebind `dst` to whatever slot `src` currently names (an SSA-style alias). -/
def aliasBind {Γ : Ctx} (vm : VarMap Γ) (dst src : String) : VarMap Γ :=
  { lookup := fun n => if n = dst then vm.lookup src else vm.lookup n }

/-! ## 2. The statement sequencer

Fold `lowerSExprW` over the statement list. Each `(dst, e)`:
* lowers `e` via `ScalarSExprWidth32Prototype.lowerSExprW w vm cnt e` — extends the context / `VarMap` and
  binds the result under a fresh `resName`;
* aliases `dst` to `resName`;
* recurses on the tail with the extended `VarMap`, then `seqOut`-threads the
  head's `ComCont` prefix in front of the tail's.

Returns the accumulated `DTransOut` (extended context + fused `ComCont` prefix +
`VarMap`) and the next-free counter. `none` if any statement's RHS declines. -/
def lowerScalarSetSeqW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) :
    List (String × SExpr) → Option (DTransOut Γ × Nat)
  | [] => some (⟨Γ, ComCont.id, vm⟩, cnt)
  | (dst, e) :: rest =>
      match ScalarSExprWidth32Prototype.lowerSExprW w vm cnt e with
      | none => none
      | some (r, resName, cnt') =>
          let head : DTransOut Γ := { r with vm := aliasBind r.vm dst resName }
          match lowerScalarSetSeqW w head.vm cnt' rest with
          | none => none
          | some (tail, cntf) => some (seqOut head tail, cntf)

/-! ## 3. The per-statement coverability predicate

`SeqCovers w vm cnt stmts` witnesses that every statement's RHS lowers, THREADING
the growing `VarMap`. The `cons` constructor stores the head's lowering witness as
an EQUATION `lowerSExprW w vm cnt e = some (r, resName, cnt')` and the tail's
coverability at the `VarMap` reached AFTER the head (`aliasBind r.vm dst resName`).
In a concrete derivation the witnesses `r`/`resName`/`cnt'` are left implicit
(`_`) and solved by unification against the `rfl` head fact — so a whole-kernel
derivation is a chain of one-statement `rfl`s, each checked at the size of ONE
statement, never the whole `Com`. -/
inductive SeqCovers (w : Nat) :
    {Γ : Ctx} → VarMap Γ → Nat → List (String × SExpr) → Prop where
  | nil {Γ : Ctx} {vm : VarMap Γ} {cnt : Nat} : SeqCovers w vm cnt []
  | cons {Γ : Ctx} {vm : VarMap Γ} {cnt : Nat} {dst : String} {e : SExpr}
      {rest : List (String × SExpr)}
      (r : DTransOut Γ) (resName : String) (cnt' : Nat)
      (hhead : ScalarSExprWidth32Prototype.lowerSExprW w vm cnt e = some (r, resName, cnt'))
      (htail : SeqCovers w (aliasBind r.vm dst resName) cnt' rest) :
      SeqCovers w vm cnt ((dst, e) :: rest)

/-! ## 4. The keystone: `isSome` by induction over the statement list -/

/-- The whole sequence lowers to a `Com catCryptDialect` prefix, provided each
    statement's RHS is coverable at the `VarMap` it is reached with. Proved BY
    INDUCTION over the `SeqCovers` derivation — composing per-statement
    `lowerSExprW`-`isSome` facts, NEVER a monolithic `native_decide` over the
    whole-kernel `Com`. -/
theorem lowerScalarSetSeqW_isSome (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat)
    (stmts : List (String × SExpr)) (h : SeqCovers w vm cnt stmts) :
    (lowerScalarSetSeqW w vm cnt stmts).isSome := by
  induction h with
  | nil => rfl
  | @cons Γ vm cnt dst e rest r resName cnt' hhead htail ih =>
      -- Unfold one step of the fold. The head `lowerSExprW` is `some (r,…)` by
      -- `hhead`; the recursive call is `isSome` by the induction hypothesis `ih`.
      obtain ⟨⟨tail, cntf⟩, hp⟩ := Option.isSome_iff_exists.mp ih
      unfold lowerScalarSetSeqW
      rw [hhead]
      -- Reduce the head match (and the `.vm` projection of the fused `head`),
      -- exposing the recursive call, which `hp` says is `some (tail, cntf)`.
      dsimp only []
      rw [hp]
      rfl

/-! ## 5. Building the final program + its jasmin lowering

`seqProg` closes the sequencer's `ComCont` prefix with a `Com.ret` of the final
result slot, giving a whole `Com catCryptDialect Γ (.sword w)`. -/

/-- Close the sequencer prefix with `ret finalName`, giving the whole-kernel
    `Com catCryptDialect`. `none` if the sequencer declines or `finalName` is
    unbound / not a `.sword w` slot. -/
def seqProg (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (stmts : List (String × SExpr))
    (finalName : String) : Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerScalarSetSeqW w vm 0 stmts with
  | some (out, _) =>
      match out.vm.lookup finalName with
      | some ⟨.sword w', v⟩ =>
          if h : w' = w then out.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

/-! ## 6. The jasmin side by structural composition

`cryptoDialectToJasminCom` recurses over the `Com` structure: `.ret` always
lowers, `.var e body` lowers iff `toJExprD e` succeeds AND `body` lowers. So the
whole `Com` reaches the owned x86 backend iff every emitted expression is in
`toJExprD`'s covered set. `ComJLowerable` records exactly that per-node condition,
and `cryptoDialectToJasminCom_isSome` discharges the whole-`Com` jasmin lowering by
INDUCTION over the `Com` — never a monolithic `native_decide`. The sequencer emits
only the covered word-op alphabet (`bvConst`/`bvAdd`/…/`bvShiftL`/`bvShiftR`), so
its output satisfies `ComJLowerable` node-by-node. -/

/-- Every expression node in the `Com` is jasmin-lowerable (`toJExprD`-covered).
    The `Com`-structural companion of `SeqCovers`: it is the exact precondition
    for `cryptoDialectToJasminCom` to succeed on the whole program. -/
inductive ComJLowerable : {Γ : Ctx} → {t : CryptoTy} → Com catCryptDialect Γ t → Prop where
  | ret {Γ : Ctx} {t : CryptoTy} (v : Ctxt.Var Γ t) : ComJLowerable (Com.ret v)
  | var {Γ : Ctx} {t s : CryptoTy} (e : Expr catCryptDialect Γ t)
      (body : Com catCryptDialect (t :: Γ) s)
      (he : (DialectToJasminCom.toJExprD e).isSome = true) (hb : ComJLowerable body) :
      ComJLowerable (Com.var e body)

/-- The whole `Com` lowers to `Com jasminDialect` (reaches owned x86) provided
    every node is jasmin-lowerable. Proved BY INDUCTION over the `Com` structure —
    composing per-node `toJExprD`-`isSome` facts, NEVER a whole-kernel
    `native_decide`. -/
theorem cryptoDialectToJasminCom_isSome {Γ : Ctx} {t : CryptoTy}
    (com : Com catCryptDialect Γ t) (h : ComJLowerable com) :
    (DialectToJasminCom.cryptoDialectToJasminCom com).isSome := by
  induction h with
  | ret v => rfl
  | var e body he hb ih =>
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.mp he
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp ih
      unfold DialectToJasminCom.cryptoDialectToJasminCom
      rw [he', hb']
      rfl

/-! ## 7. Demonstration: a 3-statement cross-lane kernel, no `native_decide`

A mini ChaCha-quarter-round-style kernel over three `.sword 32` slots `a b d`:

  `s := a + b`  ;  `x := d ^ s`  ;  `r := rotl32(x, 16)`

(the last as the disjoint shift pair `(x << 16) ^ (x >> 16)`), each statement
referencing an earlier destination. The whole-sequence `isSome` closes through
the keystone `lowerScalarSetSeqW_isSome` fed a `SeqCovers` derivation whose head
facts are ONE-STATEMENT `rfl`s — NO `native_decide`, no whole-`Com` normalisation.
The jasmin landing goes through `cryptoDialectToJasminCom_isSome`. -/

/-- Three input slots `a b d`, all `.sword 32`. -/
def demoΓ : Ctx := [.sword 32, .sword 32, .sword 32]

/-- `VarMap` binding `a b d` (a = `.here`). -/
def demoVM : VarMap demoΓ := (((VarMap.empty.bind "d").bind "b").bind "a")

/-- The 3 statements: `s := a+b`, `x := d^s`, `r := rotl32(x,16)`. -/
def demoStmts : List (String × SExpr) :=
  [("s", .SAdd (.SVar "a") (.SVar "b")),
   ("x", .SXor (.SVar "d") (.SVar "s")),
   ("r", .SXor (.SShl (.SVar "x") (.SLit 16)) (.SShr (.SVar "x") (.SLit 16)))]

/-- Per-statement coverability — a chain of ONE-STATEMENT `rfl`s (each head fact
    `lowerSExprW 32 <vm-at-that-point> <cnt> <rhs> = some …`, the witnesses solved
    by unification). No `native_decide`. -/
theorem demo_covers : SeqCovers 32 demoVM 0 demoStmts :=
  .cons _ _ _ rfl (.cons _ _ _ rfl (.cons _ _ _ rfl .nil))

/-- The WHOLE 3-statement sequence lowers to a `Com catCryptDialect` — through the
    keystone, composing the per-statement `rfl` facts. NO `native_decide`. -/
theorem demo_isSome : (lowerScalarSetSeqW 32 demoVM 0 demoStmts).isSome :=
  lowerScalarSetSeqW_isSome 32 demoVM 0 demoStmts demo_covers

/-- The whole-kernel program (closing the sequencer prefix with `ret "r"`) lowers. -/
theorem demo_seqProg_isSome : (seqProg 32 demoVM demoStmts "r").isSome := by rfl

/-- …and reaches the owned x86 backend through `cryptoDialectToJasminCom`. -/
theorem demo_jasmin_isSome :
    ((seqProg 32 demoVM demoStmts "r").bind
      DialectToJasminCom.cryptoDialectToJasminCom).isSome := by rfl

/-! ## 8. The jasmin side AT SCALE — `ComJLowerable` built inductively

The demo discharged the jasmin landing by `rfl` (cheap at 3 statements, but a
whole-`Com` normalisation that grows with the kernel). This section closes the
jasmin side the same way the dialect side is closed in §4: by INDUCTION over the
`SeqCovers` derivation, threading `toJExprD`-coverage of each emitted op through
the `ComCont` composition — never a monolithic `rfl`/`native_decide` over the
whole-kernel `Com`.

`ContJLowerable f` says the prefix `f` sends every jasmin-lowerable body to a
jasmin-lowerable program. It is closed under the three `ComCont` combinators
(`id`, `varBind` of a covered op, `comp`), so it composes exactly as the
sequencer's `ComCont` is built (`pushVarBindW` = `comp _ (varBind _)`,
`seqOut` = `comp`). `lowerSExprW` emits only the covered word-op alphabet
(`bvConst`/`bvAdd`/…/`bvShiftLV`/`bvShiftRV`), so `lowerSExprW_contJLowerable`
holds by induction on the `SExpr`; the whole-sequence
`seqCovers_contJLowerable` then follows by induction on `SeqCovers`, and
`seqProg_jasmin_isSome` lands the closed program on owned x86 via
`cryptoDialectToJasminCom_isSome`. -/

/-- A `ComCont` sends every jasmin-lowerable body to a jasmin-lowerable program.
    The `ComCont`-level companion of `ComJLowerable`: the precondition for the
    prefix's output to reach the owned x86 backend. -/
def ContJLowerable {Γ Γ' : Ctx} (f : ComCont Γ Γ') : Prop :=
  ∀ {t : CryptoTy} (body : Com catCryptDialect Γ' t),
    ComJLowerable body → ∃ com', f body = some com' ∧ ComJLowerable com'

/-- The identity prefix preserves lowerability. -/
theorem ContJLowerable.id {Γ : Ctx} : ContJLowerable (ComCont.id (Γ := Γ)) := by
  intro t body hb; exact ⟨body, rfl, hb⟩

/-- A `varBind` of a `toJExprD`-covered op preserves lowerability. -/
theorem ContJLowerable.varBind {Γ : Ctx} {s : CryptoTy} (e : Expr catCryptDialect Γ s)
    (he : (DialectToJasminCom.toJExprD e).isSome = true) :
    ContJLowerable (ComCont.varBind e) := by
  intro t body hb
  exact ⟨Com.var e body, rfl, ComJLowerable.var e body he hb⟩

/-- Lowerability of prefixes composes (Kleisli threading of the `Option`). -/
theorem ContJLowerable.comp {Γ Γ' Γ'' : Ctx} {f : ComCont Γ Γ'} {g : ComCont Γ' Γ''}
    (hf : ContJLowerable f) (hg : ContJLowerable g) :
    ContJLowerable (ComCont.comp f g) := by
  intro t body hb
  obtain ⟨b', hb', hlb'⟩ := hg body hb
  obtain ⟨c', hc', hlc'⟩ := hf b' hlb'
  refine ⟨c', ?_, hlc'⟩
  show ComCont.comp f g body = some c'
  unfold ComCont.comp
  rw [hb']; exact hc'

/-- One `pushVarBindW` (of a covered op) preserves lowerability:
    `pushVarBindW` = `comp o.cont (varBind e)`. -/
theorem ContJLowerable.pushVarBindW (w : Nat) {Γ : Ctx} {o : DTransOut Γ}
    (ho : ContJLowerable o.cont) {e : Expr catCryptDialect o.Γ' (.sword w)} {nm : String}
    (he : (DialectToJasminCom.toJExprD e).isSome = true) :
    ContJLowerable (ScalarSExprWidth32Prototype.pushVarBindW w o e nm).cont := by
  unfold ScalarSExprWidth32Prototype.pushVarBindW
  exact ContJLowerable.comp ho (ContJLowerable.varBind e he)

/-- `seqOut` preserves lowerability: `seqOut` = `comp oa.cont ob.cont`. -/
theorem ContJLowerable.seqOut {Γ : Ctx} {oa : DTransOut Γ} {ob : DTransOut oa.Γ'}
    (ha : ContJLowerable oa.cont) (hb : ContJLowerable ob.cont) :
    ContJLowerable (seqOut oa ob).cont :=
  ContJLowerable.comp ha hb

set_option maxHeartbeats 1000000 in
/-- Every prefix `lowerSExprW` emits is jasmin-lowerable — its expression nodes
    are exactly the `toJExprD`-covered word-op alphabet. Proved BY INDUCTION over
    the `SExpr`, composing the per-op coverage facts through the `ComCont`
    combinators, NEVER a whole-`Com` `native_decide`. -/
theorem lowerSExprW_contJLowerable (w : Nat) (e : SExpr) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat) (r : DTransOut Γ) (resName : String) (cnt' : Nat),
      ScalarSExprWidth32Prototype.lowerSExprW w vm cnt e = some (r, resName, cnt') →
      ContJLowerable r.cont := by
  induction e with
  | SVar x =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, -, -⟩ := h; subst hr
        exact ContJLowerable.id
      · simp at h
  | SLit n =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, -, -⟩ := h; subst hr
      exact ContJLowerable.pushVarBindW w ContJLowerable.id rfl
  | SAdd a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) rfl
          · simp at h
  | SSub a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) rfl
          · simp at h
  | SMul a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) rfl
          · simp at h
  | SAnd a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) rfl
          · simp at h
  | SXor a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) rfl
          · simp at h
  | SShl a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) (by split <;> rfl)
          · simp at h
  | SShr a b iha ihb =>
      intro Γ vm cnt r resName cnt' h
      simp only [ScalarSExprWidth32Prototype.lowerSExprW] at h
      split at h
      · simp at h
      · next Ro hla =>
        split at h
        · simp at h
        · next So hlb =>
          split at h
          · next va vb =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hr, -, -⟩ := h; subst hr
            exact ContJLowerable.pushVarBindW w
              (ContJLowerable.seqOut (iha vm cnt Ro.1 Ro.2.1 Ro.2.2 hla)
                (ihb Ro.1.vm Ro.2.2 So.1 So.2.1 So.2.2 hlb)) (by split <;> rfl)
          · simp at h
  | SLt a b _ _ | SAsr a b _ _ | SMulS a b _ _ | SMulHiU a b _ _
  | SMulHiS a b _ _ =>
      intro Γ vm cnt r resName cnt' h
      simp [ScalarSExprWidth32Prototype.lowerSExprW] at h
  | SLimb v i =>
      intro Γ vm cnt r resName cnt' h
      simp [ScalarSExprWidth32Prototype.lowerSExprW] at h

/-- The WHOLE statement sequence's `ComCont` prefix is jasmin-lowerable, provided
    each statement's RHS is coverable. Proved BY INDUCTION over the `SeqCovers`
    derivation — the `Com`-structural twin of `lowerScalarSetSeqW_isSome`. -/
theorem seqCovers_contJLowerable (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (cnt : Nat)
    (stmts : List (String × SExpr)) (h : SeqCovers w vm cnt stmts) :
    ∀ (out : DTransOut Γ) (cntf : Nat),
      lowerScalarSetSeqW w vm cnt stmts = some (out, cntf) → ContJLowerable out.cont := by
  induction h with
  | nil =>
      intro out cntf hp
      simp only [lowerScalarSetSeqW, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨ho, -⟩ := hp; subst ho
      exact ContJLowerable.id
  | @cons Γ vm cnt dst e rest r resName cnt' hhead htail ih =>
      intro out cntf hp
      obtain ⟨⟨tail, cntf'⟩, htp⟩ := Option.isSome_iff_exists.mp
        (lowerScalarSetSeqW_isSome w (aliasBind r.vm dst resName) cnt' rest htail)
      unfold lowerScalarSetSeqW at hp
      rw [hhead] at hp
      dsimp only [] at hp
      rw [htp] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨ho, -⟩ := hp; subst ho
      exact ContJLowerable.seqOut
        (lowerSExprW_contJLowerable w e vm cnt r resName cnt' hhead)
        (ih tail cntf' htp)

/-- The whole-kernel program `seqProg` (when it resolves its final slot) is
    jasmin-lowerable: every `Com` node is `toJExprD`-covered. -/
theorem seqProg_comJLowerable (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (finalName : String) (h : SeqCovers w vm 0 stmts)
    {com : Com catCryptDialect Γ (.sword w)}
    (hsp : seqProg w vm stmts finalName = some com) : ComJLowerable com := by
  obtain ⟨⟨out, cntf⟩, hlo⟩ := Option.isSome_iff_exists.mp
    (lowerScalarSetSeqW_isSome w vm 0 stmts h)
  have hcont : ContJLowerable out.cont := seqCovers_contJLowerable w vm 0 stmts h out cntf hlo
  unfold seqProg at hsp
  rw [hlo] at hsp
  dsimp only [] at hsp
  split at hsp
  · next w' v heq =>
    split at hsp
    · next hw =>
      obtain ⟨com', hcom', hlc'⟩ := hcont (Com.ret (toVIRVar (hw ▸ v))) (ComJLowerable.ret _)
      have hcc : com' = com := Option.some.inj (hcom'.symm.trans hsp)
      exact hcc ▸ hlc'
    · simp at hsp
  · simp at hsp

/-- **The keystone jasmin landing at scale.** Whenever the whole `RScalarSetExpr`
    sequence is coverable (`SeqCovers`) and its program resolves (`seqProg` is
    `some`), the program reaches the owned x86 backend through
    `cryptoDialectToJasminCom`. Footprint `[propext, Quot.sound]` — the jasmin
    side is closed by the `SeqCovers`/`Com` inductions of §4/§8, NOT by a
    whole-kernel `rfl`/`native_decide` (which is what the §7 demo used, cheap at
    3 statements but growing with the kernel). -/
theorem seqProg_jasmin_isSome (w : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (stmts : List (String × SExpr)) (finalName : String) (h : SeqCovers w vm 0 stmts)
    (hsp : (seqProg w vm stmts finalName).isSome) :
    ((seqProg w vm stmts finalName).bind
      DialectToJasminCom.cryptoDialectToJasminCom).isSome := by
  obtain ⟨com, hcom⟩ := Option.isSome_iff_exists.mp hsp
  rw [hcom]
  show (DialectToJasminCom.cryptoDialectToJasminCom com).isSome
  exact cryptoDialectToJasminCom_isSome com (seqProg_comJLowerable w vm stmts finalName h hcom)

end CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSetSeqSequencer
