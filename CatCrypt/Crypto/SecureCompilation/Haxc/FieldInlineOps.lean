/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCall
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps

/-!
# The operations of the field-inlined program

The inlining step `fieldInlineStep` replaces each `call` of a tagged field head by the body
`fieldBody` of the head. Every operation of the inlined program is in the op set `opMemB` of
the stack-memory fragment and has a result of positive width (`bindPosB`) when every
operation of the input is.

Inlining keeps an operation predicate that holds of every body of the library
(`allOps_inline?`): a splice of a body before a continuation has the operations of both, and
a renaming keeps the operations of a program. Every body of a tagged head binds operations of
`opMemB` of positive width only:

* the narrow template (`SingleWordField.ofCanonical` with `narrowMulBlk`) binds register
  constants at width `64` and register arithmetic;
* the limb generators of the Montgomery blocks (`Curve25519.adcR` to `Mont.mulMK` and
  `Mont.ciosMK`) bind register constants at the widths `64` and `1`, register arithmetic,
  `mulhi`, the carries and `select`, and pass the property from their continuation to their
  result;
* the lowered field program over word arrays (`fieldComOf`) adds loads and stores at
  constant indices, and the register block `canonRegBlock` adds nothing.

None of these blocks reads the modulus into a width or a shift amount, so the property holds
at every modulus.

## Main definitions

None.

## Main results

* `allOps_rename?`, `allOps_seq?`, `allOps_inline?` — renaming, splicing and
  inlining keep an operation predicate that holds of every body of the library.
* `allOps_ofCom` — the embedding of a straight-line program keeps the operations.
* `narrowMulBlk_mem`, `fieldBlockOf_allOps` — the narrow template blocks bind operations of
  `opMemB` of positive width only.
* `lowerOpL_mem` — the Montgomery limb block of an operation of `arithOpB P.p` binds
  operations of `opMemB` of positive width only.
* `fieldBodyOf_mem`, `wideBlockOf_allOps`, `montWordBlockOf_allOps`, `wideBody_allOps` — the
  wide and one-limb bodies bind operations of `opMemB` of positive width only.
* `fieldBody_allOps` — every body of a tagged head binds operations of `opMemB` of positive
  width only.
* `fieldInline_allOps_opMemB` — the inlining step keeps
  `allOps (fun op => opMemB op && bindPosB op)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom coveredCom_rename
  coveredCom_spliceCom)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (CoveredM)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (op_rename?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (bindPosB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC bindK adcR rowR selR xorR constsK addK mulRowK accK)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open Ctxt (Var Valuation)

/-- The Jasmin operations of `opMemB` whose result has positive width. -/
local notation "opMemPos" => fun op => opMemB op && bindPosB op

/-- The Jasmin expressions whose operation is of `opMemB` and has a result of positive
    width. -/
local notation "exprMemPos" => fun e => (opMemB (Expr.op e) && bindPosB (Expr.op e)) = true

/-! ## 1. Renaming, splicing and inlining keep the operations -/

section Inline

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- **A renamed program has the operations of the source.** -/
theorem allOps_rename? (Q : d.Op → Bool) {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {Δ : Ctxt d} (f : PRen Γ Δ) {p' : NFProg d Δ ts},
      NFProg.rename? f p = some p' → p'.allOps Q = p.allOps Q := by
  induction p with
  | ret vs =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
  | var e k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, k', hk, rfl⟩ := h
      simp only [NFProg.allOps, op_rename? he, ih _ hk]
  | forLoop count inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, b', hb, k', hk, rfl⟩ := h
      simp only [NFProg.allOps, ihb _ hb, ihk _ hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, k', hk, rfl⟩ := h
      simp only [NFProg.allOps, iht _ ht, ihe _ he, ihk _ hk]
  | whileLoop inits body k ihb ihk =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, b', hb, k', hk, rfl⟩ := h
      simp only [NFProg.allOps, ihb _ hb, ihk _ hk]
  | call fn args k ih =>
      intro Δ f p' h
      simp only [NFProg.rename?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, k', hk, rfl⟩ := h
      simp only [NFProg.allOps, ih _ hk]

/-- **A splice has the operations of the body and of the continuation.** -/
theorem allOps_seq? (Q : d.Op → Bool) {Δ : Ctxt d} {rs : List d.Ty} (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      (ρ : PRen Δ Γ) (θ : PRen Γ₀ Γ) {q : NFProg d Γ ts},
      NFProg.seq? k b ρ θ = some q → b.allOps Q = true → k.allOps Q = true →
        q.allOps Q = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      rw [allOps_rename? Q k _ h]
      exact hk
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, q', hq', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hb ⊢
      exact ⟨(op_rename? he).symm ▸ hb.1, ih k _ _ hq' hb.2 hk⟩
  | forLoop count inits body b _ ihk =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, body', hbody, b', hb', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hb ⊢
      exact ⟨(allOps_rename? Q body _ hbody).trans hb.1, ihk k _ _ hb' hb.2 hk⟩
  | ifThenElse cond thn els b _ _ ihk =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hb ⊢
      exact ⟨⟨(allOps_rename? Q thn _ ht).trans hb.1.1, (allOps_rename? Q els _ he).trans hb.1.2⟩,
        ihk k _ _ hb' hb.2 hk⟩
  | whileLoop inits body b _ ihk =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, body', hbody, b', hb', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hb ⊢
      exact ⟨(allOps_rename? Q body _ hbody).trans hb.1, ihk k _ _ hb' hb.2 hk⟩
  | call fn args b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, b', hb', rfl⟩ := h
      simp only [NFProg.allOps] at hb ⊢
      exact ih k _ _ hb' hb hk

/-- **Inlining keeps an operation predicate** that holds of every body of the library. -/
theorem allOps_inline? (L : InlineLib d) (Q : d.Op → Bool)
    (hop : ∀ o b, L.op o = some b → b.allOps Q = true)
    (hcall : ∀ f as rs b, L.call f as rs = some b → b.allOps Q = true)
    {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts) :
    ∀ {q : NFProg d Γ ts}, NFProg.inline? L p = some q → p.allOps Q = true →
      q.allOps Q = true := by
  induction p with
  | ret vs =>
      intro q h _
      cases h
      rfl
  | var e k ih =>
      intro q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff] at h
      obtain ⟨k', hk', h⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp
      have hk := ih hk' hp.2
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inlineVar] at h
      split at h
      · rename_i b hb
        exact allOps_seq? Q b k' _ _ h (hop o b hb) hk
      · cases h
        simp only [NFProg.allOps, Bool.and_eq_true]
        exact ⟨hp.1, hk⟩
  | forLoop count inits body k ihb ihk =>
      intro q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hb' hp.1, ihk hk' hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht ht' hp.1.1, ihe he' hp.1.2⟩, ihk hk' hp.2⟩
  | whileLoop inits body k ihb ihk =>
      intro q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [NFProg.allOps, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hb' hp.1, ihk hk' hp.2⟩
  | call f args k ih =>
      intro q h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff] at h
      obtain ⟨k', hk', h⟩ := h
      simp only [NFProg.allOps] at hp
      have hk := ih hk' hp
      split at h
      · rename_i b hb
        exact allOps_seq? Q b k' _ _ h (hcall _ _ _ b hb) hk
      · cases h
        exact hk

/-- The embedding of a straight-line program has the operations of the program. -/
theorem allOps_ofCom (Q : d.Op → Bool) {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t)
    (hc : CoveredCom (fun e => Q e.op = true) c) : (NFProg.ofCom c).allOps Q = true := by
  induction c with
  | ret v => rfl
  | var e k ih =>
      simp only [NFProg.ofCom, NFProg.allOps, Bool.and_eq_true]
      exact ⟨hc.1, ih hc.2⟩

end Inline

/-! ## 2. Splicing and the narrow template blocks -/

section Narrow

variable {Γ : Ctxt jasminDialect}

theorem litBlk_mem (n : Nat) :
    CoveredCom exprMemPos (FieldWord.litBlk (Γ := Γ) n) := ⟨rfl, trivial⟩

theorem binBlk_mem (op : JasminBinOp) (a b : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.binBlk op a b) := ⟨rfl, trivial⟩

theorem binLitBlk_mem (op : JasminBinOp) (a : Var Γ w64) (n : Nat) :
    CoveredCom exprMemPos (FieldWord.binLitBlk op a n) :=
  ⟨rfl, rfl, trivial⟩

theorem csubBlk_mem (P : Nat) (x : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.csubBlk P x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem addBlk_mem (P : Nat) (a b : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.addBlk P a b) := by
  unfold FieldWord.addBlk
  exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binBlk_mem _ _ _) (csubBlk_mem _ _)

theorem subBlk_mem (P : Nat) (a b : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.subBlk P a b) := by
  unfold FieldWord.subBlk
  exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (litBlk_mem _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binBlk_mem _ _ _) (csubBlk_mem _ _)

theorem negBlk_mem (P : Nat) (a : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.negBlk P a) := by
  unfold FieldWord.negBlk
  exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (litBlk_mem _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binBlk_mem _ _ _) (csubBlk_mem _ _)

theorem foldBlk_mem (c : Nat) (x : Var Γ w64) :
    CoveredCom exprMemPos (FieldWord.foldBlk c x) := by
  unfold FieldWord.foldBlk
  exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binLitBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binLitBlk_mem _ _ _) (binBlk_mem _ _ _)

theorem foldsBlk_mem (c : Nat) :
    ∀ (n : Nat) {Γ : Ctxt jasminDialect} (x : Var Γ w64),
      CoveredCom exprMemPos (FieldWord.foldsBlk c n x)
  | 0, _, _ => trivial
  | n + 1, _, x => by
      rw [FieldWord.foldsBlk]
      exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (foldBlk_mem c x)
        (foldsBlk_mem c n _)

/-- **The fold multiply of the narrow template binds operations of `opMemB` of positive width
    only.** -/
theorem narrowMulBlk_mem (p n : Nat) (a b : Var Γ w64) :
    CoveredCom exprMemPos (FieldRouteNarrow.narrowMulBlk p n a b) := by
  unfold FieldRouteNarrow.narrowMulBlk FieldWord.foldMulBlk FieldWord.foldReduceBlk
  exact coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (binBlk_mem _ _ _) <|
    coveredCom_spliceCom (d := jasminDialect) opMemPos _ _ (foldsBlk_mem _ _ _) (csubBlk_mem _ _)

/-- **The narrow template blocks bind operations of `opMemB` of positive width only**, at
    every modulus and fold count the certificate accepts. -/
theorem fieldBlockOf_allOps {p n : Nat} (h : FieldRouteNarrow.narrowCert p n = true)
    (m : _root_.Hax.FieldTag.FieldMethod) :
    (fieldBlockOf (FieldRouteNarrow.narrowField p n h) m).allOps opMemPos = true := by
  cases m
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (addBlk_mem _ _ _)
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (subBlk_mem _ _ _)
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (narrowMulBlk_mem _ _ _ _)
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (negBlk_mem _ _)
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (narrowMulBlk_mem _ _ _ _)
  · exact allOps_ofCom (d := jasminDialect) opMemPos _ (addBlk_mem _ _ _)

end Narrow

/-! ## 3. The limb generators of the Montgomery blocks -/

section Gen

/-- A binding of an expression of `opMemB` of positive width keeps the operations of every
    continuation. -/
theorem bindK_mem {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (he : (opMemB e.op && bindPosB e.op) = true)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ t → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (x : Var Δ t),
      CoveredM exprMemPos (k r x)) :
    CoveredM exprMemPos (bindK e k) :=
  ⟨he, hk _ _⟩

theorem adcR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs ys : List (Var Γ w64)) (c : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out c',
      CoveredM exprMemPos (k r out c')) →
      CoveredM exprMemPos (adcR ren xs ys c k)
  | _, _, _, _, _ :: xs, _ :: ys, _, _, hk => by
      rw [adcR]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        adcR_mem _ xs ys _ fun _ _ _ => hk _ _ _
  | _, _, _, _, [], _, _, _, hk => by rw [adcR]; exact hk _ _ _
  | _, _, _, _, _ :: _, [], _, _, hk => by rw [adcR]; exact hk _ _ _

theorem rowR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs : List (Var Γ w64)) (w z h : Var Δ w64) (c : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (rowR ren xs w z h c k)
  | _, _, _, _, [], _, _, _, _, _, hk => by
      rw [rowR]
      exact bindK_mem _ rfl fun _ _ => hk _ _
  | _, _, _, _, _ :: xs, _, _, _, _, _, hk => by
      rw [rowR]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        rowR_mem _ xs _ _ _ _ fun _ _ => hk _ _

theorem selR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (c : Var Δ w1) (xs ys : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (selR ren c xs ys k)
  | _, _, _, _, _, _ :: xs, _ :: ys, _, hk => by
      rw [selR]
      exact bindK_mem _ rfl fun _ _ => selR_mem _ _ xs ys fun _ _ => hk _ _
  | _, _, _, _, _, [], _, _, hk => by rw [selR]; exact hk _ _
  | _, _, _, _, _, _ :: _, [], _, hk => by rw [selR]; exact hk _ _

theorem xorR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (m : Var Δ w64) (xs : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (xorR ren m xs k)
  | _, _, _, _, _, _ :: xs, _, hk => by
      rw [xorR]
      exact bindK_mem _ rfl fun _ _ => xorR_mem _ _ xs fun _ _ => hk _ _
  | _, _, _, _, _, [], _, hk => by rw [xorR]; exact hk _ _

theorem constsK_mem : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ns : List Nat)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts},
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (constsK ns k)
  | _, _, [], _, hk => by rw [constsK]; exact hk _ _
  | _, _, _ :: ns, _, hk => by
      rw [constsK]
      exact bindK_mem _ rfl fun _ _ => constsK_mem ns fun _ _ => hk _ _

theorem addK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → Var Δ w1 → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out c,
      CoveredM exprMemPos (k r out c)) :
    CoveredM exprMemPos (addK xs ys k) := by
  rw [addK]
  exact bindK_mem _ rfl fun _ _ => adcR_mem _ _ _ _ fun _ _ _ => hk _ _ _

theorem mulRowK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (w : Var Γ w64) {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (mulRowK xs w k) := by
  rw [mulRowK]
  exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
    rowR_mem _ _ _ _ _ _ fun _ _ => hk _ _

theorem accK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (i : Nat)
    (xs : List (Var Γ w64)) (y : Var Γ w64) (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (accK i xs y acc k) := by
  rw [accK]
  exact mulRowK_mem _ _ fun _ _ => bindK_mem _ rfl fun _ _ =>
    addK_mem _ _ fun _ _ _ => hk _ _

variable {n : Nat} (P : LimbParams n)

theorem csubPCK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.csubPCK P xs k) := by
  rw [Mont.csubPCK]
  exact constsK_mem _ fun _ _ => addK_mem _ _ fun _ _ _ => selR_mem _ _ _ _ fun _ _ => hk _ _

theorem addMK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.addMK P xs ys k) := by
  rw [Mont.addMK]
  exact bindK_mem _ rfl fun _ _ => addK_mem _ _ fun _ _ _ =>
    csubPCK_mem P _ fun _ _ => hk _ _

theorem subMK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.subMK P xs ys k) := by
  rw [Mont.subMK]
  exact bindK_mem _ rfl fun _ _ => xorR_mem _ _ _ fun _ _ => bindK_mem _ rfl fun _ _ =>
    adcR_mem _ _ _ _ fun _ _ _ => constsK_mem _ fun _ _ => addK_mem _ _ fun _ _ _ =>
    selR_mem _ _ _ _ fun _ _ => hk _ _

theorem prodAccK_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy}
    (ren : Ctxt.Hom Γ Δ) (i : Nat) (xs : List (Var Δ w64)) (ys : List (Var Γ w64))
    (acc : List (Var Δ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (Mont.prodAccK ren i xs ys acc k)
  | _, _, _, _, _, _, [], _, _, hk => by rw [Mont.prodAccK]; exact hk _ _
  | _, _, _, _, _, _, _ :: ys, _, _, hk => by
      rw [Mont.prodAccK]
      exact accK_mem _ _ _ _ fun _ _ => prodAccK_mem _ _ _ ys _ fun _ _ => hk _ _

theorem prodNK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.prodNK xs ys k) := by
  cases ys with
  | nil => rw [Mont.prodNK]; exact hk _ _
  | cons y ys =>
      rw [Mont.prodNK]
      exact mulRowK_mem _ _ fun _ _ => prodAccK_mem _ _ _ _ _ fun _ _ => hk _ _

theorem redcStepK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.redcStepK P acc k) := by
  rw [Mont.redcStepK]
  exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
    constsK_mem _ fun _ _ => mulRowK_mem _ _ fun _ _ => addK_mem _ _ fun _ _ _ => hk _ _

theorem redcChainK_mem : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (s : Nat)
    (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts},
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (Mont.redcChainK P s acc k)
  | _, _, 0, _, _, hk => by rw [Mont.redcChainK]; exact hk _ _
  | _, _, s + 1, _, _, hk => by
      rw [Mont.redcChainK]
      exact redcStepK_mem P _ fun _ _ => redcChainK_mem s _ fun _ _ => hk _ _

theorem mulMK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.mulMK P xs ys k) := by
  rw [Mont.mulMK]
  exact prodNK_mem _ _ fun _ _ => bindK_mem _ rfl fun _ _ =>
    redcChainK_mem P _ _ fun _ _ => csubPCK_mem P _ fun _ _ => hk _ _

theorem opK_mem {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (y : Var Γ w64 ⊕ Nat)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' w64 → MC Δ' ts}
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') v,
      CoveredM exprMemPos (k r v)) :
    CoveredM exprMemPos (Mont.opK ren y k) := by
  cases y with
  | inl v => exact hk _ _
  | inr d => exact bindK_mem _ rfl fun _ _ => hk _ _

theorem fmaR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (ys : List (Var Γ w64 ⊕ Nat)) (acc : List (Var Γ w64)) (x z h : Var Δ w64)
    (cA cB : Var Δ w1)
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → Var Δ' w1 →
      Var Δ' w1 → Var Δ' w64 → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out cA' cB' h',
      CoveredM exprMemPos (k r out cA' cB' h')) →
      CoveredM exprMemPos (Mont.fmaR ren ys acc x z h cA cB k)
  | _, _, _, _, _ :: ys, _ :: acc, _, _, _, _, _, _, hk => by
      rw [Mont.fmaR]
      exact opK_mem _ _ fun _ _ => bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        bindK_mem _ rfl fun _ _ => fmaR_mem _ ys acc _ _ _ _ _ fun _ _ _ _ _ => hk _ _ _ _ _
  | _, _, _, _, [], _ :: acc, _, _, _, _, _, _, hk => by
      rw [Mont.fmaR]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        fmaR_mem _ [] acc _ _ _ _ _ fun _ _ _ _ _ => hk _ _ _ _ _
  | _, _, _, _, [], [], _, _, _, _, _, _, hk => by rw [Mont.fmaR]; exact hk _ _ _ _ _
  | _, _, _, _, _ :: _, [], _, _, _, _, _, _, hk => by rw [Mont.fmaR]; exact hk _ _ _ _ _

theorem ciosAddK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (ys : List (Var Γ w64))
    (x z : Var Γ w64) (acc : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.ciosAddK ys x z acc k) := by
  rw [Mont.ciosAddK]
  exact bindK_mem _ rfl fun _ _ => fmaR_mem _ _ _ _ _ _ _ _ fun _ _ _ _ _ => hk _ _

theorem ciosRedK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (S : List (Var Γ w64))
    (ni z : Var Γ w64)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.ciosRedK P S ni z k) := by
  rw [Mont.ciosRedK]
  exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
    fmaR_mem _ _ _ _ _ _ _ _ fun _ _ _ _ _ => hk _ _

theorem ciosRowsK_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy}
    (ren : Ctxt.Hom Γ Δ) (ys : List (Var Δ w64)) (ni z : Var Δ w64) (xs : List (Var Γ w64))
    (acc : List (Var Δ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (Mont.ciosRowsK P ren ys ni z xs acc k)
  | _, _, _, _, _, _, _, [], _, _, hk => by rw [Mont.ciosRowsK]; exact hk _ _
  | _, _, _, _, _, _, _, _ :: xs, _, _, hk => by
      rw [Mont.ciosRowsK]
      exact ciosAddK_mem _ _ _ _ fun _ _ => ciosRedK_mem P _ _ _ fun _ _ =>
        ciosRowsK_mem _ _ _ _ xs _ fun _ _ => hk _ _

theorem ciosMK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (k r out)) :
    CoveredM exprMemPos (Mont.ciosMK P xs ys k) := by
  cases xs with
  | nil => rw [Mont.ciosMK]; exact hk _ _
  | cons x xs =>
      rw [Mont.ciosMK]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        mulRowK_mem _ _ fun _ _ => ciosRedK_mem P _ _ _ fun _ _ =>
        ciosRowsK_mem P _ _ _ _ _ _ fun _ _ => csubPCK_mem P _ fun _ _ => hk _ _

theorem shrR_mem : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (sa sb : Var Δ w64) (xs : List (Var Γ w64))
    {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts},
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') out,
      CoveredM exprMemPos (k r out)) →
      CoveredM exprMemPos (Solinas.shrR ren sa sb xs k)
  | _, _, _, _, _, _, [], _, hk => by rw [Solinas.shrR]; exact hk _ _
  | _, _, _, _, _, _, [_], _, hk => by
      rw [Solinas.shrR]
      exact bindK_mem _ rfl fun _ _ => hk _ _
  | _, _, _, _, _, _, _ :: y :: ys, _, hk => by
      rw [Solinas.shrR]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        bindK_mem _ rfl fun _ _ => shrR_mem _ _ _ (y :: ys) fun _ _ => hk _ _

theorem splitK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k : Nat)
    (xs : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → List (Var Δ w64) →
      MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) hi lo,
      CoveredM exprMemPos (K r hi lo)) :
    CoveredM exprMemPos (Solinas.splitK k xs K) := by
  rw [Solinas.splitK]
  split
  · exact hK _ _ _
  · exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
      bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
      shrR_mem _ _ _ _ fun _ _ => hK _ _ _

theorem foldK_mem {Γ : Ctxt jasminDialect} {ts : List JasminTy} (k c m : Nat)
    (xs : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (K r out)) :
    CoveredM exprMemPos (Solinas.foldK k c m xs K) := by
  rw [Solinas.foldK]
  exact splitK_mem _ _ fun _ _ _ => bindK_mem _ rfl fun _ _ =>
    mulRowK_mem _ _ fun _ _ => bindK_mem _ rfl fun _ _ =>
    addK_mem _ _ fun _ _ _ => hK _ _

theorem mulSK_mem (S : Solinas.SolinasParams n) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (xs ys : List (Var Γ w64))
    {K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts}
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) out,
      CoveredM exprMemPos (K r out)) :
    CoveredM exprMemPos (Solinas.mulSK S xs ys K) := by
  rw [Solinas.mulSK]
  exact prodNK_mem _ _ fun _ _ => foldK_mem _ _ _ _ fun _ _ =>
    foldK_mem _ _ _ _ fun _ _ => csubPCK_mem (Solinas.lp S) _ fun _ _ => hK _ _

end Gen

/-! ## 4. The Montgomery limb blocks -/

section Blocks

variable {n : Nat} (P : LimbParams n) {Γ : Ctxt jasminDialect}

theorem retN_mem (k : Nat) (xs : List (Var Γ w64)) :
    CoveredM exprMemPos (Mont.retN k xs) := by
  cases xs with
  | nil => exact ⟨rfl, trivial⟩
  | cons a as => trivial

theorem montConstBlk_mem (k v : Nat) :
    CoveredM exprMemPos (Mont.constBlk (Γ := Γ) k v) := by
  rw [Mont.constBlk]
  exact constsK_mem _ fun _ _ => retN_mem _ _

theorem montAddBlk_mem (xs ys : List (Var Γ w64)) :
    CoveredM exprMemPos (Mont.addBlk P xs ys) := by
  rw [Mont.addBlk]
  exact addMK_mem P _ _ fun _ _ => retN_mem _ _

theorem montSubBlk_mem (xs ys : List (Var Γ w64)) :
    CoveredM exprMemPos (Mont.subBlk P xs ys) := by
  rw [Mont.subBlk]
  exact subMK_mem P _ _ fun _ _ => retN_mem _ _

theorem montNegBlk_mem (xs : List (Var Γ w64)) :
    CoveredM exprMemPos (Mont.negBlk P xs) := by
  rw [Mont.negBlk]
  exact constsK_mem _ fun _ _ => montSubBlk_mem P _ _

theorem mulBlkRoute_mem (xs ys : List (Var Γ w64)) :
    CoveredM exprMemPos (Mont.mulBlkRoute P xs ys) := by
  rw [Mont.mulBlkRoute]
  split
  · rw [Mont.mulBlkI]
    exact ciosMK_mem P _ _ fun _ _ => retN_mem _ _
  · rw [Mont.mulBlk]
    exact mulMK_mem P _ _ fun _ _ => retN_mem _ _

/-- **The Montgomery limb block of an operation of `arithOpB P.p` binds operations of
    `opMemB` of positive width only.** -/
theorem lowerOpL_mem (op : FieldDialect.FieldOp) (hop : FieldLower.arithOpB P.p op = true) :
    CoveredM exprMemPos (FieldToJasminLimbs.lowerOpL P op) := by
  cases op <;> simp only [FieldLower.arithOpB, beq_iff_eq, Bool.false_eq_true] at hop <;>
    subst hop <;> rw [FieldToJasminLimbs.lowerOpL] <;> simp only [ite_true, dite_eq_left]
  · exact montAddBlk_mem P _ _
  · exact montSubBlk_mem P _ _
  · exact montNegBlk_mem P _
  · exact mulBlkRoute_mem P _ _
  · exact montConstBlk_mem _ _

/-- **The Solinas limb block of an operation of `arithOpB (Solinas.p S)` binds operations of
    `opMemB` of positive width only.** -/
theorem solinasLowerOpL_mem (S : Solinas.SolinasParams n) (op : FieldDialect.FieldOp)
    (hop : FieldLower.arithOpB (Solinas.p S) op = true) :
    CoveredM exprMemPos (FieldToJasminLimbsSolinas.lowerOpL S op) := by
  cases op <;> simp only [FieldLower.arithOpB, beq_iff_eq, Bool.false_eq_true] at hop <;>
    subst hop <;> rw [FieldToJasminLimbsSolinas.lowerOpL] <;> simp only [ite_true, dite_eq_left]
  · rw [Solinas.addBlk]
    exact addMK_mem (Solinas.lp S) _ _ fun _ _ => retN_mem _ _
  · exact montSubBlk_mem (Solinas.lp S) _ _
  · exact montNegBlk_mem (Solinas.lp S) _
  · rw [Solinas.mulBlk]
    exact mulSK_mem S _ _ fun _ _ => retN_mem _ _
  · exact montConstBlk_mem _ _

end Blocks

/-! ## 5. Renaming, splicing, the lowering, the loads and the stores -/

section Lower

open MultiBlockLowering (spliceMultiK MultiBlockLoweringData)

/-- A renamed multi-result program has the operations of the source. -/
theorem rename_mem {Γ Γ' : Ctxt jasminDialect} {ts : List JasminTy}
    (h : Ctxt.Hom Γ Γ') (m : MC Γ ts) (hm : CoveredM exprMemPos m) :
    CoveredM exprMemPos (MultiReturnCom.rename h m) := by
  induction m generalizing Γ' with
  | ret => trivial
  | var e body ih =>
      obtain ⟨op, rfl, args⟩ := e
      exact ⟨hm.1, ih h.lift hm.2⟩

/-- The splice of a block of `opMemB` of positive width keeps the operations of every
    continuation. -/
theorem spliceMultiK_mem : ∀ {Γ : Ctxt jasminDialect} {ts bs : List JasminTy} (blk : MC Γ ts)
    {k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts → MC Δ bs},
    CoveredM exprMemPos blk →
    (∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ) res,
      CoveredM exprMemPos (k ren res)) →
      CoveredM exprMemPos (spliceMultiK blk k)
  | _, _, _, .ret _, _, _, hk => hk _ _
  | _, _, _, .var _ blk, _, hb, hk => ⟨hb.1, spliceMultiK_mem blk hb.2 fun _ _ => hk _ _⟩

/-- **The lowering of a covered program keeps the operations of every continuation**, when
    the block of every covered expression binds operations of `opMemB` of positive width only. -/
theorem lowerR_mem {d : Dialect} [DialectSignature d]
    (L : MultiBlockLoweringData d jasminDialect)
    {Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop}
    (hB : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      CoveredM exprMemPos (L.exprBlock e)) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt jasminDialect} {bs : List JasminTy}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (c : Com d Γ t)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        HVector (fun u => Var Δ' u) (L.mapTys t) → MC Δ' bs},
      CoveredCom Good c →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') vs,
        CoveredM exprMemPos (k r vs)) →
      CoveredM exprMemPos (L.lowerR ren c k)
  | _, _, _, _, _, .ret _, _, _, hk => by rw [MultiBlockLoweringData.lowerR]; exact hk _ _
  | _, _, _, _, ren, .var e body, _, hc, hk => by
      rw [MultiBlockLoweringData.lowerR, MultiBlockLoweringData.lowerBind]
      exact spliceMultiK_mem _ (rename_mem _ _ (hB e hc.1)) fun _ _ =>
        lowerR_mem L hB _ body hc.2 fun _ _ => hk _ _

/-- The single-result projection of a multi-result program has its operations. -/
theorem toComHead_mem {d : Dialect} [DialectSignature d]
    {Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop} :
    ∀ {Γ : Ctxt d} {t : d.Ty} {ts : List d.Ty} (m : MultiReturnCom d Γ (t :: ts)),
      CoveredM Good m → CoveredCom Good m.toComHead
  | _, _, _, .ret (.cons _ _), _ => by rw [MultiReturnCom.toComHead]; trivial
  | _, _, _, .var _ body, hm => by
      rw [MultiReturnCom.toComHead]
      exact ⟨hm.1, toComHead_mem body hm.2⟩

variable {n : Nat}

open FieldToJasminLimbs (arrTy loadLimbs loadArgs storeLimbs)

/-- **The loads of limbs at constant indices keep the operations of every continuation.** -/
theorem loadLimbs_mem {bs : List JasminTy} :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (a : Var Δ (arrTy n))
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Mont.Rn m) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h,
        CoveredM exprMemPos (k r h)) →
      CoveredM exprMemPos (loadLimbs m j a k)
  | _, 0, _, _, _, hk => by rw [loadLimbs]; exact hk _ _
  | _, m + 1, j, a, _, hk => by
      rw [loadLimbs]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        loadLimbs_mem m (j + 1) _ fun _ _ => hk _ _

/-- The loads of the limbs of every array keep the operations of every continuation. -/
theorem loadArgs_mem {bs : List JasminTy} :
    ∀ (Γ : Ctxt FieldDialect.fieldDialect) {Δ : Ctxt jasminDialect}
      (src : Ctxt.Hom (FieldToJasminLimbs.arrCtx n Γ) Δ)
      {k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' →
        Ctxt.Hom (MultiBlockLowering.ctxFlat (FieldToJasminLimbs.mapTysL n) Γ) Δ' → MC Δ' bs},
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') h,
        CoveredM exprMemPos (k r h)) →
      CoveredM exprMemPos (loadArgs Γ src k)
  | [], _, _, _, hk => by rw [loadArgs]; exact hk _ _
  | _ :: Γ, _, _, _, hk => by
      rw [loadArgs]
      exact loadLimbs_mem _ _ _ fun _ _ => loadArgs_mem Γ _ fun _ _ => hk _ _

/-- The stores of limbs at constant indices bind operations of `opMemB` of positive width only. -/
theorem storeLimbs_mem :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy n))
      (h : Ctxt.Hom (Mont.Rn m) Δ),
      CoveredM exprMemPos (storeLimbs m j o h)
  | _, 0, _, _, _ => by rw [storeLimbs]; trivial
  | _, m + 1, j, o, h => by
      rw [storeLimbs]
      exact bindK_mem _ rfl fun _ _ => bindK_mem _ rfl fun _ _ =>
        storeLimbs_mem m (j + 1) _ _

/-- **The lowered field program over word arrays binds operations of `opMemB` of positive
    width only**, for a covered program whose blocks bind operations of `opMemB` of positive
    width only. -/
theorem fieldBodyOf_mem (lo : FieldToJasminLimbs.LimbBlocks n)
    {Good : ∀ {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy},
      Expr FieldDialect.fieldDialect Γ t → Prop}
    (hB : ∀ {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy}
      (e : Expr FieldDialect.fieldDialect Γ t), Good e →
        CoveredM exprMemPos
          ((FieldToJasminLimbs.loweringOf lo).exprBlock e))
    {Γ : Ctxt FieldDialect.fieldDialect} {t : FieldDialect.FieldTy}
    (c : Com FieldDialect.fieldDialect Γ t) (hc : CoveredCom Good c) :
    CoveredM exprMemPos (FieldToJasminLimbs.fieldBodyOf lo c) := by
  rw [FieldToJasminLimbs.fieldBodyOf]
  exact loadArgs_mem Γ _ fun _ _ =>
    lowerR_mem _ hB _ c hc fun _ _ => storeLimbs_mem _ _ _ _

end Lower

/-! ## 6. The wide and one-limb bodies -/

section Wide

open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.TowerToLimbs (ArithAt)
open FieldWideInline
open FieldWideLeak (twistOp_coveredArith)

variable {n : Nat} (P : LimbParams n)

/-- The Montgomery limb block of an expression of `ArithAt P.p` binds operations of `opMemB`
    of positive width only. -/
theorem exprBlock_mem {Γ : Ctxt fieldDialect} {t : FieldTy} (e : Expr fieldDialect Γ t)
    (he : ArithAt P.p e) :
    CoveredM exprMemPos
      ((FieldToJasminLimbs.loweringOf (FieldToJasminLimbs.lowerOpL P)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  refine lowerOpL_mem P op ?_
  rcases he with h | h | h | h | ⟨c, h⟩ <;> (simp only at h; subst h; simp [FieldLower.arithOpB])

/-- **The block of the canonical Montgomery template binds operations of `opMemB` of positive
    width only**, for an operation of `arithOpB P.p`. -/
theorem ofMont_block_mem (hn : n < 2 ^ 64) (op : fieldDialect.Op)
    (hop : FieldLower.arithOpB P.p op = true) :
    CoveredCom exprMemPos
      (@FieldLower.FieldLowerTemplate.block (WideTemplate.ofMont P hn).α n
        (WideTemplate.ofMont P hn).inst (WideTemplate.ofMont P hn).P op) := by
  change CoveredCom exprMemPos
    (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbs.lowerOpL P) (twistOp n op))
  rw [FieldToJasminLimbs.fieldComOf]
  exact toComHead_mem _ (fieldBodyOf_mem _ (exprBlock_mem P) _ (twistOp_coveredArith P op hop))

/-- The Solinas limb block of an expression of `ArithAt (Solinas.p S)` binds operations of
    `opMemB` of positive width only. -/
theorem solinasExprBlock_mem (S : Solinas.SolinasParams n) {Γ : Ctxt fieldDialect}
    {t : FieldTy} (e : Expr fieldDialect Γ t) (he : ArithAt (Solinas.p S) e) :
    CoveredM exprMemPos
      ((FieldToJasminLimbs.loweringOf (FieldToJasminLimbsSolinas.lowerOpL S)).exprBlock e) := by
  obtain ⟨op, rfl, args⟩ := e
  refine solinasLowerOpL_mem S op ?_
  rcases he with h | h | h | h | ⟨c, h⟩ <;> (simp only at h; subst h; simp [FieldLower.arithOpB])

/-- **The blocks of a wide template bind operations of `opMemB` of positive width only**, for
    every operation of `arithOpB p`. -/
def WideMem {p m : Nat} (W : WideTemplate p m) : Prop :=
  ∀ op : fieldDialect.Op, FieldLower.arithOpB p op = true →
    CoveredCom exprMemPos (@FieldLower.FieldLowerTemplate.block W.α m W.inst W.P op)

theorem castN_mem {p m : Nat} (h : n = m) {W : WideTemplate p n} (hW : WideMem W) :
    WideMem (W.castN h) := by
  subst h
  exact hW

theorem castP_mem {p q : Nat} (h : p = q)
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (hW : WideMem W) :
    WideMem (W.castP h) := by
  subst h
  exact hW

/-- **The blocks of the Solinas template of a record bind operations of `opMemB` of positive
    width only.** -/
theorem ofSolinasAt_mem (S : Solinas.SolinasParams n)
    (hn : n = _root_.Hax.FieldTag.fieldLimbs (Solinas.p S)) (h64 : n < 2 ^ 64) :
    WideMem (WideTemplate.ofSolinasAt S hn h64) := by
  refine castN_mem hn fun op hop => ?_
  change CoveredCom exprMemPos
    (FieldToJasminLimbs.fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S) (FieldLower.opCom op))
  rw [FieldToJasminLimbs.fieldComOf]
  exact toComHead_mem _ (fieldBodyOf_mem _ (solinasExprBlock_mem S) _
    (FieldLower.coveredCom_opCom (fun h => h) op hop))

/-- **The blocks of a registered wide template bind operations of `opMemB` of positive width
    only.** -/
theorem wideTemplateOf_mem {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W) :
    WideMem W := by
  rcases wideTemplateOf_cases h with ⟨_, S, hn, h64, hp, rfl⟩ | ⟨_, _, hn, rfl⟩
  · exact castP_mem hp (ofSolinasAt_mem S hn h64)
  · exact fun op hop => ofMont_block_mem _ hn op hop

/-- **The body of a call at a registered wide template binds operations of `opMemB`
    of positive width only.** -/
theorem wideBlockOf_allOps {p : Nat}
    {W : WideTemplate p (_root_.Hax.FieldTag.fieldLimbs p)} (h : wideTemplateOf p = some W)
    (m : _root_.Hax.FieldTag.FieldMethod) : (wideBlockOf W m).allOps opMemPos = true :=
  allOps_ofCom (d := jasminDialect) opMemPos _
    (coveredCom_rename (d := jasminDialect) opMemPos _ _
      (wideTemplateOf_mem h _ (arithOpB_fieldOpOf m p)))

/-- The register block of the canonical Montgomery template binds operations of `opMemB`
    of positive width only, for an operation of `arithOpB P.p`. -/
theorem canonRegBlock_mem (op : fieldDialect.Op) (hg : FieldLower.arithOpB P.p op = true) :
    CoveredM exprMemPos (canonRegBlock P op) := by
  unfold canonRegBlock MultiBlockLowering.MultiBlockLoweringData.lowerMulti
  exact lowerR_mem _ (exprBlock_mem P) _ _ (twistOp_coveredArith P op hg) fun _ _ => trivial

/-- **The body of a call over one limb binds operations of `opMemB` of positive width
    only.** -/
theorem montWordBlockOf_allOps (P : LimbParams 1) (m : _root_.Hax.FieldTag.FieldMethod) :
    (montWordBlockOf P m).allOps opMemPos = true :=
  allOps_ofCom (d := jasminDialect) opMemPos _
    (coveredCom_rename (d := jasminDialect) opMemPos _ _
      (toComHead_mem _ (canonRegBlock_mem P _ (arithOpB_fieldOpOf m P.p))))

open FieldWideDecl (wideBody) in
/-- **Every body of a wide tagged head binds operations of `opMemB` of positive width only.** -/
theorem wideBody_allOps (f : String) (as rs : List JasminTy)
    (b : NFProg jasminDialect as rs) (hb : wideBody f as rs = some b) :
    b.allOps opMemPos = true := by
  unfold wideBody at hb
  split at hb
  · rename_i m p _
    split at hb
    · rename_i W hW
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        exact wideBlockOf_allOps hW m
      · cases hb
    · split at hb
      · rename_i P _
        split at hb
        · rename_i hs
          obtain ⟨rfl, rfl⟩ := hs
          cases hb
          exact montWordBlockOf_allOps P m
        · cases hb
      · cases hb
  · cases hb

end Wide

/-! ## 7. The inlining step -/

/-- **Every body of a tagged head binds operations of `opMemB` of positive width only**: the
    narrow template blocks (`fieldBlockOf_allOps`) and the wide and one-limb bodies
    (`wideBody_allOps`). -/
theorem fieldBody_allOps (f : String) (as rs : List JasminTy)
    (b : NFProg jasminDialect as rs) (hb : fieldBody f as rs = some b) :
    b.allOps opMemPos = true := by
  unfold fieldBody at hb
  split at hb
  · rename_i m p _
    split at hb
    · rename_i F hF
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        unfold narrowFieldOf at hF
        split at hF
        · rename_i k hk
          cases hF
          exact fieldBlockOf_allOps _ m
        · cases hF
      · cases hb
    · exact wideBody_allOps f as rs b hb
  · cases hb

/-- **`fieldInline_allOps_opMemB`: the inlining of the tagged field calls keeps
    `allOps (fun op => opMemB op && bindPosB op)`.** When every operation of the input is in
    the op set `opMemB` of the stack-memory fragment and has a result of positive width, so
    is every operation of the program `fieldInlineStep` returns, at every modulus the front
    admits: inlining keeps an operation predicate of the library's bodies (`allOps_inline?`),
    and every body of a tagged head binds operations of `opMemB` of positive width only
    (`fieldBody_allOps`). -/
theorem fieldInline_allOps_opMemB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p q : NFProg jasminDialect Γ ts}
    (hp : p.allOps opMemPos = true)
    (hq : (fieldInlineStep Γ ts).run p = some q) :
    q.allOps opMemPos = true := by
  change (NFProg.inline? fieldLibJ p).bind
    (fun q => if fieldFree q then some q else none) = some q at hq
  obtain ⟨q', hq', h⟩ := Option.bind_eq_some_iff.mp hq
  split at h
  · cases h
    exact allOps_inline? fieldLibJ opMemPos (fun _ _ hb => by simp [fieldLibJ] at hb)
      (fun f as rs b hb => fieldBody_allOps f as rs b hb) p hq' hp
  · cases h

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldInlineOps
