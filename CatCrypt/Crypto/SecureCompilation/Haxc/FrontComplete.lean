/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ExtChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
public import CatCrypt.Crypto.Hax.FrontOps

/-!
# The output of the hax front lies in the domain of the translation

The front `haxToNF` of a module, followed by tuple flattening `flatSameStep` and dead-binding
elimination `NFProg.dce`, returns programs of `NFToCatComplete.NBD` at the declarations
`fieldDeclsFor (linkedDecls m bi)`, every tagged call of which has a template
(`ChainTotal.fieldTemplsB`). The proof follows the operations through the passes.

`impToNF` at a call typing `S` binds only the operations of `frontOp S`: the calls `S`
types, integer literals of `ilitOk`, trip counts at an unsigned type or a word of at most
`64` bits, the subtraction of `64`-bit words, the constants, the loop counter and the tuple
constructors; its exit-flag loops carry types of `whileCarryOkB` and its regions have no
`call` node (`opsNB` at the loop test `fun cs => cs.all whileCarryOkB`). The bodies of the
callees of a module are translated at the same call typing as the entry and have no exit-flag
loop, so inlining keeps `opsNB (frontOp S)` (`opsNB_inline?`, through `seq?` and `rename?`);
after the rounds no call of a callee is left (`crateInlineOk_noCrateCall`); tuple flattening
removes the tuple operations, keeps the others and keeps the carried types of the loops,
which are no tuples (`opsNB_flatSame`); `dce` removes bindings only.

The domain also constrains the types of the arguments: the integer-slice calls of
`hax64SigOf` and a trip count at a word narrower than `64` bits are outside it. These are
excluded by the types of the variables: over a context of `tyU` types (no slice, no word
other than the `64`-bit word), every operation of `outOp m` has a `tyU` result, so every
variable of the program has a `tyU` type, and the entry of a layout binds `64`-bit words and
arrays of them (`tyU_entryCtx`).

## Main definitions

* `tyU` — the types of the variables of the output.
* `outOp` — the operations of the output of a module after inlining and flattening.

## Main results

* `opsNB_seq?`, `opsNB_inline?`, `opsNB_inlineIter` — splicing and inlining keep `opsNB`
  (module `FrontOps` defines `opsNB`, `preOps` and `frontOp` and proves that the front binds
  only operations of `frontOp`).
* `opsNB_flatProg`, `opsNB_flatSame` — tuple flattening removes the tuple operations.
* `dom_of_hax64SigOf`, `dom_of_fieldTagSig`, `dom_of_linkSig`, `dom_of_outOp` — a typed
  call, and an operation of the output on `tyU` arguments, is in the domain.
* `NBDL_of_outOp`, `fieldDeclsOf_modOk` — a program of the output over a context of `tyU`
  types satisfies `NBDL` at every list of flags, and its tagged calls are at moduli that
  pass `fieldModOk`.
* `haxToNF_flatSame_opsNBLoop` — the flattened output of the front is a program of
  `opsNB (outOp m)` whose exit-flag loops carry types of `whileCarryOkB`.
* `haxToNF_imp_NBD`, `HaxModule.refusal?_eq_none_imp_NBD` — the flattened and
  dead-code-eliminated output of the front of a module satisfies `NBD` at its declarations
  and `fieldTemplsB`.
* `noTuple_of_hax64SigOf`, `noTuple_of_linkSig`, `opFlatOk_of_frontOp`,
  `haxToNF_flatSame_isSome` — the calls of the front have no tuple type, and tuple
  flattening succeeds on the output of the front.
* `HaxModule.refusal?_eq_none_imp_extChain_isSome_of_outTyB` — on a module `refusal?`
  accepts, at a result type that passes `outTyB`, the chain `extChain` returns a program.
* `HaxModule.refusal?_eq_none_imp_extChain_isSome` — on a module `refusal?` accepts, the
  chain `extChain` returns a program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open Ctxt (Var Valuation)

/-! ## 1. The operations of a program without exit-flag loops and calls -/

section Generic

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
  [HasBoolBit d]

/-- A program of `opsNB P` all of whose operations satisfy `Q` is a program of
    `opsNB (P && Q)`. -/
theorem opsNB_and_allOps {P Q : d.Op → Bool} {W : List d.Ty → Bool} {Γ : Ctxt d}
    {ts : List d.Ty} (p : NFProg d Γ ts) (hp : opsNB P p W = true) (hq : p.allOps Q = true) :
    opsNB (fun o => P o && Q o) p W = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [opsNB, NFProg.allOps, Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨hp.1, hq.1⟩, ih hp.2 hq.2⟩
  | forLoop _ _ body k ihb ihk =>
      simp only [opsNB, NFProg.allOps, Bool.and_eq_true] at hp hq ⊢
      exact ⟨ihb hp.1 hq.1, ihk hp.2 hq.2⟩
  | ifThenElse _ thn els k iht ihe ihk =>
      simp only [opsNB, NFProg.allOps, Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨iht hp.1.1 hq.1.1, ihe hp.1.2 hq.1.2⟩, ihk hp.2 hq.2⟩
  | whileLoop _ body k ihb ihk =>
      simp only [opsNB, NFProg.allOps, Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨hp.1.1, ihb hp.1.2 hq.1⟩, ihk hp.2 hq.2⟩
  | call => simp [opsNB] at hp

/-- The splice of two programs of `opsNB P` is a program of `opsNB P`. -/
theorem opsNB_seq? {P : d.Op → Bool} {W : List d.Ty → Bool} {Δ : Ctxt d} {rs : List d.Ty}
    (b : NFProg d Δ rs) :
    ∀ {Γ₀ : Ctxt d} {ts : List d.Ty} (k : NFProg d (rs ++ Γ₀) ts) {Γ : Ctxt d}
      {ρ : PRen Δ Γ} {θ : PRen Γ₀ Γ} {q : NFProg d Γ ts}, NFProg.seq? k b ρ θ = some q →
      opsNB P b W = true → opsNB P k W = true → opsNB P q W = true := by
  induction b with
  | ret vs =>
      intro Γ₀ ts k Γ ρ θ q h _ hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      exact opsNB_rename? k h hk
  | var e b ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨e', he, b', hb', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hb ⊢
      exact ⟨(op_rename? he).symm ▸ hb.1, ih k hb' hb.2 hk⟩
  | forLoop count inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, _, _, body', hbody', b', hb', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hb ⊢
      exact ⟨opsNB_rename? body hbody' hb.1, ih k hb' hb.2 hk⟩
  | ifThenElse cond thn els b _ _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, t', ht, e', he, b', hb', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hb ⊢
      exact ⟨⟨opsNB_rename? thn ht hb.1.1, opsNB_rename? els he hb.1.2⟩, ih k hb' hb.2 hk⟩
  | whileLoop inits body b _ ih =>
      intro Γ₀ ts k Γ ρ θ q h hb hk
      simp only [NFProg.seq?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨_, _, body', hbody', b', hb', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hb ⊢
      exact ⟨⟨hb.1.1, opsNB_rename? body hbody' hb.1.2⟩, ih k hb' hb.2 hk⟩
  | call => intro _ _ _ _ _ _ _ _ hb; simp [opsNB] at hb

/-- **Inlining keeps `opsNB P`** at a library whose operation bodies are programs of
    `opsNB P`. -/
theorem opsNB_inline? {P : d.Op → Bool} {W : List d.Ty → Bool} {L : InlineLib d}
    (hL : ∀ o b, L.op o = some b → opsNB P b W = true) {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) :
    ∀ {p' : NFProg d Γ ts}, NFProg.inline? L p = some p' → opsNB P p W = true →
      opsNB P p' W = true := by
  induction p with
  | ret vs =>
      intro p' h _
      cases h
      rfl
  | var e k ih =>
      intro p' h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff] at h
      obtain ⟨k', hk', h⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp
      have hk'' := ih hk' hp.2
      obtain ⟨o, rfl, args⟩ := e
      simp only [NFProg.inlineVar] at h
      split at h
      · rename_i b hb
        exact opsNB_seq? b k' h (hL o b hb) hk''
      · cases h
        simp only [opsNB, Bool.and_eq_true]
        exact ⟨hp.1, hk''⟩
  | forLoop count inits body k ihb ihk =>
      intro p' h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb hb' hp.1, ihk hk' hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro p' h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t', ht', e', he', k', hk', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨iht ht' hp.1.1, ihe he' hp.1.2⟩, ihk hk' hp.2⟩
  | whileLoop inits body k ihb ihk =>
      intro p' h hp
      simp only [NFProg.inline?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b', hb', k', hk', rfl⟩ := h
      simp only [opsNB, Bool.and_eq_true] at hp ⊢
      exact ⟨⟨hp.1.1, ihb hb' hp.1.2⟩, ihk hk' hp.2⟩
  | call => intro _ _ hp; simp [opsNB] at hp

/-- **Repeated inlining keeps `opsNB P`** at a library whose operation bodies are programs of
    `opsNB P`. -/
theorem opsNB_inlineIter {P : d.Op → Bool} {W : List d.Ty → Bool} {L : InlineLib d}
    (hL : ∀ o b, L.op o = some b → opsNB P b W = true) {Γ : Ctxt d} {ts : List d.Ty} :
    ∀ (n : Nat) (p : NFProg d Γ ts), opsNB P p W = true → opsNB P (p.inlineIter L n) W = true
  | 0, _, hp => hp
  | n + 1, p, hp => by
      simp only [NFProg.inlineIter]
      split
      · rename_i q hq
        exact opsNB_inlineIter hL n q (opsNB_inline? hL p hq hp)
      · exact hp

end Generic

/-! ## 3. Tuple flattening -/

section Flatten

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples

/-- **Tuple flattening removes the tuple operations and keeps the others**: on a program
    every operation of which is a tuple operation or satisfies `P`, a program `flatProg`
    returns has no tuple operation, and its operations satisfy `P`; at a loop test `W` that
    accepts the flattening of every tuple it accepts, its exit-flag loops pass `W`. -/
theorem opsNB_flatProg {P : NfOp → Bool} {W : List NfTy → Bool}
    (hW : ∀ cs, W cs = true → W (flatCtx cs) = true) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt nfDialect} (ren : Ctxt.Hom (flatCtx Γ) Δ) (q : NFProg nfDialect Δ (flatCtx ts)),
      flatProg p ren = some q → opsNB (fun o => opIsTuple o || P o) p W = true →
        opsNB (fun o => !opIsTuple o && P o) q W = true := by
  induction p with
  | ret vs =>
      intro Δ ren q hq _
      rw [flatProg] at hq
      cases hq
      rfl
  | var e k ih =>
      obtain ⟨op, rfl, args⟩ := e
      intro Δ ren q hq hp
      simp only [opsNB, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      cases hT : tupleHom? ren op args with
      | some R =>
          simp only [hT] at hq
          exact ih _ q hq hp.2
      | none =>
          simp only [hT, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
          obtain ⟨args', _, R, _, k', hk, rfl⟩ := hq
          have ht := opIsTuple_of_tupleHom?_eq_none ren op args hT
          have h1 := hp.1
          simp only [ht, Bool.false_or] at h1
          simp only [opsNB, Bool.and_eq_true, ht, Bool.not_false, Bool.true_and]
          exact ⟨h1, ih _ k' hk hp.2⟩
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q hq hp
      simp only [opsNB, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      simp only [opsNB, Bool.and_eq_true]
      exact ⟨ihb _ body' hb hp.1, ihk _ k' hk hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q hq hp
      simp only [opsNB, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨thn', ht, els', he, k', hk, rfl⟩ := hq
      simp only [opsNB, Bool.and_eq_true]
      exact ⟨⟨iht _ thn' ht hp.1.1, ihe _ els' he hp.1.2⟩, ihk _ k' hk hp.2⟩
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q hq hp
      simp only [opsNB, Bool.and_eq_true] at hp
      rw [flatProg] at hq
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨body', hb, k', hk, rfl⟩ := hq
      simp only [opsNB, Bool.and_eq_true]
      exact ⟨⟨hW _ hp.1.1, ihb _ body' hb hp.1.2⟩, ihk _ k' hk hp.2⟩
  | call => intro _ _ _ _ hp; simp [opsNB] at hp

/-- `opsNB` at the loop test `W` of a program cast along equal contexts and result types. -/
theorem opsNB_cast_loop (P : NfOp → Bool) (W : List NfTy → Bool) {Γ Γ' : Ctxt nfDialect}
    {ts ts' : List NfTy} (hΓ : Γ' = Γ) (hts : ts' = ts)
    (e : NFProg nfDialect Γ' ts' = NFProg nfDialect Γ ts) (q : NFProg nfDialect Γ' ts') :
    opsNB P (cast e q) W = opsNB P q W := by
  subst hΓ
  subst hts
  rfl

/-- `flatSame` removes the tuple operations and keeps the others; at a loop test `W` that
    accepts the flattening of every tuple it accepts, its exit-flag loops pass `W`. -/
theorem opsNB_flatSame {P : NfOp → Bool} {W : List NfTy → Bool}
    (hW : ∀ cs, W cs = true → W (flatCtx cs) = true) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p q : NFProg nfDialect Γ ts} (hq : flatSame p = some q)
    (hp : opsNB (fun o => opIsTuple o || P o) p W = true) :
    opsNB (fun o => !opIsTuple o && P o) q W = true := by
  unfold flatSame at hq
  split at hq
  · rename_i h
    obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
    rw [opsNB_cast_loop _ _ (flatCtx_of_noTuple h.1) (flatCtx_of_noTuple h.2)]
    exact opsNB_flatProg hW p _ q0 hq0 hp
  · cases hq

/-- A tuple of types of `whileCarryOkB` has no tuple type. -/
theorem noTuple_of_whileCarry {cs : List NfTy}
    (h : cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB = true) : NoTuple cs := by
  simp only [NoTuple, List.all_eq_true] at h ⊢
  intro t ht
  have := h t ht
  cases t <;> simp_all [CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB, tyIsTuple]

/-- The loop test of the front, `whileCarryOkB` at every carried type, accepts the flattening
    of every tuple it accepts. -/
theorem whileCarry_flatCtx (cs : List NfTy)
    (h : cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB = true) :
    (flatCtx cs).all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB = true := by
  rw [flatCtx_of_noTuple (noTuple_of_whileCarry h)]
  exact h

end Flatten

/-! ## 4. The typed operations of the output lie in the domain of the translation -/

section Typed

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.NFToCat (ExtDecl declared declared_iff wordArrTy)
open CatCrypt.Crypto.Hax.NFToCatComplete (nbOp extOk NBDL NBD ilitOk tripOk scalarCallOk
  memCallOk)
open _root_.Hax.FieldTag (fieldTag?)

/-- The types of the variables of the front's output: every type other than a word of a
    width other than `64` and a slice. -/
def tyU : NfTy → Bool
  | .word w => decide (w = 64)
  | .slice _ => false
  | _ => true

/-- A variable of a context of `tyU` types has a `tyU` type. -/
theorem tyU_var {Γ : Ctxt nfDialect} (hΓ : ∀ t ∈ Γ, tyU t = true) :
    ∀ {t : NfTy}, Var Γ t → tyU t = true
  | _, .here => hΓ _ List.mem_cons_self
  | _, .there v => tyU_var (fun s hs => hΓ s (List.mem_cons_of_mem _ hs)) v

/-- The types of a vector of variables of a context of `tyU` types are `tyU` types. -/
theorem tyU_vars {Γ : Ctxt nfDialect} (hΓ : ∀ t ∈ Γ, tyU t = true) :
    ∀ {ss : List NfTy}, HVector (fun t => Var Γ t) ss → ∀ t ∈ ss, tyU t = true
  | [], .nil => fun _ h => absurd h List.not_mem_nil
  | _ :: _, .cons v vs => fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact tyU_var hΓ v
      · exact tyU_vars hΓ vs t ht

/-- A type of words and word arrays is a `tyU` type. -/
theorem tyU_of_wordArrTy {t : NfTy} (h : wordArrTy t = true) : tyU t = true := by
  unfold wordArrTy CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy at h
  split at h
  · rfl
  · split at h
    · rfl
    · rfl
    · cases h

open CatCrypt.Crypto.Hax.ImpToNF (hax64ScalarSig hax64SigOf hax64SigOfArr fieldTagSig
  hax64NFWordTy scalarBinOf scalarCmpOf scalarUnOf selTy fieldElemTy fieldModOk crateSigOf
  argTysFit tableOf entryCtx)

/-- **A scalar call of the `u64` typing is in the domain**: a call `hax64ScalarSig` types is
    a call of `scalarCallOk` or of `memCallOk`, at a `tyU` result type. -/
theorem dom_of_hax64ScalarSig {f : String} {as : List NfTy} {r : NfTy}
    (h : hax64ScalarSig f as = some r) :
    (scalarCallOk f as r || memCallOk f as r) = true ∧ tyU r = true := by
  rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩
  · simp [hax64ScalarSig] at h
  · simp only [hax64ScalarSig] at h
    split at h
    · cases h
      rename_i hu
      simp only [Bool.and_eq_true] at hu
      simp [scalarCallOk, hu.1, hu.2, tyU]
    · split at h
      · cases h
        rename_i hn
        obtain ⟨rfl, hn⟩ := hn
        simp [scalarCallOk, hn, tyU]
      · cases h
  · simp only [hax64ScalarSig] at h
    split at h
    · rename_i hab
      simp only [Bool.and_eq_true] at hab
      split at h
      · cases h
        rename_i hb
        simp [scalarCallOk, hab.1, hab.2, hb, tyU]
      · split at h
        · cases h
          rename_i hc
          simp [scalarCallOk, hab.1, hab.2, hc, tyU]
        · cases h
    · split at h
      · cases h
        rename_i hs
        obtain ⟨rfl, rfl, hany⟩ := hs
        simp [scalarCallOk, hany, tyU]
      · cases h
  · simp only [hax64ScalarSig] at h
    split at h
    · cases h
      rename_i hs
      obtain ⟨rfl, rfl, hb, hc⟩ := hs
      unfold selTy
      split
      · simp [memCallOk, hb, hc, tyU]
      · simp [memCallOk, hb, hc, tyU]
    · cases h
  · simp [hax64ScalarSig] at h

/-- **A call of the `u64` typing on `tyU` arguments**: a call of `scalarCallOk` or of
    `memCallOk` at a `tyU` result type, or a tagged field call `fieldTagSig` types. The
    integer-slice calls of `hax64SigOf` take a slice, which is no `tyU` type. -/
theorem dom_of_hax64SigOf {f : String} {as : List NfTy} {r : NfTy}
    (h : hax64SigOf f as = some r) (has : ∀ t ∈ as, tyU t = true) :
    ((scalarCallOk f as r || memCallOk f as r) = true ∧ tyU r = true) ∨
      fieldTagSig f as = some r := by
  unfold hax64SigOf at h
  split at h
  · cases h
    exact Or.inr ‹_›
  · split at h
    · cases h
      exact Or.inl (dom_of_hax64ScalarSig ‹_›)
    · split at h
      · exact absurd (has _ List.mem_cons_self) (by simp [tyU])
      · exact absurd (has _ List.mem_cons_self) (by simp [tyU])
      · split at h
        · rename_i t _ _ ht
          simp only [Option.some.injEq] at h
          subst h
          left
          have hw : t = NfTy.int ∨ t = NfTy.word 64 := by
            unfold CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy at ht
            split at ht <;> simp_all
          rcases hw with rfl | rfl <;> simp [scalarCallOk, tyU]
        · cases h
      · left
        unfold hax64SigOfArr at h
        split at h
        · split at h
          · cases h
            simp [memCallOk, *, tyU]
          · cases h
        · split at h
          · rename_i hti
            cases h
            simp only [memCallOk, hti, tyU, beq_self_eq_true, Bool.and_true, Bool.true_and,
              Bool.or_eq_true, and_true]
            exact Or.inr rfl
          · cases h
        · split at h
          · cases h
            simp [memCallOk, scalarCallOk, tyU]
          · cases h
        · split at h
          · rename_i hrep
            cases h
            obtain ⟨k, rfl⟩ : ∃ k, as = List.replicate k (.word 64) := ⟨_, hrep⟩
            rcases k with _ | _ | _ | k <;>
              simp [memCallOk, scalarCallOk, tyU, List.replicate]
          · cases h
        · cases h

/-- **A tagged field call is declared by its operation**: a call `fieldTagSig` types is
    declared by `opFieldDecls` at its signature, has a `tyU` result type, and its head is
    tagged at a modulus that passes `fieldModOk`. -/
theorem dom_of_fieldTagSig {f : String} {as : List NfTy} {r : NfTy}
    (h : fieldTagSig f as = some r) :
    declared (opFieldDecls (.call f as r)) f as r = true ∧ tyU r = true ∧
      ∃ mm p, fieldTag? f = some (mm, p) ∧ fieldModOk p = true := by
  obtain ⟨mm, p, hmp, has, hr⟩ := CatCrypt.Crypto.Hax.ImpToNF.fieldTagSig_some h
  have hok := CatCrypt.Crypto.Hax.ImpToNF.fieldTagSig_modOk h hmp
  subst has hr
  refine ⟨?_, ?_, mm, p, hmp, hok⟩
  · simp only [opFieldDecls, hmp]
    rw [declared_iff]
    by_cases hp : p < 2 ^ 64
    · have he : fieldElemTy p = .word 64 := ite_eq_left hp
      rw [ite_eq_left hp, he, _root_.Hax.FieldTag.FieldMethod.sigAt_word]
      refine ⟨_, List.mem_singleton_self _, rfl, rfl, rfl, ?_⟩
      cases mm <;> rfl
    · have he : fieldElemTy p = .arr (_root_.Hax.FieldTag.fieldLimbs p) (.word 64) := ite_eq_right hp
      rw [ite_eq_right hp, he]
      refine ⟨_, List.mem_singleton_self _, rfl, rfl, rfl, ?_⟩
      simp only [ExtDecl.wordSig, CatCrypt.Crypto.Hax.NFToCat.wordArrSig, FieldWideDecl.wideDecl,
        Bool.and_eq_true, List.all_eq_true]
      exact ⟨FieldWideDecl.wordArrTy_sigAt mm _, rfl⟩
  · unfold fieldElemTy
    split <;> rfl

/-- A type whose values encode as integers is a type of words and word arrays. -/
theorem wordArrTy_of_wordTy {a : NfTy} (ha : hax64NFWordTy a = true) : wordArrTy a = true := by
  unfold wordArrTy
  split
  · rfl
  · exact ha

/-- A list of argument types that fits parameter types of words and word arrays is one of
    the lists `sigVariants` gives, and its types are types of words and word arrays. -/
theorem mem_sigVariants :
    ∀ {ps as : List NfTy}, (∀ p ∈ ps, linkResOk p = true) → argTysFit ps as = true →
      as ∈ sigVariants ps ∧ as.all wordArrTy = true
  | [], [], _, _ => ⟨List.mem_singleton_self _, rfl⟩
  | [], _ :: _, _, h => by simp [argTysFit] at h
  | _ :: _, [], _, h => by simp [argTysFit] at h
  | p :: ps, a :: as, hps, h => by
      simp only [argTysFit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨hpa, h⟩ := h
      obtain ⟨hm, hall⟩ := mem_sigVariants (fun q hq => hps q (List.mem_cons_of_mem _ hq)) h
      have hp := hps p List.mem_cons_self
      have ha : a ∈ (if hax64NFWordTy p then [NfTy.word 64, NfTy.int] else [p]) ∧
          wordArrTy a = true := by
        rcases linkResOk_iff.mp hp with rfl | ⟨n, rfl⟩
        · rcases hpa with rfl | ⟨-, ha⟩
          · exact ⟨by simp [hax64NFWordTy], rfl⟩
          · refine ⟨?_, wordArrTy_of_wordTy ha⟩
            revert ha
            unfold hax64NFWordTy
            split <;> simp
        · rcases hpa with rfl | ⟨hn, -⟩
          · exact ⟨by simp [hax64NFWordTy], rfl⟩
          · simp [hax64NFWordTy] at hn
      refine ⟨?_, by simp only [List.all_cons, ha.2, Bool.true_and]; exact hall⟩
      simp only [sigVariants, List.mem_flatMap, List.mem_map]
      exact ⟨a, ha.1, as, hm, rfl⟩

/-- **A call of the typing of the linked functions on `tyU` arguments**: a call of a linked
    function, declared by the declarations of `linkedDecls` whose names are no field heads,
    at a `tyU` result type; or a call `hax64SigOf` types. -/
theorem dom_of_linkSig {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) (hls : ∀ l ∈ m.linked, linkSigOk l = true)
    (bi : _root_.Hax.Builtins) {f : String} {as : List NfTy} {r : NfTy}
    (h : m.linkSig f as = some r) :
    (declared ((linkedDecls m bi).filter fun d => !_root_.Hax.FieldTag.fieldHeadB d.name)
        f as r = true ∧
        tyU r = true) ∨ hax64SigOf f as = some r := by
  unfold CatCrypt.Crypto.Hax.HaxModule.linkSig crateSigOf at h
  split at h
  · rename_i c hc
    split at h
    · rename_i hfit
      cases h
      left
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hc)
      have hname : l.name = f := by
        have := List.find?_some hc
        simpa [CatCrypt.Crypto.Hax.LinkedFn.callee] using this
      have hsig := hls l hl
      simp only [linkSigOk, Bool.and_eq_true, List.all_eq_true] at hsig
      have hfit' : argTysFit (l.params.map (·.2)) as = true := hfit
      obtain ⟨hv, hall⟩ := mem_sigVariants (fun q hq => by
        obtain ⟨⟨x, q'⟩, hx, rfl⟩ := List.mem_map.mp hq
        exact hsig.1 (x, q') hx) hfit'
      have hres : wordArrTy l.res = true := by
        rcases linkResOk_iff.mp hsig.2 with h | ⟨n, h⟩ <;> rw [h] <;> rfl
      refine ⟨?_, tyU_of_wordArrTy hres⟩
      rw [declared_iff]
      refine ⟨⟨l.name, as, l.res, (tableOf bi).call l.name as l.res⟩, ?_, hname, rfl, rfl, ?_⟩
      · refine List.mem_filter.mpr ⟨?_, by simp [fieldHeadB_of_linkNameOk (hlk l hl)]⟩
        refine List.mem_flatMap.mpr ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, ?_⟩
        · simp [hlk l hl, hsig.2]
        · exact List.mem_map.mpr ⟨as, List.mem_filter.mpr ⟨hv, hall⟩, rfl⟩
      · simp [ExtDecl.wordSig, CatCrypt.Crypto.Hax.NFToCat.wordArrSig, hall, hres]
    · cases h
  · exact Or.inr h

/-- A list of declarations that contains every declaration of `D₁` declares every call `D₁`
    declares. -/
theorem declared_mono {D₁ D₂ : List ExtDecl} (h : ∀ d ∈ D₁, d ∈ D₂) {f : String}
    {as : List NfTy} {r : NfTy} (hd : declared D₁ f as r = true) : declared D₂ f as r = true := by
  obtain ⟨d, hd, h'⟩ := declared_iff.mp hd
  exact declared_iff.mpr ⟨d, h d hd, h'⟩

open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples (opIsTuple)
open CatCrypt.Crypto.Hax.NFInline (crateCallOp)

/-- **The operations of the output of the hax front of the module `m`** after inlining and
    tuple flattening: no tuple operation, an operation of `frontOp` at the call typing of the
    module, and no call of a function of the module. -/
def outOp (m : CatCrypt.Crypto.Hax.HaxModule) (o : NfOp) : Bool :=
  !opIsTuple o && (frontOp (crateSigOf (m.prepared nfBody) m.linkSig) o &&
    !crateCallOp (m.prepared nfBody) o)

/-- **An operation of the output on `tyU` arguments is in the domain of the translation**:
    an operation of `nbOp`, or a call that `D` declares when `D` contains the untagged
    declarations of the linked functions and the declarations `opFieldDecls` of the
    operation; its result type is a `tyU` type. -/
theorem dom_of_outOp {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) (hls : ∀ l ∈ m.linked, linkSigOk l = true)
    (bi : _root_.Hax.Builtins) {D : List ExtDecl}
    (hD : ∀ d ∈ (linkedDecls m bi).filter (fun d => !_root_.Hax.FieldTag.fieldHeadB d.name),
      d ∈ D) :
    ∀ (o : NfOp), outOp m o = true → (∀ t ∈ o.sig, tyU t = true) →
      (∀ d ∈ opFieldDecls o, d ∈ D) → (nbOp o || extOk D o) = true ∧ tyU o.ret = true := by
  intro o
  induction o with
  | named n o ih =>
      intro h hs hF
      exact ih h hs hF
  | call f as r =>
      intro h hs hF
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      obtain ⟨hS, hn⟩ := h
      have hL : m.linkSig f as = some r := by
        unfold crateSigOf at hS
        rw [hn] at hS
        exact hS
      rcases dom_of_linkSig hlk hls bi hL with ⟨hd, hr⟩ | hb
      · refine ⟨?_, hr⟩
        simp only [extOk, declared_mono hD hd, Bool.or_true]
      · rcases dom_of_hax64SigOf hb hs with ⟨hc, hr⟩ | hf
        · exact ⟨by simp only [nbOp, hc, Bool.true_or], hr⟩
        · obtain ⟨hd, hr, -⟩ := dom_of_fieldTagSig hf
          refine ⟨?_, hr⟩
          simp only [extOk, declared_mono hF hd, Bool.or_true]
  | ilit t v =>
      intro h _ _
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_true] at h
      refine ⟨by simp only [nbOp, h, Bool.true_or], ?_⟩
      simp only [ilitOk, Bool.and_eq_true, Bool.or_eq_true] at h
      rcases h.2 with h | h
      · revert h
        unfold hax64NFWordTy
        split <;> simp_all [tyU]
      · revert h
        cases t <;> simp [tyU]
  | trip t =>
      intro h hs _
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_true] at h
      have ht : tyU t = true := hs t (by simp)
      refine ⟨?_, rfl⟩
      simp only [nbOp, tripOk]
      revert h ht
      cases t <;> simp_all [tripBoundTy, tyU, hax64NFWordTy]
  | boundInt t =>
      intro h _ _
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_true] at h
      refine ⟨?_, rfl⟩
      simp only [nbOp, tripOk]
      revert h
      cases t <;> simp_all [CatCrypt.Crypto.Hax.ImpToNF.loTyOk,
        CatCrypt.Crypto.Hax.ImpToNF.hax64NFWordTy]
  | bin o w =>
      intro h _ _
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_true] at h
      refine ⟨by simp only [nbOp, h, Bool.true_or], ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp [h.2, tyU]
  | constBit => intro _ _ _; exact ⟨rfl, rfl⟩
  | constUnit => intro _ _ _; exact ⟨rfl, rfl⟩
  | ctr => intro _ _ _; exact ⟨rfl, rfl⟩
  | arrRepeat n t =>
      intro h _ _
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_true, decide_eq_true_eq] at h
      subst h
      exact ⟨by simp [nbOp], rfl⟩
  | _ => intro h; simp [outOp, NFFlattenTuples.opIsTuple, frontOp] at h

/-- **A program of the output over a context of `tyU` types is in the domain with declared
    calls** at every list of literal flags: when every operation satisfies `outOp m`, the
    program has no `call` node (its exit-flag loops pass the loop test `W`, at every `W`),
    and `D` contains the untagged declarations of the linked functions and the declarations
    `fieldDeclsOf` of the program, the program satisfies `NBDL D L`; its result types are
    `tyU` types. -/
theorem NBDL_of_outOp {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) (hls : ∀ l ∈ m.linked, linkSigOk l = true)
    (bi : _root_.Hax.Builtins) {D : List ExtDecl}
    (hD : ∀ d ∈ (linkedDecls m bi).filter (fun d => !_root_.Hax.FieldTag.fieldHeadB d.name),
      d ∈ D)
    {W : List NfTy → Bool} {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ (L : List Bool), (∀ t ∈ Γ, tyU t = true) → opsNB (outOp m) p W = true →
      (∀ d ∈ fieldDeclsOf p, d ∈ D) → NBDL D L p = true ∧ ∀ t ∈ ts, tyU t = true := by
  induction p with
  | ret vs => intro L hΓ _ _; exact ⟨rfl, tyU_vars hΓ vs⟩
  | var e k ih =>
      obtain ⟨o, rfl, args⟩ := e
      intro L hΓ hp hF
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [fieldDeclsOf, List.mem_append] at hF
      obtain ⟨hnb, hret⟩ := dom_of_outOp hlk hls bi hD o hp.1 (tyU_vars hΓ args)
        (fun d hd => hF d (Or.inl hd))
      obtain ⟨hk, hts⟩ := ih (CatCrypt.Crypto.Hax.NFToCatComplete.litOp o :: L)
        (fun t ht => by
          rcases List.mem_cons.mp ht with rfl | ht
          exacts [hret, hΓ t ht]) hp.2
        (fun d hd => hF d (Or.inr hd))
      refine ⟨?_, hts⟩
      simp only [NBDL, Bool.and_eq_true, Bool.or_eq_true]
      refine ⟨?_, hk⟩
      rcases Bool.or_eq_true_iff.mp hnb with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  | @forLoop Γ cs ts count inits body k ihb ihk =>
      intro L hΓ hp hF
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [fieldDeclsOf, List.mem_append] at hF
      have hcs := tyU_vars hΓ inits
      obtain ⟨hb, -⟩ := ihb (List.replicate cs.length false ++ false :: L)
        (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          · exact hcs t ht
          · rcases List.mem_cons.mp ht with rfl | ht
            exacts [rfl, hΓ t ht]) hp.1 (fun d hd => hF d (Or.inl hd))
      obtain ⟨hk, hts⟩ := ihk (List.replicate cs.length false ++ L)
        (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          exacts [hcs t ht, hΓ t ht]) hp.2 (fun d hd => hF d (Or.inr hd))
      exact ⟨by simp only [NBDL, hb, hk, Bool.and_self], hts⟩
  | @ifThenElse Γ rs ts cond thn els k iht ihe ihk =>
      intro L hΓ hp hF
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [fieldDeclsOf, List.mem_append] at hF
      obtain ⟨ht, hrs⟩ := iht L hΓ hp.1.1 (fun d hd => hF d (Or.inl (Or.inl hd)))
      obtain ⟨he, -⟩ := ihe L hΓ hp.1.2 (fun d hd => hF d (Or.inl (Or.inr hd)))
      obtain ⟨hk, hts⟩ := ihk (List.replicate rs.length false ++ L)
        (fun t ht => by
          rcases List.mem_append.mp ht with ht | ht
          exacts [hrs t ht, hΓ t ht]) hp.2 (fun d hd => hF d (Or.inr hd))
      exact ⟨by simp only [NBDL, ht, he, hk, Bool.and_self], hts⟩
  | @whileLoop Γ cs ts inits body k ihb ihk =>
      intro L hΓ hp hF
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [fieldDeclsOf, List.mem_append] at hF
      have hcs := tyU_vars hΓ inits
      have hΓ' : ∀ t ∈ cs ++ Γ, tyU t = true := fun t ht => by
        rcases List.mem_append.mp ht with ht | ht
        exacts [hcs t ht, hΓ t ht]
      obtain ⟨hb, -⟩ := ihb (List.replicate cs.length false ++ L) hΓ' hp.1.2
        (fun d hd => hF d (Or.inl hd))
      obtain ⟨hk, hts⟩ := ihk (List.replicate cs.length false ++ L) hΓ' hp.2
        (fun d hd => hF d (Or.inr hd))
      exact ⟨by simp only [NBDL, hb, hk, Bool.and_self], hts⟩
  | call => intro _ _ hp; simp [opsNB] at hp

/-- **The tagged calls of the output are at moduli with a template**: the declaration
    `opFieldDecls` of an operation of `outOp m` is of a head tagged at a modulus that passes
    `fieldModOk`. -/
theorem fieldModOk_of_outOp {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) (hls : ∀ l ∈ m.linked, linkSigOk l = true) :
    ∀ (o : NfOp), outOp m o = true → ∀ d ∈ opFieldDecls o, ∀ mm p,
      fieldTag? d.name = some (mm, p) → fieldModOk p = true := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
      intro h d hd mm p hmp
      have hdn : d.name = f := by
        simp only [opFieldDecls] at hd
        split at hd
        · split at hd <;>
            (obtain rfl := List.mem_singleton.mp hd; rfl)
        · split at hd
          · split at hd
            · obtain rfl := List.mem_singleton.mp hd
              rfl
            · cases hd
          · cases hd
      rw [hdn] at hmp
      simp only [outOp, NFFlattenTuples.opIsTuple, frontOp, crateCallOp, Bool.not_false,
        Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      obtain ⟨hS, hn⟩ := h
      have hL : m.linkSig f as = some r := by
        unfold crateSigOf at hS
        rw [hn] at hS
        exact hS
      rcases dom_of_linkSig hlk hls (fun _ _ => none) hL with ⟨hd', -⟩ | hb
      · obtain ⟨d', hd', hname, -⟩ := declared_iff.mp hd'
        have := (List.mem_filter.mp hd').2
        rw [hname, _root_.Hax.FieldTag.fieldHeadB_of_fieldTag? hmp] at this
        cases this
      · cases hp : fieldModOk p
        · rw [CatCrypt.Crypto.Hax.ImpToNF.hax64SigOf_eq_none_of_fieldModOk hmp hp] at hb
          cases hb
        · rfl
  | _ => intro _ d hd; simp [opFieldDecls] at hd

/-- Every declaration `fieldDeclsOf` of a program of `opsNB (outOp m)` is of a head tagged
    at a modulus that passes `fieldModOk`. -/
theorem fieldDeclsOf_modOk {m : CatCrypt.Crypto.Hax.HaxModule}
    (hlk : ∀ l ∈ m.linked, linkNameOk l.name = true) (hls : ∀ l ∈ m.linked, linkSigOk l = true)
    {W : List NfTy → Bool} {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : opsNB (outOp m) p W = true) :
    ∀ d ∈ fieldDeclsOf p, ∀ mm p', fieldTag? d.name = some (mm, p') → fieldModOk p' = true := by
  induction p with
  | ret => intro d hd; cases hd
  | var e k ih =>
      obtain ⟨o, _, _⟩ := e
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      exacts [fieldModOk_of_outOp hlk hls o hp.1 d hd, ih hp.2 d hd]
  | forLoop _ _ body k ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      exacts [ihb hp.1 d hd, ihk hp.2 d hd]
  | ifThenElse _ thn els k iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · rcases List.mem_append.mp hd with hd | hd
        exacts [iht hp.1.1 d hd, ihe hp.1.2 d hd]
      · exact ihk hp.2 d hd
  | whileLoop _ body k ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      exacts [ihb hp.1.2 d hd, ihk hp.2 d hd]
  | call => simp [opsNB] at hp

/-- The types of the entry of a layout are `tyU` types: `64`-bit words and arrays of
    `64`-bit words. -/
theorem tyU_entryCtx (σ : AbiLayout) : ∀ t ∈ entryCtx (NFToRoute.abiEntry σ), tyU t = true := by
  intro t ht
  simp only [entryCtx, NFToRoute.abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr,
    List.map_reverse, List.mem_reverse, List.map_map, List.mem_map] at ht
  obtain ⟨a, -, rfl⟩ := ht
  simp only [Function.comp_apply]
  cases a.kind <;> rfl

end Typed

/-! ## 5. The translation of a module lies in the domain -/

section Module

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF (impToNF hax64SigOf crateSigOf entryCtx entryEnv CrateFn)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody crateLib crateCallOp crateInline?_eq_some
  crateInlineOk_noCrateCall crateSigOf_append)
open CatCrypt.Crypto.Hax.NFToCatComplete (NBD)
open CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal (fieldTemplsB fieldTemplsB_of_fieldModOk)

/-- The source program `nfSrcProgC fs` is a program of `opsNB` at the operations of the front
    at the call typing `crateSigOf fs hax64SigOf`, whose exit-flag loops carry types of
    `whileCarryOkB`. -/
theorem nfSrcProgC_frontOp {fs : List CrateFn} {σ : AbiLayout} {te : _root_.Hax.TExpr}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (h : nfSrcProgC fs σ te = some q) :
    opsNB (frontOp (crateSigOf fs hax64SigOf)) q.2
      (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true := by
  unfold nfSrcProgC at h
  split at h
  · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    exact impToNF_prog_frontOpLoop _ _ _ _ o ho
  · cases h

/-- The body of an operation in the library of the callees `fs` at the typing `base` is a
    program of `opsNB` at the operations of the front at the call typing
    `crateSigOf fs base`. -/
theorem crateOp_frontOp (fs : List CrateFn) (base : String → List NfTy → Option NfTy) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o base = some b →
      opsNB (frontOp (crateSigOf fs base)) b = true := by
  intro o
  induction o with
  | call f as r =>
      intro b hb
      simp only [crateOp, Option.bind_eq_some_iff] at hb
      obtain ⟨c, -, hb⟩ := hb
      have hwf := CatCrypt.Crypto.Hax.NFInline.whileFoldFree_of_crateBody hb
      simp only [crateBody, hwf, ite_true, Option.bind_eq_some_iff] at hb
      obtain ⟨o', ho', hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        rw [opsNB_cast _ hty.1 (congrArg (fun x => [x]) hty.2)]
        exact impToNF_prog_frontOp _ _ _ _ o' ho' hwf
      · cases hb
  | named _ o ih => exact ih
  | _ => intro b hb; cases hb

/-- **The output of the front has the operations of the front that are no calls of the crate**,
    at a loop test `W` that the source programs of the front pass. -/
theorem haxToNF_opsNB_of {W : List NfTy → Bool}
    (hsrc : ∀ {fs : List CrateFn} {σ : AbiLayout} {te : _root_.Hax.TExpr}
      {q : Σ t : NfTy, NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]},
      nfSrcProgC fs σ te = some q → opsNB (frontOp (crateSigOf fs hax64SigOf)) q.2 W = true)
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} {t : NfTy}
    {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) :
    opsNB (fun o => frontOp (crateSigOf (m.prepared nfBody) m.linkSig) o
      && !crateCallOp (m.prepared nfBody) o) p W = true := by
  obtain ⟨-, -, -, p0, hp0, hinl⟩ := haxToNF_eq_some hh
  have h0 := hsrc hp0
  rw [crateSigOf_append] at h0
  unfold CatCrypt.Crypto.Hax.HaxModule.inline? at hinl
  obtain ⟨hok, hpe⟩ := crateInline?_eq_some hinl
  have h1 := opsNB_inlineIter (L := crateLib (m.prepared nfBody) m.linkSig)
    (fun o b hb => opsNB_loop_of_opsNB W b (crateOp_frontOp _ _ o b hb)) m.depth p0 h0
  have h2 := opsNB_and_allOps _ h1 (crateInlineOk_noCrateCall hok)
  rw [← hpe] at h2
  exact h2

/-- A program whose operations satisfy a test that marks no operation `ab` marks is free of
    the operations `ab` marks. -/
theorem abortFree_of_opsNB {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty]
    [HasWord64 d] [HasBoolBit d] {P ab : d.Op → Bool}
    (h : ∀ o, P o = true → ab o = false) {W : List d.Ty → Bool} :
    ∀ {Γ : Ctxt d} {ts : List d.Ty} (p : NFProg d Γ ts), opsNB P p W = true →
      NFProg.abortFree ab p = true
  | _, _, .ret _, _ => rfl
  | _, _, .var e k, hp => by
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.abortFree, h _ hp.1, Bool.not_false, Bool.true_and]
      exact abortFree_of_opsNB h k hp.2
  | _, _, .forLoop _ _ body k, hp => by
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.abortFree, abortFree_of_opsNB h body hp.1,
        abortFree_of_opsNB h k hp.2, Bool.and_self]
  | _, _, .ifThenElse _ thn els k, hp => by
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.abortFree, abortFree_of_opsNB h thn hp.1.1,
        abortFree_of_opsNB h els hp.1.2, abortFree_of_opsNB h k hp.2, Bool.and_self]
  | _, _, .whileLoop _ body k, hp => by
      simp only [opsNB, Bool.and_eq_true] at hp
      simp only [NFProg.abortFree, abortFree_of_opsNB h body hp.1.2,
        abortFree_of_opsNB h k hp.2, Bool.and_self]
  | _, _, .call .., hp => by simp [opsNB] at hp

/-- **The front of a module emits no aborting operation**: its operations satisfy `frontOp`
    (`haxToNF_opsNB_of`), which marks no abort. -/
theorem haxToNF_abortFree {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} {t : NfTy}
    {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) : NFProg.abortFree NfOp.isAbort p = true := by
  have h := haxToNF_opsNB_of (W := fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB)
    nfSrcProgC_frontOp hh
  refine abortFree_of_opsNB (fun o ho => ?_) p h
  cases o <;> first | rfl | simp [frontOp] at ho

/-- **The flattened output of the front has the operations `outOp m`**, at a loop test `W`
    that the source programs of the front pass and that accepts the flattening of every tuple
    it accepts. When `haxToNF σ m` returns the program `p` and the tuple flattening
    `flatSameStep` returns `q` on it, the program `q` is a program of `opsNB (outOp m)` at
    `W`. -/
theorem haxToNF_flatSame_opsNB_of {W : List NfTy → Bool}
    (hW : ∀ cs, W cs = true → W (NFFlattenTuples.flatCtx cs) = true)
    (hsrc : ∀ {fs : List CrateFn} {σ : AbiLayout} {te : _root_.Hax.TExpr}
      {q : Σ t : NfTy, NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]},
      nfSrcProgC fs σ te = some q → opsNB (frontOp (crateSigOf fs hax64SigOf)) q.2 W = true)
    {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} {t : NfTy}
    {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) {q : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : (flatSameStep (entryCtx (NFToRoute.abiEntry σ)) [t]).run p = some q) :
    opsNB (outOp m) q W = true := by
  have h2 := haxToNF_opsNB_of hsrc hh
  have hq' : flatSame _ = some q := hq
  exact opsNB_flatSame (P := fun o => frontOp (crateSigOf (m.prepared nfBody) m.linkSig) o
      && !crateCallOp (m.prepared nfBody) o) hW hq'
    (opsNB_mono_loop (fun o h => Bool.or_eq_true_iff.mpr (Or.inr h)) (fun _ h => h) _ h2)

/-- **The flattened output of the front has the operations `outOp m`, and its exit-flag loops
    carry types of `whileCarryOkB`.** When `haxToNF σ m` returns the program `p` and the tuple
    flattening `flatSameStep` returns `q` on it, the program `q` is a program of
    `opsNB (outOp m)` at the loop test `fun cs => cs.all whileCarryOkB`. -/
theorem haxToNF_flatSame_opsNBLoop {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    {t : NfTy} {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) {q : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : (flatSameStep (entryCtx (NFToRoute.abiEntry σ)) [t]).run p = some q) :
    opsNB (outOp m) q (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true :=
  haxToNF_flatSame_opsNB_of whileCarry_flatCtx nfSrcProgC_frontOp hh hq

/-- **The front of a module returns programs whose dead-code-eliminated flattening lies in
    the domain of the translation with declared calls.** When `haxToNF σ m` returns the
    program `p` and the tuple flattening `flatSameStep` returns `q` on it, the program
    `dce q` satisfies `NBD` at the declarations `fieldDeclsFor (linkedDecls m bi)` of its
    calls, at every table `bi`, and every one of its tagged calls has a template
    (`fieldTemplsB`). -/
theorem haxToNF_imp_NBD {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} {t : NfTy}
    {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) {q : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hq : (flatSameStep (entryCtx (NFToRoute.abiEntry σ)) [t]).run p = some q)
    (bi : _root_.Hax.Builtins) :
    NBD (fieldDeclsFor (linkedDecls m bi) (NFProg.dce q)) (NFProg.dce q) = true ∧
      fieldTemplsB (NFProg.dce q) = true := by
  obtain ⟨-, -, hlk, -, -, -⟩ := haxToNF_eq_some hh
  obtain ⟨hls, -⟩ := haxToNF_eq_some_sig hh
  have h4 : opsNB (outOp m) (NFProg.dce q)
      (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true :=
    opsNB_dce _ (haxToNF_flatSame_opsNBLoop hh hq)
  refine ⟨(NBDL_of_outOp hlk hls bi (fun d hd => List.mem_append_left _ hd) (NFProg.dce q) []
    (tyU_entryCtx σ) h4 (fun d hd => List.mem_append_right _ hd)).1, ?_⟩
  exact fieldTemplsB_of_fieldModOk _ (fieldDeclsOf_modOk hlk hls _ h4)

/-! ### The output of the front passes tuple flattening -/

open CatCrypt.Crypto.SecureCompilation.VIR.NFFlattenTuples (NoTuple FlatOk opFlatOk tyIsTuple
  opIsTuple)
open CatCrypt.Crypto.Hax.ImpToNF (hax64NFWordTy fieldElemTy hax64ScalarSig hax64SigOfArr selTy
  argTysFit)
open CatCrypt.Crypto.Hax.NFToCatComplete (ilitOk)

/-- A type that `hax64NFWordTy` accepts is no tuple type. -/
theorem tyIsTuple_of_hax64NFWordTy {t : NfTy} (h : hax64NFWordTy t = true) :
    tyIsTuple t = false := by
  cases t <;> simp_all [hax64NFWordTy, tyIsTuple]

/-- A type of words and word arrays is no tuple type. -/
theorem tyIsTuple_of_wordArrTy {t : NfTy} (h : CatCrypt.Crypto.Hax.NFToCat.wordArrTy t = true) :
    tyIsTuple t = false := by
  unfold CatCrypt.Crypto.Hax.NFToCat.wordArrTy at h
  split at h
  · rfl
  · exact tyIsTuple_of_hax64NFWordTy h

/-- The type of a field element is no tuple type. -/
theorem tyIsTuple_fieldElemTy (p : Nat) : tyIsTuple (fieldElemTy p) = false := by
  unfold fieldElemTy
  split <;> rfl

/-- **A call of the `u64` typing has no tuple type**: neither an argument type nor the result
    type of a call `hax64SigOf` types is a tuple type. -/
theorem noTuple_of_hax64SigOf {f : String} {as : List NfTy} {r : NfTy}
    (h : hax64SigOf f as = some r) : NoTuple as ∧ tyIsTuple r = false := by
  unfold hax64SigOf at h
  split at h
  · cases h
    rename_i hF
    obtain ⟨mm, p, -, has, hr⟩ := CatCrypt.Crypto.Hax.ImpToNF.fieldTagSig_some hF
    subst has hr
    refine ⟨?_, tyIsTuple_fieldElemTy p⟩
    unfold _root_.Hax.FieldTag.FieldMethod.sigAt
    split <;> simp [NoTuple, tyIsTuple_fieldElemTy p]
  · split at h
    · cases h
      rename_i hS
      rcases as with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨_, _⟩⟩⟩⟩
      · simp [hax64ScalarSig] at hS
      · simp only [hax64ScalarSig, Bool.and_eq_true] at hS
        split at hS
        · rename_i hu
          cases hS
          simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hu.1]
          decide
        · split at hS
          · rename_i hn
            cases hS
            obtain ⟨rfl, -⟩ := hn
            decide
          · cases hS
      · simp only [hax64ScalarSig, Bool.and_eq_true] at hS
        split at hS
        · rename_i hab
          split at hS
          · cases hS
            simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hab.1,
              tyIsTuple_of_hax64NFWordTy hab.2]
            decide
          · split at hS
            · cases hS
              simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hab.1,
                tyIsTuple_of_hax64NFWordTy hab.2]
              decide
            · cases hS
        · split at hS
          · rename_i hs
            cases hS
            obtain ⟨rfl, rfl, -⟩ := hs
            decide
          · cases hS
      · simp only [hax64ScalarSig] at hS
        split at hS
        · cases hS
          rename_i hs
          obtain ⟨-, rfl, hb, hc⟩ := hs
          refine ⟨by simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hb,
            tyIsTuple_of_hax64NFWordTy hc]; decide, ?_⟩
          unfold selTy
          split <;> rfl
        · cases hS
      · simp [hax64ScalarSig] at hS
    · split at h
      · rename_i hti
        split at h
        · cases h
          rename_i hw
          simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hw]
          decide
        · cases h
      · split at h
        · cases h
          rename_i hti
          simp only [Bool.and_eq_true] at hti
          simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hti.1,
            tyIsTuple_of_hax64NFWordTy hti.2]
          decide
        · cases h
      · split at h
        · cases h
          rename_i hw
          simp [NoTuple, tyIsTuple_of_hax64NFWordTy hw]
        · cases h
      · unfold hax64SigOfArr at h
        split at h
        · split at h
          · cases h
            rename_i hti
            simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hti]
            exact ⟨rfl, rfl⟩
          · cases h
        · split at h
          · cases h
            rename_i hti
            simp only [NoTuple, List.all_cons, List.all_nil, tyIsTuple_of_hax64NFWordTy hti]
            exact ⟨rfl, rfl⟩
          · cases h
        · split at h
          · cases h
            exact ⟨rfl, rfl⟩
          · cases h
        · split at h
          · rename_i hrep
            cases h
            obtain ⟨k, rfl⟩ : ∃ k, as = List.replicate k (.word 64) := ⟨_, hrep⟩
            refine ⟨?_, rfl⟩
            simp [NoTuple, tyIsTuple]
          · cases h
        · cases h

/-- **A call of the typing of the linked functions has no tuple type**: neither an argument
    type nor the result type of a call `m.linkSig` types is a tuple type. -/
theorem noTuple_of_linkSig {m : CatCrypt.Crypto.Hax.HaxModule}
    (hls : ∀ l ∈ m.linked, linkSigOk l = true) {f : String} {as : List NfTy} {r : NfTy}
    (h : m.linkSig f as = some r) : NoTuple as ∧ tyIsTuple r = false := by
  unfold CatCrypt.Crypto.Hax.HaxModule.linkSig crateSigOf at h
  split at h
  · rename_i c hc
    split at h
    · rename_i hfit
      cases h
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hc)
      have hsig := hls l hl
      simp only [linkSigOk, Bool.and_eq_true, List.all_eq_true] at hsig
      have hfit' : argTysFit (l.params.map (·.2)) as = true := hfit
      obtain ⟨-, hall⟩ := mem_sigVariants (fun q hq => by
        obtain ⟨⟨x, q'⟩, hx, rfl⟩ := List.mem_map.mp hq
        exact hsig.1 (x, q') hx) hfit'
      refine ⟨?_, ?_⟩
      · simp only [NoTuple, List.all_eq_true, Bool.not_eq_true'] at hall ⊢
        exact fun a ha => tyIsTuple_of_wordArrTy (hall a ha)
      · rcases linkResOk_iff.mp hsig.2 with h | ⟨n, h⟩ <;>
          simp [CatCrypt.Crypto.Hax.LinkedFn.callee, h, tyIsTuple]
    · cases h
  · exact noTuple_of_hax64SigOf h

/-- **An operation of the front at the call typing of a module, other than a call of a
    function of the module, is accepted by tuple flattening** (`opFlatOk`). -/
theorem opFlatOk_of_frontOp {m : CatCrypt.Crypto.Hax.HaxModule}
    (hls : ∀ l ∈ m.linked, linkSigOk l = true) :
    ∀ o : NfOp, (frontOp (crateSigOf (m.prepared nfBody) m.linkSig) o &&
      !crateCallOp (m.prepared nfBody) o) = true → opFlatOk o := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
      intro h
      simp only [frontOp, crateCallOp, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      obtain ⟨hS, hn⟩ := h
      have hL : m.linkSig f as = some r := by
        unfold crateSigOf at hS
        rw [hn] at hS
        exact hS
      exact Or.inr (noTuple_of_linkSig hls hL)
  | ilit t v =>
      intro h
      simp only [frontOp, crateCallOp, Bool.not_false, Bool.and_true, ilitOk,
        Bool.and_eq_true, Bool.or_eq_true] at h
      refine Or.inr ⟨rfl, ?_⟩
      rcases h.2 with h | h
      · exact tyIsTuple_of_hax64NFWordTy h
      · revert h
        cases t <;> simp [tyIsTuple]
  | trip t =>
      intro h
      simp only [frontOp, crateCallOp, Bool.not_false, Bool.and_true] at h
      refine Or.inr ⟨?_, rfl⟩
      revert h
      cases t <;> simp [tripBoundTy, NoTuple, tyIsTuple]
  | boundInt t =>
      intro h
      simp only [frontOp, crateCallOp, Bool.not_false, Bool.and_true] at h
      refine Or.inr ⟨?_, rfl⟩
      revert h
      cases t <;> simp [CatCrypt.Crypto.Hax.ImpToNF.loTyOk, NoTuple, tyIsTuple]
  | bin o w => intro _; exact Or.inr ⟨by simp [NoTuple, tyIsTuple], rfl⟩
  | constBit => intro _; exact Or.inr ⟨rfl, rfl⟩
  | constUnit => intro _; exact Or.inl rfl
  | ctr => intro _; exact Or.inr ⟨rfl, rfl⟩
  | tnilV => intro _; exact Or.inl rfl
  | tconsV => intro _; exact Or.inl rfl
  | thead => intro _; exact Or.inl rfl
  | ttail => intro _; exact Or.inl rfl
  | arrRepeat n t =>
      intro h
      simp only [frontOp, crateCallOp, Bool.not_false, Bool.and_true, decide_eq_true_eq] at h
      subst h
      exact Or.inr ⟨by simp [NoTuple, tyIsTuple], rfl⟩
  | _ => intro h; simp [frontOp] at h

/-- A program every operation of which satisfies `P` is covered by every predicate on
    operations that `P` implies. -/
theorem covered_of_opsNB {P : NfOp → Bool} {G : NfOp → Prop} (hPG : ∀ o, P o = true → G o)
    {W : List NfTy → Bool} {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : opsNB P p W = true) : p.Covered (fun e => G e.op) := by
  induction p with
  | ret => trivial
  | var e k ih =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ⟨hPG _ hp.1, ih hp.2⟩
  | forLoop _ _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ⟨ihb hp.1, ihk hp.2⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ⟨iht hp.1.1, ihe hp.1.2, ihk hp.2⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [opsNB, Bool.and_eq_true] at hp
      exact ⟨ihb hp.1.2, ihk hp.2⟩
  | call => simp [opsNB] at hp

/-- The entry of a layout binds no tuple type. -/
theorem noTuple_entryCtx (σ : AbiLayout) : NoTuple (entryCtx (NFToRoute.abiEntry σ)) := by
  simp only [NoTuple, List.all_eq_true, Bool.not_eq_true']
  intro t ht
  simp only [entryCtx, NFToRoute.abiEntry, CatCrypt.Crypto.Hax.NFToCat.abiParamsArr,
    List.map_reverse, List.mem_reverse, List.map_map, List.mem_map] at ht
  obtain ⟨a, -, rfl⟩ := ht
  simp only [Function.comp_apply]
  cases a.kind <;> rfl

/-- **Tuple flattening succeeds on the output of the front**: on a program `haxToNF σ m`
    returns, `flatSameStep` returns a program. -/
theorem haxToNF_flatSame_isSome {σ : AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule} {t : NfTy}
    {p : NFProg nfDialect (entryCtx (NFToRoute.abiEntry σ)) [t]}
    (hh : haxToNF σ m = some ⟨t, p⟩) :
    ((flatSameStep (entryCtx (NFToRoute.abiEntry σ)) [t]).run p).isSome = true := by
  obtain ⟨-, -, -, p0, hp0, hinl⟩ := haxToNF_eq_some hh
  obtain ⟨hls, -⟩ := haxToNF_eq_some_sig hh
  have hres : entryResOk t = true := haxToNF_eq_some_res hh
  have h0 := nfSrcProgC_frontOp hp0
  rw [crateSigOf_append] at h0
  unfold CatCrypt.Crypto.Hax.HaxModule.inline? at hinl
  obtain ⟨hok, hpe⟩ := crateInline?_eq_some hinl
  have h1 := opsNB_inlineIter (L := crateLib (m.prepared nfBody) m.linkSig)
    (fun o b hb => opsNB_loop_of_opsNB _ b (crateOp_frontOp _ _ o b hb)) m.depth p0 h0
  have h2 := opsNB_and_allOps _ h1 (crateInlineOk_noCrateCall hok)
  rw [← hpe] at h2
  have ht : NoTuple [t] := by
    simp only [NoTuple, List.all_cons, List.all_nil, Bool.and_true, Bool.not_eq_true']
    revert hres
    cases t <;> simp [entryResOk, outTyB, tyIsTuple]
  exact flatSame_isSome p (noTuple_entryCtx σ) ht
    (covered_of_opsNB (opFlatOk_of_frontOp hls) p h2)

end Module

end CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete

/-- **A module the translation refuses nothing on has its programs in the domain of the
    translation with declared calls.** When `m.refusal? σ` is `none`, `haxToNF σ m`
    returns a program `p`, and on every program `q` the tuple flattening `flatSameStep`
    returns on `p`, the program `dce q` satisfies `NBD` at the declarations
    `fieldDeclsFor (linkedDecls m bi)` of its calls, at every table `bi`, and every one of its
    tagged calls has a template (`fieldTemplsB`). -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_NBD
    {σ : CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ q, (CatCrypt.Crypto.SecureCompilation.Haxc.flatSameStep _ [t]).run p = some q →
        ∀ bi, CatCrypt.Crypto.Hax.NFToCatComplete.NBD
            (CatCrypt.Crypto.SecureCompilation.Haxc.fieldDeclsFor
              (CatCrypt.Crypto.SecureCompilation.Haxc.linkedDecls m bi)
              (CatCrypt.Crypto.SecureCompilation.VIR.NFProg.dce q))
            (CatCrypt.Crypto.SecureCompilation.VIR.NFProg.dce q) = true ∧
          CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal.fieldTemplsB
            (CatCrypt.Crypto.SecureCompilation.VIR.NFProg.dce q) = true := by
  obtain ⟨⟨t, p⟩, hp⟩ := Option.isSome_iff_exists.mp
    ((CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_iff σ m).mp hr)
  exact ⟨t, p, hp, fun q hq bi =>
    CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_imp_NBD hp hq bi⟩

/-- **A module the translation refuses nothing on runs through the chain at every result type
    the chain reads back.** When `m.refusal? σ` is `none`, `haxToNF σ m` returns a program
    `p` at a result type `t`, and when `t` passes `outTyB` (a word, an integer or an array of
    words), the chain `extChain` at the declarations `linkedDecls m bi` returns a program on
    `p`, at every table `bi`; `compileA` runs the chain at the table `Hax.hax64WExit`
    (`haxEntry.decls`). -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_extChain_isSome_of_outTyB
    {σ : CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF σ m = some ⟨t, p⟩ ∧
      (CatCrypt.Crypto.SecureCompilation.Haxc.outTyB t = true → ∀ bi,
        ((CatCrypt.Crypto.SecureCompilation.Haxc.extChain
          (CatCrypt.Crypto.SecureCompilation.Haxc.linkedDecls m bi) _ t).run p).isSome = true) := by
  obtain ⟨⟨t, p⟩, hp⟩ := Option.isSome_iff_exists.mp
    ((CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_iff σ m).mp hr)
  refine ⟨t, p, hp, fun ht bi => ?_⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
    (CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_flatSame_isSome hp)
  obtain ⟨hN, hT⟩ := CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_imp_NBD hp hq bi
  refine CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal.extChain_isSome_of_NBD _ ?_ ht hN hT
  rw [CatCrypt.Crypto.SecureCompilation.VIR.NFProg.abortElim_of_abortFree _ p
    (CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete.haxToNF_abortFree hp)]
  exact hq

/-- **A module the translation refuses nothing on runs through the chain.** When
    `m.refusal? σ` is `none`, `haxToNF σ m` returns a program `p` at a result type `t`, and
    the chain `extChain` at the declarations `linkedDecls m bi` returns a program on `p`, at
    every table `bi`. -/
theorem CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_extChain_isSome
    {σ : CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout} {m : CatCrypt.Crypto.Hax.HaxModule}
    (hr : m.refusal? σ = none) :
    ∃ (t : _) (p : _), CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF σ m = some ⟨t, p⟩ ∧
      ∀ bi, ((CatCrypt.Crypto.SecureCompilation.Haxc.extChain
          (CatCrypt.Crypto.SecureCompilation.Haxc.linkedDecls m bi) _ t).run p).isSome = true := by
  obtain ⟨t, p, hp, h⟩ :=
    CatCrypt.Crypto.Hax.HaxModule.refusal?_eq_none_imp_extChain_isSome_of_outTyB hr
  exact ⟨t, p, hp, h (CatCrypt.Crypto.SecureCompilation.Haxc.haxToNF_eq_some_res hp)⟩
