/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCatLeak
public import CatCrypt.Crypto.Hax.NFToCatImages

/-!
# Calls of declared external procedures in the translation to `catCryptDialect`

`nfToCatExt D` is the translation `nfToCat` with a list `D` of declared external procedures
(`ExtDecl`). A binding whose operation is the leaf call `NfOp.call f as r` is translated by
`catOp` when `catOp` accepts it; otherwise, when `D` declares `f` at the signature `as → r`
and every type of the signature is a type whose values encode as integers or an array of
`64`-bit words (`ExtDecl.wordSig`), the binding is the node `NFProg.call f` of
`catCryptDialect` at the signature `as.map catTy → [catTy r]`, on the variables of its
arguments. Each distinct literal value among the arguments is bound by `bvConst` in front of
the node (`pinAll`), as `catCallRd0` does for an operation (`pinRes`). Every other program is
translated as by `nfToCat`.

The value of a translated program is stated at an explicit call environment `E` of
`catCryptDialect` (`NFProg.denoteAt`). The hypothesis `ExtAgree bi E D` relates the three
readings of a declared name: the builtin table of the source answers it by the function
`sem` of the declaration (`ExtDecl.InTable`), and `E` answers it, on arguments related by
`VRel`, by a value related to the value of `sem` (`ExtDecl.ImplementedBy`).

## Main definitions

* `ExtDecl`, `wordArrTy`, `wordArrSig`, `ExtDecl.wordSig`, `declared` — a declared external
  procedure, the types and signatures of words and word arrays, and the test that a list
  declares a name at a signature.
* `extArgs`, `emitCall`, `emitOp`, `nfToCatExt` — the readings of the arguments of a declared
  call, the node of a call, the translation of a binding, and of a program.
* `ExtDecl.InTable`, `ExtDecl.ImplementedBy`, `ExtAgree` — the agreement of the builtin table,
  the declarations and the call environment of the target.
* `NFExtSound` — the simulation statement at an explicit call environment.

## Main results

* `nfToCatExt_nil` — at no declarations the translation is `nfToCat`.
* `nfToCatExt_sound` — under `SubTable bi` and `ExtAgree bi E D`, a translated program
  denotes at `E` values related to the values of the source program.
* `nfToCat_of_callFree` — a translation without `call` is the translation `nfToCat` gives.
* `nfToCatExt_calls` — every call of a translated program is a declared one, at the mapped
  signature of its declaration, a signature of `64`-bit words and memrefs.
* `nfToCatExt_opsHaveImages`, `isSome_map?_aegraphOptNF_nfToCatExt` — every operation of a
  translated program has an image in the Jasmin dialect, and the conversion is defined on
  its e-graph pass.
* `nfToCatExt_leak` — the leakage transformer on the translations without `call`.
* `nfToCatExt_leakD` — the leakage transformer at a call environment, for declarations of
  no name `index` or `array_update`: the events of the translation are the source events
  without the variable-time leaf calls of tagged field heads and of declared names
  (`stripDecl D`).
* `nfToCatExt_leakC` — the same at declarations of tagged field heads, at which
  `stripDecl D` is `stripField`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFToCatImages
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat
open Ctxt (Var Valuation)

/-! ## 1. Declarations -/

/-- A declared external procedure: its name, the types of its arguments and of its result
    in `nfDialect`, and its function on values. -/
structure ExtDecl where
  /-- The name of the procedure. -/
  name : String
  /-- The types of the arguments. -/
  args : List NfTy
  /-- The type of the result. -/
  ret : NfTy
  /-- The function of the procedure on values; `none` where the procedure fails. -/
  sem : HVector NfTy.denote args → Option ret.denote

/-- The types of words and word arrays: a type whose values encode as integers (`int` or the
    `64`-bit word), which `catTy` maps to `sword 64`, and an array of `64`-bit words, which
    `catTy` maps to a memref of its length. -/
def wordArrTy : NfTy → Bool
  | .arr _ (.word 64) => true
  | t => ImpToNF.hax64NFWordTy t

/-- The signatures of words and word arrays: every argument type and the result type pass
    `wordArrTy`. -/
def wordArrSig (as : List NfTy) (r : NfTy) : Bool :=
  as.all wordArrTy && wordArrTy r

/-- The signatures of words: the signature of the declaration passes `wordArrSig`. -/
def ExtDecl.wordSig (d : ExtDecl) : Bool :=
  wordArrSig d.args d.ret

/-- The declaration `d` is of the name `f` at the signature `as → r`, a signature of
    words. -/
def ExtDecl.isAt (d : ExtDecl) (f : String) (as : List NfTy) (r : NfTy) : Bool :=
  decide (d.name = f) && decide (d.args = as) && decide (d.ret = r) && d.wordSig

/-- The list `D` declares the name `f` at the signature `as → r`, a signature of words. -/
def declared (D : List ExtDecl) (f : String) (as : List NfTy) (r : NfTy) : Bool :=
  D.any fun d => d.isAt f as r

/-- A declaration found by `declared`. -/
theorem declared_iff {D : List ExtDecl} {f : String} {as : List NfTy} {r : NfTy} :
    declared D f as r = true ↔
      ∃ d ∈ D, d.name = f ∧ d.args = as ∧ d.ret = r ∧ d.wordSig = true := by
  simp [declared, ExtDecl.isAt, and_assoc]

/-- A type of words or word arrays maps to `sword 64` or to a memref. -/
theorem catTy_of_wordArrTy {t : NfTy} (h : wordArrTy t = true) :
    catTy t = CryptoTy.sword 64 ∨ ∃ n, catTy t = CryptoTy.memref n := by
  cases t with
  | arr n _ => exact Or.inr ⟨n, rfl⟩
  | word w => exact Or.inl (catTy_of_wordTy h)
  | int => exact Or.inl rfl
  | _ => simp [wordArrTy, ImpToNF.hax64NFWordTy] at h

/-- The mapped signature of a declaration of words is a signature of `64`-bit words and
    memrefs. -/
theorem ExtDecl.wordSig_catTy {d : ExtDecl} (h : d.wordSig = true) :
    (∀ t ∈ d.args.map catTy, t = CryptoTy.sword 64 ∨ ∃ n, t = CryptoTy.memref n) ∧
      (catTy d.ret = CryptoTy.sword 64 ∨ ∃ n, catTy d.ret = CryptoTy.memref n) := by
  simp only [ExtDecl.wordSig, wordArrSig, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun t ht => ?_, catTy_of_wordArrTy h.2⟩
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact catTy_of_wordArrTy (h.1 s hs)

/-! ## 2. The translation -/

/-- The name, the argument types and the readings of the arguments of a call that `D`
    declares, under the source names of `named`; `none` on every other operation. -/
def extArgs (D : List ExtDecl) {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig →
      Option (String × (as : List NfTy) × HVector (fun t => Rd Δ t) as)
  | .named _ op, args => extArgs D σ op args
  | .call f as r, args => if declared D f as r = true then some (f, ⟨as, σ.rds args⟩) else none
  | _, _ => none

/-- A call `extArgs` returns is of a declaration of `D`, at its signature, a signature of
    words. -/
theorem extArgs_declared {D : List ExtDecl} {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (f : String) (as : List NfTy)
      (rs : HVector (fun t => Rd Δ t) as), extArgs D σ op args = some (f, ⟨as, rs⟩) →
      ∃ d ∈ D, f = d.name ∧ as = d.args ∧ op.ret = d.ret ∧ d.wordSig = true := by
  intro op
  induction op with
  | named n op ih =>
      intro args f as rs h
      exact ih args f as rs h
  | call g bs r =>
      intro args f as rs h
      unfold extArgs at h
      split at h
      · rename_i hdec
        cases h
        obtain ⟨d, hd, hn, ha, hr, hw⟩ := declared_iff.mp hdec
        exact ⟨d, hd, hn.symm, ha.symm, hr.symm, hw⟩
      · cases h
  | _ =>
      intro args f as rs h
      cases h

/-- The node of a call of `f` on the readings `rs`, binding a result of the type `s`,
    followed by the translation `cont` of the continuation: the node on the variables of the
    readings, behind the `bvConst` bindings `pinAll` gives the literals among them. -/
def emitCall {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    {Δ : Ctxt catCryptDialect} (f : String) (as : List NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (σ : TRd Γ Δ) :
    Option (NFProg catCryptDialect Δ (ts.map catTy)) :=
  pinAll (fun σ' ws => (cont σ'.lift).map fun k' => NFProg.call (rs := [catTy s]) f ws k')
    σ rs

/-- The translation of a binding of the operation `op`, followed by the translation `cont`
    of the continuation: the bindings `emitRes` gives for `catOp`, and, on an operation
    `catOp` refuses, the node `emitCall` of a call that `D` declares. -/
def emitOp (D : List ExtDecl) {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (op : NfOp) (h : op.ret = s)
    (args : HVector (fun t => Var Γ t) op.sig) :
    Option (NFProg catCryptDialect Δ (ts.map catTy)) :=
  match catOp σ op args with
  | some res => emitRes cont h res σ
  | none => (extArgs D σ op args).bind fun c => emitCall cont c.1 c.2.1 c.2.2 σ

/-- **The translation of a program with the declared external procedures `D`**: the
    translation `nfToCat`, with a binding translated by `emitOp`. `none` on an exit-flag
    loop and on the node `call` of the source. -/
def nfToCatExt (D : List ExtDecl) : {Γ : Ctxt nfDialect} → {Δ : Ctxt catCryptDialect} →
    {ts : List NfTy} → NFProg nfDialect Γ ts → TRd Γ Δ →
      Option (NFProg catCryptDialect Δ (ts.map catTy))
  | _, _, _, .ret vs, σ => pinAll (fun _ ws => some (.ret ws)) σ (σ.rds vs)
  | _, _, _, .var ⟨op, h, args⟩ k, σ => emitOp D (fun σ' => nfToCatExt D k σ') σ op h args
  | _, _, _, .forLoop (cs := cs) count inits body k, σ =>
      pinAll (ts := .word 64 :: cs)
        (fun σ' ws =>
          (nfToCatExt D body (TRd.liftApp cs (TRd.lift σ'))).bind fun body' =>
            (nfToCatExt D k (TRd.liftApp cs σ')).map fun k' =>
              .forLoop (cs := cs.map catTy) ws.head ws.tail body' k')
        σ (.cons (σ count) (σ.rds inits))
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, σ =>
      match σ cond with
      | .var c =>
          (nfToCatExt D thn σ).bind fun thn' =>
            (nfToCatExt D els σ).bind fun els' =>
              (nfToCatExt D k (TRd.liftApp rs σ)).map fun k' =>
                .ifThenElse (rs := rs.map catTy) c thn' els' k'
      | .lit _ _ => none
  | _, _, _, .whileLoop .., _ => none
  | _, _, _, .call .., _ => none

/-! ## 3. The instance at no declarations -/

/-- No call is declared by the empty list. -/
theorem extArgs_nil {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig), extArgs [] σ op args = none := by
  intro op
  induction op with
  | named n op ih =>
      intro args
      exact ih args
  | _ =>
      intro args
      rfl

/-- **At no declarations the translation is `nfToCat`.** -/
theorem nfToCatExt_nil {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), nfToCatExt [] p σ = nfToCat p σ := by
  induction p with
  | ret vs =>
      intro Δ σ
      rfl
  | var e k ih =>
      intro Δ σ
      obtain ⟨op, rfl, args⟩ := e
      change emitOp [] (fun σ' => nfToCatExt [] k σ') σ op rfl args =
        (catOp σ op args).bind fun res => emitRes (fun σ' => nfToCat k σ') rfl res σ
      unfold emitOp
      cases catOp σ op args with
      | some res => simp only [ih, Option.bind_some]
      | none =>
          rw [extArgs_nil]
          rfl
  | forLoop count inits body k ihb ihk =>
      intro Δ σ
      simp only [nfToCatExt, nfToCat, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ
      simp only [nfToCatExt, nfToCat, iht, ihe, ihk]
      cases σ cond <;> rfl
  | whileLoop inits body k _ _ =>
      intro Δ σ
      rfl
  | call f args k _ =>
      intro Δ σ
      rfl

/-! ## 4. The value at an explicit call environment -/

/-- A let-binding denotes, at the call environment `E`, its continuation at the extended
    valuation. -/
theorem denoteAt_var (E : CallEnv catCryptDialect) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    {ts : List CryptoTy} (e : Expr catCryptDialect Γ t)
    (k : NFProg catCryptDialect (t :: Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.var e k).denoteAt E fuel V =
      e.denoteM V >>= fun x => k.denoteAt E fuel (V.extend x) := rfl

/-- A call denotes, at the call environment `E`, the callee of `E` at the looked-up
    arguments, then its continuation at the results. -/
theorem denoteAt_callNode (E : CallEnv catCryptDialect) {Γ : Ctxt catCryptDialect}
    {as rs ts : List CryptoTy} (f : String) (args : HVector (fun t => Var Γ t) as)
    (k : NFProg catCryptDialect (rs ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.call f args k).denoteAt E fuel V =
      (E.call f as rs (Expr.lookupArgs args V)).bind fun r =>
        k.denoteAt E fuel (hvAppend r V) := rfl

/-- A counted loop denotes, at the call environment `E`, the `List.range` fold of its
    body, then its continuation at the final tuple. -/
theorem denoteAt_forLoop (E : CallEnv catCryptDialect) {Γ : Ctxt catCryptDialect}
    {cs ts : List CryptoTy} (count : Var Γ (HasWord64.word (d := catCryptDialect)))
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg catCryptDialect (cs ++ HasWord64.word (d := catCryptDialect) :: Γ) cs)
    (k : NFProg catCryptDialect (cs ++ Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.forLoop count inits body k).denoteAt E fuel V =
      (List.range (HasWord64.toNat (d := catCryptDialect) (count.lookup V))).foldlM
          (fun acc i => body.denoteAt E fuel
            (hvAppend acc (.cons (HasWord64.ofNat (d := catCryptDialect) i) V)))
          (Expr.lookupArgs inits V) >>= fun acc =>
        k.denoteAt E fuel (hvAppend acc V) := rfl

/-- A branch denotes, at the call environment `E`, the arm its bit selects, then its
    continuation at the results. -/
theorem denoteAt_ifThenElse (E : CallEnv catCryptDialect) {Γ : Ctxt catCryptDialect}
    {rs ts : List CryptoTy} (cond : Var Γ (HasBitType.bit (d := catCryptDialect)))
    (thn els : NFProg catCryptDialect Γ rs) (k : NFProg catCryptDialect (rs ++ Γ) ts)
    (fuel : Nat) (V : Valuation Γ) :
    (NFProg.ifThenElse cond thn els k).denoteAt E fuel V =
      (if HasBoolBit.toBool (d := catCryptDialect) (cond.lookup V) then thn.denoteAt E fuel V
        else els.denoteAt E fuel V) >>= fun r => k.denoteAt E fuel (hvAppend r V) := rfl

/-- The builtin table `bi` answers the name of the declaration `d`, at its signature, by
    its function `sem`. -/
def ExtDecl.InTable (bi : _root_.Hax.Builtins) (d : ExtDecl) : Prop :=
  ∀ xs : HVector NfTy.denote d.args,
    (ImpToNF.tableOf bi).call d.name d.args d.ret xs = d.sem xs

/-- The call environment `E` of the target answers the name of the declaration `d`, at the
    mapped signature, by the image of `sem` under `VRel`: on arguments related to `xs`, one
    result, related to the value of `sem` on `xs`. -/
def ExtDecl.ImplementedBy (E : CallEnv catCryptDialect) (d : ExtDecl) : Prop :=
  ∀ (xs : Valuation (d := nfDialect) d.args)
    (ws : Valuation (d := catCryptDialect) (d.args.map catTy)) (y : d.ret.denote),
    VRelL d.args xs ws → d.sem xs = some y →
    ∃ y' : (catTy d.ret).denote,
      E.call d.name (d.args.map catTy) [catTy d.ret] ws = some (HVector.cons y' .nil) ∧
        VRel d.ret y y'

/-- **The agreement of the environments on the declarations `D`**: the builtin table of the
    source answers every declared name by the function of its declaration, and the call
    environment of the target implements it. -/
def ExtAgree (bi : _root_.Hax.Builtins) (E : CallEnv catCryptDialect) (D : List ExtDecl) :
    Prop :=
  ∀ d ∈ D, d.InTable bi ∧ d.ImplementedBy E

/-- Every table and every call environment agree on no declarations. -/
theorem extAgree_nil (bi : _root_.Hax.Builtins) (E : CallEnv catCryptDialect) :
    ExtAgree bi E [] := fun _ h => absurd h List.not_mem_nil

/-- **A declared call simulates.** Under `ExtAgree bi E D`, the arguments of a call
    `extArgs` returns are read by its readings, and `E` answers the name, on every vector
    related to the arguments, by one result related to the value of the operation. -/
theorem extArgs_sound {bi : _root_.Hax.Builtins} {E : CallEnv catCryptDialect}
    {D : List ExtDecl} (hD : ExtAgree bi E D) {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) {V : Valuation Γ} {W : Valuation Δ} (hag : σ.Agree V W) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (f : String) (as : List NfTy)
      (rs : HVector (fun t => Rd Δ t) as) (y : op.ret.denote),
      extArgs D σ op args = some (f, ⟨as, rs⟩) →
      nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V) = some y →
      ∃ xs : Valuation (d := nfDialect) as, RdRelL W as xs rs ∧
        ∀ ws : Valuation (d := catCryptDialect) (as.map catTy), VRelL as xs ws →
          ∃ y' : (catTy op.ret).denote,
            E.call f (as.map catTy) [catTy op.ret] ws = some (HVector.cons y' .nil) ∧
              VRel op.ret y y' := by
  intro op
  induction op with
  | named n op ih =>
      intro args f as rs y h hy
      exact ih args f as rs y h hy
  | call g bs r =>
      intro args f as rs y h hy
      unfold extArgs at h
      split at h
      · rename_i hdec
        cases h
        obtain ⟨d, hd, hn, ha, hr, -⟩ := declared_iff.mp hdec
        obtain ⟨hT, hI⟩ := hD d hd
        obtain ⟨n, a, r', sem⟩ := d
        dsimp only at hn ha hr
        subst hn ha hr
        refine ⟨Expr.lookupArgs args V, TRd.rdRelL_rds hag args, fun ws hws => ?_⟩
        exact hI _ ws y hws ((hT _).symm.trans hy)
      · cases h
  | _ =>
      intro args f as rs y h hy
      cases h

/-- **The bindings of a translated operation simulate at a call environment.** The
    statement `emitRes_sound` with the translated programs denoted at `E`. -/
theorem emitRes_denoteAt (E : CallEnv catCryptDialect) {Γ : Ctxt nfDialect} {s : NfTy}
    {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote) (out : Valuation (d := nfDialect) ts) (fuel : Nat)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' →
      ∃ out', p'.denoteAt E fuel W' = some out' ∧ VRelL ts out out') :
    ∀ {Δ : Ctxt catCryptDialect} (res : OpRes Δ s) (σ : TRd Γ Δ) (W : Valuation Δ)
      (p' : NFProg catCryptDialect Δ (ts.map catTy)),
      emitRes cont rfl res σ = some p' → σ.Agree V W → OpResRel W s y res →
      ∃ out', p'.denoteAt E fuel W = some out' ∧ VRelL ts out out' := by
  intro Δ res
  induction res with
  | rd r =>
      intro σ W p' h hag hrel
      exact HK _ p' W h (TRd.agree_cons hag hrel)
  | expr e' =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨out', hden, hR⟩ := HK σ.lift k' (W.extend (e'.denote W)) hk'
        (TRd.agree_lift hag hrel)
      refine ⟨out', ?_, hR⟩
      rw [denoteAt_var, Expr.denoteM_option_eq_some]
      exact hden
  | expr1 c e' =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hW1 := TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c)
      let W1 : Valuation (d := catCryptDialect) (CryptoTy.sword 64 :: _) :=
        W.extend (BitVec.ofNat 64 c)
      obtain ⟨out', hden, hR⟩ := HK (TRd.lift (TRd.wk σ)) k' (W1.extend (e'.denote W1)) hk'
        (TRd.agree_lift hW1 hrel)
      refine ⟨out', ?_, hR⟩
      rw [denoteAt_var, Expr.denoteM_option_eq_some]
      change NFProg.denoteAt E fuel (NFProg.var _ k') W1 = some out'
      rw [denoteAt_var, Expr.denoteM_option_eq_some]
      exact hden
  | bind c e rest ih =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨out', hden, hR⟩ := ih cont y HK σ.wk (W.extend (e.denote W)) k' hk'
        (TRd.agree_wk hag _) hrel
      refine ⟨out', ?_, hR⟩
      rw [denoteAt_var, Expr.denoteM_option_eq_some]
      exact hden

/-- **The bindings of `pinAll` simulate at a call environment.** The statement
    `pinAll_sound` with the translated programs denoted at `E`. -/
theorem pinAll_denoteAt (E : CallEnv catCryptDialect) {Γ : Ctxt nfDialect}
    {ts ts₀ : List NfTy}
    (k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) →
      Option (NFProg catCryptDialect Δ' (ts₀.map catTy)))
    (V : Valuation Γ) (xs : Valuation (d := nfDialect) ts)
    (out : Valuation (d := nfDialect) ts₀) (fuel : Nat)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy))
      (p' : NFProg catCryptDialect Δ' (ts₀.map catTy)) (W' : Valuation Δ'),
      k σ' ws = some p' → σ'.Agree V W' → VRelL ts xs (Expr.lookupArgs ws W') →
      ∃ out', p'.denoteAt E fuel W' = some out' ∧ VRelL ts₀ out out')
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (p' : NFProg catCryptDialect Δ (ts₀.map catTy)) (W : Valuation Δ)
    (h : pinAll k σ rs = some p') (hag : σ.Agree V W) (hx : RdRelL W ts xs rs) :
    ∃ out', p'.denoteAt E fuel W = some out' ∧ VRelL ts₀ out out' := by
  refine pinAll_elim
    (M := fun {Δ} σ rs p' => ∀ W : Valuation Δ, σ.Agree V W → RdRelL W ts xs rs →
      ∃ out', p'.denoteAt E fuel W = some out' ∧ VRelL ts₀ out out') ?_ ?_ σ rs p' h W hag hx
  · intro Δ σ rs ws p hws hk W hag hx
    exact HK σ ws p W hk hag (pinVars_rel xs rs ws hws hx)
  · intro Δ σ rs c p hc ih W hag hx
    obtain ⟨out', hden, hR⟩ := ih (W.extend (BitVec.ofNat 64 c))
      (TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c))
      (bindLit_rel (firstLit_lt xs rs hc hx) xs rs hx)
    refine ⟨out', ?_, hR⟩
    rw [denoteAt_var, Expr.denoteM_option_eq_some]
    exact hden

/-- **The node of a call simulates.** When the continuation `cont` simulates at `E` from
    every reading that relates `V.extend y`, and `E` answers `f`, on every vector related to
    the arguments `xs` the readings `rs` read, by one result related to `y`, the node
    `emitCall` builds simulates from every valuation the readings `σ` relate to `V`. -/
theorem emitCall_sound (E : CallEnv catCryptDialect) {Γ : Ctxt nfDialect} {s : NfTy}
    {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote) (out : Valuation (d := nfDialect) ts) (fuel : Nat)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' →
      ∃ out', p'.denoteAt E fuel W' = some out' ∧ VRelL ts out out')
    {Δ : Ctxt catCryptDialect} (f : String) (as : List NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (σ : TRd Γ Δ) (W : Valuation Δ)
    (xs : Valuation (d := nfDialect) as) (p' : NFProg catCryptDialect Δ (ts.map catTy))
    (h : emitCall cont f as rs σ = some p') (hag : σ.Agree V W) (hx : RdRelL W as xs rs)
    (hE : ∀ ws : Valuation (d := catCryptDialect) (as.map catTy), VRelL as xs ws →
      ∃ y' : (catTy s).denote,
        E.call f (as.map catTy) [catTy s] ws = some (HVector.cons y' .nil) ∧ VRel s y y') :
    ∃ out', p'.denoteAt E fuel W = some out' ∧ VRelL ts out out' := by
  refine pinAll_denoteAt E _ V xs out fuel ?_ σ rs p' W h hag hx
  intro Δ' σ' ws p'' W' hk hag' hws
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨y', hcall, hy'⟩ := hE _ hws
  obtain ⟨out', hden, hR⟩ := HK σ'.lift k' (W'.extend y') hk' (TRd.agree_lift hag' hy')
  refine ⟨out', ?_, hR⟩
  rw [denoteAt_callNode, hcall]
  exact hden

/-- **The simulation statement of the translation with declarations** of the program `p`,
    at the call environment `E`: a denotation of `p` to `out` from a valuation related to `W`
    by the readings is matched, at every fuel, by a denotation at `E` of the translated
    program from `W` to a related vector. -/
def NFExtSound (bi : _root_.Hax.Builtins) (tf : Nat) (D : List ExtDecl)
    (E : CallEnv catCryptDialect) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCatExt D p σ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (out : Valuation (d := nfDialect) ts),
    σ.Agree V W → ImpToNF.PDenP bi tf p V = some out →
    ∀ fuel, ∃ out', p'.denoteAt E fuel W = some out' ∧ VRelL ts out out'

/-- **The translation with declarations simulates the denotation.** Under `SubTable bi`
    and the agreement `ExtAgree bi E D` of the builtin table, the declarations and the call
    environment `E`, a translated program denotes at `E` values related to the values of
    the source program. -/
theorem nfToCatExt_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (tf : Nat)
    {D : List ExtDecl} {E : CallEnv catCryptDialect} (hD : ExtAgree bi E D)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    NFExtSound bi tf D E p := by
  induction p with
  | ret vs =>
      intro Δ σ p' h V W out hag hp fuel
      change some (Expr.lookupArgs vs V) = some out at hp
      cases hp
      exact pinAll_denoteAt E _ V _ _ fuel
        (fun σ' ws p'' W' hk _ hrel => by cases hk; exact ⟨_, rfl, hrel⟩)
        σ _ p' W h hag (TRd.rdRelL_rds hag vs)
  | var e k ih =>
      intro Δ σ p' h V W out hag hp fuel
      obtain ⟨op, rfl, args⟩ := e
      change (nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => ImpToNF.PDenP bi tf k (V.extend x)) = some out at hp
      obtain ⟨y, hy, hp⟩ := Option.bind_eq_some_iff.mp hp
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some p' at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_denoteAt E (fun σ' => nfToCatExt D k σ') V y out fuel
          (fun σ' p'' W' hk hag' => ih σ' p'' hk (V.extend y) W' out hag' hp fuel)
          res σ W p' h hag (catOp_sound hbi σ hag op args res y hres hy)
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨f, as, rs⟩ := c
        obtain ⟨xs, hx, hE⟩ := extArgs_sound hD σ hag op args f as rs y hc hy
        exact emitCall_sound E (fun σ' => nfToCatExt D k σ') V y out fuel
          (fun σ' p'' W' hk hag' => ih σ' p'' hk (V.extend y) W' out hag' hp fuel)
          f as rs σ W xs p' h hag hx hE
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      intro Δ σ p' h V W out hag hp fuel
      change ((List.range (count.lookup V : BitVec 64).toNat).foldlM
          (fun acc j => ImpToNF.PDenP bi tf body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
          (Expr.lookupArgs inits V)).bind (fun acc => ImpToNF.PDenP bi tf k (hvAppend acc V)) =
        some out at hp
      obtain ⟨accF, hfold, hkout⟩ := Option.bind_eq_some_iff.mp hp
      rw [List.range_eq_range'] at hfold
      have core : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ₀ Δ') (W' : Valuation Δ')
          (c : Var Δ' (CryptoTy.sword 64)) is body' k', σ'.Agree V W' →
          (count.lookup V : BitVec 64) = c.lookup W' →
          VRelL cs (Expr.lookupArgs inits V) (Expr.lookupArgs is W') →
          nfToCatExt D body (TRd.liftApp cs (TRd.lift σ')) = some body' →
          nfToCatExt D k (TRd.liftApp cs σ') = some k' →
          ∃ out', (NFProg.forLoop (cs := cs.map catTy) c is body' k').denoteAt E fuel W' =
            some out' ∧ VRelL ts₀ out out' := by
        intro Δ' σ' W' c is body' k' hag' hcnt his hb' hk'
        have key : ∀ (l : List Nat) (acc : Valuation (d := nfDialect) cs)
            (acc' : Valuation (d := catCryptDialect) (cs.map catTy))
            (accF : Valuation (d := nfDialect) cs), VRelL cs acc acc' →
            l.foldlM (fun acc j => ImpToNF.PDenP bi tf body
              (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V))) acc =
              some accF →
            ∃ accF', l.foldlM (fun acc j => body'.denoteAt E fuel
              (hvAppend acc (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 j) W')))
              acc' = some accF' ∧ VRelL cs accF accF' := by
          intro l
          exact NFProg.foldlM_rel_fwd l fun j _ acc acc' a1 hr ha1 =>
            ihb (TRd.liftApp cs (TRd.lift σ')) body' hb' _ _ a1
              (TRd.agree_liftApp (TRd.agree_lift (s := NfTy.word 64) hag'
                (x := BitVec.ofNat 64 j) (y := BitVec.ofNat 64 j) rfl) cs acc acc' hr) ha1 fuel
        obtain ⟨accF', hfold', hrF⟩ := key _ _ _ accF his hfold
        obtain ⟨out', hden, hR⟩ := ihk (TRd.liftApp cs σ') k' hk' (hvAppend accF V)
          (hvAppend accF' W') out (TRd.agree_liftApp hag' cs accF accF' hrF) hkout fuel
        refine ⟨out', ?_, hR⟩
        rw [denoteAt_forLoop]
        have hc2 : HasWord64.toNat (d := catCryptDialect) (c.lookup W') =
            (count.lookup V : BitVec 64).toNat := by
          rw [← hcnt]; rfl
        rw [hc2, List.range_eq_range']
        erw [hfold']
        exact hden
      refine pinAll_denoteAt E (ts := .word 64 :: cs) _ V
        (Expr.lookupArgs (HVector.cons count inits) V) out fuel ?_ σ _ p' W h hag
        (TRd.rdRelL_rds hag (HVector.cons count inits))
      intro Δ' σ' ws p'' W' hk hag' hrel
      rcases ws with _ | ⟨c, is⟩
      obtain ⟨body', hb', hk⟩ := Option.bind_eq_some_iff.mp hk
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
      exact core σ' W' c is body' k' hag' hrel.1 hrel.2 hb' hk'
  | @ifThenElse Γ₀ rs ts₀ cond thn els k iht ihe ihk =>
      intro Δ σ p' h V W out hag hp fuel
      change ((if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true then
          ImpToNF.PDenP bi tf thn V else ImpToNF.PDenP bi tf els V).bind
          fun r => ImpToNF.PDenP bi tf k (hvAppend r V)) = some out at hp
      obtain ⟨r, hr, hkout⟩ := Option.bind_eq_some_iff.mp hp
      have hcond := hag _ cond
      simp only [nfToCatExt] at h
      split at h
      · rename_i c hc
        rw [hc] at hcond
        obtain ⟨thn', ht', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨els', he', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        have hcb : HasBoolBit.toBool (d := catCryptDialect) (c.lookup W) =
            HasBoolBit.toBool (d := nfDialect) (cond.lookup V) := hcond.symm
        obtain ⟨r', hr', hrR⟩ : ∃ r', (if HasBoolBit.toBool (d := catCryptDialect)
            (c.lookup W) = true then thn'.denoteAt E fuel W else els'.denoteAt E fuel W) =
            some r' ∧ VRelL rs r r' := by
          rw [hcb]
          cases hb : HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
          · rw [hb] at hr
            exact ihe σ els' he' V W r hag hr fuel
          · rw [hb] at hr
            exact iht σ thn' ht' V W r hag hr fuel
        obtain ⟨out', hden, hR⟩ := ihk (TRd.liftApp rs σ) k' hk' (hvAppend r V)
          (hvAppend r' W) out (TRd.agree_liftApp hag rs r r' hrR) hkout fuel
        refine ⟨out', ?_, hR⟩
        rw [denoteAt_ifThenElse]
        erw [hr']
        exact hden
      · cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ p' h
      cases h
  | call f args k _ =>
      intro Δ σ p' h
      cases h

/-! ## 5. The translations without `call` -/

/-- The bindings of a translated operation in front of two continuations: when the second
    returns every program without `call` the first returns, so do the bindings. -/
theorem emitRes_callFree {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {c₁ c₂ : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hc : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), c₁ σ' = some q → q.callFree = true →
      c₂ σ' = some q) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), emitRes c₁ h res σ = some q →
      q.callFree = true → emitRes c₂ h res σ = some q
  | _, _, _, .rd _, _, q, hq, hf => hc _ q hq hf
  | _, _, _, .expr _, _, _, hq, hf => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [emitRes, hc _ k' hk' hf, Option.map_some]
  | _, _, _, .expr1 _ _, _, _, hq, hf => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [emitRes, hc _ k' hk' hf, Option.map_some]
  | _, _, h, .bind _ _ rest, σ, _, hq, hf => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [emitRes, emitRes_callFree hc h rest σ.wk k' hk' hf, Option.map_some]

/-- A program `emitCall` returns has a `call`. -/
theorem emitCall_callFree {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {σ : TRd Γ Δ}
    {q : NFProg catCryptDialect Δ (ts.map catTy)} (h : emitCall cont f as rs σ = some q) :
    q.callFree = false :=
  pinAll_elim (M := fun {_} _ _ q => q.callFree = false)
    (fun _ _ _ _ _ hq => by obtain ⟨k', -, rfl⟩ := Option.map_eq_some_iff.mp hq; rfl)
    (fun _ _ _ _ _ ih => by simpa [NFProg.callFree] using ih) σ rs q h

/-- The bindings of `pinAll` in front of two programs: when the second gives every program
    without `call` the first gives, so does `pinAll` on it. -/
theorem pinAll_callFree {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k₁ k₂ : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hc : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)) (q : NFProg catCryptDialect Δ' us),
      k₁ σ' ws = some q → q.callFree = true → k₂ σ' ws = some q)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k₁ σ rs = some q)
    (hf : q.callFree = true) : pinAll k₂ σ rs = some q := by
  unfold pinAll at h ⊢
  generalize ts.length = n at h ⊢
  induction n generalizing Δ with
  | zero =>
      obtain ⟨ws, hws, hk⟩ := Option.bind_eq_some_iff.mp h
      simp only [pinAllN, hws, Option.bind_some]
      exact hc σ ws q hk hf
  | succ n ih =>
      cases hfl : firstLit rs with
      | none =>
          simp only [pinAllN, hfl] at h ⊢
          obtain ⟨ws, hws, hk⟩ := Option.bind_eq_some_iff.mp h
          simp only [hws, Option.bind_some]
          exact hc σ ws q hk hf
      | some c =>
          simp only [pinAllN, hfl] at h ⊢
          obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
          simp only [ih _ _ p hf hp, Option.map_some]

/-- **A translation without `call` is the translation `nfToCat` gives.** -/
theorem nfToCat_of_callFree (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → q.callFree = true → nfToCat p σ = some q := by
  induction p with
  | ret vs =>
      intro Δ σ q h _
      exact h
  | var e k ih =>
      intro Δ σ q h hf
      obtain ⟨op, rfl, args⟩ := e
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some q at h
      change (catOp σ op args).bind (fun res => emitRes (fun σ' => nfToCat k σ') rfl res σ) =
        some q
      unfold emitOp at h
      split at h
      · rename_i res hres
        rw [hres]
        exact emitRes_callFree (fun σ' q' hq' hf' => ih σ' q' hq' hf') rfl res σ q h hf
      · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
        rw [emitCall_callFree h] at hf
        cases hf
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro Δ σ q h hf
      refine pinAll_callFree (ts := .word 64 :: cs) ?_ σ _ q h hf
      intro Δ' σ' ws q' hq' hf'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      simp only [NFProg.callFree, Bool.and_eq_true] at hf'
      simp only [ihb _ b' hb hf'.1, ihk _ k' hk hf'.2, Option.bind_some, Option.map_some]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ q h hf
      simp only [nfToCatExt] at h
      simp only [nfToCat]
      split at h
      · rename_i c hc
        obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [NFProg.callFree, Bool.and_eq_true] at hf
        simp only [hc, iht _ t' ht hf.1.1, ihe _ e' he hf.1.2, ihk _ k' hk hf.2,
          Option.bind_some, Option.map_some]
      · cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ q h
      cases h
  | call f args k _ =>
      intro Δ σ q h
      cases h

/-! ## 6. The calls of a translated program -/

/-- The calls a program `q` makes are declared by `D` at signatures of words: the symbol
    is the name of a declaration, at the mapped signature of the declaration. -/
def CallsDeclared (D : List ExtDecl) {Δ : Ctxt catCryptDialect} {ts : List CryptoTy}
    (q : NFProg catCryptDialect Δ ts) : Prop :=
  ∀ (f : String) (as rs : List CryptoTy), q.Calls f as rs →
    ∃ d ∈ D, f = d.name ∧ as = d.args.map catTy ∧ rs = [catTy d.ret] ∧ d.wordSig = true

/-- The bindings of a translated operation make the calls of the continuation. -/
theorem emitRes_calls {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    {C : String → List CryptoTy → List CryptoTy → Prop}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q →
      ∀ f as rs, q.Calls f as rs → C f as rs) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ)
      (q : NFProg catCryptDialect Δ (ts.map catTy)), emitRes cont h res σ = some q →
      ∀ f as rs, q.Calls f as rs → C f as rs
  | _, _, _, .rd _, _, q, hq => hcont _ q hq
  | _, _, _, .expr _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, _, .expr1 _ _, _, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact hcont _ k' hk'
  | _, _, h, .bind _ _ rest, σ, _, hq => by
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact emitRes_calls hcont h rest σ.wk k' hk'

/-- The bindings of `pinAll` make the calls of the program `k` gives. -/
theorem pinAll_calls {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    {C : String → List CryptoTy → List CryptoTy → Prop}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)) (q : NFProg catCryptDialect Δ' us),
      k σ' ws = some q → ∀ f as rs, q.Calls f as rs → C f as rs)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (q : NFProg catCryptDialect Δ us) (h : pinAll k σ rs = some q) :
    ∀ f as rs, q.Calls f as rs → C f as rs :=
  pinAll_elim (M := fun {_} _ _ q => ∀ f as rs, q.Calls f as rs → C f as rs)
    (fun σ _ ws q _ hq => hk σ ws q hq) (fun _ _ _ _ _ ih => ih) σ rs q h

/-- **Every call of a translated program is declared.** A program `nfToCatExt D` returns
    calls only names of `D`, each at the mapped signature of its declaration, a signature
    of `ExtDecl.wordSig`. -/
theorem nfToCatExt_calls (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → CallsDeclared D q := by
  induction p with
  | ret vs =>
      intro Δ σ q h
      refine pinAll_calls ?_ σ _ q h
      intro _ _ _ q' hq' f as rs hc
      cases hq'
      exact hc.elim
  | var e k ih =>
      intro Δ σ q h
      obtain ⟨op, rfl, args⟩ := e
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some q at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_calls (fun σ' q' hq' => ih σ' q' hq') rfl res σ q h
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨g, bs, rds⟩ := c
        obtain ⟨d, hd, rfl, rfl, hr, hw⟩ := extArgs_declared σ op args g bs rds hc
        dsimp only at h
        unfold emitCall at h
        refine pinAll_calls ?_ σ rds q h
        intro _ _ _ q' hq'
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
        intro f as rs hcl
        rcases hcl with ⟨rfl, rfl, rfl⟩ | hcl
        · exact ⟨d, hd, rfl, rfl, congrArg (fun t => [catTy t]) hr, hw⟩
        · exact ih _ k' hk' f as rs hcl
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro Δ σ q h
      refine pinAll_calls (ts := .word 64 :: cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      intro f as rs hcl
      rcases hcl with hcl | hcl
      · exact ihb _ b' hb f as rs hcl
      · exact ihk _ k' hk f as rs hcl
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ σ q h
      simp only [nfToCatExt] at h
      split at h
      · obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        intro f as rs hcl
        rcases hcl with hcl | hcl | hcl
        · exact iht _ t' ht f as rs hcl
        · exact ihe _ e' he f as rs hcl
        · exact ihk _ k' hk f as rs hcl
      · cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ q h
      cases h
  | call f args k _ =>
      intro Δ σ q h
      cases h

/-! ## 7. Images in the Jasmin dialect -/

/-- The node of a call in front of a continuation whose programs have operations with
    images is such a program. -/
theorem emitCall_opsHaveImages {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (q : NFProg catCryptDialect Δ' (ts.map catTy)), cont σ' = some q → OpsHaveImages q)
    {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {σ : TRd Γ Δ}
    {q : NFProg catCryptDialect Δ (ts.map catTy)} (h : emitCall cont f as rs σ = some q) :
    OpsHaveImages q := by
  refine pinAll_opsHaveImages ?_ σ rs q h
  intro _ _ _ q' hq'
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq'
  exact hcont _ k' hk'

/-- **Every operation of a program translated with declarations has an image.** The node
    `call` binds no expression, so the statement of `nfToCat_opsHaveImages` holds of
    `nfToCatExt D`. -/
theorem nfToCatExt_opsHaveImages (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (q : NFProg catCryptDialect Δ (ts.map catTy)),
      nfToCatExt D p σ = some q → OpsHaveImages q := by
  induction p with
  | ret vs =>
      intro _ σ q h
      refine pinAll_opsHaveImages ?_ σ _ q h
      intro _ _ _ q' hq'
      cases hq'
      trivial
  | var e k ih =>
      intro _ σ q h
      rcases e with ⟨op, he, args⟩
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op he args = some q at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        exact emitRes_opsHaveImages (fun σ' q' hq' => ih σ' q' hq') he res σ q
          (catOp_image σ op args res hres) h
      · obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact emitCall_opsHaveImages (fun σ' q' hq' => ih σ' q' hq') h
  | @forLoop _ cs _ count inits body k ihb ihk =>
      intro _ σ q h
      refine pinAll_opsHaveImages (ts := .word 64 :: cs) ?_ σ _ q h
      intro _ _ _ q' hq'
      obtain ⟨b', hb, hq'⟩ := Option.bind_eq_some_iff.mp hq'
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq'
      exact And.intro (ihb _ b' hb) (ihk _ k' hk)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ σ q h
      simp only [nfToCatExt] at h
      split at h
      · obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        exact And.intro (iht _ t' ht) (And.intro (ihe _ e' he) (ihk _ k' hk))
      · cases h
  | whileLoop => intro _ σ q h; cases h
  | call => intro _ σ q h; cases h

/-- **The conversion is defined on the e-graph pass of a program translated with
    declarations**: `map?` along `catToJasmin` is `some` on `aegraphOptNF catRules q`, at
    every renaming. -/
theorem isSome_map?_aegraphOptNF_nfToCatExt (D : List ExtDecl) {Γ : Ctxt nfDialect}
    {ts : List NfTy} (p : NFProg nfDialect Γ ts) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (q : NFProg catCryptDialect Δ (ts.map catTy)) (h : nfToCatExt D p σ = some q)
    {Δ' : Ctxt JasminDialect.jasminDialect} (ren : Ctxt.Hom (catToJasmin.mapCtx Δ) Δ') :
    (NFProg.map? catToJasmin catToJasmin_regionTypes (aegraphOptNF catRules q) ren).isSome :=
  (isSome_map?_catToJasmin_iff _ ren).2
    (aegraphOptNF_catRules_opsHaveImages q (nfToCatExt_opsHaveImages D p σ q h)).convertible

/-! ## 8. Leakage -/

/-- **The leakage transformer on the translations without `call`.** `NFProg.leakRun` has
    no run on the node `call`, so the statement of `nfToCat_leak` holds of the programs
    `nfToCatExt D` returns that have no `call`: such a program is the translation `nfToCat`
    gives. -/
theorem nfToCatExt_leak {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) (fuel : Nat) (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)) (h : nfToCatExt D p σ = some p')
    (hf : p'.callFree = true) (V : Valuation Γ) (W : Valuation Δ)
    (r : Valuation (d := nfDialect) ts × List CTLeak) (hag : σ.Agree V W)
    (hr : nfLeakRun bi fuel p V = some r) :
    ∃ r', NFProg.leakRun (catLeakModel P) fuel p' W = some r' ∧ r'.2 = r.2 ∧
      VRelL ts r.1 r'.1 :=
  nfToCat_leak hP hbi fuel p σ p' (nfToCat_of_callFree D p σ p' h hf) V W r hag hr

/-! ## 9. Leakage with calls -/

/-- Whether an event is a variable-time leaf call of a tagged field head
    (`Hax.FieldTag.fieldTag?`). -/
def isFieldEvent : CTLeak → Bool
  | .vtCall f _ => (_root_.Hax.FieldTag.fieldTag? f).isSome
  | _ => false

/-- The events with the variable-time leaf calls of tagged field heads removed. -/
def stripField (l : List CTLeak) : List CTLeak :=
  l.filter fun e => !isFieldEvent e

@[simp] theorem stripField_nil : stripField [] = [] := rfl

@[simp] theorem stripField_append (l₁ l₂ : List CTLeak) :
    stripField (l₁ ++ l₂) = stripField l₁ ++ stripField l₂ :=
  List.filter_append ..

@[simp] theorem stripField_branch (b : Bool) (l : List CTLeak) :
    stripField (.branch b :: l) = .branch b :: stripField l := by
  simp [stripField, isFieldEvent]

@[simp] theorem stripField_trip (n : Nat) (l : List CTLeak) :
    stripField (.trip n :: l) = .trip n :: stripField l := by
  simp [stripField, isFieldEvent]

/-- A call `catCallRd` translates is `index`, `array_update` or a name of `quietCall`. -/
theorem catCallRd_name {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    {rs : HVector (fun t => Rd Δ t) as} {res : OpRes Δ r} (h : catCallRd f as r rs = some res) :
    f = "index" ∨ f = "array_update" ∨ quietCall f = true := by
  have hcall : ∀ {Δ' : Ctxt catCryptDialect} (ws : HVector (fun t => Var Δ' t) (as.map catTy))
      (e : Expr catCryptDialect Δ' (catTy r)), catCall? f as r ws = some e →
      f = "index" ∨ f = "array_update" ∨ quietCall f = true := by
    intro Δ' ws e h
    unfold catCall? at h
    split at h
    · split at h
      · rename_i hf
        exact Or.inl hf
      · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
        exact Or.inr (Or.inr (quietCall_of_mem (scalarCatExpr_name h)))
    · split at h
      · rename_i hf
        exact Or.inr (Or.inl hf)
      · cases h
    · exact Or.inr (Or.inr (quietCall_of_mem (selectCat_name h)))
    · exact Or.inr (Or.inr (quietCall_of_mem (selectCat_name h)))
    · obtain ⟨rfl, -⟩ := lenCat_kind (P := CatLeakParams.owned) noVT_owned h
      exact Or.inr (Or.inr (by decide))
    · cases h
  unfold catCallRd at h
  split at h
  next h₀ =>
    unfold catCallRd0 at h₀
    split at h₀
    · obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.mp h₀
      exact hcall _ e he
    · split at h₀
      · rename_i e he
        unfold shiftImm? at he
        split at he
        · split at he
          · split at he
            · obtain ⟨x, -, he⟩ := Option.bind_eq_some_iff.mp he
              split at he
              · rename_i hf
                subst hf
                exact Or.inr (Or.inr (by decide))
              · split at he
                · rename_i hf
                  subst hf
                  exact Or.inr (Or.inr (by decide))
                · cases he
            · cases he
          · cases he
        · cases he
      · exact pinRes_elim (M := fun _ _ => f = "index" ∨ f = "array_update" ∨
          quietCall f = true) (fun _ ws e _ he => hcall ws e he) (fun _ _ _ _ ih => ih) _ _ _ h₀
  next =>
    split at h
    next h₁ =>
      exact Or.inr (Or.inr (quietCall_of_mem
        (scalarRes_quiet (P := CatLeakParams.owned) noVT_owned h₁).2))
    next =>
      obtain ⟨-, rfl⟩ := arrLitRes_quiet (P := CatLeakParams.owned) noVT_owned h
      exact Or.inr (Or.inr (by decide))

/-- The events of an operation `catOp` translates have no variable-time leaf call of a tagged
    field head. -/
theorem stripField_opLeak_of_catOp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret),
      catOp σ op args = some res → ∀ xs,
      stripField (opLeak nfLeakModel op xs) = opLeak nfLeakModel op xs := by
  intro op args res h xs
  have hk : ∀ g, nfKind op = .vtCall g → _root_.Hax.FieldTag.fieldTag? g = none := by
    clear xs
    induction op with
    | named n op ih => exact ih args res h
    | call f as r =>
        intro g hg
        have hn := catCallRd_name h
        simp only [nfKind] at hg
        split_ifs at hg with h1 h2
        cases hg
        rcases hn with rfl | rfl | hq
        · exact absurd (Or.inl rfl) h1
        · exact absurd (Or.inr rfl) h1
        · exact absurd hq h2
    | ilit t v => intro g hg; cases hg
    | ctr => intro g hg; cases hg
    | trip t => intro g hg; cases hg
    | boundInt t => intro g hg; cases hg
    | bin o w => intro g hg; cases o <;> cases hg
    | constBit b => intro g hg; cases hg
    | constUnit => intro g hg; cases hg
    | arrRepeat n t => intro g hg; cases hg
    | _ => cases h
  unfold opLeak
  split
  · rfl
  · simp [stripField, isFieldEvent]
  · simp [stripField, isFieldEvent]
  · rename_i g hg
    simp [stripField, isFieldEvent, hk g hg]

/-- The events of a call of a tagged field head are removed by `stripField`. -/
theorem stripField_opLeak_tagged {f : String}
    (hf : (_root_.Hax.FieldTag.fieldTag? f).isSome = true) (as : List NfTy) (r : NfTy) (xs) :
    stripField (opLeak nfLeakModel (.call f as r) xs) = [] := by
  unfold opLeak
  show stripField (match nfKind (.call f as r) with
    | .quiet => [] | .addrAt k => _ | .vt m => _ | .vtCall g => _) = []
  simp only [nfKind]
  split_ifs with h1 h2
  · rcases h1 with rfl | rfl <;> exact absurd hf (by decide)
  · rfl
  · simp [stripField, isFieldEvent, hf]

/-- The events of an operation `extArgs` reads as a declared call are removed by
    `stripField` when every declaration is of a tagged field head. -/
theorem stripField_opLeak_of_extArgs {D : List ExtDecl}
    (hT : ∀ d ∈ D, (_root_.Hax.FieldTag.fieldTag? d.name).isSome = true)
    {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
      (c : String × (as : List NfTy) × HVector (fun t => Rd Δ t) as),
      extArgs D σ op args = some c → ∀ xs, stripField (opLeak nfLeakModel op xs) = [] := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call g bs r =>
      intro args c hc xs
      unfold extArgs at hc
      split at hc
      · rename_i hdec
        obtain ⟨d, hd, hn, -, -, -⟩ := declared_iff.mp hdec
        exact stripField_opLeak_tagged (hn ▸ hT d hd) bs r xs
      · cases hc
  | _ => intro args c hc; cases hc

/-- Whether an event is a variable-time leaf call of a tagged field head or of a name that `D`
    declares. -/
def isDeclEvent (D : List ExtDecl) : CTLeak → Bool
  | .vtCall f _ =>
      (_root_.Hax.FieldTag.fieldTag? f).isSome || D.any fun d => decide (d.name = f)
  | _ => false

/-- The events with the variable-time leaf calls of tagged field heads and of the names that
    `D` declares removed. -/
def stripDecl (D : List ExtDecl) (l : List CTLeak) : List CTLeak :=
  l.filter fun e => !isDeclEvent D e

@[simp] theorem stripDecl_nil (D : List ExtDecl) : stripDecl D [] = [] := rfl

@[simp] theorem stripDecl_append (D : List ExtDecl) (l₁ l₂ : List CTLeak) :
    stripDecl D (l₁ ++ l₂) = stripDecl D l₁ ++ stripDecl D l₂ :=
  List.filter_append ..

@[simp] theorem stripDecl_branch (D : List ExtDecl) (b : Bool) (l : List CTLeak) :
    stripDecl D (.branch b :: l) = .branch b :: stripDecl D l := by
  simp [stripDecl, isDeclEvent]

@[simp] theorem stripDecl_trip (D : List ExtDecl) (n : Nat) (l : List CTLeak) :
    stripDecl D (.trip n :: l) = .trip n :: stripDecl D l := by
  simp [stripDecl, isDeclEvent]

/-- At declarations of tagged field heads, `stripDecl D` is `stripField`. -/
theorem stripDecl_eq_stripField {D : List ExtDecl}
    (hT : ∀ d ∈ D, (_root_.Hax.FieldTag.fieldTag? d.name).isSome = true) (l : List CTLeak) :
    stripDecl D l = stripField l := by
  unfold stripDecl stripField
  congr 1
  funext e
  cases e with
  | vtCall f _ =>
      simp only [isDeclEvent, isFieldEvent]
      cases h : (_root_.Hax.FieldTag.fieldTag? f).isSome
      · rw [Bool.false_or, List.any_eq_false.mpr fun d hd hn => by
          rw [decide_eq_true_eq] at hn
          subst hn
          rw [hT d hd] at h
          cases h]
      · rfl
  | _ => rfl

/-- A tagged field head is neither `index` nor `array_update`. -/
theorem ne_index_of_tagged {f : String}
    (hf : (_root_.Hax.FieldTag.fieldTag? f).isSome = true) :
    f ≠ "index" ∧ f ≠ "array_update" := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> exact absurd hf (by decide)

/-- The leakage kind of an operation `catOp` translates is no variable-time leaf call. -/
theorem nfKind_ne_vtCall_of_catOp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret),
      catOp σ op args = some res → ∀ g, nfKind op ≠ .vtCall g := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call f as r =>
      intro args res h g hg
      have hn := catCallRd_name h
      simp only [nfKind] at hg
      split_ifs at hg with h1 h2
      cases hg
      rcases hn with rfl | rfl | hq
      · exact absurd (Or.inl rfl) h1
      · exact absurd (Or.inr rfl) h1
      · exact absurd hq h2
  | ilit t v => intro _ _ _ g hg; cases hg
  | ctr => intro _ _ _ g hg; cases hg
  | trip t => intro _ _ _ g hg; cases hg
  | boundInt t => intro _ _ _ g hg; cases hg
  | bin o w => intro _ _ _ g hg; cases o <;> cases hg
  | constBit b => intro _ _ _ g hg; cases hg
  | constUnit => intro _ _ _ g hg; cases hg
  | arrRepeat n t => intro _ _ _ g hg; cases hg
  | _ => intro _ _ h; cases h

/-- The events of an operation `catOp` translates are kept by `stripDecl D`. -/
theorem stripDecl_opLeak_of_catOp (D : List ExtDecl) {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (op : NfOp)
    (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret)
    (h : catOp σ op args = some res) (xs) :
    stripDecl D (opLeak nfLeakModel op xs) = opLeak nfLeakModel op xs := by
  have hk := nfKind_ne_vtCall_of_catOp σ op args res h
  unfold opLeak
  split
  · rfl
  · simp [stripDecl, isDeclEvent]
  · simp [stripDecl, isDeclEvent]
  · rename_i g hg
    exact absurd hg (hk g)

/-- The events of an operation `extArgs` reads as a declared call are removed by
    `stripDecl D` when no declaration is named `index` or `array_update`. -/
theorem stripDecl_opLeak_of_extArgs {D : List ExtDecl}
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update")
    {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
      (c : String × (as : List NfTy) × HVector (fun t => Rd Δ t) as),
      extArgs D σ op args = some c → ∀ xs, stripDecl D (opLeak nfLeakModel op xs) = [] := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call g bs r =>
      intro args c hc xs
      unfold extArgs at hc
      split at hc
      · rename_i hdec
        obtain ⟨d, hd, hn, -, -, -⟩ := declared_iff.mp hdec
        subst hn
        unfold opLeak
        show stripDecl D (match nfKind (.call d.name bs r) with
          | .quiet => [] | .addrAt k => _ | .vt m => _ | .vtCall g => _) = []
        simp only [nfKind]
        split_ifs with h1 h2
        · rcases h1 with h1 | h1
          exacts [absurd h1 (hN d hd).1, absurd h1 (hN d hd).2]
        · rfl
        · simp only [stripDecl, isDeclEvent]
          simpa using Or.inr ⟨d, hd, rfl⟩
      · cases hc
  | _ => intro args c hc; cases hc

/-- The leakage transformer statement of the translation with declarations of the program
    `p` at the call environment `E`: a leakage run of `p` that succeeds from a valuation
    related to `W` by the readings is matched by a leakage run at `E` of the translated
    program from `W`, whose events are those of the source with the variable-time leaf calls
    of tagged field heads removed, and with related results. -/
def NFLeakSoundC (P : CatLeakParams) (bi : _root_.Hax.Builtins) (E : CallEnv catCryptDialect)
    (D : List ExtDecl) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCatExt D p σ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (r : Valuation (d := nfDialect) ts × List CTLeak),
    σ.Agree V W → nfLeakRun bi fuel p V = some r →
    ∃ r', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some r' ∧ r'.2 = stripField r.2 ∧
      VRelL ts r.1 r'.1

/-- The leakage transformer statement of the translation with the declarations `D` of the
    program `p` at the call environment `E`: a leakage run of `p` that succeeds from a
    valuation related to `W` by the readings is matched by a leakage run at `E` of the
    translated program from `W`, whose events are those of the source with the variable-time
    leaf calls of tagged field heads and of the names `D` declares removed (`stripDecl D`),
    and with related results. -/
def NFLeakSoundD (P : CatLeakParams) (bi : _root_.Hax.Builtins) (E : CallEnv catCryptDialect)
    (D : List ExtDecl) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCatExt D p σ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (r : Valuation (d := nfDialect) ts × List CTLeak),
    σ.Agree V W → nfLeakRun bi fuel p V = some r →
    ∃ r', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some r' ∧ r'.2 = stripDecl D r.2 ∧
      VRelL ts r.1 r'.1

/-- The literal binding `bvConst` emits no event at parameters with no variable-time
    operation. -/
theorem ctLeak_bvConst {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect} (c : Nat)
    (W : Valuation Δ) :
    Expr.ctLeak (catLeakModel P)
      (⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩ : Expr catCryptDialect Δ _) W = [] := by
  simp only [Expr.ctLeak, opLeak, catLeakModel, catKind]
  rw [hP]

/-- **The bindings of a translated operation at a call environment.** The statement
    `emitRes_leak` for the leakage run `NFProg.leakRunMC` at `E`, for any events `ev` of the
    continuation. -/
theorem emitRes_leakC {P : CatLeakParams} (hP : NoVT P) (E : CallEnv catCryptDialect)
    (fuel : Nat) {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote) (out : Valuation (d := nfDialect) ts) (ev : List CTLeak)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' →
      ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W' = some q' ∧ q'.2 = ev ∧
        VRelL ts out q'.1) :
    ∀ {Δ : Ctxt catCryptDialect} (res : OpRes Δ s) (σ : TRd Γ Δ) (W : Valuation Δ)
      (p' : NFProg catCryptDialect Δ (ts.map catTy)),
      emitRes cont rfl res σ = some p' → σ.Agree V W → OpResRel W s y res →
      ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some q' ∧
        q'.2 = resLeak P W res ++ ev ∧ VRelL ts out q'.1 := by
  intro Δ res
  induction res with
  | rd r₀ =>
      intro σ W p' h hag hrel
      exact HK _ p' W h (TRd.agree_cons hag hrel)
  | expr e' =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨q', hq', he, hR⟩ := HK σ.lift k' (W.extend (e'.denote W)) hk'
        (TRd.agree_lift hag hrel)
      refine ⟨(q'.1, Expr.ctLeak (catLeakModel P) e' W ++ q'.2), ?_, ?_, hR⟩
      · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some]
        rw [hq', Option.map_some]
      · rw [he]
        rfl
  | @expr1 Δ₀ t₀ c e' =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hW1 := TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c)
      let W1 : Valuation (d := catCryptDialect) (CryptoTy.sword 64 :: Δ₀) :=
        W.extend (BitVec.ofNat 64 c)
      obtain ⟨q', hq', he, hR⟩ := HK (TRd.lift (TRd.wk σ)) k' (W1.extend (e'.denote W1)) hk'
        (TRd.agree_lift hW1 hrel)
      refine ⟨(q'.1, Expr.ctLeak (catLeakModel P)
          (⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩ : Expr catCryptDialect Δ₀ _) W ++
        (Expr.ctLeak (catLeakModel P) e' W1 ++ q'.2)), ?_, ?_, hR⟩
      · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some]
        erw [hq']
        rfl
      · rw [ctLeak_bvConst hP, List.nil_append, he]
        rfl
  | bind c e rest ih =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨q', hq', he, hR⟩ := ih cont y HK σ.wk (W.extend (e.denote W)) k' hk'
        (TRd.agree_wk hag _) hrel
      refine ⟨(q'.1, Expr.ctLeak (catLeakModel P) e W ++ q'.2), ?_, ?_, hR⟩
      · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some]
        rw [hq', Option.map_some]
      · rw [he]
        simp only [resLeak, List.append_assoc]

/-- **The bindings of `pinAll` emit no event at a call environment.** The statement
    `pinAll_leak` for the leakage run `NFProg.leakRunMC` at `E`. -/
theorem pinAll_leakC {P : CatLeakParams} (hP : NoVT P) (E : CallEnv catCryptDialect)
    (fuel : Nat) {Γ : Ctxt nfDialect} {ts ts₀ : List NfTy}
    (k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) →
      Option (NFProg catCryptDialect Δ' (ts₀.map catTy)))
    (V : Valuation Γ) (xs : Valuation (d := nfDialect) ts)
    (out : Valuation (d := nfDialect) ts₀) (ev : List CTLeak)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy))
      (p' : NFProg catCryptDialect Δ' (ts₀.map catTy)) (W' : Valuation Δ'),
      k σ' ws = some p' → σ'.Agree V W' → VRelL ts xs (Expr.lookupArgs ws W') →
      ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W' = some q' ∧ q'.2 = ev ∧
        VRelL ts₀ out q'.1)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (p' : NFProg catCryptDialect Δ (ts₀.map catTy)) (W : Valuation Δ)
    (h : pinAll k σ rs = some p') (hag : σ.Agree V W) (hx : RdRelL W ts xs rs) :
    ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some q' ∧ q'.2 = ev ∧
      VRelL ts₀ out q'.1 := by
  refine pinAll_elim
    (M := fun {Δ} σ rs p' => ∀ W : Valuation Δ, σ.Agree V W → RdRelL W ts xs rs →
      ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some q' ∧ q'.2 = ev ∧
        VRelL ts₀ out q'.1) ?_ ?_ σ rs p' h W hag hx
  · intro Δ σ rs ws p hws hk W hag hx
    exact HK σ ws p W hk hag (pinVars_rel xs rs ws hws hx)
  · intro Δ σ rs c p hc ih W hag hx
    obtain ⟨r', hr', he, hR⟩ := ih (W.extend (BitVec.ofNat 64 c))
      (TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c))
      (bindLit_rel (firstLit_lt xs rs hc hx) xs rs hx)
    refine ⟨(r'.1, Expr.ctLeak (catLeakModel P)
      (⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩ : Expr catCryptDialect Δ _) W ++
        r'.2), ?_, ?_, hR⟩
    · simp only [NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some]
      erw [hr']
      rfl
    · rw [ctLeak_bvConst hP, List.nil_append, he]

/-- **The node of a call emits no event at a call environment.** The statement
    `emitCall_sound` for the leakage run `NFProg.leakRunMC` at `E`: the run of the node
    `emitCall` builds has the events `ev` of its continuation. -/
theorem emitCall_leakC {P : CatLeakParams} (hP : NoVT P) (E : CallEnv catCryptDialect)
    (fuel : Nat) {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote) (out : Valuation (d := nfDialect) ts) (ev : List CTLeak)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' →
      ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W' = some q' ∧ q'.2 = ev ∧
        VRelL ts out q'.1)
    {Δ : Ctxt catCryptDialect} (f : String) (as : List NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (σ : TRd Γ Δ) (W : Valuation Δ)
    (xs : Valuation (d := nfDialect) as) (p' : NFProg catCryptDialect Δ (ts.map catTy))
    (h : emitCall cont f as rs σ = some p') (hag : σ.Agree V W) (hx : RdRelL W as xs rs)
    (hE : ∀ ws : Valuation (d := catCryptDialect) (as.map catTy), VRelL as xs ws →
      ∃ y' : (catTy s).denote,
        E.call f (as.map catTy) [catTy s] ws = some (HVector.cons y' .nil) ∧ VRel s y y') :
    ∃ q', NFProg.leakRunMC (catLeakModel P) E fuel p' W = some q' ∧ q'.2 = ev ∧
      VRelL ts out q'.1 := by
  refine pinAll_leakC hP E fuel _ V xs out ev ?_ σ rs p' W h hag hx
  intro Δ' σ' ws p'' W' hk hag' hws
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
  obtain ⟨y', hcall, hy'⟩ := hE _ hws
  obtain ⟨q', hq', he, hR⟩ := HK σ'.lift k' (W'.extend y') hk' (TRd.agree_lift hag' hy')
  refine ⟨q', ?_, he, hR⟩
  simp only [NFProg.leakRunMC]
  rw [hcall, Option.bind_some]
  exact hq'

/-- **The leakage transformer of the translation with declarations.** Under `SubTable bi`,
    the agreement `ExtAgree bi E D`, parameters with no variable-time operation, and
    declarations of no name `index` or `array_update`, a leakage run of a program that
    succeeds is matched by the leakage run at `E` of its translation, in which a call node
    emits no event: the events of the translation are those of the source with the
    variable-time leaf calls of tagged field heads and of the declared names removed
    (`stripDecl D`). -/
theorem nfToCatExt_leakD {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) {E : CallEnv catCryptDialect} {D : List ExtDecl}
    (hD : ExtAgree bi E D)
    (hN : ∀ d ∈ D, d.name ≠ "index" ∧ d.name ≠ "array_update") (fuel : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    NFLeakSoundD P bi E D fuel p := by
  induction p with
  | ret vs =>
      intro Δ σ p' h V W r hag hr
      change some (Expr.lookupArgs vs V, []) = some r at hr
      cases hr
      exact pinAll_leakC hP E fuel _ V _ (Expr.lookupArgs vs V) []
        (fun σ' ws p'' W' hk _ hrel => by cases hk; exact ⟨_, rfl, rfl, hrel⟩)
        σ _ p' W h hag (TRd.rdRelL_rds hag vs)
  | var e k ih =>
      intro Δ σ p' h V W r hag hr
      obtain ⟨op, rfl, args⟩ := e
      change (nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => (nfLeakRun bi fuel k (V.extend x)).map fun q =>
          (q.1, Expr.ctLeak nfLeakModel ⟨op, rfl, args⟩ V ++ q.2)) = some r at hr
      obtain ⟨y, hy, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hr
      change emitOp D (fun σ' => nfToCatExt D k σ') σ op rfl args = some p' at h
      unfold emitOp at h
      split at h
      · rename_i res hres
        have hrel := catOp_sound hbi σ hag op args res y hres hy
        have hlk := catOp_leak hP σ hag op args res hres
        change resLeak P W res = Expr.ctLeak nfLeakModel ⟨op, rfl, args⟩ V at hlk
        obtain ⟨q', hq', he, hR⟩ := emitRes_leakC hP E fuel (fun σ' => nfToCatExt D k σ') V
          y q.1 (stripDecl D q.2)
          (fun σ' p'' W' hk hag' => ih σ' p'' hk (V.extend y) W' q hag' hq) res σ W p' h hag
          hrel
        refine ⟨q', hq', ?_, hR⟩
        rw [he, hlk, stripDecl_append]
        exact congrArg (· ++ stripDecl D q.2)
          (stripDecl_opLeak_of_catOp D σ op args res hres (Expr.lookupArgs args V)).symm
      · obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨f, as, rs⟩ := c
        obtain ⟨xs, hx, hE⟩ := extArgs_sound hD σ hag op args f as rs y hc hy
        obtain ⟨q', hq', he, hR⟩ := emitCall_leakC hP E fuel (fun σ' => nfToCatExt D k σ') V
          y q.1 (stripDecl D q.2)
          (fun σ' p'' W' hk hag' => ih σ' p'' hk (V.extend y) W' q hag' hq)
          f as rs σ W xs p' h hag hx hE
        refine ⟨q', hq', ?_, hR⟩
        rw [he, stripDecl_append]
        suffices hs : stripDecl D (Expr.ctLeak nfLeakModel ⟨op, rfl, args⟩ V) = [] by
          rw [hs, List.nil_append]
        exact stripDecl_opLeak_of_extArgs hN σ op args _ hc _
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      intro Δ σ p' h V W r hag hr
      change (forIterLeak
          (fun i acc => nfLeakRun bi fuel body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 i) V)))
          (List.range (count.lookup V : BitVec 64).toNat) (Expr.lookupArgs inits V)).bind
          (fun a => (nfLeakRun bi fuel k (hvAppend a.1 V)).map fun q =>
            (q.1, .trip (count.lookup V : BitVec 64).toNat :: (a.2 ++ q.2))) = some r at hr
      obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hr
      have core : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ₀ Δ') (W' : Valuation Δ')
          (c : Var Δ' (CryptoTy.sword 64)) is body' k', σ'.Agree V W' →
          (count.lookup V : BitVec 64) = c.lookup W' →
          VRelL cs (Expr.lookupArgs inits V) (Expr.lookupArgs is W') →
          nfToCatExt D body (TRd.liftApp cs (TRd.lift σ')) = some body' →
          nfToCatExt D k (TRd.liftApp cs σ') = some k' →
          ∃ r', NFProg.leakRunMC (catLeakModel P) E fuel
              (NFProg.forLoop (cs := cs.map catTy) c is body' k') W' = some r' ∧
            r'.2 = stripDecl D (.trip (count.lookup V : BitVec 64).toNat :: (a.2 ++ q.2)) ∧
            VRelL ts₀ q.1 r'.1 := by
        intro Δ' σ' W' c is body' k' hag' hcnt his hb' hk'
        have key : ∀ (l : List Nat) (acc : Valuation (d := nfDialect) cs)
            (acc' : Valuation (d := catCryptDialect) (cs.map catTy))
            (a : Valuation (d := nfDialect) cs × List CTLeak), VRelL cs acc acc' →
            forIterLeak (fun i acc => nfLeakRun bi fuel body
              (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 i) V))) l acc =
              some a →
            ∃ a', forIterLeak (fun i acc => NFProg.leakRunMC (catLeakModel P) E fuel body'
              (hvAppend acc (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 i) W')))
              l acc' = some a' ∧ a'.2 = stripDecl D a.2 ∧ VRelL cs a.1 a'.1 := by
          intro l
          induction l with
          | nil =>
              intro acc acc' a hr h
              simp only [forIterLeak, Option.some.injEq] at h
              subst h
              exact ⟨(acc', []), rfl, rfl, hr⟩
          | cons j l ih =>
              intro acc acc' a hr h
              simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
              obtain ⟨a1, ha1, a2, ha2, rfl⟩ := h
              have hag1 := TRd.agree_liftApp
                (TRd.agree_lift (s := NfTy.word 64) hag' (x := BitVec.ofNat 64 j)
                  (y := BitVec.ofNat 64 j) rfl) cs acc acc' hr
              obtain ⟨a1', ha1', he1, hr1⟩ := ihb (TRd.liftApp cs (TRd.lift σ')) body' hb' _ _
                a1 hag1 ha1
              obtain ⟨a2', ha2', he2, hr2⟩ := ih a1.1 a1'.1 a2 hr1 ha2
              refine ⟨(a2'.1, a1'.2 ++ a2'.2), ?_, ?_, hr2⟩
              · simp only [forIterLeak]
                erw [ha1']
                rw [Option.bind_some, ha2', Option.map_some]
              · simp only [he1, he2, stripDecl_append]
        obtain ⟨a', ha', he, hrA⟩ := key _ _ _ a his ha
        obtain ⟨q', hq', heq, hR⟩ := ihk (TRd.liftApp cs σ') k' hk' (hvAppend a.1 V)
          (hvAppend a'.1 W') q (TRd.agree_liftApp hag' cs a.1 a'.1 hrA) hq
        refine ⟨(q'.1, .trip (c.lookup W').toNat :: (a'.2 ++ q'.2)), ?_, ?_, hR⟩
        · simp only [NFProg.leakRunMC]
          have hc2 : HasWord64.toNat (d := catCryptDialect) (c.lookup W') =
              (count.lookup V : BitVec 64).toNat := by
            rw [← hcnt]; rfl
          rw [hc2]
          erw [ha']
          rw [Option.bind_some, hq', Option.map_some, ← hcnt]
        · simp only [he, heq, ← hcnt, stripDecl_trip, stripDecl_append]
      refine pinAll_leakC hP E fuel (ts := .word 64 :: cs) _ V
        (Expr.lookupArgs (HVector.cons count inits) V) q.1
        (stripDecl D (.trip (count.lookup V : BitVec 64).toNat :: (a.2 ++ q.2))) ?_ σ _ p' W h
        hag (TRd.rdRelL_rds hag (HVector.cons count inits))
      intro Δ' σ' ws p'' W' hk hag' hrel
      rcases ws with _ | ⟨c, is⟩
      obtain ⟨body', hb', hk⟩ := Option.bind_eq_some_iff.mp hk
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hk
      exact core σ' W' c is body' k' hag' hrel.1 hrel.2 hb' hk'
  | @ifThenElse Γ₀ rs ts₀ cond thn els k iht ihe ihk =>
      intro Δ σ p' h V W r hag hr
      change ((if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true then
          nfLeakRun bi fuel thn V else nfLeakRun bi fuel els V).bind fun a =>
          (nfLeakRun bi fuel k (hvAppend a.1 V)).map fun q =>
            (q.1, .branch (HasBoolBit.toBool (d := nfDialect) (cond.lookup V)) ::
              (a.2 ++ q.2))) = some r at hr
      obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hr
      have hcond := hag _ cond
      simp only [nfToCatExt] at h
      split at h
      · rename_i c hc
        rw [hc] at hcond
        obtain ⟨thn', ht', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨els', he', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        have hcb : HasBoolBit.toBool (d := catCryptDialect) (c.lookup W) =
            HasBoolBit.toBool (d := nfDialect) (cond.lookup V) := hcond.symm
        obtain ⟨a', ha', hea, hrA⟩ : ∃ a', (if HasBoolBit.toBool (d := catCryptDialect)
            (c.lookup W) = true then NFProg.leakRunMC (catLeakModel P) E fuel thn' W
            else NFProg.leakRunMC (catLeakModel P) E fuel els' W) = some a' ∧
            a'.2 = stripDecl D a.2 ∧ VRelL rs a.1 a'.1 := by
          rw [hcb]
          cases hb : HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
          · rw [hb] at ha
            exact ihe σ els' he' V W a hag ha
          · rw [hb] at ha
            exact iht σ thn' ht' V W a hag ha
        obtain ⟨q', hq', heq, hR⟩ := ihk (TRd.liftApp rs σ) k' hk' (hvAppend a.1 V)
          (hvAppend a'.1 W) q (TRd.agree_liftApp hag rs a.1 a'.1 hrA) hq
        refine ⟨(q'.1, .branch (HasBoolBit.toBool (d := catCryptDialect) (c.lookup W)) ::
          (a'.2 ++ q'.2)), ?_, ?_, hR⟩
        · simp only [NFProg.leakRunMC]
          erw [ha']
          rw [Option.bind_some, hq', Option.map_some]
        · simp only [hea, heq, hcb, stripDecl_branch, stripDecl_append]
      · cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ p' h
      cases h
  | call f args k _ =>
      intro Δ σ p' h
      cases h

/-- **The leakage transformer of the translation with declarations of tagged field heads.**
    The statement `nfToCatExt_leakD` at declarations of tagged field heads only, at which
    `stripDecl D` is `stripField` (`stripDecl_eq_stripField`). -/
theorem nfToCatExt_leakC {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) {E : CallEnv catCryptDialect} {D : List ExtDecl}
    (hD : ExtAgree bi E D)
    (hT : ∀ d ∈ D, (_root_.Hax.FieldTag.fieldTag? d.name).isSome = true) (fuel : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) :
    NFLeakSoundC P bi E D fuel p := by
  intro Δ σ p' h V W r hag hr
  obtain ⟨r', h₁, h₂, h₃⟩ := nfToCatExt_leakD hP hbi hD
    (fun d hd => ne_index_of_tagged (hT d hd)) fuel p σ p' h V W r hag hr
  exact ⟨r', h₁, h₂.trans (stripDecl_eq_stripField hT r.2), h₃⟩

end CatCrypt.Crypto.Hax.NFToCat
