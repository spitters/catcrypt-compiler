/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCat
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFLeakM
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak

/-!
# The leakage of `NFProg nfDialect` and the leakage transformer of `nfToCat`

The leakage model `nfLeakModel` of `nfDialect`: the calls `index` and `array_update`, and the
operations `index` and `update`, leak their index argument (position `1`) as a memory offset;
every other operation is quiet. A word, an integer and a bit read as natural numbers; every
other value reads as `0`. The model has no variable-time scalar operation: it is compared with
`catLeakModel P` at parameters `P` with no variable-time operation (`NoVT P`), which the owned
parameters satisfy.

`nfToCat` translates each operation to no binding (a literal, a loop counter or a trip count,
all quiet), to one binding, or to a quiet `bvConst` binding followed by one binding. The
binding of `index` is `memrefGetDyn` and that of `array_update` is `memrefSetDyn`, which leak
the word of the index; the values are related by `VRel`. The leakage transformer is therefore
the identity: a run of the source that succeeds from `V` is matched by a run of the
translated program from every valuation the readings relate to `V`, with the same events
(`nfToCat_leak`).

## Main definitions

* `nfKind`, `nfValNat`, `nfLeakModel` — the leakage model of `nfDialect`.
* `nfLeakRun` — the leakage run of a program of `nfDialect` over the leaf table of a builtin
  table.
* `NoVT` — parameters of `catCryptDialect` with no variable-time operation.

## Main results

* `nfValNat_vrel`, `valsNat_vrelL` — related values have equal readings.
* `catOp_leak` — the events of an operation are the events of its translation.
* `nfToCat_leak` — the leakage transformer of `nfToCat` is the identity.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (opLeak_eq_of)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## The leakage model of `nfDialect` -/

/-- The event class of an operation of `nfDialect`: the index argument of an array access is
    a memory offset; every other operation is quiet. -/
def nfKind : NfOp → LeakKind
  | .named _ op => nfKind op
  | .call f _ _ => if f = "index" ∨ f = "array_update" then .addrAt 1 else .quiet
  | .index _ _ | .update _ _ => .addrAt 1
  | _ => .quiet

/-- The natural-number reading of a value of `nfDialect`: a word and a bit by their bits, an
    integer by its natural number, every other value as `0`. -/
def nfValNat : (t : NfTy) → t.denote → Nat
  | .word _, x => x.toNat
  | .int, z => z.toNat
  | .bit, b => b.toNat
  | _, _ => 0

/-- The leakage model of `nfDialect`. -/
def nfLeakModel : LeakModel nfDialect where
  kind := nfKind
  valNat := nfValNat

/-- The leakage run of a program of `nfDialect` over the leaf table of the builtin table
    `bi`. -/
abbrev nfLeakRun (bi : _root_.Hax.Builtins) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    Option (Valuation (d := nfDialect) ts × List CTLeak) :=
  @NFProg.leakRunM nfDialect _ _ _ _ (nfDenote (ImpToNF.tableOf bi)) nfLeakModel fuel _ _ p V

/-- Parameters of `catCryptDialect` with no operation lowered to a variable-time
    instruction. -/
def NoVT (P : CatLeakParams) : Prop := ∀ op, P.opVT op = none

/-- The owned parameters have no variable-time operation. -/
theorem noVT_owned : NoVT CatLeakParams.owned := fun _ => rfl

/-! ## Related values have equal readings -/

/-- Values related by `VRel` have equal readings. -/
theorem nfValNat_vrel : (t : NfTy) → (x : t.denote) → (y : (catTy t).denote) → VRel t x y →
    nfValNat t x = catValNat (catTy t) y
  | .word _, _, _, h => by subst h; rfl
  | .int, z, y, h => by
      change z.toNat = y.toNat
      rw [show z = (y.toNat : Int) from h, Int.toNat_natCast]
  | .bit, b, b', h => by subst h; rfl
  | .unit, _, _, _ => rfl
  | .arr _ .int, _, _, _ => rfl
  | .arr _ .bit, _, _, h | .arr _ .unit, _, _, h | .arr _ (.word _), _, _, h
  | .arr _ (.arr _ _), _, _, h | .arr _ (.pair _ _), _, _, h | .arr _ (.uint _), _, _, h
  | .arr _ (.sint _), _, _, h | .arr _ .tnil, _, _, h | .arr _ (.tcons _ _), _, _, h
  | .arr _ (.slice _), _, _, h | .pair _ _, _, _, h | .uint _, _, _, h | .sint _, _, _, h
  | .tnil, _, _, h | .tcons _ _, _, _, h | .slice _, _, _, h => h.elim

/-- Vectors related by `VRelL` have equal readings. -/
theorem valsNat_vrelL (P : CatLeakParams) : (ts : List NfTy) →
    (xs : Valuation (d := nfDialect) ts) → (ys : Valuation (d := catCryptDialect) (ts.map catTy)) →
    VRelL ts xs ys → valsNat nfLeakModel xs = valsNat (catLeakModel P) ys
  | [], .nil, .nil, _ => rfl
  | t :: ts, .cons x xs, .cons y ys, h => by
      change nfValNat t x :: valsNat nfLeakModel xs = catValNat (catTy t) y ::
        valsNat (catLeakModel P) ys
      rw [nfValNat_vrel t x y h.1, valsNat_vrelL P ts xs ys h.2]

/-! ## The events of an operation -/

/-- A scalar call of `scalarCatExpr` is quiet at parameters with no variable-time
    operation. -/
theorem scalarCatExpr_kind {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect}
    {f : String} {a b : Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : scalarCatExpr f a b = some e) : catKind P e.op = .quiet := by
  unfold scalarCatExpr at h
  split at h <;> (try cases h) <;> simp only [catKind] <;> rw [hP]

/-- The call `catCall?` builds has the event class of the source call, at parameters with no
    variable-time operation. -/
theorem catCall_kind {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect}
    (f : String) (as : List NfTy) (r : NfTy) (ws : HVector (fun t => Var Δ t) (as.map catTy))
    (e : Expr catCryptDialect Δ (catTy r)) (h : catCall? f as r ws = some e) :
    catKind P e.op = nfKind (.call f as r) := by
  unfold catCall? at h
  split at h
  · split at h
    · rename_i hf
      obtain ⟨⟨n, a⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i, -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [catKind, nfKind, hf]
    · rename_i hf
      obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
      rw [scalarCatExpr_kind hP h]
      have hu : f ≠ "array_update" := by
        rintro rfl; simp [scalarCatExpr] at h
      simp [nfKind, hf, hu]
  · split at h
    · rename_i hf
      obtain ⟨⟨n, m⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · obtain ⟨i', -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x', -, rfl⟩ := Option.map_eq_some_iff.mp h
        simp [catKind, nfKind, hf]
      · cases h
    · cases h
  · cases h

/-- The reading of a value related to a variable `asWord` reads as a word is the number of
    that word. -/
theorem asWord_valNat {Δ : Ctxt catCryptDialect} {t : NfTy} {v : Var Δ (catTy t)}
    {w : Var Δ (.sword 64)} (h : asWord t v = some w) (W : Valuation Δ) {x : t.denote}
    (hx : VRel t x (v.lookup W)) : nfValNat t x = (w.lookup W).toNat := by
  unfold asWord at h
  split at h
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    cases t with
    | int =>
        change x = _ at hx
        subst hx
        exact Int.toNat_natCast _
    | word n =>
        have hn : n = 64 := by
          revert ht; unfold ImpToNF.hax64NFWordTy; split <;> simp_all
        subst hn
        change x = _ at hx
        subst hx
        rfl
    | _ => simp [ImpToNF.hax64NFWordTy] at ht
  · cases h

/-- **The events of a call.** The expression `catCall?` builds on variables reading values
    related to the arguments `xs` emits the events of the source call on `xs`, at parameters
    with no variable-time operation. -/
theorem catCall_leak {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect}
    (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (ws : HVector (fun t => Var Δ t) (as.map catTy)) (e : Expr catCryptDialect Δ (catTy r))
    (xs : Valuation (d := nfDialect) as) (h : catCall? f as r ws = some e)
    (hx : VRelL as xs (Expr.lookupArgs ws W)) :
    Expr.ctLeak (catLeakModel P) e W = opLeak nfLeakModel (.call f as r) xs := by
  have hk := catCall_kind hP f as r ws e h
  unfold catCall? at h
  split at h
  · rename_i ta tb args
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | _⟩⟩
    have hx₂ : VRel tb x₂ (args.tail.head.lookup W) := by
      rcases args with _ | ⟨a₁, _ | ⟨a₂, _ | _⟩⟩
      exact hx.2.1
    split at h
    · rename_i hf
      obtain ⟨⟨n, a⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Expr.ctLeak, opLeak, catLeakModel, nfLeakModel, catKind, nfKind, hf, true_or,
        if_true]
      change [CTLeak.addr "" (((i.lookup W).toNat : Nat) : Int)] =
        [CTLeak.addr "" ((nfValNat tb x₂ : Nat) : Int)]
      rw [asWord_valNat hi W hx₂]
    · rename_i hf
      have hq : nfKind (.call f [ta, tb] .int) = .quiet := by
        obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨y, -, h⟩ := Option.bind_eq_some_iff.mp h
        have hu : f ≠ "array_update" := by
          rintro rfl; simp [scalarCatExpr] at h
        simp [nfKind, hf, hu]
      unfold Expr.ctLeak opLeak
      rw [show (catLeakModel P).kind e.op = catKind P e.op from rfl, hk,
        show nfLeakModel.kind (.call f [ta, tb] .int) = nfKind (.call f [ta, tb] .int) from rfl,
        hq]
  · rename_i ta ti tv n' args
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | _⟩⟩⟩
    have hx₂ : VRel ti x₂ (args.tail.head.lookup W) := by
      rcases args with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, _ | _⟩⟩⟩
      exact hx.2.1
    split at h
    · rename_i hf
      obtain ⟨⟨n, m⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · obtain ⟨i', hi', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x', -, rfl⟩ := Option.map_eq_some_iff.mp h
        simp only [Expr.ctLeak, opLeak, catLeakModel, nfLeakModel, catKind, nfKind, hf,
          or_true, if_true]
        change [CTLeak.addr "" (((i'.lookup W).toNat : Nat) : Int)] =
          [CTLeak.addr "" ((nfValNat ti x₂ : Nat) : Int)]
        rw [asWord_valNat hi' W hx₂]
      · cases h
    · cases h
  · cases h

/-- The events of the translation of an operation at the valuation `W` of the target: none
    for a reading, the events of the expression, and the events of the expression under the
    binding of the literal (the `bvConst` binding is quiet). -/
def resLeak (P : CatLeakParams) {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {t : NfTy} :
    OpRes Δ t → List CTLeak
  | .rd _ => []
  | .expr e => Expr.ctLeak (catLeakModel P) e W
  | .expr1 k e => Expr.ctLeak (catLeakModel P) e
      (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 k) W)

/-- A shift by an immediate and its source call are quiet. -/
theorem shiftImm_leak {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect}
    (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (e : Expr catCryptDialect Δ (catTy r))
    (xs : Valuation (d := nfDialect) as) (h : shiftImm? f as r rs = some e) :
    Expr.ctLeak (catLeakModel P) e W = opLeak nfLeakModel (.call f as r) xs := by
  unfold shiftImm? at h
  split at h
  · split at h
    · split at h
      · obtain ⟨x, -, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · rename_i hf
          cases h
          subst hf
          simp only [Expr.ctLeak, opLeak, catLeakModel, nfLeakModel, catKind, nfKind]
          rw [hP]
          simp
        · split at h
          · rename_i hf
            cases h
            subst hf
            simp only [Expr.ctLeak, opLeak, catLeakModel, nfLeakModel, catKind, nfKind]
            rw [hP]
            simp
          · cases h
      · cases h
    · cases h
  · cases h

/-- **The events of a translated call.** The translation `catCallRd` of a call on readings
    related to the arguments `xs` emits the events of the source call on `xs`. -/
theorem catCallRd_leak {P : CatLeakParams} (hP : NoVT P) {Δ : Ctxt catCryptDialect}
    (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (res : OpRes Δ r) (xs : Valuation (d := nfDialect) as)
    (h : catCallRd f as r rs = some res) (hx : RdRelL W as xs rs) :
    resLeak P W res = opLeak nfLeakModel (.call f as r) xs := by
  unfold catCallRd at h
  split at h
  · rename_i ws hws
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact catCall_leak hP W f as r ws e xs he (pinVars_rel xs rs ws hws hx)
  · split at h
    · rename_i e he
      cases h
      exact shiftImm_leak hP W f as r rs e xs he
    · obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      have hk64 := firstLit_lt xs rs hk hx
      exact catCall_leak hP _ f as r ws e xs he (pinLit_rel hk64 xs rs ws hws hx)

/-- **The events of a translated operation.** Under readings that relate `V` to `W`, the
    translation `catOp` of an operation emits the events of the operation. -/
theorem catOp_leak {P : CatLeakParams} (hP : NoVT P) {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) {V : Valuation Γ} {W : Valuation Δ}
    (hag : σ.Agree V W) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret),
      catOp σ op args = some res →
      resLeak P W res = opLeak nfLeakModel op (Expr.lookupArgs args V) := by
  intro op
  induction op with
  | named n op ih =>
      intro args res h
      exact ih args res h
  | call f as r =>
      intro args res h
      exact catCallRd_leak hP W f as r (σ.rds args) res (Expr.lookupArgs args V) h
        (TRd.rdRelL_rds hag args)
  | ilit t v =>
      intro args res h
      unfold catOp at h
      split at h
      · cases h; rfl
      · cases h
  | ctr =>
      intro args res h
      rcases args with _ | ⟨lo, _ | ⟨i, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => some (OpRes.rd (Rd.ofWord (σ i)))
        | _ => none) = some res at h
      split at h
      · cases h; rfl
      · cases h
  | trip t =>
      intro args res h
      rcases args with _ | ⟨lo, _ | ⟨hi, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => (Rd.toWord64 t (σ hi)).map OpRes.rd
        | _ => none) = some res at h
      split at h
      · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.mp h
        rfl
      · cases h
  | _ =>
      intro args res h
      cases h

/-! ## Programs -/

/-- The leakage transformer statement of the translation of the program `p`: a leakage run of
    `p` that succeeds from a valuation related to `W` by the readings is matched by a leakage
    run of the translated program from `W`, with the same events and related results. -/
def NFLeakSound (P : CatLeakParams) (bi : _root_.Hax.Builtins) (fuel : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCat p σ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (r : Valuation (d := nfDialect) ts × List CTLeak),
    σ.Agree V W → nfLeakRun bi fuel p V = some r →
    ∃ r', NFProg.leakRun (catLeakModel P) fuel p' W = some r' ∧ r'.2 = r.2 ∧ VRelL ts r.1 r'.1

/-- **The leakage transformer of `nfToCat` is the identity.** Under `SubTable bi` and at
    parameters with no variable-time operation, a leakage run of a translated program that
    succeeds is matched by a leakage run of the translation with the same events. -/
theorem nfToCat_leak {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : NFLeakSound P bi fuel p := by
  induction p with
  | ret vs =>
      intro Δ σ p' h V W r hag hr
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      change some (Expr.lookupArgs vs V, []) = some r at hr
      cases hr
      exact ⟨_, rfl, rfl, pinVars_rel _ _ ws hws (TRd.rdRelL_rds hag vs)⟩
  | var e k ih =>
      intro Δ σ p' h V W r hag hr
      obtain ⟨op, rfl, args⟩ := e
      obtain ⟨res, hres, h⟩ := Option.bind_eq_some_iff.mp h
      change (nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => (nfLeakRun bi fuel k (V.extend x)).map fun q =>
          (q.1, Expr.ctLeak nfLeakModel ⟨op, rfl, args⟩ V ++ q.2)) = some r at hr
      obtain ⟨y, hy, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hr
      have hrel := catOp_sound hbi σ hag op args res y hres hy
      have hlk := catOp_leak hP σ hag op args res hres
      change resLeak P W res = Expr.ctLeak nfLeakModel ⟨op, rfl, args⟩ V at hlk
      cases res with
      | rd r₀ =>
          obtain ⟨q', hq', he, hR⟩ :=
            ih (TRd.cons r₀ σ) p' h (V.extend y) W q (TRd.agree_cons hag hrel) hq
          refine ⟨q', hq', ?_, hR⟩
          rw [he, ← hlk]
          rfl
      | expr e' =>
          obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨q', hq', he, hR⟩ := ih σ.lift k' hk' (V.extend y) (W.extend (e'.denote W))
            q (TRd.agree_lift hag hrel) hq
          refine ⟨(q'.1, Expr.ctLeak (catLeakModel P) e' W ++ q'.2), ?_, ?_, hR⟩
          · change (NFProg.leakRun (catLeakModel P) fuel k' (W.extend (e'.denote W))).map _ = _
            rw [hq', Option.map_some]
            rfl
          · change Expr.ctLeak (catLeakModel P) e' W ++ q'.2 = _
            rw [he, ← hlk]
            rfl
      | expr1 c e' =>
          obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
          have hW1 := TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 c)
          let W1 : Valuation (d := catCryptDialect) (CryptoTy.sword 64 :: Δ) :=
            W.extend (BitVec.ofNat 64 c)
          obtain ⟨q', hq', he, hR⟩ := ih (TRd.lift (TRd.wk σ)) k' hk' (V.extend y)
            (W1.extend (e'.denote W1)) q (TRd.agree_lift hW1 hrel) hq
          have h0 : Expr.ctLeak (catLeakModel P)
              (⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩ : Expr catCryptDialect Δ _) W =
              [] := by
            simp only [Expr.ctLeak, opLeak, catLeakModel, catKind]
            rw [hP]
          refine ⟨(q'.1, Expr.ctLeak (catLeakModel P)
              (⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩ : Expr catCryptDialect Δ _) W ++
            (Expr.ctLeak (catLeakModel P) e' W1 ++ q'.2)), ?_, ?_, hR⟩
          · change ((NFProg.leakRun (catLeakModel P) fuel k' (W1.extend (e'.denote W1))).map
              _).map _ = _
            rw [hq', Option.map_some, Option.map_some]
            rfl
          · rw [h0, List.nil_append, he]
            change resLeak P W (.expr1 c e') ++ q.2 = _
            rw [hlk]
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      intro Δ σ p' h V W r hag hr
      change (match σ count with
        | .var c =>
          (pinVars (σ.rds inits)).bind fun is =>
            (nfToCat body (TRd.liftApp cs (TRd.lift σ))).bind fun body' =>
              (nfToCat k (TRd.liftApp cs σ)).map fun k' =>
                NFProg.forLoop (cs := cs.map catTy) c is body' k'
        | .lit _ _ => none) = some p' at h
      obtain ⟨c, hc⟩ : ∃ c, σ count = .var c := by
        rcases hcnt' : σ count with c | ⟨_, _⟩
        · exact ⟨c, rfl⟩
        · rw [hcnt'] at h
          cases h
      rw [hc] at h
      obtain ⟨is, his, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨body', hb', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      have hcnt : (count.lookup V : BitVec 64) = c.lookup W := by
        have := hag _ count
        rw [hc] at this
        exact this
      change (forIterLeak
          (fun i acc => nfLeakRun bi fuel body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 i) V)))
          (List.range (count.lookup V : BitVec 64).toNat) (Expr.lookupArgs inits V)).bind
          (fun a => (nfLeakRun bi fuel k (hvAppend a.1 V)).map fun q =>
            (q.1, .trip (count.lookup V : BitVec 64).toNat :: (a.2 ++ q.2))) = some r at hr
      obtain ⟨a, ha, hr⟩ := Option.bind_eq_some_iff.mp hr
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hr
      have key : ∀ (l : List Nat) (acc : Valuation (d := nfDialect) cs)
          (acc' : Valuation (d := catCryptDialect) (cs.map catTy))
          (a : Valuation (d := nfDialect) cs × List CTLeak), VRelL cs acc acc' →
          forIterLeak (fun i acc => nfLeakRun bi fuel body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 i) V))) l acc =
            some a →
          ∃ a', forIterLeak (fun i acc => NFProg.leakRun (catLeakModel P) fuel body'
            (hvAppend acc (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 i) W)))
            l acc' = some a' ∧ a'.2 = a.2 ∧ VRelL cs a.1 a'.1 := by
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
              (TRd.agree_lift (s := NfTy.word 64) hag (x := BitVec.ofNat 64 j)
                (y := BitVec.ofNat 64 j) rfl) cs acc acc' hr
            obtain ⟨a1', ha1', he1, hr1⟩ := ihb (TRd.liftApp cs (TRd.lift σ)) body' hb' _ _ a1
              hag1 ha1
            obtain ⟨a2', ha2', he2, hr2⟩ := ih a1.1 a1'.1 a2 hr1 ha2
            refine ⟨(a2'.1, a1'.2 ++ a2'.2), ?_, ?_, hr2⟩
            · simp only [forIterLeak]
              erw [ha1']
              rw [Option.bind_some, ha2', Option.map_some]
            · simp only [he1, he2]
      obtain ⟨a', ha', he, hrA⟩ := key _ _ _ a
        (pinVars_rel _ _ is his (TRd.rdRelL_rds hag inits)) ha
      obtain ⟨q', hq', heq, hR⟩ := ihk (TRd.liftApp cs σ) k' hk' (hvAppend a.1 V)
        (hvAppend a'.1 W) q (TRd.agree_liftApp hag cs a.1 a'.1 hrA) hq
      refine ⟨(q'.1, .trip (c.lookup W).toNat :: (a'.2 ++ q'.2)), ?_, ?_, hR⟩
      · simp only [NFProg.leakRun]
        have hc2 : HasWord64.toNat (d := catCryptDialect) (c.lookup W) =
            (count.lookup V : BitVec 64).toNat := by
          rw [← hcnt]; rfl
        rw [hc2]
        erw [ha']
        rw [Option.bind_some, hq', Option.map_some, ← hcnt]
      · simp only [he, heq, ← hcnt]
  | ifThenElse cond thn els k _ _ _ =>
      intro Δ σ p' h
      cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ p' h
      cases h

/-- **The leakage transformer of `nfToCat` at the entry.** A leakage run of `p` that succeeds
    from a valuation `V` in range is matched by the leakage run of the translation from the
    mapped valuation `mapVal V`, with the same events. -/
theorem nfToCat_leak_id {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p : NFProg nfDialect Γ ts} {p' : NFProg catCryptDialect (Γ.map catTy) (ts.map catTy)}
    (hp : nfToCat p TRd.id = some p') (V : Valuation Γ)
    (hin : ∀ (t : NfTy) (v : Var Γ t), InRange t (v.lookup V))
    {r : Valuation (d := nfDialect) ts × List CTLeak} (hr : nfLeakRun bi fuel p V = some r) :
    ∃ r', NFProg.leakRun (catLeakModel P) fuel p' (mapVal V) = some r' ∧ r'.2 = r.2 := by
  obtain ⟨s, hs, he, -⟩ := nfToCat_leak hP hbi fuel p TRd.id p' hp V (mapVal V) r
    (TRd.agree_id V hin) hr
  exact ⟨s, hs, he⟩

/-- **Constant time through `nfToCat`, relative to source runs.** When `p` is constant time
    for `L` relative to the runs that succeed (`NFCTRel`), the translation emits equal
    events from the mapped valuations of two valuations in range that agree on the positions
    `L` marks public and from which `p` runs. -/
theorem nfToCat_ctRel {P : CatLeakParams} (hP : NoVT P) {bi : _root_.Hax.Builtins}
    (hbi : SubTable bi) (fuel : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p : NFProg nfDialect Γ ts} {p' : NFProg catCryptDialect (Γ.map catTy) (ts.map catTy)}
    (hp : nfToCat p TRd.id = some p') (L : Labels Γ)
    (hct : @NFCTRel nfDialect _ _ _ _ (nfDenote (ImpToNF.tableOf bi)) nfLeakModel Γ ts L fuel p)
    (V₁ V₂ : Valuation Γ) (hin₁ : ∀ (t : NfTy) (v : Var Γ t), InRange t (v.lookup V₁))
    (hin₂ : ∀ (t : NfTy) (v : Var Γ t), InRange t (v.lookup V₂)) (hpub : PubEqV L V₁ V₂)
    {r₁ r₂ : Valuation (d := nfDialect) ts × List CTLeak}
    (h₁ : nfLeakRun bi fuel p V₁ = some r₁) (h₂ : nfLeakRun bi fuel p V₂ = some r₂) :
    (NFProg.leakRun (catLeakModel P) fuel p' (mapVal V₁)).map Prod.snd =
      (NFProg.leakRun (catLeakModel P) fuel p' (mapVal V₂)).map Prod.snd := by
  obtain ⟨s₁, hs₁, e₁⟩ := nfToCat_leak_id hP hbi fuel hp V₁ hin₁ h₁
  obtain ⟨s₂, hs₂, e₂⟩ := nfToCat_leak_id hP hbi fuel hp V₂ hin₂ h₂
  rw [hs₁, hs₂, Option.map_some, Option.map_some, e₁, e₂, hct V₁ V₂ r₁ r₂ hpub h₁ h₂]

end CatCrypt.Crypto.Hax.NFToCat
