/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNFCond

/-!
# The front `impToNF` at the level of call trees: the counted loops

The relation `RelT` of `NFCallTreeImpToNF` for the counted loops `forFold` and `forFoldRev`,
and the theorem `impToNF_relT`: the front relates the call trees of every expression it
translates, at every target fuel at least the source fuel. The trips of a source loop at the
fuel `f` are related to the fold of the target body over the trip indices, each target body at
the target fuel `tf ≥ f` (`forTrips_relT`, `revTrips_relT`); the bounds, the trip count and the
counter bindings of the front have trees with one leaf.

## Main definitions

* `forBodyK`, `revBodyK`: the continuations of a trip of the source loops after the body.

## Main results

* `ctrOut_tree`, `atomOut_tree`, `loOut_tree`: the trees of the bindings of the counter, of an
  atom and of the lower bound.
* `forTrips_relT`, `revTrips_relT`, `loopOut_relT`: the trips and the counted loop of the front.
* `forFold_relT`, `forFoldRev_relT`: the counted loops.
* `impToNF_relT`: the front relates the call trees.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF

open _root_.Hax (ImpExpr ImpLit Value Env Outcome)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax.ImpToNF
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (LeafCall leafSig linkReader
  opTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm (LeafP)
open _root_.Hax.InlineLocalClosures (frameOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc bind_ret)
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## The counted loops -/

section ForRel

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- The continuation of a trip of `denoteForLoopT` after the body. -/
def forBodyK (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) :
    Outcome × Env → CallTree linkSig (Outcome × Env)
  | (.val (.controlFlow true v), e2) => .ret (.val v, e2)
  | (.val (.controlFlow false _), e2) => denoteForLoopT evTable n i (lo + 1) hi body e2
  | (.val _, e2) => denoteForLoopT evTable n i (lo + 1) hi body e2
  | (o, e2) => .ret (o, e2)

/-- One trip of a `forFold` loop at `lo < hi`, with the continuation `forBodyK`. -/
theorem forLoopT_succ_runK (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    denoteForLoopT evTable (n + 1) i lo hi body env =
      (denoteT evTable (n + 1) body (env.extend i (.int lo))).bind
        (forBodyK n i lo hi body) := by
  rw [NFCallTreeWhileTrue.forLoopT_succ_run (bt := evTable) n i lo hi body env h]
  congr 1

/-- The continuation of a trip at a value that is not a control-flow value is the next trip. -/
theorem forBodyK_val (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) {w : Value}
    (hw : w.isControlFlow = false) (e2 : Env) :
    forBodyK n i lo hi body (.val w, e2) = denoteForLoopT evTable n i (lo + 1) hi body e2 := by
  cases w with
  | controlFlow k u => cases hw
  | _ => rfl

/-- **The trips of a counted loop.** When every trip `k` of the source body from an environment
    satisfying `Inv`, extended with the counter `lo + k`, is related to the target body at the
    trip index `k`, the source loop from the counter `lo + k` with `m` trips left and the fold of
    the target body over the trip indices `k, …, k + m - 1` are related. -/
theorem forTrips_relT (i : String) (body : ImpExpr) (lo h : Int) {Γ₃ : Ctxt nfDialect}
    (V₃ : Valuation Γ₃) {cs : List NfTy} (bodyP : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ₃) cs)
    (Inv : Env → Valuation (d := nfDialect) cs → Prop) (tf : Nat)
    (HS : ∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs), k < 2 ^ 64 →
      lo + (k : Int) < h → f ≤ tf → Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ v acc', r.1 = .val v ∧ v.isControlFlow = false ∧
          w = some acc' ∧ Inv r.2 acc') SrcFail
        (denoteT evTable f body (e.extend i (.int (lo + k))))
        (treeAt linkReader tE tf bodyP
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)))) :
    ∀ (m k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs),
      (h - (lo + k)).toNat = m → k + m < 2 ^ 64 → f ≤ tf → Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ accF, r.1 = .val .unit ∧ w = some accF ∧ Inv r.2 accF)
        SrcFail (denoteForLoopT evTable f i (lo + k) h body e)
        (ofoldl (fun a j => treeAt linkReader tE tf bodyP
          (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V₃)))
          (List.range' k m) acc) := by
  intro m
  induction m with
  | zero =>
    intro k f e acc hm _ _ hinv
    rw [NFCallTreeWhileTrue.forLoopT_ge_run f i _ h body e (by omega)]
    exact .ret ⟨acc, rfl, rfl, hinv⟩
  | succ m ih =>
    intro k f e acc hm hk hf hinv
    have hlt : lo + k < h := by omega
    cases f with
    | zero =>
      rw [NFCallTreeWhileTrue.forLoopT_zero_run i _ h body e hlt]
      exact .fail fun v h => by cases h
    | succ f =>
      rw [forLoopT_succ_runK f i _ h body e hlt, List.range'_succ]
      refine ruttS_obindK (HS k (f + 1) e acc (by omega) hlt hf hinv) (fun r acc' hr => ?_)
        (fun r w ⟨_, _, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hfl t => ?_)
      · obtain ⟨v, acc'', h1, hcf, hw, hinv'⟩ := hr
        cases hw
        rcases r with ⟨o1, e2⟩
        dsimp only at h1 hinv'
        subst h1
        rw [forBodyK_val f i _ h body hcf e2]
        have hk1 : lo + k + 1 = lo + ((k + 1 : Nat) : Int) := by push_cast; ring
        rw [hk1]
        exact ih (k + 1) f e2 _ (by omega) (by omega) (by omega) hinv'
      · rcases r with ⟨o1, e2⟩
        cases o1 with
        | val v => exact absurd rfl (hfl v)
        | _ => exact .fail hfl

/-- **The counter binding has a tree with one leaf.** From a valuation of the loop body at the
    trip index `k` related by `σB` to `env`, with the lower bound `lo ≥ 0` in `loV` and the
    counter `ctrVal` below `2 ^ 64`, the tree of the prefix of `ctrOut` is one leaf, at a
    valuation related by its environment of names to `env` whose variable encodes the
    counter. -/
theorem ctrOut_tree (tf : Nat) {Γ₃ : Ctxt nfDialect} (cs : List NfTy) (i : String)
    (σB : NfEnv (cs ++ NfTy.word 64 :: Γ₃)) (loV : Var Γ₃ NfTy.int)
    (rev : Option (Var Γ₃ (NfTy.word 64))) (acc : Valuation (d := nfDialect) cs)
    (V₃ : Valuation Γ₃) (k : Nat) (env : Env)
    (hB : EnvRel σB env (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)))
    (hk : k < 2 ^ 64) (lo : Int) (hlo : loV.lookup V₃ = lo) (hlo0 : 0 ≤ lo)
    (hc : ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64)) < 2 ^ 64) :
    ∃ W, preTreeAt linkReader tE tf (ctrOut cs i σB loV rev).pre
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
        .ret (some W) ∧
      EnvRel (ctrOut cs i σB loV rev).σ env W ∧
      enc (ctrOut cs i σB loV rev).t ((ctrOut cs i σB loV rev).res.lookup W) =
        .int (ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64))) := by
  have hkV : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  have hloA : (Var.shiftApp cs (Var.there loV)).lookup
      (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) = lo := by
    rw [Var.lookup_shiftApp, ← hlo]; rfl
  have hkA : (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))).lookup
      (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
      BitVec.ofNat 64 k := by
    rw [Var.lookup_shiftApp]; rfl
  cases rev with
  | none =>
    simp only [ctrVal, Option.map_none] at hc ⊢
    have hargs : Expr.lookupArgs (.cons (Var.shiftApp cs (Var.there loV))
        (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
        HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
          (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) .nil) := by
      show HVector.cons _ (HVector.cons _ .nil) = _
      rw [hloA, hkA]
    refine ⟨Ctxt.Valuation.extend (t := NfTy.word 64)
      (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
      (BitVec.ofNat 64 (lo + (k : Int)).toNat), ?_,
      hB.mapV (fun v => Var.there v) fun _ _ => rfl, enc_ofNat_word64 (by omega) hc⟩
    show preTreeAt linkReader tE tf (bind1N (some i) σB .ctr _).pre _ = _
    rw [preTreeAt_bind1N tE tf (some i) _ .ctr _ _ fun _ => rfl, hargs,
      nfDenoteOp_ctr _ lo _ hlo0 (by rw [hkV]; exact hc), hkV]
    rfl
  | some m =>
    simp only [ctrVal, Option.map_some] at hc ⊢
    obtain ⟨mv, hmv⟩ : ∃ mv : BitVec 64, m.lookup V₃ = mv := ⟨_, rfl⟩
    rw [hmv] at hc ⊢
    have hargs : Expr.lookupArgs (.cons (Var.shiftApp cs (Var.there m))
        (.cons (Var.shiftApp (d := nfDialect) cs (Var.here (Γ := Γ₃))) .nil))
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) =
        HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) mv
          (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) .nil) := by
      show HVector.cons _ (HVector.cons _ .nil) = _
      rw [hkA, Var.lookup_shiftApp, ← hmv]; rfl
    have hargs2 : Expr.lookupArgs (.cons (Var.there (Var.shiftApp cs (Var.there loV)))
        (.cons (@Var.here nfDialect (cs ++ NfTy.word 64 :: Γ₃) (NfTy.word 64)) .nil))
        (Ctxt.Valuation.extend (t := NfTy.word 64)
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
          (mv - BitVec.ofNat 64 k)) =
        HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) lo
          (HVector.cons (t := NfTy.word 64) (mv - BitVec.ofNat 64 k) .nil) := by
      show HVector.cons _ (HVector.cons _ .nil) = _
      rw [← hloA]; rfl
    refine ⟨Ctxt.Valuation.extend (t := NfTy.word 64) (Ctxt.Valuation.extend
      (t := NfTy.word 64)
      (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
      (mv - BitVec.ofNat 64 k))
      (BitVec.ofNat 64 (lo + ((mv - BitVec.ofNat 64 k).toNat : Int)).toNat), ?_,
      (hB.mapV (fun v => Var.there v) fun _ _ => rfl).mapV (fun v => Var.there v)
        fun _ _ => rfl,
      enc_ofNat_word64 (by omega) hc⟩
    show preTreeAt linkReader tE tf ((bind1 σB (.bin .sub 64) _).pre.append
      (bind1N (some i) _ .ctr _).pre) _ = _
    rw [preTreeAt_append, preTreeAt_bind1 tE tf σB (.bin .sub 64) _ _ fun _ => rfl, hargs]
    show preTreeAt linkReader tE tf (bind1N (some i) _ .ctr _).pre
      (Ctxt.Valuation.extend (t := NfTy.word 64)
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
        (mv - BitVec.ofNat 64 k)) = _
    refine (preTreeAt_bind1N tE tf (some i) _ .ctr _ _ fun _ => rfl).trans ?_
    refine congrArg CallTree.ret ((congrArg (fun a => Option.map
      (Ctxt.Valuation.extend (t := NfTy.word 64) (Ctxt.Valuation.extend (t := NfTy.word 64)
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
        (mv - BitVec.ofNat 64 k))) (nfDenoteOp NfLeafTable.empty .ctr a)) hargs2).trans ?_)
    rw [nfDenoteOp_ctr _ lo _ hlo0 hc]
    rfl

end ForRel


section LoopOut

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- **The counted loop of the front relates the trees.** Let the tree of the prefix `pre₀` be
    one leaf at `V₃`, related by `σ₃` to `env`, with `lo` in `loV` and the trip count
    `(h - lo).toNat` in `tripV`; let the names `xs` carry the values of `inits`, every name of
    `σ₃` other than `i` and the names `xs` be one the body does not bind, and `rec` relate the
    trees of the body. When the source tree `src` is related to the fold of every target body
    whose trips are related to the source body at the counters `ctrVal` (`HL`), the source tree
    is related to the tree of the output of `loopOut`. -/
theorem loopOut_relT (tf : Nat) (body : ImpExpr) (tgt : Option String)
    {Γ Γ₃ : Ctxt nfDialect} (pre₀ : NFPre nfDialect Γ Γ₃) (σ₃ : NfEnv Γ₃)
    (loV : Var Γ₃ NfTy.int) (tripV : Var Γ₃ (NfTy.word 64))
    (rev : Option (Var Γ₃ (NfTy.word 64))) (i : String) (xs : List String)
    (cs : List NfTy) (inits : HVector (fun t => Var Γ₃ t) cs)
    (rec : ∀ {Δ : Ctxt nfDialect}, NfEnv Δ → Option (Out Δ)) {o : Out Γ}
    (h₀ : loopOut tgt pre₀ σ₃ loV tripV rev i xs cs inits rec = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ}, rec σ' = some o' →
      ∀ fuel', fuel' ≤ tf → RelT h₁ tE fuel' tf body σ' o')
    (hlen : xs.length = cs.length)
    (hfr : ∀ x, x ∉ xs → x ≠ i → ∀ q, σ₃.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) body = true)
    (env : Env) (V : Valuation Γ) (V₃ : Valuation Γ₃)
    (hpre : preTreeAt linkReader tE tf pre₀ V = .ret (some V₃)) (hrel : EnvRel σ₃ env V₃)
    (hcar : CarriedRel env xs cs (Expr.lookupArgs inits V₃)) (lo h : Int)
    (hlo : loV.lookup V₃ = lo) (htrip : tripV.lookup V₃ = BitVec.ofNat 64 (h - lo).toNat)
    (hM : (h - lo).toNat < 2 ^ 64) (hlo0 : 0 ≤ lo) (hh64 : h ≤ 2 ^ 64)
    (hrev : ∀ m, rev = some m →
      (m.lookup V₃ : BitVec 64) = BitVec.ofNat 64 (h - lo).toNat - 1)
    (src : CallTree linkSig (Outcome × Env))
    (HL : ∀ (Inv : Env → Valuation (d := nfDialect) cs → Prop)
      (bodyP : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ₃) cs),
      (∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs), k < 2 ^ 64 →
        lo + (k : Int) < h → f ≤ tf → Inv e acc →
        RuttS h₁ ImpRE ImpRA (fun r w => ∃ v acc', r.1 = .val v ∧ v.isControlFlow = false ∧
            w = some acc' ∧ Inv r.2 acc') SrcFail
          (denoteT evTable f body
            (e.extend i (.int (ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64))))))
          (treeAt linkReader tE tf bodyP
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)))) →
      Inv env (Expr.lookupArgs inits V₃) →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ accF, r.1 = .val .unit ∧ w = some accF ∧ Inv r.2 accF)
        SrcFail src
        (ofoldl (fun a j => treeAt linkReader tE tf bodyP
          (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V₃)))
          (List.range' 0 (h - lo).toNat) (Expr.lookupArgs inits V₃))) :
    RuttS h₁ ImpRE ImpRA (LeafRel o) SrcFail src (preTreeAt linkReader tE tf o.pre V) := by
  simp only [loopOut, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₀
  obtain ⟨ob, hob, rets, hrets, rfl⟩ := h₀
  let Inv : Env → Valuation (d := nfDialect) cs → Prop := fun e acc =>
    CarriedRel e xs cs acc ∧ FrameRel σ₃ i xs e V₃
  have hcv : ∀ k : Nat, lo + (k : Int) < h →
      ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64)) =
        (rev.map fun m => (m.lookup V₃ : BitVec 64)).elim (lo + k) fun _ => h - 1 - k :=
    fun k hk => ctrVal_trip lo h k hM hk (rev.map fun m => (m.lookup V₃ : BitVec 64))
      fun m hm => by
        obtain ⟨m', hm', hmm⟩ := Option.map_eq_some_iff.mp hm
        rw [← hmm]
        exact hrev m' hm'
  have hfr' : ∀ x, x ∉ i :: xs → ∀ q, σ₃.lookup x = some q →
      frameOk (fun _ => true) (fun n => n != x) (fun _ => true) body = true :=
    fun x hx q hq => hfr x (fun h => hx (List.mem_cons_of_mem _ h))
      (fun h => hx (h ▸ List.mem_cons_self)) q hq
  have HS : ∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs), k < 2 ^ 64 →
      lo + (k : Int) < h → f ≤ tf → Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ v acc', r.1 = .val v ∧ v.isControlFlow = false ∧
          w = some acc' ∧ Inv r.2 acc') SrcFail
        (denoteT evTable f body
          (e.extend i (.int (ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64))))))
        (treeAt linkReader tE tf ((NFPre.append (ctrOut cs i (loopEnv σ₃ i xs cs
            (headVars cs) fun v => Var.shiftApp (d := nfDialect) cs v.there) loV rev).pre
            ob.pre).plug (.ret rets))
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))) := by
    intro k f e acc hk hkh hf hinv
    have hB : EnvRel (loopEnv σ₃ i xs cs (headVars cs)
        fun v => Var.shiftApp (d := nfDialect) cs v.there) e
        (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)) :=
      EnvRel.loopEnv σ₃ i xs cs hlen (headVars cs) _
        (W := hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃))
        (by rw [lookupArgs_headVars]; exact hinv.1) hinv.2
        (by intro t v; rw [Var.lookup_shiftApp]; rfl)
    have hc : ctrVal lo k (rev.map fun m => (m.lookup V₃ : BitVec 64)) < 2 ^ 64 := by
      rw [hcv k hkh]
      generalize (rev.map fun m => (m.lookup V₃ : BitVec 64)) = q
      cases q <;> simp only [Option.elim] <;> omega
    obtain ⟨Wc, hWc, hrelC, hencC⟩ := ctrOut_tree (tE := tE) tf cs i _ loV rev acc V₃ k e hB hk
      lo hlo hlo0 hc
    rw [treeAt_plug, preTreeAt_append, hWc, obind_ret_some, ← hencC,
      ← bind_ret (denoteT evTable f body _)]
    refine ruttS_obindK (ruttS_srcLeaf (HB _ hob f hf _ Wc (hrelC.cons i _ _))
      (keeps_leafP body σ₃ (i :: xs) hfr' f _)) (fun r x hr => ?_)
      (fun r w ⟨⟨_, _, _, hw, _⟩, _⟩ => ⟨_, hw⟩) (fun r hfl t => .fail hfl)
    obtain ⟨⟨v, W', h1, hW, hrel', hv⟩, hkp⟩ := hr
    cases hW
    refine .ret ⟨v, _, h1, by rw [hv]; exact enc_isControlFlow _ _, rfl,
      CarriedRel.of_varsAt hrel' xs cs hrets, fun x hx hxi t u hl => ?_⟩
    rcases hkp x with he | hm | hn | hkx
    · rw [h1] at he
      obtain ⟨_, he⟩ := he
      cases he
    · rcases List.mem_cons.mp hm with hm | hm
      · exact absurd hm hxi
      · exact absurd hm hx
    · rw [hl] at hn
      cases hn
    · refine hkx.trans ?_
      rw [Env.extend_other _ _ _ _ hxi]
      exact hinv.2 x hx hxi t u hl
  have hfold := HL Inv _ HS ⟨hcar, fun x _ _ t v hl => hrel x t v hl⟩
  show RuttS _ _ _ _ _ src (preTreeAt linkReader tE tf (pre₀.append (.forLoop tripV inits
    ((NFPre.append (ctrOut cs i (loopEnv σ₃ i xs cs (headVars cs)
      fun v => Var.shiftApp (d := nfDialect) cs v.there) loV rev).pre ob.pre).plug (.ret rets))
    (bind1N tgt (loopEnv σ₃ i xs cs (headVars cs) fun v => Var.shiftApp cs v)
      .constUnit .nil).pre)) V)
  rw [preTreeAt_append, hpre, obind_ret_some]
  show RuttS _ _ _ _ _ src (obind (ofoldl _ (List.range (tripV.lookup V₃).toNat) _) _)
  rw [htrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hM, List.range_eq_range', ← bind_ret src]
  refine ruttS_obindK hfold (fun r accF hr => ?_) (fun r w ⟨_, _, hw, _⟩ => ⟨_, hw⟩)
    (fun r hfl t => .fail hfl)
  obtain ⟨accF', h1, hacc, hinvF⟩ := hr
  cases hacc
  rw [preTreeAt_bind1N tE tf tgt _ .constUnit .nil _ fun _ => rfl]
  rcases r with ⟨o1, e'⟩
  dsimp only at h1 hinvF
  subst h1
  have hL := EnvRel.loopEnv σ₃ i xs cs hlen (headVars cs) (fun v => Var.shiftApp cs v)
    (W := hvAppend accF V₃) (by rw [lookupArgs_headVars]; exact hinvF.1) hinvF.2
    (fun t v => Var.lookup_shiftApp cs accF v V₃)
  exact .ret ⟨_, _, rfl, rfl, hL.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩

/-- An atom has a tree with one leaf, and its source reading a leaf with the same
    environment. -/
theorem atomOut_tree (tf fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (a : ImpExpr)
    {o : Out Γ} (h : atomOut σ a = some o) (env : Env) (V : Valuation Γ)
    (hrel : EnvRel σ env V) :
    ∃ W v, preTreeAt linkReader tE tf o.pre V = .ret (some W) ∧
      denoteT evTable fuel a env = .ret (.val v, env) ∧ EnvRel o.σ env W ∧
      v = enc o.t (o.res.lookup W) := by
  cases a with
  | var x =>
    simp only [atomOut, Option.map_eq_some_iff] at h
    obtain ⟨⟨t, r⟩, hx, rfl⟩ := h
    exact ⟨V, _, rfl, NFCallTreeRepeatCount.denoteT_var_run evTable fuel x env _
      (hrel x t r hx), hrel, rfl⟩
  | lit l =>
    have hs := NFCallTreeRepeatCount.denoteT_lit_run evTable fuel l env
    cases l with
    | bool b =>
      simp only [atomOut, litOut, Option.some.injEq] at h
      subst h
      exact ⟨V.extend b, _, by rw [preTreeAt_bind1N tE tf none σ _ _ V fun _ => rfl]; rfl, hs,
        hrel.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
    | unit =>
      simp only [atomOut, litOut, Option.some.injEq] at h
      subst h
      exact ⟨V.extend (), _, by rw [preTreeAt_bind1N tE tf none σ _ _ V fun _ => rfl]; rfl, hs,
        hrel.mapV (fun v => Var.there v) fun _ _ => rfl, rfl⟩
    | int n | uintLit W n | sintLit W n =>
      simp only [atomOut, litOut, Option.bind_eq_some_iff] at h
      obtain ⟨⟨t, v⟩, hl, hs'⟩ := h
      split at hs'
      · rename_i hsome
        simp only [Option.some.injEq] at hs'
        subst hs'
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
        dsimp only at hx
        exact ⟨V.extend x, _, by
          rw [preTreeAt_bind1N tE tf none σ _ _ V fun _ => rfl]
          exact congrArg (fun q => CallTree.ret (Option.map V.extend q)) hx,
          hs, hrel.mapV (fun v => Var.there v) fun _ _ => rfl, ofLit_enc hl hx⟩
      · cases hs'
  | _ => simp [atomOut] at h

/-- **The lower bound of a counted loop.** When `loOut` accepts the lower bound `lo`, its source
    reading is a leaf with the same environment and the integer `z` (`.int z` or `.uint _ z`),
    `0 ≤ z < 2 ^ 64`, and the tree of the binding `loBind` is one leaf extending `V` with
    `z`. -/
theorem loOut_tree (tf fuel : Nat) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) (lo : ImpExpr)
    {e : Expr nfDialect Γ NfTy.int} (h : loOut σ lo = some e) (env : Env) (V : Valuation Γ)
    (hrel : EnvRel σ env V) :
    ∃ (z : Int) (vlo : Value), denoteT evTable fuel lo env = .ret (.val vlo, env) ∧
      (vlo = .int z ∨ ∃ W, ∃ n : Nat, vlo = .uint W n ∧ (n : Int) = z) ∧ 0 ≤ z ∧
      z < 2 ^ 64 ∧ preTreeAt linkReader tE tf (loBind σ e).pre V =
        .ret (some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) z V)) := by
  cases lo with
  | lit l =>
    cases l with
    | int n =>
      simp only [loOut] at h
      split at h
      · rename_i hn
        cases h
        exact ⟨n, .int n, NFCallTreeRepeatCount.denoteT_lit_run evTable fuel _ env, .inl rfl,
          hn.1, hn.2, (preTreeAt_bind1 tE tf σ (.ilit .int n) .nil V fun _ => rfl).trans rfl⟩
      · cases h
    | _ => simp [loOut] at h
  | var x =>
    simp only [loOut, Option.bind_eq_some_iff] at h
    obtain ⟨⟨t, v⟩, hx, h⟩ := h
    split at h
    · rename_i ht
      cases h
      have he := hrel x t v hx
      cases t with
      | uint W =>
        have h1 := (v.lookup V).isLt
        have h2 : 2 ^ W.bits ≤ 2 ^ 64 :=
          Nat.pow_le_pow_right (by norm_num) (by simpa [loTyOk] using ht)
        exact ⟨((v.lookup V).toNat : Int), .uint W (v.lookup V).toNat,
          NFCallTreeRepeatCount.denoteT_var_run evTable fuel x env _ he, .inr ⟨W, _, rfl, rfl⟩,
          by omega, by omega,
          (preTreeAt_bind1 tE tf σ (.boundInt (.uint W)) (.cons v .nil) V fun _ => rfl).trans
            rfl⟩
      | word w =>
        have h1 := (v.lookup V).isLt
        have hw : w = 64 := by simpa [loTyOk] using ht
        subst hw
        exact ⟨((v.lookup V).toNat : Int), .int (v.lookup V).toNat,
          NFCallTreeRepeatCount.denoteT_var_run evTable fuel x env _ he, .inl rfl, by omega,
          by omega,
          (preTreeAt_bind1 tE tf σ (.boundInt (.word 64)) (.cons v .nil) V fun _ => rfl).trans
            rfl⟩
      | _ => simp [loTyOk] at ht
    · cases h
  | _ => simp [loOut] at h

/-- The source reading of a `forFold` whose bounds read as leaves with the integers `l` and `h`
    at the same environment is the reading of the loop from `l` to `h`. -/
theorem forFold_runT_ints (fuel : Nat) (i : String) (lo hi body : ImpExpr) (env : Env)
    {vlo vhi : Value} {l h : Int}
    (hlo : denoteT evTable fuel lo env = .ret (.val vlo, env))
    (hhi : denoteT evTable fuel hi env = .ret (.val vhi, env))
    (hl : vlo = .int l ∨ ∃ W, ∃ n : Nat, vlo = .uint W n ∧ (n : Int) = l)
    (hh : vhi = .int h ∨ ∃ W, ∃ n : Nat, vhi = .uint W n ∧ (n : Int) = h) :
    denoteT evTable fuel (.forFold i lo hi body) env =
      denoteForLoopT evTable fuel i l h body env := by
  rw [denoteT, NFCallTreeRepeatCount.tm_bind_run, hlo]
  rcases hl with rfl | ⟨_, _, rfl, rfl⟩ <;>
  · show (denoteT evTable fuel hi >>= _) env = _
    rw [NFCallTreeRepeatCount.tm_bind_run, hhi]
    rcases hh with rfl | ⟨_, _, rfl, rfl⟩ <;> rfl

/-- A `forFold` whose upper bound translates to an integer literal reads it as that literal. -/
theorem hiLit_enc {fuel : Nat} {hi : ImpExpr} {env : Env} {t : NfTy} {x : t.denote}
    (hh : denoteT evTable fuel hi env = .ret (.val (enc t x), env)) :
    ∀ n, hi = .lit (.int n) → enc t x = .int n := by
  intro n hn
  subst hn
  rw [NFCallTreeRepeatCount.denoteT_lit_run] at hh
  injection hh with h1
  injection h1 with h2
  injection h2 with h3
  exact h3.symm

/-- **A counted loop relates the trees**, at every target fuel at least the source fuel, when
    the front relates the trees of its body at every such pair of fuels. -/
theorem forFold_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (hle : fuel ≤ tf) (tgt : Option String) (i : String) (lo hi body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.forFold i lo hi body) = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ},
      impToNF sigOf none σ' body = some o' → ∀ fuel' tf', fuel' ≤ tf' →
        RelT h₁ tE fuel' tf' body σ' o') :
    RelT h₁ tE fuel tf (.forFold i lo hi body) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨eLo, hLoE, oHi, hHi, hL⟩ := h
  split at hL
  case isFalse => cases hL
  rename_i hbd
  intro env V hrel
  obtain ⟨z, vlo, hl, hz, hz0, hz64, hLo⟩ := loOut_tree (tE := tE) tf fuel σ lo hLoE env V hrel
  have hrelLo : EnvRel (loBind σ eLo).σ env
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) z V) :=
    hrel.mapV (fun v => Var.there v) fun _ _ => rfl
  obtain ⟨W2, vhi, hW2, hh, hrel2, rfl⟩ := atomOut_tree (tE := tE) tf fuel _ hi hHi env _ hrelLo
  obtain ⟨hInt, htoInt⟩ := exists_toInt_of_bound hbd (hiLit_enc hh)
  have hloW : (oHi.pre.wk (loBind σ eLo).res).lookup W2 = z :=
    (preTreeAt_wk_of_ret hW2 _ _).trans rfl
  have hargsT : Expr.lookupArgs (HVector.cons (oHi.pre.wk (loBind σ eLo).res)
      (HVector.cons oHi.res .nil)) W2 =
      HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) z
        (HVector.cons (t := oHi.t) (oHi.res.lookup W2) .nil) := by
    show HVector.cons ((oHi.pre.wk (loBind σ eLo).res).lookup W2)
      (HVector.cons (oHi.res.lookup W2) .nil) = _
    rw [hloW]
    rfl
  have hTrip : preTreeAt linkReader tE tf (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).pre W2 =
      .ret (some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat) W2)) := by
    refine (preTreeAt_bind1 tE tf _ (.trip oHi.t) _ W2 fun _ => rfl).trans ?_
    refine congrArg CallTree.ret ((congrArg (fun a => Option.map _
      (nfDenoteOp NfLeafTable.empty (.trip oHi.t) a)) hargsT).trans ?_)
    show Option.map _ ((NfTy.toInt? oHi.t (oHi.res.lookup W2)).map
      fun hi => BitVec.ofNat 64 (hi - z).toNat) = _
    rw [htoInt]
    rfl
  have hrelT : EnvRel (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).σ env
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat) W2) :=
    hrel2.mapV (fun v => Var.there v) fun _ _ => rfl
  have hrange := bound_range hbd htoInt (hiLit_enc hh)
  have hM := trip_lt_of_bound hbd htoInt (hiLit_enc hh)
  rw [forFold_runT_ints fuel i lo hi body env hl hh hz (enc_toInt_cases htoInt)]
  refine loopOut_relT tf body tgt _ _ _ _ _ i _ _ _ _ hL
    (fun σ' _ h' fuel' hf => HB σ' h' fuel' tf hf)
    (by rw [List.length_map, entriesVars_length])
    (fun x hx hxi _ hl => frameOk_of_not_carried _ i body hl hxi hx)
    env V _ ?_ hrelT (CarriedRel.of_entries hrelT _ (carried_lookup _ i body)) z hInt hloW rfl
    (by omega) hz0 (by omega) (fun _ h => by cases h) _ fun Inv bodyP HS hinv => ?_
  · rw [preTreeAt_append, preTreeAt_append, hLo]
    exact (congrArg (fun t => obind t _) hW2).trans hTrip
  · have := forTrips_relT (h₁ := h₁) (tE := tE) i body z hInt _ bodyP Inv tf
      (fun k f e acc hk hkh hf hinv => HS k f e acc hk hkh hf hinv) ((hInt - z).toNat) 0
      fuel env _ (by simp) (by omega) hle hinv
    rwa [Nat.cast_zero, Int.add_zero] at this

end LoopOut


/-! ## The reverse counted loop -/

section ForRevRel

variable {h₁ : ∀ e : linkSig.Event, linkSig.Resp e} {tE : TreeCallEnv leafSig nfDialect}

/-- The continuation of a trip of `denoteForLoopRevT` after the body. -/
def revBodyK (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) :
    Outcome × Env → CallTree linkSig (Outcome × Env)
  | (.val (.controlFlow true v), e2) => .ret (.val v, e2)
  | (.val (.controlFlow false _), e2) => denoteForLoopRevT evTable n i lo (hi - 1) body e2
  | (.val _, e2) => denoteForLoopRevT evTable n i lo (hi - 1) body e2
  | (o, e2) => .ret (o, e2)

/-- A `forFoldRev` loop at `lo ≥ hi` is a leaf. -/
theorem forLoopRevT_ge_run (fuel : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : hi ≤ lo) :
    denoteForLoopRevT evTable fuel i lo hi body env = .ret (.val .unit, env) := by
  rw [denoteForLoopRevT, ite_eq_left h]; rfl

/-- A `forFoldRev` loop at `lo < hi` without fuel is a leaf. -/
theorem forLoopRevT_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    denoteForLoopRevT evTable 0 i lo hi body env = .ret (.err "out of fuel", env) := by
  rw [denoteForLoopRevT, ite_eq_right (Int.not_le.mpr h), ite_eq_left rfl]; rfl

/-- One trip of a `forFoldRev` loop at `lo < hi`, with the continuation `revBodyK`. -/
theorem forLoopRevT_succ_runK (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    denoteForLoopRevT evTable (n + 1) i lo hi body env =
      (denoteT evTable (n + 1) body (env.extend i (.int (hi - 1)))).bind
        (revBodyK n i lo hi body) := by
  rw [denoteForLoopRevT, ite_eq_right (Int.not_le.mpr h), ite_eq_right (Nat.add_one_ne_zero n)]
  change (denoteT evTable (n + 1) body (env.extend i (.int (hi - 1)))).bind _ = _
  congr 1
  funext p
  rcases p with ⟨o, e2⟩
  rcases o with w | _ | _ | _ | _
  · cases w with
    | controlFlow k u => cases k <;> rfl
    | _ => rfl
  all_goals rfl

/-- The continuation of a reverse trip at a value that is not a control-flow value is the next
    trip. -/
theorem revBodyK_val (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) {w : Value}
    (hw : w.isControlFlow = false) (e2 : Env) :
    revBodyK n i lo hi body (.val w, e2) = denoteForLoopRevT evTable n i lo (hi - 1) body e2 := by
  cases w with
  | controlFlow k u => cases hw
  | _ => rfl

/-- **The trips of a reverse counted loop.** When every trip `k` of the source body from an
    environment satisfying `Inv`, extended with the counter `h - 1 - k`, is related to the
    target body at the trip index `k`, the source loop on the range from `lo` to `h - k` with
    `m` trips left and the fold of the target body over the trip indices `k, …, k + m - 1` are
    related. -/
theorem revTrips_relT (i : String) (body : ImpExpr) (lo h : Int) {Γ₃ : Ctxt nfDialect}
    (V₃ : Valuation Γ₃) {cs : List NfTy} (bodyP : NFProg nfDialect (cs ++ NfTy.word 64 :: Γ₃) cs)
    (Inv : Env → Valuation (d := nfDialect) cs → Prop) (tf : Nat)
    (HS : ∀ (k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs), k < 2 ^ 64 →
      lo + (k : Int) < h → f ≤ tf → Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ v acc', r.1 = .val v ∧ v.isControlFlow = false ∧
          w = some acc' ∧ Inv r.2 acc') SrcFail
        (denoteT evTable f body (e.extend i (.int (h - 1 - k))))
        (treeAt linkReader tE tf bodyP
          (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 k) V₃)))) :
    ∀ (m k f : Nat) (e : Env) (acc : Valuation (d := nfDialect) cs),
      (h - k - lo).toNat = m → k + m < 2 ^ 64 → f ≤ tf → Inv e acc →
      RuttS h₁ ImpRE ImpRA (fun r w => ∃ accF, r.1 = .val .unit ∧ w = some accF ∧ Inv r.2 accF)
        SrcFail (denoteForLoopRevT evTable f i lo (h - k) body e)
        (ofoldl (fun a j => treeAt linkReader tE tf bodyP
          (hvAppend a (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V₃)))
          (List.range' k m) acc) := by
  intro m
  induction m with
  | zero =>
    intro k f e acc hm _ _ hinv
    rw [forLoopRevT_ge_run f i lo _ body e (by omega)]
    exact .ret ⟨acc, rfl, rfl, hinv⟩
  | succ m ih =>
    intro k f e acc hm hk hf hinv
    have hlt : lo < h - k := by omega
    cases f with
    | zero =>
      rw [forLoopRevT_zero_run i lo _ body e hlt]
      exact .fail fun v h => by cases h
    | succ f =>
      have hc : h - (k : Int) - 1 = h - 1 - k := by ring
      rw [forLoopRevT_succ_runK f i lo _ body e hlt, List.range'_succ, hc]
      refine ruttS_obindK (HS k (f + 1) e acc (by omega) (by omega) hf hinv)
        (fun r acc' hr => ?_) (fun r w ⟨_, _, _, _, hw, _⟩ => ⟨_, hw⟩) (fun r hfl t => ?_)
      · obtain ⟨v, acc'', h1, hcf, hw, hinv'⟩ := hr
        cases hw
        rcases r with ⟨o1, e2⟩
        dsimp only at h1 hinv'
        subst h1
        rw [revBodyK_val f i lo _ body hcf e2]
        have hk1 : h - (k : Int) - 1 = h - ((k + 1 : Nat) : Int) := by push_cast; ring
        rw [hk1]
        exact ih (k + 1) f e2 _ (by omega) (by omega) (by omega) hinv'
      · rcases r with ⟨o1, e2⟩
        cases o1 with
        | val v => exact absurd rfl (hfl v)
        | _ => exact .fail hfl

/-- The source reading of a `forFoldRev` whose bounds read as leaves with the integers `l` and
    `h` at the same environment is the reading of the reverse loop from `l` to `h`. -/
theorem forFoldRev_runT_ints (fuel : Nat) (i : String) (lo hi body : ImpExpr) (env : Env)
    {vlo vhi : Value} {l h : Int}
    (hlo : denoteT evTable fuel lo env = .ret (.val vlo, env))
    (hhi : denoteT evTable fuel hi env = .ret (.val vhi, env))
    (hl : vlo = .int l ∨ ∃ W, ∃ n : Nat, vlo = .uint W n ∧ (n : Int) = l)
    (hh : vhi = .int h ∨ ∃ W, ∃ n : Nat, vhi = .uint W n ∧ (n : Int) = h) :
    denoteT evTable fuel (.forFoldRev i lo hi body) env =
      denoteForLoopRevT evTable fuel i l h body env := by
  rw [denoteT, NFCallTreeRepeatCount.tm_bind_run, hlo]
  rcases hl with rfl | ⟨_, _, rfl, rfl⟩ <;>
  · show (denoteT evTable fuel hi >>= _) env = _
    rw [NFCallTreeRepeatCount.tm_bind_run, hhi]
    rcases hh with rfl | ⟨_, _, rfl, rfl⟩ <;> rfl

/-- **A reverse counted loop relates the trees**, at every target fuel at least the source
    fuel, when the front relates the trees of its body at every such pair of fuels: the counter
    of trip `k` is `lo + (trip - 1 - k)`, from the word `trip - 1` bound before the loop. -/
theorem forFoldRev_relT (sigOf : String → List NfTy → Option NfTy) (fuel tf : Nat)
    (hle : fuel ≤ tf) (tgt : Option String) (i : String) (lo hi body : ImpExpr)
    {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ}
    (h : impToNF sigOf tgt σ (.forFoldRev i lo hi body) = some o)
    (HB : ∀ {Δ : Ctxt nfDialect} (σ' : NfEnv Δ) {o' : Out Δ},
      impToNF sigOf none σ' body = some o' → ∀ fuel' tf', fuel' ≤ tf' →
        RelT h₁ tE fuel' tf' body σ' o') :
    RelT h₁ tE fuel tf (.forFoldRev i lo hi body) σ o := by
  simp only [impToNF, Option.bind_eq_some_iff] at h
  obtain ⟨eLo, hLoE, oHi, hHi, hL⟩ := h
  split at hL
  case isFalse => cases hL
  rename_i hbd
  intro env V hrel
  obtain ⟨z, vlo, hl, hz, hz0, hz64, hLo⟩ := loOut_tree (tE := tE) tf fuel σ lo hLoE env V hrel
  have hrelLo : EnvRel (loBind σ eLo).σ env
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) z V) :=
    hrel.mapV (fun v => Var.there v) fun _ _ => rfl
  obtain ⟨W2, vhi, hW2, hh, hrel2, rfl⟩ := atomOut_tree (tE := tE) tf fuel _ hi hHi env _ hrelLo
  obtain ⟨hInt, htoInt⟩ := exists_toInt_of_bound hbd (hiLit_enc hh)
  have hloW : (oHi.pre.wk (loBind σ eLo).res).lookup W2 = z :=
    (preTreeAt_wk_of_ret hW2 _ _).trans rfl
  have hargsT : Expr.lookupArgs (HVector.cons (oHi.pre.wk (loBind σ eLo).res)
      (HVector.cons oHi.res .nil)) W2 =
      HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.int) z
        (HVector.cons (t := oHi.t) (oHi.res.lookup W2) .nil) := by
    show HVector.cons ((oHi.pre.wk (loBind σ eLo).res).lookup W2)
      (HVector.cons (oHi.res.lookup W2) .nil) = _
    rw [hloW]
    rfl
  have hTrip : preTreeAt linkReader tE tf (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).pre W2 =
      .ret (some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat) W2)) := by
    refine (preTreeAt_bind1 tE tf _ (.trip oHi.t) _ W2 fun _ => rfl).trans ?_
    refine congrArg CallTree.ret ((congrArg (fun a => Option.map _
      (nfDenoteOp NfLeafTable.empty (.trip oHi.t) a)) hargsT).trans ?_)
    show Option.map _ ((NfTy.toInt? oHi.t (oHi.res.lookup W2)).map
      fun hi => BitVec.ofNat 64 (hi - z).toNat) = _
    rw [htoInt]
    rfl
  have hrelT : EnvRel (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).σ env
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat) W2) :=
    hrel2.mapV (fun v => Var.there v) fun _ _ => rfl
  have hOne : preTreeAt linkReader tE tf (bind1 (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).σ
      (.ilit (.word 64) 1) .nil).pre
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat) W2) =
      .ret (some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
          (BitVec.ofNat 64 (hInt - z).toNat) W2))) :=
    (preTreeAt_bind1 tE tf _ (.ilit (.word 64) 1) .nil _ fun _ => rfl).trans rfl
  have hSub : preTreeAt linkReader tE tf (bind1 (bind1 (bind1 oHi.σ (.trip oHi.t)
      (.cons (oHi.pre.wk (loBind σ eLo).res) (.cons oHi.res .nil))).σ
      (.ilit (.word 64) 1) .nil).σ (.bin .sub 64)
      (.cons (Var.there Var.here) (.cons Var.here .nil))).pre
      (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
          (BitVec.ofNat 64 (hInt - z).toNat) W2)) =
      .ret (some (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat - 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
          (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
            (BitVec.ofNat 64 (hInt - z).toNat) W2)))) :=
    (preTreeAt_bind1 tE tf _ (.bin .sub 64) _ _ fun _ => rfl).trans rfl
  have hrelM := (hrelT.mapV (fun v => Var.there (s := NfTy.word 64) v) fun _ _ => rfl).mapV
    (fun v => Var.there (s := NfTy.word 64) v)
    (W := HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
        (BitVec.ofNat 64 (hInt - z).toNat - 1)
        (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64) (BitVec.ofNat 64 1)
          (HVector.cons (f := fun t => ⟦t⟧) (t := NfTy.word 64)
            (BitVec.ofNat 64 (hInt - z).toNat) W2))) fun _ _ => rfl
  have hrange := bound_range hbd htoInt (hiLit_enc hh)
  have hM := trip_lt_of_bound hbd htoInt (hiLit_enc hh)
  rw [forFoldRev_runT_ints fuel i lo hi body env hl hh hz (enc_toInt_cases htoInt)]
  refine loopOut_relT tf body tgt _ _ _ _ _ i _ _ _ _ hL
    (fun σ' _ h' fuel' hf => HB σ' h' fuel' tf hf)
    (by rw [List.length_map, entriesVars_length])
    (fun x hx hxi _ hl => frameOk_of_not_carried _ i body hl hxi hx)
    env V _ ?_ hrelM (CarriedRel.of_entries hrelM _ (carried_lookup _ i body)) z hInt hloW rfl
    (by omega) hz0 (by omega) (fun _ hm => by cases hm; rfl) _ fun Inv bodyP HS hinv => ?_
  · rw [preTreeAt_append, preTreeAt_append, preTreeAt_append, preTreeAt_append, hLo]
    exact (congrArg (fun t => obind (obind (obind t _) _) _) hW2).trans
      ((congrArg (fun t => obind (obind t _) _) hTrip).trans
        ((congrArg (fun t => obind t _) hOne).trans hSub))
  · have hcv : ∀ k : Nat, z + (k : Int) < hInt →
        ctrVal z k (some (BitVec.ofNat 64 (hInt - z).toNat - 1)) = hInt - 1 - k :=
      fun k hk => ctrVal_trip z hInt k (by omega) hk _ fun _ hm => (Option.some.inj hm).symm
    have := revTrips_relT (h₁ := h₁) (tE := tE) i body z hInt _ bodyP Inv tf
      (fun k f e acc hk hkh hf hinv => by
        have := HS k f e acc hk hkh hf hinv
        erw [hcv k hkh] at this
        exact this)
      ((hInt - z).toNat) 0 fuel env _ (by simp) (by omega) hle hinv
    rwa [Nat.cast_zero, Int.sub_zero] at this

end ForRevRel


/-! ## The front relates the call trees -/

/-- **The front relates the call trees.** For every expression `e` the front translates from
    `σ`, every source fuel `fuel` and every target fuel `tf ≥ fuel`, the source tree of `e` at
    the tree table `evTable` and the tree of the prefix of the output are related by `RelT`, at
    every source handler that answers `repeat` as `RepeatCalls` states and every tree call
    environment of the target.

    The target fuel bounds only the iterations of `NFProg.whileLoop`. One fuel serves every
    branch: a source loop at the fuel `fuel` runs at most `fuel` trips, each body at a fuel at
    most `fuel`, while the target iteration runs at most `tf` trips, each body at the fuel `tf`.
    No typing hypothesis on the calls is needed: the answer relation `ImpRA` states that a
    source answer is the encoding of a target answer. -/
theorem impToNF_relT (sigOf : String → List NfTy → Option NfTy)
    (h₁ : ∀ e : linkSig.Event, linkSig.Resp e) (hR : RepeatCalls fun f vals => h₁ ⟨f, vals⟩)
    (tE : TreeCallEnv leafSig nfDialect) (e : ImpExpr) :
    ∀ (tgt : Option String) {Γ : Ctxt nfDialect} (σ : NfEnv Γ) {o : Out Γ},
      impToNF sigOf tgt σ e = some o → ∀ fuel tf, fuel ≤ tf → RelT h₁ tE fuel tf e σ o := by
  induction e using ImpExpr.ind
  case lit l => intro tgt Γ σ o h fuel tf _; exact litOut_relT fuel tf tgt σ l h
  case var x => intro tgt Γ σ o h fuel tf _; exact atomOut_relT fuel tf σ _ h
  case letBind x v b ihv ihb =>
    intro tgt Γ σ o h fuel tf hle
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨ov, hov, ob, hob, rfl⟩ := h
    exact letBind_relT fuel tf x (ihv _ σ hov fuel tf hle) (ihb _ _ hob fuel tf hle)
  case seq a b iha ihb =>
    intro tgt Γ σ o h fuel tf hle
    simp only [impToNF, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨oa, hoa, ob, hob, rfl⟩ := h
    exact seq_relT fuel tf (iha _ σ hoa fuel tf hle) (ihb _ _ hob fuel tf hle)
  case assign x r ih =>
    intro tgt Γ σ o h fuel tf hle
    simp only [impToNF, Option.map_eq_some_iff] at h
    obtain ⟨o', ho', rfl⟩ := h
    exact assign_relT fuel tf x tgt (ih _ σ ho' fuel tf hle)
  case app f args iha =>
    intro tgt Γ σ o h fuel tf hle
    exact app_relT hR sigOf fuel tf tgt f args σ
      (fun e he _ σ' _ h' => iha e he none σ' h' fuel tf hle) h
  case tuple es _ => intro tgt Γ σ o h fuel tf _; exact tuple_relT sigOf fuel tf tgt es σ h
  case proj e i ih =>
    intro tgt Γ σ o h fuel tf hle
    exact proj_relT sigOf fuel tf tgt e i σ h fun h' => ih none σ h' fuel tf hle
  case unitVal =>
    intro tgt Γ σ o h fuel tf _
    simp only [impToNF, Option.some.injEq] at h
    subst h
    exact unitVal_relT fuel tf tgt σ
  case typeAscription e s ih =>
    intro tgt Γ σ o h fuel tf hle env V hrel
    have hr : denoteT evTable fuel (.typeAscription e s) env = denoteT evTable fuel e env := by
      rw [denoteT]
    rw [hr]
    exact ih _ σ h fuel tf hle env V hrel
  case forFold i lo hi body _ _ ihb =>
    intro tgt Γ σ o h fuel tf hle
    exact forFold_relT sigOf fuel tf hle tgt i lo hi body σ h
      fun σ' _ h' fuel' tf' hle' => ihb none σ' h' fuel' tf' hle'
  case forFoldRev i lo hi body _ _ ihb =>
    intro tgt Γ σ o h fuel tf hle
    exact forFoldRev_relT sigOf fuel tf hle tgt i lo hi body σ h
      fun σ' _ h' fuel' tf' hle' => ihb none σ' h' fuel' tf' hle'
  case ifThenElse c a b ihc iha ihb =>
    intro tgt Γ σ o h fuel tf hle
    exact cond_relT sigOf fuel tf tgt c a b σ h (fun h' => ihc none σ h' fuel tf hle)
      (fun σ' _ h' => iha none σ' h' fuel tf hle) (fun σ' _ h' => ihb none σ' h' fuel tf hle)
  case whileFold c body _ ihb =>
    intro tgt Γ σ o h fuel tf hle
    cases c with
    | var g =>
      exact whileFold_relT sigOf fuel tf hle tgt g body σ h
        fun σ' _ h' fuel' tf' hle' => ihb none σ' h' fuel' tf' hle'
    | _ => simp [impToNF] at h
  all_goals intro tgt Γ σ o h; simp [impToNF] at h

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeImpToNF
