/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCat

/-!
# The domain of `nfToCat`

`NB` is a decidable predicate on the programs of `NFProg nfDialect`, close to their syntax:
every let-bound operation satisfies `nbOp`, and the program has no exit-flag loop and no call
node. `nbOp` is the disjunction of one predicate per construct of the translation: the
constants, the integer literals in `[0, 2^64)` at an integer, a `64`-bit word or an unsigned
integer of at most `64` bits, the subtraction of `64`-bit words, the loop counter at any
lower bound, the trip count at a bound of an integer, a `64`-bit word or an unsigned integer,
the binary, unary and comparison calls of the scalar table on integers and `64`-bit words
other than the rotations, and `index`, `array_update` and `select` at the types of arrays of
`64`-bit words, integers and `64`-bit words. `nfToCat` is `some` on every program of `NB` at
every reading of its context.

## Main definitions

* `litCount` — the number of literals among a vector of readings.
* `scalarCallOk`, `memCallOk`, `ilitOk`, `tripOk`, `nbOp` — the operations of the domain.
* `NB` — the programs of the domain.

## Main results

* `pinAllN_isSome`, `pinRes_isSome`, `emitRes_isSome` — the bindings of the literals and of
  a translated operation are defined when their continuations are.
* `catOp_isSome_of_nbOp` — `catOp` is `some` on every operation of `nbOp`.
* `nfToCat_isSome_of_NB` — `nfToCat` is `some` on every program of `NB`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCatComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.Hax.NFToCat
open Ctxt (Var Valuation)

/-! ## 1. Readings and the bindings of literals -/

/-- The number of literals among a vector of readings. -/
def litCount {Δ : Ctxt catCryptDialect} : {ts : List NfTy} → HVector (fun t => Rd Δ t) ts → Nat
  | [], .nil => 0
  | _ :: _, .cons (.lit _ _) rs => litCount rs + 1
  | _ :: _, .cons (.var _) rs => litCount rs

/-- A vector of readings has at most as many literals as entries. -/
theorem litCount_le_length {Δ : Ctxt catCryptDialect} :
    ∀ {ts : List NfTy} (rs : HVector (fun t => Rd Δ t) ts), litCount rs ≤ ts.length
  | [], .nil => le_refl _
  | _ :: _, .cons r rs => by
      have := litCount_le_length rs
      cases r <;> simp only [litCount, List.length_cons] <;> omega

/-- A vector of readings without a literal has variables. -/
theorem pinVars_isSome_of_firstLit {Δ : Ctxt catCryptDialect} :
    ∀ {ts : List NfTy} (rs : HVector (fun t => Rd Δ t) ts), firstLit rs = none →
      (pinVars rs).isSome
  | [], .nil, _ => rfl
  | _ :: _, .cons r rs, h => by
      cases r with
      | var w =>
          simp only [firstLit] at h
          simp [pinVars, pinVars_isSome_of_firstLit rs h]
      | lit k _ => simp [firstLit] at h

/-- A vector of readings with no literal counted has no first literal. -/
theorem firstLit_of_litCount {Δ : Ctxt catCryptDialect} :
    ∀ {ts : List NfTy} (rs : HVector (fun t => Rd Δ t) ts), litCount rs = 0 →
      firstLit rs = none
  | [], .nil, _ => rfl
  | _ :: _, .cons r rs, h => by
      cases r with
      | var w =>
          simp only [litCount] at h
          simp [firstLit, firstLit_of_litCount rs h]
      | lit k _ => simp [litCount] at h

/-- The binding of a literal adds no literal. -/
theorem litCount_bindLit_le {Δ : Ctxt catCryptDialect} (c : Nat) :
    ∀ {ts : List NfTy} (rs : HVector (fun t => Rd Δ t) ts), litCount (bindLit c rs) ≤ litCount rs
  | [], .nil => le_refl _
  | _ :: _, .cons r rs => by
      have := litCount_bindLit_le c rs
      cases r with
      | var w => simp only [bindLit, Rd.pin, litCount]; omega
      | lit k h =>
          simp only [bindLit, Rd.pin]
          split <;> simp only [litCount] <;> omega

/-- The binding of the first literal removes a literal. -/
theorem litCount_bindLit_lt {Δ : Ctxt catCryptDialect} :
    ∀ {ts : List NfTy} (rs : HVector (fun t => Rd Δ t) ts) {c : Nat}, firstLit rs = some c →
      litCount (bindLit c rs) < litCount rs
  | [], .nil, _, h => by cases h
  | _ :: _, .cons r rs, c, h => by
      cases r with
      | var w =>
          simp only [firstLit] at h
          have := litCount_bindLit_lt rs h
          simp only [bindLit, Rd.pin, litCount]
          omega
      | lit k hk =>
          simp only [firstLit, Option.some.injEq] at h
          subst h
          have := litCount_bindLit_le k rs
          simp only [bindLit, Rd.pin, ↓reduceIte, litCount]
          omega

/-- **`pinAllN` is defined** on a vector of at most `n` literals when its continuation is
    defined on every vector of variables. -/
theorem pinAllN_isSome {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)), (k σ' ws).isSome) :
    ∀ (n : Nat) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts),
      litCount rs ≤ n → (pinAllN k n σ rs).isSome
  | 0, _, σ, rs, hn => by
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp
        (pinVars_isSome_of_firstLit rs (firstLit_of_litCount rs (by omega)))
      simp [pinAllN, hws, hk]
  | n + 1, _, σ, rs, hn => by
      simp only [pinAllN]
      split
      · rename_i hf
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (pinVars_isSome_of_firstLit rs hf)
        simp [hws, hk]
      · rename_i c hf
        have := litCount_bindLit_lt rs hf
        simp [pinAllN_isSome hk n _ (bindLit c rs) (by omega)]

/-- `pinAll` is defined when its continuation is defined on every vector of variables. -/
theorem pinAll_isSome {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)), (k σ' ws).isSome)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts) :
    (pinAll k σ rs).isSome :=
  pinAllN_isSome hk _ σ rs (litCount_le_length rs)

/-- **`pinRes` is defined** on a vector of at most `n` literals when the expression `k` is
    defined on every vector of variables. -/
theorem pinRes_isSome {as : List NfTy} {r : NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, HVector (fun t => Var Δ' t) (as.map catTy) →
      Option (Expr catCryptDialect Δ' (catTy r))}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (ws : HVector (fun t => Var Δ' t) (as.map catTy)),
      (k ws).isSome) :
    ∀ (n : Nat) {Δ : Ctxt catCryptDialect} (rs : HVector (fun t => Rd Δ t) as),
      litCount rs ≤ n → (pinRes k n rs).isSome
  | 0, _, rs, hn => by
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp
        (pinVars_isSome_of_firstLit rs (firstLit_of_litCount rs (by omega)))
      simp [pinRes, hws, hk]
  | n + 1, _, rs, hn => by
      simp only [pinRes]
      split
      · rename_i hf
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (pinVars_isSome_of_firstLit rs hf)
        simp [hws, hk]
      · rename_i c hf
        have := litCount_bindLit_lt rs hf
        simp [pinRes_isSome hk n (bindLit c rs) (by omega)]

/-- **`emitRes` is defined** when its continuation is defined at every reading. -/
theorem emitRes_isSome {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ'), (cont σ').isSome) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ),
      (emitRes cont h res σ).isSome
  | _, _, _, .rd _, _ => hcont _
  | _, _, _, .expr _, _ => by simp [emitRes, hcont]
  | _, _, _, .expr1 _ _, _ => by simp [emitRes, hcont]
  | _, _, h, .bind _ _ rest, σ => by simp [emitRes, emitRes_isSome hcont h rest σ.wk]

/-! ## 2. The operations of the domain -/

/-- The binary, unary and comparison calls of the scalar table on integers and `64`-bit
    words, other than the rotations. -/
def scalarCallOk (f : String) : List NfTy → NfTy → Bool
  | [ta, tb], .word 64 =>
      ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb &&
        (match ImpToNF.scalarBinOf f with
          | some (o, _) => !(decide (o = .rotr) || decide (o = .rotl))
          | none => false)
  | [ta, tb], .bit =>
      ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb && (ImpToNF.scalarCmpOf f).isSome
  | [ta], .word 64 => ImpToNF.hax64NFWordTy ta && (ImpToNF.scalarUnOf f).isSome
  | _, _ => false

/-- The calls `index` and `array_update` on an array of `64`-bit words, and `select` on a bit
    and two integers or `64`-bit words, at a `64`-bit word or an integer. -/
def memCallOk (f : String) : List NfTy → NfTy → Bool
  | [.arr _ (.word 64), tb], .word 64 => f == "index" && ImpToNF.hax64NFWordTy tb
  | [.arr n (.word 64), ti, tv], .arr n' (.word 64) =>
      f == "array_update" && n == n' && ImpToNF.hax64NFWordTy ti && ImpToNF.hax64NFWordTy tv
  | [.bit, ta, tb], .word 64 =>
      f == "select" && ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb
  | [.bit, ta, tb], .int =>
      f == "select" && ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb
  | _, _ => false

/-- The integer literals in `[0, 2^64)` at an integer, a `64`-bit word or an unsigned integer
    of at most `64` bits. -/
def ilitOk (t : NfTy) (v : Int) : Bool :=
  decide (0 ≤ v) && decide (v < 2 ^ 64) &&
    (ImpToNF.hax64NFWordTy t ||
      match t with
      | .uint W => decide (W.bits ≤ 64)
      | _ => false)

/-- The types of an upper bound of a counted loop: an integer, a `64`-bit word and an
    unsigned integer. -/
def tripOk : NfTy → Bool
  | .uint _ => true
  | t => ImpToNF.hax64NFWordTy t

/-- **The operations of the domain**, one disjunct per construct. -/
def nbOp : NfOp → Bool
  | .named _ op => nbOp op
  | .call f as r => scalarCallOk f as r || memCallOk f as r
  | .bin o w => decide (o = .sub) && decide (w = 64)
  | .ilit t v => ilitOk t v
  | .constBit _ | .constUnit | .ctr => true
  | .trip t => tripOk t
  | _ => false

/-- A variable of a type whose values encode as integers has a word variable. -/
theorem asWord_isSome {Δ : Ctxt catCryptDialect} {t : NfTy}
    (ht : ImpToNF.hax64NFWordTy t = true) (v : Var Δ (catTy t)) : (asWord t v).isSome := by
  simp [asWord, ht]

/-- `withVar1` is defined on a type whose values encode as integers when its continuation is
    defined. -/
theorem withVar1_isSome {Δ : Ctxt catCryptDialect} {r ta : NfTy}
    (hta : ImpToNF.hax64NFWordTy ta = true) (ra : Rd Δ ta)
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x : Var Δ' (.sword 64)), (k x).isSome) :
    (withVar1 ta ra k).isSome := by
  cases ra with
  | var a =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome hta a)
      simp [withVar1, hx, hk]
  | lit n _ => simp [withVar1, hk]

/-- `withVar2` is defined on two types whose values encode as integers when its continuation
    is defined. -/
theorem withVar2_isSome {Δ : Ctxt catCryptDialect} {r ta tb : NfTy}
    (hta : ImpToNF.hax64NFWordTy ta = true) (htb : ImpToNF.hax64NFWordTy tb = true)
    (ra : Rd Δ ta) (rb : Rd Δ tb)
    {k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Var Δ' (.sword 64) →
      Option (OpRes Δ' r)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (x y : Var Δ' (.sword 64)), (k x y).isSome) :
    (withVar2 ta tb ra rb k).isSome := by
  cases ra with
  | var a =>
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome hta a)
      cases rb with
      | var b =>
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (asWord_isSome htb b)
          simp [withVar2, hx, hy, hk]
      | lit m _ => simp [withVar2, hx, hk]
  | lit n _ =>
      cases rb with
      | var b =>
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (asWord_isSome htb b)
          simp [withVar2, hy, hk]
      | lit m _ => simp [withVar2, hk]

/-- The translation `binChain` of a binary call other than a rotation is defined. -/
theorem binChain_isSome {Δ : Ctxt catCryptDialect} {o : ImpToNF.ScalarBin} (w : Nat)
    (ho : o ≠ .rotr ∧ o ≠ .rotl) (a b : Var Δ (.sword 64)) : (binChain o w a b).isSome := by
  unfold binChain
  split
  · rfl
  · cases o <;> simp_all [binE]

/-- A call of `scalarCallOk` is translated by `scalarRes?` on every reading. -/
theorem scalarRes_isSome {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    (h : scalarCallOk f as r = true) (rs : HVector (fun t => Rd Δ t) as) :
    (scalarRes? f as r rs).isSome := by
  unfold scalarCallOk at h
  split at h
  · rename_i ta tb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hta, htb⟩, ho⟩ := h
    rcases rs with _ | ⟨ra, _ | ⟨rb, _ | _⟩⟩
    change (scalarRes2 f ta tb ra rb (.word 64)).isSome
    simp only [scalarRes2]
    split at ho
    · rename_i o w hof
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at ho
      rw [hof]
      simp only [Option.bind_some]
      rw [if_neg (by rintro (h | h) <;> simp_all)]
      exact withVar2_isSome hta htb _ _ fun x y => binChain_isSome w ho x y
    · cases ho
  · rename_i ta tb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hta, htb⟩, hc⟩ := h
    rcases rs with _ | ⟨ra, _ | ⟨rb, _ | _⟩⟩
    change (scalarRes2 f ta tb ra rb .bit).isSome
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
    simp only [scalarRes2, hc, Option.bind_some]
    exact withVar2_isSome hta htb _ _ fun _ _ => rfl
  · rename_i ta
    simp only [Bool.and_eq_true] at h
    obtain ⟨hta, hu⟩ := h
    rcases rs with _ | ⟨ra, _ | _⟩
    change (scalarRes1 f ta ra (.word 64)).isSome
    obtain ⟨⟨o, w⟩, hu⟩ := Option.isSome_iff_exists.mp hu
    simp only [scalarRes1, hu, Option.bind_some]
    split
    · cases ra with
      | var a =>
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome hta a)
          simp [Rd.toWord64, hx]
      | lit k _ => rfl
    · exact withVar1_isSome hta ra fun _ => rfl
  · cases h

/-- A call of `memCallOk` is translated by `catCall?` on every vector of variables. -/
theorem catCall_isSome {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    (h : memCallOk f as r = true) (ws : HVector (fun t => Var Δ t) (as.map catTy)) :
    (catCall? f as r ws).isSome := by
  unfold memCallOk at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, htb⟩ := h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (asWord_isSome htb ws.tail.head)
    simp [catCall?, asArr, hi]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, hti⟩, htv⟩ := h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (asWord_isSome hti ws.tail.head)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome htv ws.tail.tail.head)
    simp [catCall?, asArr, hi, hx]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hta⟩, htb⟩ := h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome hta ws.tail.head)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (asWord_isSome htb ws.tail.tail.head)
    simp [catCall?, selectCat, asBit, hx, hy]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hta⟩, htb⟩ := h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (asWord_isSome hta ws.tail.head)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (asWord_isSome htb ws.tail.tail.head)
    simp [catCall?, selectCat, asBit, hx, hy]
  · cases h

/-- `catCallRd0` is defined when `catCall?` is defined on every vector of variables. -/
theorem catCallRd0_isSome {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (ws : HVector (fun t => Var Δ' t) (as.map catTy)),
      (catCall? f as r ws).isSome)
    (rs : HVector (fun t => Rd Δ t) as) : (catCallRd0 f as r rs).isSome := by
  unfold catCallRd0
  split
  · simp [hk]
  · split
    · rfl
    · exact pinRes_isSome hk _ rs (litCount_le_length rs)

/-- A call of the domain is translated by `catCallRd` on every reading. -/
theorem catCallRd_isSome {Δ : Ctxt catCryptDialect} {f : String} {as : List NfTy} {r : NfTy}
    (h : (scalarCallOk f as r || memCallOk f as r) = true)
    (rs : HVector (fun t => Rd Δ t) as) : (catCallRd f as r rs).isSome := by
  unfold catCallRd
  split
  · rfl
  · rename_i h0
    rcases Bool.or_eq_true_iff.mp h with hs | hm
    · exact scalarRes_isSome hs rs
    · have := catCallRd0_isSome (fun ws => catCall_isSome hm ws) rs
      rw [h0] at this
      cases this

/-- The trip count `tripSub` is defined. -/
theorem tripSub_isSome {Δ : Ctxt catCryptDialect} (rlo : Rd Δ .int) (rhi : Rd Δ (.word 64)) :
    (tripSub rlo rhi).isSome := by
  unfold tripSub
  split
  · rfl
  · exact withVar2_isSome rfl rfl _ _ fun _ _ => rfl

/-- A loop bound of `tripOk` reads as a word. -/
theorem toCount_isSome {Δ : Ctxt catCryptDialect} {t : NfTy} (ht : tripOk t = true)
    (r : Rd Δ t) : (Rd.toCount t r).isSome := by
  cases r with
  | var w =>
      cases t with
      | uint W => rfl
      | _ =>
          simp only [tripOk] at ht
          simp [Rd.toCount, asCount, asWord, ht]
  | lit k _ => rfl

/-- **`catOp` is defined on every operation of the domain**, at every reading. -/
theorem catOp_isSome_of_nbOp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp), nbOp op = true → ∀ (args : HVector (fun t => Var Γ t) op.sig),
      (catOp σ op args).isSome := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call f as r => exact fun h args => catCallRd_isSome h _
  | bin o w =>
      intro h args
      simp only [nbOp, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      change (binRes? .sub 64 (σ a) (σ b)).isSome
      unfold binRes?
      rw [dif_pos ⟨rfl, rfl⟩]
      exact withVar2_isSome rfl rfl _ _ fun x y =>
        binChain_isSome 64 ⟨by decide, by decide⟩ x y
  | ilit t v =>
      intro h args
      simp only [nbOp, ilitOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h0, h1⟩, ht⟩ := h
      unfold catOp
      split
      · rfl
      · rename_i hn
        rcases ht with ht | ht
        · exact absurd ⟨ht, h0, h1⟩ hn
        · cases t with
          | uint W =>
              simp only [decide_eq_true_eq] at ht
              simp only [uintLit?, if_pos (And.intro ht (And.intro h0 h1)), Option.isSome_some]
          | _ => simp at ht
  | constBit b => intro _ _; rfl
  | constUnit => intro _ _; rfl
  | ctr =>
      intro _ args
      rcases args with _ | ⟨lo, _ | ⟨i, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => some (OpRes.rd (σ i))
        | rlo => ctrRes rlo (σ i)).isSome
      split
      · rfl
      · exact withVar2_isSome rfl rfl _ _ fun _ _ => rfl
  | trip t =>
      intro h args
      simp only [nbOp] at h
      rcases args with _ | ⟨lo, _ | ⟨hi, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => (Rd.toCount t (σ hi)).map tripRes
        | rlo => (Rd.toCount t (σ hi)).bind (tripSub rlo)).isSome
      obtain ⟨r', hr⟩ := Option.isSome_iff_exists.mp (toCount_isSome h (σ hi))
      split
      · simp [hr]
      · simpa [hr] using tripSub_isSome _ r'
  | _ => intro h; simp [nbOp] at h

/-! ## 3. The programs of the domain -/

/-- **The programs of the domain**: every let-bound operation is in `nbOp`, and the program
    has no exit-flag loop and no call node. -/
def NB : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => nbOp e.op && NB k
  | _, _, .forLoop _ _ body k => NB body && NB k
  | _, _, .ifThenElse _ thn els k => NB thn && NB els && NB k
  | _, _, .whileLoop .. => false
  | _, _, .call .. => false

/-- **`nfToCat` is defined on every program of the domain**, at every reading of its
    context. -/
theorem nfToCat_isSome_of_NB {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : NB p = true) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), (nfToCat p σ).isSome := by
  induction p with
  | ret vs =>
      intro _ σ
      exact pinAll_isSome (fun _ _ => rfl) σ _
  | var e k ih =>
      intro _ σ
      rcases e with ⟨op, he, args⟩
      simp only [NB, Bool.and_eq_true] at hp
      obtain ⟨res, hres⟩ := Option.isSome_iff_exists.mp (catOp_isSome_of_nbOp σ op hp.1 args)
      simp only [nfToCat, hres, Option.bind_some]
      exact emitRes_isSome (fun σ' => ih hp.2 σ') he res σ
  | forLoop count inits body k ihb ihk =>
      intro _ σ
      simp only [NB, Bool.and_eq_true] at hp
      refine pinAll_isSome (fun σ' ws => ?_) σ _
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp (ihb hp.1 (TRd.liftApp _ (TRd.lift σ')))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk hp.2 (TRd.liftApp _ σ'))
      simp [hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro _ σ
      simp only [NB, Bool.and_eq_true] at hp
      obtain ⟨c, hc⟩ := Rd.eq_var_of_bit (σ cond)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (iht hp.1.1 σ)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (ihe hp.1.2 σ)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp (ihk hp.2 (TRd.liftApp _ σ))
      simp [nfToCat, hc, ht, he, hk]
  | whileLoop => simp [NB] at hp
  | call => simp [NB] at hp

end CatCrypt.Crypto.Hax.NFToCatComplete
