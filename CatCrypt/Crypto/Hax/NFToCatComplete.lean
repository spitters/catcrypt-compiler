/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCat
public import CatCrypt.Crypto.Hax.NFToCatCall

/-!
# The domain of `nfToCat`

`NB` is a decidable predicate on the programs of `NFProg nfDialect`, close to their syntax:
every let-bound operation satisfies `nbOp` or `rotOpOk`, and the program has no exit-flag loop
and no call node. `nbOp` is the disjunction of one predicate per construct of the translation:
the constants, the integer literals in `[0, 2^64)` at an integer, a `64`-bit word or an
unsigned integer of at most `64` bits, the subtraction of `64`-bit words, the loop counter at
any lower bound, the trip count at a bound of an integer, a `64`-bit word or an unsigned
integer, the binary, unary and comparison calls of the scalar table on integers and `64`-bit
words, the Boolean connectives `&&`, `||`, `Eq`, `Ne` and `Not` on bits, the rotations by any amount among them, and `index`, `array_update` and `select` at the
types of arrays of `64`-bit words, integers and `64`-bit words. `rotOpOk` is the rotation of the
scalar table by an amount bound to an integer literal in `[0, 2^64)` at an integer or a `64`-bit
word, a subset of `nbOp`; `NBL` tracks these bindings as a list of flags aligned with the
context. `nfToCat` is `some` on every program of `NB` at every reading of its context.

`NBD D` widens `NB` by the let-bound calls `NfOp.call f as r`, possibly under `named`, that the
list `D` declares (`extOk D`). The translation `nfToCatExt D` is `some` on every program of
`NBD D`: a declared call that `catOp` refuses is translated by `emitCall`.

## Main definitions

* `litCount` — the number of literals among a vector of readings.
* `litAt`, `LitOn` — the literal flags of a context and the readings that respect them.
* `scalarCallOk`, `memCallOk`, `ilitOk`, `tripOk`, `nbOp` — the operations of the domain.
* `rotCallOk`, `rotOpOk`, `litOp` — the rotations by a literal and the literal bindings.
* `NBL`, `NB` — the programs of the domain at a list of flags, and at the empty list.
* `extOk`, `NBDL`, `NBD` — the declared calls, and the programs of the domain with declared
  calls at a list of flags and at the empty list.

## Main results

* `pinAllN_isSome`, `pinRes_isSome`, `emitRes_isSome` — the bindings of the literals and of
  a translated operation are defined when their continuations are.
* `catOp_isSome_of_nbOp` — `catOp` is `some` on every operation of `nbOp`.
* `catOp_isSome_of_nbOpAt` — `catOp` is `some` on every operation of `nbOp` or `rotOpOk`.
* `nfToCat_isSome_of_NBL`, `nfToCat_isSome_of_NB` — `nfToCat` is `some` on every program of
  `NBL` at readings of its flags, and on every program of `NB`.
* `NBDL_of_NBL`, `NBD_of_NB` — the domain with declared calls contains the domain.
* `nfToCatExt_isSome_of_NBDL`, `nfToCatExt_isSome_of_NBD` — `nfToCatExt D` is `some` on every
  program of `NBDL D` at readings of its flags, and on every program of `NBD D`.
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

/-- **`pinAllN` is defined** on a vector of at most `n` literals at readings of an invariant
    `P` that the weakening preserves, when its continuation is defined on every vector of
    variables at every reading of `P`. -/
theorem pinAllN_isSome_of {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    (P : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' → Prop)
    (hP : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ'), P σ' →
      P (TRd.wk (c := CryptoTy.sword 64) σ'))
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)), P σ' → (k σ' ws).isSome) :
    ∀ (n : Nat) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts),
      P σ → litCount rs ≤ n → (pinAllN k n σ rs).isSome
  | 0, _, σ, rs, hσ, hn => by
      obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp
        (pinVars_isSome_of_firstLit rs (firstLit_of_litCount rs (by omega)))
      simp [pinAllN, hws, hk σ ws hσ]
  | n + 1, _, σ, rs, hσ, hn => by
      simp only [pinAllN]
      split
      · rename_i hf
        obtain ⟨ws, hws⟩ := Option.isSome_iff_exists.mp (pinVars_isSome_of_firstLit rs hf)
        simp [hws, hk σ ws hσ]
      · rename_i c hf
        have := litCount_bindLit_lt rs hf
        simp [pinAllN_isSome_of P hP hk n _ (bindLit c rs) (hP σ hσ) (by omega)]

/-- **`pinAllN` is defined** on a vector of at most `n` literals when its continuation is
    defined on every vector of variables. -/
theorem pinAllN_isSome {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)), (k σ' ws).isSome)
    (n : Nat) {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts)
    (hn : litCount rs ≤ n) : (pinAllN k n σ rs).isSome :=
  pinAllN_isSome_of (fun _ => True) (fun _ _ => trivial) (fun σ' ws _ => hk σ' ws) n σ rs
    trivial hn

/-- `pinAll` is defined at readings of an invariant `P` that the weakening preserves, when its
    continuation is defined on every vector of variables at every reading of `P`. -/
theorem pinAll_isSome_of {Γ : Ctxt nfDialect} {us : List CryptoTy} {ts : List NfTy}
    (P : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' → Prop)
    (hP : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ'), P σ' →
      P (TRd.wk (c := CryptoTy.sword 64) σ'))
    {k : ∀ {Δ' : Ctxt catCryptDialect}, TRd Γ Δ' →
      HVector (fun t => Var Δ' t) (ts.map catTy) → Option (NFProg catCryptDialect Δ' us)}
    (hk : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd Γ Δ')
      (ws : HVector (fun t => Var Δ' t) (ts.map catTy)), P σ' → (k σ' ws).isSome)
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) (rs : HVector (fun t => Rd Δ t) ts) (hσ : P σ) :
    (pinAll k σ rs).isSome :=
  pinAllN_isSome_of P hP hk _ σ rs hσ (litCount_le_length rs)

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

/-! ## 2. Literal flags

A list of flags `L` aligned with a context marks the variables that every reading of interest
reads as a literal (`LitOn`). The weakening and the lifting of readings preserve the flags of
the existing variables; a new variable of a lifting is not flagged. -/

/-- The flag of a variable in a list of flags aligned with its context: the entry at the
    position of the variable, `false` past the end of the list. -/
def litAt : {Γ : Ctxt nfDialect} → {t : NfTy} → List Bool → Var Γ t → Bool
  | _, _, L, .here => L.headD false
  | _, _, L, .there v => litAt L.tail v

/-- No variable is flagged in the empty list. -/
theorem litAt_nil : ∀ {Γ : Ctxt nfDialect} {t : NfTy} (v : Var Γ t), litAt [] v = false
  | _, _, .here => rfl
  | _, _, .there v => litAt_nil v

/-- The readings `σ` read every variable flagged in `L` as a literal. -/
def LitOn {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (L : List Bool) (σ : TRd Γ Δ) :
    Prop :=
  ∀ (t : NfTy) (v : Var Γ t), litAt L v = true → ∃ k h, σ v = .lit k h

/-- Every reading satisfies the empty list of flags. -/
theorem litOn_nil {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    LitOn [] σ := by
  intro t v h
  rw [litAt_nil] at h
  cases h

/-- The weakening preserves the flags. -/
theorem litOn_wk {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {c : CryptoTy}
    {L : List Bool} {σ : TRd Γ Δ} (hσ : LitOn L σ) : LitOn L (TRd.wk (c := c) σ) := by
  intro t v h
  obtain ⟨k, hk, he⟩ := hσ t v h
  exact ⟨k, hk, by simp [TRd.wk, he, Rd.wk]⟩

/-- The extension by a reading `r` that is a literal when its flag `b` is set. -/
theorem litOn_cons {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy} {b : Bool}
    {L : List Bool} {r : Rd Δ s} {σ : TRd Γ Δ} (hr : b = true → ∃ k h, r = .lit k h)
    (hσ : LitOn L σ) : LitOn (b :: L) (TRd.cons r σ) := by
  intro t v h
  cases v with
  | here => exact hr h
  | there v => exact hσ t v h

/-- The lifting preserves the flags and does not flag the new variable. -/
theorem litOn_lift {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy}
    {L : List Bool} {σ : TRd Γ Δ} (hσ : LitOn L σ) :
    LitOn (false :: L) (TRd.lift (s := s) σ) :=
  litOn_cons (fun h => absurd h Bool.false_ne_true) (litOn_wk hσ)

/-- The lifting under the bindings `cs` preserves the flags and does not flag the new
    variables. -/
theorem litOn_liftApp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {L : List Bool}
    {σ : TRd Γ Δ} (hσ : LitOn L σ) :
    ∀ (cs : List NfTy), LitOn (List.replicate cs.length false ++ L) (TRd.liftApp cs σ)
  | [] => hσ
  | _ :: cs => litOn_lift (litOn_liftApp hσ cs)

/-- **`emitRes` is defined** at readings of the flags `L` when its continuation is defined at
    every reading of the flags `L` extended by an unset flag. -/
theorem emitRes_isSome_of {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy} {L : List Bool}
    {cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))}
    (hcont : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ'), LitOn (false :: L) σ' →
      (cont σ').isSome) :
    ∀ {Δ : Ctxt catCryptDialect} {t : NfTy} (h : t = s) (res : OpRes Δ t) (σ : TRd Γ Δ),
      LitOn L σ → (emitRes cont h res σ).isSome
  | _, _, _, .rd _, _, hσ => hcont _ (litOn_cons (fun h => absurd h Bool.false_ne_true) hσ)
  | _, _, _, .expr _, _, hσ => by simp [emitRes, hcont _ (litOn_lift hσ)]
  | _, _, _, .expr1 _ _, _, hσ => by simp [emitRes, hcont _ (litOn_lift (litOn_wk hσ))]
  | _, _, h, .bind _ _ rest, σ, hσ => by
      simp [emitRes, emitRes_isSome_of hcont h rest σ.wk (litOn_wk hσ)]

/-! ## 3. The operations of the domain -/

/-- The binary, unary and comparison calls of the scalar table on integers and `64`-bit
    words, and the Boolean connectives of `ImpToNF.hax64BitTable` on bits. -/
def scalarCallOk (f : String) : List NfTy → NfTy → Bool
  | [ta, tb], .word 64 =>
      ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb && (ImpToNF.scalarBinOf f).isSome
  | [ta, tb], .bit =>
      (ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb && (ImpToNF.scalarCmpOf f).isSome) ||
        (decide (ta = .bit) && decide (tb = .bit) &&
          (ImpToNF.scalarBitOf f).any ImpToNF.ScalarBit.binary)
  | [ta], .word 64 => ImpToNF.hax64NFWordTy ta && (ImpToNF.scalarUnOf f).isSome
  | [ta], .bit => decide (ta = .bit) && decide (ImpToNF.scalarBitOf f = some .not)
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
    obtain ⟨⟨o, w⟩, hof⟩ := Option.isSome_iff_exists.mp ho
    simp only [scalarRes2, hof, Option.bind_some]
    split
    · cases rb with
      | lit k _ => exact withVar1_isSome hta _ fun _ => rfl
      | var _ => exact withVar2_isSome hta htb _ _ fun _ _ => rfl
    · rename_i hrot
      exact withVar2_isSome hta htb _ _ fun x y =>
        binChain_isSome w ⟨fun h => hrot (Or.inl h), fun h => hrot (Or.inr h)⟩ x y
  · rename_i ta tb
    rcases rs with _ | ⟨ra, _ | ⟨rb, _ | _⟩⟩
    change (scalarRes2 f ta tb ra rb .bit).isSome
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hta, htb⟩, hc⟩ := h
      have hne : ta ≠ .bit := by rintro rfl; cases hta
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hc
      simp only [scalarRes2, if_neg hne, hc, Option.bind_some]
      exact withVar2_isSome hta htb _ _ fun _ _ => rfl
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, rfl⟩, hany⟩ := h
      obtain ⟨o, hp, hb⟩ := (Option.any_eq_true _ _).mp hany
      simp only [scalarRes2, if_pos]
      cases ra with
      | lit _ hk => cases hk
      | var a =>
          cases rb with
          | lit _ hk => cases hk
          | var b =>
              simp only [bitRes2, asBit, Option.bind_some, hp]
              cases o <;> first | rfl | cases hb
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
  · rename_i ta
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, hp⟩ := h
    rcases rs with _ | ⟨ra, _ | _⟩
    change (scalarRes1 f .bit ra .bit).isSome
    cases ra with
    | lit _ hk => cases hk
    | var a => simp [scalarRes1, bitRes1, asBit, hp]
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

/-- The rotations of the scalar table on an integer or a `64`-bit word by a second operand
    flagged in `L` as a literal. -/
def rotCallOk {Γ : Ctxt nfDialect} (L : List Bool) (f : String) :
    (as : List NfTy) → NfTy → HVector (fun t => Var Γ t) as → Bool
  | [ta, tb], .word 64, args =>
      ImpToNF.hax64NFWordTy ta && ImpToNF.hax64NFWordTy tb && litAt L args.tail.head &&
        (match ImpToNF.scalarBinOf f with
          | some (o, _) => decide (o = .rotr) || decide (o = .rotl)
          | none => false)
  | _, _, _ => false

/-- The operations whose translation depends on the literal flags `L` of their arguments: the
    rotations of `rotCallOk`. -/
def rotOpOk {Γ : Ctxt nfDialect} (L : List Bool) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Bool
  | .named _ op, args => rotOpOk L op args
  | .call f as r, args => rotCallOk L f as r args
  | _, _ => false

/-- The operations that bind a literal reading: the integer literals in `[0, 2^64)` at an
    integer or a `64`-bit word. -/
def litOp : NfOp → Bool
  | .named _ op => litOp op
  | .ilit t v => ImpToNF.hax64NFWordTy t && decide (0 ≤ v) && decide (v < 2 ^ 64)
  | _ => false

/-- An operation of `litOp` is translated to a literal reading. -/
theorem catOp_litOp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp), litOp op = true → ∀ (args : HVector (fun t => Var Γ t) op.sig),
      ∃ k h, catOp σ op args = some (.rd (.lit k h)) := by
  intro op
  induction op with
  | named n op ih => exact ih
  | ilit t v =>
      intro h _
      simp only [litOp, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨ht, h0⟩, h1⟩ := h
      exact ⟨v.toNat, ht, by simp only [catOp, dif_pos (And.intro ht (And.intro h0 h1))]⟩
  | _ => intro h; simp [litOp] at h

/-- A rotation of `rotCallOk` is translated by `catCallRd` at every reading of the flags. -/
theorem catCallRd_isSome_of_rot {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) {L : List Bool} (hσ : LitOn L σ) {f : String} {as : List NfTy} {r : NfTy}
    (args : HVector (fun t => Var Γ t) as) (h : rotCallOk L f as r args = true) :
    (catCallRd f as r (σ.rds args)).isSome := by
  unfold rotCallOk at h
  split at h
  · rename_i ta tb args
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hta, htb⟩, hb⟩, ho⟩ := h
    obtain ⟨k, hk, hbk⟩ := hσ _ b hb
    replace hbk : σ b = .lit k hk := hbk
    unfold catCallRd
    split
    · rfl
    · change (scalarRes2 f ta tb (σ a) (σ b) (.word 64)).isSome
      split at ho
      · rename_i o w hof
        simp only [scalarRes2, hof, Option.bind_some]
        rw [if_pos (by simpa using ho), hbk]
        exact withVar1_isSome hta _ fun _ => rfl
      · cases ho
  · cases h

/-- **`catOp` is defined on every operation of `nbOp` and of `rotOpOk`** at every reading of
    the flags `L`. -/
theorem catOp_isSome_of_nbOpAt {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    (σ : TRd Γ Δ) {L : List Bool} (hσ : LitOn L σ) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig),
      (nbOp op || rotOpOk L op args) = true → (catOp σ op args).isSome := by
  intro op args h
  rcases Bool.or_eq_true_iff.mp h with h1 | h2
  · exact catOp_isSome_of_nbOp σ op h1 args
  · clear h
    induction op with
    | named n op ih => exact ih args h2
    | call f as r => exact catCallRd_isSome_of_rot σ hσ args h2
    | _ => simp [rotOpOk] at h2

/-! ## 4. The programs of the domain -/

/-- **The programs of the domain at the literal flags `L`** of their context: every let-bound
    operation is in `nbOp` or in `rotOpOk`, and the program has no exit-flag loop and no call
    node. A binding of `litOp` flags its variable; the variables of a loop and of the results
    of a branch are not flagged. -/
def NBL : {Γ : Ctxt nfDialect} → {ts : List NfTy} → List Bool → NFProg nfDialect Γ ts → Bool
  | _, _, _, .ret _ => true
  | _, _, L, .var e k => (nbOp e.op || rotOpOk L e.op e.args) && NBL (litOp e.op :: L) k
  | _, _, L, .forLoop (cs := cs) _ _ body k =>
      NBL (List.replicate cs.length false ++ false :: L) body &&
        NBL (List.replicate cs.length false ++ L) k
  | _, _, L, .ifThenElse (rs := rs) _ thn els k =>
      NBL L thn && NBL L els && NBL (List.replicate rs.length false ++ L) k
  | _, _, _, .whileLoop .. => false
  | _, _, _, .call .. => false

/-- **The programs of the domain**: `NBL` with no variable of the context flagged. -/
def NB {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : Bool :=
  NBL [] p

/-- **`nfToCat` is defined on every program of `NBL` at the flags `L`**, at every reading of
    its context that reads the flagged variables as literals. -/
theorem nfToCat_isSome_of_NBL {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ (L : List Bool), NBL L p = true →
      ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), LitOn L σ → (nfToCat p σ).isSome := by
  induction p with
  | ret vs =>
      intro _ _ _ σ _
      exact pinAll_isSome (fun _ _ => rfl) σ _
  | var e k ih =>
      intro L hp _ σ hσ
      rcases e with ⟨op, he, args⟩
      simp only [NBL, Bool.and_eq_true] at hp
      obtain ⟨res, hres⟩ :=
        Option.isSome_iff_exists.mp (catOp_isSome_of_nbOpAt σ hσ op args hp.1)
      simp only [nfToCat, hres, Option.bind_some]
      cases hl : litOp op
      · rw [hl] at hp
        exact emitRes_isSome_of (fun σ' hσ' => ih _ hp.2 σ' hσ') he res σ hσ
      · rw [hl] at hp
        obtain ⟨n, hn, hc⟩ := catOp_litOp σ op hl args
        rw [hc] at hres
        cases hres
        subst he
        exact ih _ hp.2 _ (litOn_cons (fun _ => ⟨n, hn, rfl⟩) hσ)
  | forLoop count inits body k ihb ihk =>
      intro L hp _ σ hσ
      simp only [NBL, Bool.and_eq_true] at hp
      refine pinAll_isSome_of (fun σ' => LitOn L σ') (fun _ h => litOn_wk h)
        (fun σ' ws hσ' => ?_) σ _ hσ
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ihb _ hp.1 (TRd.liftApp _ (TRd.lift σ')) (litOn_liftApp (litOn_lift hσ') _))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp
        (ihk _ hp.2 (TRd.liftApp _ σ') (litOn_liftApp hσ' _))
      simp [hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro L hp _ σ hσ
      simp only [NBL, Bool.and_eq_true] at hp
      obtain ⟨c, hc⟩ := Rd.eq_var_of_bit (σ cond)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (iht _ hp.1.1 σ hσ)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (ihe _ hp.1.2 σ hσ)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp
        (ihk _ hp.2 (TRd.liftApp _ σ) (litOn_liftApp hσ _))
      simp [nfToCat, hc, ht, he, hk]
  | whileLoop => intro _ hp; simp [NBL] at hp
  | call => intro _ hp; simp [NBL] at hp

/-- **`nfToCat` is defined on every program of the domain**, at every reading of its
    context. -/
theorem nfToCat_isSome_of_NB {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : NB p = true) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), (nfToCat p σ).isSome :=
  fun σ => nfToCat_isSome_of_NBL p [] hp σ (litOn_nil σ)

/-! ## 5. The programs of the domain with declared calls -/

/-- The calls that the list `D` declares, under the source names of `named`. -/
def extOk (D : List ExtDecl) : NfOp → Bool
  | .named _ op => extOk D op
  | .call f as r => declared D f as r
  | _ => false

/-- `extArgs` is defined on every call of `extOk D`. -/
theorem extArgs_isSome_of_extOk {D : List ExtDecl} {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    ∀ (op : NfOp), extOk D op = true →
      ∀ (args : HVector (fun t => Var Γ t) op.sig), (extArgs D σ op args).isSome := by
  intro op
  induction op with
  | named n op ih => exact ih
  | call f as r =>
      intro h args
      simp only [extOk] at h
      simp [extArgs, h]
  | _ => intro h; simp [extOk] at h

/-- **The programs of the domain with the declared calls `D`, at the literal flags `L`**:
    `NBL`, where a let-bound operation may also be a call of `extOk D`. -/
def NBDL (D : List ExtDecl) :
    {Γ : Ctxt nfDialect} → {ts : List NfTy} → List Bool → NFProg nfDialect Γ ts → Bool
  | _, _, _, .ret _ => true
  | _, _, L, .var e k =>
      (nbOp e.op || rotOpOk L e.op e.args || extOk D e.op) && NBDL D (litOp e.op :: L) k
  | _, _, L, .forLoop (cs := cs) _ _ body k =>
      NBDL D (List.replicate cs.length false ++ false :: L) body &&
        NBDL D (List.replicate cs.length false ++ L) k
  | _, _, L, .ifThenElse (rs := rs) _ thn els k =>
      NBDL D L thn && NBDL D L els && NBDL D (List.replicate rs.length false ++ L) k
  | _, _, _, .whileLoop .. => false
  | _, _, _, .call .. => false

/-- **The programs of the domain with the declared calls `D`**: `NBDL` with no variable of the
    context flagged. -/
def NBD (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Bool :=
  NBDL D [] p

/-- A program of `NBL` is a program of `NBDL` at every list of declarations. -/
theorem NBDL_of_NBL (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : ∀ (L : List Bool), NBL L p = true → NBDL D L p = true := by
  induction p with
  | ret => intro _ _; rfl
  | var e k ih =>
      intro L hp
      simp only [NBL, Bool.and_eq_true] at hp
      simp only [NBDL, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨Or.inl (Bool.or_eq_true_iff.mp hp.1), ih _ hp.2⟩
  | forLoop count inits body k ihb ihk =>
      intro L hp
      simp only [NBL, Bool.and_eq_true] at hp
      simp only [NBDL, Bool.and_eq_true]
      exact ⟨ihb _ hp.1, ihk _ hp.2⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro L hp
      simp only [NBL, Bool.and_eq_true] at hp
      simp only [NBDL, Bool.and_eq_true]
      exact ⟨⟨iht _ hp.1.1, ihe _ hp.1.2⟩, ihk _ hp.2⟩
  | whileLoop => intro _ hp; simp [NBL] at hp
  | call => intro _ hp; simp [NBL] at hp

/-- A program of `NB` is a program of `NBD` at every list of declarations. -/
theorem NBD_of_NB (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : NB p = true) : NBD D p = true :=
  NBDL_of_NBL D p [] hp

/-- **`nfToCatExt D` is defined on every program of `NBDL D` at the flags `L`**, at every
    reading of its context that reads the flagged variables as literals. -/
theorem nfToCatExt_isSome_of_NBDL (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) :
    ∀ (L : List Bool), NBDL D L p = true →
      ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), LitOn L σ → (nfToCatExt D p σ).isSome := by
  induction p with
  | ret vs =>
      intro _ _ _ σ _
      exact pinAll_isSome (fun _ _ => rfl) σ _
  | var e k ih =>
      intro L hp _ σ hσ
      rcases e with ⟨op, he, args⟩
      simp only [NBDL, Bool.and_eq_true] at hp
      obtain ⟨hop, hk⟩ := hp
      change (emitOp D (fun σ' => nfToCatExt D k σ') σ op he args).isSome
      unfold emitOp
      cases hc : catOp σ op args with
      | some res =>
          cases hl : litOp op
          · rw [hl] at hk
            exact emitRes_isSome_of (fun σ' hσ' => ih _ hk σ' hσ') he res σ hσ
          · rw [hl] at hk
            obtain ⟨n, hn, hc'⟩ := catOp_litOp σ op hl args
            rw [hc'] at hc
            cases hc
            subst he
            exact ih _ hk _ (litOn_cons (fun _ => ⟨n, hn, rfl⟩) hσ)
      | none =>
          have hl : litOp op = false := by
            cases hl : litOp op
            · rfl
            · obtain ⟨n, hn, hc'⟩ := catOp_litOp σ op hl args
              rw [hc'] at hc
              cases hc
          rw [hl] at hk
          have hx : extOk D op = true := by
            rcases Bool.or_eq_true_iff.mp hop with h1 | h2
            · have := catOp_isSome_of_nbOpAt σ hσ op args h1
              rw [hc] at this
              cases this
            · exact h2
          obtain ⟨c, hcx⟩ :=
            Option.isSome_iff_exists.mp (extArgs_isSome_of_extOk σ op hx args)
          simp only [hcx, Option.bind_some, emitCall]
          refine pinAll_isSome_of (fun σ' => LitOn L σ') (fun _ h => litOn_wk h)
            (fun σ' ws hσ' => ?_) σ _ hσ
          obtain ⟨k', hk'⟩ :=
            Option.isSome_iff_exists.mp (ih _ hk σ'.lift (litOn_lift hσ'))
          simp [hk']
  | forLoop count inits body k ihb ihk =>
      intro L hp _ σ hσ
      simp only [NBDL, Bool.and_eq_true] at hp
      refine pinAll_isSome_of (fun σ' => LitOn L σ') (fun _ h => litOn_wk h)
        (fun σ' ws hσ' => ?_) σ _ hσ
      obtain ⟨b', hb⟩ := Option.isSome_iff_exists.mp
        (ihb _ hp.1 (TRd.liftApp _ (TRd.lift σ')) (litOn_liftApp (litOn_lift hσ') _))
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp
        (ihk _ hp.2 (TRd.liftApp _ σ') (litOn_liftApp hσ' _))
      simp [hb, hk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro L hp _ σ hσ
      simp only [NBDL, Bool.and_eq_true] at hp
      obtain ⟨c, hc⟩ := Rd.eq_var_of_bit (σ cond)
      obtain ⟨t', ht⟩ := Option.isSome_iff_exists.mp (iht _ hp.1.1 σ hσ)
      obtain ⟨e', he⟩ := Option.isSome_iff_exists.mp (ihe _ hp.1.2 σ hσ)
      obtain ⟨k', hk⟩ := Option.isSome_iff_exists.mp
        (ihk _ hp.2 (TRd.liftApp _ σ) (litOn_liftApp hσ _))
      simp [nfToCatExt, hc, ht, he, hk]
  | whileLoop => intro _ hp; simp [NBDL] at hp
  | call => intro _ hp; simp [NBDL] at hp

/-- **`nfToCatExt D` is defined on every program of the domain with the declared calls `D`**,
    at every reading of its context. -/
theorem nfToCatExt_isSome_of_NBD (D : List ExtDecl) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hp : NBD D p = true) :
    ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ), (nfToCatExt D p σ).isSome :=
  fun σ => nfToCatExt_isSome_of_NBDL D p [] hp σ (litOn_nil σ)

end CatCrypt.Crypto.Hax.NFToCatComplete
