/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.DenoteTotal
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTSource
public import CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect
public import CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect
public meta import HaxLean.DenoteTotal
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeCTSource
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect

/-!
# Totality of word programs on their entry states

The bodies the front prepares from `mpn_and_n` and `ltu` run under `hax64WExit` to a value
from the entry environment of every valuation their layouts read off an entry state
satisfying the regions condition of the layout. Each statement is the run hypothesis
`hterm` of `haxc_ct_proved_all`, at every precondition `Pre`, every callee fuel and every
fuel at least the bound of the checker. The same statements for `mpn_mul_1` and
`mpn_cnd_copy_n` are `Mul1Correct.mul1_hterm` and `CndCopy.cndCopy_hterm`, beside their
layouts.

The proof is the totality theorem `Hax.Total.KindSig.denote'_run_val_of_check` at one kind
signature `wKindSig` of `u64` word programs: integer ranges, which carry the words, the count,
the loop counter and the index arithmetic, and arrays of `n` words. The count bound
`n ≤ 4` of the loops is the bound of the count register in `AbiLayout.Regions`; the entry
environment encodes every word as `Value.int` of its number and every array as the list of
its words, so every entry value has its kind.

## Main definitions

* `WKind`, `wKindSig`, `wOfKind` — the kinds of the word programs, their signature and values.
* `andKindCtx`, `ltuKindCtx` — the parameters at their kinds.

## Main results

* `wKindSig_sound` — the signature is sound for `hax64WExit`.
* `and_check`, `ltu_check` — the checker accepts the two prepared bodies, with the fuel
  bounds `4` and `0`.
* `and_hterm`, `ltu_hterm` — the run hypotheses of `haxc_ct_proved_all` at the two programs
  under `andAbi4` and `ltuAbi`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality

open CatCrypt.Crypto.SecureCompilation.Haxc
open AndNCorrect LtuCorrect
open _root_.Hax (Value Env denote')
open _root_.Hax.Total (KindSig)
open CatCrypt.Crypto.Hax (hax64WExit hax64WExit_of_ne exitScalarRes exitMarshalOk
  towerOfCallName hax64ScalarAdmit hax64ArgsShape hax64IntArgs scalarValNB hax64Exit_of_scalarAdmit
  hax64WideHead)

/-! ## The kinds of the word programs -/

/-- The kinds of the values of a `u64` word program: an array of `n` words and an integer in
    a closed range. A word is an integer in the range `[0, 2^64 - 1]`. -/
inductive WKind where
  | arr (n : Nat)
  | rng (a b : Int)
  deriving DecidableEq, Repr

/-- The kind of a word. -/
abbrev WKind.word : WKind := .rng 0 (2 ^ 64 - 1)

/-- A kind whose values are words: a range inside `[0, 2^64 - 1]`. -/
def WKind.isWord : WKind → Bool
  | .rng a b => decide (0 ≤ a) && decide (b < 2 ^ 64)
  | .arr _ => false

/-- The `u64` word operations of the signature, two words to a word. -/
def wBinOps : List String :=
  ["BitAnd#64", "BitXor#64", "wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64",
    "mulhi#64"]

/-- The checked `u64` additions of the signature: the untagged `Add` and its width-tagged
    forms `Add#64` and `Add#size`, which answer as `Add` on words. -/
def wAddOps : List String := ["Add", "Add#64", "Add#size"]

/-- The kind signature of the word programs: the word operations `wBinOps` and the shift
    `Shr#64` by an amount below `64` give words; the checked additions `wAddOps` add ranges
    whose sum stays a word; `index` and `array_update` take an index range inside the
    array. -/
def wKindSig : KindSig WKind where
  lit
    | .int n => some (.rng n n)
    | _ => none
  sig f ks :=
    match f, ks with
    | "Shr#64", [k, .rng a b] =>
      if k.isWord ∧ 0 ≤ a ∧ b < 64 then some .word else none
    | "Add", [.rng a b, .rng c d] | "Add#64", [.rng a b, .rng c d]
    | "Add#size", [.rng a b, .rng c d] =>
      if 0 ≤ a ∧ 0 ≤ c ∧ b + d < 2 ^ 64 then some (.rng (a + c) (b + d)) else none
    | "index", [.arr n, .rng a b] => if 0 ≤ a ∧ b < n then some .word else none
    | "array_update", [.arr n, .rng a b, k] =>
      if 0 ≤ a ∧ b < n ∧ k.isWord then some (.arr n) else none
    | g, [k, l] => if g ∈ wBinOps ∧ k.isWord ∧ l.isWord then some .word else none
    | _, _ => none
  range
    | .rng a b => some (a, b)
    | _ => none
  ctr a c := .rng a (c - 1)

/-- The values of a kind: an array of `n` words is the array of the integers of `n` words,
    and a range holds the integers in it. -/
def wOfKind : WKind → Value → Prop
  | .arr n, v => ∃ xs : List Nat, v = .array (xs.map fun x : Nat => Value.int (x : Int)) ∧
      xs.length = n ∧ ∀ x ∈ xs, x < 2 ^ 64
  | .rng a b, v => ∃ x : Int, v = .int x ∧ a ≤ x ∧ x ≤ b

/-! ## Contexts and fuel bounds -/

/-- The parameters of `mpn_and_n` at their kinds, the count at most `4`. -/
def andKindCtx : List (String × WKind) :=
  [("rp", .arr 4), ("up", .arr 4), ("vp", .arr 4), ("n", .rng 0 4)]

/-- The parameters of `ltu` at their kinds. -/
def ltuKindCtx : List (String × WKind) := [("x", .word), ("y", .word)]

/-! ## The heads under `hax64WExit` -/

/-- A scalar call that `hax64WExit` admits answers two words with the value of
    `Hax.hax64Builtins` when that value is a word. -/
theorem hax64WExit_word {f : String} (h1 : f ≠ "array_lit") (h2 : f ≠ "repeat")
    (h3 : f ≠ "eq#arr") (h4 : f ≠ "ne#arr") (hw : ¬ hax64WideHead f) (hl : f ≠ "len")
    (hN : f ≠ "Not") (hres : exitScalarRes f = true)
    (hto : exitMarshalOk (towerOfCallName f) = true) {a b r : Nat} (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) (hr : r < 2 ^ 64)
    (hbi : _root_.Hax.hax64Builtins f [.int a, .int b] = some (.int r)) :
    hax64WExit f [.int a, .int b] = some (.int r) := by
  rw [hax64WExit_of_ne h1 h2 h3 h4 hw (CatCrypt.Crypto.Hax.ne_select_of_exitScalarRes hres)]
  refine hax64Exit_of_scalarAdmit hbi rfl ?_
  unfold hax64ScalarAdmit hax64ArgsShape
  cases hop : CatCrypt.Crypto.Hax.hax64ScalarOp f <;>
    simp [hres, hto, hl, hN, hax64IntArgs, scalarValNB] <;> omega

/-- `Hax.hax64Builtins` computes a word operation given by `u64BinOp` on two words. -/
theorem hax64Builtins_u64 {f : String} {g : Nat → Nat → Option Nat}
    (hwo : ∀ a b : Int, _root_.Hax.hax64WordOps f [.int a, .int b] = _root_.Hax.u64BinOp a b g)
    {a b r : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hg : g a b = some r) :
    _root_.Hax.hax64Builtins f [.int a, .int b] = some (.int r) := by
  unfold _root_.Hax.hax64Builtins
  rw [hwo, _root_.Hax.u64BinOp_natCast ha hb, hg]
  rfl

/-- The heads `wBinOps`, `Shr#64` and `wAddOps` are scalar calls that `hax64WExit`
    admits. -/
theorem w_admit {f : String} (hf : f ∈ wBinOps ∨ f = "Shr#64" ∨ f ∈ wAddOps) :
    f ≠ "array_lit" ∧ f ≠ "repeat" ∧ f ≠ "eq#arr" ∧ f ≠ "ne#arr" ∧ ¬ hax64WideHead f ∧
      f ≠ "len" ∧ f ≠ "Not" ∧ exitScalarRes f = true ∧
      exitMarshalOk (towerOfCallName f) = true := by
  have hto : exitMarshalOk (towerOfCallName f) =
      exitMarshalOk (CatCrypt.Crypto.Hax.towerOfCallName_default f) := rfl
  rw [hto]
  simp only [wBinOps, wAddOps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | (rfl | rfl | rfl) <;>
    refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩ <;>
    simp [exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall, CatCrypt.Crypto.Hax.exitScalarCalls,
      CatCrypt.Crypto.Hax.towerOfCallName_default, CatCrypt.Crypto.Hax.arrCtorLen,
      exitMarshalOk, Jasmin.LowCT.TowerType.storageBytes]

/-- A word operation of `wBinOps` answers two words with a word under `hax64WExit`. -/
theorem wBinOp_total {f : String} (hf : f ∈ wBinOps) {a b : Nat} (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) : ∃ r : Nat, hax64WExit f [.int a, .int b] = some (.int r) ∧ r < 2 ^ 64 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := w_admit (.inl hf)
  have key : ∀ {g : Nat → Nat → Option Nat},
      (∀ a b : Int, _root_.Hax.hax64WordOps f [.int a, .int b] = _root_.Hax.u64BinOp a b g) →
      ∀ r : Nat, g a b = some r → r < 2 ^ 64 →
        ∃ r : Nat, hax64WExit f [.int a, .int b] = some (.int r) ∧ r < 2 ^ 64 :=
    fun hwo r hg hr => ⟨r, hax64WExit_word h1 h2 h3 h4 h5 h6 h7 h8 h9 ha hb hr
      (hax64Builtins_u64 hwo ha hb hg), hr⟩
  simp only [wBinOps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _root_.Hax.hax64WordOps_bitAnd _ rfl
      (Nat.and_lt_two_pow _ (Nat.mod_lt _ (by norm_num)))
  · exact key _root_.Hax.hax64WordOps_bitXor _ rfl
      (Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)))
  · exact key _root_.Hax.hax64WordOps_wrapping_add _ rfl (Nat.mod_lt _ (by norm_num))
  · exact key _root_.Hax.hax64WordOps_wrapping_sub _ rfl (Nat.mod_lt _ (by norm_num))
  · exact key _root_.Hax.hax64WordOps_wrapping_mul _ rfl (Nat.mod_lt _ (by norm_num))
  · refine key _root_.Hax.hax64WordOps_mulhi _ rfl ?_
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' ha hb)

/-- The shift `Shr#64` of a word by an amount below `64` is a word under `hax64WExit`. -/
theorem shr_total {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 64) :
    ∃ r : Nat, hax64WExit "Shr#64" [.int a, .int b] = some (.int r) ∧ r < 2 ^ 64 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := w_admit (f := "Shr#64") (.inr (.inl rfl))
  have hr : (a % 2 ^ 64) >>> b < 2 ^ 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by norm_num))
  exact ⟨_, hax64WExit_word h1 h2 h3 h4 h5 h6 h7 h8 h9 (b := b) ha (by omega) hr
    (hax64Builtins_u64 _root_.Hax.hax64WordOps_shr ha (by omega)
      (by simp [hb])), hr⟩

/-- A checked addition of `wAddOps` of two words whose sum is a word is that sum under
    `hax64WExit`. -/
theorem add_total {f : String} (hf : f ∈ wAddOps) {a b : Nat} (hab : a + b < 2 ^ 64) :
    hax64WExit f [.int a, .int b] = some (.int (a + b : Nat)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := w_admit (.inr (.inr hf))
  have hwo : ∀ x y : Int, _root_.Hax.hax64WordOps f [.int x, .int y] =
      _root_.Hax.u64BinOp x y fun x y => if x + y < 2 ^ 64 then some (x + y) else none := by
    intro x y
    simp only [wAddOps, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact _root_.Hax.hax64WordOps_add x y
    · rw [_root_.Hax.hax64WordOps_add64_eq_Add]; exact _root_.Hax.hax64WordOps_add x y
    · rw [_root_.Hax.hax64WordOps_addSize_eq_Add]; exact _root_.Hax.hax64WordOps_add x y
  exact hax64WExit_word h1 h2 h3 h4 h5 h6 h7 h8 h9 (by omega) (by omega) hab
    (hax64Builtins_u64 hwo (by omega) (by omega) (ite_eq_left hab))

/-! ## Soundness of the signature -/

/-- A value of a word kind is the integer of a word. -/
theorem word_of_isWord {k : WKind} (hk : k.isWord = true) {v : Value} (hv : wOfKind k v) :
    ∃ x : Nat, v = .int x ∧ x < 2 ^ 64 := by
  cases k with
  | arr n => simp [WKind.isWord] at hk
  | rng a b =>
    simp only [WKind.isWord, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨x, rfl, h1, h2⟩ := hv
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
    exact ⟨j, rfl, by omega⟩

/-- A word is a value of the word kind. -/
theorem wOfKind_word {x : Nat} (hx : x < 2 ^ 64) : wOfKind .word (.int x) :=
  ⟨x, rfl, by omega, by omega⟩

/-- **The kind signature of the word programs is sound for `hax64WExit`.** -/
theorem wKindSig_sound : wKindSig.Sound wOfKind hax64WExit where
  noCF k v h := by
    cases k <;> obtain ⟨_, rfl, _⟩ := h <;> rfl
  lit l k h := by
    cases l <;> simp only [wKindSig, reduceCtorEq, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, le_refl _, le_refl _⟩
  sig f ks k h vs hvs := by
    simp only [wKindSig] at h
    split at h
    next k' a b =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨hx, ⟨y, rfl, hy1, hy2⟩, -⟩ := hvs
      obtain ⟨x, rfl, hx'⟩ := word_of_isWord hc.1 hx
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
      obtain ⟨r, hr, hr'⟩ := shr_total hx' (b := j) (by omega)
      exact ⟨_, hr, wOfKind_word hr'⟩
    all_goals first
      | (rename_i a b c d
         split_ifs at h with hc
         cases h
         rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;>
           simp only [KindSig.KindsOK, and_false] at hvs
         obtain ⟨⟨x, rfl, hx1, hx2⟩, ⟨y, rfl, hy1, hy2⟩, -⟩ := hvs
         obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ x)
         obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ y)
         exact ⟨_, add_total (by simp [wAddOps]) (by omega), _, rfl, by omega, by omega⟩)
      | skip
    next n a b =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨⟨xs, rfl, hlen, hxs⟩, ⟨i, rfl, hi1, hi2⟩, -⟩ := hvs
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      have hj : j < (xs.map fun x : Nat => Value.int (x : Int)).length := by simp; omega
      refine ⟨_, CatCrypt.Crypto.Hax.arrayOps_hax64WExit.index _ j hj
        (by simp [Value.isControlFlow]), ?_⟩
      simp only [List.getElem_map]
      exact wOfKind_word (hxs _ (List.getElem_mem _))
    next n a b k' =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩ <;>
        simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨⟨xs, rfl, hlen, hxs⟩, ⟨i, rfl, hi1, hi2⟩, hz, -⟩ := hvs
      obtain ⟨u, rfl, hu⟩ := word_of_isWord hc.2.2 hz
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
      have hj : j < (xs.map fun x : Nat => Value.int (x : Int)).length := by simp; omega
      refine ⟨_, CatCrypt.Crypto.Hax.arrayOps_hax64WExit.update _ j _ hj, xs.set j u, ?_,
        by simpa using hlen, ?_⟩
      · rw [List.map_set]
      · intro x hx
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hxs x hx
        · exact hu
    next g k1 k2 _ _ _ _ =>
      split_ifs at h with hc
      cases h
      rcases vs with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩ <;> simp only [KindSig.KindsOK, and_false] at hvs
      obtain ⟨hx, hy, -⟩ := hvs
      obtain ⟨x, rfl, hx'⟩ := word_of_isWord hc.2.1 hx
      obtain ⟨y, rfl, hy'⟩ := word_of_isWord hc.2.2 hy
      obtain ⟨r, hr, hr'⟩ := wBinOp_total hc.1 hx' hy'
      exact ⟨_, hr, wOfKind_word hr'⟩
    next => cases h
  range k a b h v hv := by
    cases k <;> simp only [wKindSig, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, rfl, h1, h2⟩ := hv
    exact ⟨x, rfl, h1, h2⟩
  ctr a c n h1 h2 := ⟨n, rfl, h1, by omega⟩

/-! ## Entry environments -/

open CatCrypt.Crypto.Hax.ImpToNF (entryCtx entryEnvOf crateBi)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.Hax.NFToCat (mapVal)
open CatCrypt.Crypto.SecureCompilation.VIR (Ctxt)

/-- The encoding of an array of `n` words is a value of the kind of an array of `n` words. -/
theorem wOfKind_arr {n : Nat} (f : Fin n → BitVec 64) :
    wOfKind (.arr n) (.array (List.ofFn fun i => Value.int ((f i).toNat : Int))) :=
  ⟨List.ofFn fun i => (f i).toNat, by simp [List.map_ofFn, Function.comp_def], by simp,
    by simp only [List.mem_ofFn]; rintro _ ⟨i, rfl⟩; exact (f i).isLt⟩

/-- The encoding of a word is a value of the word kind. -/
theorem wOfKind_bv (x : BitVec 64) : wOfKind .word (.int (x.toNat : Int)) :=
  wOfKind_word x.isLt

/-- The encoding of a word whose number is at most `c` is a value of the range `[0, c]`. -/
theorem wOfKind_bv_le {c : Nat} (x : BitVec 64) (h : x.toNat ≤ c) :
    wOfKind (.rng 0 c) (.int (x.toNat : Int)) :=
  ⟨_, rfl, by omega, by omega⟩

/-! ## `mpn_and_n` -/

/-- The checker accepts the body the front prepares from `mpn_and_n` at the kind of an array
    of `4` words, with the fuel bound `4`. -/
theorem and_check :
    wKindSig.check andKindCtx (nfBody (bindConsts andAbi4.consts Mpn.mpn_and_n_texpr)) =
      some (some (.arr 4), 4) := by
  native_decide

/-- **Totality of `mpn_and_n` on entry states.** For every precondition `Pre`, callee fuel
    `fuelC` and fuel `F` at least `4`, from the entry environment of every valuation `V` that
    `andAbi4` reads off an entry state satisfying `andAbi4.Regions`, the body the front
    prepares from `mpn_and_n` runs to a value at the builtins of the module. The count bound
    `n ≤ 4` is the bound of `%rcx` in `andAbi4.Regions`; this is the run hypothesis `hterm` of
    `haxc_ct_proved_all` at `mpn_and_n` under `andAbi4`. The proof is
    `KindSig.denote'_run_val_of_check` at `wKindSig` with the checker run `and_check`. -/
theorem and_hterm (Pre : AState → Prop) (fuelC : Nat) {F : Nat} (hF : 4 ≤ F) :
    ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry andAbi4))), andAbi4.Regions sa →
      Pre sa → AbiValOf andAbi4 sa (ctMapValD (mapVal V)) →
      ∃ v env', (denote' (crateBi ((Mpn.mpn_and_n_texpr : HaxModule).prepared nfBody)
        hax64WExit fuelC (Mpn.mpn_and_n_texpr : HaxModule).depth) F
        (nfBody (bindConsts andAbi4.consts (Mpn.mpn_and_n_texpr : HaxModule).entry))).run
          (entryEnvOf (abiEntry andAbi4) V) = (.val v, env') := by
  intro sa V hR _ hV
  rw [crateBi_prepared_of_fns_nil rfl]
  refine KindSig.denote'_run_val_of_check wKindSig_sound and_check hF ?_
  rcases V with _ | ⟨n, _ | ⟨vp, _ | ⟨up, _ | ⟨rp, _ | _⟩⟩⟩⟩
  obtain ⟨_, ha, -, _, hn⟩ := hV.reg (w := 64) .here
  change andAbi4.args[3]? = _ at ha
  simp only [andAbi4, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.some.injEq] at ha
  subst ha
  change n = sa.regs "%rcx" at hn
  have hb : n.toNat ≤ 4 := hn ▸ hR.1 ("%rcx", 4) (by simp [andAbi4])
  intro x k hx
  simp only [andKindCtx, List.lookup_cons, List.lookup_nil] at hx
  by_cases h1 : x = "rp"
  · subst h1; cases hx; exact ⟨_, rfl, wOfKind_arr _⟩
  by_cases h2 : x = "up"
  · subst h2; cases hx; exact ⟨_, rfl, wOfKind_arr _⟩
  by_cases h3 : x = "vp"
  · subst h3; cases hx; exact ⟨_, rfl, wOfKind_arr _⟩
  by_cases h4 : x = "n"
  · subst h4; cases hx; exact ⟨_, rfl, wOfKind_bv_le n hb⟩
  rw [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2, beq_eq_false_iff_ne.mpr h3,
    beq_eq_false_iff_ne.mpr h4] at hx
  cases hx

/-! ## `ltu` -/

/-- The checker accepts the body the front prepares from `ltu`, with the constant `ONES`
    bound, at the word kind, with the fuel bound `0`. -/
theorem ltu_check :
    wKindSig.check ltuKindCtx (nfBody (bindConsts ltuAbi.consts Mpn.ltu_texpr)) =
      some (some .word, 0) := by
  native_decide

/-- **Totality of `ltu` on entry states.** For every precondition `Pre`, callee fuel `fuelC`
    and fuel `F`, from the entry environment of every valuation of the two words of `ltu`,
    the body the front prepares from `ltu` with the constant `ONES` bound runs to a value at
    the builtins of the module: the run hypothesis `hterm` of `haxc_ct_proved_all` at `ltu`
    under `ltuAbi`. The body is straight-line, so no bound on the entry state is used. -/
theorem ltu_hterm (Pre : AState → Prop) (fuelC F : Nat) :
    ∀ (sa : AState) (V : Ctxt.Valuation (entryCtx (abiEntry ltuAbi))), ltuAbi.Regions sa →
      Pre sa → AbiValOf ltuAbi sa (ctMapValD (mapVal V)) →
      ∃ v env', (denote' (crateBi ((Mpn.ltu_texpr : HaxModule).prepared nfBody)
        hax64WExit fuelC (Mpn.ltu_texpr : HaxModule).depth) F
        (nfBody (bindConsts ltuAbi.consts (Mpn.ltu_texpr : HaxModule).entry))).run
          (entryEnvOf (abiEntry ltuAbi) V) = (.val v, env') := by
  intro sa V _ _ _
  rw [crateBi_prepared_of_fns_nil rfl]
  refine KindSig.denote'_run_val_of_check wKindSig_sound ltu_check (Nat.zero_le F) ?_
  rcases V with _ | ⟨y, _ | ⟨x, _ | _⟩⟩
  intro z k hz
  simp only [ltuKindCtx, List.lookup_cons, List.lookup_nil] at hz
  by_cases h1 : z = "x"
  · subst h1; cases hz; exact ⟨_, rfl, wOfKind_bv x⟩
  by_cases h2 : z = "y"
  · subst h2; cases hz; exact ⟨_, rfl, wOfKind_bv y⟩
  rw [beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2] at hz
  cases hz

end CatCrypt.Crypto.SecureCompilation.Haxc.CTTotality
