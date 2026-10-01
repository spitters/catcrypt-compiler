/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

/-!
# The `u64` fragment of `NFProg nfDialect` in `catCryptDialect`

`nfToCat` translates a program of `NFProg nfDialect` over the `u64` table into a program of
`NFProg catCryptDialect`, which `NFProgToComL.nfToComL` lowers to `ComL`. The types map by
`catTy`: a `64`-bit word and an integer to `sword 64`, an integer array of `n` elements to
`memref n`. A value of the source and a value of the target are related by `VRel`: an integer
is the natural number of the word, an array element by element. The variables map by a typed
renaming `TRen` along `catTy`.

The operations of the fragment are the scalar calls of `hax64NFScalar` on two words, `index`
and `array_update` on integer arrays, integer literals in `[0, 2^64)` and the loop operations
`ctr` and `trip`. A counted loop is translated when its lower bound is the literal `0`, which
the readings of the literal zeros `ZeroRd` record: `trip 0 hi` and `ctr 0 i` are word
additions of the zero word.

## Main definitions

* `catTy`, `VRel`, `VRelL` — the type map and the relation of values.
* `TRen`, `TRen.lift`, `TRen.liftApp`, `TRen.Agree` — typed renamings along `catTy`, and
  the relation of valuations they state.
* `catOp?`, `nfToCat` — the translation of an operation and of a program.
* `ZeroRd` — the readings of the variables bound to the literal `0`.
* `toCatVal`, `mapVal`, `TRen.id`, `abiParamsArr` — the entry: the mapped valuation, the
  renaming of a context to its mapped context, and the parameters of a System V layout with
  integer array types.

## Main results

* `catOp_sound` — a translated operation denotes a value related to the value of the source
  operation.
* `nfToCat_sound` — a translated program denotes values related to the values of the source
  program, under every leaf table contained in the `u64` table.
* `TRen.agree_id`, `inRange_of_envOf` — the entry valuation is in range and related to its
  mapped valuation.
* `entryTyped_of_envOf_arr` — an environment a layout reads off an entry state is typed at
  `abiParamsArr σ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.NFToCat

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open Ctxt (Var Valuation)

/-! ## 1. Types and values -/

/-- The type of `catCryptDialect` a type of the fragment maps to: a word to a word, an
    integer to a `64`-bit word, an array to a memref of its length, a bit and the unit to
    themselves. -/
@[reducible] def catTy : NfTy → CryptoTy
  | .word w => .sword w
  | .int => .sword 64
  | .arr n _ => .memref n
  | .bit => .bit
  | _ => .unit

/-- The relation of a source value and a target value at a type of the fragment: equal
    words and bits, an integer equal to the natural number of the word, an integer array
    element by element. -/
def VRel : (t : NfTy) → t.denote → (catTy t).denote → Prop
  | .word _, x, y => x = y
  | .int, z, y => z = (y.toNat : Int)
  | .arr _ .int, f, g => ∀ i, f i = ((g i).toNat : Int)
  | .bit, b, b' => b = b'
  | .unit, _, _ => True
  | _, _, _ => False

/-- The relation of two vectors of values, component by component. -/
def VRelL : (ts : List NfTy) → Valuation (d := nfDialect) ts →
    Valuation (d := catCryptDialect) (ts.map catTy) → Prop
  | [], .nil, .nil => True
  | t :: ts, .cons x xs, .cons y ys => VRel t x y ∧ VRelL ts xs ys

/-! ## 2. Typed renamings -/

/-- A renaming from `Γ` to `Δ` along `catTy`: each variable to a variable of the mapped
    type. -/
abbrev TRen (Γ : Ctxt nfDialect) (Δ : Ctxt catCryptDialect) : Type :=
  ∀ {t : NfTy}, Var Γ t → Var Δ (catTy t)

/-- A renaming under one more binding. -/
def TRen.lift {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy} (σ : TRen Γ Δ) :
    TRen (s :: Γ) (catTy s :: Δ)
  | _, .here => .here
  | _, .there v => .there (σ v)

/-- A renaming under the bindings `cs`. -/
def TRen.liftApp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} :
    (cs : List NfTy) → TRen Γ Δ → TRen (cs ++ Γ) (cs.map catTy ++ Δ)
  | [], σ => σ
  | _ :: cs, σ => TRen.lift (TRen.liftApp cs σ)

/-- A renaming applied to a vector of variables. -/
def TRen.vars {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRen Γ Δ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts →
      HVector (fun t => Var Δ t) (ts.map catTy)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (σ v) (σ.vars vs)

/-- The renaming `σ` relates the valuations `V` and `W`: every variable reads in `W`, at
    its image, a value related to the value it reads in `V`. -/
def TRen.Agree {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRen Γ Δ)
    (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : NfTy) (v : Var Γ t), VRel t (v.lookup V) ((σ v).lookup W)

/-- The lifted renaming relates the valuations extended by related values. -/
theorem TRen.agree_lift {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy}
    {σ : TRen Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) {x : s.denote}
    {y : (catTy s).denote} (hxy : VRel s x y) :
    TRen.Agree (TRen.lift (s := s) σ) (V.extend x) (W.extend y) := by
  intro t v
  cases v with
  | here => exact hxy
  | there v => exact h t v

/-- The renaming lifted under `cs` relates the valuations extended by related vectors. -/
theorem TRen.agree_liftApp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    {σ : TRen Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) :
    (cs : List NfTy) → (A : Valuation (d := nfDialect) cs) →
    (B : Valuation (d := catCryptDialect) (cs.map catTy)) → VRelL cs A B →
    TRen.Agree (TRen.liftApp cs σ) (hvAppend A V) (hvAppend B W)
  | [], .nil, .nil, _ => h
  | _ :: cs, .cons _ A, .cons _ B, hAB =>
      TRen.agree_lift (TRen.agree_liftApp h cs A B hAB.2) hAB.1

/-- The variables a renaming maps read related vectors. -/
theorem TRen.vrelL_vars {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {σ : TRen Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts),
      VRelL ts (Expr.lookupArgs vs V) (Expr.lookupArgs (σ.vars vs) W)
  | [], .nil => trivial
  | t :: _, .cons v vs => ⟨h t v, TRen.vrelL_vars h vs⟩

/-! ## 3. The scalar operations -/

/-- The expression of `catCryptDialect` of a scalar call of `hax64NFScalar` on two words. -/
def scalarCatExpr {Δ : Ctxt catCryptDialect} (f : String) (a b : Var Δ (.sword 64)) :
    Option (Expr catCryptDialect Δ (.sword 64)) :=
  match f with
  | "BitXor#64" => some ⟨.bvXor 64, rfl, .cons a (.cons b .nil)⟩
  | "BitAnd#64" => some ⟨.bvAnd 64, rfl, .cons a (.cons b .nil)⟩
  | "wrapping_add#64" => some ⟨.bvAdd 64, rfl, .cons a (.cons b .nil)⟩
  | "wrapping_sub#64" => some ⟨.bvSub 64, rfl, .cons a (.cons b .nil)⟩
  | "wrapping_mul#64" => some ⟨.bvMul 64, rfl, .cons a (.cons b .nil)⟩
  | "mulhi#64" => some ⟨.bvMulHi 64, rfl, .cons a (.cons b .nil)⟩
  | "Shr#64" => some ⟨.bvShiftRV 64, rfl, .cons a (.cons b .nil)⟩
  | "Shl#64" => some ⟨.bvShiftLV 64, rfl, .cons a (.cons b .nil)⟩
  | "Add" => some ⟨.bvAdd 64, rfl, .cons a (.cons b .nil)⟩
  | _ => none

/-- The word a scalar call of `scalarCatExpr` computes. -/
def scalarSem : String → BitVec 64 → BitVec 64 → BitVec 64
  | "BitXor#64", x, y => x ^^^ y
  | "BitAnd#64", x, y => x &&& y
  | "wrapping_add#64", x, y => x + y
  | "wrapping_sub#64", x, y => x - y
  | "wrapping_mul#64", x, y => x * y
  | "mulhi#64", x, y => mulHiC x y
  | "Shr#64", x, y => x >>> y.toNat
  | "Shl#64", x, y => x <<< y.toNat
  | "Add", x, y => x + y
  | _, _, _ => 0

/-- The expression of a scalar call denotes the word of `scalarSem`. -/
theorem scalarCatExpr_denote {Δ : Ctxt catCryptDialect} {f : String}
    {a b : Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : scalarCatExpr f a b = some e) (W : Valuation Δ) :
    e.denote W = scalarSem f (a.lookup W) (b.lookup W) := by
  unfold scalarCatExpr at h
  split at h <;> (try cases h) <;> rfl

/-- **A scalar call on the integers of two words returns the integer of the word of
    `scalarSem`.** -/
theorem scalarSem_sound {Δ : Ctxt catCryptDialect} {f : String}
    {a b : Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : scalarCatExpr f a b = some e) (x y : BitVec 64) {v : _root_.Hax.Value}
    (hv : _root_.Hax.hax64Builtins f [.int (x.toNat : Int), .int (y.toNat : Int)] = some v) :
    v = .int ((scalarSem f x y).toNat : Int) := by
  have hx := x.isLt
  have hy := y.isLt
  unfold scalarCatExpr at h
  split at h <;> (try cases h) <;> simp only [_root_.Hax.hax64Builtins] at hv
  · rw [_root_.Hax.hax64WordOps_bitXor, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    simp [scalarSem, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, BitVec.toNat_xor]
  · rw [_root_.Hax.hax64WordOps_bitAnd, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    simp [scalarSem, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, BitVec.toNat_and]
  · rw [_root_.Hax.hax64WordOps_wrapping_add, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    simp [scalarSem, BitVec.toNat_add]
  · rw [_root_.Hax.hax64WordOps_wrapping_sub, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    simp only [scalarSem, BitVec.toNat_sub, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    congr 2
    omega
  · rw [_root_.Hax.hax64WordOps_wrapping_mul, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    simp [scalarSem, BitVec.toNat_mul]
  · rw [_root_.Hax.hax64WordOps_mulhi, _root_.Hax.u64BinOp_natCast hx hy] at hv
    obtain rfl : _ = v := Option.some.inj hv
    have hlt : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
        _ = 2 ^ 64 * 2 ^ 64 := rfl
    show _root_.Hax.Value.int (((x.toNat * y.toNat) >>> 64 : Nat) : Int) =
      _root_.Hax.Value.int (((BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64)).toNat : Nat) : Int)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, Nat.shiftRight_eq_div_pow]
  · rw [_root_.Hax.hax64WordOps_shr, _root_.Hax.u64BinOp_natCast hx hy] at hv
    split at hv
    · obtain rfl : _ = v := Option.some.inj hv
      simp [scalarSem, Nat.mod_eq_of_lt hx, BitVec.toNat_ushiftRight]
    · simp [_root_.Hax.widthArrayOps] at hv
  · rw [_root_.Hax.hax64WordOps_shl, _root_.Hax.u64BinOp_natCast hx hy] at hv
    split at hv
    · obtain rfl : _ = v := Option.some.inj hv
      simp [scalarSem, Nat.mod_eq_of_lt hx, BitVec.toNat_shiftLeft]
    · simp [_root_.Hax.widthArrayOps] at hv
  · rw [_root_.Hax.hax64WordOps_add, _root_.Hax.u64BinOp_natCast hx hy] at hv
    split at hv
    · rename_i hxy
      obtain rfl : _ = v := Option.some.inj hv
      simp [scalarSem, BitVec.toNat_add, Nat.mod_eq_of_lt hxy]
    · simp [_root_.Hax.widthArrayOps] at hv

/-! ## 4. The operations -/

/-- A type whose values encode as integers maps to `sword 64`. -/
theorem catTy_of_wordTy {t : NfTy} (h : ImpToNF.hax64NFWordTy t = true) :
    catTy t = .sword 64 := by
  cases t with
  | int => rfl
  | word w =>
      have hw : w = 64 := by
        revert h; unfold ImpToNF.hax64NFWordTy; split <;> simp_all
      subst hw; rfl
  | _ => simp [ImpToNF.hax64NFWordTy] at h

/-- A variable of a type whose values encode as integers, at `sword 64`. -/
def asWord {Δ : Ctxt catCryptDialect} (t : NfTy) (v : Var Δ (catTy t)) :
    Option (Var Δ (.sword 64)) :=
  if h : ImpToNF.hax64NFWordTy t = true then some (catTy_of_wordTy h ▸ v) else none

/-- A variable of an integer array type, at the memref of its length. -/
def asArr {Δ : Ctxt catCryptDialect} : (t : NfTy) → Var Δ (catTy t) →
    Option (Σ n : Nat, Var Δ (.memref n))
  | .arr n .int, v => some ⟨n, v⟩
  | _, _ => none

/-- The expression of a call `f` of the `u64` table on the renamed arguments `args`: a scalar
    call of `hax64NFScalar`, `index` of an integer array, `array_update` of an integer
    array. -/
def catCall? {Δ : Ctxt catCryptDialect} (f : String) :
    (as : List NfTy) → (r : NfTy) → HVector (fun t => Var Δ t) (as.map catTy) →
      Option (Expr catCryptDialect Δ (catTy r))
  | [ta, tb], .int, args =>
      if f = "index" then
        (asArr ta args.head).bind fun ⟨n, a⟩ => (asWord tb args.tail.head).map fun i =>
          ⟨.memrefGetDyn n, rfl, .cons a (.cons i .nil)⟩
      else (asWord ta args.head).bind fun x => (asWord tb args.tail.head).bind fun y =>
        scalarCatExpr f x y
  | [ta, ti, tv], .arr n' .int, args =>
      if f = "array_update" then
        (asArr ta args.head).bind fun ⟨n, m⟩ =>
          if h : n = n' then
            (asWord ti args.tail.head).bind fun i' => (asWord tv args.tail.tail.head).map fun x' =>
              ⟨.memrefSetDyn n, congrArg CryptoTy.memref h, .cons m (.cons i' (.cons x' .nil))⟩
          else none
      else none
  | _, _, _ => none

/-- The readings of the literal zeros of a context: `true` for an integer variable whose value
    is `0`. -/
abbrev ZeroRd (Γ : Ctxt nfDialect) : Type := ∀ {t : NfTy}, Var Γ t → Bool

/-- The readings of the literal zeros under one more binding. -/
def ZeroRd.cons {Γ : Ctxt nfDialect} {s : NfTy} (z : Bool) (κ : ZeroRd Γ) : ZeroRd (s :: Γ)
  | _, .here => z
  | _, .there v => κ v

/-- The readings of the literal zeros under the bindings `cs`, none of which is a literal
    zero. -/
def ZeroRd.app {Γ : Ctxt nfDialect} : (cs : List NfTy) → ZeroRd Γ → ZeroRd (cs ++ Γ)
  | [], κ => κ
  | _ :: cs, κ => ZeroRd.cons false (ZeroRd.app cs κ)

/-- The readings of the literal zeros hold of the valuation `V`. -/
def ZeroRd.Ok {Γ : Ctxt nfDialect} (κ : ZeroRd Γ) (V : Valuation Γ) : Prop :=
  ∀ (t : NfTy) (v : Var Γ t), κ v = true → NfTy.toInt? t (v.lookup V) = some 0

/-- The operation `op` binds the literal zero. -/
def zeroLit : NfOp → Bool
  | .named _ op => zeroLit op
  | .ilit .int 0 => true
  | _ => false

/-- **The expression of an operation** of the fragment on the variables `args`, through the
    renaming `σ`: a call by `catCall?`, an integer literal in `[0, 2^64)` by `bvConst`, and
    `ctr` and `trip` on a lower bound that reads as the literal zero as the word addition of
    the zero word. -/
def catOp? {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRen Γ Δ) (κ : ZeroRd Γ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Option (Expr catCryptDialect Δ (catTy op.ret))
  | .named _ op, args => catOp? σ κ op args
  | .call f as r, args => catCall? f as r (σ.vars args)
  | .ilit t v, _ =>
      if ht : t = .int ∧ 0 ≤ v ∧ v < 2 ^ 64 then
        some ⟨.bvConst 64 (BitVec.ofNat 64 v.toNat), by rw [ht.1]; rfl, .nil⟩
      else none
  | .ctr, args =>
      if κ args.head then
        some ⟨.bvAdd 64, rfl, .cons (σ args.head) (.cons (σ args.tail.head) .nil)⟩
      else none
  | .trip t, args =>
      if κ args.head then
        (asWord t (σ args.tail.head)).map fun h =>
          ⟨.bvAdd 64, rfl, .cons (σ args.head) (.cons h .nil)⟩
      else none
  | _, _ => none

/-! ## 5. The operations simulate -/

/-- A value of a type whose values encode as integers, related to a word, encodes as the
    integer of the word. -/
theorem asWord_enc {Δ : Ctxt catCryptDialect} {t : NfTy} {v : Var Δ (catTy t)}
    {w : Var Δ (.sword 64)} (h : asWord t v = some w) (W : Valuation Δ) {x : t.denote}
    (hx : VRel t x (v.lookup W)) : ImpToNF.enc t x = .int ((w.lookup W).toNat : Int) := by
  unfold asWord at h
  split at h
  · rename_i ht
    simp only [Option.some.injEq] at h
    subst h
    cases t with
    | int =>
        change x = _ at hx
        subst hx
        rfl
    | word n =>
        have hn : n = 64 := by
          revert ht; unfold ImpToNF.hax64NFWordTy; split <;> simp_all
        subst hn
        change x = _ at hx
        subst hx
        rfl
    | _ => simp [ImpToNF.hax64NFWordTy] at ht
  · cases h

/-- A value of an integer array type, related to a memref, encodes as the integers of a
    function related to the memref element by element. -/
theorem asArr_rel {Δ : Ctxt catCryptDialect} {t : NfTy} {v : Var Δ (catTy t)} {n : Nat}
    {m : Var Δ (.memref n)} (h : asArr t v = some ⟨n, m⟩) (W : Valuation Δ) {x : t.denote}
    (hx : VRel t x (v.lookup W)) :
    ∃ g : Fin n → Int, ImpToNF.enc t x = .array (List.ofFn fun k => .int (g k)) ∧
      ∀ k, g k = ((m.lookup W) k).toNat := by
  unfold asArr at h
  split at h
  · cases h
    exact ⟨x, rfl, hx⟩
  · cases h

/-- The dynamic read of a memref below its length is the element. -/
theorem memGetDyn_of_lt' {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n) :
    memGetDyn arr k = arr ⟨k, hk⟩ := by
  match n, arr with
  | m + 1, arr =>
      simp only [memGetDyn]
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hk)

/-- The dynamic write of a memref below its length writes the element. -/
theorem memSetDyn_of_lt' {n : Nat} (arr : Fin n → BitVec 64) {k : Nat} (hk : k < n)
    (v : BitVec 64) : memSetDyn arr k v = fun j => if j = ⟨k, hk⟩ then v else arr j := by
  match n, arr with
  | m + 1, arr =>
      funext j
      simp only [memSetDyn]
      congr 1
      simp only [Nat.mod_eq_of_lt hk]

/-- `index` of an array of integers returns the integer at an index below its length. -/
theorem index_ofFn {n : Nat} {g : Fin n → Int} {i : Nat} {v : _root_.Hax.Value}
    (hv : _root_.Hax.hax64Builtins "index"
      [.array (List.ofFn fun k => .int (g k)), .int (i : Int)] = some v) :
    ∃ hk : i < n, v = .int (g ⟨i, hk⟩) := by
  simp only [_root_.Hax.hax64Builtins] at hv
  rw [_root_.Hax.hax64WordOps_index] at hv
  change _root_.Hax.widthArrayOps "index"
    [.array (List.ofFn fun k => .int (g k)), .int (i : Int)] = some v at hv
  rw [_root_.Hax.widthArrayOps_index_int] at hv
  simp only [Int.natCast_nonneg, if_true, Int.toNat_natCast, List.getElem?_ofFn] at hv
  by_cases hk : i < n
  · refine ⟨hk, ?_⟩
    simp only [hk, dif_pos, Option.bind_some] at hv
    exact (Option.some.inj hv).symm
  · simp [hk] at hv

/-- `array_update` of an array of integers at an index below its length with an integer
    returns the array with that element replaced; it fails at an index beyond. -/
theorem update_ofFn {n : Nat} {g : Fin n → Int} {i : Nat} {z : Int} {v : _root_.Hax.Value}
    (hv : _root_.Hax.hax64Builtins "array_update"
      [.array (List.ofFn fun k => .int (g k)), .int (i : Int), .int z] = some v) :
    ∃ hk : i < n, v = .array (List.ofFn fun k => .int (if k = ⟨i, hk⟩ then z else g k)) := by
  simp only [_root_.Hax.hax64Builtins] at hv
  rw [_root_.Hax.hax64WordOps_array_update] at hv
  change _root_.Hax.widthArrayOps "array_update"
    [.array (List.ofFn fun k => .int (g k)), .int (i : Int), .int z] = some v at hv
  rw [_root_.Hax.widthArrayOps_array_update_int] at hv
  simp only [Int.natCast_nonneg, decide_true, Int.toNat_natCast, List.length_ofFn,
    Bool.true_and] at hv
  by_cases hk : i < n
  · refine ⟨hk, ?_⟩
    simp only [hk, decide_true, if_true, Option.some.injEq] at hv
    subst hv
    congr 1
    apply List.ext_getElem
    · simp
    · intro j h1 h2
      simp only [List.getElem_set, List.getElem_ofFn, Fin.mk.injEq]
      by_cases hj : i = j
      · subst hj; simp
      · simp [hj, Ne.symm hj]
  · simp [hk] at hv

/-- The integers of a function decode as that function at its array type. -/
theorem dec_arr_ofFn {n : Nat} (g : Fin n → Int) :
    ImpToNF.dec (.arr n .int) (.array (List.ofFn fun k => .int (g k))) = some g := by
  obtain ⟨g', hd, he⟩ := ImpToNF.dec_arr_int (n := n) (List.ofFn fun k => .int (g k))
    (fun w hw => by obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hw; exact ⟨g k, rfl⟩) (by simp)
  rw [hd]
  congr 1
  funext k
  have := congrArg (fun w : _root_.Hax.Value => match w with
    | .array l => l[k.1]? | _ => none) he
  simp only [ImpToNF.enc, List.getElem?_ofFn, k.2, dif_pos] at this
  simpa using this.symm

/-- The table `bi` is a part of the `u64` table. -/
def SubTable (bi : _root_.Hax.Builtins) : Prop :=
  ∀ f vals v, bi f vals = some v → _root_.Hax.hax64Builtins f vals = some v

/-- **A call of the `u64` table simulates.** Under `SubTable bi`, the expression `catCall?`
    builds on variables reading values related to the arguments denotes a value related to the
    value of the call. -/
theorem catCall_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) :
    ∀ (as : List NfTy) (r : NfTy) (args : HVector (fun t => Var Δ t) (as.map catTy))
      (e : Expr catCryptDialect Δ (catTy r)) (xs : Valuation (d := nfDialect) as)
      (y : r.denote), catCall? f as r args = some e →
      VRelL as xs (Expr.lookupArgs args W) →
      (bi f (ImpToNF.encAll as xs)).bind (ImpToNF.dec r) = some y →
      VRel r y (e.denote W) := by
  intro as r args e xs y h hx hy
  unfold catCall? at h
  split at h
  · rename_i ta tb args
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | _⟩⟩
    obtain ⟨hx₁, hx₂, -⟩ := hx
    change (bi f [ImpToNF.enc ta x₁, ImpToNF.enc tb x₂]).bind (ImpToNF.dec .int) = some y at hy
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hv := hbi _ _ _ hbv
    have hyv := ImpToNF.dec_sound .int v y hdv
    split at h
    · rename_i hf
      subst hf
      obtain ⟨⟨n, a'⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨g, hg, hgm⟩ := asArr_rel ha W hx₁
      rw [hg, asWord_enc hi W hx₂] at hv
      obtain ⟨hk, hvk⟩ := index_ofFn hv
      rw [hvk] at hyv
      change y = ((memGetDyn (a'.lookup W) (i'.lookup W).toNat).toNat : Int)
      rw [memGetDyn_of_lt' _ hk, ← hgm]
      change _root_.Hax.Value.int _ = _root_.Hax.Value.int y at hyv
      exact (_root_.Hax.Value.int.inj hyv).symm
    · obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
      rw [asWord_enc hxa W hx₁, asWord_enc hw W hx₂] at hv
      have := scalarSem_sound h _ _ hv
      rw [this] at hyv
      have hd : (e.denote W : BitVec 64) = scalarSem f (x.lookup W) (w.lookup W) :=
        scalarCatExpr_denote h W
      change _root_.Hax.Value.int _ = _root_.Hax.Value.int y at hyv
      change y = (((e.denote W : BitVec 64)).toNat : Int)
      rw [hd]
      exact (_root_.Hax.Value.int.inj hyv).symm
  · rename_i ta ti tv n' args
    rcases args with _ | ⟨m₀, _ | ⟨i₀, _ | ⟨x₀, _ | _⟩⟩⟩
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | _⟩⟩⟩
    obtain ⟨hx₁, hx₂, hx₃, -⟩ := hx
    change (bi f [ImpToNF.enc ta x₁, ImpToNF.enc ti x₂, ImpToNF.enc tv x₃]).bind
      (ImpToNF.dec (.arr n' .int)) = some y at hy
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hv := hbi _ _ _ hbv
    split at h
    · rename_i hf
      subst hf
      obtain ⟨⟨n, m⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      dsimp only at h
      split at h
      · rename_i hn
        subst hn
        obtain ⟨i', hi, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨g, hg, hgm⟩ := asArr_rel ha W hx₁
        rw [hg, asWord_enc hi W hx₂, asWord_enc hx' W hx₃] at hv
        obtain ⟨hk, hvk⟩ := update_ofFn hv
        rw [hvk, dec_arr_ofFn] at hdv
        cases hdv
        intro k
        change _ = ((memSetDyn (m.lookup W) (i'.lookup W).toNat (x'.lookup W) k).toNat : Int)
        rw [memSetDyn_of_lt' _ hk]
        by_cases hkk : k = ⟨(i'.lookup W).toNat, hk⟩
        · simp [hkk]
        · simp [hkk, hgm]
      · cases h
    · cases h
  · cases h

/-- **An operation of the fragment simulates.** Under `SubTable bi`, the expression `catOp?`
    builds, from a renaming relating the valuations and readings of literal zeros that hold,
    denotes a value related to the value of the operation. -/
theorem catOp_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi) {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRen Γ Δ) (κ : ZeroRd Γ) {V : Valuation Γ}
    {W : Valuation Δ} (hag : σ.Agree V W) (hκ : κ.Ok V) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig)
      (e : Expr catCryptDialect Δ (catTy op.ret)) (y : op.ret.denote),
      catOp? σ κ op args = some e →
      nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V) = some y →
      VRel op.ret y (e.denote W) := by
  intro op
  induction op with
  | named n op ih =>
      intro args e y h hy
      exact ih args e y h hy
  | call f as r =>
      intro args e y h hy
      exact catCall_sound hbi W f as r (σ.vars args) e (Expr.lookupArgs args V) y h
        (TRen.vrelL_vars hag args) hy
  | ilit t v =>
      intro args e y h hy
      change (if ht : t = .int ∧ 0 ≤ v ∧ v < 2 ^ 64 then
        some (⟨.bvConst 64 (BitVec.ofNat 64 v.toNat), by rw [ht.1]; rfl, .nil⟩ :
          Expr catCryptDialect Δ (catTy t))
        else none) = some e at h
      split at h
      · rename_i ht
        obtain ⟨rfl, h0, h1⟩ := ht
        cases h
        change some v = some y at hy
        cases hy
        change v = ((BitVec.ofNat 64 v.toNat).toNat : Int)
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
      · cases h
  | ctr =>
      intro args e y h hy
      rcases args with _ | ⟨lo, _ | ⟨i, _ | _⟩⟩
      change (if κ lo then
        some (⟨.bvAdd 64, rfl, .cons (σ lo) (.cons (σ i) .nil)⟩ :
          Expr catCryptDialect Δ (catTy .int))
        else none) = some e at h
      split at h
      · rename_i hz
        cases h
        have hy' := Option.some.inj hy
        subst hy'
        have h0 : @Eq Int (lo.lookup V) 0 := Option.some.inj (hκ _ lo hz)
        have hlo : @Eq Int (lo.lookup V) (((σ lo).lookup W : BitVec 64).toNat) := hag _ lo
        have hi : (i.lookup V : BitVec 64) = (σ i).lookup W := hag _ i
        have hz' : @Eq (BitVec 64) ((σ lo).lookup W) 0 := by
          have h1 : (((σ lo).lookup W : BitVec 64).toNat : Int) = 0 := by rw [← hlo, h0]
          apply BitVec.eq_of_toNat_eq
          have : (0 : BitVec 64).toNat = 0 := rfl
          omega
        change @Eq Int ((show Int from lo.lookup V) +
            (((show BitVec 64 from i.lookup V)).toNat : Int))
          (((show BitVec 64 from (σ lo).lookup W) + (show BitVec 64 from (σ i).lookup W)).toNat :
            Int)
        simp [hz', h0, hi]
      · cases h
  | trip t =>
      intro args e y h hy
      rcases args with _ | ⟨lo, _ | ⟨hi, _ | _⟩⟩
      change (if κ lo then
        (asWord t (σ hi)).map (fun h =>
          (⟨.bvAdd 64, rfl, .cons (σ lo) (.cons h .nil)⟩ :
            Expr catCryptDialect Δ (catTy (.word 64))))
        else none) = some e at h
      split at h
      · rename_i hz
        obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
        have h0 : @Eq Int (lo.lookup V) 0 := Option.some.inj (hκ _ lo hz)
        have hlo : @Eq Int (lo.lookup V) (((σ lo).lookup W : BitVec 64).toNat) := hag _ lo
        have hz' : @Eq (BitVec 64) ((σ lo).lookup W) 0 := by
          have h1 : (((σ lo).lookup W : BitVec 64).toNat : Int) = 0 := by rw [← hlo, h0]
          apply BitVec.eq_of_toNat_eq
          have : (0 : BitVec 64).toNat = 0 := rfl
          omega
        have he := asWord_enc hw W (hag _ hi)
        change ((NfTy.toInt? t (hi.lookup V)).map fun hh =>
          BitVec.ofNat 64 (hh - (show Int from lo.lookup V)).toNat) = some y at hy
        have ht : NfTy.toInt? t (hi.lookup V) = some ((w.lookup W).toNat : Int) := by
          unfold asWord at hw
          split at hw
          · rename_i hwt
            cases t with
            | int =>
                change _root_.Hax.Value.int _ = _root_.Hax.Value.int _ at he
                exact congrArg some (_root_.Hax.Value.int.inj he)
            | word n =>
                have hn : n = 64 := by
                  by_contra hne
                  simp [ImpToNF.hax64NFWordTy, hne] at hwt
                subst hn
                change _root_.Hax.Value.int _ = _root_.Hax.Value.int _ at he
                exact congrArg some (_root_.Hax.Value.int.inj he)
            | _ => simp [ImpToNF.hax64NFWordTy] at hwt
          · cases hw
        rw [ht, Option.map_some] at hy
        have hy' := Option.some.inj hy
        subst hy'
        change BitVec.ofNat 64 (((w.lookup W).toNat : Int) - lo.lookup V).toNat =
          (show BitVec 64 from (σ lo).lookup W) + w.lookup W
        simp [hz', h0]
        exact (BitVec.zero_add _).symm
      · cases h
  | _ =>
      intro args e y h hy
      cases h

/-! ## 6. Programs -/

/-- **The translation of a program** of the fragment through the renaming `σ`, with the
    readings `κ` of the literal zeros: a return to the return of the renamed variables, a
    binding to the binding of `catOp?`, and a counted loop to the counted loop of the
    translated body and continuation; `none` on a branch and an exit-flag loop. -/
def nfToCat : {Γ : Ctxt nfDialect} → {Δ : Ctxt catCryptDialect} → {ts : List NfTy} →
    NFProg nfDialect Γ ts → TRen Γ Δ → ZeroRd Γ →
      Option (NFProg catCryptDialect Δ (ts.map catTy))
  | _, _, _, .ret vs, σ, _ => some (.ret (σ.vars vs))
  | _, _, _, .var ⟨op, h, args⟩ k, σ, κ =>
      (catOp? σ κ op args).bind fun e' =>
        (nfToCat k (TRen.lift σ) (ZeroRd.cons (zeroLit op) κ)).map fun k' =>
          .var ⟨e'.op, e'.retTy_eq.trans (congrArg catTy h), e'.args⟩ k'
  | _, _, _, .forLoop (cs := cs) count inits body k, σ, κ =>
      (nfToCat body (TRen.liftApp cs (TRen.lift σ)) (ZeroRd.app cs (ZeroRd.cons false κ))).bind
        fun body' => (nfToCat k (TRen.liftApp cs σ) (ZeroRd.app cs κ)).map fun k' =>
          .forLoop (cs := cs.map catTy) (σ count) (σ.vars inits) body' k'
  | _, _, _, .ifThenElse .., _, _ => none
  | _, _, _, .whileLoop .., _, _ => none

/-- An operation that binds the literal zero denotes `0`. -/
theorem zeroLit_sound {T : NfLeafTable} :
    ∀ (op : NfOp) (xs : HVector NfTy.denote op.sig) (y : op.ret.denote),
      zeroLit op = true → nfDenoteOp T op xs = some y →
      NfTy.toInt? op.ret y = some 0
  | .named _ op, xs, y, hz, hy => zeroLit_sound op xs y hz hy
  | .ilit t v, _, y, hz, hy => by
      cases t with
      | int =>
          have hv : v = 0 := by
            by_contra hne
            simp [zeroLit, hne] at hz
          subst hv
          change some (0 : Int) = some y at hy
          cases hy
          rfl
      | _ => simp [zeroLit] at hz
  | .call .., _, _, hz, _ | .const .., _, _, hz, _ | .bin .., _, _, hz, _
  | .un .., _, _, hz, _ | .cast .., _, _, hz, _ | .scast .., _, _, hz, _
  | .cmp .., _, _, hz, _ | .andB, _, _, hz, _ | .orB, _, _, hz, _ | .xorB, _, _, hz, _
  | .eqB, _, _, hz, _ | .notB, _, _, hz, _ | .index .., _, _, hz, _
  | .update .., _, _, hz, _ | .arrLit .., _, _, hz, _ | .arrRepeat .., _, _, hz, _
  | .mkPair .., _, _, hz, _ | .fst .., _, _, hz, _ | .snd .., _, _, hz, _
  | .ctr, _, _, hz, _ | .trip _, _, _, hz, _ | .tnilV, _, _, hz, _ | .tconsV .., _, _, hz, _
  | .thead .., _, _, hz, _ | .ttail .., _, _, hz, _ | .constBit _, _, _, hz, _
  | .constUnit, _, _, hz, _ => by simp [zeroLit] at hz

/-- The readings of the literal zeros extended by the reading of a new binding hold of the
    extended valuation. -/
theorem ZeroRd.ok_cons {Γ : Ctxt nfDialect} {κ : ZeroRd Γ} {V : Valuation Γ} (h : κ.Ok V)
    {T : NfLeafTable} (op : NfOp) (xs : HVector NfTy.denote op.sig) {y : op.ret.denote}
    (hy : nfDenoteOp T op xs = some y) :
    ZeroRd.Ok (ZeroRd.cons (s := op.ret) (zeroLit op) κ) (V.extend y) := by
  intro t v hv
  cases v with
  | here => exact zeroLit_sound op xs y hv hy
  | there v => exact h _ v hv

/-- The readings of the literal zeros under bindings that are not literal zeros hold of the
    extended valuation. -/
theorem ZeroRd.ok_app {Γ : Ctxt nfDialect} {κ : ZeroRd Γ} {V : Valuation Γ} (h : κ.Ok V) :
    ∀ (cs : List NfTy) (A : Valuation (d := nfDialect) cs),
      ZeroRd.Ok (ZeroRd.app cs κ) (hvAppend A V)
  | [], .nil => h
  | c :: cs, .cons a A => by
      intro t v hv
      have key : ∀ (v : Var (d := nfDialect) (c :: (cs ++ Γ)) t),
          ZeroRd.cons (s := c) false (ZeroRd.app cs κ) v = true →
          NfTy.toInt? t (v.lookup (Valuation.extend (hvAppend A V) a)) = some 0 := by
        intro v hv
        cases v with
        | here => cases hv
        | there v => exact ZeroRd.ok_app h cs A _ v hv
      exact key v hv

/-- The readings of the literal zeros under a binding that is not a literal zero hold of the
    extended valuation. -/
theorem ZeroRd.ok_cons_false {Γ : Ctxt nfDialect} {κ : ZeroRd Γ} {V : Valuation Γ}
    (h : κ.Ok V) {s : NfTy} (x : s.denote) :
    ZeroRd.Ok (ZeroRd.cons (s := s) false κ) (V.extend x) := by
  intro t v hv
  cases v with
  | here => cases hv
  | there v => exact h _ v hv

/-- **The simulation statement of the translation** of the program `p`: a denotation of `p`
    to `out` from a valuation related to `W` by the renaming, with readings of the literal
    zeros that hold, is matched, at every fuel, by a denotation of the translated program
    from `W` to a related vector. -/
def NFSound (bi : _root_.Hax.Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRen Γ Δ) (κ : ZeroRd Γ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCat p σ κ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (out : Valuation (d := nfDialect) ts),
    σ.Agree V W → κ.Ok V → ImpToNF.PDenP bi tf p V = some out →
    ∀ fuel, ∃ out', p'.denote fuel W = some out' ∧ VRelL ts out out'

/-- **The translation simulates the denotation.** -/
theorem nfToCat_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (tf : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : NFSound bi tf p := by
  induction p with
  | ret vs =>
      intro Δ σ κ p' h V W out hag _ hp fuel
      change some (NFProg.ret (σ.vars vs)) = some p' at h
      cases h
      change some (Expr.lookupArgs vs V) = some out at hp
      cases hp
      exact ⟨_, rfl, TRen.vrelL_vars hag vs⟩
  | var e k ih =>
      intro Δ σ κ p' h V W out hag hκ hp fuel
      obtain ⟨op, rfl, args⟩ := e
      change (catOp? σ κ op args).bind (fun e' =>
        (nfToCat k (TRen.lift σ) (ZeroRd.cons (zeroLit op) κ)).map fun k' =>
          NFProg.var ⟨e'.op, e'.retTy_eq.trans (congrArg catTy rfl), e'.args⟩ k') =
        some p' at h
      obtain ⟨e', he', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      change (nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => ImpToNF.PDenP bi tf k (V.extend x)) = some out at hp
      obtain ⟨y, hy, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hrel := catOp_sound hbi σ κ hag hκ op args e' y he' hy
      obtain ⟨out', hden, hR⟩ := ih (TRen.lift σ) _ k' hk' (V.extend y) (W.extend (e'.denote W))
        out (TRen.agree_lift hag hrel) (ZeroRd.ok_cons hκ op _ hy) hp fuel
      refine ⟨out', ?_, hR⟩
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
      exact hden
  | @forLoop Γ₀ cs ts₀ count inits body k ihb ihk =>
      intro Δ σ κ p' h V W out hag hκ hp fuel
      change (nfToCat body (TRen.liftApp cs (TRen.lift σ))
          (ZeroRd.app cs (ZeroRd.cons false κ))).bind
        (fun body' => (nfToCat k (TRen.liftApp cs σ) (ZeroRd.app cs κ)).map fun k' =>
          NFProg.forLoop (cs := cs.map catTy) (σ count) (σ.vars inits) body' k') = some p' at h
      obtain ⟨body', hb', h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      change ((List.range (count.lookup V : BitVec 64).toNat).foldlM
          (fun acc j => ImpToNF.PDenP bi tf body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V)))
          (Expr.lookupArgs inits V)).bind (fun acc => ImpToNF.PDenP bi tf k (hvAppend acc V)) =
        some out at hp
      obtain ⟨accF, hfold, hkout⟩ := Option.bind_eq_some_iff.mp hp
      have hcnt : (count.lookup V : BitVec 64) = (σ count).lookup W := hag _ count
      have key : ∀ (l : List Nat) (acc : Valuation (d := nfDialect) cs)
          (acc' : Valuation (d := catCryptDialect) (cs.map catTy))
          (accF : Valuation (d := nfDialect) cs), VRelL cs acc acc' →
          l.foldlM (fun acc j => ImpToNF.PDenP bi tf body
            (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V))) acc =
            some accF →
          ∃ accF', l.foldlM (fun acc j => body'.denote fuel
            (hvAppend acc (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 j) W))) acc' =
            some accF' ∧ VRelL cs accF accF' := by
        intro l
        induction l with
        | nil =>
            intro acc acc' accF hr h
            simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
            subst h
            exact ⟨acc', rfl, hr⟩
        | cons j l ih =>
            intro acc acc' accF hr h
            rw [List.foldlM_cons] at h
            obtain ⟨a1, ha1, h⟩ := Option.bind_eq_some_iff.mp h
            have hag1 := TRen.agree_liftApp
              (TRen.agree_lift (s := NfTy.word 64) hag (x := BitVec.ofNat 64 j)
                (y := BitVec.ofNat 64 j) rfl) cs acc acc' hr
            obtain ⟨a1', ha1', hr1⟩ := ihb (TRen.liftApp cs (TRen.lift σ)) _ body' hb' _ _ a1
              hag1 (ZeroRd.ok_app (ZeroRd.ok_cons_false hκ _) cs acc) ha1 fuel
            obtain ⟨accF', hf', hrF⟩ := ih a1 a1' accF hr1 h
            refine ⟨accF', ?_, hrF⟩
            have ha1'' : NFProg.denote fuel body'
                (hvAppend acc' (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 j) W)) =
                some a1' := ha1'
            rw [List.foldlM_cons, ha1'']
            exact hf'
      rw [List.range_eq_range'] at hfold
      obtain ⟨accF', hfold', hrF⟩ := key _ _ _ accF (TRen.vrelL_vars hag inits) hfold
      obtain ⟨out', hden, hR⟩ := ihk (TRen.liftApp cs σ) _ k' hk' (hvAppend accF V)
        (hvAppend accF' W) out (TRen.agree_liftApp hag cs accF accF' hrF)
        (ZeroRd.ok_app hκ cs accF) hkout fuel
      refine ⟨out', ?_, hR⟩
      rw [NFProg.denote_forLoop]
      have hc2 : HasWord64.toNat (d := catCryptDialect) ((σ count).lookup W) =
          (count.lookup V : BitVec 64).toNat := by
        rw [← hcnt]; rfl
      rw [hc2, List.range_eq_range']
      erw [hfold']
      exact hden
  | ifThenElse cond thn els k _ _ _ =>
      intro Δ σ κ p' h
      cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ κ p' h
      cases h

/-! ## 7. The entry -/

/-- The value of the target type a value of the fragment maps to: a word to itself, an
    integer to the word of its natural number, an integer array element by element. -/
def toCatVal : (t : NfTy) → t.denote → (catTy t).denote
  | .word _, x => x
  | .int, z => BitVec.ofNat 64 z.toNat
  | .arr _ .int, f => fun k => BitVec.ofNat 64 (f k).toNat
  | .arr _ _, _ => fun _ => 0
  | .bit, b => b
  | .unit, _ => ()
  | .pair _ _, _ => ()
  | .uint _, _ => ()
  | .sint _, _ => ()
  | .tnil, _ => ()
  | .tcons _ _, _ => ()
  | .slice _, _ => ()

/-- A value of the fragment whose integers are in `[0, 2^64)`. -/
def InRange : (t : NfTy) → t.denote → Prop
  | .word _, _ => True
  | .int, z => 0 ≤ z ∧ z < 2 ^ 64
  | .arr _ .int, f => ∀ k, 0 ≤ f k ∧ f k < 2 ^ 64
  | .bit, _ => True
  | .unit, _ => True
  | _, _ => False

/-- An integer in `[0, 2^64)` is the natural number of the `64`-bit word of its natural
    number. -/
theorem int_eq_ofNat_toNat {z : Int} (h0 : 0 ≤ z) (h1 : z < 2 ^ 64) :
    z = ((BitVec.ofNat 64 z.toNat).toNat : Int) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A value in range is related to the value it maps to. -/
theorem vrel_toCatVal : ∀ (t : NfTy) (x : t.denote), InRange t x → VRel t x (toCatVal t x)
  | .word _, _, _ => rfl
  | .int, _, ⟨h0, h1⟩ => int_eq_ofNat_toNat h0 h1
  | .arr _ .int, _, h => fun k => int_eq_ofNat_toNat (h k).1 (h k).2
  | .bit, _, _ => rfl
  | .unit, _, _ => trivial
  | .arr _ .bit, _, h | .arr _ .unit, _, h | .arr _ (.word _), _, h | .arr _ (.arr _ _), _, h
  | .arr _ (.pair _ _), _, h | .arr _ (.uint _), _, h | .arr _ (.sint _), _, h
  | .arr _ .tnil, _, h | .arr _ (.tcons _ _), _, h | .arr _ (.slice _), _, h
  | .pair _ _, _, h | .uint _, _, h | .sint _, _, h | .tnil, _, h | .tcons _ _, _, h
  | .slice _, _, h => h.elim

/-- The renaming of a context to its mapped context. -/
def TRen.id : {Γ : Ctxt nfDialect} → TRen Γ (Γ.map catTy)
  | _ :: _, _, .here => .here
  | _ :: _, _, .there v => .there (TRen.id v)

/-- A valuation mapped value by value. -/
def mapVal : {Γ : Ctxt nfDialect} → Valuation Γ → Valuation (d := catCryptDialect) (Γ.map catTy)
  | [], .nil => .nil
  | t :: _, .cons x V => .cons (toCatVal t x) (mapVal V)

/-- The renaming of a context to its mapped context relates a valuation in range to its
    mapped valuation. -/
theorem TRen.agree_id : ∀ {Γ : Ctxt nfDialect} (V : Valuation Γ),
    (∀ (t : NfTy) (v : Var Γ t), InRange t (v.lookup V)) → TRen.Agree TRen.id V (mapVal V)
  | [], .nil, _ => fun _ v => nomatch v
  | s :: Γ, .cons x V, h => by
      intro t v
      cases v with
      | here => exact vrel_toCatVal s x (h s .here)
      | there v => exact TRen.agree_id V (fun t v => h t v.there) t v

/-- The readings of no literal zero. -/
def ZeroRd.none {Γ : Ctxt nfDialect} : ZeroRd Γ := fun _ => false

theorem ZeroRd.ok_none {Γ : Ctxt nfDialect} (V : Valuation Γ) : ZeroRd.none.Ok V :=
  fun _ _ h => by cases h

/-- The type of a parameter of a System V layout: a scalar is a `64`-bit word, an array of
    `n` words an integer array of `n` elements. -/
def abiKindArr : SecureCompilation.Haxc.ArgKind → NfTy
  | .scalar => .word 64
  | .words n => .arr n .int

/-- The parameters of a System V layout with their types. -/
def abiParamsArr (σ : SecureCompilation.Haxc.AbiLayout) : List (String × NfTy) :=
  σ.args.map fun a => (a.name, abiKindArr a.kind)

/-- The value a parameter reads off an entry state encodes a value of its type, in range. -/
theorem abiArg_read_enc (a : SecureCompilation.Haxc.AbiArg)
    (sa : SecureCompilation.Ascent.AddrMem.AState) :
    ∃ y : (abiKindArr a.kind).denote, a.read sa = ImpToNF.enc (abiKindArr a.kind) y ∧
      InRange (abiKindArr a.kind) y := by
  obtain ⟨name, reg, kind⟩ := a
  cases kind with
  | scalar => exact ⟨sa.regs reg, rfl, trivial⟩
  | words n =>
      refine ⟨fun k => ((SecureCompilation.Ascent.AddrMem.read64 sa.mem
        (sa.regs reg + BitVec.ofNat 64 (8 * k.1))).toNat : Int), ?_, fun k => ?_⟩
      · simp only [SecureCompilation.Haxc.AbiArg.read, SecureCompilation.Haxc.wordsAt, abiKindArr,
          ImpToNF.enc]
        congr 1
        apply List.ext_getElem <;> simp
      · dsimp only
        exact ⟨Int.natCast_nonneg _, show ((_ : Nat) : Int) < 2 ^ 64 by exact_mod_cast BitVec.isLt _⟩

/-- An encoding is determined by the value it encodes, at an integer array type and at a word
    type. -/
theorem enc_inj_abi {k : SecureCompilation.Haxc.ArgKind} {y y' : (abiKindArr k).denote}
    (h : ImpToNF.enc (abiKindArr k) y = ImpToNF.enc (abiKindArr k) y') : y = y' := by
  cases k with
  | scalar =>
      change _root_.Hax.Value.int _ = _root_.Hax.Value.int _ at h
      exact BitVec.eq_of_toNat_eq (by exact_mod_cast _root_.Hax.Value.int.inj h)
  | words n =>
      change _root_.Hax.Value.array _ = _root_.Hax.Value.array _ at h
      have h' := _root_.Hax.Value.array.inj h
      funext i
      have := congrArg (fun l : List _root_.Hax.Value => l[i.1]?) h'
      simp only [List.getElem?_ofFn, i.2, dif_pos, Option.some.injEq] at this
      exact _root_.Hax.Value.int.inj this

/-- **The entry valuation is in range.** A valuation whose encodings a source environment the
    layout reads off an entry state holds at the parameters of the layout has its integers in
    `[0, 2^64)`. -/
theorem inRange_of_envOf {sa : SecureCompilation.Ascent.AddrMem.AState} {env : _root_.Hax.Env} :
    ∀ (as : List SecureCompilation.Haxc.AbiArg), (∀ a ∈ as, env a.name = some (a.read sa)) →
      ∀ (V : Valuation (ImpToNF.entryCtx (as.map fun a => (a.name, abiKindArr a.kind)))),
      ImpToNF.EntryVals env (as.map fun a => (a.name, abiKindArr a.kind)) V →
      ∀ (t : NfTy) (v : Var (ImpToNF.entryCtx (as.map fun a => (a.name, abiKindArr a.kind))) t),
        InRange t (v.lookup V)
  | [], _, .nil, _, _, v => nomatch v
  | a :: as, h, .cons y V, ⟨hy, hV⟩, t, v => by
      cases v with
      | here =>
          obtain ⟨y', hr, hin⟩ := abiArg_read_enc a sa
          rw [h a List.mem_cons_self, hr] at hy
          have := enc_inj_abi (Option.some.inj hy)
          subst this
          exact hin
      | there v =>
          exact inRange_of_envOf as (fun a' ha => h a' (List.mem_cons_of_mem _ ha)) V hV t v

/-- A source environment a System V layout reads off an entry state is typed at the
    parameters `abiParamsArr σ`. -/
theorem entryTyped_of_envOf_arr {σ : SecureCompilation.Haxc.AbiLayout}
    {sa : SecureCompilation.Ascent.AddrMem.AState} {env : _root_.Hax.Env} (h : σ.EnvOf sa env) :
    ImpToNF.EntryTyped env (abiParamsArr σ) := by
  intro x t hm
  simp only [abiParamsArr, List.mem_map, Prod.mk.injEq] at hm
  obtain ⟨a, ha, rfl, rfl⟩ := hm
  obtain ⟨y, hr, -⟩ := abiArg_read_enc a sa
  exact ⟨y, by rw [h.1 a ha, hr]⟩

end CatCrypt.Crypto.Hax.NFToCat
