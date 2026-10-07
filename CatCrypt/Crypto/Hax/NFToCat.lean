/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpToNF
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgToComL
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel
public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout

/-!
# The `u64` fragment of `NFProg nfDialect` in `catCryptDialect`

`nfToCat` translates a program of `NFProg nfDialect` over the `u64` table into a program of
`NFProg catCryptDialect`, which `NFProgCatToJasmin.nfToComLVia` lowers to `ComL`. The types
map by `catTy`: a `64`-bit word and an integer to `sword 64`, an array of `n` elements to
`memref n`. A value of the source and a value of the target are related by `VRel`: an integer
is the natural number of the word, an array element by element. Each variable of the source
has a reading `Rd`: a variable of the target, or a literal in `[0, 2^64)`. A literal has no
target binding; an operation that reads one binds it by `bvConst` immediately before itself,
so that a literal used in a loop body is bound inside the body.

The operations of the fragment are the scalar calls of `hax64NFScalar`, `index` and
`array_update` on arrays of `64`-bit words, integer literals in `[0, 2^64)` and the loop operations
`ctr` and `trip`. A shift `Shr#64` or `Shl#64` by a literal below `64` is the shift by an
immediate. Every scalar is a `64`-bit word of the target: a call of the scalar table at a
width below `64` computes on `64`-bit words and reduces modulo `2 ^ w` by a mask, and a
comparison is a bit (`scalarRes?`); such a translation is a sequence of bindings
(`OpRes.bind`). A counted loop is translated when its lower bound reads as the literal `0`;
`ctr 0 i` is then the reading of `i`, and `trip 0 hi` the reading of `hi`, or the binding of
the literal `hi`.

## Main definitions

* `catTy`, `VRel`, `VRelL` — the type map and the relation of values.
* `Rd`, `RdRel`, `TRd`, `TRd.lift`, `TRd.liftApp`, `TRd.Agree` — readings, their relation to
  source values, and the readings of a context.
* `scalarRes?`, `binChain`, `rotChain`, `unChain`, `cmpChain` — the translation of the
  scalar table on `64`-bit words.
* `catCallRd`, `catOp`, `emitRes`, `nfToCat` — the translation of a call, of an operation,
  of the bindings of a translated operation and of a program.
* `toCatVal`, `mapVal`, `TRd.id`, `abiParamsArr` — the entry: the mapped valuation, the
  readings of a context in its mapped context, and the parameters of a System V layout with
  the types of arrays of `64`-bit words.

## Main results

* `scalarRes_sound` — a translated call of the scalar table is related to its value.
* `catOp_sound` — a translated operation is related to the value of the source operation.
* `emitRes_sound` — the bindings of a translated operation simulate.
* `nfToCat_sound` — a translated program denotes values related to the values of the source
  program, under every leaf table that agrees with the `u64` table at the translated calls
  (`SubTable`).
* `TRd.agree_id`, `inRange_of_envOf` — the entry valuation is in range and related to its
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
    words and bits, an integer equal to the natural number of the word, an array of words
    element by element, by the natural numbers of the elements. -/
def VRel : (t : NfTy) → t.denote → (catTy t).denote → Prop
  | .word _, x, y => x = y
  | .int, z, y => z = (y.toNat : Int)
  | .arr _ (.word _), f, g => ∀ i, (f i).toNat = (g i).toNat
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

/-- A variable of the type of an array of `64`-bit words, at the memref of its length. -/
def asArr {Δ : Ctxt catCryptDialect} : (t : NfTy) → Var Δ (catTy t) →
    Option (Σ n : Nat, Var Δ (.memref n))
  | .arr n (.word 64), v => some ⟨n, v⟩
  | _, _ => none

/-- A variable of the bit type, at `bit`. -/
def asBit {Δ : Ctxt catCryptDialect} : (t : NfTy) → Var Δ (catTy t) → Option (Var Δ .bit)
  | .bit, v => some v
  | _, _ => none

/-- The expression of the call `select` on a bit and two values of types whose values encode
    as integers: the select `ite` of `catCryptDialect` on two words. -/
def selectCat {Δ : Ctxt catCryptDialect} (f : String) (tc ta tb : NfTy)
    (args : HVector (fun t => Var Δ t) ([tc, ta, tb].map catTy)) :
    Option (Expr catCryptDialect Δ (.sword 64)) :=
  if f = "select" then
    (asBit tc args.head).bind fun c => (asWord ta args.tail.head).bind fun x =>
      (asWord tb args.tail.tail.head).map fun y =>
        ⟨.ite (.sword 64), rfl, .cons c (.cons x (.cons y .nil))⟩
  else none

/-- The expression of a call `f` of the `u64` table on the renamed arguments `args`: a scalar
    call of `hax64NFScalar`, `index` of an array of `64`-bit words, `array_update` of an
    array of `64`-bit words, `select` of two values of types whose values encode as
    integers. -/
def catCall? {Δ : Ctxt catCryptDialect} (f : String) :
    (as : List NfTy) → (r : NfTy) → HVector (fun t => Var Δ t) (as.map catTy) →
      Option (Expr catCryptDialect Δ (catTy r))
  | [ta, tb], .word 64, args =>
      if f = "index" then
        (asArr ta args.head).bind fun ⟨n, a⟩ => (asWord tb args.tail.head).map fun i =>
          ⟨.memrefGetDyn n, rfl, .cons a (.cons i .nil)⟩
      else
        (asWord ta args.head).bind fun x => (asWord tb args.tail.head).bind fun y =>
          scalarCatExpr f x y
  | [ta, ti, tv], .arr n' (.word 64), args =>
      if f = "array_update" then
        (asArr ta args.head).bind fun ⟨n, m⟩ =>
          if h : n = n' then
            (asWord ti args.tail.head).bind fun i' => (asWord tv args.tail.tail.head).map fun x' =>
              ⟨.memrefSetDyn n, congrArg CryptoTy.memref h, .cons m (.cons i' (.cons x' .nil))⟩
          else none
      else none
  | [tc, ta, tb], .word 64, args => selectCat f tc ta tb args
  | [tc, ta, tb], .int, args => selectCat f tc ta tb args
  | _, _, _ => none

/-! ## 4. Readings and the translation of an operation -/

/-- The reading of a variable of the fragment in the target program: a variable of the mapped
    type, or a literal of a type whose values encode as integers. A literal has no variable;
    it is materialised by a `bvConst` binding at the operation that reads it. -/
inductive Rd (Δ : Ctxt catCryptDialect) (t : NfTy) : Type where
  /-- A variable of the mapped type. -/
  | var (w : Var Δ (catTy t))
  /-- The literal `k`. -/
  | lit (k : Nat) (h : ImpToNF.hax64NFWordTy t = true)

/-- A reading under one more binding of the target. -/
def Rd.wk {Δ : Ctxt catCryptDialect} {c : CryptoTy} {t : NfTy} : Rd Δ t → Rd (c :: Δ) t
  | .var w => .var w.there
  | .lit k h => .lit k h

/-- The relation of a source value and a reading at the valuation `W` of the target: the
    relation `VRel` with the value of the variable, or the integer of the value is the
    literal, in `[0, 2^64)`. -/
def RdRel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (t : NfTy) (x : t.denote) :
    Rd Δ t → Prop
  | .var w => VRel t x (w.lookup W)
  | .lit k _ => NfTy.toInt? t x = some (k : Int) ∧ k < 2 ^ 64

/-- The relation of two vectors of source values and readings, component by component. -/
def RdRelL {Δ : Ctxt catCryptDialect} (W : Valuation Δ) : (ts : List NfTy) →
    Valuation (d := nfDialect) ts → HVector (fun t => Rd Δ t) ts → Prop
  | [], .nil, .nil => True
  | t :: ts, .cons x xs, .cons r rs => RdRel W t x r ∧ RdRelL W ts xs rs

/-- The readings of the variables of a context. -/
abbrev TRd (Γ : Ctxt nfDialect) (Δ : Ctxt catCryptDialect) : Type :=
  ∀ {t : NfTy}, Var Γ t → Rd Δ t

/-- The readings extended by the reading `r` of a new variable. -/
def TRd.cons {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy} (r : Rd Δ s)
    (σ : TRd Γ Δ) : TRd (s :: Γ) Δ
  | _, .here => r
  | _, .there v => σ v

/-- The readings under one more binding of the target. -/
def TRd.wk {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {c : CryptoTy} (σ : TRd Γ Δ) :
    TRd Γ (c :: Δ) :=
  fun v => (σ v).wk

/-- The readings under one more binding of the source and of the target. -/
def TRd.lift {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy} (σ : TRd Γ Δ) :
    TRd (s :: Γ) (catTy s :: Δ) :=
  TRd.cons (.var .here) σ.wk

/-- The readings under the bindings `cs`. -/
def TRd.liftApp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} :
    (cs : List NfTy) → TRd Γ Δ → TRd (cs ++ Γ) (cs.map catTy ++ Δ)
  | [], σ => σ
  | _ :: cs, σ => TRd.lift (TRd.liftApp cs σ)

/-- The readings of a vector of variables. -/
def TRd.rds {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    {ts : List NfTy} → HVector (fun t => Var Γ t) ts → HVector (fun t => Rd Δ t) ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (σ v) (σ.rds vs)

/-- The readings `σ` relate the valuations `V` and `W`. -/
def TRd.Agree {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (V : Valuation Γ) (W : Valuation Δ) : Prop :=
  ∀ (t : NfTy) (v : Var Γ t), RdRel W t (v.lookup V) (σ v)

/-- The variables of a vector of readings, when none is a literal. -/
def pinVars {Δ : Ctxt catCryptDialect} : {ts : List NfTy} → HVector (fun t => Rd Δ t) ts →
    Option (HVector (fun t => Var Δ t) (ts.map catTy))
  | [], .nil => some .nil
  | _ :: _, .cons r rs =>
      match r with
      | .var w => (pinVars rs).map (.cons w)
      | .lit _ _ => none

/-- The variable of a literal: the new binding of `sword 64`, at the mapped type of a type
    whose values encode as integers. -/
def litVar {Δ : Ctxt catCryptDialect} {t : NfTy} (h : ImpToNF.hax64NFWordTy t = true) :
    Var (CryptoTy.sword 64 :: Δ) (catTy t) :=
  (catTy_of_wordTy h).symm ▸ (Var.here : Var (d := catCryptDialect) (CryptoTy.sword 64 :: Δ)
    (.sword 64))

/-- The variables of a vector of readings under a binding of the literal `k`: the variables
    weakened, and every literal, which must be `k`, the new binding. -/
def pinLit {Δ : Ctxt catCryptDialect} (k : Nat) : {ts : List NfTy} →
    HVector (fun t => Rd Δ t) ts →
    Option (HVector (fun t => Var (d := catCryptDialect) (CryptoTy.sword 64 :: Δ) t)
      (ts.map catTy))
  | [], .nil => some .nil
  | _ :: _, .cons r rs =>
      match r with
      | .var w => (pinLit k rs).map (.cons w.there)
      | .lit k' h => if k' = k then (pinLit k rs).map (.cons (litVar h)) else none

/-- The first literal of a vector of readings. -/
def firstLit {Δ : Ctxt catCryptDialect} : {ts : List NfTy} → HVector (fun t => Rd Δ t) ts →
    Option Nat
  | [], .nil => none
  | _ :: _, .cons r rs =>
      match r with
      | .lit k _ => some k
      | .var _ => firstLit rs

/-- A shift `Shr#64` or `Shl#64` of a variable by a literal below `64`, as the shift by an
    immediate. -/
def shiftImm? {Δ : Ctxt catCryptDialect} (f : String) :
    (as : List NfTy) → (r : NfTy) → HVector (fun t => Rd Δ t) as →
      Option (Expr catCryptDialect Δ (catTy r))
  | [ta, _], .word 64, rs =>
      match rs.head, rs.tail.head with
      | .var a, .lit k _ =>
          if k < 64 then
            (asWord ta a).bind fun x =>
              if f = "Shr#64" then some ⟨.bvShiftR 64 k, rfl, .cons x .nil⟩
              else if f = "Shl#64" then some ⟨.bvShiftL 64 k, rfl, .cons x .nil⟩
              else none
          else none
      | _, _ => none
  | _, _, _ => none

/-- The translation of an operation: a new reading (`rd`), an expression on the target
    variables (`expr`), an expression under a binding of the literal `k` (`expr1`), or a
    binding of an intermediate value followed by the translation in the extended context
    (`bind`). -/
inductive OpRes : Ctxt catCryptDialect → NfTy → Type where
  /-- The value is read by `r`; no binding. -/
  | rd {Δ : Ctxt catCryptDialect} {t : NfTy} (r : Rd Δ t) : OpRes Δ t
  /-- The value is bound by `e`. -/
  | expr {Δ : Ctxt catCryptDialect} {t : NfTy} (e : Expr catCryptDialect Δ (catTy t)) :
      OpRes Δ t
  /-- The literal `k` is bound, and then the value by `e`. -/
  | expr1 {Δ : Ctxt catCryptDialect} {t : NfTy} (k : Nat)
      (e : Expr catCryptDialect (CryptoTy.sword 64 :: Δ) (catTy t)) : OpRes Δ t
  /-- The intermediate value `e` of type `c` is bound, and then the translation `k`. -/
  | bind {Δ : Ctxt catCryptDialect} {t : NfTy} (c : CryptoTy) (e : Expr catCryptDialect Δ c)
      (k : OpRes (c :: Δ) t) : OpRes Δ t

/-- The translation of a call of `catCall?` on readings: `catCall?` on the variables when no
    reading is a literal; a shift by a literal as the shift by an immediate; otherwise
    `catCall?` under one binding of the literal, which every literal reading must be. -/
def catCallRd0 {Δ : Ctxt catCryptDialect} (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) : Option (OpRes Δ r) :=
  match pinVars rs with
  | some ws => (catCall? f as r ws).map OpRes.expr
  | none =>
      match shiftImm? f as r rs with
      | some e => some (.expr e)
      | none =>
          (firstLit rs).bind fun k =>
            (pinLit k rs).bind fun ws => (catCall? f as r ws).map (OpRes.expr1 k)

/-- A reading of a `64`-bit word as a reading of an integer. -/
def Rd.ofWord {Δ : Ctxt catCryptDialect} : Rd Δ (.word 64) → Rd Δ .int
  | .var w => .var w
  | .lit k _ => .lit k rfl

/-- A reading of a type whose values encode as integers as a reading of a `64`-bit word. -/
def Rd.toWord64 {Δ : Ctxt catCryptDialect} (t : NfTy) : Rd Δ t → Option (Rd Δ (.word 64))
  | .var w => (asWord t w).map .var
  | .lit k _ => some (.lit k rfl)

/-! ### The scalar table on `64`-bit words

Every scalar of the fragment is a `64`-bit word of the target. An operation of the scalar
table at a width `w` below `64` computes on `64`-bit words and reduces the result modulo
`2 ^ w` by a conjunction with the mask `maskW w`; a logical right shift and a rotation reduce
their operand first. A rotation is by a literal amount, as two immediate shifts. A complement
is the exclusive or with the all-ones word or with the mask. A comparison is `bvEq` on two
words, or the carry of `x + ~~~y + c`, which is `1` exactly when `y ≤ x` at `c = 1` and when
`y < x` at `c = 0`: the sum (`bvAddCarryLo`) and its carry (`bvAddCarryHi`) are bound one
after the other on the same operands, and the bit is the equality of the carry with `1`. -/

/-- The mask of the low `w` bits of a `64`-bit word. -/
def maskW (w : Nat) : BitVec 64 := BitVec.ofNat 64 (2 ^ w - 1)

/-- The constant `v`. -/
def cstE {Δ : Ctxt catCryptDialect} (v : BitVec 64) : Expr catCryptDialect Δ (.sword 64) :=
  ⟨.bvConst 64 v, rfl, .nil⟩

/-- The conjunction of two words. -/
def andE {Δ : Ctxt catCryptDialect} (a b : Var Δ (.sword 64)) :
    Expr catCryptDialect Δ (.sword 64) :=
  ⟨.bvAnd 64, rfl, .cons a (.cons b .nil)⟩

/-- The expression of a binary operation of the scalar table on two words, before the
    reduction modulo `2 ^ w`; `none` for a rotation. -/
def binE {Δ : Ctxt catCryptDialect} :
    ImpToNF.ScalarBin → Var Δ (.sword 64) → Var Δ (.sword 64) →
      Option (Expr catCryptDialect Δ (.sword 64))
  | .add, a, b => some ⟨.bvAdd 64, rfl, .cons a (.cons b .nil)⟩
  | .sub, a, b => some ⟨.bvSub 64, rfl, .cons a (.cons b .nil)⟩
  | .mul, a, b => some ⟨.bvMul 64, rfl, .cons a (.cons b .nil)⟩
  | .and, a, b => some ⟨.bvAnd 64, rfl, .cons a (.cons b .nil)⟩
  | .or, a, b => some ⟨.bvOr 64, rfl, .cons a (.cons b .nil)⟩
  | .xor, a, b => some ⟨.bvXor 64, rfl, .cons a (.cons b .nil)⟩
  | .shl, a, b => some ⟨.bvShiftLV 64, rfl, .cons a (.cons b .nil)⟩
  | .shr, a, b => some ⟨.bvShiftRV 64, rfl, .cons a (.cons b .nil)⟩
  | .mulhi, a, b => some ⟨.bvMulHi 64, rfl, .cons a (.cons b .nil)⟩
  | .addc, a, b => some ⟨.bvAdd 64, rfl, .cons a (.cons b .nil)⟩
  | .subc, a, b => some ⟨.bvSub 64, rfl, .cons a (.cons b .nil)⟩
  | .rotr, _, _ => none
  | .rotl, _, _ => none

/-- The word `binE` computes. -/
def binBV : ImpToNF.ScalarBin → BitVec 64 → BitVec 64 → BitVec 64
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .and, x, y => x &&& y
  | .or, x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat
  | .mulhi, x, y => mulHiC x y
  | .addc, x, y => x + y
  | .subc, x, y => x - y
  | .rotr, _, _ => 0
  | .rotl, _, _ => 0

/-- The value `e` reduced modulo `2 ^ w`: `e` at `w = 64`, otherwise `e`, the mask and their
    conjunction. -/
def maskRes {Δ : Ctxt catCryptDialect} (w : Nat) (e : Expr catCryptDialect Δ (.sword 64)) :
    OpRes Δ (.word 64) :=
  if w = 64 then .expr e
  else .bind _ e (.bind _ (cstE (maskW w)) (.expr (andE (Var.there .here) .here)))

/-- The translation of a binary operation of the scalar table at the width `w` on two words:
    a logical right shift below `64` bits reduces its operand and shifts; every other
    operation is `binE` reduced by `maskRes`. -/
def binChain {Δ : Ctxt catCryptDialect} (o : ImpToNF.ScalarBin) (w : Nat)
    (a b : Var Δ (.sword 64)) : Option (OpRes Δ (.word 64)) :=
  if o = .shr ∧ w ≠ 64 then
    some (.bind _ (cstE (maskW w)) (.bind _ (andE a.there .here)
      (.expr ⟨.bvShiftRV 64, rfl, .cons .here (.cons b.there.there .nil)⟩)))
  else (binE o a b).map (maskRes w)

/-- The translation of a rotation of the scalar table at the width `w` by the literal amount
    `k`: the operand reduced modulo `2 ^ w`, shifted right and left by immediates, the
    disjunction, reduced modulo `2 ^ w`. -/
def rotChain {Δ : Ctxt catCryptDialect} (right : Bool) (w k : Nat) (a : Var Δ (.sword 64)) :
    OpRes Δ (.word 64) :=
  let j := k % w
  .bind _ (cstE (maskW w)) (.bind _ (andE a.there .here)
    (.bind _ (if right then ⟨.bvShiftR 64 j, rfl, .cons .here .nil⟩
        else ⟨.bvShiftL 64 j, rfl, .cons .here .nil⟩)
      (.bind _ (if right then ⟨.bvShiftL 64 (w - j), rfl, .cons (Var.there .here) .nil⟩
          else ⟨.bvShiftR 64 (w - j), rfl, .cons (Var.there .here) .nil⟩)
        (.bind _ ⟨.bvOr 64, rfl, .cons (Var.there .here) (.cons .here .nil)⟩
          (.expr (andE .here (Var.there (Var.there (Var.there (Var.there .here))))))))))

/-- The complement of a word reduced modulo `2 ^ w`: at `w = 64` the exclusive or with the
    all-ones word; otherwise the mask, the exclusive or with it and the conjunction with it. -/
def notChain {Δ : Ctxt catCryptDialect} (w : Nat) (a : Var Δ (.sword 64)) :
    OpRes Δ (.word 64) :=
  if w = 64 then
    .bind _ (cstE (BitVec.allOnes 64))
      (.expr ⟨.bvXor 64, rfl, .cons a.there (.cons .here .nil)⟩)
  else
    .bind _ (cstE (maskW w))
      (.bind _ ⟨.bvXor 64, rfl, .cons a.there (.cons .here .nil)⟩
        (.expr (andE .here (Var.there .here))))

/-- The translation of a unary operation of the scalar table at the width `w` on a word: the
    complement by `notChain`, the negation as `0 - x`, and the truncation as the conjunction
    with the mask. -/
def unChain {Δ : Ctxt catCryptDialect} (o : ImpToNF.ScalarUn) (w : Nat)
    (a : Var Δ (.sword 64)) : OpRes Δ (.word 64) :=
  match o with
  | .not => notChain w a
  | .neg => .bind _ (cstE 0) (.expr ⟨.bvSub 64, rfl, .cons .here (.cons a.there .nil)⟩)
  | .cast => .bind _ (cstE (maskW w)) (.expr (andE a.there .here))

/-- The bit of an ordering of two words: the complement of `y` as the exclusive or with the
    all-ones word, the carry-in `c`, the sum `x + ~~~y + c` and its carry as two adjacent
    bindings on the same operands, the constant `1`, and the equality of the carry with it.
    At the carry-in `1` the bit is `y ≤ x`, at the carry-in `0` it is `y < x`. -/
def geChain {Δ : Ctxt catCryptDialect} (c : BitVec 1) (x y : Var Δ (.sword 64)) :
    OpRes Δ .bit :=
  .bind _ (cstE (BitVec.allOnes 64))
    (.bind _ ⟨.bvXor 64, rfl, .cons y.there (.cons .here .nil)⟩
      (.bind (.sword 1) ⟨.bvConst 1 c, rfl, .nil⟩
        (.bind _ ⟨.bvAddCarryLo 64, rfl,
            .cons x.there.there.there (.cons (Var.there .here) (.cons .here .nil))⟩
          (.bind (.sword 1) ⟨.bvAddCarryHi 64, rfl,
              .cons x.there.there.there.there
                (.cons (Var.there (Var.there .here)) (.cons (Var.there .here) .nil))⟩
            (.bind (.sword 1) ⟨.bvConst 1 1, rfl, .nil⟩
              (.expr ⟨.bvEq 1, rfl, .cons (Var.there .here) (.cons .here .nil)⟩))))))

/-- The negation of the bit just bound, as the value of a comparison. -/
def notRes {Δ : Ctxt catCryptDialect} : OpRes (.bit :: Δ) .bit :=
  .expr ⟨.not, rfl, .cons .here .nil⟩

/-- The translation of a comparison of the scalar table on two words: `bvEq` and its
    negation, and the orderings by `geChain`. -/
def cmpChain {Δ : Ctxt catCryptDialect} (c : ImpToNF.ScalarCmp) (x y : Var Δ (.sword 64)) :
    OpRes Δ .bit :=
  match c with
  | .eq => .expr ⟨.bvEq 64, rfl, .cons x (.cons y .nil)⟩
  | .ne => .bind .bit ⟨.bvEq 64, rfl, .cons x (.cons y .nil)⟩ notRes
  | .ge => geChain 1 x y
  | .le => geChain 1 y x
  | .lt => geChain 0 y x
  | .gt => geChain 0 x y

/-- The word variable of a reading of a type whose values encode as integers, passed to `k`;
    a literal is bound by `bvConst` first. -/
def withVar1 {Δ : Ctxt catCryptDialect} {r : NfTy} (ta : NfTy) (ra : Rd Δ ta)
    (k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Option (OpRes Δ' r)) :
    Option (OpRes Δ r) :=
  match ra with
  | .var a => (asWord ta a).bind fun x => k x
  | .lit n _ => (k (Δ' := CryptoTy.sword 64 :: Δ) .here).map
      (.bind _ (cstE (BitVec.ofNat 64 n)))

/-- The word variables of two readings, passed to `k`; each literal is bound by `bvConst`
    first. -/
def withVar2 {Δ : Ctxt catCryptDialect} {r : NfTy} (ta tb : NfTy) (ra : Rd Δ ta)
    (rb : Rd Δ tb)
    (k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Var Δ' (.sword 64) →
      Option (OpRes Δ' r)) : Option (OpRes Δ r) :=
  match ra, rb with
  | .var a, .var b => (asWord ta a).bind fun x => (asWord tb b).bind fun y => k x y
  | .lit n _, .var b => (asWord tb b).bind fun y =>
      (k (Δ' := CryptoTy.sword 64 :: Δ) .here y.there).map
        (.bind _ (cstE (BitVec.ofNat 64 n)))
  | .var a, .lit n _ => (asWord ta a).bind fun x =>
      (k (Δ' := CryptoTy.sword 64 :: Δ) x.there .here).map
        (.bind _ (cstE (BitVec.ofNat 64 n)))
  | .lit n _, .lit m _ =>
      (k (Δ' := CryptoTy.sword 64 :: CryptoTy.sword 64 :: Δ) (Var.there .here) .here).map
        fun res => .bind _ (cstE (BitVec.ofNat 64 n)) (.bind _ (cstE (BitVec.ofNat 64 m)) res)

/-- The translation of a binary call of the scalar table on two readings, at the result type
    `r`: an integer call by `binChain`, a rotation by a literal amount by `rotChain`, a
    comparison by `cmpChain`. -/
def scalarRes2 {Δ : Ctxt catCryptDialect} (f : String) (ta tb : NfTy) (ra : Rd Δ ta)
    (rb : Rd Δ tb) : (r : NfTy) → Option (OpRes Δ r)
  | .word 64 =>
      (ImpToNF.scalarBinOf f).bind fun ⟨o, w⟩ =>
        if o = .rotr ∨ o = .rotl then
          match rb with
          | .lit k _ => withVar1 ta ra fun x => some (rotChain (o == .rotr) w k x)
          | .var _ => none
        else withVar2 ta tb ra rb fun x y => binChain o w x y
  | .bit =>
      (ImpToNF.scalarCmpOf f).bind fun c =>
        withVar2 ta tb ra rb fun x y => some (cmpChain c x y)
  | _ => none

/-- The translation of a unary call of the scalar table on a reading, at the result type
    `r`: the truncation to `64` bits as the reading of its operand, every other call by
    `unChain`. -/
def scalarRes1 {Δ : Ctxt catCryptDialect} (f : String) (ta : NfTy) (ra : Rd Δ ta) :
    (r : NfTy) → Option (OpRes Δ r)
  | .word 64 =>
      (ImpToNF.scalarUnOf f).bind fun ⟨o, w⟩ =>
        if o = .cast ∧ w = 64 then (Rd.toWord64 ta ra).map .rd
        else withVar1 ta ra fun x => some (unChain o w x)
  | _ => none

/-- The translation of a call of the scalar table on readings at the result type `r`: a
    binary call by `scalarRes2`, a unary call by `scalarRes1`. -/
def scalarRes? {Δ : Ctxt catCryptDialect} (f : String) :
    (as : List NfTy) → (r : NfTy) → HVector (fun t => Rd Δ t) as → Option (OpRes Δ r)
  | [ta, tb], r, .cons ra (.cons rb .nil) => scalarRes2 f ta tb ra rb r
  | [ta], r, .cons ra .nil => scalarRes1 f ta ra r
  | _, _, _ => none

/-- **The translation of a call** of the `u64` table on readings: `catCallRd0`, and else the
    scalar table by `scalarRes?`. -/
def catCallRd {Δ : Ctxt catCryptDialect} (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) : Option (OpRes Δ r) :=
  match catCallRd0 f as r rs with
  | some res => some res
  | none => scalarRes? f as r rs

/-- The translation of a trip count read by `r`: the reading of a variable, and the binding
    of a literal by `bvConst`, so that the count of a counted loop is a variable. -/
def tripRes {Δ : Ctxt catCryptDialect} : Rd Δ (.word 64) → OpRes Δ (.word 64)
  | .var w => .rd (.var w)
  | .lit k _ => .expr (cstE (BitVec.ofNat 64 k))

/-- **The translation of an operation** of the fragment on the readings `σ` of its
    arguments: a call by `catCallRd`; an integer literal in `[0, 2^64)` as a literal reading;
    `ctr` and `trip` on a lower bound that reads as the literal `0` as the reading of the
    index and of the upper bound. -/
def catOp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) :
    (op : NfOp) → HVector (fun t => Var Γ t) op.sig → Option (OpRes Δ op.ret)
  | .named _ op, args => catOp σ op args
  | .call f as r, args => catCallRd f as r (σ.rds args)
  | .ilit t v, _ =>
      if ht : ImpToNF.hax64NFWordTy t = true ∧ 0 ≤ v ∧ v < 2 ^ 64 then
        some (.rd (.lit v.toNat ht.1))
      else none
  | .ctr, args =>
      match σ args.head with
      | .lit 0 _ => some (.rd (σ args.tail.head))
      | _ => none
  | .trip t, args =>
      match σ args.head with
      | .lit 0 _ => (Rd.toWord64 t (σ args.tail.head)).map tripRes
      | _ => none
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

/-- A value of the type of an array of `64`-bit words, related to a memref, encodes as the
    integers of a function related to the memref element by element. -/
theorem asArr_rel {Δ : Ctxt catCryptDialect} {t : NfTy} {v : Var Δ (catTy t)} {n : Nat}
    {m : Var Δ (.memref n)} (h : asArr t v = some ⟨n, m⟩) (W : Valuation Δ) {x : t.denote}
    (hx : VRel t x (v.lookup W)) :
    ∃ g : Fin n → Int, ImpToNF.enc t x = .array (List.ofFn fun k => .int (g k)) ∧
      ∀ k, g k = ((m.lookup W) k).toNat := by
  unfold asArr at h
  split at h
  · cases h
    exact ⟨fun k => ((x k).toNat : Int), rfl, fun k => congrArg Nat.cast (hx k)⟩
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

/-- `index` of an array of integers returns the integer at an index below its length; it
    fails at an index beyond. -/
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

/-- An array of `64`-bit words the integers of a function decode as has those integers as the
    natural numbers of its elements. -/
theorem dec_arr_ofFn {n : Nat} {g : Fin n → Int} {y : Fin n → BitVec 64}
    (hd : ImpToNF.dec (.arr n (.word 64)) (.array (List.ofFn fun k => .int (g k))) = some y)
    (k : Fin n) : g k = ((y k).toNat : Int) := by
  have he := ImpToNF.dec_sound _ _ _ hd
  have := congrArg (fun w : _root_.Hax.Value => match w with
    | .array l => l[k.1]? | _ => none) he
  simp only [ImpToNF.enc, List.getElem?_ofFn, k.2, dif_pos] at this
  simpa using this

/-- The names of the calls the fragment translates: the scalar calls `hax64NFScalar`,
    `index` and `array_update`. -/
def CatName (f : String) : Prop :=
  f ∈ ImpToNF.hax64NFScalar () ∨ f = "index" ∨ f = "array_update"

/-- The table `bi` agrees with the `u64` table with `select` at the names of the calls the
    fragment translates. -/
def SubTable (bi : _root_.Hax.Builtins) : Prop :=
  ∀ f vals v, CatName f → bi f vals = some v →
    ImpToNF.withSelect _root_.Hax.hax64Builtins f vals = some v

/-- Under `SubTable bi`, at a name of a translated call other than `select`, a value of `bi`
    is a value of the `u64` table. -/
theorem SubTable.base {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (f : String)
    (vals : List _root_.Hax.Value) (v : _root_.Hax.Value) (hc : CatName f)
    (hne : f ≠ "select") (h : bi f vals = some v) :
    _root_.Hax.hax64Builtins f vals = some v := by
  have hv := hbi f vals v hc h
  rwa [ImpToNF.withSelect_of_ne _ hne] at hv

/-- Under `SubTable bi`, a value of `select` of `bi` on a Boolean and two values is the first
    value at `true` and the second at `false`. -/
theorem SubTable.select {bi : _root_.Hax.Builtins} (hbi : SubTable bi) {k : Bool}
    {x y v : _root_.Hax.Value} (h : bi "select" [.bool k, x, y] = some v) :
    v = if k then x else y := by
  have hv := hbi _ _ _ (Or.inl (by decide)) h
  rw [ImpToNF.withSelect_select_bool] at hv
  exact (Option.some.inj hv).symm

/-- The `u64` table with `select` agrees with itself at every name. -/
theorem subTable_withSelect : SubTable (ImpToNF.withSelect _root_.Hax.hax64Builtins) :=
  fun _ _ _ _ h => h

/-- `SubTable` passes to the table with `select`. -/
theorem subTable_withSelect_of {bi : _root_.Hax.Builtins} (hbi : SubTable bi) :
    SubTable (ImpToNF.withSelect bi) := by
  intro f vals v hc h
  by_cases hf : f = "select"
  · subst hf
    rw [ImpToNF.withSelect_select] at h ⊢
    exact h
  · rw [ImpToNF.withSelect_of_ne _ hf] at h
    exact hbi f vals v hc h

/-- The names of the binary integer calls, the unary integer calls and the comparisons are
    not `select`. -/
theorem tables_ne_select :
    (∀ e ∈ ImpToNF.hax64BinTable, e.1 ≠ "select") ∧
    (∀ e ∈ ImpToNF.hax64UnTable, e.1 ≠ "select") ∧
    (∀ e ∈ ImpToNF.hax64CmpTable, e.1 ≠ "select") := by decide

/-- A scalar call `scalarCatExpr` translates has a name of `hax64NFScalar`. -/
theorem scalarCatExpr_name {Δ : Ctxt catCryptDialect} {f : String} {a b : Var Δ (.sword 64)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : scalarCatExpr f a b = some e) :
    f ∈ ImpToNF.hax64NFScalar () := by
  unfold scalarCatExpr at h
  split at h <;> (try cases h) <;> decide

/-- A scalar call `scalarCatExpr` translates is not `select`. -/
theorem scalarCatExpr_ne_select {Δ : Ctxt catCryptDialect} {f : String}
    {a b : Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : scalarCatExpr f a b = some e) : f ≠ "select" := by
  unfold scalarCatExpr at h
  split at h <;> (try cases h) <;> decide

/-- A value of the bit type, related to a bit, encodes as the Boolean of the bit. -/
theorem asBit_enc {Δ : Ctxt catCryptDialect} {t : NfTy} {v : Var Δ (catTy t)}
    {c : Var Δ .bit} (h : asBit t v = some c) (W : Valuation Δ) {x : t.denote}
    (hx : VRel t x (v.lookup W)) : ImpToNF.enc t x = .bool (c.lookup W) := by
  unfold asBit at h
  split at h
  · cases h
    change x = _ at hx
    subst hx
    rfl
  · cases h

/-- **A call of `select` simulates.** Under `SubTable bi`, a value of the call on a bit and
    two values related to the variables of `selectCat` is the integer of the word the
    expression denotes. -/
theorem selectCat_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {f : String} {tc ta tb : NfTy}
    {args : HVector (fun t => Var Δ t) ([tc, ta, tb].map catTy)}
    {e : Expr catCryptDialect Δ (.sword 64)} (h : selectCat f tc ta tb args = some e)
    {xs : Valuation (d := nfDialect) [tc, ta, tb]}
    (hx : VRelL [tc, ta, tb] xs (Expr.lookupArgs args W)) {v : _root_.Hax.Value}
    (hbv : bi f (ImpToNF.encAll [tc, ta, tb] xs) = some v) :
    v = .int (((e.denote W : BitVec 64)).toNat : Int) := by
  unfold selectCat at h
  split at h
  · rename_i hf
    subst hf
    rcases args with _ | ⟨c₀, _ | ⟨a₀, _ | ⟨b₀, _ | _⟩⟩⟩
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | _⟩⟩⟩
    obtain ⟨hx₁, hx₂, hx₃, -⟩ := hx
    obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hyb, rfl⟩ := Option.map_eq_some_iff.mp h
    change bi "select" [ImpToNF.enc tc x₁, ImpToNF.enc ta x₂, ImpToNF.enc tb x₃] = some v at hbv
    rw [asBit_enc hc W hx₁, asWord_enc hxa W hx₂, asWord_enc hyb W hx₃] at hbv
    rw [hbi.select hbv]
    change _ = _root_.Hax.Value.int
      (((if c.lookup W then x.lookup W else y.lookup W : BitVec 64)).toNat : Int)
    generalize c.lookup W = k
    cases k <;> rfl
  · cases h

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
    change (bi f [ImpToNF.enc ta x₁, ImpToNF.enc tb x₂]).bind (ImpToNF.dec (.word 64)) =
      some y at hy
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hyv := ImpToNF.dec_sound (.word 64) v y hdv
    split at h
    · rename_i hf
      subst hf
      have hv := hbi.base _ _ _ (Or.inr (Or.inl rfl)) (by decide) hbv
      obtain ⟨⟨n, a'⟩, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨g, hg, hgm⟩ := asArr_rel ha W hx₁
      rw [hg, asWord_enc hi W hx₂] at hv
      obtain ⟨hk, hvk⟩ := index_ofFn hv
      rw [hvk] at hyv
      change y = memGetDyn (a'.lookup W) (i'.lookup W).toNat
      rw [memGetDyn_of_lt' _ hk]
      change _root_.Hax.Value.int _ = _root_.Hax.Value.int ((y : BitVec 64).toNat : Int) at hyv
      have hyg := _root_.Hax.Value.int.inj hyv
      rw [hgm] at hyg
      exact (BitVec.eq_of_toNat_eq (by exact_mod_cast hyg)).symm
    · obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.mp h
      have hv := hbi.base _ _ _ (Or.inl (scalarCatExpr_name h)) (scalarCatExpr_ne_select h) hbv
      rw [asWord_enc hxa W hx₁, asWord_enc hw W hx₂] at hv
      have := scalarSem_sound h _ _ hv
      rw [this] at hyv
      have hd : (e.denote W : BitVec 64) = scalarSem f (x.lookup W) (w.lookup W) :=
        scalarCatExpr_denote h W
      change _root_.Hax.Value.int _ = _root_.Hax.Value.int ((y : BitVec 64).toNat : Int) at hyv
      change y = (e.denote W : BitVec 64)
      rw [hd]
      exact (BitVec.eq_of_toNat_eq (by exact_mod_cast (_root_.Hax.Value.int.inj hyv))).symm
  · rename_i ta ti tv n' args
    rcases args with _ | ⟨m₀, _ | ⟨i₀, _ | ⟨x₀, _ | _⟩⟩⟩
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | _⟩⟩⟩
    obtain ⟨hx₁, hx₂, hx₃, -⟩ := hx
    change (bi f [ImpToNF.enc ta x₁, ImpToNF.enc ti x₂, ImpToNF.enc tv x₃]).bind
      (ImpToNF.dec (.arr n' (.word 64))) = some y at hy
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    split at h
    · rename_i hf
      subst hf
      have hv := hbi.base _ _ _ (Or.inr (Or.inr rfl)) (by decide) hbv
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
        rw [hvk] at hdv
        intro k
        have hyk := dec_arr_ofFn hdv k
        change (y k).toNat = (memSetDyn (m.lookup W) (i'.lookup W).toNat (x'.lookup W) k).toNat
        rw [memSetDyn_of_lt' _ hk]
        by_cases hkk : k = ⟨(i'.lookup W).toNat, hk⟩
        · simp only [hkk, if_true] at hyk ⊢
          exact_mod_cast hyk.symm
        · simp only [hkk, if_false, hgm] at hyk ⊢
          exact_mod_cast hyk.symm
      · cases h
    · cases h
  · obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hyv := ImpToNF.dec_sound (.word 64) v y hdv
    rw [selectCat_sound hbi W h hx hbv] at hyv
    change _root_.Hax.Value.int _ = _root_.Hax.Value.int ((y : BitVec 64).toNat : Int) at hyv
    change y = (e.denote W : BitVec 64)
    exact (BitVec.eq_of_toNat_eq (by exact_mod_cast (_root_.Hax.Value.int.inj hyv))).symm
  · obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hyv := ImpToNF.dec_sound .int v y hdv
    rw [selectCat_sound hbi W h hx hbv] at hyv
    change y = (((e.denote W : BitVec 64)).toNat : Int)
    exact (_root_.Hax.Value.int.inj hyv).symm
  · cases h

/-! ### Readings relate values -/

/-- A reading relates a value under one more binding of the target. -/
theorem rdRel_wk {Δ : Ctxt catCryptDialect} {c : CryptoTy} (W : Valuation Δ)
    (y : CryptoTy.denote c) {t : NfTy} (x : t.denote) :
    ∀ (r : Rd Δ t), RdRel W t x r → RdRel (W.extend y) t x r.wk
  | .var _, h => h
  | .lit _ _, h => h

theorem TRd.agree_cons {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy}
    {σ : TRd Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) {x : s.denote}
    {r : Rd Δ s} (hr : RdRel W s x r) : TRd.Agree (TRd.cons r σ) (V.extend x) W := by
  intro t v
  cases v with
  | here => exact hr
  | there v => exact h t v

theorem TRd.agree_wk {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {c : CryptoTy}
    {σ : TRd Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W)
    (y : CryptoTy.denote c) : TRd.Agree (TRd.wk (c := c) σ) V (W.extend y) :=
  fun t v => rdRel_wk W y _ (σ v) (h t v)

theorem TRd.agree_lift {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {s : NfTy}
    {σ : TRd Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) {x : s.denote}
    {y : (catTy s).denote} (hxy : VRel s x y) :
    TRd.Agree (TRd.lift (s := s) σ) (V.extend x) (W.extend y) :=
  TRd.agree_cons (TRd.agree_wk h y) hxy

theorem TRd.agree_liftApp {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect}
    {σ : TRd Γ Δ} {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) :
    (cs : List NfTy) → (A : Valuation (d := nfDialect) cs) →
    (B : Valuation (d := catCryptDialect) (cs.map catTy)) → VRelL cs A B →
    TRd.Agree (TRd.liftApp cs σ) (hvAppend A V) (hvAppend B W)
  | [], .nil, .nil, _ => h
  | _ :: cs, .cons _ A, .cons _ B, hAB =>
      TRd.agree_lift (TRd.agree_liftApp h cs A B hAB.2) hAB.1

theorem TRd.rdRelL_rds {Γ : Ctxt nfDialect} {Δ : Ctxt catCryptDialect} {σ : TRd Γ Δ}
    {V : Valuation Γ} {W : Valuation Δ} (h : σ.Agree V W) :
    ∀ {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts),
      RdRelL W ts (Expr.lookupArgs vs V) (σ.rds vs)
  | [], .nil => trivial
  | t :: _, .cons v vs => ⟨h t v, TRd.rdRelL_rds h vs⟩

theorem pinVars_rel {Δ : Ctxt catCryptDialect} {W : Valuation Δ} :
    ∀ {ts : List NfTy} (xs : Valuation (d := nfDialect) ts) (rs : HVector (fun t => Rd Δ t) ts)
      (ws : HVector (fun t => Var Δ t) (ts.map catTy)), pinVars rs = some ws →
      RdRelL W ts xs rs → VRelL ts xs (Expr.lookupArgs ws W)
  | [], .nil, .nil, ws, h, _ => by
      cases h
      trivial
  | _ :: _, .cons _ xs, .cons r rs, ws, h, hr => by
      cases r with
      | var w =>
          simp only [pinVars, Option.map_eq_some_iff] at h
          obtain ⟨ws', h', rfl⟩ := h
          exact ⟨hr.1, pinVars_rel xs rs ws' h' hr.2⟩
      | lit _ _ => cases h

/-- A type whose values encode as integers is `int` or the `64`-bit word. -/
theorem wordTy_cases {t : NfTy} (h : ImpToNF.hax64NFWordTy t = true) :
    t = .int ∨ t = .word 64 := by
  cases t with
  | int => exact Or.inl rfl
  | word w =>
      have hw : w = 64 := by
        revert h; unfold ImpToNF.hax64NFWordTy; split <;> simp_all
      exact Or.inr (hw ▸ rfl)
  | _ => simp [ImpToNF.hax64NFWordTy] at h

/-- The variable of a literal reads the word of the literal. -/
theorem litVar_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {t : NfTy}
    (h : ImpToNF.hax64NFWordTy t = true) {x : t.denote} {k : Nat}
    (hx : NfTy.toInt? t x = some (k : Int)) (hk : k < 2 ^ 64) :
    VRel t x ((litVar h).lookup (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 k) W)) := by
  rcases wordTy_cases h with rfl | rfl
  · change some x = some (k : Int) at hx
    obtain rfl := Option.some.inj hx
    change ((k : Int)) = (((BitVec.ofNat 64 k).toNat : Nat) : Int)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]
  · change some (x.toNat : Int) = some (k : Int) at hx
    have hx' : x.toNat = k := by exact_mod_cast Option.some.inj hx
    change x = BitVec.ofNat 64 k
    rw [← hx', BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pinLit_rel {Δ : Ctxt catCryptDialect} {W : Valuation Δ} {k : Nat} (hk : k < 2 ^ 64) :
    ∀ {ts : List NfTy} (xs : Valuation (d := nfDialect) ts) (rs : HVector (fun t => Rd Δ t) ts)
      (ws : HVector (fun t => Var (d := catCryptDialect) (CryptoTy.sword 64 :: Δ) t)
        (ts.map catTy)), pinLit k rs = some ws → RdRelL W ts xs rs →
      VRelL ts xs (Expr.lookupArgs ws (HVector.cons (t := CryptoTy.sword 64)
        (BitVec.ofNat 64 k) W))
  | [], .nil, .nil, ws, h, _ => by
      cases h
      trivial
  | _ :: _, .cons _ xs, .cons r rs, ws, h, hr => by
      cases r with
      | var w =>
          simp only [pinLit, Option.map_eq_some_iff] at h
          obtain ⟨ws', h', rfl⟩ := h
          exact ⟨hr.1, pinLit_rel hk xs rs ws' h' hr.2⟩
      | lit k' hw =>
          simp only [pinLit] at h
          split at h
          · rename_i hkk
            subst hkk
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨ws', h', rfl⟩ := h
            exact ⟨litVar_rel W hw hr.1.1 hk, pinLit_rel hk xs rs ws' h' hr.2⟩
          · cases h

theorem firstLit_lt {Δ : Ctxt catCryptDialect} {W : Valuation Δ} :
    ∀ {ts : List NfTy} (xs : Valuation (d := nfDialect) ts) (rs : HVector (fun t => Rd Δ t) ts)
      {k : Nat}, firstLit rs = some k → RdRelL W ts xs rs → k < 2 ^ 64
  | [], .nil, .nil, _, h, _ => by cases h
  | _ :: _, .cons _ xs, .cons r rs, _, h, hr => by
      cases r with
      | var w => exact firstLit_lt xs rs h hr.2
      | lit k' _ =>
          simp only [firstLit, Option.some.injEq] at h
          subst h
          exact hr.1.2

/-- A value of a type whose values encode as integers, whose integer is `k`, encodes as `k`. -/
theorem enc_of_toInt {t : NfTy} (h : ImpToNF.hax64NFWordTy t = true) {x : t.denote} {k : Int}
    (hx : NfTy.toInt? t x = some k) : ImpToNF.enc t x = .int k := by
  rcases wordTy_cases h with rfl | rfl
  · change some x = some k at hx
    obtain rfl := Option.some.inj hx
    rfl
  · change some (x.toNat : Int) = some k at hx
    obtain rfl := Option.some.inj hx
    rfl

/-- The relation of a value and an operation result at the valuation `W` of the target. -/
def OpResRel : {Δ : Ctxt catCryptDialect} → (W : Valuation Δ) → (t : NfTy) → (y : t.denote) →
    OpRes Δ t → Prop
  | _, W, t, y, .rd r => RdRel W t y r
  | _, W, t, y, .expr e => VRel t y (e.denote W)
  | _, W, t, y, .expr1 k e => VRel t y (e.denote (HVector.cons (t := CryptoTy.sword 64)
      (BitVec.ofNat 64 k) W))
  | _, W, t, y, .bind _ e k => OpResRel (W.extend (e.denote W)) t y k

/-- **A shift by an immediate simulates.** -/
theorem shiftImm_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) :
    ∀ (as : List NfTy) (r : NfTy) (rs : HVector (fun t => Rd Δ t) as)
      (e : Expr catCryptDialect Δ (catTy r)) (xs : Valuation (d := nfDialect) as)
      (y : r.denote), shiftImm? f as r rs = some e → RdRelL W as xs rs →
      (bi f (ImpToNF.encAll as xs)).bind (ImpToNF.dec r) = some y →
      VRel r y (e.denote W) := by
  intro as r rs e xs y h hx hy
  unfold shiftImm? at h
  split at h
  · rename_i ta tb rs
    rcases rs with _ | ⟨r₁, _ | ⟨r₂, _ | _⟩⟩
    rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | _⟩⟩
    obtain ⟨hx₁, hx₂, -⟩ := hx
    obtain ⟨a, rfl⟩ : ∃ a, r₁ = .var a := by
      cases r₁ with
      | var a => exact ⟨a, rfl⟩
      | lit _ _ => cases r₂ <;> cases h
    obtain ⟨k, hkt, rfl⟩ : ∃ k hkt, r₂ = .lit k hkt := by
      cases r₂ with
      | lit k hkt => exact ⟨k, hkt, rfl⟩
      | var _ => cases h
    split at h
    · rename_i a' k' hk'' heq1 heq2
      change Rd.var a = Rd.var a' at heq1
      change Rd.lit k hkt = Rd.lit k' hk'' at heq2
      cases heq1
      cases heq2
      split at h
      · rename_i hk64
        obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
        change (bi f [ImpToNF.enc ta x₁, ImpToNF.enc tb x₂]).bind (ImpToNF.dec (.word 64)) =
          some y at hy
        obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
        have hyv := ImpToNF.dec_sound (.word 64) v y hdv
        rw [asWord_enc hxa W hx₁, enc_of_toInt hkt hx₂.1] at hbv
        have hk2 : k < 2 ^ 64 := by omega
        have hk3 : k < 18446744073709551616 := hk2
        have hk' : ((BitVec.ofNat 64 k).toNat : Int) = (k : Int) := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk2]
        split at h
        · rename_i hf
          subst hf
          obtain rfl := Option.some.inj ‹some _ = some e›
          have hv := hbi.base _ _ _ (Or.inl (by decide)) (by decide) hbv
          rw [← hk'] at hv
          have := scalarSem_sound (a := x) (b := x)
            (e := ⟨.bvShiftRV 64, rfl, .cons x (.cons x .nil)⟩) rfl (x.lookup W)
            (BitVec.ofNat 64 k) hv
          rw [this] at hyv
          change _root_.Hax.Value.int _ = _root_.Hax.Value.int ((y : BitVec 64).toNat : Int)
            at hyv
          have hn : (y : BitVec 64).toNat =
              (scalarSem "Shr#64" (x.lookup W) (BitVec.ofNat 64 k)).toNat := by
            exact_mod_cast (_root_.Hax.Value.int.inj hyv).symm
          change (y : BitVec 64) = BitVec.ushiftRight (x.lookup W) k
          apply BitVec.eq_of_toNat_eq
          rw [hn]
          simp [scalarSem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk3]
        · split at h
          · rename_i _ hf
            subst hf
            obtain rfl := Option.some.inj ‹some _ = some e›
            have hv := hbi.base _ _ _ (Or.inl (by decide)) (by decide) hbv
            rw [← hk'] at hv
            have := scalarSem_sound (a := x) (b := x)
              (e := ⟨.bvShiftLV 64, rfl, .cons x (.cons x .nil)⟩) rfl (x.lookup W)
              (BitVec.ofNat 64 k) hv
            rw [this] at hyv
            change _root_.Hax.Value.int _ = _root_.Hax.Value.int ((y : BitVec 64).toNat : Int)
              at hyv
            have hn : (y : BitVec 64).toNat =
                (scalarSem "Shl#64" (x.lookup W) (BitVec.ofNat 64 k)).toNat := by
              exact_mod_cast (_root_.Hax.Value.int.inj hyv).symm
            change (y : BitVec 64) = (show BitVec 64 from x.lookup W) <<< k
            apply BitVec.eq_of_toNat_eq
            rw [hn]
            simp [scalarSem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk3]
          · cases h
      · cases h
    · cases h
  · cases h

/-- A call of `catCallRd0` on readings simulates. -/
theorem catCallRd0_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (res : OpRes Δ r) (xs : Valuation (d := nfDialect) as)
    (y : r.denote) (h : catCallRd0 f as r rs = some res) (hx : RdRelL W as xs rs)
    (hy : (bi f (ImpToNF.encAll as xs)).bind (ImpToNF.dec r) = some y) :
    OpResRel W r y res := by
  unfold catCallRd0 at h
  split at h
  · rename_i ws hws
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact catCall_sound hbi W f as r ws e xs y he (pinVars_rel xs rs ws hws hx) hy
  · split at h
    · rename_i e he
      cases h
      exact shiftImm_sound hbi W f as r rs e xs y he hx hy
    · obtain ⟨k, hk, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ws, hws, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
      have hk64 := firstLit_lt xs rs hk hx
      exact catCall_sound hbi _ f as r ws e xs y he (pinLit_rel hk64 xs rs ws hws hx) hy

/-! ### The scalar table simulates -/

/-- The natural number of a word reduced by the mask is its residue modulo `2 ^ w`. -/
theorem toNat_and_maskW (z : BitVec 64) {w : Nat} (hw : w ≤ 64) :
    (z &&& maskW w).toNat = z.toNat % 2 ^ w := by
  have h1 : 2 ^ w - 1 < 2 ^ 64 := by
    have : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw
    have : 0 < 2 ^ w := by positivity
    omega
  rw [BitVec.toNat_and, maskW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The residue modulo `2 ^ w` of the residue modulo `2 ^ 64`, for `w ≤ 64`. -/
theorem mod64_mod (n : Nat) {w : Nat} (hw : w ≤ 64) : n % 2 ^ 64 % 2 ^ w = n % 2 ^ w :=
  Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 hw)

/-- A word is related at `word 64` to the result of `maskRes w e` when its natural number is
    the residue of the value of `e` modulo `2 ^ w`. -/
theorem maskRes_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {w : Nat} (hw : w ≤ 64)
    (e : Expr catCryptDialect Δ (.sword 64)) (y : BitVec 64)
    (hy : y.toNat = (e.denote W).toNat % 2 ^ w) :
    OpResRel W (.word 64) y (maskRes w e) := by
  unfold maskRes
  split
  · rename_i h64
    subst h64
    change y = e.denote W
    apply BitVec.eq_of_toNat_eq
    rw [hy]
    exact Nat.mod_eq_of_lt (e.denote W).isLt
  · change y = (show BitVec 64 from e.denote W) &&& maskW w
    apply BitVec.eq_of_toNat_eq
    rw [hy, toNat_and_maskW _ hw]

/-- The widths of the binary integer calls, and the width `64` of the high word and the
    checked addition and subtraction. -/
theorem binTable_w : ∀ e ∈ ImpToNF.hax64BinTable,
    (e.2.2 = 8 ∨ e.2.2 = 16 ∨ e.2.2 = 32 ∨ e.2.2 = 64) ∧
      ((e.2.1 = .mulhi ∨ e.2.1 = .addc ∨ e.2.1 = .subc) → e.2.2 = 64) := by decide

/-- The widths of the unary integer calls, and the width `64` of the negation. -/
theorem unTable_w : ∀ e ∈ ImpToNF.hax64UnTable,
    (e.2.2 = 8 ∨ e.2.2 = 16 ∨ e.2.2 = 32 ∨ e.2.2 = 64) ∧ (e.2.1 = .neg → e.2.2 = 64) := by
  decide

/-- **The words of `binE` reduced modulo `2 ^ w` are the values of the scalar table.** -/
theorem binBV_mod (o : ImpToNF.ScalarBin) {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (h64 : (o = .shr ∨ o = .mulhi ∨ o = .addc ∨ o = .subc) → w = 64)
    (hrot : o ≠ .rotr ∧ o ≠ .rotl)
    (x y : BitVec 64) {r : Nat} (h : o.nat w x.toNat y.toNat = some r) :
    (binBV o x y).toNat % 2 ^ w = r := by
  have hx := x.isLt
  have hy := y.isLt
  have hw64 : w ≤ 64 := by omega
  cases o <;> simp only [ImpToNF.ScalarBin.nat] at h
  case add =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_add, mod64_mod _ hw64]
  case sub =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_sub]
    rcases hw with rfl | rfl | rfl | rfl <;> omega
  case mul =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_mul, mod64_mod _ hw64]
  case and =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_and, Nat.and_mod_two_pow]
  case or =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_or, Nat.or_mod_two_pow]
  case xor =>
    obtain rfl := Option.some.inj h
    simp only [binBV, BitVec.toNat_xor, Nat.xor_mod_two_pow]
  case shl =>
    split at h
    · obtain rfl := Option.some.inj h
      simp only [binBV, BitVec.toNat_shiftLeft, mod64_mod _ hw64, Nat.shiftLeft_eq]
      conv_rhs => rw [Nat.mul_mod]
      rw [Nat.mul_mod, Nat.mod_mod]
    · cases h
  case shr =>
    obtain rfl := h64 (Or.inl rfl)
    split at h
    · obtain rfl := Option.some.inj h
      simp only [binBV, BitVec.toNat_ushiftRight, Nat.mod_eq_of_lt hx]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) hx)
    · cases h
  case mulhi =>
    obtain rfl := h64 (Or.inr (Or.inl rfl))
    obtain rfl := Option.some.inj h
    have hlt : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      exact Nat.mul_lt_mul'' hx hy
    simp only [binBV, mulHiC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.shiftRight_eq_div_pow]
  case addc =>
    obtain rfl := h64 (Or.inr (Or.inr (Or.inl rfl)))
    split at h
    · rename_i hs
      obtain rfl := Option.some.inj h
      simp only [binBV, BitVec.toNat_add, Nat.mod_eq_of_lt hs]
    · cases h
  case subc =>
    obtain rfl := h64 (Or.inr (Or.inr (Or.inr rfl)))
    split at h
    · rename_i hs
      obtain rfl := Option.some.inj h
      simp only [binBV, BitVec.toNat_sub]
      omega
    · cases h
  case rotr => exact absurd rfl hrot.1
  case rotl => exact absurd rfl hrot.2

/-- The word `binE` denotes. -/
theorem binE_denote {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {o : ImpToNF.ScalarBin}
    {a b : Var Δ (.sword 64)} {e : Expr catCryptDialect Δ (.sword 64)}
    (h : binE o a b = some e) : e.denote W = binBV o (a.lookup W) (b.lookup W) := by
  cases o <;> simp only [binE, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- A `64`-bit word decoded from the integer of a natural number is the word of that
    number. -/
theorem dec_word64_eq {n : Nat} {y : BitVec 64}
    (h : ImpToNF.dec (.word 64) (.int (n : Int)) = some y) : y = BitVec.ofNat 64 n := by
  simp only [ImpToNF.dec] at h
  split at h
  · cases h
    simp
  · cases h

/-- **The translation of a binary operation of the scalar table is related to its value.** -/
theorem binChain_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (o : ImpToNF.ScalarBin)
    {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (h64 : (o = .mulhi ∨ o = .addc ∨ o = .subc) → w = 64) (hrot : o ≠ .rotr ∧ o ≠ .rotl)
    (a b : Var Δ (.sword 64)) {res : OpRes Δ (.word 64)} (h : binChain o w a b = some res)
    {r : Nat} (hr : o.nat w (a.lookup W).toNat (b.lookup W).toNat = some r) :
    OpResRel W (.word 64) (BitVec.ofNat 64 r) res := by
  have hw64 : w ≤ 64 := by omega
  have hr64 : r < 2 ^ 64 :=
    ImpToNF.ScalarBin.nat_lt o hw64 (a.lookup W).isLt (b.lookup W).isLt hr
  unfold binChain at h
  split at h
  · rename_i hs
    obtain ⟨rfl, -⟩ := hs
    cases h
    simp only [ImpToNF.ScalarBin.nat] at hr
    split at hr
    · obtain rfl := Option.some.inj hr
      change BitVec.ofNat 64 _ =
        ((show BitVec 64 from a.lookup W) &&& maskW w) >>> (b.lookup W).toNat
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, BitVec.toNat_ushiftRight,
        toNat_and_maskW _ hw64]
    · cases hr
  · rename_i hs
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    refine maskRes_rel W hw64 e _ ?_
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr64, binE_denote W he]
    refine (binBV_mod o hw ?_ hrot _ _ hr).symm
    rintro (rfl | rfl | rfl | rfl)
    · by_contra hne
      exact hs ⟨rfl, hne⟩
    · exact h64 (Or.inl rfl)
    · exact h64 (Or.inr (Or.inl rfl))
    · exact h64 (Or.inr (Or.inr rfl))

/-- **The translation of a rotation is related to its value.** -/
theorem rotChain_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (right : Bool) {w : Nat}
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (k : Nat) (a : Var Δ (.sword 64)) :
    OpResRel W (.word 64)
      (BitVec.ofNat 64 (if right then _root_.Hax.rotrNat w (a.lookup W).toNat k
        else _root_.Hax.rotlNat w (a.lookup W).toNat k)) (rotChain right w k a) := by
  have hw64 : w ≤ 64 := by omega
  have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw64
  have hm : ∀ n, n % 2 ^ w < 2 ^ 64 := fun n =>
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hp
  cases right
  · change BitVec.ofNat 64 (_root_.Hax.rotlNat w (a.lookup W).toNat k) =
      ((((show BitVec 64 from a.lookup W) &&& maskW w) <<< (k % w)) |||
        (((show BitVec 64 from a.lookup W) &&& maskW w) >>> (w - k % w))) &&& maskW w
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, _root_.Hax.rotlNat, Nat.mod_eq_of_lt (hm _), toNat_and_maskW _ hw64,
      BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      toNat_and_maskW _ hw64, Nat.or_mod_two_pow, Nat.or_mod_two_pow, mod64_mod _ hw64]
  · change BitVec.ofNat 64 (_root_.Hax.rotrNat w (a.lookup W).toNat k) =
      ((((show BitVec 64 from a.lookup W) &&& maskW w) >>> (k % w)) |||
        (((show BitVec 64 from a.lookup W) &&& maskW w) <<< (w - k % w))) &&& maskW w
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, _root_.Hax.rotrNat, Nat.mod_eq_of_lt (hm _), toNat_and_maskW _ hw64,
      BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
      toNat_and_maskW _ hw64, Nat.or_mod_two_pow, Nat.or_mod_two_pow, mod64_mod _ hw64]

/-- The exclusive or with a word, restricted to that word, is the complement restricted to
    it. -/
theorem xor_and_self_eq_not_and (x m : BitVec 64) : (x ^^^ m) &&& m = ~~~x &&& m := by
  ext i hi
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not]
  cases x[i] <;> cases m[i] <;> rfl

/-- A word is related at `word 64` to the result of `notChain w a` when its natural number
    is the residue of the complement of the value of `a` modulo `2 ^ w`. -/
theorem notChain_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {w : Nat} (hw : w ≤ 64)
    (a : Var Δ (.sword 64)) (y : BitVec 64)
    (hy : y.toNat = (~~~(show BitVec 64 from a.lookup W)).toNat % 2 ^ w) :
    OpResRel W (.word 64) y (notChain w a) := by
  unfold notChain
  split
  · rename_i h64
    subst h64
    change y = (show BitVec 64 from a.lookup W) ^^^ BitVec.allOnes 64
    rw [BitVec.xor_allOnes]
    apply BitVec.eq_of_toNat_eq
    rw [hy]
    exact Nat.mod_eq_of_lt (BitVec.isLt _)
  · change y = ((show BitVec 64 from a.lookup W) ^^^ maskW w) &&& maskW w
    rw [xor_and_self_eq_not_and]
    apply BitVec.eq_of_toNat_eq
    rw [hy, toNat_and_maskW _ hw]

/-- **The translation of a unary operation is related to its value.** -/
theorem unChain_rel{Δ : Ctxt catCryptDialect} (W : Valuation Δ) (o : ImpToNF.ScalarUn)
    {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) (hneg : o = .neg → w = 64)
    (a : Var Δ (.sword 64)) {v : _root_.Hax.Value}
    (hv : o.val w ((a.lookup W).toNat : Int) = some v) :
    ∃ r : Nat, v = .int (r : Int) ∧ OpResRel W (.word 64) (BitVec.ofNat 64 r) (unChain o w a) := by
  have hw64 : w ≤ 64 := by omega
  have hx := (a.lookup W).isLt
  cases o
  · simp only [ImpToNF.ScalarUn.val, _root_.Hax.u64UnOp, Int.natCast_nonneg, true_and,
      Int.toNat_natCast] at hv
    split at hv
    · obtain rfl := Option.some.inj hv
      refine ⟨_, rfl, notChain_rel W hw64 _ _ ?_⟩
      obtain ⟨X, hX⟩ : ∃ X : BitVec 64, a.lookup W = X := ⟨_, rfl⟩
      simp only [hX] at hx ⊢
      rw [BitVec.toNat_not, BitVec.toNat_ofNat]
      rcases hw with rfl | rfl | rfl | rfl <;> omega
    · cases hv
  · obtain rfl := hneg rfl
    simp only [ImpToNF.ScalarUn.val, _root_.Hax.u64UnOp, Int.natCast_nonneg, true_and,
      Int.toNat_natCast] at hv
    split at hv
    · obtain rfl := Option.some.inj hv
      refine ⟨_, rfl, ?_⟩
      obtain ⟨X, hX⟩ : ∃ X : BitVec 64, a.lookup W = X := ⟨_, rfl⟩
      change BitVec.ofNat 64 _ = BitVec.ofNat 64 0 - (show BitVec 64 from a.lookup W)
      simp only [hX] at hx ⊢
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.zero_mod]
      omega
    · cases hv
  · simp only [ImpToNF.ScalarUn.val, Int.natCast_nonneg, if_true, Int.toNat_natCast] at hv
    obtain rfl := Option.some.inj hv
    refine ⟨_, rfl, ?_⟩
    change BitVec.ofNat 64 _ = (show BitVec 64 from a.lookup W) &&& maskW w
    apply BitVec.eq_of_toNat_eq
    have hp : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hw64
    have hlt : (a.lookup W).toNat % 2 ^ w < 2 ^ 64 :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) hp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, toNat_and_maskW _ hw64]

/-- The carry of `x + ~~~y + 1` is `1` exactly when `y ≤ x`. -/
theorem carry_not_eq_one (x y : BitVec 64) :
    decide (carryOutBitC x (~~~y) (1 : BitVec 1) = 1) = decide (y.toNat ≤ x.toNat) := by
  have hy := y.isLt
  have h1 : (1 : BitVec 1).toNat = 1 := rfl
  unfold carryOutBitC
  rw [BitVec.toNat_not, h1]
  by_cases h : y.toNat ≤ x.toNat
  · rw [if_pos (by omega)]
    simp [h]
  · rw [if_neg (by omega)]
    simp [h]

/-- The carry of `x + ~~~y` is `1` exactly when `y < x`. -/
theorem carry_not_zero_eq_one (x y : BitVec 64) :
    decide (carryOutBitC x (~~~y) (0 : BitVec 1) = 1) = decide (y.toNat < x.toNat) := by
  have hy := y.isLt
  have h0 : (0 : BitVec 1).toNat = 0 := rfl
  unfold carryOutBitC
  rw [BitVec.toNat_not, h0]
  by_cases h : y.toNat < x.toNat
  · rw [if_pos (by omega)]
    simp [h]
  · rw [if_neg (by omega)]
    simp [h]

/-- The comparison `bvEq` of two words is the equality of their natural numbers. -/
theorem decide_eq_toNat (x y : BitVec 64) :
    decide (x = y) = (((x.toNat : Int) == (y.toNat : Int)) : Bool) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun he => h (BitVec.eq_of_toNat_eq he)
    simp [h, this]

/-- **The translation of a comparison is related to its value.** -/
theorem cmpChain_rel {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (c : ImpToNF.ScalarCmp)
    (a b : Var Δ (.sword 64)) :
    OpResRel W .bit (c.val ((a.lookup W).toNat : Int) ((b.lookup W).toNat : Int))
      (cmpChain c a b) := by
  have key : ∀ x y : BitVec 64, decide ((y.toNat : Int) ≤ (x.toNat : Int)) =
      decide (carryOutBitC x (y ^^^ BitVec.allOnes 64) (1 : BitVec 1) = 1) := by
    intro x y
    rw [BitVec.xor_allOnes, carry_not_eq_one]
    simp
  have key0 : ∀ x y : BitVec 64, decide ((y.toNat : Int) < (x.toNat : Int)) =
      decide (carryOutBitC x (y ^^^ BitVec.allOnes 64) (0 : BitVec 1) = 1) := by
    intro x y
    rw [BitVec.xor_allOnes, carry_not_zero_eq_one]
    simp
  cases c
  · change ((((a.lookup W).toNat : Int) == ((b.lookup W).toNat : Int)) : Bool) =
      decide ((show BitVec 64 from a.lookup W) = b.lookup W)
    rw [decide_eq_toNat]
  · change (!(((a.lookup W).toNat : Int) == ((b.lookup W).toNat : Int)) : Bool) =
      !decide ((show BitVec 64 from a.lookup W) = b.lookup W)
    rw [decide_eq_toNat]
  · change decide (((a.lookup W).toNat : Int) < ((b.lookup W).toNat : Int)) =
      decide (carryOutBitC (show BitVec 64 from b.lookup W) ((show BitVec 64 from
        a.lookup W) ^^^ BitVec.allOnes 64) (0 : BitVec 1) = 1)
    rw [← key0]
  · change decide (((a.lookup W).toNat : Int) ≤ ((b.lookup W).toNat : Int)) =
      decide (carryOutBitC (show BitVec 64 from b.lookup W) ((show BitVec 64 from
        a.lookup W) ^^^ BitVec.allOnes 64) (1 : BitVec 1) = 1)
    rw [← key]
  · change decide (((b.lookup W).toNat : Int) < ((a.lookup W).toNat : Int)) =
      decide (carryOutBitC (show BitVec 64 from a.lookup W) ((show BitVec 64 from
        b.lookup W) ^^^ BitVec.allOnes 64) (0 : BitVec 1) = 1)
    rw [← key0]
  · change decide (((b.lookup W).toNat : Int) ≤ ((a.lookup W).toNat : Int)) =
      decide (carryOutBitC (show BitVec 64 from a.lookup W) ((show BitVec 64 from
        b.lookup W) ^^^ BitVec.allOnes 64) (1 : BitVec 1) = 1)
    rw [← key]

/-- The word of a literal reading, bound by `bvConst`, is the literal, and the value it reads
    encodes as the literal. -/
theorem lit_enc_word {t : NfTy} {x : t.denote} {n : Nat} {hn : ImpToNF.hax64NFWordTy t = true}
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (h : RdRel W t x (.lit n hn)) :
    ImpToNF.enc t x = .int ((BitVec.ofNat 64 n).toNat : Int) := by
  rw [enc_of_toInt hn h.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.2]

/-- **`withVar1` simulates**: its result is related to `y` when the continuation is, on every
    word variable reading the integer the value of the reading encodes as. -/
theorem withVar1_sound {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {r ta : NfTy}
    {ra : Rd Δ ta} {x₁ : ta.denote} (h1 : RdRel W ta x₁ ra)
    (k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Option (OpRes Δ' r))
    (y : r.denote) {res : OpRes Δ r} (h : withVar1 ta ra k = some res)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (W' : Valuation Δ') (a : Var Δ' (.sword 64))
      (res' : OpRes Δ' r), k a = some res' →
      ImpToNF.enc ta x₁ = .int ((a.lookup W').toNat : Int) → OpResRel W' r y res') :
    OpResRel W r y res := by
  cases ra with
  | var a =>
      obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
      exact HK W x res h (asWord_enc hxa W h1)
  | lit n hn =>
      obtain ⟨res', hres', rfl⟩ := Option.map_eq_some_iff.mp h
      exact HK _ .here res' hres' (lit_enc_word W h1)

/-- **`withVar2` simulates**: its result is related to `y` when the continuation is, on every
    two word variables reading the integers the values of the readings encode as. -/
theorem withVar2_sound {Δ : Ctxt catCryptDialect} (W : Valuation Δ) {r ta tb : NfTy}
    {ra : Rd Δ ta} {rb : Rd Δ tb} {x₁ : ta.denote} {x₂ : tb.denote} (h1 : RdRel W ta x₁ ra)
    (h2 : RdRel W tb x₂ rb)
    (k : ∀ {Δ' : Ctxt catCryptDialect}, Var Δ' (.sword 64) → Var Δ' (.sword 64) →
      Option (OpRes Δ' r))
    (y : r.denote) {res : OpRes Δ r} (h : withVar2 ta tb ra rb k = some res)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (W' : Valuation Δ') (a b : Var Δ' (.sword 64))
      (res' : OpRes Δ' r), k a b = some res' →
      ImpToNF.enc ta x₁ = .int ((a.lookup W').toNat : Int) →
      ImpToNF.enc tb x₂ = .int ((b.lookup W').toNat : Int) → OpResRel W' r y res') :
    OpResRel W r y res := by
  cases ra with
  | var a =>
      cases rb with
      | var b =>
          obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
          exact HK W x z res h (asWord_enc hxa W h1) (asWord_enc hz W h2)
      | lit m hm =>
          obtain ⟨x, hxa, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨res', hres', rfl⟩ := Option.map_eq_some_iff.mp h
          exact HK _ x.there .here res' hres' (asWord_enc hxa W h1) (lit_enc_word W h2)
  | lit n hn =>
      cases rb with
      | var b =>
          obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨res', hres', rfl⟩ := Option.map_eq_some_iff.mp h
          exact HK _ .here z.there res' hres' (lit_enc_word W h1) (asWord_enc hz W h2)
      | lit m hm =>
          obtain ⟨res', hres', rfl⟩ := Option.map_eq_some_iff.mp h
          exact HK _ (Var.there .here) .here res' hres' (lit_enc_word W h1)
            (lit_enc_word W h2)

/-- A binary call of the scalar table on readings simulates. -/
theorem scalarRes2_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) (ta tb r : NfTy)
    (ra : Rd Δ ta) (rb : Rd Δ tb) (res : OpRes Δ r) (x₁ : ta.denote) (x₂ : tb.denote)
    (y : r.denote) (h : scalarRes2 f ta tb ra rb r = some res) (h1 : RdRel W ta x₁ ra)
    (h2 : RdRel W tb x₂ rb)
    (hy : (bi f [ImpToNF.enc ta x₁, ImpToNF.enc tb x₂]).bind (ImpToNF.dec r) = some y) :
    OpResRel W r y res := by
  unfold scalarRes2 at h
  split at h
  · obtain ⟨⟨o, w⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    have hmem := ImpToNF.mem_of_find?_map hp
    have hcat : CatName f := Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨_, hmem, rfl⟩)))))))
    obtain ⟨hw, h64⟩ := binTable_w _ hmem
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hv := hbi.base _ _ _ hcat (tables_ne_select.1 _ hmem) hbv
    have key : ∀ (aN bN : Nat), ImpToNF.enc ta x₁ = .int (aN : Int) →
        ImpToNF.enc tb x₂ = .int (bN : Int) →
        ∃ rn, o.nat w aN bN = some rn ∧ y = BitVec.ofNat 64 rn := by
      intro aN bN ha hb
      rw [ha, hb, ImpToNF.hax64BinTable_sem _ hmem, ImpToNF.orElse_none_eq] at hv
      obtain ⟨rn, hrn, rfl, -, -, -, -⟩ := ImpToNF.u64BinOp_some hv
      simp only [Int.toNat_natCast] at hrn
      exact ⟨rn, hrn, dec_word64_eq hdv⟩
    split at h
    · rename_i hrot
      split at h
      · rename_i k hk _
        refine withVar1_sound W h1 _ y h ?_
        intro Δ' W' a res' hres' he1
        cases hres'
        obtain ⟨rn, hrn, rfl⟩ := key _ k he1 (enc_of_toInt hk h2.1)
        rcases hrot with rfl | rfl
        · simp only [ImpToNF.ScalarBin.nat, Option.some.injEq] at hrn
          subst hrn
          exact rotChain_rel W' true hw k a
        · simp only [ImpToNF.ScalarBin.nat, Option.some.injEq] at hrn
          subst hrn
          exact rotChain_rel W' false hw k a
      · cases h
    · rename_i hrot
      refine withVar2_sound W h1 h2 _ y h ?_
      intro Δ' W' a b res' hres' he1 he2
      obtain ⟨rn, hrn, rfl⟩ := key _ _ he1 he2
      exact binChain_rel W' o hw h64 ⟨fun h => hrot (Or.inl h), fun h => hrot (Or.inr h)⟩
        a b hres' hrn
  · obtain ⟨c, hp, h⟩ := Option.bind_eq_some_iff.mp h
    have hmem := ImpToNF.mem_of_find?_map hp
    have hcat : CatName f := Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_map.mpr ⟨_, hmem, rfl⟩)))))
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hv := hbi.base _ _ _ hcat (tables_ne_select.2.2 _ hmem) hbv
    refine withVar2_sound W h1 h2 _ y h ?_
    intro Δ' W' a b res' hres' he1 he2
    cases hres'
    rw [he1, he2, ImpToNF.hax64CmpTable_sem _ hmem, ImpToNF.orElse_none_eq] at hv
    cases hv
    simp only [ImpToNF.dec, Option.some.injEq] at hdv
    subst hdv
    exact cmpChain_rel W' c a b
  · cases h

/-- A unary call of the scalar table on a reading simulates. -/
theorem scalarRes1_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) (ta r : NfTy)
    (ra : Rd Δ ta) (res : OpRes Δ r) (x₁ : ta.denote) (y : r.denote)
    (h : scalarRes1 f ta ra r = some res) (h1 : RdRel W ta x₁ ra)
    (hy : (bi f [ImpToNF.enc ta x₁]).bind (ImpToNF.dec r) = some y) :
    OpResRel W r y res := by
  unfold scalarRes1 at h
  split at h
  · obtain ⟨⟨o, w⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    have hmem := ImpToNF.mem_of_find?_map hp
    have hcat : CatName f := Or.inl (List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, hmem, rfl⟩)))))))
    obtain ⟨hw, hneg⟩ := unTable_w _ hmem
    obtain ⟨v, hbv, hdv⟩ := Option.bind_eq_some_iff.mp hy
    have hv := hbi.base _ _ _ hcat (tables_ne_select.2.1 _ hmem) hbv
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨rr, hrr, rfl⟩ := Option.map_eq_some_iff.mp h
      cases ra with
      | var z =>
          obtain ⟨z', hz', rfl⟩ := Option.map_eq_some_iff.mp hrr
          rw [asWord_enc hz' W h1, ImpToNF.hax64UnTable_sem _ hmem,
            ImpToNF.orElse_none_eq] at hv
          simp only [ImpToNF.ScalarUn.val, Int.natCast_nonneg, if_true, Int.toNat_natCast,
            Option.some.injEq] at hv
          subst hv
          rw [Nat.mod_eq_of_lt (z'.lookup W).isLt] at hdv
          change y = z'.lookup W
          rw [dec_word64_eq hdv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      | lit k hk =>
          cases hrr
          rw [enc_of_toInt hk h1.1, ImpToNF.hax64UnTable_sem _ hmem,
            ImpToNF.orElse_none_eq] at hv
          simp only [ImpToNF.ScalarUn.val, Int.natCast_nonneg, if_true, Int.toNat_natCast,
            Option.some.injEq] at hv
          subst hv
          rw [Nat.mod_eq_of_lt h1.2] at hdv
          refine ⟨?_, h1.2⟩
          rw [dec_word64_eq hdv]
          change some (((BitVec.ofNat 64 k).toNat : Nat) : Int) = some (k : Int)
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1.2]
    · refine withVar1_sound W h1 _ y h ?_
      intro Δ' W' a res' hres' he1
      cases hres'
      rw [he1, ImpToNF.hax64UnTable_sem _ hmem, ImpToNF.orElse_none_eq] at hv
      obtain ⟨rn, rfl, hrel⟩ := unChain_rel W' o hw hneg a hv
      rw [dec_word64_eq hdv]
      exact hrel
  · cases h

/-- **A call of the scalar table on readings simulates.** -/
theorem scalarRes_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (res : OpRes Δ r) (xs : Valuation (d := nfDialect) as)
    (y : r.denote) (h : scalarRes? f as r rs = some res) (hx : RdRelL W as xs rs)
    (hy : (bi f (ImpToNF.encAll as xs)).bind (ImpToNF.dec r) = some y) :
    OpResRel W r y res :=
  match as, rs, xs, hx, hy, h with
  | [_, _], .cons ra (.cons rb .nil), .cons x₁ (.cons x₂ .nil), hx, hy, h =>
      scalarRes2_sound hbi W f _ _ r ra rb res x₁ x₂ y h hx.1 hx.2.1 hy
  | [_], .cons ra .nil, .cons x₁ .nil, hx, hy, h =>
      scalarRes1_sound hbi W f _ r ra res x₁ y h hx.1 hy
  | [], .nil, _, _, _, h => by cases h
  | _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)), _, _, _, h => by cases h

/-- **A call on readings simulates.** -/
theorem catCallRd_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    {Δ : Ctxt catCryptDialect} (W : Valuation Δ) (f : String) (as : List NfTy) (r : NfTy)
    (rs : HVector (fun t => Rd Δ t) as) (res : OpRes Δ r) (xs : Valuation (d := nfDialect) as)
    (y : r.denote) (h : catCallRd f as r rs = some res) (hx : RdRelL W as xs rs)
    (hy : (bi f (ImpToNF.encAll as xs)).bind (ImpToNF.dec r) = some y) :
    OpResRel W r y res := by
  unfold catCallRd at h
  split at h
  next res₀ h₀ =>
    cases h
    exact catCallRd0_sound hbi W f as r rs res xs y h₀ hx hy
  next => exact scalarRes_sound hbi W f as r rs res xs y h hx hy

/-- **An operation of the fragment simulates.** Under `SubTable bi`, the result `catOp`
    builds from readings relating the valuations is related to the value of the
    operation. -/
theorem catOp_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi) {Γ : Ctxt nfDialect}
    {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ) {V : Valuation Γ} {W : Valuation Δ}
    (hag : σ.Agree V W) :
    ∀ (op : NfOp) (args : HVector (fun t => Var Γ t) op.sig) (res : OpRes Δ op.ret)
      (y : op.ret.denote), catOp σ op args = some res →
      nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V) = some y →
      OpResRel W op.ret y res := by
  intro op
  induction op with
  | named n op ih =>
      intro args res y h hy
      exact ih args res y h hy
  | call f as r =>
      intro args res y h hy
      exact catCallRd_sound hbi W f as r (σ.rds args) res (Expr.lookupArgs args V) y h
        (TRd.rdRelL_rds hag args) hy
  | ilit t v =>
      intro args res y h hy
      unfold catOp at h
      split at h
      · rename_i ht
        obtain ⟨hw, h0, h1⟩ := ht
        cases h
        rcases wordTy_cases hw with rfl | rfl
        · change some v = some y at hy
          cases hy
          refine ⟨?_, by omega⟩
          change some v = some ((v.toNat : Nat) : Int)
          rw [Int.toNat_of_nonneg h0]
        · change (if 0 ≤ v ∧ v < 2 ^ 64 then some (BitVec.ofNat 64 v.toNat) else none) =
            some y at hy
          rw [if_pos ⟨h0, h1⟩] at hy
          cases hy
          refine ⟨?_, by omega⟩
          change some (((BitVec.ofNat 64 v.toNat).toNat : Nat) : Int) = some ((v.toNat : Nat) : Int)
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      · cases h
  | ctr =>
      intro args res y h hy
      rcases args with _ | ⟨lo, _ | ⟨i, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => some (OpRes.rd (σ i))
        | _ => none) = some res at h
      split at h
      · rename_i hz hlo
        cases h
        have h0 := hag _ lo
        rw [hlo] at h0
        have h0' : @Eq Int (lo.lookup V) 0 := by
          have := h0.1
          change some _ = some _ at this
          exact_mod_cast Option.some.inj this
        have hi := hag _ i
        change (if 0 ≤ (show Int from lo.lookup V) ∧ (show Int from lo.lookup V) +
            (((show BitVec 64 from i.lookup V)).toNat : Int) < 2 ^ 64 then
          some (BitVec.ofNat 64 ((show Int from lo.lookup V) +
            (((show BitVec 64 from i.lookup V)).toNat : Int)).toNat) else none) = some y at hy
        rw [h0', zero_add] at hy
        split at hy
        · have hy' := Option.some.inj hy
          rw [Int.toNat_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hy'
          subst hy'
          exact hi
        · cases hy
      · cases h
  | trip t =>
      intro args res y h hy
      rcases args with _ | ⟨lo, _ | ⟨hi, _ | _⟩⟩
      change (match σ lo with
        | .lit 0 _ => (Rd.toWord64 t (σ hi)).map tripRes
        | _ => none) = some res at h
      split at h
      · rename_i hz hlo
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have h0 := hag _ lo
        rw [hlo] at h0
        have h0' : @Eq Int (lo.lookup V) 0 := by
          have := h0.1
          change some _ = some _ at this
          exact_mod_cast Option.some.inj this
        change ((NfTy.toInt? t (hi.lookup V)).map fun hh =>
          BitVec.ofNat 64 (hh - (show Int from lo.lookup V)).toNat) = some y at hy
        have hhi := hag _ hi
        revert hr hhi
        cases σ hi with
        | var w =>
            intro hr hhi
            obtain ⟨w', hw', rfl⟩ := Option.map_eq_some_iff.mp hr
            have he := asWord_enc hw' W hhi
            have hwt : ImpToNF.hax64NFWordTy t = true := by
              unfold asWord at hw'
              split at hw'
              · assumption
              · cases hw'
            have ht : NfTy.toInt? t (hi.lookup V) = some ((w'.lookup W).toNat : Int) := by
              rcases wordTy_cases hwt with rfl | rfl
              · change _root_.Hax.Value.int _ = _root_.Hax.Value.int _ at he
                exact congrArg some (_root_.Hax.Value.int.inj he)
              · change _root_.Hax.Value.int _ = _root_.Hax.Value.int _ at he
                exact congrArg some (_root_.Hax.Value.int.inj he)
            rw [ht, Option.map_some, h0'] at hy
            obtain rfl := Option.some.inj hy
            change BitVec.ofNat 64 (((w'.lookup W).toNat : Int) - 0).toNat = w'.lookup W
            simp
        | lit k hk =>
            intro hr hhi
            cases hr
            rw [hhi.1, Option.map_some, h0'] at hy
            obtain rfl := Option.some.inj hy
            change BitVec.ofNat 64 (((k : Int) - 0)).toNat = BitVec.ofNat 64 k
            simp only [sub_zero, Int.toNat_natCast]
      · cases h
  | _ =>
      intro args res y h hy
      cases h

/-! ## 6. Programs -/

/-- The bindings of the translation `res` of an operation of result type `t = s`, from the
    readings `σ`, followed by the translation `cont` of the continuation: no binding for a
    reading, the binding of the expression, the binding of a literal and then of the
    expression, or the binding of an intermediate value and then the rest. -/
def emitRes {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy))) :
    {Δ : Ctxt catCryptDialect} → {t : NfTy} → t = s → OpRes Δ t → TRd Γ Δ →
      Option (NFProg catCryptDialect Δ (ts.map catTy))
  | _, _, h, .rd r, σ => cont (TRd.cons (h ▸ r) σ)
  | _, _, h, .expr e', σ => (cont σ.lift).map fun k' =>
      .var ⟨e'.op, e'.retTy_eq.trans (congrArg catTy h), e'.args⟩ k'
  | _, _, h, .expr1 c e', σ => (cont (TRd.lift (TRd.wk σ))).map fun k' =>
      .var ⟨.bvConst 64 (BitVec.ofNat 64 c), rfl, .nil⟩
        (.var ⟨e'.op, e'.retTy_eq.trans (congrArg catTy h), e'.args⟩ k')
  | _, _, h, .bind _ e rest, σ => (emitRes cont h rest σ.wk).map fun k' => .var e k'

/-- **The translation of a program** of the fragment on the readings `σ`: a return to the
    return of the variables it reads; a binding to the bindings `emitRes` gives for the
    translation `catOp` of its operation; and a counted loop whose seeds are variables to the
    counted loop of the translated body and continuation, on the variable of the count or,
    for a count that reads as a literal, on a `bvConst` binding of the literal in front of the
    loop; and a branch to the branch of the translated arms and continuation on the variable
    of its condition (a bit has no literal reading). `none` on an exit-flag loop and a
    call. -/
def nfToCat : {Γ : Ctxt nfDialect} → {Δ : Ctxt catCryptDialect} → {ts : List NfTy} →
    NFProg nfDialect Γ ts → TRd Γ Δ → Option (NFProg catCryptDialect Δ (ts.map catTy))
  | _, _, _, .ret vs, σ => (pinVars (σ.rds vs)).map .ret
  | _, _, _, .var ⟨op, h, args⟩ k, σ =>
      (catOp σ op args).bind fun res => emitRes (fun σ' => nfToCat k σ') h res σ
  | _, _, _, .forLoop (cs := cs) count inits body k, σ =>
      match σ count with
      | .var c =>
          (pinVars (σ.rds inits)).bind fun is =>
            (nfToCat body (TRd.liftApp cs (TRd.lift σ))).bind fun body' =>
              (nfToCat k (TRd.liftApp cs σ)).map fun k' =>
                .forLoop (cs := cs.map catTy) c is body' k'
      | .lit n _ =>
          (pinVars (TRd.rds (TRd.wk (c := CryptoTy.sword 64) σ) inits)).bind fun is =>
            (nfToCat body (TRd.liftApp cs (TRd.lift (TRd.wk (c := CryptoTy.sword 64) σ)))).bind
              fun body' =>
                (nfToCat k (TRd.liftApp cs (TRd.wk (c := CryptoTy.sword 64) σ))).map fun k' =>
                  .var ⟨.bvConst 64 (BitVec.ofNat 64 n), rfl, .nil⟩
                    (.forLoop (cs := cs.map catTy) .here is body' k')
  | _, _, _, .ifThenElse (rs := rs) cond thn els k, σ =>
      match σ cond with
      | .var c =>
          (nfToCat thn σ).bind fun thn' =>
            (nfToCat els σ).bind fun els' =>
              (nfToCat k (TRd.liftApp rs σ)).map fun k' =>
                .ifThenElse (rs := rs.map catTy) c thn' els' k'
      | .lit _ _ => none
  | _, _, _, .whileLoop .., _ => none
  | _, _, _, .call .., _ => none

/-- **The simulation statement of the translation** of the program `p`: a denotation of `p`
    to `out` from a valuation related to `W` by the readings is matched, at every fuel, by a
    denotation of the translated program from `W` to a related vector. -/
def NFSound (bi : _root_.Hax.Builtins) (tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) : Prop :=
  ∀ {Δ : Ctxt catCryptDialect} (σ : TRd Γ Δ)
    (p' : NFProg catCryptDialect Δ (ts.map catTy)), nfToCat p σ = some p' →
    ∀ (V : Valuation Γ) (W : Valuation Δ) (out : Valuation (d := nfDialect) ts),
    σ.Agree V W → ImpToNF.PDenP bi tf p V = some out →
    ∀ fuel, ∃ out', p'.denote fuel W = some out' ∧ VRelL ts out out'

/-- **The bindings of a translated operation simulate.** When the continuation `cont`
    simulates from every reading that relates `V.extend y`, the bindings `emitRes` builds for
    a translation `res` related to `y` simulate from every valuation the readings `σ` relate
    to `V`. -/
theorem emitRes_sound {Γ : Ctxt nfDialect} {s : NfTy} {ts : List NfTy}
    (cont : ∀ {Δ' : Ctxt catCryptDialect}, TRd (s :: Γ) Δ' →
      Option (NFProg catCryptDialect Δ' (ts.map catTy)))
    (V : Valuation Γ) (y : s.denote) (out : Valuation (d := nfDialect) ts) (fuel : Nat)
    (HK : ∀ {Δ' : Ctxt catCryptDialect} (σ' : TRd (s :: Γ) Δ')
      (p' : NFProg catCryptDialect Δ' (ts.map catTy)) (W' : Valuation Δ'),
      cont σ' = some p' → σ'.Agree (V.extend y) W' →
      ∃ out', p'.denote fuel W' = some out' ∧ VRelL ts out out') :
    ∀ {Δ : Ctxt catCryptDialect} (res : OpRes Δ s) (σ : TRd Γ Δ) (W : Valuation Δ)
      (p' : NFProg catCryptDialect Δ (ts.map catTy)),
      emitRes cont rfl res σ = some p' → σ.Agree V W → OpResRel W s y res →
      ∃ out', p'.denote fuel W = some out' ∧ VRelL ts out out' := by
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
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
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
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
      change NFProg.denote fuel (NFProg.var _ k') W1 = some out'
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
      exact hden
  | bind c e rest ih =>
      intro σ W p' h hag hrel
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨out', hden, hR⟩ := ih cont y HK σ.wk (W.extend (e.denote W)) k' hk'
        (TRd.agree_wk hag _) hrel
      refine ⟨out', ?_, hR⟩
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
      exact hden

/-- **The translation simulates the denotation.** -/
theorem nfToCat_sound {bi : _root_.Hax.Builtins} (hbi : SubTable bi) (tf : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) : NFSound bi tf p := by
  induction p with
  | ret vs =>
      intro Δ σ p' h V W out hag hp fuel
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      change some (Expr.lookupArgs vs V) = some out at hp
      cases hp
      exact ⟨_, rfl, pinVars_rel _ _ ws hws (TRd.rdRelL_rds hag vs)⟩
  | var e k ih =>
      intro Δ σ p' h V W out hag hp fuel
      obtain ⟨op, rfl, args⟩ := e
      obtain ⟨res, hres, h⟩ := Option.bind_eq_some_iff.mp h
      change (nfDenoteOp (ImpToNF.tableOf bi) op (Expr.lookupArgs args V)).bind
        (fun x => ImpToNF.PDenP bi tf k (V.extend x)) = some out at hp
      obtain ⟨y, hy, hp⟩ := Option.bind_eq_some_iff.mp hp
      have hrel := catOp_sound hbi σ hag op args res y hres hy
      exact emitRes_sound (fun σ' => nfToCat k σ') V y out fuel
        (fun σ' p'' W' hk hag' => ih σ' p'' hk (V.extend y) W' out hag' hp fuel)
        res σ W p' h hag hrel
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
          pinVars (σ'.rds inits) = some is →
          nfToCat body (TRd.liftApp cs (TRd.lift σ')) = some body' →
          nfToCat k (TRd.liftApp cs σ') = some k' →
          ∃ out', (NFProg.forLoop (cs := cs.map catTy) c is body' k').denote fuel W' =
            some out' ∧ VRelL ts₀ out out' := by
        intro Δ' σ' W' c is body' k' hag' hcnt his hb' hk'
        have key : ∀ (l : List Nat) (acc : Valuation (d := nfDialect) cs)
            (acc' : Valuation (d := catCryptDialect) (cs.map catTy))
            (accF : Valuation (d := nfDialect) cs), VRelL cs acc acc' →
            l.foldlM (fun acc j => ImpToNF.PDenP bi tf body
              (hvAppend acc (HVector.cons (t := NfTy.word 64) (BitVec.ofNat 64 j) V))) acc =
              some accF →
            ∃ accF', l.foldlM (fun acc j => body'.denote fuel
              (hvAppend acc (HVector.cons (t := CryptoTy.sword 64) (BitVec.ofNat 64 j) W')))
              acc' = some accF' ∧ VRelL cs accF accF' := by
          intro l
          exact NFProg.foldlM_rel_fwd l fun j _ acc acc' a1 hr ha1 =>
            ihb (TRd.liftApp cs (TRd.lift σ')) body' hb' _ _ a1
              (TRd.agree_liftApp (TRd.agree_lift (s := NfTy.word 64) hag'
                (x := BitVec.ofNat 64 j) (y := BitVec.ofNat 64 j) rfl) cs acc acc' hr) ha1 fuel
        obtain ⟨accF', hfold', hrF⟩ := key _ _ _ accF
          (pinVars_rel _ _ is his (TRd.rdRelL_rds hag' inits)) hfold
        obtain ⟨out', hden, hR⟩ := ihk (TRd.liftApp cs σ') k' hk' (hvAppend accF V)
          (hvAppend accF' W') out (TRd.agree_liftApp hag' cs accF accF' hrF) hkout fuel
        refine ⟨out', ?_, hR⟩
        rw [NFProg.denote_forLoop]
        have hc2 : HasWord64.toNat (d := catCryptDialect) (c.lookup W') =
            (count.lookup V : BitVec 64).toNat := by
          rw [← hcnt]; rfl
        rw [hc2, List.range_eq_range']
        erw [hfold']
        exact hden
      have hcount := hag _ count
      simp only [nfToCat] at h
      split at h
      · rename_i c hc
        rw [hc] at hcount
        obtain ⟨is, his, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨body', hb', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        exact core σ W c is body' k' hag hcount his hb' hk'
      · rename_i n hn hc
        rw [hc] at hcount
        obtain ⟨is, his, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨body', hb', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        have hn' : (count.lookup V : BitVec 64).toNat = n := by
          exact_mod_cast Option.some.inj hcount.1
        obtain ⟨out', hden, hR⟩ := core (TRd.wk (c := CryptoTy.sword 64) σ)
          (W.extend (BitVec.ofNat 64 n)) .here is body' k'
          (TRd.agree_wk (c := CryptoTy.sword 64) hag (BitVec.ofNat 64 n))
          (by
            change (count.lookup V : BitVec 64) = BitVec.ofNat 64 n
            rw [← hn', BitVec.ofNat_toNat, BitVec.setWidth_eq]) his hb' hk'
        refine ⟨out', ?_, hR⟩
        rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
        exact hden
  | @ifThenElse Γ₀ rs ts₀ cond thn els k iht ihe ihk =>
      intro Δ σ p' h V W out hag hp fuel
      change ((if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) = true then
          ImpToNF.PDenP bi tf thn V else ImpToNF.PDenP bi tf els V).bind
          fun r => ImpToNF.PDenP bi tf k (hvAppend r V)) = some out at hp
      obtain ⟨r, hr, hkout⟩ := Option.bind_eq_some_iff.mp hp
      have hcond := hag _ cond
      simp only [nfToCat] at h
      split at h
      · rename_i c hc
        rw [hc] at hcond
        obtain ⟨thn', ht', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨els', he', h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp h
        have hcb : HasBoolBit.toBool (d := catCryptDialect) (c.lookup W) =
            HasBoolBit.toBool (d := nfDialect) (cond.lookup V) := hcond.symm
        obtain ⟨r', hr', hrR⟩ : ∃ r', (if HasBoolBit.toBool (d := catCryptDialect)
            (c.lookup W) = true then thn'.denote fuel W else els'.denote fuel W) = some r' ∧
            VRelL rs r r' := by
          rw [hcb]
          cases hb : HasBoolBit.toBool (d := nfDialect) (cond.lookup V)
          · rw [hb] at hr
            exact ihe σ els' he' V W r hag hr fuel
          · rw [hb] at hr
            exact iht σ thn' ht' V W r hag hr fuel
        obtain ⟨out', hden, hR⟩ := ihk (TRd.liftApp rs σ) k' hk' (hvAppend r V)
          (hvAppend r' W) out (TRd.agree_liftApp hag rs r r' hrR) hkout fuel
        refine ⟨out', ?_, hR⟩
        rw [NFProg.denote_ifThenElse]
        erw [hr']
        exact hden
      · cases h
  | whileLoop inits body k _ _ =>
      intro Δ σ p' h
      cases h
  | call f args k _ =>
      intro Δ σ p' h
      cases h

/-! ## 7. The entry -/

/-- The value of the target type a value of the fragment maps to: a word to itself, an
    integer to the word of its natural number, an array of words element by element, to
    the `64`-bit words of the natural numbers of its elements. -/
def toCatVal : (t : NfTy) → t.denote → (catTy t).denote
  | .word _, x => x
  | .int, z => BitVec.ofNat 64 z.toNat
  | .arr _ (.word _), f => fun k => BitVec.ofNat 64 (f k).toNat
  | .arr _ _, _ => fun _ => 0
  | .bit, b => b
  | .unit, _ => ()
  | .pair _ _, _ => ()
  | .uint _, _ => ()
  | .sint _, _ => ()
  | .tnil, _ => ()
  | .tcons _ _, _ => ()
  | .slice _, _ => ()

/-- A value of the fragment whose integers, and the natural numbers of whose array elements,
    are in `[0, 2^64)`. -/
def InRange : (t : NfTy) → t.denote → Prop
  | .word _, _ => True
  | .int, z => 0 ≤ z ∧ z < 2 ^ 64
  | .arr _ (.word _), f => ∀ k, (f k).toNat < 2 ^ 64
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
  | .arr _ (.word _), f, h => fun k => by
      change (f k).toNat = (BitVec.ofNat 64 (f k).toNat).toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h k)]
  | .bit, _, _ => rfl
  | .unit, _, _ => trivial
  | .arr _ .bit, _, h | .arr _ .unit, _, h | .arr _ .int, _, h | .arr _ (.arr _ _), _, h
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

/-- The readings of a context in its mapped context: each variable by its variable. -/
def TRd.id {Γ : Ctxt nfDialect} : TRd Γ (Γ.map catTy) := fun v => .var (TRen.id v)

/-- The readings of a context in its mapped context relate a valuation in range to its mapped
    valuation. -/
theorem TRd.agree_id {Γ : Ctxt nfDialect} (V : Valuation Γ)
    (h : ∀ (t : NfTy) (v : Var Γ t), InRange t (v.lookup V)) :
    TRd.Agree TRd.id V (mapVal V) :=
  fun t v => TRen.agree_id V h t v

/-- The type of a parameter of a System V layout: a scalar is a `64`-bit word, an array of
    `n` words an array of `n` `64`-bit words. -/
def abiKindArr : SecureCompilation.Haxc.ArgKind → NfTy
  | .scalar => .word 64
  | .words n => .arr n (.word 64)

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
      refine ⟨fun k => SecureCompilation.Ascent.AddrMem.read64 sa.mem
        (sa.regs reg + BitVec.ofNat 64 (8 * k.1)), ?_, fun k => BitVec.isLt _⟩
      simp only [SecureCompilation.Haxc.AbiArg.read, SecureCompilation.Haxc.wordsAt, abiKindArr,
        ImpToNF.enc]
      congr 1
      apply List.ext_getElem <;> simp

/-- An encoding is determined by the value it encodes, at the type of an array of `64`-bit
    words and at a word type. -/
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
      exact BitVec.eq_of_toNat_eq (by exact_mod_cast _root_.Hax.Value.int.inj this)

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
