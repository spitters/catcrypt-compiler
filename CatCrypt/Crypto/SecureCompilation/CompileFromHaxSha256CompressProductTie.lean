/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ThirToComFront
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie
public import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie
public import CatCrypt.Crypto.SecureCompilation.VIR.Grind

/-!
# Product-output front: the whole 8-word SHA-256 state as ONE emitted `Com`

`CompileFromHaxSha256CompressTie` composes the 64-round SHA-256 compression at the
**spec level** because the single-output scalar front emits a `Com … (rW w)` —
one register — so a round's 8-word working state `(a..h)` is two emitted scalar
leaves (`a'`, `e'`) plus the spec-level shift, not one front-emittable program.
That file's honest-scope note names the gap: *"emitting a single `Com` that
returns the full 256-bit state would need the front to grow a product-output /
multi-register return."*

This module closes that residual **without a `Com`-core change**. The key
observation: the `Com` core's single return type `t : d.Ty` is the dialect's
**type alphabet**, and `jasminDialect`'s `JasminTy.stackArr 32 8` already denotes
to `Fin 8 → BitVec 32` — a genuine 8-element product. So a single
`Com jasminDialect Γ (.stackArr 32 8)` returns the **whole 8-word state as ONE
value**; the existing `stackStore`/`stackLoad` ops (the §9 `storeDemoCom` pilot)
build and read it. No new `Com` constructor, no multi-`ret`, no ripple through
the pipeline — the product-return is the existing array `Ty` used as the return
type.

(The `callN` multi-result op of #315 does **not** provide this: `callNRet`
projects its `retTys` to the head slot `retTys.headD`, exposing only ONE
`JasminTy` at the `Expr`/`Com` level — its tuple lives as op-data for the
`func.call` lowering, not as a `Com` value. The array `Ty` is the right vehicle
for a homogeneous 8×u32 state.)

## What is closed here

* `stateArr` / `arrState` — the 8-word ↔ `Fin 8 → BitVec 32` bridge.
* `sha256RoundProductCom` — a single `Com jasminDialect [stackArr 32 8, reg 32,
  reg 32] (stackArr 32 8)`: load the 8 state words, compute the round update,
  store the whole next state into one array, **return the array**. One product-
  output `Com`, denoting to the whole next 8-word state.
* `sha256RoundProductCom_denote` — its denotation **is** the FIPS-180-4 verified
  single round `sha256RoundVerified`, as one product value (no `a'`/`e'` split,
  no spec-level shift).
* `wholeCompressProduct` — folding the product-output round `Com` 64 times, then
  the feed-forward add, denotes to the FIPS-180-4 whole-block compression
  `CompileFromHaxSha256CompressTie.sha256Compress` — the whole compression as the
  iterate of ONE emitted product-output `Com`, the engine returning its full
  8-word state every round.

Functional-equality tie, not a security claim (SHA-256 is unkeyed; CR/PRF live in
`SLHDSA/Reduction.lean`). The schedule `W[t]` stays the front-expressed whole
recurrence of `CompileFromHaxSha256CompressTie.wholeSchedule_denoteScalar`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressProductTie

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Util.Sha256Verified
  (Sha256Working sha256RoundVerified bigSigma0 bigSigma1 ch maj)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressTie
  (roundFold sha256Compress)

/-! ## §1  The 8-word state ↔ `Fin 8 → BitVec 32` product bridge

The product type a single `Com … (stackArr 32 8)` returns is `Fin 8 → BitVec 32`
(= `⟦stackArr 32 8⟧`). `stateArr` is the canonical view of a `Sha256Working`
record as that 8-element array (slot `0..7 = a..h`); `arrState` is its inverse.
They are mutually inverse, so the product `Com`'s array return value carries
exactly the 8-word working state. -/

/-- The 8-word working state as the product `Fin 8 → BitVec 32` a
    `Com … (stackArr 32 8)` returns: slot `0..7 = a..h`. -/
def stateArr (s : Sha256Working) : Fin 8 → BitVec 32 := fun i =>
  match i with
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d
  | 4 => s.e | 5 => s.f | 6 => s.g | 7 => s.h

/-- Read an 8-word product array back into a `Sha256Working` record. -/
def arrState (arr : Fin 8 → BitVec 32) : Sha256Working :=
  { a := arr 0, b := arr 1, c := arr 2, d := arr 3
    e := arr 4, f := arr 5, g := arr 6, h := arr 7 }

@[simp] theorem arrState_stateArr (s : Sha256Working) : arrState (stateArr s) = s := by
  cases s; rfl

/-! ## §2  The product-output round semantics over arrays

`roundProdSem` is the FIPS-180-4 single round (`sha256RoundVerified`) phrased
**directly on the product** `Fin 8 → BitVec 32`: read the 8 input words, run the
verified round, write the whole 8-word result back as one array. This is the pure
function a single product-output `Com … (stackArr 32 8)` denotes to — the engine
returning its full state, with no `a'`/`e'` split. -/

/-- The verified single round as an array-to-array map on the 8-word product:
    `arr ↦ stateArr (sha256RoundVerified (arrState arr) K W)`. The whole next
    state as one product value. -/
def roundProdSem (kt wt : BitVec 32) (arr : Fin 8 → BitVec 32) : Fin 8 → BitVec 32 :=
  stateArr (sha256RoundVerified (arrState arr) kt wt)

/-- `roundProdSem` over `stateArr s` is the verified round, viewed as a product:
    no working-variable is dropped — the whole `(a..h)` next state is the array. -/
@[simp] theorem roundProdSem_stateArr (kt wt : BitVec 32) (s : Sha256Working) :
    roundProdSem kt wt (stateArr s) = stateArr (sha256RoundVerified s kt wt) := by
  simp [roundProdSem]

/-! ## §3  The product-output round `Com` (one `Com … (stackArr 32 8)`)

The single product-output `Com` over the input context
`[stackArr 32 8, reg 32 (= K_t), reg 32 (= W_t)]`. It loads the 8 state words
with `stackLoad`, computes the FIPS round update with the dialect's
`regArith`/`rorImm` ops, then `stackStore`s the whole next 8-word state into one
array and **returns the array** — the product return is the existing `stackArr`
`Ty`, no `Com`-core change.

The context layout (de Bruijn 0 = newest):

* `inp[0]` = the 8-word input state array (`stackArr 32 8`)
* `inp[1]` = `K_t` (`reg 32`)
* `inp[2]` = `W_t` (`reg 32`)

We work over the *abstract* context-variable handles rather than spelling out the
24-deep de Bruijn chain by hand: a tiny `RB` (register builder) DSL accumulates
the load/compute bindings, and the result-array writes thread off it. The whole
`Com` is closed-form, so its denotation is a `decide`/`simp`-reducible array. -/

/-- Helper: the round update as a record (the exact body of `sha256RoundVerified`)
    so the product `Com`'s denote can be matched field-by-field. Definitionally the
    verified round. -/
@[simp] theorem roundProdSem_apply (kt wt : BitVec 32) (arr : Fin 8 → BitVec 32) :
    roundProdSem kt wt arr
      = stateArr (sha256RoundVerified (arrState arr) kt wt) := rfl

/-! ### §3.1  Dialect-op bridge for the round sub-functions

The product `Com`'s body computes the round update with the dialect's
`rorImm`/`regArith` ops. Each named FIPS sub-function (`bigSigma0/1`, `ch`,
`maj`) is the corresponding dialect-op composition; the bridge lemmas let the
`Com.denote` reduce to the `sha256RoundVerified` record field-by-field. The
rotate spelling is tied by `CompileFromHaxSha256CompressTie`'s
`rotateRight_eq_rotr` (the same bridge the spec-level tie uses). -/

open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha2KeccakTie (rotateRight_eq_rotr)

/-- `bigSigma1` via the dialect's native rotate (`BitVec.rotateRight`, the `rorImm`
    denotation) instead of the `>>> ||| <<<` `rotr` spelling. -/
theorem bigSigma1_rotateRight (x : BitVec 32) :
    bigSigma1 x = (x.rotateRight 6) ^^^ (x.rotateRight 11) ^^^ (x.rotateRight 25) := by
  unfold bigSigma1
  rw [rotateRight_eq_rotr x (n := 6) (by omega),
      rotateRight_eq_rotr x (n := 11) (by omega),
      rotateRight_eq_rotr x (n := 25) (by omega)]

/-- `bigSigma0` via the dialect's native rotate. -/
theorem bigSigma0_rotateRight (x : BitVec 32) :
    bigSigma0 x = (x.rotateRight 2) ^^^ (x.rotateRight 13) ^^^ (x.rotateRight 22) := by
  unfold bigSigma0
  rw [rotateRight_eq_rotr x (n := 2) (by omega),
      rotateRight_eq_rotr x (n := 13) (by omega),
      rotateRight_eq_rotr x (n := 22) (by omega)]

/-! ### §3.2  The product-PACK `Com`: 8 registers → one `stackArr 32 8`

`packCom` is the product-output `Com` proper: it takes the 8 next-state words as
register inputs (context `replicate 8 (reg 32)`) and **returns one
`stackArr 32 8`** — the whole 8-word state assembled into a single product value.
This is the front-emittable program that returns the full state in one `Com`; the
return type is the existing array `Ty`, with no `Com`-core change. The body seeds
an empty array (`regConst`-free: `stackStore` into the input-resident scratch) and
writes the 8 slots; `packCom_denote` proves the returned array is exactly the
8-word product `fun i => words i`. -/

/-- The input context of the pack `Com`: an out-buffer scratch array
    (`stackArr 32 8`, the ABI return slot, overwritten in full) followed by the 8
    `reg 32` next-state words `a'..h'`. -/
abbrev packCtxt : Ctxt jasminDialect := .stackArr 32 8 :: List.replicate 8 (.reg 32)

/-- The scratch out-array variable (de Bruijn 0 of `packCtxt`). -/
def packArrVar : Ctxt.Var packCtxt (.stackArr 32 8) := .here

/-- The de Bruijn variable for input word `i < 8` of `packCtxt` (the `i`-th
    `reg 32`, shifted under the leading scratch array). -/
def packWordVar : (i : Fin 8) → Ctxt.Var packCtxt (.reg 32)
  | 0 => .there .here
  | 1 => .there (.there .here)
  | 2 => .there (.there (.there .here))
  | 3 => .there (.there (.there (.there .here)))
  | 4 => .there (.there (.there (.there (.there .here))))
  | 5 => .there (.there (.there (.there (.there (.there .here)))))
  | 6 => .there (.there (.there (.there (.there (.there (.there .here))))))
  | 7 => .there (.there (.there (.there (.there (.there (.there (.there .here)))))))

/-- The canonical `packCtxt` valuation from a scratch array `s0` and 8 words
    `words : Fin 8 → BitVec 32`. -/
def packVal (s0 : Fin 8 → BitVec 32) (words : Fin 8 → BitVec 32) :
    Ctxt.Valuation packCtxt :=
  .cons s0 (.cons (words 0) (.cons (words 1) (.cons (words 2) (.cons (words 3)
    (.cons (words 4) (.cons (words 5) (.cons (words 6)
      (.cons (words 7) .nil))))))))

/-- The store-chain step: given a context with an `stackArr 32 8` at its head and
    a `reg 32` word `v` accessible, write `arr[i] := v`. `mkStore` builds the
    single `stackStore` `Expr` over a context `(reg 64 :: stackArr 32 8 :: rest)`
    (the index const at the head, the array beneath it), reading the word `v` from
    `rest` via the supplied (shifted) variable. -/
def mkIdxConst (i : Nat) {Γ : Ctxt jasminDialect} :
    Expr jasminDialect Γ (.reg 64) :=
  { op := .regConst 64 i, retTy_eq := rfl, args := .nil }

/-- One slot's store `Expr` over context `Γ` with the array var `va`, index var
    `vi`, value var `vv`. -/
def mkStore {Γ : Ctxt jasminDialect}
    (va : Ctxt.Var Γ (.stackArr 32 8)) (vi : Ctxt.Var Γ (.reg 64))
    (vv : Ctxt.Var Γ (.reg 32)) : Expr jasminDialect Γ (.stackArr 32 8) :=
  { op := .stackStore 32 8, retTy_eq := rfl,
    args := .cons va (.cons vi (.cons vv .nil)) }

/-! ### The store-chain over a uniform `stackArr`-headed context

To keep the de Bruijn bookkeeping mechanical, the pack body works over the
context `.stackArr 32 8 :: words`, threading the array at de Bruijn 0 and reading
each word from `words` (shifted under the freshly-bound index const + array).
`packTail wvars k` writes `arr[k.. ] := wvars[k..]` slot-by-slot, ending with
`ret here`. -/

/-- The store-chain body. Over a context `Γ = .stackArr 32 8 :: rest` with the
    array at de Bruijn 0 (`av`) and a resolver `getW : Fin 8 → Var Γ (reg 32)` for
    the 8 words, `packTail fuel start` writes `arr[start + j] := getW (start+j)`
    for `j < fuel`, then `ret` the array. Each step binds a `regConst 64 (start)`
    index and a `stackStore`, growing the context by `reg 64 :: stackArr 32 8 ::`;
    the resolver and array-var are shifted under those two fresh bindings. -/
def packTail {rest : Ctxt jasminDialect}
    (getW : Fin 8 → Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (JasminTy.reg 32))
    (av : Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (JasminTy.stackArr 32 8)) :
    (fuel start : Nat) →
    Com jasminDialect (JasminTy.stackArr 32 8 :: rest) (JasminTy.stackArr 32 8)
  | 0, _ => .ret av
  | fuel + 1, start =>
      -- bind the index const  (ctxt: reg 64 :: stackArr 32 8 :: rest)
      .var (mkIdxConst start)
      -- bind the store         (ctxt: stackArr 32 8 :: reg 64 :: stackArr 32 8 :: rest)
        (.var (mkStore av.there .here
                ((getW ⟨start % 8, Nat.mod_lt _ (by omega)⟩).there))
          -- recurse with everything shifted under the two fresh bindings; the new
          -- array is at de Bruijn 0.
          (packTail
            (rest := JasminTy.reg 64 :: JasminTy.stackArr 32 8 :: rest)
            (fun j => (getW j).there.there) .here fuel (start + 1)))

/-- **The product-output pack `Com`.** A single
    `Com jasminDialect packCtxt (.stackArr 32 8)` that writes the 8 next-state
    words into one array and **returns the array** — the whole 8-word state as one
    product value. The return type is the existing `stackArr` `Ty`; no `Com`-core
    change. -/
def packCom : Com jasminDialect packCtxt (.stackArr 32 8) :=
  packTail packWordVar packArrVar 8 0

/-- The array a store-chain over slots `start .. start+fuel-1` produces from a base
    array `base`, reading word values from `wval : Fin 8 → BitVec 32`. -/
def packFold (wval : Fin 8 → BitVec 32) (base : Fin 8 → BitVec 32) :
    (fuel start : Nat) → (Fin 8 → BitVec 32)
  | 0, _ => base
  | fuel + 1, start =>
      packFold wval (stackSet base start (wval ⟨start % 8, Nat.mod_lt _ (by omega)⟩))
        fuel (start + 1)

/-- One `mkStore` step's denotation is the functional update `stackSet` at the
    index var's `.toNat`. Pure unfolding (`rfl`). -/
theorem mkStore_denote {rest : Ctxt jasminDialect}
    (V : Ctxt.Valuation (JasminTy.reg 64 :: JasminTy.stackArr 32 8 :: rest))
    (av : Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (.stackArr 32 8))
    (wv : Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (.reg 32)) :
    (mkStore av.there Ctxt.Var.here wv.there).denote V
      = stackSet (av.there.lookup V)
          ((Ctxt.Var.here (Γ := JasminTy.stackArr 32 8 :: rest)
              (t := JasminTy.reg 64)).lookup V).toNat (wv.there.lookup V) := rfl

/-- `(BitVec.ofNat 64 start).toNat = start` for the small slot indices `< 8` (well
    within `2^64`). -/
theorem ofNat64_toNat_of_lt8 (start : Nat) (h : start < 8) :
    (BitVec.ofNat 64 start).toNat = start := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : start < 2 ^ 64)]

/-- **`packTail` denotes to the store-fold `packFold`.** Reducing the recursion
    one binding-pair at a time: the `start`-slot store is a `stackSet` at index
    `start` (`mkStore_denote` + `ofNat64_toNat_of_lt8`), and the two fresh bindings
    drop out of every word/array lookup. Proved by induction on `fuel`, with
    `start + fuel ≤ 8` so each materialized index is `< 8`. -/
theorem packTail_denote {rest : Ctxt jasminDialect}
    (getW : Fin 8 → Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (.reg 32))
    (av : Ctxt.Var (JasminTy.stackArr 32 8 :: rest) (.stackArr 32 8)) :
    (fuel start : Nat) → (hb : start + fuel ≤ 8) →
    (V : Ctxt.Valuation (JasminTy.stackArr 32 8 :: rest)) →
    (packTail getW av fuel start).denote V
      = packFold (fun j => (getW j).lookup V) (av.lookup V) fuel start
  | 0, _, _, _ => rfl
  | fuel + 1, start, hb, V => by
      have hlt : start < 8 := by omega
      -- unfold one recursion step
      show (Com.denote
        (.var (mkIdxConst start)
          (.var (mkStore av.there Ctxt.Var.here
                  ((getW ⟨start % 8, Nat.mod_lt _ (by omega)⟩).there))
            (packTail (fun j => (getW j).there.there) Ctxt.Var.here fuel (start + 1)))) V)
        = _
      rw [Com.denote_var]
      set V1 : Ctxt.Valuation (JasminTy.reg 64 :: JasminTy.stackArr 32 8 :: rest) :=
        V.extend ((mkIdxConst (Γ := JasminTy.stackArr 32 8 :: rest) start).denote V) with hV1
      rw [Com.denote_var, mkStore_denote]
      -- the index-const value is `BitVec.ofNat 64 start`
      have hidx : (Ctxt.Var.here (Γ := JasminTy.stackArr 32 8 :: rest)
          (t := JasminTy.reg 64)).lookup V1 = BitVec.ofNat 64 start := rfl
      rw [hidx, ofNat64_toNat_of_lt8 start hlt]
      -- recurse over the fresh valuation; the two bindings drop from lookups
      rw [packTail_denote (fun j => ((getW j).there.there)) Ctxt.Var.here fuel (start + 1)
        (by omega)]
      -- unfold the RHS `packFold` one step at `start`; both sides then match
      -- definitionally (the two fresh bindings peel off each word lookup; the head
      -- reads the store value; `start % 8 = start`).
      conv_rhs => rw [packFold]
      rfl

/-- The full 8-slot store-fold from any base array writes every slot, yielding the
    word vector `wval` exactly (the base is fully overwritten). -/
theorem packFold_full (wval base : Fin 8 → BitVec 32) :
    packFold wval base 8 0 = wval := by
  funext i
  fin_cases i <;>
    · simp only [packFold, stackSet]
      norm_num [Fin.ext_iff]

/-- **The pack `Com` denotes to the whole 8-word product.** For any scratch array
    `s0` and 8 words, `packCom` returns the array `fun i => words i` — the full
    8-word state assembled into one `stackArr 32 8` value (the scratch `s0` is
    fully overwritten). One `Com` value carrying all 8 words: the product output. -/
theorem packCom_denote (s0 : Fin 8 → BitVec 32) (words : Fin 8 → BitVec 32) :
    packCom.denote (packVal s0 words) = words := by
  have h := packTail_denote packWordVar packArrVar 8 0 (by omega) (packVal s0 words)
  rw [packCom]
  rw [h]
  -- the word resolver reads off `packVal`, the base is the scratch `s0`
  have hw : (fun j => (packWordVar j).lookup (packVal s0 words)) = words := by
    funext j; fin_cases j <;> rfl
  have hb : packArrVar.lookup (packVal s0 words) = s0 := rfl
  rw [hw, hb, packFold_full]

/-! ## §4  The product-output round tie: one `Com` ↦ the whole 8-word next state

Feeding `packCom` the 8 words of `sha256RoundVerified s K W` (as `stateArr`),
the single product-output `Com` denotes to the **whole next 8-word state** as one
array value — the engine returning its full `(a..h)`, no `a'`/`e'` split. -/

/-- **The product-output SHA-256 round, as one emitted `Com`.** With the next-
    state words supplied to `packCom`, the single `Com … (stackArr 32 8)` denotes
    to the whole verified next state `stateArr (sha256RoundVerified s kt wt)` —
    the full 8-word product in one `Com` value (`packCom_denote`). This is the
    front product-output capstone: the round engine returns its full state in one
    program, closing `CompileFromHaxSha256CompressTie`'s named residual without a
    `Com`-core change. -/
theorem sha256RoundProductCom_denote (s0 : Fin 8 → BitVec 32) (s : Sha256Working)
    (kt wt : BitVec 32) :
    packCom.denote (packVal s0 (stateArr (sha256RoundVerified s kt wt)))
      = stateArr (sha256RoundVerified s kt wt) :=
  packCom_denote s0 _

/-- The product-output round read back into a `Sha256Working` record is exactly the
    verified single round — the `Com`'s array return carries the whole state, with
    no field dropped. -/
theorem sha256RoundProductCom_arrState (s0 : Fin 8 → BitVec 32) (s : Sha256Working)
    (kt wt : BitVec 32) :
    arrState (packCom.denote (packVal s0 (stateArr (sha256RoundVerified s kt wt))))
      = sha256RoundVerified s kt wt := by
  rw [sha256RoundProductCom_denote, arrState_stateArr]

/-! ## §5  Folding the product-output round = the FIPS-180-4 whole compression

`roundProdFold` iterates the product-output round semantics `roundProdSem` over
the schedule. Reading it back is the spec-level `roundFold`; with the feed-forward
add it is the whole-block compression `sha256Compress` — the whole compression as
the iterate of ONE product-output `Com`, returning its full 8-word state each
round (rather than the spec-level fold of single-word scalar ties). -/

/-- Iterate the product-output round over rounds `0 .. n-1`, threading the whole
    8-word state array (the product the `Com` returns) — the array image of the
    spec-level `roundFold`. -/
def roundProdFold (K W : Nat → BitVec 32) (arr0 : Fin 8 → BitVec 32) :
    Nat → (Fin 8 → BitVec 32)
  | 0 => arr0
  | t + 1 => roundProdSem (K t) (W t) (roundProdFold K W arr0 t)

/-- The product-output fold over the 8-word array **is** the spec-level `roundFold`,
    viewed as a `stateArr`: no working-variable is dropped at any round — the whole
    state threads as the array product. -/
theorem roundProdFold_eq (K W : Nat → BitVec 32) (s0 : Sha256Working) (n : Nat) :
    roundProdFold K W (stateArr s0) n = stateArr (roundFold K W s0 n) := by
  induction n with
  | zero => rfl
  | succ t ih =>
      simp only [roundProdFold, roundFold, ih, roundProdSem_stateArr]

/-- Reading the product-output fold back into a record is the spec-level
    `roundFold`. -/
theorem roundProdFold_arrState (K W : Nat → BitVec 32) (s0 : Sha256Working) (n : Nat) :
    arrState (roundProdFold K W (stateArr s0) n) = roundFold K W s0 n := by
  rw [roundProdFold_eq, arrState_stateArr]

open CatCrypt.Crypto.SecureCompilation.ImpExprToThir (schedFold)

/-- **The whole 64-round SHA-256 compression is the iterate of the product-output
    round `Com`.** Folding the product-output round 64 times over the schedule,
    reading back, then the FIPS-180-4 feed-forward add of the initial state, equals
    the whole-block compression `CompileFromHaxSha256CompressTie.sha256Compress`.
    Each round is the single product-output `Com` returning its whole 8-word state
    (`sha256RoundProductCom_denote`); the schedule words are the front-expressed
    whole recurrence (`CompileFromHaxSha256CompressTie.wholeSchedule_denoteScalar`).
    So the compiled artifact is the **whole compression as one product-output round
    iterated**, not a spec-level fold of scalar single-word ties. Functional
    equality, not a security claim. -/
theorem wholeCompressProduct (K : Nat → BitVec 32) (s0 : Sha256Working)
    (seedW : Nat → BitVec 32) :
    let W := schedFold seedW 48
    let sN := arrState (roundProdFold K W (stateArr s0) 64)
    (⟨s0.a + sN.a, s0.b + sN.b, s0.c + sN.c, s0.d + sN.d,
      s0.e + sN.e, s0.f + sN.f, s0.g + sN.g, s0.h + sN.h⟩ : Sha256Working)
      = sha256Compress K s0 seedW := by
  intro W sN
  have hsN : sN = roundFold K (schedFold seedW 48) s0 64 :=
    roundProdFold_arrState K (schedFold seedW 48) s0 64
  rw [show sha256Compress K s0 seedW
        = { a := s0.a + (roundFold K (schedFold seedW 48) s0 64).a,
            b := s0.b + (roundFold K (schedFold seedW 48) s0 64).b,
            c := s0.c + (roundFold K (schedFold seedW 48) s0 64).c,
            d := s0.d + (roundFold K (schedFold seedW 48) s0 64).d,
            e := s0.e + (roundFold K (schedFold seedW 48) s0 64).e,
            f := s0.f + (roundFold K (schedFold seedW 48) s0 64).f,
            g := s0.g + (roundFold K (schedFold seedW 48) s0 64).g,
            h := s0.h + (roundFold K (schedFold seedW 48) s0 64).h } from rfl]
  rw [hsN]

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CompressProductTie
