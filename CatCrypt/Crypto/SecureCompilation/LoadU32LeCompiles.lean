/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.TExprToThir
public import CatCrypt.Crypto.SecureCompilation.TExprToThir
public meta import CatCrypt.Crypto.SecureCompilation.Generated.LoadU32LeTExpr
public import CatCrypt.Crypto.SecureCompilation.Generated.LoadU32LeTExpr

/-!
# A typed compile rooted in a real extraction (`load_u32_le`)

This module pushes the typed front (`TExprToThir.lean`) at a **real** hax
extraction — `load_u32_le` from `chacha20poly1305-hax`, parsed by hax-lean into
`loadU32LeTexpr : Hax.TExpr` (`Generated/LoadU32LeTExpr.lean`) — rather than the
hand-built σ₀/round components. The real extraction exercises three features the
clean-head hand-built components do not have:

1. **`#w`-suffixed op heads** (`BitOr#32`, `Shl#32`, `cast#32`) instead of the
   clean `BitXor`/`shift_left` heads;
2. a **width-coercion** `cast#32` (the byte-widen `(u32) bytes[i]`);
3. **array-index reads** `index[bytes, off + k]` over a `&[u8;32]` parameter at a
   runtime offset.

## What is proved here

* **Suffix-tolerance + `cast#w`** are handled by the front recognisers
  (`recogBinTy`/`recogShiftTy`/`recogCastTy`, `TExprToThir.lean`), spelled as
  flat string-literal disjuncts so the committed clean-head σ₀/round-component
  proofs short-circuit unchanged. Here they are demonstrated *firing* on the
  real `#32`/`cast#32` heads:
  - `loadU32LeModel` — the little-endian u32-combine
    `b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)` built with the **real** extraction
    heads `cast#32`/`Shl#32`/`BitOr#32` — compiles end-to-end through the
    committed `Thir → Com jasminDialect` back half and denotes to the LE-load
    formula (`loadU32LeModel_compiles`). Its op heads are exactly the
    suffixed/cast strings a real hax export emits.

## Scope: the runtime array-index read

The full literal `loadU32LeTexpr` translates to **`none`**: its byte reads are
`index[bytes, off + k]` where `bytes : &[u8; 32]` and `off : usize` is a
**runtime** value. This is a `Thir`-level gap, not a missing recogniser:

* `bytes` is a `&[u8; 32]` — a `stackArr 8 32`, **not** a `rW w` register. The
  front's `Atom`/`FState`/`frontCtxt`/`inputValuation` are a **homogeneous
  register file** (`replicate nIn (rW w)`); a stack-array-typed input has no slot.
* the index `off + k` is a **runtime register**, so the read is the dialect's
  `stackLoad w n : [stackArr w n, reg 64] → reg w`, not a compile-time
  `Atom.inp i`.

This is exactly the **heterogeneous-typing pass** that `ThirToComFront.lean` §9
already defers for the *store* (`stackStore`): *"a stack-array value is not a
`rW w` register, so threading a mutable `stackArr` through the homogeneous
register-file front (`thirToJasmin`) would require a heterogeneous typing pass.
That generalisation is deferred."* The same restriction applies to the array
*read* with a runtime index. The dialect has the `stackLoad` op; the front
(`Atom`/`Rhs`/`FState`) carries no `stackArr`-typed input alongside the register
file. An `index` *recogniser* alone would not suffice, because the recognised
read has no slot in the register-file `frontCtxt`.

The module thus proves the two recogniser features (suffix-tolerance, `cast`)
end-to-end on the real extraction heads; the heterogeneous stack-array input is
outside the front's scope.
-/

@[expose] public section

set_option autoImplicit false
-- The LE-combine denote reduces through the suffix-tolerant recognisers (each op
-- head a 5-7-way string-eq disjunction); the 10-binder chain is defeq-heavy.
set_option maxHeartbeats 800000

namespace CatCrypt.Crypto.SecureCompilation.LoadU32LeCompiles

open Hax
open CatCrypt.Crypto.SecureCompilation.TExprToThir
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  Scope: the real literal needs a heterogeneous stack input

The real `load_u32_le` extraction `loadU32LeTexpr` translates to `none`: its
byte reads are runtime-indexed array reads `index[bytes, off + k]` over a
`&[u8; 32]` parameter, which the homogeneous register-file front cannot model
(see the module docstring). -/

-- GAP (array-index read): the real `load_u32_le` body reads `index[bytes, off+k]`
-- over a `&[u8;32]` parameter. The front is a homogeneous `rW w` register file:
-- `bytes` is a `stackArr 8 32` with no `rW w` input slot, and `off+k` is a runtime
-- register. The dialect HAS `stackLoad w n : [stackArr w n, reg 64] → reg w`, but
-- `Atom`/`FState`/`frontCtxt`/`inputValuation` have no heterogeneous slot for the
-- array input — the same heterogeneous-typing pass `ThirToComFront` §9 defers for
-- the dual `stackStore`. An `index` recogniser alone does not suffice; the read
-- has no slot. (Not pinned as a `= none` theorem, since an array-read pass would
-- falsify it.) The model below
-- isolates the part the front CAN compile — the LE-combine over the four bytes, on
-- the real `cast#32`/`Shl#32`/`BitOr#32` heads.

/-! ## §2  The two recogniser features on the REAL extraction heads

The suffix-tolerant `#32` heads and the `cast#32` coercion fire on the real
extraction head strings (over atom arguments — the part the front *can* model).
`loadU32LeModel` is the little-endian u32-combine built with those real
heads (`cast#32`/`Shl#32`/`BitOr#32`), let-normalized to the ANF the front
consumes (every op argument an atom). It takes the four already-extracted bytes
`b0..b3` (the values `bytes[off + k]` of the full extraction)
bundled as `nIn = 4` inputs, each a `BitVec 8` value held in a `BitVec 32`
register (the `cast#32` widen is the identity at the working width). -/

/-- `u32` / `i32` as real `Hax.ImpType`s (the literal carries `i32` on the shift
    counts, `u32` on the values — matching the real `loadU32LeTexpr`). -/
abbrev tyU32 : Hax.ImpType := Hax.ImpType.uint .w32
abbrev tyS32 : Hax.ImpType := Hax.ImpType.sint .w32

/-- A typed `u32` var. -/
def vU32 (x : String) : Hax.TExpr := .mk (.var x) tyU32
/-- A typed `u32`-result application. -/
def appU32 (f : String) (args : List Hax.TExpr) : Hax.TExpr := .mk (.app f args) tyU32
/-- A typed `i32` literal (the shift counts in the real literal are `i32`). -/
def litS32 (n : Int) : Hax.TExpr := .mk (.lit (.int n)) tyS32
/-- The real `cast#32` widen head. -/
def castU32 (e : Hax.TExpr) : Hax.TExpr := appU32 "cast#32" [e]
/-- The real `Shl#32` left-shift head. -/
def shlU32 (e : Hax.TExpr) (k : Int) : Hax.TExpr := appU32 "Shl#32" [e, litS32 k]
/-- The real `BitOr#32` head. -/
def orU32 (a b : Hax.TExpr) : Hax.TExpr := appU32 "BitOr#32" [a, b]

/-- The little-endian u32 load `b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)`, built
    with the **real** `load_u32_le` extraction heads `cast#32`/`Shl#32`/`BitOr#32`,
    let-normalized to ANF (each op argument an atom). Inputs `b0..b3` are the four
    bytes `bytes[off + k]` would supply, bundled as `nIn = 4`. -/
def loadU32LeModel : Hax.TExpr :=
  .mk (.letBind "c0" (castU32 (vU32 "b0"))
   (.mk (.letBind "c1" (castU32 (vU32 "b1"))
    (.mk (.letBind "c2" (castU32 (vU32 "b2"))
     (.mk (.letBind "c3" (castU32 (vU32 "b3"))
      (.mk (.letBind "s1" (shlU32 (vU32 "c1") 8)
       (.mk (.letBind "s2" (shlU32 (vU32 "c2") 16)
        (.mk (.letBind "s3" (shlU32 (vU32 "c3") 24)
         (.mk (.letBind "o1" (orU32 (vU32 "c0") (vU32 "s1"))
          (.mk (.letBind "o2" (orU32 (vU32 "o1") (vU32 "s2"))
           (.mk (.letBind "r" (orU32 (vU32 "o2") (vU32 "s3"))
            (vU32 "r")) tyU32)) tyU32)) tyU32)) tyU32)) tyU32)) tyU32)) tyU32)) tyU32)) tyU32)) tyU32

/-- The model denotes (under the typed source semantics) to the little-endian
    u32-load formula `b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)` (the `cast#32`s
    are `BitVec.setWidth 32`, the identity at the working width). The proof goes
    purely through the new suffix-tolerant/`cast` recogniser reductions. -/
theorem loadU32LeModel_denote (I : Fin 4 → BitVec 32) :
    TExpr.denoteScalarT ["b0", "b1", "b2", "b3"] I loadU32LeModel (fun _ => none)
      = some (BitVec.setWidth 32 (inpGet I 0) |||
              (BitVec.setWidth 32 (inpGet I 1) <<< (8 : Nat)) |||
              (BitVec.setWidth 32 (inpGet I 2) <<< (16 : Nat)) |||
              (BitVec.setWidth 32 (inpGet I 3) <<< (24 : Nat))) := by
  simp (config := { maxSteps := 4000000 }) only [loadU32LeModel, castU32, shlU32, orU32, appU32, vU32, litS32,
    TExpr.denoteScalarT, TExpr.denoteAtomT, recogBinTy, recogShiftTy, recogCastTy,
    litNatT?, ShiftKind.apply, List.idxOf?, List.findIdx?,
    reduceIte, String.reduceEq, beq_iff_eq, Bool.or_eq_true]
  rfl

/-- The model lowers via the typed front — the real `cast#32`/`Shl#32`/`BitOr#32`
    heads are recognised (suffix-tolerance + `cast`), no clean-head needed. -/
theorem loadU32LeModel_lowers :
    (texprToThir ["b0", "b1", "b2", "b3"] loadU32LeModel).isSome := by native_decide

/-! ## §3  End-to-end: the real-head LE-combine compiles to the LE-load spec

`loadU32LeModel` compiles through the **committed** `Thir → Com jasminDialect`
back half (unchanged) and the lowered `Com`'s `BitVec 32` denotation is exactly
the little-endian u32-load formula — for the real extraction heads
`cast#32`/`Shl#32`/`BitOr#32`. The chain is `texprToThir_denoteScalarT` (typed
front, with the new recognisers) ∘ `thirToJasmin_denote` (committed back half),
identical in shape to the σ₀/round-component compiles. -/

/-- **`load_u32_le` little-endian combine, end-to-end from the typed front, on
    the REAL extraction heads.** There is a `Thir` `t` and a `Com jasminDialect`
    `c` such that the real-head LE-combine `loadU32LeModel` (built with
    `cast#32`/`Shl#32`/`BitOr#32`) translates to `t` via `texprToThir`, `t` lowers
    to `c` through the committed front, and `c`'s `BitVec 32` denotation is the
    little-endian u32-load `b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)` for every
    input. Its op heads are exactly the suffixed/cast strings a real hax
    export emits.
    (composition plumbing through the committed `thirToJasmin`.) -/
theorem loadU32LeModel_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 4 []) (rW 32)),
      texprToThir ["b0", "b1", "b2", "b3"] loadU32LeModel = some t ∧
      thirToJasmin [] (initFState 32 4) t = some c ∧
      ∀ (b0 b1 b2 b3 : BitVec 32),
        c.denote (inputValuation 32 4 ![b0, b1, b2, b3])
          = BitVec.setWidth 32 b0 |||
              (BitVec.setWidth 32 b1 <<< (8 : Nat)) |||
              (BitVec.setWidth 32 b2 <<< (16 : Nat)) |||
              (BitVec.setWidth 32 b3 <<< (24 : Nat)) := by
  set t := (texprToThir ["b0", "b1", "b2", "b3"] loadU32LeModel).get loadU32LeModel_lowers
    with ht_def
  have ht : texprToThir ["b0", "b1", "b2", "b3"] loadU32LeModel = some t :=
    (Option.some_get _).symm
  have hcSome : (thirToJasmin [] (initFState 32 4) t).isSome := by rw [ht_def]; native_decide
  set c := (thirToJasmin [] (initFState 32 4) t).get hcSome with hc_def
  have hc : thirToJasmin [] (initFState 32 4) t = some c := (Option.some_get _).symm
  refine ⟨t, c, ht, hc, ?_⟩
  intro b0 b1 b2 b3
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 4) ["b0", "b1", "b2", "b3"]
      ![b0, b1, b2, b3] loadU32LeModel (fun _ => none) ht
  have hfront := thirToJasmin_denote (w := 32) (nIn := 4) []
      ![b0, b1, b2, b3] t (LEnv.empty 32) (initFState 32 4)
      (inputValuation 32 4 ![b0, b1, b2, b3]) c (initAgree ![b0, b1, b2, b3]) hc
  have hspec :
      TExpr.denoteScalarT ["b0", "b1", "b2", "b3"] ![b0, b1, b2, b3] loadU32LeModel
          (fun _ => none)
        = some (BitVec.setWidth 32 b0 ||| (BitVec.setWidth 32 b1 <<< (8 : Nat)) |||
                (BitVec.setWidth 32 b2 <<< (16 : Nat)) |||
                (BitVec.setWidth 32 b3 <<< (24 : Nat))) := by
    have h := loadU32LeModel_denote ![b0, b1, b2, b3]
    simpa only [inpGet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.cons_val] using! h
  have hchain :
      some (BitVec.setWidth 32 b0 ||| (BitVec.setWidth 32 b1 <<< (8 : Nat)) |||
            (BitVec.setWidth 32 b2 <<< (16 : Nat)) |||
            (BitVec.setWidth 32 b3 <<< (24 : Nat)))
        = some (c.denote (inputValuation 32 4 ![b0, b1, b2, b3])) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

end CatCrypt.Crypto.SecureCompilation.LoadU32LeCompiles
