/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle

/-!
# The waist semantics at a leaf oracle

`semScalar` binds the destination of every opaque leaf call to `CryptoTy.default`.
`semScalarL ls` is the same semantics with the destination bound to the value of the
leaf oracle `ls : SemLeafSpec` at the leaf name, the destination type and the argument
values read from the environment; `semUL ls fuel` is `semU fuel` over `semScalarL ls`.
At the default oracle both are the existing semantics:
`semScalar = semScalarL defaultLeaf` and `semU fuel = semUL defaultLeaf fuel`.

`argVals`, `locNames`, `semCallNDestsL`, `semScalarL`, `semScalarL_default` and
`semScalar_eq_semScalarL` are declared in this namespace in
`Dialects.TranslateDialectScalarDenote`, next to `semScalar`, where the preservation
theorems at a leaf oracle (`translateDialectFull_denoteWith`,
`translateDialectControl_denote_ctlWith`) are stated over them.

Each leaf arm passes the oracle the name and the arguments of the `extCall` that
`translateDialectFull` emits for it:

| arm | leaf name | arguments |
|---|---|---|
| `RCall f dst args` | `f` | `args` |
| `RCallDstThreaded f dst args` | `f` | `dst :: args` |
| `RTupleLoad dst src i` | `"tupleLoad:i"` | `[src]` |
| `RSelect dst sel src0 src1`, slots other than words | `"select"` | `[sel, src0, src1]` |
| `RArrLoadLit dst src i`, other than a word read of a `TArr _ .TU64` | `"arrLoad:i"` | `[src]` |
| `RArrStoreLit arr i src`, other than a word write to a `TArr _ .TU64` | `"arrStore:i"` | `[arr, src]` |
| `RArrLoad dst src i`, other than a word read | `"arrLoadDyn"` | `[src, i]` |
| `RArrStore arr i src`, other than a word write | `"arrStoreDyn"` | `[arr, src, i]` |
| `RCallSwap f d1 d2 args` | `f`, twice | `args`, the second read after `d1` is written |
| `RCloneCall cv _ old f new args` | `"clone"`, then `f` | `[old]`, then `args` after `cv` is written |
| `RCallN f dests args` | `callNLeafName f i` per destination | `args`, read before each write |

The arguments are read with `argVals`, which drops unbound names; where the front
succeeds every argument is bound, and the list is the front's argument vector.

## Main definitions

* `semUL` — the unified waist semantics at a leaf oracle

## Main results

* `semUL_default`, `semU_eq_semUL` — the default oracle gives `semU`
* `semUL_leaf` — on a node that is not seq-like, `semUL` is `semScalarL`
* `semScalarL_rCall`, `semScalarL_rSelect_word`, `semScalarL_rSelect_leaf`,
  `semScalarL_rArrLoadLit_word`, `semScalarL_rArrLoadLit_leaf`,
  `semScalarL_rArrStoreLit_word`, `semScalarL_rArrStoreLit_leaf`,
  `semScalarL_rCallDstThreaded`, `semScalarL_rTupleLoad`, `semScalarL_rCallSwap`,
  `semScalarL_rCloneCall`, `semScalarL_rCallN` — the arm equations used by the ascent
* `argVals_upd_other`, `semCallNDestsL_other` — frame equations of the argument values and
  of the `RCallN` fold
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr callNLeafName)

/-- The unified waist semantics `semU` over `semScalarL ls`. -/
def semUL (ls : SemLeafSpec) (fuel : Nat) : LowCT → SEnvScalar → Option SEnvScalar
  | .RSeq c₁ c₂, env => (semUL ls fuel c₁ env).bind (fun e => semUL ls fuel c₂ e)
  | .RBlock body, env => semUL ls fuel body env
  | .RIfNz name thenBlk .RSkip, env =>
      semScalarCond (fun e => semUL ls fuel thenBlk e) (guardNz name) env
  | .RWhileNz name body, env =>
      semScalarWhile (fun e => semUL ls fuel body e) (guardNz name) fuel env
  | .RFor x N body, env =>
      semRForD (fun e => semUL ls fuel body e) x N env
  | c, env => semScalarL ls c env

/-- On a node that is not one of the combinator shapes, `semUL` is `semScalarL`. -/
theorem semUL_leaf (ls : SemLeafSpec) (fuel : Nat) (env : SEnvScalar) {c : LowCT}
    (h : isSeqLike c = false) : semUL ls fuel c env = semScalarL ls c env := by
  unfold semUL
  split <;> first | rfl | simp [isSeqLike] at h

/-- At the default oracle `semUL` is `semU`. -/
theorem semUL_default (fuel : Nat) : ∀ (c : LowCT) (env : SEnvScalar),
    semUL defaultLeaf fuel c env = semU fuel c env := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => intro env; simp only [semUL, semU, ih₁, ih₂]
  | RBlock body ih => intro env; simp only [semUL, semU, ih]
  | RWhileNz name body ih => intro env; simp only [semUL, semU, ih]
  | RFor x N body ih => intro env; simp only [semUL, semU, ih]
  | RIfNz name thenBr elseBr ihT _ =>
      intro env
      cases elseBr
      case RSkip => simp only [semUL, semU, ihT]
      all_goals
        rw [semUL_leaf _ _ _ rfl, semU_leaf _ _ rfl, semScalarL_default]
  | _ => intro env; rw [semUL_leaf _ _ _ rfl, semU_leaf _ _ rfl, semScalarL_default]

/-- `semU` is `semUL` at the default oracle. -/
theorem semU_eq_semUL (fuel : Nat) : semU fuel = semUL defaultLeaf fuel := by
  funext c env; exact (semUL_default fuel c env).symm

/-! ## Arm equations -/

/-- The leaf call `RCall` binds its destination to the oracle at its name and arguments. -/
theorem semScalarL_rCall (ls : SemLeafSpec) (fname : String) (dst : Located)
    (args : List Located) (env : SEnvScalar) :
    semScalarL ls (.RCall fname dst args) env =
      some (env.upd dst.locVar (t := encodeTy dst.locSrc)
        (ls fname (encodeTy dst.locSrc) (argVals env (locNames args)))) := rfl

/-- A select into a `u64` word from three bound words is `selectWord`. -/
theorem semScalarL_rSelect_word (ls : SemLeafSpec) (dst : Located) (sel : String)
    (src0 src1 : Located) (env : SEnvScalar) (s a c : BitVec 64) (hd : dst.locSrc = .TU64)
    (hs : env sel = some ⟨.sword 64, s⟩) (ha : env src0.locVar = some ⟨.sword 64, a⟩)
    (hc : env src1.locVar = some ⟨.sword 64, c⟩) :
    semScalarL ls (.RSelect dst sel src0 src1) env =
      some (env.upd dst.locVar (t := .sword 64) (selectWord s a c)) := by
  simp only [semScalarL, Located.locDst, hd, hs, ha, hc]

/-- A select outside the word case binds its destination to the oracle at `"select"`
    on the selector and the two sources. -/
theorem semScalarL_rSelect_leaf (ls : SemLeafSpec) (dst : Located) (sel : String)
    (src0 src1 : Located) (env : SEnvScalar)
    (hleaf : ∀ s a c : BitVec 64, dst.locSrc = .TU64 → env sel = some ⟨.sword 64, s⟩ →
      env src0.locVar = some ⟨.sword 64, a⟩ → env src1.locVar = some ⟨.sword 64, c⟩ → False) :
    semScalarL ls (.RSelect dst sel src0 src1) env =
      some (env.upd dst.locVar (t := encodeTy dst.locSrc)
        (ls "select" (encodeTy dst.locSrc) (argVals env (sel :: locNames [src0, src1])))) := by
  simp only [semScalarL]
  split
  · rename_i s a c hd hs ha hc
    exact (hleaf s a c hd hs ha hc).elim
  · rfl

/-- A literal-index word read of a bound `TArr _ .TU64` array is `memGetDyn`. -/
theorem semScalarL_rArrLoadLit_word (ls : SemLeafSpec) (dst src : Located) (idx : Nat)
    (env : SEnvScalar) (k n : Nat) (arr : Fin n → BitVec 64) (hd : dst.locSrc = .TU64)
    (hsrc : src.locSrc = .TArr k .TU64)
    (hs : env src.locVar = some ⟨.memref n, arr⟩) :
    semScalarL ls (.RArrLoadLit dst src idx) env =
      some (env.upd dst.locVar (t := .sword 64)
        (memGetDyn arr (BitVec.ofNat 64 idx).toNat)) := by
  simp only [semScalarL, Located.locDst, hd, hsrc, hs]

/-- A literal-index read outside the word case binds its destination to the oracle at
    `"arrLoad:idx"` and the source. -/
theorem semScalarL_rArrLoadLit_leaf (ls : SemLeafSpec) (dst src : Located) (idx : Nat)
    (env : SEnvScalar)
    (hleaf : ∀ (k n : Nat) (arr : Fin n → BitVec 64), dst.locSrc = .TU64 →
      src.locSrc = .TArr k .TU64 → env src.locVar = some ⟨.memref n, arr⟩ → False) :
    semScalarL ls (.RArrLoadLit dst src idx) env =
      some (env.upd dst.locVar (t := encodeTy dst.locSrc)
        (ls ("arrLoad:" ++ toString idx) (encodeTy dst.locSrc)
          (argVals env (locNames [src])))) := by
  simp only [semScalarL]
  split
  · rename_i k n arr hd hsrc hs
    exact (hleaf k n arr hd hsrc hs).elim
  · rfl

/-- A literal-index word write to a bound `TArr _ .TU64` array is `memSetDyn`. -/
theorem semScalarL_rArrStoreLit_word (ls : SemLeafSpec) (arr src : Located) (idx : Nat)
    (env : SEnvScalar) (k n : Nat) (a : Fin n → BitVec 64) (v : BitVec 64)
    (harr : arr.locSrc = .TArr k .TU64)
    (ha : env arr.locVar = some ⟨.memref n, a⟩) (hs : env src.locVar = some ⟨.sword 64, v⟩) :
    semScalarL ls (.RArrStoreLit arr idx src) env =
      some (env.upd arr.locVar (t := .memref n)
        (memSetDyn a (BitVec.ofNat 64 idx).toNat v)) := by
  simp only [semScalarL, Located.locDst, harr, ha, hs]

/-- A literal-index write outside the word case binds the array to the oracle at
    `"arrStore:idx"` on the array and the source. -/
theorem semScalarL_rArrStoreLit_leaf (ls : SemLeafSpec) (arr src : Located) (idx : Nat)
    (env : SEnvScalar)
    (hleaf : ∀ (k n : Nat) (a : Fin n → BitVec 64) (v : BitVec 64), arr.locSrc = .TArr k .TU64 →
      env arr.locVar = some ⟨.memref n, a⟩ → env src.locVar = some ⟨.sword 64, v⟩ → False) :
    semScalarL ls (.RArrStoreLit arr idx src) env =
      some (env.upd arr.locVar (t := encodeTy arr.locSrc)
        (ls ("arrStore:" ++ toString idx) (encodeTy arr.locSrc)
          (argVals env (locNames [arr, src])))) := by
  simp only [semScalarL]
  split
  · rename_i k n a v harr ha hs
    exact (hleaf k n a v harr ha hs).elim
  · rfl

/-- The destination-threaded leaf call binds its destination to the oracle at its name on
    the destination followed by the arguments. -/
theorem semScalarL_rCallDstThreaded (ls : SemLeafSpec) (fname : String) (dst : Located)
    (args : List Located) (env : SEnvScalar) :
    semScalarL ls (.RCallDstThreaded fname dst args) env =
      some (env.upd dst.locVar (t := encodeTy dst.locSrc)
        (ls fname (encodeTy dst.locSrc) (argVals env (locNames (dst :: args))))) := rfl

/-- The tuple component read binds its destination to the oracle at `"tupleLoad:idx"` on
    the source. -/
theorem semScalarL_rTupleLoad (ls : SemLeafSpec) (dst src : Located) (idx : Nat)
    (env : SEnvScalar) :
    semScalarL ls (.RTupleLoad dst src idx) env =
      some (env.upd dst.locVar (t := encodeTy dst.locSrc)
        (ls ("tupleLoad:" ++ toString idx) (encodeTy dst.locSrc)
          (argVals env (locNames [src])))) := rfl

/-- The two-destination call binds `dest1`, then `dest2`, to the oracle at its name on the
    arguments, the second read after the first write. -/
theorem semScalarL_rCallSwap (ls : SemLeafSpec) (fname : String) (dest1 dest2 : Located)
    (args : List Located) (env : SEnvScalar) :
    semScalarL ls (.RCallSwap fname dest1 dest2 args) env =
      some ((env.upd dest1.locVar (t := encodeTy dest1.locSrc)
          (ls fname (encodeTy dest1.locSrc) (argVals env (locNames args)))).upd
        dest2.locVar (t := encodeTy dest2.locSrc)
          (ls fname (encodeTy dest2.locSrc)
            (argVals (env.upd dest1.locVar (t := encodeTy dest1.locSrc)
              (ls fname (encodeTy dest1.locSrc) (argVals env (locNames args)))) (locNames args)))) :=
  rfl

/-- The clone-and-call node on a bound old destination binds the clone variable to the
    oracle at `"clone"` on the old value, then the new destination to the oracle at the
    inner name on the arguments. -/
theorem semScalarL_rCloneCall (ls : SemLeafSpec) (cv : String) (tt : TowerType)
    (oldDest : Located) (innerF : String) (newDest : Located) (args : List Located)
    (env : SEnvScalar) (cloneTy : CryptoTy) (old : ⟦cloneTy⟧)
    (hold : env oldDest.locVar = some ⟨cloneTy, old⟩) :
    semScalarL ls (.RCloneCall cv tt oldDest innerF newDest args) env =
      some ((env.upd cv (t := cloneTy) (ls "clone" cloneTy (argVals env [oldDest.locVar]))).upd
        newDest.locVar (t := encodeTy newDest.locSrc)
          (ls innerF (encodeTy newDest.locSrc)
            (argVals (env.upd cv (t := cloneTy) (ls "clone" cloneTy (argVals env [oldDest.locVar])))
              (locNames args)))) := by
  have h : argVals env [oldDest.locVar] = [⟨cloneTy, old⟩] := by simp [argVals, hold]
  rw [h]
  simp only [semScalarL, hold]

/-- The multi-destination call is the fold `semCallNDestsL` from index `0`. -/
theorem semScalarL_rCallN (ls : SemLeafSpec) (fname : String) (dests args : List Located)
    (env : SEnvScalar) :
    semScalarL ls (.RCallN fname dests args) env =
      some (semCallNDestsL ls fname args dests 0 env) := rfl

/-- The argument values are unchanged by a write to a name outside the argument list. -/
theorem argVals_upd_other (env : SEnvScalar) (y : String) {t : CryptoTy} (v : ⟦t⟧) :
    ∀ names : List String, y ∉ names → argVals (env.upd y v) names = argVals env names
  | [], _ => rfl
  | x :: xs, h => by
      have hxy : x ≠ y := fun hxy => h (hxy ▸ List.mem_cons_self)
      have ih := argVals_upd_other env y v xs (fun hm => h (List.mem_cons_of_mem _ hm))
      simp only [argVals, List.filterMap_cons] at ih ⊢
      rw [ih]
      simp [SEnvScalar.upd, hxy]

/-- The `RCallN` fold leaves every name outside the destinations unchanged. -/
theorem semCallNDestsL_other (ls : SemLeafSpec) (fname : String) (args : List Located) :
    ∀ (dests : List Located) (i : Nat) (env : SEnvScalar) (y : String),
      y ∉ locNames dests → semCallNDestsL ls fname args dests i env y = env y
  | [], _, _, _, _ => rfl
  | d :: rest, i, env, y, h => by
      have hyd : y ≠ d.locVar := fun hyd => h (by simp [locNames, hyd])
      have hyr : y ∉ locNames rest := fun hm => h (by simp [locNames] at hm ⊢; exact Or.inr hm)
      show semCallNDestsL ls fname args rest (i + 1) (env.upd d.locVar _) y = env y
      rw [semCallNDestsL_other ls fname args rest (i + 1) _ y hyr]
      simp [SEnvScalar.upd, hyd]

end CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
