/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapM
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainCall

/-!
# Raising the tagged field calls into the field dialect

`fieldRaiseStep` rewrites a structured program of `jasminDialect` whose field calls are
tagged heads (`Hax.FieldTag.fieldTag?`) into a structured program of the field dialect
`jasField` of `VIR/FieldChainDialect.lean`. Each `call` of a tagged head of the method `m`
at the modulus `p` that has a template body `fieldBody` becomes the block
`fromWords; op; toWords`:
the arguments are cast to the canonical field `pf p canon` (`fromWords p canon 64 k`), the
operation of `m` in `pfDialect` is applied, and the result is cast back to words
(`toWords p canon 64 k`). On registers (a modulus with a narrow template, or with a one-limb
record and no wide template) each register is first stored in an array of one word and the
result word is loaded back; on arrays (a modulus with a wide template) the casts act on the
arrays of `fieldLimbs p` words directly. The tagged heads and signatures raised are exactly
those `fieldBody` has a body for (`raiseBody_isSome`). A Montgomery head
(`Hax.FieldTag.fieldTagM?`) of the method `m` at an odd modulus `p < 2⁶⁴` and the radix `2^k`
is raised on registers at the representation `mont k`: the casts read and write stored
residues, so the operation on the values gives the Montgomery value `fieldValMont`
(`val_toRep_fieldOp_mont`, `wordBody_tableMont`), with the same events as at `canon`.

The step includes the program into `jasField` (`NFProg.map?` along the inclusion `liftJ` of
`jasminDialect` into `jasPf`, then `embed` into `jasField`), inlines the raised bodies with
`NFProg.inline?` at the library `raiseLib`, and refuses a result that keeps a `call` of a
field head. The call environment of `jasField` is `liftEnv E`, which answers a symbol at
injected types by `E` (`liftCall_liftV`).

The certificate `fieldRaiseCert` relates the semantics at `fieldEnv E`, in which a field
head is answered by the `u64` table, to the semantics at `liftEnv E`, with the injection of
valuations and results; a field value denotes in `ZMod p`, and on arguments the table
accepts each raised body returns the value of the table (`wordBody_table`,
`wordBody_tableMont`, `arrBody_table`). The field operations and the casts emit no event; a raised body on
registers emits the access at index `0` of its one-word array, a raised body on arrays
emits nothing (`raiseEv`), so two runs with equal source events have equal events after
the step (`fieldRaiseStep_leakRunC`).

The step is the first stage of the field dialect step `FieldDialectStep.fieldDialectStep`,
the seventh step of `extChainCore`.

## Main definitions

* `liftV`, `liftCall`, `liftEnvP`, `liftEnv`: valuations and call environments along
  `Sum.inl`.
* `liftJ`, `embed`: the inclusions `jasminDialect → jasPf` and `NFProg jasPf → NFProg jasField`.
* `wordBody`, `arrBody`, `raiseBody`, `raiseEv`, `raiseLib`: the raised bodies, their events
  and the inlining library.
* `fieldRaiseStep`, `fieldRaiseCert`: the chain stage and its certificate.

## Main results

* `map_leakRunMC`, `embed_leakRunMC`, `lift_denoteAt`: the inclusion keeps the results and the
  events.
* `wordBody_table`, `wordBody_tableMont`, `arrBody_table`: a raised body returns the value of
  the `u64` table.
* `raiseLib_sound`, `raiseLib_leakSound`: the library is sound for the denotation and for the
  leakage run.
* `raiseBody_isSome`: the raised heads are the heads `fieldBody` has a body for.
* `fieldRaiseStep_leakRunC`: equal source events give equal events after the step.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldRaise

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel opLeak)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum (castVar castArgs lookup_castVar
  lookupArgs_castArgs)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (forIterLeak whileIterLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open Ctxt (Var Valuation)

/-! ## 1. The trip counter and the branch bit of `jasPf` -/

/-- The trip counter of `jasPf` is the 64-bit register of `jasminDialect`. -/
instance : HasWord64 jasPf where
  word := .inl (JasminTy.reg 64)
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- The branch bit of `jasPf` is the 1-bit register of `jasminDialect`, read as `true`
    exactly at `1#1`. -/
instance : HasBoolBit jasPf where
  bit := .inl (JasminTy.reg 1)
  toBool := fun (b : BitVec 1) => decide (b = 1#1)

/-! ## 2. Valuations and call environments along `Sum.inl` -/

/-- The valuation of the injected context: the identity on every value. -/
def liftV {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as) :
    HVector (fun t => ⟦t⟧) (as.map (Sum.inl (β := PfTy))) :=
  transArgs Sum.inl (fun x => x) x

/-- The injected valuation is `mapValInl`. -/
theorem liftV_eq_mapValInl : ∀ {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as),
    liftV x = mapValInl (d := jasminDialect) (e := pfDialect) x
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (HVector.cons _) (liftV_eq_mapValInl xs)

/-- Stripping the tags of an injected valuation gives the valuation. -/
theorem unmapInl_liftV : ∀ {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as),
    unmapInl (d := jasminDialect) (e := pfDialect) (liftV x) = x
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (HVector.cons _) (unmapInl_liftV xs)

/-- The types of `jasminDialect` a list of injected types holds, or `none` when a type of
    `pfDialect` occurs. -/
def ofInl? : List (JasminTy ⊕ PfTy) → Option (List JasminTy)
  | [] => some []
  | .inl t :: as => (ofInl? as).map (t :: ·)
  | .inr _ :: _ => none

/-- An injected list of types is read back. -/
theorem ofInl?_map : ∀ as : List JasminTy, ofInl? (as.map Sum.inl) = some as
  | [] => rfl
  | t :: as => by simp [ofInl?, ofInl?_map as]

/-- A list read back is the injection of the result. -/
theorem map_inl_of_ofInl? : ∀ {as : List (JasminTy ⊕ PfTy)} {bs : List JasminTy},
    ofInl? as = some bs → bs.map Sum.inl = as
  | [], bs, h => by cases h; rfl
  | .inl t :: as, bs, h => by
      simp only [ofInl?, Option.map_eq_some_iff] at h
      obtain ⟨cs, hcs, rfl⟩ := h
      simp [map_inl_of_ofInl? hcs]
  | .inr _ :: _, _, h => by cases h

/-- A valuation carried along an equality of type lists. -/
def castV {as bs : List (JasminTy ⊕ PfTy)} (h : as = bs) (x : HVector (fun t => ⟦t⟧) as) :
    HVector (fun t => ⟦t⟧) bs :=
  h ▸ x

/-- The callee of the symbol `f` at injected types: the callee of `E` at the types of
    `jasminDialect` they inject, on the stripped arguments, with the injected results;
    no callee at a list of types in which a type of `pfDialect` occurs. -/
def liftCall (E : CallEnv jasminDialect) (f : String) (as rs : List (JasminTy ⊕ PfTy))
    (x : HVector (fun t => ⟦t⟧) as) : Option (HVector (fun t => ⟦t⟧) rs) :=
  match ha : ofInl? as, hr : ofInl? rs with
  | some as', some rs' =>
      (E.call f as' rs'
        (unmapInl (d := jasminDialect) (e := pfDialect)
          (castV (map_inl_of_ofInl? ha).symm x))).map
        fun y => castV (map_inl_of_ofInl? hr) (liftV y)
  | _, _ => none

/-- At injected types, `liftCall E` answers what `E` answers, injected. -/
theorem liftCall_liftV (E : CallEnv jasminDialect) (f : String) (as rs : List JasminTy)
    (x : HVector (fun t => ⟦t⟧) as) :
    liftCall E f (as.map Sum.inl) (rs.map Sum.inl) (liftV x) = (E.call f as rs x).map liftV := by
  unfold liftCall
  split
  · rename_i as' rs' ha hr
    rw [ofInl?_map] at ha hr
    cases ha
    cases hr
    simp only [castV, unmapInl_liftV]
  · rename_i h
    exact absurd (ofInl?_map as) (fun e => h _ _ e (ofInl?_map rs))

/-- The call environment of `jasPf` from a call environment of `jasminDialect`. -/
def liftEnvP (E : CallEnv jasminDialect) : CallEnv jasPf := ⟨liftCall E⟩

/-- The call environment of `jasField` from a call environment of `jasminDialect`. -/
def liftEnv (E : CallEnv jasminDialect) : CallEnv jasField := ⟨liftCall E⟩

/-- At a symbol that is no field head, `liftCall (fieldEnv E)` is `liftCall E`. -/
theorem liftCall_fieldEnv_of_none (E : CallEnv jasminDialect) {f : String}
    (h : _root_.Hax.FieldTag.fieldHeadB f = false) (as rs : List (JasminTy ⊕ PfTy))
    (x : HVector (fun t => ⟦t⟧) as) :
    liftCall (fieldEnv E) f as rs x = liftCall E f as rs x := by
  unfold liftCall
  split
  · rw [fieldEnv_of_none E h]
  · rfl

/-! ## 3. The lowering of `jasminDialect` into `jasPf` -/

/-- **The inclusion of `jasminDialect` into `jasPf`** as a partial block lowering: each
    expression becomes the one-binding block of its operation tagged `.inl`. -/
def liftJ : PartialBlockLowering jasminDialect jasPf where
  mapTy := Sum.inl
  mapCtx := List.map Sum.inl
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVarInl (e := pfDialect)
  lowerExprBlock? e :=
    some (.var ((inlLowering jasminDialect pfDialect).lowerExpr e) (.ret .here))

/-- The type map of `liftJ` keeps the trip-counter type and the bit type. -/
theorem liftJ_regionTypes : liftJ.RegionTypes := ⟨rfl, rfl⟩

/-- The variable leaf of `liftJ`. -/
theorem liftJ_varTransports :
    liftJ.VarTransports (fun x => x) (fun V => liftV V) := fun v V => by
  show (mapVarInl (e := pfDialect) v).lookup (liftV V) = v.lookup V
  rw [liftV_eq_mapValInl, lookup_mapVarInl]

/-- The binding leaf of `liftJ`. -/
theorem liftJ_mapValExtends :
    liftJ.MapValExtends (fun x => x) (fun V => liftV V) := fun _ _ => rfl

/-- The value transport of `liftJ` is the identity on the trip counter and the bit. -/
theorem liftJ_regionTransports :
    liftJ.RegionTransports liftJ_regionTypes (fun x => x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The block leaf of `liftJ`: a block denotes the value of its expression. -/
theorem liftJ_block {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t) blk
    (hb : liftJ.lowerExprBlock? e = some blk) (V : Valuation Γ) :
    blk.denote (liftV V) = e.denote V := by
  cases hb
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenote.denote (d := jasminDialect) op
      (unmapInl (Expr.lookupArgs (mapArgsInl (e := pfDialect) args) (liftV V))) = _
  rw [liftV_eq_mapValInl, lookupArgs_mapArgsInl]
  rfl

/-- The leakage leaf of `liftJ`: a block emits the events of its expression. -/
theorem liftJ_blockLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) blk (hb : liftJ.lowerExprBlock? e = some blk)
    (V : Valuation Γ) :
    ComLevelCheck.Com.ctLeak (sumLeak M pfLeakModel) blk (liftV V) =
      ComLevelCheck.Expr.ctLeak M e V := by
  cases hb
  obtain ⟨op, rfl, args⟩ := e
  show opLeak (sumLeak M pfLeakModel) (.inl op)
      (Expr.lookupArgs (mapArgsInl (e := pfDialect) args) (liftV V)) ++ [] =
    opLeak M op (Expr.lookupArgs args V)
  rw [List.append_nil, opLeak_inl, liftV_eq_mapValInl, lookupArgs_mapArgsInl]

/-- **The inclusion keeps the leakage run.** A program `map?` returns along `liftJ` runs at
    `liftEnvP E` from the injected valuation to the injected results and to the events of
    the source run at `E`. -/
theorem map_leakRunMC (M : LeakModel jasminDialect) (E : CallEnv jasminDialect) (fuel : Nat)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    {q : NFProg jasPf (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hq : NFProg.map? liftJ liftJ_regionTypes p (fun v => v) = some q) (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRunMC (sumLeak M pfLeakModel) (liftEnvP E) fuel q (liftV V) =
      (Dialects.NFLeak.NFProg.leakRunMC M E fuel p V).map fun r => (liftV r.1, r.2) :=
  NFProg.map?_leakRunMC liftJ (fun x => x) (fun V => liftV V) M (sumLeak M pfLeakModel)
    liftJ_regionTypes (fun _ => True) liftJ_varTransports
    (fun e _ blk hb V => liftJ_block e blk hb V) (fun e _ blk hb V => liftJ_blockLeak M e blk hb V)
    liftJ_mapValExtends liftJ_regionTransports E (liftEnvP E) fuel p
    (NFProg.covered_of_forall _ (fun _ => trivial) p)
    (fun f as rs x _ => liftCall_liftV E f as rs x) (fun v => v) V (liftV V)
    (FieldDialectBlockDescent.pullV_id _) q hq

/-! ## 4. The inclusion of `NFProg jasPf` into `NFProg jasField` -/

/-- An expression of `jasPf` as an expression of `jasField`: the operation tagged `.inl`,
    the arguments unchanged. -/
def embedPfExpr {Γ : Ctxt jasPf} {t : jasPf.Ty} (e : Expr jasPf Γ t) : Expr jasField Γ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := castArgs e.args

/-- A program of `jasPf` as a program of `jasField`: every let-bound operation tagged `.inl`,
    the regions and calls kept. -/
def embed : {Γ : Ctxt jasPf} → {ts : List jasPf.Ty} → NFProg jasPf Γ ts →
    NFProg jasField Γ ts
  | _, _, .ret vs => .ret (castArgs vs)
  | _, _, .var e k => .var (embedPfExpr e) (embed k)
  | _, _, .forLoop count inits body k =>
      .forLoop (castVar count) (castArgs inits) (embed body) (embed k)
  | _, _, .ifThenElse cond thn els k =>
      .ifThenElse (castVar cond) (embed thn) (embed els) (embed k)
  | _, _, .whileLoop inits body k => .whileLoop (castArgs inits) (embed body) (embed k)
  | _, _, .call f args k => .call f (castArgs args) (embed k)

/-- An included expression denotes as the expression. -/
theorem embedPfExpr_denoteM {Γ : Ctxt jasPf} {t : jasPf.Ty} (e : Expr jasPf Γ t)
    (V : Valuation Γ) :
    (embedPfExpr e).denoteM (M := Option) V = e.denoteM (M := Option) V := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenoteM.denoteM (d := jasField) (M := Option) (.inl op)
      (Expr.lookupArgs (d := jasField) (castArgs args) V) = _
  rw [lookupArgs_castArgs args V]
  rfl

/-- The readings of values under `jasFieldLeak M` are those under `sumLeak M pfLeakModel`. -/
theorem valsNat_jasFieldLeak (M : LeakModel jasminDialect) :
    ∀ {tys : List (JasminTy ⊕ PfTy)} (vals : HVector (fun t => ⟦t⟧) tys),
      ComLevelCheck.valsNat (jasFieldLeak M) vals =
        ComLevelCheck.valsNat (sumLeak M pfLeakModel) vals
  | [], .nil => rfl
  | _ :: _, .cons _ vs => congrArg (List.cons _) (valsNat_jasFieldLeak M vs)

/-- An included expression emits the events of the expression. -/
theorem embedPfExpr_ctLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasPf} {t : jasPf.Ty}
    (e : Expr jasPf Γ t) (V : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak M) (embedPfExpr e) V =
      ComLevelCheck.Expr.ctLeak (sumLeak M pfLeakModel) e V := by
  show opLeak (jasFieldLeak M) (.inl e.op)
      (Expr.lookupArgs (d := jasField) (castArgs e.args) V) = _
  rw [lookupArgs_castArgs e.args V]
  unfold ComLevelCheck.Expr.ctLeak opLeak
  rw [valsNat_jasFieldLeak]
  rfl

/-- The append of two vectors over the types of `jasField` is their append over the types
    of `jasPf`. -/
theorem hvAppend_jasField {f : (JasminTy ⊕ PfTy) → Type} :
    ∀ {xs ys : List (JasminTy ⊕ PfTy)} (A : HVector f xs) (B : HVector f ys),
      hvAppend (d := jasField) A B = hvAppend (d := jasPf) A B
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons a A, B => congrArg (HVector.cons a) (hvAppend_jasField A B)

/-- The counted iteration with events of `jasField` is that of `jasPf`. -/
theorem forIterLeak_jasField {cs : List (JasminTy ⊕ PfTy)}
    (step : Nat → Valuation (d := jasPf) cs →
      Option (Valuation (d := jasPf) cs × List CTLeak)) :
    ∀ (is : List Nat) (acc : Valuation (d := jasPf) cs),
      forIterLeak (d := jasField) step is acc = forIterLeak (d := jasPf) step is acc
  | [], _ => rfl
  | i :: is, acc => by
      show ((step i acc).bind fun r =>
          (forIterLeak (d := jasField) step is r.1).map fun q => (q.1, r.2 ++ q.2))
        = ((step i acc).bind fun r =>
          (forIterLeak (d := jasPf) step is r.1).map fun q => (q.1, r.2 ++ q.2))
      simp only [forIterLeak_jasField step is]

/-- The exit-flag iteration with events of `jasField` is that of `jasPf`. -/
theorem whileIterLeak_jasField {cs : List (JasminTy ⊕ PfTy)}
    (step : Valuation (d := jasPf) cs →
      Option (Valuation (d := jasPf) (HasBitType.bit (d := jasPf) :: cs) × List CTLeak)) :
    ∀ (n : Nat) (acc : Valuation (d := jasPf) cs),
      whileIterLeak (d := jasField) step n acc = whileIterLeak (d := jasPf) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := jasPf) r.1.head then
            (whileIterLeak (d := jasField) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
        = ((step acc).bind fun r =>
          if HasBoolBit.toBool (d := jasPf) r.1.head then
            (whileIterLeak (d := jasPf) step n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
      simp only [whileIterLeak_jasField step n]

/-- **The inclusion keeps the leakage run**: at call environments of `jasField` and `jasPf`
    with the same callees, an included program runs to the results and the events of the
    program. -/
theorem embed_leakRunMC (M : LeakModel jasminDialect)
    (c : (f : String) → (as rs : List (JasminTy ⊕ PfTy)) → HVector (fun t => ⟦t⟧) as →
      Option (HVector (fun t => ⟦t⟧) rs))
    (fuel : Nat) {Γ : Ctxt jasPf} {ts : List jasPf.Ty} (p : NFProg jasPf Γ ts)
    (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) (⟨c⟩ : CallEnv jasField) fuel
        (embed p) V =
      Dialects.NFLeak.NFProg.leakRunMC (sumLeak M pfLeakModel) (⟨c⟩ : CallEnv jasPf) fuel
        p V := by
  induction p with
  | ret vs => exact congrArg (fun x => some (x, [])) (lookupArgs_castArgs vs V)
  | var e k ih =>
      simp only [embed, Dialects.NFLeak.NFProg.leakRunMC, embedPfExpr_denoteM, ih,
        embedPfExpr_ctLeak]
      rfl
  | forLoop count inits body k ihb ihk =>
      simp only [embed, Dialects.NFLeak.NFProg.leakRunMC, ihb, ihk, lookupArgs_castArgs,
        lookup_castVar, hvAppend_jasField, forIterLeak_jasField]
      rfl
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [embed, Dialects.NFLeak.NFProg.leakRunMC, iht, ihe, ihk, lookup_castVar,
        hvAppend_jasField]
      rfl
  | whileLoop inits body k ihb ihk =>
      simp only [embed, Dialects.NFLeak.NFProg.leakRunMC, ihb, ihk, lookupArgs_castArgs,
        hvAppend_jasField, whileIterLeak_jasField]
  | call f args k ih =>
      simp only [embed, Dialects.NFLeak.NFProg.leakRunMC, ih, lookupArgs_castArgs,
        hvAppend_jasField]

/-! ## 5. The raised bodies of the tagged heads -/

/-- The 64-bit register of `jasField`. -/
abbrev wT : JasminTy ⊕ PfTy := .inl (.reg 64)

/-- The array of `k` words of `jasField`. -/
abbrev aT (k : Nat) : JasminTy ⊕ PfTy := .inl (.stackArr 64 k)

/-- The field type at the modulus `p` and the representation `r`, canonical by default. -/
abbrev fT (p : Nat) (r : FieldRepr := .canon) : JasminTy ⊕ PfTy := .inr (.pf p r)

/-- The fresh array of one word. -/
def zeroE {Γ : Ctxt jasField} : Expr jasField Γ (aT 1) :=
  ⟨.inl (.inl (.stackZero 64 1)), rfl, .nil⟩

/-- The store of the register `a` at index `0` of the array `z` of one word. -/
def storeE {Γ : Ctxt jasField} (z : Var Γ (aT 1)) (a : Var Γ wT) : Expr jasField Γ (aT 1) :=
  ⟨.inl (.inl (.stackStoreImm 64 1 0)), rfl, .cons z (.cons a .nil)⟩

/-- The cast of `k` words to the field at `p` in the representation `r`. -/
def fromE (p k : Nat) {Γ : Ctxt jasField} (a : Var Γ (aT k)) (r : FieldRepr := .canon) :
    Expr jasField Γ (fT p r) :=
  ⟨.inr (.fromWords p r 64 k), rfl, .cons a .nil⟩

/-- The cast of a field value at `p` in the representation `r` to `k` words. -/
def toE (p k : Nat) {Γ : Ctxt jasField} {r : FieldRepr} (x : Var Γ (fT p r)) :
    Expr jasField Γ (aT k) :=
  ⟨.inr (.toWords p r 64 k), rfl, .cons x .nil⟩

/-- The register constant `0`. -/
def constE {Γ : Ctxt jasField} : Expr jasField Γ wT :=
  ⟨.inl (.inl (.regConst 64 0)), rfl, .nil⟩

/-- The load of the word at index `i` of an array of one word. -/
def loadE {Γ : Ctxt jasField} (z : Var Γ (aT 1)) (i : Var Γ wT) : Expr jasField Γ wT :=
  ⟨.inl (.inl (.stackLoad 64 1)), rfl, .cons z (.cons i .nil)⟩

/-- The operation of `pfDialect` of a method at the representation `r`; a method with one
    argument reads `x`. -/
def opE (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat) {Γ : Ctxt jasField} {r : FieldRepr}
    (x y : Var Γ (fT p r)) : Expr jasField Γ (fT p r) :=
  match m with
  | .add => ⟨.inl (.inr (.add p r)), rfl, .cons x (.cons y .nil)⟩
  | .sub => ⟨.inl (.inr (.sub p r)), rfl, .cons x (.cons y .nil)⟩
  | .mul => ⟨.inl (.inr (.mul p r)), rfl, .cons x (.cons y .nil)⟩
  | .neg => ⟨.inl (.inr (.neg p r)), rfl, .cons x .nil⟩
  | .square => ⟨.inl (.inr (.square p r)), rfl, .cons x .nil⟩
  | .double => ⟨.inl (.inr (.double p r)), rfl, .cons x .nil⟩

/-- The tail of a raised body on registers: the field value `x` written as one word and
    read back. -/
def wordTail {Γ : Ctxt jasField} (p : Nat) {r : FieldRepr} (x : Var Γ (fT p r)) :
    NFProg jasField Γ [wT] :=
  .var (toE p 1 x) <| .var constE <| .var (loadE (.there .here) .here) <| .ret (.cons .here .nil)

/-- The raised body of a method with two arguments on registers: each register stored in
    an array of one word and cast to the field at the representation `r`, the operation, and
    `wordTail`. -/
def wordBody2 (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat) (r : FieldRepr := .canon) :
    NFProg jasField [wT, wT] [wT] :=
  .var zeroE <| .var (storeE .here (.there .here)) <|
    .var (storeE (.there .here) (.there (.there (.there .here)))) <|
    .var (fromE p 1 (.there .here) r) <| .var (fromE p 1 (.there .here) r) <|
    .var (opE m p (.there .here) .here) <| wordTail p .here

/-- The raised body of a method with one argument on registers. -/
def wordBody1 (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat) (r : FieldRepr := .canon) :
    NFProg jasField [wT] [wT] :=
  .var zeroE <| .var (storeE .here (.there .here)) <| .var (fromE p 1 .here r) <|
    .var (opE m p .here .here) <| wordTail p .here

/-- The raised body of a method with two arguments on arrays of `k` words. -/
def arrBody2 (m : _root_.Hax.FieldTag.FieldMethod) (p k : Nat) (r : FieldRepr := .canon) :
    NFProg jasField [aT k, aT k] [aT k] :=
  .var (fromE p k .here r) <| .var (fromE p k (.there (.there .here)) r) <|
    .var (opE m p (.there .here) .here) <| .var (toE p k .here) <| .ret (.cons .here .nil)

/-- The raised body of a method with one argument on arrays of `k` words. -/
def arrBody1 (m : _root_.Hax.FieldTag.FieldMethod) (p k : Nat) (r : FieldRepr := .canon) :
    NFProg jasField [aT k] [aT k] :=
  .var (fromE p k .here r) <| .var (opE m p .here .here) <| .var (toE p k .here) <|
    .ret (.cons .here .nil)

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (wordSig wideSig wordNats wideArrs
  wideTemplateOf montWordOf montWordOf_p)

/-- **The raised body of a method on registers** at the representation `r`: at the
    signature `wordSig m` injected. -/
def wordBody (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat) (r : FieldRepr := .canon) :
    NFProg jasField ((wordSig m).map Sum.inl) [wT] :=
  match m with
  | .add => wordBody2 .add p r
  | .sub => wordBody2 .sub p r
  | .mul => wordBody2 .mul p r
  | .neg => wordBody1 .neg p r
  | .square => wordBody1 .square p r
  | .double => wordBody1 .double p r

/-- **The raised body of a method on arrays of `k` words** at the representation `r`: at the
    signature `wideSig k m` injected. -/
def arrBody (m : _root_.Hax.FieldTag.FieldMethod) (p k : Nat) (r : FieldRepr := .canon) :
    NFProg jasField ((wideSig k m).map Sum.inl) [aT k] :=
  match m with
  | .add => arrBody2 .add p k r
  | .sub => arrBody2 .sub p k r
  | .mul => arrBody2 .mul p k r
  | .neg => arrBody1 .neg p k r
  | .square => arrBody1 .square p k r
  | .double => arrBody1 .double p k r

/-! ## 6. The runs of the raised bodies -/

open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (fieldOp)

/-- The operation of a method denotes `fieldOp`. -/
theorem opE_denoteM (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat) {Γ : Ctxt jasField}
    {r : FieldRepr} (x y : Var Γ (fT p r)) (V : Valuation Γ) :
    (opE m p x y).denoteM (M := Option) V = some (fieldOp m (x.lookup V) (y.lookup V)) := by
  cases m <;> rfl

/-- The operation of a method emits no event. -/
theorem opE_ctLeak (M : LeakModel jasminDialect) (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat)
    {Γ : Ctxt jasField} {r : FieldRepr} (x y : Var Γ (fT p r)) (V : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak M) (opE m p x y) V = [] := by
  cases m <;> exact jasFieldLeak_ctLeak_pf M _ _ rfl V

/-- The leakage run of a binding whose expression succeeds with `x` and emits `l`. -/
theorem leakRunMC_var_of (M : LeakModel jasminDialect) (E : CallEnv jasField) (fuel : Nat)
    {Γ : Ctxt jasField} {t : jasField.Ty} {ts : List jasField.Ty} (e : Expr jasField Γ t)
    (k : NFProg jasField (t :: Γ) ts) (V : Valuation Γ) (x : ⟦t⟧) (l : List CTLeak)
    (hx : e.denoteM (M := Option) V = some x)
    (hl : ComLevelCheck.Expr.ctLeak (jasFieldLeak M) e V = l) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E fuel (.var e k) V =
      (Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E fuel k (V.extend x)).map
        fun r => (r.1, l ++ r.2) := by
  simp only [Dialects.NFLeak.NFProg.leakRunMC, hx, Option.bind_some]
  rw [← hl]

/-- The head variable reads the head value. -/
@[simp] theorem lookup_here_cons_jasField {Γ : Ctxt jasField} {t : jasField.Ty} (x : ⟦t⟧)
    (V : Valuation Γ) : (Var.here : Var (t :: Γ) t).lookup (HVector.cons x V) = x := rfl

/-- A shifted variable reads in the tail. -/
@[simp] theorem lookup_there_cons_jasField {Γ : Ctxt jasField} {s t : jasField.Ty} (v : Var Γ t)
    (x : ⟦s⟧) (V : Valuation Γ) : (Var.there v : Var (s :: Γ) t).lookup (HVector.cons x V) =
      v.lookup V := rfl

section Exprs

variable {Γ : Ctxt jasField} (V : Valuation Γ)

/-- The fresh array is the zero array. -/
@[simp] theorem zeroE_denoteM : (zeroE (Γ := Γ)).denoteM (M := Option) V =
    some (fun _ => (0 : BitVec 64)) := rfl

/-- The store updates index `0`. -/
@[simp] theorem storeE_denoteM (z : Var Γ (aT 1)) (a : Var Γ wT) :
    (storeE z a).denoteM (M := Option) V =
      some (stackSet (n := 1) (z.lookup V) 0 (a.lookup V)) := rfl

/-- The cast from words is `fromWordsF`. -/
@[simp] theorem fromE_denoteM (p k : Nat) (a : Var Γ (aT k)) (r : FieldRepr) :
    (fromE p k a r).denoteM (M := Option) V = fromWordsF p r 64 k (a.lookup V) := rfl

/-- The cast to words is `toWordsF`. -/
@[simp] theorem toE_denoteM (p k : Nat) {r : FieldRepr} (x : Var Γ (fT p r)) :
    (toE p k x).denoteM (M := Option) V = some (toWordsF p r 64 k (x.lookup V)) := rfl

/-- The register constant is the word `0`. -/
@[simp] theorem constE_denoteM : (constE (Γ := Γ)).denoteM (M := Option) V =
    some (BitVec.ofNat 64 0) := rfl

/-- The load reads the array at its index. -/
@[simp] theorem loadE_denoteM (z : Var Γ (aT 1)) (i : Var Γ wT) :
    (loadE z i).denoteM (M := Option) V = some (stackGet (z.lookup V) (i.lookup V).toNat) := rfl

variable {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
include hV

/-- The fresh array emits no event. -/
theorem zeroE_ctLeak :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak (jLeakModel Pj)) (zeroE (Γ := Γ)) V = [] :=
  ComLevelCheck.Expr.ctLeak_of_quiet _ _ (show (jasFieldLeak (jLeakModel Pj)).kind
    (.inl (.inl (.stackZero 64 1))) = .quiet from by
      rw [jasFieldLeak_kind_jasmin]
      exact Dialects.JasminComLLeak.jKind_stackZero Pj 64 1 (hV _)) V

/-- The constant-index store emits no event. -/
theorem storeE_ctLeak (z : Var Γ (aT 1)) (a : Var Γ wT) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak (jLeakModel Pj)) (storeE z a) V = [] :=
  ComLevelCheck.Expr.ctLeak_of_quiet _ _ (show (jasFieldLeak (jLeakModel Pj)).kind
    (.inl (.inl (.stackStoreImm 64 1 0))) = .quiet from by
      rw [jasFieldLeak_kind_jasmin]
      exact Dialects.JasminComLLeak.jKind_stackStoreImm Pj 64 1 0 (hV _)) V

/-- The register constant emits no event. -/
theorem constE_ctLeak :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak (jLeakModel Pj)) (constE (Γ := Γ)) V = [] :=
  ComLevelCheck.Expr.ctLeak_of_quiet _ _ (show (jasFieldLeak (jLeakModel Pj)).kind
    (.inl (.inl (.regConst 64 0))) = .quiet from by
      rw [jasFieldLeak_kind_jasmin]
      simp only [jLeakModel, Dialects.JasminComLLeak.jKind, hV]) V

omit hV in
/-- The load emits the access at its index. -/
theorem loadE_ctLeak (z : Var Γ (aT 1)) (i : Var Γ wT) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak (jLeakModel Pj)) (loadE z i) V =
      [.addr "" (((i.lookup V).toNat : Nat) : Int)] := rfl

end Exprs

/-- The cast from words emits no event. -/
theorem fromE_ctLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasField} (p k : Nat)
    (a : Var Γ (aT k)) (r : FieldRepr) (V : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak M) (fromE p k a r) V = [] :=
  jasFieldLeak_ctLeak_cast M _ _ rfl V

/-- The cast to words emits no event. -/
theorem toE_ctLeak (M : LeakModel jasminDialect) {Γ : Ctxt jasField} (p k : Nat)
    {r : FieldRepr} (x : Var Γ (fT p r)) (V : Valuation Γ) :
    ComLevelCheck.Expr.ctLeak (jasFieldLeak M) (toE p k x) V = [] :=
  jasFieldLeak_ctLeak_cast M _ _ rfl V

/-- The cast at the representation `r` of the array of one word holding `a < p` is the value
    of the stored residue `a`. -/
theorem fromWordsF_one {p : Nat} (r : FieldRepr) (a : BitVec 64) (ha : a.toNat < p) :
    fromWordsF p r 64 1 (stackSet (fun _ => (0 : BitVec 64)) 0 a) =
      some (r.ofRep ((a.toNat : Nat) : ZMod p)) := by
  simp [fromWordsF, wordsVal, stackSet, ha]

/-- The word at index `0` of the one-word cast of a field value at the representation `r`
    is the representative of its stored residue. -/
theorem stackGet_toWordsF_one {p : Nat} (r : FieldRepr) (x : ZMod p) :
    stackGet (toWordsF p r 64 1 x) (BitVec.ofNat 64 0).toNat =
      BitVec.ofNat 64 (r.toRep x).val := by
  simp [toWordsF, wordsOf, stackGet]

/-- **The run of the raised body of a method with two arguments on registers** at the
    representation `r`: on registers below `p`, the word of the stored residue of the value
    of the method on the values of the registers, with one memory access at index `0`. -/
theorem wordBody2_leakRunMC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasField) (fuel : Nat) (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat)
    (r : FieldRepr) (a b : BitVec 64) (ha : a.toNat < p) (hb : b.toNat < p) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E fuel (wordBody2 m p r)
        (.cons a (.cons b .nil)) =
      some (.cons (BitVec.ofNat 64 (r.toRep (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
        (r.ofRep ((b.toNat : Nat) : ZMod p)))).val) .nil, [.addr "" 0]) := by
  have hab := fromWordsF_one (p := p) r a ha
  have hbb := fromWordsF_one (p := p) r b hb
  unfold wordBody2 wordTail
  rw [leakRunMC_var_of (t := aT 1) (x := fun _ => 0) (l := []),
    leakRunMC_var_of (t := aT 1) (x := stackSet (n := 1) (fun _ => 0) 0 a) (l := []),
    leakRunMC_var_of (t := aT 1) (x := stackSet (n := 1) (fun _ => 0) 0 b) (l := []),
    leakRunMC_var_of (t := fT p r) (x := r.ofRep ((a.toNat : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p r) (x := r.ofRep ((b.toNat : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p r) (x := fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
      (r.ofRep ((b.toNat : Nat) : ZMod p))) (l := []),
    leakRunMC_var_of (t := aT 1) (x := toWordsF p r 64 1
      (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p)) (r.ofRep ((b.toNat : Nat) : ZMod p))))
      (l := []),
    leakRunMC_var_of (t := wT) (x := BitVec.ofNat 64 0) (l := []),
    leakRunMC_var_of (t := wT) (x := BitVec.ofNat 64
      (r.toRep (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
        (r.ofRep ((b.toNat : Nat) : ZMod p)))).val)
      (l := [.addr "" 0])]
  all_goals first
    | rfl
    | exact hab
    | exact hbb
    | exact zeroE_ctLeak _ hV
    | exact storeE_ctLeak _ hV _ _
    | exact constE_ctLeak _ hV
    | exact fromE_ctLeak _ _ _ _ _ _
    | exact toE_ctLeak _ _ _ _ _
    | exact opE_ctLeak _ _ _ _ _ _
    | exact opE_denoteM _ _ _ _ _
    | exact congrArg some (stackGet_toWordsF_one _ _)

/-- **The run of the raised body of a method with one argument on registers** at the
    representation `r`. -/
theorem wordBody1_leakRunMC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasField) (fuel : Nat) (m : _root_.Hax.FieldTag.FieldMethod) (p : Nat)
    (r : FieldRepr) (a : BitVec 64) (ha : a.toNat < p) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E fuel (wordBody1 m p r)
        (.cons a .nil) =
      some (.cons (BitVec.ofNat 64 (r.toRep (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
        (r.ofRep ((a.toNat : Nat) : ZMod p)))).val) .nil, [.addr "" 0]) := by
  have hab := fromWordsF_one (p := p) r a ha
  unfold wordBody1 wordTail
  rw [leakRunMC_var_of (t := aT 1) (x := fun _ => 0) (l := []),
    leakRunMC_var_of (t := aT 1) (x := stackSet (n := 1) (fun _ => 0) 0 a) (l := []),
    leakRunMC_var_of (t := fT p r) (x := r.ofRep ((a.toNat : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p r) (x := fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
      (r.ofRep ((a.toNat : Nat) : ZMod p))) (l := []),
    leakRunMC_var_of (t := aT 1) (x := toWordsF p r 64 1
      (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p)) (r.ofRep ((a.toNat : Nat) : ZMod p))))
      (l := []),
    leakRunMC_var_of (t := wT) (x := BitVec.ofNat 64 0) (l := []),
    leakRunMC_var_of (t := wT) (x := BitVec.ofNat 64
      (r.toRep (fieldOp m (r.ofRep ((a.toNat : Nat) : ZMod p))
        (r.ofRep ((a.toNat : Nat) : ZMod p)))).val)
      (l := [.addr "" 0])]
  all_goals first
    | rfl
    | exact hab
    | exact zeroE_ctLeak _ hV
    | exact storeE_ctLeak _ hV _ _
    | exact constE_ctLeak _ hV
    | exact fromE_ctLeak _ _ _ _ _ _
    | exact toE_ctLeak _ _ _ _ _
    | exact opE_ctLeak _ _ _ _ _ _
    | exact opE_denoteM _ _ _ _ _
    | exact congrArg some (stackGet_toWordsF_one _ _)

/-- The cast of `k` words whose value is below `p` is the residue of their value. -/
theorem fromWordsF_lt {p k : Nat} (A : Fin k → BitVec 64) (hA : wordsVal k A < p) :
    fromWordsF p .canon 64 k A = some ((wordsVal k A : Nat) : ZMod p) := by
  simp [fromWordsF, hA, FieldRepr.ofRep]

/-- **The run of the raised body of a method with two arguments on arrays**: on arrays
    whose values are below `p`, the words of the value of the method, with no event. -/
theorem arrBody2_leakRunMC (M : LeakModel jasminDialect) (E : CallEnv jasField) (fuel : Nat)
    (m : _root_.Hax.FieldTag.FieldMethod) (p k : Nat) (A B : Fin k → BitVec 64)
    (hA : wordsVal k A < p) (hB : wordsVal k B < p) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E fuel (arrBody2 m p k)
        (.cons A (.cons B .nil)) =
      some (.cons (toWordsF p .canon 64 k (fieldOp m ((wordsVal k A : Nat) : ZMod p)
        ((wordsVal k B : Nat) : ZMod p))) .nil, []) := by
  have hab := fromWordsF_lt (p := p) A hA
  have hbb := fromWordsF_lt (p := p) B hB
  unfold arrBody2
  rw [leakRunMC_var_of (t := fT p) (x := ((wordsVal k A : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p) (x := ((wordsVal k B : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p)
      (x := fieldOp m ((wordsVal k A : Nat) : ZMod p) ((wordsVal k B : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := aT k) (x := toWordsF p .canon 64 k
      (fieldOp m ((wordsVal k A : Nat) : ZMod p) ((wordsVal k B : Nat) : ZMod p))) (l := [])]
  all_goals first
    | rfl
    | exact hab
    | exact hbb
    | exact fromE_ctLeak _ _ _ _ _ _
    | exact toE_ctLeak _ _ _ _ _
    | exact opE_ctLeak _ _ _ _ _ _
    | exact opE_denoteM _ _ _ _ _

/-- **The run of the raised body of a method with one argument on arrays.** -/
theorem arrBody1_leakRunMC (M : LeakModel jasminDialect) (E : CallEnv jasField) (fuel : Nat)
    (m : _root_.Hax.FieldTag.FieldMethod) (p k : Nat) (A : Fin k → BitVec 64)
    (hA : wordsVal k A < p) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E fuel (arrBody1 m p k) (.cons A .nil) =
      some (.cons (toWordsF p .canon 64 k (fieldOp m ((wordsVal k A : Nat) : ZMod p)
        ((wordsVal k A : Nat) : ZMod p))) .nil, []) := by
  have hab := fromWordsF_lt (p := p) A hA
  unfold arrBody1
  rw [leakRunMC_var_of (t := fT p) (x := ((wordsVal k A : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := fT p)
      (x := fieldOp m ((wordsVal k A : Nat) : ZMod p) ((wordsVal k A : Nat) : ZMod p)) (l := []),
    leakRunMC_var_of (t := aT k) (x := toWordsF p .canon 64 k
      (fieldOp m ((wordsVal k A : Nat) : ZMod p) ((wordsVal k A : Nat) : ZMod p))) (l := [])]
  all_goals first
    | rfl
    | exact hab
    | exact fromE_ctLeak _ _ _ _ _ _
    | exact toE_ctLeak _ _ _ _ _
    | exact opE_ctLeak _ _ _ _ _ _
    | exact opE_denoteM _ _ _ _ _

/-! ## 7. The raised bodies return the values of the `u64` table -/

open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldVal fieldVal_lt fieldLimbs limbsOf limbsDec
  limbsDec_limbsOf)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs (arrTy)

/-- The representative of the value of a method on residues below `p` is `fieldVal`. -/
theorem val_fieldOp {p : Nat} [NeZero p] (m : FieldMethod) {a b : Nat} (ha : a < p)
    (hb : b < p) : (fieldOp m (a : ZMod p) (b : ZMod p)).val = fieldVal m p a b := by
  rw [← NFMontify.fieldVal_nat m ha hb, ZMod.val_natCast,
    Nat.mod_eq_of_lt (fieldVal_lt m (Nat.pos_of_neZero p) a b)]

/-- A method with one argument does not read its second argument. -/
theorem fieldOp_unary_eq {p : Nat} (m : FieldMethod) (hm : m.binary = false) (u v w : ZMod p) :
    fieldOp m u v = fieldOp m u w := by
  cases m <;> first | rfl | cases hm

/-- **A raised body on registers runs as the `u64` table**: when the table answers the
    tagged head of `m` at `p < 2⁶⁴` on registers, the raised body returns the injected
    result, with one memory access at index `0`. -/
theorem wordBody_table {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasField) (fuel : Nat) {f : String} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? f = some (m, p)) (hp : p < 2 ^ 64)
    (x : Valuation (d := jasminDialect) (wordSig m))
    (y : Valuation (d := jasminDialect) [.reg 64])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (wordSig m) [.reg 64] x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E fuel (wordBody m p)
        (liftV x) = some (liftV y, [.addr "" 0]) := by
  obtain ⟨ha, hb, rfl⟩ := FieldWideDecl.tableEnv_word hp ht x y hy
  have : NeZero p := ⟨by omega⟩
  have h0 : 0 < p := Nat.pos_of_neZero p
  cases m <;> rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  all_goals first
    | (have ha' : a.toNat < p := ha
       have hb' : b.toNat < p := hb rfl
       exact (wordBody2_leakRunMC hV E fuel _ p .canon a b ha' hb').trans
        (by simp only [FieldRepr.toRep, FieldRepr.ofRep]; rw [val_fieldOp _ ha' hb']; rfl))
    | (have ha' : a.toNat < p := ha
       exact (wordBody1_leakRunMC hV E fuel _ p .canon a ha').trans
        (by
          simp only [FieldRepr.toRep, FieldRepr.ofRep]
          rw [fieldOp_unary_eq _ rfl _ _ (((0 : Nat) : ZMod p)), val_fieldOp _ ha' h0]; rfl))

open _root_.Hax.FieldTag (fieldTagM? fieldValMont fieldValMont_lt montRInv montRInv_mul_pow) in
/-- **The stored residue of a method at a Montgomery representation** is the value of the
    Montgomery head: at an odd modulus `p` and the radix `2^k`, on stored residues `a` and `b`
    below `p`, the representative of the stored residue of `fieldOp m` on the values of `a`
    and `b` is `fieldValMont m p k a b`. -/
theorem val_toRep_fieldOp_mont {p : Nat} [NeZero p] (hodd : p % 2 = 1) (k : Nat)
    (m : FieldMethod) {a b : Nat} (ha : a < p) (hb : b < p) :
    ((FieldRepr.mont k).toRep (fieldOp m ((FieldRepr.mont k).ofRep (a : ZMod p))
      ((FieldRepr.mont k).ofRep (b : ZMod p)))).val = fieldValMont m p k a b := by
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
  have hu := FieldRepr.isUnit_two_pow hcop k
  have hinv : ((2 : ZMod p) ^ k)⁻¹ * (2 : ZMod p) ^ k = 1 := ZMod.inv_mul_of_unit _ hu
  have hR : ((montRInv p k : Nat) : ZMod p) = ((2 : ZMod p) ^ k)⁻¹ := by
    have h2 : ((montRInv p k : Nat) : ZMod p) * (2 : ZMod p) ^ k = 1 := by
      have := congrArg (fun n : Nat => (n : ZMod p)) (montRInv_mul_pow hodd k)
      simpa [Nat.cast_mul, Nat.cast_pow, ZMod.natCast_mod] using this
    calc ((montRInv p k : Nat) : ZMod p)
        = ((montRInv p k : Nat) : ZMod p) * ((2 : ZMod p) ^ k * ((2 : ZMod p) ^ k)⁻¹) := by
          rw [ZMod.mul_inv_of_unit _ hu, mul_one]
      _ = ((2 : ZMod p) ^ k)⁻¹ := by rw [← mul_assoc, h2, one_mul]
  cases m with
  | add =>
      show _ = fieldVal .add p a b
      rw [← val_fieldOp .add ha hb]
      congr 1
      simp only [FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination ((a : ZMod p) + b) * hinv
  | sub =>
      show _ = fieldVal .sub p a b
      rw [← val_fieldOp .sub ha hb]
      congr 1
      simp only [FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination ((a : ZMod p) - b) * hinv
  | neg =>
      show _ = fieldVal .neg p a b
      rw [← val_fieldOp .neg ha hb]
      congr 1
      simp only [FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination (-(a : ZMod p)) * hinv
  | double =>
      show _ = fieldVal .double p a b
      rw [← val_fieldOp .double ha hb]
      congr 1
      simp only [FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination ((a : ZMod p) + a) * hinv
  | mul =>
      show _ = a * b * montRInv p k % p
      rw [← ZMod.val_natCast (n := p) (a * b * montRInv p k)]
      congr 1
      simp only [Nat.cast_mul, hR, FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination (a : ZMod p) * b * ((2 : ZMod p) ^ k)⁻¹ * hinv
  | square =>
      show _ = a * a * montRInv p k % p
      rw [← ZMod.val_natCast (n := p) (a * a * montRInv p k)]
      congr 1
      simp only [Nat.cast_mul, hR, FieldRepr.toRep, FieldRepr.ofRep, fieldOp]
      linear_combination (a : ZMod p) * a * ((2 : ZMod p) ^ k)⁻¹ * hinv

open _root_.Hax.FieldTag (fieldTagM? fieldValMont fieldValMont_lt) in
/-- **The `u64` table at a Montgomery head on registers.** When the call environment read off
    the `u64` table answers the Montgomery head of `m` at an odd `p < 2^64` and the radix
    `2^k` on a valuation at the signature `wordSig` of `m`, the numbers of the valuation are
    below `p` and the result is the word of `fieldValMont m p k` of the numbers. -/
theorem tableEnv_wordMont {p k : Nat} (hodd : p % 2 = 1) (hp : p < 2 ^ 64) {f : String}
    {m : FieldMethod} (ht : fieldTagM? f = some (m, p, k))
    (x : Valuation (d := jasminDialect) (wordSig m)) (y : Valuation (d := jasminDialect) [.reg 64])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (wordSig m) [.reg 64] x = some y) :
    (wordNats m x).1 < p ∧ (m.binary = true → (wordNats m x).2 < p) ∧
      y = .cons (BitVec.ofNat 64 (fieldValMont m p k (wordNats m x).1 (wordNats m x).2)) .nil := by
  change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
      (CatCrypt.Crypto.Hax.ImpToNF.dec (.word 64) v).map fun z =>
        (HVector.cons z .nil : Valuation (d := jasminDialect) [.reg 64])) = some y at hy
  have hd : denVals x = _root_.Hax.FieldTag.fieldArgs m (wordNats m x).1 (wordNats m x).2 := by
    cases m <;> rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl
  rw [hd, _root_.Hax.hax64Builtins_fieldArgsMont ht hodd hp] at hy
  unfold _root_.Hax.FieldTag.fieldArmMont at hy
  split at hy
  · rename_i hc
    refine ⟨hc.1, hc.2, ?_⟩
    have hv := fieldValMont_lt m (by omega : 0 < p) k (wordNats m x).1 (wordNats m x).2
    have hdec : CatCrypt.Crypto.Hax.ImpToNF.dec (.word 64)
        (.int ((fieldValMont m p k (wordNats m x).1 (wordNats m x).2 : Nat) : Int)) =
          some (BitVec.ofNat 64 (fieldValMont m p k (wordNats m x).1 (wordNats m x).2)) := by
      simp only [CatCrypt.Crypto.Hax.ImpToNF.dec]
      rw [ite_eq_left (by omega)]
      simp
    rw [Option.bind_some, hdec, Option.map_some] at hy
    cases hy
    rfl
  · cases hy

open _root_.Hax.FieldTag (fieldTagM?) in
/-- **A raised body on registers at a Montgomery representation runs as the `u64` table**:
    when the table answers the Montgomery head of `m` at an odd `p < 2⁶⁴` and the radix `2^k`
    on registers, the raised body at `mont k` returns the injected result, with one memory
    access at index `0`. -/
theorem wordBody_tableMont {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasField) (fuel : Nat) {f : String} {m : FieldMethod} {p k : Nat}
    (ht : fieldTagM? f = some (m, p, k)) (hodd : p % 2 = 1) (hp : p < 2 ^ 64)
    (x : Valuation (d := jasminDialect) (wordSig m))
    (y : Valuation (d := jasminDialect) [.reg 64])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (wordSig m) [.reg 64] x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E fuel
        (wordBody m p (.mont k)) (liftV x) = some (liftV y, [.addr "" 0]) := by
  obtain ⟨ha, hb, rfl⟩ := tableEnv_wordMont hodd hp ht x y hy
  have : NeZero p := ⟨by omega⟩
  have h0 : 0 < p := Nat.pos_of_neZero p
  cases m <;> rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  all_goals first
    | (have ha' : a.toNat < p := ha
       have hb' : b.toNat < p := hb rfl
       exact (wordBody2_leakRunMC hV E fuel _ p (.mont k) a b ha' hb').trans
        (by rw [val_toRep_fieldOp_mont hodd k _ ha' hb']; rfl))
    | (have ha' : a.toNat < p := ha
       exact (wordBody1_leakRunMC hV E fuel _ p (.mont k) a ha').trans
        (by
          rw [fieldOp_unary_eq _ rfl _ _ ((FieldRepr.mont k).ofRep ((0 : Nat) : ZMod p)),
            val_toRep_fieldOp_mont hodd k _ ha' h0]
          rfl))

/-- The limbs of `N` in `n` words, as a map over the indices. -/
theorem limbsOf_eq_map : ∀ (n N : Nat),
    limbsOf n N = (List.range n).map fun i => .int ((N / 2 ^ (64 * i) % 2 ^ 64 : Nat) : Int)
  | 0, _ => rfl
  | n + 1, N => by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      show .int ((N % 2 ^ 64 : Nat) : Int) :: limbsOf n (N / 2 ^ 64) = _
      rw [limbsOf_eq_map n]
      congr 1
      · simp
      · refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← Nat.pow_add]
        rw [Nat.succ_eq_add_one, Nat.mul_add_one, Nat.add_comm (64 * i) 64]

/-- **The source values of the words of `N` are the limbs of `N`.** -/
theorem wordsOf_wordsOf (n N : Nat) :
    FieldWideInline.wordsOf (FieldChainDialect.wordsOf 64 n N) = limbsOf n N := by
  rw [FieldWideInline.wordsOf, FieldWideInline.limbWords_arrLimbs, limbsOf_eq_map]
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  cases n with
  | zero => omega
  | succ k =>
      simp only [stackGet, FieldChainDialect.wordsOf, Nat.zero_add, Nat.mod_eq_of_lt hi',
        BitVec.toNat_ofNat]

/-- Limbs that `limbsDec` reads as `a` are the words of an array of value `a`. -/
theorem wordsVal_of_limbsDec {n : Nat} (A : Fin n → BitVec 64) {a : Nat}
    (h : limbsDec (FieldWideInline.wordsOf A) = some a) : wordsVal n A = a := by
  rw [← wordsOf_wordsVal n A, wordsOf_wordsOf, limbsDec_limbsOf,
    Nat.mod_eq_of_lt (wordsVal_lt n A)] at h
  exact Option.some.inj h

/-- `dec` reads the limbs of `N < 2^(64 n)` as the words of `N`. -/
theorem dec_limbsOf {n N : Nat} {z : Fin n → BitVec 64}
    (h : CatCrypt.Crypto.Hax.ImpToNF.dec (.arr n (.word 64)) (.array (limbsOf n N)) = some z) :
    z = FieldChainDialect.wordsOf 64 n N := by
  rw [← wordsOf_wordsOf, FieldWideDecl.dec_wordsOf] at h
  exact (Option.some.inj h).symm

/-- **A raised body on arrays runs as the `u64` table**: when the table answers the tagged
    head of `m` at `p` on arrays of `fieldLimbs p` words, the raised body returns the
    injected result, with no event. -/
theorem arrBody_table (M : LeakModel jasminDialect) (E : CallEnv jasField) (fuel : Nat)
    {f : String} {m : FieldMethod} {p : Nat} (ht : fieldTag? f = some (m, p))
    (x : Valuation (d := jasminDialect) (wideSig (fieldLimbs p) m))
    (y : Valuation (d := jasminDialect) [arrTy (fieldLimbs p)])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (wideSig (fieldLimbs p) m)
      [arrTy (fieldLimbs p)] x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E fuel (arrBody m p (fieldLimbs p))
        (liftV x) = some (liftV y, []) := by
  change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
    (CatCrypt.Crypto.Hax.ImpToNF.dec (.arr (fieldLimbs p) (.word 64)) v).map fun z =>
      (HVector.cons z .nil : Valuation (d := jasminDialect) [arrTy (fieldLimbs p)])) = some y at hy
  obtain ⟨v, hv, hd⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨a, c, ha, hap, hc, rfl⟩ := FieldWideDecl.hax64Builtins_wide ht x hv
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hd
  have hz' := dec_limbsOf hz
  subst hz'
  have : NeZero p := ⟨by omega⟩
  have h0 : 0 < p := Nat.pos_of_neZero p
  cases m <;> rcases x with _ | ⟨A, _ | ⟨B, _ | _⟩⟩
  all_goals first
    | (have hA := wordsVal_of_limbsDec A ha
       obtain ⟨hcB, hcp⟩ := hc rfl
       have hB := wordsVal_of_limbsDec B hcB
       subst hA hB
       exact (arrBody2_leakRunMC M E fuel _ p _ A B hap hcp).trans
        (by rw [toWordsF, FieldRepr.toRep, val_fieldOp _ hap hcp]; rfl))
    | (have hA := wordsVal_of_limbsDec A ha
       subst hA
       exact (arrBody1_leakRunMC M E fuel _ p _ A hap).trans
        (by rw [toWordsF, FieldRepr.toRep, fieldOp_unary_eq _ rfl _ _ (((0 : Nat) : ZMod p)),
          val_fieldOp _ hap h0]; rfl))

/-! ## 8. The library of the raised bodies -/

/-- The raised body of a method on registers at the representation `r` and the injected
    signature `as → rs`, or `none` at another signature. -/
def raiseWord (m : FieldMethod) (p : Nat) (as rs : List (JasminTy ⊕ PfTy))
    (r : FieldRepr := .canon) : Option (NFProg jasField as rs) :=
  if hs : as = (wordSig m).map Sum.inl ∧ rs = [wT] then some (hs.1 ▸ hs.2 ▸ wordBody m p r)
  else none

/-- The raised body of a method on arrays of `fieldLimbs p` words at the injected signature
    `as → rs`, or `none` at another signature. -/
def raiseArr (m : FieldMethod) (p : Nat) (as rs : List (JasminTy ⊕ PfTy)) :
    Option (NFProg jasField as rs) :=
  if hs : as = (wideSig (fieldLimbs p) m).map Sum.inl ∧ rs = [aT (fieldLimbs p)] then
    some (hs.1 ▸ hs.2 ▸ arrBody m p (fieldLimbs p))
  else none

/-- **The raised body of a field head** at the injected signature `as → rs`. At a tagged
    head, at the heads and signatures `fieldBody` has a body for: at a modulus with a narrow
    template, or with no wide template and a one-limb record, the raised body on registers;
    at a modulus with no narrow template and a wide template, the raised body on arrays. At
    a Montgomery head (`Hax.FieldTag.fieldTagM?`) of the method `m` at an odd modulus
    `p < 2⁶⁴` and the radix `2^k`, the raised body on registers at the representation
    `mont k`. `none` otherwise. -/
def raiseBody (f : String) (as rs : List (JasminTy ⊕ PfTy)) : Option (NFProg jasField as rs) :=
  match fieldTag? f with
  | some (m, p) =>
      match narrowFieldOf p, wideTemplateOf p, montWordOf p with
      | some _, _, _ => raiseWord m p as rs
      | none, some _, _ => raiseArr m p as rs
      | none, none, some _ => raiseWord m p as rs
      | none, none, none => none
  | none =>
      match _root_.Hax.FieldTag.fieldTagM? f with
      | some (m, p, k) => if p % 2 = 1 ∧ p < 2 ^ 64 then raiseWord m p as rs (.mont k) else none
      | none => none

/-- The signature of a method on registers in `NFMontify` is `wordSig`. -/
theorem fieldJSig_eq_wordSig (m : FieldMethod) : fieldJSig m = wordSig m := by
  cases m <;> rfl

/-- **`raiseBody` recognises the tagged heads that have a template body**: at a tagged head
    and an injected signature, the raised body exists exactly when `fieldBody` has a body. -/
theorem raiseBody_isSome (f : String) (as rs : List JasminTy) (ht : (fieldTag? f).isSome = true) :
    (raiseBody f (as.map Sum.inl) (rs.map Sum.inl)).isSome = (fieldBody f as rs).isSome := by
  have hinj : Function.Injective (List.map (Sum.inl (α := JasminTy) (β := PfTy))) :=
    List.map_injective_iff.mpr Sum.inl_injective
  unfold raiseBody fieldBody FieldWideDecl.wideBody
  rcases h : fieldTag? f with _ | ⟨m, p⟩
  · rw [h] at ht
    cases ht
  · simp only
    rcases narrowFieldOf p with _ | F <;> rcases wideTemplateOf p with _ | W <;>
      rcases montWordOf p with _ | P <;>
      simp only [raiseWord, raiseArr, fieldJSig_eq_wordSig]
    all_goals first | rfl | (split <;> split <;> grind [hinj.eq_iff, List.map_eq_cons_iff])

/-- The events of the raised body of a field head: one memory access at index `0` on
    registers, none on arrays. A Montgomery head is raised on registers only. -/
def raiseEv (f : String) (_ _ : List (JasminTy ⊕ PfTy)) : List CTLeak :=
  match fieldTag? f with
  | some (_, p) =>
      match narrowFieldOf p, wideTemplateOf p with
      | none, some _ => []
      | _, _ => [.addr "" 0]
  | none =>
      match _root_.Hax.FieldTag.fieldTagM? f with
      | some _ => [.addr "" 0]
      | none => []

/-- **The inlining library of the raised bodies**: no operation has a body, and a `call` of
    a field head has the raised body `raiseBody`. -/
def raiseLib : InlineLib jasField where
  op _ := none
  call := raiseBody

/-- Injecting the stripped valuation gives the valuation. -/
theorem liftV_unmapInl : ∀ {as : List JasminTy}
    (x : HVector (fun t => ⟦t⟧) (as.map (Sum.inl (β := PfTy)))),
    liftV (unmapInl (d := jasminDialect) (e := pfDialect) x) = x
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (HVector.cons _) (liftV_unmapInl xs)

/-- A modulus with a one-limb record is below `2⁶⁴`. -/
theorem lt_of_montWordOf {p : Nat} {P} (h : montWordOf p = some P) : p < 2 ^ 64 := by
  unfold montWordOf at h
  split at h
  · rename_i hc
    exact hc.2.2
  · cases h

/-- The raised body on registers runs, on arguments the callee of `liftEnv (fieldEnv E)`
    answers, to the answer, with one memory access at index `0`. -/
theorem raiseWord_run {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasminDialect) (E' : CallEnv jasField) (fuel : Nat) {f : String}
    {m : FieldMethod} {p : Nat} (ht : fieldTag? f = some (m, p)) (hp : p < 2 ^ 64)
    {as rs : List (JasminTy ⊕ PfTy)} {b : NFProg jasField as rs}
    (hb : raiseWord m p as rs = some b) (x : HVector (fun t => ⟦t⟧) as)
    (y : HVector (fun t => ⟦t⟧) rs) (hy : liftCall (fieldEnv E) f as rs x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E' fuel b x =
      some (y, [.addr "" 0]) := by
  unfold raiseWord at hb
  split at hb
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases hb
    rw [← liftV_unmapInl x] at hy ⊢
    change liftCall (fieldEnv E) f _ ([JasminTy.reg 64].map Sum.inl) _ = _ at hy
    rw [liftCall_liftV] at hy
    obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hy
    rw [fieldEnv_of_isSome E (by simp [ht])] at hy'
    exact wordBody_table hV E' fuel ht hp _ y' hy'
  · cases hb

/-- The raised body on registers at the representation `mont k` runs, on arguments the
    callee of `liftEnv (fieldEnv E)` answers at a Montgomery head of radix `2^k`, to the
    answer, with one memory access at index `0`. -/
theorem raiseWordMont_run {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasminDialect) (E' : CallEnv jasField) (fuel : Nat) {f : String}
    {m : FieldMethod} {p k : Nat} (ht : _root_.Hax.FieldTag.fieldTagM? f = some (m, p, k))
    (hodd : p % 2 = 1) (hp : p < 2 ^ 64) {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (hb : raiseWord m p as rs (.mont k) = some b)
    (x : HVector (fun t => ⟦t⟧) as) (y : HVector (fun t => ⟦t⟧) rs)
    (hy : liftCall (fieldEnv E) f as rs x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E' fuel b x =
      some (y, [.addr "" 0]) := by
  unfold raiseWord at hb
  split at hb
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases hb
    rw [← liftV_unmapInl x] at hy ⊢
    change liftCall (fieldEnv E) f _ ([JasminTy.reg 64].map Sum.inl) _ = _ at hy
    rw [liftCall_liftV] at hy
    obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hy
    rw [fieldEnv_of_fieldTagM? E ht] at hy'
    exact wordBody_tableMont hV E' fuel ht hodd hp _ y' hy'
  · cases hb

/-- The raised body on arrays runs, on arguments the callee of `liftEnv (fieldEnv E)`
    answers, to the answer, with no event. -/
theorem raiseArr_run (M : LeakModel jasminDialect) (E : CallEnv jasminDialect)
    (E' : CallEnv jasField) (fuel : Nat) {f : String} {m : FieldMethod} {p : Nat}
    (ht : fieldTag? f = some (m, p)) {as rs : List (JasminTy ⊕ PfTy)}
    {b : NFProg jasField as rs} (hb : raiseArr m p as rs = some b)
    (x : HVector (fun t => ⟦t⟧) as) (y : HVector (fun t => ⟦t⟧) rs)
    (hy : liftCall (fieldEnv E) f as rs x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak M) E' fuel b x = some (y, []) := by
  unfold raiseArr at hb
  split at hb
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    cases hb
    rw [← liftV_unmapInl x] at hy ⊢
    change liftCall (fieldEnv E) f _ ([arrTy (fieldLimbs p)].map Sum.inl) _ = _ at hy
    rw [liftCall_liftV] at hy
    obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.mp hy
    rw [fieldEnv_of_isSome E (by simp [ht])] at hy'
    exact arrBody_table M E' fuel ht _ y' hy'
  · cases hb

/-- **A raised body runs as the callee of `liftEnv (fieldEnv E)`**, with the events
    `raiseEv`. -/
theorem raiseBody_run {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasminDialect) (E' : CallEnv jasField) (fuel : Nat) {f : String}
    {as rs : List (JasminTy ⊕ PfTy)} {b : NFProg jasField as rs}
    (hb : raiseBody f as rs = some b) (x : HVector (fun t => ⟦t⟧) as)
    (y : HVector (fun t => ⟦t⟧) rs) (hy : liftCall (fieldEnv E) f as rs x = some y) :
    Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) E' fuel b x =
      some (y, raiseEv f as rs) := by
  unfold raiseBody at hb
  unfold raiseEv
  split at hb
  · rename_i m p ht
    split at hb
    · rename_i F hF
      obtain ⟨-, hp, -⟩ := narrowFieldOf_spec hF
      simp only [hF]
      exact raiseWord_run hV E E' fuel ht (by omega) hb x y hy
    · rename_i W hN hW
      simp only [hN, hW]
      exact raiseArr_run _ E E' fuel ht hb x y hy
    · rename_i P hN hW hP
      simp only [hN, hW]
      exact raiseWord_run hV E E' fuel ht (lt_of_montWordOf hP) hb x y hy
    · cases hb
  · split at hb
    · rename_i m p k hM
      split at hb
      · rename_i hc
        rw [hM]
        exact raiseWordMont_run hV E E' fuel hM hc.1 hc.2 hb x y hy
      · cases hb
    · cases hb

/-- **The library of the raised bodies is sound for the leakage run** at
    `liftEnv (fieldEnv E)`, with the events `raiseEv` of each head. -/
theorem raiseLib_leakSound {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E : CallEnv jasminDialect) (fuel : Nat) :
    raiseLib.LeakSound (jasFieldLeak (jLeakModel Pj)) (liftEnv (fieldEnv E)) fuel raiseEv :=
  ⟨fun _ _ hb => (by cases hb), fun _ _ _ _ hb x y hy => raiseBody_run hV E _ fuel hb x y hy⟩

/-- **The library of the raised bodies is sound** at `liftEnv (fieldEnv E)`. -/
theorem raiseLib_sound (E : CallEnv jasminDialect) (fuel : Nat) :
    @InlineLib.Sound jasField _ _ _ _ _ ⟨liftEnv (fieldEnv E)⟩ raiseLib fuel := by
  refine @InlineLib.Sound.mk jasField _ _ _ _ _ ⟨liftEnv (fieldEnv E)⟩ raiseLib fuel
    (fun _ _ hb => by cases hb) ?_
  intro f as rs b hb x y hy
  have h := raiseBody_run (Pj := {}) (fun _ => rfl) E (liftEnv (fieldEnv E)) fuel hb x y hy
  have hf := Dialects.NFLeak.NFProg.leakRunMC_fst (jasFieldLeak (jLeakModel {}))
    (liftEnv (fieldEnv E)) fuel b x
  rw [h] at hf
  exact hf.symm

/-! ## 9. The chain stage -/

/-- **The inclusion keeps the denotation.** A program `map?` returns along `liftJ`, included
    into `jasField`, denotes at `liftEnv E` the injection of the denotation of the source
    program at `E`. -/
theorem lift_denoteAt (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts)
    {q : NFProg jasPf (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hq : NFProg.map? liftJ liftJ_regionTypes p (fun v => v) = some q) (V : Valuation Γ) :
    (embed q).denoteAt (liftEnv E) fuel (liftV V) = (p.denoteAt E fuel V).map liftV := by
  rw [← Dialects.NFLeak.NFProg.leakRunMC_fst (jasFieldLeak (jLeakModel {})) (liftEnv E) fuel,
    ← Dialects.NFLeak.NFProg.leakRunMC_fst (jLeakModel {}) E fuel]
  have h1 := embed_leakRunMC (jLeakModel {}) (liftCall E) fuel q (liftV V)
  have h2 := map_leakRunMC (jLeakModel {}) E fuel p hq V
  change Option.map Prod.fst (Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel {}))
    (⟨liftCall E⟩ : CallEnv jasField) fuel (embed q) (liftV V)) = _
  rw [h1]
  change Option.map Prod.fst (Dialects.NFLeak.NFProg.leakRunMC (sumLeak (jLeakModel {})
    pfLeakModel) (liftEnvP E) fuel q (liftV V)) = _
  rw [h2]
  cases Dialects.NFLeak.NFProg.leakRunMC (jLeakModel {}) E fuel p V <;> rfl

/-- **The raising of the tagged field calls as a chain step**: the inclusion of the program
    into `jasField` (`map?` along `liftJ`, then `embed`), one round of `NFProg.inline?` at
    the library `raiseLib`, refused when the result keeps a `call` of a field head. -/
def fieldRaiseStep (Γ : Ctxt jasminDialect) (ts : List JasminTy) :
    PassChain.Step (NFProg jasminDialect Γ ts)
      (NFProg jasField (Γ.map Sum.inl) (ts.map Sum.inl)) :=
  ⟨"fieldRaise", fun p => (NFProg.map? liftJ liftJ_regionTypes p (fun v => v)).bind fun q =>
    (NFProg.inline? raiseLib (embed q)).bind fun r => if fieldFree r then some r else none⟩

/-- **The certificate of the raising step**, from the semantics at `fieldEnv E` to the
    semantics at `liftEnv E`, with the injection of valuations as input relation and the
    injection of result tuples as output relation: the inclusion keeps every run
    (`lift_denoteAt`), inlining under the sound library keeps every run at
    `liftEnv (fieldEnv E)` (`NFProg.denoteAt_inline?`, `raiseLib_sound`), and the result
    calls no field head, at which alone the two environments differ
    (`NFProg.denoteAt_congr`). -/
def fieldRaiseCert (E : CallEnv jasminDialect) (fuel : Nat) (Γ : Ctxt jasminDialect)
    (ts : List JasminTy) :
    PassChain.StepCert (fieldRaiseStep Γ ts).run (NFProgPasses.nfSemE (fieldEnv E) fuel Γ ts)
      (NFProgPasses.nfSemE (liftEnv E) fuel (Γ.map Sum.inl) (ts.map Sum.inl)) where
  relIn V W := W = liftV V
  relOut o o' := o' = liftV o
  sound := by
    intro p r V W o hf hVW hd
    subst hVW
    change p.denoteAt (fieldEnv E) fuel V = some o at hd
    obtain ⟨q, hq, hf⟩ := Option.bind_eq_some_iff.mp hf
    obtain ⟨r0, hr0, hif⟩ := Option.bind_eq_some_iff.mp hf
    split at hif
    · rename_i hff
      cases hif
      refine ⟨liftV o, ?_, rfl⟩
      have h1 := (lift_denoteAt (fieldEnv E) fuel p hq V).trans (congrArg (Option.map liftV) hd)
      have h2 := NFProg.denoteAt_inline? (liftEnv (fieldEnv E)) (raiseLib_sound E fuel)
        (embed q) hr0 h1
      exact (NFProg.denoteAt_congr r (liftEnv E) (liftEnv (fieldEnv E)) (fun f as rs x hc =>
        (liftCall_fieldEnv_of_none E (fieldHeadB_of_fieldFree r hff hc) as rs x).symm) fuel
        _).trans h2
    · cases hif

/-- **Two leakage runs before the raising give two runs of its result, with equal events
    from equal events.** At leakage parameters of `jasminDialect` with no variable-time
    operation, the inclusion keeps the results and the events (`map_leakRunMC`,
    `embed_leakRunMC`), the library of the raised bodies is sound for the leakage run at
    `liftEnv (fieldEnv E')` with a fixed list of events per head (`raiseLib_leakSound`),
    so the inlined program runs from each valuation to the injected results, with equal
    events when the source events are equal (`NFProg.leakRunMC_inline?_prefix`); the result
    calls no field head, at which alone `liftEnv (fieldEnv E')` and `liftEnv E'` differ
    (`NFProg.leakRunMC_congr`). -/
theorem fieldRaiseStep_leakRunC {Pj : JLeakParams} (hV : ∀ op, Pj.opVT op = none)
    (E' : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasField (Γ.map Sum.inl) (ts.map Sum.inl)}
    (hf : (fieldRaiseStep Γ ts).run p = some q) {V₁ V₂ : Valuation Γ}
    {r₁ r₂ : Valuation (d := jasminDialect) ts × List CTLeak}
    (h₁ : Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₁ = some r₁)
    (h₂ : Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V₂ =
      some r₂) :
    ∃ l₁ l₂,
      Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) (liftEnv E') fuel q
          (liftV V₁) = some (liftV r₁.1, l₁) ∧
        Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj)) (liftEnv E') fuel q
          (liftV V₂) = some (liftV r₂.1, l₂) ∧
        (r₁.2 = r₂.2 → l₁ = l₂) := by
  obtain ⟨q0, hq0, hf⟩ := Option.bind_eq_some_iff.mp hf
  obtain ⟨r0, hr0, hif⟩ := Option.bind_eq_some_iff.mp hf
  split at hif
  · rename_i hff
    cases hif
    have lift : ∀ (V : Valuation Γ) r,
        Dialects.NFLeak.NFProg.leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p V = some r →
        Dialects.NFLeak.NFProg.leakRunMC (jasFieldLeak (jLeakModel Pj))
          (liftEnv (fieldEnv E')) fuel (embed q0) (liftV V) = some (liftV r.1, r.2) := by
      intro V r hr
      have h1 := embed_leakRunMC (jLeakModel Pj) (liftCall (fieldEnv E')) fuel q0 (liftV V)
      have h2 := map_leakRunMC (jLeakModel Pj) (fieldEnv E') fuel p hq0 V
      rw [hr] at h2
      exact h1.trans h2
    obtain ⟨l₁, l₂, e₁, e₂, hl⟩ :=
      VIR.NFProg.leakRunMC_inline?_prefix (jasFieldLeak (jLeakModel Pj)) (liftEnv (fieldEnv E'))
        (raiseLib_leakSound hV E' fuel) (embed q0) hr0 (lift V₁ r₁ h₁) (lift V₂ r₂ h₂)
    have hc := fun V => Dialects.NFLeak.NFProg.leakRunMC_congr (jasFieldLeak (jLeakModel Pj)) q
      (liftEnv (fieldEnv E')) (liftEnv E') (fun f as rs x hc =>
        liftCall_fieldEnv_of_none E' (fieldHeadB_of_fieldFree q hff hc) as rs x) fuel V
    exact ⟨l₁, l₂, (hc _).symm.trans e₁, (hc _).symm.trans e₂,
      fun he => (hl [] [] (by simp only [he])).1⟩
  · cases hif

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldRaise
