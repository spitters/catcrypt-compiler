/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoops

/-!
# The constant-time leakage of `jasminDialect` and of `ComL`

The instance of `ComLevelCheck.LeakModel` for `jasminDialect`, the leakage of the looped
programs `ComL`, and the leakage transformer of the lowering `cryptoDialectToJasminCom`.

The model `jLeakModel Pj`:

* `stackLoad` and `stackStore` leak their index argument (position `1`) as a memory offset;
* the opaque array leaves `arrLoadDyn` and `arrStoreDyn` leak their last argument, the
  index; an `extCall` of any other leaf is quiet when the parameters list its name
  (`leafQuiet`) and leaks its argument values otherwise;
* an operation the parameters map to a variable-time instruction (`opVT`) leaks its
  argument values as that instruction's operands;
* every other operation is quiet.

A register value reads as the natural number of its bits, every other value as `0`
(`jValNat`).

`ComL.ctLeak M c V` is the list of events of the run of a looped program: the events of
each binding in order, and for a loop node the event `trip n` of its trip count followed by
the events of each iteration of its body, in iteration order.

The lowering `cryptoDialectToJasminCom` maps each operation to one operation with the same
arguments, so its leakage transformer is the identity: the lowered program on the
transported valuation leaks the trace of the source program (`cryptoDialectToJasminCom_ctLeak`).

## Main definitions

* `JLeakParams`, `jKind`, `jValNat`, `jLeakModel` — the leakage model of `jasminDialect`.
* `iterLeak`, `ComL.ctLeak`, `ComLCT` — the leakage of a looped program and its constant
  time for entry labels.
* `LeakCompat` — the agreement of the parameters of the two dialects on the lowered
  operations.

## Main results

* `jValNat_ctTransTy` — the transport of values preserves their natural-number reading.
* `toJExprD_ctLeak`, `cryptoDialectToJasminCom_ctLeak` — the leakage transformer of the
  lowering is the identity.
* `toJBlockD_ctLeak` — a block of `toJBlockD` emits the events of its source expression.
* `leakCompat_owned` — the parameters of the owned route agree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD ctMapValD_lookup)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComLeaf (ctMapHV lookupArgs_toJArgsD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTime X86Mnem)

/-! ## The leakage model of `jasminDialect` -/

/-- The parameters of the leakage of `jasminDialect`: the leaf calls classed quiet (every
    leaf call of another name is variable time) and the operations that are variable-time
    instructions. -/
structure JLeakParams where
  leafQuiet : String → Bool := fun _ => false
  opVT : JasminOp → Option X86Mnem := fun _ => none

/-- The parameters of the owned x86 route: the quiet leaves `ownedQuietLeaf` and no
    variable-time operation. -/
def JLeakParams.owned : JLeakParams := { leafQuiet := ownedQuietLeaf }

/-- The event class of an operation of `jasminDialect`. The match lists every constructor of
    `JasminOp`: a stack access leaks its index, a leaf call is quiet when `Pj.leafQuiet`
    lists its name and variable time otherwise, and each remaining operation is classed by
    `Pj.opVT`. The dialect has no division and no arithmetic shift right by a register
    count; `sarImm` shifts by an immediate. -/
def jKind (Pj : JLeakParams) (op : JasminOp) : LeakKind :=
  match op with
  | .stackLoad _ _ | .stackStore _ _ => .addrAt 1
  | .extCall name argTys _ =>
      if name = "arrLoadDyn" ∨ name = "arrStoreDyn" then .addrAt (argTys.length - 1)
      else if Pj.leafQuiet name then .quiet
      else .vtCall name
  | .regArith _ _ | .castW _ _ | .regConst _ _ | .vpackZMM _ | .vpackZMMd _ | .vprordZMM _
  | .vpslldq _ | .vpsrldq _ | .vsimd _ | .mulhi _ | .addCarryLo _ | .addCarryHi _
  | .rorImm _ _ | .shrImm _ _ | .sarImm _ _ | .shlImm _ _ | .select _ | .callN _ _ _
  | .vymm _ | .cmp _ _ | .cmpImm _ _ _ =>
      match Pj.opVT op with
      | some m => .vt m
      | none => .quiet

/-- The array leaf `arrLoadDyn` leaks its last argument. -/
@[simp] theorem jKind_extCall_arrLoadDyn (Pj : JLeakParams) (argTys : List JasminTy)
    (r : JasminTy) :
    jKind Pj (.extCall "arrLoadDyn" argTys r) = .addrAt (argTys.length - 1) := by
  simp [jKind]

/-- The array leaf `arrStoreDyn` leaks its last argument. -/
@[simp] theorem jKind_extCall_arrStoreDyn (Pj : JLeakParams) (argTys : List JasminTy)
    (r : JasminTy) :
    jKind Pj (.extCall "arrStoreDyn" argTys r) = .addrAt (argTys.length - 1) := by
  simp [jKind]

/-- A leaf call of a name `Pj.leafQuiet` lists, other than the two array leaves, is
    quiet. -/
theorem jKind_extCall_quiet {Pj : JLeakParams} {name : String}
    (hl : name ≠ "arrLoadDyn") (hs : name ≠ "arrStoreDyn") (hq : Pj.leafQuiet name = true)
    (argTys : List JasminTy) (r : JasminTy) :
    jKind Pj (.extCall name argTys r) = .quiet := by
  simp [jKind, hl, hs, hq]

/-- A leaf call of a name `Pj.leafQuiet` does not list, other than the two array leaves,
    is a variable-time leaf call. -/
theorem jKind_extCall_vt {Pj : JLeakParams} {name : String}
    (hl : name ≠ "arrLoadDyn") (hs : name ≠ "arrStoreDyn") (hq : Pj.leafQuiet name = false)
    (argTys : List JasminTy) (r : JasminTy) :
    jKind Pj (.extCall name argTys r) = .vtCall name := by
  simp [jKind, hl, hs, hq]

/-- The natural-number reading of a value of `jasminDialect`: a register by its bits, every
    other value as `0`. -/
def jValNat : (t : JasminTy) → ⟦t⟧ → Nat
  | .reg _, w => w.toNat
  | _, _ => 0

/-- The leakage model of `jasminDialect` at the parameters `Pj`. -/
def jLeakModel (Pj : JLeakParams) : LeakModel jasminDialect where
  kind := jKind Pj
  valNat := jValNat

/-! ## The leakage of `ComL` -/

/-- The events of the iterations `ts` of a loop from the accumulator `a`: the events
    `leak t a` of the iteration at index `t`, then the events of the remaining iterations
    from the accumulator `step t a`. -/
def iterLeak {α : Type} (leak : Nat → α → List CTLeak) (step : Nat → α → α) :
    List Nat → α → List CTLeak
  | [], _ => []
  | t :: ts, a => leak t a ++ iterLeak leak step ts (step t a)

/-- The events of the run of a looped program from a valuation. A binding emits the events
    of its operation; a loop node emits `trip n` for its trip count `n`, then the events of
    its iterations, then the events of its continuation. A nested loop emits, per outer
    iteration, the events of the inner trip count computation, `trip` of the inner count and
    the events of the inner iterations. -/
def ComL.ctLeak (M : LeakModel jasminDialect) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → Ctxt.Valuation Γ → List CTLeak
  | _, _, .ret _, _ => []
  | _, _, .var e body, V => Expr.ctLeak M e V ++ ComL.ctLeak M body (V.extend (e.denote V))
  | _, _, .forLoop loop init body, V =>
      .trip loop.n ::
        (iterLeak (fun _ acc => Com.ctLeak M loop.update (.cons acc .nil))
            (fun _ acc => JLoopBody.stepC loop.update acc) (List.range loop.n)
            (init.lookup V) ++
          ComL.ctLeak M body (V.extend (loop.denote (init.lookup V))))
  | _, _, .forLoopN loop init invs body, V =>
      .trip loop.n ::
        (iterLeak (fun t acc => Com.ctLeak M loop.update
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (fun t acc => JLoopBodyN.stepC loop.update (Expr.lookupArgs invs V) t acc)
            (List.range loop.n) (init.lookup V) ++
          ComL.ctLeak M body
            (V.extend (loop.denote (Expr.lookupArgs invs V) (init.lookup V))))
  | _, _, .forLoopNRt update count init invs body, V =>
      .trip (count.lookup V).toNat ::
        (iterLeak (fun t acc => Com.ctLeak M update
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (fun t acc => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
            (List.range (count.lookup V).toNat) (init.lookup V) ++
          ComL.ctLeak M body (V.extend
            ((List.range (count.lookup V).toNat).foldl
              (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
              (init.lookup V))))
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, V =>
      .trip (outerCount.lookup V).toNat ::
        (iterLeak
            (fun jd acc =>
              Com.ctLeak M innerCount (.cons (BitVec.ofNat 64 jd) (Expr.lookupArgs invs V)) ++
                .trip (JLoopBodyN.innerTripAtC innerCount (Expr.lookupArgs invs V) jd) ::
                iterLeak (fun t acc2 => Com.ctLeak M innerUpdate
                    (.cons acc2 (.cons (BitVec.ofNat 64 t)
                      (.cons (BitVec.ofNat 64 jd) (Expr.lookupArgs invs V)))))
                  (fun t acc2 => JLoopBodyN.stepCNested innerUpdate (Expr.lookupArgs invs V)
                    jd t acc2)
                  (List.range (JLoopBodyN.innerTripAtC innerCount (Expr.lookupArgs invs V) jd))
                  acc)
            (fun jd acc =>
              (List.range (JLoopBodyN.innerTripAtC innerCount (Expr.lookupArgs invs V) jd)).foldl
                (fun acc2 t => JLoopBodyN.stepCNested innerUpdate (Expr.lookupArgs invs V)
                  jd t acc2) acc)
            (List.range (outerCount.lookup V).toNat) (init.lookup V) ++
          ComL.ctLeak M body (V.extend
            (JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
              (Expr.lookupArgs invs V) (init.lookup V))))
  | _, _, .whileNz update guard init invs body, V =>
      .trip (guard.lookup V).toNat ::
        (iterLeak (fun t acc => Com.ctLeak M update
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (fun t acc => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
            (List.range (guard.lookup V).toNat) (init.lookup V) ++
          ComL.ctLeak M body (V.extend
            ((List.range (guard.lookup V).toNat).foldl
              (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
              (init.lookup V))))
  | _, _, .forLoopBlock loopBody count init invs body, V =>
      .trip (count.lookup V).toNat ::
        (iterLeak (fun t acc => ComL.ctLeak M loopBody
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (fun t acc => loopBody.denote
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (List.range (count.lookup V).toNat) (init.lookup V) ++
          ComL.ctLeak M body (V.extend
            ((List.range (count.lookup V).toNat).foldl
              (fun acc t => loopBody.denote
                (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
              (init.lookup V))))

/-- Constant time of a looped program for the entry labels `L`: valuations that agree on
    the positions `L` marks public give equal leakage. -/
def ComLCT (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (L : Labels Γ) (c : ComL Γ t) : Prop :=
  ConstantTime (PubEqV L) (ComL.ctLeak M c)

/-! ## The leakage transformer of the lowering -/

/-- The parameters of the two dialects agree on the lowered operations: the same leaf calls
    are quiet, an operation and its one-expression lowering `toJExprD` are the same
    variable-time instruction, and a block of several bindings `toJMultiD` emits, on the
    transported valuation, the events of its source operation. -/
def LeakCompat (P : CatLeakParams) (Pj : JLeakParams) : Prop :=
  Pj.leafQuiet = P.leafQuiet ∧
    (∀ {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
      (e' : Expr jasminDialect (mapCtx Γ) (mapTy t)),
      toJExprD e = some e' → Pj.opVT e'.op = P.opVT e.op) ∧
    ∀ {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
      (blk : Com jasminDialect (mapCtx Γ) (mapTy t)),
      toJMultiD e = some blk → ∀ V : Ctxt.Valuation (d := catCryptDialect) Γ,
        Com.ctLeak (jLeakModel Pj) blk (ctMapValD V) = Expr.ctLeak (catLeakModel P) e V

/-- The parameters of the owned route agree: no operation is a variable-time instruction
    on either side, so a block of constants, `xor` and `select` and its source operation
    both emit no event. -/
theorem leakCompat_owned : LeakCompat CatLeakParams.owned JLeakParams.owned := by
  refine ⟨rfl, fun _ _ _ => rfl, fun e blk h V => ?_⟩
  obtain ⟨op, hop, args⟩ := e
  cases op <;> cases hop <;> simp only [toJMultiD, reduceCtorEq] at h <;> cases h <;> rfl

/-- The transport of values preserves their natural-number reading. -/
theorem jValNat_ctTransTy : (t : CryptoTy) → (x : CryptoTy.denote t) →
    jValNat (mapTy t) (ctTransTy x) = catValNat t x
  | .sword _, _ => rfl
  | .bit, b => by cases b <;> rfl
  | .unit, _ => rfl
  | .memref _, _ => rfl
  | .memrefW _ _, _ => rfl
  | .pair _ _, _ => rfl
  | .sum _ _, _ => rfl

/-- The readings of a transported value vector are the readings of the vector. -/
theorem valsNat_ctMapHV (Pj : JLeakParams) (P : CatLeakParams) :
    {tys : List CryptoTy} → (vals : HVector (fun t => ⟦t⟧) tys) →
    valsNat (jLeakModel Pj) (ctMapHV vals) = valsNat (catLeakModel P) vals
  | [], .nil => rfl
  | t :: _, .cons v rest => by
      change jValNat (mapTy t) (ctTransTy v) :: valsNat (jLeakModel Pj) (ctMapHV rest) =
        catValNat t v :: valsNat (catLeakModel P) rest
      rw [jValNat_ctTransTy, valsNat_ctMapHV Pj P rest]

/-- Two operations of the same event class on argument vectors with the same readings emit
    the same events. -/
theorem opLeak_eq_of {d d' : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [TyDenote d'.Ty] [DialectSignature d'] (M : LeakModel d) (M' : LeakModel d')
    (op : d.Op) (op' : d'.Op) (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig op))
    (vals' : HVector (fun t => ⟦t⟧) (DialectSignature.sig op'))
    (hk : M.kind op = M'.kind op') (hv : valsNat M vals = valsNat M' vals') :
    opLeak M op vals = opLeak M' op' vals' := by
  unfold opLeak
  rw [hk, hv]

/-- The empty argument vectors have the same readings. -/
theorem valsNat_nil (P : CatLeakParams) (Pj : JLeakParams) {Γ : Ctx}
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    valsNat (jLeakModel Pj)
        (Expr.lookupArgs (HVector.nil : HVector (fun ty => Ctxt.Var (mapCtx Γ) ty) [])
          (ctMapValD V)) =
      valsNat (catLeakModel P)
        (Expr.lookupArgs
          (HVector.nil : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) []) V) :=
  rfl

/-- A lowered argument variable in front of argument vectors with the same readings gives
    argument vectors with the same readings. -/
theorem valsNat_cons (P : CatLeakParams) (Pj : JLeakParams) {Γ : Ctx}
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) {s : CryptoTy} {tys : List JasminTy}
    {tysC : List CryptoTy} (a : Ctxt.Var (d := catCryptDialect) Γ s)
    (rest : HVector (fun ty => Ctxt.Var (d := jasminDialect) (mapCtx Γ) ty) tys)
    (restC : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) tysC)
    (h : valsNat (jLeakModel Pj) (Expr.lookupArgs rest (ctMapValD V)) =
      valsNat (catLeakModel P) (Expr.lookupArgs restC V)) :
    valsNat (jLeakModel Pj) (Expr.lookupArgs (HVector.cons (toJVarD a) rest) (ctMapValD V)) =
      valsNat (catLeakModel P) (Expr.lookupArgs (HVector.cons a restC) V) := by
  change jValNat (mapTy s) ((toJVarD a).lookup (ctMapValD V)) ::
      valsNat (jLeakModel Pj) (Expr.lookupArgs rest (ctMapValD V)) =
    catValNat s (a.lookup V) :: valsNat (catLeakModel P) (Expr.lookupArgs restC V)
  rw [ctMapValD_lookup, jValNat_ctTransTy, h]

/-- **The leakage transformer of an operation.** An expression the lowering maps to `e'`
    emits, on the transported valuation, the events of the source expression. -/
theorem toJExprD_ctLeak {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (e' : Expr jasminDialect (mapCtx Γ) (mapTy t)) (he : toJExprD e = some e')
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    Expr.ctLeak (jLeakModel Pj) e' (ctMapValD V) = Expr.ctLeak (catLeakModel P) e V := by
  have hvt := hc.2.1 e e' he
  obtain ⟨op, hop, args⟩ := e
  unfold Expr.ctLeak
  cases op
  case' ite => rename_i ty; cases ty
  case' vsimd => rename_i sop; cases sop
  case' extCall => rename_i retTy; cases retTy
  all_goals (cases hop; simp only [toJExprD] at he)
  all_goals (try (cases he))
  all_goals
    apply opLeak_eq_of
    · simp only [jLeakModel, catLeakModel, jKind, catKind, mkBin] at hvt ⊢
      try (rw [hvt]; rfl)
      try simp [hc.1, List.length_map]
    · first
      | exact (congrArg _ (lookupArgs_toJArgsD args V)).trans (valsNat_ctMapHV Pj P _)
      | (rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
         first
         | exact valsNat_nil P Pj V
         | exact valsNat_cons P Pj V a .nil .nil (valsNat_nil P Pj V)
         | exact valsNat_cons P Pj V a (.cons (toJVarD b) .nil) (.cons b .nil)
             (valsNat_cons P Pj V b .nil .nil (valsNat_nil P Pj V))
         | exact valsNat_cons P Pj V a (.cons (toJVarD b) (.cons (toJVarD c) .nil))
             (.cons b (.cons c .nil)) (valsNat_cons P Pj V b (.cons (toJVarD c) .nil)
               (.cons c .nil) (valsNat_cons P Pj V c .nil .nil (valsNat_nil P Pj V))))

/-- **The leakage transformer of a block.** A block `toJBlockD` gives an expression emits,
    on the transported valuation, the events of the source expression. -/
theorem toJBlockD_ctLeak {P : CatLeakParams} {Pj : JLeakParams} (hc : LeakCompat P Pj)
    {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t)) (h : toJBlockD e = some blk)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    Com.ctLeak (jLeakModel Pj) blk (ctMapValD V) = Expr.ctLeak (catLeakModel P) e V := by
  unfold toJBlockD at h
  split at h
  · next e' he =>
      cases h
      show Expr.ctLeak (jLeakModel Pj) e' (ctMapValD V) ++ [] = _
      rw [List.append_nil, toJExprD_ctLeak hc e e' he V]
  · exact hc.2.2 e blk h V

/-- **The leakage transformer of the lowering.** A program `cryptoDialectToJasminCom` lowers
    to `jc` leaks, on the transported valuation, the trace of the source program. -/
theorem cryptoDialectToJasminCom_ctLeak {P : CatLeakParams} {Pj : JLeakParams}
    (hc : LeakCompat P Pj) {Γ : Ctx} {t : CryptoTy} :
    (c : Com catCryptDialect Γ t) → (jc : Com jasminDialect (mapCtx Γ) (mapTy t)) →
    cryptoDialectToJasminCom c = some jc → (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    Com.ctLeak (jLeakModel Pj) jc (ctMapValD V) = Com.ctLeak (catLeakModel P) c V
  | .ret v, jc, h, V => by
      simp only [cryptoDialectToJasminCom, Option.some.injEq] at h
      subst h
      rfl
  | .var e body, jc, h, V => by
      simp only [cryptoDialectToJasminCom] at h
      split at h
      · next e' he =>
          split at h
          · next body' hbody =>
              simp only [Option.some.injEq] at h
              subst h
              change Expr.ctLeak (jLeakModel Pj) e' (ctMapValD V) ++
                  Com.ctLeak (jLeakModel Pj) body' ((ctMapValD V).extend (e'.denote (ctMapValD V)))
                = Expr.ctLeak (catLeakModel P) e V ++
                  Com.ctLeak (catLeakModel P) body (V.extend (e.denote V))
              rw [toJExprD_ctLeak hc e e' he V,
                DialectToJasminComCorrect.dialectJasminLeafAgrees_holds e V e' he,
                ← DialectToJasminComCorrect.ctMapValD_extend V (e.denote V),
                cryptoDialectToJasminCom_ctLeak hc body body' hbody]
          · cases h
      · cases h

end CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
