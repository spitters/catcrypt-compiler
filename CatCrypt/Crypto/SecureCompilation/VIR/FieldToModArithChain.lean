/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapM
public import CatCrypt.Crypto.SecureCompilation.VIR.NFMapLeakBlockEv

/-!
# The chain stage from the field dialect to the `mod_arith` dialect

The target dialect `jasMod` of `VIR/FieldChainDialect.lean` joins the operations of
`jasminDialect` and `modArithDialect` with the word casts `toWordsM` and `fromWordsM` between
word tuples and residues of `ZMod p`, and denotes in `Option`.

`fieldToModArithJ : PartialBlockLowering jasField jasMod` keeps every operation of
`jasminDialect`. It maps the type `pf p r` to `fp p` and transports a field value `x` to its
stored residue `r.toRep x`. Addition, subtraction, negation, doubling, copies and constants
become their `mod_arith` twins at every representation; multiplication and squaring become
`modMul` at `canon` and `montMul` with the radix inverse of `radixParams k` at `mont k`;
`toMont p k` multiplies by the constant `2 ^ k` and `fromMont p k` is `montReduce` by the
radix inverse; the casts `fromWords` and `toWords` become `fromWordsM` and `toWordsM`. The
lowering refuses an operation at a representation `mont k` that is not admissible at its
modulus (`p` even) where the value equation needs the radix to be a unit: multiplication,
squaring, `fromMont` and `fromWords`.

`fieldToModArithStep` is `NFProgPasses.mapStep` along `fieldToModArithJ`, and
`fieldToModArithCert` its chain certificate from `PassChain.StepCert.ofMapAtM?`.

## Main definitions

* `radixParams k`: the Montgomery parameters of radix `2 ^ k` at the odd moduli.
* `mapTy`, `mapVar`, `transTy`, `mapVal`, `fieldToModArithJ`: the lowering and its
  transports.
* `fieldToModArithStep`, `fieldToModArithCert`: the chain stage and its certificate.
* `opCanon`: the operations at the representation `canon`.
* `liftCallM`, `liftEnvM`: the call environment of `jasMod` from one of `jasminDialect`.

## Main results

* `fieldToModArith_lookup_mapVar`, `fieldToModArith_varTransports`,
  `fieldToModArith_mapValExtends`, `regionTypes`, `regionTransports`: the leaves of the
  lowering other than the block leaf.
* `block_fwd`: a successful source expression has a successful block with the stored
  residue of its value.
* `isSome_map?_of_opCanon`, `fieldToModArithStep_isSome`: the stage returns a program when
  every operation is at the representation `canon`.
* `liftCallM_liftVM`: at injected types, `liftEnvM E` answers what `E` answers.
* `blockEvO_eq`: at a quiet leakage model of `modArithDialect`, the blocks of an expression
  emit its events.
* `fieldToModArithStep_leakRunMC`, `fieldToModArithStep_leakRunC`: the lowered program runs
  to the transported results with the source events, and equal source events give equal
  events after the stage.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithMont
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)

/-! ## 1. Montgomery parameters of a radix -/

/-- Admissibility of a representation is decidable. -/
instance decAdmits (p : Nat) : (r : FieldRepr) → Decidable (r.Admits p)
  | .canon => isTrue trivial
  | .mont _ => inferInstanceAs (Decidable (Nat.Coprime 2 p))

/-- The Montgomery parameters of radix `2 ^ k`: the Montgomery flag is set at the odd
    moduli, the radix is `2 ^ k` and its inverse `(2 ^ k)⁻¹`. -/
def radixParams (k : Nat) : MontParams where
  isMont q := decide (Nat.Coprime 2 q)
  R _ := 2 ^ k
  rInv _ := (2 ^ k)⁻¹
  R_mul_rInv _ h := ZMod.mul_inv_of_unit _ (FieldRepr.isUnit_two_pow (of_decide_eq_true h) k)

/-! ## 2. The lowering -/

/-- The type map: a type of `jasminDialect` is kept, `pf p r` goes to `fp p`. -/
@[reducible] def mapTy : JasminTy ⊕ PfTy → JasminTy ⊕ ModArithTy
  | .inl t => .inl t
  | .inr (.pf p _) => .inr (.fp p)

/-- The variable map along `mapTy`. -/
def mapVar : {Γ : Ctxt jasField} → {t : jasField.Ty} → Var Γ t →
    Var (d := jasMod) (Γ.map mapTy) (mapTy t)
  | _, _, .here => .here
  | _, _, .there v => .there (mapVar v)

/-- The mapped argument variables of an operation of `jasminDialect`. -/
def argsJ {Γ : Ctxt jasField} : {ts : List JasminTy} →
    HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := PfTy))) →
    HVector (fun t => Var (d := jasMod) (Γ.map mapTy) t) (ts.map (Sum.inl (β := ModArithTy)))
  | [], _ => .nil
  | _ :: _, .cons v vs => .cons (mapVar v) (argsJ vs)

/-- The one-binding block applying `op` to `args`. -/
@[reducible] def opB {Δ : Ctxt jasMod} (op : jasMod.Op)
    (args : HVector (fun t => Var Δ t) (DialectSignature.sig (d := jasMod) op)) :
    Com jasMod Δ (DialectSignature.ret (d := jasMod) op) :=
  .var ⟨op, rfl, args⟩ (.ret .here)

/-- The block of an operation of `pfDialect`, or `none` at a representation `mont k` that
    is not admissible where the value equation needs the radix to be a unit. -/
def pfBlock? {Γ : Ctxt jasField} : (o : PfOp) →
    HVector (fun t => Var Γ t) ((DialectSignature.sig (d := pfDialect) o).map
      (Sum.inr (α := JasminTy))) →
    Option (Com jasMod (Γ.map mapTy) (mapTy (.inr (DialectSignature.ret (d := pfDialect) o))))
  | .add p _, args =>
      some (opB (.inl (.inr (.modAdd p)))
        (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)))
  | .sub p _, args =>
      some (opB (.inl (.inr (.modSub p)))
        (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)))
  | .neg p _, args => some (opB (.inl (.inr (.modNeg p))) (.cons (mapVar args.head) .nil))
  | .mul p .canon, args =>
      some (opB (.inl (.inr (.modMul p)))
        (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)))
  | .mul p (.mont k), args =>
      if Nat.Coprime 2 p then
        some (opB (.inl (.inr (.montMul p ((radixParams k).rInv p))))
          (.cons (mapVar args.head) (.cons (mapVar args.tail.head) .nil)))
      else none
  | .square p .canon, args =>
      some (opB (.inl (.inr (.modMul p)))
        (.cons (mapVar args.head) (.cons (mapVar args.head) .nil)))
  | .square p (.mont k), args =>
      if Nat.Coprime 2 p then
        some (opB (.inl (.inr (.montMul p ((radixParams k).rInv p))))
          (.cons (mapVar args.head) (.cons (mapVar args.head) .nil)))
      else none
  | .double p _, args =>
      some (opB (.inl (.inr (.modAdd p)))
        (.cons (mapVar args.head) (.cons (mapVar args.head) .nil)))
  | .const p r c, _ => some (opB (.inl (.inr (.modConst p (r.toRep c)))) .nil)
  | .copy p _, args => some (opB (.inl (.inr (.modCopy p))) (.cons (mapVar args.head) .nil))
  | .toMont p k, args =>
      some (.var ⟨.inl (.inr (.modConst p (2 ^ k))), rfl, .nil⟩
        (.var ⟨.inl (.inr (.modMul p)), rfl,
          .cons (.there (mapVar args.head)) (.cons .here .nil)⟩ (.ret .here)))
  | .fromMont p k, args =>
      if Nat.Coprime 2 p then
        some (opB (.inl (.inr (.montReduce p ((radixParams k).rInv p))))
          (.cons (mapVar args.head) .nil))
      else none

/-- The block of a cast, or `none` for `fromWords` at a representation that is not
    admissible. -/
def castBlock? {Γ : Ctxt jasField} : (o : CastOp) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := castDialect) o) →
    Option (Com jasMod (Γ.map mapTy) (mapTy (DialectSignature.ret (d := castDialect) o)))
  | .fromWords p r w n, args =>
      if r.Admits p then
        some (opB (.inr (.fromWordsM p w n)) (.cons (mapVar args.head) .nil))
      else none
  | .toWords p _ w n, args => some (opB (.inr (.toWordsM p w n)) (.cons (mapVar args.head) .nil))

/-- The block of an operation of `jasField`. -/
def opBlock? {Γ : Ctxt jasField} : (op : jasField.Op) →
    HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasField) op) →
    Option (Com jasMod (Γ.map mapTy) (mapTy (DialectSignature.ret (d := jasField) op)))
  | .inl (.inl o), args => some (opB (.inl (.inl o)) (argsJ args))
  | .inl (.inr o), args => pfBlock? o args
  | .inr o, args => castBlock? o args

/-- The block of an expression of `jasField`. -/
def lowerBlock? : {Γ : Ctxt jasField} → {t : jasField.Ty} → Expr jasField Γ t →
    Option (Com jasMod (Γ.map mapTy) (mapTy t))
  | _, _, ⟨op, rfl, args⟩ => opBlock? op args

/-- **The lowering of `jasField` to `jasMod`.** The partial block lowering that keeps the
    operations of `jasminDialect`, lowers the operations of `pfDialect` to `mod_arith` at
    the stored residues, and lowers the casts to the word casts of residues. -/
def fieldToModArithJ : PartialBlockLowering jasField jasMod where
  mapTy := mapTy
  mapCtx := List.map mapTy
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  lowerExprBlock? := lowerBlock?

/-! ## 3. The transports and the leaves -/

/-- The value transport: the identity on a value of `jasminDialect`, the stored residue
    `r.toRep x` on a field value at `pf p r`. -/
def transTy : {t : JasminTy ⊕ PfTy} → ⟦t⟧ → ⟦mapTy t⟧
  | .inl _, x => x
  | .inr (.pf _ r), x => r.toRep x

/-- The valuation transport: `transTy` at every variable. -/
def mapVal {Γ : Ctxt jasField} (V : Valuation Γ) : Valuation (d := jasMod) (Γ.map mapTy) :=
  transArgs mapTy transTy V

/-- A mapped variable reads the transported value. -/
theorem fieldToModArith_lookup_mapVar : ∀ {Γ : Ctxt jasField} {t : jasField.Ty} (v : Var Γ t)
    (V : Valuation Γ), (mapVar v).lookup (mapVal V) = transTy (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => fieldToModArith_lookup_mapVar v xs

/-- The variable leaf of `fieldToModArithJ`. -/
theorem fieldToModArith_varTransports :
    fieldToModArithJ.VarTransports (fun x => transTy x) (fun V => mapVal V) :=
  fun v V => fieldToModArith_lookup_mapVar v V

/-- The binding leaf of `fieldToModArithJ`. -/
theorem fieldToModArith_mapValExtends :
    fieldToModArithJ.MapValExtends (fun x => transTy x) (fun V => mapVal V) :=
  fun _ _ => rfl

/-- The type map of `fieldToModArithJ` keeps the trip-counter type and the bit type. -/
theorem regionTypes : fieldToModArithJ.RegionTypes := ⟨rfl, rfl⟩

/-- The value transport of `fieldToModArithJ` is the identity on the trip counter and the
    bit. -/
theorem regionTransports :
    fieldToModArithJ.RegionTransports regionTypes (fun x => transTy x) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The mapped argument variables of an operation of `jasminDialect` read the argument
    values. -/
theorem unmapInl_lookupArgs_argsJ {Γ : Ctxt jasField} (V : Valuation Γ) :
    {ts : List JasminTy} → (args : HVector (fun t => Var Γ t) (ts.map (Sum.inl (β := PfTy)))) →
    unmapInl (e := modArithDialect) (Expr.lookupArgs (argsJ args) (mapVal V)) =
      unmapInl (e := pfDialect) (Expr.lookupArgs args V)
  | [], _ => rfl
  | _ :: _, .cons v vs =>
      congrArg₂ HVector.cons (fieldToModArith_lookup_mapVar v V)
        (unmapInl_lookupArgs_argsJ V vs)

/-- **The block leaf of `fieldToModArithJ`, forward form.** A source expression that
    succeeds with `x` has a block that succeeds, on the transported valuation, with the
    stored residue of `x`. -/
theorem block_fwd {Γ : Ctxt jasField} {t : jasField.Ty} (e : Expr jasField Γ t) blk
    (hb : fieldToModArithJ.lowerExprBlock? e = some blk) (V : Valuation Γ) (x : ⟦t⟧)
    (hx : e.denoteM (M := Option) V = some x) :
    blk.denoteM (M := Option) (mapVal V) = some (transTy x) := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · cases hb
    have hx' : some (DialectDenote.denote (d := jasminDialect) o
        (unmapInl (e := pfDialect) (Expr.lookupArgs args V))) = some x := hx
    cases hx'
    show some (DialectDenote.denote (d := jasminDialect) o
      (unmapInl (e := modArithDialect) (Expr.lookupArgs (argsJ args) (mapVal V)))) = some _
    rw [unmapInl_lookupArgs_argsJ]
    rfl
  · cases o with
    | add p r =>
        match args with
        | .cons a (.cons b .nil) =>
            cases hb
            have hx' : some (modAddF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            show some (modAddF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar, fieldToModArith_lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_add r _ _)
    | sub p r =>
        match args with
        | .cons a (.cons b .nil) =>
            cases hb
            have hx' : some (modSubF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            show some (modSubF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar, fieldToModArith_lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_sub r _ _)
    | neg p r =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (modNegF (p := p) (a.lookup V)) = some x := hx
            cases hx'
            show some (modNegF ((mapVar a).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_neg r _)
    | mul p r =>
        match args with
        | .cons a (.cons b .nil) =>
            have hx' : some (modMulF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            cases r with
            | canon =>
                cases hb
                show some (modMulF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V)))
                  = _
                rw [fieldToModArith_lookup_mapVar, fieldToModArith_lookup_mapVar]
                rfl
            | mont k =>
                have hb' : (if Nat.Coprime 2 p then some _ else none) = some blk := hb
                split at hb'
                · rename_i h
                  cases hb'
                  have hM : (radixParams k).isMont p = true := decide_eq_true h
                  show some (montMulF ((radixParams k).rInv p) ((mapVar a).lookup (mapVal V))
                    ((mapVar b).lookup (mapVal V))) = _
                  rw [fieldToModArith_lookup_mapVar, fieldToModArith_lookup_mapVar]
                  show some (montMulF _ ((FieldRepr.mont k).toRep _)
                    ((FieldRepr.mont k).toRep _)) = some ((FieldRepr.mont k).toRep _)
                  simp only [FieldRepr.toRep_mont_eq (radixParams k) hM rfl]
                  exact congrArg some (toRep_montMul _ hM _ _)
                · cases hb'
    | square p r =>
        match args with
        | .cons a .nil =>
            have hx' : some (modMulF (p := p) (a.lookup V) (a.lookup V)) = some x := hx
            cases hx'
            cases r with
            | canon =>
                cases hb
                show some (modMulF ((mapVar a).lookup (mapVal V)) ((mapVar a).lookup (mapVal V)))
                  = _
                rw [fieldToModArith_lookup_mapVar]
                rfl
            | mont k =>
                have hb' : (if Nat.Coprime 2 p then some _ else none) = some blk := hb
                split at hb'
                · rename_i h
                  cases hb'
                  have hM : (radixParams k).isMont p = true := decide_eq_true h
                  show some (montMulF ((radixParams k).rInv p) ((mapVar a).lookup (mapVal V))
                    ((mapVar a).lookup (mapVal V))) = _
                  rw [fieldToModArith_lookup_mapVar]
                  show some (montMulF _ ((FieldRepr.mont k).toRep _)
                    ((FieldRepr.mont k).toRep _)) = some ((FieldRepr.mont k).toRep _)
                  simp only [FieldRepr.toRep_mont_eq (radixParams k) hM rfl]
                  exact congrArg some (toRep_montMul _ hM _ _)
                · cases hb'
    | double p r =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (modAddF (p := p) (a.lookup V) (a.lookup V)) = some x := hx
            cases hx'
            show some (modAddF ((mapVar a).lookup (mapVal V)) ((mapVar a).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_add r _ _)
    | const p r c =>
        cases hb
        have hx' : some c = some x := hx
        cases hx'
        rfl
    | copy p r =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (a.lookup V) = some x := hx
            cases hx'
            show some (modCopyF ((mapVar a).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar]
    | toMont p k =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (a.lookup V) = some x := hx
            cases hx'
            show some (modMulF ((mapVar a).lookup (mapVal V)) (2 ^ k)) = _
            rw [fieldToModArith_lookup_mapVar]
            rfl
    | fromMont p k =>
        match args with
        | .cons a .nil =>
            have hx' : some (a.lookup V) = some x := hx
            cases hx'
            have hb' : (if Nat.Coprime 2 p then some _ else none) = some blk := hb
            split at hb'
            · rename_i h
              cases hb'
              show some (montReduceF ((radixParams k).rInv p) ((mapVar a).lookup (mapVal V))) = _
              rw [fieldToModArith_lookup_mapVar]
              exact congrArg some (FieldRepr.ofRep_toRep (r := .mont k) h _)
            · cases hb'
  · cases o with
    | fromWords p r w n =>
        match args with
        | .cons a .nil =>
            have hb' : (if r.Admits p then some _ else none) = some blk := hb
            split at hb'
            · rename_i hr
              cases hb'
              have hx' : fromWordsF p r w n (a.lookup V) = some x := hx
              rw [fromWordsF] at hx'
              split at hx'
              · rename_i hlt
                cases hx'
                show (fromWordsMF p w n ((mapVar a).lookup (mapVal V)) >>= fun v => some v) = _
                rw [fieldToModArith_lookup_mapVar]
                show (fromWordsMF p w n (a.lookup V) >>= fun v => some v) = _
                rw [fromWordsMF, ite_eq_left hlt]
                exact congrArg some (FieldRepr.toRep_ofRep hr _).symm
              · cases hx'
            · cases hb'
    | toWords p r w n =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (toWordsF p r w n (a.lookup V)) = some x := hx
            cases hx'
            show some (toWordsMF p w n ((mapVar a).lookup (mapVal V))) = _
            rw [fieldToModArith_lookup_mapVar]
            rfl

/-! ## 4. The chain stage -/

/-- **The chain stage `jasField → jasMod`.** The lowering of structured programs along
    `fieldToModArithJ`. -/
def fieldToModArithStep (Γ : Ctxt jasField) (ts : List jasField.Ty) :
    PassChain.Step (NFProg jasField Γ ts) (NFProg jasMod (Γ.map mapTy) (ts.map mapTy)) :=
  NFProgPasses.mapStep fieldToModArithJ regionTypes Γ ts

/-- **The certificate of the chain stage.** Under the agreement `hCall` of the call
    environments `E` and `E'` along the transport, `fieldToModArithStep Γ ts` is certified
    from the semantics at `E` to the semantics at `E'`, at every fuel, with the graph of
    `mapVal` as input relation and the graph of the transport of result tuples as output
    relation. -/
def fieldToModArithCert (E : CallEnv jasField) (E' : CallEnv jasMod)
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun y => transTy y) x) (fun _ _ _ => True))
    (fuel : Nat) (Γ : Ctxt jasField) (ts : List jasField.Ty) :
    PassChain.StepCert (fieldToModArithStep Γ ts).run (NFProgPasses.nfSemE E fuel Γ ts)
      (NFProgPasses.nfSemE E' fuel (Γ.map mapTy) (ts.map mapTy)) :=
  PassChain.StepCert.ofMapAtM? fieldToModArithJ regionTypes (fun x => transTy x)
    (fun V => mapVal V) fieldToModArith_varTransports
    (fun e blk hb V x hx => block_fwd e blk hb V x hx)
    fieldToModArith_mapValExtends regionTransports E E' hCall fuel Γ ts

/-! ## 5. The stage is defined at the representation `canon` -/

/-- An operation of `jasField` at the representation `canon`: every operation of
    `jasminDialect`, an operation of `pfDialect` other than `toMont` and `fromMont` whose
    representation is `canon`, and a cast at `canon`. -/
def opCanon : jasField.Op → Bool
  | .inl (.inl _) => true
  | .inl (.inr (.add _ .canon)) => true
  | .inl (.inr (.sub _ .canon)) => true
  | .inl (.inr (.neg _ .canon)) => true
  | .inl (.inr (.mul _ .canon)) => true
  | .inl (.inr (.square _ .canon)) => true
  | .inl (.inr (.double _ .canon)) => true
  | .inl (.inr (.const _ .canon _)) => true
  | .inl (.inr (.copy _ .canon)) => true
  | .inr (.fromWords _ .canon _ _) => true
  | .inr (.toWords _ .canon _ _) => true
  | _ => false

/-- An expression whose operation is at the representation `canon` has a block. -/
theorem lowerBlock?_isSome_of_opCanon {Γ : Ctxt jasField} {t : jasField.Ty}
    (e : Expr jasField Γ t) (h : opCanon e.op = true) :
    (fieldToModArithJ.lowerExprBlock? e).isSome = true := by
  obtain ⟨op, rfl, args⟩ := e
  rcases op with (o | o) | o
  · rfl
  · cases o with
    | mul _ r => cases r <;> first | rfl | (simp [opCanon] at h)
    | square _ r => cases r <;> first | rfl | (simp [opCanon] at h)
    | fromMont => simp [opCanon] at h
    | _ => rfl
  · cases o <;> rename_i r _ _ <;> cases r <;> first | rfl | (simp [opCanon] at h)

/-- **`map?` is defined at the representation `canon`.** At every renaming, `map?` along
    `fieldToModArithJ` returns a program on every program each of whose let-bound
    expressions, in every region, has its operation at the representation `canon`. -/
theorem isSome_map?_of_opCanon {Γ : Ctxt jasField} {ts : List jasField.Ty}
    (p : NFProg jasField Γ ts) (hp : p.Covered (fun {_ _} e => opCanon e.op = true))
    {Δ : Ctxt jasMod} (ren : Ctxt.Hom (fieldToModArithJ.mapCtx Γ) Δ) :
    (NFProg.map? fieldToModArithJ regionTypes p ren).isSome = true :=
  (NFProg.isSome_map?_iff fieldToModArithJ regionTypes p ren).2
    (NFProg.Covered.mono (fun e he => lowerBlock?_isSome_of_opCanon e he) hp)

/-- The chain stage returns a program on every program whose operations are at the
    representation `canon`. -/
theorem fieldToModArithStep_isSome {Γ : Ctxt jasField} {ts : List jasField.Ty}
    (p : NFProg jasField Γ ts) (hp : p.Covered (fun {_ _} e => opCanon e.op = true)) :
    ((fieldToModArithStep Γ ts).run p).isSome = true :=
  isSome_map?_of_opCanon p hp _

/-! ## 6. The call environment of `jasMod` along `Sum.inl` -/

/-- The types of `jasminDialect` a list of types of `jasMod` holds, or `none` when a type of
    `modArithDialect` occurs. -/
def ofInlM? : List (JasminTy ⊕ ModArithTy) → Option (List JasminTy)
  | [] => some []
  | .inl t :: as => (ofInlM? as).map (t :: ·)
  | .inr _ :: _ => none

/-- An injected list of types is read back. -/
theorem ofInlM?_map : ∀ as : List JasminTy, ofInlM? (as.map Sum.inl) = some as
  | [] => rfl
  | t :: as => by simp [ofInlM?, ofInlM?_map as]

/-- A list read back is the injection of the result. -/
theorem map_inl_of_ofInlM? : ∀ {as : List (JasminTy ⊕ ModArithTy)} {bs : List JasminTy},
    ofInlM? as = some bs → bs.map Sum.inl = as
  | [], bs, h => by cases h; rfl
  | .inl t :: as, bs, h => by
      simp only [ofInlM?, Option.map_eq_some_iff] at h
      obtain ⟨cs, hcs, rfl⟩ := h
      simp [map_inl_of_ofInlM? hcs]
  | .inr _ :: _, _, h => by cases h

/-- The valuation of the injected types of `jasMod`: the identity on every value. -/
def liftVM {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as) :
    HVector (fun t => ⟦t⟧) (as.map (Sum.inl (β := ModArithTy))) :=
  transArgs Sum.inl (fun x => x) x

/-- Stripping the tags of an injected valuation gives the valuation. -/
theorem unmapInl_liftVM : ∀ {as : List JasminTy} (x : HVector (fun t => ⟦t⟧) as),
    unmapInl (d := jasminDialect) (e := modArithDialect) (liftVM x) = x
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (HVector.cons _) (unmapInl_liftVM xs)

/-- A valuation of `jasMod` carried along an equality of type lists. -/
def castVM {as bs : List (JasminTy ⊕ ModArithTy)} (h : as = bs)
    (x : HVector (fun t => ⟦t⟧) as) : HVector (fun t => ⟦t⟧) bs :=
  h ▸ x

/-- The callee of the symbol `f` at injected types of `jasMod`: the callee of `E` at the
    types of `jasminDialect` they inject, on the stripped arguments, with the injected
    results; no callee at a list of types in which a type of `modArithDialect` occurs. -/
def liftCallM (E : CallEnv jasminDialect) (f : String) (as rs : List (JasminTy ⊕ ModArithTy))
    (x : HVector (fun t => ⟦t⟧) as) : Option (HVector (fun t => ⟦t⟧) rs) :=
  match ha : ofInlM? as, hr : ofInlM? rs with
  | some as', some rs' =>
      (E.call f as' rs'
        (unmapInl (d := jasminDialect) (e := modArithDialect)
          (castVM (map_inl_of_ofInlM? ha).symm x))).map
        fun y => castVM (map_inl_of_ofInlM? hr) (liftVM y)
  | _, _ => none

/-- At injected types, `liftCallM E` answers what `E` answers, injected. -/
theorem liftCallM_liftVM (E : CallEnv jasminDialect) (f : String) (as rs : List JasminTy)
    (x : HVector (fun t => ⟦t⟧) as) :
    liftCallM E f (as.map Sum.inl) (rs.map Sum.inl) (liftVM x) =
      (E.call f as rs x).map liftVM := by
  unfold liftCallM
  split
  · rename_i as' rs' ha hr
    rw [ofInlM?_map] at ha hr
    cases ha
    cases hr
    simp only [castVM, unmapInl_liftVM]
  · rename_i h
    exact absurd (ofInlM?_map as) (fun e => h _ _ e (ofInlM?_map rs))

/-- **The call environment of `jasMod`** from a call environment of `jasminDialect`: a
    symbol at injected types is answered by `E`, and refuses at a signature in which a type
    of `modArithDialect` occurs. -/
def liftEnvM (E : CallEnv jasminDialect) : CallEnv jasMod := ⟨liftCallM E⟩

/-! ## 7. The events of the stage -/

section Events

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (ExprEv)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak.NFProg (leakRunMC)

/-- The readings under `jasModLeak M N` of injected values of `jasminDialect` are their
    readings under `M`. -/
theorem valsNat_jasModLeak_inl (M : LeakModel jasminDialect) (N : LeakModel modArithDialect) :
    ∀ {ts : List JasminTy} (vals : HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := ModArithTy)))),
      valsNat (jasModLeak M N) vals =
        valsNat M (unmapInl (d := jasminDialect) (e := modArithDialect) vals)
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (List.cons _) (valsNat_jasModLeak_inl M N xs)

/-- The readings under `jasFieldLeak M` of injected values of `jasminDialect` are their
    readings under `M`. -/
theorem valsNat_jasFieldLeak_inl (M : LeakModel jasminDialect) :
    ∀ {ts : List JasminTy} (vals : HVector (fun t => ⟦t⟧) (ts.map (Sum.inl (β := PfTy)))),
      valsNat (jasFieldLeak M) vals =
        valsNat M (unmapInl (d := jasminDialect) (e := pfDialect) vals)
  | [], .nil => rfl
  | _ :: _, .cons _ xs => congrArg (List.cons _) (valsNat_jasFieldLeak_inl M xs)

/-- **The blocks of an expression emit its events.** At a leakage model `N` of
    `modArithDialect` whose operations are quiet, the block events of `fieldToModArithJ` at
    `jasModLeak M N` are the events of `jasFieldLeak M`: an operation of `jasminDialect` emits
    its own events in its block, and the operations of `pfDialect`, the casts and their blocks
    emit none. -/
theorem blockEvO_eq (M : LeakModel jasminDialect) (N : LeakModel modArithDialect)
    (hN : ∀ o, N.kind o = .quiet) :
    blockEvO fieldToModArithJ (fun V => mapVal V) (jasModLeak M N : ExprEv jasMod) =
      (jasFieldLeak M : ExprEv jasField) := by
  have hE : ∀ {Δ : Ctxt jasMod} {t : jasMod.Ty} (m : ModArithOp)
      (h : DialectSignature.ret (d := jasMod) (.inl (.inr m)) = t)
      (args : HVector (fun t => Var Δ t) (DialectSignature.sig (d := jasMod) (.inl (.inr m))))
      (W : Valuation Δ),
      Expr.ctLeak (jasModLeak M N) (⟨.inl (.inr m), h, args⟩ : Expr jasMod Δ t) W = [] :=
    fun m _ _ W => Expr.ctLeak_of_quiet _ _ (hN m) W
  have hC : ∀ {Δ : Ctxt jasMod} {t : jasMod.Ty} (o : ModWordCastOp)
      (h : DialectSignature.ret (d := jasMod) (.inr o) = t)
      (args : HVector (fun t => Var Δ t) (DialectSignature.sig (d := jasMod) (.inr o)))
      (W : Valuation Δ),
      Expr.ctLeak (jasModLeak M N) (⟨.inr o, h, args⟩ : Expr jasMod Δ t) W = [] :=
    fun o _ _ W => jasModLeak_ctLeak_cast M N _ o rfl W
  have key : ∀ {Γ : Ctxt jasField} {t : jasField.Ty} (e : Expr jasField Γ t)
      (V : Valuation Γ),
      (blockEvO fieldToModArithJ (fun V => mapVal V) (jasModLeak M N : ExprEv jasMod)).ev
        _ _ e V = Expr.ctLeak (jasFieldLeak M) e V := by
    intro Γ t e V
    obtain ⟨op, rfl, args⟩ := e
    rcases op with (o | o) | o
    · show Com.ctLeakO _ (opB (Δ := Γ.map mapTy) (.inl (.inl o)) (argsJ args)) (mapVal V) = _
      simp only [Com.ctLeakO]
      split <;> simp only [List.append_nil] <;>
        (unfold Expr.ctLeak opLeak
         simp only [valsNat_jasModLeak_inl, valsNat_jasFieldLeak_inl, unmapInl_lookupArgs_argsJ]
         rfl)
    · rw [Expr.ctLeak_of_quiet _ _ rfl]
      rcases o with ⟨p, _ | k⟩ | ⟨p, _ | k⟩ | ⟨p, _ | k⟩ | ⟨p, _ | k⟩ | ⟨p, _ | k⟩ |
        ⟨p, _ | k⟩ | ⟨p, _ | k, c⟩ | ⟨p, _ | k⟩ | ⟨p, k⟩ | ⟨p, k⟩
      all_goals
        simp only [blockEvO, fieldToModArithJ, lowerBlock?, opBlock?, pfBlock?]
        try split
      all_goals try simp only [Com.ctLeakO, hE, List.nil_append]
      all_goals first
        | (split <;> (try split) <;> rfl)
        | (rename_i hb
           split at hb
           · cases hb
             simp only [Com.ctLeakO, hE, List.nil_append]
             split <;> rfl
           · cases hb)
    · rw [Expr.ctLeak_of_quiet _ _ (by cases o <;> rfl)]
      rcases o with ⟨p, _ | k, w, n⟩ | ⟨p, _ | k, w, n⟩
      all_goals
        simp only [blockEvO, fieldToModArithJ, lowerBlock?, opBlock?, castBlock?]
        try split
      all_goals try simp only [Com.ctLeakO, hC, List.nil_append]
      all_goals first
        | (split <;> rfl)
        | (rename_i hb
           split at hb
           · cases hb
             simp only [Com.ctLeakO, hC, List.nil_append]
             split <;> rfl
           · cases hb)
  show (⟨_⟩ : ExprEv jasField) = ⟨_⟩
  congr
  funext Γ t e V
  exact key e V

/-- **The leakage run of the stage.** At a leakage model `N` of `modArithDialect` whose
    operations are quiet, and call environments `E` and `E'` that agree along the transport at
    the calls of `p`, a successful leakage run of `p` at `E` with the events of
    `jasFieldLeak M` is matched by a run of the lowered program at `E'` with the events of
    `jasModLeak M N`, from the transported valuation to the transported results and to the
    same events. -/
theorem fieldToModArithStep_leakRunMC (M : LeakModel jasminDialect)
    (N : LeakModel modArithDialect) (hN : ∀ o, N.kind o = .quiet) (E : CallEnv jasField)
    (E' : CallEnv jasMod) (fuel : Nat) {Γ : Ctxt jasField} {ts : List jasField.Ty}
    {p : NFProg jasField Γ ts} {q : NFProg jasMod (Γ.map mapTy) (ts.map mapTy)}
    (hf : (fieldToModArithStep Γ ts).run p = some q)
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun y => transTy y) x) p.Calls)
    {V : Valuation Γ} {r : Valuation ts × List CTLeak}
    (h : leakRunMC (jasFieldLeak M) E fuel p V = some r) :
    leakRunMC (jasModLeak M N) E' fuel q (mapVal V) =
      some (transArgs mapTy (fun y => transTy y) r.1, r.2) :=
  map?_leakRunMC_blockEvO fieldToModArithJ (fun x => transTy x) (fun V => mapVal V)
    (jasModLeak M N) regionTypes fieldToModArith_varTransports
    (fun e blk hb V x hx => block_fwd e blk hb V x hx) fieldToModArith_mapValExtends
    regionTransports E E' fuel p hCall (fun v => v) V (mapVal V) (NFProg.renRel_id _) q hf r
    (by rw [blockEvO_eq M N hN]; exact h)

/-- **Two leakage runs before the stage give two runs of its result, with equal events from
    equal events.** At a leakage model `N` of `modArithDialect` whose operations are quiet,
    and call environments `E` and `E'` that agree along the transport at the calls of `p`, two
    runs of the source program at `E` are matched by runs of the lowered program at `E'` from
    the transported valuations to the transported results; when the source events are equal,
    so are the events of the two lowered runs. -/
theorem fieldToModArithStep_leakRunC (M : LeakModel jasminDialect)
    (N : LeakModel modArithDialect) (hN : ∀ o, N.kind o = .quiet) (E : CallEnv jasField)
    (E' : CallEnv jasMod) (fuel : Nat) {Γ : Ctxt jasField} {ts : List jasField.Ty}
    {p : NFProg jasField Γ ts} {q : NFProg jasMod (Γ.map mapTy) (ts.map mapTy)}
    (hf : (fieldToModArithStep Γ ts).run p = some q)
    (hCall : E.Transports E' (fun as => as.map mapTy)
      (fun x => transArgs mapTy (fun y => transTy y) x) p.Calls)
    {V₁ V₂ : Valuation Γ} {r₁ r₂ : Valuation ts × List CTLeak}
    (h₁ : leakRunMC (jasFieldLeak M) E fuel p V₁ = some r₁)
    (h₂ : leakRunMC (jasFieldLeak M) E fuel p V₂ = some r₂) :
    ∃ l₁ l₂,
      leakRunMC (jasModLeak M N) E' fuel q (mapVal V₁) =
          some (transArgs mapTy (fun y => transTy y) r₁.1, l₁) ∧
        leakRunMC (jasModLeak M N) E' fuel q (mapVal V₂) =
          some (transArgs mapTy (fun y => transTy y) r₂.1, l₂) ∧
        (r₁.2 = r₂.2 → l₁ = l₂) :=
  ⟨r₁.2, r₂.2, fieldToModArithStep_leakRunMC M N hN E E' fuel hf hCall h₁,
    fieldToModArithStep_leakRunMC M N hN E E' fuel hf hCall h₂, id⟩

end Events

end CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain
