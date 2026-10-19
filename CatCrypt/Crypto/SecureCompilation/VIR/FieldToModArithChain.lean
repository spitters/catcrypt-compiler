/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMapM

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

## Main results

* `lookup_mapVar`, `varTransports`, `mapValExtends`, `regionTypes`, `regionTransports`: the
  leaves of the lowering other than the block leaf.
* `block_fwd`: a successful source expression has a successful block with the stored
  residue of its value.
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
instance decAdmissible (p : Nat) : (r : FieldRepr) → Decidable (r.Admissible p)
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
      if r.Admissible p then
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
theorem lookup_mapVar : ∀ {Γ : Ctxt jasField} {t : jasField.Ty} (v : Var Γ t)
    (V : Valuation Γ), (mapVar v).lookup (mapVal V) = transTy (v.lookup V)
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ xs => lookup_mapVar v xs

/-- The variable leaf of `fieldToModArithJ`. -/
theorem varTransports :
    fieldToModArithJ.VarTransports (fun x => transTy x) (fun V => mapVal V) :=
  fun v V => lookup_mapVar v V

/-- The binding leaf of `fieldToModArithJ`. -/
theorem mapValExtends :
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
      congrArg₂ HVector.cons (lookup_mapVar v V) (unmapInl_lookupArgs_argsJ V vs)

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
            rw [lookup_mapVar, lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_add r _ _)
    | sub p r =>
        match args with
        | .cons a (.cons b .nil) =>
            cases hb
            have hx' : some (modSubF (p := p) (a.lookup V) (b.lookup V)) = some x := hx
            cases hx'
            show some (modSubF ((mapVar a).lookup (mapVal V)) ((mapVar b).lookup (mapVal V))) = _
            rw [lookup_mapVar, lookup_mapVar]
            exact congrArg some (FieldRepr.toRep_sub r _ _)
    | neg p r =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (modNegF (p := p) (a.lookup V)) = some x := hx
            cases hx'
            show some (modNegF ((mapVar a).lookup (mapVal V))) = _
            rw [lookup_mapVar]
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
                rw [lookup_mapVar, lookup_mapVar]
                rfl
            | mont k =>
                have hb' : (if Nat.Coprime 2 p then some _ else none) = some blk := hb
                split at hb'
                · rename_i h
                  cases hb'
                  have hM : (radixParams k).isMont p = true := decide_eq_true h
                  show some (montMulF ((radixParams k).rInv p) ((mapVar a).lookup (mapVal V))
                    ((mapVar b).lookup (mapVal V))) = _
                  rw [lookup_mapVar, lookup_mapVar]
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
                rw [lookup_mapVar]
                rfl
            | mont k =>
                have hb' : (if Nat.Coprime 2 p then some _ else none) = some blk := hb
                split at hb'
                · rename_i h
                  cases hb'
                  have hM : (radixParams k).isMont p = true := decide_eq_true h
                  show some (montMulF ((radixParams k).rInv p) ((mapVar a).lookup (mapVal V))
                    ((mapVar a).lookup (mapVal V))) = _
                  rw [lookup_mapVar]
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
            rw [lookup_mapVar]
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
            rw [lookup_mapVar]
    | toMont p k =>
        match args with
        | .cons a .nil =>
            cases hb
            have hx' : some (a.lookup V) = some x := hx
            cases hx'
            show some (modMulF ((mapVar a).lookup (mapVal V)) (2 ^ k)) = _
            rw [lookup_mapVar]
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
              rw [lookup_mapVar]
              exact congrArg some (FieldRepr.ofRep_toRep (r := .mont k) h _)
            · cases hb'
  · cases o with
    | fromWords p r w n =>
        match args with
        | .cons a .nil =>
            have hb' : (if r.Admissible p then some _ else none) = some blk := hb
            split at hb'
            · rename_i hr
              cases hb'
              have hx' : fromWordsF p r w n (a.lookup V) = some x := hx
              rw [fromWordsF] at hx'
              split at hx'
              · rename_i hlt
                cases hx'
                show (fromWordsMF p w n ((mapVar a).lookup (mapVal V)) >>= fun v => some v) = _
                rw [lookup_mapVar]
                show (fromWordsMF p w n (a.lookup V) >>= fun v => some v) = _
                rw [fromWordsMF, if_pos hlt]
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
            rw [lookup_mapVar]
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
    (fun V => mapVal V) varTransports (fun e blk hb V x hx => block_fwd e blk hb V x hx)
    mapValExtends regionTransports E E' hCall fuel Γ ts

end CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain
