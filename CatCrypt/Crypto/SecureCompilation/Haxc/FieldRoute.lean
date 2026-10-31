/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbsSolinas
public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

@[expose] public section

set_option autoImplicit false

/-!
# The field route: a field program to a route's program over word arrays

For a modulus record `P : LimbParams n` and a field program `c` over the source context
`Γ`, `compileField P c` is the straight-line route program `fieldCom P c` of
`FieldToJasminLimbs` when the coverage decision `GoodVB` accepts `c`. Its context is a
word array of `n` limbs for each source variable followed by the output array, and its
result is the last stored output array.

For a Solinas record `S : SolinasParams n` (`p = 2^k - c`), `compileFieldS S c` is the
same program over the blocks of `FieldToJasminLimbsSolinas`, which carry an element by the
limbs of its canonical representative.

Both are the run of a `PassChain.Chain` of the shape `limbChainVia opt good low`: the
optimisation step `opt` on `Com fieldDialect`, the limb lowering `low` guarded by the
coverage decision `good` (`limbStep`), the identity at the jasmin level and the route
wrapper. `compileField P` is the run of `fieldChainId P` and `compileFieldS S` the run of
`fieldChainSId S`, at the identity step `Step.id`. The denotation theorems
`compileField_denote` and `compileFieldS_denote` follow from `Cert.sound` of the
chain certificate `limbChainViaCert`. A `FieldTemplate n` bundles a modulus, its limb
encoding and a route compiler with its denotation theorem; `montTemplate` and
`solinasTemplate` are the two instances. A template is a function from a parameter record to
straight-line word arithmetic with one denotation theorem over every record; an instance
contributes its record, whose proof fields are its certificate. The byte-level statement over
the templates is `field_correct_bytes` (`Haxc/FieldBytes.lean`).

For a program over `Γ` the System V layout `fieldAbi |Γ| n` passes the output array in
`%rdi` and the operand `i` in the register of the parameter `|Γ| - i` (`%rsi`, `%rdx`,
`%rcx`, `%r8`, `%r9`), each a `words n` parameter, and reads back the `n` words at the entry
`%rdi`. `abiValN n sa Γ` is the valuation of the program's context read off a machine state
`sa`, and `abiValOf_fieldAbi` states that the layout reads it off `sa` (`AbiValOf`), the
hypothesis `RegionBackend.compileRegion_correct` takes. The binary layout `fieldAbi2 n` is
`fieldAbi 2 n`: the second operand in `%rsi` and the first in `%rdx`.

## Main results

* `LimbCtx`, `limbStep`, `limbIn`, `limbCert`: the limb lowering as a chain step and its
  certificate.
* `limbChainVia`, `limbChainViaCert`, `limbChainVia_denote`: the limb chain at an
  optimisation step, its certificate, and the output limbs of a program it produces.
* `fieldChainId`, `fieldChainSId`: the limb chains at the identity step at a Montgomery and
  a Solinas record.
* `compileField_eq`, `compileFieldS_eq`: the runs of these chains.
* `compileField`, `compileField_denote`: the route program of a covered field program,
  and its output array, whose limbs are the encoding of the program's value.
* `compileFieldS`, `compileFieldS_denote`: the same at a Solinas modulus.
* `FieldTemplate`, `montTemplate`, `solinasTemplate`, `FieldTemplate.route_abi_denote`: the
  templates, and the output limbs of a routed program at the valuation of a machine state.
* `fieldAbi`, `abiValN`, `abiValOf_fieldAbi`: the layout of a field program of any arity
  and the valuation it reads off a machine state.
* `fieldAbi2`, `abiVal2`, `abiValOf_fieldAbi2`, `compileField2_denote`: the binary
  instance, and the output limbs of a compiled binary program at a machine state.
* `mulProg`, `compileField_mul`, `fieldMul_denote`: the field product as a program, its
  route program at every modulus record, and its output limbs at the valuation of a
  machine state whose input arrays hold the encodings of `x` and `y`.
* `mulConstProg`, `addProg`, `mulConstProg_covered`, `addProg_covered`: the programs
  `x * y * c` and `x + y`, and their coverage at every modulus record.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)

/-! ## 0. The limb chain -/

section Limb

variable {n : Nat} {Γ : Ctxt fieldDialect} {t : FieldTy}

/-- The context of a lowered field program over `Γ`: a word array of `n` limbs per source
    variable, then the output array. -/
abbrev LimbCtx (n : Nat) (Γ : Ctxt fieldDialect) : Ctxt jasminDialect :=
  arrCtx n Γ ++ [arrTy n]

/-- The limb lowering `low` as a chain step: it refuses a program that `good` rejects. -/
def limbStep (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n)) :
    Step (Com fieldDialect Γ t) (Com jasminDialect (LimbCtx n Γ) (arrTy n)) :=
  ⟨"fieldLimbs", fun c => if good c then some (low c) else none⟩

/-- The input relation of the limb lowering at the encoding `enc`: the input arrays hold
    the limbs of the values of `V`, and the output array is arbitrary. -/
def limbIn (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t)) (V : Valuation Γ)
    (W : Valuation (LimbCtx n Γ)) : Prop :=
  ∃ (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64),
    @Eq (Valuation (LimbCtx n Γ)) W (hvAppend A (.cons o .nil)) ∧
      arrFlat A = flatVal (fun {t} x => enc (t := t) x) V

/-- The certificate of the limb lowering, from a denotation theorem `h` of `low` on the
    programs `good` accepts: the input relation is `limbIn enc`, and the output relation
    says that the output array holds the limbs of the source value. -/
def limbCert (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t))
    (h : ∀ c, good c = true → ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
      (o : Fin n → BitVec 64), arrFlat A = flatVal (fun {t} x => enc (t := t) x) V →
      arrLimbs ((low c).denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V)) :
    StepCert (limbStep good low).run (comSemOf fieldDialect Γ t)
      (comSemOf jasminDialect (LimbCtx n Γ) (arrTy n)) where
  relIn := limbIn enc
  relOut x y := arrLimbs y n 0 = enc x
  sound := by
    intro c q V W o hf hVW hd
    obtain ⟨A, o', rfl, hA⟩ := hVW
    simp only [limbStep] at hf
    split at hf
    · rename_i hc
      cases hf
      cases hd
      exact ⟨_, rfl, h c hc V A o' hA⟩
    · cases hf

/-- **The limb chain at the optimisation step `opt`**: the step `opt` on `Com fieldDialect`,
    the limb lowering `low` guarded by `good`, the identity at the jasmin level and the
    route wrapper. -/
def limbChainVia (opt : Step (Com fieldDialect Γ t) (Com fieldDialect Γ t))
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n)) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  .cons opt <| .cons (limbStep good low) <| .cons (Step.id _) <|
    .cons (straightStep _ _) <| .nil _

/-- **The certificate of the limb chain at `opt`**, for a step `opt` whose output has the
    denotation of its input (`hopt`): one step certificate per step. -/
def limbChainViaCert (opt : Step (Com fieldDialect Γ t) (Com fieldDialect Γ t))
    (hopt : ∀ c q, opt.run c = some q → q.denote = c.denote)
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t))
    (h : ∀ c, good c = true → ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
      (o : Fin n → BitVec 64), arrFlat A = flatVal (fun {t} x => enc (t := t) x) V →
      arrLimbs ((low c).denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V)) :
    Cert (limbChainVia opt good low) (comSemOf fieldDialect Γ t)
      (routeSem (LimbCtx n Γ) (arrTy n)) :=
  .cons (StepCert.ofDenoteEq _ fun c q hf => by
      funext V
      show some _ = some _
      rw [hopt c q hf]) <|
    .cons (limbCert good low enc h) <| .cons (StepCert.id _) <|
    .cons (straightCert _ _) <| .nil _

/-- **The output limbs of a program of the limb chain at `opt`**, from `Cert.sound` of
    `limbChainViaCert`: for input arrays holding the limbs of the values of `V`, the output
    array holds the limbs of the value of the source program. -/
theorem limbChainVia_denote (opt : Step (Com fieldDialect Γ t) (Com fieldDialect Γ t))
    (hopt : ∀ c q, opt.run c = some q → q.denote = c.denote)
    (good : Com fieldDialect Γ t → Bool)
    (low : Com fieldDialect Γ t → Com jasminDialect (LimbCtx n Γ) (arrTy n))
    (enc : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t))
    (h : ∀ c, good c = true → ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
      (o : Fin n → BitVec 64), arrFlat A = flatVal (fun {t} x => enc (t := t) x) V →
      arrLimbs ((low c).denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V))
    {c : Com fieldDialect Γ t} {rp : RouteProg (LimbCtx n Γ) (arrTy n)}
    (hrun : (limbChainVia opt good low).run c = some rp) (V : Valuation Γ)
    (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => enc (t := t) x) V) :
    arrLimbs (rp.denote (hvAppend A (.cons o .nil))) n 0 = enc (c.denote V) := by
  obtain ⟨o', ho', x, hx, y, hy, z, hz, w, hw, hwo⟩ :=
    (limbChainViaCert opt hopt good low enc h).sound (V := V) (W := hvAppend A (.cons o .nil))
      (o := c.denote V) hrun
      ⟨V, rfl, _, ⟨A, o, rfl, hA⟩, _, rfl, _, rfl, rfl⟩ rfl
  cases ho'
  cases hx
  cases hz
  cases hw
  cases hwo
  exact hy

/-- The identity step has the denotation of its input. -/
theorem stepId_denote (c q : Com fieldDialect Γ t) (hf : (Step.id _).run c = some q) :
    q.denote = c.denote := by
  cases hf
  rfl

end Limb

/-- **The field chain at the identity step** at the Montgomery record `P`: the limb chain
    at `Step.id`, `GoodVB P` and `fieldCom P`. -/
def fieldChainId {n : Nat} (P : LimbParams n) (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  limbChainVia (Step.id _) (GoodVB P) (fieldCom P)

/-- **The Solinas field chain at the identity step** at the Solinas record `S`: the limb
    chain at `Step.id`, `GoodLB S` and the Solinas blocks `lowerOpL S`. -/
def fieldChainSId {n : Nat} (S : SolinasParams n) (Γ : Ctxt fieldDialect) (t : FieldTy) :
    Chain (Com fieldDialect Γ t) (RouteProg (LimbCtx n Γ) (arrTy n)) :=
  limbChainVia (Step.id _) (FieldToJasminLimbsSolinas.GoodLB S)
    (fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S))

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams enc)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Solinas (SolinasParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn argIdx)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain (Chain Step)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain (limbChainVia limbChainVia_denote limbStep
  stepId_denote fieldChainId fieldChainSId)

/-! ## 1. The route program -/

section Route

variable {n : Nat} (P : LimbParams n)

/-- **The route program of a field program**: the run of the field chain at the identity
    step `fieldChainId P`. -/
def compileField {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Option (RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)) :=
  (fieldChainId P Γ t).run c

/-- The route program of a field program is the straight-line program `fieldCom P c` over
    word arrays when `GoodVB` accepts `c`, and `none` otherwise. -/
theorem compileField_eq {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    compileField P c = if GoodVB P c then some (.straight (fieldCom P c)) else none := by
  simp only [compileField, fieldChainId, limbChainVia, Chain.run, Step.id, limbStep,
    Option.bind_some]
  split <;> rfl

/-- **The output array of a compiled field program**, from `Cert.sound` of the chain
    certificate. For a route program of a field program `c` and input arrays whose limbs
    are the encodings of the values of `V`, the output array holds the limbs of the
    encoding of `c.denote V`. -/
theorem compileField_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    {c : Com fieldDialect Γ t} {p : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : compileField P c = some p) (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
    (o : Fin n → BitVec 64) (hA : arrFlat A = flatVal (fun {t} x => encL P (t := t) x) V) :
    arrLimbs (p.denote (hvAppend A (.cons o .nil))) n 0 = encL P (c.denote V) :=
  limbChainVia_denote (Step.id _) stepId_denote _ _ (fun {t} x => encL P (t := t) x)
    (fun c hc => fieldCom_denote P hn c (GoodVB_sound P c hc)) h V A o hA

end Route

/-! ## 2. The route program at a Solinas modulus -/

section Solinas

variable {n : Nat} (S : SolinasParams n)

/-- **The route program of a field program at a Solinas modulus**: the run of the Solinas
    field chain at the identity step `fieldChainSId S`. -/
def compileFieldS {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    Option (RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)) :=
  (fieldChainSId S Γ t).run c

/-- The route program of a field program at a Solinas modulus is the straight-line program
    `fieldComOf (lowerOpL S) c` over word arrays when `GoodLB` accepts `c`, and `none`
    otherwise. -/
theorem compileFieldS_eq {Γ : Ctxt fieldDialect} {t : FieldTy} (c : Com fieldDialect Γ t) :
    compileFieldS S c =
      if FieldToJasminLimbsSolinas.GoodLB S c then
        some (.straight (fieldComOf (FieldToJasminLimbsSolinas.lowerOpL S) c))
      else none := by
  simp only [compileFieldS, fieldChainSId, limbChainVia, Chain.run, Step.id, limbStep,
    Option.bind_some]
  split <;> rfl

/-- **The output array of a compiled field program at a Solinas modulus**, from
    `Cert.sound` of the chain certificate. For input arrays whose limbs are the encodings of
    the values of `V`, the output array holds the limbs of the encoding of `c.denote V`. -/
theorem compileFieldS_denote (hn : n < 2 ^ 64) {Γ : Ctxt fieldDialect} {t : FieldTy}
    {c : Com fieldDialect Γ t} {p : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : compileFieldS S c = some p) (V : Valuation Γ) (A : Valuation (arrCtx n Γ))
    (o : Fin n → BitVec 64)
    (hA : arrFlat A = flatVal (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x) V) :
    arrLimbs (p.denote (hvAppend A (.cons o .nil))) n 0
      = FieldToJasminLimbsSolinas.encL S (c.denote V) :=
  limbChainVia_denote (Step.id _) stepId_denote _ _
    (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x)
    (fun c hc => fieldComOf_denote (FieldToJasminLimbsSolinas.lowerOpL S)
      (fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x)
      (FieldToJasminLimbsSolinas.GoodL S) (FieldToJasminLimbsSolinas.blockSquareL S) hn c
      (FieldToJasminLimbsSolinas.GoodLB_sound S c hc)) h V A o hA

end Solinas

/-! ## 3. Field templates -/

/-- **A field template over `n` limbs**: a modulus `p`, the encoding `enc` of an element of
    `ZMod p` as `n` limbs (extended by `encL` to every field type), and a partial compiler
    `route` from field programs to route programs over word arrays whose output array holds
    the encoding of the program's value. -/
structure FieldTemplate (n : Nat) where
  /-- The modulus. -/
  p : Nat
  one_lt : 1 < p
  /-- The limbs of an element. -/
  enc : ZMod p → ListDenote (Mont.Rn n)
  /-- The limbs of a value of every field type. -/
  encL : ∀ {t : fieldDialect.Ty}, ⟦t⟧ → Valuation (mapTysL n t)
  encL_fp : ∀ x : ZMod p, encL (t := .fp p) x = enc x
  /-- The route program of a field program, when the template covers it. -/
  route : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Com fieldDialect Γ t →
    Option (RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n))
  route_denote : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy} {c : Com fieldDialect Γ t}
    {rp : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}, route c = some rp →
    ∀ (V : Valuation Γ) (A : Valuation (arrCtx n Γ)) (o : Fin n → BitVec 64),
      arrFlat A = flatVal (fun {t} x => encL (t := t) x) V →
      arrLimbs (rp.denote (hvAppend A (.cons o .nil))) n 0 = encL (c.denote V)

/-- **The Montgomery template** of the record `P`: Montgomery limbs, routed by
    `compileField P`. -/
def montTemplate {n : Nat} (P : LimbParams n) (hn : n < 2 ^ 64) : FieldTemplate n where
  p := P.p
  one_lt := P.one_lt
  enc := enc P
  encL := fun {t} x => encL P (t := t) x
  encL_fp := encL_fp P
  route := fun c => compileField P c
  route_denote := fun h => compileField_denote P hn h

/-- **The Solinas template** of the record `S`: the limbs of the canonical representative,
    routed by `compileFieldS S`. -/
def solinasTemplate {n : Nat} (S : SolinasParams n) (hn : n < 2 ^ 64) : FieldTemplate n where
  p := Solinas.p S
  one_lt := by have := Solinas.c_add_three_lt S; simp only [Solinas.p]; omega
  enc := Solinas.enc S
  encL := fun {t} x => FieldToJasminLimbsSolinas.encL S (t := t) x
  encL_fp := FieldToJasminLimbsSolinas.encL_fp S
  route := fun c => compileFieldS S c
  route_denote := fun h => compileFieldS_denote S hn h

/-! ## 4. The layout of a field program of any arity -/

/-- The System V register of the parameter `j`: `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`,
    `%r9`. -/
def fieldArgReg (j : Nat) : String := ["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"].getD j ""

/-- The name of the parameter `j` of a field program of arity `m`: `out` for the output
    array, and `x`, `y`, `z`, `u`, `v` for the operands in source order. -/
def fieldArgName (m j : Nat) : String :=
  if j = 0 then "out" else ["x", "y", "z", "u", "v"].getD (m - j) ""

/-- **The layout of a field program of arity `m` over `n` limbs**: the output array in
    `%rdi` and the operand `i` in the System V register of the parameter `m - i`, each of
    `n` words; the result is the `n` words at the entry `%rdi`; the body's stack words lie in
    the `4096` bytes below the entry `%rsp`. -/
def fieldAbi (m n : Nat) : AbiLayout where
  args := (List.range (m + 1)).map fun j => ⟨fieldArgName m j, fieldArgReg j, .words n⟩
  consts := []
  result := .words "%rdi" n
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- The operand arrays of a field program over `Γ` read off the machine state `sa`: the
    `n` words at the entry register of each operand. -/
def opVals (n : Nat) (sa : AState) : (Γ : Ctxt fieldDialect) → Valuation (arrCtx n Γ)
  | [] => .nil
  | _ :: Γ => .cons (wordsFn sa (sa.regs (fieldArgReg (Γ.length + 1))) n) (opVals n sa Γ)

/-- The valuation of the context of a field program over `Γ` read off the machine state
    `sa`: the operand arrays, then the `n` words at the entry `%rdi`. -/
def abiValN (n : Nat) (sa : AState) (Γ : Ctxt fieldDialect) :
    Valuation (arrCtx n Γ ++ [arrTy n]) :=
  hvAppend (opVals n sa Γ) (.cons (wordsFn sa (sa.regs "%rdi") n) .nil)

/-- The lowered context `arrCtx n Γ` has one array per variable of `Γ`. -/
theorem arrCtx_length (n : Nat) : ∀ Γ : Ctxt fieldDialect, (arrCtx n Γ).length = Γ.length
  | [] => rfl
  | _ :: Γ => congrArg (· + 1) (arrCtx_length n Γ)

/-- Every variable of the context of a field program is a word array of `n` limbs. -/
theorem abiValN_ty (n : Nat) :
    ∀ (Γ : Ctxt fieldDialect) {t : JasminTy} (_ : Var (arrCtx n Γ ++ [arrTy n]) t), t = arrTy n
  | [], _, .here => rfl
  | _ :: _, _, .here => rfl
  | _ :: Γ, _, .there v => abiValN_ty n Γ v

/-- The de Bruijn index of a variable is below the length of its context. -/
theorem varIndex_lt_length : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (v : Var Γ t),
    JasminLprogExport.varIndex v < Γ.length
  | _, _, .here => by simp [JasminLprogExport.varIndex]
  | _ :: _, _, .there v => by
      have := varIndex_lt_length v
      simp only [JasminLprogExport.varIndex, List.length_cons]
      omega

/-- The argument position of the newest variable of `t :: Γ` is `|Γ|`. -/
theorem argIdx_here {Γ : Ctxt jasminDialect} {t : JasminTy} :
    argIdx (Var.here : Var (t :: Γ) t) = Γ.length := by
  simp [argIdx, JasminLprogExport.varIndex]

/-- Extending the context by one variable keeps the argument position of an older variable. -/
theorem argIdx_there {Γ : Ctxt jasminDialect} {s t : JasminTy} (v : Var Γ t) :
    argIdx (Var.there v : Var (s :: Γ) t) = argIdx v := by
  have := varIndex_lt_length v
  simp only [argIdx, JasminLprogExport.varIndex, List.length_cons]
  omega

/-- A variable of the context of a field program reads the words at the register of its
    parameter. -/
theorem abiValN_lookup (n : Nat) (sa : AState) :
    ∀ (Γ : Ctxt fieldDialect) (v : Var (arrCtx n Γ ++ [arrTy n]) (arrTy n)),
      argIdx v ≤ Γ.length ∧
        v.lookup (abiValN n sa Γ) = wordsFn sa (sa.regs (fieldArgReg (argIdx v))) n
  | [], .here => ⟨by simp [argIdx], rfl⟩
  | _ :: Γ, .here => by
      have e : argIdx (Var.here : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n))
          = Γ.length + 1 := by
        rw [argIdx_here, List.length_append, arrCtx_length]
        rfl
      refine ⟨?_, ?_⟩
      · change argIdx (Var.here : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n)) ≤ _
        rw [e]
        rfl
      · change _ = wordsFn sa (sa.regs (fieldArgReg
          (argIdx (Var.here : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n))))) n
        rw [e]
        rfl
  | _ :: Γ, .there v => by
      obtain ⟨h1, h2⟩ := abiValN_lookup n sa Γ v
      have e : argIdx (Var.there v : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n))
          = argIdx v := argIdx_there v
      refine ⟨?_, ?_⟩
      · change argIdx (Var.there v : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n)) ≤ _
        rw [e, List.length_cons]
        omega
      · change _ = wordsFn sa (sa.regs (fieldArgReg
          (argIdx (Var.there v : Var (arrTy n :: (arrCtx n Γ ++ [arrTy n])) (arrTy n))))) n
        rw [e]
        exact h2

/-- For `j ≤ m`, argument `j` of the layout `fieldAbi m n` is a `words n` parameter named
    `fieldArgName m j` in the register `fieldArgReg j`. -/
theorem fieldAbi_args {m n j : Nat} (h : j ≤ m) :
    (fieldAbi m n).args[j]? = some ⟨fieldArgName m j, fieldArgReg j, .words n⟩ := by
  simp [fieldAbi, List.getElem?_range (show j < m + 1 by omega)]

/-- **The layout of arity `|Γ|` reads `abiValN` off the machine state.** -/
theorem abiValOf_fieldAbi (n : Nat) (sa : AState) (Γ : Ctxt fieldDialect) :
    AbiValOf (fieldAbi Γ.length n) sa (abiValN n sa Γ) where
  arg := fun v => by
    have := abiValN_ty n Γ v
    subst this
    rw [fieldAbi_args (abiValN_lookup n sa Γ v).1]
    rfl
  reg := fun v => by
    have := abiValN_ty n Γ v
    cases this
  arr := fun v => by
    have := abiValN_ty n Γ v
    cases this
    obtain ⟨h1, h2⟩ := abiValN_lookup n sa Γ v
    exact ⟨_, fieldAbi_args h1, rfl, rfl, h2⟩

/-- **The output limbs of a routed field program at a machine state.** At the valuation
    `abiValN` of a machine state whose operand arrays hold the limbs of the values of `V`,
    the output array of the route program of `c` holds the limbs of the value of `c`. -/
theorem FieldTemplate.route_abi_denote {n : Nat} (T : FieldTemplate n) {Γ : Ctxt fieldDialect}
    {c : Com fieldDialect Γ (.fp T.p)} {rp : RouteProg (arrCtx n Γ ++ [arrTy n]) (arrTy n)}
    (h : T.route c = some rp) (sa : AState) (V : Valuation Γ)
    (hV : arrFlat (opVals n sa Γ) = flatVal (fun {t} x => T.encL (t := t) x) V) :
    arrLimbs (rp.denote (abiValN n sa Γ)) n 0 = T.enc (c.denote V) := by
  rw [← T.encL_fp]
  exact T.route_denote h V _ _ hV

/-! ## 5. The layout of a binary field program -/

/-- **The layout of a binary field program over `n` limbs**: the output array in `%rdi`,
    the second operand in `%rsi`, the first operand in `%rdx`, each of `n` words. -/
abbrev fieldAbi2 (n : Nat) : AbiLayout := fieldAbi 2 n

/-- The context of a binary field program over word arrays. -/
abbrev ctx2 (n : Nat) (p : Nat) : Ctxt jasminDialect :=
  arrCtx n [FieldTy.fp p, FieldTy.fp p] ++ [arrTy n]

/-- The valuation of the context of a binary field program read off the machine state
    `sa`: the `n` words at the entry `%rdx`, `%rsi` and `%rdi`. -/
abbrev abiVal2 (n p : Nat) (sa : AState) : Valuation (ctx2 n p) :=
  abiValN n sa [FieldTy.fp p, FieldTy.fp p]

/-- The binary layout `fieldAbi2 n` reads the valuation `abiVal2 n p sa` off the machine state
    `sa`: the instance of `abiValOf_fieldAbi` at two operands of the modulus `p`. -/
theorem abiValOf_fieldAbi2 (n p : Nat) (sa : AState) :
    AbiValOf (fieldAbi2 n) sa (abiVal2 n p sa) :=
  abiValOf_fieldAbi n sa [FieldTy.fp p, FieldTy.fp p]

/-- **The output limbs of a compiled binary field program at a machine state.** At the
    valuation `abiVal2` of a machine state whose arrays at `%rdx` and `%rsi` hold the
    Montgomery limbs of `x` and `y`, the output array of the route program of a covered
    program `c` over `[x, y]` holds the Montgomery limbs of the value of `c`. -/
theorem compileField2_denote {n : Nat} (P : LimbParams n) (hn : n < 2 ^ 64)
    {c : Com fieldDialect [FieldTy.fp P.p, FieldTy.fp P.p] (FieldTy.fp P.p)}
    {rp : RouteProg (ctx2 n P.p) (arrTy n)} (h : compileField P c = some rp) (sa : AState)
    (x y : ZMod P.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0 = enc P x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0 = enc P y) :
    arrLimbs (rp.denote (abiVal2 n P.p sa)) n 0 = enc P (c.denote (.cons x (.cons y .nil))) := by
  have h' := compileField_denote P hn h (.cons x (.cons y .nil))
    (.cons (wordsFn sa (sa.regs "%rdx") n) (.cons (wordsFn sa (sa.regs "%rsi") n) .nil))
    (wordsFn sa (sa.regs "%rdi") n) (by
      show hvAppend _ (hvAppend _ .nil) = hvAppend (encL P (t := .fp P.p) x)
        (hvAppend (encL P (t := .fp P.p) y) .nil)
      rw [encL_fp, encL_fp, hx, hy])
  rw [← encL_fp P]
  exact h'

/-! ## 3. The field product -/

/-- The field product `x * y` at the modulus `p`, over the context `[x, y]`. -/
def mulProg (p : Nat) : Com fieldDialect [.fp p, .fp p] (.fp p) :=
  .var ⟨.fMul p, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

section Mul

variable {n : Nat} (P : LimbParams n)

/-- At every modulus record `P`, the route compiler accepts the field product and returns the
    straight-line program `fieldCom P (mulProg P.p)`. -/
theorem compileField_mul : compileField P (mulProg P.p) = some (.straight (fieldCom P (mulProg P.p))) := by
  simp [compileField_eq, GoodVB, opGoodB, mulProg]

/-- **The output limbs of the compiled field product at a machine state.** At the
    valuation `abiVal2` of a machine state whose arrays at `%rdx` and `%rsi` hold the
    Montgomery limbs of `x` and `y`, the output array of the compiled product holds the
    Montgomery limbs of `x * y`. -/
theorem fieldMul_denote (hn : n < 2 ^ 64) (sa : AState) (x y : ZMod P.p)
    (hx : arrLimbs (wordsFn sa (sa.regs "%rdx") n) n 0 = enc P x)
    (hy : arrLimbs (wordsFn sa (sa.regs "%rsi") n) n 0 = enc P y) :
    arrLimbs ((RouteProg.straight (fieldCom P (mulProg P.p))).denote (abiVal2 n P.p sa)) n 0
      = enc P (x * y) :=
  compileField2_denote P hn (compileField_mul P) sa x y hx hy

end Mul

/-! ## 4. The product with a constant and the sum -/

/-- The field program `x * y * c` at the modulus `p`, over the context `[x, y]`. -/
def mulConstProg (p : Nat) (c : ZMod p) : Com fieldDialect [.fp p, .fp p] (.fp p) :=
  .var ⟨.fMul p, rfl, .cons .here (.cons (.there .here) .nil)⟩
    (.var ⟨.fConst p c, rfl, .nil⟩
      (.var ⟨.fMul p, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)))

/-- The field program `x + y` at the modulus `p`, over the context `[x, y]`. -/
def addProg (p : Nat) : Com fieldDialect [.fp p, .fp p] (.fp p) :=
  .var ⟨.fAdd p, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The program `mulConstProg p c` denotes `x * y * c` at the operands `x` and `y`. -/
theorem mulConstProg_denote (p : Nat) (c x y : ZMod p) :
    (mulConstProg p c).denote (.cons x (.cons y .nil)) = x * y * c := rfl

/-- The program `addProg p` denotes `x + y` at the operands `x` and `y`. -/
theorem addProg_denote (p : Nat) (x y : ZMod p) :
    (addProg p).denote (.cons x (.cons y .nil)) = x + y := rfl

section MulConstAdd

variable {n : Nat} (P : LimbParams n)

/-- At every modulus record `P` and constant `c`, the program `x * y * c` is covered by the
    limb lowering of `P`. -/
theorem mulConstProg_covered (c : ZMod P.p) : CoveredCom (GoodV P) (mulConstProg P.p c) :=
  GoodVB_sound P _ (by simp [GoodVB, opGoodB, mulConstProg])

/-- At every modulus record `P`, the program `x + y` is covered by the limb lowering of `P`. -/
theorem addProg_covered : CoveredCom (GoodV P) (addProg P.p) :=
  GoodVB_sound P _ (by simp [GoodVB, opGoodB, addProg])

end MulConstAdd

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
