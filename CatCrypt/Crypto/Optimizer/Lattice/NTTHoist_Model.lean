/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Lattice.NTTHoist

/-!
# A concrete model `LeafSpec` discharging the hoist's assumptions

`NTTHoist.nttHoist_maccLoop_eq` and the NTT poly-mul pass's
`NTTPolyMul.nttAgreesPolyMul` are stated *under hypotheses* about the
leaf specification (the `ntt_poly_mul` / `basemul` / `invntt` / `poly_add`
leaves and the additivity of `invntt`).  Those hypotheses are discharged
on instantiation against a concrete kernel — which the project otherwise
defers (it needs a byte-layout decision for libcrux/formosa primitives).

This module defines a **witness**: a concrete `LeafSpec` over the byte-array
value representation (`RustVal t = JArray t.storageBytes`) in which

* `poly_add` is pointwise byte XOR — an abelian-group operation with unit
  `default` (the all-zero array);
* `invntt` is byte-index reversal — a *non-trivial* additive involution
  (`gInv (a ⊕ b) = gInv a ⊕ gInv b`, `gInv 0 = 0`), so the linearity
  hypothesis is exercised, not trivialised by `invntt = id`;
* `ntt_poly_mul = invntt ∘ basemul`, and `poly_mul` routes to the same
  leaf as `ntt_poly_mul`.

We then discharge `nttAgreesPolyMul` and every leaf hypothesis of the
hoist for this model, and close with a **hypothesis-free** capstone
(`model_hoist_acc_eq`): for this concrete `LeafSpec`, the source loop and
the hoisted target agree on the accumulator.  This shows the assumptions
are jointly satisfiable (non-vacuous).  Bottoming the chain out in
formosa/libcrux's *actual* primitives remains the separately-deferred
byte-layout `LeafSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.NTTHoist

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  Concrete leaf operations on the byte-array representation -/

/-- Pointwise byte XOR — the model's `poly_add` (abelian group, unit 0). -/
def gAdd {t : TowerType} (a b : RustVal t) : RustVal t := fun i => a i ^^^ b i

/-- Byte-index reversal — the model's `invntt`: a non-trivial additive
    involution. -/
def gInv {t : TowerType} (a : RustVal t) : RustVal t := fun i => a (Fin.rev i)

/-- An arbitrary `basemul` (pointwise byte AND); its exact value is
    irrelevant to the obligations. -/
def gBasemul {t : TowerType} (a b : RustVal t) : RustVal t := fun i => a i &&& b i

/-- `gInv` is additive w.r.t. `gAdd`. -/
theorem gInv_add {t : TowerType} (x y : RustVal t) :
    gAdd (gInv x) (gInv y) = gInv (gAdd x y) := rfl

/-- `gInv` fixes the zero array. -/
theorem gInv_zero {t : TowerType} : gInv (default : RustVal t) = default := by
  funext i; rfl

/-! ## §2  The model `LeafSpec` -/

/-- Extract the `i`-th argument at type `dt` (default if absent or
    mistyped). -/
def getArg (dt : TowerType) (args : List (Σ t : TowerType, RustVal t)) (i : Nat) :
    RustVal dt :=
  match args[i]? with
  | some ⟨t, v⟩ => if h : t = dt then h ▸ v else default
  | none => default

/-- The model call oracle: routes `poly_mul` / `ntt_poly_mul` to
    `invntt ∘ basemul`, `basemul` / `invntt` / `poly_add` to their ops,
    everything else to identity. -/
def modelCall (q n : Nat) : CallSpec := fun f dt _argTs oldV args =>
  if f == NTTPolyMul.nttPolyMulName q n || f == "poly_mul" || f == "polymul" then
    gInv (gBasemul (getArg dt args 0) (getArg dt args 1))
  else if f == nttBasemulName q n then
    gBasemul (getArg dt args 0) (getArg dt args 1)
  else if f == nttInvnttName q n then
    gInv (getArg dt args 0)
  else if f == "poly_add" || f == "polyadd" then
    gAdd (getArg dt args 0) (getArg dt args 1)
  else oldV

/-- The model leaf specification (other oracles are identity defaults). -/
def modelLeafSpec (q n : Nat) : LeafSpec :=
  { call := modelCall q n
    limbStore := fun _ oldV _ _ => oldV }

/-! ## §3  Discharging the assumptions -/

/-- The NTT poly-mul pass's agreement holds in the model: `ntt_poly_mul`
    and `poly_mul` route to the same leaf. -/
theorem model_nttAgrees (q n : Nat) :
    NTTPolyMul.nttAgreesPolyMul (modelLeafSpec q n) q n := by
  intro f dt argTs oldV args hf
  simp only [NTTPolyMul.isPolyMulName] at hf
  rcases (by simpa using hf) with hf | hf <;>
    subst hf <;>
    simp [modelLeafSpec, modelCall, NTTPolyMul.nttPolyMulName, nttBasemulName,
          nttInvnttName]

/-! ## §4  Hoist leaf obligations (ML-KEM-768 params) + capstone

We fix `(q, n) = (3329, 256)` so the leaf names are concrete strings and
the dispatch conditions decide. -/

def Q : Nat := 3329
def Nn : Nat := 256

theorem model_hAdd {T : TowerType} (o x y : RustVal T) :
    (modelLeafSpec Q Nn).call "poly_add" T [T, T] o [⟨T, x⟩, ⟨T, y⟩] = gAdd x y := by
  simp (config := { decide := true }) [modelLeafSpec, modelCall, getArg, Q, Nn,
        NTTPolyMul.nttPolyMulName, nttBasemulName, nttInvnttName]

theorem model_hInv {T : TowerType} (o x : RustVal T) :
    (modelLeafSpec Q Nn).call (nttInvnttName Q Nn) T [T] o [⟨T, x⟩] = gInv x := by
  simp (config := { decide := true }) [modelLeafSpec, modelCall, getArg, Q, Nn,
        NTTPolyMul.nttPolyMulName, nttBasemulName, nttInvnttName]

theorem model_hMulN {T : TowerType} (o : RustVal T) (aV bV : RustVal T) :
    (modelLeafSpec Q Nn).call (nttBasemulName Q Nn) T [T, T] o [⟨T, aV⟩, ⟨T, bV⟩]
      = gBasemul aV bV := by
  simp (config := { decide := true }) [modelLeafSpec, modelCall, getArg, Q, Nn,
        NTTPolyMul.nttPolyMulName, nttBasemulName, nttInvnttName]

theorem model_hMulC {T : TowerType} (o : RustVal T) (aV bV : RustVal T) :
    (modelLeafSpec Q Nn).call (NTTPolyMul.nttPolyMulName Q Nn) T [T, T] o
        [⟨T, aV⟩, ⟨T, bV⟩] = gInv (gBasemul aV bV) := by
  simp (config := { decide := true }) [modelLeafSpec, modelCall, getArg, Q, Nn,
        NTTPolyMul.nttPolyMulName, nttBasemulName, nttInvnttName]

/-- **Capstone — hypothesis-free instance of the hoist.**  For the
    concrete `modelLeafSpec`, the source NTT multiply-accumulate loop and
    the hoisted target (NTT-domain loop + a single closing `invntt`)
    agree on the accumulator.  *Every* leaf-agreement and additivity
    hypothesis of `nttHoist_letAccProd_eq` is discharged by the model —
    so the assumptions are jointly satisfiable. -/
theorem model_hoist_acc_eq {N : Nat} (T : TowerType) (aV bV : RustVal T) (k : Nat)
    {rs rsS rsT : RustState}
    (hA : rs.rsTower "a" = some ⟨T, aV⟩)
    (hB : rs.rsTower "b" = some ⟨T, bV⟩)
    (hSrc : RustExec N (modelLeafSpec Q Nn)
        (.RLetZero "acc" T (.RLetZero "prod" T
          (.RFor "i" k (.RSeq
            (.RCall (NTTPolyMul.nttPolyMulName Q Nn) ⟨"prod", T⟩ [⟨"a", T⟩, ⟨"b", T⟩])
            (.RCall "poly_add" ⟨"acc", T⟩ [⟨"acc", T⟩, ⟨"prod", T⟩]))))) rs rsS)
    (hTgt : RustExec N (modelLeafSpec Q Nn)
        (.RLetZero "acc" T (.RLetZero "prod" T
          (.RSeq
            (.RFor "i" k (.RSeq
              (.RCall (nttBasemulName Q Nn) ⟨"prod", T⟩ [⟨"a", T⟩, ⟨"b", T⟩])
              (.RCall "poly_add" ⟨"acc", T⟩ [⟨"acc", T⟩, ⟨"prod", T⟩])))
            (.RCall (nttInvnttName Q Nn) ⟨"acc", T⟩ [⟨"acc", T⟩])))) rs rsT) :
    rsS.rsTower "acc" = rsT.rsTower "acc" :=
  nttHoist_letAccProd_eq (leafSpec := modelLeafSpec Q Nn)
    (NTTPolyMul.nttPolyMulName Q Nn) (nttBasemulName Q Nn) "poly_add" (nttInvnttName Q Nn)
    "a" "b" "acc" "prod" "i" gAdd gInv (gBasemul aV bV) aV bV
    (fun o => model_hMulN o aV bV) (fun o => model_hMulC o aV bV)
    (fun o x y => model_hAdd o x y) (fun o x => model_hInv o x)
    (fun x y => gInv_add x y) gInv_zero
    (by decide) (by decide) (by decide) (by decide) (by decide)
    k hA hB hSrc hTgt

end CatCrypt.Crypto.Optimizer.Lattice.NTTHoist
