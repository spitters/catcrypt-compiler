/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ReifyImpBridge

/-!
# A `reifyImp%` pilot with a conditional and `Option`

`decodeLean` has the rejection shape of a decoder: it returns `some p` when a Bool-valued
leaf rejects nothing, and `none` otherwise. Its literal `decodeImp` ends in a conditional
whose branches return the hax constructors `None` and `Some`; the builtin table `decBi`
interprets them by the Lean constructors of `Option`.

## Main definitions

* `decBi` — the builtin table of the pilot: `mul`, `isZero`, `Some`, `None`
* `decodeLean`, `decodeImp` — the pilot and its literal
* `decRetTy` — the Rust return type `Option<(Fe,Fe,Fe,Fe)>`

## Main results

* `decodeImp_eq` — the literal of the pilot, stated in full
* `decode_fnCorres` — the literal denotes `decodeLean`
* `decode_prints` — the literal prints as a Rust function
* `decode_evalImp` — `evalImp` of `forToLoop decodeImp` returns the encoding of
  `decodeLean`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.ReifyImp

open _root_.Hax _root_.Hax.Ascent
open CatCrypt.Crypto.Hax (forToLoop evalImp)

variable {α : Type} [HaxEnc α] [HaxEnc.Inj α]

/-! ## The builtin table -/

/-- The builtin table of the decode pilot: the field multiplication `mul`, the test
    `isZero`, and the constructors `Some` and `None` of `Option (α × α × α × α)`. -/
noncomputable def decBi (mul : α → α → α) (isZero : α → Bool) : Builtins :=
  Table.toBuiltins [("mul", leaf2 mul), ("isZero", leaf1 isZero),
    ("Some", leaf1 (some : α × α × α × α → Option (α × α × α × α))),
    ("None", leaf0 (none : Option (α × α × α × α)))]

section Leaves

variable (mul : α → α → α) (isZero : α → Bool)

theorem decBi_mul (x y : α) : decBi mul isZero "mul" [enc x, enc y] = some (enc (mul x y)) := by
  rw [decBi, Table.toBuiltins_of_lookup rfl, leaf2_apply]

theorem decBi_isZero (x : α) : decBi mul isZero "isZero" [enc x] = some (enc (isZero x)) := by
  rw [decBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

theorem decBi_some (p : α × α × α × α) :
    decBi mul isZero "Some" [enc p] = some (enc (some p)) := by
  rw [decBi, Table.toBuiltins_of_lookup rfl, leaf1_apply]

theorem decBi_none : decBi mul isZero "None" [] = some (enc (none : Option (α × α × α × α))) := by
  rw [decBi, Table.toBuiltins_of_lookup rfl, leaf0_apply]

end Leaves

/-- The table `decBi` produces no control-flow value when the encoding of `α` carries
    none. -/
theorem decBi_deepNoControlFlow (hα : ∀ x : α, (enc x).deepNoControlFlow = true)
    (mul : α → α → α) (isZero : α → Bool) : (decBi mul isZero).DeepNoControlFlow := by
  have hp : ∀ r : α × α × α × α, (enc r).deepNoControlFlow = true := fun r => by
    obtain ⟨x, y, z, t⟩ := r
    simp [HaxTupleEnc.encList, Value.deepNoControlFlow, hα]
  have ho : ∀ o : Option (α × α × α × α), (enc o).deepNoControlFlow = true := fun o => by
    cases o <;> simp [Value.deepNoControlFlow, hp]
  intro f args v h _
  simp only [decBi, Table.toBuiltins, Table.over, List.lookup] at h
  split at h
  · rename_i g hg
    repeat' split at hg
    all_goals first
      | (cases hg; obtain ⟨b, rfl⟩ := liftFn_eq_enc h; first | exact hα b | exact ho b | rfl)
      | cases hg
  · cases h

variable [HaxEnc.Plain α]

/-! ## The pilot -/

/-- The point `p` when the square of its third coordinate is not zero, and `none`
    otherwise. -/
def decodeLean (mul : α → α → α) (isZero : α → Bool) (p : α × α × α × α) :
    Option (α × α × α × α) :=
  let z := p.2.2.1
  let zz := mul z z
  if isZero zz then none else some p

/-- The literal of `decodeLean` over the parameter `p`. -/
def decodeImp : ImpExpr := reifyImp% 1 decodeLean

/-- The literal of the pilot: the projection and the product bound by `let`, the test bound
    to a fresh name, and a conditional whose branches bind `None` and `Some p`. -/
theorem decodeImp_eq : decodeImp =
    .letBind "z" (.proj (.var "p") 2)
    (.letBind "zz" (.app "mul" [.var "z", .var "z"])
    (.letBind "t" (.app "isZero" [.var "zz"])
    (.ifThenElse (.var "t")
      (.letBind "t_1" (.app "None" []) (.var "t_1"))
      (.letBind "t_2" (.app "Some" [.var "p"]) (.var "t_2"))))) :=
  rfl

/-- **The pilot is validated.** From the entry environment binding `p`, the literal
    `decodeImp` returns the encoding of `decodeLean` under the table `decBi`. -/
theorem decode_fnCorres (mul : α → α → α) (isZero : α → Bool) :
    FnCorres (decBi mul isZero) decodeImp (A := (α × α × α × α) × Unit)
      (fun a => bindParams [("p", enc a.1)]) (fun _ => True)
      (fun a => decodeLean mul isZero a.1) := by
  ascend_reified (decodeLean mul isZero)
    using [decBi_mul, decBi_isZero, decBi_some, decBi_none]

/-- The Rust return type of the pilot. -/
def decRetTy : Crypto.Hax.ImpRust.Tok := "Option<(Fe,Fe,Fe,Fe)>"

/-- The literal of the pilot prints as the Rust function
    `pub fn decode(p : (Fe,Fe,Fe,Fe)) -> Option<(Fe,Fe,Fe,Fe)>`, which
    `Crypto.Hax.parse_ppImpRustFnRet` reads back to `decodeImp`. -/
theorem decode_prints :
    (Crypto.Hax.ppImpRustFnRet "decode" [("p", edPointTy)] decRetTy (fun _ => none)
      decodeImp).isSome = true := by
  decide +kernel

/-! ## The pilot through `evalImp` -/

/-- The pilot literal lies in the fragment. -/
theorem decodeImp_reifyFrag : ReifyFrag decodeImp := by
  unfold decodeImp
  repeat' first
    | constructor
    | simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]

/-- **The pilot through `evalImp`.** From the environment binding `p`, when the encoding of
    `α` carries no control-flow value, the `evalImp` run of `forToLoop decodeImp` under
    `decBi` returns the encoding of `decodeLean`, from some fuel on. -/
theorem decode_evalImp (hα : ∀ x : α, (enc x).deepNoControlFlow = true)
    (mul : α → α → α) (isZero : α → Bool) (p : α × α × α × α) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → ∃ env',
      evalImp (decBi mul isZero) fuel (forToLoop decodeImp) (bindParams [("p", enc p)]) =
        some (enc (decodeLean mul isZero p), env') := by
  have hp : ∀ r : α × α × α × α, (enc r).deepNoControlFlow = true := fun r => by
    obtain ⟨x, y, z, t⟩ := r
    simp [HaxTupleEnc.encList, Value.deepNoControlFlow, hα]
  exact fnCorres_evalImp (A := (α × α × α × α) × Unit)
    (f := fun a => decodeLean mul isZero a.1)
    (decBi_deepNoControlFlow hα mul isZero) decodeImp_reifyFrag
    (fun a _ => Env.NoControlFlow.empty.extend (hp a.1))
    (decode_fnCorres mul isZero) (p, ()) trivial

end CatCrypt.Hax.ReifyImp

end
