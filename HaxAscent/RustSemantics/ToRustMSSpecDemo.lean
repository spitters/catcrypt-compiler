/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxAscent.RustSemantics.ToRustMSSpec
public import HaxAscent.Ascent.AscendHaxDemo

/-!
# The specifications of the reading on a straight-line literal

The literal `Hax.Ascent.Demo.lineLit` (twenty bindings `x_k := x_{k-1} + k`) has the
correspondence `line_corres_gen` with `lineFn a = a + 210` under the table `addBuiltins`.
`addApp` reads the calls of that table: `Add` on two integer literals as the addition of
integers, which is the value of `addBuiltins` and no operation of Rust, and `Add` on a word
by `appArith`.

* On an integer argument the reading `lineI n` returns a value (`lineI_ok`), and the
  correspondence gives the total triple `lineI_triple` and the `spec` form `lineI_spec`.
  `linePair_triple` proves a caller of two runs by `mvcgen` with `lineI_triple` as the
  specification of each call.
* On a `u64` argument the reading `lineW x` performs twenty checked additions and fails on
  overflow, so the correspondence gives the partial triple `lineW_triple_partial` only.
* `line_failApp`: the reading of calls that always fails satisfies `AppOk addBuiltins`,
  and the reading of `lineLit` under it fails from every environment. A function
  correspondence and `AppOk` therefore do not give a total triple.

## Main results

* `addApp_ok`, `line_fnCorres`
* `lineI_triple`, `lineI_spec`, `linePair_triple`
* `lineW_triple_partial`
* `line_failApp`
-/

@[expose] public section

set_option autoImplicit false
set_option mvcgen.warning false

namespace CatCrypt.Hax.RustSemantics.SpecDemo

open Aeneas.Std Aeneas.Std.WP Std.Do
open Hax.Ascent Hax.Ascent.Demo

/-- The reading of the calls of `addBuiltins`: `Add` on two integer literals as the addition
    of integers, the value of the table, and on a word operand as the checked addition
    `appArith`. -/
def addApp : String → List AVal → RustM AVal
  | "Add", [.int n, .int m] => .ok (.int (n + m))
  | "Add", [a, b] => appArith .add a b
  | _, _ => .fail .undef

theorem addApp_ok : AppOk addBuiltins addApp := by
  intro f vs r h
  unfold addApp at h
  split at h
  · cases h
    rfl
  · obtain ⟨x, y, ha, hb, hr⟩ := appArith_ok h
    simp only [AVal.toValues, ha, hb, hr]
    rfl
  · cases h

/-- The function correspondence of `lineLit`, from `line_corres_gen`. -/
theorem line_fnCorres :
    FnCorres addBuiltins lineLit (fun a : Int => bindParams [("a", HaxEnc.enc a)])
      (fun _ => True) lineFn :=
  fnCorres_of_corres line_corres_gen

theorem upd_self (ρ : AEnv) (x : String) (v : AVal) : (ρ.upd x v) x = some v := by
  simp [AEnv.upd]

/-- One binding `x := y + k` of the reading, on an integer value of `y`. -/
theorem step_int (x y : String) (k m : Int) (b : Hax.ImpExpr) (ρ : AEnv)
    (hy : ρ y = some (.int m)) :
    toRustMS addApp (.letBind x (.app "Add" [.var y, .lit (.int k)]) b) ρ =
      toRustMS addApp b (ρ.upd x (.int (m + k))) := by
  simp [toRustMS, hy, addApp]

/-- The environment binding the parameter to an integer literal. -/
def lineEnvI (n : Int) : AEnv := bindA [("a", .int n)]

/-- The environment binding the parameter to a `u64` word. -/
def lineEnvW (x : U64) : AEnv := bindA [("a", .w .U64 x)]

/-- The reading of `lineLit` on an integer argument. -/
def lineI (n : Int) : RustM (AVal × AEnv) := toRustMS addApp lineLit (lineEnvI n)

/-- The reading of `lineLit` on a `u64` argument. -/
def lineW (x : U64) : RustM (AVal × AEnv) := toRustMS addApp lineLit (lineEnvW x)

/-- The reading on an integer argument returns a value. -/
theorem lineI_ok (n : Int) : ∃ r, lineI n = .ok r := by
  unfold lineI lineLit lineEnvI
  simp only [bindA]
  iterate 20 rw [step_int _ _ _ _ _ _ (upd_self _ _ _)]
  exact ⟨_, by simp only [toRustMS, upd_self]; rfl⟩

/-- **The total triple of the reading on an integer argument**: the returned value encodes
    `n + 210`. -/
theorem lineI_triple (n : Int) :
    ⦃⌜True⌝⦄ lineI n ⦃⇓ r => ⌜r.1.toValue = .int (n + 210)⌝⦄ :=
  fnCorres_toRustMS_triple line_fnCorres addApp_ok n trivial (lineEnvI n)
    (by rw [lineEnvI, encEnv_bindA]; rfl) (lineI_ok n)

/-- The `spec` form of `lineI_triple`. -/
theorem lineI_spec (n : Int) : spec (lineI n) (fun r => r.1.toValue = .int (n + 210)) :=
  fnCorres_toRustMS_spec line_fnCorres addApp_ok n trivial (lineEnvI n)
    (by rw [lineEnvI, encEnv_bindA]; rfl) (lineI_ok n)

/-- **The partial triple of the reading on a `u64` argument**: a returned value encodes
    `x + 210`; the reading fails when a checked addition overflows. -/
theorem lineW_triple_partial (x : U64) :
    ⦃⌜True⌝⦄ lineW x
    ⦃post⟨fun r => ⌜r.1.toValue = .int (x.val + 210)⌝, fun _ => ⌜True⌝, fun _ => ⌜True⌝⟩⦄ :=
  fnCorres_toRustMS_triple_partial line_fnCorres addApp_ok (x.val : Int) trivial (lineEnvW x)
    (by rw [lineEnvW, encEnv_bindA]; rfl)

/-- A caller of two runs of the reading, returning the pair of the encoded values. -/
def linePair (n m : Int) : RustM Hax.Value := do
  let r ← lineI n
  let s ← lineI m
  pure (.tuple [r.1.toValue, s.1.toValue])

/-- The caller returns the pair `(n + 210, m + 210)`; `mvcgen` applies `lineI_triple` at
    both calls. -/
theorem linePair_triple (n m : Int) :
    ⦃⌜True⌝⦄ linePair n m ⦃⇓ v => ⌜v = .tuple [.int (n + 210), .int (m + 210)]⌝⦄ := by
  mvcgen [linePair, lineI_triple]
  simp_all

/-- The reading of calls that always fails satisfies `AppOk addBuiltins`, and under it the
    reading of `lineLit` fails from every environment. -/
theorem line_failApp :
    AppOk addBuiltins (fun _ _ => .fail .undef) ∧
      ∀ ρ, toRustMS (fun _ _ => .fail .undef) lineLit ρ = .fail .undef := by
  refine ⟨fun _ _ _ h => (by cases h), fun ρ => ?_⟩
  unfold lineLit
  cases h : ρ "a" <;> simp [toRustMS, h]

end CatCrypt.Hax.RustSemantics.SpecDemo
