/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Arrays

/-!
# The Aeneas reading of NF programs and its simulation

`nfToRustM p V` runs an NF program `p : NFProg nfDialect Γ ts` in the result monad `RustM`
of the vendored Aeneas model, on the values `V` of its context: every call of the scalar and
array names of the compiler's table is read as the Aeneas operation that the squares of
`AeneasFront/Scalars.lean` and `AeneasFront/Arrays.lean` relate to it (`aeCallV`; the call
`select` of a Boolean and two words is the selection `selW`, by the square `select_square`; the
call `Not` of a Boolean its negation, by `notBool_square`), the other operations as their NF
meaning, a counted loop as a fold of its body, a branch by its bit, an exit-flag loop as the
Aeneas combinator `loop`, and a call of a symbol fails.

The simulation runs the other way than an equation: a value of the reading is a value of
the denotation `PDenP hax64WExit` of the compiler, from some fuel on. The step lemmas
`sim_ret`, `sim_var`, `sim_ifThenElse`, `sim_forLoop` give the step for each constructor from
the statement for its parts; `nfToRustM_sim_whileFree` assembles them for every program
without `whileLoop` (`AeneasFront/Loops.lean` adds the exit-flag loop).

## Main definitions

* `readW`, `readB`, `readArr`: the Aeneas words, Booleans and arrays a chain value stands for
* `aeCallV`: the Aeneas reading of a call of the table on chain values
* `aeTable`: the leaf table of the reading on NF values
* `aeOp`, `aeExpr`: the reading of an operation and of an expression
* `nfToRustM`: the reading of an NF program

## Main results

* `aeCallV_sound`: a value of the reading of a call is the value of `hax64WExit`
* `aeTable_le`: the reading's table is below `tableOf hax64WExit`
* `aeExpr_sim`: a value of the reading of an expression is its denotation
* `sim_ret`, `sim_var`, `sim_ifThenElse`, `sim_forLoop`: the simulation steps
* `nfToRustM_sim_whileFree`: the simulation for every program without `whileLoop`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll tableOf PDenP)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)
open MultiBlockLowering (hvAppend)

/-! ## Reading chain values as Aeneas values -/

/-- The Aeneas word of the width `ty` an integer in its range stands for. -/
def readW (ty : UScalarTy) : Value → RustM (UScalar ty)
  | .int n => litA ty n
  | _ => .fail .undef

theorem readW_ok {ty : UScalarTy} {v : Value} {x : UScalar ty} (h : readW ty v = .ok x) :
    v = wordV x := by
  cases v with
  | int n =>
    have := litA_ok h
    simp only [enc_uscalar] at this
    simp [wordV, this]
  | _ => cases h

/-- The Boolean a chain Boolean stands for. -/
def readB : Value → RustM Bool
  | .bool b => .ok b
  | _ => .fail .undef

theorem readB_ok {v : Value} {b : Bool} (h : readB v = .ok b) : v = .bool b := by
  cases v with
  | bool b' =>
    cases h
    rfl
  | _ => cases h

/-- The words of `u64` a list of chain values stands for. -/
def readWs : List Value → RustM (List U64)
  | [] => .ok []
  | v :: vs => readW .U64 v >>= fun x => readWs vs >>= fun xs => .ok (x :: xs)

theorem readWs_ok : ∀ {vs : List Value} {xs : List U64}, readWs vs = .ok xs →
    vs = xs.map wordV
  | [], xs, h => by cases h; rfl
  | v :: vs, xs, h => by
    obtain ⟨x, hx, h⟩ := rustM_bind_ok h
    obtain ⟨ys, hys, h⟩ := rustM_bind_ok h
    cases h
    rw [List.map_cons, readW_ok hx, readWs_ok hys]

/-- The Aeneas array of `u64` words a chain array stands for, with its length. -/
def readArr : Value → RustM (Σ n : Usize, Aeneas.Std.Array U64 n)
  | .array vs => readWs vs >>= fun xs => litA .Usize xs.length >>= fun n =>
      if h : xs.length = n.val then .ok ⟨n, Aeneas.Std.Array.make n xs h⟩ else .fail .undef
  | _ => .fail .undef

theorem readArr_ok {v : Value} {a : Σ n : Usize, Aeneas.Std.Array U64 n}
    (h : readArr v = .ok a) : v = arrV a.2 := by
  cases v with
  | array vs =>
    obtain ⟨xs, hxs, h⟩ := rustM_bind_ok h
    obtain ⟨n, -, h⟩ := rustM_bind_ok h
    split at h
    · cases h
      rw [readWs_ok hxs]
      rfl
    · cases h
  | _ => cases h

/-! ## The reading of the calls -/

/-- The comparison a name of the table denotes. -/
def CmpOp.ofName? (f : String) : Option CmpOp :=
  if f = "Lt" then some .lt else if f = "Le" then some .le
  else if f = "Gt" then some .gt else if f = "Ge" then some .ge
  else if f = "Eq" then some .eq else if f = "Ne" then some .ne else none

theorem CmpOp.ofName?_spec {f : String} {c : CmpOp} (h : CmpOp.ofName? f = some c) :
    f = c.name := by
  unfold CmpOp.ofName? at h
  (repeat' split at h) <;> cases h <;> assumption

/-- The connective a name of the table denotes. -/
def BoolOp.ofName? (f : String) : Option BoolOp :=
  if f = "&&" then some .and else if f = "||" then some .or else none

theorem BoolOp.ofName?_spec {f : String} {o : BoolOp} (h : BoolOp.ofName? f = some o) :
    f = o.name := by
  unfold BoolOp.ofName? at h
  (repeat' split at h) <;> cases h <;> assumption

/-- A binary call: a tagged word operation, a checked operation, a comparison, a
    connective or `index`. -/
def aeCall2 (f : String) (a b : Value) : RustM Value :=
  match wordOpAt? f with
  | some (ty, o) =>
    if wordAt ty o then
      readW ty a >>= fun x => readW ty b >>= fun y => o.aen x y >>= fun z => .ok (wordV z)
    else .fail .undef
  | none =>
  match checkedAt? f with
  | some (ty, o) =>
    if tableTy ty && taggedOp o then
      readW ty a >>= fun x => readW ty b >>= fun y => o.aen x y >>= fun z => .ok (wordV z)
    else .fail .undef
  | none =>
  match CmpOp.ofName? f with
  | some c => readW .U64 a >>= fun x => readW .U64 b >>= fun y => .ok (.bool (c.aen x y))
  | none =>
  match BoolOp.ofName? f with
  | some o => readB a >>= fun p => readB b >>= fun q => .ok (.bool (o.val p q))
  | none =>
  if f = "index" then
    readArr a >>= fun arr => readW .Usize b >>= fun i =>
      arr.2.index_usize i >>= fun z => .ok (wordV z)
  else .fail .undef

/-- A unary call: the negation `Not` of a Boolean, a complement `Not#t` or a cast `cast#t` of a
    `u64` word. -/
def aeCall1 (f : String) (a : Value) : RustM Value :=
  if f = "Not" then readB a >>= fun b => .ok (.bool !b) else
  match tagTyAt? "Not#" f with
  | some ty =>
    if tableTy ty then readW ty a >>= fun x => .ok (wordV (~~~x)) else .fail .undef
  | none =>
  match tagTyAt? "cast#" f with
  | some ty =>
    if tableTy ty then readW .U64 a >>= fun x => .ok (wordV (UScalar.cast ty x))
    else .fail .undef
  | none => .fail .undef

/-- A ternary call: `array_update`, and `select` of one of two `u64` words by a Boolean. -/
def aeCall3 (f : String) (a i v : Value) : RustM Value :=
  if f = "array_update" then
    readArr a >>= fun arr => readW .Usize i >>= fun j => readW .U64 v >>= fun x =>
      arr.2.update j x >>= fun arr' => .ok (arrV arr')
  else if f = "select" then
    readB a >>= fun k => readW .U64 i >>= fun x => readW .U64 v >>= fun y =>
      .ok (wordV (selW k x y))
  else .fail .undef

/-- **The Aeneas reading of a call of the table** on chain values. -/
def aeCallV (f : String) : List Value → RustM Value
  | [a] => aeCall1 f a
  | [a, b] => aeCall2 f a b
  | [a, i, v] => aeCall3 f a i v
  | _ => .fail .undef

theorem aeCall2_sound {f : String} {a b v : Value} (h : aeCall2 f a b = .ok v) :
    hax64WExit f [a, b] = some v := by
  unfold aeCall2 at h
  rcases hw : wordOpAt? f with _ | ⟨ty, o⟩
  · rw [hw] at h
    simp only at h
    rcases hc : checkedAt? f with _ | ⟨ty, o⟩
    · rw [hc] at h
      simp only at h
      rcases hcm : CmpOp.ofName? f with _ | c
      · rw [hcm] at h
        simp only at h
        rcases hb : BoolOp.ofName? f with _ | o
        · rw [hb] at h
          simp only at h
          split at h
          · rename_i hf
            subst hf
            obtain ⟨arr, ha, h⟩ := rustM_bind_ok h
            obtain ⟨i, hi, h⟩ := rustM_bind_ok h
            obtain ⟨z, hz, h⟩ := rustM_bind_ok h
            cases h
            rw [readArr_ok ha, readW_ok hi]
            exact index_square arr.2 i z hz
          · cases h
        · rw [hb] at h
          simp only at h
          obtain ⟨p, hp, h⟩ := rustM_bind_ok h
          obtain ⟨q, hq, h⟩ := rustM_bind_ok h
          cases h
          rw [readB_ok hp, readB_ok hq, BoolOp.ofName?_spec hb]
          exact bool_square o p q
      · rw [hcm] at h
        simp only at h
        obtain ⟨x, hx, h⟩ := rustM_bind_ok h
        obtain ⟨y, hy, h⟩ := rustM_bind_ok h
        cases h
        rw [readW_ok hx, readW_ok hy, CmpOp.ofName?_spec hcm]
        exact cmp_square (by decide) c x y
    · rw [hc] at h
      simp only at h
      split at h
      · rename_i hto
        simp only [Bool.and_eq_true] at hto
        obtain ⟨x, hx, h⟩ := rustM_bind_ok h
        obtain ⟨y, hy, h⟩ := rustM_bind_ok h
        obtain ⟨z, hz, h⟩ := rustM_bind_ok h
        cases h
        rw [readW_ok hx, readW_ok hy]
        have hf : f = checkedName o ty := by
          rcases checkedAt?_spec hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
        rw [hf]
        exact checked_square hto.1 hto.2 x y z hz
      · cases h
  · rw [hw] at h
    simp only at h
    split at h
    · rename_i hwa
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      obtain ⟨y, hy, h⟩ := rustM_bind_ok h
      obtain ⟨z, hz, h⟩ := rustM_bind_ok h
      cases h
      rw [readW_ok hx, readW_ok hy, ofName_opName (wordOpAt?_spec hw)]
      exact word_square hwa x y z hz
    · cases h

theorem aeCall1_sound {f : String} {a v : Value} (h : aeCall1 f a = .ok v) :
    hax64WExit f [a] = some v := by
  unfold aeCall1 at h
  split at h
  · rename_i hf
    subst hf
    obtain ⟨b, hb, h⟩ := rustM_bind_ok h
    cases h
    rw [readB_ok hb]
    exact notBool_square b
  rcases hn : tagTyAt? "Not#" f with _ | ty
  · rw [hn] at h
    simp only at h
    rcases hc : tagTyAt? "cast#" f with _ | ty
    · rw [hc] at h
      cases h
    · rw [hc] at h
      simp only at h
      split at h
      · rename_i hty
        obtain ⟨x, hx, h⟩ := rustM_bind_ok h
        cases h
        rw [readW_ok hx, tagTyAt?_spec hc]
        exact cast_square (by decide) hty x
      · cases h
  · rw [hn] at h
    simp only at h
    split at h
    · rename_i hty
      obtain ⟨x, hx, h⟩ := rustM_bind_ok h
      cases h
      rw [readW_ok hx, tagTyAt?_spec hn]
      exact not_square hty x
    · cases h

theorem aeCall3_sound {f : String} {a i x v : Value} (h : aeCall3 f a i x = .ok v) :
    hax64WExit f [a, i, x] = some v := by
  unfold aeCall3 at h
  split at h
  · rename_i hf
    subst hf
    obtain ⟨arr, ha, h⟩ := rustM_bind_ok h
    obtain ⟨j, hj, h⟩ := rustM_bind_ok h
    obtain ⟨y, hy, h⟩ := rustM_bind_ok h
    obtain ⟨arr', harr, h⟩ := rustM_bind_ok h
    cases h
    rw [readArr_ok ha, readW_ok hj, readW_ok hy]
    exact update_square arr.2 j y arr' harr
  · split at h
    · rename_i hf
      subst hf
      obtain ⟨k, hk, h⟩ := rustM_bind_ok h
      obtain ⟨x', hx, h⟩ := rustM_bind_ok h
      obtain ⟨y', hy, h⟩ := rustM_bind_ok h
      cases h
      rw [readB_ok hk, readW_ok hx, readW_ok hy]
      exact select_square k x' y'
    · cases h

/-- **Soundness of the reading of the calls**: a value the Aeneas reading of a call returns
    is the value of `hax64WExit` on the same arguments. -/
theorem aeCallV_sound {f : String} {vs : List Value} {v : Value} (h : aeCallV f vs = .ok v) :
    hax64WExit f vs = some v := by
  match vs, h with
  | [a], h => exact aeCall1_sound h
  | [a, b], h => exact aeCall2_sound h
  | [a, i, x], h => exact aeCall3_sound h
  | [], h => cases h
  | _ :: _ :: _ :: _ :: _, h => cases h

/-! ## The reading of operations on NF values -/

/-- The leaf table of the reading: a call encodes its arguments, runs the Aeneas reading,
    and decodes its value at the result type. -/
def aeTable : NfLeafTable :=
  ⟨fun f as r xs => match aeCallV f (encAll as xs) with
    | .ok v => dec r v
    | _ => none⟩

/-- The reading's table is below the compiler's: every value of `aeTable` is the value of
    `tableOf hax64WExit`. -/
theorem aeTable_le {f : String} {as : List NfTy} {r : NfTy} {xs : HVector NfTy.denote as}
    {y : r.denote} (h : aeTable.call f as r xs = some y) :
    (tableOf hax64WExit).call f as r xs = some y := by
  change (match aeCallV f (encAll as xs) with | .ok v => dec r v | _ => none) = some y at h
  change (hax64WExit f (encAll as xs)).bind (dec r) = some y
  rcases hc : aeCallV f (encAll as xs) with v | e | _
  · rw [hc] at h
    rw [aeCallV_sound hc, Option.bind_some]
    exact h
  · rw [hc] at h
    cases h
  · rw [hc] at h
    cases h

/-- An operation denotes, with a table below another, a value the other also gives it. -/
theorem nfDenoteOp_mono {T T' : NfLeafTable}
    (hT : ∀ f as r xs y, T.call f as r xs = some y → T'.call f as r xs = some y) :
    ∀ (op : NfOp) (xs : HVector NfTy.denote op.sig) (y : op.ret.denote),
      nfDenoteOp T op xs = some y → nfDenoteOp T' op xs = some y := by
  intro op
  induction op with
  | call f as r => exact fun xs y h => hT f as r xs y h
  | named n op ih => exact fun xs y h => ih xs y h
  | _ => exact fun _ _ h => h

/-- The reading of an operation: its NF meaning with the reading's leaf table, failing where
    that meaning has no value. -/
def aeOp (op : NfOp) (xs : HVector NfTy.denote op.sig) : RustM op.ret.denote :=
  match nfDenoteOp aeTable op xs with
  | some y => .ok y
  | none => .fail .undef

/-- The reading of an expression. -/
def aeExpr {Γ : Ctxt nfDialect} {t : NfTy} (e : Expr nfDialect Γ t) (V : Valuation Γ) :
    RustM t.denote :=
  e.retTy_eq ▸ aeOp e.op (Expr.lookupArgs e.args V)

/-- **A value of the reading of an expression is its denotation.** -/
theorem aeExpr_sim {Γ : Ctxt nfDialect} {t : NfTy} (e : Expr nfDialect Γ t)
    (V : Valuation Γ) {x : t.denote} (h : aeExpr e V = .ok x) :
    @Expr.denoteM nfDialect Option _ _ (nfDenote (tableOf hax64WExit)) Γ t e V = some x := by
  obtain ⟨op, rfl, args⟩ := e
  change aeOp op (Expr.lookupArgs args V) = .ok x at h
  change nfDenoteOp (tableOf hax64WExit) op (Expr.lookupArgs args V) = some x
  unfold aeOp at h
  split at h
  · rename_i y hy
    cases h
    exact nfDenoteOp_mono (fun _ _ _ _ _ => aeTable_le) op _ _ hy
  · cases h

/-! ## The reading of programs -/

/-- One run of the body of an exit-flag loop as a step of the Aeneas `loop`: continue with
    the next tuple on the bit `true`, stop with it on `false`. -/
def flagStep {cs : List NfTy} (r : Valuation (d := nfDialect) (NfTy.bit :: cs)) :
    Aeneas.Std.ControlFlow (Valuation (d := nfDialect) cs) (Valuation (d := nfDialect) cs) :=
  if r.head then .cont r.tail else .done r.tail

/-- **The Aeneas reading of an NF program.** -/
def nfToRustM : {Γ : Ctxt nfDialect} → {ts : List NfTy} → NFProg nfDialect Γ ts →
    Valuation Γ → RustM (Valuation (d := nfDialect) ts)
  | _, _, .ret vs, V => .ok (Expr.lookupArgs vs V)
  | _, _, .var e k, V => aeExpr e V >>= fun x => nfToRustM k (V.extend x)
  | _, _, .forLoop count inits body k, V =>
      (List.range (HasWord64.toNat (d := nfDialect) (count.lookup V))).foldlM
          (fun acc i =>
            nfToRustM body (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
          (Expr.lookupArgs inits V) >>= fun acc =>
        nfToRustM k (hvAppend acc V)
  | _, _, .ifThenElse cond thn els k, V =>
      (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) then nfToRustM thn V
        else nfToRustM els V) >>= fun r => nfToRustM k (hvAppend r V)
  | _, _, .whileLoop inits body k, V =>
      loop (fun acc => nfToRustM body (hvAppend acc V) >>= fun r => .ok (flagStep r))
          (Expr.lookupArgs inits V) >>= fun acc => nfToRustM k (hvAppend acc V)
  | _, _, .call _ _ _, _ => .fail .undef

/-! ## The simulation steps -/

/-- The statement of the simulation at a program and a valuation: a value of the reading is
    the denotation at every fuel from some fuel on. -/
def Sim {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) (V : Valuation Γ) :
    Prop :=
  ∀ W, nfToRustM p V = .ok W → ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel p V = some W

theorem sim_ret {Γ : Ctxt nfDialect} {ts : List NfTy} (vs : HVector (fun t => Var Γ t) ts)
    (V : Valuation Γ) : Sim (.ret vs) V := by
  intro W h
  rw [nfToRustM] at h
  cases h
  exact ⟨0, fun _ _ => rfl⟩

theorem sim_var {Γ : Ctxt nfDialect} {t : NfTy} {ts : List NfTy} (e : Expr nfDialect Γ t)
    (k : NFProg nfDialect (t :: Γ) ts) (V : Valuation Γ) (hk : ∀ x, Sim k (V.extend x)) :
    Sim (.var e k) V := by
  intro W h
  rw [nfToRustM] at h
  obtain ⟨x, hx, h⟩ := rustM_bind_ok h
  obtain ⟨N, hN⟩ := hk x W h
  refine ⟨N, fun fuel hf => ?_⟩
  change (@Expr.denoteM nfDialect Option _ _ (nfDenote (tableOf hax64WExit)) _ _ e V) >>=
    (fun x => PDenP hax64WExit fuel k (V.extend x)) = some W
  rw [aeExpr_sim e V hx, Option.bind_eq_bind, Option.bind_some]
  exact hN fuel hf

theorem sim_ifThenElse {Γ : Ctxt nfDialect} {rs ts : List NfTy}
    (cond : Var Γ (HasBitType.bit (d := nfDialect))) (thn els : NFProg nfDialect Γ rs)
    (k : NFProg nfDialect (rs ++ Γ) ts) (V : Valuation Γ) (ht : Sim thn V) (he : Sim els V)
    (hk : ∀ r, Sim k (hvAppend r V)) : Sim (.ifThenElse cond thn els k) V := by
  intro W h
  rw [nfToRustM] at h
  obtain ⟨r, hr, h⟩ := rustM_bind_ok h
  obtain ⟨N₂, hN₂⟩ := hk r W h
  have hb : ∃ N₁, ∀ fuel, N₁ ≤ fuel →
      (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) then PDenP hax64WExit fuel thn V
        else PDenP hax64WExit fuel els V) = some r := by
    split
    · rename_i hc
      simp only [hc, ite_true] at hr
      exact ht r hr
    · rename_i hc
      simp only [hc] at hr
      exact he r hr
  obtain ⟨N₁, hN₁⟩ := hb
  refine ⟨max N₁ N₂, fun fuel hf => ?_⟩
  change (if HasBoolBit.toBool (d := nfDialect) (cond.lookup V) then PDenP hax64WExit fuel thn V
      else PDenP hax64WExit fuel els V) >>= (fun r => PDenP hax64WExit fuel k (hvAppend r V)) =
    some W
  rw [hN₁ fuel (le_of_max_le_left hf), Option.bind_eq_bind, Option.bind_some]
  exact hN₂ fuel (le_of_max_le_right hf)

/-- The fold of a body of a counted loop: a value of the fold of the reading is the value of
    the fold of the denotation, from some fuel on. -/
theorem sim_foldlM {cs : List NfTy}
    (f : Valuation (d := nfDialect) cs → Nat → RustM (Valuation (d := nfDialect) cs))
    (g : Nat → Valuation (d := nfDialect) cs → Nat → Option (Valuation (d := nfDialect) cs))
    (hfg : ∀ acc i W, f acc i = .ok W → ∃ N, ∀ fuel, N ≤ fuel → g fuel acc i = some W) :
    ∀ (l : List Nat) (acc W : Valuation (d := nfDialect) cs), l.foldlM f acc = .ok W →
      ∃ N, ∀ fuel, N ≤ fuel → l.foldlM (g fuel) acc = some W
  | [], acc, W, h => by
    cases h
    exact ⟨0, fun _ _ => rfl⟩
  | i :: l, acc, W, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h2⟩ := rustM_bind_ok h
    obtain ⟨N₁, hN₁⟩ := hfg acc i acc' h1
    obtain ⟨N₂, hN₂⟩ := sim_foldlM f g hfg l acc' W h2
    refine ⟨max N₁ N₂, fun fuel hf => ?_⟩
    rw [List.foldlM_cons, hN₁ fuel (le_of_max_le_left hf), Option.bind_eq_bind,
      Option.bind_some]
    exact hN₂ fuel (le_of_max_le_right hf)

theorem sim_forLoop {Γ : Ctxt nfDialect} {cs ts : List NfTy}
    (count : Var Γ (HasWord64.word (d := nfDialect))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg nfDialect (cs ++ HasWord64.word (d := nfDialect) :: Γ) cs)
    (k : NFProg nfDialect (cs ++ Γ) ts) (V : Valuation Γ)
    (hb : ∀ V', Sim body V') (hk : ∀ acc, Sim k (hvAppend acc V)) :
    Sim (.forLoop count inits body k) V := by
  intro W h
  rw [nfToRustM] at h
  obtain ⟨acc, hacc, h⟩ := rustM_bind_ok h
  obtain ⟨N₂, hN₂⟩ := hk acc W h
  obtain ⟨N₁, hN₁⟩ := sim_foldlM _
    (fun fuel acc i => PDenP hax64WExit fuel body
      (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
    (fun acc i W' hW => hb _ W' hW) _ _ _ hacc
  refine ⟨max N₁ N₂, fun fuel hf => ?_⟩
  change (List.range (HasWord64.toNat (d := nfDialect) (count.lookup V))).foldlM
      (fun acc i => PDenP hax64WExit fuel body
        (hvAppend acc (.cons (HasWord64.ofNat (d := nfDialect) i) V)))
      (Expr.lookupArgs inits V) >>= (fun acc => PDenP hax64WExit fuel k (hvAppend acc V)) =
    some W
  rw [hN₁ fuel (le_of_max_le_left hf), Option.bind_eq_bind, Option.bind_some]
  exact hN₂ fuel (le_of_max_le_right hf)

/-- **The simulation without exit-flag loops.** For every NF program without `whileLoop`,
    a value of the Aeneas reading is the denotation `PDenP hax64WExit` of the compiler at
    every fuel from some fuel on. -/
theorem nfToRustM_sim_whileFree : ∀ {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts), p.whileFree = true → ∀ V, Sim p V
  | _, _, .ret vs, _, V => sim_ret vs V
  | _, _, .var e k, hp, V => sim_var e k V fun x => nfToRustM_sim_whileFree k hp _
  | _, _, .forLoop count inits body k, hp, V => by
    simp only [NFProg.whileFree, Bool.and_eq_true] at hp
    exact sim_forLoop count inits body k V (fun V' => nfToRustM_sim_whileFree body hp.1 V')
      (fun acc => nfToRustM_sim_whileFree k hp.2 _)
  | _, _, .ifThenElse cond thn els k, hp, V => by
    simp only [NFProg.whileFree, Bool.and_eq_true] at hp
    exact sim_ifThenElse cond thn els k V (nfToRustM_sim_whileFree thn hp.1.1 V)
      (nfToRustM_sim_whileFree els hp.1.2 V) (fun r => nfToRustM_sim_whileFree k hp.2 _)
  | _, _, .whileLoop _ _ _, hp, _ => by simp [NFProg.whileFree] at hp
  | _, _, .call _ _ _, _, _ => fun _ h => by rw [nfToRustM] at h; cases h

end CatCrypt.Crypto.SecureCompilation.AeneasFront
