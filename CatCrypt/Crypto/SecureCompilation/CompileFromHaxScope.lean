/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-!
# A syntactic scope condition under which `compileFromHax` succeeds

`compileFromHax` returns `none` exactly when an operand fails to resolve: the
translator `impExprToThir` rejects a non-atom argument, and the lowering
`thirToJasmin` rejects an operand naming a local that is not in scope or an input
index that is out of range. This module packages that as a *state-free* sufficient
condition:

* `OperandInScope params nIn S e` — the read-expression `e` is a local named in
  `S`, a bare parameter at an index below `nIn`, or an indexed read of an array
  parameter at an index below `nIn`;
* `Compiles params w nIn S e` — `e` translates and lowers in every scope whose
  state resolves `S`.

`Compiles` is closed under the `letBind` forms of the ARX fragment
(`Compiles.letBin`, `Compiles.letShift`, `Compiles.letLit`) and is monotone in
`S`, so a program produced by an unroller is proved to compile by induction on
the unroll depth, with `compileFromHax_isSome_of_compiles` as the entry point.

§4 records the CT axis of the same lowering: `rhsExpr` binds only register ops,
so every `Com` the front emits lies in the index-free fragment
(`compileFromHax_ct`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## §1  States that resolve a set of names -/

/-- A lowering state resolves the name list `S` when every input index below
    `nIn` and every local in `S` maps to a `Com` variable. -/
def StateResolves {w nIn : Nat} {locals : List String} (st : FState w nIn locals)
    (S : List String) : Prop :=
  (∀ i, i < nIn → (st.inpVar i).isSome) ∧ (∀ x ∈ S, (st.localVar x).isSome)

/-- Input index `i` of a replicate context has a de-Bruijn variable when
    `i < nIn`. -/
theorem inputVarRep_isSome (w : Nat) :
    ∀ (nIn i : Nat), i < nIn → (inputVarRep w nIn i).isSome
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => rfl
  | m + 1, k + 1, h => by
      simpa [inputVarRep] using inputVarRep_isSome w m k (Nat.lt_of_succ_lt_succ h)

/-- The initial state resolves every input index and no local. -/
theorem initFState_resolves (w nIn : Nat) :
    StateResolves (initFState w nIn) [] :=
  ⟨fun i hi => inputVarRep_isSome w nIn i hi, fun _ hx => by simp at hx⟩

/-- Pushing a binding adds its name and preserves every prior resolution. -/
theorem StateResolves.push {w nIn : Nat} {locals : List String}
    {st : FState w nIn locals} {S : List String} (h : StateResolves st S)
    (x : String) : StateResolves (st.push x) (x :: S) := by
  refine ⟨fun i hi => Option.isSome_map.trans (h.1 i hi), fun y hy => ?_⟩
  by_cases hyx : y = x
  · simp [FState.push, hyx]; rfl
  · rcases List.mem_cons.mp hy with rfl | hy
    · exact absurd rfl hyx
    · simp only [FState.push, if_neg hyx]
      exact Option.isSome_map.trans (h.2 y hy)

/-- Resolving a larger name list resolves a smaller one. -/
theorem StateResolves.mono {w nIn : Nat} {locals : List String}
    {st : FState w nIn locals} {S S' : List String} (h : StateResolves st S)
    (hsub : ∀ y ∈ S', y ∈ S) : StateResolves st S' :=
  ⟨h.1, fun x hx => h.2 x (hsub x hx)⟩

/-! ## §2  Read-expressions that resolve -/

/-- A read-expression that resolves to a `Com` variable in every state resolving
    `S`: a local named in `S` that is not a parameter, a bare scalar parameter at
    index `i < nIn`, or an indexed read `P[k]` of an array parameter `P` at an
    index `k < nIn`. -/
inductive OperandInScope (params : List String) (nIn : Nat) (S : List String) :
    ImpExpr → Prop
  | local_ (x : String) (hp : params.idxOf? x = none) (hx : x ∈ S) :
      OperandInScope params nIn S (.var x)
  | param (x : String) (i : Nat) (hp : params.idxOf? x = some i) (hi : i < nIn) :
      OperandInScope params nIn S (.var x)
  | input (P : String) (l : ImpLit) (k : Nat) (hP : P ∈ params)
      (hl : litNat? l = some k) (hk : k < nIn) :
      OperandInScope params nIn S (.app "index" [.var P, .lit l])

/-- `OperandInScope` is monotone in the name list. -/
theorem OperandInScope.mono {params : List String} {nIn : Nat} {S S' : List String}
    {e : ImpExpr} (h : OperandInScope params nIn S e) (hsub : ∀ y ∈ S, y ∈ S') :
    OperandInScope params nIn S' e := by
  cases h with
  | local_ x hp hx => exact .local_ x hp (hsub x hx)
  | param x i hp hi => exact .param x i hp hi
  | input P l k hP hl hk => exact .input P l k hP hl hk

/-- A read-expression in scope translates to an `Atom` that resolves to a
    variable of the lowering context. -/
theorem OperandInScope.resolve {w nIn : Nat} {locals : List String}
    {params S : List String} {st : FState w nIn locals} {e : ImpExpr}
    (h : OperandInScope params nIn S e) (hst : StateResolves st S) :
    ∃ a v, atomOf params e = some a ∧ Atom.toVar st a = some v := by
  cases h with
  | local_ x hp hx =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hst.2 x hx)
      exact ⟨.lvar x, v, by simp [atomOf, hp], hv⟩
  | param x i hp hi =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hst.1 i hi)
      exact ⟨.inp i, v, by simp [atomOf, hp], hv⟩
  | input P l k hP hl hk =>
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hst.1 k hk)
      exact ⟨.inp k, v, by simp [atomOf, indexAtom?, hP, hl], hv⟩

/-! ## §3  Programs that compile -/

/-- `e` translates to a `Thir` and lowers to a `Com` in every scope whose state
    resolves `S`. -/
def Compiles (params : List String) (w nIn : Nat) (S : List String)
    (e : ImpExpr) : Prop :=
  ∀ (locals : List String) (st : FState w nIn locals), StateResolves st S →
    ∃ t : Thir, impExprToThir params e = some t ∧
      (thirToJasmin locals st t).isSome

/-- `Compiles` is monotone in the name list. -/
theorem Compiles.mono {params : List String} {w nIn : Nat} {S S' : List String}
    {e : ImpExpr} (h : Compiles params w nIn S e) (hsub : ∀ y ∈ S, y ∈ S') :
    Compiles params w nIn S' e :=
  fun locals st hst => h locals st (hst.mono hsub)

/-- A local named in `S` is a compilable tail expression. -/
theorem Compiles.var {params : List String} {w nIn : Nat} {S : List String}
    {x : String} (hp : params.idxOf? x = none) (hx : x ∈ S) :
    Compiles params w nIn S (.var x) := by
  intro locals st hst
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hst.2 x hx)
  exact ⟨.ret (.lvar x), by simp [impExprToThir, atomOf, hp],
    by simp [thirToJasmin, rhsExpr, Atom.toVar, hv]⟩

/-- A `letBind` compiles when its right-hand side lowers to an `Expr` and its
    body compiles with the bound name added. -/
theorem Compiles.letBind {params : List String} {w nIn : Nat} {S : List String}
    {x : String} {v body : ImpExpr}
    (hv : ∀ (locals : List String) (st : FState w nIn locals), StateResolves st S →
      ∃ r : Rhs, rhsOf params v = some r ∧ (rhsExpr st r).isSome)
    (hbody : Compiles params w nIn (x :: S) body) :
    Compiles params w nIn S (.letBind x v body) := by
  intro locals st hst
  obtain ⟨r, hr, he⟩ := hv locals st hst
  obtain ⟨e, he'⟩ := Option.isSome_iff_exists.mp he
  obtain ⟨t, ht, hc⟩ := hbody (x :: locals) (st.push x) (hst.push x)
  obtain ⟨c, hc'⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨.let_ x r t, by simp [impExprToThir, hr, ht],
    by simp [thirToJasmin, he', hc']⟩

/-- A recognised binary ALU application of two in-scope operands lowers. -/
theorem rhsOf_bin_isSome {params : List String} {w nIn : Nat} {S : List String}
    {f : String} {op : JasminBinOp} (hf : recogBin f = some op)
    {a b : ImpExpr} (ha : OperandInScope params nIn S a)
    (hb : OperandInScope params nIn S b) (locals : List String)
    (st : FState w nIn locals) (hst : StateResolves st S) :
    ∃ r : Rhs, rhsOf params (.app f [a, b]) = some r ∧ (rhsExpr st r).isSome := by
  obtain ⟨av, va, hav, hva⟩ := ha.resolve hst
  obtain ⟨bv, vb, hbv, hvb⟩ := hb.resolve hst
  exact ⟨.bin op av bv, by simp [rhsOf, hf, hav, hbv],
    by simp [rhsExpr, hva, hvb]⟩

/-- A recognised shift/rotate application of an in-scope operand and a literal
    count lowers. -/
theorem rhsOf_shift_isSome {params : List String} {w nIn : Nat} {S : List String}
    {f : String} {k : ShiftKind} (hf : recogBin f = none)
    (hs : recogShift f = some k) {a : ImpExpr} {l : ImpLit} {n : Nat}
    (ha : OperandInScope params nIn S a) (hl : litNat? l = some n)
    (locals : List String) (st : FState w nIn locals) (hst : StateResolves st S) :
    ∃ r : Rhs, rhsOf params (.app f [a, .lit l]) = some r ∧
      (rhsExpr st r).isSome := by
  obtain ⟨av, va, hav, hva⟩ := ha.resolve hst
  cases k with
  | ror => exact ⟨.ror n av, by simp [rhsOf, hf, hs, hav, hl], by simp [rhsExpr, hva]⟩
  | shr => exact ⟨.shrImm n av, by simp [rhsOf, hf, hs, hav, hl], by simp [rhsExpr, hva]⟩
  | sar => exact ⟨.sarImm n av, by simp [rhsOf, hf, hs, hav, hl], by simp [rhsExpr, hva]⟩
  | shl => exact ⟨.shlImm n av, by simp [rhsOf, hf, hs, hav, hl], by simp [rhsExpr, hva]⟩

/-- A literal right-hand side lowers to a `regConst`. -/
theorem rhsOf_lit_isSome {params : List String} {w nIn : Nat} {locals : List String}
    {l : ImpLit} {n : Nat} (hl : litNat? l = some n) (st : FState w nIn locals) :
    ∃ r : Rhs, rhsOf params (.lit l) = some r ∧ (rhsExpr st r).isSome :=
  ⟨.atom (.lit n), by simp [rhsOf, atomOf, hl], by simp [rhsExpr]⟩

/-- Binding a recognised binary ALU application of two in-scope operands. -/
theorem Compiles.letBin {params : List String} {w nIn : Nat} {S : List String}
    {x f : String} {op : JasminBinOp} (hf : recogBin f = some op)
    {a b body : ImpExpr} (ha : OperandInScope params nIn S a)
    (hb : OperandInScope params nIn S b)
    (hbody : Compiles params w nIn (x :: S) body) :
    Compiles params w nIn S (.letBind x (.app f [a, b]) body) :=
  Compiles.letBind (fun locals st hst => rhsOf_bin_isSome hf ha hb locals st hst) hbody

/-- Binding a recognised shift/rotate of an in-scope operand by a literal. -/
theorem Compiles.letShift {params : List String} {w nIn : Nat} {S : List String}
    {x f : String} {k : ShiftKind} (hf : recogBin f = none)
    (hs : recogShift f = some k) {a body : ImpExpr} {l : ImpLit} {n : Nat}
    (ha : OperandInScope params nIn S a) (hl : litNat? l = some n)
    (hbody : Compiles params w nIn (x :: S) body) :
    Compiles params w nIn S (.letBind x (.app f [a, .lit l]) body) :=
  Compiles.letBind
    (fun locals st hst => rhsOf_shift_isSome hf hs ha hl locals st hst) hbody

/-- Binding a literal constant. -/
theorem Compiles.letLit {params : List String} {w nIn : Nat} {S : List String}
    {x : String} {l : ImpLit} {n : Nat} {body : ImpExpr} (hl : litNat? l = some n)
    (hbody : Compiles params w nIn (x :: S) body) :
    Compiles params w nIn S (.letBind x (.lit l) body) :=
  Compiles.letBind (fun _ st _ => rhsOf_lit_isSome hl st) hbody

/-- **The front succeeds on a program that compiles in the empty scope.** -/
theorem compileFromHax_isSome_of_compiles {w nIn : Nat} {params : List String}
    {e : ImpExpr} (h : Compiles params w nIn [] e) :
    (compileFromHax (w := w) (nIn := nIn) params e).isSome := by
  obtain ⟨t, ht, hc⟩ := h [] (initFState w nIn) (initFState_resolves w nIn)
  simpa [compileFromHax, ht] using hc

/-! ## §4  Everything the front emits is index-free -/

/-- Every `Expr` the front binds for a `Rhs` uses a register op, never a
    `stackLoad`/`stackStore`. -/
theorem rhsExpr_no_addr_surface {w nIn : Nat} {locals : List String}
    (st : FState w nIn locals) (r : Rhs)
    {e : Expr jasminDialect (frontCtxt w nIn locals) (rW w)}
    (h : rhsExpr st r = some e) : jasminOpAddrSurface e.op = false := by
  cases r with
  | atom a =>
      cases a with
      | lit n => simp only [rhsExpr, Option.some.injEq] at h; subst h; rfl
      | lvar x =>
          simp only [rhsExpr, Option.map_eq_some_iff] at h
          obtain ⟨_, _, he⟩ := h; subst he; rfl
      | inp i =>
          simp only [rhsExpr, Option.map_eq_some_iff] at h
          obtain ⟨_, _, he⟩ := h; subst he; rfl
  | add a b | mul a b | mulHi a b | bin _ a b =>
      simp only [rhsExpr] at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rfl
      · exact absurd h (by simp)
  | ror n a | shrImm n a | sarImm n a | shlImm n a | cast a =>
      simp only [rhsExpr, Option.map_eq_some_iff] at h
      obtain ⟨_, _, he⟩ := h; subst he; rfl
  | call name args =>
      simp only [rhsExpr, Option.map_eq_some_iff] at h
      obtain ⟨_, _, he⟩ := h; subst he; rfl

/-- The fuelled form of `thirToJasmin_ct`, recursing on a bound for the unrolling
    measure `thirMeasure`. -/
theorem thirToJasmin_ct_aux {w nIn : Nat} :
    ∀ (n : Nat) (t : Thir), thirMeasure t ≤ n → ∀ (locals : List String)
      (st : FState w nIn locals) (c : Com jasminDialect (frontCtxt w nIn locals) (rW w)),
      thirToJasmin locals st t = some c → ComJasminCTByConstruction c := by
  intro n
  induction n with
  | zero =>
      intro t ht locals st c hc
      match t with
      | .ret a =>
          simp only [thirToJasmin, Option.map_eq_some_iff] at hc
          obtain ⟨e, he, hce⟩ := hc
          subst hce
          exact ⟨rhsExpr_no_addr_surface st _ he, trivial⟩
      | .let_ x r body => simp [thirMeasure] at ht
      | .forUp acc init k body => simp [thirMeasure] at ht
  | succ n ih =>
      intro t ht locals st c hc
      match t with
      | .ret a =>
          simp only [thirToJasmin, Option.map_eq_some_iff] at hc
          obtain ⟨e, he, hce⟩ := hc
          subst hce
          exact ⟨rhsExpr_no_addr_surface st _ he, trivial⟩
      | .let_ x r body =>
          rw [thirToJasmin] at hc
          split at hc
          · rename_i e bc he hbc
            simp only [Option.some.injEq] at hc
            subst hc
            refine ⟨rhsExpr_no_addr_surface st r he, ?_⟩
            exact ih body (by simp [thirMeasure] at ht; omega) _ _ _ hbc
          · exact absurd hc (by simp)
      | .forUp acc init k body =>
          rw [thirToJasmin] at hc
          refine ih _ ?_ locals st c hc
          rw [thirMeasure_unrollFor]
          simp only [thirMeasure] at ht
          omega

/-- Every `Com` the `Thir` lowering emits is in the index-free fragment. -/
theorem thirToJasmin_ct {w nIn : Nat} {locals : List String}
    (st : FState w nIn locals) (t : Thir)
    {c : Com jasminDialect (frontCtxt w nIn locals) (rW w)}
    (h : thirToJasmin locals st t = some c) : ComJasminCTByConstruction c :=
  thirToJasmin_ct_aux (thirMeasure t) t le_rfl locals st c h

/-- **Every `Com` the compile-from-hax front emits is constant-time by
    construction** — the front binds only register ops, so no `stackLoad` /
    `stackStore` addressing surface is ever created. -/
theorem compileFromHax_ct {w nIn : Nat} {params : List String} {e : ImpExpr}
    {c : Com jasminDialect (frontCtxt w nIn []) (rW w)}
    (h : compileFromHax (w := w) (nIn := nIn) params e = some c) :
    ComJasminCTByConstruction c := by
  simp only [compileFromHax, Option.bind_eq_some_iff] at h
  obtain ⟨t, _, hct⟩ := h
  exact thirToJasmin_ct (initFState w nIn) t hct

/-- A property holding of every value an `Option` can hold transfers to
    `Option.get`. Stated for a variable `Option` so that instantiating it costs no
    reduction of the underlying term. -/
theorem get_of_forall_eq {α : Type} {o : Option α} {P : α → Prop} (h : o.isSome)
    (hall : ∀ c, o = some c → P c) : P (o.get h) :=
  hall (o.get h) (Option.some_get h).symm

/-- **The `Com` a successful compile yields is constant-time by construction.**
    The `Option.get` form of `compileFromHax_ct`. -/
theorem compileFromHax_get_ct {w nIn : Nat} {params : List String} {e : ImpExpr}
    (h : (compileFromHax (w := w) (nIn := nIn) params e).isSome) :
    ComJasminCTByConstruction
      ((compileFromHax (w := w) (nIn := nIn) params e).get h) :=
  get_of_forall_eq (P := fun c => ComJasminCTByConstruction c) h
    (fun _ hc => compileFromHax_ct hc)

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxScope
