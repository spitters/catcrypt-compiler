/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.Optimizer.ComDCE
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
public meta import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin

/-!
# Output arrays of straight-line programs

A straight-line program `c : Com jasminDialect Γ t` with `nOut` outputs computes its
outputs as its last `nOut` bindings (`ComDCE.outputs nOut c`). `stageOuts ws nOut c` is the
structured program over the context `Γ ++ [stackArr ws nOut]` that runs the bindings of `c`
and then stores binding `comLen c - nOut + j` at index `j` of the array argument by
`stackStoreImm ws nOut j`, for `j = 0, …, nOut - 1`, and returns the array. It is `none`
when `c` has fewer than `nOut` bindings or one of its last `nOut` bindings is not a
`reg ws`.

The array argument is the last entry of the context, so the variables of `Γ` keep their
de Bruijn indices, and `nfToJasmin` makes it parameter `0` of the function
(`nfToJasmin` orders the parameters as the reversed context). `outsSig` is the signature
with that parameter as a `reg mut ptr` that holds the result.

## Main definitions

* `stageOuts`: the program `c` followed by the stores of its last `nOut` bindings.
* `outsSig`: the signature with the output array `out` as parameter `0`.
* `emitJazzOuts`: the text of `stageOuts ws nOut c` through `nfToJasmin` and the checked
  printer.

## Main results

* `stageOuts_denote`: word `j` of the returned array is entry `j` of
  `ComDCE.outputs nOut c V`.
* `emitJazzOuts_parse`: a returned text parses to the lowered unit without its extern
  signatures.
* `stageOuts_regionExportable`, `stageOuts_linearArrB`, `stageOuts_jasminWidthsB`: the
  staged program passes the checks of `nfToJasmin` whenever `NFProg.ofCom c` passes them.
* `stageOuts_nfToJasmin_isSome`, `emitJazzOuts_eq_printChecked`: `nfToJasmin` then
  succeeds on the staged program, and `emitJazzOuts` is the checked printer applied to its
  unit.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvAppend inlHom inrHom lookup_inlHom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (varIndex)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (RegionExportable BindMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (ScalarMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.Jasmin.Jazz (Storage PType JazzUnit)

/-! ## 1. Variables by index -/

/-- The entry of a context at the index of a variable is the type of the variable. -/
theorem getElem?_varIndex : ∀ {Γ : Ctxt jasminDialect} {u : JasminTy} (v : Ctxt.Var Γ u),
    Γ[varIndex v]? = some u
  | _, _, .here => rfl
  | _, _, .there v => by simp only [varIndex, List.getElem?_cons_succ, getElem?_varIndex v]

/-- The embedding of `Γ` into `Γ ++ [A]` keeps the index of a variable. -/
theorem varIndex_inlHom {A : JasminTy} : ∀ {Γ : Ctxt jasminDialect} {u : JasminTy}
    (v : Ctxt.Var Γ u), varIndex (inlHom [A] v) = varIndex v
  | _, _, .here => rfl
  | _, _, .there v => by simp only [inlHom, varIndex, varIndex_inlHom v]

/-- The embedding of `Γ` into `Γ ++ [A]` as a context homomorphism. -/
def appHom (A : JasminTy) {Γ : Ctxt jasminDialect} : Ctxt.Hom Γ (Γ ++ [A]) :=
  fun v => inlHom [A] v

/-- The last variable of `Γ ++ [A]` has the index `Γ.length`. -/
theorem varIndex_inrHom (A : JasminTy) : ∀ (Γ : Ctxt jasminDialect),
    varIndex (inrHom Γ (Ctxt.Var.here : Ctxt.Var [A] A)) = Γ.length
  | [] => rfl
  | _ :: Γ => by simp only [inrHom, varIndex, varIndex_inrHom A Γ, List.length_cons]

/-- The embedding of `Γ` into `Γ ++ [A]` keeps the indices of an argument vector. -/
theorem hvIdxs_renameVars {A : JasminTy} {Γ : Ctxt jasminDialect} :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Ctxt.Var Γ t) ts),
      hvIdxs (HVector.renameVars (appHom A) vs) = hvIdxs vs
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show varIndex (inlHom [A] v) :: hvIdxs (HVector.renameVars (appHom A) vs)
        = varIndex v :: hvIdxs vs
      rw [varIndex_inlHom, hvIdxs_renameVars vs]

/-- The values of a valuation with their types, from index `0`. -/
def valList : {Δ : Ctxt jasminDialect} → Ctxt.Valuation Δ → List (Σ u : JasminTy, ⟦u⟧)
  | [], .nil => []
  | u :: _, .cons x V => ⟨u, x⟩ :: valList V

@[simp] theorem valList_nil : valList (.nil : Ctxt.Valuation ([] : Ctxt jasminDialect)) = [] :=
  rfl

@[simp] theorem valList_cons {u : JasminTy} {Δ : Ctxt jasminDialect} (x : ⟦u⟧)
    (V : Ctxt.Valuation Δ) :
    valList (.cons x V : Ctxt.Valuation (u :: Δ)) = ⟨u, x⟩ :: valList V :=
  rfl

@[simp] theorem valList_extend {u : JasminTy} {Δ : Ctxt jasminDialect} (V : Ctxt.Valuation Δ)
    (x : ⟦u⟧) : valList (V.extend x) = ⟨u, x⟩ :: valList V :=
  rfl

theorem valList_hvAppend : ∀ {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ)
    {Δ : Ctxt jasminDialect} (W : Ctxt.Valuation Δ),
    valList (hvAppend V W) = valList V ++ valList W
  | [], .nil, _, _ => rfl
  | _ :: _, .cons x V, _, W => by
      show ⟨_, x⟩ :: valList (hvAppend V W) = _
      rw [valList_hvAppend V W]
      rfl

/-- The variable of index `i` of `Δ` when it is a `reg w`. -/
def regIdx? (w : Nat) : (Δ : Ctxt jasminDialect) → Nat → Option (Ctxt.Var Δ (.reg w))
  | [], _ => none
  | t :: _, 0 => if h : t = .reg w then some (Ctxt.Var.castTy h .here) else none
  | _ :: Δ, i + 1 => (regIdx? w Δ i).map .there

/-- A variable `regIdx?` returns has the index `i`, and entry `i` of every valuation is its
value. -/
theorem regIdx?_spec {w : Nat} : ∀ {Δ : Ctxt jasminDialect} {i : Nat}
    {v : Ctxt.Var Δ (.reg w)}, regIdx? w Δ i = some v →
    Δ[i]? = some (.reg w) ∧ varIndex v = i ∧
      ∀ V : Ctxt.Valuation Δ, (valList V)[i]? = some ⟨.reg w, v.lookup V⟩
  | [], _, _, h => by simp [regIdx?] at h
  | t :: Δ, 0, v, h => by
      simp only [regIdx?] at h
      split at h
      · rename_i ht
        subst ht
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨rfl, rfl, fun V => ?_⟩
        cases V
        rfl
      · simp at h
  | t :: Δ, i + 1, v, h => by
      simp only [regIdx?, Option.map_eq_some_iff] at h
      obtain ⟨v', hv', rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := regIdx?_spec hv'
      refine ⟨by simpa using h1, by simp [varIndex, h2], fun V => ?_⟩
      cases V with
      | cons x V =>
          show (⟨_, x⟩ :: valList V)[i + 1]? = some ⟨.reg w, v'.lookup V⟩
          simpa using h3 V

/-! ## 2. The staged program -/

/-- The stores of the outputs: with `k` stores left, the next one writes the `reg ws`
variable of index `nOut - 1` at index `j` of the array `arr`; the program returns the
array after the last store. -/
def storesGo (ws nOut : Nat) : (k j : Nat) → {Δ : Ctxt jasminDialect} →
    Ctxt.Var Δ (.stackArr ws nOut) → Option (NFProg jasminDialect Δ [.stackArr ws nOut])
  | 0, _, _, arr => some (.ret (.cons arr .nil))
  | k + 1, j, Δ, arr => (regIdx? ws Δ (nOut - 1)).bind fun v =>
      (storesGo ws nOut k (j + 1) (Δ := .stackArr ws nOut :: Δ) .here).map fun r =>
        .var ⟨.stackStoreImm ws nOut j, rfl, .cons arr (.cons v .nil)⟩ r

/-- The bindings of `c` over the context `Γ ++ [stackArr ws nOut]`, followed by the stores
of the outputs into the last variable of the context. -/
def stageGo (ws nOut : Nat) : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t →
    Option (NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut])
  | Γ, _, .ret _ => storesGo ws nOut nOut 0 (inrHom Γ .here)
  | Γ, _, .var e body =>
      (stageGo ws nOut body).map
        (.var (e.rename (appHom (Γ := Γ) (.stackArr ws nOut))))

/-- **The program `c` with its last `nOut` bindings stored to an output array**: over the
context `Γ ++ [stackArr ws nOut]`, the bindings of `c`, then the store of binding
`comLen c - nOut + j` at index `j` of the array argument for each `j < nOut`, then the
return of the array. `none` when `c` has fewer than `nOut` bindings or one of the last
`nOut` is not a `reg ws`. -/
def stageOuts (ws nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) :
    Option (NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]) :=
  if nOut ≤ Optimizer.UncomputePass.comLen c then stageGo ws nOut c else none

/-- The signature of a function with an output array: the parameter `out`, a
`reg mut ptr` array of `nOut` words of width `ws` that holds the result, followed by the
parameters `ps` of the context `Γ` in the reverse order of the context. -/
def outsSig {Γ : Ctxt jasminDialect} (ws nOut : Nat) (ps : List (String × Storage × PType))
    (h : ps.length = Γ.length) :
    JazzSig (Γ ++ [.stackArr ws nOut]) (.stackArr ws nOut) where
  params := ("out", .regPtr true, ptyOf (.stackArr ws nOut)) :: ps
  result := (.regPtr true, ptyOf (.stackArr ws nOut))
  resultParam := some 0
  params_length := by simp [h]

/-- `outsSig` fits its context when the surface type of each parameter of `ps` is the type
of its argument. -/
theorem outsSig_fits {Γ : Ctxt jasminDialect} (ws nOut : Nat)
    (ps : List (String × Storage × PType)) (h : ps.length = Γ.length)
    (hps : ∀ q ∈ ps.zip Γ.reverse, q.1.2.2.toSType = styOf q.2) :
    (outsSig ws nOut ps h).Fits := by
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [outsSig, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.zip_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · rfl
    · exact hps q hq
  · exact ⟨_, rfl, rfl, rfl⟩

/-- **The text of `c` with an output array**: `stageOuts ws nOut c` printed as the
`export fn` `name` with the signature `sig` by `nfToJasmin` and the checked printer. -/
def emitJazzOuts {Γ : Ctxt jasminDialect} {t : JasminTy} (name : String) (ws nOut : Nat)
    (sig : JazzSig (Γ ++ [.stackArr ws nOut]) (.stackArr ws nOut))
    (c : Com jasminDialect Γ t) : Option String :=
  (stageOuts ws nOut c).bind (JasminPrintText.emitJazzNF name sig)

/-! ## 3. The denotation -/

/-- The stores from index `j` with `k = nOut - j` stores left return an array whose word
`i ≥ j` is entry `nOut - 1 - (i - j)` of the valuation and whose word `i < j` is word `i`
of `arr`. -/
theorem storesGo_denote {ws nOut : Nat} (fuel : Nat) : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]}
    (V : Ctxt.Valuation Δ), storesGo ws nOut k j arr = some p → j + k = nOut →
    ∃ a, p.denote fuel V = some (.cons a .nil) ∧
      (∀ i : Fin nOut, j ≤ i.val →
        (valList V)[nOut - 1 - (i.val - j)]? = some ⟨.reg ws, a i⟩) ∧
      (∀ i : Fin nOut, i.val < j → a i = arr.lookup V i)
  | 0, j, Δ, arr, p, V, h, hk => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      exact ⟨arr.lookup V, rfl, fun i hi => by omega, fun _ _ => rfl⟩
  | k + 1, j, Δ, arr, p, V, h, hk => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, r, hr, rfl⟩ := h
      have hj : j < nOut := by omega
      obtain ⟨_, _, hvV⟩ := regIdx?_spec hv
      obtain ⟨a, hden, hhi, hlo⟩ := storesGo_denote fuel k (j + 1) .here
        (Ctxt.Valuation.extend V (stackSet (arr.lookup V) j (v.lookup V))) hr (by omega)
      have hset := stackSet_fin (arr.lookup V) ⟨j, hj⟩ (v.lookup V)
      refine ⟨a, ?_, fun i hi => ?_, fun i hi => ?_⟩
      · rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
        exact hden
      · rcases Nat.lt_or_ge j i.val with hji | hji
        · have := hhi i (by omega)
          have hidx : nOut - 1 - (i.val - (j + 1)) = (nOut - 1 - (i.val - j)) + 1 := by omega
          rw [hidx, valList_extend, List.getElem?_cons_succ] at this
          exact this
        · have hij : i = ⟨j, hj⟩ := Fin.ext (show i.val = j by omega)
          have ha : a i = v.lookup V := by
            rw [hlo i (by omega)]
            show stackSet (arr.lookup V) j (v.lookup V) i = _
            rw [hset]
            exact if_pos hij
          rw [ha, show nOut - 1 - (i.val - j) = nOut - 1 by omega]
          exact hvV V
      · have hij : i ≠ ⟨j, hj⟩ := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        rw [hlo i (by omega)]
        show stackSet (arr.lookup V) j (v.lookup V) i = _
        rw [hset]
        exact if_neg hij

/-- The staged program returns an array whose word `i` is entry `nOut - 1 - i` of the
binding values of `c` in reverse order, followed by the valuation and the array
argument. -/
theorem stageGo_denote {ws nOut : Nat} (fuel : Nat) : ∀ {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p →
    ∀ (V : Ctxt.Valuation Γ) (o : ⟦JasminTy.stackArr ws nOut⟧),
      ∃ a, p.denote fuel (hvAppend V (.cons o .nil)) = some (.cons a .nil) ∧
        ∀ i : Fin nOut, ((Optimizer.ComDCE.bindVals c V).reverse ++ valList V
          ++ [⟨.stackArr ws nOut, o⟩])[nOut - 1 - i.val]? = some ⟨.reg ws, a i⟩
  | Γ, _, .ret _, p, h, V, o => by
      simp only [stageGo] at h
      obtain ⟨a, hd, hhi, -⟩ :=
        storesGo_denote fuel nOut 0 (inrHom Γ .here) (hvAppend V (.cons o .nil)) h (by omega)
      refine ⟨a, hd, fun i => ?_⟩
      have := hhi i (Nat.zero_le _)
      rw [valList_hvAppend, valList_cons, valList_nil] at this
      simpa [Optimizer.ComDCE.bindVals] using this
  | _, _, .var e body, p, h, V, o => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      obtain ⟨a, hd, hw⟩ := stageGo_denote fuel body hp' (V.extend (e.denote V)) o
      have hV : Ctxt.Valuation.comap (appHom (JasminTy.stackArr ws nOut))
          (hvAppend V (.cons o .nil) : Ctxt.Valuation (_ ++ [JasminTy.stackArr ws nOut]))
          = V :=
        Ctxt.Valuation.ext _ _ fun _ v => by
          rw [Ctxt.Valuation.lookup_comap]
          exact lookup_inlHom _ v V
      refine ⟨a, ?_, fun i => ?_⟩
      · rw [NFProg.denote_var, Expr.denoteM_option_eq_some, Expr.denote_rename, hV]
        exact hd
      · have := hw i
        simp only [valList_extend] at this
        simpa [Optimizer.ComDCE.bindVals, List.reverse_cons, List.append_assoc] using this

/-- **The denotation of the staged program**: from every valuation `V` of `Γ` and every
initial array `o`, `stageOuts ws nOut c` returns an array whose word `j` is entry `j` of
the last `nOut` binding values `ComDCE.outputs nOut c V` of `c`. -/
theorem stageOuts_denote {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (h : stageOuts ws nOut c = some p) (fuel : Nat) (V : Ctxt.Valuation Γ)
    (o : ⟦JasminTy.stackArr ws nOut⟧) :
    ∃ a, p.denote fuel (hvAppend V (.cons o .nil)) = some (.cons a .nil) ∧
      ∀ j : Fin nOut, (Optimizer.ComDCE.outputs nOut c V)[j.val]? = some ⟨.reg ws, a j⟩ := by
  unfold stageOuts at h
  split at h
  · rename_i hn
    obtain ⟨a, hd, hw⟩ := stageGo_denote fuel c h V o
    refine ⟨a, hd, fun j => ?_⟩
    have hlen := Optimizer.ComDCE.length_bindVals c V
    rw [← hw j, Optimizer.ComDCE.outputs, List.getElem?_drop, List.append_assoc,
      List.getElem?_append_left (by simp only [List.length_reverse]; omega),
      List.getElem?_reverse (by omega)]
    congr 1
    omega
  · simp at h

/-! ## 4. The checks of `nfToJasmin` -/

/-- Renaming keeps the scalar stack-memory fragment. -/
theorem scalarMemN_rename {Γ : Ctxt jasminDialect} {u : JasminTy}
    {c : Com jasminDialect Γ u} (hc : ScalarMemN c) :
    ∀ {Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ'), ScalarMemN (c.rename h) := by
  induction hc with
  | ret v => intro _ h; exact .ret (h v)
  | var bop heq args _ ih => intro _ h; exact .var bop heq _ (ih h.lift)
  | const n hwn heq args _ ih => intro _ h; exact .const n hwn heq _ (ih h.lift)
  | sel heq args _ ih => intro _ h; exact .sel heq _ (ih h.lift)
  | shr hm heq args _ ih => intro _ h; exact .shr hm heq _ (ih h.lift)
  | shl hm heq args _ ih => intro _ h; exact .shl hm heq _ (ih h.lift)
  | sar hm heq args _ ih => intro _ h; exact .sar hm heq _ (ih h.lift)
  | mulhi heq args _ ih => intro _ h; exact .mulhi heq _ (ih h.lift)
  | addLo heq args _ ih => intro _ h; exact .addLo heq _ (ih h.lift)
  | addHi heq args _ ih => intro _ h; exact .addHi heq _ (ih h.lift)
  | cast heq args _ ih => intro _ h; exact .cast heq _ (ih h.lift)
  | load heq args _ ih => intro _ h; exact .load heq _ (ih h.lift)
  | store heq args _ ih => intro _ h; exact .store heq _ (ih h.lift)
  | cmp c heq args _ ih => intro _ h; exact .cmp c heq _ (ih h.lift)
  | cmpImm c heq args _ ih => intro _ h; exact .cmpImm c heq _ (ih h.lift)
  | zero heq args _ ih => intro _ h; exact .zero heq _ (ih h.lift)
  | storeImm heq args _ ih => intro _ h; exact .storeImm heq _ (ih h.lift)

/-- Renaming keeps the array-returning stack-memory fragment. -/
theorem arrMemN_rename {w n : Nat} {Γ : Ctxt jasminDialect}
    {c : Com jasminDialect Γ (.stackArr w n)} (hc : ArrMemN c) :
    ∀ {Γ' : Ctxt jasminDialect} (h : Ctxt.Hom Γ Γ'), ArrMemN (c.rename h) := by
  induction hc with
  | ret v => intro _ h; exact .ret (h v)
  | reg e he _ ih => intro _ h; exact .reg (e.rename h) (scalarMemN_rename he h) (ih h.lift)
  | store heq args _ ih => intro _ h; exact .store heq _ (ih h.lift)
  | zero heq args _ ih => intro _ h; exact .zero heq _ (ih h.lift)
  | storeImm heq args _ ih => intro _ h; exact .storeImm heq _ (ih h.lift)

/-- Renaming keeps the bindings of the stack-memory fragment. -/
theorem bindMemN_rename {Γ Γ' : Ctxt jasminDialect} {u : JasminTy}
    {e : Expr jasminDialect Γ u} (h : Ctxt.Hom Γ Γ') (he : BindMemN e) :
    BindMemN (e.rename h) := by
  rcases he with ⟨w, v, hv⟩ | ⟨w, n, v, hv⟩
  · exact Or.inl ⟨w, h.lift v, scalarMemN_rename hv h⟩
  · exact Or.inr ⟨w, n, h.lift v, arrMemN_rename hv h⟩

/-- The array operand of an in-place store is an array variable. -/
theorem storeSrc?_type {Γ : Ctxt jasminDialect} {u : JasminTy} (e : Expr jasminDialect Γ u)
    {a : Nat} (h : storeSrc? e.op (hvIdxs e.args) = some a) :
    ∃ w n, Γ[a]? = some (.stackArr w n) := by
  obtain ⟨op, heq, args⟩ := e
  cases op
  case stackStore w n =>
    cases args with
    | cons v vs =>
        have h' : storeSrc? (JasminOp.stackStore w n) (varIndex v :: hvIdxs vs) = some a := h
        simp only [storeSrc?, Option.some.injEq] at h'
        subst h'
        exact ⟨w, n, getElem?_varIndex v⟩
  case stackStoreImm w n i =>
    cases args with
    | cons v vs =>
        have h' : storeSrc? (JasminOp.stackStoreImm w n i) (varIndex v :: hvIdxs vs)
          = some a := h
        simp only [storeSrc?, Option.some.injEq] at h'
        subst h'
        exact ⟨w, n, getElem?_varIndex v⟩
  all_goals simp [storeSrc?] at h

/-- The stores are in the stack-memory fragment. -/
theorem storesGo_regionExportable {ws nOut : Nat} : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]},
    storesGo ws nOut k j arr = some p → RegionExportable p
  | 0, _, _, _, p, h => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      trivial
  | k + 1, j, Δ, arr, p, h => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, _, r, hr, rfl⟩ := h
      exact ⟨Or.inr ⟨ws, nOut, .here, ArrMemN.storeImm rfl _ (ArrMemN.ret _)⟩,
        storesGo_regionExportable k (j + 1) .here hr⟩

/-- The stores pass the width check at a register width `ws`. -/
theorem storesGo_widthsGo {ws nOut : Nat} (hws : widthOkB ws = true) :
    ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]},
    storesGo ws nOut k j arr = some p → widthsGo p = true
  | 0, _, _, _, p, h => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      rfl
  | k + 1, j, Δ, arr, p, h => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, _, r, hr, rfl⟩ := h
      show (tyOkB (.stackArr ws nOut) && opOkB (.stackStoreImm ws nOut j) && widthsGo r) = true
      simp only [tyOkB, opOkB, hws, storesGo_widthsGo hws k (j + 1) .here hr, Bool.and_self]

/-- The entries `j, …, nOut - 1` of the context of the stores from index `j` are
`reg ws`. -/
theorem storesGo_types {ws nOut : Nat} : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]},
    storesGo ws nOut k j arr = some p → j + k = nOut →
    ∀ i, j ≤ i → i < nOut → Δ[i]? = some (.reg ws)
  | 0, j, _, _, _, _, hk, i, hi, hn => by omega
  | k + 1, j, Δ, arr, p, h, hk, i, hi, hn => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, r, hr, rfl⟩ := h
      rcases Nat.lt_or_ge i (nOut - 1) with hlt | hge
      · have := storesGo_types k (j + 1) .here hr (by omega) (i + 1) (by omega) (by omega)
        simpa using this
      · rw [show i = nOut - 1 by omega]
        exact (regIdx?_spec hv).1

/-- The stores from index `j` read the array `arr` and the variables of index
`j, …, nOut - 1`. -/
theorem storesGo_usesIdx {ws nOut : Nat} : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]},
    storesGo ws nOut k j arr = some p → j + k = nOut → ∀ i, usesIdx p i = true →
    i = varIndex arr ∨ (j ≤ i ∧ i < nOut)
  | 0, j, _, arr, p, h, _, i, hu => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      have hu' : [varIndex arr].contains i = true := hu
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hu'
      exact Or.inl hu'
  | k + 1, j, Δ, arr, p, h, hk, i, hu => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, r, hr, rfl⟩ := h
      have hvi := (regIdx?_spec hv).2.1
      have hu' : ([varIndex arr, varIndex v].contains i || usesIdx r (i + 1)) = true := hu
      simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true,
        beq_iff_eq, hvi] at hu'
      rcases hu' with (hu | hu) | hu
      · exact Or.inl hu
      · exact Or.inr ⟨by omega, by omega⟩
      · rcases storesGo_usesIdx k (j + 1) .here hr (by omega) (i + 1) hu with h0 | ⟨h1, h2⟩
        · simp [varIndex] at h0
        · exact Or.inr ⟨by omega, by omega⟩

/-- The stores pass the in-place store check when the array `arr` is bound in the region
and is not one of the variables `j + 1, …` that later stores read. -/
theorem storesGo_linGo {ws nOut : Nat} : ∀ (k j : Nat) {Δ : Ctxt jasminDialect}
    (arr : Ctxt.Var Δ (.stackArr ws nOut)) {p : NFProg jasminDialect Δ [.stackArr ws nOut]}
    (loc : Nat), storesGo ws nOut k j arr = some p → j + k = nOut → varIndex arr < loc →
    (varIndex arr < j ∨ nOut ≤ varIndex arr + 1) → linGo p loc = true
  | 0, _, _, _, p, _, h, _, _, _ => by
      simp only [storesGo, Option.some.injEq] at h
      subst h
      rfl
  | k + 1, j, Δ, arr, p, loc, h, hk, hloc, harr => by
      simp only [storesGo, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, r, hr, rfl⟩ := h
      have hr' : usesIdx r (varIndex arr + 1) = false := by
        cases hu : usesIdx r (varIndex arr + 1)
        · rfl
        · rcases storesGo_usesIdx k (j + 1) .here hr (by omega) _ hu with h0 | ⟨h1, h2⟩
          · simp [varIndex] at h0
          · omega
      show (decide (varIndex arr < loc) && !usesIdx r (varIndex arr + 1)
        && linGo r (loc + 1)) = true
      rw [hr', decide_eq_true hloc, Bool.not_false, Bool.and_self, Bool.true_and]
      exact storesGo_linGo k (j + 1) .here (loc + 1) hr (by omega) (by simp [varIndex])
        (Or.inl (by simp [varIndex]))

/-- The entries of the context of `c` that the stores read as outputs are `reg ws`. -/
theorem stageGo_types {ws nOut : Nat} : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p → ∀ i, i + Optimizer.UncomputePass.comLen c < nOut →
      (Γ ++ [JasminTy.stackArr ws nOut])[i]? = some (.reg ws)
  | Γ, _, .ret _, p, h, i, hi => by
      simp only [stageGo] at h
      exact storesGo_types nOut 0 _ h (by omega) i (Nat.zero_le _)
        (by simpa [Optimizer.UncomputePass.comLen] using hi)
  | _, _, .var e body, p, h, i, hi => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      have := stageGo_types body hp' (i + 1)
        (by simp only [Optimizer.UncomputePass.comLen_var] at hi; omega)
      simpa using this

/-- The staged program reads a variable that `NFProg.ofCom c` reads, an output binding
or the array argument. -/
theorem stageGo_usesIdx {ws nOut : Nat} : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p → ∀ i, usesIdx p i = true →
      usesIdx (NFProg.ofCom c) i = true ∨ i + Optimizer.UncomputePass.comLen c < nOut ∨
        i = Γ.length
  | Γ, _, .ret _, p, h, i, hu => by
      simp only [stageGo] at h
      rcases storesGo_usesIdx nOut 0 _ h (by omega) i hu with h0 | ⟨_, h1⟩
      · rw [varIndex_inrHom] at h0
        exact Or.inr (Or.inr h0)
      · exact Or.inr (Or.inl (by simpa [Optimizer.UncomputePass.comLen] using h1))
  | _, _, .var e body, p, h, i, hu => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      simp only [usesIdx, Expr.args_rename, Bool.or_eq_true] at hu
      rcases hu with hu | hu
      · have hu2 : (hvIdxs e.args).contains i = true := by
          rw [← hvIdxs_renameVars (A := JasminTy.stackArr ws nOut) e.args]
          exact hu
        refine Or.inl ?_
        simp only [NFProg.ofCom, usesIdx, hu2, Bool.true_or]
      · rcases stageGo_usesIdx body hp' (i + 1) hu with h0 | h0 | h0
        · exact Or.inl (by simp [NFProg.ofCom, usesIdx, h0])
        · exact Or.inr (Or.inl (by simp only [Optimizer.UncomputePass.comLen_var]; omega))
        · exact Or.inr (Or.inr (by simpa using h0))

/-- The staged program passes the in-place store check when `NFProg.ofCom c` does. -/
theorem stageGo_linGo {ws nOut : Nat} : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p → linGo (NFProg.ofCom c) Γ.length = true →
    nOut ≤ Optimizer.UncomputePass.comLen c + Γ.length + 1 →
    linGo p (Γ.length + 1) = true
  | Γ, _, .ret _, p, h, _, hn => by
      simp only [stageGo] at h
      refine storesGo_linGo nOut 0 _ _ h (by omega) (by rw [varIndex_inrHom]; omega)
        (Or.inr ?_)
      rw [varIndex_inrHom]
      simpa [Optimizer.UncomputePass.comLen] using hn
  | Γ, _, .var e body, p, h, hl, hn => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      simp only [NFProg.ofCom, linGo, Bool.and_eq_true] at hl
      obtain ⟨hs, hk⟩ := hl
      have hk' := stageGo_linGo body hp' (by simpa using hk)
        (by simp only [Optimizer.UncomputePass.comLen_var] at hn; simp; omega)
      simp only [linGo, Expr.op_rename, Expr.args_rename, hvIdxs_renameVars, Bool.and_eq_true]
      refine ⟨?_, by simpa [Nat.add_assoc] using hk'⟩
      cases hsrc : storeSrc? e.op (hvIdxs e.args) with
      | none => rfl
      | some a =>
          rw [hsrc] at hs
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hs
          obtain ⟨ha, hua⟩ := hs
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
          refine ⟨by omega, ?_⟩
          cases hu : usesIdx p' (a + 1)
          · rfl
          · exfalso
            rcases stageGo_usesIdx body hp' (a + 1) hu with h0 | h0 | h0
            · rw [hua] at h0
              exact Bool.false_ne_true h0
            · obtain ⟨w, n, hwn⟩ := storeSrc?_type e hsrc
              have ht := stageGo_types body hp' (a + 1) h0
              simp only [List.cons_append, List.getElem?_cons_succ] at ht
              rw [List.getElem?_append_left ha, hwn] at ht
              simp at ht
            · simp at h0
              omega

/-- The staged program is in the fragment of `RegionExportable` when `NFProg.ofCom c`
is. -/
theorem stageGo_regionExportable {ws nOut : Nat} : ∀ {Γ : Ctxt jasminDialect}
    {t : JasminTy} (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p → RegionExportable (NFProg.ofCom c) → RegionExportable p
  | _, _, .ret _, p, h, _ => by
      simp only [stageGo] at h
      exact storesGo_regionExportable nOut 0 _ h
  | _, _, .var e body, p, h, hc => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      exact ⟨bindMemN_rename _ hc.1, stageGo_regionExportable body hp' hc.2⟩

/-- The staged program passes the width check when `NFProg.ofCom c` does, at a register
width `ws`. -/
theorem stageGo_widthsGo {ws nOut : Nat} (hws : widthOkB ws = true) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : Com jasminDialect Γ t)
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]},
    stageGo ws nOut c = some p → widthsGo (NFProg.ofCom c) = true → widthsGo p = true
  | _, _, .ret _, p, h, _ => by
      simp only [stageGo] at h
      exact storesGo_widthsGo hws nOut 0 _ h
  | _, _, .var e body, p, h, hc => by
      simp only [stageGo, Option.map_eq_some_iff] at h
      obtain ⟨p', hp', rfl⟩ := h
      simp only [NFProg.ofCom, widthsGo, Bool.and_eq_true] at hc
      simp only [widthsGo, Expr.op_rename, hc.1.1, hc.1.2,
        stageGo_widthsGo hws body hp' hc.2, Bool.and_self]

theorem stageOuts_eq_some {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (h : stageOuts ws nOut c = some p) :
    nOut ≤ Optimizer.UncomputePass.comLen c ∧ stageGo ws nOut c = some p := by
  unfold stageOuts at h
  split at h
  · exact ⟨‹_›, h⟩
  · simp at h

/-- The staged program is in the fragment of `RegionExportable` when `NFProg.ofCom c`
is. -/
theorem stageOuts_regionExportable {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (h : stageOuts ws nOut c = some p) (hc : RegionExportable (NFProg.ofCom c)) :
    RegionExportable p :=
  stageGo_regionExportable c (stageOuts_eq_some h).2 hc

/-- The staged program passes `linearArrB` when `NFProg.ofCom c` does. -/
theorem stageOuts_linearArrB {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (h : stageOuts ws nOut c = some p) (hc : linearArrB (NFProg.ofCom c) = true) :
    linearArrB p = true := by
  obtain ⟨hn, hp⟩ := stageOuts_eq_some h
  unfold linearArrB at hc ⊢
  rw [List.length_append, List.length_singleton]
  exact stageGo_linGo c hp hc (by omega)

/-- The staged program passes `jasminWidthsB` when `NFProg.ofCom c` does, at a register
width `ws`. -/
theorem stageOuts_jasminWidthsB {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (h : stageOuts ws nOut c = some p) (hws : widthOkB ws = true)
    (hc : jasminWidthsB (NFProg.ofCom c) = true) : jasminWidthsB p = true := by
  unfold jasminWidthsB at hc ⊢
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hΓ, _⟩, hw⟩ := hc
  simp only [List.all_append, List.all_cons, List.all_nil, tyOkB, hws, hΓ, Bool.and_self,
    stageGo_widthsGo hws c (stageOuts_eq_some h).2 hw]

/-- **Completeness of the lowering on staged programs**: `nfToJasmin` succeeds on the
staged program of every `c` whose embedding `NFProg.ofCom c` is in the fragment of
`RegionExportable` and passes `linearArrB` and `jasminWidthsB`, at a register width `ws`
and a signature that fits. -/
theorem stageOuts_nfToJasmin_isSome {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (sig : JazzSig (Γ ++ [.stackArr ws nOut]) (.stackArr ws nOut)) (name : String)
    (h : stageOuts ws nOut c = some p) (hws : widthOkB ws = true)
    (hp : RegionExportable (NFProg.ofCom c)) (hlin : linearArrB (NFProg.ofCom c) = true)
    (hw : jasminWidthsB (NFProg.ofCom c) = true) (hsig : sig.Fits) :
    (nfToJasmin sig name p).isSome :=
  nfToJasmin_isSome sig name (stageOuts_regionExportable h hp) (stageOuts_linearArrB h hlin)
    (stageOuts_jasminWidthsB h hws hw) hsig

/-- Under the hypotheses of `stageOuts_nfToJasmin_isSome`, `emitJazzOuts` is the checked
printer applied to the unit `nfToJasmin` returns on the staged program. -/
theorem emitJazzOuts_eq_printChecked {ws nOut : Nat} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {c : Com jasminDialect Γ t}
    {p : NFProg jasminDialect (Γ ++ [.stackArr ws nOut]) [.stackArr ws nOut]}
    (sig : JazzSig (Γ ++ [.stackArr ws nOut]) (.stackArr ws nOut)) (name : String)
    (h : stageOuts ws nOut c = some p) (hws : widthOkB ws = true)
    (hp : RegionExportable (NFProg.ofCom c)) (hlin : linearArrB (NFProg.ofCom c) = true)
    (hw : jasminWidthsB (NFProg.ofCom c) = true) (hsig : sig.Fits) :
    ∃ u, nfToJasmin sig name p = some u ∧
      emitJazzOuts name ws nOut sig c = CatCrypt.Crypto.Jasmin.Jazz.printChecked u := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp
    (stageOuts_nfToJasmin_isSome sig name h hws hp hlin hw hsig)
  refine ⟨u, hu, ?_⟩
  simp [emitJazzOuts, h, JasminPrintText.emitJazzNF, hu]

/-- **A returned text parses to the lowered unit**: the unit `nfToJasmin` returns on the
staged program, without its extern signatures. -/
theorem emitJazzOuts_parse {ws nOut : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {name : String} {sig : JazzSig (Γ ++ [.stackArr ws nOut]) (.stackArr ws nOut)}
    {c : Com jasminDialect Γ t} {s : String} (h : emitJazzOuts name ws nOut sig c = some s) :
    ∃ p u, stageOuts ws nOut c = some p ∧ nfToJasmin sig name p = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok { u with externs := [] } := by
  unfold emitJazzOuts at h
  obtain ⟨p, hp, hs⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u, hu, hparse⟩ := JasminPrintText.emitJazzNF_parse hs
  exact ⟨p, u, hp, hu, hparse⟩

/-! ## 5. Checks -/

/-- The program `x + y`, `x ^ y` on two `reg 64` arguments, whose two bindings are its
outputs. -/
def sumXorCom : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var ⟨.regArith .add 64, rfl, .cons .here (.cons (.there .here) .nil)⟩
    (.var ⟨.regArith .xor 64, rfl, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩
      (.ret .here))

/-- The signature of `sumXorCom` with a two-word output array. -/
def sumXorSig : JazzSig ([.reg 64, .reg 64] ++ [.stackArr 64 2]) (.stackArr 64 2) :=
  outsSig 64 2 [("y", .reg, ptyOf (.reg 64)), ("x", .reg, ptyOf (.reg 64))] rfl

-- The two outputs of `sumXorCom` print to an output array through the checked printer.
#kat (emitJazzOuts "sum_xor_outs" 64 2 sumXorSig sumXorCom).isSome

end CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage
