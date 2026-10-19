/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.Peephole
public import CatCrypt.Crypto.Jasmin.JazzRoundTrip
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
public meta import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public meta import CatCrypt.Crypto.Jasmin.JazzRoundTrip

/-!
# Jasmin text of dialect programs through the single printer

The text of a straight-line program `Com jasminDialect Γ t` and of a structured program
`NFProg jasminDialect Γ [t]` is the lowering `nfToJasmin` to a compilation unit followed by
the checked printer `Jazz.printChecked`, which returns the text only when it parses back
to the erasure of the unit.

A bounded loop `JForProg accTy` (`acc := init; for _ in 0..n { acc := update acc }`)
becomes the structured program `JForProg.toNF`: the trip count `n` bound by `regConst 64`,
then a counted loop `forLoop` carrying the accumulator, whose body is `update` embedded
in the loop context. A list of loops run in sequence is `JForProg.seqToNF`.

## Main definitions

* `emitJazzNF`, `emitJazzN`: the text of a structured and of a straight-line program.
* `JazzSig.acc`: the signature `reg acc → reg` of a one-accumulator function.
* `JForProg.loopK`, `JForProg.toNF`, `JForProg.seqToNF`: bounded loops as structured
  programs.

## Main results

* `emitJazzNF_parse`, `emitJazzN_parse`: a returned text parses to the lowered unit
  without its extern signatures.
* `JForProg.loopK_denote`, `JForProg.toNF_denote`, `JForProg.seqToNF_denote`: the
  structured programs denote the `n`-fold iteration of the loop body, for every trip
  count below `2 ^ 64` and every fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

/-! ## 1. Bounded loops as structured programs -/

/-- The embedding of the one-variable context `[t]` as the head of `t :: Δ`. -/
def headHom {t : JasminTy} (Δ : Ctxt jasminDialect) : Ctxt.Hom [t] (t :: Δ) := fun
  | .here => .here

/-- The valuation of `[t]` read off the head of a valuation of `t :: Δ`. -/
theorem comap_headHom {t : JasminTy} {Δ : Ctxt jasminDialect} (a : ⟦t⟧)
    (V : Ctxt.Valuation Δ) :
    (Ctxt.Valuation.comap (headHom Δ) (.cons a V : Ctxt.Valuation (t :: Δ))) = .cons a .nil :=
  Ctxt.Valuation.ext _ _ fun _ v => by
    cases v with
    | here => rfl
    | there v => cases v

/-- The loop `p` on the accumulator at the head of the context `accTy :: Δ`, followed by
the continuation `k`: the trip count `p.n` is bound by `regConst 64`, and the counted
loop carries the accumulator through `update` embedded in the loop context. The
continuation sees the final accumulator, the trip count and the context. -/
def JForProg.loopK {accTy : JasminTy} (p : JForProg accTy) {Δ : Ctxt jasminDialect}
    {ts : List JasminTy} (k : NFProg jasminDialect (accTy :: JasminTy.reg 64 :: accTy :: Δ) ts) :
    NFProg jasminDialect (accTy :: Δ) ts :=
  .var ⟨JasminOp.regConst 64 p.n, rfl, .nil⟩
    (NFProg.forLoop (d := jasminDialect) (cs := [accTy])
      (Γ := JasminTy.reg 64 :: accTy :: Δ) .here (.cons (.there .here) .nil)
      (NFProg.ofCom (p.update.rename (headHom _))) k)

/-- The structured program of a bounded loop: `loopK` followed by the return of the
final accumulator. -/
def JForProg.toNF {accTy : JasminTy} (p : JForProg accTy) :
    NFProg jasminDialect [accTy] [accTy] :=
  p.loopK (Δ := []) (.ret (.cons .here .nil))

/-- The structured program of a list of loops run in sequence on one accumulator. -/
def JForProg.seqToNF {accTy : JasminTy} :
    List (JForProg accTy) → {Δ : Ctxt jasminDialect} → NFProg jasminDialect (accTy :: Δ) [accTy]
  | [], _ => .ret (.cons .here .nil)
  | p :: ps, _ => p.loopK (seqToNF ps)

/-- Folding a step that agrees with a total step `g` is `some` of the fold of `g`. -/
private theorem foldlM_eq_some_foldl {α β : Type} {f : α → β → Option α} (l : List β) (g : α → β → α)
    (a : α) (h : ∀ acc b, f acc b = some (g acc b)) :
    l.foldlM f a = some (l.foldl g a) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [List.foldlM_cons, h, Option.bind_eq_bind, Option.bind_some,
      List.foldl_cons]; exact ih _

/-- The fold of the step of `p` on one-variable valuations is the fold of the step on
values. -/
theorem JForProg.foldl_step {accTy : JasminTy} (p : JForProg accTy) {β : Type} (l : List β)
    (a : ⟦accTy⟧) :
    l.foldl (fun (acc : Ctxt.Valuation (d := jasminDialect) [accTy]) _ =>
        .cons (p.step acc.head) .nil) (.cons a .nil)
      = (.cons (l.foldl (fun acc _ => p.step acc) a) .nil :
          Ctxt.Valuation (d := jasminDialect) [accTy]) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (p.step a)

/-- **The loop with a continuation denotes the `n`-fold iteration of the body**, then the
continuation at the final accumulator, the trip count and the context. -/
theorem JForProg.loopK_denote {accTy : JasminTy} (p : JForProg accTy)
    {Δ : Ctxt jasminDialect} {ts : List JasminTy}
    (k : NFProg jasminDialect (accTy :: JasminTy.reg 64 :: accTy :: Δ) ts)
    (hn : p.n < 2 ^ 64) (fuel : Nat) (a : ⟦accTy⟧) (V : Ctxt.Valuation Δ) :
    (p.loopK k).denote fuel (.cons a V) =
      k.denote fuel (.cons (p.denote a) (.cons (BitVec.ofNat 64 p.n) (.cons a V))) := by
  simp only [JForProg.loopK, NFProg.denote, NFProg.denote_ofCom,
    Expr.denoteM_option_eq_some, Option.bind_eq_bind, Option.bind_some]
  rw [foldlM_eq_some_foldl _ (fun acc _ => .cons (p.step acc.head) .nil)]
  · have hc : (⟨JasminOp.regConst 64 p.n, rfl, .nil⟩ :
        Expr jasminDialect (accTy :: Δ) (JasminTy.reg 64)).denote (.cons a V) =
          BitVec.ofNat 64 p.n := rfl
    have ht : (BitVec.ofNat 64 p.n).toNat = p.n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    simp only [hc]
    dsimp only [Ctxt.Var.lookup, Ctxt.Valuation.extend, Expr.lookupArgs, HasWord64.toNat]
    erw [ht, p.foldl_step]
    rfl
  · intro acc i
    cases acc with
    | cons a' acc =>
        cases acc
        simp only [Com.denote_rename]
        exact congrArg (fun x => some (HVector.cons (p.update.denote x) .nil))
          (comap_headHom a' _)

/-- **The structured program of a bounded loop denotes the loop**: at every fuel and
every trip count below `2 ^ 64`, `p.toNF` returns the `p.n`-fold iteration of the body
on the start value. -/
theorem JForProg.toNF_denote {w : Nat} (p : JForProg (.reg w)) (hn : p.n < 2 ^ 64)
    (fuel : Nat) (a : BitVec w) :
    p.toNF.denote fuel (.cons a .nil) = some (.cons (p.denote a) .nil) := by
  unfold JForProg.toNF
  rw [JForProg.loopK_denote p _ hn fuel a .nil]
  rfl

/-- **The sequence of loops denotes the sequential composition of the loops**: at every
fuel, when every trip count is below `2 ^ 64`. -/
theorem JForProg.seqToNF_denote {accTy : JasminTy} :
    (ps : List (JForProg accTy)) → (∀ p ∈ ps, p.n < 2 ^ 64) → {Δ : Ctxt jasminDialect} →
    (fuel : Nat) → (a : ⟦accTy⟧) → (V : Ctxt.Valuation Δ) →
    (JForProg.seqToNF ps (Δ := Δ)).denote fuel (.cons a V) =
      some (.cons (ps.foldl (fun acc p => p.denote acc) a) .nil)
  | [], _, _, _, _, _ => rfl
  | p :: ps, h, _, fuel, a, V => by
      simp only [JForProg.seqToNF, List.foldl_cons]
      rw [JForProg.loopK_denote p _ (h p List.mem_cons_self) fuel a V]
      exact JForProg.seqToNF_denote ps (fun q hq => h q (List.mem_cons_of_mem _ hq)) fuel _ _

end CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
open CatCrypt.Crypto.Jasmin.Jazz (JazzUnit)

/-! ## 2. The text of a program -/

/-- The text of the structured program `p` as the `export fn` `name` with the signature
`sig`: `nfToJasmin` followed by the checked printer. -/
def emitJazzNF {Γ : Ctxt jasminDialect} {t : JasminTy} (name : String) (sig : JazzSig Γ t)
    (p : NFProg jasminDialect Γ [t]) : Option String :=
  (nfToJasmin sig name p).bind CatCrypt.Crypto.Jasmin.Jazz.printChecked

/-- The text of the straight-line program `com`: `emitJazzNF` of its embedding. -/
def emitJazzN {Γ : Ctxt jasminDialect} {t : JasminTy} (name : String) (sig : JazzSig Γ t)
    (com : Com jasminDialect Γ t) : Option String :=
  emitJazzNF name sig (NFProg.ofCom com)

/-- **A returned text parses to the lowered unit**: the unit `nfToJasmin` returns, without
its extern signatures, which the parser does not read. -/
theorem emitJazzNF_parse {Γ : Ctxt jasminDialect} {t : JasminTy} {name : String}
    {sig : JazzSig Γ t} {p : NFProg jasminDialect Γ [t]} {s : String}
    (h : emitJazzNF name sig p = some s) :
    ∃ u, nfToJasmin sig name p = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok { u with externs := [] } := by
  unfold emitJazzNF at h
  obtain ⟨u, hu, hs⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨u, hu, ?_⟩
  rw [(CatCrypt.Crypto.Jasmin.Jazz.printChecked_sound hs).2, nfToJasmin_erase hu]

/-- **A returned text of a straight-line program parses to the lowered unit** without its
extern signatures. -/
theorem emitJazzN_parse {Γ : Ctxt jasminDialect} {t : JasminTy} {name : String}
    {sig : JazzSig Γ t} {com : Com jasminDialect Γ t} {s : String}
    (h : emitJazzN name sig com = some s) :
    ∃ u, nfToJasmin sig name (NFProg.ofCom com) = some u ∧
      CatCrypt.Crypto.Jasmin.JazzToInstrR.parseUnit s = .ok { u with externs := [] } :=
  emitJazzNF_parse h

/-- The signature of a one-accumulator function: the register parameter `acc` and a
register result, both at the surface type of `t`. -/
def JazzSig.acc (t : JasminTy) : JazzSig [t] t where
  params := [("acc", .reg, ptyOf t)]
  result := (.reg, ptyOf t)
  resultParam := none
  params_length := rfl

/-! ## 3. Checks -/

-- The doubling loop `JasminPrint.doubleLoop` prints through the checked printer.
#kat (emitJazzNF "double_loop" (JazzSig.acc (.reg 64)) JasminPrint.doubleLoop.toNF).isSome

end CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintText
