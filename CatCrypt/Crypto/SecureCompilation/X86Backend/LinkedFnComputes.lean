/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Entry

/-!
# The bytes of a linked function compute a source function

A linked function `l` that meets its contract (`LinkedFn.Meets`) has bytes that decode to a
block whose runs, from an entry state at which the resources of a call hold and the meaning
`l.sem` is defined at the argument values, end in a state from which the layout reads back
the value of the meaning. This module composes that contract with a statement that the
meaning agrees with a source function, so that the conclusion names the source function:

* a function `f : A → β` with encodings `encA` of its arguments and `encB` of its values,
  whose meaning at `encA x` is `encB (f x)` for every `x` in a guard `G` (`Meets.computes`);
  a Lean function read by the Lean front is the instance with `encB = enc`, and the
  correspondence `FnCorres` of the ascent states the agreement for the source run;
* an Aeneas function `src.fn` of a source `src : AeSrc` of the Aeneas front, whose meaning
  agrees with the semantics `aeneasRuns` of the front (`Meets.computes_aeneas`): from an entry
  state that encodes an argument tuple `x` with `src.fn x = .ok y`, every run returns the
  encoding of `y`.

The read-back is stated from the entry registers of the logical variables, the form of the
contract (`LinkedFnContract.resultAt`); when the read-back depends on the entry state only at
the registers of the layout, it is the read-back from the entry state
(`Meets.result_of_sem_entry`).

## Main results

* `contractPre_of_entryAt`: the precondition of the contract from the resources at entry and a
  defined meaning.
* `Meets.result_of_sem`, `Meets.result_of_sem_entry`: every run of the decoded bytes from an
  entry state returns the value of the meaning, and some run exists.
* `Meets.computes`: the bytes compute a function the meaning agrees with.
* `Meets.computes_aeneas`: the bytes compute an Aeneas function the meaning agrees with.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.SecureCompilation.SepLogic
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (abiRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (runOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnContract
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.AeneasFront (AeSrc AeTy aeneasRuns)
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Valuation)
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.Hax.ImpToNF (enc entryCtx EntryVals)
open _root_.Hax (Value Env)
open Footprinted SAssert

namespace CatCrypt.Crypto.Hax.LinkedFn

/-- **The precondition of the contract** holds at a state where the resources at entry hold
    and the meaning is defined at the argument values. -/
theorem contractPre_of_entryAt {l : LinkedFn} {a : CallVar} {s : AState}
    (hs : (l.entryAt a).holds s) (hv : (l.sem a.vals).isSome = true) :
    (l.contractPre a).holds s :=
  ⟨by simp [SAssert.pure], hs, hv⟩

/-- **The runs of the bytes of a linked function return the value of its meaning.** Let `l`
    meet its contract and its bytes decode to `q`. At an entry state where the resources of a
    call at the logical variables `a` hold and the meaning at the argument values `a.vals` is
    `v`, the leaky run of `q` under `.doitm` exists, and every such run ends in a state from
    which the layout reads back `v` at the entry registers `a.rv`. -/
theorem Meets.result_of_sem {l : LinkedFn} (h : l.Meets) {q : List RInstr}
    (hq : decodeLprog l.bytes = some q) {a : CallVar} {s : AState} (hs : (l.entryAt a).holds s)
    {v : Value} (hv : l.sem a.vals = some v) :
    (∃ t s', runOf .doitm q s t s') ∧
      ∀ t s', runOf .doitm q s t s' → l.layout.ResultOf (entryRegs a.rv) s' v := by
  obtain ⟨q', hq', hC⟩ := h.code
  rw [hq] at hq'
  cases hq'
  have hpre : (l.contractPre a).holds s := contractPre_of_entryAt hs (by rw [hv]; rfl)
  refine ⟨hC.halts a s hpre, fun t s' hr => ?_⟩
  obtain ⟨w, hw, hR⟩ := (hC.post a s t s' hpre hr).2.2.2
  rw [hv, Option.some.injEq] at hw
  exact hw ▸ hR

/-- **The runs return the value of the meaning, read back from the entry state.** The
    statement of `Meets.result_of_sem` when the read-back of the result depends on the entry
    state only at the registers of the layout (`hread`; `Haxc.read_entry_congr` gives it when
    the registers of `Haxc.resultRegs` of the result are among them): the read-back is from
    the entry state `s`, and the meaning is taken at the values the layout reads off `s`. -/
theorem Meets.result_of_sem_entry {l : LinkedFn} (h : l.Meets)
    (hread : ∀ sa sb sa' : AState, (∀ r ∈ abiRegs l.layout, sa.regs r = sb.regs r) →
      l.layout.result.read sa sa' = l.layout.result.read sb sa')
    {q : List RInstr} (hq : decodeLprog l.bytes = some q) {a : CallVar} {s : AState}
    (hs : (l.entryAt a).holds s) {v : Value} (hv : l.sem (l.layout.args.map (·.read s)) = some v) :
    (∃ t s', runOf .doitm q s t s') ∧
      ∀ t s', runOf .doitm q s t s' → l.layout.ResultOf s s' v := by
  obtain ⟨hregs, -, hvals, -, -⟩ := holds_entryAt hs
  rw [hvals] at hv
  refine ⟨(h.result_of_sem hq hs hv).1, fun t s' hr => ?_⟩
  have hR := (h.result_of_sem hq hs hv).2 t s' hr
  unfold AbiLayout.ResultOf at hR ⊢
  rw [hR]
  exact hread _ _ _ fun r hr => (hregs r hr).symm

/-- **The bytes of a linked function compute a function its meaning agrees with.** Let `l`
    meet its contract, its bytes decode to `q`, and its meaning at the encoding `encA x` of an
    argument `x` in the guard `G` be the encoding `encB (f x)` of the value of `f`. Then from
    every entry state where the resources of a call hold and the layout reads `encA x`, for
    `x` in the guard, a run of `q` exists, and every run ends in a state from which the layout
    reads back `encB (f x)` at the entry registers. -/
theorem Meets.computes {A β : Type} {l : LinkedFn} (h : l.Meets) (encA : A → List Value)
    (encB : β → Value) (G : A → Prop) (f : A → β)
    (hf : ∀ x, G x → l.sem (encA x) = some (encB (f x))) {q : List RInstr}
    (hq : decodeLprog l.bytes = some q) {a : CallVar} {s : AState} (hs : (l.entryAt a).holds s)
    {x : A} (hG : G x) (hx : l.layout.args.map (·.read s) = encA x) :
    (∃ t s', runOf .doitm q s t s') ∧
      ∀ t s', runOf .doitm q s t s' → l.layout.ResultOf (entryRegs a.rv) s' (encB (f x)) := by
  have hvals : a.vals = encA x := (holds_entryAt hs).2.2.1.symm.trans hx
  exact h.result_of_sem hq hs (hvals ▸ hf x hG)

/-- **The bytes of a linked function compute an Aeneas function its meaning agrees with.**
    Let `l` meet its contract, its bytes decode to `q`, and its meaning agree with the
    semantics `aeneasRuns` of the Aeneas front at the source `src`: at an entry state from
    which a run of the source returns `v`, the meaning at the values the layout reads is `v`.
    Let the entry state `s` encode an argument tuple `x` of `src.fn`: the layout reads off `s`
    an environment `e` holding the encodings of the valuation `V`, the image of `x`. If
    `src.fn x = .ok y`, a run of `q` from `s` exists, and every run ends in a state from which
    the layout reads back the encoding of the image of `y`. -/
theorem Meets.computes_aeneas {l : LinkedFn} (h : l.Meets) (src : AeSrc)
    (hag : ∀ sa v, aeneasRuns l.layout src sa v →
      l.sem (l.layout.args.map (·.read sa)) = some v)
    {q : List RInstr} (hq : decodeLprog l.bytes = some q) {a : CallVar} {s : AState}
    (hs : (l.entryAt a).holds s) (hΓ : entryCtx (abiEntry l.layout) = src.Γ) {e : Env}
    {V : Valuation (entryCtx (abiEntry l.layout))} (he : l.layout.EnvOf s e)
    (hV : EntryVals e (abiEntry l.layout) V) {x : AeTy.Args src.args} (hx : hΓ ▸ V = src.argVal x)
    {y : src.res.denote} (hy : src.fn x = .ok y) :
    (∃ t s', runOf .doitm q s t s') ∧
      ∀ t s', runOf .doitm q s t s' →
        l.layout.ResultOf (entryRegs a.rv) s' (enc src.t (src.resVal y)) := by
  have hv := hag s _ ⟨hΓ, e, V, x, y, he, hV, hx, hy, rfl⟩
  rw [(holds_entryAt hs).2.2.1] at hv
  exact h.result_of_sem hq hs hv

end CatCrypt.Crypto.Hax.LinkedFn
