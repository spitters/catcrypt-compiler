/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.BytesToDialectJoin

/-!
# Discharging the lift's freshness hypothesis from a decidable check

`JInstrToArithBlock.liftBlock_runBlock` carries `FreshFor nm (dstStream ops)` as
a hypothesis. This module derives that hypothesis from a Boolean check on the
parsed ops together with a finite list of the live register names.

## The decomposition

`dstStream ops i` is the `i`-th op's destination inside the list and
`padName (i - ops.length)` past the end, so `FreshFor nm (dstStream ops)` splits
into four conditions: the destinations in `ops` are pairwise distinct; no
destination is a padding name; no destination is the name of a live variable; no
live name is a padding name.

The two padding conditions quantify over an index, so they are routed through
`NotPad` and its Boolean sufficient condition `notPadB`: a name whose character
list is `'%' :: c :: rest` with `c ≠ 'p'` is not a padding name. The other two
conditions are `List.Nodup` and list membership on concrete data.

## What is proved

* `notPad_of_notPadB` — the Boolean condition implies `NotPad`.
* `freshFor_of_checks` — the four conditions give `FreshFor nm (dstStream ops)`.
* `freshFor_of_freshCheck` — the same from the single Boolean `freshCheck`.
* `liftBlock_runBlock_checked` — the lift with `freshCheck ops live = true` and
  the enumeration of live names in place of `FreshFor`.
* `joinOps_fresh_checked` — the freshness of the `BytesToDialectJoin` allocation
  obtained from `freshCheck`.

The caller supplies only `hlive`, the list containing every live register name.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. Not a padding name -/

/-- A name distinct from every padding name. -/
def NotPad (r : String) : Prop := ∀ k : Nat, r ≠ padName k

/-- The Boolean sufficient condition for `NotPad`: the character list is `'%'`
    followed by a character other than `'p'`. -/
def notPadB (r : String) : Bool :=
  match r.toList with
  | '%' :: c :: _ => c != 'p'
  | _ => false

/-- `notPadB` implies `NotPad`. -/
theorem notPad_of_notPadB {r : String} (h : notPadB r = true) : NotPad r := by
  intro k
  unfold notPadB at h
  split at h
  · rename_i c rest hr
    exact ne_padName_of_second r c rest hr (by simpa using h) k
  · exact absurd h (by simp)

/-! ## 2. Reading the destination stream -/

/-- Inside the list, the stream is the op's destination. -/
theorem dstStream_eq_dst {ops : List RawArith} {i : Nat} {o : RawArith}
    (h : ops[i]? = some o) : dstStream ops i = o.dst := by
  simp [dstStream, h]

/-- Past the end of the list, the stream is a padding name. -/
theorem dstStream_eq_pad {ops : List RawArith} {i : Nat} (h : ops[i]? = none) :
    dstStream ops i = padName (i - ops.length) := by
  simp [dstStream, h]

/-- Distinct in-range indices of a list with pairwise-distinct destinations give
    distinct destinations. -/
theorem dst_ne_of_nodup {ops : List RawArith}
    (hnd : (ops.map RawArith.dst).Nodup) {i j : Nat} {oi oj : RawArith}
    (hi : ops[i]? = some oi) (hj : ops[j]? = some oj) (hij : i ≠ j) :
    oi.dst ≠ oj.dst := by
  intro hdst
  refine hij ((List.getElem?_inj (l := ops.map RawArith.dst) ?_ hnd).mp ?_)
  · simpa using (List.getElem?_eq_some_iff.mp hi).1
  · simp only [List.getElem?_map, hi, hj, Option.map_some, hdst]

/-! ## 3. The freshness invariant from the four conditions -/

/-- **Freshness from the four conditions.** The destinations in `ops` pairwise
    distinct, none of them a padding name, none of them the name of a live
    variable, and no live name a padding name, give the fresh-allocation
    invariant for the destination stream. -/
theorem freshFor_of_checks {Γ : Ctxt jasminDialect} (nm : RegMapG Γ)
    (ops : List RawArith) (live : List String)
    (hlive : ∀ v : Ctxt.Var Γ (.reg 64), nm v ∈ live)
    (hnd : (ops.map RawArith.dst).Nodup)
    (hdp : ∀ o ∈ ops, NotPad o.dst)
    (hlp : ∀ r ∈ live, NotPad r)
    (hdis : ∀ o ∈ ops, o.dst ∉ live) :
    FreshFor nm (dstStream ops) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    rcases hi : ops[i]? with _ | oi
    · rcases hj : ops[j]? with _ | oj
      · rw [dstStream_eq_pad hi, dstStream_eq_pad hj]
        have hli := List.getElem?_eq_none_iff.mp hi
        have hlj := List.getElem?_eq_none_iff.mp hj
        exact fun h => hij (by have := padName_inj h; omega)
      · rw [dstStream_eq_pad hi, dstStream_eq_dst hj]
        exact fun h =>
          hdp oj (List.mem_of_getElem? hj) (i - ops.length) h.symm
    · rcases hj : ops[j]? with _ | oj
      · rw [dstStream_eq_dst hi, dstStream_eq_pad hj]
        exact hdp oi (List.mem_of_getElem? hi) (j - ops.length)
      · rw [dstStream_eq_dst hi, dstStream_eq_dst hj]
        exact dst_ne_of_nodup hnd hi hj hij
  · intro i v
    rcases hi : ops[i]? with _ | oi
    · rw [dstStream_eq_pad hi]
      exact fun h => hlp (nm v) (hlive v) (i - ops.length) h.symm
    · rw [dstStream_eq_dst hi]
      exact fun h => hdis oi (List.mem_of_getElem? hi) (h ▸ hlive v)

/-! ## 4. The Boolean front end -/

/-- The Boolean freshness check on the parsed ops and the list of live register
    names: the destinations are pairwise distinct, neither the destinations nor
    the live names are padding names, and no destination is live. -/
def freshCheck (ops : List RawArith) (live : List String) : Bool :=
  decide (ops.map RawArith.dst).Nodup && ops.all (fun o => notPadB o.dst)
    && live.all notPadB && ops.all (fun o => !(live.contains o.dst))

/-- **Freshness from the Boolean check.** The only hypothesis left to the caller
    is the list containing every live register name. -/
theorem freshFor_of_freshCheck {Γ : Ctxt jasminDialect} (nm : RegMapG Γ)
    (ops : List RawArith) (live : List String)
    (hlive : ∀ v : Ctxt.Var Γ (.reg 64), nm v ∈ live)
    (h : freshCheck ops live = true) :
    FreshFor nm (dstStream ops) := by
  simp only [freshCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hnd, hdp⟩, hlp⟩, hdis⟩ := h
  refine freshFor_of_checks nm ops live hlive hnd (fun o ho => notPad_of_notPadB (hdp o ho))
    (fun r hr => notPad_of_notPadB (hlp r hr)) (fun o ho hmem => ?_)
  have hc : live.contains o.dst = true := List.contains_iff_mem.mpr hmem
  have hno := hdis o ho
  rw [hc] at hno
  exact absurd hno (by simp)

/-! ## 5. The lift with the check in place of the hypothesis -/

/-- **The lift, freshness discharged by the check.** The statement of
    `liftBlock_runBlock` with `FreshFor nm (dstStream ops)` replaced by the
    Boolean `freshCheck` and the enumeration of the live register names. -/
theorem liftBlock_runBlock_checked {Γ : Ctxt jasminDialect}
    (blk : List (JInstr 64)) (ops : List RawArith)
    (nm : RegMapG Γ) (find : String → Option (Ctxt.Var Γ (.reg 64)))
    (hfind : ∀ (v : Ctxt.Var Γ (.reg 64)) (r : String), find r = some v → nm v = r)
    (out : String) (ab : ArithBlock Γ) (live : List String)
    (hlive : ∀ v : Ctxt.Var Γ (.reg 64), nm v ∈ live)
    (hparse : parseBlock blk = some ops) (helab : elabOps find ops out = some ab)
    (hcheck : freshCheck ops live = true)
    (s : JState 64) (V : Ctxt.Valuation Γ) (hinterp : JStateInterpG nm V s) :
    (runBlock s blk).get (outReg ab nm (dstStream ops)) = ab.toCom.denote V :=
  liftBlock_runBlock blk ops nm find hfind out ab hparse helab s V hinterp
    (freshFor_of_freshCheck nm ops live hlive hcheck)

/-! ## 6. The check on the concrete allocation of `BytesToDialectJoin` -/

/-- The live register names of `Γj` under `nmJ`. -/
def liveJ : List String := ["%rax", "%rbx"]

/-- Every `Γj` variable's register name is in `liveJ`. -/
theorem nmJ_mem_liveJ : ∀ v : Ctxt.Var Γj (.reg 64), nmJ v ∈ liveJ := by
  intro v
  match v with
  | .here => exact List.Mem.head _
  | .there .here => exact List.Mem.tail _ (List.Mem.head _)

/-- The Boolean check passes on the one-op allocation of `BytesToDialectJoin`. -/
theorem joinOps_freshCheck : freshCheck joinOps liveJ = true := by decide

/-- The fresh-allocation invariant of `joinOps_fresh`, obtained from the Boolean
    check and the enumeration of the live names. -/
theorem joinOps_fresh_checked : FreshFor nmJ (dstStream joinOps) :=
  freshFor_of_freshCheck nmJ joinOps liveJ nmJ_mem_liveJ joinOps_freshCheck

end CatCrypt.Crypto.SecureCompilation.Ascent
