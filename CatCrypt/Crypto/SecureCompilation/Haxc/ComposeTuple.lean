/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTPub
public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCrypt.Crypto.SecureCompilation.Haxc.TupleTail

@[expose] public section

set_option autoImplicit false

/-!
# The compiler on a pair of an array and one of its words

A kernel whose body ends in `let y = a[k]; (a, y)` returns its array accumulator and the word
at the index `k`. Its layout reads the pair back as `.tuple [.words r n, .wordAt r i]`, `i`
the register of the scalar parameter `k`. The first stage of `compileA`, `pairStage`, compiles
such a body with that tail replaced by `a` (`stripArrTailT`) under the array part of the
layout (`AbiLayout.arrPart`), and `haxc_correct_auto` reads the pair back
(`haxRuns_pairStage`).

`haxc_correct_auto_tuple` is `haxc_correct_auto` on a single function with a pair tail
(`pairTailOf`), stated from a run of the source reading: the source condition of the
word-array route on the stripped body gives that the run returns a value that is not a
control-flow value.

## Main results

* `wordArrResult_bindConsts` — the source condition of the word-array route passes to the
  extraction with the constants of the layout bound.
* `haxc_correct_auto_tuple` — the value theorem of `compileA` at a pair result, from a run of
  the source reading.

The joint value and constant-time theorem at a pair result,
`haxc_correct_auto_tuple_ct_regions`, is in `ComposeCTStraight`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.Hax (hax64WExit)
open _root_.Hax (TExpr Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-- The source condition of the word-array route passes to the extraction with the constants
    of the layout bound at its head. -/
theorem wordArrResult_bindConsts {σ : AbiLayout} {te : TExpr} (h : WordArrResult σ te) :
    WordArrResult σ (bindConsts σ.consts te) := by
  intro sa env fuel v env' hsep henv hrun
  rw [run_bindConsts_of_envOf hax64WExit fuel te henv] at hrun
  exact h sa env fuel v env' hsep henv hrun

/-- A run of the source reading of a function with a pair tail (`pairTailOf`) from an
    environment `σ` reads off an entry state satisfying `σ.Regions` returns a value that is
    not a control-flow value, when the stripped body satisfies the source condition of the
    word-array route at the array part of `σ`: the stripped body returns an array of
    integers (`denoteSpine_stripArrTail`), and the pair of it and its word at an index is no
    control-flow value. -/
theorem isControlFlow_false_of_pairTail {te : TExpr} {σ : AbiLayout} {d : String × String}
    (hpt : pairTailOf te σ = some d) (hres : WordArrResult σ.arrPart (stripArrTailT te))
    {sa : AState} (hsep : σ.Regions sa) {env : Env} (henv : σ.EnvOf sa env)
    {fuel : Nat} {v : Value} {env' : Env}
    (hrun : (denoteSpine hax64WExit fuel te.erase).run env = (.val v, env')) :
    v.isControlFlow = false := by
  obtain ⟨hdat, -⟩ := pairTailOf_spec hpt
  obtain ⟨r, n, a, -, htail, hk, hkeep⟩ := arrWordTailOf_spec hdat
  obtain ⟨x, env'', hrs, hdisj⟩ := denoteSpine_stripArrTail hax64WExit fuel te.erase htail hkeep
    (envOf_scalarArg hk henv) hrun
  rw [← erase_stripArrTailT] at hrs
  obtain ⟨zs, rfl⟩ := hres sa env fuel _ env'' ((arrPart_regions σ sa).2 hsep)
    ((arrPart_envOf σ sa env).2 henv) hrs
  rcases hdisj with ⟨hcf, -⟩ | ⟨-, w, hw, hv⟩
  · simp [Value.isControlFlow] at hcf
  · obtain ⟨z, rfl⟩ := index_int_words hw rfl
    rcases hv with ⟨hwc, -⟩ | rfl
    · simp [Value.isControlFlow] at hwc
    · rfl

/-- **The general compiler theorem on a pair result, from a run of the source reading.** For
    the result of `compileA` on a function `te` with a pair tail at `σ` (`pairTailOf`), under
    the source condition of the word-array route on the stripped body at the array part of
    the layout: from every entry state satisfying `σ.Regions` and every hax environment `σ`
    reads off it, every run of the source reading of `te` to a value `v` is matched by a
    halting run of the machine on the decoded bytes from which `σ` reads back `v`, the pair.
    It is `haxc_correct_auto` at the single function, on a layout whose narrow parameters are
    not cut to their widths (`hn`), where the source reads the whole registers. -/
theorem haxc_correct_auto_tuple (te : TExpr) (σ : AbiLayout) (fname : String) (P : Lprog)
    (bytes : List (BitVec 8)) (hc : compileA te σ fname = some (P, bytes))
    {d : String × String} (hpt : pairTailOf te σ = some d)
    (hres : WordArrResult σ.arrPart (stripArrTailT te))
    (sa : AState) (hsep : σ.Regions sa) (env : Env) (henv : σ.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WExit fuel te.erase).run env = (.val v, env'))
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' v := by
  have he : narrowEntry te σ sa = sa := by simp [narrowEntry, hn]
  obtain ⟨prog, hd, ⟨sa', hh, hR, -⟩ | ⟨cs, hsub, hne, -⟩⟩ :=
    haxc_correct_auto te σ fname P bytes hc sa hsep v
      ((haxRuns_single σ te sa v).mpr ⟨env, fuel, env', (by rw [he]; exact henv), hrun,
        isControlFlow_false_of_pairTail hpt hres hsep henv hrun⟩)
  · exact ⟨prog, sa', hd, hh, hR⟩
  · exact absurd (List.sublist_nil.mp hsub) hne

end CatCrypt.Crypto.SecureCompilation.Haxc
