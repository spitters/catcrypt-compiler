/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram
public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockRealloc
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.Ascent.Control

/-!
# The counted loop over the `psem.v` mirror and over `runBlock`

`ComJasminBridgeProgram.corresSem_for` relates a counted `Cfor` over the `psem.v`
mirror to the abstract loop `forFold step n`. This module identifies that abstract
loop with the abstract loops of the ascent's loop rules, `loopStep` of
`corresJ_loop` (over `runBlock`) and `nfold` of `corres_for` (over `semScalar`), so
that a loop proved on two machines at the same abstract step gives the same
abstract result on both.

## Main results

* `forFold_eq_loopStep`, `forFold_const_eq_nfold` — the abstract loops coincide.
* `iterFold_eq_nfold` — the abstract loop of `corresSem_while` is `nfold`.
* `mulx_hi_eq_mulHiW` — the high word of `x86_MULX_lo_hi` is `mulHiW`.
* `mulhiLoop_corresJ` — the `runBlock` loop of `n` copies of `MULX h, lo, h, b`
  corresponds at `loopStep (hiStep b) n`, by `corresJ_loop`.
* `mulhiLoop_mirror_runBlock` — the mirror program `MulhiLoop.mainLoop n` (a
  `Cfor` calling a function whose body is a `MULX_64` `Copn`) ends with the word
  at `h` that the `runBlock` loop leaves in register `h`, from states agreeing on
  `h` and `b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.CoqSemMirror
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComJasminBridgeProgram

/-- The abstract loop of `corresSem_for` is the abstract loop of `corresJ_loop`. -/
theorem forFold_eq_loopStep {A : Type} (step : Nat → A → A) :
    ∀ n, forFold step n = loopStep step n
  | 0 => rfl
  | n + 1 => by
    funext a
    show step n (forFold step n a) = step n (loopStep step n a)
    rw [forFold_eq_loopStep step n]

/-- At a step independent of the index, the abstract loop of `corresSem_for` is
    the abstract loop of `corres_for`. -/
theorem forFold_const_eq_nfold {A : Type} (fa : A → A) :
    ∀ n, forFold (fun _ => fa) n = nfold fa n
  | 0 => rfl
  | n + 1 => by
    funext a
    show fa (forFold (fun _ => fa) n a) = fa (nfold fa n a)
    rw [forFold_const_eq_nfold fa n]

/-- The abstract loop of `corresSem_while` is the abstract loop of `corres_for`. -/
theorem iterFold_eq_nfold {A : Type} (fa : A → A) (n : Nat) : iterFold fa n = nfold fa n :=
  forFold_const_eq_nfold fa n

/-- The high word of the x86 `MULX` result tuple is `mulHiW`. -/
theorem mulx_hi_eq_mulHiW (a b : BitVec 64) : (x86_MULX_lo_hi a b).2 = mulHiW a b := by
  simp only [x86_MULX_lo_hi, wumul, mulHiW, high_bits]

/-- The `runBlock` loop of `n` copies of `MULX h, lo, h, b` corresponds, over the
    relation reading `h` and `b`, at `loopStep (hiStep b) n`. -/
theorem mulhiLoop_corresJ (b : BitVec 64) (n : Nat) :
    CorresJ (fun st h => st.get "h" = h ∧ st.get "b" = b) (fun _ => True)
      (loopStep (MulhiLoop.hiStep b) n)
      (loopBlock (fun _ => lowerMulHi "h" "b" "h" "lo") n) := by
  refine corresJ_loop _ (fun _ => ?_) (fun _ _ _ => trivial) n
  intro st h ⟨hh, hb⟩ _
  refine ⟨?_, ?_⟩
  · rw [lowerMulHi_get_dstHi, hh, hb, MulhiLoop.hiStep, mulx_hi_eq_mulHiW]
  · rw [lowerMulHi_get_other _ _ _ _ _ (by decide) (by decide), hb]

/-- **The mirror loop and the `runBlock` loop agree.** From a mirror state and a
    `JState` holding the same `h0` at `h` and `b` at `b`, the mirror program
    `MulhiLoop.mainLoop n` has a `SemIr` derivation under `x86AsmSem` to a state
    whose `h` holds the word that `runBlock` of the `n`-fold `MULX` loop leaves in
    register `h`, and whose memory is unchanged. -/
theorem mulhiLoop_mirror_runBlock {SyscallState Mem : Type} [MemModel Mem]
    (opS : OpSem) (gd : GlobDecls) (n : Nat) (h0 b : BitVec 64)
    (s : Estate SyscallState Mem) (st : JState 64)
    (hh : (s.evm).get (MulhiLoop.wv "h").v_var = .Vword .U64 h0)
    (hb : (s.evm).get (MulhiLoop.wv "b").v_var = .Vword .U64 b)
    (sth : st.get "h" = h0) (stb : st.get "b" = b) :
    ∃ s', SemIr x86AsmSem opS gd MulhiLoop.prog s (MulhiLoop.mainLoop n) s'
      ∧ (s'.evm).get (MulhiLoop.wv "h").v_var
          = .Vword .U64
              ((runBlock st (loopBlock (fun _ => lowerMulHi "h" "b" "h" "lo") n)).get "h")
      ∧ s'.emem = s.emem := by
  obtain ⟨s', hs', hh', hm'⟩ := MulhiLoop.mainLoop_sem opS gd n h0 b s hh hb
  refine ⟨s', hs', ?_, hm'⟩
  rw [hh', (mulhiLoop_corresJ b n st h0 ⟨sth, stb⟩ trivial).1]
  exact congrArg (Value.Vword .U64)
    (congrFun (forFold_eq_loopStep (MulhiLoop.hiStep b) n) h0)

end CatCrypt.Crypto.SecureCompilation.Ascent
