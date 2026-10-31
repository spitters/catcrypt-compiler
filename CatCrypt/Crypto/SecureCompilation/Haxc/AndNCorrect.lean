/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.AndNFacts
public import CatCrypt.Crypto.SecureCompilation.Haxc.AndNFacts
public meta import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The general compiler theorem on `mpn_and_n`

`mpn_and_n` (from `mpn-hax`) is a word-only loop kernel over three arrays of `4` words
(`[u64; NU]` in the source) and a count `n`. The typed front lowers it through the word-array
lowering `exitArrLower`, and the back half compiles its single runtime-count loop through the
image route.

`mpn_and_n_correct_auto` is the case without linked functions of `haxc_correct_auto`,
`NFEntry.compileR_correct` at the hax entry, at `mpn_and_n` under the System V layout
`andAbi4` of `AndNFacts` (`rp` in
`%rdi`, `up` in `%rsi`, `vp` in `%rdx`, four words each, `n` in `%rcx` at most `4`, the result
the four words at the entry `%rdi`, the stack frame from `-256` to `-8`), with the source
condition of the word-array route discharged by `and_wordArrResult` of `AndNFacts`. Its
hypotheses are the compilation, the separation and bounds of the entry state
(`andAbi4.Regions`), an environment the layout reads off it, and the source run.

## Main results

* `and_bindConsts` — `andAbi4` binds no constant.
* `mpn_and_n_correct_auto` — the general compiler theorem at `mpn_and_n`.

`mpn_and_n` is a kernel, linked code outside the compiler's source; this module is an
illustrative instance of the general theorem, and a correct compiler change that breaks it
removes the instance rather than adapting the compiler.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open _root_.Hax (Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (hax64WExit)

/-! ## The compiler taking no witness -/

/-- The layout `andAbi4` binds no constant, so `compileA` compiles `mpn_and_n` itself. -/
theorem and_bindConsts : bindConsts andAbi4.consts Mpn.mpn_and_n_texpr = Mpn.mpn_and_n_texpr :=
  rfl

/-- **The general compiler theorem at `mpn_and_n` with no witness.** For the result of
    `compileA` on `mpn_and_n` under `andAbi4`: from every entry state satisfying
    `andAbi4.Regions` (the count `%rcx` at most `4`, the three arrays pairwise disjoint and
    disjoint from the stack frame) and every hax environment `andAbi4` reads off it, every run
    of the source reading to a value `v` is matched by a halting run of the machine on the
    decoded bytes from which `andAbi4` reads back `v`. -/
theorem mpn_and_n_correct_auto (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.mpn_and_n_texpr andAbi4 "mpn_and_n" = some (P, bytes))
    (sa : AState) (hsep : andAbi4.Regions sa) (env : Env) (henv : andAbi4.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WExit fuel Mpn.mpn_and_n_texpr.erase).run env = (.val v, env')) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ andAbi4.ResultOf sa sa' v := by
  obtain ⟨prog, sa', hd, hh, hR, -⟩ :=
    haxEntry.compileR_correct (Mpn.mpn_and_n_texpr : CatCrypt.Crypto.Hax.HaxModule) andAbi4
      "mpn_and_n" P bytes
      ((linkedNil_compileA_eq (m := Mpn.mpn_and_n_texpr) rfl _ _).symm.trans hc) sa hsep v
      ((haxRuns_single andAbi4 Mpn.mpn_and_n_texpr sa v).mpr ⟨env, fuel, env', henv, hrun,
        isControlFlow_false_of_wordResult
          (.inl (by rw [and_bindConsts]; exact and_wordArrResult)) hsep henv hrun⟩)
  exact ⟨prog, sa', hd, hh, hR⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect
