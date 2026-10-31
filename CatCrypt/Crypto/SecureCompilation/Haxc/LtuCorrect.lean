/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LtuFacts
public import CatCrypt.Crypto.SecureCompilation.Haxc.LtuFacts
public meta import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public import CatCrypt.Crypto.Mpn.Extraction.Mpn_haxpipe
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The compiler on the straight-line program `ltu`

`ltu` (from `mpn-hax`) is the branch-free unsigned comparison of two words `x` and `y`, with
the constant `ONES` (all bits set) and a scalar result; `ltuAbi` is its System V layout and
`ltuK` the extraction with `ONES` bound (`LtuFacts`). `compileA` compiles `ltu` by the
region back half, with `ONES` bound at the head of the entry.

`ltu` is a kernel, linked code outside the compiler's source; this module is an illustrative
instance of the general theorem, and a correct compiler change that breaks it removes the
instance chain rather than adapting the compiler.

## Main results

* `ltu_correct_auto` — the general compiler theorem at `ltu`, from the compilation, the entry
  conditions of `ltuAbi`, an environment `ltuAbi` reads off the entry state, and the source run.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.Hax (hax64WExit)
open _root_.Hax (Value Env)
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-- **The general compiler theorem at `ltu` with no witness.** For the result of `compileA` on
    `ltu` under `ltuAbi`: from every entry state satisfying `ltuAbi.Regions` and every hax
    environment `ltuAbi` reads off it, every run of the source reading to a value `v` is matched
    by a halting run of the machine on the decoded bytes from which `ltuAbi` reads back `v`. -/
theorem ltu_correct_auto (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA Mpn.ltu_texpr ltuAbi "ltu" = some (P, bytes))
    (sa : AState) (hsep : ltuAbi.Regions sa) (env : Env) (henv : ltuAbi.EnvOf sa env)
    (fuel : Nat) (v : Value) (env' : Env)
    (hrun : (denoteSpine hax64WExit fuel Mpn.ltu_texpr.erase).run env = (.val v, env')) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ ltuAbi.ResultOf sa sa' v := by
  obtain ⟨prog, sa', hd, hh, hR, -⟩ :=
    haxEntry.compileR_correct (Mpn.ltu_texpr : CatCrypt.Crypto.Hax.HaxModule) ltuAbi "ltu" P
      bytes ((linkedNil_compileA_eq (m := Mpn.ltu_texpr) rfl _ _).symm.trans hc) sa hsep v
      ((haxRuns_single ltuAbi Mpn.ltu_texpr sa v).mpr ⟨env, fuel, env', henv, hrun,
        isControlFlow_false_of_wordResult (.inr ltu_wordScalResult) hsep henv hrun⟩)
  exact ⟨prog, sa', hd, hh, hR⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.LtuCorrect
