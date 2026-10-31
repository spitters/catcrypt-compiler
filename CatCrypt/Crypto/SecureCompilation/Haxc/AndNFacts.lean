/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.WordResult
public import CatCrypt.Crypto.SecureCompilation.Haxc.WordResult
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame
public meta import CatCrypt.Crypto.Hax.HaxFrontTResultWords
public import CatCrypt.Crypto.Hax.HaxFrontTResultWords
public import CatCryptCore.Tactics.KatGuard

@[expose] public section

set_option autoImplicit false

/-!
# The route conditions of `mpn_and_n`

The facts of the side table and the System V layout of `mpn_and_n` (four-word arrays `rp`,
`up`, `vp` and the count `n`) on the word-array route:

* every source run from an environment the layout reads off an entry state returns an array
  of integer words (`and_wordArrResult`, from the typing of `HaxFrontTResultWords`).

## Main results

* `andAbi4`, `andAbi4_nodup` — the layout of `mpn_and_n` and the distinctness of its names.
* `envW_of_envOf`, `and_wordArrResult` — the source condition of the word-array route.

`mpn_and_n` is a kernel, linked code outside the compiler's source; this module is an
illustrative kernel instance, and a correct compiler change that breaks it removes the instance
chain rather than adapting the compiler.
-/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap encodeTy)

namespace CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState read64)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded (srcNameB
  srcName_of_srcNameB)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRoute (envOf)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteFrame (TripInv)
open CatCrypt.Crypto.SecureCompilation.Dialects.FrontRoutePlan (peelBinders)
open CatCrypt.Crypto.Hax.ResultType (WordTy andTyEnv mpn_and_n_words)
open CatCrypt.Hax.TExprTypingSpine (EnvW)
open _root_.Hax (Value Env)

/-- The System V layout of `mpn_and_n` on arrays of `4` words, with the stack words from
    `-256` to `-8` below the entry stack pointer. -/
def andAbi4 : AbiLayout where
  args := [⟨"rp", "%rdi", .words 4⟩, ⟨"up", "%rsi", .words 4⟩, ⟨"vp", "%rdx", .words 4⟩,
    ⟨"n", "%rcx", .scalar⟩]
  consts := []
  result := .words "%rdi" 4
  bounds := [("%rcx", 4)]
  frameLo := -256
  frameHi := -8

/-! ## 1. The source condition -/

theorem andAbi4_read {sa : AState} {env : Env} (henv : andAbi4.EnvOf sa env) :
    env "rp" = some (.array (wordsAt sa.mem (sa.regs "%rdi") 4)) ∧
    env "up" = some (.array (wordsAt sa.mem (sa.regs "%rsi") 4)) ∧
    env "vp" = some (.array (wordsAt sa.mem (sa.regs "%rdx") 4)) ∧
    env "n" = some (.int (sa.regs "%rcx").toNat) := by
  have h := henv.1
  refine ⟨h ⟨"rp", "%rdi", .words 4⟩ (by simp [andAbi4]), h ⟨"up", "%rsi", .words 4⟩
    (by simp [andAbi4]), h ⟨"vp", "%rdx", .words 4⟩ (by simp [andAbi4]),
    h ⟨"n", "%rcx", .scalar⟩ (by simp [andAbi4])⟩

theorem wordTy_wordsAt (sa : AState) (base : BitVec 64) :
    WordTy Mpn.ty_1 (.array (wordsAt sa.mem base 4)) :=
  .array (fun x hx => by
    simp only [wordsAt, List.mem_map, List.mem_range] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact .int rfl) (by simp [wordsAt])

/-- An environment the layout reads off an entry state is typed by `andTyEnv` under the word
    interpretation. -/
theorem envW_of_envOf {sa : AState} {env : Env} (henv : andAbi4.EnvOf sa env) :
    EnvW WordTy andTyEnv env := by
  obtain ⟨hr, hu, hv, hn⟩ := andAbi4_read henv
  intro x τ hx
  simp only [andTyEnv, CatCrypt.Hax.TExprTyping.TyEnv.extend] at hx
  split_ifs at hx with h1 h2 h3 h4
  · cases hx; rw [eq_of_beq h1]; exact ⟨_, hn, .int rfl⟩
  · cases hx; rw [eq_of_beq h2]; exact ⟨_, hv, wordTy_wordsAt sa _⟩
  · cases hx; rw [eq_of_beq h3]; exact ⟨_, hu, wordTy_wordsAt sa _⟩
  · cases hx; rw [eq_of_beq h4]; exact ⟨_, hr, wordTy_wordsAt sa _⟩

/-- **The source condition of `mpn_and_n`**: every run from an environment `andAbi4` reads off
    an entry state returns an array of integer words. -/
theorem and_wordArrResult : WordArrResult andAbi4 Mpn.mpn_and_n_texpr := by
  intro sa env fuel v env' _ henv hrun
  obtain ⟨zs, hv, -⟩ := mpn_and_n_words (envW_of_envOf henv) hrun
  exact ⟨zs, hv⟩

/-- The names of `andAbi4` are pairwise distinct. -/
theorem andAbi4_nodup : andAbi4.envNames.Nodup := by decide

end CatCrypt.Crypto.SecureCompilation.Haxc.AndNCorrect
