/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote

/-!
# ML-DSA `ExpandA` (`rej_uniform`) rejection sampler as a data-dependent `RWhileNz` whole-program denote

ML-DSA-65's matrix expansion (`ExpandA`, PQClean `ml-dsa-65/clean` `poly.c`
`rej_uniform`) rejection-samples uniform-mod-`q` coefficients from a SHAKE128 XOF
stream: read a 23-bit candidate `t = (b0 | b1<<8 | b2<<16) & 0x7FFFFF` from the
3-byte window, accept it iff `< q = 8380417`, advance the byte cursor `pos += 3`,
and repeat until the output polynomial is full. The number of windows is
decided at run time by how many candidates land below `q`, so this is a
data-dependent loop, the `while (name != 0)` shape `RWhileNz` models.

The loop is stated as a `LowCT` term and descended through the unified front
`transU` of `TranslateDialectUnifiedDenote`, whose whole-program denote
`transU_denote` relates the emitted `Com` prefix to the unified waist `semU`. It
is the ML-DSA twin of `MLKEM.RejUniformCovered` (ML-DSA reads a 23-bit candidate
from a 3-byte window, ML-KEM a 12-bit candidate). The owned byte-exact
counterpart is `MLDSA.SamplerEmit` (`rejUniWindowBody` / `uniGuard`).

## The source term

One window is `if lt { store } ; advance ; extract ; compare`: the store runs
only when the public accept flag `lt = (cand < q)` is set, and every window
advances the cursor and reads the next candidate. The conditional is the guarded
block `RIfNz "lt" acceptStore RSkip`, which `semU` models by `semScalarCond` (the
block runs iff the guard is nonzero) and `transU` descends by `condSkipD`. The
whole is wrapped in `RWhileNz "remaining"`, the buffer-not-full guard.

* `rej_extract_cand` — opaque leaf: extract the next 23-bit candidate from
  the (public) SHAKE128 byte stream at the cursor.
* `rej_lt_q` — opaque leaf: the public `< q` comparison, producing the accept flag.
* `rej_store` — opaque leaf: store an accepted coefficient into the output.
* `rej_advance` — opaque leaf: advance the byte cursor (`pos += 3`).

The candidate stream and the arithmetic are opaque leaves (their FIPS-204
correctness is the byte-KAT obligation of the owned-emit kernel
`MLDSA.SamplerEmit`); the statement here is about the rejection control
structure.

`transU` selects its descent by the run's guard values and trip count, so the
emitted `Com` of `transU_denote` is the unrolling of one run. The static fact
`rejUniform_front_fires` states that both legs of one window front-compile
through `translateDialectControl`: the taken leg (store, then the tail from the
post-store map) and the skipped leg (the tail from the entry map).

## CT note — the guard and the branch are public

`ExpandA` expands the matrix `A` from the public seed `ρ`, so the XOF stream,
every `cand < q` decision, and the buffer-full guard are public (FIPS-204
§Algorithm 7). The `RWhileNz` guard `remaining` and the `RIfNz` flag `lt` depend
only on public data. `ExpandS`'s `rej_eta`, which expands the secret vectors, is a
different sampler and is not stated here. The buffer index is a public counter.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.SamplerCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 1. The source: `rej_uniform` as a data-dependent `while` -/

/-- The (public) SHAKE128 XOF byte-stream / output bundle tower type — a byte
    buffer (rate-168 SHAKE128 block, ML-DSA `ExpandA`). -/
def bundleTy : TowerType := .TBytes 168

/-- A located byte-bundle slot (`buf`, `out`, `cand`). -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- A located 64-bit scalar slot (`pos` cursor, `lt` accept flag). -/
def locS (n : String) : Located := { locVar := n, locSrc := .TU64 }

/-- Advance the byte cursor (`pos += 3`) and read the next 23-bit candidate,
    recomputing the public accept flag `lt = (cand < q)`. Straight-line
    (`IsCoveredS`): an `RSeq` of the advance, extract, and compare leaves. -/
def rejAdvanceExtract : LowCT :=
  .RSeq (.RCall "rej_advance" (locS "pos") [locS "pos"])
    (.RSeq (.RCall "rej_extract_cand" (loc "cand") [loc "buf", locS "pos"])
           (.RCall "rej_lt_q" (locS "lt") [loc "cand"]))

/-- Store the accepted coefficient into the output. -/
def acceptStore : LowCT :=
  .RCall "rej_store" (loc "out") [loc "out", loc "cand"]

/-- The `rej_uniform` window body: store when the public accept flag `lt` is set,
    then advance and read the next candidate. -/
def rejBody : LowCT :=
  .RSeq (.RIfNz "lt" acceptStore .RSkip) rejAdvanceExtract

/-- The whole `ExpandA` rejection sampler: iterate the window body while the
    output polynomial is not full (`remaining != 0`). -/
def rejUniformLowCT : LowCT :=
  .RWhileNz "remaining" rejBody

/-! ## 2. Coverage -/

/-- The advance-and-extract tail is straight-line covered. -/
theorem rejAdvanceExtract_coveredS : IsCoveredS rejAdvanceExtract :=
  .rSeq (.rCall "rej_advance" (locS "pos") [locS "pos"])
    (.rSeq (.rCall "rej_extract_cand" (loc "cand") [loc "buf", locS "pos"])
           (.rCall "rej_lt_q" (locS "lt") [loc "cand"]))

/-- The store is straight-line covered. -/
theorem acceptStore_coveredS : IsCoveredS acceptStore :=
  .rCall "rej_store" (loc "out") [loc "out", loc "cand"]

/-- The window body is in the unified fragment: a guarded block sequenced with
    the straight-line tail. -/
theorem rejBody_coveredU : IsCoveredSU rejBody :=
  .rSeq (.rCond (.ofCtl (.ofStraight acceptStore_coveredS) rfl))
    (.rSeq (.ofCtl (.ofStraight (.rCall "rej_advance" (locS "pos") [locS "pos"])) rfl)
      (.rSeq
        (.ofCtl (.ofStraight (.rCall "rej_extract_cand" (loc "cand") [loc "buf", locS "pos"]))
          rfl)
        (.ofCtl (.ofStraight (.rCall "rej_lt_q" (locS "lt") [loc "cand"])) rfl)))

/-- The whole rejection sampler is in the unified fragment. -/
theorem rejUniform_coveredU : IsCoveredSU rejUniformLowCT :=
  .rWhile rejBody_coveredU

/-! ## 3. Concrete argument context — the window legs front-compile -/

/-- The argument context: the byte bundles `buf`/`out`/`cand` and the 64-bit
    scalars `pos` (cursor), `lt` (accept flag), `remaining` (buffer-not-full
    guard). -/
def rejArgVM :=
  ((((((VarMap.empty.bind (t := encodeTy bundleTy) "buf").bind
      (t := encodeTy bundleTy) "out").bind
      (t := encodeTy bundleTy) "cand").bind
      (t := .sword 64) "pos").bind
      (t := .sword 64) "lt").bind
      (t := .sword 64) "remaining")

/-- Both legs of one window front-compile through `translateDialectControl`: the
    taken leg (the store, then the tail from the post-store map) and the skipped
    leg (the tail from the entry map). These are the translations `transU`
    composes per trip. -/
theorem rejUniform_front_fires :
    (match translateDialectControl rejArgVM acceptStore with
      | some o => (translateDialectControl o.vm rejAdvanceExtract).isSome
      | none => false) = true ∧
      (translateDialectControl rejArgVM rejAdvanceExtract).isSome := by
  native_decide

/-! ## 4. The whole-program denote -/

/-- **Whole-program denote of the ML-DSA `ExpandA` rejection sampler.** For any
    context/valuation/env consistent triple on which the unified descent succeeds
    and the unified waist `semU` halts within `fuel`, the descended dialect-`Com`
    prefix denotes the waist run: the store fires on the windows whose accept
    flag is set, and every window advances. The instance of `transU_denote` at
    `rejUniform_coveredU`. -/
theorem rejUniformCovered_denote (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : transU fuel vm env rejUniformLowCT = some o)
    (hrun : semU fuel rejUniformLowCT env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  transU_denote fuel rejUniform_coveredU vm V env env' o hc htr hrun

/-! ## 5. Axiom audit -/

#print axioms rejUniform_coveredU
#print axioms rejUniform_front_fires
#print axioms rejUniformCovered_denote

end CatCrypt.Crypto.MLDSA.SamplerCovered
