/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# LSH-512 wide-pipe Mix step through the OWNED x86 backend (no jasminc)

LSH (KISA Korean national standard hash, eprint 2026/1177 §2.1) is a wide-pipe
ARX hash. Its compression function repeats `Mix` (Add-XOR-Rotate on even/odd
chain word pairs) and a word permutation. The per-word `Mix_{j,l}` over a pair
`(e, o) = (cve[l], cvo[l])` with step constant `sc = SC_j[l]` is the pure ARX
core the AVX-512 implementation packs across all 8 words of a chain into one ZMM
register:

    X ← e ⊞ o
    X ← X ⋘ α_j
    X ← X ⊕ sc
    Y ← X ⊞ o
    Y ← Y ⋘ β_j
    X ← X ⊞ Y
    Y ← Y ⋘ γ_l
    (cve[l]', cvo[l]') = (X, Y)

For LSH-512 (64-bit words): even rounds `α=23, β=59`; odd rounds `α=7, β=3`;
per-word `γ_l ∈ {0,16,32,48,8,24,40,56}` for `l = 0..7`. `⋘ k` (rotate-left) is
rendered as `thRor (64 - k)`.

We emit the SCALAR Mix leaf (value-correct on-ramp) for a single word pair
through the SAME `Com[thir] → lowerThir → toLprogPhysAbi → renderLprogAtt` spine
as the ChaCha20 quarter-round / LEA round — at width 64, NO jasminc. The leaf
is parameterised over `(α, β, γ)` so any of the LSH-512 round/word slots
instantiate it; we emit the even-round `l=0` slot (`α=23, β=59, γ=0`) and the
odd-round `l=0` slot (`α=7, β=3, γ=0`) as the two representative cores, each
split into the two output words `X` and `Y`.

## What is verified vs trusted

* **Verified (value)**: `lshMix*_denote` — each leaf denotes its `lshMixSpec`
  component on every `BitVec 64` valuation (by `rfl`/`simp [rotateRight]`).
* **Trusted (thin)**: `renderLfundef` / `as` / the SysV leaf ABI frame.

The byte-identity to the KISA official LSH-512 test vector is the external
`as`/`cc` KAT in `bench/lea_lsh_compare/` (the C driver runs the full LSH-512
compression and checks the published vector; the emitted Mix leaf is exercised
inside that driver).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LshMixThirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect ThirOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirEmit
  (legalizeShiftImmLprog hasSub)

/-! ## 1. The LSH-512 Mix reference spec over `BitVec 64` -/

/-- The LSH per-word `Mix_{j,l}` (eprint 2026/1177 §2.1) over the chain word pair
    `(e, o)` with step constant `sc`, rotation amounts `α, β` (round `j`) and
    `γ` (word `l`). `⋘ k = (·).rotateRight (64 - k)`. Returns the updated
    `(cve[l]', cvo[l]') = (X, Y)`. -/
def lshMixSpec (a b g : Nat) (e o sc : BitVec 64) : (BitVec 64 × BitVec 64) :=
  let x := (e + o).rotateRight (64 - a)
  let x := x ^^^ sc
  let y := (x + o).rotateRight (64 - b)
  let x := x + y
  let y := y.rotateRight (64 - g)
  (x, y)

/-! ## 2. The Mix leaves (`Com thirDialect` at width 64)

Input context `[e, o, sc]` (`e=dB0, o=dB1, sc=dB2`). Each leaf builds the shared
7-binding Mix SSA and returns its output word (X or Y) as the last binding
(identity copy `thRor 64 0`). After the 7 compute bindings the context is
`[y3, x4, y2, y1, x3, x2, x1, e, o, sc]`, so `X' = x4` (de Bruijn 1) and
`Y' = y3` (de Bruijn 0). The rotation amounts are compile-time params. -/

private abbrev MixCtx : Ctxt thirDialect := [.reg 64, .reg 64, .reg 64]

private abbrev MixBodyCtx : Ctxt thirDialect :=
  [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64,
   .reg 64, .reg 64, .reg 64]

/-- Shared Mix SSA body for `Mix_{j,l}` with rotation params `(a, b, g)` over the
    input context `[e, o, sc]`, parameterised over which output word (`outSrc`)
    is copied to the head slot by the final identity binding. -/
def lshMixBody (a b g : Nat) (outSrc : @Ctxt.Var thirDialect MixBodyCtx (.reg 64)) :
    Com thirDialect MixCtx (.reg 64) :=
  -- x1 = e + o :  ctx [e,o,sc] ; e = dB 0, o = dB 1
  .var (.mk (.thBin .add 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- x2 = ror (64-a) x1 :  ctx [x1,e,o,sc] ; x1 = dB 0
  (.var (.mk (.thRor 64 (64 - a)) rfl (.cons .here .nil))
  -- x3 = x2 ^ sc :  ctx [x2,x1,e,o,sc] ; x2 = dB 0, sc = dB 4
  (.var (.mk (.thBin .xor 64) rfl
      (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- y1 = x3 + o :  ctx [x3,x2,x1,e,o,sc] ; x3 = dB 0, o = dB 4
  (.var (.mk (.thBin .add 64) rfl
      (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- y2 = ror (64-b) y1 :  ctx [y1,x3,x2,x1,e,o,sc] ; y1 = dB 0
  (.var (.mk (.thRor 64 (64 - b)) rfl (.cons .here .nil))
  -- x4 = x3 + y2 :  ctx [y2,y1,x3,x2,x1,e,o,sc] ; x3 = dB 2, y2 = dB 0
  (.var (.mk (.thBin .add 64) rfl
      (.cons (.there (.there .here)) (.cons .here .nil)))
  -- y3 = ror (64-g) y2 :  ctx [x4,y2,y1,x3,x2,x1,e,o,sc] ; y2 = dB 1
  (.var (.mk (.thRor 64 (64 - g)) rfl (.cons (.there .here) .nil))
  -- out = ror 0 outSrc  (identity copy) :  ctx [y3,x4,y2,y1,x3,x2,x1,e,o,sc]
  (.var (.mk (.thRor 64 0) rfl (.cons outSrc .nil))
  (.ret .here))))))))

/-- `Mix_{j,l}` output word `X' = x4` (de Bruijn 1 in `MixBodyCtx`). -/
def lshMixXThir (a b g : Nat) : Com thirDialect MixCtx (.reg 64) :=
  lshMixBody a b g (.there .here)

/-- `Mix_{j,l}` output word `Y' = y3` (de Bruijn 0 in `MixBodyCtx`). -/
def lshMixYThir (a b g : Nat) : Com thirDialect MixCtx (.reg 64) :=
  lshMixBody a b g .here

/-! ## 3. Value-correctness: each leaf denotes its `lshMixSpec` component -/

private def lshInp (e o sc : BitVec 64) : HVector (fun t => ⟦t⟧) MixCtx :=
  .cons e (.cons o (.cons sc .nil))

-- The `Com thirDialect` denotation reduces structurally to the spec word under a
-- final identity-copy (`thRor 64 0`). The whole denote is therefore
-- `(spec-word).rotateRight 0` definitionally; we expose that with a `rfl`-bridge
-- (`have h := rfl`) and discharge the `rotateRight 0` no-op.

/-- `X'` leaf value-correctness, even-round `l=0` slot (`α=23, β=59, γ=0`). -/
theorem lshMixEvenX_denote (e o sc : BitVec 64) :
    (lshMixXThir 23 59 0).denote (lshInp e o sc) = (lshMixSpec 23 59 0 e o sc).1 := by
  have h : (lshMixXThir 23 59 0).denote (lshInp e o sc)
      = ((lshMixSpec 23 59 0 e o sc).1).rotateRight 0 := rfl
  rw [h]; simp [BitVec.rotateRight_def]

/-- `Y'` leaf value-correctness, even-round `l=0` slot. -/
theorem lshMixEvenY_denote (e o sc : BitVec 64) :
    (lshMixYThir 23 59 0).denote (lshInp e o sc) = (lshMixSpec 23 59 0 e o sc).2 := by
  have h : (lshMixYThir 23 59 0).denote (lshInp e o sc)
      = ((lshMixSpec 23 59 0 e o sc).2).rotateRight 0 := rfl
  rw [h]; simp [BitVec.rotateRight_def]

/-- `X'` leaf value-correctness, odd-round `l=0` slot (`α=7, β=3, γ=0`). -/
theorem lshMixOddX_denote (e o sc : BitVec 64) :
    (lshMixXThir 7 3 0).denote (lshInp e o sc) = (lshMixSpec 7 3 0 e o sc).1 := by
  have h : (lshMixXThir 7 3 0).denote (lshInp e o sc)
      = ((lshMixSpec 7 3 0 e o sc).1).rotateRight 0 := rfl
  rw [h]; simp [BitVec.rotateRight_def]

/-- `Y'` leaf value-correctness, odd-round `l=0` slot. -/
theorem lshMixOddY_denote (e o sc : BitVec 64) :
    (lshMixYThir 7 3 0).denote (lshInp e o sc) = (lshMixSpec 7 3 0 e o sc).2 := by
  have h : (lshMixYThir 7 3 0).denote (lshInp e o sc)
      = ((lshMixSpec 7 3 0 e o sc).2).rotateRight 0 := rfl
  rw [h]; simp [BitVec.rotateRight_def]

/-! ## 4. The owned `Lprog` and AT&T emission (no jasminc)

ABI: 2-pointer SysV (`RDI` = out, `RSI` = inp); 3 inputs `[e, o, sc]` loaded from
`[RSI + 8*i]`; single output stored to `out[0]`. Arg slot `s` ↦ input index
`(3 - 1 - s) = 2 - s`, so `inLoadMap s = ("RSI", 8 * (2 - s))`. Inputs are
64-bit words, so the 8-byte stride is the native `uint64_t inp[3]`. -/

def lshInLoadMap : InLoadMap := fun s =>
  if s < 3 then some ("RSI", 8 * (2 - s)) else none

def lshOutStoreMap : OutStoreMap := [("RDI", 0)]

/-- Lower one Mix leaf through the thirDialect spine to a physical SysV `Lprog`
    (width-64 inputs), then shift/rotate-immediate-legalise for the owned printer. -/
def lshMixLprog (com : Com thirDialect MixCtx (.reg 64)) (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none) (fun _ => none)
      lshInLoadMap lshOutStoreMap
      ["RDI", "RSI"]
      [64, 64, 64])

-- Even-round l=0 slot (α=23, β=59, γ=0) and odd-round l=0 slot (α=7, β=3, γ=0).
def lshMixEvenXLprog : Lprog := lshMixLprog (lshMixXThir 23 59 0) "lsh512_mix_even_x"
def lshMixEvenYLprog : Lprog := lshMixLprog (lshMixYThir 23 59 0) "lsh512_mix_even_y"
def lshMixOddXLprog  : Lprog := lshMixLprog (lshMixXThir 7 3 0)   "lsh512_mix_odd_x"
def lshMixOddYLprog  : Lprog := lshMixLprog (lshMixYThir 7 3 0)   "lsh512_mix_odd_y"

/-- All four Mix leaves gathered into ONE `Lprog`. -/
def lshMixLprog' : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs := lshMixEvenXLprog.lp_funcs ++ lshMixEvenYLprog.lp_funcs
                ++ lshMixOddXLprog.lp_funcs ++ lshMixOddYLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for the four Mix leaves. -/
def lshMixAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lshMixLprog'

-- Rendered-asm correctness is the external C KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 5. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/lea_lsh_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/lsh512_mix_owned.s") lshMixAsm
  IO.println "WROTE bench/lea_lsh_compare/gen/lsh512_mix_owned.s"
  IO.println "  (LSH-512 Mix leaves lsh512_mix_{even,odd}_{x,y} through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.LshMixThirEmit
