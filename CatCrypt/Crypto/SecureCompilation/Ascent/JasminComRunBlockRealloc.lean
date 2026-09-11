/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.JasminComRunBlockSeq

/-!
# Extending the ascent keystone toward a general D: register reuse + a non-arith op

`JasminComRunBlockSeq.lowerBlock_tie` ties a straight-line scalar-arithmetic block
(`Com jasminDialect` ↔ `runBlock`) under a **fresh** register allocation. This
module widens that keystone two ways toward the general `Com jasminDialect ↔
JState` correspondence D:

1. **The register-reuse leg** (`lowerBlock_tie_realloc`). The keystone lowers with
   a fresh (injective, range-disjoint) allocation; a real allocator then *reuses*
   physical registers via a renaming `ρr`. Composing the keystone with
   `Optimizer.RandomizedRegAlloc.regalloc_runBlock_sound` (the `StateRel`
   renaming-soundness theorem) lifts the tie from the fresh allocation to the
   renamed one: reading the *renamed* output register after `runBlock` of the
   renamed lowered block still equals the block's `Com` denotation.

2. **One non-arithmetic op** (`mulhi`, the `MULX` high word). The six scalar-arith
   arms of `ArithBlock` all denote a plain `BitVec 64` ALU op; `mulhi` denotes the
   widening-multiply high word (`mulHiW`), lowered to the two-write machine `MULX`
   whose `dstHi` read carries it. Its single-op tie (`mulhiOp_runBlock_tie`) is the
   `jasminOp_runBlock_tie` analogue. `RegBlock` then folds the arith and mulhi arms
   into one straight-line block type and `lowerBlockR_tie` re-proves the keystone
   over it — a block that covers more than the scalar-arith fragment.

## What is proved

* `lowerBlock_tie_realloc` — the reuse leg: composition of `lowerBlock_tie` with
  `regalloc_runBlock_sound`, transported through `StateRel`'s register-agreement
  projection to move the `.get` across the rename.
* `lowerMulHi_get_dstHi` / `lowerMulHi_get_other` — the per-op mulhi value
  agreement (the `dstHi` read equals `mulHiW`) and its frame (only `dstHi`/`dstLo`
  are written).
* `mulhiOp_runBlock_tie` — the single-op `Com ↔ runBlock` tie for `mulhi`.
* `RegBlock` / `lowerBlockR` / `outRegR` / `RegBlock.toCom` — the combined
  straight-line block over arith + mulhi arms.
* `lowerBlockR_tie` — the keystone re-proved over the combined block: the mulhi
  arm consumes two fresh registers (`dstHi = g 0`, scratch `dstLo = g 1`) and the
  fresh invariant is preserved by `FreshFor_extend2`.

Both sides of every tie are genuine — a real machine register read after a real
`runBlock`, and a real `Com jasminDialect` denotation (`bop.apply` / `mulHiW`
folds), never `default`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-! ## 1. The register-reuse leg

The keystone `lowerBlock_tie` reads the fresh-allocation output register. A real
allocator reuses physical registers, applying a renaming `ρr` (injective on the
live set, with left inverse `σr`). `regalloc_runBlock_sound` certifies that the
renamed run's register `ρr n` agrees with the original run's register `n`; taking
`n` to be the keystone's output register moves the tie onto the reused allocation. -/

/-- **The reuse leg.** Lower the block with a fresh allocation (`lowerBlock`), then
    apply a register renaming `ρr` (injective, left inverse `σr`) — a register
    *reuse*. Reading the renamed output register `ρr (outReg …)` after `runBlock`
    of the renamed block from the `σr`-renamed initial state still equals the
    block's `Com jasminDialect` denotation. This composes the fresh-allocation
    keystone (`lowerBlock_tie`) with the renaming-soundness theorem
    (`regalloc_runBlock_sound`), transported through `StateRel`'s register
    agreement (`ρr n` of the renamed run = `n` of the original run). -/
theorem lowerBlock_tie_realloc {Γ : Ctxt jasminDialect} (block : ArithBlock Γ)
    (ρ : RegMapG Γ) (g : Nat → String) (s : JState 64) (V : Ctxt.Valuation Γ)
    (hinterp : JStateInterpG ρ V s) (hfresh : FreshFor ρ g)
    (ρr σr : String → String) (hρr : Function.Injective ρr)
    (hσr : Function.LeftInverse σr ρr) :
    (runBlock (renameState σr s) (renameBlock ρr (lowerBlock block ρ g))).get
        (ρr (outReg block ρ g))
      = block.toCom.denote V := by
  have hrel := regalloc_runBlock_sound hρr hσr (lowerBlock block ρ g) s
  have hbase := lowerBlock_tie block ρ g s V hinterp hfresh
  have hreg := hrel.regs (outReg block ρ g)
  simp only [JState.get] at hbase ⊢
  rw [hreg]; exact hbase

/-! ## 2. The `mulhi` op: single-instruction lowering and value agreement

`mulhi` is the widening-multiply high word — the `hi` output of x86 `MULX`. It is
not a plain ALU op (unlike `add/sub/and/or/xor/mul`), so it exercises a genuinely
different arm. The machine `MULX` writes both outputs `(lo, hi)`; reading `dstHi`
recovers `mulHiW`. -/

/-- **The mulhi machine lowering.** A single `MULX dstHi dstLo, a, b`: the widening
    multiply writing the low word to the scratch `dstLo` and the high word to
    `dstHi`. Register-only (no memory), so trivially in the machine constant-time
    class. -/
def lowerMulHi (ra rb dstHi dstLo : String) : List (JInstr 64) :=
  [ .mulx dstHi dstLo (.reg ra) (.reg rb) ]

/-- **Per-op value agreement (mulhi).** Running the lowered `MULX` and reading
    `dstHi` yields `mulHiW (s.get ra) (s.get rb)` — the same `BitVec 64` high word
    the dialect's `mulhi 64` op denotes. No side condition on `dstHi`/`dstLo`: the
    `hi` write is the outermost, so the read recovers it regardless of aliasing. -/
theorem lowerMulHi_get_dstHi (ra rb dstHi dstLo : String) (s : JState 64) :
    (runBlock s (lowerMulHi ra rb dstHi dstLo)).get dstHi
      = mulHiW (s.get ra) (s.get rb) := by
  simp only [lowerMulHi, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MULX_lo_hi, wumul, JState.setReg, JState.get, mulHiW, high_bits, if_true]

/-- **Per-op frame (mulhi).** The lowered `MULX` writes only `dstHi` and `dstLo`;
    reading any other register `r` (distinct from both) falls through unchanged. -/
theorem lowerMulHi_get_other (ra rb dstHi dstLo r : String)
    (hHi : r ≠ dstHi) (hLo : r ≠ dstLo) (s : JState 64) :
    (runBlock s (lowerMulHi ra rb dstHi dstLo)).get r = s.get r := by
  simp only [lowerMulHi, runBlock_cons, runBlock_nil, evalInstr, JOperand.eval,
    x86_MULX_lo_hi, wumul, JState.setReg, JState.get, if_neg hHi, if_neg hLo]

/-! ## 3. The single-op `mulhi` tie -/

/-- The single-op `mulhi 64` program `let s = mulhi a b in ret s : Com jasminDialect`
    over `[reg 64, reg 64]`, built like `jasminSingleOp` but with the `mulhi` op. -/
def mulhiSingleOp : Com jasminDialect Γ2 (.reg 64) :=
  .var (.mk (.mulhi 64) rfl (.cons vA (.cons vB .nil))) (.ret .here)

/-- The dialect side: the single-op `mulhi` `Com` denotes to
    `mulHiW (V a) (V b)`, a genuine widening-multiply high word read from `V`. -/
theorem mulhiSingleOp_denote (V : Ctxt.Valuation Γ2) :
    mulhiSingleOp.denote V = mulHiW (vA.lookup V) (vB.lookup V) := rfl

/-- **The single-op mulhi `.denote ↔ runBlock` tie.** Under the state
    correspondence `JStateInterp ρ V s`, reading `dstHi` after running the lowered
    `MULX` equals the `mulhi` `Com`'s denotation on `V`. The non-arith analogue of
    `jasminOp_runBlock_tie`: both sides are `mulHiW (V a) (V b)`. -/
theorem mulhiOp_runBlock_tie (ρ : RegMap) (dstHi dstLo : String) (s : JState 64)
    (V : Ctxt.Valuation Γ2) (hinterp : JStateInterp ρ V s) :
    (runBlock s (lowerMulHi (ρ vA) (ρ vB) dstHi dstLo)).get dstHi
      = mulhiSingleOp.denote V := by
  rw [mulhiSingleOp_denote, lowerMulHi_get_dstHi, hinterp vA, hinterp vB]

/-! ## 4. Non-vacuity of the mulhi machine side

A concrete `MULX` whose high word is nonzero: `2^32 · 2^33 = 2^65`, high word `2`
— a real machine run, not a `default`/zero collapse. -/

/-- Concrete machine state with `"a" = 2^32`, `"b" = 2^33`. -/
def mulhiSampleS : JState 64 :=
  { regs := fun r => if r = "a" then (BitVec.ofNat 64 (2 ^ 32)) else
                     if r = "b" then (BitVec.ofNat 64 (2 ^ 33)) else 0 }

/-- The machine `MULX` high-word read is the genuine value `2` (`2^65 / 2^64`). -/
example :
    (runBlock mulhiSampleS (lowerMulHi "a" "b" "hi" "lo")).get "hi"
      = (2 : BitVec 64) := by
  rw [lowerMulHi_get_dstHi]; decide

/-! ## 5. Folding mulhi into the block induction

`RegBlock` is the covered straight-line block over both the scalar-arith arms and
the mulhi arm — all two-input, single-`reg 64`-output ops binding a fresh slot.
The keystone re-proves over it (`lowerBlockR_tie`). The mulhi arm consumes **two**
fresh registers: `dstHi = g 0` (the SSA slot) and a scratch `dstLo = g 1` (dead —
never in the register map's range), so the recursion shifts the fresh stream by
two and `FreshFor` is preserved by `FreshFor_extend2`. -/

/-- **The covered straight-line block over arith + mulhi.** A chain of two-input,
    single-`reg 64`-output ops — the scalar-arith arms (`arith`) and the widening
    high-word arm (`mulhi`) — each binding a fresh slot, terminated by returning a
    variable. Strictly widens `ArithBlock` (which lacks the `mulhi` arm). -/
inductive RegBlock : Ctxt jasminDialect → Type where
  /-- Return one `reg 64` variable — the block's output. -/
  | ret {Γ : Ctxt jasminDialect} (v : Ctxt.Var Γ (.reg 64)) : RegBlock Γ
  /-- One scalar op `d := a ⟨bop⟩ b`, binding a fresh slot, then continue. -/
  | arith {Γ : Ctxt jasminDialect} (bop : JasminBinOp) (hbop : IsScalarBop bop)
      (a b : Ctxt.Var Γ (.reg 64)) (rest : RegBlock (.reg 64 :: Γ)) : RegBlock Γ
  /-- One high-word op `d := mulhi a b` (the `MULX` `hi`), binding a fresh slot. -/
  | mulhi {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
      (rest : RegBlock (.reg 64 :: Γ)) : RegBlock Γ

/-- The `mulhi 64` expression on two `reg 64` variables, at width 64. -/
def mulhiExpr {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64)) :
    Expr jasminDialect Γ (.reg 64) :=
  .mk (.mulhi 64) rfl (.cons a (.cons b .nil))

/-- The `mulhi` expression denotes to `mulHiW (a.lookup V) (b.lookup V)` — a genuine
    widening-multiply high word from the valuation. -/
theorem mulhiExpr_denote {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg 64))
    (V : Ctxt.Valuation Γ) :
    (mulhiExpr a b).denote V = mulHiW (a.lookup V) (b.lookup V) := rfl

/-- **Compile a `RegBlock` to a genuine `Com jasminDialect`.** `.arith` binds
    `arithExpr`; `.mulhi` binds `mulhiExpr`; `.ret` is `Com.ret`. -/
def RegBlock.toCom : {Γ : Ctxt jasminDialect} → RegBlock Γ →
    Com jasminDialect Γ (.reg 64)
  | _, .ret v => .ret v
  | _, .arith bop _ a b rest => .var (arithExpr bop a b) rest.toCom
  | _, .mulhi a b rest => .var (mulhiExpr a b) rest.toCom

/-- The fresh invariant is preserved after consuming **two** fresh names (the mulhi
    arm's `dstHi = g 0` and scratch `dstLo = g 1`): the twice-shifted stream stays
    injective and disjoint from the extended register map's range. -/
theorem FreshFor_extend2 {Γ : Ctxt jasminDialect} (ρ : RegMapG Γ) (g : Nat → String)
    (hfresh : FreshFor ρ g) :
    FreshFor (ρ.extend (g 0)) (fun k => g (k + 2)) := by
  obtain ⟨hinj, hdisj⟩ := hfresh
  refine ⟨fun i j hij => hinj (i + 2) (j + 2) (by omega), ?_⟩
  intro i v
  match v with
  | .here => exact hinj (i + 2) 0 (by omega)
  | .there w0 => exact hdisj (i + 2) w0

/-- **The combined block lowering.** Each `arith` op consumes one fresh register
    (`g 0`); each `mulhi` op consumes two (`dstHi = g 0`, scratch `dstLo = g 1`),
    shifting the stream accordingly. The `.ret` emits nothing. -/
def lowerBlockR : {Γ : Ctxt jasminDialect} → RegBlock Γ → RegMapG Γ →
    (Nat → String) → List (JInstr 64)
  | _, .ret _, _, _ => []
  | _, .arith bop _ a b rest, ρ, g =>
      lowerArith2 bop (ρ a) (ρ b) (g 0)
        ++ lowerBlockR rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .mulhi a b rest, ρ, g =>
      lowerMulHi (ρ a) (ρ b) (g 0) (g 1)
        ++ lowerBlockR rest (ρ.extend (g 0)) (fun k => g (k + 2))

/-- The combined block's output register (the register of the returned variable
    under the accumulated register map). -/
def outRegR : {Γ : Ctxt jasminDialect} → RegBlock Γ → RegMapG Γ →
    (Nat → String) → String
  | _, .ret v, ρ, _ => ρ v
  | _, .arith _ _ _ _ rest, ρ, g =>
      outRegR rest (ρ.extend (g 0)) (fun k => g (k + 1))
  | _, .mulhi _ _ rest, ρ, g =>
      outRegR rest (ρ.extend (g 0)) (fun k => g (k + 2))

/-- **The keystone re-proved over the combined arith + mulhi block.** For every
    straight-line `RegBlock`, under the state correspondence `JStateInterpG ρ V s`
    and a fresh allocation `FreshFor ρ g`, reading the block's output register
    after `runBlock` of the whole lowered block equals the multi-op `Com
    jasminDialect` denotation on `V`. Structural induction composing the two
    single-op ties (`lowerArith2_get_dst`, `lowerMulHi_get_dstHi`) with their
    frames (`lowerArith2_get_other`, `lowerMulHi_get_other`); the mulhi arm's two
    fresh registers are handled by `FreshFor_extend2`. -/
theorem lowerBlockR_tie : {Γ : Ctxt jasminDialect} → (block : RegBlock Γ) →
    (ρ : RegMapG Γ) → (g : Nat → String) → (s : JState 64) →
    (V : Ctxt.Valuation Γ) → JStateInterpG ρ V s → FreshFor ρ g →
    (runBlock s (lowerBlockR block ρ g)).get (outRegR block ρ g)
      = block.toCom.denote V
  | _, .ret v, ρ, g, s, V, hinterp, _ => by
      simp only [lowerBlockR, outRegR, runBlock_nil, RegBlock.toCom, Com.denote]
      exact hinterp v
  | _, .arith bop hbop a b rest, ρ, g, s, V, hinterp, hfresh => by
      have hdisj := hfresh.2 0
      have hinterp' : JStateInterpG (ρ.extend (g 0))
          (V.extend ((arithExpr bop a b).denote V))
          (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))) := by
        intro w
        match w with
        | .here =>
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (g 0)
                = bop.apply (a.lookup V) (b.lookup V)
            rw [lowerArith2_get_dst bop hbop (ρ a) (ρ b) (g 0) (hdisj b) s,
              hinterp a, hinterp b]
        | .there w0 =>
            show (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0))).get (ρ w0)
                = w0.lookup V
            rw [lowerArith2_get_other bop hbop (ρ a) (ρ b) (g 0) (ρ w0)
              (fun h => (hdisj w0) h.symm) s]
            exact hinterp w0
      have hfresh' : FreshFor (ρ.extend (g 0)) (fun k => g (k + 1)) :=
        FreshFor_extend ρ g hfresh
      have key := lowerBlockR_tie rest (ρ.extend (g 0)) (fun k => g (k + 1))
        (runBlock s (lowerArith2 bop (ρ a) (ρ b) (g 0)))
        (V.extend ((arithExpr bop a b).denote V)) hinterp' hfresh'
      simpa only [lowerBlockR, outRegR, RegBlock.toCom, Com.denote, runBlock_append]
        using key
  | _, .mulhi a b rest, ρ, g, s, V, hinterp, hfresh => by
      have hdisj := hfresh.2
      have hinterp' : JStateInterpG (ρ.extend (g 0))
          (V.extend ((mulhiExpr a b).denote V))
          (runBlock s (lowerMulHi (ρ a) (ρ b) (g 0) (g 1))) := by
        intro w
        match w with
        | .here =>
            show (runBlock s (lowerMulHi (ρ a) (ρ b) (g 0) (g 1))).get (g 0)
                = mulHiW (a.lookup V) (b.lookup V)
            rw [lowerMulHi_get_dstHi (ρ a) (ρ b) (g 0) (g 1) s, hinterp a, hinterp b]
        | .there w0 =>
            show (runBlock s (lowerMulHi (ρ a) (ρ b) (g 0) (g 1))).get (ρ w0)
                = w0.lookup V
            rw [lowerMulHi_get_other (ρ a) (ρ b) (g 0) (g 1) (ρ w0)
              (fun h => (hdisj 0 w0) h.symm) (fun h => (hdisj 1 w0) h.symm) s]
            exact hinterp w0
      have hfresh' : FreshFor (ρ.extend (g 0)) (fun k => g (k + 2)) :=
        FreshFor_extend2 ρ g hfresh
      have key := lowerBlockR_tie rest (ρ.extend (g 0)) (fun k => g (k + 2))
        (runBlock s (lowerMulHi (ρ a) (ρ b) (g 0) (g 1)))
        (V.extend ((mulhiExpr a b).denote V)) hinterp' hfresh'
      simpa only [lowerBlockR, outRegR, RegBlock.toCom, Com.denote, runBlock_append]
        using key

/-! ## 6. Non-vacuity of the combined block

A concrete 2-op block exercising **both** arms: `s1 := a + b ; s2 := mulhi s1 a ;
ret s2`. The denotation is a real `mulHiW ∘ add` composition (symbolic `rfl`, not a
concrete-value KAT), so neither side collapses to `default`. -/

/-- A combined 2-op block over `Δ2`: `s1 := a + b ; s2 := mulhi s1 a ; ret s2`. -/
def blockAM : RegBlock Δ2 :=
  .arith .add trivial dA dB
    (.mulhi (.here) (.there .here)
      (.ret .here))

/-- The combined block denotes to `mulHiW (a + b) a` over the valuation — a genuine
    composition of `JasminBinOp.add.apply` and `mulHiW`, not `default`. -/
theorem blockAM_denote (V : Ctxt.Valuation Δ2) :
    blockAM.toCom.denote V
      = mulHiW (JasminBinOp.add.apply (dA.lookup V) (dB.lookup V)) (dA.lookup V) := by
  rfl

/-- **The combined keystone on the 2-op block.** The machine `runBlock` of the whole
    lowered block reads exactly `mulHiW (a + b) a` — the composed dialect
    denotation over both arms. -/
theorem blockAM_tie (ρ : RegMapG Δ2) (g : Nat → String) (s : JState 64)
    (V : Ctxt.Valuation Δ2) (hinterp : JStateInterpG ρ V s) (hfresh : FreshFor ρ g) :
    (runBlock s (lowerBlockR blockAM ρ g)).get (outRegR blockAM ρ g)
      = mulHiW (JasminBinOp.add.apply (dA.lookup V) (dB.lookup V)) (dA.lookup V) := by
  rw [lowerBlockR_tie blockAM ρ g s V hinterp hfresh, blockAM_denote]

end CatCrypt.Crypto.SecureCompilation.Ascent
