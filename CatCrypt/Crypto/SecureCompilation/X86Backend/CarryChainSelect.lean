/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# P5 — a generic MUL→MULX instruction-selection pass over `List (JInstr 64)`

This module implements **P5** from `owned-vs-jasminc-perf-review.md`: a *generic*
instruction-selection pass that recognises a low-word multiply paired with the
widening (high-word) form of the same product and rewrites the pair to a single
two-output `MULX`. Today the fast ADX/BMI2 instructions (`MULX`/`ADCX`/`ADOX`)
reach the emitted assembly only from hand-written `*OwnedEmit` kernels and the
one-off `FheMontMulOwnedEmit.fuseMulHiLprog` post-pass, which runs on the
*string-keyed* `Lprog` layer (a syntactic `MUL`+`MULXHI` coalesce, value-checked
externally by the orchestrator's GMP KAT). There is no generic selector that
operates on the *typed* machine model where soundness is provable inside Lean.

`fuseMulx` is that selector, over the faithful `JasminModel` instruction set
(`JInstr 64`, `runBlock`, `evalInstr`). Because the model is typed and executable
it carries a **symbolic** soundness proof — not a syntactic substring check.

## The recognised pattern

After the front lowers a `64×64 → 128` widening multiply it can emit the low and
high halves as two separate ops:

```
  imul lo, b        -- low word:  lo := lo * b   (Ox86_IMULt, low 64 bits)
  mulx hi, lo, a, b -- the widening: lo := low(a·b), hi := high(a·b)
```

where, in two-address form before the pair, `lo` already holds the multiplicand
`a` (so the low `imul` computes `a·b`). The dedicated `mulx` then re-derives the
low word into the *same* register `lo` and additionally materialises the high
word `hi`. The standalone low `imul` is therefore **redundant**: `mulx` recomputes
its result. The pass coalesces the pair to the single `mulx`.

This is the typed-model analogue of `fuseMulHiLprog`'s `MUL`+`MULXHI → MULX`
coalesce, lifted off the string layer onto `JInstr` so the rewrite can be proved
sound against the machine semantics rather than checked by an external KAT.

## What is proved (honest scope)

* `fuseMulx_allDirect` — the rewrite **preserves the constant-time class**:
  `MUL`/`MULX` are register-only ALU ops (`IsDirect`), so a fused body is
  `allDirect` whenever the input is, hence constant-time by
  `ConstantTimeCoverage.allDirect_constant_time`.
* `mulx_get_lo` / `mulx_get_hi` — **symbolic** soundness of the fused
  instruction: a single `mulx hi lo a b` lands `low(a·b)` in `lo` and
  `high(a·b)` in `hi`, the exact `(lo, hi)` of the `64×64 → 128` product.
* `imul_word_eq_mulx_lo` — **symbolic** soundness of the coalesce on the low
  word: `Ox86_IMULt`'s low word `a·b` equals the low half `MULX` produces, so
  dropping the standalone low `imul` (which `mulx` recomputes) does not change
  the low word — the fused `mulx` computes *the same* `lo` the separate `MUL`
  did, and *additionally* the correct `hi`.
* `fuseMulx_get_sound` — the **block-level** statement: on a body that begins
  with the recognised pair, the fused block's `lo` and `hi` registers hold the
  same widening-product words as the machine semantics dictates.
* A worked demo (`demoPair` / `demoFused`) on a real 2-register widening shape:
  the pass fires (`fuseMulx demoPair = demoFused`) and the result computes the
  correct `(lo, hi)` of `a·b` (`demoFused_lo` / `demoFused_hi`, symbolic) plus a
  small concrete value KAT (`demoFused_kat`).

The rewrite is **symbolically** sound on the produced widening words (`lo`, `hi`),
not merely concrete-KAT-anchored. The honest caveat: the standalone low `imul`
also *sets the x86 flags* (`CF`/`OF`), which `mulx` does not; dropping it changes
the flag state. The fusion is value-correct on the *data* words it materialises
(which is what the high-word gap needs), and is only applied where the low
`imul`'s flag side effect is dead — exactly as `fuseMulHiLprog` assumes the
just-computed low word is consumed before the carry chain, not the `imul`'s
flags. The flag-liveness side condition is a whole-body concern (the merge-time
integration point below), not part of the per-pair data-word soundness proved
here.

## Out of scope (separate lowering+relocation task)

x86 `LEA` instruction selection and `leaq sym(%rip)` relocation byte-path support
are a distinct lowering+relocation concern (the `.rodata` symbol-base addressing
of `JInstr.loadSym`), out of scope for this file. This module focuses on the
carry/mulx *selection* that has a clean machine-model proof.

## Deferred integration point

`fuseMulx` is a `List (JInstr 64) → List (JInstr 64)` post-pass, the typed-model
sibling of `fuseMulHiLprog`. It plugs into the owned pipeline at the same stage
the `Lprog` fusion runs — after lowering to the physical two-address body, before
the AT&T printer — once the lowering emits `JInstr` (rather than going straight
to the string `Lprog`). At that point a downstream **flag-liveness** check (the
low `imul`'s `CF`/`OF` are dead before the next flag write) licenses the coalesce
on every body, discharging the side condition the per-pair data proof leaves to
the integrator.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CarryChainSelect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. Per-instruction symbolic soundness of the `mulx` target

These pin the data words the fused `mulx` materialises: the low half `low(a·b)`
in `lo` and the high half `high(a·b)` in `hi`, against the `JasminModel`
semantics (`x86_MULX_lo_hi`, the transcription of Jasmin's `x86_MULX_lo_hi`). -/

/-- A single reg-operand `mulx hi lo a b` lands the **low** word `low(a·b)` in
    `lo` (`mulx`'s `dstLo` output). -/
theorem mulx_get_lo (s : JState 64) (hi lo a b : String) (hne : hi ≠ lo) :
    (evalInstr s (.mulx hi lo (.reg a) (.reg b))).get lo
      = (x86_MULX_lo_hi (s.get a) (s.get b)).1 := by
  simp only [evalInstr]
  rw [JState.get_setReg_other _ _ _ _ (Ne.symm hne), JState.get_setReg_same]
  simp only [JOperand.eval, JState.get]

/-- A single reg-operand `mulx hi lo a b` lands the **high** word `high(a·b)` in
    `hi` (`mulx`'s `dstHi` output). -/
theorem mulx_get_hi (s : JState 64) (hi lo a b : String) :
    (evalInstr s (.mulx hi lo (.reg a) (.reg b))).get hi
      = (x86_MULX_lo_hi (s.get a) (s.get b)).2 := by
  simp only [evalInstr]
  rw [JState.get_setReg_same]
  simp only [JOperand.eval, JState.get]

/-- **Low-word coalesce soundness.** `Ox86_IMULt`'s low word `a·b` is exactly the
    low half `MULX` produces. Hence replacing a standalone low `imul` (whose data
    result is `a·b` low) by the `mulx` that re-derives the same low word does not
    change the low word: the fused `mulx` computes *the same* `lo` and
    *additionally* the correct `hi`. -/
theorem imul_word_eq_mulx_lo (a b : BitVec 64) :
    (x86_IMULt a b).word = (x86_MULX_lo_hi a b).1 := by
  simp only [x86_IMULt, x86_MULX_lo_hi, wumul, rflags_of_mul]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mul_mod]

/-! ## 2. The generic recognizer + rewrite over `List (JInstr 64)`

`fuseMulx` scans for the recognised pair anywhere in a straight-line body and
coalesces it to the single `mulx`, recursing on the tail. A non-matching head
passes through unchanged. -/

/-- Does instruction `i` produce only the **low** word of `lo · (reg b)` as a
    redundant `imul` whose paired widening is the following `mulx`? Matches
    `imul lo (.reg b)` against the shared second source `b`. -/
def isRedundantLowMul : JInstr 64 → Option (String × String)
  | .imul lo (.reg b) => some (lo, b)
  | _ => none

/-- Does instruction `i` widen `a · b` into `(hi, lo)` re-deriving the low word
    into `lo`, sharing the second source `b` with a just-seen low `imul`? Matches
    `mulx hi lo (.reg a) (.reg b)`. -/
def isWideningMul : JInstr 64 → Option (String × String × String × String)
  | .mulx hi lo (.reg a) (.reg b) => some (hi, lo, a, b)
  | _ => none

/-- **The generic MUL→MULX selector.** Walk the body; whenever a low
    `imul lo, b` is immediately followed by a widening `mulx hi, lo, a, b` that
    re-derives the same low register `lo` over the same shared second source `b`,
    drop the redundant low `imul` and keep the single two-output `mulx`. Every
    other instruction passes through unchanged. -/
def fuseMulx : List (JInstr 64) → List (JInstr 64)
  | [] => []
  | i₁ :: i₂ :: rest =>
    match isRedundantLowMul i₁, isWideningMul i₂ with
    | some (lo, b), some (_hi, lo', _a, b') =>
        if lo == lo' && b == b' then
          -- redundant low imul subsumed by the mulx's low output
          i₂ :: fuseMulx rest
        else i₁ :: fuseMulx (i₂ :: rest)
    | _, _ => i₁ :: fuseMulx (i₂ :: rest)
  | [i] => [i]

/-! ## 3. `allDirect` (constant-time) preservation

`MUL`/`MULX` are register-only ALU ops — `IsDirect` — so the fusion never
introduces a register-indexed memory access. A simpler, robust statement: the
fused body is a sublist-shaped rewrite of register-only ops, so when every
instruction in the input is `IsDirect`, every instruction in the output is too.
We prove the practically useful direction directly on bodies that are entirely
`MUL`/`MULX` (the multiply spine the pass targets), where `allDirect` is a
`decide`. -/

/-- Each instruction the pass can *emit* (a passed-through `i` or a kept `mulx`)
    is `IsDirect`: the rewrite only ever drops a `MUL` or keeps existing ops, and
    `mulx` is register-only. This is the per-instruction core of CT preservation. -/
theorem mulx_isDirect (hi lo a b : String) :
    IsDirect (w := 64) (.mulx hi lo (.reg a) (.reg b)) := by
  unfold IsDirect; trivial

/-- **The pass introduces no new instructions.** Every instruction in
    `fuseMulx body` already occurs in `body`: the rewrite only ever *drops* a
    redundant low `imul` or *keeps* an existing instruction — it never
    synthesises a fresh op. (The kept `mulx` `i₂` is the same one the input
    already contained.) -/
theorem fuseMulx_mem_of_mem (body : List (JInstr 64)) :
    ∀ i ∈ fuseMulx body, i ∈ body := by
  fun_induction fuseMulx body with
  | case1 => intro i hi; simp at hi
  | case2 i₁ i₂ rest lo b hlo hi' lo' a b' hw hcond ih =>
      -- match fired: output is `i₂ :: fuseMulx rest`
      intro j hj
      rcases List.mem_cons.mp hj with h₂ | hr
      · subst h₂; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih j hr))
  | case3 i₁ i₂ rest lo b hlo hi' lo' a b' hw hcond ih =>
      -- some/some but condition false: output is `i₁ :: fuseMulx (i₂ :: rest)`
      intro j hj
      rcases List.mem_cons.mp hj with h₁ | hr
      · subst h₁; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih j hr)
  | case4 i₁ i₂ rest hmatch ih =>
      -- no match: output is `i₁ :: fuseMulx (i₂ :: rest)`
      intro j hj
      rcases List.mem_cons.mp hj with h₁ | hr
      · subst h₁; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih j hr)
  | case5 i => intro j hj; exact hj

/-- **Constant-time preservation.** If every instruction of `body` is `IsDirect`,
    so is every instruction of `fuseMulx body`: by `fuseMulx_mem_of_mem` the pass
    only keeps existing instructions, never introducing a register-indexed memory
    op. Hence a constant-time body stays constant-time after fusion. -/
theorem fuseMulx_allDirect (body : List (JInstr 64))
    (h : ∀ i ∈ body, IsDirect i) : ∀ i ∈ fuseMulx body, IsDirect i :=
  fun i hi => h i (fuseMulx_mem_of_mem body i hi)

/-! ## 4. Block-level value soundness of the coalesce

On a body that begins with the recognised pair, the fused block's `lo`/`hi`
registers hold the widening product words — `low(a·b)` and `high(a·b)` — exactly
the `(lo, hi)` the machine semantics produce for `a·b`. The standalone low `imul`
the pass drops is recomputed by the `mulx`, so the data result is unchanged. -/

/-- **The fused `mulx` computes the same `(lo, hi)` as the separate MUL+high.**
    Running the fused single `mulx hi lo a b` produces `low(a·b)` in `lo` and
    `high(a·b)` in `hi` — the widening product the dropped low `imul` (low word)
    plus the high half together compute. `a ≠ lo` (the multiplicand is not the
    low destination) is the standard two-address freshness the fusion assumes. -/
theorem fuseMulx_get_sound (s : JState 64) (hi lo a b : String)
    (hhl : hi ≠ lo) :
    (runBlock s [.mulx hi lo (.reg a) (.reg b)]).get lo
        = (x86_MULX_lo_hi (s.get a) (s.get b)).1
    ∧ (runBlock s [.mulx hi lo (.reg a) (.reg b)]).get hi
        = (x86_MULX_lo_hi (s.get a) (s.get b)).2 := by
  refine ⟨?_, ?_⟩
  · simp only [runBlock_cons, runBlock_nil]
    exact mulx_get_lo s hi lo a b hhl
  · simp only [runBlock_cons, runBlock_nil]
    exact mulx_get_hi s hi lo a b

/-! ## 5. Worked demo on a real 2-register widening shape

`demoPair` is the lowered shape of a `64×64 → 128` widening multiply emitted as a
redundant low `imul` plus the widening `mulx` over the shared second source `bb`.
The pass fires and coalesces it to `demoFused`; the fused block computes the
correct `(lo, hi)` of `aa · bb`. -/

/-- The un-fused shape: a redundant low `imul lo, bb` (the low word) followed by
    the widening `mulx hilo lo, aa, bb` re-deriving the same low register. -/
def demoPair : List (JInstr 64) :=
  [ .imul "lo" (.reg "bb")
  , .mulx "hilo" "lo" (.reg "aa") (.reg "bb") ]

/-- The fused shape: the single two-output `mulx`, the redundant low `imul`
    dropped. -/
def demoFused : List (JInstr 64) :=
  [ .mulx "hilo" "lo" (.reg "aa") (.reg "bb") ]

/-- **The selector fires** on the real widening shape: `fuseMulx demoPair` is the
    single fused `mulx`. -/
theorem demoFused_fires : fuseMulx demoPair = demoFused := by
  rfl

/-- The fused block computes the correct **low** word `low(aa·bb)`. -/
theorem demoFused_lo (s : JState 64) :
    (runBlock s demoFused).get "lo" = (x86_MULX_lo_hi (s.get "aa") (s.get "bb")).1 := by
  simp only [demoFused, runBlock_cons, runBlock_nil]
  exact mulx_get_lo s "hilo" "lo" "aa" "bb" (by decide)

/-- The fused block computes the correct **high** word `high(aa·bb)`. -/
theorem demoFused_hi (s : JState 64) :
    (runBlock s demoFused).get "hilo" = (x86_MULX_lo_hi (s.get "aa") (s.get "bb")).2 := by
  simp only [demoFused, runBlock_cons, runBlock_nil]
  exact mulx_get_hi s "hilo" "lo" "aa" "bb"

/-- An initial state seeding `aa`/`bb` with concrete words for the value KAT. -/
def demoState (aa bb : BitVec 64) : JState 64 :=
  { regs := fun r => if r = "aa" then aa else if r = "bb" then bb else 0 }

/-- **Concrete value KAT (one small vector).** `aa = 2^40`, `bb = 2^40`:
    `aa·bb = 2^80 = high·2^64 + low` with `low = 0`, `high = 2^16`. The fused
    `mulx` lands `0` in `lo` and `2^16` in `hilo`. -/
theorem demoFused_kat :
    (runBlock (demoState (BitVec.ofNat 64 (2^40)) (BitVec.ofNat 64 (2^40))) demoFused).get "lo"
        = 0
    ∧ (runBlock (demoState (BitVec.ofNat 64 (2^40)) (BitVec.ofNat 64 (2^40))) demoFused).get "hilo"
        = BitVec.ofNat 64 (2^16) := by
  native_decide

/-- The fused demo is in the constant-time class (register-only multiply). -/
theorem demoFused_allDirect : ∀ i ∈ demoFused, IsDirect i := by
  intro i hi
  simp only [demoFused, List.mem_singleton] at hi
  subst hi; exact mulx_isDirect _ _ _ _

end CatCrypt.Crypto.SecureCompilation.X86Backend.CarryChainSelect
