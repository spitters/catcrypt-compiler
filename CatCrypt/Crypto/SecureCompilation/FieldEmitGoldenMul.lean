/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ComBuilder
import CatCrypt.Crypto.SecureCompilation.VIR.MulDenoteErgonomics
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.VIR.Grind
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

/-!
# Golden path, capstone: the GF(251) full multiply `(a * b) mod 251`

This is the asm-sourced big-kernel that defeated the hand-written routes: a
19-binding straight-line kernel with two genuine `regArith .mul` bindings (the
`a * b` product and the `hi * 5` Solinas fold) plus the branchless
conditional-subtract reduction tail. Hand-authoring its de-Bruijn `Com` chain
and discharging its denotation by a brute `rfl` (or `native_decide`) is exactly
what `EMIT_PROVENANCE.md` flagged as the wall.

It is now mechanizable end-to-end via the two enablers:

* **`ComBuilder`** — the named-SSA → `Com` builder. The kernel is written as a
  flat list of `Binding`s whose operands reference earlier results *by level*;
  `build` resolves the de-Bruijn indices automatically (no hand `.there` chain),
  and the general `build_preserves_ComOK` lemma discharges `ComOK` turnkey from a
  per-binding `SupportedOp` check.
* **`MulDenoteErgonomics.com_denote`** — the two-phase denotation tactic that
  rewrites the binder chain open and settles the per-op residue with the `mul`
  terms (`a * b`, `hi * 5`) left **symbolic**, so the value proof does not force
  the `a.toNat * b.toNat` arithmetic and does not need `native_decide`.

The arithmetic: for `a, b < 251`, `a * b < 251² = 63001 < 2^16`. Two Solinas
folds `256 ≡ 5 (mod 251)` collapse `a*b` to a representative `< 2·251` (each fold
peels the high byte, weights it by `5`, and adds the low byte), and the
branchless `condsub-251` tail subtracts the prime once if needed — yielding the
canonical residue. The kernel computes this *over `BitVec 64`*; correctness of
the modular value (for `a, b` in range) is the Solinas/condsub algebra, here we
golden the **emit**: one source, `ComOK`, `Com.denote = spec`, both backends.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ComBuilder
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## A. The named-SSA kernel

Two inputs `a = level 0`, `b = level 1`. Bindings name results by level
`2 … 19`; the return is level `19`. The `c5` (level 4) and `c255` (level 6)
constants are materialised once and reused across both Solinas folds. -/

/-- The GF(251) full-multiply named-SSA program: `imul`, two Solinas `256 ≡ 5`
    folds, then the branchless `condsub-251`. Operands reference results by
    level; `build` resolves the de-Bruijn indices. -/
def gf251MulSSA : NamedSSA where
  nInputs := 2
  bindings :=
    [ ⟨.regArith .mul 64, [0, 1]⟩    -- prod = a*b           [2]
    , ⟨.shrImm 64 8, [2]⟩            -- hi  = prod>>8        [3]
    , ⟨.regConst 64 5, []⟩           -- c5                   [4]
    , ⟨.regArith .mul 64, [3, 4]⟩    -- him = hi*5           [5]
    , ⟨.regConst 64 255, []⟩         -- c255                 [6]
    , ⟨.regArith .and 64, [2, 6]⟩    -- lo  = prod&255       [7]
    , ⟨.regArith .add 64, [5, 7]⟩    -- f1  = him+lo         [8]
    , ⟨.shrImm 64 8, [8]⟩            -- hi2 = f1>>8          [9]
    , ⟨.regArith .mul 64, [9, 4]⟩    -- him2= hi2*5  (c5)    [10]
    , ⟨.regArith .and 64, [8, 6]⟩    -- lo2 = f1&255 (c255)  [11]
    , ⟨.regArith .add 64, [10, 11]⟩  -- f2  = him2+lo2       [12]
    , ⟨.regConst 64 251, []⟩         -- c251                 [13]
    , ⟨.regArith .sub 64, [12, 13]⟩  -- t   = f2-c251        [14]
    , ⟨.shrImm 64 63, [14]⟩          -- bit = t>>>63         [15]
    , ⟨.regConst 64 0, []⟩           -- c0                   [16]
    , ⟨.regArith .sub 64, [16, 15]⟩  -- m   = c0-bit         [17]
    , ⟨.regArith .and 64, [17, 13]⟩  -- masked = m&c251      [18]
    , ⟨.regArith .add 64, [14, 18]⟩  -- r   = t+masked       [19]
    ]
  retLevel := 19

/-! ## B. The built `Com`

`build` succeeds (every operand level is in range and the op signatures all take
`reg 64`); `.get (by decide)` extracts the `Com` over the two-input context. -/

/-- The generated `Com jasminDialect [.reg 64, .reg 64] (.reg 64)` for the GF(251)
    full multiply — de-Bruijn indices resolved by the builder, no hand `.there`. -/
def gf251MulBuilt : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  (build gf251MulSSA).get (by decide)

/-! ## C. The value proof — `Com.denote = NamedSSA.eval`, the turnkey eval route

For this wide kernel the per-kernel `Com.denote` `rfl` (and the `com_denote`
binder-chain rewrite) hits the `whnf` heartbeat wall `EMIT_PROVENANCE.md` flagged.
The turnkey value layer is `build_preserves_denote`: `Com.denote` of a built kernel
equals the **computable** `NamedSSA.eval`, so a denote fact becomes an `eval`
*computation* (`decide`/`native_decide`) rather than a deep `Com.denote` unfolding.

The reference value the kernel computes is `condSub251 (solFold (solFold (a * b)))`
— `imul` then two Solinas `256 ≡ 5 (mod 251)` folds then the branchless
`condsub-251` tail. `solFold` matches `MulDenoteErgonomics.solinas251Fold`. -/

/-- The branchless `condsub-251` tail as a `BitVec 64` function: `t = x - 251`,
    `r = t + ((0 - (t >>> 63)) &&& 251)`. -/
def condSub251 (x : BitVec 64) : BitVec 64 :=
  (x - (251 : BitVec 64))
    + (((0 : BitVec 64) - ((x - (251 : BitVec 64)) >>> 63)) &&& (251 : BitVec 64))

/-- One GF(251) Solinas `256 ≡ 5` fold: `(x >>> 8) * 5 + (x &&& 255)`. The same
    fold `MulDenoteErgonomics.solinas251Fold` proves; restated here for the
    composed reference. -/
def solFold (x : BitVec 64) : BitVec 64 :=
  ((x >>> 8) * (5 : BitVec 64)) + (x &&& (255 : BitVec 64))

/-- **The GF(251) full-multiply reference value.** `imul` then two Solinas folds
    then the condsub-251 tail; the two `mul`s stay symbolic. -/
def gf251MulSpec (a b : BitVec 64) : BitVec 64 :=
  condSub251 (solFold (solFold (a * b)))

/-- **`gf251MulSSA` is well-formed** (no forward/self operand references): every
    binding's operands, and the `retLevel`, are in scope at the point they are read.
    The side condition `build_preserves_denote` needs. -/
theorem gf251MulSSA_wf : BindingsWF 2 gf251MulSSA.bindings 19 := by
  unfold gf251MulSSA
  simp only [BindingsWF]
  norm_num [List.mem_cons]

/-- **The evaluator is symbolically faithful.** For every `a, b`, `NamedSSA.eval`
    returns exactly the composed GF(251) Solinas-fold/condsub reference value — a
    `rfl` on the computable evaluator (the two `mul`s stay symbolic). -/
theorem gf251Mul_eval_symbolic (a b : BitVec 64) :
    gf251MulSSA.eval [a, b] = some (gf251MulSpec a b) :=
  rfl

/-- **The generated `Com`'s denotation equals the reference, via the eval route** —
    `build_preserves_denote` carries `Com.denote = NamedSSA.eval`, and
    `gf251Mul_eval_symbolic` identifies the eval value with the composed
    Solinas/condsub reference. Turnkey: NO per-kernel `Com.denote` `rfl`, NO
    `com_denote` binder-chain rewrite (both of which hit the `whnf` heartbeat wall at
    this width), NO `native_decide` — the wide-kernel denote is the computable `eval`. -/
theorem gf251MulBuilt_denote (a b : BitVec 64) :
    Com.denote gf251MulBuilt (.cons b (.cons a .nil)) = gf251MulSpec a b := by
  have hcorr : EnvCorr ([.reg 64, .reg 64] : Ctxt jasminDialect)
      (.cons b (.cons a .nil))
      (fun L => ([a, b] : List (BitVec 64))[L]?.getD 0) 2 := by
    intro L hL; interval_cases L <;> rfl
  exact build_preserves_denote gf251MulSSA gf251MulBuilt (.cons b (.cons a .nil))
    [a, b] (gf251MulSpec a b) hcorr gf251MulSSA_wf rfl (gf251Mul_eval_symbolic a b)

/-! ### Authoritative GF(251) products

The kernel is pinned to four authoritative GF(251) products `(a · b) mod 251`:

| `a` | `b` | `a · b` | `mod 251` |
|-----|-----|---------|-----------|
| 200 | 200 | 40000   | 91        |
| 250 | 250 | 62500   | 1         |
| 0   | 123 | 0       | 0         |
| 7   | 13  | 91      | 91        |

(`251 · 159 = 39909`, `40000 − 39909 = 91`; `251 · 249 = 62499`,
`62500 − 62499 = 1`; `91 < 251`.) -/

/-- **The evaluator computes the GF(251) product.** Four authoritative vectors on the
    computable `NamedSSA.eval` — a `native_decide` computation, not a `Com.denote`
    unfolding. -/
theorem gf251Mul_eval_kats :
    gf251MulSSA.eval [200, 200] = some 91
      ∧ gf251MulSSA.eval [250, 250] = some 1
      ∧ gf251MulSSA.eval [0, 123] = some 0
      ∧ gf251MulSSA.eval [7, 13] = some 91 := by
  native_decide

/-- **The generated 18-binding `Com` computes the GF(251) product.** Its `Com.denote`
    matches the same authoritative vectors: `gf251MulBuilt_denote` carries the
    `Com.denote = eval` identity and `gf251Mul_eval_kats` (via `gf251Mul_eval_symbolic`)
    pins the values. So the builder's auto-resolved de-Bruijn resolution across all 18
    bindings denotes `(a · b) mod 251`. -/
theorem gf251MulBuilt_kats :
    (Com.denote gf251MulBuilt (.cons (200 : BitVec 64) (.cons (200 : BitVec 64) .nil))).toNat = 91
      ∧ (Com.denote gf251MulBuilt (.cons (250 : BitVec 64) (.cons (250 : BitVec 64) .nil))).toNat = 1
      ∧ (Com.denote gf251MulBuilt (.cons (123 : BitVec 64) (.cons (0 : BitVec 64) .nil))).toNat = 0
      ∧ (Com.denote gf251MulBuilt (.cons (13 : BitVec 64) (.cons (7 : BitVec 64) .nil))).toNat = 91 := by
  obtain ⟨k1, k2, k3, k4⟩ := gf251Mul_eval_kats
  have e : ∀ a b : BitVec 64, gf251MulSpec a b = (gf251MulSSA.eval [a, b]).getD 0 := by
    intro a b; rw [gf251Mul_eval_symbolic]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gf251MulBuilt_denote 200 200, e, k1]; rfl
  · rw [gf251MulBuilt_denote 250 250, e, k2]; rfl
  · rw [gf251MulBuilt_denote 0 123, e, k3]; rfl
  · rw [gf251MulBuilt_denote 7 13, e, k4]; rfl

/-! ## D. `ComOK` — turnkey via the general builder lemma

No per-binding de-Bruijn `ComOK.var` chain: `build_preserves_ComOK` discharges it
from the `AllBindingsSupported` check, which is a finite per-binding `SupportedOp`
verification (`decide`-able). -/

/-- Every binding of `gf251MulSSA` uses a `SupportedOp` (the ALU ops `add`/`sub`/
    `and`/`mul`, `shrImm`, and `regConst`). -/
theorem gf251MulSSA_supported : AllBindingsSupported gf251MulSSA.bindings := by
  intro b hb
  simp only [gf251MulSSA, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp only [SupportedOp]
  · exact Or.inl ⟨.mul, rfl, by tauto⟩          -- prod = a*b
  · exact Or.inr (Or.inr (Or.inl ⟨8, Or.inl rfl⟩))   -- hi = prod>>8
  · exact Or.inr (Or.inr (Or.inr ⟨5, rfl⟩))     -- c5
  · exact Or.inl ⟨.mul, rfl, by tauto⟩          -- him = hi*5
  · exact Or.inr (Or.inr (Or.inr ⟨255, rfl⟩))   -- c255
  · exact Or.inl ⟨.and, rfl, by tauto⟩          -- lo = prod&255
  · exact Or.inl ⟨.add, rfl, by tauto⟩          -- f1 = him+lo
  · exact Or.inr (Or.inr (Or.inl ⟨8, Or.inl rfl⟩))   -- hi2 = f1>>8
  · exact Or.inl ⟨.mul, rfl, by tauto⟩          -- him2 = hi2*5
  · exact Or.inl ⟨.and, rfl, by tauto⟩          -- lo2 = f1&255
  · exact Or.inl ⟨.add, rfl, by tauto⟩          -- f2 = him2+lo2
  · exact Or.inr (Or.inr (Or.inr ⟨251, rfl⟩))   -- c251
  · exact Or.inl ⟨.sub, rfl, by tauto⟩          -- t = f2-c251
  · exact Or.inr (Or.inr (Or.inl ⟨63, Or.inl rfl⟩)) -- bit = t>>>63
  · exact Or.inr (Or.inr (Or.inr ⟨0, rfl⟩))     -- c0
  · exact Or.inl ⟨.sub, rfl, by tauto⟩          -- m = c0-bit
  · exact Or.inl ⟨.and, rfl, by tauto⟩          -- masked = m&c251
  · exact Or.inl ⟨.add, rfl, by tauto⟩          -- r = t+masked

/-- **`ComOK gf251MulBuilt`, turnkey.** Discharged by the general
    `build_preserves_ComOK` from the per-binding `SupportedOp` check — no
    hand-authored `ComOK.var` witness chain. -/
theorem gf251MulBuilt_ok : ComOK gf251MulBuilt :=
  build_preserves_ComOK gf251MulSSA gf251MulBuilt gf251MulSSA_supported (by rfl)

/-! ## E. Emit — both verified backends + the x86 ELF leg

The two-input context is all-`reg 64`; `com_arm_e2e`/`com_riscv_e2e` discharge
both backend blocks from `gf251MulBuilt_ok` via the single `comToReg_faithful`. -/

/-- The two-input context is all-`reg 64`. -/
theorem allReg64_two : AllReg64 ([.reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu; rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · exact absurd h List.not_mem_nil

/-- **The GF(251) full multiply emits to AArch64**, discharged by `com_arm_e2e`
    via the single `comToReg_faithful` — `imul`/`umulh`-free scalar Solinas. -/
theorem gf251MulBuilt_arm_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 2 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg gf251MulBuilt 2))).regs)
        (comRetName gf251MulBuilt 2)
      = Com.denote gf251MulBuilt V :=
  com_arm_e2e gf251MulBuilt_ok allReg64_two V s hs

/-- **The same source emits to RISC-V** — one source, two backends, both verified,
    both discharged by the single `comToReg_faithful`. -/
theorem gf251MulBuilt_riscv_e2e (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 2 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg gf251MulBuilt 2))).regs)
        (comRetName gf251MulBuilt 2)
      = Com.denote gf251MulBuilt V :=
  com_riscv_e2e gf251MulBuilt_ok allReg64_two V s hs

/-- **The compiled statements' shift counts are in range** (`ShiftAmtOK`): the
    kernel's `shrImm 8` (×2) and `shrImm 63` lower to `shrI` statements whose counts
    `8`, `63` are `< 2^64`. The bounded `∀` is not directly `Decidable`, so it is
    bridged through a `List.all` Bool predicate (`native_decide` over the concrete
    compiled program). -/
theorem gf251MulBuilt_shiftOK :
    ∀ stmt ∈ comToRegProg gf251MulBuilt 2, ScalarLinX86Demo.ShiftAmtOK stmt := by
  have h : (comToRegProg gf251MulBuilt 2).all
      (fun s => match s with
        | .shrI _ _ i | .shlI _ _ i => decide (i < 2 ^ 64)
        | _ => true) = true := by native_decide
  intro stmt hm
  have hb := (List.all_eq_true.mp h) stmt hm
  simp only [ScalarLinX86Demo.ShiftAmtOK]
  revert hb
  cases stmt <;> simp_all

/-- **The end-to-end x86 leg** (full mirror of the ARM/RISC-V legs, via
    `ScalarLinX86Demo.com_x86_e2e`). The register-freshness faithfulness is
    discharged automatically by `comToRegProg_X86Faithful`; the only residual side
    condition is the shift-count range `ShiftAmtOK` (`gf251MulBuilt_shiftOK`). -/
theorem gf251MulBuilt_x86_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64] : Ctxt jasminDialect))
    (s : ScalarLinX86Demo.XState) (hs : s.regs = envOf 2 V) :
    ((ScalarLinX86Demo.x86Target.runOps s
        (ScalarLinX86Demo.x86Target.compile (comToRegProg gf251MulBuilt 2))).regs)
        (comRetName gf251MulBuilt 2)
      = Com.denote gf251MulBuilt V :=
  ScalarLinX86Demo.com_x86_e2e gf251MulBuilt_ok allReg64_two V s hs gf251MulBuilt_shiftOK

/-- **The x86 owned-emit leg** (KAT-gated tier, as the rest of `FieldEmitGoldenPath`):
    the same `Com` source compiled to ELF `.o` bytes via the generic driver. -/
def gf251MulBuilt_x86_elf : ByteArray :=
  X86Backend.CompileComToElfJInstrFull6.compileComToElfJInstrFull6 gf251MulBuilt "gf251_mul"

end CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenMul
