/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ComBuilder
import CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull6
import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull

/-!
# Two more all-ALU golden field reductions, via the Com-generator

This file is the "step 1" continuation of the leaf-emission plan: two further
field-reduction kernels emitted by the verified compiler, each authored through
the **named-SSA generator** (`ComBuilder.build`) rather than by hand-writing
de-Bruijn `.there` chains. No new compiler capability is introduced — both
reductions live in the same all-ALU (`regArith`/`shrImm`/`regConst`) fragment as
`FieldEmitGoldenPath.fieldCondSub251Com`, lower through the same
`comToReg_faithful`, and emit to AArch64, RISC-V, and x86 ELF.

The recipe per kernel (mirroring `ComBuilder.condSub251SSA`/`condSub251Built`):
1. write a `NamedSSA` (operands named by de-Bruijn *level*; the generator
   resolves the indices);
2. `build … |>.get (by decide)` materialises the `Com`;
3. `ComOK` via the direct per-op witnesses (the general builder-preserves-`ComOK`
   lemma is owned by another stream; here we give the explicit chain so this file
   stands alone);
4. `…_denote` by `rfl` — the load-bearing check that the auto-resolved de-Bruijn
   indices coincide with the intended ALU expression (a miscounted level would
   make this `rfl` fail);
5. `arm_e2e`/`riscv_e2e` via `com_arm_e2e`/`com_riscv_e2e` + `allReg64_one`, and
   `x86_elf := compileComToElf …`.

## Kernel 1 — GF(127) Mersenne reduce (QRUOV)

`127 = 2^7 - 1`, so `a mod 127` folds by `lo := a & 127 ; hi := a >> 7 ;
s := lo + hi` followed by the branchless condsub-127 tail
(`t := s - 127 ; m := 0 - (t >>> 63) ; r := t + (127 & m)`). For `a < 127^2` one
fold plus the condsub suffices; the denote is stated as the resulting ALU
expression.

## Kernel 2 — lattice `q = 3329` conditional-subtract (ML-KEM / ML-DSA tail)

`a ≥ 3329 ? a - 3329 : a` — the Barrett-reduce tail, structurally identical to
`fieldCondSub251Com` with the constant `251` replaced by `3329`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenReduces

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv
open CatCrypt.Crypto.SecureCompilation.ComBuilder
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath (allReg64_one)

/-! ## Kernel 1 — GF(127) Mersenne reduce -/

/-- The named-SSA description of the GF(127) Mersenne reduce `a mod 127`
    (`127 = 2^7 - 1`). One Mersenne fold (`lo + hi`) then the branchless
    condsub-127 tail. Single input `a` at level `0`:

    ```
    v1  := 127              -- c127   (regConst)
    v2  := a & v1           -- lo  = a & 127
    v3  := a >>> 7          -- hi  = a >> 7
    v4  := v2 + v3          -- s   = lo + hi
    v5  := v4 - v1          -- t   = s - 127
    v6  := v5 >>> 63        -- bit = sign(t)
    v7  := 0                -- c0     (regConst)
    v8  := v7 - v6          -- m   = 0 - bit
    v9  := v8 & v1          -- masked = m & 127
    v10 := v5 + v9          -- r   = t + masked
    ret v10
    ``` -/
def gf127ReduceSSA : NamedSSA where
  nInputs := 1
  bindings :=
    [ ⟨.regConst 64 127, []⟩       -- v1  := 127
    , ⟨.regArith .and 64, [0, 1]⟩  -- v2  := a & c127
    , ⟨.shrImm 64 7, [0]⟩          -- v3  := a >>> 7
    , ⟨.regArith .add 64, [2, 3]⟩  -- v4  := lo + hi
    , ⟨.regArith .sub 64, [4, 1]⟩  -- v5  := s - c127
    , ⟨.shrImm 64 63, [5]⟩         -- v6  := t >>> 63
    , ⟨.regConst 64 0, []⟩         -- v7  := 0
    , ⟨.regArith .sub 64, [7, 6]⟩  -- v8  := c0 - bit
    , ⟨.regArith .and 64, [8, 1]⟩  -- v9  := m & c127
    , ⟨.regArith .add 64, [5, 9]⟩  -- v10 := t + masked
    ]
  retLevel := 10

/-- The generator succeeds and produces a `Com` over the single-input context. -/
def gf127ReduceBuilt : Com jasminDialect [.reg 64] (.reg 64) :=
  (build gf127ReduceSSA).get (by decide)

/-- The generated GF(127)-reduce `Com` is in the supported straight-line fragment.
    Direct per-op witnesses (regConst, and, shrImm, add, sub, shrImm, regConst,
    sub, and, add). -/
theorem gf127ReduceBuilt_ok : ComOK gf127ReduceBuilt := by
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨127, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.and, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inl ⟨7, Or.inl rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inl ⟨63, Or.inl rfl⟩))) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨0, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inl ⟨.and, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) ?_
  exact ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) (ComOK.ret _)

/-- **Step 2 — value proof, cheap `rfl`** (all-ALU, no `mul`). The generated `Com`
    denotes the GF(127) Mersenne-fold + condsub-127 ALU expression. This `rfl`
    validates the generated de-Bruijn levels. -/
theorem gf127ReduceBuilt_denote (a : BitVec 64) :
    Com.denote gf127ReduceBuilt (.cons a .nil)
      = (((a &&& (127 : BitVec 64)) + (a >>> 7)) - (127 : BitVec 64))
          + (((0 : BitVec 64)
                - ((((a &&& (127 : BitVec 64)) + (a >>> 7)) - (127 : BitVec 64)) >>> 63))
              &&& (127 : BitVec 64)) :=
  rfl

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem gf127ReduceBuilt_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg gf127ReduceBuilt 1))).regs)
        (comRetName gf127ReduceBuilt 1)
      = Com.denote gf127ReduceBuilt V :=
  com_arm_e2e gf127ReduceBuilt_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem gf127ReduceBuilt_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg gf127ReduceBuilt 1))).regs)
        (comRetName gf127ReduceBuilt 1)
      = Com.denote gf127ReduceBuilt V :=
  com_riscv_e2e gf127ReduceBuilt_ok allReg64_one V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/qruov_compare/`, not byte identity with `compileComToElf`. -/
def gf127ReduceBuilt_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf gf127ReduceBuilt "gf127_reduce"

/-! ## Kernel 2 — lattice `q = 3329` conditional-subtract -/

/-- The named-SSA description of the `q = 3329` conditional-subtract
    `a ≥ 3329 ? a - 3329 : a` — the ML-KEM/ML-DSA Barrett-reduce tail, structurally
    identical to `ComBuilder.condSub251SSA` with `251` replaced by `3329`. Single
    input `a` at level `0`:

    ```
    v1 := 3329             -- c3329  (regConst)
    v2 := a - v1           -- t = a - 3329
    v3 := v2 >>> 63        -- sign bit
    v4 := 0                -- c0     (regConst)
    v5 := v4 - v3          -- m = 0 - bit
    v6 := v5 & v1          -- masked = m & 3329
    v7 := v2 + v6          -- r = t + masked
    ret v7
    ``` -/
def condSub3329SSA : NamedSSA where
  nInputs := 1
  bindings :=
    [ ⟨.regConst 64 3329, []⟩      -- v1 := 3329
    , ⟨.regArith .sub 64, [0, 1]⟩  -- v2 := a - c3329
    , ⟨.shrImm 64 63, [2]⟩         -- v3 := t >>> 63
    , ⟨.regConst 64 0, []⟩         -- v4 := 0
    , ⟨.regArith .sub 64, [4, 3]⟩  -- v5 := c0 - bit
    , ⟨.regArith .and 64, [5, 1]⟩  -- v6 := m & c3329
    , ⟨.regArith .add 64, [2, 6]⟩  -- v7 := t + masked
    ]
  retLevel := 7

/-- The generator succeeds and produces a `Com` over the single-input context. -/
def condSub3329Built : Com jasminDialect [.reg 64] (.reg 64) :=
  (build condSub3329SSA).get (by decide)

/-- The generated `q = 3329` condsub `Com` is in the supported straight-line
    fragment (regConst, sub, shrImm, regConst, sub, and, add). -/
theorem condSub3329Built_ok : ComOK condSub3329Built := by
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨3329, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inl ⟨63, Or.inl rfl⟩))) ?_
  refine ComOK.var (Or.inr (Or.inr (Or.inr ⟨0, rfl⟩))) ?_
  refine ComOK.var (Or.inl ⟨.sub, rfl, Or.inr (Or.inl rfl)⟩) ?_
  refine ComOK.var (Or.inl ⟨.and, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) ?_
  exact ComOK.var (Or.inl ⟨.add, rfl, Or.inl rfl⟩) (ComOK.ret _)

/-- **Step 2 — value proof, cheap `rfl`** (all-ALU, no `mul`). The generated `Com`
    denotes the branchless `q = 3329` condsub ALU expression. This `rfl` validates
    the generated de-Bruijn levels. -/
theorem condSub3329Built_denote (a : BitVec 64) :
    Com.denote condSub3329Built (.cons a .nil)
      = (a - (3329 : BitVec 64))
          + (((0 : BitVec 64) - ((a - (3329 : BitVec 64)) >>> 63)) &&& (3329 : BitVec 64)) :=
  rfl

/-- **Emitted AArch64**, discharged by `comToReg_faithful` via `com_arm_e2e`. -/
theorem condSub3329Built_arm_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 1 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg condSub3329Built 1))).regs)
        (comRetName condSub3329Built 1)
      = Com.denote condSub3329Built V :=
  com_arm_e2e condSub3329Built_ok allReg64_one V s hs

/-- **Emitted RISC-V** — same source, same `comToReg_faithful`. -/
theorem condSub3329Built_riscv_e2e (V : Ctxt.Valuation ([.reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 1 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg condSub3329Built 1))).regs)
        (comRetName condSub3329Built 1)
      = Com.denote condSub3329Built V :=
  com_riscv_e2e condSub3329Built_ok allReg64_one V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/mlkem_compare/`, not byte identity with `compileComToElf`. -/
def condSub3329Built_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf condSub3329Built "mlkem_condsub3329"

end CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenReduces
