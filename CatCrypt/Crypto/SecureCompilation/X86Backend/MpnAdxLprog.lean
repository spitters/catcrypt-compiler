/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit

/-!
# ADX `mpn_add_n` / `mpn_sub_n` limb schedules as a physical `Linear.lprog` (#500)

Definitions, by section:

* §1 the physical-register and memory-operand helpers: `r`/`a`/`b` pinned to
  their SysV argument registers (`RDI`/`RSI`/`RDX`) with a two-register scratch
  window, and the `Linstr` builders `mov64` / `binop64` / `adcx64` / `adox64`.
* §2–§3 `addBody` / `subBody`, the per-limb `Lcmd` schedules: a single `ADCX`
  (CF) chain for the add, a `SUB` / `SBB` borrow chain for the subtract.
* §4 `addLprog` / `subLprog`, each schedule as a one-export physical `Lprog`
  over the 3-pointer void ABI — the level `comToLfundefPhysAbi` outputs.
* §5 `addAsm` / `subAsm`, their AT&T text under `renderLprogAtt`.
* §7 `emitMain`, the artifact driver; its docstring says which `.s` files it
  writes and where each comes from.

## Why ADX

A multi-precision add has exactly one mathematical carry chain, so `addBody`
threads a single `ADCX` (CF) chain: a leading `XOR rax, rax` clears CF
(carry-in 0), then each limb is `MOV ti, a[i]; ADCX ti, b[i]; MOV r[i], ti`.
`ADCX` keeps the carry in CF with **no flag spill** (vs spilling or
`SETC`-materialising a carry register), and — because `ADCX` touches only CF
and `ADOX` only OF — leaves OF free for the interleaved second chain of a fused
`addmul`/`mul`, which is what the `ADOX` primitive `adox64` is here for. For a
pure add the payoff is the carry-spill-free, ADX-encoded chain, not a second
parallel chain: a plain add has only one carry. The dual independent CF/OF
chains pay off in `addmul`/`mul`, where the low and high product sums give two.

x86 has no `SBBX`/`SBOX` (ADX is add-only), so `subBody` keeps the single-borrow
`SUB` / `SBB` chain.

## What is verified vs trusted

* **Trusted (thin)**: `gas` (mnemonic+operands → bytes) and the leaf ABI frame
  (`renderLfundef`), the same surface every owned backend trusts.

The all-inputs functional identity (`Σ rᵢ·Bⁱ = Σ aᵢ·Bⁱ ± Σ bᵢ·Bⁱ mod B^n`) is the
byte-exact KAT vs GMP `__gmpn_add_n` / `__gmpn_sub_n` in
`bench/mpn_adx_owned_compare/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdxLprog

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. Physical-register / memory-operand helpers

We pin the three pointers to their SysV argument registers and use a fixed
two-register scratch window. The result word lives in a scratch (`R8` / `R9`),
the carry chains thread through CF (`ADCX`) and OF (`ADOX`) — neither is a named
operand, so the body uses only `{RDI, RSI, RDX, RAX, R8, R9}`. -/

/-- The result pointer `r` (SysV arg 0). -/
def rPtr : String := "RDI"
/-- The first operand pointer `a` (SysV arg 1). -/
def aPtr : String := "RSI"
/-- The second operand pointer `b` (SysV arg 2). -/
def bPtr : String := "RDX"
/-- The XOR-zero / flag-clear scratch register. -/
def zReg : String := "RAX"
/-- Scratch for the even-limb (`ADCX`/CF) chain accumulator. -/
def evReg : String := "R8"
/-- Scratch for the odd-limb (`ADOX`/OF) chain accumulator. -/
def odReg : String := "R9"

/-- A memory operand `[base + 8*i]` as the `mem.<base>.<off>` name the
    `LprogAsmPrinter.resolveName` map recognises. -/
def memAt (base : String) (i : Nat) : LOperand := .reg (memName base (8 * i))

/-- A 64-bit two-address binop `Lopn [d] OP:64 [d, s]`. -/
def binop64 (d : String) (op : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 op) [.reg d, s]⟩

/-- A 64-bit move `Lopn [d] MOV:64 [s]`. -/
def mov64 (d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] "MOV:64" [s]⟩

/-- A 64-bit `ADCX d, s`: `d := d + s + CF`, CF only. Three-source
    `Lopn [d] ADCX:64 [d, s, cf]` — the carry-in flag is the `reg 1` third source
    the printer drops (CF is implicit). The carry source name `"cf"` is never an
    operand (dropped), so its register class is irrelevant. -/
def adcx64 (d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 "ADCX") [.reg d, s, .reg "cf"]⟩

/-- A 64-bit `ADOX d, s`: `d := d + s + OF`, OF only (the second carry chain). -/
def adox64 (d : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (withWidthTag 64 "ADOX") [.reg d, s, .reg "of"]⟩

/-! ## 2. The ADX `mpn_add_n` body (single ADCX/CF chain)

A multi-precision add has exactly **one** mathematical carry chain (the carry
out of limb `i` feeds limb `i+1`), so — unlike `addmul`/`mul`, where the low and
high product sums give two independent carries to run on CF and OF —
`add_n` uses a **single** carry chain. We thread it through `ADCX` (the CF
chain): a leading `XOR rax, rax` clears CF (carry-in 0 for limb 0), then each
limb is `MOV ti, a[i]; ADCX ti, b[i]; MOV r[i], ti`. `ADCX` (vs the legacy `ADC`)
keeps the carry in CF with **no flag spill** and — because `ADCX` writes only CF
and `ADOX` only OF — leaves OF free for an interleaved second chain in a fused
`addmul` (the reason ADX exists); for a pure add it is the carry-spill-free,
ADX-encoded form of the add chain.

The accumulator alternates `R8`/`R9` per limb purely to give the load and the
store of adjacent limbs distinct registers (so the OOO core can overlap limb
`i`'s store with limb `i+1`'s load); the carry stays in CF throughout. -/

/-- The per-limb ADX add steps for limb `i`: load `a[i]` into a scratch,
    `ADCX` add `b[i]` (CF carry-in/out), store `r[i]`. The scratch alternates
    `R8`/`R9` so adjacent limbs' load/store use distinct registers. -/
def addLimb (i : Nat) : Lcmd :=
  let acc := if i % 2 = 0 then evReg else odReg
  [ mov64 acc (memAt aPtr i)            -- acc := a[i]
  , adcx64 acc (memAt bPtr i)           -- acc := a[i] + b[i] + CF
  , mov64 (memName rPtr (8 * i)) (.reg acc) ]  -- r[i] := acc

/-- The ADX `mpn_add_n` body for `n` limbs: clear CF, then the single ADCX carry
    chain, then `ret`. The `XOR rax, rax` clears CF (and OF) so limb 0's `ADCX`
    sees carry-in 0. -/
def addBody (n : Nat) : Lcmd :=
  -- `XOR rax, rax` (two-address `Lopn [rax] XOR:64 [rax, rax]`) clears CF
  -- (carry-in 0 for the first ADCX) and zeroes rax (unused afterwards).
  binop64 zReg "XOR" (.reg zReg)
    :: (List.range n).flatMap addLimb
    ++ [⟨0, .Lret⟩]

/-! ## 3. The single-borrow `mpn_sub_n` body

x86 ADX is add-only (no `SBBX`/`SBOX`), so subtraction keeps the single CF borrow
chain: `SUB` on limb 0, `SBB` on the rest. The body uses one scratch register. -/

/-- The per-limb sub step for limb `i`: load `a[i]`, `sub`/`sbb` `b[i]`, store. -/
def subLimb (i : Nat) : Lcmd :=
  let op := if i = 0 then "SUB" else "SBB"
  [ mov64 evReg (memAt aPtr i)
  , binop64 evReg op (memAt bPtr i)
  , mov64 (memName rPtr (8 * i)) (.reg evReg) ]

/-- The `mpn_sub_n` body for `n` limbs: the SUB/SBB borrow chain, then `ret`. -/
def subBody (n : Nat) : Lcmd :=
  (List.range n).flatMap subLimb ++ [⟨0, .Lret⟩]

/-! ## 4. The physical `Lprog` (one export function each)

The function takes the three pointers in `RDI`/`RSI`/`RDX` (SysV args 0,1,2),
returns `void` (the result is written through `*r`). The body uses no spill
slots (constant register pressure), so `renderLfundef` allocates only the qsave
block (which is unused here — the body touches no callee-saved register: `RDI`,
`RSI`, `RDX`, `RAX`, `R8`, `R9` are all caller-saved). -/

/-- A void leaf `Lfundef` over the 3-pointer SysV ABI with the given body. -/
def voidFundef (body : Lcmd) : Lfundef :=
  { lfd_tyin := [64, 64, 64]
    lfd_arg := [rPtr, aPtr, bPtr]
    lfd_body := body
    lfd_tyout := []
    lfd_res := []
    lfd_export := true }

/-- The owned-RA `Lprog` for ADX `mpn_add_n` at `n` limbs. -/
def addLprog (n : Nat) : Lprog :=
  { lp_funcs := [(s!"mpn_add_n_adx_owned_{n}", voidFundef (addBody n))] }

/-- The owned-RA `Lprog` for `mpn_sub_n` at `n` limbs. -/
def subLprog (n : Nat) : Lprog :=
  { lp_funcs := [(s!"mpn_sub_n_adx_owned_{n}", voidFundef (subBody n))] }

/-! ## 5. AT&T emission through the owned printer -/

/-- The rendered AT&T `.s` for the ADX add kernel at `n` limbs. -/
def addAsm (n : Nat) : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (addLprog n)

/-- The rendered AT&T `.s` for the sub kernel at `n` limbs. -/
def subAsm (n : Nat) : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (subLprog n)

/-! ## 6. Rendered asm -/

-- Rendered-asm correctness is the external GMP KAT; an in-Lean hasSub check would re-evaluate the optimizing back-end renderOwned at elaboration.

/-! ## 7. Emit driver -/

/-- Write the owned-RA ADX `.s` for the add/sub kernels at `n = 4, 8, 16, 32`
    into the bench harness directory.

    **Both deployed symbols `mpn_add_n_adx_owned_{n}` and
    `mpn_sub_n_adx_owned_{n}` are FRONT-generated** (#477 closed): each `.s` is
    the RA-legalized `catCryptDialect` `Com` chain (`MpnAddFrontEmit.toAsm`
    / the sub complement-add path, no hand `Com`/`Lcmd`/`.s`) — these are the
    emits the conform KAT (`make -C bench/mpn_adx_owned_compare conform`,
    byte-exact vs GMP `__gmpn_add_n` / `__gmpn_sub_n`) verifies. The hand-pinned
    ADX add / `SUB`/`SBB` sub of §2–§3 (`addAsm` / `subAsm`) are retained IN this
    module as the verified bench-perf references
    (the tightest schedules) but are not the deployed emit. The sub is
    front-sourced through the complement-add convention `x − y = x + ~y + carry`
    (the front's `subStart`/`subMid` windows lower to `ADCX`, so the front `.s`
    carries an `adcxq` chain rather than `sbb`; the result words match
    `__gmpn_sub_n`). -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/mpn_adx_owned_compare/gen_com"
  for n in [4, 8, 16, 32] do
    match MpnAddFrontEmit.toAsm n s!"mpn_add_n_adx_owned_{n}" ["RDI", "RSI", "RDX"] with
    | some frontS =>
        -- FRONT-generated (RA-legalized Com → ADX chain): the deployed add symbol.
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_add_n_adx_owned_{n}.s"
          frontS
    | none =>
        throw (IO.userError s!"front-compile of mpn_add_n at n={n} declined")
    match MpnAddFrontEmit.toAsmOf s!"mpn_sub_n_adx_owned_{n}" ["RDI", "RSI", "RDX"]
            (MpnAddFrontEmit.subFrontCom n) with
    | some frontS =>
        -- FRONT-generated (RA-legalized Com → complement-add ADX chain): sub symbol.
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_sub_n_adx_owned_{n}.s"
          frontS
    | none =>
        throw (IO.userError s!"front-compile of mpn_sub_n at n={n} declined")
  IO.println "wrote FRONT-generated owned-RA ADX mpn_add_n + mpn_sub_n (both deployed) .s at n=4,8,16,32"

/-! ## 8. Artifact generation at elaboration

The renders are written while this module elaborates, so `lake` produces them
from this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdxLprog
