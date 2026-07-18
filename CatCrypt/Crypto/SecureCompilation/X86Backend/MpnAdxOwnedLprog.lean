/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAddFrontEmit

/-!
# GMP-class `mpn_add_n` / `mpn_sub_n` through the owned-RA `LprogAsmPrinter` ADX path (#500)

`MpnLinearKernels.lean` lowers `mpn_add_n` / `mpn_sub_n` through the *hand-pinned*
owned x86 backend (`AsmPrinter.renderJInstr` over a fixed `GpAlloc`), with a
**single** CF carry chain (`add` / `adc`, resp. `sub` / `sbb`). This module is
the **linear-jasmin owned-RA counterpart**: it builds the kernels as a physical,
two-address `Linear.lprog` — the exact IR `JasminLprogExport.Com.toLprogPhysAbi`
emits — and renders them through `LprogAsmPrinter.renderLprogAtt` (the owned
`Lcmd → AT&T gas` consumer, task #537), the linear-path printer that also drives
the owned-RA SHA-256 / Keccak / Poseidon2 bodies.

## What is new here vs `MpnLinearKernels`

* **ADX carry chain (no carry-spill).** A multi-precision add has exactly one
  mathematical carry chain, so the add kernel threads a **single** `ADCX` (CF)
  chain: a leading `XOR rax, rax` clears CF (carry-in 0), then each limb is
  `MOV ti, a[i]; ADCX ti, b[i]; MOV r[i], ti`. `ADCX` keeps the carry in CF with
  **no flag spill** (vs spilling/`SETC`-materialising a carry register), and —
  because `ADCX` touches only CF and `ADOX` only OF — leaves OF free for the
  interleaved second chain of a fused `addmul`/`mul` (the reason ADX exists; the
  `ADOX` primitive `adox64` is provided here for that use). For a pure add the
  payoff is the carry-spill-free, ADX-encoded chain, not a second parallel chain
  (a plain add has only one carry). The dual independent CF/OF chains pay off in
  `addmul`/`mul`, where the low and high product sums give two genuine carries.
* **The owned-RA `LprogAsmPrinter` path** (not the `AsmPrinter`/`GpAlloc` path):
  the body is a `Linear.lprog`, rendered by `renderLprogAtt`, assembled by `gas`
  exactly like the SHA-256 `*_x86_from_lean.s`.

## A note on the level of the source (honest scope) — #477 closed

The bodies here are constructed at the **physical-`Lprog`** level — the level
`comToLfundefPhysAbi` *outputs*, with pointers pinned to their SysV argument
registers (`RDI`=r, `RSI`=a, `RDX`=b) and a fixed two-register scratch window.
They are the **hand-pinned bench-perf twin** (constant register pressure, no
spills, tight `off(%base)` accesses): the tightest ADX schedule, kept as the
speed reference.

The #477 caveat that motivated hand-authoring — "the `Com → Lprog` register
allocator legalizes only the two-source binop alphabet; the three-source
flag-coupled `ADCX`/`ADOX` pass through unlegalized" — is **stale**. The
`Com → Lprog` RA (`JasminLprogExport.physBody` / `physBodyWithStores`) already
legalizes the three-source `ADCX`/`ADOX`: a `Lopn [d] ADCX [a, s, cin]` falls
through `physBodyRmap`'s two-source arm to the general operand-remap arm (all
operands remapped, never truncated); the owned printer expands it to the
two-address `mov a,d; adcx s,d` shape and threads the explicit carry-in; and
`AdxChainFuse.fuseAdxChain` collapses the value-threaded limb triples into a
live-flag `adcx` chain that — by construction — never crosses a flag-clobbering
instruction (its `findConsumer` scan stops at any non-`MOV` op). The streaming
`[base + 8·i]` access is the memref ABI's `mem.<base>.<off>` / SIB
`(%base,%idx,8)` form. The FRONT-generated, RA-legalized `mpn_add_n` **and**
`mpn_sub_n` (a `catCryptDialect` `Com` whose carry/borrow chain is
`bvAddCarryLo`/`bvAddCarryHi` threading one `sword 1` carry limb-to-limb; the
sub uses the complement-add convention `x − y = x + ~y + carry`, so it too
lowers to `ADCX`) live in `X86Backend.MpnAddFrontEmit` (with
`denote = (X±Y) mod 2^(64·n)` witnesses and `no-flag-clobber` `adcxq`-chain
shape checks). `Bn254TowerFrontEmit` is the deployed end-to-end witness of the
same Com → RA → ADX path.

## Subtraction

x86 has no `SBBX`/`SBOX` (ADX is add-only). The **hand** `mpn_sub_n` twin (§3)
uses the single-borrow `SUB` / `SBB` chain (one borrow flag, CF); the owned-RA
printer renders that chain too (the `SUB`/`ADD` two-address arms already
existed). The **deployed, front-generated** `mpn_sub_n` instead expresses the
subtract as the complement-add `x − y = x + ~y + carry`
(`MpnAddFrontEmit.subFrontCom`), which lowers to the same `ADCX` carry chain as
the add — so the front sub `.s` carries an `adcxq` chain, and its result words
match GMP `__gmpn_sub_n`. (The hand `SUB`/`SBB` twin is kept for the perf
reference.)

## What is verified vs trusted

* **Verified (printer)**: `LprogAsmPrinter.renderLinstrR` is a thin syntactic map
  (one `Lopn` → one AT&T line; the carry-out / MULX-hi bindings render to no
  line). The shape lemmas below pin that the emitted `.s` contains the `adcx` /
  `adox` (resp. `sub`/`sbb`) chain and reads/writes the three pointer registers.
* **Trusted (thin)**: `gas` (mnemonic+operands → bytes) and the leaf ABI frame
  (`renderLfundef`), the same surface every owned backend trusts.

The all-inputs functional identity (`Σ rᵢ·Bⁱ = Σ aᵢ·Bⁱ ± Σ bᵢ·Bⁱ mod B^n`) is the
byte-exact KAT vs GMP `__gmpn_add_n` / `__gmpn_sub_n` in
`bench/mpn_adx_owned_compare/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdxOwnedLprog

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
high product sums give two genuinely independent carries to run on CF and OF —
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
def addAsm (n : Nat) : String := renderLprogAtt (addLprog n)

/-- The rendered AT&T `.s` for the sub kernel at `n` limbs. -/
def subAsm (n : Nat) : String := renderLprogAtt (subLprog n)

/-! ## 6. Shape checks on the emitted asm

Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The add kernel emits the ADX carry chain: the carry-spill-free `adcxq` (CF
    chain) per limb, seeded by a leading `xorq` (clears CF/OF), reading `a`/`b`
    from `%rsi`/`%rdx` and writing `r` through `%rdi`. -/
theorem addAsm_8_shape :
    hasSub (addAsm 8) "adcxq"
      ∧ hasSub (addAsm 8) "xorq"
      ∧ hasSub (addAsm 8) "(%rsi)"
      ∧ hasSub (addAsm 8) "(%rdx)"
      ∧ hasSub (addAsm 8) "(%rdi)" := by native_decide

/-- The add kernel emits **no** `# UNHANDLED` sentinel (every body op rendered to
    a real AT&T line — the printer recognises the ADX class). -/
theorem addAsm_8_no_unhandled :
    hasSub (addAsm 8) "UNHANDLED" = false := by native_decide

/-- The sub kernel emits the single-borrow `subq`/`sbbq` chain. -/
theorem subAsm_8_shape :
    hasSub (subAsm 8) "subq" ∧ hasSub (subAsm 8) "sbbq"
      ∧ hasSub (subAsm 8) "UNHANDLED" = false := by native_decide

/-! ## 7. Emit driver -/

/-- Write the owned-RA ADX `.s` for the add/sub kernels at `n = 4, 8, 16, 32`
    into the bench harness directory.

    **Both deployed symbols `mpn_add_n_adx_owned_{n}` and
    `mpn_sub_n_adx_owned_{n}` are FRONT-generated** (#477 closed): each `.s` is
    the RA-legalized `catCryptDialect` `Com` chain (`MpnAddFrontEmit.toOwnedAsm`
    / the sub complement-add path, no hand `Com`/`Lcmd`/`.s`) — these are the
    emits the conform KAT (`make -C bench/mpn_adx_owned_compare conform`,
    byte-exact vs GMP `__gmpn_add_n` / `__gmpn_sub_n`) verifies. The hand-pinned
    ADX add / `SUB`/`SBB` sub of §2–§3 (`addAsm` / `subAsm`, their §6 shape
    theorems) are retained IN this module as the verified bench-perf references
    (the tightest schedules) but are no longer the deployed emit. The sub is
    front-sourced through the complement-add convention `x − y = x + ~y + carry`
    (the front's `subStart`/`subMid` windows lower to `ADCX`, so the front `.s`
    carries an `adcxq` chain rather than `sbb`; the result words match
    `__gmpn_sub_n`). -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/mpn_adx_owned_compare/gen_com"
  for n in [4, 8, 16, 32] do
    match MpnAddFrontEmit.toOwnedAsm n s!"mpn_add_n_adx_owned_{n}" ["RDI", "RSI", "RDX"] with
    | some frontS =>
        -- FRONT-generated (RA-legalized Com → ADX chain): the deployed add symbol.
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_add_n_adx_owned_{n}.s"
          frontS
    | none =>
        throw (IO.userError s!"front-compile of mpn_add_n at n={n} declined")
    match MpnAddFrontEmit.toOwnedAsmOf s!"mpn_sub_n_adx_owned_{n}" ["RDI", "RSI", "RDX"]
            (MpnAddFrontEmit.subFrontCom n) with
    | some frontS =>
        -- FRONT-generated (RA-legalized Com → complement-add ADX chain): sub symbol.
        IO.FS.writeFile s!"bench/mpn_adx_owned_compare/gen_com/mpn_sub_n_adx_owned_{n}.s"
          frontS
    | none =>
        throw (IO.userError s!"front-compile of mpn_sub_n at n={n} declined")
  IO.println "wrote FRONT-generated owned-RA ADX mpn_add_n + mpn_sub_n (both deployed) .s at n=4,8,16,32"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnAdxOwnedLprog
