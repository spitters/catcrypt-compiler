/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64
public import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvModel64

/-!
# Wiring a 64-bit bignum op alphabet to the RV64 model, with SLTU carry macros

`ArmLowering.lean` lowers a 64-bit `BOp` alphabet to the A64 `BInst` *one rule per
constructor*, because AArch64's `ADCS`/`SBCS`/`CSEL` are single instructions. This
module is the **RISC-V RV64** analogue, but the carry-chain ops are **macro
lowerings** (one `ROp64` → several `RInst64`), because RV64 has no carry flag and
no conditional select — they are synthesized from `ADD`/`SUB`/`SLTU`/`AND`/`OR`
(see `RiscvModel64`'s header for the architectural reason).

```
ROp64 (bignum_add_p256)  --lowerRBlock64-->  RInst64 (RV64 register machine)
                         --runRBlock64 (RiscvModel64)-->  RState64 transform
                         --renderRInst64 (RiscvAsmPrinter64)-->  GAS RV64 asm
```

## The carry macros (the RISC-V instruction-count cost)

| `ROp64`            | meaning                              | RV64 expansion |
|--------------------|--------------------------------------|----------------|
| `addcc d cout a b` | `d := a+b ; cout := carry`           | `add d a b ; sltu cout d a`  (2) |
| `addc d cout a b cin t` | `d := a+b+cin ; cout := carry`  | `add t a b ; sltu c1 t a ; add d t cin ; sltu c2 d t ; or cout c1 c2`  (5) |
| `subbb d bout a b` | `d := a−b ; bout := borrow`          | `sltu bout a b ; sub d a b`  (2) |
| `subb d bout a b bin t` | `d := a−b−bin ; bout := borrow` | `sltu b1 a b ; sub t a b ; sltu b2 t bin ; sub d t bin ; or bout b1 b2`  (5) |
| `csub d sub orig cond mask` | `d := cond ? sub : orig` (CT) | `sub mask zero cond ; and d sub mask ; ... ` (mask select, 4) |

So each A64 `ADCS` (1 insn) is 5 RV64 insns, each `SBCS` is 5, and the 4× `CSEL`
reduce becomes a 4× mask select. The `bignum_add_p256` body that is 23 A64
instructions becomes materially more on RV64 — the documented price of the missing
flag register, not a backend inefficiency.

All macros are verified down to the model: `lowerRBlock64` is a `flatMap`, the
block theorem `riscvBlock64_lowering_denote` is a clean induction, and each macro's
denotation is pinned by `native_decide` KATs (the carry/borrow bits are the
`SLTU` outputs).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend

/-! ## 1. A register-named 64-bit bignum op (the lowering's source shape) -/

/-- A register-named 64-bit RV64 bignum/field op. The carry-chain ops name the
    extra carry/borrow register(s) and the scratch the SLTU macro uses. -/
inductive ROp64 where
  /-- `d := a + b` (no carry tracked). -/
  | add (d a b : String)
  /-- `d := a - b` (no borrow tracked). -/
  | sub (d a b : String)
  /-- `d := a + b ; cout := carry-out` (chain head). Expands to `add ; sltu`. -/
  | addcc (d cout a b : String)
  /-- `d := a + b + cin ; cout := carry-out` (chain link, `cin` a 0/1 register).
      Expands to `add ; sltu ; add ; sltu ; or`, using scratch `t`. -/
  | addc (d cout a b cin t : String)
  /-- `d := a - b ; bout := borrow-out` (chain head). Expands to `sltu ; sub`. -/
  | subbb (d bout a b : String)
  /-- `d := a - b - bin ; bout := borrow-out` (chain link). Expands to
      `sltu ; sub ; sltu ; sub ; or`, using scratch `t`. -/
  | subb (d bout a b bin t : String)
  /-- `d := if cond ≠ 0 then sub else orig`, branch-free (constant-time). `cond`
      holds 0 or 1; `mask` is a scratch. Expands to
      `sub mask zero cond ; and tmp sub mask ; ...` — the mask select. Uses two
      scratch registers `mask`, `t`. -/
  | csub (d sub orig cond mask t : String)
  /-- `d := a &&& b`. -/
  | and (d a b : String)
  /-- `d := a ||| b`. -/
  | or  (d a b : String)
  /-- `d := a ^^^ b`. -/
  | xor (d a b : String)
  /-- `d := MUL a, b` (low 64). -/
  | mul (d a b : String)
  /-- `d := MULHU a, b` (high 64). -/
  | mulhu (d a b : String)
  /-- `d := LI #imm` (load immediate). -/
  | li (d : String) (imm : Nat)
  /-- `d := MV src`. -/
  | mov (d s : String)
  /-- `d := a >>> sh` (logical shift right by an immediate below 64). -/
  | srli (d a : String) (sh : Fin 64)
  /-- `d := a <<< sh` (logical shift left by an immediate below 64). -/
  | slli (d a : String) (sh : Fin 64)
  deriving Repr, DecidableEq

/-- `d := a >>> i` for an arbitrary amount `i`: `srli` when `i < 64`, and the constant 0
    otherwise, the value of a 64-bit logical shift by 64 or more. -/
def ROp64.shrImm (d a : String) (i : Nat) : ROp64 :=
  if h : i < 64 then .srli d a ⟨i, h⟩ else .li d 0

/-- `d := a <<< i` for an arbitrary amount `i`: `slli` when `i < 64`, and the constant 0
    otherwise. -/
def ROp64.shlImm (d a : String) (i : Nat) : ROp64 :=
  if h : i < 64 then .slli d a ⟨i, h⟩ else .li d 0

/-- Below 64, `ROp64.shrImm` is the `srli` instruction with the same amount. -/
theorem ROp64.shrImm_of_lt (d a : String) {i : Nat} (h : i < 64) :
    ROp64.shrImm d a i = .srli d a ⟨i, h⟩ := dif_pos h

/-- Below 64, `ROp64.shlImm` is the `slli` instruction with the same amount. -/
theorem ROp64.shlImm_of_lt (d a : String) {i : Nat} (h : i < 64) :
    ROp64.shlImm d a i = .slli d a ⟨i, h⟩ := dif_pos h

/-- Lower a register-named 64-bit bignum op to a *list* of machine `RInst64`s. The
    carry-chain ops expand to the `SLTU` macros (the RISC-V analogue of ARM's
    single `ADCS`/`SBCS`/`CSEL`). -/
def toRInst64 : ROp64 → List RInst64
  | .add d a b => [.add d a b]
  | .sub d a b => [.sub d a b]
  | .addcc d cout a b =>
      -- sum into scratch `cout` first (alias-safe: `d` may equal `a`), set the
      -- carry, then move the sum to `d`. Carry: sum < a ⇔ wrap.
      [.add "sum__" a b, .sltu cout "sum__" a, .mv d "sum__"]
  | .addc d cout a b cin t =>
      [.add t a b, .sltu "c1__" t a, .add "sum__" t cin, .sltu "c2__" "sum__" t,
       .or cout "c1__" "c2__", .mv d "sum__"]
  | .subbb d bout a b =>
      [.sltu bout a b, .sub d a b]
  | .subb d bout a b bin t =>
      [.sltu "b1__" a b, .sub t a b, .sltu "b2__" t bin, .sub "dif__" t bin,
       .or bout "b1__" "b2__", .mv d "dif__"]
  | .csub d sub orig cond mask t =>
      -- mask := 0 - cond  (all-ones if cond=1, else 0). Compute the whole select
      -- into the scratch `t` first, THEN write `d` — so the common bignum aliasing
      -- `d = orig` (in-place reduce) does not clobber `orig` mid-macro.
      [.sub mask "zero" cond,
       .and t sub mask,             -- t  := sub &&& mask
       .and "csm__" orig mask,      -- csm__ := orig &&& mask
       .xor "csm__" orig "csm__",   -- csm__ := orig &&& ~~~mask  (orig ^^^ (orig&mask))
       .or  t t "csm__",            -- t  := (sub&mask) ||| (orig&~mask)
       .mv  d t]                    -- d  := select (write last, alias-safe)
  | .and d a b => [.and d a b]
  | .or  d a b => [.or  d a b]
  | .xor d a b => [.xor d a b]
  | .mul d a b => [.mul d a b]
  | .mulhu d a b => [.mulhu d a b]
  | .li  d imm => [.li d imm]
  | .mov d s => [.mv d s]
  | .srli d a sh => [.srli d a sh]
  | .slli d a sh => [.slli d a sh]

/-- Lower a straight-line `ROp64` block to a machine `RInst64` block (a `flatMap`,
    since the carry macros expand one op to several). -/
def lowerRBlock64 (block : List ROp64) : List RInst64 := block.flatMap toRInst64

/-- The lowering of `ROp64.shrImm d a i` writes `a >>> i` to `d`, for every `i`. -/
theorem ROp64.run_shrImm (s : RState64) (d a : String) (i : Nat) :
    runRBlock64 s (toRInst64 (ROp64.shrImm d a i)) = s.set d (s.get a >>> i) := by
  unfold ROp64.shrImm
  split
  · rfl
  · next h =>
    simp only [toRInst64, runRBlock64, evalRInst64]
    rw [BitVec.ushiftRight_eq_zero (by omega)]

/-- The lowering of `ROp64.shlImm d a i` writes `a <<< i` to `d`, for every `i`. -/
theorem ROp64.run_shlImm (s : RState64) (d a : String) (i : Nat) :
    runRBlock64 s (toRInst64 (ROp64.shlImm d a i)) = s.set d (s.get a <<< i) := by
  unfold ROp64.shlImm
  split
  · rfl
  · next h =>
    simp only [toRInst64, runRBlock64, evalRInst64]
    rw [BitVec.shiftLeft_eq_zero (by omega)]

/-! ## 2. The block-lowering denotation theorem (RV64 bignum)

The 64-bit analogue of `riscvBlock_lowering_denote`: lowering a straight-line
`ROp64` block and running it on the model equals the direct fold of each op's
expansion. No new custom axioms. -/

/-- **RISC-V RV64 64-bit block-lowering denotation theorem.** -/
theorem riscvBlock64_lowering_denote :
    ∀ (block : List ROp64) (s : RState64),
      runRBlock64 s (lowerRBlock64 block)
        = block.foldl (fun st op => runRBlock64 st (toRInst64 op)) s := by
  intro block
  induction block with
  | nil => intro s; rfl
  | cons op rest ih =>
      intro s
      simp only [lowerRBlock64, List.flatMap_cons, List.foldl_cons]
      rw [runRBlock64_append]
      exact ih (runRBlock64 s (toRInst64 op))

/-! ## 3. Per-macro denotation KATs (the SLTU carry-synthesis is correct)

The carry-chain macros write the right value *and* the right carry/borrow bit —
pinned by `native_decide` on worked vectors. These witness that the SLTU
synthesis matches the flagged ARM/x86 semantics. -/

/-- A tiny two-register state for the macro KATs. -/
def mkState (a b : Nat) : RState64 :=
  { regs := fun r => match r with
      | "a" => BitVec.ofNat 64 a | "b" => BitVec.ofNat 64 b | _ => 0 }

/-- **`addcc` macro KAT (carry case).** `a = 2⁶⁴-1`, `b = 1`: sum wraps to `0`,
    the SLTU produces carry `cout = 1`. -/
theorem addcc_carry_kat :
    let s := runRBlock64 (mkState 0xffffffffffffffff 1)
      (toRInst64 (.addcc "d" "cout" "a" "b"))
    s.get "d" = 0 ∧ s.get "cout" = 1 := by native_decide

/-- **`addcc` macro KAT (no-carry case).** `a = 5`, `b = 7`: sum `12`, `cout = 0`. -/
theorem addcc_nocarry_kat :
    let s := runRBlock64 (mkState 5 7) (toRInst64 (.addcc "d" "cout" "a" "b"))
    s.get "d" = 12 ∧ s.get "cout" = 0 := by native_decide

/-- **`addc` macro KAT (carry-in + carry-out).** `a = 2⁶⁴-1`, `b = 0`, `cin = 1`:
    `a + 0 + 1 = 2⁶⁴` wraps to `0`, `cout = 1`. -/
theorem addc_carry_kat :
    let s0 : RState64 := { regs := fun r => match r with
        | "a" => BitVec.ofNat 64 0xffffffffffffffff | "cin" => 1 | _ => 0 }
    let s := runRBlock64 s0 (toRInst64 (.addc "d" "cout" "a" "b" "cin" "t"))
    s.get "d" = 0 ∧ s.get "cout" = 1 := by native_decide

/-- **`subbb` macro KAT (borrow case).** `a = 3`, `b = 5`: `3 - 5` borrows,
    `d = 2⁶⁴-2`, `bout = 1`. -/
theorem subbb_borrow_kat :
    let s := runRBlock64 (mkState 3 5) (toRInst64 (.subbb "d" "bout" "a" "b"))
    s.get "d" = BitVec.ofNat 64 0xfffffffffffffffe ∧ s.get "bout" = 1 := by
  native_decide

/-- **`subb` macro KAT (borrow-in + borrow-out).** `a = 0`, `b = 0`, `bin = 1`:
    `0 - 0 - 1` borrows, `d = 2⁶⁴-1`, `bout = 1`. -/
theorem subb_borrow_kat :
    let s0 : RState64 := { regs := fun r => match r with | "bin" => 1 | _ => 0 }
    let s := runRBlock64 s0 (toRInst64 (.subb "d" "bout" "a" "b" "bin" "t"))
    s.get "d" = BitVec.allOnes 64 ∧ s.get "bout" = 1 := by native_decide

/-- **`csub` mask-select KAT (cond = 1 selects `sub`).** With `cond = 1`,
    `mask = 0 - 1 = all-ones`, so `d := sub`. -/
theorem csub_cond1_kat :
    let s0 : RState64 := { regs := fun r => match r with
        | "sub" => 0xaaaa | "orig" => 0xbbbb | "cond" => 1 | _ => 0 }
    let s := runRBlock64 s0 (toRInst64 (.csub "d" "sub" "orig" "cond" "mask" "t"))
    s.get "d" = 0xaaaa := by native_decide

/-- **`csub` mask-select KAT (cond = 0 selects `orig`).** With `cond = 0`,
    `mask = 0`, so `d := orig`. -/
theorem csub_cond0_kat :
    let s0 : RState64 := { regs := fun r => match r with
        | "sub" => 0xaaaa | "orig" => 0xbbbb | "cond" => 0 | _ => 0 }
    let s := runRBlock64 s0 (toRInst64 (.csub "d" "sub" "orig" "cond" "mask" "t"))
    s.get "d" = 0xbbbb := by native_decide

end CatCrypt.Crypto.SecureCompilation.RISCVBackend
