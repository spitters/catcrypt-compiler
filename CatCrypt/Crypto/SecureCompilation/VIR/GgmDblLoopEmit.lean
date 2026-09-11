/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import Std.Tactic.BVDecide
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Owned ROLLED counted-loop kernel emit: GGM doubling accumulator (`ComL.forLoop`)

This module is the **end-to-end demonstration** that the `ComL.forLoop` loop node
(`JasminLprogExport`, §3b) closes a real counted-loop kernel as an owned
**ROLLED** `.s` — one body copy plus a real `jne .L` back-edge — where the only
prior options were unrolling to `n` body copies or falling back to jasminc.

## The kernel

The GGM PRF-tree's per-level **doubling** accumulator: at each tree level the
running index is doubled (`acc := acc + acc`, the left-child index expansion).
Iterated `n` times from a seed it computes `acc := init * 2^n`, i.e. a
fixed-trip `BitVec 64` shift-by-`n`. It is **accumulator-shaped** (one
`Com jasminDialect [reg 64] (reg 64)` body over a single accumulator register),
so it fits the `JLoopBody` shape exactly, and it has a closed-form functional
spec (`init <<< n`) that the `ComL.denote` is checked against directly.

* `dblBody` — one iteration `acc ↦ acc + acc`, a `regArith .add 64` over the
  accumulator with itself.
* `ggmDblLoop n` — the whole kernel: a single `.forLoop ⟨n, dblBody⟩` whose loop
  result is returned. The trip count `n` is a public configuration constant
  (the GGM tree depth), so the counter/back-edge are CT-admissible (#460).

## The two pieces of end-to-end evidence

1. **`denote = spec`** (`ggm_denote`): `(ggmDblLoop n).denote ⟨init⟩ = init <<< n`,
   by induction on `n` via `JLoopBody.denote_succ` + `bv_decide` (`x + x = x <<< 1`).
   The `#eval` KAT below confirms a concrete instance (`init = 1`, `n = 12 ↦ 4096`).

2. **ONE body copy + a real back-edge** (`ggm_one_label`/`ggm_one_cond`/
   `ggm_one_body`/`ggm_body_len`): the emitted body for a **4095-trip** loop
   (`ggmDblLfundef 4095`) has exactly **one** `Llabel`, **one** `Lcond` back-edge,
   and **one** `ADD:64` body copy — the body length is a constant 9 instructions,
   *independent of the 4095 trip count*. An unrolled emission would carry 4095
   `ADD` copies; the rolled emission carries one, with the `jne .L` closing the
   loop. `ggmDblAsm` renders the AT&T `.s` (`.L<f>_1:` … `jne .L<f>_1`).

## Assemblable physical-register operands (the physical RA loop path)

This emit lowers via `ComL.toLprogPhys` / `ComL.toLfundefPhys` — the **physical**
(post-RA, two-address) loop renderer in `JasminLprogExport` (§7e). It runs the
rolled `comLToBody` back-edge through the SAME physical RA as a straight-line
`Com`: the accumulator lands in `%rax`, the trip counter in `%rbx`, the body
temporary in `%rcx`, the SysV argument `a0` is materialized into `%rbx` at entry,
and the result is moved to `%rax` before the trailing `ret`. No operand is left
as an `%<UNKNOWN>` SSA name, so `renderLprogAtt` produces an **assemblable** `.s`:
real registers, one `addq` body copy, and a real `jne .L<d>` back-edge.

(The previous emission lowered via `ComL.toLfundef`, the pre-RA SSA body, whose
virtual register names `r1`/`Lctr1`/`L1_r1` rendered as `%<UNKNOWN>` placeholders
— only the control-flow skeleton was final. That path is replaced here.)

## The `JLoopBody` accumulator-shape limitation (reported, not worked around)

`JLoopBody.update : Com jasminDialect [accTy] accTy` carries a **single**
accumulator type. A kernel whose loop body does an **indexed array load/store**
each iteration (e.g. `mayo_encode`: `out[i] := f(in[i])` over a `stackArr`) needs
the loop body to take both the array(s) and the index `i` as iteration state and
to advance `i` — neither expressible in the single-accumulator `[accTy] accTy`
body. The accumulator demo here is the in-scope target; the next `JLoopBody` /
`comLToBody` extension required for in-loop indexed memory is a **multi-binder
loop body** carrying `(arr, i)` state with an index-advance step (the
`MultiBinderLoopBody` / `MultiAccumLoop` direction), so the body `Com` can read
`stackLoad`/write `stackStore` at the per-iteration index. That extension is the
prerequisite for rolling `mayo_encode` and the `*_sign_rwhile` kernels.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.GgmDblLoopEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. The kernel: GGM doubling accumulator -/

/-- One iteration of the GGM doubling accumulator: `acc ↦ acc + acc`. A single
    `regArith .add 64` reading the accumulator with itself. -/
def dblBody : Com jasminDialect [JasminTy.reg 64] (JasminTy.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons .here .nil)))
    (.ret .here)

/-- The whole counted-loop kernel: `ggmDblLoop n` doubles its seed argument
    `n` times via a single `.forLoop` node and returns the final accumulator.
    `n` is the public GGM tree depth (a configuration constant). -/
def ggmDblLoop (n : Nat) : ComL [JasminTy.reg 64] (JasminTy.reg 64) :=
  .forLoop ⟨n, dblBody⟩ .here (.ret .here)

/-! ## 2. `denote = spec` (the functional correctness of the rolled kernel) -/

/-- One doubling step denotes to a shift-by-one: `acc + acc = acc <<< 1`. -/
theorem step_spec (x : BitVec 64) : JLoopBody.stepC dblBody x = x <<< 1 := by
  show x + x = x <<< 1; bv_decide

/-- The whole kernel denotes to the closed-form spec `init <<< n` (doubling `n`
    times = multiply by `2^n` mod `2^64`). Proved by induction on the trip count
    via `JLoopBody.denote_succ`, each step discharged by `bv_decide`. This is the
    mathematical ground truth the rolled back-edge (`jne .L`) realises. -/
theorem ggm_denote (n : Nat) (init : BitVec 64) :
    (ggmDblLoop n).denote (.cons init .nil) = init <<< n := by
  show JLoopBody.denote ⟨n, dblBody⟩ init = init <<< n
  induction n with
  | zero => simp [JLoopBody.denote_zero]
  | succ k ih =>
      rw [JLoopBody.denote_succ, ih, BitVec.shiftLeft_add init k 1]
      show (init <<< k) + (init <<< k) = (init <<< k) <<< 1
      bv_decide

/-! ## 3. The owned ROLLED emission (PHYSICAL register allocation)

The kernel is lowered through `ComL.toLprogPhys` / `ComL.toLfundefPhys` — the
loop-aware **physical** (post-RA, two-address) export. The rolled `comLToBody`
back-edge is run through the same physical RA as a straight-line `Com`, so every
operand is a real x86 register and `renderLprogAtt` yields an **assemblable**
`.s` (real registers, one `addq`, a real `jne .L<d>` back-edge). -/

/-- The exported PHYSICAL `lfundef` for the `n`-trip kernel: `ComL.toLfundefPhys`
    lowers the `.forLoop` node to its rolled back-edge AND runs it through the
    physical register allocator — the accumulator → `RAX`, counter → `RBX`, body
    temp → `RCX`, SysV arg `a0` materialized into `RBX`, result returned in
    `RAX`. No operand is left as an `%<UNKNOWN>` SSA name. -/
def ggmDblLfundef (n : Nat) : Lfundef :=
  ComL.toLfundefPhys (ggmDblLoop n)

/-- The exported PHYSICAL `lprog` for the `n`-trip kernel. -/
def ggmDblLprog (n : Nat) (fname : String := "ggm_dbl_loop") : Lprog :=
  ComL.toLprogPhys (ggmDblLoop n) fname

/-- The rendered, **assemblable** AT&T `.s` of the rolled kernel: real registers
    (`%rax`/`%rbx`/`%rcx`), one `addq`, a real `jne .L<d>` back-edge — no
    `%<UNKNOWN>` placeholder survives. -/
def ggmDblAsm (n : Nat) (fname : String := "ggm_dbl_loop") : String :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned (ggmDblLprog n fname)

/-- The serialized physical lprog blob (magic + textual lprog) for the `n`-trip
    kernel. -/
def ggmDblLprogText (n : Nat) (fname : String := "ggm_dbl_loop") : String :=
  ComL.toLprogPhysText (ggmDblLoop n) fname

/-- Write the assemblable physical `.s` of the `n`-trip GGM doubling loop to the
    bench gen directory, so the orchestrator can re-emit + `gcc -c` + byte-KAT
    (`in <<< n`). Value ABI: `reg u64 in → reg u64 out = in <<< n` (arg in `RDI`,
    result in `RAX`). -/
def writeGgmDblAsm (n : Nat)
    (path : System.FilePath :=
      "bench/faest_ggm_owned/gen/ggm_dbl_loop_owned.s")
    (fname : String := "ggm_dbl_loop") : IO Unit :=
  IO.FS.writeFile path (ggmDblAsm n fname)

/-! ## 4. ROLLED-not-unrolled + REAL-REGISTER structural witnesses

For a **4095-trip** kernel the PHYSICAL body carries exactly one of each loop
landmark, a constant instruction count, and **only real x86 registers** — all
independent of the trip count. An unrolled emission would carry 4095 `ADD:64`
copies; an un-allocated (pre-RA) emission would carry `%<UNKNOWN>` SSA names. -/

/-- The physical (post-RA) body of the 4095-trip kernel. -/
def ggmDblPhysBody : Lcmd := (ggmDblLfundef 4095).lfd_body

/-- Count the `Llabel` instructions in a body. -/
def countLabel : Lcmd → Nat :=
  List.countP (fun i => match i.li_i with | .Llabel _ _ => true | _ => false)

/-- Count the `Lcond` (conditional back-edge) instructions in a body. -/
def countCond : Lcmd → Nat :=
  List.countP (fun i => match i.li_i with | .Lcond _ _ => true | _ => false)

/-- Count the `ADD:64` (loop-body doubling) instructions in a body. -/
def countAdd : Lcmd → Nat :=
  List.countP (fun i => match i.li_i with | .Lopn _ "ADD:64" _ => true | _ => false)

/-- Exactly **one** loop label, for a 4095-trip kernel. -/
theorem ggm_one_label : countLabel ggmDblPhysBody = 1 := by native_decide

/-- Exactly **one** conditional back-edge, for a 4095-trip kernel. -/
theorem ggm_one_cond : countCond ggmDblPhysBody = 1 := by native_decide

/-- Exactly **one** `ADD:64` body copy — NOT 4095 unrolled copies. This is the
    rolled-not-unrolled core fact, preserved through physical RA. -/
theorem ggm_one_body : countAdd ggmDblPhysBody = 1 := by native_decide

/-- **No `%<UNKNOWN>` SSA names survive:** every `Lopn` register operand in the
    physical body is a real x86 register, not an SSA-shape name (`r…`/`L…`/`Lctr…`)
    that the owned printer maps to `%<UNKNOWN>`. -/
theorem ggm_no_ssa_names :
    ggmDblPhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          ((dsts ++ srcs).filterMap LOperand.regName?).all (fun n =>
            !("L".isPrefixOf n) && !("r".isPrefixOf n))
      | _ => true) = true := by native_decide

/-- The whole rolled, physically-allocated body, as exported for a 4095-trip
    kernel: accumulator in `RAX`, counter in `RBX`, temp in `RCX`, arg
    materialized into `RBX`, result in `RAX`, one `ADD:64`, a real `Lcond`
    back-edge. The only trip-count-dependent operand is the counter seed `#4095`;
    the instruction sequence is otherwise constant (9 body instructions after the
    arg-materialize MOV and seed MOV — independent of the 4095 trip count). -/
theorem ggm_phys_body_expected :
    ggmDblPhysBody.map (fun i => i.li_i.toText) =
      [ "Lopn [RBX] MOVQ [RDI]"        -- materialize SysV arg a0 → RBX
      , "Lopn [RAX] MOV:64 [RBX]"      -- seed accumulator RAX ← a0
      , "Lopn [RBX] MOV:64 [#4095]"    -- trip counter RBX ← 4095
      , "Llabel int 1"                 -- .L1:  (back-edge target)
      , "Lopn [RCX] MOV:64 [RAX]"      -- two-address: temp ← acc
      , "Lopn [RCX] ADD:64 [RCX,RAX]"  -- acc + acc   (ONE body copy)
      , "Lopn [RAX] MOV:64 [RCX]"      -- feedback acc ← temp
      , "Lopn [RBX] SUB:64 [RBX,#1]"   -- counter--
      , "Lopn [RBX] CMP:64 [RBX,#0]"   -- counter == 0 ?
      , "Lcond NZ 1"                   -- jne .L1   (real back-edge)
      , "Lret" ] := by native_decide

/-! ## 5. KAT smoke checks -/

-- Concrete functional KAT: doubling `1` twelve times = `4096`.
/-- info: 4096#64 -/
#guard_msgs in #eval (ggmDblLoop 12).denote (.cons (1 : BitVec 64) .nil)

/-- info: 4096#64 -/
#guard_msgs in #eval ((1 : BitVec 64) <<< 12)

end CatCrypt.Crypto.SecureCompilation.VIR.GgmDblLoopEmit
