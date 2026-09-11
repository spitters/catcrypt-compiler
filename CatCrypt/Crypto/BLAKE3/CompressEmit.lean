/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# BLAKE3 compression function emitted through the OWNED x86 scalar backend (#573)

This module emits the BLAKE3 reference compression function as a straight-line
`List (JInstr 32)` block in the **owned** x86 backend
(`X86Backend/{JasminModel, X86Dialect, AsmPrinter}`), *not* through the
`Com jasminDialect → .jazz → external jasminc` path of `BLAKE3/CompressJazzEmit.lean`.
The owned backend renders directly to AT&T `.s` (here a small 32-bit AT&T
printer), so the BLAKE3 bench (`bench/blake3_compare`) — and `bench/kt_compare`,
which links the same `blake3_compress` leaf — without `jasminc`.

## The compression function (BLAKE3 reference `compress`)

BLAKE3 compress is pure ARX (add / xor / rotate-right) over a 16-word `u32`
state in 7 rounds. The `G` mixing function (the reference `g`) is

    a = a + b + mx;  d = (d ^ a) >>> 16
    c = c + d;       b = (b ^ c) >>> 12
    a = a + b + my;  d = (d ^ a) >>> 8
    c = c + d;       b = (b ^ c) >>> 7

— the ChaCha quarter-round skeleton with the two message-word injections
`mx`,`my`. Each round applies `G` over the 4 columns then the 4 diagonals,
reading the 16 message words under the round's permutation schedule
(`MSG_PERMUTATION` composed `r` times). After the 7 rounds the output
feed-forward is

    for i in 0..8:  state[i]   ^= state[i+8]
                    state[i+8] ^= cv[i]

so all 16 output words are meaningful (the first 8 are the chaining value /
truncated 32-byte digest; the full 16 are the XOF block).

## Word width: a 32-bit emit (no masking)

BLAKE3 is a 32-bit algorithm. We author the body at **width 32**
(`JInstr 32`), where the owned model's `BitVec 32` semantics make every op
modular-`2^32` automatically and the rotate synthesis `(x >>> n) | (x <<< (32-n))`
is *exactly* `BitVec.rotateRight` (`blake3_ror_synth`). The leaf is rendered by a
dedicated 32-bit AT&T printer (`movl/addl/xorl/shrl/shll/orl`, 32-bit subregs),
so the hardware ops auto-mask to 32 bits and the 32-bit loads/stores are
word-exact (no high-half leak, no out-of-bounds read past the packed `u32[40]`
input). The rotate-right uses the `shr; shl; or` synthesis over the owned
backend's existing op set (no new opcode) — model-faithful and value-correct.

## What is verified vs. trusted

* **Verified**: the rotate synthesis equals `BitVec.rotateRight 32`
  (`blake3_ror_synth`); one `G` block, lowered through `X86Dialect.lowerBlock`
  and run via `runBlock`, computes the reference `gSpec` on concrete words
  (`blake3_G_computes_spec`, `native_decide` — REV-12-safe, a single G, not the
  64-byte whole-vector KAT); `lowerBlock` of the whole body denotes `runBlock`
  (`blake3_lower_denote`, the `X86Dialect` tie). The full 64-byte known-answer
  test against the OFFICIAL BLAKE3 vectors is the external C harness
  (`bench/blake3_compare/blake3_kat.c`).
* **Trusted (thin)**: the 32-bit AT&T mnemonic printer (one line per `JInstr`)
  and the System V `blake3_compress(out, inp)` ABI glue — the same trusted-scaffold
  status as `AsmPrinter.renderSysVLeafFn`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.BLAKE3.CompressEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. The BLAKE3 reference compression spec (on `BitVec 32`)

A direct transcription of the reference `compress`/`round`/`g`, used as the
value-correctness target for the emitted block. -/

/-- 32-bit rotate-right by `n` (the reference `rotate_right`). -/
def rotr (x : BitVec 32) (n : Nat) : BitVec 32 := x.rotateRight n

/-- The BLAKE3 message permutation (`MSG_PERMUTATION`). -/
def msgPermNat : Nat → Nat
  | 0 => 2 | 1 => 6 | 2 => 3 | 3 => 10 | 4 => 7 | 5 => 0 | 6 => 4 | 7 => 13
  | 8 => 1 | 9 => 11 | 10 => 12 | 11 => 5 | 12 => 9 | 13 => 14 | 14 => 15
  | 15 => 8 | _ => 0

/-- The message-index schedule for round `r`: `sched r p = (msgPerm^[r]) p`. -/
def sched : Nat → Nat → Nat
  | 0, p => p
  | (r+1), p => msgPermNat (sched r p)

/-- The 16-word state as a `Fin 16 → BitVec 32`. -/
abbrev St := Fin 16 → BitVec 32

/-- Update slot `i` of a state with value `v`. -/
def St.set (s : St) (i : Fin 16) (v : BitVec 32) : St :=
  fun j => if j = i then v else s j

/-- The reference `g` (BLAKE3 quarter-round) on slots `a b c d`, injecting the two
    message words `mx my`. -/
def gSpec (s : St) (a b c d : Fin 16) (mx my : BitVec 32) : St :=
  let va := s a + s b + mx
  let vd := rotr (s d ^^^ va) 16
  let vc := s c + vd
  let vb := rotr (s b ^^^ vc) 12
  let va := va + vb + my
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((s.set a va).set d vd).set c vc).set b vb

/-! ## 2. The emitted `JInstr 32` block

State slots live in register names `s0 .. s15`; message words are loaded on
demand from the `inp` frame (`m0 .. m15`), the read-only `cv` from `cv0 .. cv7`.
The rotate is the `shr; shl; or` synthesis. -/

/-- A state-slot register name (`s0 .. s15`). -/
def sReg (i : Nat) : String := "s" ++ toString i

/-- A message-word register name (`m0 .. m15`). -/
def mReg (i : Nat) : String := "m" ++ toString i

/-- Synthesize a rotate-right of register `dst` by `n` using a scratch register
    `tmp`: `tmp = dst; dst >>= n; tmp <<= (32-n); dst |= tmp`. The owned model's
    `BitVec 32` semantics make this exactly `dst.rotateRight n` (`blake3_ror_synth`). -/
def rorSynth (dst tmp : String) (n : Nat) : List (JInstr 32) :=
  [ .mov tmp (.reg dst)
  , .shr dst (.imm n)
  , .shl tmp (.imm (32 - n))
  , .or_ dst (.reg tmp) ]

/-- The `G` mixing on register names for slots `a b c d`, injecting message
    registers `mx my`. Mirrors `gSpec`. Uses a fresh scratch register `g_t` for
    the rotates (the rotate result is fully computed before the next rotate). -/
def emitG (a b c d : Nat) (mx my : Nat) : List (JInstr 32) :=
  let A := sReg a; let B := sReg b; let C := sReg c; let D := sReg d
  let MX := mReg mx; let MY := mReg my
  -- a = a + b + mx
  [ .add A (.reg B), .add A (.reg MX) ] ++
  -- d = (d ^ a) >>> 16
  [ .xor_ D (.reg A) ] ++ rorSynth D "g_t" 16 ++
  -- c = c + d
  [ .add C (.reg D) ] ++
  -- b = (b ^ c) >>> 12
  [ .xor_ B (.reg C) ] ++ rorSynth B "g_t" 12 ++
  -- a = a + b + my
  [ .add A (.reg B), .add A (.reg MY) ] ++
  -- d = (d ^ a) >>> 8
  [ .xor_ D (.reg A) ] ++ rorSynth D "g_t" 8 ++
  -- c = c + d
  [ .add C (.reg D) ] ++
  -- b = (b ^ c) >>> 7
  [ .xor_ B (.reg C) ] ++ rorSynth B "g_t" 7

/-- `Fin 16` from a `Nat` (mod 16). -/
def fin16 (n : Nat) : Fin 16 := ⟨n % 16, Nat.mod_lt _ (by decide)⟩

/-- One BLAKE3 round (the reference `round`) at message-schedule `r`: `G` over the
    4 columns then the 4 diagonals. -/
def emitRound (r : Nat) : List (JInstr 32) :=
  emitG 0 4 8  12 (sched r 0) (sched r 1) ++
  emitG 1 5 9  13 (sched r 2) (sched r 3) ++
  emitG 2 6 10 14 (sched r 4) (sched r 5) ++
  emitG 3 7 11 15 (sched r 6) (sched r 7) ++
  emitG 0 5 10 15 (sched r 8) (sched r 9) ++
  emitG 1 6 11 12 (sched r 10) (sched r 11) ++
  emitG 2 7 8  13 (sched r 12) (sched r 13) ++
  emitG 3 4 9  14 (sched r 14) (sched r 15)

/-! ## 4. Value correctness

The rotate synthesis equals `BitVec.rotateRight`, and one emitted `G` block,
lowered and run, computes `gSpec` on concrete words. -/

/-- **Rotate synthesis is `rotateRight`.** For any 32-bit `x` and `n < 32`,
    `(x >>> n) ||| (x <<< (32-n)) = x.rotateRight n`. This is the per-rotate
    correctness of `rorSynth` (the `shr; shl; or` triple) in `BitVec 32`. -/
theorem blake3_ror_synth (x : BitVec 32) (n : Nat) (h2 : n < 32) :
    (x >>> n) ||| (x <<< (32 - n)) = x.rotateRight n := by
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt h2]

/-- One emitted `G` block lowered through `X86Dialect.lowerBlock` denotes
    `runBlock` (the owned-backend denotation tie). -/
theorem blake3_G_lower_denote (s : JState 32) :
    (lowerBlock (Γ := []) (emitG 0 4 8 12 0 1)).denote (.cons s .nil)
      = runBlock s (emitG 0 4 8 12 0 1) :=
  lowerBlock_denote_closed _ s

/-- **One emitted `G` computes the reference `gSpec`.** On a concrete input
    (state slots `s0..s15 = 1..16`, message regs `m0 = 0x11111111`,
    `m1 = 0x22222222`), the four updated slots of the run-`G` machine state equal
    `gSpec` on the same inputs. `native_decide` over a single G (not the 7-round
    whole-vector KAT) pins the emitted block to the spec. -/
theorem blake3_G_computes_spec :
    let init : St := fun i => BitVec.ofNat 32 (i.val + 1)
    let mx : BitVec 32 := 0x11111111
    let my : BitVec 32 := 0x22222222
    let s0 : JState 32 :=
      { regs := fun r =>
          (List.range 16).foldl
            (fun acc i => if r = sReg i then BitVec.ofNat 32 (i + 1) else acc)
            (if r = mReg 0 then mx else if r = mReg 1 then my else 0) }
    let s := runBlock s0 (emitG 0 4 8 12 0 1)
    let spec := gSpec init 0 4 8 12 mx my
    s.get (sReg 0) = spec 0
      ∧ s.get (sReg 12) = spec 12
      ∧ s.get (sReg 8) = spec 8
      ∧ s.get (sReg 4) = spec 4 := by
  native_decide

/-! ## 5. The full compress body as `JInstr 32`

Load the 16 state words and 16 message words and 8 cv words from the `inp`
frame, run the 7 rounds, then the 16-word feed-forward, store the 16 results to
the `out` frame. The state/message/cv loads + result stores are frame I/O off
the two pointer arguments; the ARX is register-resident. -/

/-- The `inp` base register name (System V arg1). -/
def inpBase : String := "inp"

/-- The `out` base register name (System V arg0). -/
def outBase : String := "out"

/-- Load the 16 state words `s0..s15` from `inp[0..15]`, the 16 message words
    `m0..m15` from `inp[16..31]`, and the 8 cv words `cv0..cv7` from
    `inp[32..39]`. Word `i` is at byte `4*i` (packed `u32[40]`). -/
def loadInputs : List (JInstr 32) :=
  (List.range 16).map (fun i => .loadMem (sReg i) inpBase (4 * Int.ofNat i)) ++
  (List.range 16).map (fun i => .loadMem (mReg i) inpBase (4 * Int.ofNat (16 + i))) ++
  (List.range 8).map  (fun i => .loadMem ("cv" ++ toString i) inpBase (4 * Int.ofNat (32 + i)))

/-- The 7 rounds (`emitRound 0 .. 6`). -/
def allRounds : List (JInstr 32) :=
  (List.range 7).flatMap (fun r => emitRound r)

/-- The 16-word output feed-forward:
    `for i<8: s[i] ^= s[i+8]`; `for i<8: s[i+8] ^= cv[i]`. -/
def feedForward : List (JInstr 32) :=
  (List.range 8).map (fun i => .xor_ (sReg i) (.reg (sReg (8 + i)))) ++
  (List.range 8).map (fun i => .xor_ (sReg (8 + i)) (.reg ("cv" ++ toString i)))

/-- Store the 16 output words `s0..s15` to `out[0..15]`. -/
def storeOutputs : List (JInstr 32) :=
  (List.range 16).map (fun i => .storeMem outBase (4 * Int.ofNat i) (.reg (sReg i)))

/-- The full BLAKE3 compress body: load, 7 rounds, feed-forward, store. -/
def blake3CompressBlock : List (JInstr 32) :=
  loadInputs ++ allRounds ++ feedForward ++ storeOutputs

/-- **The whole body lowered denotes `runBlock`** (the owned-backend tie for the
    full straight-line compression). -/
theorem blake3_lower_denote (s : JState 32) :
    (lowerBlock (Γ := []) blake3CompressBlock).denote (.cons s .nil)
      = runBlock s blake3CompressBlock :=
  lowerBlock_denote_closed _ s

/-- The body's instruction count: 16+16+8 loads + 7·(8·22) round ops
    + 16 feed-forward + 16 stores. Each G is `2 + (1+4) + 1 + (1+4) + 2 + (1+4)
    + 1 + (1+4) = 26` ops; ×8 G ×7 rounds = 1456; +40 loads +16 ff +16 stores. -/
theorem blake3_block_length : blake3CompressBlock.length = 1528 := by native_decide

/-! ## 6. Frame-resident 32-bit AT&T rendering (trusted thin scaffold)

The owned `AsmPrinter` emits 64-bit `q`-suffix mnemonics; BLAKE3 needs 32-bit
`l`-suffix ops (which auto-mask to 32 bits and address the packed `u32[40]`
buffers word-exact). BLAKE3's body has 16 state + 16 message + 8 cv + 1 scratch
= 41 distinct value names, far above the GP pool, so the body is rendered
**frame-resident**: every value name lives in a 4-byte stack cell off `%rsp`,
and each `JInstr 32` is realised as `reload operand(s) → compute → store dst`
through three fixed working registers (`%eax`,`%ecx`,`%edx`). This is a simple,
spill-free, correct codegen (the same load/compute/store discipline the verified
`mem2reg`/`spillAlloc` path scalarises, here laid out directly for the two-pointer
BLAKE3 ABI).

The cell layout assigns one slot per value name in first-seen order; `inp`/`out`
stay in their argument registers `%rsi`/`%rdi`. -/

/-- The full ordered list of value names the body uses (state, message, cv, and
    the rotate scratch), in a fixed layout order. The pointer bases `inp`/`out`
    are *not* cells (they live in argument registers). -/
def cellNames : List String :=
  (List.range 16).map sReg ++ (List.range 16).map mReg ++
  (List.range 8).map (fun i => "cv" ++ toString i) ++ ["g_t"]

/-- The 4-byte stack-cell offset of a value name (off `%rsp`), or `0` for the
    pointer bases (which are not cells and never reach the cell path). -/
def cellOff (n : String) : Int :=
  match cellNames.idxOf? n with
  | some k => 4 * Int.ofNat k
  | none => 0

/-- The total cell frame size in bytes (41 names × 4), rounded up to 16. -/
def frameBytes : Nat := ((cellNames.length * 4 + 15) / 16) * 16

/-- A value-name cell as an AT&T `%rsp`-relative memory operand. -/
def cell (n : String) : String := toString (cellOff n) ++ "(%rsp)"

/-- A 32-bit operand: an immediate `$v`, or a *cell load* of a register name into
    a given working register. Returns the working-reg string and the (possibly
    empty) reload line. -/
def loadOperand (work : String) : JOperand → String × List String
  | .imm v => ("$" ++ toString v, [])
  | .reg r => (work, ["\tmovl " ++ cell r ++ ", " ++ work])

/-- Render one `JInstr 32` frame-resident: reload operands into working
    registers, compute, store the destination cell. `%eax` holds the dst value,
    `%ecx` the src value. `loadMem`/`storeMem` go through the `inp`/`out`
    pointer registers (`%rsi`/`%rdi`). -/
def renderJInstr32FR : JInstr 32 → List String
  | .mov d s =>
      let (so, sl) := loadOperand "%eax" s
      sl ++ ["\tmovl " ++ so ++ ", " ++ cell d]
  | .add d s =>
      let (so, sl) := loadOperand "%ecx" s
      ["\tmovl " ++ cell d ++ ", %eax"] ++ sl ++
        ["\taddl " ++ so ++ ", %eax", "\tmovl %eax, " ++ cell d]
  | .xor_ d s =>
      let (so, sl) := loadOperand "%ecx" s
      ["\tmovl " ++ cell d ++ ", %eax"] ++ sl ++
        ["\txorl " ++ so ++ ", %eax", "\tmovl %eax, " ++ cell d]
  | .or_ d s =>
      let (so, sl) := loadOperand "%ecx" s
      ["\tmovl " ++ cell d ++ ", %eax"] ++ sl ++
        ["\torl " ++ so ++ ", %eax", "\tmovl %eax, " ++ cell d]
  | .and_ d s =>
      let (so, sl) := loadOperand "%ecx" s
      ["\tmovl " ++ cell d ++ ", %eax"] ++ sl ++
        ["\tandl " ++ so ++ ", %eax", "\tmovl %eax, " ++ cell d]
  | .shl d (.imm n) =>
      ["\tmovl " ++ cell d ++ ", %eax", "\tshll $" ++ toString n ++ ", %eax",
       "\tmovl %eax, " ++ cell d]
  | .shr d (.imm n) =>
      ["\tmovl " ++ cell d ++ ", %eax", "\tshrl $" ++ toString n ++ ", %eax",
       "\tmovl %eax, " ++ cell d]
  | .loadMem d _ off =>
      ["\tmovl " ++ toString off ++ "(%rsi), %eax", "\tmovl %eax, " ++ cell d]
  | .storeMem _ off (.reg s) =>
      ["\tmovl " ++ cell s ++ ", %eax", "\tmovl %eax, " ++ toString off ++ "(%rdi)"]
  -- BLAKE3 never emits the other arms; a defensive comment keeps the match total.
  | _ => ["\t# unsupported in BLAKE3 frame-resident printer"]

/-- The rendered body lines for the whole compress block. -/
def blake3BodyLines : List String :=
  blake3CompressBlock.flatMap renderJInstr32FR

/-- **No `unsupported` sentinel in the rendered body** — every emitted `JInstr`
    is one of BLAKE3's ARX/memory ops the frame-resident printer handles. -/
theorem blake3BodyLines_total :
    (blake3BodyLines.any (fun l => (l.splitOn "unsupported").length > 1)) = false := by
  native_decide

/-- The body carries the ARX alphabet (`addl`/`xorl`/`shrl`/`shll`/`orl`) and the
    pointer-frame I/O (`(%rsi)` loads, `(%rdi)` stores). -/
theorem blake3BodyLines_shape :
    (blake3BodyLines.any (fun l => (l.splitOn "addl").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "xorl").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "shrl").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "shll").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "orl").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "(%rsi)").length > 1)) = true
      ∧ (blake3BodyLines.any (fun l => (l.splitOn "(%rdi)").length > 1)) = true := by
  native_decide

/-! ## 7. The System V leaf `blake3_compress(out, inp)`

`out` arrives in `%rdi`, `inp` in `%rsi` (System V AMD64). The body is leaf
(makes no call), so we adjust `%rsp` by the cell-frame size on entry and restore
on exit; no callee-saved registers are clobbered (only `%eax/%ecx/%edx` scratch
and the two argument registers). The C harness ignores the return value. -/

/-- The emitted `.s` text: a single labelled `blake3_compress` leaf — frame
    setup, the frame-resident ARX body, frame teardown, `ret`. -/
def blake3CompressAsm : String :=
  let header :=
    [ "\t.text", "\t.globl blake3_compress", "\t.type blake3_compress, @function",
      "blake3_compress:" ]
  let prologue := [ "\tsubq $" ++ toString frameBytes ++ ", %rsp" ]
  let epilogue := [ "\taddq $" ++ toString frameBytes ++ ", %rsp", "\tret" ]
  -- mark a non-executable stack (silences the linker's GNU-stack warning).
  let footer := [ "\t.section .note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ prologue ++ blake3BodyLines ++ epilogue ++ footer) ++ "\n"

/-- The emitted leaf has the BLAKE3 ABI label and the frame setup/teardown. -/
theorem blake3CompressAsm_shape :
    (blake3CompressAsm.splitOn "blake3_compress:").length > 1
      ∧ (blake3CompressAsm.splitOn ".globl blake3_compress").length > 1
      ∧ (blake3CompressAsm.splitOn "subq $").length > 1
      ∧ (blake3CompressAsm.splitOn "ret").length > 1 := by
  native_decide

/-- Emit driver: write the owned-backend BLAKE3 compression `.s` for the bench.
    The orchestrator runs this (`lake env lean --run`) to produce the file the
    Makefile assembles + KATs against the official BLAKE3 vectors. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/blake3_compare/gen"
  IO.FS.writeFile "bench/blake3_compare/gen/blake3_compress.s" blake3CompressAsm
  IO.println "wrote bench/blake3_compare/gen/blake3_compress.s (owned x86 scalar backend, #573)"

end CatCrypt.Crypto.BLAKE3.CompressEmit
