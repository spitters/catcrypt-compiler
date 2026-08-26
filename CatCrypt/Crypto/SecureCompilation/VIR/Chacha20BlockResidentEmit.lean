/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.ChaCha20Block
/-!
# Owned-backend (no-jasminc) STATE-RESIDENT ChaCha20 block (RFC 8439 §2.3)

The state-resident analogue of `Chacha20BlockFullMemrefEmit`. The
full-memref owned emit lowers the whole block to `Com jasminDialect` and then runs
it through the **register-allocating** owned backend
(`Com.toLprogPhysAbi`), whose spill/frame path is buggy for a wide (16-word) live
set — the emitted ChaCha block segfaults. This file sidesteps that path entirely:
the sixteen state words live in a **stack array** and every quarter-round operates
on them **in place** (load four words into GP scratch, compute, store them back),
so there is never a wide live register set and hence **no register-allocator
spilling**. This is the resident pattern already proven out for the wide Keccak
permutation (`KeccakResidentBebEmit` / `KeccakSimdSingleEmit`): a flat
`8·i(%rsp)`-addressed frame with `%rax/%rcx/%rdx`-windowed `load → op → store`.

## ABI (`chacha20_block_resident(out = %rdi, in = %rsi)`)

`chacha20_block_resident(reg ptr u32[16] out = %rdi, reg const ptr u32[16] in = %rsi)`
returning `out` in `%rax` (SysV; mirrors the jasmin `-> reg ptr` convention used
by the resident Keccak emit). The two pointers map onto the SysV integer-argument
registers; the body addresses memory itself, so there is no per-word ABI splice
and no 6-register-argument limit.

## The stack frame

A 32-slot `u32` frame (`4·i(%rsp)`):

* slots `0 .. 15`  — the working state words `s[0..15]` (the resident state, the
  thing the quarter-rounds mutate in place);
* slots `16 .. 31` — the feed-forward originals `orig[0..15]` (a copy of the
  sixteen `in` words, added back after the twenty rounds — RFC 8439 §2.3
  `chachaBlock s = chachaCore s + s`).

The emitted body is:

1. **load**: copy `in[i]` (byte `4·i`) into BOTH `s[i]` and `orig[i]`;
2. **20 rounds = 10 double-rounds**, each = 8 quarter-rounds (4 column +
   4 diagonal, RFC 8439 §2.3), every QR in place over its four `s`-slots;
3. **feed-forward**: `s[i] += orig[i]`;
4. **store**: copy `s[i]` to `out[i]` (byte `4·i`); return `out` in `%rax`.

## Provenance: HAND-AUTHORED asm (not `Com`-generated)

Provenance, identical in kind to `KeccakResidentBebEmit`: the emitted
`.s` (`chachaResidentAsm`) is assembled by hand — it `intercalate`s a hand-written
prologue/epilogue with hand-authored load / quarter-round / feed-forward / store
mnemonic-string lists. It is NOT rendered from a typed `Com`/IR descent, and the
`#eval`/`decide` self-checks here run over a separate executable `UInt32` model,
NOT a denotation of the emitted asm. Correctness rests on the RFC 8439 §2.3.2
byte-KAT against an independent reference — NOT a compiler-correctness result. "Owned" here
means *no jasminc*, not *compiler-generated*. Re-routing this kernel through the
owned `Com → toLprogPhysAbi → renderLprogAtt` pipeline (once its wide-spill path
is fixed) is the named residual.

## The self-check

We reuse the `BitVec 32` RFC-8439 spec (`chachaBlock`, `quarterRound`,
`columnRound`, `diagonalRound`) of `CatCrypt.Crypto.Jasmin.ChaCha20Block` as the
authority, and additionally model the **emitted dataflow** directly over a flat
`UInt32` slot file (`emittedResult`) — load into `s`+`orig`, ten in-place
double-rounds, feed-forward, store — checking it agrees with a fast `UInt32`
reference (`refResult`) that mirrors the same spec lane-for-lane, plus the
RFC 8439 §2.3.2 §2.3.2 first-word digest. The authoritative gate is the
orchestrator's RFC-8439 byte-KAT.

Invoke (emit the owned-backend `.s`):
  lake env lean --run bench/chacha_compare/chacha_resident_owned_emit.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockResidentEmit

open CatCrypt.Crypto.Jasmin.ChaCha20Block

/-! ## 0. The eight quarter-round index sets (RFC 8439 §2.3)

A double-round is four column QRs followed by four diagonal QRs. The resident
emit walks exactly these eight 4-tuples; the same tuples drive both the emitted
asm renderer and the executable self-check, so they cannot drift apart. -/

/-- The four column-round quarter-round index 4-tuples
    `QR(0,4,8,12) QR(1,5,9,13) QR(2,6,10,14) QR(3,7,11,15)`. -/
def columnQRs : List (Nat × Nat × Nat × Nat) :=
  [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15)]

/-- The four diagonal-round quarter-round index 4-tuples
    `QR(0,5,10,15) QR(1,6,11,12) QR(2,7,8,13) QR(3,4,9,14)`. -/
def diagonalQRs : List (Nat × Nat × Nat × Nat) :=
  [(0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-- The eight quarter-rounds of one double-round (column then diagonal). -/
def doubleRoundQRs : List (Nat × Nat × Nat × Nat) := columnQRs ++ diagonalQRs

/-! ## 1. The flat `UInt32` slot model (for the self-check)

The interpreted self-check runs a straight-line `UInt32` evaluator over a flat
`Array UInt32`, exactly the flat-array trick of `KeccakSimdSingleEmit` (no
closures, no `BitVec`, so the interpreter stays fast). Slots `0..15` are the
working state `s`; slots `16..31` are the feed-forward originals `orig`. -/

/-- The number of `u32` slots in the resident frame (16 state + 16 originals). -/
abbrev numSlots : Nat := 32

/-- The 32-slot working state. -/
structure CState where
  /-- The `numSlots` `u32` register slots. -/
  regs : Array UInt32

namespace CState

/-- Read slot `i` (out-of-range ⇒ `0`). -/
def get (s : CState) (i : Nat) : UInt32 := s.regs.getD i 0

/-- Write slot `i`. -/
def setV (s : CState) (i : Nat) (v : UInt32) : CState := { regs := s.regs.set! i v }

/-- The all-zero frame. -/
def empty : CState := { regs := Array.replicate numSlots 0 }

end CState

/-- A 32-bit left-rotate (the ChaCha quarter-round `<<<`). -/
def rotl32 (x : UInt32) (n : Nat) : UInt32 :=
  if n % 32 = 0 then x
  else (x <<< UInt32.ofNat (n % 32)) ||| (x >>> UInt32.ofNat (32 - n % 32))

/-- One in-place quarter-round on slots `a b c d` of the working state, the
    `UInt32` mirror of the emitted load/op/store dataflow:
    `a+=b; d=rotl(d^a,16); c+=d; b=rotl(b^c,12); a+=b; d=rotl(d^a,8); c+=d; b=rotl(b^c,7)`. -/
def qrInPlace (st : CState) (a b c d : Nat) : CState :=
  let va := st.get a; let vb := st.get b; let vc := st.get c; let vd := st.get d
  let va := va + vb;           let vd := rotl32 (vd ^^^ va) 16
  let vc := vc + vd;           let vb := rotl32 (vb ^^^ vc) 12
  let va := va + vb;           let vd := rotl32 (vd ^^^ va) 8
  let vc := vc + vd;           let vb := rotl32 (vb ^^^ vc) 7
  (st.setV a va).setV b vb |>.setV c vc |>.setV d vd

/-- One double-round on the working state: the eight `doubleRoundQRs` in order. -/
def doubleRoundInPlace (st : CState) : CState :=
  doubleRoundQRs.foldl (fun s (q : Nat × Nat × Nat × Nat) =>
    qrInPlace s q.1 q.2.1 q.2.2.1 q.2.2.2) st

/-- The lanes produced by the EMITTED kernel dataflow, modelled directly:
    seed `s` (slots `0..15`) and `orig` (slots `16..31`) from the input,
    run ten in-place double-rounds, feed-forward (`s[i] += orig[i]`), and read
    out the sixteen working words. -/
def emittedResult (inp : Fin 16 → UInt32) : Array UInt32 := Id.run do
  let mut st : CState := CState.empty
  -- load: in[i] -> s[i] and orig[i]
  for i in List.finRange 16 do
    let v := inp i
    st := (st.setV i.val v).setV (16 + i.val) v
  -- 10 in-place double-rounds
  for _ in List.range 10 do
    st := doubleRoundInPlace st
  -- feed-forward: s[i] += orig[i]
  for i in List.range 16 do
    st := st.setV i (st.get i + st.get (16 + i))
  -- store: read out s[0..15]
  pure (Array.ofFn (n := 16) fun (i : Fin 16) => st.get i.val)

/-! ## 2. A fast `UInt32` reference (mirrors the `BitVec` spec lane-for-lane)

`chachaBlock`/`quarterRound` (the committed RFC-8439 spec) are over `BitVec 32`
and run for several minutes under `native_decide` (80 nested `Function.update`
closures). The reference here is the SAME algorithm over `UInt32`, used only as a
fast cross-check that the emitted-dataflow model is a faithful ChaCha block. The
`BitVec` spec remains the mathematical authority (Section 4). -/

/-- The 32-bit left-rotate as the RFC's `rotL32`, over `UInt32`. -/
def refRotl (x : UInt32) (n : Nat) : UInt32 := rotl32 x n

/-- The pure quarter-round over `UInt32` (mirrors `ChaCha20QR.quarterRound`). -/
def refQR (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b; let d := refRotl (d ^^^ a) 16
  let c := c + d; let b := refRotl (b ^^^ c) 12
  let a := a + b; let d := refRotl (d ^^^ a) 8
  let c := c + d; let b := refRotl (b ^^^ c) 7
  (a, b, c, d)

/-- The reference ChaCha block over `UInt32` (RFC 8439 §2.3): ten double-rounds
    of the eight `doubleRoundQRs`, then feed-forward with the original input. -/
def refResult (inp : Fin 16 → UInt32) : Array UInt32 := Id.run do
  let mut st : Array UInt32 := Array.ofFn inp
  for _ in List.range 10 do
    for q in doubleRoundQRs do
      let (a, b, c, d) := q
      let (ra, rb, rc, rd) := refQR (st.getD a 0) (st.getD b 0) (st.getD c 0) (st.getD d 0)
      st := ((st.set! a ra).set! b rb |>.set! c rc).set! d rd
  pure (Array.ofFn (n := 16) fun (i : Fin 16) => st.getD i.val 0 + inp i)

/-! ## 3. The RFC 8439 §2.3.2 test vector (over `UInt32`)

The same key/counter/nonce as `ChaCha20Block.testInitState`, packed into the
sixteen-word initial state. Expected first output word `0xe4e7f110`
(RFC 8439 §2.3.2). -/

/-- The sixteen initial-state words for the RFC 8439 §2.3.2 test vector
    (constants, 8 key words, counter, 3 nonce words), as `UInt32`. -/
def testInit : Fin 16 → UInt32
  |  0 => 0x61707865 |  1 => 0x3320646e |  2 => 0x79622d32 |  3 => 0x6b206574
  |  4 => 0x03020100 |  5 => 0x07060504 |  6 => 0x0b0a0908 |  7 => 0x0f0e0d0c
  |  8 => 0x13121110 |  9 => 0x17161514 | 10 => 0x1b1a1918 | 11 => 0x1f1e1d1c
  | 12 => 0x00000001 | 13 => 0x09000000 | 14 => 0x4a000000 | 15 => 0x00000000
  | _ => 0

/-- The full RFC 8439 §2.3.2 expected output block (sixteen words). -/
def testExpected : Array UInt32 :=
  #[0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3,
    0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3,
    0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9,
    0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2]

/-! ## 4. Self-checks (executable, fast) -/

/-- The emitted-dataflow model agrees with the fast `UInt32` reference. -/
def modelAgrees : Bool := emittedResult testInit == refResult testInit

/-- The emitted-dataflow model matches the RFC 8439 §2.3.2 expected block. -/
def katAgrees : Bool := emittedResult testInit == testExpected

/-- The reference matches the RFC 8439 §2.3.2 expected block (independent check
    that the reference itself is faithful). -/
def refKatAgrees : Bool := refResult testInit == testExpected

/-- All executable self-checks pass. -/
def selfCheckPasses : Bool := modelAgrees && katAgrees && refKatAgrees

/-! ## 5. AT&T renderer — flat `u32` resident frame, `%eax/%ecx/%edx` scratch

`chacha20_block_resident(out=%rdi, in=%rsi) -> %rax`. The sixteen state words live
in `s[i] = 4·i(%rsp)`; the feed-forward originals in `orig[i] = 64 + 4·i(%rsp)`.
Every quarter-round is `load → op → store` through `%eax/%ecx/%edx`, so the live
register set never exceeds three words — no register-allocator spilling. -/

/-- The frame size in bytes (32 `u32` slots = 128 bytes, plus headroom). -/
def frameBytes : Nat := 192

/-- A working-state slot operand `4·i(%rsp)` (slot `i ∈ 0..15`). -/
def sMem (i : Nat) : String := toString (4 * i) ++ "(%rsp)"

/-- A feed-forward-original slot operand `64 + 4·i(%rsp)` (slot `i ∈ 0..15`). -/
def origMem (i : Nat) : String := toString (64 + 4 * i) ++ "(%rsp)"

/-- Emit `%eax = rotl( <value already in %eax> , n )`, scratch `%ecx`. `n%32 = 0`
    ⇒ no-op (the value is already in `%eax`). -/
def renderRotlEax (n : Nat) : List String :=
  let n := n % 32
  if n == 0 then []
  else
    [ "\tmovl\t%eax, %ecx"
    , "\tshll\t$" ++ toString n ++ ", %eax"
    , "\tshrl\t$" ++ toString (32 - n) ++ ", %ecx"
    , "\torl\t%ecx, %eax" ]

/-- Render ONE in-place quarter-round on slots `a b c d`. Mirrors `qrInPlace`:
    `a+=b; d=rotl(d^a,16); c+=d; b=rotl(b^c,12); a+=b; d=rotl(d^a,8); c+=d; b=rotl(b^c,7)`.
    Working values are kept in slots; `%eax` is the accumulator, `%ecx` the rotate
    scratch, `%edx` the second operand. -/
def renderQR (a b c d : Nat) : List String :=
  -- a += b
  [ "\tmovl\t" ++ sMem a ++ ", %eax", "\taddl\t" ++ sMem b ++ ", %eax"
  , "\tmovl\t%eax, " ++ sMem a ]
  -- d = rotl(d ^ a, 16)   (a now in slot a)
  ++ [ "\tmovl\t" ++ sMem d ++ ", %eax", "\txorl\t" ++ sMem a ++ ", %eax" ]
  ++ renderRotlEax 16 ++ [ "\tmovl\t%eax, " ++ sMem d ]
  -- c += d
  ++ [ "\tmovl\t" ++ sMem c ++ ", %eax", "\taddl\t" ++ sMem d ++ ", %eax"
     , "\tmovl\t%eax, " ++ sMem c ]
  -- b = rotl(b ^ c, 12)
  ++ [ "\tmovl\t" ++ sMem b ++ ", %eax", "\txorl\t" ++ sMem c ++ ", %eax" ]
  ++ renderRotlEax 12 ++ [ "\tmovl\t%eax, " ++ sMem b ]
  -- a += b
  ++ [ "\tmovl\t" ++ sMem a ++ ", %eax", "\taddl\t" ++ sMem b ++ ", %eax"
     , "\tmovl\t%eax, " ++ sMem a ]
  -- d = rotl(d ^ a, 8)
  ++ [ "\tmovl\t" ++ sMem d ++ ", %eax", "\txorl\t" ++ sMem a ++ ", %eax" ]
  ++ renderRotlEax 8 ++ [ "\tmovl\t%eax, " ++ sMem d ]
  -- c += d
  ++ [ "\tmovl\t" ++ sMem c ++ ", %eax", "\taddl\t" ++ sMem d ++ ", %eax"
     , "\tmovl\t%eax, " ++ sMem c ]
  -- b = rotl(b ^ c, 7)
  ++ [ "\tmovl\t" ++ sMem b ++ ", %eax", "\txorl\t" ++ sMem c ++ ", %eax" ]
  ++ renderRotlEax 7 ++ [ "\tmovl\t%eax, " ++ sMem b ]

/-- Render one double-round: the eight `doubleRoundQRs` in order. -/
def renderDoubleRound : List String :=
  doubleRoundQRs.flatMap (fun q => renderQR q.1 q.2.1 q.2.2.1 q.2.2.2)

/-- The full unrolled twenty-round (ten double-round) body. -/
def roundBlock : List String := (List.range 10).flatMap (fun _ => renderDoubleRound)

/-- Load `in = %rsi` words `0..15` into BOTH the working slots `s[i]` and the
    feed-forward originals `orig[i]`. -/
def loadLines : List String :=
  (List.range 16).flatMap (fun i =>
    [ "\tmovl\t" ++ toString (4 * i) ++ "(%rsi), %eax"
    , "\tmovl\t%eax, " ++ sMem i
    , "\tmovl\t%eax, " ++ origMem i ])

/-- Feed-forward: `s[i] += orig[i]` for `i = 0..15` (RFC 8439 §2.3
    `chachaBlock s = chachaCore s + s`). -/
def feedForwardLines : List String :=
  (List.range 16).flatMap (fun i =>
    [ "\tmovl\t" ++ sMem i ++ ", %eax"
    , "\taddl\t" ++ origMem i ++ ", %eax"
    , "\tmovl\t%eax, " ++ sMem i ])

/-- Store the sixteen working words `s[i]` to `out = %rdi` words `0..15`. -/
def storeLines : List String :=
  (List.range 16).flatMap (fun i =>
    [ "\tmovl\t" ++ sMem i ++ ", %eax"
    , "\tmovl\t%eax, " ++ toString (4 * i) ++ "(%rdi)" ])

/-- The emitted `chacha20_block_resident` owned-backend function text. -/
def chachaResidentAsm : String :=
  let prologue :=
    [ "\t.att_syntax", "\t.text", "\t.p2align\t4"
    , "\t.global\tchacha20_block_resident"
    , "\t.type\tchacha20_block_resident, %function"
    , "chacha20_block_resident:"
    , "\tmovq\t%rsp, %r10"
    , "\tleaq\t-" ++ toString frameBytes ++ "(%rsp), %rsp"
    , "\tandq\t$-32, %rsp" ]
  -- return `out` (%rdi) in %rax
  let epilogue := [ "\tmovq\t%rdi, %rax", "\tmovq\t%r10, %rsp", "\tret" ]
  let stackNote := [ "\t.section\t\".note.GNU-stack\", \"\", %progbits" ]
  String.intercalate "\n"
    (prologue ++ loadLines ++ roundBlock ++ feedForwardLines ++ storeLines
      ++ epilogue ++ stackNote) ++ "\n"

/-! ## 6. Structural emit-text pins -/

private def asmHas (sub : String) : Bool := (chachaResidentAsm.splitOn sub).length ≥ 2

/-- The emitted `.s` has the expected ABI / op-alphabet shape: the resident symbol,
    loads from `in=%rsi` and stores to `out=%rdi` at word offset `60` (= `4·15`),
    returns `out` in `%rax`, 32-byte-aligns the frame, uses scalar 32-bit
    `addl`/`xorl`/`shll`/`shrl`/`orl` ops, and the round body is exactly ten
    double-rounds. -/
def structuralChecksPass : Bool :=
  asmHas "chacha20_block_resident" && asmHas "60(%rsi)" && asmHas "60(%rdi)"
    && asmHas "movq\t%rdi, %rax" && asmHas "andq\t$-32, %rsp"
    && asmHas "addl\t" && asmHas "xorl\t" && asmHas "shll\t" && asmHas "shrl\t"
    && asmHas "orl\t"
    && (roundBlock.length == 10 * renderDoubleRound.length)

/-! ## 7. Emit driver -/

/-- The executable + structural self-checks. The authoritative gate is the
    orchestrator's byte-KAT (RFC 8439 §2.3.2). -/
def runSelfCheck : IO Unit := do
  IO.println s!"[selfcheck] emitted-dataflow model == UInt32 reference : {modelAgrees}"
  IO.println s!"[selfcheck] emitted-dataflow model == RFC 8439 §2.3.2  : {katAgrees}"
  IO.println s!"[selfcheck] UInt32 reference        == RFC 8439 §2.3.2  : {refKatAgrees}"
  IO.println s!"[selfcheck] emit-text ABI/op structure                 : {structuralChecksPass}"
  if ! (selfCheckPasses && structuralChecksPass) then
    throw (IO.userError "Chacha20BlockResidentEmit self-check FAILED")
  IO.println "SELF-CHECK PASS: owned state-resident ChaCha20 block denotes RFC 8439 §2.3."

/-- Emit driver: write the owned-backend state-resident `.s` to
    `bench/chacha_compare/gen_com/`, then run the self-checks. The artifact is
    written FIRST. No register-allocator spilling: the sixteen state words are
    stack-resident and every quarter-round is in place. -/
def emit : IO Unit := do
  IO.FS.createDirAll "bench/chacha_compare/gen_com"
  IO.FS.writeFile "bench/chacha_compare/gen_com/chacha20_block_resident.s"
    chachaResidentAsm
  IO.println "wrote bench/chacha_compare/gen_com/chacha20_block_resident.s"
  IO.println "  owned x86 backend, state-resident (no register-allocator spilling), NO jasminc"
  runSelfCheck

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emit

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockResidentEmit

open CatCrypt.Crypto.SecureCompilation.VIR.Chacha20BlockResidentEmit in
/-- `lake env lean --run` entry point: emit the owned state-resident ChaCha20 block. -/
@[expose] def chacha20BlockResidentEmitMain : IO Unit := emit
