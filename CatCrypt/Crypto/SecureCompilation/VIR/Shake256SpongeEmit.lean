/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront

/-!
# Owned variable-length SHAKE256 sponge over the owned Keccak-f[1600] permutation

The owned Keccak emit (`bench/keccak_compare/gen/keccak_f1600_resident.s`) exposes
the bare 25-lane permutation `keccak_f1600_resident(out u64[25], inp u64[25])`
(FIPS-202 KAT'd). What every PQC whole-protocol (ML-DSA, SLH-DSA, MAYO, HAWK, UOV,
ML-KEM) still needs around it — and what their C glue still supplies — is the
FIPS-202 **rate management**: the multi-block absorb loop, the `pad10*1` domain
pad, and the multi-block squeeze loop. `SDitH/ShakeEmit.lean` already emits a
*single-block, fixed-length* SHAKE128 sponge; this module closes the remaining
residual by emitting the **variable-length** SHAKE256 sponge — a bounded
absorb loop + byte-granular tail + pad + squeeze loop — as a hand-built owned
`Lcmd`, exactly the way `ShakeEmit`'s `shakeBody` composes the marshalling
around a `call keccak_f1600_resident`: buffer marshalling owned, the round
arithmetic is the called permutation leaf, NOT re-implemented.

SHAKE256 has rate `r = 136` bytes (17 lanes), capacity `c = 512` bits; the
1600-bit state is 25 u64 lanes. The emitted routine implements, for any input
length `inlen` and output length `outlen`:

* zero the 200-byte state (25 lanes);
* **absorb loop** (top-tested `while inlen >= 136`): XOR the 17 rate words of the
  current input block into state lanes `0..16`, permute in place, advance the
  input pointer by 136, subtract 136 from `inlen`;
* **final block** (`inlen < 136` bytes): a byte loop XORs the `inlen` remaining
  bytes into the state buffer, then `pad10*1` with the SHAKE domain suffix —
  `state[inlen] ^= 0x1f` and `state[135] ^= 0x80` — then permute in place;
* **squeeze loop** (`while outlen > 0`): copy `min(outlen,136)` state bytes to the
  output, and if more is needed permute in place between blocks.

This is byte-identical to the FIPS-202 SHAKE256 sponge (the same algorithm the
`bench/keccak_compare/keccak_kat.c` C `sponge()` runs over the permutation), now
with the rate-management loop ITSELF emitted as owned x86 — so the whole
`SHAKE256(input) -> output` is one owned artifact, permutation plus rate
management, with no rate-management C glue on the artifact path.

## ABI

`void shake256(uint8_t *out, size_t outlen, const uint8_t *in, size_t inlen)`
(SysV: `out → RDI`, `outlen → RSI`, `in → RDX`, `inlen → RCX`). The four ABI
values are parked in callee-saved registers (`RBX`/`R12`/`R13`/`R14`) that survive
the permutation calls; the 200-byte state lives in the routine's own frame. The
permutation is called in place (`RDI = RSI = &state`), matching the `ShakeEmit`
single-block leaf (the resident permute reads its 25 input lanes before writing,
so the in-place alias is value-exact).

SHAKE128 (rate 168 = 21 lanes, same `0x1f`/`0x80` pad) is the trivial rate
variant: identical structure with `rate = 168`, `rateWords = 21`. Only SHAKE256
is emitted here (the ML-DSA / SLH-DSA rate variant) to demonstrate; the rate is a
single parameter.

Invoke:  lake env lean --run bench/keccak_compare/shake256_sponge_owned_emit.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLprogAtt)

/-! ## 0. Substring helper -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 1. Small `Lcmd` builders (mirrors `SDitH/ShakeEmit`) -/

/-- A 64-bit register-to-register / immediate move `d := s`. -/
def movR (d : String) (s : LOperand) : Linstr := ⟨0, .Lopn [.reg d] "MOV:64" [s]⟩

/-- A 64-bit two-address binop `d := d OP s`. -/
def binR (d op : String) (s : LOperand) : Linstr :=
  ⟨0, .Lopn [.reg d] (op ++ ":64") [.reg d, s]⟩

/-- `leaq off(%base), %d` — the effective address of a frame / pointer slot. -/
def leaR (d base : String) (off : Nat) : Linstr :=
  ⟨0, .Lopn [.reg d] "LEA:64" [.reg (memName base off)]⟩

/-- A word load `d := [base + off]`. -/
def loadR (d base : String) (off : Nat) : Linstr :=
  ⟨0, .Lopn [.reg d] "LOAD:64" [.reg (memName base off)]⟩

/-- A word store `[base + off] := s`. -/
def storeR (base : String) (off : Nat) (s : String) : Linstr :=
  ⟨0, .Lopn [.reg (memName base off)] "STORE:64" [.reg s]⟩

/-- A 64-bit XOR into a memory word `[base + off] ^= s`. -/
def xorMemR (base : String) (off : Nat) (s : String) : Linstr :=
  ⟨0, .Lopn [.reg (memName base off)] "XOR:64" [.reg (memName base off), .reg s]⟩

/-- A byte load (zero-extended) `d := (u8)[base + off]`. -/
def loadB (d base : String) (off : Nat) : Linstr :=
  ⟨0, .Lopn [.reg d] "MOV:8" [.reg (memName base off)]⟩

/-- A 8-bit XOR into a memory byte `[base + off] ^= s` (low byte of `s`). -/
def xorMemB (base : String) (off : Nat) (s : String) : Linstr :=
  ⟨0, .Lopn [.reg (memName base off)] "XOR:8" [.reg (memName base off), .reg s]⟩

/-- A byte store `[base + off] := (u8)s`. -/
def storeB (base : String) (off : Nat) (s : String) : Linstr :=
  ⟨0, .Lopn [.reg (memName base off)] "MOV:8" [.reg s]⟩

/-- A `call` to an intra-object or inter-object leaf symbol. -/
def callR (sym : String) : Linstr := ⟨0, .Lcall none (sym, 0)⟩

/-- An explicit frame-size directive (`renderLfundef.frameSize` reads it). -/
def frameR (bytes : Nat) : Linstr := ⟨0, .Lopn [] "FRAME" [.imm bytes]⟩

/-- A loop-top internal label. -/
def labelR (l : Nat) : Linstr := ⟨0, .Llabel .internal l⟩

/-- An unconditional jump to internal label `l`. -/
def gotoR (l : Nat) : Linstr := ⟨0, .Lgoto ("", l)⟩

/-- A conditional jump `j<cc> .L<l>`. -/
def condR (cc : String) (l : Nat) : Linstr := ⟨0, .Lcond (.reg cc) l⟩

/-! ## 2. The owned permutation leaf symbol + rate parameters -/

/-- The emitted owned Keccak-f[1600] permutation leaf
    (`bench/keccak_compare/gen/keccak_f1600_resident.s`,
    `keccak_f1600_resident(out u64[25], inp u64[25])`). The sponge `call`s it. -/
def permSym : String := "keccak_f1600_resident"

/-- SHAKE256 rate in bytes (`1088 / 8 = 136`). -/
def rate : Nat := 136
/-- SHAKE256 rate in 64-bit lanes (`136 / 8 = 17`). -/
def rateWords : Nat := 17
/-- SHAKE domain suffix byte for the `pad10*1` (`0x1f`). -/
def dsByte : Nat := 0x1f
/-- The high pad bit `0x80` at the last rate byte. -/
def padBit : Nat := 0x80

/-! ## 3. Frame layout -/

/-- 200-byte (25-lane) Keccak state at frame offset 8 (a word above `%rsp`). -/
def stateOff : Nat := 8
/-- Frame for the sponge: 200-byte state at `stateOff = 8` (`8..207`). 256 bytes
    keeps `%rsp` 16-aligned at the inner `call keccak_f1600_resident` after the
    printer's callee-save pushes and the `leaq -frame`. -/
def spongeFrame : Nat := 264

/-! ## 4. The `shake256` body -/

/-- Internal loop labels. -/
def absorbTop : Nat := 0
def absorbDone : Nat := 1
def tailTop : Nat := 2
def tailDone : Nat := 3
def tailBody : Nat := 14
def squeezeTop : Nat := 4
def squeezeDone : Nat := 5
def squeezeMore : Nat := 6

/-- Zero the 25 state lanes (RAX = 0 scratch). -/
def zeroState : Lcmd :=
  (movR "RAX" (.imm 0))
    :: (List.range 25).map (fun i => storeR "RSP" (stateOff + 8 * i) "RAX")

/-- One absorb iteration: XOR the 17 rate words `[R13 + 8i]` into state lanes
    `0..16`, permute in place, advance `R13 += 136`, `R14 -= 136`. `R13` is the
    moving input pointer, `R14` the remaining byte count. -/
def absorbBody : Lcmd :=
  ((List.range rateWords).flatMap (fun i =>
      [ loadR "RAX" "R13" (8 * i)
      , xorMemR "RSP" (stateOff + 8 * i) "RAX" ]))
  ++ [ leaR "RDI" "RSP" stateOff
     , leaR "RSI" "RSP" stateOff
     , callR permSym
     , binR "R13" "ADD" (.imm rate)
     , binR "R14" "SUB" (.imm rate) ]

/-- The top-tested absorb loop `while (R14 >= 136) { absorbBody }`. -/
def absorbLoop : Lcmd :=
  [ labelR absorbTop
  , binR "R14" "CMP" (.imm rate)        -- compare remaining vs rate
  , condR "B" absorbDone ]              -- jb done  (unsigned <)
  ++ absorbBody
  ++ [ gotoR absorbTop
     , labelR absorbDone ]

/-- The byte-granular tail absorb + `pad10*1`.

    `R14` holds the remaining byte count `inlen < 136`; `R13` the input tail
    pointer. A byte loop XORs the `R14` remaining bytes into the state buffer at a
    moving state-byte pointer `R15`, decrementing a counter `RCX`. Then the pad:
    `state[inlen] ^= 0x1f` (via the now-advanced `R15`, which points at
    `&state + inlen`) and `state[135] ^= 0x80`, then permute in place. -/
def tailAbsorb : Lcmd :=
  -- R15 := &state ; RCX := remaining count (R14)
  [ leaR "R15" "RSP" stateOff
  , movR "RCX" (.reg "R14")
  -- top-tested byte loop: while RCX != 0 { state[*] ^= in[*]; ++ptrs; --RCX }
  , labelR tailTop
  , binR "RCX" "CMP" (.imm 0)
  , condR "NZ" tailBody             -- count != 0 → run a byte; else fall to done
  , gotoR tailDone
  , labelR tailBody
  , loadB "RAX" "R13" 0             -- al = in[i]  (zero-extended)
  , xorMemB "R15" 0 "RAX"           -- state[i] ^= al
  , binR "R13" "ADD" (.imm 1)       -- ++in_ptr
  , binR "R15" "ADD" (.imm 1)       -- ++state_ptr
  , binR "RCX" "SUB" (.imm 1)       -- --count
  , gotoR tailTop
  , labelR tailDone ]
  -- pad10*1 with the SHAKE domain suffix:
  --   R15 now points at &state + inlen  →  state[inlen] ^= 0x1f
  ++ [ movR "RAX" (.imm dsByte)
     , xorMemB "R15" 0 "RAX"
  --   state[135] ^= 0x80  (last rate byte)
     , movR "RAX" (.imm padBit)
     , xorMemB "RSP" (stateOff + (rate - 1)) "RAX"
  -- permute in place
     , leaR "RDI" "RSP" stateOff
     , leaR "RSI" "RSP" stateOff
     , callR permSym ]

/-- Squeeze a single block of `min(R12, rate)` bytes, then decide whether to
    permute. Implemented with a byte copy loop bounded by a running counter `RCX`
    that is set to `min(R12, rate)` via a forward skip. -/
def squeezeBlock : Lcmd :=
  [ labelR squeezeTop
  -- if R12 == 0, done
  , binR "R12" "CMP" (.imm 0)
  , condR "NZ" squeezeMore
  , gotoR squeezeDone
  , labelR squeezeMore
  -- RCX := min(R12, rate):  RCX = rate; if R12 < rate then RCX = R12
  , movR "RCX" (.imm rate)
  , binR "R12" "CMP" (.imm rate)
  , condR "AE" 9            -- R12 >= rate → keep RCX = rate, skip the override
  , movR "RCX" (.reg "R12")
  , labelR 9
  -- save the block size for the post-copy R12 decrement
  , movR "R9" (.reg "RCX")
  -- RDX := &state read pointer
  , leaR "RDX" "RSP" stateOff
  -- copy loop: while RCX != 0 { out[*] = state[*]; ++ptrs; --RCX }
  , labelR 10
  , binR "RCX" "CMP" (.imm 0)
  , condR "NZ" 11
  , gotoR 12
  , labelR 11
  , loadB "RAX" "RDX" 0
  , storeB "RBX" 0 "RAX"
  , binR "RBX" "ADD" (.imm 1)
  , binR "RDX" "ADD" (.imm 1)
  , binR "RCX" "SUB" (.imm 1)
  , gotoR 10
  , labelR 12
  -- R12 -= blockSize (R9)
  , binR "R12" "SUB" (.reg "R9")
  -- if R12 == 0 done, else permute and loop
  , binR "R12" "CMP" (.imm 0)
  , condR "NZ" 13
  , gotoR squeezeDone
  , labelR 13
  , leaR "RDI" "RSP" stateOff
  , leaR "RSI" "RSP" stateOff
  , callR permSym
  , gotoR squeezeTop
  , labelR squeezeDone ]

/-- Body of `shake256(out → RDI, outlen → RSI, in → RDX, inlen → RCX)`. -/
def shake256Body : Lcmd :=
  [ frameR spongeFrame
  -- park ABI values in callee-saved regs (survive the permute calls)
  , movR "RBX" (.reg "RDI")          -- RBX := out  (moving output pointer)
  , movR "R12" (.reg "RSI")          -- R12 := outlen (remaining out bytes)
  , movR "R13" (.reg "RDX")          -- R13 := in   (moving input pointer)
  , movR "R14" (.reg "RCX") ]        -- R14 := inlen (remaining in bytes)
  ++ zeroState
  ++ absorbLoop
  ++ tailAbsorb
  ++ squeezeBlock

/-- The `shake256` `Lfundef` (4-pointer/size SysV ABI). -/
def shake256Fundef : Lfundef :=
  { lfd_tyin := [64, 64, 64, 64], lfd_arg := ["RDI", "RSI", "RDX", "RCX"]
    lfd_body := shake256Body
    lfd_tyout := [], lfd_res := [] }

/-! ## 5. The composed SHAKE256 object -/

/-- The owned SHAKE256 sponge in one `.s`. The Keccak-f permutation is an external
    symbol (`keccak_f1600_resident`, linked from the owned Keccak emit). -/
def shake256Funcs : List (String × Lfundef) :=
  [ ("shake256_owned", shake256Fundef) ]

def shake256Lprog : Lprog := { lp_funcs := shake256Funcs }

/-- The owned SHAKE256 sponge `.s` text. -/
def shake256Asm : String := renderLprogAtt shake256Lprog

/-! ## 6. Shape checks (the sponge renders with no unhandled op) -/

/- The sponge renders the absorb word-XORs, the byte-granular tail, the SHAKE
    pad immediates, the `call keccak_f1600_resident` permute, the absorb/squeeze
    back-edges, and no unhandled op. -/
#guard (occursIn "shake256_owned" shake256Asm)
    && (occursIn "call keccak_f1600_resident" shake256Asm)
    && !(occursIn "UNHANDLED" shake256Asm)

/-! ## 7. FRONT: `shake256Body` is the sponge-front schedule's output

The deployed `shake256Body` is RE-SOURCED from the SHAKE256 sponge-front schedule
(`Shake256SpongeFront.shake256Steps`) rendered by `spband 64`: the runtime absorb
loop, the byte-granular tail + `pad10*1`, and the runtime squeeze loop are the
front's `SpStep` schedule — `BStep` control (the `QuerySampleBranchFront`
loop/branch/word-memory core) plus the sponge extras (`FRAME`/`leaq`/back-edge
`goto`/word XOR-into-memory absorb/byte read/byte XOR-into-cell tail/byte copy
store/runtime subtract). The equality below is byte-exact, so the emitted `.s` and
its FIPS-202 SHAKE256 KAT are unchanged. -/

open CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeFront
  (SpongeConfig spband shake256Steps)

/-- The deployed SHAKE256 layout as a front `SpongeConfig` (rate 136 / 17 lanes,
    capacity 512, variable output; state at frame offset 8, `0x1f`/`0x80` pad,
    frame 264) — built from this module's own constants (single source of truth). -/
def spongeCfg : SpongeConfig :=
  { rate := rate, rateWords := rateWords, stateOff := stateOff, dsByte := dsByte
    padBit := padBit, frame := spongeFrame, permSym := permSym
    absorbTop := absorbTop, absorbDone := absorbDone
    tailTop := tailTop, tailDone := tailDone, tailBody := tailBody
    squeezeTop := squeezeTop, squeezeDone := squeezeDone, squeezeMore := squeezeMore }

set_option maxRecDepth 6000 in
/-- **FRONT.** The deployed `shake256Body` is exactly the sponge-front schedule
    rendered by `spband 64` — the runtime absorb loop, the byte tail + pad, and the
    runtime squeeze loop are GENERATED from the `SpStep` schedule, not
    hand-authored. Byte-exact, so `shake256Asm` and its FIPS-202 KAT carry over. -/
theorem shake256Body_front_sourced :
    shake256Body = spband 64 (shake256Steps spongeCfg) := by rfl

/- The front-sourced sponge renders the runtime loops (`jb`/`jne`/`jmp`
    back-edges), the byte-granular tail (`movb`/`xorb`), the SHAKE `pad10*1` at the
    last rate byte (`143(%rsp)` = `stateOff + rate - 1`), and the `call
    keccak_f1600_resident` permute — the full absorb/pad/squeeze owned control. -/
#guard (occursIn "call keccak_f1600_resident" shake256Asm)
    && (occursIn "jmp .Lshake256_owned_0" shake256Asm)
    && (occursIn "xorb %al, (%r15)" shake256Asm)
    && (occursIn "movb %al, (%rbx)" shake256Asm)

end CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeEmit
