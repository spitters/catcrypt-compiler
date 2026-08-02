/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

/-!
# OWNED AES-128-CTR whole `.s` emit on the UNIFIED `Com jasminDialect`

`Aes128CtrEmit.lean` emits the AES-NI AES-128-CTR keystream generator
(MAYO's `PK_PRF = AES_128_CTR`, `aes128ctr.c`'s `AES_128_CTR_NI`) through the
**bespoke** `Vec128`/`VCryptOp` crypto-SIMD IR: its AES key schedule
(`VAESKEYGENASSIST` + `VPSHUFD $0xff` + `VPSLLDQ` / `VPXOR` mix) and the 4-wide /
1-wide ECB bodies (`VPXOR` whitening, `VAESENC` rounds, `VAESENCLAST`) are
`List VCryptOp` lowered by `Vec128Lowering` and printed by
`Vec128AsmPrinter.renderVCryptInst`.

This module re-authors the SAME whole emit on the **unified** stack

```
Com jasminDialect  (vsimd fragment)  ──renderVsimdCom──▶  AT&T .s lines
```

with **zero** dependency on `Vec128Lowering` / `Vec128Model` / `Vec128AsmPrinter`.
The only crypto-SIMD import is `VIR.VsimdAsmPrint` (the committed owned AT&T
renderer, whose `.vaesenc`/`.vaesenclast`/`.vaeskeygen`/`.vpshufd`/`vpslldq`/
`.bitwise .xor` arms are byte-identical to `renderVCryptInst`).

## The AES round semantics, dialect-native

Each AES op rides `JasminOp.vsimd (op : SimdOp)`:

| bespoke `VCryptOp`     | unified `SimdOp`        | denote                  |
|------------------------|-------------------------|-------------------------|
| `.aesenc`              | `vsimd .vaesenc`        | `wAESENCW`              |
| `.aesenclast`          | `vsimd .vaesenclast`    | `wAESENCLASTW`          |
| `.aeskeygen rcon`      | `vsimd (.vaeskeygen rcon)` | `wAESKEYGENASSISTW`  |
| `.shufd _ 0xFF`        | `vsimd (.vpshufd 0xFF)` | `wVPSHUFDW`             |
| `.slldq n`             | `vpslldq n`             | byte left-shift         |
| `.xorq`                | `vsimd (.bitwise .xor)` | `^^^`                   |

The `SimdOp` AES denotes (`wAESENCW`/… in `JasminDialect`) are the
verbatim-copied bespoke `Vec128Model.vaesenc`/… (= the carried
`Jasmin.wAESENC` / FIPS-197 / Sail-x86 anchor), so the migrated kernel computes
the SAME AES as the bespoke `aesCtrBlk`.

## What is emitted

`aes128_ctr_owned(out=%rdi, outlen=%rsi, key=%rdx, keylen=%rcx)` (with the WEAK
`AES_128_CTR_owned` drop-in alias), written to the SAME path
`bench/aes_compare/gen/aes128_ctr_owned.s` as the bespoke driver, with the SAME
export symbol. The verified key schedule and the 4-wide / 1-wide ECB bodies are now
rendered by `renderVsimdCom` (the owned AT&T `vsimd` printer); the CTR
sequencing (the +1 increment, the loop, the in-register `VPSHUFB` byteswap, the
tail copy) is the SAME straight-line ABI glue as the bespoke driver.

## Status

Each crypto Com program is pinned `denote = spec` by a whole-program `rfl`
(unfolding the `Com`/`Expr` smart constructors resolves the `vsimd`/`vpslldq`
denote arms to the same `wAESENC`/`wAESKEYGENASSIST`/`^^^` fold the bespoke
`aesCtrBlk` threads through `evalVCryptInst`). The round keys `rk0..rk10` and
lane states `st0..st3` are pinned to the SAME XMM slots as the bespoke
`aesCtrAlloc` (`rk_r ↦ %xmm_r`, `st_l ↦ %xmm(11+l)`, `ctrmask ↦ %xmm15`). The
structural `strContains` smoke pins match the bespoke driver's. The acceptance
gate is the `aes128_ctr_owned_kat.c` NIST SP 800-38A / FIPS-197 KAT re-run on the
new `.s`, NOT a byte-diff. Fully proved, no new axiom.

Invoke:  lake env lean --run
         CatCrypt/Crypto/SecureCompilation/X86Backend/Aes128CtrVsimdEmit.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Aes128CtrVsimdEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint

/-! ## 1. `Expr` smart-constructors for the AES `vsimd` fragment -/

/-- `r128` abbreviation. -/
abbrev r128 : JasminTy := .reg 128

/-- `vaesenc(state, rk)` Expr at two source vars. -/
private def eAesenc {Γ : Ctxt jasminDialect} (vs vk : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd .vaesenc) rfl (.cons vs (.cons vk .nil))

/-- `vaesenclast(state, rk)` Expr at two source vars. -/
private def eAesenclast {Γ : Ctxt jasminDialect} (vs vk : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd .vaesenclast) rfl (.cons vs (.cons vk .nil))

/-- `vaeskeygenassist(src, rcon)` Expr at one source var (UNARY; `rcon` baked). -/
private def eAeskeygen {Γ : Ctxt jasminDialect} (rcon : BitVec 8)
    (vsrc : Ctxt.Var Γ r128) : Expr jasminDialect Γ r128 :=
  .mk (.vsimd (.vaeskeygen rcon)) rfl (.cons vsrc .nil)

/-- `vpshufd(src, imm)` Expr at one source var (UNARY; `imm` baked). -/
private def eShufd {Γ : Ctxt jasminDialect} (imm : Nat) (vsrc : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd (.vpshufd imm)) rfl (.cons vsrc .nil)

/-- `xorq` (whole-128 bitwise xor) Expr at two source vars. -/
private def eXor {Γ : Ctxt jasminDialect} (va vb : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vsimd (.bitwise .xor)) rfl (.cons va (.cons vb .nil))

/-- `slldq n` (128-bit byte left-shift) Expr at one source var. -/
private def eSll {Γ : Ctxt jasminDialect} (n : Nat) (va : Ctxt.Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  .mk (.vpslldq n) rfl (.cons va .nil)

/-- De Bruijn shift-by-one (weaken under one fresh binding). -/
private abbrev shift1 {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (v : Ctxt.Var Γ t) : Ctxt.Var (s :: Γ) t := .there v

/-! ## 2. The AES round constants (FIPS-197) -/

/-- The 10 AES-128 round constants. -/
def aesRcon : List Nat := [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]

/-! ## 3. One key-expand round as a `Com` program

`keyExpandRoundCom rcon` takes the previous round key `kPrev` (`#0`) and computes
`rk = AES-NI key-expand round`, mirroring the bespoke `keyExpandRoundBlk`:

```
t1 = aeskeygenassist(kPrev, rcon)
t1 = vpshufd(t1, 0xFF)
t2 = slldq(kPrev, 4)
k  = kPrev ⊕ t2
t2 = slldq(k, 4)
k  = k ⊕ t2
t2 = slldq(k, 4)
k  = k ⊕ t2
k  = k ⊕ t1
```

The single output `rk` is the head of the returned program. -/

/-- The key-expand round input context: `[kPrev]` (`reg 128`). -/
abbrev keCtx : Ctxt jasminDialect := [r128]

/-- One AES-128 key-expand round over `[kPrev]`, `kPrev = #0`. The spec value is
    `keyExpandRoundSpec`. -/
def keyExpandRoundCom (rcon : Nat) : Com jasminDialect keCtx r128 :=
  -- b0  t1 = aeskeygenassist(kPrev, rcon)        ; kPrev=#0
  .var (eAeskeygen (BitVec.ofNat 8 rcon) .here)
  -- b1  t1 = vpshufd(t1, 0xFF)                   ; t1=#0
  (.var (eShufd 0xFF .here)
  -- b2  t2 = slldq(kPrev, 4)                     ; kPrev=#2
  (.var (eSll 4 (.there (.there .here)))
  -- b3  k  = kPrev ⊕ t2                          ; kPrev=#3 ; t2=#0
  (.var (eXor (.there (.there (.there .here))) .here)
  -- b4  t2 = slldq(k, 4)                         ; k=#0
  (.var (eSll 4 .here)
  -- b5  k  = k ⊕ t2                              ; k=#1 ; t2=#0
  (.var (eXor (.there .here) .here)
  -- b6  t2 = slldq(k, 4)                         ; k=#0
  (.var (eSll 4 .here)
  -- b7  k  = k ⊕ t2                              ; k=#1 ; t2=#0
  (.var (eXor (.there .here) .here)
  -- b8  k  = k ⊕ t1                              ; k=#0 ; t1=#6 (= the broadcast
  --     `vpshufd` result, binding b1)
  (.var (eXor .here (.there (.there (.there (.there (.there (.there .here)))))))
  (.ret .here)))))))))

/-! ## 4. The key-expand round spec -/

/-- The GF value the bespoke `keyExpandRoundBlk` computes: the AES-NI key-expand
    round on `kPrev` with round constant `rcon`. -/
def keyExpandRoundSpec (rcon : Nat) (kPrev : BitVec 128) : BitVec 128 :=
  let t1  := wAESKEYGENASSISTW kPrev (BitVec.ofNat 8 rcon)
  let t1' := wVPSHUFDW t1 0xFF
  let t2a := kPrev <<< (4 * 8)
  let k0  := kPrev ^^^ t2a
  let t2b := k0 <<< (4 * 8)
  let k1  := k0 ^^^ t2b
  let t2c := k1 <<< (4 * 8)
  let k2  := k1 ^^^ t2c
  k2 ^^^ t1'

/-- A concrete valuation builder for `keCtx`. -/
def keVal (kPrev : BitVec 128) : Ctxt.Valuation keCtx := .cons kPrev .nil

set_option maxRecDepth 100000 in
/-- **Key-expand round denotation pin.** -/
theorem keyExpandRoundCom_denote (rcon : Nat) (kPrev : BitVec 128) :
    (keyExpandRoundCom rcon).denote (keVal kPrev) = keyExpandRoundSpec rcon kPrev := by
  simp only [keyExpandRoundCom, keyExpandRoundSpec, keVal, eAeskeygen, eShufd,
    eSll, eXor]
  rfl

/-! ## 5. The 1-wide ECB body as a `Com` program

`ecbCom` takes the counter block `ctr` (`#0`) and the 11 round keys
`rk0..rk10` (`#1 … #11`), and computes one AES-128-ECB block:

```
st = ctr ⊕ rk0
for i = 1..9: st = aesenc(st, rk_i)
st = aesenclast(st, rk10)
```

mirroring the bespoke `aes128Ecb1Blk`. -/

/-- The ECB input context: `[ctr, rk0, rk1, …, rk10]` (12 × `reg 128`).
    `ctr = #0`, `rk0 = #1`, …, `rk10 = #11`. -/
abbrev ecbCtx : Ctxt jasminDialect :=
  [r128, r128, r128, r128, r128, r128, r128, r128, r128, r128, r128, r128]

/-- One AES-128-ECB block over `ecbCtx = [ctr, rk0, …, rk10]`:
    `st = ctr ⊕ rk0`, 9 `aesenc(st, rk_i)`, one `aesenclast(st, rk10)`. The single
    output `st` is the head of the returned program. Each binding pushes one fresh
    `r128`, so the running `st` is always `.here`. After `k` bindings `ctr` sits at
    depth `k` and `rk_i` at depth `k + i + 1` (de Bruijn nests written inline). -/
def ecbCom : Com jasminDialect ecbCtx r128 :=
  -- b0  st = ctr ⊕ rk0        ; ctr=#0 ; rk0=#1
  .var (eXor .here (.there .here))
  -- b1  st = aesenc(st, rk1)  ; st=#0 ; rk1=#3 (= k1 + i1 + 1 = 1+1+1)
  (.var (eAesenc .here (.there (.there (.there .here))))
  -- b2  st = aesenc(st, rk2)  ; rk2 at depth 2+2+1 = 5
  (.var (eAesenc .here (.there (.there (.there (.there (.there .here))))))
  -- b3  st = aesenc(st, rk3)  ; rk3 at depth 3+3+1 = 7
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there .here))))))))
  -- b4  st = aesenc(st, rk4)  ; rk4 at depth 4+4+1 = 9
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
  -- b5  st = aesenc(st, rk5)  ; rk5 at depth 5+5+1 = 11
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
  -- b6  st = aesenc(st, rk6)  ; rk6 at depth 6+6+1 = 13
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
  -- b7  st = aesenc(st, rk7)  ; rk7 at depth 7+7+1 = 15
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
  -- b8  st = aesenc(st, rk8)  ; rk8 at depth 8+8+1 = 17
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))
  -- b9  st = aesenc(st, rk9)  ; rk9 at depth 9+9+1 = 19
  (.var (eAesenc .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))
  -- b10 st = aesenclast(st, rk10) ; rk10 at depth 10+10+1 = 21
  (.var (eAesenclast .here (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))
  (.ret .here)))))))))))

/-! ## 6. The ECB spec -/

/-- The AES-128-ECB value the bespoke `aes128Ecb1Blk` computes on counter block
    `ctr` and round keys `rk`. -/
def ecbSpec (ctr : BitVec 128) (rk : Nat → BitVec 128) : BitVec 128 :=
  let s0 := ctr ^^^ rk 0
  let s1 := wAESENCW s0 (rk 1)
  let s2 := wAESENCW s1 (rk 2)
  let s3 := wAESENCW s2 (rk 3)
  let s4 := wAESENCW s3 (rk 4)
  let s5 := wAESENCW s4 (rk 5)
  let s6 := wAESENCW s5 (rk 6)
  let s7 := wAESENCW s6 (rk 7)
  let s8 := wAESENCW s7 (rk 8)
  let s9 := wAESENCW s8 (rk 9)
  wAESENCLASTW s9 (rk 10)

/-- A concrete valuation builder for `ecbCtx` from `ctr` and the 11 round keys. -/
def ecbVal (ctr : BitVec 128) (rk : Nat → BitVec 128) : Ctxt.Valuation ecbCtx :=
  .cons ctr (.cons (rk 0) (.cons (rk 1) (.cons (rk 2) (.cons (rk 3) (.cons (rk 4)
    (.cons (rk 5) (.cons (rk 6) (.cons (rk 7) (.cons (rk 8) (.cons (rk 9)
    (.cons (rk 10) .nil)))))))))))

set_option maxRecDepth 100000 in
/-- **ECB denotation pin.** -/
theorem ecbCom_denote (ctr : BitVec 128) (rk : Nat → BitVec 128) :
    ecbCom.denote (ecbVal ctr rk) = ecbSpec ctr rk := by
  simp only [ecbCom, ecbSpec, ecbVal, eXor, eAesenc, eAesenclast]
  rfl

/-! ## 7. Pinning the round keys / lane states to fixed XMM slots

The CTR loop holds the 11 round keys and (up to 4) lane states live across
iterations, so they are pinned to fixed XMM registers — the SAME assignment as
the bespoke `aesCtrAlloc` (`allocXmmCrypto aesCtrReserved …`):
`rk_r ↦ %xmm_r` (`r = 0..10`), `st_l ↦ %xmm(11+l)` (`l = 0..3`),
`ctrmask ↦ %xmm15`. The key-schedule scratch reuses the lane-0/lane-1 state
registers (`%xmm11`/`%xmm12`), exactly as the bespoke `t1Reg`/`t2Reg`. -/

/-- `%xmmN`. -/
def xmmName (i : Nat) : String := "%xmm" ++ toString i

/-- The fixed register for round key `rk_r` (`r = 0..10`): `%xmm_r`. -/
def rkXmm (r : Nat) : String := xmmName r

/-- The fixed register for lane state `st_l` (`l = 0..3`): `%xmm(11+l)`. -/
def stXmm (l : Nat) : String := xmmName (11 + l)

/-- The persistent byteswap-mask register (`%xmm15`). -/
def ctrMaskXmm : String := xmmName 15

/-! ### Key-schedule round rendering

`keyExpandRoundCom rcon` has params `p0 = kPrev` and SSA temps `v0..v8`. We pin
`p0 ↦ rk_{r-1}` and the result/scratch as in the bespoke `keyExpandRoundBlk`:
the four `k` values (`v3/v5/v7/v8`, all in place) ↦ `rk_r`; the broadcast `t1`
(`v0/v1`) ↦ the lane-0 scratch `%xmm11`; the shifted `t2` (`v2/v4/v6`) ↦ the
lane-1 scratch `%xmm12`. The result name `v8` lands at `rk_r`. -/

/-- The XMM allocation for the `r`-th key-expand round (`1 ≤ r ≤ 10`): input
    `kPrev = rk_{r-1}`, output + the four in-place `k` temps → `rk_r`, the
    `aeskeygen`/`vpshufd` broadcast `t1` (`v0/v1`) → `%xmm11`, the byte-shift `t2`
    (`v2/v4/v6`) → `%xmm12`. -/
def keyRoundAlloc (r : Nat) : XAlloc :=
  [ ("p0", rkXmm (r - 1)),
    ("v0", xmmName 11), ("v1", xmmName 11),                 -- t1 (keygen, shufd)
    ("v2", xmmName 12),                                      -- t2 (slldq)
    ("v3", rkXmm r),                                         -- k = kPrev ⊕ t2
    ("v4", xmmName 12),                                      -- t2 (slldq)
    ("v5", rkXmm r),                                         -- k ⊕= t2
    ("v6", xmmName 12),                                      -- t2 (slldq)
    ("v7", rkXmm r),                                         -- k ⊕= t2
    ("v8", rkXmm r) ]                                        -- k ⊕= t1 (result)

/-- The rendered AT&T lines for the `r`-th key-expand round. -/
def keyRoundLines (rcon r : Nat) : List String :=
  (renderVsimdCom (keyRoundAlloc r) (keyExpandRoundCom rcon)).1

/-- The whole AES-128 key schedule, rendered once (rounds 1..10), `rk0` seeded by
    the caller from the key pointer. -/
def keyScheduleLines : List String :=
  (aesRcon.zipIdx).flatMap (fun (rcon, i) => keyRoundLines rcon (i + 1))

/-! ### ECB body rendering

`ecbCom` has params `p0 = ctr`, `p1..p11 = rk0..rk10`, and SSA temps `v0..v10`
(the running state). For lane `l`, we pin `p0 ↦ st_l` and every `v{n} ↦ st_l`
(the in-place chain stays in the lane's register), and `p_{i+1} ↦ rk_i`. -/

/-- The XMM allocation for the ECB body of lane `l`: counter/state in `st_l`,
    round keys in their fixed slots. The 11 in-place SSA temps all map to `st_l`. -/
def ecbLaneAlloc (l : Nat) : XAlloc :=
  [ ("p0", stXmm l) ] ++
  ((List.range 11).map (fun i => ("p" ++ toString (i + 1), rkXmm i))) ++
  ((List.range 11).map (fun n => ("v" ++ toString n, stXmm l)))

/-- The rendered AT&T lines for the ECB body of lane `l` (11 lines: 1 whiten,
    9 `vaesenc`, 1 `vaesenclast`). -/
def ecbLaneLines (l : Nat) : List String :=
  (renderVsimdCom (ecbLaneAlloc l) ecbCom).1

/-- The 4-wide interleaved ECB body: the four lanes' 11-line bodies zipped
    round-by-round (instruction `k` of each lane in turn) so the scheduler sees
    four independent `vaesenc` chains in flight — the AES-NI throughput path,
    structurally matching the bespoke `aes128Ecb4Blk` interleave. Each lane body
    has the same length (11), so the transpose is total. -/
def ecb4Lines : List String :=
  let lanes := (List.range 4).map ecbLaneLines
  (List.range 11).flatMap (fun k => lanes.map (fun body => body[k]!))

/-- The 1-wide (tail) ECB body: lane 0's serial 11-line chain. -/
def ecb1Lines : List String :=
  ecbLaneLines 0

/-! ## 8. The CTR sequencing / ABI glue (straight-line, same as the bespoke driver)

The counter sequencing (the +1 increment, the loop, the in-register `VPSHUFB`
byteswap, the tail copy) is the SAME straight-line ABI glue as
`Aes128CtrEmit`. The counter is kept in the GP register `%r8`; each lane's
XMM counter block is built register-to-register (`vmovq %r8 → st_l`,
`vpslldq $8`, the verified `VPSHUFB` byteswap against `ctrmask`). -/

/-- The byteswap-mask bytes (little-endian), `set_epi8(8,9,…,15, 7,6,…,0)`:
    byte `i` = `i` for `i < 8` (low-lane identity), `23 - i` for `8 ≤ i < 16`
    (high-lane reversed). -/
def ctrMaskBytes : List Nat :=
  (List.range 16).map (fun i => if i < 8 then i else 23 - i)

/-- Emit the byteswap-mask setup: write the 16 mask bytes to the red zone and
    load them into `ctrmask` (once, before the CTR loop). -/
def ctrMaskSetupLines : String :=
  let stores := String.join (ctrMaskBytes.zipIdx.map (fun (b, i) =>
    "\tmovb\t$" ++ toString b ++ ", -" ++ toString (16 - i) ++ "(%rsp)\n"))
  stores ++ "\tvmovdqu\t-16(%rsp), " ++ ctrMaskXmm ++ "\n"

/-- The verified `vpshufb st_l, st_l, ctrmask` byteswap line, rendered through the
    owned `vsimd` printer (the `.vpshufb` arm — byte-identical to the bespoke
    `renderVCryptInst`). Big-endian byteswap of the counter into AES-input layout. -/
def ctrByteswapLine (l : Nat) : String :=
  renderVsimdInstr [] .vpshufb (stXmm l) (stXmm l) ctrMaskXmm

/-- Build the big-endian counter block for `%r8 + delta` into `st_l`, in register
    (no red-zone round-trip): counter into the low 64-bit lane (`vmovq`), shift to
    the high lane (`vpslldq $8`), then the verified `VPSHUFB` byteswap. -/
def loadCtrLane (l delta : Nat) : String :=
  let seed :=
    if delta = 0 then "\tvmovq\t%r8, " ++ stXmm l ++ "\n"
    else
      "\tleaq\t" ++ toString delta ++ "(%r8), %r11\n" ++
      "\tvmovq\t%r11, " ++ stXmm l ++ "\n"
  seed ++
  "\tvpslldq\t$8, " ++ stXmm l ++ ", " ++ stXmm l ++ "\n" ++
  ctrByteswapLine l ++ "\n"

/-! ## 9. The emitted `.s` text (owned backend, SysV ABI)

`aes128_ctr_owned(out=%rdi, outlen=%rsi, key=%rdx, keylen=%rcx)` — the exact
`AES_128_CTR` signature MAYO's `PK_PRF` calls, with the WEAK
`AES_128_CTR_owned` drop-in alias. The crypto bodies (key schedule, 4-wide /
1-wide ECB) are the verified Com-rendered lines; the loop/ABI glue is the
straight-line counter sequencing. -/

/-- The emitted `aes128_ctr_owned` function text. The CTR loop is 4-wide
    (interleaved, the AES-NI throughput path) with a 1-wide tail and a byte-copy
    for a partial final block. -/
def aesCtrExportAsm : String :=
  let ks   := String.intercalate "\n" keyScheduleLines
  let ecb4 := String.intercalate "\n" ecb4Lines
  let ecb1 := String.intercalate "\n" ecb1Lines
  let loadLanes := String.join ((List.range 4).map (fun l => loadCtrLane l l))
  "\t.att_syntax\n" ++
  "\t.text\n" ++
  "\t.p2align\t5\n" ++
  "\t.global\taes128_ctr_owned\n" ++
  "\t.type\taes128_ctr_owned, %function\n" ++
  "\t.weak\tAES_128_CTR_owned\n" ++
  "\t.type\tAES_128_CTR_owned, %function\n" ++
  "AES_128_CTR_owned:\n" ++
  "aes128_ctr_owned:\n" ++
  -- args: out=%rdi outlen=%rsi key=%rdx keylen=%rcx
  "\tvmovdqu\t(%rdx), " ++ rkXmm 0 ++ "\n" ++         -- rk0 = key
  ks ++ "\n" ++                                         -- verified key schedule
  ctrMaskSetupLines ++                                  -- ctrmask = BE byteswap mask
  "\txorq\t%r8, %r8\n" ++                               -- counter = 0 (LE GP int)
  "\tmovq\t%rdi, %r9\n" ++                              -- out cursor
  "\tmovq\t%rsi, %r10\n" ++                             -- remaining bytes
  -- ===== 4-wide fast path (64 bytes / iter) =====
  ".Laesctr_loop4:\n" ++
  "\tcmpq\t$64, %r10\n" ++
  "\tjb\t.Laesctr_tail1\n" ++
  loadLanes ++                                          -- st0..st3 = ctr blocks
  ecb4 ++ "\n" ++                                       -- 4 interleaved AES-128 chains
  "\tvmovdqu\t" ++ stXmm 0 ++ ", (%r9)\n" ++
  "\tvmovdqu\t" ++ stXmm 1 ++ ", 16(%r9)\n" ++
  "\tvmovdqu\t" ++ stXmm 2 ++ ", 32(%r9)\n" ++
  "\tvmovdqu\t" ++ stXmm 3 ++ ", 48(%r9)\n" ++
  "\taddq\t$64, %r9\n" ++
  "\tsubq\t$64, %r10\n" ++
  "\taddq\t$4, %r8\n" ++                                -- counter += 4
  "\tjmp\t.Laesctr_loop4\n" ++
  -- ===== 1-wide tail (16 bytes / iter) =====
  ".Laesctr_tail1:\n" ++
  "\ttestq\t%r10, %r10\n" ++
  "\tjz\t.Laesctr_done\n" ++
  loadCtrLane 0 0 ++                                    -- st0 = counter block
  ecb1 ++ "\n" ++                                       -- 1 AES-128 chain
  "\tcmpq\t$16, %r10\n" ++
  "\tjb\t.Laesctr_partial\n" ++
  "\tvmovdqu\t" ++ stXmm 0 ++ ", (%r9)\n" ++
  "\taddq\t$16, %r9\n" ++
  "\tsubq\t$16, %r10\n" ++
  "\taddq\t$1, %r8\n" ++
  "\tjmp\t.Laesctr_tail1\n" ++
  -- ===== partial final block: byte-copy %r10 (< 16) bytes =====
  ".Laesctr_partial:\n" ++
  "\tvmovdqu\t" ++ stXmm 0 ++ ", -16(%rsp)\n" ++
  "\tleaq\t-16(%rsp), %r11\n" ++
  ".Laesctr_partialcopy:\n" ++
  "\ttestq\t%r10, %r10\n" ++
  "\tjz\t.Laesctr_done\n" ++
  "\tmovb\t(%r11), %al\n" ++
  "\tmovb\t%al, (%r9)\n" ++
  "\tincq\t%r11\n" ++
  "\tincq\t%r9\n" ++
  "\tdecq\t%r10\n" ++
  "\tjmp\t.Laesctr_partialcopy\n" ++
  ".Laesctr_done:\n" ++
  "\txorl\t%eax, %eax\n" ++
  "\tmovl\t%esi, %eax\n" ++                             -- return (int)outlen
  "\tret\n"

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println aesCtrExportAsm

/-! ## 10. Structural smoke pins (matching the bespoke driver) -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/-- The export entry point is present. -/
theorem asm_has_export :
    strContains aesCtrExportAsm "aes128_ctr_owned:" = true := by native_decide

/- The drop-in (weak) `AES_128_CTR_owned` symbol is exported. -/
#guard (strContains aesCtrExportAsm "\t.weak\tAES_128_CTR_owned\n")

/- The AES-128 key schedule is emitted (`VAESKEYGENASSIST` + `VPSHUFD $255`),
    lowercase owned mnemonics. -/
#guard (strContains aesCtrExportAsm "vaeskeygenassist")
    && (strContains aesCtrExportAsm "vpshufd $255")

/- The AES-128-ECB body is emitted: the `VAESENC` rounds and the final
    `VAESENCLAST`. -/
#guard (strContains aesCtrExportAsm "vaesenc ") && (strContains aesCtrExportAsm "vaesenclast ")

/- The CTR loop is emitted: the 4-wide fast path, the 1-wide tail, and the
    in-register counter byteswap (`VPSHUFB` against `ctrmask = %xmm15`) — no GP
    red-zone round-trip. -/
#guard (strContains aesCtrExportAsm ".Laesctr_loop4:")
    && (strContains aesCtrExportAsm ".Laesctr_tail1:")
    && (strContains aesCtrExportAsm "vpshufb ")
    && (strContains aesCtrExportAsm "vmovq\t%r8, ")

/- The counter path is fully in-register: no `bswapq`/red-zone counter trip
    (the byteswap moved to the verified `VPSHUFB`). -/
#guard !(strContains aesCtrExportAsm "bswapq")

/- No register name escaped allocation (the 11 round keys + 4 states + ctrmask
    fit in 16 XMM, no spill). -/
#guard !(strContains aesCtrExportAsm "UNALLOCATED")

/- No UPPERCASE jasmin intrinsic survives — the owned (no-jasminc)
    lowercase-mnemonic path. -/
#guard !(strContains aesCtrExportAsm "VAESENC")
    && !(strContains aesCtrExportAsm "VAESKEYGENASSIST")

/-! ## 11. Emit driver -/

/-- Write the owned-backend `.s` to `bench/aes_compare/gen/aes128_ctr_owned.s`
    (the SAME path + symbol as the bespoke driver). -/
def emit : IO Unit := do
  let path := "bench/aes_compare/gen/aes128_ctr_owned.s"
  IO.FS.writeFile path aesCtrExportAsm
  IO.println s!"wrote {path}"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Aes128CtrVsimdEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Aes128CtrVsimdEmit in
/-- `lake env lean --run` entry point: emit the owned-backend AES-128-CTR `.s`
    on the unified `Com jasminDialect`. `private` so it does not collide with
    other `main`s in the `EmitAll` rot-guard aggregator. -/
private def main : IO Unit := emit
