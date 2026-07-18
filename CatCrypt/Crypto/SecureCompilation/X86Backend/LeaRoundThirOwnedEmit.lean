/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirOwnedEmit

/-!
# LEA block-cipher encryption round through the OWNED x86 backend (no jasminc)

The LEA (KISA Korean national standard, ISO/IEC 29192-2) encryption round is a
pure ARX (XOR+Add+Rotate) word function over four `u32` state words
`(X0, X1, X2, X3)` and six per-round subkeys `(RK0..RK5)` (eprint 2026/1177
§2.2):

    X0' = ROL((X0 ⊕ RK0) ⊞ (X1 ⊕ RK1), 9)
    X1' = ROR((X1 ⊕ RK2) ⊞ (X2 ⊕ RK3), 5)
    X2' = ROR((X2 ⊕ RK4) ⊞ (X3 ⊕ RK5), 3)
    X3' = X0

`⊞` is wrapping `u32` add, `⊕` XOR, ROL/ROR rotate. Each round is independent
across blocks — the SIMD-parallel CTR core the paper packs 16 blocks into one
ZMM register. Here we emit the SCALAR round (the value-correct on-ramp): four
single-output leaves through the SAME `Com[thir] → lowerThir → toLprogPhysAbi →
renderLprogAtt` spine as the ChaCha20 quarter-round, NO jasminc.

`ROL(x,n)` is rendered as `x.rotateRight (32 - n)` (the `thRor (32 - n)` front
encoding); `ROR(x,n)` is `thRor n` directly.

Input file (10 words, all `reg 32`):
`[X0, X1, X2, X3, RK0, RK1, RK2, RK3, RK4, RK5]`, so de Bruijn:
`X0=0, X1=1, X2=2, X3=3, RK0=4, …, RK5=9`.

## What is verified vs trusted

* **Verified (value)**: `lea*Thir_denote` — each leaf denotes its `leaRoundSpec`
  component on every `BitVec 32` valuation (by `rfl`/`simp [rotateRight]`).
* **Verified (printer)**: `leaRoundOwnedAsm_shape` pins the four SysV leaf labels
  and the no-unhandled-op sentinel in the emitted `.s`.
* **Trusted (thin)**: `renderLfundef` / `as` / the SysV leaf ABI frame.

The byte-identity to the KISA official test vector is the external `as`/`cc` KAT
in `bench/lea_lsh_compare/` (driver runs all 24 rounds + key schedule in C and
checks the published LEA-128 vector).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LeaRoundThirOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (lowerThir thirDialect ThirOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ChaChaQRThirOwnedEmit
  (legalizeShiftImmLprog hasSub)

/-! ## 1. The LEA round reference spec over `BitVec 32` -/

/-- The LEA encryption round (ISO/IEC 29192-2 / eprint 2026/1177 §2.2) over four
    `BitVec 32` state words and six round-key words, returning `(X0',X1',X2',X3')`.
    `ROL(x,n) = x.rotateRight (32 - n)`, `ROR(x,n) = x.rotateRight n`. -/
def leaRoundSpec (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  let x0' := ((x0 ^^^ rk0) + (x1 ^^^ rk1)).rotateRight (32 - 9)
  let x1' := ((x1 ^^^ rk2) + (x2 ^^^ rk3)).rotateRight 5
  let x2' := ((x2 ^^^ rk4) + (x3 ^^^ rk5)).rotateRight 3
  -- X3' = X0 (the OLD first word), per ISO/IEC 29192-2.
  (x0', x1', x2', x0)

/-! ## 2. The four single-output LEA-round leaves (`Com thirDialect`)

The input context is the 10 words `[X0,X1,X2,X3,RK0,RK1,RK2,RK3,RK4,RK5]`. Each
leaf builds the minimal SSA for its output and ends with an identity copy
(`thRor 32 0`) of that word so the register-arith emit reads it back as the
result (same convention as `qrBody`). -/

private abbrev LeaCtx : Ctxt thirDialect :=
  [.reg 32, .reg 32, .reg 32, .reg 32, .reg 32,
   .reg 32, .reg 32, .reg 32, .reg 32, .reg 32]

-- de-Bruijn variable helpers into `LeaCtx` (newest binding = `.here`). Since each
-- leaf starts from the 10-word input file we name the input positions explicitly.

/-- LEA round `X0'` output: `ROL((X0⊕RK0)⊞(X1⊕RK1), 9)`.
    Bindings (head-first after build): out, r, s, t1, t0; with X0=dB4..,
    here-relative once locals stack. We build bottom-up. -/
def leaX0Thir : Com thirDialect LeaCtx (.reg 32) :=
  -- t0 = X0 ^ RK0 :  X0 = dB 0, RK0 = dB 4
  .var (.mk (.thBin .xor 32) rfl (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)))
  -- t1 = X1 ^ RK1 :  now X1 = dB 2, RK1 = dB 6 (one local pushed)
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- s = t0 + t1 :  t1 = dB 0, t0 = dB 1
  (.var (.mk (.thBin .add 32) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r = ror 23 s   (= rol 9) :  s = dB 0
  (.var (.mk (.thRor 32 (32 - 9)) rfl (.cons .here .nil))
  -- out = ror 0 r  (identity copy)
  (.var (.mk (.thRor 32 0) rfl (.cons .here .nil))
  (.ret .here)))))

/-- LEA round `X1'` output: `ROR((X1⊕RK2)⊞(X2⊕RK3), 5)`.
    X1 = dB1, RK2 = dB6; after one local is pushed X2 = dB3, RK3 = dB8. Both
    XORs read two raw ABI inputs directly; the allocator gives same-site
    operands distinct registers (pinned by `leaX1_reloads_distinct`). -/
def leaX1Thir : Com thirDialect LeaCtx (.reg 32) :=
  -- t0 = X1 ^ RK2 :  X1 = dB 1, RK2 = dB 6
  .var (.mk (.thBin .xor 32) rfl
      (.cons (.there .here)
        (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)))
  -- t1 = X2 ^ RK3 :  X2 = dB 3 (one local pushed), RK3 = dB 8
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  -- s = t0 + t1 :  t0 = dB 1, t1 = dB 0
  (.var (.mk (.thBin .add 32) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r = ror 5 s
  (.var (.mk (.thRor 32 5) rfl (.cons .here .nil))
  (.var (.mk (.thRor 32 0) rfl (.cons .here .nil))
  (.ret .here)))))

/-- LEA round `X2'` output: `ROR((X2⊕RK4)⊞(X3⊕RK5), 3)`.
    X2 = dB2, RK4 = dB8, X3 = dB3, RK5 = dB9. -/
def leaX2Thir : Com thirDialect LeaCtx (.reg 32) :=
  -- t0 = X2 ^ RK4 :  X2 = dB 2, RK4 = dB 8
  .var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there .here))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))
  -- t1 = X3 ^ RK5 :  X3 = dB 4, RK5 = dB 10
  (.var (.mk (.thBin .xor 32) rfl
      (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))
  -- s = t0 + t1
  (.var (.mk (.thBin .add 32) rfl (.cons (.there .here) (.cons .here .nil)))
  -- r = ror 3 s
  (.var (.mk (.thRor 32 3) rfl (.cons .here .nil))
  (.var (.mk (.thRor 32 0) rfl (.cons .here .nil))
  (.ret .here)))))

/-- LEA round `X3'` output: `X3` (just a copy of the input X0 — wait, X3' = X0). -/
def leaX3Thir : Com thirDialect LeaCtx (.reg 32) :=
  -- out = ror 0 X0  (X3' = X0, identity copy of input X0 = dB 0)
  .var (.mk (.thRor 32 0) rfl (.cons .here .nil))
  (.ret .here)

/-! ## 3. Value-correctness: each leaf denotes its `leaRoundSpec` component -/

/-- Denotation input HVector packing the 10 LEA-round words. -/
private def leaInp (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    HVector (fun t => ⟦t⟧) LeaCtx :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons rk0
    (.cons rk1 (.cons rk2 (.cons rk3 (.cons rk4 (.cons rk5 .nil)))))))))

theorem leaX0Thir_denote (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    leaX0Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = (leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).1 := by
  have e : leaX0Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = ((leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

theorem leaX1Thir_denote (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    leaX1Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = (leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.1 := by
  have e : leaX1Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = ((leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

theorem leaX2Thir_denote (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    leaX2Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = (leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.2.1 := by
  have e : leaX2Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = ((leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.2.1).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

theorem leaX3Thir_denote (x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5 : BitVec 32) :
    leaX3Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = (leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.2.2 := by
  have e : leaX3Thir.denote (leaInp x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5)
      = ((leaRoundSpec x0 x1 x2 x3 rk0 rk1 rk2 rk3 rk4 rk5).2.2.2).rotateRight 0 := rfl
  rw [e]; simp [BitVec.rotateRight_def]

/-! ## 4. The owned `Lprog` and AT&T emission (no jasminc)

ABI: 2-pointer SysV (`RDI` = out, `RSI` = inp). The 10 inputs are loaded from
`[RSI + 8*i]` (8-byte-strided slots, matching the chacha leaf's `uint64_t inp[]`
harness layout); the single output stored to `out[0]`. Arg slot `s` ↦ input index
`(10 - 1 - s) = 9 - s`, so `inLoadMap s = ("RSI", 8 * (9 - s))`. -/

/-- Input-load map for the 10-in / 1-out width-32 LEA-round leaves:
    arg slot `s` ↦ `("RSI", 8 * (9 - s))` for `s < 10`, else absent. -/
def leaInLoadMap : InLoadMap := fun s =>
  if s < 10 then some ("RSI", 8 * (9 - s)) else none

/-- Output-store map: the single result word stored to `out[0]`. -/
def leaOutStoreMap : OutStoreMap := [("RDI", 0)]

/-- Lower one LEA-round leaf through the thirDialect spine to a physical SysV
    `Lprog`, then shift/rotate-immediate-legalise for the owned printer. -/
def leaOwnedLprog (com : Com thirDialect LeaCtx (.reg 32)) (fname : String) : Lprog :=
  legalizeShiftImmLprog
    (Com.toLprogPhysAbi (lowerThir com) fname
      (fun _ => none) (fun _ => none)
      leaInLoadMap leaOutStoreMap
      ["RDI", "RSI"]
      [32, 32, 32, 32, 32, 32, 32, 32, 32, 32])

def leaX0OwnedLprog : Lprog := leaOwnedLprog leaX0Thir "lea_round_x0"
def leaX1OwnedLprog : Lprog := leaOwnedLprog leaX1Thir "lea_round_x1"
def leaX2OwnedLprog : Lprog := leaOwnedLprog leaX2Thir "lea_round_x2"
def leaX3OwnedLprog : Lprog := leaOwnedLprog leaX3Thir "lea_round_x3"

/-- All four LEA-round leaves gathered into ONE `Lprog`. -/
def leaRoundOwnedLprog : Lprog :=
  { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
    lp_funcs := leaX0OwnedLprog.lp_funcs ++ leaX1OwnedLprog.lp_funcs
                ++ leaX2OwnedLprog.lp_funcs ++ leaX3OwnedLprog.lp_funcs }

/-- The rendered owned-backend AT&T `.s` for the four LEA-round leaves. -/
def leaRoundOwnedAsm : String := renderLprogAtt leaRoundOwnedLprog

/-- The emitted `.s` carries all four SysV leaf labels and no unhandled-op
    sentinel. -/
theorem leaRoundOwnedAsm_shape :
    hasSub leaRoundOwnedAsm "lea_round_x0"
      ∧ hasSub leaRoundOwnedAsm "lea_round_x1"
      ∧ hasSub leaRoundOwnedAsm "lea_round_x2"
      ∧ hasSub leaRoundOwnedAsm "lea_round_x3"
      ∧ hasSub leaRoundOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 4b. Regression: same-site ABI-input reloads land in distinct registers

`leaX1Thir` is the leaf shape whose binops read two raw single-use ABI inputs
each (`X1⊕RK2`, `X2⊕RK3`). If the exporter's register allocation ever placed
the two operands of one binop on the same physical register — e.g. via a stale
`bodyNameInfo` name table, where every unknown name collapses onto the
out-of-universe sentinel slot (see `bodyNameInfoCacheRef`) — the two use-site
reloads would clobber each other and `X2 ^ RK3` would silently compute
`X2 ^ X2`. The shape theorem below pins, on the emitted four-leaf `Lprog`
(the same value `leaRoundOwnedAsm` renders), that each XOR's two input reloads
target distinct registers. -/

/-- The destination register of the unique ABI-input reload `MOV dst, [R14+off]`
    in a function body (`none` if absent or not unique). -/
def reloadDstFor (body : Lcmd) (off : Nat) : Option String :=
  match body.filterMap (fun i =>
    match i.li_i with
    | .Lopn [.reg d] _ [.reg src] =>
        if src == memName reloadScratch2 off then some d else none
    | _ => none) with
  | [d] => some d
  | _ => none

/-- The emitted `lea_round_x1` body inside the four-leaf `Lprog`. -/
def leaRoundX1Body : Lcmd :=
  match leaRoundOwnedLprog.lp_funcs.find? (fun p => p.1 == "lea_round_x1") with
  | some (_, f) => f.lfd_body
  | none => []

/-- Each XOR of the `lea_round_x1` leaf reloads its two raw ABI inputs into
    **distinct** physical registers: `X1`/`RK2` (offsets 8/48) and `X2`/`RK3`
    (offsets 16/56). A same-register pair would make the first reload dead and
    the binop degenerate to `x ^ x`. -/
theorem leaX1_reloads_distinct :
    ((reloadDstFor leaRoundX1Body 16).isSome
      ∧ (reloadDstFor leaRoundX1Body 56).isSome
      ∧ reloadDstFor leaRoundX1Body 16 ≠ reloadDstFor leaRoundX1Body 56)
    ∧ ((reloadDstFor leaRoundX1Body 8).isSome
      ∧ (reloadDstFor leaRoundX1Body 48).isSome
      ∧ reloadDstFor leaRoundX1Body 8 ≠ reloadDstFor leaRoundX1Body 48) := by
  native_decide

/-! ## 5. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/lea_lsh_compare/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/lea_round_owned.s") leaRoundOwnedAsm
  IO.println "WROTE bench/lea_lsh_compare/gen/lea_round_owned.s"
  IO.println "  (LEA encryption round leaves lea_round_{x0,x1,x2,x3} through"
  IO.println "   Com[thir] -> lowerThir -> toLprogPhysAbi -> renderLprogAtt onto the"
  IO.println "   OWNED x86 backend, NO jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.LeaRoundThirOwnedEmit
