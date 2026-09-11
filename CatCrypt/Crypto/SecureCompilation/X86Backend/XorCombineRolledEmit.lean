/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-!
# Byte-wise XOR combine as a rolled `ComL.forLoopN` (3-pointer dual-input map)

The canonical stream-cipher / AES-CTR **keystream-combine** leaf:
```
out[i] = a[i] ^ b[i];   for i in 0 .. N
```
(e.g. ciphertext `= plaintext ⊕ keystream`, or the AES-CTR / ChaCha20 XOR step).
This is the **dual-input single-index array-map** leaf: each iteration reads
*two* input elements at the same runtime index `i` (one from each input array)
and writes *one* output element at `i`.

## Exercises the multi-binder loop's TWO-invariant-base path

Where `EncodeRolledEmit` / `DecodeRolledEmit` thread a *single* input array
(one invariant base + an in-body `2i`/`2i+1` access), this kernel threads **two**
invariant array bases through `ComL.forLoopN`'s `invTys` — the first use of the
multi-binder loop's multi-base path for an emitted leaf. The `JLoopBodyN` body
runs over `accTy :: .reg 64 :: [stackArr 8 N, stackArr 8 N]`: the accumulator
(output array), the `.reg 64` loop index `i`, and the two input bases `a`, `b`.
Each base gets a synthetic `CMP Lctr, base` live-range touch so the linear scan
pins both input pointers in fixed registers across the whole loop. One body copy
lowers to a rolled two-`LOADIDX` / one-`STOREIDX` SIB loop with a real
`jne .L<d>` back-edge.

The body, per trip `i`:

* `av := stackLoad a[i]`     (`reg 8`)
* `bv := stackLoad b[i]`     (`reg 8`)
* `x  := av ^^^ bv`          (`regArith .xor 8`)
* `acc := stackStore out[i] := x` (return the new array)

`ComL.denote` of the loop is the mathematical array map `i ↦ a[i] ^^^ b[i]`
(`xorProg_denote`, proved at a small size by `decide`), and `ComL.toLfundefPhys`
lowers it to ONE rolled body copy in real x86 registers (the `_*Phys_*` evidence
theorems), at a representative size as well as the small instance — the loop is
rolled, never unrolled. The exported function has the 3-pointer ABI
`xor_combine(out, a, b)` (`RDI = out`, `RSI = a`, `RDX = b`). Because XOR is
commutative the result is independent of the `a`/`b` ↔ `RSI`/`RDX` assignment,
so the byte-KAT passes regardless of which physical pointer holds which input.

The orchestrator emits the `.s` from `xorProgReal` (`ComL.writeLprogPhysAbiFile
… "xor_combine" "a2" ["a1","a0"] … ["RDI","RSI","RDX"] [64,64,64]`) and byte-KATs
against an independent `out[i] = a[i] ^ b[i]` reference.
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.XorCombineRolledEmit

set_option autoImplicit false

/-! ## The XOR-combine loop body (shared, parametric in the array size) -/

/-- The dual-input map body `out[i] := a[i] ^^^ b[i]` over the multi-binder
    context `[accTy = stackArr 8 N, idx = reg 64, a = stackArr 8 N, b = stackArr 8 N]`.
    Two distinct `LOADIDX ·[i*1]` byte loads (one per input base), an `xor`, and
    one `STOREIDX out[i*1]`. -/
def xorBody (N : Nat) :
    Com jasminDialect [.stackArr 8 N, .reg 64, .stackArr 8 N, .stackArr 8 N] (.stackArr 8 N) :=
  -- Γ0 = [acc, idx, a, b];  idx = .there .here,  a = .there^2 .here,  b = .there^3 .here
  -- v0 := av = stackLoad a[idx]
  .var (.mk (.stackLoad 8 N) rfl
        (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- Γ1 = [av, acc, idx, a, b];  b = .there^4 .here,  idx = .there^2 .here
  -- v1 := bv = stackLoad b[idx]
  (.var (.mk (.stackLoad 8 N) rfl
        (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there .here)) .nil)))
  -- Γ2 = [bv, av, acc, idx, a, b];  av = .there .here,  bv = .here
  -- v2 := x = av ^^^ bv
  (.var (.mk (.regArith .xor 8) rfl (.cons (.there .here) (.cons .here .nil)))
  -- Γ3 = [x, bv, av, acc, idx, a, b];  acc = .there^3 .here,  idx = .there^4 .here,  x = .here
  -- v3 := stackStore acc[idx] := x
  (.var (.mk (.stackStore 8 N) rfl
        (.cons (.there (.there (.there .here)))
          (.cons (.there (.there (.there (.there .here))))
            (.cons .here .nil))))
  (.ret .here))))

/-- The `N`-trip multi-binder XOR-combine loop. -/
def xorLoop (N : Nat) : JLoopBodyN (.stackArr 8 N) [.stackArr 8 N, .stackArr 8 N] :=
  ⟨N, xorBody N⟩

/-- The exported program: seed the accumulator from `out` (`.here`), thread `a`
    (`.there .here`) and `b` (`.there^2 .here`) as the two invariant bases, loop
    `N` times, return the combined array. Three-pointer ABI:
    `xor_combine(out, a, b)`. -/
def xorProg (N : Nat) :
    ComL [.stackArr 8 N, .stackArr 8 N, .stackArr 8 N] (.stackArr 8 N) :=
  .forLoopN (xorLoop N) .here
    (.cons (.there .here) (.cons (.there (.there .here)) .nil)) (.ret .here)

/-! ## Denote = the XOR-combine spec (small instance, by `decide`) -/

/-- A small instance: `N = 6`. -/
abbrev sN : Nat := 6

/-- Deterministic sample inputs. -/
def sampleA : Fin sN → BitVec 8 := fun i => BitVec.ofNat 8 ((i.val * 53 + 11) &&& 0xFF)
def sampleB : Fin sN → BitVec 8 := fun i => BitVec.ofNat 8 ((i.val * 17 + 3) &&& 0xFF)

/-- **Denote = XOR-combine spec.** The rolled loop denotes `out[i] = a[i] ^ b[i]`
    at every output index (`stackGet` is the dialect's total array read). -/
theorem xorProg_denote :
    (ComL.denote (xorProg sN)
        (.cons (fun _ => (0 : BitVec 8)) (.cons sampleA (.cons sampleB .nil))))
      = (fun i => stackGet sampleA i.val ^^^ stackGet sampleB i.val) := by
  funext i; revert i; decide

/-! ## Rolled lowering with real registers — small instance -/

/-- The physical (post-RA) lowered body of the small-instance XOR-combine loop. -/
def xorPhysBody : Lcmd := (ComL.toLfundefPhys (xorProg sN)).lfd_body

/-- **Two indexed loads IN one rolled body copy:** exactly TWO `LOADIDX` ops —
    the `a[i]` and `b[i]` SIB byte loads — and the loop is rolled (two loads
    total, not `2·N` unrolled). -/
theorem xorPhysBody_two_indexed_loads :
    (xorPhysBody.filter (fun i => match i.li_i with
      | .Lopn _ "LOADIDX" _ => true | _ => false)).length = 2 := by native_decide

/-- **Single indexed store:** exactly one `STOREIDX out[i]` per body copy. -/
theorem xorPhysBody_one_indexed_store :
    (xorPhysBody.filter (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" _ => true | _ => false)).length = 1 := by native_decide

/-- **Real back-edge + label:** the physical body has both an internal `Llabel`
    and a `Lcond` (`jne .L<d>`) — a genuine rolled loop. -/
theorem xorPhysBody_has_backedge :
    xorPhysBody.any (fun i => match i.li_i with | .Lcond _ _ => true | _ => false) = true ∧
    xorPhysBody.any (fun i => match i.li_i with | .Llabel _ _ => true | _ => false) = true :=
  ⟨by native_decide, by native_decide⟩

/-- **Every physical body operand is a real x86 register** — no leftover SSA name
    that the owned printer would render as `%<UNKNOWN>`. (Immediates and the `NZ`
    flag are excluded.) -/
theorem xorPhysBody_all_real_registers :
    xorPhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- **No SSA names survive in the SIB operands either:** every `LOADIDX`/`STOREIDX`
    SIB base and index in the physical body is a real x86 register (both input
    bases and the output base are pinned). -/
theorem xorPhysBody_sib_real_registers :
    xorPhysBody.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts ++ srcs).all (fun o => match o with
            | .arrIdx b idx _ => isRealGPName b && isRealGPName idx
            | _ => true)
      | _ => true) = true := by native_decide

/-! ## Representative size: the actual emitted leaf -/

/-- A representative AES-block-multiple size (`N = 64`, one cache line / four
    AES blocks). The orchestrator may instantiate any `N`. -/
abbrev pN : Nat := 64

/-- **The actual emitted leaf:** the XOR-combine loop at the representative size.
    The orchestrator writes its `.s` via `ComL.writeLprogPhysAbiFile … "xor_combine"
    "a2" ["a1","a0"] … ["RDI","RSI","RDX"] [64,64,64]` and byte-KATs against an
    independent `out[i] = a[i] ^ b[i]` reference. -/
def xorProgReal : ComL [.stackArr 8 pN, .stackArr 8 pN, .stackArr 8 pN] (.stackArr 8 pN) :=
  xorProg pN

/-- The full-size physical body. -/
def xorPhysBodyReal : Lcmd := (ComL.toLfundefPhys xorProgReal).lfd_body

/-- **Still rolled at the representative size:** exactly two `LOADIDX` (the loop is
    NOT unrolled 64×), one `STOREIDX`. -/
theorem xorPhysBodyReal_two_indexed_loads :
    (xorPhysBodyReal.filter (fun i => match i.li_i with
      | .Lopn _ "LOADIDX" _ => true | _ => false)).length = 2 := by native_decide

theorem xorPhysBodyReal_one_indexed_store :
    (xorPhysBodyReal.filter (fun i => match i.li_i with
      | .Lopn _ "STOREIDX" _ => true | _ => false)).length = 1 := by native_decide

/-- **All real x86 registers at the representative size** — the emitted `.s` has no
    `%<UNKNOWN>` SSA leftover. -/
theorem xorPhysBodyReal_all_real_registers :
    xorPhysBodyReal.all (fun i =>
      match i.li_i with
      | .Lopn dsts _ srcs =>
          (dsts.filterMap LOperand.regName?).all isRealGPName &&
          (srcs.filterMap LOperand.regName?).all isRealGPName
      | _ => true) = true := by native_decide

/-- Write the rolled physical-register `.s` blob for the orchestrator. Symbol
    `xor_combine`, 3-pointer ABI (`RDI = out`, `RSI = a`, `RDX = b`). -/
def writeEmit (path : System.FilePath) : IO Unit :=
  ComL.writeLprogPhysAbiFile xorProgReal "xor_combine" "a2" ["a1", "a0"] path
    (fun _ => none) (fun _ => none) ["RDI", "RSI", "RDX"] [64, 64, 64]

end CatCrypt.Crypto.SecureCompilation.X86Backend.XorCombineRolledEmit
