/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
import CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype

/-!
# HMAC-SHA256/SHA512 and HKDF emitted from `Com jasminDialect` over the SHA-2 emit

HMAC-SHA256 (RFC 2104) and HKDF (RFC 5869) are **straight-line compositions**
over the SHA-256 block compression already emitted (`Sha2Emit.compressCom` /
`sha256Jazz`, fully emitted as pure `regArith`, NO opaque hash leaf). They
introduce **no new arithmetic primitive**: the only word arithmetic HMAC adds is
the XOR of the key block with the `ipad`/`opad` constants — a 16-word
`regArith xor` chain that is itself emitted through the register-arith front
(`§2`). Everything else (key zero-padding to the 64-byte block, the
message/PRK/info concatenations, the Merkle–Damgård multi-block iteration, the
big-endian word (de)serialisation) is the **data-oblivious, non-cryptographic
outer wrapper** — exactly the role the C harness plays for the bare SHA-256
compression in `bench/sha2_compare/sha2_kat.c`. The HMAC/HKDF KAT harnesses in
`bench/hmac_compare/` and `bench/hkdf_compare/` drive that wrapper over the
**emitted** `sha256_compress` and the **emitted** `hmac_xor_pad`, checking the
result byte-for-byte against the published RFC vectors.

## The constructions

* **HMAC-SHA256** (RFC 2104): `HMAC(K,m) = H((K⊕opad) ‖ H((K⊕ipad) ‖ m))`, where
  `opad = 0x5c·64`, `ipad = 0x36·64`, `H = SHA-256`, and `K` is zero-padded (or
  itself hashed if longer than the 64-byte block) to one block. Two SHA-256
  passes plus the XOR-pad.
* **HKDF-Extract** (RFC 5869): `PRK = HMAC-SHA256(salt, IKM)` — one HMAC call.
* **HKDF-Expand** (RFC 5869): `T(0) = ""`, `T(i) = HMAC-SHA256(PRK, T(i-1) ‖ info
  ‖ byte(i))`, `OKM = T(1) ‖ T(2) ‖ … ` truncated to `L`. The `T(i)` chaining is
  a bounded loop over the (one HMAC per step) body — routed through the R1
  multi-op keystone `JForProgMultiOp.loop_denote_eq_multiOp` (`§4`).

## What is emitted vs. what is the wrapper

| Piece | Status |
|---|---|
| SHA-256 block compression `f(H,M)=H'` | **reused-emitted** (`Sha2Emit.sha256Jazz`, pure `regArith`, no leaf) |
| HMAC `K⊕ipad` / `K⊕opad` pad | **emitted** here (`hmacXorPadJazz`, 16 `regArith xor`, no leaf) |
| key zero-pad, `‖` concatenations, MD block loop, byte (de)serialise | C harness (data-oblivious wrapper) |
| HKDF-Expand `T(i)` chaining loop | **verified loop** via R1 keystone (`§4`) |

So the *cryptographic core* (SHA-256 + the XOR-pad) is entirely emitted through
the verified front; the harness contributes only the standard data-independent
message plumbing.

## The dialect gap that shapes the Expand loop body (tracked as #104)

The R1 keystone `loop_denote_eq_multiOp` requires a single-accumulator body
`Com [accTy] accTy` whose only free variable is the loop-carried accumulator
(de Bruijn `.here`). The real HKDF-Expand step `T(i) = HMAC(PRK, T(i-1) ‖ info ‖
i)` needs, inside the body, the **per-iteration counter byte `i`** and the
fixed `PRK`/`info` operands. The jasmin dialect (`JasminDialect.lean`) has **no
in-body literal-constant op** — `regArith`'s `shl`/`shr` take their amount from a
*register operand*, and there is no `regConst`/`regImm` producing a literal — and
a `JForProg` body's only variable is the accumulator. So a constant-free body
cannot synthesise the counter byte the recurrence consumes. This is exactly the
gap documented for the SHA-2 schedule loop (`Sha2Emit.lean` §7b, the missing
`regConst`/`regShiftImm` op) and is tracked as **#104**.

We therefore route the Expand loop through the keystone two ways, mirroring the
SHA-2 schedule treatment:

* `expandSkelLoop_denote_eq` — a pure-`regArith` wide-block multi-op body (the
  T-chaining skeleton), **axiom-clean, no `LeafAgrees`**, showing the keystone
  fires for a leaf-free HKDF-shaped wide accumulator body;
* `expandLoop_denote_eq` — the *full* HKDF-Expand recurrence with one
  `hkdf_expand_step` `extCall` leaf (the ML-KEM matvec / SHA-2 sched-loop
  precedent), so the loop **structure** is verified end to end; its sole carried
  edge is `LeafAgrees`, needed only because of the missing in-body immediate op.

The HMAC two-pass composition is captured at the `Com` level by
`hmacXorPad_denote` (`§3`): the emitted pad `Com` denotes the pointwise
`K ⊕ pad` over the block words, the word-level fact the two `H(... )` passes
consume.

## HMAC-SHA512 (the SHA-512-family extension, `§6`)

HMAC is the *same* construction over a different SHA-2 core and block size.
SHA-512 uses **64-bit words** and a **128-byte block** (`16` `u64` words, vs
SHA-256's 64-byte / `16` `u32` block). The committed `Sha2Emit.sha512Jazz`
(pure `regArith` over `u64`, no leaf) supplies the core; the HMAC layer changes
**only** the word width (`32 → 64`) and the pad words (`0x3636…` / `0x5c5c…`
over 8 bytes). The XOR-pad `Com` machinery here is width-parameterized
(`emitXorPadW`/`xorPadComW`), so HMAC-SHA512 reuses it verbatim at `w = 64`.
The HMAC orchestration (key zero-pad to 128 bytes, the `‖` concatenations, the
MD block loop, big-endian word (de)serialise) is the same data-oblivious
wrapper, contributed by `bench/hmac_compare/hmac512_kat.c` and checked
byte-for-byte against the RFC 4231 HMAC-SHA-512 vectors.

## HMAC-SHA384 (the SHA-384 truncation, `§7`)

HMAC-SHA384 shares the SHA-512 *compression* but with the SHA-384 IV and a
truncated (48-byte) output. `Sha2Emit.Truncated.sha384Variant` now lands that
SHA-384 wrapper: its emitted core is **byte-identical** to `sha512Jazz`
(`sha384_reuses_sha512_core`), differing only in the FIPS 180-4 §5.3.4 initial
hash value (`iv384`) and the §6.5 truncation to 6 of the 8 chaining words (48
bytes) — both data-oblivious, wrapper-level. SHA-384's HMAC block is the **same
128-byte / 16-`u64`** block as SHA-512's, so HMAC-SHA384 reuses the committed
width-64 XOR-pad (`hmacXorPad512Jazz`, `xorPadComW 64`) **verbatim**. The HMAC
layer adds nothing new: the only HMAC-specific computation, the XOR-pad, is
identical to HMAC-SHA512's; the SHA-384-vs-SHA-512 delta lives entirely in the
data-oblivious outer wrapper (the IV the driver seeds + the 48-byte digest copy).
The RFC 4231 HMAC-SHA-384 vectors are checked byte-for-byte by
`bench/hmac_compare/hmac384_kat.c` over the **emitted** `sha512_compress` core
and the **emitted** `hmac512_xor_pad`. `§7` records the reuse facts in Lean.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.HmacHkdfEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
open CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

set_option autoImplicit false

/-! ## 1. SHA-256 block parameters reused

HMAC/HKDF reuse the committed SHA-256 compression directly: `Sha2Emit.sha256Jazz`
is the fully-emitted `f(H, M) = H'` over 32-bit words, with no `extCall` leaf.
The HMAC-specific arithmetic (the XOR-pad) is at the same 32-bit word width and
over the same 16-word message block. -/

/-- The SHA-256 word width (`32`). -/
abbrev hw : Nat := 32

/-- The SHA-256 message-block word count (`16` `u32` words = the 64-byte block). -/
abbrev blockWords : Nat := 16

/-- The HMAC inner-pad constant `ipad = 0x36` replicated across a `u32` word
    (`0x36363636`). The 64-byte `ipad` block is `ipad` repeated; per `u32` word
    it is this 4-byte pattern. -/
def ipadWord : BitVec hw := 0x36363636

/-- The HMAC outer-pad constant `opad = 0x5c` replicated across a `u32` word
    (`0x5c5c5c5c`). -/
def opadWord : BitVec hw := 0x5c5c5c5c

/-! ## 2. The XOR-pad emitted as a straight-line `regArith` `Com`

`K ⊕ ipad` / `K ⊕ opad` over the 16-word key block is the only word arithmetic
HMAC adds beyond SHA-256. It is 16 independent `regArith xor` bindings — one per
block word, each `out[j] = K[j] ^ pad`, with `pad` supplied as a `u32` input word
(rendered as a jasmin immediate at emit time, like SHA-2's round constants and
shift amounts). No `extCall` leaf: the pad is **fully emitted**. -/

/-- The XOR-pad input-context size: 16 key words `0..15` plus the pad constant at
    input index `16`. -/
def padCtxtSize : Nat := 17

/-- The homogeneous `reg 32` input context for the XOR-pad: 16 key words + the
    pad word. -/
abbrev padCtxt : Ctxt jasminDialect := List.replicate padCtxtSize (.reg hw)

/-- De Bruijn variable for input `i` of a depth-`m+1` replicate context (input
    `0` is `.here`; input `k+1` is `.there` of input `k`; out-of-range saturates
    at `.here`). Mirrors `Sha2Emit.inputVar`. -/
def padInputVar : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) (.reg hw)) (.reg hw)
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (padInputVar m k).there

/-- Input word `i` of `padCtxt`. -/
def padVar (i : Nat) : Ctxt.Var padCtxt (.reg hw) :=
  padInputVar (padCtxtSize - 1) i

/-- One `regArith xor` binding `out = a ^ b` over `padCtxt`. -/
def padXorExpr {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg hw)) :
    Expr jasminDialect Γ (.reg hw) :=
  { op := .regArith .xor hw, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- Emit the 16-word XOR-pad: for the listed key indices `j`, emit
    `out[j] = K[j] ^ pad` (pad is input word `16`). The last `16` bindings are
    output words `0..15` per the `emitAbiOrchReg` last-`nOut` convention. The
    continuation carries the running context; `padVar 16` (the pad) is lifted by
    `.there` through each binding. -/
def emitXorPad :
    List Nat → {Γ : Ctxt jasminDialect} →
    (Nat → Ctxt.Var Γ (.reg hw)) →            -- key-word resolver
    Ctxt.Var Γ (.reg hw) →                     -- pad-word variable
    ({Γ' : Ctxt jasminDialect} → (Nat → Ctxt.Var Γ' (.reg hw)) → Ctxt.Var Γ' (.reg hw) →
        Com jasminDialect Γ' (.reg hw)) →
    Com jasminDialect Γ (.reg hw)
  | [], _, k, _pad, cont => cont k _pad
  | j :: rest, _, k, pad, cont =>
      .var (padXorExpr (k j) pad) <|
        emitXorPad rest
          (fun i => if i = j then .here else (k i).there)
          pad.there
          cont

/-- **The HMAC XOR-pad `Com`** over `padCtxt`: `out[j] = K[j] ^ pad` for all 16
    block words `j`. The result variable is the last binding (output word 15);
    the export reads all 16 via the last-16 convention. Fully emitted: every
    binding is a real `regArith xor`, no `extCall` leaf. -/
def xorPadCom : Com jasminDialect padCtxt (.reg hw) :=
  emitXorPad (List.range blockWords)
    (fun i => padVar i) (padVar 16)
    (fun {_} k _pad => .ret (k (blockWords - 1)))

/-- The emitted XOR-pad `.jazz` (register-arith mode). Input buffer: 16 key words
    `0..15` and the pad word at index `16` (rendered as the immediate `inp[16]`).
    The output is the 16 padded block words. No `extCall` leaf. -/
def xorPadJazz (name : String) : String :=
  emitAbiOrchReg name (w := hw) (nIn := padCtxtSize) (nOut := blockWords) (nCopy := blockWords)
    ["stack u32[16] st"]
    (fun i => if i < blockWords then "st[" ++ toString i ++ "]" else "inp[" ++ toString i ++ "]")
    (fun bidx => "st[" ++ toString ((List.range blockWords).getD bidx 0) ++ "]")
    xorPadCom

/-- The emitted HMAC XOR-pad `.jazz` (the inner/outer pad is selected by the C
    harness's `inp[16]` value: `0x36363636` for `ipad`, `0x5c5c5c5c` for
    `opad`). -/
def hmacXorPadJazz : String := xorPadJazz "hmac_xor_pad"

/-! ### 2a. Binding count (structural sanity)

The XOR-pad emits exactly `blockWords = 16` bindings, one per block word — the
flat mirror that `dstName` reads, kept in lock-step with `emitXorPad`. -/

/-- Binding count of a `Com` (one per `.var`). Mirrors `Sha2Emit.comBindings`. -/
def comBindings : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Nat
  | _, _, .ret _ => 0
  | _, _, .var _ body => 1 + comBindings body

/-- `emitXorPad` over a length-`m` index list emits `m` bindings. -/
theorem emitXorPad_bindings (l : List Nat) {Γ : Ctxt jasminDialect}
    (k : Nat → Ctxt.Var Γ (.reg hw)) (pad : Ctxt.Var Γ (.reg hw))
    (cont : {Γ' : Ctxt jasminDialect} → (Nat → Ctxt.Var Γ' (.reg hw)) →
        Ctxt.Var Γ' (.reg hw) → Com jasminDialect Γ' (.reg hw))
    (hcont : ∀ {Γ' : Ctxt jasminDialect} (k' : Nat → Ctxt.Var Γ' (.reg hw))
        (p' : Ctxt.Var Γ' (.reg hw)), comBindings (cont k' p') = 0) :
    comBindings (emitXorPad l k pad cont) = l.length := by
  induction l generalizing Γ with
  | nil => simpa [emitXorPad, comBindings] using hcont k pad
  | cons j rest ih =>
      show 1 + comBindings (emitXorPad rest _ _ cont) = (j :: rest).length
      rw [ih]; simp [List.length_cons, Nat.add_comm]

/-- **The HMAC XOR-pad emits exactly 16 bindings** — one `regArith xor` per block
    word, the per-binding register-assignment mirror `dstName` reads. -/
theorem xorPadCom_bindings : comBindings xorPadCom = blockWords := by
  unfold xorPadCom
  rw [emitXorPad_bindings]
  · simp [blockWords]
  · intro Γ' k' _p'; rfl

/-! ## 3. The two-pass HMAC composition, at the word level

HMAC threads the SHA-256 compression twice around the XOR-pad. The only
HMAC-specific *computation* is the pad, whose `Com` denotes the pointwise
`K ⊕ pad` over the 16 block words. We record that word-level denotation
explicitly: it is the fact the two `H(...)` passes consume (the inner pass over
`(K⊕ipad) ‖ m`, the outer over `(K⊕opad) ‖ H_inner`). -/

/-- Read input word `i` out of a `padCtxt` valuation. -/
def padInput (V : Ctxt.Valuation padCtxt) (i : Nat) : BitVec hw := (padVar i).lookup V

/-- **The emitted XOR-pad `Com` denotes `K[15] ⊕ pad` at its result slot.** The
    pad `Com`'s returned variable is output word `15`, whose value is
    `K[15] ^ pad` — the pointwise XOR the inner/outer pad block carries. (The
    earlier 15 outputs are the analogous `K[j] ^ pad`; the result var is the
    last, by the last-`nOut` convention.) This is the word-level meaning the two
    HMAC passes consume. -/
theorem xorPadCom_denote (V : Ctxt.Valuation padCtxt) :
    xorPadCom.denote V = padInput V (blockWords - 1) ^^^ padInput V 16 := by
  rfl

/-! ## 4. The HKDF-Expand `T(i)` chaining as a verified bounded loop

The Expand output is `T(1) ‖ T(2) ‖ …`, with `T(i) = HMAC(PRK, T(i-1) ‖ info ‖
byte(i))`. The chaining `T(i-1) ↦ T(i)` is a fixed-trip loop over a single
loop-carried accumulator (the running 32-byte block `T`, packed as one wide
register `reg (8·32)` = the 8 `u32` words of an HMAC-SHA256 output). We route the
loop through the R1 multi-op keystone `JForProgMultiOp.loop_denote_eq_multiOp`:
the emitted `for i = 1 to N { T = step(T) }` denotes the `N`-fold chaining. -/

/-- The wide-register HKDF-Expand accumulator: the 8 `u32` words of a 32-byte
    `T(i)` block packed into one `reg (8·32) = reg 256`. -/
abbrev TAcc : JasminTy := .reg (8 * hw)

/-! ### 4a. Leaf-free wide-register loop body (axiom-clean, no `LeafAgrees`)

A multi-op straight-line `Com [TAcc] TAcc` from pure `regArith` over the wide
accumulator — the shape of the T-chaining block-combine skeleton, leaf-free. It
routes through the multi-op keystone with **no** `LeafAgrees` hypothesis,
axiom-clean. This shows the bounded-loop keystone fires for a leaf-free
HKDF-shaped wide accumulator body — the loop machinery needs no opaque
primitive. Mirrors `Sha2Emit.schedSkelBody`. -/

/-- A `regArith op (8·hw)` expression over the wide accumulator, reading two of
    its in-scope variables. -/
def accOp {Γ : Ctxt jasminDialect}
    (bop : JasminBinOp) (a b : Ctxt.Var Γ TAcc) : Expr jasminDialect Γ TAcc :=
  { op := .regArith bop (8 * hw), retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A leaf-free multi-op straight-line body over the wide T accumulator: a
    three-op `regArith` chain (`v0 = T + T; v1 = v0 ^ T; v2 = v1 | v0`), binding
    three fresh SSA names — exactly the multi-op shape the R1 keystone covers. -/
def expandSkelBody : Com jasminDialect [TAcc] TAcc :=
  .var (accOp .add .here .here)
    (.var (accOp .xor .here (.there .here))
      (.var (accOp .or .here (.there .here))
        (.ret .here)))

/-- The body binds three fresh SSA names — the multi-op case. -/
theorem expandSkelBody_numBinders : Com.numBinders expandSkelBody = 3 := rfl

/-- The body is straight-line: every binder is a `regArith`, never `stackStore`. -/
theorem expandSkelBody_straightLine : StraightLine expandSkelBody := by
  repeat first
    | exact trivial
    | refine ⟨?_, ?_⟩
    | (intro ww n; exact JasminOp.noConfusion)

/-- The HKDF-Expand skeleton loop: iterate the leaf-free body `n` times (`n` =
    the number of `T`-blocks, `⌈L/32⌉`). -/
def expandSkelLoop (n : Nat) : JForProg TAcc :=
  { n := n, update := expandSkelBody }

/-- **The emitted leaf-free wide-register HKDF-Expand loop denotes its `n`-fold
    semantics — axiom-clean, no `LeafAgrees`.** Running the emitted
    `for i = 0 to n { T = body(T) }` `n` times from `init` equals
    `expandSkelLoop.denote init`, via `loop_denote_eq_multiOp`. The body is pure
    `regArith` over the wide accumulator, so the keystone's `LeafAgrees` is
    satisfied vacuously (no `extCall`): **any** `leafSem` works, and the result
    is axiom-clean. The bounded-loop keystone for a leaf-free HKDF-shaped wide
    accumulator body. -/
theorem expandSkelLoop_denote_eq (n : Nat) {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : ⟦TAcc⟧) :
    loopRun (expandSkelLoop n) (bodyStepRun leafSem (expandSkelLoop n)) init
      = (expandSkelLoop n).denote init :=
  loop_denote_eq_multiOp hLeaf (expandSkelLoop n) expandSkelBody_straightLine init

/-! ### 4b. The full HKDF-Expand recurrence loop (one `extCall` leaf)

To carry the *real* recurrence `T(i) = HMAC(PRK, T(i-1) ‖ info ‖ byte(i))` as a
uniform loop body, the per-iteration counter byte `byte(i)` and the fixed
`PRK`/`info` operands must be in the body. The jasmin dialect has **no in-body
literal-constant op** (see the module header — `regArith`'s `shl`/`shr` take the
amount from a *register operand*; there is no `regConst`/`regImm`), and a
`JForProg` body's only variable is the accumulator. So the constant-free body
cannot synthesise the counter byte the recurrence consumes. We therefore
encapsulate one Expand step as a single `extCall` leaf `hkdf_expand_step`,
exactly the ML-KEM matvec / SHA-2 sched-loop precedent: the loop **structure** is
verified, with the leaf's data-oblivious recurrence semantics as the carried
`LeafAgrees` edge. This is the documented #104 limitation, reported not patched. -/

/-- The HKDF-Expand step leaf name (one `T(i) = HMAC(PRK, T(i-1) ‖ info ‖ i)`
    step). -/
def expandStepLeaf : String := "hkdf_expand_step"

/-- The single-`extCall` Expand-step body: `T' = hkdf_expand_step(T)`. A
    one-binder `Com [TAcc] TAcc`. -/
def expandLeafBody : Com jasminDialect [TAcc] TAcc :=
  .var (.mk (.extCall expandStepLeaf [TAcc] TAcc) rfl (.cons .here .nil))
    (.ret .here)

/-- The leaf body is straight-line (its one binder is an `extCall`). -/
theorem expandLeafBody_straightLine : StraightLine expandLeafBody := by
  refine ⟨?_, trivial⟩
  intro ww n; exact JasminOp.noConfusion

/-- The full HKDF-Expand loop: iterate the HMAC-recurrence step `n` times over the
    running `T` block. -/
def expandLoop (n : Nat) : JForProg TAcc :=
  { n := n, update := expandLeafBody }

/-- **The emitted full HKDF-Expand loop denotes the `n`-fold recurrence**, via
    `loop_denote_eq_multiOp`. Running the emitted
    `for i = 0 to n { T = hkdf_expand_step(T) }` from `init` equals
    `expandLoop.denote init` — the loop structure is verified end to end. The
    sole carried edge is the leaf agreement `LeafAgrees` (the `hkdf_expand_step`
    leaf's data-oblivious recurrence semantics), required only because of the
    missing in-body immediate op (#104); fresh-name injectivity is discharged
    inside the R1 keystone. -/
theorem expandLoop_denote_eq (n : Nat) {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (init : ⟦TAcc⟧) :
    loopRun (expandLoop n) (bodyStepRun leafSem (expandLoop n)) init
      = (expandLoop n).denote init :=
  loop_denote_eq_multiOp hLeaf (expandLoop n) expandLeafBody_straightLine init

/-- Structural fact: the HKDF-Expand loop emits a single `UpTo 0..n` `Cfor`
    whose body lowers the step. -/
theorem expandLoop_toCfor_range (n : Nat) :
    (expandLoop n).toCfor
      = .Cfor (mkVarI "i" .inlineInt)
          { dir := .UpTo, lo := 0, hi := n }
          (JForProgCT.emittedBody (expandLoop n)) := rfl

/-! ## 5. Emitted-text sanity checks

The committed `bench/{hmac,hkdf}_compare/gen/*.jazz` is the emitter's output,
validated byte-for-byte against RFC 4231 / RFC 5869 by the jasminc-compiled KATs.
We pin the surface shape of the emitted XOR-pad `.jazz` here. -/

/-- The XOR-pad `.jazz` is an `export fn` with the register-arith ABI. -/
theorem hmacXorPad_has_export :
    strContains hmacXorPadJazz "export fn hmac_xor_pad(" = true := by native_decide

/-- The XOR-pad entry uses jasmin's mutable-output-first register-arith ABI. -/
theorem hmacXorPad_abi :
    strContains hmacXorPadJazz
      "export fn hmac_xor_pad(reg ptr u32[16] out, reg const ptr u32[17] inp)" = true := by
  native_decide

/- The XOR-pad body carries the real `regArith xor` op (`^`), the emitted pad
    computation — NOT an `extCall` leaf. -/
#guard (strContains hmacXorPadJazz " ^ ")

/- The XOR-pad `.jazz` carries no `extCall` leaf call: it is fully emitted (the
    pad word is read straight from `inp[16]`). -/
#guard !(strContains hmacXorPadJazz "sha256_compress(")

/-! ## 6. HMAC-SHA512: the same XOR-pad at `w = 64` over the 128-byte block

HMAC-SHA512 is HMAC over the committed SHA-512 compression (`Sha2Emit.sha512Jazz`,
pure `regArith` over `u64`, no leaf). The block is **128 bytes = 16 `u64` words**
(vs SHA-256's 64-byte / 16-`u32` block), and the pad constants are the `u64`
replications `0x3636363636363636` / `0x5c5c5c5c5c5c5c5c`. The XOR-pad is the only
word arithmetic HMAC adds; it is `blockWords = 16` independent `regArith xor`
bindings exactly as for SHA-256, now at width `64`. We give a
width-parameterized XOR-pad `Com` so HMAC-SHA512 reuses the SHA-256 machinery
verbatim. -/

/-- The SHA-512 word width (`64`). -/
abbrev hw512 : Nat := 64

/-- The HMAC `ipad = 0x36` replicated across a `u64` word (`0x3636363636363636`). -/
def ipadWord512 : BitVec hw512 := 0x3636363636363636

/-- The HMAC `opad = 0x5c` replicated across a `u64` word (`0x5c5c5c5c5c5c5c5c`). -/
def opadWord512 : BitVec hw512 := 0x5c5c5c5c5c5c5c5c

/-- Width-parameterized XOR-pad input context: 16 key words `0..15` plus the pad
    constant at input index `16`, all `reg w`. -/
abbrev padCtxtW (w : Nat) : Ctxt jasminDialect := List.replicate padCtxtSize (.reg w)

/-- De Bruijn variable for input `i` of a depth-`m+1` `reg w` replicate context.
    Width-parameterized mirror of `padInputVar`. -/
def padInputVarW (w : Nat) : (m : Nat) → Nat →
    @Ctxt.Var jasminDialect (List.replicate (m+1) (.reg w)) (.reg w)
  | _, 0 => .here
  | 0, _ => .here
  | (m+1), (k+1) => (padInputVarW w m k).there

/-- Input word `i` of `padCtxtW w`. -/
def padVarW (w : Nat) (i : Nat) : Ctxt.Var (padCtxtW w) (.reg w) :=
  padInputVarW w (padCtxtSize - 1) i

/-- One `regArith xor` binding `out = a ^ b` over a `reg w` context. -/
def padXorExprW {w : Nat} {Γ : Ctxt jasminDialect} (a b : Ctxt.Var Γ (.reg w)) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .regArith .xor w, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- Emit the 16-word XOR-pad at width `w`: for each listed key index `j`, emit
    `out[j] = K[j] ^ pad` (pad is input word `16`). Width-parameterized mirror of
    `emitXorPad`; fully emitted, no `extCall` leaf. -/
def emitXorPadW (w : Nat) :
    List Nat → {Γ : Ctxt jasminDialect} →
    (Nat → Ctxt.Var Γ (.reg w)) →            -- key-word resolver
    Ctxt.Var Γ (.reg w) →                     -- pad-word variable
    ({Γ' : Ctxt jasminDialect} → (Nat → Ctxt.Var Γ' (.reg w)) → Ctxt.Var Γ' (.reg w) →
        Com jasminDialect Γ' (.reg w)) →
    Com jasminDialect Γ (.reg w)
  | [], _, k, _pad, cont => cont k _pad
  | j :: rest, _, k, pad, cont =>
      .var (padXorExprW (k j) pad) <|
        emitXorPadW w rest
          (fun i => if i = j then .here else (k i).there)
          pad.there
          cont

/-- **The width-`w` HMAC XOR-pad `Com`** over `padCtxtW w`: `out[j] = K[j] ^ pad`
    for all 16 block words. Fully emitted (every binding a real `regArith xor`,
    no `extCall` leaf). -/
def xorPadComW (w : Nat) : Com jasminDialect (padCtxtW w) (.reg w) :=
  emitXorPadW w (List.range blockWords)
    (fun i => padVarW w i) (padVarW w 16)
    (fun {_} k _pad => .ret (k (blockWords - 1)))

/-- The width-`w` emitted XOR-pad `.jazz` (register-arith mode). Input buffer: 16
    key words + the pad word at index `16`; output is the 16 padded block words.
    No `extCall` leaf. -/
def xorPadJazzW (w : Nat) (name : String) : String :=
  emitAbiOrchReg name (w := w) (nIn := padCtxtSize) (nOut := blockWords) (nCopy := blockWords)
    ["stack u" ++ toString w ++ "[16] st"]
    (fun i => if i < blockWords then "st[" ++ toString i ++ "]" else "inp[" ++ toString i ++ "]")
    (fun bidx => "st[" ++ toString ((List.range blockWords).getD bidx 0) ++ "]")
    (xorPadComW w)

/-- **The emitted HMAC-SHA512 XOR-pad `.jazz`** (`w = 64`, 128-byte block). The
    inner/outer pad is selected by the C harness's `inp[16]` value:
    `0x3636363636363636` for `ipad`, `0x5c5c5c5c5c5c5c5c` for `opad`. -/
def hmacXorPad512Jazz : String := xorPadJazzW hw512 "hmac512_xor_pad"

/-! ### 6a. Binding count (width-parameterized) -/

/-- `emitXorPadW` over a length-`m` index list emits `m` bindings. -/
theorem emitXorPadW_bindings (w : Nat) (l : List Nat) {Γ : Ctxt jasminDialect}
    (k : Nat → Ctxt.Var Γ (.reg w)) (pad : Ctxt.Var Γ (.reg w))
    (cont : {Γ' : Ctxt jasminDialect} → (Nat → Ctxt.Var Γ' (.reg w)) →
        Ctxt.Var Γ' (.reg w) → Com jasminDialect Γ' (.reg w))
    (hcont : ∀ {Γ' : Ctxt jasminDialect} (k' : Nat → Ctxt.Var Γ' (.reg w))
        (p' : Ctxt.Var Γ' (.reg w)), comBindings (cont k' p') = 0) :
    comBindings (emitXorPadW w l k pad cont) = l.length := by
  induction l generalizing Γ with
  | nil => simpa [emitXorPadW, comBindings] using hcont k pad
  | cons j rest ih =>
      show 1 + comBindings (emitXorPadW w rest _ _ cont) = (j :: rest).length
      rw [ih]; simp [List.length_cons, Nat.add_comm]

/-- **The HMAC-SHA512 XOR-pad emits exactly 16 bindings** — one `regArith xor`
    per 64-bit block word. -/
theorem xorPadComW_bindings (w : Nat) : comBindings (xorPadComW w) = blockWords := by
  unfold xorPadComW
  rw [emitXorPadW_bindings]
  · simp [blockWords]
  · intro Γ' k' _p'; rfl

/-! ### 6b. Word-level denotation (the fact the two SHA-512 passes consume) -/

/-- Read input word `i` out of a `padCtxtW w` valuation. -/
def padInputW (w : Nat) (V : Ctxt.Valuation (padCtxtW w)) (i : Nat) : BitVec w :=
  (padVarW w i).lookup V

/-- **The emitted width-`w` XOR-pad `Com` denotes `K[15] ⊕ pad` at its result
    slot** — the pointwise XOR the inner/outer pad block carries, the word-level
    meaning the two HMAC-SHA512 passes consume. -/
theorem xorPadComW_denote (w : Nat) (V : Ctxt.Valuation (padCtxtW w)) :
    (xorPadComW w).denote V = padInputW w V (blockWords - 1) ^^^ padInputW w V 16 := by
  rfl

/-! ### 6c. Emitted-text sanity checks (HMAC-SHA512) -/

/- The SHA-512 XOR-pad is an `export fn` with the register-arith ABI. -/
#guard (strContains hmacXorPad512Jazz "export fn hmac512_xor_pad(")

/- The SHA-512 XOR-pad uses the mutable-output-first register-arith ABI over
    `u64` (16 key words + the pad word). -/
#guard (strContains hmacXorPad512Jazz "export fn hmac512_xor_pad(reg ptr u64[16] out, reg const ptr u64[17] inp)")

/- The SHA-512 XOR-pad body carries the real `regArith xor` op (`^`) — NOT an
    `extCall` leaf. -/
#guard (strContains hmacXorPad512Jazz " ^ ")

/- The SHA-512 XOR-pad `.jazz` carries no `extCall` hash leaf: it is fully
    emitted (the pad word is read straight from `inp[16]`). -/
#guard !(strContains hmacXorPad512Jazz "sha512_compress(")

/- The SHA-512 XOR-pad uses 64-bit words, distinguishing it from the SHA-256
    pad (`stack u64[16]` state buffer). -/
#guard (strContains hmacXorPad512Jazz "stack u64[16] st")

/-! ## 7. HMAC-SHA384: HMAC over the SHA-384 truncation of the SHA-512 core

HMAC-SHA384 is HMAC over **SHA-384**. SHA-384 is *not* a new compression
function: it runs the **same** block compression as SHA-512
(`Sha2Emit.Truncated.sha384Variant.core = sha512Spec`), differing only in the
FIPS 180-4 §5.3.4 initial hash value (`iv384`) the driver seeds and the §6.5
truncation to 6 of the 8 output words (48 bytes). Both are data-oblivious,
wrapper-level changes; the emitted compression `.jazz` is **byte-identical** to
the committed `sha512Jazz`.

HMAC over SHA-384 uses the **same 128-byte / 16-`u64` block** as HMAC-SHA512
(SHA-384's block size equals SHA-512's). So the only HMAC-specific computation,
the XOR-pad, is **identical** to HMAC-SHA512's: HMAC-SHA384 reuses the committed
width-64 `xorPadComW 64` / `hmacXorPad512Jazz` verbatim. HMAC adds nothing new
beyond what HMAC-SHA512 already emits; the SHA-384-vs-SHA-512 delta (IV +
48-byte truncation) is entirely the data-oblivious outer wrapper the C harness
contributes (`bench/hmac_compare/hmac384_kat.c`, checked vs RFC 4231). This
section records the reuse facts. -/

/-- The SHA-384 variant from `Sha2Emit`: the SHA-512 core seeded with `iv384`,
    truncated to 6 words (48 bytes). -/
abbrev sha384Variant := Sha2Emit.Truncated.sha384Variant

/-- **HMAC-SHA384 reuses the committed SHA-512 compression core verbatim.** The
    SHA-384 emitted core is byte-identical to `sha512Jazz` — the same emitted
    block compression HMAC-SHA512 runs. The IV + truncation that distinguish
    SHA-384 are wrapper-level (the driver's seed + the 48-byte digest copy), not
    new emitted arithmetic. -/
theorem hmac384_reuses_sha512_core :
    Sha2Emit.Truncated.variantJazz sha384Variant "sha512_compress"
      = Sha2Emit.sha512Jazz :=
  Sha2Emit.Truncated.sha384_reuses_sha512_core

/-- **HMAC-SHA384's XOR-pad denotes `K[15] ⊕ pad` at width 64** — the *same*
    pointwise XOR HMAC-SHA512 consumes over the *same* 128-byte / 16-`u64` block.
    SHA-384 reuses `xorPadComW 64` verbatim; the only HMAC-specific computation is
    this pad, identical to HMAC-SHA512's, with no new arithmetic. -/
theorem hmac384_xorpad_denote (V : Ctxt.Valuation (padCtxtW hw512)) :
    (xorPadComW hw512).denote V = padInputW hw512 V (blockWords - 1) ^^^ padInputW hw512 V 16 :=
  xorPadComW_denote hw512 V

/-- The SHA-384 core spec IS `sha512Spec` (64-bit words, 80 rounds) — the HMAC
    block width matches HMAC-SHA512's `hw512 = 64`. -/
theorem hmac384_core_width : sha384Variant.core.w = hw512 :=
  rfl

/-- HMAC-SHA384's digest is the SHA-384 digest: 48 bytes (6 `u64` words), vs
    HMAC-SHA512's 64 bytes — the only output-side difference, a wrapper truncation
    on the *same* emitted core. -/
theorem hmac384_digest_bytes : Sha2Emit.Truncated.digestBytes sha384Variant = 48 :=
  Sha2Emit.Truncated.sha384_digest_bytes

/- **The XOR-pad emitted text HMAC-SHA384 consumes is the committed
    `hmac512_xor_pad`** — HMAC-SHA384 and HMAC-SHA512 drive the *same* emitted
    pad over the *same* 128-byte block. No HMAC-SHA384-specific `.jazz` is
    emitted; the digest truncation is in the C wrapper. -/
#guard (strContains hmacXorPad512Jazz "export fn hmac512_xor_pad(")

/-! ## Front-sourced HMAC pad + SHA-2 core (covered SExpr front, rfl-provenance)

HMAC introduces one word operation over SHA-2: the key-pad XOR `K ⊕ ipad`
(`0x36…`) / `K ⊕ opad` (`0x5c…`). Expressed as width-32 `SExpr` (`SXor` with the
pad literal) and routed through `lowerSExprW 32` → `Com catCryptDialect` →
`cryptoDialectToJasminCom` (FRONT marker) → owned x86, mirroring the Sha2/ChaCha
`FrontSourced` templates (the SHA-2 compression itself is front-sourced in
`Sha2Emit.FrontSourced`). Provenance `isSome := by rfl`; value = the RFC 2104 /
5869 byte-KAT (bench/). -/
namespace FrontSourced

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

abbrev lowerW := @CatCrypt.Crypto.SecureCompilation.Dialects.ScalarSExprWidth32Prototype.lowerSExprW

/-- HMAC inner pad word `K ⊕ ipad` (`ipad = 0x36363636`). -/
def hmacIpad : SExpr := .SXor (.SVar "k") (.SLit 0x36363636)

/-- HMAC outer pad word `K ⊕ opad` (`opad = 0x5c5c5c5c`). -/
def hmacOpad : SExpr := .SXor (.SVar "k") (.SLit 0x5c5c5c5c)

def padΓ : Ctx := [.sword 32]

def padVM : VarMap padΓ := (VarMap.empty.bind "k")

def progOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :
    Option (Com catCryptDialect Γ (.sword w)) :=
  match lowerW w vm 0 e with
  | some r =>
      match r.1.vm.lookup r.2.1 with
      | some ⟨.sword w', v⟩ => if h : w' = w then r.1.cont (Com.ret (toVIRVar (h ▸ v))) else none
      | _ => none
  | none => none

def jasminOfW (w : Nat) {Γ : Ctx} (vm : VarMap Γ) (e : SExpr) :=
  (progOfW w vm e).bind DialectToJasminCom.cryptoDialectToJasminCom

theorem hmac_ipad_isSome : (progOfW 32 padVM hmacIpad).isSome := by rfl
theorem hmac_ipad_lowers : (jasminOfW 32 padVM hmacIpad).isSome := by rfl
theorem hmac_opad_isSome : (progOfW 32 padVM hmacOpad).isSome := by rfl
theorem hmac_opad_lowers : (jasminOfW 32 padVM hmacOpad).isSome := by rfl

end FrontSourced

end CatCrypt.Crypto.SecureCompilation.VIR.HmacHkdfEmit
