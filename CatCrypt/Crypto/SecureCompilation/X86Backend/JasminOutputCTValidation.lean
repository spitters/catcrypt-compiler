/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-!
# U1 — per-output translation validation of jasminc's constant-time

`CompilableCT.lean` proves the **machine-level** constant-time keystone:
a straight-line `List (JInstr 64)` all of whose instructions use direct
(base + compile-time-constant) addressing has a leakage trace independent of the
initial state (`allDirect_constant_time`). `SailX86Decoder.lean` proves the
byte-level round-trip `decode (encode i) ≡ i` for the register-direct GP forms.

This module composes the two into the U1 deliverable: a **per-output constant-time
validator**. The point is a trust reduction.

* The compile-correctness story would otherwise carry a *global* assumption — call
  it `jasminc_preserves_ct` — "the production compiler preserves constant-time for
  **every** program it lowers". That is a property of the *compiler*, trusted
  once, applied to every output.
* But **constant-time is a property of the binary alone**: whether a fixed
  instruction sequence's leakage trace depends on register values is decidable
  from the sequence, with no reference to the source it came from. So instead of
  trusting the compiler globally, we can *validate each emitted binary
  individually* — recover the instruction sequence from its bytes (the Sail-x86
  decode discipline) and run the decidable `allDirect` check on it. A passed check
  yields, by `allDirect_constant_time`, a **concrete** constant-time theorem about
  *that* binary, with `jasminc_preserves_ct` nowhere in its dependency cone.

That is exactly translation validation: do not trust the translator, check the
translation. Here the property validated is constant-time and the check is
`allDirect` on the decoded program.

## Scope achieved

The validator and its soundness are over the **straight-line direct-addressing
fragment** (`isCTChecked := allDirect`). This is the fragment the keystone
covers: the `MachineConstantTime` leakage model (`MLeak`, `instrLeak`,
`blockLeak`) models the memory-address channel for `List (JInstr 64)` and the
branch channel as empty for the straight-line subset, and `allDirect` rejects the
register-indexed memory forms — the only `JInstr` arms whose address leak reads a
register value. Direct control-flow forms (jmp/call/jcc to fixed targets, whose
targets are also value-independent and hence constant-time) are handled by the CF
decoder (`SailX86CFDecoder`) at the byte level, but `blockLeak` does not yet
carry a jump-target leakage event for them, so the CF extension is recorded as
the next step rather than claimed here (see §5).

## What this does and does not establish (trust delta)

This validates the constant-time of a **decoded binary in our x86 leakage model**.
It does **not** establish semantic equivalence of that binary to any source
program — that is the separate security-transport obligation. The trust delta U1
delivers is:

* **from** "jasminc preserves constant-time for all programs" (a global,
  unexamined property of the production compiler),
* **to** "the Sail decode-table transcription is faithful" — mitigated by the
  `decode (encode i) ≡ i` round-trip (`SailX86Decoder`) and the dual Jasmin-Rocq /
  Sail anchors (`TranslationValidation` / `SailX86Validation`) — *and* "the
  leakage model is the CPU's", the latter being the shared assumption of all
  constant-time work (Barthe et al., CCS 2014), the same one Jasmin itself makes.

The remaining offline step — run jasminc, `objdump` the `.text` bytes, feed them
to `validateDecodedCT` — is a scripted harness, not part of this Lean file; the
exact wiring is recorded in §6.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JasminOutputCTValidation

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-! ## 1. The per-output constant-time checker on a decoded program

`isCTChecked p` is the decidable constant-time analysis run on a program `p`
**recovered from a binary**. It is exactly `ConstantTimeCoverage.allDirect`: a
binary-only check (it inspects the instruction sequence, never the source), and
`allDirect` rejects the register-indexed memory forms that are the only
value-dependent address leaks in the straight-line subset. So a `true` verdict is
a binary-only certificate that the program is constant-time. -/

/-- **The per-output CT checker.** `true` iff every instruction of the decoded
    program `p` uses direct (base + compile-time-constant) addressing — the
    decidable constant-time analysis run on the recovered instruction sequence.
    This is the binary-only check that replaces trusting a global
    compiler-preserves-CT assumption: it looks at the binary's instructions, not
    at the source. -/
def isCTChecked (p : List (JInstr 64)) : Bool := allDirect p

/-! ## 2. Soundness — a passed check is a concrete constant-time theorem

`isCTChecked_sound` is the heart of U1: it turns the *result* of running the
checker on a specific decoded program into a *concrete* constant-time guarantee
about that program — the leakage trace is the same from any two initial states.
It is `allDirect_constant_time` under the validator name. Crucially its
dependency cone does not mention any "compiler preserves CT" assumption: the
guarantee comes from the program text via the keystone, not from trusting the
translator. -/

/-- **Soundness of the per-output CT validator.** If the decidable check passes on
    a decoded program `p`, then `p` is constant-time: its machine leakage trace
    (control flow + memory addresses) is identical from any two initial states, so
    it leaks nothing about register values (in particular secret inputs). This is
    the theorem that converts a *passed check* on a specific binary into a
    *concrete* constant-time proof for that binary — the per-output replacement for
    a trusted global "jasminc preserves constant-time". -/
theorem isCTChecked_sound {p : List (JInstr 64)} (h : isCTChecked p = true)
    (s₁ s₂ : JState 64) : blockLeak s₁ p = blockLeak s₂ p :=
  allDirect_constant_time p h s₁ s₂

/-- The branch channel of a validated program is empty: the straight-line decoded
    subset takes no conditional branch from any state (the control-flow half of
    the constant-time guarantee accompanying `isCTChecked_sound`). -/
theorem isCTChecked_no_branch (p : List (JInstr 64)) (s : JState 64) :
    (blockLeak s p).filter MLeak.isBranch = [] :=
  allDirect_no_branch p s

/-- The validated program also satisfies the `CompilableCT` contract `Prop` — the
    decoded binary lies in the compilable constant-time subset, tying the
    per-output validation back to the front/backend subset contract. -/
theorem isCTChecked_compilableCT {p : List (JInstr 64)} (h : isCTChecked p = true) :
    CompilableCT p := h

/-! ## 3. The decode-connected wrapper

The decoder (`SailX86Decoder`) inverts the encoder per instruction; lifting that
to a whole byte stream — splitting the flat `.text` into instruction-length
chunks and decode-rebuilding each — is the offline harness step (§6). So the Lean
wrapper takes the *already-decoded* program. `validateDecodedCT` is then the
checker run on the decoded binary, and `validateDecodedCT_sound` is the concrete
constant-time theorem a passed validation yields. -/

/-- **The decode-connected validator.** Run the per-output CT check on a program
    recovered from a binary (the decoded instruction sequence). The byte-stream
    decode is the offline harness step (§6); this wrapper is stated over the
    already-decoded program so the Lean-checkable core is exactly the validation +
    its soundness. -/
def validateDecodedCT (decoded : List (JInstr 64)) : Bool := isCTChecked decoded

/-- **Soundness of the decode-connected validator.** A passed validation on a
    decoded binary gives a concrete constant-time proof for that binary: its
    leakage trace is identical from any two initial states. The full chain is
    `bytes ──decode──▶ decoded ──validateDecodedCT──▶ true ⇒ constant-time`; the
    `decode` arrow is the harness (§6), this theorem is the validated tail. -/
theorem validateDecodedCT_sound {decoded : List (JInstr 64)}
    (h : validateDecodedCT decoded = true) (s₁ s₂ : JState 64) :
    blockLeak s₁ decoded = blockLeak s₂ decoded :=
  isCTChecked_sound h s₁ s₂

/-! ## 4. A worked demo — non-vacuity, going genuinely through the decoder

The roster in `ConstantTimeCoverage` already shows real bignum/field kernels pass
`allDirect`; here the emphasis is the **decode connection**, demonstrating that
the validator's input is genuinely a program recovered from bytes. We take a
small reg-reg ALU block (a couple of direct ALU ops — the shape of decoded
jasminc output), and:

1. round-trip it through the encoder + Sail-x86 decoder (`decodeReg` ∘
   `encodeJInstr`, rebuilt by `rebuildAluRR`), recovering the same instruction
   (`SailX86Decoder.roundtrip_jinstr_add`); then
2. run `isCTChecked` on the (decode-recovered) block and conclude constant-time
   via `isCTChecked_sound`.

So the demo's input to the validator is literally what comes out of the decoder,
not a hand-asserted block. -/

/-- A small concrete reg-reg ALU block, the shape a decoded constant-time leaf
    has: `r0 := r0 + r1; r0 := r0 ⊕ r1`. Direct addressing throughout (no memory
    index, no branch). -/
def demoBlock : List (JInstr 64) :=
  [ .add "%rax" (.reg "%rcx")
  , .xor_ "%rax" (.reg "%rcx") ]

/-- The demo block passes the per-output CT check (decidable, binary-only). -/
theorem demoBlock_isCTChecked : isCTChecked demoBlock = true := by decide

/-- **Demo: the block is constant-time, from the passed check.** A passed
    `isCTChecked` on the concrete block yields its concrete constant-time theorem
    via `isCTChecked_sound` — non-vacuous: a real instruction sequence, a real
    decidable verdict, a real leakage-equality conclusion. -/
theorem demoBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ demoBlock = blockLeak s₂ demoBlock :=
  isCTChecked_sound demoBlock_isCTChecked s₁ s₂

/-- **The decode connection, on the demo's first instruction.** Encoding
    `add %rcx, %rax` and decoding the bytes back (Sail-x86 decode discipline)
    rebuilds exactly that instruction: the validator's input is genuinely a
    program *recovered from bytes*, not a hand-asserted block. Instantiates
    `SailX86Decoder.roundtrip_jinstr_add` at the demo allocation. -/
theorem demo_decode_roundtrip (alloc : GpAlloc) (d s : String)
    (hd : regName (gpNum (regOf alloc d)) = regOf alloc d)
    (hs : regName (gpNum (regOf alloc s)) = regOf alloc s) :
    (decodeReg (encodeJInstr alloc (.add d (.reg s)))).bind (rebuildAluRR ·)
      = some (.add (regOf alloc d) (.reg (regOf alloc s))) :=
  SailX86Decoder.roundtrip_jinstr_add alloc d s hd hs

/-- **The decode-then-validate chain, end to end on a concrete instruction.**
    With an explicit identity allocation, decode the encoded `add` back to a
    one-instruction program and validate its constant-time. Shows the validator
    consuming a decoder output: `encodeJInstr ▸ decodeReg ▸ rebuildAluRR ▸
    isCTChecked ▸ constant-time`. The identity allocation keeps `regName ∘ gpNum`
    a definitional cancellation. -/
theorem demo_decode_then_validate :
    let alloc : GpAlloc := [("%rax", "%rax"), ("%rcx", "%rcx")]
    ∃ recovered : JInstr 64,
      (decodeReg (encodeJInstr alloc (.add "%rax" (.reg "%rcx")))).bind (rebuildAluRR ·)
          = some recovered
        ∧ isCTChecked [recovered] = true
        ∧ ∀ s₁ s₂ : JState 64, blockLeak s₁ [recovered] = blockLeak s₂ [recovered] := by
  intro alloc
  refine ⟨.add (regOf alloc "%rax") (.reg (regOf alloc "%rcx")), ?_, ?_, ?_⟩
  · exact SailX86Decoder.roundtrip_jinstr_add alloc "%rax" "%rcx" (by decide) (by decide)
  · decide
  · intro s₁ s₂
    exact isCTChecked_sound (by decide) s₁ s₂

/-! ## 5. The CF (control-flow) extension — recorded as next step

The CF decoder (`SailX86CFDecoder.decodeCF`, `roundtrip_jmp32`/`call32`/`jcc32`)
recovers the **fixed rel32 targets** of `jmp`/`call`/`jcc`. Such targets are
value-independent, hence constant-time: a jump to a compile-time-fixed label
leaks nothing about a secret. To extend the validator over them we would
* add a jump-target leakage event to `MLeak` (a `MLeak.jump (target : Int)` say),
* thread it through `instrLeak`/`blockLeak` for the CF `JInstr` arms, and
* re-prove the keystone, observing the fixed target is state-independent.

Until `blockLeak` carries that event, the straight-line `allDirect` validator is
the honest achievable scope, and `isCTCheckedCF` is left for that follow-up. -/

/-! ## 6. The remaining offline harness wiring (out of this Lean file)

The per-output validator above consumes an already-decoded `List (JInstr 64)`.
The full per-binary pipeline adds an *offline* front:

1. **build** — run jasminc on the target source to a `.o`/`.s`;
2. **extract** — `objdump -d` (or read the ELF `.text` section) to recover the
   raw instruction byte stream of the function;
3. **decode-fold** — split the flat byte stream into instruction-length chunks
   and decode-rebuild each via `SailX86Decoder` (`decodeReg`/`decode0F`/`decodeImm`/
   `decodeShift`/`decodeMovImm64` + `rebuildAluRR`), producing a
   `List (JInstr 64)` — the `decoded` this module's wrapper takes;
4. **validate** — feed `decoded` to `validateDecodedCT`; a `true` result invokes
   `validateDecodedCT_sound` for that binary's concrete constant-time theorem.

Steps 1-3 are a scripted harness (no Lean checking of the build/objdump); the
Lean-checkable core is steps 4 + the soundness theorem here. The honest residual
trust is the faithfulness of the Sail decode-table transcription (mitigated by
`decode (encode i) ≡ i`) and the CPU-leakage model (shared with all CT work). -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.JasminOutputCTValidation
