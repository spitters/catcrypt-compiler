/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit
import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA

/-!
# A multi-limb curve-field COMPOSITION `a·b + c·d` emitted from PROVEN blocks

`Curve4MontMulProvenEmit.lean` emits ONE leaf — the secp256k1 Montgomery field
multiply `secp256k1_montmul_proven` — assembled from the two proven `runBlock`
cores. That is the curve-family analogue of BabyBear's single `bbMul` word block.
The curve-family analogue of the **field-pipeline keystone**
(`Poseidon2/FieldPipelineEmitBB.lean`, which emits the whole 21-round Poseidon2
permutation as one `.s` through the field schedule) is a *composition* of those
proven leaves: this file emits the field-op tree

    dot(a, b, c, d) = a·b + c·d   over secp256k1's base field 𝔽ₚ

the same `Com fieldDialect` `RelationalCompileHigh.Demo.dotProg Psecp` whose
`denote = α·β + γ·δ` and whose three Stage-2 leaf squares (one per `fMul`/`fAdd`
node) are discharged in `FieldDescentMultiLimb.lean`
(`secp256k1_mmMul_realizes` / `secp256k1_mmAdd_realizes`,
`dotComposition_realizes`).

## What rides the compiler, and what stays GMP-KAT-gated (REV-12)

The composition `dotProg` schedules three field ops:

    m1 = fMul a b ;  m2 = fMul c d ;  s = fAdd m1 m2 ; ret s

Each `fMul` node's Stage-2 word realization is the proven Montgomery multiply
`montMulProvenBlock secp256k1LimbImms secp256k1NPrime` (the proven
`emitProductBlock4` product + `emitMontRedc4Block` reduce; the per-op square is
`FieldDescentMultiLimb.secp256k1_mmMul_realizes`). The `fAdd` node's Stage-2 word
realization is the proven canonical field add
`FieldAddSubTierA.emitAdcChain` ripple-add + conditional subtract of `p`
(`FieldAddSubTierA.modAdd_runBlock`: `condSubP p (runBlockAddValue …) = (a+b) % p`
for reduced inputs; the per-op square is `secp256k1_mmAdd_realizes`).

The emitted `.s` realizes the `dotProg` schedule: it calls the proven montmul leaf
twice (`m1`, `m2`) and runs the proven add+cond-sub on the two products. The
**composition schedule** (the two-call sequence + the staging of `m1`, `m2` and the
canonicalising add) is what rides the compiler — its leaf squares are the proven
blocks above. The single multi-limb leaf *byte-identity* of `secp256k1_montmul_proven`
stays GMP-KAT-gated (REV-12: a 256×256→256 field multiply is **never** `#eval`'d in
Lean — that OOMs the shared LSP), and so the whole composition's value identity is
GMP-KAT-gated end to end
(`bench/secp256k1_compare/secp256k1_dot_owned_kat.c`, GMP reference
`a·b·R⁻¹ + c·d·R⁻¹ mod p`).

This is the **curve family** (3rd self-emitted field family after BabyBear scalar
and the Pasta/BN254/P256 leaves): a genuine multi-limb field-op tree emitted to
owned x86-64 over proven Montgomery + canonical-add blocks, with the value gate
external (GMP).

## The orchestration schedule (trusted composition scaffolding)

The orchestrator `secp256k1_dot(z, a, b, c, d)` is a System-V function
(`z`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`, `c`→`%rcx`, `d`→`%r8`):

* `call secp256k1_montmul_proven` with `(m1buf, a, b)`     — the proven `fMul` leaf
* `call secp256k1_montmul_proven` with `(m2buf, c, d)`     — the proven `fMul` leaf
* inline proven ripple-add `m1buf + m2buf` then conditional subtract of `p` into
  `z`                                                       — the proven `fAdd` leaf

The two scratch buffers live in the caller's red-zone/stack frame. The call
sequence + scratch staging is trusted composition scaffolding (outside the
`runBlock`-verified blocks), exactly as the `secp256k1_orch_owned.s` orchestrator
composes its leaves and as `renderLeafFn`'s prologue/epilogue ABI glue is trusted.
The verified content is the two proven leaves and the proven canonical add.

**0 sorries** here (this is an emit driver — `IO`/`String` rendering); the proven
content is in `Curve4MontMulProvenEmit` / `FieldAddSubTierA` / `FieldDescentMultiLimb`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4DotProvenEmit

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4MontMulProvenEmit

/-! ## 1. The proven canonical field-add block (secp256k1, in-orchestrator)

The `fAdd` node realizes `(m1 + m2) mod p` via the proven `FieldAddSubTierA`
ripple-add (`emitAdcChain`) + a conditional subtract of `p`. We render that block
inline in the orchestrator over four accumulator registers `%r9..%r12`
(the sum) with the trial difference in `%r13..%rax`, selecting branch-free with
`CMOVB`. The secp256k1 modulus limbs are the immediates. -/

/-- secp256k1 base-field prime little-endian 64-bit limbs (as `Nat` immediates) —
    the same `secp256k1LimbImms` the montmul leaf materialises. -/
def secpLimbImms : List Nat := secp256k1LimbImms

/-- The proven canonical field-add body: `acc = m1 + m2` (ripple `add`/`adc` —
    the `emitAdcChain` shape), then trial `acc − p` (borrow chain `sub`/`sbb`) with
    a 5th-word borrow capture, then branch-free `CMOVB` selecting the unreduced
    `acc` back on `acc < p`. Operands: `m1` in `%r9..%r12`, `m2` in `%r13..%rax`,
    modulus limbs as immediates `secpLimbImms`. Result canonical in `%r9..%r12`.

    This is the proven `FieldAddSubTierA.modAdd_runBlock` shape: ripple-add then
    `condSubP` of `p` — `(m1 + m2) mod p` for reduced inputs. -/
def condAddCanonBody : List String :=
  let m1 := ["%r9", "%r10", "%r11", "%r12"]
  let m2 := ["%r13", "%r14", "%r15", "%rbx"]
  -- the modulus limbs materialised into %rax (one at a time; subq cannot take a
  -- full 64-bit immediate — only movabsq does, so we movabsq each limb into %rax
  -- and sub/sbb register-form).
  let pl := secpLimbImms
  -- ripple add  acc(m1) += m2   (emitAdcChain shape: add then 3×adc)
  [ s!"\taddq {m2.getD 0 "%rax"}, {m1.getD 0 "%rax"}" ]
    ++ (List.range 3).map (fun k =>
        s!"\tadcq {m2.getD (k+1) "%rax"}, {m1.getD (k+1) "%rax"}")
  -- 5th-bit carry of the sum into %rcx
    ++ [ "\tmovq $0, %rcx", "\tadcq $0, %rcx" ]
  -- trial difference: copy acc(m1) into m2, then sub p limb-by-limb via %rax,
  -- threading the borrow (subq first, sbbq for limbs 1..3, sbbq $0 for 5th word).
    ++ (List.range 4).map (fun k => s!"\tmovq {m1.getD k "%rax"}, {m2.getD k "%rax"}")
    ++ [ s!"\tmovabsq ${pl.getD 0 0}, %rax", s!"\tsubq %rax, {m2.getD 0 "%rax"}" ]
    ++ (List.range 3).flatMap (fun k =>
        [ s!"\tmovabsq ${pl.getD (k+1) 0}, %rax"
        , s!"\tsbbq %rax, {m2.getD (k+1) "%rax"}" ])
    ++ [ "\tsbbq $0, %rcx" ]
  -- CMOV: acc := (sum ≥ p) ? sum−p : sum. After the trial sub, m2 = sum − p and
  -- the final borrow (CF) is set iff sum < p; `cmovae m2 → m1` picks the reduced
  -- difference exactly when sum ≥ p (no borrow), else keeps the unreduced sum.
    ++ (List.range 4).map (fun k =>
        s!"\tcmovaeq {m2.getD k "%rax"}, {m1.getD k "%rax"}")

/-! ## 2. The orchestrator `secp256k1_dot` (composition schedule)

`secp256k1_dot(z, a, b, c, d)` — System-V `void secp256k1_dot(uint64_t *z,
const uint64_t *a, const uint64_t *b, const uint64_t *c, const uint64_t *d)`.
Calls the proven `secp256k1_montmul_proven` leaf twice to form the two Montgomery
products `m1 = a·b`, `m2 = c·d` into stack scratch, then runs the proven canonical
add to write `z = m1 + m2 mod p`. The `.s` text concatenates the proven montmul
leaf (so the object is self-contained) with this orchestrator. -/

/-- Stack-frame layout (all rbp-relative, BELOW the 5 pushed callee-saved
    registers which occupy `-8(%rbp) .. -40(%rbp)`):

      -48 z   -56 a   -64 b   -72 c   -80 d          (saved pointer args)
      -88..-112  m1buf   (4 limbs, base &m1buf = -112(%rbp))
      -120..-144 m2buf   (4 limbs, base &m2buf = -144(%rbp))

    The `subq $136` frame covers `[-40, -176](%rbp)`, so every scratch slot is
    live and disjoint from the pushed registers. -/
def dotOrchBody : List String :=
  -- prologue: save callee-saved (rbp, then rbx,r12-r15), frame the scratch.
  -- After `pushq %rbp` rsp is 16-aligned; the 5 further pushes leave rsp%16=8,
  -- so the frame `subq $136` re-aligns rsp to 16 before the `call`s (System-V).
  [ "\tpushq %rbp", "\tmovq %rsp, %rbp"
  , "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
  , "\tsubq $136, %rsp"
  -- save the four input pointers (a=%rsi,b=%rdx,c=%rcx,d=%r8) and z=%rdi
  , "\tmovq %rdi, -48(%rbp)"   -- z
  , "\tmovq %rsi, -56(%rbp)"   -- a
  , "\tmovq %rdx, -64(%rbp)"   -- b
  , "\tmovq %rcx, -72(%rbp)"   -- c
  , "\tmovq %r8,  -80(%rbp)"   -- d
  -- m1 = montmul(a, b)  -> m1buf base at -112(%rbp)
  , "\tleaq -112(%rbp), %rdi"  -- z arg = &m1buf
  , "\tmovq -56(%rbp), %rsi"   -- x arg = a
  , "\tmovq -64(%rbp), %rdx"   -- y arg = b
  , "\tcall secp256k1_montmul_proven"
  -- m2 = montmul(c, d)  -> m2buf base at -144(%rbp)
  , "\tleaq -144(%rbp), %rdi"  -- z arg = &m2buf
  , "\tmovq -72(%rbp), %rsi"   -- x arg = c
  , "\tmovq -80(%rbp), %rdx"   -- y arg = d
  , "\tcall secp256k1_montmul_proven" ]
  -- load m1buf into %r9..%r12, m2buf into %r13..%rbx (rbp-relative), run the
  -- proven canonical add
  ++ [ "\tmovq -112(%rbp), %r9", "\tmovq -104(%rbp), %r10"
     , "\tmovq -96(%rbp), %r11", "\tmovq -88(%rbp), %r12"
     , "\tmovq -144(%rbp), %r13","\tmovq -136(%rbp), %r14"
     , "\tmovq -128(%rbp), %r15","\tmovq -120(%rbp), %rbx" ]
  ++ condAddCanonBody
  -- store canonical result (%r9..%r12) to z
  ++ [ "\tmovq -48(%rbp), %rax" ]   -- z pointer
  ++ [ "\tmovq %r9,  0(%rax)", "\tmovq %r10, 8(%rax)"
     , "\tmovq %r11, 16(%rax)", "\tmovq %r12, 24(%rax)" ]
  -- epilogue: undo the scratch frame, restore callee-saved in reverse push order
  ++ [ "\taddq $136, %rsp"
     , "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx"
     , "\tpopq %rbp", "\tret" ]

/-- The orchestrator `.s` text (label + globl + body). -/
def dotOrchAsm : String :=
  let header :=
    [ "\t.text", "\t.globl secp256k1_dot", "\t.type secp256k1_dot, @function"
    , "secp256k1_dot:" ]
  let footer := [ "\t.section .note.GNU-stack,\"\",@progbits" ]
  String.intercalate "\n" (header ++ dotOrchBody ++ footer) ++ "\n"

/-- The full self-contained `.s`: the proven `secp256k1_montmul_proven` leaf
    (`Curve4MontMulProvenEmit.secp256k1ProvenAsm`) followed by the
    `secp256k1_dot` orchestrator that composes it twice + the proven add. -/
def dotProvenAsm : String :=
  secp256k1ProvenAsm ++ "\n" ++ dotOrchAsm

/-- Emit the composition `.s` to `gen_com/secp256k1_dot_proven.s`. -/
def emitMainSecp256k1Dot : IO Unit := do
  IO.FS.createDirAll "bench/secp256k1_compare/gen_com"
  IO.FS.writeFile
    "bench/secp256k1_compare/gen_com/secp256k1_dot_proven.s" dotProvenAsm
  IO.println s!"wrote bench/secp256k1_compare/gen_com/secp256k1_dot_proven.s ({dotProvenAsm.toUTF8.size} bytes, symbols secp256k1_montmul_proven + secp256k1_dot)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4DotProvenEmit
