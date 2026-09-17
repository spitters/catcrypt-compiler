# Importing s2n-bignum kernels

This directory takes two of s2n-bignum's hand-written x86-64 kernels modulo `p_384`,
the Montgomery multiplication `bignum_montmul_p384` and the Montgomery squaring
`bignum_montsqr_p384`, into CatCrypt's scalar machine IR `JInstr 64`. It prints them
back to assembly with CatCrypt's own x86 printer, encodes them with CatCrypt's byte
encoder, and checks the results against s2n-bignum.

| file | role |
|---|---|
| `import_s2n.sh KERNEL`, `translate.awk` | the importer: source `.S` to the Lean module `CatCrypt/Crypto/SecureCompilation/Ascent/Demos/<ident>.lean` |
| `kernels/<kernel>.sh` (`kernels/bignum_montmul_p384.sh`, `kernels/bignum_montsqr_p384.sh`) | per kernel: the module name, the pinned commit and SHA-256, and the kernel-specific docstring text |
| `reemit.lean`, `reemit_montsqr.lean` | prints the imported block with `AsmPrinter.renderBlockBody` and `renderLeafFn` to `gen/<kernel>_reemitted.s` |
| `encode.lean`, `encode_montsqr.lean` | encodes the imported block with `ScalarEncoder.encodeJBlock` and writes the bytes as `.byte` directives to `gen/<kernel>_encoded.s` |
| `compare_insns.sh [KERNEL]` | assembles the re-emitted and encoded files and compares their disassembly and size with the s2n-bignum archive |
| `Makefile` | `import`, `reemit`, `encode`, `compare` (each for both kernels, or `-montmul` / `-montsqr`), `field` |

The known-answer gate and the timing are the `s2n-reemitted`, `s2n-encoded`,
`s2n-sqr-reemitted` and `s2n-sqr-encoded` arms of
`bench/p384_ecdsa_rust/src/bin/fieldbench.rs` (`make field`).

| kernel | module | body instructions | archive / re-emitted / encoded bytes |
|---|---|---|---|
| `bignum_montmul_p384` | `S2nMontmulP384` (17 segments) | 264 | 1206 / 1257 / 1332 |
| `bignum_montsqr_p384` | `S2nMontsqrP384` (21 segments) | 230 | 1063 / 1117 / 1174 |

The byte counts are function sizes including the 14-instruction frame
(`compare_insns.sh`).

## Encoding

`encode.lean` writes `encodeJBlock s2nAlloc s2nMontmulP384Block`, where `s2nAlloc`
maps each canonical `%rN` name to itself, inside s2n-bignum's frame written as
text. `Ascent.Demos.S2nMontmulP384Bytes.s2nMontmulP384_decode` proves that these
body bytes decode, by CatCrypt's decoder, to the imported block, and
`s2nMontmulP384Bytes_correct` that the decoded instructions compute the Montgomery
product under `JasminModel`. The frame lines are outside both theorems. Whether the
decoder and `JasminModel.evalInstr` agree with the processor on these instructions
is not proved; the `s2n-encoded` known-answer gate tests the bytes against
`bignum_montmul_p384`.

The body is 1307 bytes and the assembled function 1332, against 1206 for
s2n-bignum's object and 1257 for the re-emitted file. The encoded and re-emitted
functions disassemble to the same 278 instructions; the 75-byte difference is the
25 `adcq $0` / `sbbq $0` instructions, which the encoder writes as `81 /digit imm32`
(7 bytes) where the assembler selects `83 /digit imm8` (4 bytes).

`encode_montsqr.lean` writes `encodeJBlock idAlloc s2nMontsqrP384Block` with the same
identity allocation, after checking `encodableJBlock` and that every instruction is in
`encodableJInstr`. No theorem is stated over the square's block or its bytes; the
`s2n-sqr-encoded` gate tests them against `bignum_montsqr_p384`. The encoded body is
1149 bytes. The encoded, re-emitted and archive functions disassemble to the same 244
instructions up to the widened forms below; the 57-byte difference between encoded and
re-emitted is the 19 `adcq $0` / `sbbq $0` instructions, in the same two forms.

## The framed function

`encode_framed.lean` writes `bignum_montmul_p384_framed`: the encoder's bytes for
`S2nMontmulP384FramedBlock`, which is `LeafFrame.framePrologue`, the imported block and
`LeafFrame.frameEpilogue`. The prologue stores the six System V callee-saved registers
in the red zone (`movq %rbx, -8(%rsp)` … `movq %r15, -48(%rsp)`) and the epilogue loads
them back. Only `endbr64`, `retq` and the section directives are literal text; the body
is 1367 bytes.

`Ascent.Demos.S2nMontmulP384.s2nMontmulP384FramedBytes_correct` states that these bytes
decode to 276 instructions which, under `JasminModel.runBlock`, compute the Montgomery
product and leave `%rsp` and the six callee-saved registers as they were on entry. The
theorem uses the name-keyed memory of `JasminModel`, in which the red-zone slots are the
bank `"%rsp"`. That the red zone is disjoint from the caller's buffers is the System V
convention and is assumed. `ret` is not modelled.

`make framed-kat` assembles the file with `kat_framed/kat.c` and
`kat_framed/check_saved.s` against `libs2nbignum.a`. It compares the output with
`bignum_montmul_p384` on 200000 random pairs below p384 and 16 edge pairs, including
the in-place calls `z = x` and `z = x = y`, and checks the six callee-saved registers
across one call: 0 mismatches.

## The importer is untrusted

The importer is a shell script and an awk program with no proof about them. Its
output, the `JInstr 64` list, is the object a correctness proof is stated over:
the list is shown to compute `x * y * 2^(-384) mod p_384` against the `JasminModel`
semantics, so an importer defect either makes that proof fail or changes nothing
the proof relies on. The differential gate here checks that the list, printed
back, is s2n-bignum's program; it is evidence about the importer, not a
substitute for the proof.

## The translation

0. Reads `kernels/<kernel>.sh` (`kernels/bignum_montmul_p384.sh`, `kernels/bignum_montsqr_p384.sh`) and refuses to run unless the checkout is at the pinned
   commit, the source file has no local change, and its SHA-256 equals the pinned
   value.
1. Runs the C preprocessor (`cpp`, or `$CPP`) over
   `x86_att/p384/KERNEL.S` from the `x86_att` directory with
   `-I ../include`, keeping line markers so each instruction carries its source
   line.
2. Splits each preprocessed line on `;`, which separates the instructions of one
   macro expansion.
3. Checks the frame and drops it: after the function label, an optional CET
   landing pad (`endbr64`, or its `.byte` spelling), `pushq` of callee-saved
   registers; at the end, `popq` of the same registers in reverse order and one
   `retq`. `.cfi_*` directives inside the function are dropped; any other
   directive or label inside the function stops the import.
4. Translates each remaining instruction to one `JInstr 64` constructor.
   Registers keep their physical names (`"%rax"`, …), so there is no allocation.
5. Records the checkout's commit and the source file's SHA-256 in the module
   docstring.
6. Groups the list into segments, one per paragraph of the source (a run of
   instructions with no blank or comment-only line between them). A paragraph of
   more than 22 instructions is divided into near-equal parts at preprocessed-line
   boundaries, so a macro expansion stays in one segment. No paragraph of
   `bignum_montmul_p384` is divided; in `bignum_montsqr_p384` the squaring paragraph
   (35 instructions) becomes two segments and the six `montreds` lines (108) six.

The length theorem evaluates each segment's length by `rfl`. For
`bignum_montsqr_p384`, `simp only [s2nMontsqrP384Block, List.length_append]` exceeds
200000 heartbeats at `whnf`, while `unfold s2nMontsqrP384Block` followed by the same
`simp only [List.length_append]; rfl` elaborates without error; new kernels use the
second form, and `bignum_montmul_p384` keeps the first (`length_tactic` in its
parameter file).

## Accepted shapes

Any instruction outside this table stops the import with `file:line: message` on
stderr and exit status 1, and the Lean module is left unchanged.

| source | `JInstr 64` |
|---|---|
| `movq %s, %d` / `movq $imm, %d` | `mov d (.reg s)` / `mov d (.imm v)`, any 64-bit value |
| `movq disp(%b), %d` / `movq %s, disp(%b)` | `loadMem d b disp` / `storeMem b disp (.reg s)` |
| `addq` `subq` `adcq` `sbbq` `xorq` `andq` `orq` with `%s` or `$imm` | `add` `sub` `adc` `sbb` `xor_` `and_` `or_`; the immediate must be below `2^31` |
| `addq disp(%b), %d` | `addMem d b disp` |
| `shlq` `shrq` `sarq` `$imm, %d` | `shl` `shr` `sar`, count below 64 |
| `adcxq` `adoxq` with `%s` or `disp(%b)` | `adcx` `adox` / `adcxMem` `adoxMem` |
| `mulxq %s, %lo, %hi` / `mulxq disp(%b), %lo, %hi` | `mulx hi lo (.reg "%rdx") (.reg s)` / `mulxMem hi lo (.reg "%rdx") b disp`; `lo` and `hi` distinct |
| `cmovnzq` `cmovneq` / `cmovzq` `cmoveq` / `cmovbq` `cmovcq` with `%s` | `cmovne` / `cmove` / `cmovb` |
| `xorl %r32, %r32`, one register | `xor_ r64 (.reg r64)` |
| `movl $imm, %r32`, immediate below `2^32` | `mov r64 (.imm v)` |
| `adcl %r32, %r32`, one register, see below | `adc r64 (.reg r64)` |

Memory operands take a 64-bit base register and an optional literal displacement,
no index. `%rsp` is not an accepted register.

The three 32-bit forms are translated to 64-bit forms with the same register
value and the same flags:

* `xorl %r, %r` writes 0 to the whole 64-bit register and sets `CF = OF = SF = 0`,
  `ZF = PF = 1`, as `xorq` does.
* `movl $imm, %r` zero-extends the immediate into the 64-bit register and writes
  no flag, as a 64-bit move of the same value does.
* `adcl %r, %r` is equal to `adcq %r, %r` only when the register is 0: both
  then compute `CF` with the same flags. The importer accepts it only when the
  previous instruction touching the 64-bit register (explicitly, as a memory base,
  or as the implicit `%rdx` of `mulxq`) is `xorl` zeroing that register, on the
  same preprocessed line, which is the same macro expansion. In
  `bignum_montmul_p384` this is `adcl %ebp, %ebp` in `montredc`;
  `bignum_montsqr_p384` has no `adcl`.

`bignum_montsqr_p384` uses 2 `xorl` and 17 `movl` (among them `movl $0, %ebx`
before `adcq %rbx, %rbx` in `montreds`), and 4 `xorq %r, %r`, which the table
already covers.

The printer writes the 64-bit forms, so the re-emitted object differs from
s2n-bignum's in the encoding of exactly those 29 instructions (`xor %ebp,%ebp`
becomes `xor %rbp,%rbp`, `mov $0xffffffff,%ebx` becomes `movabs`); every other
instruction disassembles identically. `compare_insns.sh` prints the difference. For
`bignum_montsqr_p384` the widened instructions are the 19 `xorl`/`movl` forms: `mov $0x0`
and `mov $0x1` on 32-bit registers become 64-bit `mov`, `mov $0xffffffff` becomes
`movabs`, `xor %ebp,%ebp` becomes `xor %rbp,%rbp`.

## Re-emission

`reemit.lean` uses the identity register allocation on the block's names and
checks that each name is a 64-bit general register. Its prologue and epilogue are
s2n-bignum's frame (`endbr64`, six `pushq`, six `popq`, `retq`), written as text:
like every `renderLeafFn` frame they are outside the translated block.
