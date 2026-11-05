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
| `encode_framed.lean`, `kat_framed/` | the framed montmul and its known-answer test ([§ The framed function](#the-framed-function)) |
| `import_owned.sh FILE.s MODULE [SYMBOL]`, `translate_owned.awk`, `owned_kernels.txt` | the importer for x86-64 files printed by the compiler's backend ([§ Importing the compiler's backend output](#importing-the-compilers-backend-output)) |
| `reemit_owned.lean`, `compare_owned.sh` | prints the imported functions of the compiler's backend back and compares them with their sources |
| `Makefile` | `import`, `reemit`, `encode`, `compare` (each for both kernels, or `-montmul` / `-montsqr`), `encode-framed`, `framed-kat`, `field`, `import-owned`, `reemit-owned`, `compare-owned` |

The known-answer gate and the timing are the `s2n-reemitted`, `s2n-encoded`,
`s2n-sqr-reemitted` and `s2n-sqr-encoded` arms of
`bench/p384_ecdsa_rust/src/bin/fieldbench.rs` (`make field`); the recorded
figures are in [PERF.md](../p384_ecdsa_rust/PERF.md) of that directory.

## Settings and what runs Lean

`S2N_BIGNUM_DIR` names the s2n-bignum checkout, a directory holding `x86_att/`
and a built `x86/libs2nbignum.a`. The `Makefile`, `import_s2n.sh` and
`compare_insns.sh` read it, as does `bench/p384_ecdsa_rust`; its default is
the checkout of the sibling SSProve-lean tree,
`../SSProve-lean/bench/reference_install/s2n-bignum` relative to the root of
this repository. A target or script that needs the checkout stops with the path
it looked for when the checkout is absent. `make import` also requires the
checkout to be at the commit pinned in `kernels/<kernel>.sh`.

`reemit`, `encode` and `encode-framed` run `lake lean` from the repository
root, which builds the imported modules when needed. `BUILD_PREFIX` is a
command prefix for those commands (for instance a build-lock wrapper), empty by default. `compare` and `field` depend on the files `reemit` and
`encode` write, so they run Lean when those files are older than their Lean
sources. `import` and `framed-kat` run no Lean when their inputs are present:
`framed-kat` needs the framed file `$(FRAMED)`, which `encode-framed` writes.

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
   `s2n-bignum:x86_att/p384/KERNEL.S` from the `x86_att` directory with
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

## Importing the compiler's backend output

`import_owned.sh FILE.s MODULE [SYMBOL]` translates one function of an x86-64 AT&T
file printed by the compiler's backend (`AsmPrinter.renderLeafFn`,
`renderSysVLeafFn`, `LprogAsmPrinter`) into
`CatCrypt/Crypto/SecureCompilation/Ascent/Imported/<MODULE>.lean`, with the same
guarantees as `import_s2n.sh`: an instruction outside the accepted shapes stops the
import with `file:line: message` and exit status 1, and the module is left
unchanged. `SYMBOL` is required when the file defines more than one function. The
module docstring records the file's path in its git repository, that repository's
commit, whether the file is tracked and unchanged there, and its SHA-256. With
`SRC_REV` set in the environment the file is read as it is at that commit of its
repository (`git show`), and the docstring records that commit.
`owned_kernels.txt` lists the imported functions, with an optional fourth column
giving that commit; `make import-owned` regenerates them from `OWNED_ASM` (default
`../SSProve-lean/crates/catcrypt-ed25519/asm`).

The file is read as printed; no preprocessor runs. Comments (`# ...`) are dropped.
A directive or label inside the function stops the import; other functions of the
file are skipped.

### Frame

Kept out of the block, with a check, and written to `<module>Prologue` and
`<module>Epilogue` (`endbr64` and `ret` excepted):

* `endbr64` as the first instruction;
* `pushq` of callee-saved registers at entry, each at most once, and the `popq`
  sequence in reverse order before `ret`;
* one stack allocation `leaq -N(%rsp), %rsp` or `subq $N, %rsp` after the pushes,
  and the release `leaq N(%rsp), %rsp` or `addq $N, %rsp` with the same `N`, which
  must precede the `popq` sequence and `ret`;
* `ret` or `retq`.

In the prologue and epilogue lists, `pushq r` is `lea "%rsp" "%rsp" "%rsp" 0 (-8)`
followed by `storeMem "%rsp" 0 (.reg r)`, and `popq r` is `loadMem r "%rsp" 0`
followed by `lea "%rsp" "%rsp" "%rsp" 0 8`: `lea` writes no flag, as `pushq` and `popq`
write none. The allocation and release are `lea` for `leaq` and `sub`/`add` with an
immediate for `subq`/`addq`, whose flag effects are those of the hardware
instruction. `Ascent.CallFrame` states these lists as `framePro` and `frameEpi` and
proves the frame theorem over them.

Kept as instructions: every `%rsp`-relative move, the red-zone saves of
`renderSysVLeafFn` (`movq %rbx, -8(%rsp)` …) and the argument and callee-saved
stores of the `LprogAsmPrinter` frame (`movq %rdi, 232(%rsp)` …), as
`storeMem "%rsp" off (.reg r)` and `loadMem r "%rsp" off`. These are the forms
`LeafFrame.framePrologue` and `frameEpilogue` use. Offsets are relative to `%rsp`
after the dropped allocation. The importer places the entry run of stores into
`%rsp` slots in segment 1, and the exit run of loads of callee-saved registers,
each from the slot the entry run stored it to, in the last segment. For
`fe25519_mul_x86_from_lean` segment 1 has the six instructions of
`LeafFrame.framePrologue` and the last segment the six of `frameEpilogue`. No
instruction of the body may name `%rsp` as a register, except as a memory base
or `leaq` base.

### Accepted shapes

| source | `JInstr 64` | agreement with `evalInstr` |
|---|---|---|
| `movq %s, %d` / `movq $imm, %d` | `mov d (.reg s)` / `mov d (.imm v)`, `v < 2^64` | `setReg d v`, no flag |
| `movq D(%b), %d` / `movq %s, D(%b)` | `loadMem d b D` / `storeMem b D (.reg s)` | cell `(b, D)`; no flag |
| `movq (%b, %i, k), %d` / `movq %s, (%b, %i, k)`, `k ∈ {1,2,4,8}`, displacement 0 | `loadMemIdx d b i k` / `storeMemIdx b i k (.reg s)` | cell `(b, k·i)`; no flag |
| `movl $imm, %r32`, `imm < 2^32` | `mov r64 (.imm imm)` | the processor zero-extends into the 64-bit register and writes no flag |
| `leaq D(%b), %d` | `lea d b b 0 D` | `b + b·0 + D = b + D`; no flag |
| `leaq D(%b, %i, k), %d` | `lea d b i k D` | `b + i·k + D`; no flag |
| `addq` `subq` `adcq` `sbbq` `andq` `orq` `xorq` with `%s` or `$imm`, `imm < 2^31` | `add` `sub` `adc` `sbb` `and_` `or_` `xor_` | Jasmin's five-flag results; below `2^31` the sign-extended `imm32` is the value `BitVec.ofNat 64 imm` |
| `addq D(%b), %d` | `addMem d b D` | `x86_ADD` with the cell |
| `shlq` `shrq` `sarq` `$k, %d`, `1 ≤ k ≤ 63` | `shl` `shr` `sar` | count 0 is refused: the processor leaves the flags unchanged, `x86_SHL` makes them undefined |
| `negq %d` | `neg d` | `x86_NEG` |
| `imulq %s, %d` | `imul d (.reg s)` | low word, `OF = CF` the signed overflow, `SF`/`ZF`/`PF` undefined (as in the SDM) |
| `imulq $imm, %s, %d`, `imm < 2^31` | `imulri d s imm` | `x86_IMULt (get s) imm` |
| `mulx` / `mulxq %s, %lo, %hi`, `mulxq D(%b), %lo, %hi`, `lo ≠ hi` | `mulx hi lo (.reg "%rdx") (.reg s)` / `mulxMem hi lo (.reg "%rdx") b D` | unsigned `%rdx · src`, no flag |
| `adcx` / `adcxq`, `adox` / `adoxq` with `%s` or `D(%b)` | `adcx` `adox` / `adcxMem` `adoxMem` | carry to `CF` / `OF` only |
| `btq $k, %r`, `k < 64` | `bt r (.imm k)` | writes `CF` = bit `k` only; see below |
| `setc %r8` (or `setb`) followed by `movzbq %r8, %r64` of the same register | `setc r64` | `evalInstr_setc_eq_setcc_movzx`: the pair writes `CF` zero-extended, no flag |
| `setc %r8` not so followed | `setcc .b r64` | low byte under `MSB_MERGE` |
| `movzbq %r8, %r64` not after `setc` | `movzx d 8 s` | low 8 bits of `s`, no flag |
| `testq %s, %d` | `test d (.reg s)` | `x86_TEST`, no register written |
| `cmovneq` `cmovnzq` / `cmoveq` `cmovzq` / `cmovbq` `cmovcq` with registers | `cmovne` / `cmove` / `cmovb` | reads `ZF` / `ZF` / `CF` |
| `call SYM` | ends a `CallSeg` run with `callee := some SYM` | outside `JasminModel` |

`%r8` stands for a low-byte register (`%al`, `%bl`, `%cl`, `%dl`, `%sil`, `%dil`,
`%bpl`, `%r8b` … `%r15b`); `%ah` and the other high-byte registers are refused.

The Intel SDM leaves `OF`, `SF` and `PF` undefined after `BT`; `evalInstr` keeps
their previous values, as Jasmin's `x86_BT` does. The importer refuses an `adox`
(the one accepted instruction that reads `OF`) between a `btq` and the next
instruction that writes `OF`. No accepted instruction reads `SF` or `PF`.

Refused, among others: `movl $imm, D(%b)`, which writes the low 4 bytes of an
8-byte cell and has no counterpart in the word-granular `JState.store`; any jump;
an indexed memory operand with a nonzero displacement; an immediate at or above
`2^31` in a sign-extended position.

### Functions with calls

`JInstr` has no call instruction. A function containing `call` is imported as a
`List CallSeg` (`Ascent/Imported/CallSeg.lean`): each element is a run of
instructions and the symbol of the call that ends it, or `none`. The function is
the concatenation of the runs with each recorded call after its run. The module
states the instruction count over `CallSeg.instrs` and the call count over
`CallSeg.callees`. A proof over such a function supplies a specification of each
callee.

### Memory model

`JasminModel` keys memory by the name of the base register and an offset, one
word per cell. A proof over an imported block is a statement about that model. It
agrees with the processor when each base register holds one address throughout
the block and distinct names address disjoint words. The importer lists in the
module docstring the base registers it sees violate the first condition: a
register written between two memory accesses through it (`%r14` in
`sc_reduce`, `sc_muladd`, `pack_sign`, `join16`), and a register set by `leaq`
from another register before a memory access through it (`%r9` from `%rsp` in
`madd`, which reads the result of `join16` through `%r9` while `join16` wrote it
through its own argument register).

### Segments and count lemmas

A segment ends after a call, after the entry run of `%rsp` stores, before the exit
run of `%rsp` loads, and after 32 instructions (`MAXSEG`). A block of more than 16
segments is grouped in parts of at most 16 segments, each with a count lemma
(`…Part01_length`, or `…Part01_instrs` and `…Part01_calls`), and the block lemma
rewrites with the part lemmas. A single `simp only [List.length_append]; rfl` over
138 segments of 32 instructions exceeds the default recursion depth; over 16
segments of 32 it elaborates without error, as does the block lemma over the parts.

### Imported functions

| module | function | instructions | calls | segments | parts |
|---|---|---|---|---|---|
| `Fe25519MulShipped` | `fe25519_mul_x86_from_lean` | 108 | 0 | 5 | 0 |
| `Fe25519SqrShipped` | `fe25519_sqr_x86_from_lean` | 95 | 0 | 3 | 0 |
| `Fe25519AddShipped` | `fe25519_add_x86_from_lean` | 46 | 0 | 2 | 0 |
| `Fe25519SubShipped` | `fe25519_sub_x86_from_lean` | 27 | 0 | 1 | 0 |
| `Ed25519CombSelectShipped` | `ed25519_comb_select_x86_from_lean` | 168 | 0 | 6 | 0 |
| `Ed25519CompressShipped` | `ed25519_compress_x86_from_lean` | 15 | 4 | 4 | 0 |
| `Ed25519PackSignShipped` | `ed25519_pack_sign_x86_from_lean` | 51 | 0 | 4 | 0 |
| `Ed25519MaddShipped` | `ed25519_madd_x86_from_lean` | 98 | 15 | 18 | 2 |
| `Ed25519Join16Shipped` | `ed25519_join16_x86_from_lean` | 102 | 0 | 5 | 0 |
| `Ed25519InvertShipped` | `ed25519_invert_x86_from_lean` | 543 | 265 | 265 | 17 |
| `Ed25519ScReduceShipped` | `ed25519_sc_reduce_x86_from_lean` | 3540 | 0 | 113 | 8 |
| `Ed25519ScMuladdShipped` | `ed25519_sc_muladd_x86_from_lean` | 4354 | 0 | 138 | 9 |
| `Ed25519PointAddShipped` | `ed25519_point_add` (file `ed25519_point_add_x86_from_lean`) | 4859 | 0 | 154 | 10 |

Not imported:

* the file `ed25519_comb_table_from_lean` of `OWNED_ASM`: `.quad` data, no instructions.

### Round trip

`reemit_owned.lean` prints each imported block with `AsmPrinter.renderBlockBody`
under the identity allocation, each call as `call SYM`, between its prologue and
epilogue printed back as `pushq`, `popq` and the allocation and release, to
`gen/owned/<MODULE>.s` (`make reemit-owned`). `compare_owned.sh [MODULE ...]`
removes a leading `endbr64` and the trailing `ret` from the source function (at the
commit of the manifest's fourth column, when present) and compares the two line by
line after this normalisation, applied to both sides:

* comments removed, whitespace collapsed, one space after each comma;
* `setb` is `setc`, `adcx` is `adcxq`, `adox` is `adoxq`, `mulx` is `mulxq`, `retq`
  is `ret`, `callq` is `call`, `cmovnzq` is `cmovneq`, `cmovzq` is `cmoveq`,
  `cmovcq` is `cmovbq`;
* `movl $v, %r32` is `movq $v, %r64`;
* a memory operand `(…)` is `0(…)`;
* `D(%b, %b, 0)` is `D(%b)`.

The spellings differ because the printers differ: `AsmPrinter` prints `setb` for
`setc`, `adcx`/`adox` without suffix, `mulx` with a `# src1=` comment, and
`D(%b, %b, 0)` for the index-free `lea`, which the assembler rejects (scale 0); the
files of the compiler's backend print `setc`, `adcxq`, `(%r10)` and `leaq D(%b)`. `make compare-owned`
exits 1 on any difference.
