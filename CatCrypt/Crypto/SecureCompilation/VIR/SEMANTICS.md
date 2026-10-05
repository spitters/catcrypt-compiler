# Operation semantics against LLVM, MLIR and Rust

The compiler's intermediate representations are expected to follow the semantics of
LLVM IR (LangRef) and of the MLIR `arith` dialect. This document enforces one rule:
a deviation from LLVM semantics is either removed or stated here with its principle
and with the side condition or theorem that discharges it. A row whose status is
"deviates, to be fixed" names a defect and its proposed repair.

Paths are relative to `CatCrypt/Crypto/SecureCompilation/` unless they start with
`Jasmin/` (under `CatCrypt/Crypto/`) or `HaxAscent/` (package root). Declarations of
the two dependencies, hax-lean (`Hax.*`, `UScalar.*`, `IScalar.*`) and the VeIR fork
(`Veir.*`, `LLVM.Int.*`), are cited by name only. `w` is the bit width of an operand.

## Status values

| Status | Meaning |
|---|---|
| follows LLVM | the value equals that of the LLVM operation, or of a fixed composition of LLVM operations, wherever LLVM defines one |
| deviates, principled | the value differs from LLVM's, or is defined where LLVM gives poison or undefined behaviour; a principle justifies it and a named condition or theorem discharges the difference |
| deviates, to be fixed | a defect; the row gives the declaration and the proposed repair |
| VeIR deviates from LLVM | the VeIR interpreter differs from LangRef; our semantics are judged against LangRef |

## Principles

Each principled row cites one of these.

- P1, totality. Every denotation from `semScalar` downwards is a total function on
  `BitVec` and `Bool`; poison and undefined behaviour do not occur, because the fronts
  (hax from safe Rust, Jasmin) produce only programs whose LLVM counterparts are free
  of undefined behaviour. A total value refines a poison value; `veirRunCom_refines`
  states this for the `arith` fragment.
  At the runtime layer the same holds with the panic conditions of Rust (zero
  divisor, `MIN` divided by −1, overflow) as obligations of the source program.
- P2, shifts. A shift by an amount of at least `w` denotes 0, or the sign fill for an
  arithmetic right shift, as Jasmin's `wshl`, `wshr` and `wsar` do. Every lowering to
  a machine shift carries the condition that the amount is below `w`. The condition
  holds of a source program proved panic-free, since the reference semantics of the
  Rust operators panics on such an amount.
- P3, overflow. Addition, subtraction and multiplication wrap modulo `2^w` in the
  IR, which is LLVM's value without `nsw` or `nuw`. The overflow panic of checked
  Rust arithmetic is an obligation of the front.
- P4, memory. Memory is a total map. Bounds, separation and initialisation are safety
  properties, discharged by static checks on the emitted block and by the absence of
  `unsafe` in the covered source language.
- P5, machine models. A machine model follows the manual of its instruction set. Where
  LLVM gives poison, the defined machine value refines it, and the lowering carries
  the condition under which machine value and IR value agree.
- P6, untagged runtime names. An untagged runtime operation computes on unbounded
  integers. It agrees with the Rust operation wherever the operand type makes the two
  coincide (unsigned division, non-overflowing arithmetic); the printer emits the
  width-tagged operation in every other case. An untagged name reaching the runtime
  at a type where the two differ is a defect of the adapter.

## Reference semantics

| Operation class | LLVM (LangRef section) | MLIR `arith` | Rust |
|---|---|---|---|
| Shift, amount ≥ `w` | poison ("shl", "lshr", "ashr") | poison (`shli`, `shrui`, `shrsi`) | panic under overflow checks; `wrapping_shl` and `wrapping_shr` reduce the amount modulo `w` (Reference, "Arithmetic and Logical Binary Operators", "Overflow") |
| Division, remainder | zero divisor: undefined behaviour; `sdiv`, `srem` of `MIN` by −1: undefined behaviour; quotient rounds toward zero; remainder has the sign of the dividend ("udiv", "sdiv", "urem", "srem") | same (`divui`, `divsi`, `remui`, `remsi`) | panic on a zero divisor and on `MIN` divided by −1, with or without overflow checks; same rounding; `checked_div` returns `None` |
| Add, sub, mul | wrap; poison on overflow under `nsw` or `nuw` ("add", "sub", "mul") | wrap (`addi`, `subi`, `muli`) | panic under overflow checks, wrap otherwise; `wrapping_*`, `checked_*`, `saturating_*`, `overflowing_*` method documentation |
| Comparison, select | `i1` result ("icmp"); a poison condition gives poison, the unselected arm does not propagate ("select") | `cmpi`, `select` | `bool` |
| Casts | "trunc .. to", "zext .. to", "sext .. to" | `trunci`, `extui`, `extsi` | `as`: truncation, zero extension of an unsigned source, sign extension of a signed source (Reference, "Type cast expressions") |
| Rotate | amount modulo `w` ("llvm.fshl", "llvm.fshr") | none | `rotate_left`, `rotate_right`: amount modulo `w` |
| Carry, wide multiply | "llvm.uadd.with.overflow", "llvm.umul.with.overflow"; no three-input add | `addui_extended`, `mului_extended` | `overflowing_add`, `widening_mul` |
| Memory | out-of-bounds access and access below the stated alignment: undefined behaviour ("load", "store", "Pointer Aliasing Rules"); uninitialised memory reads as undef ("Undefined Values") | `memref.load`, `memref.store` | safe Rust: bounds-checked indexing with panic, no uninitialised read |
| Poison, undefined behaviour | "Poison Values", "Undefined Values" | inherited | none in safe Rust |

## Layer 1: hax runtime and `RustExec`

The hax runtime (hax-lean, namespace `Hax`) interprets extracted Rust over `Int`.
A name tagged with a width (`op_w w`, `op_iw w`) is the operation at that width; an
untagged name is the operation on unbounded integers. The tables in
`HaxAscent/RustSemantics/Arith.lean`, `HaxAscent/RustSemantics/Bitwise.lean` and
`HaxAscent/RustSemantics/Casts.lean` relate each runtime name to the checked scalar
operation (`UScalar.*`, `IScalar.*`), either by a proved square or by a refuted one.

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| Untagged `+ - *` | unbounded `Int` (`Hax.add`, `Hax.sub`, `Hax.mul`) | wrap | panic or wrap | deviates, principled | P3: the unbounded result equals the checked scalar result whenever that result is not a panic. `add_u_square`, `add_i_square`, `sub_u_square`, `mul_u_square`; the panic itself is `UScalar.tryMk` |
| `wrapping_add#w`, `wrapping_mul#w`, signed forms | residue modulo `2^w` (`Hax.wrapping_add_w`, `Hax.wrapping_mul_w`, `Hax.wrapping_add_iw`) | wrap | `wrapping_*` | follows LLVM | `wrapping_add_w_u_square`, `wrapping_mul_w_u_square`, `wrapping_add_iw_square` |
| Untagged `wrapping_add`, `wrapping_mul` at `Int` | `a + b`, `a * b` without reduction (`Hax.wrapping_add`, `Hax.wrapping_mul`) | wrap | `wrapping_*` | deviates, to be fixed | Defect: hax-lean runtime, `Hax.wrapping_add` and `Hax.wrapping_mul` at `Int` do not wrap (`wrapping_add_u_counterexample`, `wrapping_mul_u_counterexample`). Fix: the printer emits the width-tagged name at every scalar type; the untagged instance is restricted to fixed-width carriers |
| Untagged `/`, `%` | Lean `Int` division, which rounds toward −∞: −7 / 2 = −4, −7 % 2 = 1 (`Hax.div`, `Hax.rem`) | truncating: −3, −1 | truncating | deviates, principled | P6: the printer routes a signed, width-tagged division to `Hax.div_iw` and `Hax.rem_iw` (`PrettyPrint.widthAwareRuntime`) and emits the untagged name at unsigned operands, where the two roundings agree (`div_u_square`, `rem_u_square`). On a signed operand the untagged name disagrees with Rust (`div_i_counterexample`, `rem_i_counterexample`); it reaches the runtime only when the adapter omits the width tag, which is open repair 1 |
| Zero divisor; `MIN` divided by −1 | a total value: Lean's quotient by 0 is 0 and its remainder by 0 is the dividend (`Hax.div`, `Hax.rem`); `Hax.div_iw` gives 0 and `Hax.rem_iw` the reduced dividend; `Hax.div_iw` wraps `MIN` divided by −1 | undefined behaviour | panic | deviates, principled | P1 at the runtime layer: Rust panics on these inputs, and the squares against the checked operations (`UScalar.div`, `IScalar.div`) are stated where those return a value. No Lean theorem states that an extracted program is free of these panics; the front does not prove it |
| `Div#iw`, `Rem#iw`, nonzero divisor, no overflow | truncating (`Hax.div_iw`, `Hax.rem_iw`) | truncating | truncating | follows LLVM | by definition (`Int.tdiv`, `Int.tmod`) |
| `Shl#w`, `Shr#w`, amount ≥ `w` | unbounded shift, then reduction: 0 (`Hax.shl_w`, `Hax.shr_w`) | poison | panic | deviates, principled | P2. `shl_w_u_square`, `shr_w_u_square`, `shl_iw_square`, `shr_iw_square` relate the value to the checked operation wherever that operation returns |
| Untagged `Shl`; untagged signed `Shr` | no truncation (`Hax.shl`); a negative operand shifts as 0 (`Hax.shr`) | `shl`, `ashr` | `<<`, `>>` | deviates, to be fixed | Defect: hax-lean runtime, `Hax.shl` and `Hax.shr` at `Int` (`shl_u_counterexample`, `shl_i_counterexample`, `shr_i_counterexample`). Fix: as for untagged `wrapping_add` |
| `rotate_right#w` | amount modulo `w` (`Hax.rotate_right_w`) | `llvm.fshr` | `rotate_right` | follows LLVM | `rotate_right_w_u_square` |
| Untagged `rotate_right` | correct at `u64` only (`Hax.rotate_right`) | `llvm.fshr` | `rotate_right` | deviates, to be fixed | Defect: hax-lean runtime, `Hax.rotate_right` at widths other than 64 (`rotate_right_u32_counterexample`, `rotate_right_i_counterexample`). Fix: as for untagged `wrapping_add` |
| Casts | residue modulo `2^w` (`Hax.cast_uw`); checked scalars `UScalar.cast`, `IScalar.cast` | `trunc`, `zext`, `sext` | `as` | follows LLVM | `cast_u_square`, `cast_iu_square`, `cast_ii_square`, `cast_ui_square` |
| `RustExec` scalar expressions | unbounded `Nat`, saturating `SSub`, unbounded `SShl` (`SExpr.evalState`, `SExpr.eval`; `Jasmin/LowCTExec.lean`) | wrap | `saturating_sub` for `SSub` | deviates, principled | `RustExec` is the referent for `saturating_sub`, counters, indices and values below `2^64` only; wrapping kernels refer to `semScalar`. `SExpr.inRange`, `SExpr.evalBV_eq_ofNat_eval`, `rustExec_semScalar_agree` |

## Layer 2: LowCT `semScalar`

`semScalar` (`Dialects/TranslateDialectScalarDenote.lean`) evaluates scalar
expressions by `SExpr.evalBV` (`Jasmin/LowCTSExpr.lean`) on 64-bit words. The layer
has one scalar type, so a truth value is the word 0 or 1.

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| `SAdd`, `SSub`, `SMul` | wrap modulo `2^64` (`SExpr.evalBV`) | wrap | `wrapping_*` | follows LLVM | P3 for the checked source operators |
| `SShl`, `SShr`, amount ≥ 64 | 0 (`a <<< b.toNat`) | poison | panic | deviates, principled | P2. The shift arms of `SExpr.inRange` require the amount below 64 |
| `SAsr`, amount ≥ 64 | sign fill | poison | panic | deviates, principled | P2, with the same source condition |
| `SLt` | unsigned comparison; result the word 0 or 1 | `icmp ult`, then `zext` to `i64` | `<` on `u64`, then `as u64` | follows LLVM | a composition of two LLVM operations |
| `RSelect`, φ-merge | second source when the selector word is nonzero (`selectWord`, `phiSelect`) | `icmp ne 0`, then `select` | `if s != 0` | follows LLVM | a composition; a lowering to `arith.select` inserts `cmpi ne 0` |
| `SMulHiU`, `SMulHiS`, `SMulS` | high half of the unsigned or signed 128-bit product; signed low product (`sexprMulHiU`, `sexprMulHiS`) | `mul` at `i128` and `lshr` or `ashr`; `mului_extended`, `mulsi_extended` | `widening_mul` | follows LLVM | by definition |

## Layer 3: the crypto and Jasmin dialects (`Com`)

Denotations are in `VIR/JasminDialect.lean` and `VIR/CatCryptDialect.lean`. Neither
dialect has a division, remainder or bit-counting operation, and `JasminCmp` has the
predicates `eq`, `ne`, `ult`, `ule`, `ugt`, `uge` only. A division added later follows
LLVM, with the nonzero-divisor and no-overflow guards as obligations of the front.

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| `add`, `sub`, `mul`, `and`, `or`, `xor` | wrap; bitwise (`JasminBinOp.apply`) | same without flags | `wrapping_*`, `& \| ^` | follows LLVM | P3 for the checked source operators |
| Variable `shl`, `shr`; `bvShiftLV`, `bvShiftRV`; amount ≥ `w` | 0 (`a <<< b.toNat`, `JasminBinOp.apply`) | poison | panic | deviates, principled | P2. `ComShiftSafe` (VeIR route, `veirRunCom_eq`); `IsScalarUn` (x86 route, `lowerUn_get_dst`) |
| Immediate `shlImm`, `shrImm`, `sarImm`; `bvShiftL`, `bvShiftR`, `bvShiftRA`; `n` ≥ `w` | 0, or sign fill for the arithmetic shift | poison | compile-time error or panic | deviates, principled | P2; the amount is static. `IsScalarUn` (`k < 64`), `shiftCount_imm` |
| `rorImm`; `bvRor`, `bvRol` | `rotateRight n`, `rotateLeft n`: amount modulo `w` | `llvm.fshr`, `llvm.fshl` | `rotate_right`, `rotate_left` | follows LLVM | by definition |
| `cmp` | `BitVec 1`, 1 when the relation holds (`cmpBit`, `JasminCmp.holds`); `bvEq` returns `Bool` | `icmp` to `i1`; `cmpi` | `bool` | follows LLVM | by definition |
| `select`; `ite` | first arm when the condition is `1#1` (`selectW`) or `true` | `select` | `if` | follows LLVM | P1: no operand is poison |
| `castW` | `zeroExtend`: zero extension or truncation | `zext`, `trunc`; `extui`, `trunci` | `as` from an unsigned source | follows LLVM | no sign-extending cast exists in `jasminDialect` |
| `bitToSword` | all ones or 0 | `sext` of `i1`; `extsi` | `(b as iN).wrapping_neg()` | follows LLVM | emitted as `arith.extsi` by the bridge |
| `MlirArithDialect.extsi` | all ones or 0 (`VIR/MlirArithDialect.lean`) | `sext` of `i1`; `arith.extsi` | `(b as iN).wrapping_neg()` | follows LLVM | `agree_bitToSword`: equal to `bitToSword` by `rfl` |
| `addCarryLo`, `addCarryHi` | `a + b + cin` and its carry-out, `cin : BitVec 1` (`addCarryWord`, `carryOutBit`) | two `llvm.uadd.with.overflow` and an `or`; `addui_extended` has no carry-in | two `overflowing_add` | follows LLVM | a composition; the three-input form matches x86 `ADC`, `ADCX`, `ADOX` |
| `bvAdd64` | `(carry, sum)`, the carry as a `w`-bit word 0 or 1 | `llvm.uadd.with.overflow`, then `zext` | `overflowing_add` | follows LLVM | a composition; the result order is (carry, sum), LLVM's is (sum, carry) |
| `bvAdc` | carry-in `cin : BitVec w`; any nonzero value counts as 1 | carry is `i1` | `bool` | deviates, to be fixed | Defect: `VIR/CatCryptDialect.lean`, op `bvAdc`, accepts a `w`-bit carry-in and tests `cin.toNat ≠ 0`. Fix: a one-bit carry-in, as `addCarryLo` has |
| `mulhi`; `bvMulHi` | high half of the unsigned double-width product (`mulHiW`) | `mului_extended`, high result | `widening_mul` | follows LLVM | by definition |
| `andn` | `(~~~a) &&& b`: the first operand is complemented (`JasminBinOp.apply`) | no operation; `xor a, -1` then `and` | `!a & b` | deviates, principled | The order is that of x86 BMI1 `ANDN`; RISC-V `andn` complements the second operand. No side condition: the denotation fixes the order, and a lowering to another instruction set permutes the operands |
| Array read and write | index reduced modulo the length; an empty array reads 0 (`stackGet`, `stackSet`, `memGetDyn`, `memSetDyn`, `memWGetDyn`) | out of bounds: undefined behaviour | panic | deviates, principled | P4. `idxOkB` and the checked step `evalInstrPMemFk` reject an index at or above the length |

## Layer 4: `Lprog` and the instruction-set layer

`Lprog` instructions are evaluated by `applyOpn` (`VIR/JasminLsem.lean`); the `Isa`
record (`VIR/LprogIsa.lean`) runs them over a register file, flags and name-keyed
arrays (`LstateM`, `VIR/JasminLsemMem.lean`).

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| Two-source `SHL`, `SHR`, amount ≥ `w` | 0 (`a <<< b.toNat`, `applyOpn`) | poison | panic | deviates, principled | P2, the value of layer 3 unchanged. `IsScalarUn` at the lowering to x86 |
| Count-tagged `SHL:k`, `SHR:k`, `SAR:k` | shift by the literal `k` | poison for `k` ≥ `w` | as layer 3 | deviates, principled | P2. `IsScalarUn`, `shiftCount_imm` |
| Count-tagged `ROL:k`, `ROR:k` | `rotateLeft k`, `rotateRight k` | `llvm.fshl`, `llvm.fshr` | `rotate_*` | follows LLVM | by definition |
| Indexed load and store | name-keyed arrays, index as in layer 3; with the check flag, `none` out of bounds | undefined behaviour | panic | deviates, principled | P4. `idxOkB`, `evalInstrPMemFk` (`VIR/JasminLsemMemChecked.lean`) |

## Layer 5: machine models

x86 has the decoded-bytes machine `x86Mach` (`X86Backend/X86Isa.lean`) over the
address memory `AMem` (`Ascent/AddrMem.lean`). ARM and RISC-V have instruction models
with encoder and decoder round trips (`ARMBackend/ArmModel.lean`,
`RISCVBackend/RiscvModel64.lean`, memory `Mem64` in `MachineMem64.lean`). No model has
a division instruction.

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| x86 shifts | count reduced modulo `w`, then Jasmin's clamped shift (`shiftCount`, `wshl`, `wshr`, `wsar`; `X86Backend/JasminModel.lean`) | poison for a count ≥ `w` | `wrapping_shl` | deviates, principled | P5; the IR value (0) and the machine value agree for a count below `w`. `IsScalarUn`, `shiftCount_imm`, `lowerUn_get_dst` |
| x86 carry, high multiply | `addCarry`, `mulHi` (`X86Backend/Model.lean`) | as layer 3 | as layer 3 | follows LLVM | the dialect definitions `carryOutBit` and `mulHiW` are stated to coincide with them |
| ARM immediate shifts | `lsl`, `lsr` with the amount bounded by type, `Fin 64` in `BInst` and `Fin 32` in `AInst` (`ARMBackend/ArmModel.lean`); the encoder writes the amount without reduction (`encodeBInst`, `encodeAInst`). A `RegStmt` shift by an arbitrary `Nat` is selected through `BOp.shrImm`, `BOp.shlImm`, which give `movz dst 0` for an amount ≥ 64 | poison for `sh` ≥ 64 | panic | follows LLVM | No instruction value carries an amount at or above the width, so the model and the encoded word shift by the same amount. `roundtrip_binst_lsr`, `roundtrip_binst_lsl`, `roundtrip_ainst_lsr`, `roundtrip_ainst_lsl` carry no range hypothesis (`lsl` by 0 is excluded: its word is that of `lsr` by 0); `BOp.eval_shrImm`, `BOp.eval_shlImm` |
| RISC-V immediate shifts | `slli`, `srli` with `sh : Fin 64` (`evalRInst64`); `encodeWord64` packs the amount into the 12-bit immediate, whose upper six bits stay 0. A `RegStmt` shift by an arbitrary `Nat` is selected through `ROp64.shrImm`, `ROp64.shlImm`, which give `li d 0` for an amount ≥ 64 | poison for `sh` ≥ 64 | panic | follows LLVM | `roundtrip_RInst64` holds for every `RInst64` other than `li` with its register names in `emittedRegs`, with no condition on the amount; `ROp64.run_shrImm`, `ROp64.run_shlImm` |
| RISC-V 32-bit immediate shifts | `slliw`, `srliw`, `roriw` with `imm : Fin 32` (`evalRInst`, `RISCVBackend/RiscvModel.lean`); `encodeWord` packs the amount into the 5-bit `shamt` (`RISCVBackend/RiscvEncoder.lean`). An `ROp` shift or rotate by an arbitrary `Nat` is selected through `RInst.shlImm`, `RInst.shrImm`, which give `xor d a a` (the constant 0) for an amount ≥ 32, and `RInst.rorImm`, which gives `mv d a` for an amount ≥ 32; the rotate macro of `RiscvLowering.toRInst` is built from them, so its second shift at `m = 0` is the constant 0 | poison for `m` ≥ 32 | panic | follows LLVM | `roundtrip_RInst` holds for every `RInst` with its register names in `emittedRegs`, with no condition on the amount; `evalRInst_shlImm`, `evalRInst_shrImm`, `evalRInst_rorImm`; `rotl_run_denote`, `rotr_run_denote` hold for every amount against `opRol`, `opRor`, which are the identity at 0 and at amounts ≥ 32 |
| Memory bounds | total byte map; addresses wrap modulo `2^64` (`AMem`, `Mem64`, `read64`, `write64`) | undefined behaviour | panic | deviates, principled | P4. `disciplinedB`, `Separated`, `MemSep`; `idxOkB` one layer up |
| Memory alignment | never checked; jasminc's `is_aligned_if` assertion is dropped (`VIR/JasmincWArrayAlignment.lean`) | access below the stated alignment: undefined behaviour | references are aligned | deviates, to be fixed | Defect: no model has an alignment predicate, and no theorem states that every emitted access is aligned or that the emitted instructions have no alignment requirement. Fix: an alignment conjunct beside `idxOkB` in the checked step, or that theorem over the emitted instruction set |
| Uninitialised read | the total map returns the stored byte (`AMem`, `Mem64`) | undef | impossible in safe Rust | deviates, principled | P4: a total memory is a conservative extension of one in which every read is initialised. No Lean theorem discharges it; it rests on the absence of `unsafe` in the covered source language |
| Poison, undefined behaviour | none at any layer from `semScalar` down | "Poison Values", "Undefined Values" | none in safe Rust | deviates, principled | P1. `veirRunCom_refines` on the `arith` fragment (`ComInArith`) |

## Layer 6: the VeIR bridge

The bridge (`VIR/ComToVeir.lean`, `VIR/ComToVeir_JasminDialect.lean`,
`VIR/ComToVeir_CatCryptDialect.lean`, `VIR/ComToVeirSemantics.lean`,
`VIR/ComToVeirShifts.lean`) translates a `Com` to VeIR operations. VeIR's interpreter
returns `Interp` (fail, undefined behaviour or a value), and its integers are
`LLVM.Int w` (a value or poison). The first table judges the bridge against LLVM; the
second lists the points where VeIR's interpreter differs from LangRef.

`jasminDialect` has one table of expansions, `JasminOp.bridgeExpansion? bare`
(`VIR/ComToVeir_JasminDialect.lean`), which covers the scalar fragment
`JasminOp.InBridge`. The `ToVeirOp jasminDialect` instance, which the entry points of
`VIR/ComToVeir.lean` use, takes it at `bare = false`
(`veirRunOp_uses_instances`, `veirExpansionOf_eq_bridgeExpansionOf`); the builders
`lowerComWfWith`, `lowerComToFuncAtWf` and `lowerComToModuleWf` take either value as
`bridgeExpansionOf bare`. `JasminOp.expandVeir?` is the restriction of the table to
`JasminOp.InArith` (`JasminOp.bridgeExpansion?_false_of_inArith`). `veirRunCom`
interprets the operations the instance emits; `veirRunCom_bridge_refines` and
`veirRunCom_bridge_eq_denote` (`VIR/ComToVeirShifts.lean`) state its refinement and its
equation with the denotation on `JasminOp.InBridge`. The rows below describe
`bridgeExpansion?`; a row that does not name `bare` holds for both values and so for
the instance.

| Operation | Our semantics (declaration) | LLVM / MLIR | Rust | Status | Principle and discharge |
|---|---|---|---|---|---|
| `add`, `sub`, `mul` | emitted without `nsw` or `nuw` (`veirBinInt`: `LLVM.Int.add`, `LLVM.Int.sub`, `LLVM.Int.mul` with default flags) | wrap | `wrapping_*` | follows LLVM | `interpretOp'_regArith` |
| Variable shift, `bare = false` and the instance | emitted as a compare and a select around the shift (`JasminOp.shiftSelectExpansion`), which yields 0 for an amount ≥ `w` | poison for the bare shift | panic | follows LLVM | `veirRunComBridge_eq_denote` and `veirRunCom_bridge_eq_denote` hold for every shift amount |
| Variable shift, `bare = true` | emitted as one `arith.shli` or `arith.shrui` | poison for an amount ≥ `w` | panic | follows LLVM | `veirRunComBare_eq` under `ComShiftSafe` (every shift amount below the width), which the front discharges from Rust's panic freedom; `veirRunComWith_bridge_refines` for every amount, VeIR's value being poison where ours is 0 |
| `andn` | constant all ones, `arith.xori` of the first operand with it, `arith.andi` with the second (`JasminOp.andnExpansion`); the first operand is the complemented one, as in `JasminBinOp.apply .andn` | `xor a, -1` then `and` | `!a & b` | follows LLVM | `veirAndn_val`. `veirBinInt`, arm `.andn`, is poison and is not reached: `andn` has an expansion for both values of `bare` |
| Immediate shifts `shlImm`, `shrImm`, `sarImm` | the constant amount and `arith.shli`, `arith.shrui` or `arith.shrsi` when `n < w`; for `n ≥ w` the constant 0 (`shlImm`, `shrImm`) or `arith.shrsi` by `w - 1` (`sarImm`), so no emitted amount reaches the width | poison for an amount ≥ `w` | panic | follows LLVM | `veirShlImm_val`, `veirShrImm_val`, `veirSarImm_val` (`sshiftRight_min`) |
| `rorImm` | `arith.shrui` by `n % w`, `arith.shli` by `w - n % w` and `arith.ori`; no operation when `n % w = 0` (`JasminOp.rorImmExpansion`) | `llvm.fshr`, amount modulo the width | `rotate_right` | follows LLVM | `veirRorImm_val`. The `arith` dialect has no rotate; VeIR interprets the funnel shifts as `llvm.intr.fshl` and `llvm.intr.fshr` of its `llvm` dialect, which the bridge does not emit |
| `castW` | `arith.extui`, `arith.trunci`, or no operation at equal widths | `zext`, `trunc` | `as` between unsigned types | follows LLVM | `veirCastW_val` |
| `mulhi` | second result of `arith.mului_extended` | high half of the double-width product | `widening_mul` high word | follows LLVM | `umulHigh_val` |
| `cmp`, `cmpImm` | `arith.cmpi`, against a constant for `cmpImm` | `icmp` | `bool` | follows LLVM | `icmp_val` |
| `select` | `arith.select` | `select`: poison in the arm not picked does not propagate | `if` | follows LLVM | `select_val`, `select_refines` |
| `addCarryLo`, `addCarryHi` | the carry zero-extended to the word; two `arith.addi` for the word, two `arith.addui_extended` and `arith.ori` of their flags for the carry-out | two `uadd.with.overflow` and `or` | `carrying_add` | follows LLVM | `veirAddCarryLo_val`, `veirAddCarryHi_val` (`carryOutBit_eq_or`). `arith.addui_extended` takes no carry-in, so no single operation matches |
| `bitToSword` | emitted as `arith.extsi` | `sext` of `i1` | as layer 3 | follows LLVM | by definition of the translation |
| `bvEq` | emitted as `arith.cmpi` | `icmp` | `bool` | follows LLVM | `catCryptDialect`: no semantic theorem yet |

Memory operations (`stackLoad`, `stackStore`), calls (`extCall`, `callN`), the vector
operations and loops are outside `JasminOp.InBridge`; the theorems of
`VIR/ComToVeirShifts.lean` do not cover them. The block-level theorems of
`VIR/ComToVeirWf.lean` are in two groups. The structural ones (the builder returns a
well-formed context, every expansion reads only its arguments and earlier results,
no step carries discardable attributes, and the entry point
`lowerClosedComToModuleWithExterns` returns the context of `lowerComToFuncWf`) hold for
every op with the instance's table (`bindingExpansion_inScope`,
`bindingExpansion_attrs`, `lowerComToFuncWf_isSome`,
`lowerClosedComToModuleWithExterns_eq_lowerComToFuncWf`). The semantic ones
(`interpretBlock`, `interpretFunction` on the built context) are stated on
`JasminOp.InArith`. These are coverage limits of the theorems and are recorded here so
that no row above is read as covering them.

| Operation | VeIR (declaration) | LLVM | Status | Consequence for us |
|---|---|---|---|---|
| RISC-V dialect load and store | memory grows to contain the access, which never raises undefined behaviour (`riscvLoad`, `MemoryState.ensureSize`) | out of bounds: undefined behaviour | VeIR deviates from LLVM | a simulation between `Mem64` and `MemoryState` on RISC-V must not use VeIR as the bounds oracle |
| Alignment | `MemoryState.llvmLoad` and `MemoryState.llvmStore` check the address against 0 and the bounds, never the alignment | undefined behaviour below the stated alignment | VeIR deviates from LLVM | agreement with VeIR gives no alignment evidence; see the alignment row of layer 5 |
| Cast from an integer to a RISC-V register | poison maps to 0 (`LLVM.Int.toReg`) | poison | follows LLVM | a refinement of poison; listed because the register type has no poison |
| Shifts, division, select on `LLVM.Int` | poison for an amount ≥ `w` (`LLVM.Int.shl`, `LLVM.Int.lshr`, `LLVM.Int.ashr`); undefined behaviour on a zero divisor and on `MIN` divided by −1 (`Interp.checkUnsignedDivision`, `Interp.checkSignedDivision`); `LLVM.Int.select` | same | follows LLVM | the reference for rows of layers 2 to 4 |
| RISC-V register shifts and division | amount reduced to 6 bits (`Veir.Data.RISCV.sll`); division by zero gives all ones (`Veir.Data.RISCV.div`, `Veir.Data.RISCV.divu`); argument order `(rs2 rs1)` | instruction-set semantics | follows the RISC-V specification | P5 applies; `Veir.Data.RISCV.andn` complements `rs2`, the opposite of our `andn` |

## Open repairs

The rows with status "deviates, to be fixed", in the order of the layers:

1. The adapter omits the width tag at some scalar types, so the untagged
   `Hax.wrapping_add`, `Hax.wrapping_mul`, `Hax.shl`, `Hax.shr`, `Hax.rotate_right`,
   and `Hax.div`, `Hax.rem` on a signed operand, reach the runtime where they do not
   agree with Rust. The repair is in the hax front: emit the width-tagged name at
   every scalar type.
2. `bvAdc`: carry-in wider than one bit.
3. Memory alignment: no predicate and no theorem.
4. Bridge: the `ToVeirOp jasminDialect` instance uses `JasminOp.bridgeExpansion? false`,
   so the entry points of `VIR/ComToVeir.lean` emit `andn`, the rotate, the immediate
   shifts, the width cast, the immediate comparison and the carry words as registered
   `arith` operations, and the op-by-op theorems `veirRunCom_bridge_refines` and
   `veirRunCom_bridge_eq_denote` cover `JasminOp.InBridge` at the instance. What
   remains: the `interpretBlock` and `interpretFunction` theorems of
   `VIR/ComToVeirWf.lean`, which read the built pointer graph, are stated on
   `JasminOp.InArith`; extending them to `JasminOp.InBridge` needs
   `bindingExpansion_run` (the conformance-checked run `veirRunStepsC`) for the
   expansions outside the `arith` fragment.

A change that adds an operation to a dialect, a machine model or the bridge adds its
row here in the same change.
