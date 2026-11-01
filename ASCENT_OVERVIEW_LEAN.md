# The ascent: Lean companion

This document maps [ASCENT_OVERVIEW_HIGHLEVEL.md](ASCENT_OVERVIEW_HIGHLEVEL.md) to the
Lean code. Section *n* here lists the declarations that realise section *n* there and
adds what is specific to the code: names, modules, counts and build cost. The
mathematical statements are not repeated.

`Ascent/` stands for `CatCrypt/Crypto/SecureCompilation/Ascent/`. The ascent over
extracted Rust is the library `HaxAscent` (lakefile `lean_lib HaxAscent`, module root
`HaxAscent/`), which imports only Lean, Std, Batteries and hax-lean:

- `HaxAscent/Ascent/`: `FnCorres`, the hax generator, coverage, monomorphisation and
  `FnCorresUnique`;
- `HaxAscent/RustSemantics/`: the `RustM` reading `toRustMS` of `ImpExpr`, the Aeneas
  operation squares, termination on the kinded fragment (`ToRustMSTotalCtl`), the hax
  contract demo and the local `RCompOk` and `ArrayRel` (`RustSemantics/RCompOk`), which
  replace the ParamTransfer import;
- `HaxAscent/Calculus/`: the generic judgement `CorresM` (`CorresMCore`), its
  postcondition form (`CorresGenericSpec`), `IFold`, and the `RustM` square calculus
  (`RustMSquare`, `RustMSquareSpec`, `RustMSquareLoop`);
- `HaxAscent/Runtime`, `HaxAscent/ListBlocks`.

The declarations of `HaxAscent` are in the namespaces `Hax.Ascent`,
`CatCrypt.Hax.RustSemantics` and `CatCrypt.Crypto.SecureCompilation.Ascent`. The two
double-category leaves `SquareDouble` and `RustMSquareDouble` import CatCrypt-core and are
in the compiler library, as are the machine-level judgements, the engines and the kernel
proofs, which import `HaxAscent`.

## 1. The problem and the relation to descent

The judgement, at the x86 level and in its generic form:

```lean
def CorresJ {AState : Type} (SR : JState 64 → AState → Prop) (P : AState → Prop)
    (fa : AState → AState) (c : List (JInstr 64)) : Prop :=
  ∀ st a, SR st a → P a → SR (runBlock st c) (fa a)

def CorresM {M : Type} {C : Type} {AState : Type} (step : C → M → Option M)
    (SR : M → AState → Prop) (P : AState → Prop) (fa : AState → AState) (c : C) : Prop :=
  ∀ m a, SR m a → P a → ∃ m', step c m = some m' ∧ SR m' (fa a)
```

| Semantics | Judgement | Program type | Semantic function | Module |
|---|---|---|---|---|
| scalar language | `Corres`; `CorresU` with `while` | `LowCT` | `semScalar`; `semU` | `Ascent/Corres`, `Ascent/WhileTop` |
| x86-64 | `CorresJ` | `List (JInstr 64)` | `runBlock` | `Ascent/RunBlockCorres` |
| RV64 | `CorresR` | RV64 block | `runRBlock64` | `Ascent/CorresRiscv` |
| hax expressions | `Corres`, `FnCorres` | `ImpExpr` | `denote'` with fuel | `HaxAscent/Ascent/Corres` |
| instruction set (x86-64, AArch64, RV64) | `CorresIsa isa P SR Pre fa fuel` | `LprogM` | `Isa.lsemFuelMemF` (instances `x86Isa`, `armIsa`, `rvIsa`) | `Ascent/CorresIsa` |

The generic definition is `CorresM` (`HaxAscent/Calculus/CorresMCore`). The
identifications are `corres_eq_corresM` (by `rfl`), `corresJ_eq_corresM`,
`corresR_eq_corresM` and `corresIsa_eq_corresM`. Fuel: `lsemFuelMemF_halted`,
`lsemFuelMemF_add`, `corresIsa_fuel_mono`; the per-state fuel form is `CorresIsaRun`
(`corresIsaRun_of_corresIsa`).

Transport from `CorresJ` (`Ascent/CorresIsaX86`): `corresIsa_x86_of_corresJ` for blocks
in `InSubsetM`, `corresIsa_arm_of_corresJ` for blocks in `InFieldArithSubset`, both over
the side relation `liftSR`, which leaves the flags unrelated; examples `corresIsa_x86_add2`,
`corresIsa_arm_add2`. `corresIsa_x86_of_corresJ_mov` (`Ascent/CorresIsaX86Mov`) covers
blocks with register-to-register moves (`InMovRegSubset`); it is an instance of
`corresIsa_x86_of_runStraightF`, which takes the agreement of the flag machine with
`runBlock` as a hypothesis. No transport targets `rvIsa`.

Control flow (`Ascent/CorresIsaCfg`, namespace `IsaCfg`): `corresIsa_of_cutPoint` is the
cut-point rule of `HaxAscent/Calculus/CorresMCutPoint` at `Isa.lsemFuelMemF`;
`corresIsa_of_labels_floyd` takes an invariant per cut point (program entry or the
position after a label), a measure and a step bound `B` per segment, and gives
`CorresIsa` with fuel `B * (N + 1)`; `lsemFuelMemF_of_labels_floyd` is the same rule with
the fuel `B * (μ none m a + 1)` of the initial state, and `corresIsaRun_of_labels_floyd`
its form as `CorresIsaRun`. Segments come from `steps_of_runL`, or from the segment
predicate `SegAt` of `Ascent/CorresIsaCfgTactic`: `corresIsa_of_cuts` states the rule with
one `SegAt` goal per cut point, `isa_cutpoints` applies it, `isa_steps` runs a segment
forward by the lemma of the instruction at the counter and splits at a conditional jump
on a register, and `isa_exit` and `isa_cut` end a segment and leave the exit relation or
the invariant and the decrease of the measure. Examples of the rule over `x86Isa`
(`Ascent/Demos/KrakenCfgDemo`), written on `Lprog` code with virtual registers:
`abs_corresIsa` (absolute value by a branch on a register), `idxAlias_corresIsa` (two
indexed stores at possibly equal indices of one array), `loop_corresIsa` (a counting
loop, with fuel linear in a bound on its input). The loop is a simpler relative of the
example `P3` of the Kraken x64 framework. The other two are not its examples `Cond` (a
jump on the zero flag after a decrement, with a postcondition for one branch) and `Alias`
(two labels at one address). The machine model expresses no branch on the flags of an
arithmetic instruction, no aliasing of pointers and no mapped stack.

Call and return (`VIR/LprogIsa`, `Ascent/CorresIsaCall`): `Isa.withCalls` is the record
`isa` with a step for `Lcall` and `Lret` (return address pushed at the stack pointer of
`IsaAbi`, or written to a link register), and agrees with `isa` on every other
instruction (`Isa.withCalls_step_of_not_call`). `IsaCall.ProcSpec` is a procedure
specification from an entry label to a return position, with a frame condition and
`RetFrame` (stack pointer and return cell preserved); `IsaCall.steps_call` runs a call
site through call, callee and return in at most `B + 2` steps, and is one segment of
`corresIsa_of_labels_floyd`. Example: `call_corresIsa` (`Ascent/Demos/KrakenCallDemo`),
a caller of a doubling procedure, twice, a simpler relative of the Kraken example
`CallSwap`. A return through a link register has no step
(`Ligoto`), and the three instance records are not extended: results with calls are
stated over `isa.withCalls`. For a program without a call instruction the two machines
give the same judgement (`corresIsa_withCalls_iff`).

Programs the compiler emits (`Ascent/CorresIsaNode`, `Ascent/CorresIsaStackFrame`,
`Ascent/ImageSpFree`). A node is a program run by the flag machine `lsemFuelMemF` beside a
decoded machine program run by the address machine. `corresIsa_of_node_halts_fuel` states
the pair of runs as one `CorresIsa x86Isa` at a fixed fuel, over the two-phase abstract
state `PhaseAbs` (the machine entry state, then the output): the specification is the
output of the source, and the exit clause of the state relation is a halting run of the
decoded program. `x86Isa` has no step at `Lret`; the body followed by its return is treated
as a callee over `x86Isa.withCalls`. `x86_procSpec_of_image_judgement` gives, from such a
judgement on a body that contains no call or return and names no stack pointer (two
Boolean checks), the procedure specification of the body placed after a label and followed
by a return, and `virtImg_spFreeBodyB` and `virtImg_noCall` prove the two checks for the
image of every covered printed body of the hax compiler
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#compiled-bodies-as-callees)).

Imported Jasmin with control flow (`Ascent/JasminJumpLevel`): `compileS` compiles a
structured program to labelled code, `compileS_run` simulates a structured run on
`x86Isa` with fuel `stepBound`, and `corresIsa_of_bignumExec` gives `CorresIsa x86Isa`
against `bignumExecFuel` for every body in the fragment: register-only blocks and
zero-flag guards. Memory and carries are outside it, because the flag machine's memory
is keyed by base name and displacement; example `sum_corresIsa`
(`Ascent/Demos/JasminJumpDemo`).

Footprints over effective addresses (`Ascent/FootprintEA`, with `Ascent/Rng`):
`footprint_eq_footprintEA`, `read_frame_ea`, `frame_rule_ea`, `footCheckFrom_frame_ea`.

Uniqueness (`HaxAscent/Ascent/FnCorresUnique`): `fnCorres_val_unique`,
`fnCorres_haxEval`, `fnCorres_enc_unique`.

Case split (`HaxAscent/Ascent/FnCorresIte`): `fnCorres_ifThenElse` gives the function
correspondence of a conditional from those of its branches, each under the guard
strengthened by the value of the condition, so a step whose top is a conditional is ascended
one branch at a time; `fnCorres_letBind` passes the `let`s of the A-normal form before the
conditional by extending the entry environment.

| Weld | Declaration |
|---|---|
| refinement, correspondence and emission | `legWeld`: `RRefines spec c`, `Corres SRwordNT P fa c` and the emit leg, for a command that reads no entry variable |
| descent result to compiled x86 block | `corres_of_refines_x86`: the result register of the `ScalarTarget` block under `xrun` holds one slot of the specification |
| hax pipeline and source tower | `feSub_raw_source_to_bytes`: hax-lean's `pipeline_correct` for an `ImpExpr` whose output is the constant `feSubSourceWord`, beside the source tower, which ends at the Jasmin-dialect denotation |
| emitted carry chains from correspondences | `emitSbbChain_runBlock`, `emitAdcChain_runBlock`, from `corresJ_sbbChain`, `corresJ_adcChain` (`Ascent/EcMultiLimbCapstone`) |

Jasmin source (`CatCrypt/Crypto/Jasmin/`): `JazzToInstrR` parses `.jazz` text
(`parseJazz`, `parseJazzProg`) into the `InstrR` syntax that `bignumExec` interprets, with
two `#kat` round trips against the printer. `BignumToJ` translates the straight-line
fragment (`toJ`, `toJBlock`), relates the states by `BJCorr`, and proves
`toJ_sim`, `bignumExec_runBlockA_sim` (simulation into `runBlockA`) and
`bignumExec_progress`.

[CORRECTNESS.md](CORRECTNESS.md#composition-of-the-techniques) states the welds in full.

## 2. Provenance

The port is [sgraf812/ascent](https://github.com/sgraf812/ascent);
[PROVENANCE.md](PROVENANCE.md) records the details. The names taken are `Ascent`,
`ascend` and `Corres`. No declaration is taken: of the port's 293 declaration names, two
(`Heap`, `incr`) recur in the `Ascent` modules, with different definitions. The port's
judgement is `RTriple`, over the relational weakest precondition `rwp` of
`Std.Internal.Do`. The connection of this package's judgements to `Std.Do` triples is
`corresJ_iff_triple`, `corresM_iff_triple` (over `RustM`'s `WP` instance) and
`fnCorres_iff_triple` (section 4). The judgements over `semScalar`, `runBlock`,
`runBlockA`, `runRBlock64` and `denote'` are defined in this package.

## 3. Squares as a thin double category

The class is `ThinDoubleCategory` in core's module
`CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory`. The horizontal category is
carried by the type synonym `Hor C`.

| Notion | Declaration |
|---|---|
| square predicate and its closure | `Sq u f g w`; `vcomp`, `hcomp`, `vid`, `hid` |
| coherence laws by `rfl` | `interchange`, `vcomp_hid`, `hcomp_vid`, `vid_id_eq_hid_id` |
| coherence laws as heterogeneous equalities | `vcomp_assoc`, `hcomp_assoc`, the four unit laws |
| relational instance | `ofRelSemantics`, over `relCategory` (composition `Relation.Comp`) |
| functorial semantics | `RelSemantics`, laws `sem_id`, `sem_comp` |
| lax square | `RelSemantics.LaxSq` |

```lean
def RelSemantics.LaxSq (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) : Prop :=
  ∀ x y y', f x y → S.sem w y y' → ∃ x', S.sem u x x' ∧ g x' y'
```

| Level | Instance | Objects | Composition | Judgement as square |
|---|---|---|---|---|
| x86 | `JLevel A` ([SquareStrictDouble](CatCrypt/Crypto/SecureCompilation/Ascent/SquareStrictDouble.lean)) | `mach : JState 64`, `abs : A` | `++`, unit `[]` | `sq_mach_iff`, `corresJ_iff_sq`, `runBlockTriple_iff_sq` |
| monadic Rust | `MLevel C S` ([RustMSquareDouble](CatCrypt/Crypto/SecureCompilation/Ascent/RustMSquareDouble.lean)) | `conc A : A × C`, `abs A : A × S` | `kseq` on `A → C → RustM (B × C)`, unit `pureK` | `sq_conc_iff`, `corresM_iff_sq` |
| hax expressions | `CLevel bi S` ([SquareDouble](CatCrypt/Hax/Ascent/SquareDouble.lean)) | `conc : Env × Value`, `abs : S × Value` | `++` on lists of `ImpExpr` legs | `sq_conc_iff`, `sq_single_of_corres`, `corres_seqOfList_of_sq` |

- x86. Functoriality is `runBlock_append`. `Ascent/SquareStrict` states the same algebra
  without the class (`VMapJ`, `corresJ_hcomp`, `vmapJ_hcomp_interchange`).
- Monadic Rust. The monad is `Aeneas.Std.RustM`; the program equalities are
  `kseq_pure_left`, `kseq_pure_right` and `kseq_assoc` (`HaxAscent/Calculus/RustMSquare`). Exclusion
  of failure and divergence: `corresM_ne_fail`, `corresM_ne_div`. The bind rule is
  `corresM_bind`; its reading as horizontal pasting is in the docstring only. This
  `CorresM` (`Hax.Ascent.RustM`) is a different declaration from the generic one of
  section 1.
- hax expressions. Associativity up to runs: `denote'_seq_assoc`. Failure of the right
  unit: `corres_letBind_var_right_not_iff`, over `.letBind x e (.var x)`; no exit relation
  repairs it: `not_exit_of_read_of_lower`; the law up to the bound name:
  `letBind_var_right_unit_offName`.
- The levels without an instance are `runBlockA`, `CorresR`, `CorresIsa` and `LowCT`.
- `SquareDouble` and `RustMSquareDouble` are the only modules of this section outside
  `HaxAscent`: they instantiate core's class and so stay in the compiler library.

## 4. Verification-condition generation

The program logic is Lean's `Std.Do` and the generator is `mvcgen`. The central
equivalence is in
[CorresHoare](CatCrypt/Crypto/SecureCompilation/Ascent/CorresHoare.lean):

```lean
theorem corresJ_iff_triple {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) :
    CorresJ SR P fa c
      ↔ ∀ a, P a → RunBlockTriple (fun st => SR st a) c (fun st => SR st (fa a))
```

| Statement | Declarations |
|---|---|
| `RunBlockTriple P c Q` is the `Std.Do` triple over `runBlockM c : StateM (JState 64) Unit` | `runBlockM_run`, `runBlockM_triple_iff` (`Ascent/RunBlockMvcgen`) |
| concatenation is bind | `runBlockM_append`, `runBlockM_triple_hcomp` |
| the leaf proved by the generator (`sbb`, by `mvcgen [stepM_spec]`) | `sbb_leaf_triple_mvcgen` |
| transport along `θ : StateM S → StateT S Option` | `theta_pure`, `theta_bind`, `wp_theta_eq` (`rfl`), `Spec.wp_theta` |
| monadic Rust correspondence as a total triple | `corresM_iff_triple` |
| `FnCorres` as a triple over `optGuard G f a` | `fnCorres_iff_triple`, `triple_option_iff` |
| arbitrary postcondition, generic judgement | `StepTriple`, `corresM_post`, `corresM_iff_post` (`HaxAscent/Calculus/CorresGenericSpec`) |
| arbitrary postcondition, per level | `corres_iff_post` (LowCT), `corresJ_iff_post_generic` (x86), `corresR_iff_post` (RV64) (`Ascent/CorresInstanceSpec`); `corresIsa_post`, `corresIsa_of_post`, `corresIsa_iff_post` (`Ascent/CorresIsa`); x86 over `RunBlockTriple`: `corresJ_triple_post`, `corresJ_iff_triple_post` (`Ascent/CorresHoareSpec`) |
| specification lemmas for `mvcgen` | x86 `corresJ_spec_at` (state-indexed), `corresJ_spec` (arbitrary `Q`, tail position only) (`Ascent/CorresHoareSpec`); `RustM` `corresM_spec_at`, `corresM_iff_spec_at`, `corresM_spec_post` (`HaxAscent/Calculus/RustMSquareSpec`) |
| demo: a caller proved by `mvcgen` with an ascent result as callee specification | `sbb_then_sbb_triple`, `sbb_then_step_triple`, `step_then_sbb_triple` (`Ascent/Demos/CorresAsSpecDemo`) |
| `FnCorres` and the `RustM` reading `toRustMS` | partial: `fnCorres_toRustMS_partialSpec`, `fnCorres_toRustMS_triple_partial`; total under termination: `fnCorres_toRustMS_spec`, `fnCorres_toRustMS_triple`, `fnCorres_toRustMS_triple_iff` (`HaxAscent/RustSemantics/ToRustMSSpec`) |
| termination on the straight-line fragment | `straightOk`, `AppTotalOn`, `EnvOk`, `toRustMS_total`, `fnCorres_toRustMS_triple_of_straightOk` (`HaxAscent/RustSemantics/ToRustMSTotal`); `line_failApp` shows `AppOk` alone does not give termination (`ToRustMSSpecDemo`) |
| termination with conditionals, loops and checked arithmetic | `kindOf`, `Kd`, `EnvTy`, `AppTyped`, `loopS_total`, `toRustMS_total_kind`, `fnCorres_toRustMS_triple_of_kindOf`; checked operations `appTyped_add` (kinds `WB`), `appTyped_addI`, `appTyped_sub`, `appTyped_mul`, `appTyped_div`, `appTyped_rem` (range kinds `WI`); instance `keyEqLit_triple` (`HaxAscent/RustSemantics/ToRustMSTotalCtl`). Loop bounds of index-range kind: `kindOfL`, `boundRange`, `toRustMS_total_kindL`, instance `varLoopLit` (`varLoopLit_kind`, `varLoopLit_total`). Tagged shifts: `appTyped_shl`, `appTyped_shr`; untagged shifts fail (`appRt_Shl_undef`, `appRt_Shr_undef`). Signed checked arithmetic has no total kind, and arithmetic on two integer literals has no reading (`appRt_arith_int_undef`). The straight-line theorems of `ToRustMSTotal` are instances of `toRustMS_total_kindL` through `kindOfL_of_straightOk` |
| a printed hax contract closed by an ascent result | `Spec` (the printer's structure restated over `Aeneas.Std.RustM`), `keyEqRun_contract`, `keyEqRun.spec` (`HaxAscent/RustSemantics/ToRustMSContractDemo`) |
| loop rule from the invariant rule | x86: `runBlockM_loop_triple`, `corresJ_loop_of_triple` (`Ascent/RunBlockLoopTriple`); `RustM`, over hax-lean's `loop` with a `ControlFlow` body: `corresM_loop`, `corresM_loop_iff_spec`, `countedBody_spec`, `corresM_loopK` (`HaxAscent/Calculus/RustMSquareLoop`, from `loop.spec_decr_nat`); extracted `for` loops: `foldRangeK_eq_loopK` (hax-lean's `fold_range` equals the counted loop), `corresM_foldRange` |
| `mvcgen` with the abstract function as a metavariable | `sbb1Synth_val`, `sbb2Synth_val`, `sbb2Synth_eq_sym`; failures recorded by `fail_if_success` (`Ascent/Demos/SchematicMvcgenProbe`) |

The abstract function that the ascent outputs is `asemWExpr c` for the scalar engines and
`Ns.HaxGen.f.gen` for the hax generator. No module under `HaxAscent/Ascent/` uses `mvcgen`. The
`*Mvcgen` modules other than `RunBlockMvcgen*` are probes outside the calculus
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#research-probes-outside-the-calculus)).

## 5. Abstraction phases

| Phase | Definitions | Soundness |
|---|---|---|
| word abstraction | `wEnc : BitVec 64 → ZMod 2^64` | `corres_WA` (`Ascent/Phases`) |
| value abstraction | `ValueAbs C A`; store relations `SRof V`, `SRcarryOf V`; closure `pair`, `pi`, `comp` | `feAddN_capstone`, an `adcx` chain (`Ascent/Demos/HeapAbs`) |
| type strengthening | `tsLowCTL` | `tsLowCT_sound` (`Ascent/Strengthen`); demo `feSubC_ts_refines` |
| guards | `ascendG fuel c` | `ascendG_sound` (`Ascent/Guards`) |

The value abstraction is in the module `HeapAbs`. The constructors the total abstraction
handles and the guards it assigns are listed in
[ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#the-total-abstraction-over-an-array-layout).

## 6. Loops, calls and frames

Each rule is applied to few kernels. The last column names the other modules whose
proofs apply it.

| Rule | Declaration | Lean form | Applied in |
|---|---|---|---|
| counted loop | `corres_for` (`Ascent/Control`) | `RFor` realises `nfold fa N` | `LoopSourceLeaf`, `KeystoneControl` |
| indexed counted loop | `corres_for_indexed` | `ifold fa N` | `MlkemPolyFoldCorres` |
| while, partial | `corresU_while` (`Ascent/WhileTop`) | over `RWhileNz` | none |
| while, functional | `corresU_whileFun`, `_total` (`Ascent/WhileFun`) | `loopFun guardA fb (fb a)` | `WhileFunSum`, `WhileFunEmit` |
| while with early exit | `corresU_while_exit` (`Ascent/Exit`) | `whileE C fb` | none |
| block replication | `corresJ_loop` (`Ascent/RunBlockCorres`) | `loopStep step n` | `JasminMirrorTie` |
| call frame | `framedCall_popped` (`Ascent/CallFrame`), on `runBlockA` | `%rsp` and pushed registers | the Ed25519 call proofs |

The loop theorem at the bytes is `and_n_bytes_value`, about `mpn_and_n_loop_owned`, with
layout condition `AndNLayout` and postcondition `AndNPost`. `CallFrame` writes `push`,
`pop`, `call` and `ret` as `JInstr` sequences. The framed Montgomery multiplication is
`s2nMontmulP384FramedBytes_correct`; it replaces the source's `pushq`/`popq` by red-zone
stores.

## 7. Automation and its cost

The tactic per goal shape is in [ASCENT.md](ASCENT.md#tactics).

| Kind | Entry point | Soundness or mechanism | Demo |
|---|---|---|---|
| decision by reflection | `ascend_expr!` | fragment `IsAscendableExpr`; `ascend_expr_sound` gives `Corres SRwordNT (fun _ => True) (asemWExpr c) c` | `arithK_expr` |
| symbolic engine | `corres_sym` and siblings | worklist in `Lean.Meta.Sym` over a `CorresSymEngine.Machine` (leaves of `CorresJ`, `CorresR` or `Corres`); side conditions to `decide` or returned | `sbb3_refines`, `addCarry_ascends` |
| verified symbolic executor | `partCheck_sound` (`Ascent/Demos/Ed25519SymExec`) | check run by `decide +kernel`; `mapHolds_cat` chains parts; certificates from `scripts/cutgen/`, run outside the build | the Ed25519 cut modules (`Ed25519ScReduceCut*`, `Ed25519ScMuladdCut*`) |
| hax generator | `Hax.Ascent.Gen.ascendFn`; `hax_ascend Ns` over an extraction | `line_corres_gen` (tactic `hax_corres`) and `line_corres_rules` prove one statement both ways; `fnCorres_monomorphise_iff` for trait-generic functions | `line_corres_gen` |

`scripts/build-cost-baseline.tsv` records per module the elaboration and import times and
the peak memory. Its highest ascent peaks are `Ed25519PointAddShippedProof` (3,788 MB),
`CarryMulCorrect` (3,756 MB) and `Ed25519ScMuladdShippedProof` (3,563 MB); the
s2n-bignum modules stay below 1,900 MB.

## 8. Results and comparison

Most results are stated on the address machine `runBlockA`; the s2n-bignum byte and
framed forms use `runBlock`. [ASCENT.md](ASCENT.md) has the full result tables.

| Kernel | Theorems | Lean-specific limit |
|---|---|---|
| `bignum_montmul_p384` | `s2nMontmulP384_correct_addr`; bytes: `s2nMontmulP384Bytes_correct` | |
| `carry_mul`, `solinas_square` | `carryMul_correct_addr`, `solinasSquare_correct_addr` | `RegionsApart` between the inputs and against the frame; for `solinas_square` also input against output |
| `ed25519_point_add` | `paShippedBytes_correct`, `paSpec_addSpec` (agreement with the extended-coordinate formulas); `ed25519PointAdd_constant_time` over the block | `Separated`; inputs below p |
| `ed25519_sc_reduce`, `sc_muladd` | `scReduceShipped_correct_addr`, `scMuladdShipped_correct_addr` | `Separated` (`scrCells`, `scmCells`) |
| `ed25519_madd`, `invert`, `compress` | `maddShipped_correct` (callees discharged through `maddCallees_maddCallModel`; `maddShipped_correct_cross` is the form relative to `MaddCallees`), `invertShipped_correct`, `invertShipped_inv`, `compressShipped_correct` (`compressShipped_correct_addr` is the form relative to `CompressCallees`) | inputs below p; `ChainSep`, `RangeDisj`, `CompressSep` buffer disjointness |
| `fe25519_mul`, comb select | `feMulBlock_mod`, `combSelectBytes_correct`, `selBytes_constant_time` | |
| RV64 `(x + y) mod p256` | `addp256_correct` | |

The example statement, in
[S2nMontmulP384Addr](CatCrypt/Crypto/SecureCompilation/Ascent/Demos/S2nMontmulP384Addr.lean):

```lean
theorem s2nMontmulP384_correct_addr (sa : AState) (px py pz : BitVec 64)
    (hx : sa.regs "%rsi" = px) (hy : sa.regs "%rdx" = py) (hz : sa.regs "%rdi" = pz)
    (hxy : limbs6 sa.mem px * limbs6 sa.mem py ≤ 2 ^ 384 * p384) :
    limbs6 (runBlockA sa s2nMontmulP384Block).mem pz < p384 ∧
      ((limbs6 (runBlockA sa s2nMontmulP384Block).mem pz : Nat) : ZMod p384)
        = (limbs6 sa.mem px : ZMod p384) * (limbs6 sa.mem py : Nat)
          * ((2 ^ 384 : Nat) : ZMod p384)⁻¹
```

The encoder and decoder of the byte statements are `encodeJBlock` and `decodeJStream`.
The correctness theorem of the hax compiler, `haxc_correct_auto`, is stated at a run of
the source reading under the compiler's builtin table; the congruence lemmas that move an
ascent result between readings of the calls are listed in
[ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#source-readings-joined-to-compiled-bytes).
In the comparison table, the Aeneas row refers to `CorresM` over `Aeneas.Std.RustM`
(`MLevel`) and the Jasmin row to `runBlock` and `legWeld`.

## Further reading

- [ASCENT.md](ASCENT.md): the guide, quick start, tactics and result tables.
- [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md): layers, entry points and exact hypotheses.
- [CORRECTNESS.md](CORRECTNESS.md): descent, ascent and transfer, and their welds.
- [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) and
  [HAX_RUST.md](HAX_RUST.md#3-existing-rust--lean-the-ascent-on-impexpr): imports and hax.
