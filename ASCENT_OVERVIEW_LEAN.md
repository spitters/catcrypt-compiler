# The ascent: Lean companion

This document maps [ASCENT_OVERVIEW_HIGHLEVEL.md](ASCENT_OVERVIEW_HIGHLEVEL.md) to the
Lean code. Section *n* here lists the declarations that realise section *n* there and
adds what is specific to the code: names, modules, counts and build cost. The
mathematical statements are not repeated.

`Ascent/` stands for `CatCrypt/Crypto/SecureCompilation/Ascent/` and `Hax/Ascent/` for
`CatCrypt/Hax/Ascent/`.

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
| hax expressions | `Corres`, `FnCorres` | `ImpExpr` | `denote'` with fuel | `Hax/Ascent/Corres` |

The generic definition is `CorresGeneric.CorresM`. The identifications are
`corres_eq_corresM` (by `rfl`), `corresJ_eq_corresM` and `corresR_eq_corresM`.

| Weld | Declaration |
|---|---|
| refinement, correspondence and emission | `legWeld`: `RRefines spec c`, `Corres SRwordNT P fa c` and the emit leg |
| descent result to compiled x86 block | `corres_of_refines_x86` |
| hax pipeline and source tower | `feSub_raw_source_to_bytes`, over hax-lean's `pipeline_correct` |

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
  `kseq_pure_left`, `kseq_pure_right` and `kseq_assoc` (`Ascent/RustMSquare`). Exclusion
  of failure and divergence: `corresM_ne_fail`, `corresM_ne_div`. The bind rule is
  `corresM_bind`; its reading as horizontal pasting is in the docstring only. This
  `CorresM` (`Hax.Ascent.RustM`) is a different declaration from the generic one of
  section 1.
- hax expressions. Associativity up to runs: `denote'_seq_assoc`. Failure of the right
  unit: `corres_letBind_var_right_not_iff`, over `.letBind x e (.var x)`; no exit relation
  repairs it: `not_exit_of_read_of_lower`; the law up to the bound name:
  `letBind_var_right_unit_offName`.
- The levels without an instance are `runBlockA`, `CorresR` and `LowCT`.

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
| arbitrary postcondition, generic judgement | `StepTriple`, `corresM_post`, `corresM_iff_post` (`Ascent/CorresGenericSpec`) |
| arbitrary postcondition, per level | `corres_iff_post` (LowCT), `corresJ_iff_post_generic` (x86), `corresR_iff_post` (RV64) (`Ascent/CorresInstanceSpec`); x86 over `RunBlockTriple`: `corresJ_triple_post`, `corresJ_iff_triple_post` (`Ascent/CorresHoareSpec`) |
| specification lemmas for `mvcgen` | x86 `corresJ_spec_at` (state-indexed), `corresJ_spec` (arbitrary `Q`, tail position only) (`Ascent/CorresHoareSpec`); `RustM` `corresM_spec_at`, `corresM_iff_spec_at`, `corresM_spec_post` (`Ascent/RustMSquareSpec`) |
| demo: a caller proved by `mvcgen` with an ascent result as callee specification | `sbb_then_sbb_triple`, `sbb_then_step_triple`, `step_then_sbb_triple` (`Ascent/Demos/CorresAsSpecDemo`) |
| `FnCorres` and the `RustM` reading `toRustMS` | partial: `fnCorres_toRustMS_partialSpec`, `fnCorres_toRustMS_triple_partial`; total under termination: `fnCorres_toRustMS_spec`, `fnCorres_toRustMS_triple`, `fnCorres_toRustMS_triple_iff` (`Hax/RustSemantics/ToRustMSSpec`) |
| termination on the straight-line fragment | `straightOk`, `AppTotalOn`, `EnvOk`, `toRustMS_total`, `fnCorres_toRustMS_triple_of_straightOk` (`Hax/RustSemantics/ToRustMSTotal`); `line_failApp` shows `AppOk` alone does not give termination (`ToRustMSSpecDemo`) |
| termination with conditionals, loops and checked arithmetic | `kindOf`, `Kd`, `EnvTy`, `AppTyped`, `loopS_total`, `toRustMS_total_kind`, `fnCorres_toRustMS_triple_of_kindOf`; checked operations `appTyped_add` (kinds `WB`), `appTyped_addI`, `appTyped_sub`, `appTyped_mul`, `appTyped_div`, `appTyped_rem` (range kinds `WI`); instance `keyEqLit_triple` (`Hax/RustSemantics/ToRustMSTotalCtl`). The straight-line proof of `ToRustMSTotal` is not a special case of the kinded one: `kindOf` rebinds a name only at its existing kind |
| a printed hax contract closed by an ascent result | `Spec` (the printer's structure restated over `Aeneas.Std.RustM`), `keyEqRun_contract`, `keyEqRun.spec` (`Hax/RustSemantics/ToRustMSContractDemo`) |
| loop rule from the invariant rule | x86: `runBlockM_loop_triple`, `corresJ_loop_of_triple` (`Ascent/RunBlockLoopTriple`); `RustM`, over hax-lean's `loop` with a `ControlFlow` body: `corresM_loop`, `corresM_loop_iff_spec`, `countedBody_spec`, `corresM_loopK` (`Ascent/RustMSquareLoop`, from `loop.spec_decr_nat`); extracted `for` loops: `foldRangeK_eq_loopK` (hax-lean's `fold_range` equals the counted loop), `corresM_foldRange` |
| `mvcgen` with the abstract function as a metavariable | `sbb1Synth_val`, `sbb2Synth_val`, `sbb2Synth_eq_sym`; failures recorded by `fail_if_success` (`Ascent/Demos/SchematicMvcgenProbe`) |

The abstract function that the ascent outputs is `asemWExpr c` for the scalar engines and
`Ns.HaxGen.f.gen` for the hax generator. No module under `Hax/Ascent/` uses `mvcgen`. The
`*Mvcgen` modules other than `RunBlockMvcgen*` are probes outside the calculus
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#research-probes-outside-the-calculus)).

## 5. Abstraction phases

| Phase | Definitions | Soundness |
|---|---|---|
| word abstraction | `wEnc : BitVec 64 → ZMod 2^64` | `corres_WA` (`Ascent/Phases`) |
| value abstraction | `ValueAbs C A`; store relations `SRof V`, `SRcarryOf V`; closure `pair`, `pi`, `comp` | `feAddN_capstone`, an `adcx` chain (`Ascent/Demos/HeapAbs`) |
| type strengthening | `tsLowCTL` | `tsLowCT_sound` (`Ascent/Strengthen`); demo `feSubC_ts_refines` |
| guards | `ascendG fuel c` | `ascendG_sound` (`Ascent/Guards`) |

The value abstraction lives in a module named `HeapAbs` although it lifts no heap. The
total abstraction gives 11 constructors the guard `False`
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#the-total-abstraction-assigns-an-unsatisfiable-guard-to-11-constructors)).

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
| `carry_mul`, `solinas_square` | `carryMul_correct_addr`, `solinasSquare_correct_addr` | `RegionsApart` |
| `ed25519_point_add` | `paShippedBytes_correct`, `paSpec_addSpec`; `ed25519PointAdd_constant_time` over the block | `Separated`; eleven `native_decide` checks |
| `ed25519_sc_reduce`, `sc_muladd` | `scReduceShipped_correct_addr`, `scMuladdShipped_correct_addr` | eight and nine `native_decide` footprint checks |
| `ed25519_madd`, `invert`, `compress` | `maddShipped_correct_cross`, `invertShipped_correct`, `compressShipped_correct_addr` | `madd` relative to `MaddCallees` |
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

The encoder and decoder of the byte statements are `encodeJBlock` and `decodeJStream`
([ASCENT.md](ASCENT.md#scope-of-the-statements)). The missing composition of `FnCorres`
with a machine square is discussed in
[CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md#the-ascent-against-a-hax-reference).
In the comparison table, the Aeneas row refers to `CorresM` over `Aeneas.Std.RustM`
(`MLevel`) and the Jasmin row to `runBlock` and `legWeld`.

## Further reading

- [ASCENT.md](ASCENT.md): the guide, quick start, tactics and result tables.
- [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md): layers, entry points and exact hypotheses.
- [CORRECTNESS.md](CORRECTNESS.md): descent, ascent and transfer, and their welds.
- [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) and
  [HAX_RUST.md](HAX_RUST.md#3-existing-rust--lean-the-ascent-on-impexpr): imports and hax.
