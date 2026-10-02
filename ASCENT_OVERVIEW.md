# The ascent: an overview

This document states what the ascent proves, where its design comes from, its
categorical form and its relation to verification-condition generation. `Ascent/` stands
for `CatCrypt/Crypto/SecureCompilation/Ascent/` and `Hax/Ascent/` for `CatCrypt/Hax/Ascent/`.

1. [The problem and the relation to descent](#1-the-problem-and-the-relation-to-descent)
2. [Provenance](#2-provenance)
3. [Squares as a thin double category](#3-squares-as-a-thin-double-category)
4. [Verification-condition generation](#4-verification-condition-generation)
5. [Abstraction phases](#5-abstraction-phases)
6. [Loops, calls and frames](#6-loops-calls-and-frames)
7. [Automation and its cost](#7-automation-and-its-cost)
8. [Results and comparison](#8-results-and-comparison)
9. [Further reading](#further-reading)

## 1. The problem and the relation to descent

The ascent proves that given code computes a stated Lean function. The code exists
before the proof: third-party assembly, output of this project's backend checked again,
hand-written blocks, or Rust extracted by hax. Descent runs the other way: the verified
compiler produces code from a specification ([CORRECTNESS.md](CORRECTNESS.md)).

The judgement is a forward simulation. `CorresJ SR P fa c` holds when every machine state
related by `SR` to an abstract `a` with `P a` runs under block `c` to a state related to
`fa a` (`Ascent/RunBlockCorres`). The same shape is stated over four semantics:

| Judgement | Program | Semantics | Module |
|---|---|---|---|
| `Corres`, `CorresU` | `LowCT` command | `semScalar`; `semU` with `while` | `Ascent/Corres`, `Ascent/WhileTop` |
| `CorresJ` | `List (JInstr 64)` | `runBlock`, Jasmin's x86 semantics in Lean | `Ascent/RunBlockCorres` |
| `CorresR` | RV64 block | `runRBlock64` | `Ascent/CorresRiscv` |
| `Corres`, `FnCorres` | hax `ImpExpr` | `denote'` with fuel | `Hax/Ascent/Corres` |

`CorresGeneric.CorresM step SR P fa c` states the simulation once for a step function
`step : C → M → Option M`; `corres_eq_corresM` (by `rfl`), `corresJ_eq_corresM` and
`corresR_eq_corresM` identify the three machine judgements with it.

Ascent and descent meet at three welds
([CORRECTNESS.md](CORRECTNESS.md#composition-of-the-techniques)). `legWeld` joins a
descent refinement `RRefines spec c`, an ascent square `Corres SRwordNT P fa c` and the
emit leg into the denotation of the emitted Jasmin program. `corres_of_refines_x86` turns
a descent result into a simulation of the compiled x86 block, and
`feSub_raw_source_to_bytes` composes hax-lean's `pipeline_correct` with a source tower.

## 2. Provenance

The calculus follows AutoCorres (Greenaway, Andronick, Klein, ITP 2012; Greenaway, Lim,
Andronick, Klein, PLDI 2014) as ported to Lean by Sebastian Graf in
[sgraf812/ascent](https://github.com/sgraf812/ascent); [PROVENANCE.md](PROVENANCE.md)
records the details. The package takes from the port a correspondence relation named
`Corres`, abstraction organised in AutoCorres phases, and the names `Ascent`, `ascend` and
`Corres`. No declaration is taken: of the port's 293 declaration names, two (`Heap`,
`incr`) recur in the `Ascent` modules, with different definitions. The port's judgement
is a relational weakest-precondition triple over `Std.Internal.Do`; the package's is a
forward simulation over its own semantics. The judgements over `semScalar`, `runBlock`,
`runBlockA`, `runRBlock64` and `denote'`, the double-category presentation, the `Std.Do`
equivalences, the loop, call and frame rules, the engines and every kernel-level theorem
are this project's own.

## 3. Squares as a thin double category

The x86, `RustM` and `ImpExpr` judgements are squares of strict thin double
categories of relations. Core's module
`CatCryptCore.ForMathlib.CategoryTheory.ThinDoubleCategory` defines the class
`ThinDoubleCategory`: a vertical category on `C`, a horizontal category on the synonym
`Hor C`, and a `Prop`-valued predicate `Sq u f g w` on boundaries (top `u`, left `f`,
right `g`, bottom `w`) closed under `vcomp`, `hcomp`, `vid` and `hid`. Thinness makes
every coherence law hold by proof irrelevance: `interchange`, `vcomp_hid`, `hcomp_vid`
and `vid_id_eq_hid_id` are `rfl`; `vcomp_assoc`, `hcomp_assoc` and the four unit laws are
heterogeneous equalities.

The relational instance `ofRelSemantics` takes carriers `X : C → Type`, vertical arrows
the relations between carriers (`relCategory`: identity `=`, composition
`Relation.Comp`), and a functorial semantics of horizontal arrows as relations
(`RelSemantics`, laws `sem_id`, `sem_comp`). Its squares are the lax squares
`f ; ⟦w⟧ ⊆ ⟦u⟧ ; g`, the forward simulations of the bottom arrow by the top one:

```lean
def RelSemantics.LaxSq (S : RelSemantics X) {a b c d : C} (u : Hor.of a ⟶ Hor.of b)
    (f : X a → X c → Prop) (g : X b → X d → Prop) (w : Hor.of c ⟶ Hor.of d) : Prop :=
  ∀ x y y', f x y → S.sem w y y' → ∃ x', S.sem u x x' ∧ g x' y'
```

The content of an instance is the functoriality of its semantics and the identification
of a judgement with a square. Three instances exist:

| Instance | Objects and carriers | Horizontal arrows | Judgement as square |
|---|---|---|---|
| `JLevel A` ([SquareStrictDouble](CatCrypt/Crypto/SecureCompilation/Ascent/SquareStrictDouble.lean)) | `mach : JState 64`, `abs : A` | blocks under `++`, unit `[]`; steps `A → A` | `sq_mach_iff`, `corresJ_iff_sq`, `runBlockTriple_iff_sq` |
| `MLevel C S` ([RustMSquareDouble](CatCrypt/Crypto/SecureCompilation/Ascent/RustMSquareDouble.lean)) | `conc A : A × C`, `abs A : A × S` | `A → C → RustM (B × C)` under `kseq`, unit `pureK`; maps `S → A → B` | `sq_conc_iff`, `corresM_iff_sq` |
| `CLevel bi S` ([SquareDouble](CatCrypt/Hax/Ascent/SquareDouble.lean)) | `conc : Env × Value`, `abs : S × Value` | lists of `ImpExpr` legs under `++` | `sq_conc_iff`, `sq_single_of_corres`, `corres_seqOfList_of_sq` |

At `JLevel` a block denotes the graph of `runBlock`, and functoriality is
`runBlock_append`. A Hoare triple is the square over the one-point abstract state with
the identity step at the bottom (`runBlockTriple_iff_sq`). `Ascent/SquareStrict` states
the same algebra directly (`VMapJ`, `corresJ_hcomp`, `vmapJ_hcomp_interchange`).

At `MLevel` the concrete horizontal category is the Kleisli category of state-passing
programs over `Aeneas.Std.RustM`; `kseq_pure_left`, `kseq_pure_right` and `kseq_assoc`
are equalities of programs (`Ascent/RustMSquare`). A program denotes the relation of its
`.ok` results, so `.fail` and `.div` relate to nothing (`corresM_ne_fail`,
`corresM_ne_div`). The docstring identifies `corresM_bind` with horizontal pasting of
value-pinned squares; no theorem derives one from the other. This `CorresM`
(`Hax.Ascent.RustM`) is a different declaration from the generic one of section 1.

`ImpExpr` is the contrasting case. `.seq` is associative only up to equality of runs
(`denote'_seq_assoc`), so the instance takes lists of legs, and its squares are the
plain-valued correspondences. The right unit of `letBind` composition fails:
`corres_letBind_var_right_not_iff` exhibits a square over `.letBind x e (.var x)` that
holds while the square over `e` does not, and `not_exit_of_read_of_lower` shows that no
exit relation of the needed shape closes the converse. `letBind_var_right_unit_offName`
proves the law up to the bound name. No instance exists for `runBlockA`, `CorresR` or
`LowCT`.

## 4. Verification-condition generation

An x86 square is a family of Hoare triples, and these triples are Lean `Std.Do`
triples. The central equivalence is `corresJ_iff_triple`
([CorresHoare](CatCrypt/Crypto/SecureCompilation/Ascent/CorresHoare.lean)):

```lean
theorem corresJ_iff_triple {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) :
    CorresJ SR P fa c
      ↔ ∀ a, P a → RunBlockTriple (fun st => SR st a) c (fun st => SR st (fa a))
```

| Statement | Declarations |
|---|---|
| `RunBlockTriple P c Q` is the `Std.Do` triple over `runBlockM c : StateM (JState 64) Unit` | `runBlockM_run`, `runBlockM_triple_iff` (`Ascent/RunBlockMvcgen`) |
| sequencing of blocks is monadic bind | `runBlockM_append`, `runBlockM_triple_hcomp` |
| the `sbb` leaf is proved by `mvcgen [stepM_spec]` | `sbb_leaf_triple_mvcgen` |
| weakest preconditions transport along `θ : StateM S → StateT S Option` | `theta_pure`, `theta_bind`, `wp_theta_eq` (`rfl`), `Spec.wp_theta` |
| a `RustM` square holds iff, per entry, some exit state satisfies a total triple | `corresM_iff_triple` |
| `FnCorres` is a triple over the `Option` program `optGuard G f a` | `fnCorres_iff_triple`, `triple_option_iff` |

The two automations produce different objects. The ascent engines output an abstract
function (`asemWExpr c`, or `Ns.HaxGen.f.gen` from the hax generator); `mvcgen` takes a
postcondition and outputs verification conditions. No theorem relates the two beyond the
equivalences above, and no module under `Hax/Ascent/` uses `mvcgen`. The `*Mvcgen`
modules other than `RunBlockMvcgen*` are probes outside the calculus
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#research-probes-outside-the-calculus)).

## 5. Abstraction phases

Three AutoCorres phases have a counterpart here, each with a soundness theorem, and a
guarded total abstraction covers every `LowCT` command.

| Phase | Content | Soundness |
|---|---|---|
| word abstraction | `wEnc : BitVec 64 → ZMod 2^64` lifts a word-level square to a ring-level one, given a naturality square | `corres_WA` (`Ascent/Phases`) |
| value abstraction | `ValueAbs C A`, an encoding with a refinement predicate; store relations `SRof V`, `SRcarryOf V`; closed under `pair`, `pi`, `comp` | `feAddN_capstone`: an `n`-limb `adcx` chain over register windows (`Ascent/Demos/HeapAbs`) |
| type strengthening | the lowest result monad (pure, `Option`, exception) for the abstract program | `tsLowCT_sound` (`Ascent/Strengthen`); demo `feSubC_ts_refines` |
| guards | `ascendG fuel c`: a word transformer and a list of guards | `ascendG_sound` (`Ascent/Guards`) |

The value abstraction lives in a module named `HeapAbs`, but it reads named scalar
variables and registers; it is not a typed-heap lifting. The total abstraction gives 11
constructors the guard `False`
([ASCENT_REFERENCE.md](ASCENT_REFERENCE.md#the-total-abstraction-assigns-an-unsatisfiable-guard-to-11-constructors)).

## 6. Loops, calls and frames

Loop rules exist for `LowCT` and x86 blocks and a frame lemma for calls on `runBlockA`;
each is applied to few kernels. The last column names the other modules whose proofs
apply the rule.

| Rule | Statement | Applied in |
|---|---|---|
| `corres_for` (`Ascent/Control`) | a counted `RFor` loop realises `nfold fa N` | `LoopSourceLeaf`, `KeystoneControl` |
| `corres_for_indexed` | the same with an index-dependent step, `ifold fa N` | `MlkemPolyFoldCorres` |
| `corresU_while` (`Ascent/WhileTop`) | a terminating `RWhileNz` run reaches some `a'` with `P a'` and the guard false | none |
| `corresU_whileFun`, `_total` (`Ascent/WhileFun`) | the run is related to `loopFun guardA fb (fb a)`; total under a fuel bound | `WhileFunSum`, `WhileFunEmit` |
| `corresU_while_exit` (`Ascent/Exit`) | a loop with early exit is simulated by `whileE C fb` | none |
| `corresJ_loop` (`Ascent/RunBlockCorres`) | `n` copies of a block body realise `loopStep step n` | `JasminMirrorTie` |
| `framedCall_popped` (`Ascent/CallFrame`) | a call returns `%rsp` and each pushed register at its value at the call | the Ed25519 call proofs |

`and_n_bytes_value` is a loop theorem at the bytes, about a loop this project's backend
exports: every program the bytes of `mpn_and_n_loop_owned` decode to halts, for
`1 ≤ n < 2^64` and pointers satisfying `AndNLayout`, in a state satisfying `AndNPost`. `CallFrame` writes `push`, `pop`, `call`
and `ret` as `JInstr` sequences, since `JInstr 64` has none of them.
`s2nMontmulP384FramedBytes_correct` replaces the source's `pushq`/`popq` by red-zone
stores and concludes that `%rsp` and the callee-saved registers end at their entry values.

## 7. Automation and its cost

Four kinds of automation, of different trust, close ascent goals; the tactic per goal
shape is in [ASCENT.md](ASCENT.md#tactics).

- Deciding tactics. `ascend_expr!` decides membership in the fragment `IsAscendableExpr`
  and applies `ascend_expr_sound`, which gives
  `Corres SRwordNT (fun _ => True) (asemWExpr c) c` (demo `arithK_expr`).
- A symbolic engine over an instruction table. `corres_sym` and its siblings run a
  worklist in `Lean.Meta.Sym` over a `CorresSymEngine.Machine`: the leaves of a judgement
  (`CorresJ`, `CorresR` or `Corres`) indexed by state relation and instruction, with its
  composition and weakening lemmas. Side conditions go to `decide` or are returned
  (demos `sbb3_refines`, `addCarry_ascends`).
- A verified symbolic executor. `partCheck_sound` (`Ascent/Demos/Ed25519SymExec`) turns a
  passing check of one part of a block, run by `decide +kernel`, into a `runBlock`
  implication between location maps; `mapHolds_cat` chains parts. Programs in
  `scripts/cutgen/`, run outside the build, generate the cut certificates.
- The hax generator. `Hax.Ascent.Gen.ascendFn` produces the abstract function and its
  `FnCorres`; `hax_ascend Ns` runs it over an extraction. `line_corres_gen` (tactic
  `hax_corres`) and `line_corres_rules` (rule by rule) prove one statement both ways.
  `fnCorres_monomorphise_iff` covers trait-generic functions.

`scripts/build-cost-baseline.tsv` records per module the elaboration and import times and
the peak memory. Its highest ascent peaks are `Ed25519PointAddShippedProof` (3,788 MB),
`CarryMulCorrect` (3,756 MB) and `Ed25519ScMuladdShippedProof` (3,563 MB); the
s2n-bignum modules stay below 1,900 MB.

## 8. Results and comparison

The table adds a limit to each result of [ASCENT.md](ASCENT.md). Most are stated on the
address machine `runBlockA`; the s2n-bignum byte and framed forms use `runBlock`.

| Kernel | Origin | Theorem | Limit |
|---|---|---|---|
| `bignum_montmul_p384`, 264 instr. | s2n-bignum, third-party, hand-written | `s2nMontmulP384_correct_addr`; bytes: `s2nMontmulP384Bytes_correct` | `x·y ≤ 2^384·p384`, the source's precondition; no buffer separation assumed |
| `carry_mul` (167), `solinas_square` (99) | CryptOpt, third-party | `carryMul_correct_addr`, `solinasSquare_correct_addr` | `RegionsApart` against the stack frame; `carry_mul` limbs below `2^54`; no byte statement |
| `ed25519_point_add`, 4,909 instr. | this project's backend, verified again | `paShippedBytes_correct`, `paSpec_addSpec` | `Separated` cells; eleven `native_decide` checks; no frame conclusion |
| `ed25519_sc_reduce`, `sc_muladd` | this project's backend | `scReduceShipped_correct_addr`, `scMuladdShipped_correct_addr` | eight and nine `native_decide` footprint checks |
| `ed25519_madd`, `invert`, `compress` | this project's backend | `maddShipped_correct_cross`, `invertShipped_correct`, `compressShipped_correct_addr` | `madd` relative to `MaddCallees` |
| `fe25519_mul`, comb select | hand-written in this project | `feMulBlock_mod`, `combSelectBytes_correct`, `selBytes_constant_time` | constant time for `n ≤ 2^26` entries |
| RV64 `(x + y) mod p256` | hand transcription | `addp256_correct` | registers only; no memory, no bytes |

The s2n-bignum theorem over the imported text is in
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

A statement at the bytes says that this package's encoding `encodeJBlock` of the block
decodes under `decodeJStream` to instructions with the stated behaviour. No theorem is
about an object file; the assembler, the loader and the import of third-party text are
checked by tests ([ASCENT.md](ASCENT.md#scope-of-the-statements)).
`ed25519PointAdd_constant_time` is stated over the block, not the bytes. No theorem
composes `FnCorres` with a machine square
([CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md#the-ascent-against-a-hax-reference)).

| Approach | Relation established in this repository |
|---|---|
| AutoCorres | design source; word abstraction, type strengthening and guards have counterparts |
| sgraf812/ascent | design and names; no shared declarations |
| Lean `mvcgen` | x86 squares are families of `Std.Do` triples; one leaf proved by `mvcgen` |
| Jasmin | `runBlock` transcribes Jasmin's x86 semantics; `legWeld` ends at an emitted Jasmin program |
| CryptOpt | two of its kernels proved correct over the imported text |
| s2n-bignum | one kernel proved correct under the precondition stated in its source |
| translation validation | the Ed25519 blocks are single backend outputs checked without the compiler's theorems |
| Aeneas | `CorresM` over `Aeneas.Std.RustM` forms the Kleisli instance `MLevel` |

The table is restricted to what the code in this repository establishes; comparisons of
method, proof effort and trusted base need the literature and are not made here.

## Further reading

- [ASCENT.md](ASCENT.md): the guide, quick start, tactics and result tables.
- [ASCENT_REFERENCE.md](ASCENT_REFERENCE.md): layers, entry points and exact hypotheses.
- [CORRECTNESS.md](CORRECTNESS.md): descent, ascent and transfer, and their welds.
- [CERTIFYING_THIRD_PARTY_CODE.md](CERTIFYING_THIRD_PARTY_CODE.md) and
  [HAX_RUST.md](HAX_RUST.md#3-existing-rust--lean-the-ascent-on-impexpr): imports and hax.
