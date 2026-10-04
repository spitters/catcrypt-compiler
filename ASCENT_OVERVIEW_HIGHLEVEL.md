# The ascent: mathematical overview

This document states what the ascent proves, where its design comes from, its
categorical form and its relation to verification-condition generation. It contains no
Lean. [ASCENT_OVERVIEW_LEAN.md](ASCENT_OVERVIEW_LEAN.md) gives, section by section under
the same numbers, the declarations and modules that realise each statement.

1. [The problem and the relation to descent](#1-the-problem-and-the-relation-to-descent)
2. [Provenance](#2-provenance)
3. [Squares as a thin double category](#3-squares-as-a-thin-double-category)
4. [Verification-condition generation](#4-verification-condition-generation)
5. [Abstraction phases](#5-abstraction-phases)
6. [Loops, calls and frames](#6-loops-calls-and-frames)
7. [Automation](#7-automation)
8. [Results and comparison](#8-results-and-comparison)

Appendix: [Terminology and related constructions](#appendix-terminology-and-related-constructions)

## 1. The problem and the relation to descent

The ascent proves that given code computes a stated mathematical function. The code
exists before the proof: third-party assembly, output of this project's backend checked
again, hand-written blocks, or Rust extracted by hax. Descent runs the other way: a
verified compiler produces code from a specification.

**Judgement.** Fix a set M of machine states, a set A of abstract states, a state
relation R ⊆ M × A, a precondition P ⊆ A, an abstract step f : A → A and a program c with
a partial semantics ⟦c⟧ : M ⇀ M. The program c *corresponds to* f when

    ∀ m a.  R(m, a) ∧ P(a)  ⇒  ⟦c⟧(m) is defined  ∧  R(⟦c⟧(m), f(a)).

This is a forward simulation of f by c along R: related states with the precondition run
to related states, and the machine run does not fail.

The judgement is parametric in the semantics. It is instantiated at four:

1. a structured scalar language, first without and then with `while`;
2. blocks of x86-64 instructions, under a semantics transcribed from Jasmin's;
3. blocks of RV64 instructions;
4. the imperative expression language that hax extracts Rust to, under a fuelled
   denotation, with a companion judgement for whole functions.

The first three are instances of one definition over a step function C → M → Option M.

**Welds.** Ascent and descent compose at three points.

- A descent refinement of a specification by a scalar command, an ascent correspondence
  for the same command and the emission step compose to a statement about the denotation
  of the emitted program.
- A descent result yields a correspondence for the compiled x86 block.
- The correctness theorem of the hax front-end pipeline composes with a tower of
  correspondences over the source, from Rust source to bytes.

## 2. Provenance

The calculus follows AutoCorres [GAK12, GLAK14] as ported to Lean by Sebastian Graf.
From the port come the idea of a correspondence relation, the organisation of
abstraction into phases and the vocabulary.

The judgements are defined differently and are connected through the monadic program
logic. The port's is a triple over a relational weakest precondition, relating two
monadic programs. The one used here is the forward simulation of section 1, relating a
program under this project's own semantics to a function. Section 4 proves the
simulation equivalent to triples of the standard monadic logic at three levels: x86
blocks through the state monad, monadic Rust through the weakest-precondition structure
of its result monad, and extracted functions through the option monad. These are unary
triples; no theorem is stated about the port's relational triple itself. The
double-category presentation, the equivalences
with Hoare triples, the loop, call and frame rules, the automation and the kernel-level
theorems are this project's own.

## 3. Squares as a thin double category

**Reminder: the double category Rel.** Its objects are sets. Its arrows in one direction
are functions and in the other direction relations. A square with functions f, g and
relations R, S

        f
    X ────▶ X'
    │R      │S
    ▼       ▼
    Y ────▶ Y'
        g

exists when R(x, y) implies S(f(x), g(y)). A boundary carries at most one square, and
squares paste in both directions because implications compose. The double categories
below have the same form, with relations in both directions.
[Terminology and related constructions](#appendix-terminology-and-related-constructions)
are at the end.

**Definition.** A strict thin double category has a category of vertical arrows and a
category of horizontal arrows on the same objects, and a predicate Sq(u, f, g, w) on
boundaries

        u
    a ────▶ b
    │f      │g
    ▼       ▼
    c ────▶ d
        w

closed under vertical and horizontal pasting and containing the vertical and horizontal
identity squares. A boundary carries at most one square, so every coherence law
(interchange, associativity of both pastings, the unit laws, agreement of the two
identity squares on an identity boundary) holds without further proof obligations.

**Relational instance.** Assign to each object a a set X(a). Vertical arrows a → c are
relations between X(a) and X(c), with equality as identity and relational composition.
Horizontal arrows carry a functorial semantics ⟦−⟧ into relations. A square is a lax
square

    f ; ⟦w⟧ ⊆ ⟦u⟧ ; g,

that is, ∀ x y y'. f(x, y) ∧ ⟦w⟧(y, y') ⇒ ∃ x'. ⟦u⟧(x, x') ∧ g(x', y'): the top arrow
forward-simulates the bottom one. Pasting of squares is composition of simulations. The
content of an instance is the functoriality of its semantics and the identification of a
correspondence judgement with a square.

**Three instances.**

| Level | Objects | Horizontal arrows | Functoriality |
|---|---|---|---|
| x86 | machine states; abstract states A | instruction blocks under concatenation; steps A → A | running a concatenation is running the parts in sequence |
| monadic Rust | pairs of a value and a concrete state; pairs of a value and an abstract state | state-passing Kleisli arrows of the Rust result monad; pure maps | the monad laws, as equalities of programs |
| hax expressions | environment and value; abstract state and value | lists of expression legs under concatenation | running a list is running its legs in sequence |

At the x86 level a block denotes the graph of its run. A Hoare triple is the square over
the one-point abstract state with the identity step.

At the monadic level a program denotes the relation of its successful results, so a
failing or diverging program relates to nothing and a correspondence excludes both. The
bind rule of the correspondence calculus has the shape of horizontal pasting of squares
with the intermediate value fixed; the derivation of one from the other is not carried
out.

The expression level is the contrasting case. Sequencing of expressions is associative
only up to equality of runs, so the horizontal category is taken on lists of legs. The
right unit law of let-binding fails for squares: there is a square over
`let x = e in x` whose counterpart over `e` does not hold, and no exit relation of the
required shape repairs the converse. The law holds up to the bound name.

No instance is given for the address-level x86 machine, for RV64 or for the scalar
language.

## 4. Verification-condition generation

**Squares are families of triples.** Write {Q} c {Q'} for the Hoare triple over the
machine semantics. Then

    c corresponds to f under R, P   ⇔   ∀ a. P(a) ⇒ { R(−, a) } c { R(−, f(a)) }.

The triple on the right is the triple of the standard monadic program logic for the
state monad: running a block is a state-monad computation, and concatenation of blocks
is monadic bind. A verification-condition generator for that logic therefore applies to
x86 correspondence goals, and one instruction leaf is proved that way.

Three further statements connect the levels.

- Weakest preconditions transport along the monad morphism from total state
  computations to partial ones.
- A monadic Rust correspondence holds iff, for each related entry, some exit state
  satisfies a total-correctness triple.
- A function-level correspondence for extracted Rust is a triple over the partial
  program that guards the abstract function by its precondition.

**Correspondences as specification lemmas.** For every postcondition Q,

    c corresponds to f under R, P   ⇔
      ∀ Q.  { m | ∃ a. R(m, a) ∧ P(a) ∧ ∀ m'. R(m', f(a)) ⇒ Q(m') }  c  { Q }.

The statement holds for the generic step-function judgement and so for the scalar
language, x86 and RV64, and in a state-indexed form for the monadic Rust square. For a
verification-condition generator the useful form is the state-indexed family
{ R(−, a) } c { R(−, f(a)) }: used as the specification of a callee, it composes in any
position of the caller. The form with arbitrary Q composes only when the callee comes
last, because the generator does not continue under the existential.

**Extracted Rust.** For a function-level correspondence of an extracted function e with
abstract function f, the monadic reading of e satisfies the partial-correctness triple
"every returned value encodes f(a)". The total triple is equivalent to termination of
the reading, which the correspondence does not imply: the correspondence constrains
the operation table only where it returns, and checked word operations fail on
overflow. On a kind-checked fragment the reading terminates, and the total triple
follows from the correspondence together with a typing of the operation table. The
fragment has literals, variables, let-binding, sequencing, applications of typed
operations, conditionals on Boolean conditions, and counted loops with literal bounds in
[0, 2³²]. Kinds include index ranges, so array indexing in a loop is total, and word
ranges [L, U), under which each checked operation is total: addition when U₁ + U₂ fits
the width, subtraction when the subtrahend's upper bound is at most the minuend's lower
bound plus one, multiplication when U₁ · U₂ fits the width, division and remainder when
the divisor's lower bound is at least one. The example is an equality test on 32-byte
arrays, a 32-step loop whose body is a conditional; its contract, in the form the hax
Lean printer emits (a precondition, a postcondition and the triple between them), is
closed from the correspondence, without a verification-condition proof over the body.

**Loops.** The block-replication rule of section 6 is an instance of the invariant rule
of the program logic, at the invariant "the machine state is related to the i-fold
step". The same holds at the monadic Rust level: for a loop whose body carries a counter
i and continues while i < N, the square for the N-fold abstract step follows from the
body squares through the invariant rule with measure N − i, and a square for a loop is
equivalent to the corresponding total specification. The iteration that extracted `for`
loops use is equal, as a program, to such a counted loop, so the rule applies to them
directly.

**The two automations produce different objects.** The ascent takes a program and
computes its abstract function, together with the correspondence. A
verification-condition generator takes a program and a postcondition and returns proof
obligations. Given the abstract function as an unknown, the generator does not
synthesise it: it reduces the goal to one condition per instruction with the unknown
unassigned, and that condition is solved, and the unknown determined, by the ascent's
leaf correspondences.

## 5. Abstraction phases

Three AutoCorres phases have a counterpart, each with a soundness theorem, and a guarded
total abstraction covers every scalar command.

| Phase | Content | Soundness statement |
|---|---|---|
| word abstraction | the encoding of 64-bit words in ℤ/2⁶⁴ | a word-level correspondence for f_w and a naturality square enc ∘ f_w = f ∘ enc give a ring-level correspondence for f |
| value abstraction | an encoding C → A with a refinement predicate on C, inducing state relations; closed under products, function spaces and composition | an n-limb addition with carry over register windows corresponds to addition of the encoded values |
| type strengthening | the abstract program is placed in the lowest monad that expresses it: pure, option, or exception | the strengthened program refines the original |
| guards | every command is assigned a word transformer and a list of guards | under the guards, the command corresponds to the transformer |

The value abstraction reads named scalar variables and registers; it is not a lifting of
a typed heap. The total abstraction assigns the unsatisfiable guard to the constructs
outside its fragment, where its soundness statement is vacuous.

## 6. Loops, calls and frames

Write f^N for N-fold iteration.

| Rule | Statement |
|---|---|
| counted loop | if the body corresponds to f, the loop of N iterations corresponds to f^N |
| indexed counted loop | with an index-dependent step f_i, the loop corresponds to f_{N−1} ∘ … ∘ f_0 |
| while, partial | a terminating run from a state related to a with P(a) ends in a state related to some a' with P(a') and the guard false |
| while, functional | the run is related to the abstract iteration of the body while the abstract guard holds; the statement is total under a bound on the iteration count |
| while with early exit | the loop is simulated by an abstract loop in the exception monad |
| block replication | n copies of an x86 block that corresponds to f correspond to f^n |
| call frame | a call returns with the stack pointer and each pushed register at its value at the call |

One loop theorem is stated at the bytes, about a loop this project's backend exports
(limb-wise AND of two n-limb operands): every program that the bytes decode to halts,
for 1 ≤ n < 2⁶⁴ and pointers satisfying a layout condition, in a state satisfying the
postcondition.

The x86 instruction type has no `push`, `pop`, `call` or `ret`; the call-frame theory
expresses them as instruction sequences. For the third-party Montgomery multiplication of
section 8, the pushes and pops of the source are replaced by stores below the stack
pointer, and the theorem concludes that the stack pointer and the callee-saved registers
end at their entry values.

## 7. Automation

Four kinds of automation close correspondence goals. They differ in what is trusted.

- **Decision by reflection.** A decidable predicate delimits a fragment of scalar
  commands; a soundness theorem gives, for each command c in the fragment, the
  correspondence of c with a computed word-level function, under the trivial
  precondition.
- **Symbolic engine over an instruction table.** A worklist procedure composes proved
  leaf correspondences, indexed by state relation and instruction, using the composition
  and weakening rules. It produces an ordinary proof term; side conditions are decided
  or returned to the user.
- **Verified symbolic executor.** A checker for one part of a block is proved sound: a
  passing check yields an implication between symbolic location maps across the run of
  that part, and parts chain. The check is evaluated by the kernel. Cut certificates are
  generated by programs outside the proof assistant and are untrusted.
- **Generator for extracted Rust.** A procedure produces, for each extracted function,
  its abstract function and the function-level correspondence. The same statement is
  provable through the generator and rule by rule. Trait-generic functions are covered
  by a monomorphisation equivalence.

## 8. Results and comparison

**Example statement.** For the third-party Montgomery multiplication modulo the P-384
prime p, with six-limb operands x, y read at the argument pointers and the result z read
at the destination pointer after the run:

    x · y ≤ 2³⁸⁴ · p   ⇒   z < p   ∧   z ≡ x · y · 2⁻³⁸⁴  (mod p).

The hypothesis is the precondition stated in the source; no separation of the buffers is
assumed.

| Kernel | Origin | Statement | Limit |
|---|---|---|---|
| Montgomery multiplication mod p384, 264 instructions | s2n-bignum, third-party, hand-written | the statement above, over the instruction block and over its encoding | the source's precondition |
| field multiplication (167 instructions) and squaring (99) | CryptOpt, third-party | the output limbs are congruent to x·y, respectively x², modulo 2²⁵⁵ − 19 (no z < p) | inputs disjoint from each other and from the stack frame; for squaring, input and output disjoint; multiplication limbs below 2⁵⁴; no byte statement |
| Ed25519 point addition, 4,909 instructions | this project's backend, verified again | for the eight input coordinates below p, the decoded bytes compute the four output coordinates of the specification, which agrees in ℤ/p with the extended twisted-Edwards addition formulas | separated memory cells; inputs below p; eleven compiled-evaluation checks; no frame conclusion |
| Ed25519 scalar reduction and multiply-add | this project's backend | the output is x mod L, respectively (a·b + c) mod L, below L, with L the group order | separated memory cells; eight and nine compiled-evaluation footprint checks |
| Ed25519 mixed addition, inversion, compression | this project's backend | mixed addition computes its specification; inversion computes z^(p−2) mod p, the inverse for z ≠ 0; compression outputs y + 2²⁵⁵·(x mod 2) for the affine coordinates x, y | inputs below p; buffer disjointness; the callees are discharged over the shipped blocks |
| field multiplication mod 2²⁵⁵ − 19; comb-table selection | hand-written in this project | the product is (x·y) mod p; for an index D < 16, the selected words equal table entry D, with the table, the stack pointer and the callee-saved registers unchanged, at the bytes; the leakage trace is independent of the index | constant time for tables of at most 2²⁶ entries |
| RV64 addition mod p256 | hand transcription | for x, y < p256, the result is (x + y) mod p256 | registers only; no memory, no bytes |

**Scope.** A statement at the bytes says that this project's encoding of the block
decodes, under this project's decoder, to instructions with the stated behaviour. No
theorem concerns an object file; the assembler, the loader and the import of third-party
text are covered by tests. The constant-time statement for point addition is over the
block. No theorem composes a function-level correspondence for extracted Rust with a
machine-level square.

| Approach | Relation established |
|---|---|
| AutoCorres | design source; word abstraction, type strengthening and guards have counterparts |
| Graf's Lean port | design and vocabulary |
| monadic verification-condition generation | x86 squares are families of triples of the standard logic; one leaf proved by the generator |
| Jasmin | the x86 semantics transcribes Jasmin's; one weld ends at an emitted Jasmin program |
| CryptOpt | two kernels proved correct over the imported text |
| s2n-bignum | one kernel proved correct under its source precondition |
| translation validation | the Ed25519 blocks are single backend outputs checked without the compiler's theorems |
| Aeneas | the monadic level is the Kleisli instance over its result monad |

The table is restricted to what is proved; comparisons of method, proof effort and
trusted base need the literature and are not made here.

## Appendix: terminology and related constructions

**Thin and flat.** A double category in which a square is determined by its boundary is
called *flat* by Grandis and Paré [GP99, §1.1]. This document says *thin*, by analogy
with thin categories (preorders). In the double-category literature *thin* has another
use: a *thin structure* on an edge-symmetric double category (Spencer; Brown and Mosa
[BM99]) is a double functor from the double category of commutative squares that
selects the thin squares, and Brown and Mosa prove it equivalent to a connection pair.
That notion is not meant here.

**Quintets in Rel.** The relational instance of section 3 has relations in both
directions, since programs are interpreted as relations. Ehresmann's quintet
construction [Eh63] turns a 2-category K into a double category Q K whose arrows in both
directions are the 1-cells of K; a square with top u, left f, right g and bottom w is a
2-cell u ; g ⇒ f ; w of K [GP99, §1.3]. For K the 2-category Rel of sets, relations and
inclusions, the squares of this document, f ; ⟦w⟧ ⊆ ⟦u⟧ ; g, carry the opposite 2-cell:
they are the quintets of Rel^co, equivalently the squares of the transpose of Q Rel. Rel
is locally a preorder, so these quintets are flat. The instance of section 3 is this
double category pulled back along the semantics functor from programs to relations. The
double category Rel of the reminder is the part of it whose horizontal arrows are graphs
of functions.

**Related uses.**

- Data refinement. Take an abstraction relation R from abstract to concrete states as
  both vertical sides, the abstract operation A on top and the concrete operation C at
  the bottom. A lax square is then the forward (downward) simulation condition
  R ; C ⊆ A ; R of He, Hoare and Sanders [HHS86, HHS87], which de Roever and Engelhardt
  call L-simulation [dRE98]. Horizontal pasting is sequential composition of programs;
  vertical pasting is composition of refinement steps. The squares of this document
  ask more than the inclusion when the program is partial: the run must exist, so a
  correspondence also excludes failure.
- Tile logic [GM00]. Operational semantics is presented as a double category whose
  squares are rewrite tiles; distinct tiles may share a boundary, so it is not flat in
  general.
- Categorical systems theory [My21]. Open dynamical systems form a double category whose
  arrows in one direction are behaviours (trajectories, steady states, periodic orbits)
  and in the other wirings; its squares are commuting conditions.

**References.**

- [BM99] R. Brown, G. H. Mosa. Double categories, 2-categories, thin structures and
  connections. Theory Appl. Categ. 5(7):163–175, 1999.
- [dRE98] W.-P. de Roever, K. Engelhardt. Data Refinement: Model-Oriented Proof Methods
  and their Comparison. Cambridge Tracts in Theoretical Computer Science 47, CUP, 1998.
  doi:10.1017/CBO9780511663079.
- [Eh63] C. Ehresmann. Catégorie double des quintettes; applications covariantes. C. R.
  Acad. Sci. Paris 256:1891–1894, 1963.
- [GM00] F. Gadducci, U. Montanari. The tile model. In G. Plotkin, C. Stirling, M. Tofte
  (eds.), Proof, Language, and Interaction: Essays in Honour of Robin Milner, MIT Press,
  2000, 133–166.
- [GP99] M. Grandis, R. Paré. Limits in double categories. Cahiers Topologie Géom.
  Différentielle Catég. 40(3):162–220, 1999.
- [GAK12] D. Greenaway, J. Andronick, G. Klein. Bridging the gap: automatic verified
  abstraction of C. ITP 2012, LNCS 7406, 99–115. doi:10.1007/978-3-642-32347-8_8.
- [GLAK14] D. Greenaway, J. Lim, J. Andronick, G. Klein. Don't sweat the small stuff:
  formal verification of C code without the pain. PLDI 2014, 429–439.
  doi:10.1145/2594291.2594296.
- [HHS86] He Jifeng, C. A. R. Hoare, J. W. Sanders. Data refinement refined. ESOP 86,
  LNCS 213, 187–196. doi:10.1007/3-540-16442-1_14.
- [HHS87] C. A. R. Hoare, He Jifeng, J. W. Sanders. Prespecification in data refinement.
  Inf. Process. Lett. 25(2):71–76, 1987. doi:10.1016/0020-0190(87)90224-9.
- [My21] D. J. Myers. Double categories of open dynamical systems (extended abstract).
  ACT 2020, EPTCS 333:154–167, 2021. doi:10.4204/EPTCS.333.11.
