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

The calculus follows AutoCorres (Greenaway, Andronick, Klein, ITP 2012; Greenaway, Lim,
Andronick, Klein, PLDI 2014) as ported to Lean by Sebastian Graf. From the port come the
idea of a correspondence relation, the organisation of abstraction into phases and the
vocabulary.

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

**The two automations produce different objects.** The ascent takes a program and
computes its abstract function, together with the correspondence. A
verification-condition generator takes a program and a postcondition and returns proof
obligations. The equivalences above are the only relation proved between them.

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
| field multiplication (167 instructions) and squaring (99) | CryptOpt, third-party | functional correctness over the instruction block | regions disjoint from the stack frame; multiplication limbs below 2⁵⁴; no byte statement |
| Ed25519 point addition, 4,909 instructions | this project's backend, verified again | the block computes its specification, which agrees with the group-law specification; stated at the bytes | separated memory cells; eleven compiled-evaluation checks; no frame conclusion |
| Ed25519 scalar reduction and multiply-add | this project's backend | functional correctness over the instruction block | eight and nine compiled-evaluation footprint checks |
| Ed25519 mixed addition, inversion, compression | this project's backend | functional correctness | mixed addition relative to assumed callees |
| field multiplication mod 2²⁵⁵ − 19; comb-table selection | hand-written in this project | correctness modulo p; selection correct at the bytes and constant time | constant time for tables of at most 2²⁶ entries |
| RV64 addition mod p256 | hand transcription | functional correctness | registers only; no memory, no bytes |

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
called *flat* by Grandis and Paré (Limits in double categories, 1999). This document
says *thin*, by analogy with thin categories (preorders). In the double-category
literature "thin" has another use: a *thin structure* in the sense of Brown and Mosa is
a double category with connections, which is not meant here.

**Quintets in Rel.** The relational instance of section 3 has relations in both
directions, since programs are interpreted as relations. It is an instance of
Ehresmann's quintet construction, which turns a 2-category K into a double category
whose arrows in both directions are the 1-cells of K and whose squares are the 2-cells
between the two composites round the boundary. For K the 2-category Rel of sets,
relations and inclusions, a quintet is a lax square f ; ⟦w⟧ ⊆ ⟦u⟧ ; g. Rel is locally a
preorder, so its quintets are flat. The instance of section 3 is this double category
pulled back along the semantics functor from programs to relations. The double category
Rel of the reminder is the part of it whose horizontal arrows are graphs of functions.

**Related uses.**

- Data refinement. Lax commuting squares of relations are the forward (downward)
  simulations of Hoare and He and of de Roever and Engelhardt. Horizontal pasting is
  sequential composition of programs; vertical pasting is composition of refinement
  steps.
- Tile logic (Gadducci and Montanari). Operational semantics is presented as a double
  category whose squares are rewrite tiles; it is not flat in general.
- Categorical systems theory (Myers). Double categories whose squares are simulations
  between open systems.

The references are cited from memory and have not been checked against the sources; the
direction of the inclusion has not been compared with the conventions for quintets.
