# FAQ

## Is there a command-line compiler?

No. The compiler is a Lean library, like the CertiCoq Coq plugin: a program is a
Lean term or a Rust source extracted by hax, and "compile" means applying verified
functions and building the module. [GETTING_STARTED.md](GETTING_STARTED.md) compiles
one in a single command.

## How do I compile my own program?

Feed it through a front. A Rust routine goes through hax and the `thirToJasmin`
front; a Lean specification goes through relational compilation. Then apply the
backend and print the result — `CompilerHelloDemo.lean` is the template, and
[DEMO.md](DEMO.md) walks both fronts.

## How do I see the emitted assembly?

The backend has assembly printers. `lake env lean
CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean` compiles a routine and
prints its AArch64.

## What does "verified" mean here?

Every emitted kernel denotes its source specification, proved once over the compiler
rather than per primitive — the manual's "Headline theorems" section names the three
capstones. The guarantee covers the source fragment the compiler accepts.

## What is trusted?

`lake env lean AxiomAudit.lean` prints the axiom ledger of the headline theorems: the
cryptographic-hardness assumptions, the per-architecture machine model, the cited
Jasmin constant-time-preservation theorem, and the fidelity of hax extraction.

## Which programs are in scope?

The covered source — straight-line leaf calls, counted and public-condition loops,
branchless select, public-index array access, tuples, byte slices, integer
arithmetic, and data-dependent loops, over the prime-ir algebra. A public-input
variable-time path such as RSA verification is accepted; a secret-dependent one is
rejected.

## Which targets?

One owned backend emits x86-64, AArch64, and RISC-V as machine bytes. The
constant-time clause is anchored on the x86 model.

## Why is the first build slow?

It builds mathlib and the CatCrypt libraries once; afterwards the build is
incremental. See [BUILDING.md](BUILDING.md).
