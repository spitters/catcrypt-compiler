# Changelog

## Unreleased

Documentation, one demo module, CI, and dead-code removal since
`v0.1.0-alpha.1`; the compiler's supported interfaces and headline theorems are
unchanged.

- New documentation: `GETTING_STARTED.md` (compile a program in one command),
  `DEMO.md`, `EXAMPLES.md`, `PROVENANCE.md`, `bench.md`, and the Verso manual under
  `docs/` — a separate Lake package, so verso is not a dependency of the library.
- New module `CatCrypt/Crypto/SecureCompilation/CompilerHelloDemo.lean`: a Rust
  routine lowered through the hax front to AArch64, printing the emitted assembly.
- `DOCS.md` removed; the manual and `BUILDING.md` cover its content.
- Removed three dead prototype modules
  (`Dialects/ByteMemrefFrontPrototype.lean`, `X86Backend/_MpnFrontCheck.lean`,
  `X86Backend/_MpnFrontScratch.lean`) and a small set of unused declarations;
  nothing in the library referenced them.
- CI caps the compiler build to two cores to fit the runner memory.

## 0.1.0-alpha.1 — 2026-07-18 (pre-release)

Pre-release research code (SemVer pre-release; major version 0). Interfaces, the
covered source fragment, and the trust surface may change without notice — do not
depend on it as a stable API. The CatCrypt verified compiler as a standalone Lake
package.

- Two fronts (hax/Rust → LowCT → `Com` IR) lowering to one verified
  x86/ARM/RISC-V backend, packaged as the import-closure of the compiler subtree
  (1851 modules), free of every scheme security proof and of the `MPC`/`Examples`
  protocol proofs.
- End-to-end capstones `rustToJasminCom_endToEnd`, `robustCompilation_source_to_x86`,
  and `compile_correct_all` over the covered `IsCoveredCtl` fragment.
- The ISA byte-level facts are proven; the residual trust is jasmin/ISA
  definitional opacity plus one `native_decide` reflection axiom (`AxiomAudit.lean`).
- Dependencies resolve from git (`catcryptCore`, `Veir`, `paramTransfer`,
  `CompPoly`, `hax-lean`, `mathlib`); MIT licensed; `CITATION.cff` (ePrint 2026/604).

> Experimental research prototype — not a production tool.
