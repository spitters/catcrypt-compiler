# Changelog

## Unreleased

Pre-release research code (major version 0). Interfaces, the covered source
fragment, and the trust surface may change without notice — do not depend on it
as a stable API. The CatCrypt verified compiler as a standalone Lake package.

- Two fronts (hax/Rust → LowCT → `Com` IR) lowering to one verified owned
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
