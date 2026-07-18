# catcrypt-compiler

The CatCrypt **verified compiler** as a standalone Lake package: two fronts
(hax/Rust → LowCT → `Com` IR) lowering to one verified owned x86/ARM/RISC-V
backend. This package holds the compiler's **trust surface** — the ISA machine
models and jasmin-semantics *opacity* — kept out of `catcrypt-core`'s
near-axiom-free ledger. The byte-level instruction facts (`decode ∘ encode = id`,
ADCX/ADOX/MULX) are *proven*, not assumed (see the axiom ledger below).

## Scope (what is and isn't proved)

The correctness results cover the **`IsCoveredCtl` sublanguage** — the fragment
of hax-extracted Rust the front is proved to handle (ANF/control-flow shape;
see `COMPILER_ROADMAP.md` in the dev tree). It is **not** a proof that arbitrary
Rust compiles correctly. The end-to-end capstones present here include
`rustToJasminCom_endToEnd`, `robustCompilation_source_to_x86`, and
`compile_correct_all`. Per-scheme concrete emit endpoints (ECDSA/MLKEM/… byte
kernels) are deliberately **not** in this package — they live dev-side; this is
the generic verified compiler plus the covered fragment.

## Why a separate package

A component earns its own package when it needs a distinct **dependency/axiom
profile** a shared package can't express. The compiler qualifies: its deps are
`{catcryptCore, Veir, paramTransfer/CompPoly, hax-lean, mathlib}` — disjoint from
the security methodology — and it carries trust axioms that must not enter core's
ledger. Because Lake `require`s are per-package and edges point only
compiler → core, the split keeps core's axiom ledger clean.

## Module set

The `CatCryptCompiler` lib is the import-closure of the compiler subtree
(`CatCrypt.Crypto.{SecureCompilation,Jasmin,Optimizer}.*`) over the workspace:
the verified compiler proper plus the `catcryptCore` shims and foundational
leaves it consumes (1851 modules). The closure is free of every scheme security
proof and of the `MPC`/`Examples` protocol proofs; its only security-methodology
dependency is the foundational cost/monad layer in `catcryptCore`. Namespaces are
preserved so the dev tree consumes this package without import churn.

## Building

See [BUILDING.md](BUILDING.md) for first-time setup (`lake update` + the mathlib
cache), the build (memory-intensive — cap the workers), the axiom-ledger check,
and the API docs.

## Dependencies

`catcryptCore`, `Veir` (v4.29.0), `paramTransfer` + `CompPoly`, `hax-lean`,
`mathlib` (v4.30.0). **Not** VCVio. For a public build these must resolve from
public sources; `catcryptCore` is public, and `paramTransfer`/`hax-lean` are
being prepared for publication (see the release notes).

## Axiom ledger

Beyond Lean's standard axioms, the end-to-end capstones
(`rustToJasminCom_endToEnd`, `robustCompilation_source_to_x86`,
`compile_correct_all`) rest on exactly one extra axiom: a `native_decide`
reflection (`ofReduceBool`) discharging an AES S-box array-size check
(`JasminDialect.aesSboxArrayW_size`) — a candidate for elimination via a manual
decidability proof. The ISA byte-level facts (`decode ∘ encode`, ADCX/ADOX/MULX)
are proven, not axiomatised; the residual trust is definitional opacity of the
jasmin/ISA semantics plus that one `native_decide`. `AxiomAudit.lean` reproduces
the ledger (`lake env lean AxiomAudit.lean`) and should be a CI check.

## License & citation

MIT (`LICENSE`). If you use this, please cite the CatCrypt paper — see
`CITATION.cff`.
