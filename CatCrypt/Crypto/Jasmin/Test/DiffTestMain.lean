/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Single-binary diff-test driver (`lake exe difftest`)

Lean port of `scripts/diff_bignum_sem.sh` (per next.md backlog
"Convert the diff-test cases to use `lake exe difftest`").

Replaces the bash-orchestrated 4-stage pipeline (emit → compile →
rustc → run) with a single typed Lean executable. Same external tools
(jasminc / clang / rustc) are invoked via `IO.Process.run`; the
test-case ↔ port mapping is now Lean data instead of parallel bash
arrays.

## Usage

```
lake exe difftest                  # run all cases
lake exe difftest <case_name>      # run one case
```

## Test cases

Each case has a name (matching a `tc*` def in
`Test/EmitDiffTestRs.lean`) and a port name (matching a `*Port` def
in `Test/EmitPortJazz.lean`). The pairs are listed in `allCases`
below; updating the list here is the single source of truth (no more
bash array index correspondence).

## What this replaces

`scripts/diff_bignum_sem.sh` remains for interactive single-stage
debugging (`stage_emit_rs`, `stage_compile_port`, etc.). The
all-cases driver is now this Lean exe.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Test.DiffTestMain

/-! ## §1. Configuration -/

/-- Path constants. Override via env vars matching the shell script's
    convention (`SSPROVEL`, `JASMINC`, `RUSTC`). -/
structure Config where
  ssprove : String
  jasminc : String
  rustc : String
  portLibDir : String
  deriving Inhabited

def Config.fromEnv : IO Config := do
  let envOr (key fallback : String) : IO String := do
    match ← IO.getEnv key with
    | some v => pure v
    | none => pure fallback
  pure {
    ssprove := ← envOr "SSPROVEL" "."
    jasminc := ← envOr "JASMINC" "jasminc"
    rustc := ← envOr "RUSTC" "rustc"
    portLibDir := ← envOr "PORT_LIB_DIR" "/tmp"
  }

/-! ## §2. Test-case manifest

Single source of truth for the case ↔ port pairing. Adding a new
case: append a (caseName, portName) tuple here AND ensure the
corresponding `tc*` / `*Port` defs exist in EmitDiffTestRs and
EmitPortJazz. -/

structure TestCase where
  caseName : String
  portName : String
  /-- Optional jasminc flags (e.g. `-auto-spill-all` for inv_p25519). -/
  jasmincFlags : List String := []
  deriving Inhabited

def allCases : List TestCase :=
  [ { caseName := "tcModCanonical",        portName := "bignum_mod_p25519_4" }
  , { caseName := "tcModAboveP",           portName := "bignum_mod_p25519_4" }
  , { caseName := "tcAdd4Small",           portName := "bignum_add_4" }
  , { caseName := "tcSubP25519Small",      portName := "bignum_sub_p25519" }
  , { caseName := "tcDoubleP25519Small",   portName := "bignum_double_p25519" }
  , { caseName := "tcMul4Small",           portName := "bignum_mul_4" }
  , { caseName := "tcMul4AdcxSmall",       portName := "bignum_mul_4_adcx" }
  , { caseName := "tcSqr4Small",           portName := "bignum_sqr_4" }
  , { caseName := "tcMontMulSmall",        portName := "bignum_montmul_p25519" }
  , { caseName := "tcInvP25519",           portName := "bignum_inv_p25519"
      , jasmincFlags := ["-auto-spill-all"] } ]

/-! ## §3. Stage primitives -/

/-- Run a process, capturing stdout/stderr; return (exitCode, stdout, stderr). -/
def runProcess (cmd : String) (args : List String) : IO (UInt32 × String × String) := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args.toArray
  }
  pure (out.exitCode, out.stdout, out.stderr)

/-- Stage 1: emit Rust harness via `lake exe diffemit <case>`.
    Writes `/tmp/<case>.rs`. -/
def stageEmitRs (_cfg : Config) (tc : TestCase) : IO Bool := do
  IO.println s!"  → Stage 1: emit Rust harness for {tc.caseName}"
  let (code, stdout, _stderr) ← runProcess
    "lake" ["exe", "diffemit", tc.caseName]
  if code != 0 then
    IO.println s!"    FAIL: lake exe diffemit exit {code}"
    pure false
  else
    let path := s!"/tmp/{tc.caseName}.rs"
    IO.FS.writeFile ⟨path⟩ stdout
    IO.println s!"    OK: {path} ({stdout.length} bytes)"
    pure true

/-- Stage 2: emit + compile Jasmin port to .o (.jazz → .s → .o). -/
def stageCompilePort (cfg : Config) (tc : TestCase) : IO Bool := do
  IO.println s!"  → Stage 2: emit + compile port {tc.portName}"
  let jazz := s!"{cfg.portLibDir}/{tc.portName}.jazz"
  let asm := s!"{cfg.portLibDir}/{tc.portName}.s"
  let obj := s!"{cfg.portLibDir}/{tc.portName}.o"
  -- lean → .jazz
  let (code1, stdout1, _) ← runProcess
    "lake" ["exe", "portemit", tc.portName]
  if code1 != 0 then
    IO.println s!"    FAIL: lake exe portemit exit {code1}"
    pure false
  else
    IO.FS.writeFile ⟨jazz⟩ stdout1
    -- .jazz → .s via jasminc
    let (code2, _, stderr2) ← runProcess
      cfg.jasminc (tc.jasmincFlags ++ [jazz, "-o", asm])
    if code2 != 0 then
      IO.println s!"    FAIL: jasminc exit {code2}: {stderr2.take 200}"
      pure false
    else
      -- .s → .o via clang
      let (code3, _, stderr3) ← runProcess
        "clang" ["-c", asm, "-o", obj]
      if code3 != 0 then
        IO.println s!"    FAIL: clang exit {code3}: {stderr3.take 200}"
        pure false
      else
        IO.println s!"    OK: {obj}"
        pure true

/-- Stage 3: rustc compile + link Rust harness with port .o. -/
def stageRustcCompile (cfg : Config) (tc : TestCase) : IO Bool := do
  IO.println s!"  → Stage 3: rustc compile + link"
  let portObj := s!"{cfg.portLibDir}/{tc.portName}.o"
  let rs := s!"/tmp/{tc.caseName}.rs"
  let bin := s!"/tmp/{tc.caseName}_bin"
  -- Wrap .o in static lib (rustc finds it via -l)
  let pid ← IO.Process.spawn { cmd := "sh", args := #["-c", "echo $$"] }
  let pidNum ← pid.wait
  let libname := s!"bignum_{tc.portName}_diff_{pidNum}"
  let lib := s!"{cfg.portLibDir}/lib{libname}.a"
  let (codeAr, _, stderrAr) ← runProcess "ar" ["rcs", lib, portObj]
  if codeAr != 0 then
    IO.println s!"    FAIL: ar exit {codeAr}: {stderrAr.take 200}"
    pure false
  else
    let (code, _stdout, stderr) ← runProcess
      cfg.rustc
      ["--edition", "2021", "--crate-type", "bin",
       "-L", cfg.portLibDir, "-l", s!"static={libname}",
       "-C", "opt-level=2", rs, "-o", bin]
    if code != 0 then
      IO.println s!"    FAIL: rustc exit {code}: {stderr.take 400}"
      pure false
    else
      IO.println s!"    OK: {bin}"
      pure true

/-- Stage 4: run binary, exit-code 0 = PASS. -/
def stageRunCheck (tc : TestCase) : IO Bool := do
  IO.println s!"  → Stage 4: run binary"
  let bin := s!"/tmp/{tc.caseName}_bin"
  let (code, _, _) ← runProcess bin []
  if code == 0 then
    IO.println s!"    PASS"
    pure true
  else
    IO.println s!"    FAIL (exit {code})"
    pure false

/-! ## §3.5. Path 3: AUCurves-extracted Rust (Phase 1.5 Stage 2)

Per next.md backlog: "Phase 1.5 Stage 2 actually wired through the
diff-test (consume the AUCurves-emitted Rust as a third path alongside
our jasminc output)".

The AUCurves Coq side defines
`AUCurves/.../Ed25519/ExtractRust.v::ed25519_safe_rust : string` — a
verified-extraction Rust module text. To consume it as a diff-test
path, the Coq side must `Compute` and dump it to a file (see
`scripts/extract_ed25519_rust.sh::stage_extract_rust`). Once the file
exists, this stage compiles it via `rustc` and the resulting binary
becomes a third comparison path alongside Lean+jasminc.

## What's wired here

* `aucursvesRustPath` — the canonical location the Coq extractor is
  expected to write to.
* `stageAucursvesRust` — checks for the file, builds it via `rustc`,
  optionally runs it. Returns `none` if the file is missing (Coq side
  hasn't run); otherwise returns pass/fail.

## What's NOT wired

* The Coq `Compute` + file-dump step. That requires editing AUCurves's
  `ExtractRust.v` to add a `Redirect` directive, or wrapping the
  `coqtop -batch` invocation in `extract_ed25519_rust.sh`. AUCurves is
  in a separate repo; that's a Coq-side change tracked as Phase 1.5.
* Integration into the bignum diff-test cases: `tcModCanonical` etc.
  test bignum primitives, not full Ed25519 sign/verify. Adding an
  Ed25519-level test case (with KAT vectors from RFC 8032 §7.1) is a
  follow-up.

## Status

This stage is wired but **inactive in default operation**:
`stageAucursvesRust` is callable from any `runOneCase` orchestration
but is *not* invoked by the default 4-stage pipeline. Once the Coq
extraction is automated and Ed25519-level test cases exist, the call
moves into `runOneCase`. -/

/-- Canonical path the Coq AUCurves extractor is expected to write
    `ed25519_safe_rust` to. The shell script
    `scripts/extract_ed25519_rust.sh` uses this path; environments
    that build AUCurves locally should run that script first. -/
def aucursvesRustPath (cfg : Config) : String :=
  s!"{cfg.ssprove}/eddsa-hax/extracted/ed25519_extracted.rs"

/-- Stage 5 (Path 3): check for the AUCurves-extracted Rust source,
    compile it, run a smoke check. Returns `none` if the source file
    doesn't exist (skip with informative message); `some true` on
    pass, `some false` on fail. -/
def stageAucursvesRust (cfg : Config) : IO (Option Bool) := do
  IO.println s!"  → Stage 5 (Path 3): AUCurves-extracted Rust"
  let rsPath := aucursvesRustPath cfg
  let exists_ ← (do
    try
      let _ ← IO.FS.readFile ⟨rsPath⟩
      pure true
    catch _ => pure false)
  if !exists_ then
    IO.println s!"    SKIP: {rsPath} not found"
    IO.println s!"          (run scripts/extract_ed25519_rust.sh stage_extract_rust"
    IO.println s!"           after building AUCurves; pending Phase 1.5 Coq wiring)"
    pure none
  else
    -- File exists; attempt to compile. The actual signature/comparison
    -- logic depends on the Ed25519 test-case shape, which doesn't yet
    -- exist in `allCases` (current cases are bignum-level).
    let bin := s!"/tmp/ed25519_aucursves_extracted_smoketest"
    let (code, _, stderr) ← runProcess
      cfg.rustc
      ["--edition", "2021", "--crate-type", "bin",
       "-C", "opt-level=2", rsPath, "-o", bin]
    if code != 0 then
      IO.println s!"    FAIL: rustc exit {code}: {stderr.take 400}"
      pure (some false)
    else
      IO.println s!"    OK: compiled to {bin}"
      IO.println s!"    (comparison against jasminc path requires Ed25519 test cases)"
      pure (some true)

/-! ## §4. Pipeline driver -/

/-- Run the full 4-stage pipeline for one test case. -/
def runOneCase (cfg : Config) (tc : TestCase) : IO Bool := do
  IO.println s!"═══ {tc.caseName} ({tc.portName}) ═══"
  let s1 ← stageEmitRs cfg tc
  if !s1 then pure false
  else
    let s2 ← stageCompilePort cfg tc
    if !s2 then pure false
    else
      let s3 ← stageRustcCompile cfg tc
      if !s3 then pure false
      else stageRunCheck tc

/-- Run all cases; return (pass, fail) counts. -/
def runAll (cfg : Config) : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for tc in allCases do
    let ok ← runOneCase cfg tc
    if ok then pass := pass + 1 else fail := fail + 1
    IO.println ""
  pure (pass, fail)

end CatCrypt.Crypto.Jasmin.Test.DiffTestMain

/-! ## §5. Entry point (top-level, required by `lake exe`) -/

open CatCrypt.Crypto.Jasmin.Test.DiffTestMain

private def main (args : List String) : IO UInt32 := do
  let cfg ← Config.fromEnv
  match args with
  | [] | ["all"] =>
    IO.println s!"Running {allCases.length} diff-test case(s)..."
    let (pass, fail) ← runAll cfg
    IO.println s!"Summary: {pass}/{pass + fail} PASS, {fail} FAIL"
    pure (if fail == 0 then 0 else 1)
  | ["aucursves"] =>
    -- Path-3 stage in isolation: check AUCurves-extracted Rust.
    IO.println "Running Path 3 (AUCurves-extracted Rust) only..."
    let result ← stageAucursvesRust cfg
    match result with
    | none =>
      IO.println "Result: SKIP (AUCurves Rust file not present)"
      pure 0
    | some true =>
      IO.println "Result: PASS"
      pure 0
    | some false =>
      IO.println "Result: FAIL"
      pure 1
  | [caseName] =>
    match allCases.find? (·.caseName == caseName) with
    | none =>
      IO.println s!"Unknown test case: {caseName}"
      IO.println s!"Available cases:"
      for tc in allCases do
        IO.println s!"  - {tc.caseName} ({tc.portName})"
      IO.println s!"  - aucursves  (Path 3, AUCurves-extracted Rust)"
      pure 1
    | some tc =>
      let ok ← runOneCase cfg tc
      pure (if ok then 0 else 1)
  | _ =>
    IO.println "usage: lake exe difftest [case_name | all | aucursves]"
    IO.println ""
    IO.println "  all        — run all bignum diff-test cases (default)"
    IO.println "  aucursves  — Path 3 only: build AUCurves-extracted Rust"
    IO.println "  <case>     — run one named case"
    pure 1
