/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# `ScalarLin`: the target-neutral scalar straight-line waist (Waist 1)

The `regArith` fragment of `Com jasminDialect`, in named-SSA straight-line form,
shared by *every* backend. Each ISA backend (AArch64, RISC-V, x86, the GPU tile
thread-body) provides a `ScalarTarget` instance — an instruction selection
`RegStmt → List Op`, a machine run, and a one-line per-statement correctness
proof — and gets the **whole-program denotation theorem for free** from the
single generic `ScalarTarget.compile_denote` here. So the theorem is proved
ONCE and factored over the four backends, rather than copy-pasted per ISA.

This is the narrow waist of the architecture: one `Com jasminDialect → RegProg`
flattening (the de-Bruijn front, proved once) feeds this IR; each target only
proves the trivial straight-line selection. Lowering `Com` directly per target
would instead redo the flattening proof four times.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ScalarLin

/-! ## 1. The scalar straight-line IR (the `regArith` fragment) -/

/-- A straight-line scalar statement over named SSA registers — the field-leaf
    fragment of `Com jasminDialect`. Each statement writes one destination from
    existing sources; `movz`/`movk` are the constant-materialisation primitives. -/
inductive RegStmt where
  | add (dst a b : String)
  | sub (dst a b : String)
  | mul (dst a b : String)
  | and (dst a b : String)
  | orr (dst a b : String)
  | eor (dst a b : String)
  | umulh (dst a b : String)
  | shrI (dst a : String) (imm : Nat)
  | shlI (dst a : String) (imm : Nat)
  | mov (dst a : String)
  | movz (dst : String) (imm16 : Nat)
  | movk (dst : String) (imm16 hw : Nat)
  /-- Backend-neutral 64-bit constant load. ARM lowers it to a `movz`/`movk`
      chain; RISC-V lowers it to `li` (`lui`+`addi`). The neutral semantics is the
      direct `set dst (ofNat 64 n)`, so the front stays ISA-agnostic. -/
  | loadImm (dst : String) (n : Nat)
  deriving Repr, DecidableEq

/-- A straight-line program. -/
abbrev RegProg := List RegStmt

/-! ## 2. The backend interface + the one generic denotation theorem

A `ScalarTarget` is everything a backend must supply to compile this IR with a
correctness proof: a machine op type `Op`, a state `St`, a machine run of a
compiled op-block (`runOps`) that is additive over concatenation, the source
semantics `step`, the instruction selection `toOps`, and the per-statement
selection-correctness `select_correct` (one `rfl`-class proof per backend). -/

/-- A scalar backend: instruction selection + machine semantics + a per-statement
    correctness witness. -/
structure ScalarTarget where
  /-- The backend's machine op type (e.g. `BOp`, `ROp64`). -/
  Op : Type
  /-- The backend's machine state (e.g. `BState`, `RState64`). -/
  St : Type
  /-- Run a compiled op-block on the machine (lower + run). -/
  runOps : St → List Op → St
  /-- Running the empty block is the identity. -/
  runOps_nil : ∀ (s : St), runOps s [] = s
  /-- `runOps` is additive over block concatenation. -/
  runOps_append : ∀ (xs ys : List Op) (s : St),
    runOps s (xs ++ ys) = runOps (runOps s xs) ys
  /-- The source effect of one statement on this backend's state. -/
  step : St → RegStmt → St
  /-- Instruction selection for one statement. -/
  toOps : RegStmt → List Op
  /-- Per-statement selection correctness: the selected ops realise the source
      effect (one near-`rfl` proof per backend). -/
  select_correct : ∀ (s : St) (stmt : RegStmt), runOps s (toOps stmt) = step s stmt

namespace ScalarTarget

/-- Compile a whole program to the backend's op-block. -/
def compile (T : ScalarTarget) (p : RegProg) : List T.Op := p.flatMap T.toOps

/-- The source denotation on the backend's state. -/
def denote (T : ScalarTarget) (p : RegProg) (s : T.St) : T.St := p.foldl T.step s

/-- **The generic denotation theorem.** For any backend, the compiled machine block computes
    the source program's denotation, by induction on the program — proved once,
    instantiated per ISA. -/
theorem compile_denote (T : ScalarTarget) (p : RegProg) (s : T.St) :
    T.runOps s (T.compile p) = T.denote p s := by
  induction p generalizing s with
  | nil => simp only [compile, List.flatMap_nil, T.runOps_nil, denote, List.foldl_nil]
  | cons x xs ih =>
      simp only [compile, List.flatMap_cons] at *
      rw [T.runOps_append, T.select_correct, denote, List.foldl_cons]
      exact ih (T.step s x)

end ScalarTarget

end CatCrypt.Crypto.SecureCompilation.ScalarLin
