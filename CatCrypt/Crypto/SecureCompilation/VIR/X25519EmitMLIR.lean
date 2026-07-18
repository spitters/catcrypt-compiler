/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint
import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom

/-!
# Direct-VIR emission of an X25519 ladder step

Authors the ladder step's VIR `Com` directly using `CatCryptOp.extCall`,
as a ground-truth reference for what the `CryptoSSA → VIR` translation
should produce. Post-2026-05-14 the translation works (see
`X25519Program.ladderStepX2_mlir`); this file remains as a hand-written
benchmark and a target to diff against.

The emitted MLIR is linked against externally-supplied `fp_add`/`fp_sub`/
`fp_mul`/`fp_sqr` funcs.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitMLIR

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptPrint
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-- Shorthand: a single Fp25519 limb-vector as MLIR `memref<5xi64>`. -/
abbrev Fp25519Ty : CryptoTy := .memref 5

/-- Build a VIR `Expr` for `func.call @fp_add`. -/
def fpAddExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fp_add" [Fp25519Ty, Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons a (.cons b .nil) }

def fpSubExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fp_sub" [Fp25519Ty, Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons a (.cons b .nil) }

def fpMulExpr {Γ : Ctxt catCryptDialect}
    (a b : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fp_mul" [Fp25519Ty, Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons a (.cons b .nil) }

def fpSqrExpr {Γ : Ctxt catCryptDialect}
    (a : Ctxt.Var Γ Fp25519Ty) : Expr catCryptDialect Γ Fp25519Ty :=
  { op := .extCall "fp_sqr" [Fp25519Ty] Fp25519Ty
    retTy_eq := rfl
    args := .cons a .nil }

/-! ## A half-ladder-step: computes x2' = AA * BB where
      AA = (x2 + z2)², BB = (x2 - z2)².
    Inputs: x2, z2 (two `Fp25519` memrefs).
    Output: x2' (one `Fp25519` memref). -/

/-- Context for the half-step function: two Fp25519 args.
    De Bruijn: `.here` = z2 (last-pushed), `.there .here` = x2. -/
abbrev StepCtx : Ctxt catCryptDialect := [Fp25519Ty, Fp25519Ty]

/-- The VIR program. Inputs %arg0=x2, %arg1=z2 (by our printer's
    convention: arg0 is oldest = .there .here, arg1 is newest = .here). -/
def halfStep : Com catCryptDialect StepCtx Fp25519Ty :=
  let x2_in : Ctxt.Var StepCtx Fp25519Ty := .there .here
  let z2_in : Ctxt.Var StepCtx Fp25519Ty := .here
  -- let A = x2 + z2  (x2 at .there .here, z2 at .here)
  .var (fpAddExpr x2_in z2_in)
    -- Γ' = Fp :: StepCtx; A at .here
    (.var (fpSubExpr (.there x2_in) (.there z2_in))
      -- Γ'' = Fp :: Fp :: StepCtx; B at .here, A at .there .here
      (.var (fpSqrExpr (.there .here))    -- AA = A²
        (.var (fpSqrExpr (.there .here))    -- BB = B²
          (.var (fpMulExpr (.there .here) .here)   -- x2' = AA * BB
            (.ret .here)))))

/-- External `func.func` declarations in MLIR for the oracle leaves. -/
def externs : List String :=
  [ "func.func private @fp_add(memref<5xi64>, memref<5xi64>) -> memref<5xi64>"
  , "func.func private @fp_sub(memref<5xi64>, memref<5xi64>) -> memref<5xi64>"
  , "func.func private @fp_mul(memref<5xi64>, memref<5xi64>) -> memref<5xi64>"
  , "func.func private @fp_sqr(memref<5xi64>) -> memref<5xi64>" ]

/-- Full textual MLIR module for the half-step. -/
def halfStepMLIR : String :=
  Com.printModuleWithExterns halfStep "x25519_halfstep" externs

#eval halfStepMLIR

/-! ## Full Montgomery ladder step (dbl + dadd)

Inputs: x1 (base point x-coord), x2, z2, x3, z3 (ladder state).
Outputs: x2', z2', x3', z3' (new state).

Formulas (Bernstein 2006, Curve25519):
  A  = x2 + z2         ; B  = x2 - z2
  C  = x3 + z3         ; D  = x3 - z3
  AA = A²              ; BB = B²
  E  = AA - BB
  DA = D * A           ; CB = C * B
  x3' = (DA + CB)²
  z3' = x1 * (DA - CB)²
  x2' = AA * BB
  z2' = E * (BB + 121666 * E)

Our VIR returns one struct-like result; we emit four separate
`func.func`s — one per output — sharing the same input signature.
Simpler than multi-return and maps cleanly onto MLIR. -/

/-- Context for full-step functions: 5 Fp25519 args in order
    [x1, x2, z2, x3, z3] where `.here` = x3, `.there .here` = x2, etc. -/
abbrev FullCtx : Ctxt catCryptDialect :=
  [Fp25519Ty, Fp25519Ty, Fp25519Ty, Fp25519Ty, Fp25519Ty]

/-- Build a full-step `Com` that produces x2' (= AA * BB).
    Index convention: `.here` = oldest (arg0) after `printModuleArgs`
    builds the Names list; see `Com.printModuleArgs`. -/

-- A small syntactic helper: lift a Var across a cons.
-- (there = weakening by one binding)
private def lift1 {d : Dialect} {Γ : Ctxt d} {t s : d.Ty}
    (v : Ctxt.Var Γ t) : Ctxt.Var (s :: Γ) t := .there v

/-! ## Four separate entry points for the four outputs

For a given (x1, x2, z2, x3, z3), the full ladder step produces
(x2', z2', x3', z3'). We emit four funcs that share the same signature
and each computes one output. The linker + MLIR optimizer can dedup
common subexpressions if inlined. -/

/-- x2' = AA * BB where AA = (x2+z2)², BB = (x2-z2)².
    FullCtx convention: .here = arg0 = x1, .there .here = arg1 = x2,
    .there² .here = arg2 = z2, .there³ .here = arg3 = x3,
    .there⁴ .here = arg4 = z3. -/
def fullStep_x2p : Com catCryptDialect FullCtx Fp25519Ty :=
  let x2 : Ctxt.Var FullCtx Fp25519Ty := .there .here
  let z2 : Ctxt.Var FullCtx Fp25519Ty := .there (.there .here)
  .var (fpAddExpr x2 z2)             -- %0: A
    (.var (fpSubExpr (lift1 x2) (lift1 z2))    -- %1: B
      (.var (fpSqrExpr (lift1 .here))   -- %2: AA (over %0)
        (.var (fpSqrExpr (lift1 .here))  -- %3: BB (over %1, shifted)
          -- Now: AA at .there .here, BB at .here
          (.var (fpMulExpr (.there .here) .here)   -- %4: x2' = AA*BB
            (.ret .here)))))

/-- z2' = E * (BB + a24·E) where E = AA - BB, a24 = 121666.
    (We use an `fp_mul_a24` helper for the constant multiply.) -/
def fullStep_z2p : Com catCryptDialect FullCtx Fp25519Ty :=
  let x2 : Ctxt.Var FullCtx Fp25519Ty := .there .here
  let z2 : Ctxt.Var FullCtx Fp25519Ty := .there (.there .here)
  .var (fpAddExpr x2 z2)              -- %0: A
    (.var (fpSubExpr (lift1 x2) (lift1 z2))    -- %1: B
      (.var (fpSqrExpr (lift1 .here))    -- %2: AA
        (.var (fpSqrExpr (lift1 .here))   -- %3: BB
          -- AA: .there .here; BB: .here
          (.var (fpSubExpr (.there .here) .here)   -- %4: E = AA - BB
            -- E: .here
            (.var ({ op := .extCall "fp_mul_a24" [Fp25519Ty] Fp25519Ty
                     retTy_eq := rfl, args := .cons .here .nil })   -- %5: a24 * E
              -- a24·E: .here; E: .there .here; BB: .there (.there .here)
              (.var (fpAddExpr (.there (.there .here)) .here)   -- %6: BB + a24·E
                (.var (fpMulExpr (.there (.there .here)) .here)   -- %7: E * (BB + a24·E)
                  (.ret .here))))))))

/-- x3' = (DA + CB)² where DA = D·A, CB = C·B. -/
def fullStep_x3p : Com catCryptDialect FullCtx Fp25519Ty :=
  let x2 : Ctxt.Var FullCtx Fp25519Ty := .there .here
  let z2 : Ctxt.Var FullCtx Fp25519Ty := .there (.there .here)
  let x3 : Ctxt.Var FullCtx Fp25519Ty := .there (.there (.there .here))
  let z3 : Ctxt.Var FullCtx Fp25519Ty := .there (.there (.there (.there .here)))
  .var (fpAddExpr x2 z2)          -- %0: A
    (.var (fpSubExpr (lift1 x2) (lift1 z2))    -- %1: B
      (.var (fpAddExpr (lift1 (lift1 x3)) (lift1 (lift1 z3)))   -- %2: C
        (.var (fpSubExpr (lift1 (lift1 (lift1 x3))) (lift1 (lift1 (lift1 z3))))  -- %3: D
          -- A: .there (.there (.there .here)); B: .there (.there .here); C: .there .here; D: .here
          (.var (fpMulExpr .here (.there (.there (.there .here))))  -- %4: DA = D*A
            -- DA: .here
            (.var (fpMulExpr (.there (.there .here)) (.there (.there (.there .here))))   -- %5: CB = C*B
              -- DA: .there .here; CB: .here
              (.var (fpAddExpr (.there .here) .here)   -- %6: DA+CB
                (.var (fpSqrExpr .here)                -- %7: (DA+CB)²
                  (.ret .here))))))))

/-- z3' = x1 · (DA - CB)². -/
def fullStep_z3p : Com catCryptDialect FullCtx Fp25519Ty :=
  let x1 : Ctxt.Var FullCtx Fp25519Ty := .here
  let x2 : Ctxt.Var FullCtx Fp25519Ty := .there .here
  let z2 : Ctxt.Var FullCtx Fp25519Ty := .there (.there .here)
  let x3 : Ctxt.Var FullCtx Fp25519Ty := .there (.there (.there .here))
  let z3 : Ctxt.Var FullCtx Fp25519Ty := .there (.there (.there (.there .here)))
  .var (fpAddExpr x2 z2)              -- %0: A
    (.var (fpSubExpr (lift1 x2) (lift1 z2))    -- %1: B
      (.var (fpAddExpr (lift1 (lift1 x3)) (lift1 (lift1 z3)))  -- %2: C
        (.var (fpSubExpr (lift1 (lift1 (lift1 x3))) (lift1 (lift1 (lift1 z3))))  -- %3: D
          (.var (fpMulExpr .here (.there (.there (.there .here))))  -- %4: DA = D*A
            (.var (fpMulExpr (.there (.there .here)) (.there (.there (.there .here))))  -- %5: CB = C*B
              (.var (fpSubExpr (.there .here) .here)  -- %6: DA - CB
                (.var (fpSqrExpr .here)              -- %7: (DA-CB)²
                  (.var (fpMulExpr (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                                    .here)   -- %8: x1 * (DA-CB)²
                    (.ret .here)))))))))

/-- External decl for the `a24` multiplier. -/
def externsFull : List String :=
  externs ++
  [ "func.func private @fp_mul_a24(memref<5xi64>) -> memref<5xi64>" ]

/-- Emit all four outputs as separate funcs in one module. -/
def fullStepMLIR : String :=
  let allExterns := externsFull
  let nl := "\n"
  let body :=
    Com.printModuleArgs fullStep_x2p "x25519_step_x2" ++ nl ++
    Com.printModuleArgs fullStep_z2p "x25519_step_z2" ++ nl ++
    Com.printModuleArgs fullStep_x3p "x25519_step_x3" ++ nl ++
    Com.printModuleArgs fullStep_z3p "x25519_step_z3"
  String.intercalate nl allExterns ++ nl ++ nl ++ body

/-! ## Multi-return fullstep (D2.4): a single program emitting all four
outputs `(x2', z2', x3', z3')` from one shared computation of A, B, C, D,
AA, BB, DA, CB. Eliminates the writeup §5.5 CSE-trap that the four
single-return funcs above hit. -/

/-- Helper: lift a Var across `k` cons-extensions on the left. -/
private def liftN {d : Dialect} {Γ : Ctxt d} {t : d.Ty} :
    (k : Nat) → (Δ : List d.Ty) → Δ.length = k → Ctxt.Var Γ t →
    Ctxt.Var (Δ ++ Γ) t
  | 0, [], _, v => v
  | k+1, s :: rest, h, v =>
    .there (liftN k rest (by simp at h; exact h) v)

/-- Multi-return X25519 ladder full-step. Returns
`[x2', z2', x3', z3']` from inputs `(x1, x2, z2, x3, z3)`.

Convention: `.here` = x1 (matches the four single-return funcs above).
-/
def fullStep_multi :
    MultiReturnCom catCryptDialect FullCtx
      [Fp25519Ty, Fp25519Ty, Fp25519Ty, Fp25519Ty] :=
  -- Inputs in the original FullCtx (depths 0..4):
  -- x1 = .here, x2 = .there.here, z2 = .there².here,
  -- x3 = .there³.here, z3 = .there⁴.here
  -- Step 1: A = x2 + z2  [Γ size grows by 1; A goes to .here, all original
  -- depths increase by 1]
  .var (fpAddExpr (.there .here) (.there (.there .here)))     -- %0: A
  -- Now depths: A=0, x1=1, x2=2, z2=3, x3=4, z3=5
  -- Step 2: B = x2 - z2
  (.var (fpSubExpr (.there (.there .here))                    -- x2 at depth 2
                   (.there (.there (.there .here))))          -- z2 at depth 3
  -- Step 3: C = x3 + z3
  (.var (fpAddExpr (.there (.there (.there (.there (.there .here)))))  -- x3 at depth 5
                   (.there (.there (.there (.there (.there (.there .here)))))))  -- z3 at depth 6
  -- Step 4: D = x3 - z3
  (.var (fpSubExpr (.there (.there (.there (.there (.there (.there .here))))))    -- x3 at depth 6
                   (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- z3 at depth 7
  -- After 4 binds: D=0, C=1, B=2, A=3, x1=4, x2=5, z2=6, x3=7, z3=8
  -- Step 5: AA = A²  (A at depth 3 ⇒ after this bind at depth 4)
  (.var (fpSqrExpr (.there (.there (.there .here))))          -- A at depth 3
  -- After: AA=0, D=1, C=2, B=3, A=4, x1=5, x2=6, z2=7, x3=8, z3=9
  -- Step 6: BB = B² (B at depth 3 ⇒ after this bind at depth 4)
  (.var (fpSqrExpr (.there (.there (.there .here))))          -- B at depth 3
  -- After: BB=0, AA=1, D=2, C=3, B=4, A=5, x1=6, ...
  -- Step 7: DA = D * A
  (.var (fpMulExpr (.there (.there .here))                    -- D at depth 2
                   (.there (.there (.there (.there (.there .here))))))  -- A at depth 5
  -- After: DA=0, BB=1, AA=2, D=3, C=4, B=5, A=6, x1=7, ...
  -- Step 8: CB = C * B
  (.var (fpMulExpr (.there (.there (.there (.there .here))))  -- C at depth 4
                   (.there (.there (.there (.there (.there .here))))))  -- B at depth 5
  -- After: CB=0, DA=1, BB=2, AA=3, D=4, C=5, B=6, A=7, x1=8, x2=9, z2=10, x3=11, z3=12
  -- Step 9: E = AA - BB
  (.var (fpSubExpr (.there (.there (.there .here)))           -- AA at depth 3
                   (.there (.there .here)))                   -- BB at depth 2
  -- After: E=0, CB=1, DA=2, BB=3, AA=4, D=5, ..., x1=9
  -- Step 10: a24E = a24·E  (uses fp_mul_a24 extern)
  (.var ({ op := .extCall "fp_mul_a24" [Fp25519Ty] Fp25519Ty
           retTy_eq := rfl, args := .cons .here .nil })       -- E at depth 0
  -- After: a24E=0, E=1, CB=2, DA=3, BB=4, AA=5, D=6, ..., x1=10
  -- Step 11: bb_plus = BB + a24E
  (.var (fpAddExpr (.there (.there (.there (.there .here))))  -- BB at depth 4
                   .here)                                     -- a24E at depth 0
  -- After: bb_plus=0, a24E=1, E=2, CB=3, DA=4, BB=5, AA=6, ..., x1=11
  -- Step 12: z2' = E * bb_plus
  (.var (fpMulExpr (.there (.there .here))                    -- E at depth 2
                   .here)                                     -- bb_plus at depth 0
  -- After: z2'=0, bb_plus=1, a24E=2, E=3, CB=4, DA=5, BB=6, AA=7, D=8, C=9, B=10, A=11, x1=12, x2=13, z2=14, x3=15, z3=16
  -- Step 13: x2' = AA * BB
  (.var (fpMulExpr (.there (.there (.there (.there (.there (.there (.there .here)))))))  -- AA at depth 7
                   (.there (.there (.there (.there (.there (.there .here)))))))  -- BB at depth 6
  -- After: x2'=0, z2'=1, bb_plus=2, a24E=3, E=4, CB=5, DA=6, BB=7, AA=8, ..., x1=13
  -- Step 14: dpc = DA + CB
  (.var (fpAddExpr (.there (.there (.there (.there (.there (.there .here))))))  -- DA at depth 6
                   (.there (.there (.there (.there (.there .here))))))  -- CB at depth 5
  -- After: dpc=0, x2'=1, z2'=2, bb_plus=3, a24E=4, E=5, CB=6, DA=7, BB=8, AA=9, ..., x1=14
  -- Step 15: x3' = sqr(dpc)
  (.var (fpSqrExpr .here)                                     -- dpc at depth 0
  -- After: x3'=0, dpc=1, x2'=2, z2'=3, bb_plus=4, a24E=5, E=6, CB=7, DA=8, BB=9, AA=10, ..., x1=15
  -- Step 16: dmc = DA - CB
  (.var (fpSubExpr (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- DA at depth 8
                   (.there (.there (.there (.there (.there (.there (.there .here))))))))  -- CB at depth 7
  -- After: dmc=0, x3'=1, dpc=2, x2'=3, z2'=4, bb_plus=5, a24E=6, E=7, CB=8, DA=9, BB=10, AA=11, ..., x1=16
  -- Step 17: sq = sqr(dmc)
  (.var (fpSqrExpr .here)                                     -- dmc at depth 0
  -- After: sq=0, dmc=1, x3'=2, dpc=3, x2'=4, z2'=5, bb_plus=6, a24E=7, E=8, CB=9, DA=10, BB=11, AA=12, D=13, C=14, B=15, A=16, x1=17
  -- Step 18: z3' = x1 * sq
  (.var (fpMulExpr (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))  -- x1 at depth 17
                   .here)                                     -- sq at depth 0
  -- After: z3'=0, sq=1, dmc=2, x3'=3, dpc=4, x2'=5, z2'=6, ...
  -- Return [x2', z2', x3', z3']: depths 5, 6, 3, 0
  (.ret (.cons (.there (.there (.there (.there (.there .here)))))  -- x2' at depth 5
         (.cons (.there (.there (.there (.there (.there (.there .here))))))  -- z2' at depth 6
         (.cons (.there (.there (.there .here)))               -- x3' at depth 3
         (.cons .here .nil))))                                 -- z3' at depth 0
  ))))))))))))))))))

/-- Multi-return MLIR for the X25519 fullstep. Single `func.func` with
4-tuple return. Eliminates the §5.5 CSE-trap by exposing all shared
work (A, B, C, D, AA, BB, DA, CB) to the MLIR optimizer. -/
def fullStepMLIRMulti : String :=
  let nl := "\n"
  let externBlock := String.intercalate nl externsFull
  externBlock ++ nl ++ nl ++
    MultiReturnCom.printModuleArgs fullStep_multi "x25519_fullstep_multi"

/-- Write the multi-return MLIR module. -/
def writeFullStepMLIRMulti (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path fullStepMLIRMulti

/-- Write `fullStepMLIR` to a file (called from a build action). -/
def writeFullStepMLIR (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path fullStepMLIR

/-- Also write the halfStep separately (keeps the existing bench Makefile
    happy). -/
def writeHalfStepMLIR (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path halfStepMLIR

-- Emit all three when this file is evaluated.  Path resolution is via the
-- `CATCRYPT_BENCH_DIR` env var (default: skip).  The previous hard-coded
-- absolute paths were author-specific and broke CI on other machines.
private def benchDir : IO (Option System.FilePath) := do
  let some d ← IO.getEnv "CATCRYPT_BENCH_DIR" | return none
  return some d

#eval do
  let some d ← benchDir | return ()
  writeHalfStepMLIR (d / "x25519_halfstep.mlir")
  writeFullStepMLIR (d / "x25519_fullstep.mlir")
  writeFullStepMLIRMulti (d / "x25519_fullstep_multi.mlir")

end CatCrypt.Crypto.SecureCompilation.VIR.X25519EmitMLIR
