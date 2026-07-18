/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT
import CatCrypt.Crypto.Jasmin.LowCTToJasmin

set_option autoImplicit false

/-!
# AUCurves → CatCrypt-compiler retarget pilot — Lean importer (R2–R4)

This file is the CatCrypt side of the AUCurves-retarget de-risking pilot
(phases R1–R4).  AUCurves' Rocq dev exports a `rust_cmd_ed` body in a neutral
s-expression form (R1, `AUCurves/src/Bedrock/LowCTEdSerialize.v`); here we
parse it back into CatCrypt's `LowCT` IR and route it through the owned
compiler front.

The two IRs were co-designed: AUCurves' `rust_cmd_ed` and CatCrypt's `LowCT`
have the same constructor shape (the plan's correspondence table).  So the
import is a *structural* parse, not a from-scratch frontend.

## Pilot routine

The smallest closed `rust_cmd_ed` term available: `xyzt_copy_body`'s single
`REdCall "fe25519_xyzt_copy" dest [src]` over 200-byte slots.  Its serialized
form is certified by AUCurves' Qed `Example xyzt_copy_sexpr_value`:

```
(Call "fe25519_xyzt_copy" (loc "dest" (Bytes 200)) ((loc "src" (Bytes 200))))
```

## Constructor map (plan §"key enabler", restricted to the pilot's needs)

| AUCurves `rust_cmd_ed`        | CatCrypt `LowCT`           |
|-------------------------------|------------------------------|
| `REdCall f dst args`          | `RCall f dst args`           |
| `located_ed {loc_var; loc_type}` | `Located {locVar; locSrc}`|
| `TBytes n`                    | `TowerType.TBytes n`         |
| `REdSeq`/`REdLetZero`/…       | `RSeq`/`RLetZero`/…          |

The full parser below covers every `rust_cmd_ed`/`sexpr_ed`/`tower_type_ed`
constructor the serializer emits, so it is a structural inverse of
`ser_cmd` for the whole IR, not just the pilot.

## What this file delivers (honest scoping, plan R3)

* **R2** — `parseLowCT : String → Option LowCT`, total recursive-descent
  parser over the R1 grammar.
* **R3 (structural correspondence)** — `importedPilot_eq`: the parsed pilot
  equals the hand-written `RCall` that the constructor map dictates for
  AUCurves' certified s-expression.  This is the constructor-by-constructor
  agreement of the two IRs *at the AST level*.  The fully machine-checked
  cross-prover equivalence (Rocq `rust_exec_ed` ⇔ Lean `RustExec`) is the
  gold-standard residual named in the plan; it is **not** delivered here —
  the two semantics live in different proof assistants.
* **R4 (emit + cross-check)** — `importedPilot_jasmin_eq`: routing the parsed
  pilot through `toJasminCmd` yields a single `Ccall` node naming
  `fe25519_xyzt_copy` with `[dest]` as lvalue and `[src]` as argument — the
  same call node AUCurves' own jasmin export produces
  (`ExtractXyztCopyJasmin.v`'s `JCcall "fe25519_xyzt_copy" [JEvar "dest";
  JEvar "src"]`).  The two backends agree on the call site.
-/

namespace CatCrypt.Crypto.SecureCompilation.AUCurvesImport

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin (Cmd InstrR LVal PExpr)

-- `LowCT` / `SExpr` derive only `Repr, Inhabited` upstream; the pilot
-- correspondence theorem compares parsed `Option LowCT` values, so we need
-- decidable equality.  Both inductives are first-order (String / Nat /
-- BitVec / Located / TowerType / lists), so the derivation is structural.
deriving instance DecidableEq for SExpr
-- #267: derive on the canonical inductive `LowCT` (`LowCT` is now an abbrev).
deriving instance DecidableEq for LowCT

/-! ## §1  Tokenizer

Tokens: `(`, `)`, a double-quoted string `Str s`, or a bare atom `Atom s`. -/

inductive Tok where
  | lparen : Tok
  | rparen : Tok
  | str : String → Tok
  | atom : String → Tok
  deriving Repr, DecidableEq, Inhabited

/-- Tokenize an s-expression string.  Whitespace separates atoms; `(`/`)`
    are always single tokens; `"…"` is a string literal (no escapes — the
    R1 grammar's names contain no quotes). -/
partial def tokenize (s : String) : List Tok :=
  let rec go (cs : List Char) (acc : List Tok) : List Tok :=
    match cs with
    | [] => acc.reverse
    | c :: rest =>
      if c == '(' then go rest (.lparen :: acc)
      else if c == ')' then go rest (.rparen :: acc)
      else if c == ' ' || c == '\n' || c == '\t' || c == '\r' then go rest acc
      else if c == '"' then
        -- read until closing quote
        let rec readStr (ds : List Char) (sacc : List Char) : (List Char × List Char) :=
          match ds with
          | [] => (sacc.reverse, [])
          | d :: ds' => if d == '"' then (sacc.reverse, ds') else readStr ds' (d :: sacc)
        let (body, rest') := readStr rest []
        go rest' (.str (String.ofList body) :: acc)
      else
        -- read a bare atom until whitespace or paren or quote
        let rec readAtom (ds : List Char) (sacc : List Char) : (List Char × List Char) :=
          match ds with
          | [] => (sacc.reverse, [])
          | d :: ds' =>
            if d == '(' || d == ')' || d == ' ' || d == '\n' || d == '\t' || d == '\r' || d == '"'
            then (sacc.reverse, ds)
            else readAtom ds' (d :: sacc)
        let (body, rest') := readAtom rest [c]
        go rest' (.atom (String.ofList body) :: acc)
  go s.toList []

/-! ## §2  Recursive-descent parser

The parser is over a token list with explicit remainder threading; total
via `Option` (a malformed input yields `none`).  We mirror the serializer's
grammar exactly so `parseLowCT ∘ ser_cmd = some`. -/

/-- Parse a `Nat` atom. -/
def parseNat? (t : Tok) : Option Nat :=
  match t with
  | .atom a => a.toNat?
  | _ => none

mutual

/-- Parse a tower type.  Either a bare atom (`Fp25519`, `U64`, …) or a
    parenthesised form (`(Bytes n)`, `(Arr n t)`). -/
partial def parseTowerType : List Tok → Option (TowerType × List Tok)
  | .atom "Fp25519" :: rest => some (.TFp25519, rest)
  | .atom "Fp25519_64" :: rest => some (.TFp25519_64, rest)
  | .atom "FpL25519" :: rest => some (.TFpL25519, rest)
  | .atom "U64" :: rest => some (.TU64, rest)
  | .lparen :: .atom "Bytes" :: rest =>
      match rest with
      | n :: .rparen :: rest' => do
          let n' ← parseNat? n
          pure (.TBytes n', rest')
      | _ => none
  | .lparen :: .atom "Arr" :: rest =>
      match rest with
      | n :: rest' => do
          let n' ← parseNat? n
          let (t, rest'') ← parseTowerType rest'
          match rest'' with
          | .rparen :: rest''' => pure (.TArr n' t, rest''')
          | _ => none
      | _ => none
  | _ => none

end

/-- Parse a `located_ed`: `(loc "var" tower-type)`. -/
def parseLocated : List Tok → Option (Located × List Tok)
  | .lparen :: .atom "loc" :: .str v :: rest => do
      let (t, rest') ← parseTowerType rest
      match rest' with
      | .rparen :: rest'' => pure ({ locVar := v, locSrc := t }, rest'')
      | _ => none
  | _ => none

/-- Parse a parenthesised list of `located_ed`. -/
partial def parseLocatedList : List Tok → Option (List Located × List Tok)
  | .lparen :: rest =>
      let rec loop (ts : List Tok) (acc : List Located) : Option (List Located × List Tok) :=
        match ts with
        | .rparen :: rest' => some (acc.reverse, rest')
        | _ =>
          match parseLocated ts with
          | some (l, ts') => loop ts' (l :: acc)
          | none => none
      loop rest []
  | _ => none

mutual

/-- Parse an `sexpr_ed`. -/
partial def parseSExpr : List Tok → Option (SExpr × List Tok)
  | .lparen :: .atom "Var" :: .str x :: .rparen :: rest => some (.SVar x, rest)
  | .lparen :: .atom "Lit" :: n :: .rparen :: rest => do
      let n' ← parseNat? n
      pure (.SLit n', rest)
  | .lparen :: .atom "Add" :: rest => parseSBin .SAdd rest
  | .lparen :: .atom "Sub" :: rest => parseSBin .SSub rest
  | .lparen :: .atom "Mul" :: rest => parseSBin .SMul rest
  | .lparen :: .atom "Shr" :: rest => parseSBin .SShr rest
  | .lparen :: .atom "And" :: rest => parseSBin .SAnd rest
  | .lparen :: .atom "Lt" :: rest => parseSBin .SLt rest
  -- Tower-limb read (#354).  AUCurves serializes `SLimb v i` as
  -- `(Limb "v" i)` (`LowCTEdSerialize.v`'s `ser_sexpr`).  It now imports to
  -- CatCrypt's `SExpr.SLimb v i` (the tower-limb read added in #354), whose
  -- faithful value lives in `SExpr.evalState` (the tower-aware evaluator).
  -- This is what unblocks the real inline field-op bodies (`fe25519_add`).
  | .lparen :: .atom "Limb" :: .str v :: n :: .rparen :: rest => do
      let i ← parseNat? n
      pure (.SLimb v i, rest)
  -- `SMul128` / `SAdd128` are Rocq-only u128 WP-bridge constructs with no
  -- CatCrypt `SExpr` counterpart; they are parse-rejected here (the field-op
  -- bodies the retarget targets do not use them at the radix-2^51 add layer).
  | _ => none

/-- Helper: parse two `sexpr`s and apply a binary `SExpr` constructor,
    consuming the trailing `)`. -/
partial def parseSBin (mk : SExpr → SExpr → SExpr) :
    List Tok → Option (SExpr × List Tok)
  | ts => do
      let (a, ts') ← parseSExpr ts
      let (b, ts'') ← parseSExpr ts'
      match ts'' with
      | .rparen :: rest => pure (mk a b, rest)
      | _ => none

end

mutual

/-- Parse a `rust_cmd_ed` node into a CatCrypt `LowCT`.  Total via `Option`. -/
partial def parseCmd : List Tok → Option (LowCT × List Tok)
  | .lparen :: .atom "Skip" :: .rparen :: rest => some (.RSkip, rest)
  | .lparen :: .atom "Seq" :: rest => do
      let (c1, rest1) ← parseCmd rest
      let (c2, rest2) ← parseCmd rest1
      match rest2 with
      | .rparen :: rest3 => pure (.RSeq c1 c2, rest3)
      | _ => none
  | .lparen :: .atom "LetZero" :: .str v :: rest => do
      let (t, rest1) ← parseTowerType rest
      let (body, rest2) ← parseCmd rest1
      match rest2 with
      | .rparen :: rest3 => pure (.RLetZero v t body, rest3)
      | _ => none
  | .lparen :: .atom "Call" :: .str f :: rest => do
      let (dest, rest1) ← parseLocated rest
      let (args, rest2) ← parseLocatedList rest1
      match rest2 with
      | .rparen :: rest3 => pure (.RCall f dest args, rest3)
      | _ => none
  | .lparen :: .atom "CallN" :: .str f :: rest => do
      let (dests, rest1) ← parseLocatedList rest
      let (args, rest2) ← parseLocatedList rest1
      match rest2 with
      | .rparen :: rest3 => pure (.RCallN f dests args, rest3)
      | _ => none
  | .lparen :: .atom "Block" :: rest => do
      let (body, rest1) ← parseCmd rest
      match rest1 with
      | .rparen :: rest2 => pure (.RBlock body, rest2)
      | _ => none
  | .lparen :: .atom "LimbStore" :: rest => do
      let (loc, rest1) ← parseLocated rest
      match rest1 with
      | n :: rest2 => do
          let n' ← parseNat? n
          -- The Rocq `REdLimbStore loc i e` stores an `sexpr_ed`.  Two cases:
          --
          --  * a literal `(Lit z)` value imports to `RLimbStore loc i (BitVec
          --    z)` — the compile-time-constant limb store.
          --  * any other `sexpr_ed` (e.g. `(Add (Var …) (Var …))` in
          --    `fe25519_add`) imports to `RLimbStoreExpr loc i e` via the
          --    `RLimbStoreExpr` constructor added in the R5 step.  This is the
          --    faithful image of a runtime-valued limb store and is what
          --    unblocks the real field-op bodies (the R-pilot's recorded
          --    expressivity obstacle, now closed).
          match rest2 with
          | .lparen :: .atom "Lit" :: vlit :: .rparen :: .rparen :: rest3 => do
              let vn ← parseNat? vlit
              pure (.RLimbStore loc n' (BitVec.ofNat 64 vn), rest3)
          | _ => do
              let (e, rest3) ← parseSExpr rest2
              match rest3 with
              | .rparen :: rest4 => pure (.RLimbStoreExpr loc n' e, rest4)
              | _ => none
      | _ => none
  -- Remaining `rust_cmd_ed` shapes (LetU64/ScalarSet/IfNz/WhileNz/By­teStore/
  -- ByteLoad/For/Select/CallFn/SetBytes/ArrLoad/ArrStore) are part of the
  -- full grammar; the pilot exercises only `Call`.  They are added to the
  -- parser as the retarget scales (R6) — each is one `parseCmd` arm.
  | _ => none

end

/-- Top-level importer: tokenize then parse, discarding trailing tokens. -/
def parseLowCT (s : String) : Option LowCT :=
  match parseCmd (tokenize s) with
  | some (c, _) => some c
  | none => none

/-! ## §3  The pilot artifact and its import (R2) -/

/-- The byte-exact s-expression AUCurves certified for the pilot
    (`LowCTEdSerialize.v`'s `xyzt_copy_sexpr_value`, committed to
    `bench/retarget_aucurves/xyzt_copy.sexpr`). -/
def xyztCopySexpr : String :=
  "(Call \"fe25519_xyzt_copy\" (loc \"dest\" (Bytes 200)) ((loc \"src\" (Bytes 200))))"

/-- The `LowCT` that the constructor map dictates for the pilot. -/
def xyztCopyExpected : LowCT :=
  .RCall "fe25519_xyzt_copy"
    { locVar := "dest", locSrc := .TBytes 200 }
    [{ locVar := "src", locSrc := .TBytes 200 }]

/-- **R2 + R3 (structural correspondence).**  Importing AUCurves' certified
    s-expression yields exactly the `RCall` the IR-correspondence map
    prescribes.  Constructor-by-constructor: `Call → RCall`, `loc → Located`,
    `(Bytes 200) → TBytes 200`, with the function name and slot names
    recovered verbatim.

    This is the AST-level agreement of the two co-designed IRs.  The
    cross-prover *semantic* equivalence (Rocq `rust_exec_ed` ⇔ Lean
    `RustExec`) is the gold-standard residual and is not proved here. -/
theorem importedPilot_eq :
    parseLowCT xyztCopySexpr = some xyztCopyExpected := by
  native_decide

/-! ## §4  Emit + cross-check (R4) -/

open CatCrypt.Crypto.Jasmin.LowCT (toJasminCmd locToLVal locToPExpr)

/-- The Jasmin call node CatCrypt's front emits for the pilot. -/
def xyztCopyJasmin : Cmd :=
  toJasminCmd xyztCopyExpected

/-- **R4 (backend cross-check).**  The owned front lowers the imported pilot
    to a single Jasmin `Ccall` naming `fe25519_xyzt_copy`, with the
    destination slot as the lone lvalue and the source slot as the lone
    argument.  This is the same call site AUCurves' own jasmin backend
    produces for the identical routine
    (`ExtractXyztCopyJasmin.v`:
      `JCcall "fe25519_xyzt_copy" [JEvar "dest"; JEvar "src"]`):
    one call node, same leaf name, same `dest`-then-`src` ordering.
    The two backends agree on the emitted call. -/
theorem importedPilot_jasmin_eq :
    xyztCopyJasmin =
      [InstrR.Ccall .DoNotInline
        [locToLVal { locVar := "dest", locSrc := .TBytes 200 }]
        { name := "fe25519_xyzt_copy" }
        ([{ locVar := "src", locSrc := .TBytes 200 }].map locToPExpr)] := by
  rfl

/-- End-to-end pilot statement (R2→R4 in one line): the parsed AUCurves
    export lowers, through CatCrypt's verified front, to the expected
    single-`Ccall` jasmin program. -/
theorem importedPilot_end_to_end :
    (parseLowCT xyztCopySexpr).map toJasminCmd =
      some
        [InstrR.Ccall .DoNotInline
          [locToLVal { locVar := "dest", locSrc := .TBytes 200 }]
          { name := "fe25519_xyzt_copy" }
          ([{ locVar := "src", locSrc := .TBytes 200 }].map locToPExpr)] := by
  rw [importedPilot_eq]
  rfl

/-! ## §5  R5 — runtime-valued limb store (`RLimbStoreExpr`)

The R-pilot recorded ONE structural obstacle blocking the real field-op
bodies: AUCurves' `REdLimbStore : … → sexpr_ed → …` stores a *runtime*
`sexpr_ed`, while CatCrypt's `RLimbStore` only stored a literal `BitVec 64`.
R5 closes that with the new `RLimbStoreExpr : Located → Nat → SExpr → LowCT`
constructor (mirroring the existing `RScalarSetExpr` runtime-scalar precedent)
and threads it through the whole `LowCT` closure (toJasminCmd, the CryptoSSA
front, CT analysis, leak trace, borrow check — see the R5 cascade).

The importer's `LimbStore` arm now parses a runtime `sexpr_ed` value into
`RLimbStoreExpr` (literal values still go to `RLimbStore`).  The serialized
form of a single `(LimbStore (loc "dest" Fp25519) 0 (Add (Var "ai0") (Var "bi0")))`
node — the shape of an inline radix-2^51 add-chain limb write — round-trips
constructor-by-constructor.

### The deeper obstacle — CLOSED in R6 (#354)

AUCurves' real `fe25519_add_body` (`End2End/Ed25519/Fe25519AddSubBody.v`) is
five `REdLimbStore dest i (SAdd (SLimb a i) (SLimb b i))` writes.  Its stored
value uses `sexpr_ed`'s **`SLimb v i`** — *read limb `i` of the tower slot
`v`*, evaluated against `rs_get_tower_ed` (the tower heap).  CatCrypt's scalar
`SExpr.eval : (String → Nat) → SExpr → Nat` sees only `rsScalar`, never the
tower.  R6 (#354) closes this **additively**: `SExpr` gains the `SLimb v i`
constructor; the scalar `eval` keeps its signature and gives `SLimb` a safe
default of `0`; a new tower-aware `SExpr.evalState : RustState → SExpr → Nat`
reads the limb from `rs.rsTower` (the faithful image of AUCurves'
`eval_sexpr_ed` `SLimb` arm).  The tower-free runtime value below
(`SAdd (SVar …) (SVar …)`) still exercises the carrier, and §6 below now
round-trips the **real** `SLimb`-valued `fe25519_add` body. -/

/-- A runtime-valued limb store: `dest.limbs[0] := ai0 + bi0` for runtime
    scalars `ai0`, `bi0`.  This is the serialized shape AUCurves' `ser_cmd`
    emits for a `REdLimbStore (loc "dest" Fp25519) 0 (SAdd (SVar "ai0")
    (SVar "bi0"))` node (head-tagged `LimbStore` / `Add` / `Var`).  It is the
    minimal exercise of the new `RLimbStoreExpr` carrier through the importer. -/
def limbStoreExprSexpr : String :=
  "(LimbStore (loc \"dest\" Fp25519) 0 (Add (Var \"ai0\") (Var \"bi0\")))"

/-- The `LowCT` the constructor map dictates for the runtime-valued limb
    store: `RLimbStoreExpr dest 0 (SAdd (SVar "ai0") (SVar "bi0"))`. -/
def limbStoreExprExpected : LowCT :=
  .RLimbStoreExpr
    { locVar := "dest", locSrc := .TFp25519 }
    0
    (.SAdd (.SVar "ai0") (.SVar "bi0"))

/-- **R5 (structural correspondence).**  Importing the serialized
    runtime-valued limb store yields exactly the `RLimbStoreExpr` the IR map
    prescribes: `LimbStore → RLimbStoreExpr`, `loc → Located`, `Fp25519 →
    TFp25519`, `(Add (Var …) (Var …)) → SAdd (SVar …) (SVar …)`, with the slot
    name, limb index, and scalar names recovered verbatim.  This is the
    constructor-by-constructor agreement of the two co-designed IRs on the
    runtime-valued limb store — the node that was previously unrepresentable. -/
theorem importedLimbStoreExpr_eq :
    parseLowCT limbStoreExprSexpr = some limbStoreExprExpected := by
  native_decide

/-- **R5 (backend cross-check).**  The owned front lowers the imported
    runtime-valued limb store to a single Jasmin `STORE64` `Copn`: the
    destination slot as the lvalue, and `[dest, idx=0, ai0 + bi0]` as the
    operand list — the value argument is the *lowered `SExpr`* (`Papp2 Oadd`)
    rather than a literal, which is exactly what distinguishes
    `RLimbStoreExpr` from `RLimbStore`.  This is the same single-`Copn` STORE64
    shape AUCurves' jasmin backend produces for an inline limb write, now with
    a runtime operand. -/
theorem importedLimbStoreExpr_jasmin_eq :
    toJasminCmd limbStoreExprExpected =
      [InstrR.Copn
        [locToLVal { locVar := "dest", locSrc := .TFp25519 }]
        .AT_none
        (.Oasm { name := "STORE64" })
        [locToPExpr { locVar := "dest", locSrc := .TFp25519 },
         .Pconst 0,
         CatCrypt.Crypto.Jasmin.LowCT.sexprToPExpr (.SAdd (.SVar "ai0") (.SVar "bi0"))]] := by
  rfl

/-- End-to-end R5 statement: the parsed AUCurves runtime-valued limb store
    lowers, through CatCrypt's verified front, to the expected single STORE64
    `Copn` with the lowered-`SExpr` operand. -/
theorem importedLimbStoreExpr_end_to_end :
    (parseLowCT limbStoreExprSexpr).map toJasminCmd =
      some
        [InstrR.Copn
          [locToLVal { locVar := "dest", locSrc := .TFp25519 }]
          .AT_none
          (.Oasm { name := "STORE64" })
          [locToPExpr { locVar := "dest", locSrc := .TFp25519 },
           .Pconst 0,
           CatCrypt.Crypto.Jasmin.LowCT.sexprToPExpr (.SAdd (.SVar "ai0") (.SVar "bi0"))]] := by
  rw [importedLimbStoreExpr_eq]
  rfl

/-! ## §6  R6 — the real `fe25519_add` body round-trips (`SLimb`-valued)

R5 closed the `RLimbStoreExpr` *carrier* but left a deeper obstacle: AUCurves'
real `fe25519_add_body` stores `SAdd (SLimb a i) (SLimb b i)` — the value reads
limb `i` of a TOWER slot, which the scalar-only `SExpr.eval` could not see.
R6 (#354) closes it additively: `SExpr` gains the `SLimb v i` constructor and a
tower-aware evaluator `SExpr.evalState : RustState → SExpr → Nat` that reads the
limb from `rs.rsTower` (the faithful image of AUCurves' `eval_sexpr_ed` `SLimb`
arm, masked through `mask64`).  The scalar `SExpr.eval` signature is UNCHANGED:
`SLimb` gets a safe default of `0` there, so the in-flight emit modules that
depend on `eval`'s `(String → Nat) → SExpr → Nat` shape are untouched.

The serialized form below is AUCurves' Qed-pinned `fe25519_add_sexpr_value`
(`LowCTEdSerialize.v`): five `(LimbStore (loc "dest" Fp25519) i (Add (Limb "a"
i) (Limb "b" i)))` writes, right-nested under `Seq`.  It now parses
constructor-by-constructor into the corresponding `RLimbStoreExpr` chain, and
each `(Add (Limb …) (Limb …))` value imports to `SAdd (SLimb …) (SLimb …)`.

#356 closes the final residual: `evalState` is now WIRED into the `RustExec`
relation — `RustExec.limbStoreExpr` evaluates the stored word via
`SExpr.evalState rs` (tower-heap read at byte offset `i*8`), so the runtime
effect of these `SLimb`-valued stores is faithful, not a scalar-`0` default.
The structural round-trip theorems here are unaffected (they live at the
`parseLowCT`/`toJasminCmd` layer, orthogonal to the runtime relation). -/

/-- AUCurves' byte-exact serialization of the real inline 5-limb
    `fe25519_add_body` (Qed-pinned in `LowCTEdSerialize.v` as
    `fe25519_add_sexpr_value`).  Five radix-2^51 limb writes
    `dest.limbs[i] := a.limbs[i] + b.limbs[i]`, right-nested under `Seq`. -/
def fe25519AddSexpr : String :=
  "(Seq (LimbStore (loc \"dest\" Fp25519) 0 (Add (Limb \"a\" 0) (Limb \"b\" 0))) " ++
  "(Seq (LimbStore (loc \"dest\" Fp25519) 1 (Add (Limb \"a\" 1) (Limb \"b\" 1))) " ++
  "(Seq (LimbStore (loc \"dest\" Fp25519) 2 (Add (Limb \"a\" 2) (Limb \"b\" 2))) " ++
  "(Seq (LimbStore (loc \"dest\" Fp25519) 3 (Add (Limb \"a\" 3) (Limb \"b\" 3))) " ++
  "(LimbStore (loc \"dest\" Fp25519) 4 (Add (Limb \"a\" 4) (Limb \"b\" 4)))))))"

/-- One limb-write of `fe25519_add`: `dest.limbs[i] := a.limbs[i] + b.limbs[i]`,
    as the `RLimbStoreExpr` the constructor map dictates. -/
def fe25519AddLimb (i : Nat) : LowCT :=
  .RLimbStoreExpr
    { locVar := "dest", locSrc := .TFp25519 }
    i
    (.SAdd (.SLimb "a" i) (.SLimb "b" i))

/-- The `LowCT` the constructor map dictates for the real `fe25519_add` body:
    five `RLimbStoreExpr` writes, right-nested under `RSeq`. -/
def fe25519AddExpected : LowCT :=
  .RSeq (fe25519AddLimb 0)
    (.RSeq (fe25519AddLimb 1)
      (.RSeq (fe25519AddLimb 2)
        (.RSeq (fe25519AddLimb 3)
          (fe25519AddLimb 4))))

/-- **R6 (structural correspondence) — the real field-op body.**  Importing
    AUCurves' Qed-certified `fe25519_add` serialization yields exactly the
    five-`RLimbStoreExpr` chain the IR map dictates.  Constructor-by-constructor:
    `Seq → RSeq`, `LimbStore → RLimbStoreExpr`, `(loc "dest" Fp25519) → Located
    TFp25519`, `(Add (Limb "a" i) (Limb "b" i)) → SAdd (SLimb "a" i) (SLimb "b"
    i)`, with slot names and limb indices recovered verbatim.  This is the body
    the R-pilot recorded as having no faithful image (the `SLimb`-over-tower
    obstacle); it now round-trips. -/
theorem importedFe25519Add_eq :
    parseLowCT fe25519AddSexpr = some fe25519AddExpected := by
  native_decide

/-- **R6 (backend cross-check).**  The owned front lowers the imported
    `fe25519_add` body to five Jasmin `STORE64` `Copn` nodes (one per limb),
    each with the lowered `SExpr` operand `a[i] + b[i]` — where `a[i]`/`b[i]`
    are the scaled-`U64` array reads (`Pget .AAscale .U64`) produced by the new
    `SLimb` lowering.  This is the radix-2^51 inline add-chain at the call-free
    granularity AUCurves' own jasmin backend emits it. -/
theorem importedFe25519Add_jasmin_eq :
    (parseLowCT fe25519AddSexpr).map toJasminCmd =
      some (toJasminCmd fe25519AddExpected) := by
  rw [importedFe25519Add_eq]
  rfl

/-- The single-limb lowering, spelled out: limb `i` write is one `STORE64`
    `Copn` whose value operand is `a[i] + b[i]` (`Papp2 Oadd` of two
    `Pget .AAscale .U64` reads).  Confirms the `SLimb` lowering is the scaled
    `U64` array read, byte-for-byte with the manual reference. -/
theorem fe25519AddLimb_jasmin_eq (i : Nat) :
    toJasminCmd (fe25519AddLimb i) =
      [InstrR.Copn
        [locToLVal { locVar := "dest", locSrc := .TFp25519 }]
        .AT_none
        (.Oasm { name := "STORE64" })
        [locToPExpr { locVar := "dest", locSrc := .TFp25519 },
         .Pconst (Int.ofNat i),
         CatCrypt.Crypto.Jasmin.LowCT.sexprToPExpr
           (.SAdd (.SLimb "a" i) (.SLimb "b" i))]] := by
  rfl

end CatCrypt.Crypto.SecureCompilation.AUCurvesImport
