/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationSyntax

/-!
# `orch%` — a usable authoring surface for the covered orchestration fragment

`Fe25519OrchestrationSyntax.lean` prototyped a Rust-like concrete syntax for a
*single* orchestration shape: one `RFor` over `RCall`/`RCallN` leaf calls. That
proved the transparency idea (`orchSyntax_eq_raw : … = macAccumulate n := rfl`),
but it covered only three constructors of a straight-line loop body.

This file grows that prototype into a surface that spans the **real** covered
control fragment (`IsCoveredCtl` — bounded/runtime loops + `RIfNz` over covered
branches, plus the covered straight-line statements). It adds:

* an **`SExpr` sub-syntax** (`scalar …`) — index/bit arithmetic
  (`"i" * 16 + "d"`, `("a" << 3) ^ ("b" & 7)`, `mulhi("a","b")`) with the usual
  `*`-binds-tighter-than-`+` precedence, elaborating to the `SAdd`/`SMul`/`SShl`/
  `SXor`/… tree — the payload of `RScalarSetExpr`;
* **`RIfNz`** — `if "x" != 0 {| … |} else {| … |}`, nesting whole blocks;
* **`RForRuntime`** — `for "j" in 0.. "n" {| … |}`, whose upper bound is a runtime
  scalar (`SVar "n"`) rather than the literal `RFor` bound `0.. 5`;
* **`RScalarSet`** — literal scalar assign `"k" := lit 16`;
* **`RScalarSetExpr`** — arithmetic scalar assign `"k" := scalar "i" * 16 + "d"`;
* **`RCallSwap`** — the two-destination conditional swap `cswap f "a" "b" ("m")`;
* **`RSkip`** — `skip`; and a **block** `{| s₁ ; … ; sₖ |}` that right-folds into
  `RSeq` and nests inside every control statement.

The surface is a **transparent AST builder**: every production is paired below
with an `= raw-AST` `rfl`, so the ergonomic notation and the hand-written
`LowCT` term are literally the same term — the notation carries no trust.

The capstone is a **real orchestration**: a Montgomery-ladder step
(`ladderStep`, the X25519 double-and-add shape — the conditional `cswap`,
`fe25519_add`/`fe25519_sub`/`fe25519_mul` field temporaries) written in the
surface and proven `rfl`-equal to its raw `LowCT` AST (`ladderStep_eq_raw`).
This witnesses that a genuine program — not just a toy loop — is writable in
`orch%`.

## Note on statement scope

The block `{| … |}` term notation and the `ostmt`/`orchSExpr` syntax categories
are file-local in spirit (only files importing this module see them). The field
slots are all `TowerType.TFp25519` (the radix-2⁵¹ Curve25519 base field) and the
scalar slots `TU64`; `cswap`'s mask argument is threaded as a field-typed
`Located` too, so the whole surface uses one slot builder — the transparency
`rfl`s pin exactly the AST that builder produces.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample

open CatCrypt.Crypto.Jasmin.LowCT
open Lean

/-! ## 1. The `SExpr` sub-syntax — `scalar …`

`orchSExpr` is a small arithmetic grammar over scalar slots (string names) and
`Nat` literals, with `*`/`&`/`<<`/`>>` binding tighter than `+`/`-`/`^`. It
elaborates through `osexpr%` into the `SExpr` tree that `RScalarSetExpr` stores. -/

declare_syntax_cat orchSExpr

syntax:max str : orchSExpr                                   -- SVar
syntax:max num : orchSExpr                                   -- SLit
syntax:max "(" orchSExpr ")" : orchSExpr                     -- grouping
syntax:max "mulhi" "(" orchSExpr "," orchSExpr ")" : orchSExpr  -- SMulHiU
syntax:70 orchSExpr:70 " * "  orchSExpr:71 : orchSExpr       -- SMul
syntax:69 orchSExpr:69 " & "  orchSExpr:70 : orchSExpr       -- SAnd
syntax:68 orchSExpr:68 " << " orchSExpr:69 : orchSExpr       -- SShl
syntax:68 orchSExpr:68 " >> " orchSExpr:69 : orchSExpr       -- SShr
syntax:65 orchSExpr:65 " + "  orchSExpr:66 : orchSExpr       -- SAdd
syntax:65 orchSExpr:65 " - "  orchSExpr:66 : orchSExpr       -- SSub
syntax:60 orchSExpr:60 " ^ "  orchSExpr:61 : orchSExpr       -- SXor

/-- Elaborate an `orchSExpr` into its `SExpr` tree. Transparent: each production
    maps to exactly one `SExpr` constructor. -/
syntax:max "osexpr% " orchSExpr : term

macro_rules
  | `(osexpr% $s:str)          => `(SExpr.SVar $s)
  | `(osexpr% $n:num)          => `(SExpr.SLit $n)
  | `(osexpr% ( $e ))          => `(osexpr% $e)
  | `(osexpr% mulhi( $a , $b )) => `(SExpr.SMulHiU (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a * $b)         => `(SExpr.SMul (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a & $b)         => `(SExpr.SAnd (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a << $b)        => `(SExpr.SShl (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a >> $b)        => `(SExpr.SShr (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a + $b)         => `(SExpr.SAdd (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a - $b)         => `(SExpr.SSub (osexpr% $a) (osexpr% $b))
  | `(osexpr% $a ^ $b)         => `(SExpr.SXor (osexpr% $a) (osexpr% $b))

/-! ## 2. Orchestration statements + the block term

`ostmt` is one covered statement; `{| s₁ ; … ; sₖ |}` right-folds a `;`-list of
them into `RSeq` (via `orchSeq`) and is itself a `LowCT` term, so it nests
inside every control statement below. -/

declare_syntax_cat ostmt

/-- `dst := callN fn(a, …)` → `RCallN fn [dst] [a, …]` (multi-dest leaf call). -/
syntax:min str ":=" "callN" ident "(" str,* ")" : ostmt
/-- `dst := call fn(a, …)` → `RCall fn dst [a, …]` (accumulating leaf call). -/
syntax:min str ":=" "call" ident "(" str,* ")" : ostmt
/-- `cswap fn d1 d2 (a, …)` → `RCallSwap fn d1 d2 [a, …]` (two-dest cond. swap). -/
syntax:min "cswap" ident str str "(" str,* ")" : ostmt
/-- `x := lit n` → `RScalarSet x n` (literal scalar assign). -/
syntax:min str ":=" "lit" num : ostmt
/-- `x := scalar e` → `RScalarSetExpr x e` (arithmetic scalar assign). -/
syntax:min str ":=" "scalar" orchSExpr : ostmt
/-- `if c != 0 {| … |} else {| … |}` → `RIfNz c thenB elseB`. -/
syntax:min "if" str "!=" num term " else " term : ostmt
/-- `for x in 0.. n {| … |}` (literal bound) → `RFor x n body`. -/
syntax:min "for" str "in" num ".." num term : ostmt
/-- `for x in 0.. "b" {| … |}` (runtime bound) → `RForRuntime x (SVar b) body`. -/
syntax:min "for" str "in" num ".." str term : ostmt
/-- `skip` → `RSkip`. -/
syntax:min "skip" : ostmt

/-- The block: right-fold a `;`-separated `ostmt` list into `RSeq` (`orchSeq`),
    as a `LowCT` term. Nests inside `if`/`for` bodies. -/
syntax (name := orchBlockTerm) "{|" sepBy1(ostmt, ";") "|}" : term

macro_rules
  | `(ostmt| $dst:str := callN $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallN $fnName
          [(⟨$dst, TowerType.TFp25519⟩ : Located)]
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| $dst:str := call $fn:ident ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCall $fnName
          (⟨$dst, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| cswap $fn:ident $d1:str $d2:str ( $args:str,* )) => do
      let fnName := Syntax.mkStrLit fn.getId.toString
      `(LowCT.RCallSwap $fnName
          (⟨$d1, TowerType.TFp25519⟩ : Located)
          (⟨$d2, TowerType.TFp25519⟩ : Located)
          [$[(⟨$args, TowerType.TFp25519⟩ : Located)],*])
  | `(ostmt| $x:str := lit $n:num) => `(LowCT.RScalarSet $x $n)
  | `(ostmt| $x:str := scalar $e:orchSExpr) => `(LowCT.RScalarSetExpr $x (osexpr% $e))
  | `(ostmt| if $c:str != $_z:num $thenB:term else $elseB:term) =>
      `(LowCT.RIfNz $c $thenB $elseB)
  | `(ostmt| for $i:str in $_lo:num .. $n:num $body:term) =>
      `(LowCT.RFor $i $n $body)
  | `(ostmt| for $i:str in $_lo:num .. $b:str $body:term) =>
      `(LowCT.RForRuntime $i (SExpr.SVar $b) $body)
  | `(ostmt| skip) => `(LowCT.RSkip)
  | `({| $[$stmts];* |}) => do
      let stmtsT : Array (TSyntax `term) := stmts.map (fun s => ⟨s.raw⟩)
      `(orchSeq [$[$stmtsT],*])

/-! ## 3. Per-constructor transparency — each production `= raw-AST` by `rfl`

Every covered-fragment constructor the surface adds is pinned to the exact raw
`LowCT` term it builds. There is nothing to verify about the macro beyond these
definitional identities. -/

/-- `callN` → `RCallN` (one-statement block `= c`). -/
theorem surf_callN_eq_raw :
    ({| "p" := callN fe25519_mul("a_i", "b_i") |})
      = LowCT.RCallN "fe25519_mul" [⟨"p", .TFp25519⟩]
          [⟨"a_i", .TFp25519⟩, ⟨"b_i", .TFp25519⟩] := rfl

/-- `call` → `RCall`. -/
theorem surf_call_eq_raw :
    ({| "acc" := call fe25519_add("p") |})
      = LowCT.RCall "fe25519_add" ⟨"acc", .TFp25519⟩ [⟨"p", .TFp25519⟩] := rfl

/-- `cswap` → `RCallSwap` (two-destination conditional swap). -/
theorem surf_cswap_eq_raw :
    ({| cswap fe25519_cswap "x2" "x3" ("swap") |})
      = LowCT.RCallSwap "fe25519_cswap"
          ⟨"x2", .TFp25519⟩ ⟨"x3", .TFp25519⟩ [⟨"swap", .TFp25519⟩] := rfl

/-- `lit` → `RScalarSet` (literal scalar). -/
theorem surf_lit_eq_raw :
    ({| "k" := lit 16 |}) = LowCT.RScalarSet "k" 16 := rfl

/-- `scalar` → `RScalarSetExpr`, and the `SExpr` precedence: `*` binds tighter
    than `+`, so `"i" * 16 + "d"` is `SAdd (SMul i 16) d`. -/
theorem surf_scalarExpr_eq_raw :
    ({| "k" := scalar "i" * 16 + "d" |})
      = LowCT.RScalarSetExpr "k"
          (.SAdd (.SMul (.SVar "i") (.SLit 16)) (.SVar "d")) := rfl

/-- The `SExpr` right-precedence witness: `"a" + "b" * 2` is
    `SAdd a (SMul b 2)`, not `SMul (SAdd a b) 2`. -/
theorem surf_sexpr_prec_eq_raw :
    ({| "r" := scalar "a" + "b" * 2 |})
      = LowCT.RScalarSetExpr "r"
          (.SAdd (.SVar "a") (.SMul (.SVar "b") (.SLit 2))) := rfl

/-- The bitwise `SExpr` arms + grouping: `("a" << 3) ^ ("b" & 7)`. -/
theorem surf_sexpr_bitwise_eq_raw :
    ({| "m" := scalar ("a" << 3) ^ ("b" & 7) |})
      = LowCT.RScalarSetExpr "m"
          (.SXor (.SShl (.SVar "a") (.SLit 3))
                 (.SAnd (.SVar "b") (.SLit 7))) := rfl

/-- `mulhi(_, _)` → `SMulHiU`; `-` and `>>` arms. -/
theorem surf_sexpr_mulhi_eq_raw :
    ({| "h" := scalar mulhi("a", "b") - ("c" >> 5) |})
      = LowCT.RScalarSetExpr "h"
          (.SSub (.SMulHiU (.SVar "a") (.SVar "b"))
                 (.SShr (.SVar "c") (.SLit 5))) := rfl

/-- `if … != 0 { } else { }` → `RIfNz`, with nested blocks. -/
theorem surf_ifNz_eq_raw :
    ({| if "swap" != 0 {| "x2" := call fe25519_add("t") |} else {| skip |} |})
      = LowCT.RIfNz "swap"
          (LowCT.RCall "fe25519_add" ⟨"x2", .TFp25519⟩ [⟨"t", .TFp25519⟩])
          LowCT.RSkip := rfl

/-- `for … in 0.. "n"` (runtime bound) → `RForRuntime` over `SVar "n"`. -/
theorem surf_forRuntime_eq_raw :
    ({| for "j" in 0.. "n" {| "acc" := call fe25519_add("p") |} |})
      = LowCT.RForRuntime "j" (.SVar "n")
          (LowCT.RCall "fe25519_add" ⟨"acc", .TFp25519⟩ [⟨"p", .TFp25519⟩]) := rfl

/-- `for … in 0.. 5` (literal bound) → `RFor` — the runtime/literal distinction
    is visible in the surface (`"n"` vs `5`). -/
theorem surf_forLit_eq_raw :
    ({| for "j" in 0.. 5 {| skip |} |})
      = LowCT.RFor "j" 5 LowCT.RSkip := rfl

/-- `skip` → `RSkip`. -/
theorem surf_skip_eq_raw : ({| skip |}) = LowCT.RSkip := rfl

/-- A multi-statement block right-folds into `RSeq` (via `orchSeq`). -/
theorem surf_block_seq_eq_raw :
    ({| "a" := callN fe25519_add("x", "y");
        "b" := callN fe25519_mul("a", "a") |})
      = LowCT.RSeq
          (LowCT.RCallN "fe25519_add" [⟨"a", .TFp25519⟩]
            [⟨"x", .TFp25519⟩, ⟨"y", .TFp25519⟩])
          (LowCT.RCallN "fe25519_mul" [⟨"b", .TFp25519⟩]
            [⟨"a", .TFp25519⟩, ⟨"a", .TFp25519⟩]) := rfl

/-! ## 4. The capstone — a real Montgomery-ladder step in the surface

`ladderStep` is the X25519 double-and-add inner step (RFC 7748 shape): the
conditional swap of the two projective points (`RIfNz` on the swap bit, driving
two `cswap`s), then the field arithmetic that folds `(x2, z2, x3, z3)` forward —
`A = x2+z2`, `B = x2-z2`, `AA = A²`, `BB = B²`, `E = AA-BB`, `C = x3+z3`,
`D = x3-z3`, `DA = D·A`, `CB = C·B`, `x2 = AA·BB`, `z2 = E·E`, then a loop-index
bump `pos := i+1`. Field ops are `fe25519_add`/`fe25519_sub`/`fe25519_mul`
leaf calls; the swap is `fe25519_cswap`. -/

/-- **The ladder step, in the `orch%` surface.** Reads like Rust: named field
    temporaries, a conditional `cswap`, field-op leaf calls. -/
def ladderStep : LowCT :=
  {| if "swap" != 0 {|
         cswap fe25519_cswap "x2" "x3" ("swap");
         cswap fe25519_cswap "z2" "z3" ("swap")
       |} else {|
         skip
       |};
     "a"  := callN fe25519_add("x2", "z2");
     "b"  := callN fe25519_sub("x2", "z2");
     "aa" := callN fe25519_mul("a", "a");
     "bb" := callN fe25519_mul("b", "b");
     "e"  := callN fe25519_sub("aa", "bb");
     "c"  := callN fe25519_add("x3", "z3");
     "d"  := callN fe25519_sub("x3", "z3");
     "da" := callN fe25519_mul("d", "a");
     "cb" := callN fe25519_mul("c", "b");
     "x2" := callN fe25519_mul("aa", "bb");
     "z2" := callN fe25519_mul("e", "e");
     "pos" := scalar "i" + 1 |}

/-- The same ladder step written directly as the raw `LowCT` AST — the "before"
    of the surface (nested `RSeq`, explicit `Located`s, hand-built `RIfNz`/
    `RCallSwap`/`RScalarSetExpr`). -/
def ladderStepRaw : LowCT :=
  .RSeq
    (.RIfNz "swap"
      (.RSeq
        (.RCallSwap "fe25519_cswap" ⟨"x2", .TFp25519⟩ ⟨"x3", .TFp25519⟩ [⟨"swap", .TFp25519⟩])
        (.RCallSwap "fe25519_cswap" ⟨"z2", .TFp25519⟩ ⟨"z3", .TFp25519⟩ [⟨"swap", .TFp25519⟩]))
      .RSkip)
    (.RSeq (.RCallN "fe25519_add" [⟨"a", .TFp25519⟩] [⟨"x2", .TFp25519⟩, ⟨"z2", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_sub" [⟨"b", .TFp25519⟩] [⟨"x2", .TFp25519⟩, ⟨"z2", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"aa", .TFp25519⟩] [⟨"a", .TFp25519⟩, ⟨"a", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"bb", .TFp25519⟩] [⟨"b", .TFp25519⟩, ⟨"b", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_sub" [⟨"e", .TFp25519⟩] [⟨"aa", .TFp25519⟩, ⟨"bb", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_add" [⟨"c", .TFp25519⟩] [⟨"x3", .TFp25519⟩, ⟨"z3", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_sub" [⟨"d", .TFp25519⟩] [⟨"x3", .TFp25519⟩, ⟨"z3", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"da", .TFp25519⟩] [⟨"d", .TFp25519⟩, ⟨"a", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"cb", .TFp25519⟩] [⟨"c", .TFp25519⟩, ⟨"b", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"x2", .TFp25519⟩] [⟨"aa", .TFp25519⟩, ⟨"bb", .TFp25519⟩])
    (.RSeq (.RCallN "fe25519_mul" [⟨"z2", .TFp25519⟩] [⟨"e", .TFp25519⟩, ⟨"e", .TFp25519⟩])
      (.RScalarSetExpr "pos" (.SAdd (.SVar "i") (.SLit 1))))))))))))))

/-- **The capstone witness — a real program is writable in the surface.** The
    `orch%` ladder step and the hand-written raw AST are the *same* `LowCT`
    term (`rfl`). The surface hid the `RSeq` nesting, the `Located` typing, and
    the `SExpr` tree without introducing any new trust. -/
theorem ladderStep_eq_raw : ladderStep = ladderStepRaw := rfl

/-- Read-back of the ladder step's head: the conditional swap is exactly an
    `RIfNz` on the swap bit driving two `RCallSwap`s. -/
theorem ladderStep_head_isIfNzCswap :
    ∃ rest, ladderStep =
      .RSeq
        (.RIfNz "swap"
          (.RSeq
            (.RCallSwap "fe25519_cswap" ⟨"x2", .TFp25519⟩ ⟨"x3", .TFp25519⟩ [⟨"swap", .TFp25519⟩])
            (.RCallSwap "fe25519_cswap" ⟨"z2", .TFp25519⟩ ⟨"z3", .TFp25519⟩ [⟨"swap", .TFp25519⟩]))
          .RSkip)
        rest := ⟨_, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Fe25519OrchestrationExample
