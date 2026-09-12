/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Ascent.AscendDecide
public import CatCrypt.Crypto.SecureCompilation.Ascent.AscendDecide
public import Lean

/-!
# Fragment membership by syntax walk: `ascend_meta`

`ascend!` / `ascend_expr!` / `ascend_bitwise!` (`Ascent/AscendDecide.lean`) decide
fragment membership by `decide` on a `Bool` checker over the whole `LowCT` term, so
the elaborator reduces the checker over every node of the kernel before the proof
exists. `ascend_meta` is the membership route for large terms: an elaborator that
walks the term's syntax and builds the proof from the fragment's constructors
directly, one constructor application per `LowCT` / `SExpr` node.

The walk is over the term after `whnf` at each node, so `def`-bound kernels,
`let`-bound abbreviations and bodies built by `List.foldr` / `List.map` over a
lane list are all accepted; the constructor is read off the head symbol.

Each leaf side condition is closed on that leaf alone: a variable's `¬ isTmpName x`
by `notTmpB_sound` with `decide` on the one string, a literal's `n < 2 ^ 64` by
`isArithCleanB_sound` / `isWordCleanB_sound` with `decide` on the one `SLit` node.
No `decide` runs over a compound term.

## Main results

* `ascend_meta` — closes `IsAscendable c`, `IsAscendableExpr c`,
  `IsAscendableBitwise c`, and a `Corres` goal at the `asemW` / `asemWExpr` /
  `asemWBV` spec of a concrete kernel, through `ascend_sound`,
  `ascend_expr_sound`, `ascend_expr_sound_of_isAscendable` or
  `ascend_bitwise_sound`.
* `keccakRoundBody` — one Keccak-f[1600] round (θ, ρ, π, χ, ι) over 25 named
  lanes as a bitwise straight-line `LowCT` kernel; `keccakRoundBody_bitwise` lifts it
  to its `BitVec 64` spec by `ascend_meta`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT

namespace AscendMeta

meta section

open Lean Meta Elab Tactic

/-- The three straight-line fragments: literal terminals only (`IsAscendable`),
    arithmetic expression terminals (`IsAscendableExpr`), bitwise expression terminals
    (`IsAscendableBitwise`). -/
inductive Frag where
  | lit
  | arith
  | word
  deriving BEq, Repr

/-- The membership predicate of a fragment. -/
def Frag.predName : Frag → Name
  | .lit => ``IsAscendable
  | .arith => ``IsAscendableExpr
  | .word => ``IsAscendableBitwise

/-- The expression cleanliness predicate of a fragment with expression terminals. -/
def Frag.cleanName : Frag → Name
  | .lit => ``IsArithClean
  | .arith => ``IsArithClean
  | .word => ``IsWordClean

/-- The `Bool` checker of the cleanliness predicate. -/
def Frag.cleanBName : Frag → Name
  | .lit => ``isArithCleanB
  | .arith => ``isArithCleanB
  | .word => ``isWordCleanB

/-- The soundness lemma from the `Bool` checker to the cleanliness predicate. -/
def Frag.cleanBSoundName : Frag → Name
  | .lit => ``isArithCleanB_sound
  | .arith => ``isArithCleanB_sound
  | .word => ``isWordCleanB_sound

/-- A proof of `¬ isTmpName x`: `notTmpB_sound x` on a `decide` of the single string.
    A string literal starting with `'_'` is rejected before any proof is built. -/
def proveNotTmp (x : Expr) : MetaM Expr := do
  let x' ← whnf x
  if let .lit (.strVal s) := x' then
    if s.front == '_' then
      throwError "ascend_meta: the name {repr s} starts with '_' and is not proved non-temp"
  let prop ← mkEq (mkApp (mkConst ``notTmpB) x) (mkConst ``Bool.true)
  return mkApp2 (mkConst ``notTmpB_sound) x (← mkDecideProof prop)

/-- A proof of the cleanliness predicate on one `SLit n` node, by the fragment's
    `Bool` soundness lemma on a `decide` of that node alone. -/
def proveLitLeaf (frag : Frag) (e n : Expr) : MetaM Expr := do
  let n' ← whnf n
  if let .lit (.natVal v) := n' then
    if v ≥ 2 ^ 64 then
      throwError "ascend_meta: the literal {v} is not below 2 ^ 64"
  let prop ← mkEq (mkApp (mkConst frag.cleanBName) e) (mkConst ``Bool.true)
  return mkApp2 (mkConst frag.cleanBSoundName) e (← mkDecideProof prop)

/-- A proof of `IsArithClean e` (fragment `arith`) or `IsWordClean e` (fragment `word`)
    by recursion over the constructors of the `whnf` of `e`: `SVar` through
    `proveNotTmp`, `SLit` through `proveLitLeaf`, a binary node of the fragment
    through `And.intro` on its two operands. -/
partial def proveClean (frag : Frag) (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let binary (a b : Expr) : MetaM Expr := do
    let ha ← proveClean frag a
    let hb ← proveClean frag b
    let P := mkConst frag.cleanName
    return mkApp4 (mkConst ``And.intro) (mkApp P a) (mkApp P b) ha hb
  match e.getAppFnArgs with
  | (``SExpr.SVar, #[x]) => proveNotTmp x
  | (``SExpr.SLit, #[n]) => proveLitLeaf frag e n
  | (``SExpr.SAdd, #[a, b]) | (``SExpr.SSub, #[a, b]) | (``SExpr.SMul, #[a, b]) =>
      if frag == .arith then binary a b
      else throwError "ascend_meta: {e} is an arithmetic node outside the bitwise fragment"
  | (``SExpr.SXor, #[a, b]) | (``SExpr.SAnd, #[a, b])
  | (``SExpr.SShl, #[a, b]) | (``SExpr.SShr, #[a, b]) =>
      if frag == .word then binary a b
      else throwError "ascend_meta: {e} is a bitwise node outside the arithmetic fragment"
  | _ => throwError "ascend_meta: {e} is outside the {frag.cleanName} fragment"

/-- A proof of the fragment's membership predicate on `c` by recursion over the
    constructors of the `whnf` of `c`: `RSkip`, `RBlock`, `RSeq`, `RScalarSet`, and for
    the expression fragments `RScalarSetExpr` with its side condition from
    `proveClean`. -/
partial def proveMember (frag : Frag) (c : Expr) : MetaM Expr := do
  let c ← whnf c
  let pred := frag.predName
  match c.getAppFnArgs with
  | (``LowCT.RSkip, #[]) => return mkConst (.str pred "rSkip")
  | (``LowCT.RBlock, #[body]) =>
      return mkApp2 (mkConst (.str pred "rBlock")) body (← proveMember frag body)
  | (``LowCT.RSeq, #[c₁, c₂]) =>
      let h₁ ← proveMember frag c₁
      let h₂ ← proveMember frag c₂
      return mkApp4 (mkConst (.str pred "rSeq")) c₁ c₂ h₁ h₂
  | (``LowCT.RScalarSet, #[name, n]) =>
      return mkApp2 (mkConst (.str pred "rScalarSet")) name n
  | (``LowCT.RScalarSetExpr, #[x, e]) =>
      if frag == .lit then
        throwError "ascend_meta: {c} is an expression terminal outside {pred}"
      return mkApp3 (mkConst (.str pred "rScalarSetExpr")) x e (← proveClean frag e)
  | _ => throwError "ascend_meta: {c} is outside the fragment {pred}"

/-- The fragment and kernel of a membership goal `IsAscendable c` /
    `IsAscendableExpr c` / `IsAscendableBitwise c`. -/
def fragOfGoal? (t : Expr) : Option (Frag × Expr) :=
  match t.getAppFnArgs with
  | (``IsAscendable, #[c]) => some (.lit, c)
  | (``IsAscendableExpr, #[c]) => some (.arith, c)
  | (``IsAscendableBitwise, #[c]) => some (.word, c)
  | _ => none

/-- Close a membership goal by `proveMember`, checking the proof's type against the
    goal. -/
def solveMembership (g : MVarId) : MetaM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let t ← whnfR t
  match fragOfGoal? t with
  | some (frag, c) =>
      let p ← proveMember frag c
      unless ← isDefEq (← inferType p) t do
        throwError "ascend_meta: the membership proof does not match the goal {t}"
      g.assign p
  | none => throwError "ascend_meta: the goal {t} is not a fragment membership"

/-- The `Corres` entry points, each with the fragment its hypothesis ranges over. -/
def corresRoutes : List (Name × Frag) :=
  [(``ascend_expr_sound, .arith),
   (``ascend_expr_sound_of_isAscendable, .lit),
   (``ascend_sound, .lit),
   (``ascend_bitwise_sound, .word)]

/-- `ascend_meta` closes a fragment membership goal `IsAscendable c` /
    `IsAscendableExpr c` / `IsAscendableBitwise c` by walking the syntax of `c`, and a
    `Corres` goal at a kernel's `asemW` / `asemWExpr` / `asemWBV` spec by applying the
    first of `ascend_expr_sound`, `ascend_expr_sound_of_isAscendable`, `ascend_sound`,
    `ascend_bitwise_sound` that unifies with the goal at reducible transparency and
    then walking the kernel. -/
elab "ascend_meta" : tactic => do
  let g ← getMainGoal
  let t ← g.withContext do whnfR (← instantiateMVars (← g.getType))
  if (fragOfGoal? t).isSome then
    liftMetaTactic fun g => do
      solveMembership g
      return []
  else
    let mut lastErr : Option Exception := none
    for (thm, _) in corresRoutes do
      let s ← saveState
      try
        let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels thm)
        match gs with
        | [g'] =>
            solveMembership g'
            replaceMainGoal []
            return
        | _ => throwError "ascend_meta: {thm} left {gs.length} goals"
      catch e =>
        restoreState s
        lastErr := some e
    match lastErr with
    | some e => throwError "ascend_meta: no ascent route closes the goal; last error: {e.toMessageData}"
    | none => throwError "ascend_meta: no ascent route"

end

end AscendMeta

/-! ## The small kernels

The kernels of `AscendDecide.lean`, closed by the syntax walk instead of `decide`. -/

/-- Two arithmetic expression terminals in sequence. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RSeq (.RScalarSetExpr "acc" (.SAdd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "out" (.SMul (.SVar "acc") (.SVar "c")))))
      (.RSeq (.RScalarSetExpr "acc" (.SAdd (.SVar "a") (.SVar "b")))
        (.RScalarSetExpr "out" (.SMul (.SVar "acc") (.SVar "c")))) := by
  ascend_meta

/-- A nested block mixing a literal leaf with an expression terminal. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemWExpr (.RBlock (.RSeq (.RScalarSet "k" 5)
        (.RScalarSetExpr "r" (.SSub (.SVar "x") (.SVar "k"))))))
      (.RBlock (.RSeq (.RScalarSet "k" 5)
        (.RScalarSetExpr "r" (.SSub (.SVar "x") (.SVar "k"))))) := by
  ascend_meta

/-- A ChaCha-style quarter-round step over the bitwise fragment. -/
example :
    Corres SRwordBV (fun _ => True)
      (asemWBV (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SAnd (.SVar "b") (.SVar "c")))))
      (.RSeq (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SVar "a")))
        (.RScalarSetExpr "b" (.SAnd (.SVar "b") (.SVar "c")))) := by
  ascend_meta

/-- The literal fragment over the total relation `SRword`. -/
example :
    Corres SRword (fun _ => True)
      (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
      (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by
  ascend_meta

/-- A literal-only kernel stated at the `asemW` spec, over the non-temp relation. -/
example :
    Corres SRwordNT (fun _ => True)
      (asemW (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)))
      (.RSeq (.RScalarSet "x" 5) (.RScalarSet "y" 7)) := by
  ascend_meta

/-- A membership goal on its own, with a `let`-bound kernel. -/
example :
    let k : LowCT := .RSeq (.RScalarSet "c" 0)
      (.RScalarSetExpr "d" (.SXor (.SVar "d") (.SLit (2 ^ 64 - 1))))
    IsAscendableBitwise k := by
  intro k
  ascend_meta

/-! ## A Keccak-f[1600] round

The state is 25 lanes `a00 … a44` (`axy`, column `x`, row `y`). θ writes the column
parities `c0 … c4` and the column differences `d0 … d4`, then folds each `dx` into
its column; ρ and π rotate each lane into `b00 … b44`; χ writes the state back from
`b`; ι mixes a round constant into `a00`. A rotate is `(e <<< k) ^^^ (e >>> (64 - k))`
and a complement is a xor with the all-ones literal, so the round is in the bitwise
fragment. -/

/-- The lane names, index `5 * x + y`. -/
def keccakLaneNames : List String :=
  ["a00", "a01", "a02", "a03", "a04",
   "a10", "a11", "a12", "a13", "a14",
   "a20", "a21", "a22", "a23", "a24",
   "a30", "a31", "a32", "a33", "a34",
   "a40", "a41", "a42", "a43", "a44"]

/-- The ρ-π intermediate lane names, index `5 * x + y`. -/
def keccakBNames : List String :=
  ["b00", "b01", "b02", "b03", "b04",
   "b10", "b11", "b12", "b13", "b14",
   "b20", "b21", "b22", "b23", "b24",
   "b30", "b31", "b32", "b33", "b34",
   "b40", "b41", "b42", "b43", "b44"]

/-- The θ column parity names. -/
def keccakColNames : List String := ["c0", "c1", "c2", "c3", "c4"]

/-- The θ column difference names. -/
def keccakDNames : List String := ["d0", "d1", "d2", "d3", "d4"]

/-- The ρ rotation offsets, index `5 * x + y`. -/
def keccakRho : List Nat :=
  [0, 36, 3, 41, 18,
   1, 44, 10, 45, 2,
   62, 6, 43, 15, 61,
   28, 55, 25, 21, 56,
   27, 20, 39, 8, 14]

/-- The lane `(x, y)`, coordinates taken modulo 5. -/
def keccakLane (x y : Nat) : String := keccakLaneNames.getD (5 * (x % 5) + y % 5) "a00"

/-- The intermediate lane `(x, y)`, coordinates taken modulo 5. -/
def keccakB (x y : Nat) : String := keccakBNames.getD (5 * (x % 5) + y % 5) "b00"

/-- The rotation offset of lane `(x, y)`. -/
def keccakRhoOff (x y : Nat) : Nat := keccakRho.getD (5 * (x % 5) + y % 5) 0

/-- `e` rotated left by `k` as shifts and a xor. -/
def rotlExpr (e : SExpr) (k : Nat) : SExpr :=
  .SXor (.SShl e (.SLit k)) (.SShr e (.SLit (64 - k)))

/-- The 25 lane coordinates. -/
def keccakXY : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4),
   (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
   (2, 0), (2, 1), (2, 2), (2, 3), (2, 4),
   (3, 0), (3, 1), (3, 2), (3, 3), (3, 4),
   (4, 0), (4, 1), (4, 2), (4, 3), (4, 4)]

/-- The five column indices. -/
def keccakCols : List Nat := [0, 1, 2, 3, 4]

/-- A statement list as a right-nested `RSeq` chain ending in `RSkip`. -/
def seqAll (cs : List LowCT) : LowCT := cs.foldr .RSeq .RSkip

/-- θ, column parities: `cx := ax0 ^^^ ax1 ^^^ ax2 ^^^ ax3 ^^^ ax4`. -/
def keccakThetaC : List LowCT := keccakCols.map fun x =>
  .RScalarSetExpr (keccakColNames.getD x "c0")
    (.SXor (.SVar (keccakLane x 0)) (.SXor (.SVar (keccakLane x 1))
      (.SXor (.SVar (keccakLane x 2)) (.SXor (.SVar (keccakLane x 3)) (.SVar (keccakLane x 4))))))

/-- θ, column differences: `dx := c(x-1) ^^^ rotl(c(x+1), 1)`. -/
def keccakThetaD : List LowCT := keccakCols.map fun x =>
  .RScalarSetExpr (keccakDNames.getD x "d0")
    (.SXor (.SVar (keccakColNames.getD ((x + 4) % 5) "c0"))
      (rotlExpr (.SVar (keccakColNames.getD ((x + 1) % 5) "c0")) 1))

/-- θ, the fold into the state: `axy := axy ^^^ dx`. -/
def keccakThetaApply : List LowCT := keccakXY.map fun p =>
  .RScalarSetExpr (keccakLane p.1 p.2)
    (.SXor (.SVar (keccakLane p.1 p.2)) (.SVar (keccakDNames.getD p.1 "d0")))

/-- ρ and π: `b(y, 2x+3y) := rotl(axy, r[x][y])`. -/
def keccakRhoPi : List LowCT := keccakXY.map fun p =>
  .RScalarSetExpr (keccakB p.2 (2 * p.1 + 3 * p.2))
    (rotlExpr (.SVar (keccakLane p.1 p.2)) (keccakRhoOff p.1 p.2))

/-- χ: `axy := bxy ^^^ ((b(x+1)y ^^^ ones) &&& b(x+2)y)`. -/
def keccakChi : List LowCT := keccakXY.map fun p =>
  .RScalarSetExpr (keccakLane p.1 p.2)
    (.SXor (.SVar (keccakB p.1 p.2))
      (.SAnd (.SXor (.SVar (keccakB (p.1 + 1) p.2)) (.SLit (2 ^ 64 - 1)))
        (.SVar (keccakB (p.1 + 2) p.2))))

/-- ι with the round-24 constant: `a00 := a00 ^^^ 0x8000000080008008`. -/
def keccakIota : LowCT := .RScalarSetExpr "a00" (.SXor (.SVar "a00") (.SLit 0x8000000080008008))

/-- One Keccak-f[1600] round as a straight-line bitwise kernel: 86 `RScalarSetExpr`
    terminals in a right-nested `RSeq` chain. -/
def keccakRoundBody : LowCT :=
  seqAll (keccakThetaC ++ keccakThetaD ++ keccakThetaApply ++ keccakRhoPi ++ keccakChi ++
    [keccakIota])

/-- The Keccak round is in the bitwise fragment, by the syntax walk. -/
theorem keccakRoundBody_isAscendableBitwise : IsAscendableBitwise keccakRoundBody := by
  ascend_meta

/-- The Keccak round lifts to its `BitVec 64` word spec `asemWBV keccakRoundBody` by
    one `ascend_meta`. -/
theorem keccakRoundBody_bitwise :
    Corres SRwordBV (fun _ => True) (asemWBV keccakRoundBody) keccakRoundBody := by
  ascend_meta

/-- The same goal by `ascend_bitwise!`, the `decide` route, for comparison. -/
theorem keccakRoundBody_bitwise_decide :
    Corres SRwordBV (fun _ => True) (asemWBV keccakRoundBody) keccakRoundBody := by
  ascend_bitwise!

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.keccakRoundBody_bitwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keccakRoundBody_bitwise

end CatCrypt.Crypto.SecureCompilation.Ascent
