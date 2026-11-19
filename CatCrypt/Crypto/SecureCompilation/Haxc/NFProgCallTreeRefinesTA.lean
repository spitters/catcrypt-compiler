/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree

/-!
# Refinement of trees at an answer predicate: transitivity and the iteration combinators

`RefinesTA Sk` is a transitive relation and a congruence of the tree combinators `ofoldl` and
`owhileIter`, as `RefinesT h₁` is at the answers of a handler. The lemmas are stated in
`NFProgCallTree.lean`, beside `RefinesTA`, in the namespace `NFProgCallTreeRuttSA`; this module
collects them with the `RuttSA` relation of `NFProgCallTreeRuttSA` for its importers.

## Main results

* `RefinesTA.trans`: refinement at a skip predicate composes.
* `RefinesTA.ofoldl`: refined steps give a refined fold.
* `RefinesTA.owhileIter`: refined bodies give a refined exit-flag iteration.
-/
