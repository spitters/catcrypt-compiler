/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.Security
public import CatCrypt.Crypto.UCDSL

/-!
# Hash Security: SHAKE bounds by capacity

Concrete SHAKE-128 and SHAKE-256 instances of the bound
`eps_rp + q^2/2^c` of `Security.lean`, where

- `eps_rp` = random permutation advantage for Keccak-f[1600]
- `q` = number of permutation queries
- `c` = capacity bits (256 for SHAKE-128, 512 for SHAKE-256)

The bound is the one of Bertoni-Daemen-Peeters-Van Assche (CRYPTO 2008) for
sponge indifferentiability. No theorem in this package proves it: in
`shake_rom_security` (`Security.lean`) both hops, the permutation replacement
(`h_rp`) and the sponge-to-random-oracle step (`h_reduce`), are hypotheses, and
the games are parameters not tied to Keccak-f. This file states the
arithmetic of the bound: monotonicity in the query count and the capacity.

## Main results

* `shake128_bound` / `shake256_bound` -- the bound at each SHAKE capacity
* `shake256_at_least_as_secure` -- the SHAKE-256 bound is at most the SHAKE-128 bound
* `sponge_bound_quadratic` -- the bound is monotone in queries
* `sponge_bound_capacity` -- the bound is anti-monotone in capacity
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Reduction

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Security
open CatCrypt.Crypto.UCDSL
open scoped ENNReal

/-! ## Concrete SHAKE Bounds -/

/-- SHAKE-128 bound: `eps_rp + q^2/2^256`. -/
noncomputable def shake128_bound (eps_rp : ENNReal) (q : Nat) : ENNReal :=
  shake128_rom_bound eps_rp q

/-- SHAKE-256 bound: `eps_rp + q^2/2^512`. -/
noncomputable def shake256_bound (eps_rp : ENNReal) (q : Nat) : ENNReal :=
  shake256_rom_bound eps_rp q

/-- The SHAKE-256 bound is at most the SHAKE-128 bound. -/
theorem shake256_at_least_as_secure (eps_rp : ENNReal) (q : Nat) :
    shake256_bound eps_rp q <= shake128_bound eps_rp q :=
  shake256_stronger_than_128 eps_rp q

/-! ## Indifferentiability Bound Properties -/

/-- The sponge indifferentiability bound grows quadratically in queries. -/
theorem sponge_bound_quadratic {q1 q2 : Nat} (h : q1 <= q2) (c : Nat) :
    sponge_indiff_bound q1 c <= sponge_indiff_bound q2 c :=
  sponge_indiff_bound_mono h c

/-- The sponge indifferentiability bound shrinks with larger capacity. -/
theorem sponge_bound_capacity {c1 c2 : Nat} (h : c1 <= c2) (q : Nat) :
    sponge_indiff_bound q c2 <= sponge_indiff_bound q c1 :=
  sponge_indiff_bound_capacity_mono h q

/-- Zero queries give zero indifferentiability bound. -/
theorem sponge_bound_zero_queries (c : Nat) :
    sponge_indiff_bound 0 c = 0 :=
  sponge_indiff_bound_zero c

end CatCrypt.Crypto.Hash.Reduction
