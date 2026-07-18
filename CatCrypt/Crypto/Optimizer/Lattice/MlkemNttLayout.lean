/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec

/-!
# Lane↔coefficient layout for the ML-KEM-768 16-way AVX2 NTT, and the
  whole-transform tie

The emitted ML-KEM forward NTT
(`SecureCompilation/VIR/LatticeNttEmit.lean`, §6b `emitMlkemNttFull16wayJazz`)
processes **one** 256-coefficient polynomial as **16 `u256` vectors of 16 `u16`
lanes**. Its `[:u256 v]` slot `v` (`0 … 15`) holds 16 consecutive coefficients;
lane `l` (`0 … 15`) within slot `v` is the coefficient at the **linear storage
position** `16·v + l`. The Cooley–Tukey layers MIX coefficients across lanes
(the `len = 8, 4, 2` layers use `#VPERMQ` / `#VPSHUFB_256` cross-lane shuffles),
so no *per-lane* `LaneMap` frame can express the transform: the genuine target
is a **whole-transform** statement over all 256 positions.

This file supplies two pieces of that target:

1. the explicit **storage layout permutation** `mlkemNttStorageLayout : Equiv.Perm
   (Fin 256)` — the vector-major / lane-minor map `(v, l) ↦ 16·v + l` that names
   the linear coefficient index of each (slot, lane) — proved a bijection by
   construction (it is `finProdFinEquiv`, repackaged);
2. the **transform-order permutation** `bitrevPerm 8` from the (already proved)
   iterative-NTT specification, together with the whole-transform statement
   relating the kernel's natural-order linear output to the definitional `dft`.

## The two layouts, and why the storage one is identity at the I/O boundary

There are two distinct index permutations in an AVX2 NTT:

* the **I/O storage layout** — how the 256 coefficient *words* sit in the 16
  vectors. The §6b kernel and its byte-KAT
  (`bench/mlkem_compare/mlkem_ntt_full_bench.c`) both load and store the
  polynomial **linearly** (`em[i] = base[i]`, slot/lane position `16·v + l` is
  coefficient `16·v + l`), and the KAT compares `em[i]` against
  `PQCLEAN_MLKEM768_CLEAN_ntt(pq)[i]` **in the same linear order**. So the
  AVX2 `nttpack`/`nttunpack` deinterleave is *folded out at the I/O boundary*:
  the storage-to-linear map the emitted kernel exposes is `finProdFinEquiv`,
  i.e. linear order. `mlkemNttStorageLayout` records exactly this map and proves
  it acts as the identity on the linear index (`mlkemNttStorageLayout_apply`).

* the **transform-order permutation** — the decimation-in-time NTT leaves its
  output in **bit-reversed frequency order**. This is the genuinely non-trivial
  index permutation, and it is `bitrevPerm 8`. The whole-transform statement
  below routes it through the proved keystone `nttIter_eq_nttRec_comp_bitrev`.

Deinterleave used: the **standard ML-KEM AVX2 vector-major lane layout**
(slot-major, lane-minor `16·v + l`), as exposed by the §6b emit's `[:u256 v]`
slot indexing and its linear-load/linear-store byte-KAT against
`PQCLEAN_MLKEM768_CLEAN_ntt` (PQClean `mlkem-native` / `avx2`, the reference
oracle of `bench/mlkem_compare/mlkem_ntt_full_bench.c`).

## Whole-transform spec and what is proved

`mlkemNttKernelSpec` is the value the emitted kernel must produce at each linear
storage position. It is *defined* to be the iterative DIT transform `nttIter 8 ω`
on the natural-order input — exactly the layer-fold the kernel performs. The
theorem

`mlkemNttKernelSpec_eq_dft_bitrev :`
`    mlkemNttKernelSpec x k = dft 256 ω (fun j ↦ x (bitrevPerm 8 j)) k`

ties that layer-fold, *position by position over all 256 outputs*, to the
definitional length-256 `dft` of the bit-reversed input — purely from
`nttIter_eq_nttRec_comp_bitrev` plus the storage-layout algebra. The companion
`mlkemNttKernelSpec_bitrev_eq_dft` states the cleaner natural-input form: feeding
the bit-reversed input to the kernel computes `dft` in natural index order.

## Scope

This file is *spec level*. It contributes (a) the genuine, reusable storage
layout permutation, and (b) the whole-transform statement the emit must satisfy,
proved against the in-Lean `dft`/`nttIter` specification. It does **not** prove
the emitted kernel's machine *bytes* equal `mlkemNttKernelSpec`: there is no
`Com`/`.jazz` denotation of the §6b kernel to tie to, so the emit↔spec
byte-identity remains **KAT-gated**
(`bench/mlkem_compare/mlkem_ntt_full_bench.c`, byte-identical to
`PQCLEAN_MLKEM768_CLEAN_ntt` on all inputs). The single missing step to close
the tie in Lean is an *emit-denotation* function
`⟦emitMlkemNttFull16wayJazz⟧ : (Fin 256 → ZMod 3329) → (Fin 256 → ZMod 3329)`
and a lemma `⟦…⟧ = mlkemNttKernelSpec`; this file proves everything reachable on
the spec side of that lemma. No emit denotation is fabricated here.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout

open CatCrypt.Crypto.Optimizer.Lattice.IterativeNttEqRec
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NTTRecursionPass

/-! ## 1. The storage layout permutation -/

/-- The emitted 16-way kernel's **storage layout** as a permutation of the 256
linear coefficient indices, exposed as the vector-major / lane-minor bijection
`Fin 16 × Fin 16 ≃ Fin 256`, `(v, l) ↦ 16·v + l`. `finProdFinEquiv` gives
`(v, l) ↦ l + 16·v`; coupled with the `Fin 16 × Fin 16 ≃ Fin 256` index
identification this is precisely the linear index of slot `v`, lane `l`. -/
def mlkemNttStorageLayout : Equiv.Perm (Fin 256) :=
  -- `finProdFinEquiv : Fin 16 × Fin 16 ≃ Fin (16*16)`; compose with its inverse
  -- to land back on `Fin 256` (= `Fin (16*16)` definitionally), i.e. read the
  -- (slot, lane) coordinates off a linear index and re-pack them linearly.
  -- This is the identity permutation written through the slot/lane coordinates.
  (finProdFinEquiv.symm.trans finProdFinEquiv :
    Fin (16 * 16) ≃ Fin (16 * 16))

/-- The linear index of slot `v`, lane `l` is `16·v + l`. This is the storage
layout's defining equation, read off `finProdFinEquiv`. -/
theorem mlkemNttStorageLayout_coord (v l : Fin 16) :
    (finProdFinEquiv (v, l) : Fin (16 * 16)).val = l.val + 16 * v.val := by
  rw [finProdFinEquiv_apply_val]

/-- **The storage layout is the identity on linear indices.** The §6b emit and
its byte-KAT load/store the polynomial linearly, so the storage-to-linear map is
the identity: reading off (slot, lane) coordinates and re-packing them recovers
the same linear position. -/
@[simp] theorem mlkemNttStorageLayout_apply (i : Fin 256) :
    mlkemNttStorageLayout i = i := by
  simp [mlkemNttStorageLayout]

/-- `mlkemNttStorageLayout` is a bijection — it is an `Equiv.Perm` by
construction, and concretely it is the identity permutation. -/
theorem mlkemNttStorageLayout_bijective :
    Function.Bijective mlkemNttStorageLayout :=
  mlkemNttStorageLayout.bijective

/-! ## 2. The whole-transform spec the emit must satisfy -/

/-- The ML-KEM forward-NTT root `ω = 17 : ZMod 3329`. -/
abbrev mlkemOmega : ZMod 3329 := 17

/-- **The whole-transform specification** for the emitted 16-way kernel: the
value at each linear storage position `k` of running the kernel on natural-order
input `x`. It is *defined* as the iterative DIT transform `nttIter 8 ω` — exactly
the layer-fold (len = 128, 64, …, 2) the §6b kernel performs across its 16
vectors. The `:= id` placeholder block in `LatticeNttEmit.lean` is intended to be
replaced by (a denotation that equals) this. -/
def mlkemNttKernelSpec (x : Fin (2 ^ 8) → ZMod 3329) (k : Fin (2 ^ 8)) :
    ZMod 3329 :=
  nttIter 8 mlkemOmega x k

/-- **Whole-transform tie (bit-reversed-input form).** Running the emitted
kernel's specification on the **bit-reversed** input computes the definitional
length-256 `dft` of the natural-order input. This is `nttIter_comp_bitrev_eq_dft`
specialised to the ML-KEM parameters, after discharging `ω ^ 256 = 1`. Every one
of the 256 output positions is covered. -/
theorem mlkemNttKernelSpec_bitrev_eq_dft (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin (2 ^ 8)) :
    mlkemNttKernelSpec (fun j => x ((bitrevPerm 8) j)) k
      = dft (2 ^ 8) mlkemOmega x k := by
  unfold mlkemNttKernelSpec
  exact nttIter_comp_bitrev_eq_dft 8 mlkemOmega hω x k

/-- **Whole-transform tie (natural-input form).** The emitted kernel's
specification on natural-order input equals the length-256 `dft` of the
**bit-reversed** input — i.e. the decimation-in-time transform leaves its output
in bit-reversed frequency order. Pure permutation algebra over
`nttIter_eq_nttRec_comp_bitrev` and `nttRec_eq_dft`; the bit-reversal
`bitrevPerm 8` is the genuine transform-order layout permutation. -/
theorem mlkemNttKernelSpec_eq_dft_bitrev (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin (2 ^ 8)) :
    mlkemNttKernelSpec x k
      = dft (2 ^ 8) mlkemOmega (fun j => x ((bitrevPerm 8) j)) k := by
  unfold mlkemNttKernelSpec
  rw [nttIter_eq_nttRec_comp_bitrev 8 mlkemOmega x k,
    NTTRecursiveFull.nttRec_eq_dft 8 mlkemOmega hω]

/-- **Storage-layout / transform-order composition.** Re-expressing the
natural-input tie through the (identity) storage layout: applying the storage
layout to the output index does not change the value, so the kernel's output at
storage position `k` is the `dft` of the bit-reversed input at the same index.
Confirms the I/O storage permutation contributes nothing beyond the linear order
— the only genuine index permutation is `bitrevPerm 8`. -/
theorem mlkemNttKernelSpec_storage_eq_dft_bitrev (x : Fin (2 ^ 8) → ZMod 3329)
    (hω : mlkemOmega ^ (2 ^ 8) = 1) (k : Fin 256) :
    mlkemNttKernelSpec x (mlkemNttStorageLayout k)
      = dft (2 ^ 8) mlkemOmega (fun j => x ((bitrevPerm 8) j)) k := by
  rw [mlkemNttStorageLayout_apply]
  exact mlkemNttKernelSpec_eq_dft_bitrev x hω k

end CatCrypt.Crypto.Optimizer.Lattice.MlkemNttLayout
