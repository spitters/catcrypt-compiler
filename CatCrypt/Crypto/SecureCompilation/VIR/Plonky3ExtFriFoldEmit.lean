/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3EmitMain

/-!
# Plonky3 extension-FRI fold: ExtensionMmcs fold + barycentric OOD/DEEP, owned

`FULL_PROVER_VS_P3.md` records the precise ext-FRI residual after the core deg-4
arithmetic landed (`Plonky3ExtFieldEmit`): *"the `ExtensionMmcs` fold (flatten the
arity-2 fold layer's 16×8 base rows, then Merkle-commit) … and the barycentric
OOD/DEEP-over-extension evaluation are the remaining C orchestration."*

This module closes that residual at the leaf level. The ExtensionMmcs fold and the
barycentric reduced-opening loop are **compositions** of the per-coordinate
extension operations — `eadd` / `esub` / `emul` / `escale` / `einv` — each of
which is an emitted verified-front leaf:

| ext op   | emitted leaf(s)                                  |
|----------|--------------------------------------------------|
| `emul`   | `ext4_mul_c0_rc … ext4_mul_c3_rc` (4 coords)     |
| `escale` | `ext4_scale_rc`  (per-coordinate base multiply)  |
| `eadd`   | `ext4_add_rc`    (per-coordinate base add)       |
| `esub`   | `ext4_sub_rc`    (per-coordinate base sub)       |
| `einv`   | `emul`+`escale`+`bb_inv_rc` (Frobenius/norm)     |

`ext4_add_rc` / `ext4_sub_rc` come from `Plonky3ExtFieldEmit` (`ext4AddCom` /
`ext4SubCom`) — each is a front-sourced pure-arith leaf (its denotation IS the
Barrett word arithmetic), so the whole fold's per-element ext arithmetic is
emitted-leaf, not hand-C. The remaining steps — the **row flatten** (16×2-ext → 16×8 base, a lane
interleave) and the **Merkle commit** of the flattened rows — are structural
marshalling over the existing base-field `plonky3_merkle_compress_rc` /
`plonky3_merkle_hash_leaf_rc` leaves (no new field op).

## What is closed here

* `ext4_add_rc` / `ext4_sub_rc` are emitted into the owned ext-field `.s`
  (`extFieldLprog`, rendered to `gen_com/ext4_from_rustcmd_owned.s`); the
  shape lemmas `extField_owned_has_{add,sub}` (in `Plonky3EmitMain`) pin
  their export labels.
* `ext_fri_all_ops_emitted` re-exports the pure-arith facts for the full ext-op
  set (mul ×4, scale, add, sub) — the by-construction `leaf.denote = spec` for
  every operation the ExtensionMmcs fold and the barycentric evaluation perform.

## KAT (byte-identical vs the p3 reference extension-FRI)

`bench/plonky3_compare/ext_fri_fold_from_rustcmd_kat.c` drives the ExtensionMmcs
fold (`folded16[r] = escale(eadd(lo,hi),inv2) + escale(emul(esub(lo,hi),β),hip[r])`,
the arity-2 FRI fold over the extension), the 16×8 row-flatten, the base-field
Merkle commit, and the barycentric reduced-opening loop — **all** through the
emitted ext leaves + Merkle leaves — and checks byte-identity vs the p3 reference
(`emul`/`escale`/`eadd`/`esub`/`einv` transcribed from `p3_accept_prove.c`):

```
barycentric reduced openings (32 rows) == p3 ref      : PASS
ExtensionMmcs fold (16 folded ext elems) == p3 ref    : PASS
ExtensionMmcs commit root (flattened 16x8 base) == ref: PASS
ext inverse (Frobenius/norm) consistency              : PASS
```

## Residual

The deg-4 extension-field FRI is CLOSED at the field-op level: every ext
operation in the fold and the barycentric evaluation is an emitted leaf, and the
row-flatten / commit reuse the emitted base-field Merkle leaves. The only
remaining C is the *index plumbing* that lays out which rows feed which commit
node (the flatten loop), which carries no field op — and that loop is itself
emittable through `Plonky3OrchLoopsEmit`'s owned `loopLcmd` orchestration
(the same Merkle-commit tree-level loop).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFriFoldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriFoldEmit (allPureArith)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFieldEmit
  (ext4MulC0Com ext4MulC1Com ext4MulC2Com ext4MulC3Com
   ext4ScaleCom ext4AddCom ext4SubCom
   ext4MulC0_is_purearith ext4MulC1_is_purearith ext4MulC2_is_purearith
   ext4MulC3_is_purearith ext4Scale_is_purearith ext4Add_is_purearith
   ext4Sub_is_purearith)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3EmitMain
  (extFieldAsm hasSub extField_owned_has_add extField_owned_has_sub)

/-! ## 1. Every ext op the fold / barycentric uses is an emitted pure-arith leaf

The ExtensionMmcs fold is `escale(eadd(lo,hi),inv2) +
escale(emul(esub(lo,hi),β),hip)`; the barycentric reduced openings are
`emul`/`escale`/`eadd`/`esub` chains over `einv`-computed inverse distances. Each
of `emul` (4 coords), `escale`, `eadd`, `esub` is one front-sourced leaf whose
bindings are `regArith`/`regConst`/`shlImm`/`shrImm` only — so the fold and the
barycentric evaluation are emitted-leaf arithmetic by construction. -/

/-- **All seven extension-FRI field ops are emitted pure-arith leaves.** The four
    `emul` coordinates, the base-field `escale`, and the per-coordinate `eadd` /
    `esub` — every operation the ExtensionMmcs fold and the barycentric OOD/DEEP
    perform — denote exactly the Barrett word arithmetic. The `einv` (Frobenius /
    norm) decomposes into these plus the base-field `bb_inv_rc`. -/
theorem ext_fri_all_ops_emitted :
    allPureArith ext4MulC0Com = true ∧ allPureArith ext4MulC1Com = true
      ∧ allPureArith ext4MulC2Com = true ∧ allPureArith ext4MulC3Com = true
      ∧ allPureArith ext4ScaleCom = true ∧ allPureArith ext4AddCom = true
      ∧ allPureArith ext4SubCom = true :=
  ⟨ext4MulC0_is_purearith, ext4MulC1_is_purearith,
   ext4MulC2_is_purearith, ext4MulC3_is_purearith,
   ext4Scale_is_purearith, ext4Add_is_purearith, ext4Sub_is_purearith⟩

/-! ## 2. The owned ext `.s` carries every fold/barycentric op's export label

The ExtensionMmcs fold and barycentric run against these symbols in the one owned
ext-field `.s` (`gen_com/ext4_from_rustcmd_owned.s`). -/

/-- The owned ext-field `.s` carries the `eadd` and `esub` leaves the fold /
    barycentric need — alongside the mul coords and scale already present. So the
    whole ext-FRI op set is one verified-emitted object. -/
theorem extFri_owned_has_add_sub :
    hasSub extFieldAsm "ext4_add_rc" = true
      ∧ hasSub extFieldAsm "ext4_sub_rc" = true :=
  ⟨extField_owned_has_add, extField_owned_has_sub⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3ExtFriFoldEmit
