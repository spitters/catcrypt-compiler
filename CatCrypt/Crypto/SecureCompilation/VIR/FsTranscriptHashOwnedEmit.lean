/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Shake256SpongeOwnedEmit

/-!
# Fiat–Shamir transcript hash: stable byte-interface symbol

The Fiat–Shamir transcript-hash realization target for the ArkLib connection.
This module renders the already-proven owned variable-length SHAKE256 sponge
(`Shake256SpongeOwnedEmit.shake256Fundef` — absorb loop, `pad10*1`, squeeze
loop, `call keccak_f1600_resident` between blocks) under a **stable, documented
C-ABI symbol** that byte-realization instances can link against. No new code is
authored here: `fsFundef` is *definitionally* the committed sponge `Lfundef`;
only the exported symbol name differs (the asm printer's `.L<name>_<l>`
function-scoped labels make the rename link-safe next to `shake256_owned`).

## Symbol contract (for the ReprTransfer / byte-realization instance)

```
void catcrypt_fs_absorb_squeeze(uint8_t *out, size_t outlen,
                                const uint8_t *in, size_t inlen);
```

* **ABI**: SysV x86-64 — `out → RDI`, `outlen → RSI`, `in → RDX`,
  `inlen → RCX`. Callee-saved discipline per the printer; the 200-byte Keccak
  state lives in the routine's own frame (no global state, re-entrant).
* **Semantics**: `out[0..outlen)` = the first `outlen` bytes of
  `SHAKE256(in[0..inlen))` per FIPS 202 (rate 136 bytes, domain suffix
  `0x1f`, `pad10*1`). Deterministic; any `inlen`/`outlen` (including 0).
* **Fiat–Shamir usage**: one-shot. The caller serializes the transcript
  (statement ‖ commitments ‖ prior messages) into a single contiguous byte
  string and squeezes the challenge bytes in one call. No incremental
  absorb/squeeze state is retained between calls; multi-round Fiat–Shamir
  re-absorbs the extended transcript each round.
* **Linking**: the emitted object (`bench/keccak_compare/gen_com/
  fs_transcript_hash_owned.s`) references one external symbol,
  `keccak_f1600_resident` (the owned FIPS-202-KAT'd permutation leaf,
  `bench/keccak_compare/gen/keccak_f1600_resident.s`). Link both.
* **Byte equivalence**: `fsFundef = Shake256SpongeOwnedEmit.shake256Fundef`
  holds by `rfl`, so every byte-level property of the KAT'd `shake256_owned`
  routine transfers to `catcrypt_fs_absorb_squeeze` unchanged.

KAT: `make -C bench/keccak_compare fs-transcript-kat` — NIST FIPS-202
SHAKE256 anchors + a PQClean `fips202.c` reference sweep over
transcript-shaped input/challenge lengths, driving the stable symbol.

Invoke:  lake env lean --run bench/keccak_compare/fs_transcript_hash_owned_emit.lean
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FsTranscriptHashOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLprogAtt)

/-- The stable Fiat–Shamir transcript-hash symbol. Byte-realization instances
    link against this name; it is the contract surface and must not change. -/
def fsSym : String := "catcrypt_fs_absorb_squeeze"

/-- The transcript-hash `Lfundef`: definitionally the committed owned
    variable-length SHAKE256 sponge (absorb / `pad10*1` / squeeze around
    `call keccak_f1600_resident`). -/
def fsFundef : Lfundef := Shake256SpongeOwnedEmit.shake256Fundef

/-- The stable symbol carries the sponge body unchanged (byte-equivalence
    anchor for the realization instance). -/
theorem fsFundef_eq_sponge :
    fsFundef = Shake256SpongeOwnedEmit.shake256Fundef := rfl

/-- The one-function object exporting the stable symbol. -/
def fsLprog : Lprog := { lp_funcs := [(fsSym, fsFundef)] }

/-- The rendered `.s` text (written to
    `bench/keccak_compare/gen_com/fs_transcript_hash_owned.s`). -/
def fsAsm : String := renderLprogAtt fsLprog

/-! ## Shape checks -/

/-- The object exports the stable symbol, `call`s the owned permutation leaf,
    and renders with no unhandled op. -/
theorem fs_transcript_shape :
    occursIn "catcrypt_fs_absorb_squeeze" fsAsm = true
      ∧ occursIn "call keccak_f1600_resident" fsAsm = true
      ∧ occursIn "UNHANDLED" fsAsm = false := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.FsTranscriptHashOwnedEmit
