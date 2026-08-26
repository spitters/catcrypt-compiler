/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Model-free ChaCha20 little-endian byte serialization (RFC 8439 §2.3)

The ChaCha20 block function (RFC 8439 §2.3) finishes, after the twenty rounds and
the +input feedback, by serializing the sixteen 32-bit output words little-endian
to 64 bytes: for word index `i ∈ 0..15` and byte offset `k ∈ 0..3`, the output
byte at position `4·i + k` is the `k`-th little-endian byte of output word `i`,
i.e. `(out[i] >>> 8·k) & 0xFF`.

This module restates the serialization tie
`Chacha20DwordFinalizeRealization.serializeLE32_byte` **model-free**: over a
plain `Fin 16 → BitVec 32` word vector, with no dependence on the `ZState32` dword
lane model (`Avx512DwordModel`). The serialization is pure data movement — no
arithmetic — so the tie is a pure `BitVec` byte-extraction identity. This file
imports only `JasminDialect` (for `BitVec`), never the dword model, so the
RFC-8439 §2.3 serialization tie survives deleting `Avx512DwordModel`.

The statements (`leByte`, `serializeLE32`, `serializeLE32_byte`) are bit-for-bit
the same as the bespoke realization-file versions; they were already model-free
and merely happened to live alongside the `ZState32` finalization realization.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordSerializeCom

/-- The `k`-th little-endian byte of a 32-bit word `w` (`k ∈ 0..3`): the byte
    `(w >>> 8·k) & 0xFF`, as a `BitVec 8`. The RFC 8439 §2.3 little-endian
    word→byte projection. Model-free (pure `BitVec`). -/
def leByte (w : BitVec 32) (k : Fin 4) : BitVec 8 :=
  (w >>> (8 * k.val)).setWidth 8

/-- **The abstract little-endian serialization** of the sixteen ChaCha20 output
    words to 64 bytes (RFC 8439 §2.3). Byte at position `j ∈ 0..63` is the
    `(j % 4)`-th little-endian byte of output word `j / 4`. Indexed by `Fin 64`.
    The serialization is pure data movement (no arithmetic), so this is stated
    over a plain `Fin 16 → BitVec 32` word vector — no machine model. -/
def serializeLE32 (w : Fin 16 → BitVec 32) : Fin 64 → BitVec 8 :=
  fun j => leByte (w ⟨j.val / 4, by omega⟩) ⟨j.val % 4, by omega⟩

/-- **The serialization byte tie (RFC 8439 §2.3), model-free.** Byte `4·i + k` of
    the little-endian serialization of the output words `w` is exactly the `k`-th
    little-endian byte of output word `i` — `(w i >>> 8·k) & 0xFF`. The word→byte
    projection is bit-exact (`setWidth 8`). Stated over a plain
    `Fin 16 → BitVec 32`, so it carries no dependence on the `ZState32` dword lane
    model — the identity is pure `BitVec`/`Fin` arithmetic. -/
theorem serializeLE32_byte (w : Fin 16 → BitVec 32) (i : Fin 16) (k : Fin 4) :
    serializeLE32 w ⟨4 * i.val + k.val, by omega⟩ = leByte (w i) k := by
  have hi : (4 * i.val + k.val) / 4 = i.val := by omega
  have hk : (4 * i.val + k.val) % 4 = k.val := by omega
  simp only [serializeLE32, leByte, hi, hk, Fin.eta]

end CatCrypt.Crypto.SecureCompilation.VIR.Chacha20DwordSerializeCom
