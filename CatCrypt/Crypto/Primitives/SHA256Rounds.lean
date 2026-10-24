/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import CatCrypt.Crypto.Primitives.SHA256

/-!
# SHA-256 compression as an iteration of the round function

`CatCrypt.Crypto.Primitives.SHA256.compress` folds a `Vector`-based round
body 64 times over the message schedule. This file identifies that fold with
`compressRounds`, the iteration of the exported `compressRound`, and carries
the identification up to `sha256Short`.

## References

* FIPS 180-4, Section 6.2.2 — SHA-256 compression
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.SHA256

/-- Transport a `Fin.foldl` along a pair of mutually inverse maps whose step
    functions correspond. -/
theorem foldl_transfer {α : Type} {β : Type} (r : α → β) (s : β → α)
    (hr : ∀ a, s (r a) = a) (hs : ∀ b, r (s b) = b) :
    ∀ (n : Nat) (stepA : α → Fin n → α) (stepB : β → Fin n → β)
      (_ : ∀ a t, stepB (r a) t = r (stepA a t)) (b : β),
      Fin.foldl n stepB b = r (Fin.foldl n stepA (s b)) := by
  intro n
  induction n with
  | zero => intro stepA stepB h b; simp [hs]
  | succ n ih =>
    intro stepA stepB h b
    rw [Fin.foldl_succ, Fin.foldl_succ]
    have hb : stepB b 0 = r (stepA (s b) 0) := by
      have := h (s b) 0
      rwa [hs] at this
    rw [ih (fun a t => stepA a t.succ) (fun b t => stepB b t.succ)
      (fun a t => h a t.succ) (stepB b 0), hb, hr]

/-- The 64 SHA-256 rounds run over a message schedule `w`, starting from `state`.
    Round `t` uses `w t` and the round constant `kConst t`. -/
def compressRounds (w : Fin 64 → UInt32) (state : State256) : State256 :=
  Fin.foldl 64 (fun s t => compressRound s (w t) (kConst t.val)) state

unseal compress compressRound in
/-- **`compress` is the 64-fold of `compressRound` plus the feed-forward.**
    The compression function adds its input state to the result of running
    `compressRounds` over the block's message schedule. -/
theorem compress_eq_compressRounds (state : State256) (block : Fin 64 → UInt8) :
    compress state block = fun i => state i + compressRounds (messageSchedule block) state i := by
  funext i
  simp only [compress, compressRounds]
  congr 1
  refine (congrFun (foldl_transfer (fun v : Vector UInt32 8 => fun j => v[j]) Vector.ofFn
    (fun _ => Vector.ofFn_getElem) (fun _ => by funext j; simp) 64 _ _ ?_ state) i).symm
  intro v t
  funext j
  simp [compressRound, Vector.ofFn_getElem]

unseal sha256Short in
/-- **The one-block SHA-256 digest is the serialized 64-round iteration.**
    `sha256Short` pads its message, runs `compressRounds` from the FIPS 180-4
    initial state over the padded block's message schedule, adds the initial
    state, and serializes. -/
theorem sha256Short_eq_compressRounds (msg : List UInt8) :
    sha256Short msg =
      serializeState (fun i =>
        hInit i + compressRounds (messageSchedule (padShort msg)) hInit i) := by
  rw [sha256Short, compress_eq_compressRounds]

end CatCrypt.Crypto.Primitives.SHA256
