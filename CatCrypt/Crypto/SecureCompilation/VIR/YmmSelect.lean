/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc

/-!
# Vector instruction selection: rotates and three-input logic

A peephole pass over `List YmmInstr` that replaces two instruction idioms with
single AVX-512VL instructions:

* **Rotate.** `t₁ := vpsllq k x`, `t₂ := vpsrlq (64 - k) x`, `d := vpor t₁ t₂`
  becomes `d := vprolq k x`.
* **And-not-xor.** `t := vpandn b c`, `d := vpxor a t` becomes
  `d := vpternlogq 0xD2 d b c` when `d` is `a`, or `vmovdqu a → d` followed by
  it when `d` is distinct from `a`, `b` and `c`.

Either idiom is rewritten only when its temporaries are read by no later
instruction, so removing them changes no value any later instruction sees. The
checks are conservative: a temporary mentioned anywhere later blocks the
rewrite, whatever redefines it first.

The value each rewrite relies on is proved: `qword_rotl_eq_shiftOr` for the
rotate, lane by lane, and `chi_is_ternlog_d2` for the and-not-xor at the full
256 bits. The immediate `0xD2` is the truth table of `a ^ (~b & c)`, which is
Keccak's chi step.

The pass is generic over the instruction stream; it has no knowledge of the
program it runs on.

## Main definitions

* `readsLater`: whether a name is read by any instruction in a suffix.
* `selectYmm`: the peephole.
* `qword_rotl_eq_shiftOr`, `chi_is_ternlog_d2`: the value identities.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

/-- The truth table of `a ^ (~b & c)` with `a` the high input: Keccak's chi. -/
def chiImm : Nat := 0xD2

/-- Whether `n` is read by any instruction of `rest`. -/
def readsLater (n : String) (rest : List YmmInstr) : Bool :=
  rest.any (fun i => (ymmReadNames i).contains n)

/-- Whether the three instructions `t₁ := vpsllq k x`, `t₂ := vpsrlq k₂ x₂`,
    `d := vpor srcs`, followed by `rest`, form a rotate the pass may fuse. -/
def rotateOk (k k₂ : Nat) (t₁ t₂ x x₂ : String) (srcs : List String)
    (rest : List YmmInstr) : Bool :=
  x == x₂ && k + k₂ == 64 && 0 < k && k < 64
    && (srcs == [t₁, t₂] || srcs == [t₂, t₁])
    && t₁ != t₂ && t₁ != x && t₂ != x
    && !readsLater t₁ rest && !readsLater t₂ rest

/-- The replacement for `t := vpandn b c`, `d := vpxor srcs`, if the pair is an
    and-not-xor the pass may fuse; `none` otherwise. -/
def chiRewrite (t b c d : String) (srcs : List String) (rest : List YmmInstr) :
    Option (List YmmInstr) :=
  let a? : Option String :=
    match srcs with
    | [p, q] => if q == t then some p else if p == t then some q else none
    | _ => none
  match a? with
  | none => none
  | some a =>
    if t == a || t == b || t == c || readsLater t rest then none
    else if d == a then some [.ternlog chiImm d b c]
    else if d == b || d == c then none
    else some [.ymov d a, .ternlog chiImm d b c]

/-- The peephole. Each rewrite consumes its whole idiom; otherwise the head
    instruction is kept and the pass moves one instruction on. -/
def selectYmm : List YmmInstr → List YmmInstr
  | (.alu (.vpsllq k) t₁ [x]) :: (.alu (.vpsrlq k₂) t₂ [x₂]) :: (.alu .vpor d srcs) :: rest =>
      if rotateOk k k₂ t₁ t₂ x x₂ srcs rest then
        .alu (.vprolq k) d [x] :: selectYmm rest
      else
        .alu (.vpsllq k) t₁ [x] ::
          selectYmm ((.alu (.vpsrlq k₂) t₂ [x₂]) :: (.alu .vpor d srcs) :: rest)
  | (.alu .vpandn t [b, c]) :: (.alu .vpxor d srcs) :: rest =>
      match chiRewrite t b c d srcs rest with
      | some out => out ++ selectYmm rest
      | none => .alu .vpandn t [b, c] :: selectYmm ((.alu .vpxor d srcs) :: rest)
  | i :: rest => i :: selectYmm rest
  | [] => []
termination_by l => l.length

/-! ## The value identities -/

/-- A left rotate of a 64-bit lane is the OR of its two shifts. The rotate
    rewrite fuses exactly this triple, lane by lane. -/
theorem qword_rotl_eq_shiftOr (x : BitVec 64) (k : Nat) (hk : k < 64) :
    x.rotateLeft k = (x <<< k) ||| (x >>> (64 - k)) := by
  rw [BitVec.rotateLeft_def]
  simp [Nat.mod_eq_of_lt hk]

/-- `vpternlogq 0xD2` computes `a ^ (~b & c)` on all 256 bits: the and-not-xor
    rewrite replaces `vpandn` and `vpxor` by one instruction of the same value. -/
theorem chi_is_ternlog_d2 (a b c : BitVec 256) :
    ternlogW chiImm a b c = vpxorW a (vpandnW b c) := by
  simp only [chiImm, ternlogW, vpxorW, vpandnW, List.range, List.range.loop, List.foldl]
  simp (config := { decide := true })
  ext i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_xor]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

end CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
