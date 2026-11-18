/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.AES
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.StraightLine

/-!
# A bitsliced AES round as a constant-time `jasminDialect` template

The AES-128 round `AES128.aesRound` and the final round `AES128.aesFinalRound`, run on `w`
blocks at once, as straight-line programs of `jasminDialect` on `w`-bit words generated through
the compiler of `HashTemplate.StraightLine`.

The layout has one word per bit of the state: the plane numbered `8 k + b` holds bit `b` of
byte `k` of every block, lane `j` of the word belonging to block `j`. The state and the round
key are 128 planes each. Every gate of the program is a bitwise operation, which acts on each
lane independently, so the program computes the round of each block in its own lane.

* SubBytes is the depth-16 boolean circuit of Boyar and Peralta for the S-box (128 gates:
  exclusive or, conjunction and the complement of the exclusive or), applied to the eight
  planes of each byte position. Its value is checked once over the 256 bytes against
  `AES128.sbox` and lifted to `w`-bit words lane by lane.
* ShiftRows is a renaming of planes.
* MixColumns and AddRoundKey are exclusive ors of planes: bit `b` of byte `(r, c)` of the
  result is the exclusive or of the planes of `xtime (y r c ⊕ y (r+1) c)` at bit `b`, of bit `b`
  of `y (r+1) c`, `y (r+2) c`, `y (r+3) c`, and of the key plane, `y` the bytes after SubBytes
  and ShiftRows; multiplication by `x` in GF(2⁸) is a renaming of planes and two exclusive ors.

The program reads the 128 state planes and the 128 key planes from one stack array of 256
words and stores the 128 planes of the result by register index into a second stack array,
the output array, which it does not read. It has no branch and no memory access at an index
that depends on its inputs.

## Main definitions

* `AesGate`, `runGates`, `gatesWF`: boolean circuits over numbered wires and their values.
* `aesSboxGates`: the S-box circuit of Boyar and Peralta.
* `aesSubLets`, `aesOutLets`: the symbolic SubBytes layer and the symbolic output planes.
* `aesBody`, `aesRoundBody`, `aesFinalRoundBody`: the programs.
* `aesUnpack`, `aesPack`: the bytes of block `j` in the planes, and the planes of `w` blocks.

## Main results

* `aesSboxGates_table`: the circuit computes `AES128.sbox` on each of the 256 bytes.
* `evalLets_reloc_getLsbD`: a circuit compiled to word expressions computes, in each lane,
  the circuit on the bits of that lane.
* `aesRoundBody_value`, `aesFinalRoundBody_value`: the programs return the planes of the round
  and of the final round of each block, whatever the contents of the output array.
* `aesRoundBody_events`, `aesFinalRoundBody_events`: the programs emit the same events at every
  two valuations, at leakage parameters with no variable-time operation.

## References

* J. Boyar, R. Peralta, "A depth-16 circuit for the AES S-box", SEC 2012.
* E. Käsper, P. Schwabe, "Faster and timing-attack resistant AES-GCM", CHES 2009.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.Primitives
open Ctxt (Var Valuation)

/-! ## 1. Boolean circuits and their lane-wise compilation -/

/-- A gate of a boolean circuit over numbered wires: the exclusive or, the conjunction and the
    complement of the exclusive or of two wires. -/
inductive AesGate where
  /-- The exclusive or. -/
  | xor (a b : Nat)
  /-- The conjunction. -/
  | and (a b : Nat)
  /-- The complement of the exclusive or. -/
  | xnor (a b : Nat)
  deriving DecidableEq, Repr

namespace AesGate

/-- The word expression of a gate at width `w`, its wires renamed by `f`. -/
def toWExp (w : Nat) (f : Nat → Nat) : AesGate → WExp w
  | .xor a b => .bin .xor (.var (f a)) (.var (f b))
  | .and a b => .bin .and (.var (f a)) (.var (f b))
  | .xnor a b => .bin .xor (.bin .xor (.var (f a)) (.var (f b))) (.const (BitVec.allOnes w))

/-- The value of a gate at the boolean values `v` of the wires. -/
def evalB (v : Nat → Bool) : AesGate → Bool
  | .xor a b => v a ^^ v b
  | .and a b => v a && v b
  | .xnor a b => !(v a ^^ v b)

/-- Both inputs of the gate are wires numbered below `n`. -/
def inputsBelow (n : Nat) : AesGate → Bool
  | .xor a b => a < n && b < n
  | .and a b => a < n && b < n
  | .xnor a b => a < n && b < n

/-- Lane `j` of the value of a compiled gate is the gate at lane `j` of its inputs. -/
theorem toWExp_eval_getLsbD (w : Nat) (f : Nat → Nat) (g : AesGate) (ρ : Nat → BitVec w)
    (j : Nat) (hj : j < w) :
    ((g.toWExp w f).eval ρ).getLsbD j = g.evalB (fun i => (ρ (f i)).getLsbD j) := by
  cases g <;> simp [toWExp, evalB, WExp.eval, JasminBinOp.apply, hj]

/-- A gate reads only its inputs. -/
theorem evalB_congr (g : AesGate) (n : Nat) (hg : g.inputsBelow n = true) (v v' : Nat → Bool)
    (h : ∀ i < n, v i = v' i) : g.evalB v = g.evalB v' := by
  cases g <;> simp_all [inputsBelow, evalB]

end AesGate

/-- The values of the wires of a circuit: the input values `inp`, then the value of each gate
    in order, each gate reading the wires before it. -/
def runGates (inp : List Bool) (C : List AesGate) : List Bool :=
  C.foldl (fun acc g => acc ++ [g.evalB fun i => acc.getD i false]) inp

/-- Every gate of `C` reads only the `n` inputs and the gates before it. -/
def gatesWF : Nat → List AesGate → Bool
  | _, [] => true
  | n, g :: C => g.inputsBelow n && gatesWF (n + 1) C

/-- A circuit has a wire for each input and each gate. -/
theorem runGates_length (C : List AesGate) : ∀ inp : List Bool,
    (runGates inp C).length = inp.length + C.length := by
  induction C with
  | nil => intro inp; simp [runGates]
  | cons g C ih =>
      intro inp
      simp only [runGates, List.foldl_cons] at ih ⊢
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

/-- A last gate appends its value to the wires of the circuit before it. -/
theorem runGates_append (inp : List Bool) (C : List AesGate) (g : AesGate) :
    runGates inp (C ++ [g]) =
      runGates inp C ++ [g.evalB fun i => (runGates inp C).getD i false] := by
  simp [runGates, List.foldl_append]

/-- A circuit with a last gate is well formed when the circuit before it is and the gate reads
    only earlier wires. -/
theorem gatesWF_append (n : Nat) (C : List AesGate) (g : AesGate) :
    gatesWF n (C ++ [g]) = (gatesWF n C && g.inputsBelow (n + C.length)) := by
  induction C generalizing n with
  | nil => simp [gatesWF]
  | cons g' C ih =>
      simp only [List.cons_append, gatesWF, ih, List.length_cons, Bool.and_assoc]
      grind

/-- The renaming of the wires of a circuit with eight inputs: the input `o < 8` to `f o`, the
    gate wire `8 + t` to `base + t`. -/
def relocWire (f : Nat → Nat) (base o : Nat) : Nat := if o < 8 then f o else base + (o - 8)

/-- **A compiled circuit computes the circuit in each lane**: the gates of `C`, compiled to
    word expressions binding the words numbered from `base`, its eight inputs read from the
    words `f i` below `base`; lane `j` of every wire is the value of the wire of `C` at lane `j`
    of the inputs. -/
theorem evalLets_reloc_getLsbD (w : Nat) (C : List AesGate) (hC : gatesWF 8 C = true)
    (f : Nat → Nat) (base : Nat) (hf : ∀ i < 8, f i < base) (ρ : Nat → BitVec w) (j : Nat)
    (hj : j < w) : ∀ o < 8 + C.length,
      (evalLets ρ base (C.map (AesGate.toWExp w (relocWire f base)))
          (relocWire f base o)).getLsbD j =
        (runGates (List.ofFn fun i : Fin 8 => (ρ (f i)).getLsbD j) C).getD o false := by
  induction C using List.reverseRecOn with
  | nil =>
      intro o ho
      simp only [List.length_nil, Nat.add_zero] at ho
      simp only [relocWire, ho, ite_true, runGates, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simpa using ho), List.getElem_ofFn]
      rfl
  | append_singleton C g ih =>
      rw [gatesWF_append, Bool.and_eq_true] at hC
      have hlen := runGates_length C (List.ofFn fun i : Fin 8 => (ρ (f i)).getLsbD j)
      simp only [List.length_ofFn] at hlen
      have hrel : ∀ o < 8 + C.length, relocWire f base o < base + C.length := by
        intro o ho
        unfold relocWire
        split
        · have := hf o (by omega); omega
        · omega
      intro o ho
      rw [List.map_append, evalLets_append, runGates_append]
      simp only [List.length_map, List.map_cons, List.map_nil, evalLets]
      simp only [List.length_append, List.length_cons, List.length_nil] at ho
      by_cases hlt : o < 8 + C.length
      · rw [ite_eq_right (Nat.ne_of_lt (hrel o hlt)), ih hC.1 o hlt,
          List.getD_append _ _ _ _ (by omega)]
      · have ho' : o = 8 + C.length := by omega
        subst ho'
        have hr : relocWire f base (8 + C.length) = base + C.length := by
          simp [relocWire]
        rw [hr, ite_eq_left rfl, AesGate.toWExp_eval_getLsbD _ _ _ _ _ hj,
          List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simp only [List.getD_cons_zero]
        refine AesGate.evalB_congr g _ hC.2 _ _ fun i hi => ?_
        exact ih hC.1 i hi

/-! ## 2. The S-box circuit -/

/-- Input `U i` of the S-box circuit of Boyar and Peralta: bit `7 - i` of the byte. -/
def bpU (i : Nat) : Nat := 7 - i
/-- The wire of the gate `T i` (`1 ≤ i ≤ 27`) of the top linear layer. -/
def bpT (i : Nat) : Nat := 7 + i
/-- The wire of the gate `M i` (`1 ≤ i ≤ 63`) of the middle layer. -/
def bpM (i : Nat) : Nat := 34 + i
/-- The wire of the gate `L i` (`0 ≤ i ≤ 29`) of the bottom linear layer. -/
def bpL (i : Nat) : Nat := 98 + i
/-- The wire of the output `S i` (`0 ≤ i ≤ 7`): bit `7 - i` of the S-box value. -/
def bpS (i : Nat) : Nat := 128 + i

/-- **The S-box circuit of Boyar and Peralta** (depth 16, 128 gates), over the eight inputs
    numbered `0, …, 7` by bit position; gate `t` binds the wire `8 + t`. -/
def aesSboxGates : List AesGate := [
  -- top linear layer
  .xor (bpU 0) (bpU 3), .xor (bpU 0) (bpU 5), .xor (bpU 0) (bpU 6), .xor (bpU 3) (bpU 5),
  .xor (bpU 4) (bpU 6), .xor (bpT 1) (bpT 5), .xor (bpU 1) (bpU 2), .xor (bpU 7) (bpT 6),
  .xor (bpU 7) (bpT 7), .xor (bpT 6) (bpT 7), .xor (bpU 1) (bpU 5), .xor (bpU 2) (bpU 5),
  .xor (bpT 3) (bpT 4), .xor (bpT 6) (bpT 11), .xor (bpT 5) (bpT 11), .xor (bpT 5) (bpT 12),
  .xor (bpT 9) (bpT 16), .xor (bpU 3) (bpU 7), .xor (bpT 7) (bpT 18), .xor (bpT 1) (bpT 19),
  .xor (bpU 6) (bpU 7), .xor (bpT 7) (bpT 21), .xor (bpT 2) (bpT 22), .xor (bpT 2) (bpT 10),
  .xor (bpT 20) (bpT 17), .xor (bpT 3) (bpT 16), .xor (bpT 1) (bpT 12),
  -- middle layer
  .and (bpT 13) (bpT 6), .and (bpT 23) (bpT 8), .xor (bpT 14) (bpM 1), .and (bpT 19) (bpU 7),
  .xor (bpM 4) (bpM 1), .and (bpT 3) (bpT 16), .and (bpT 22) (bpT 9), .xor (bpT 26) (bpM 6),
  .and (bpT 20) (bpT 17), .xor (bpM 9) (bpM 6), .and (bpT 1) (bpT 15), .and (bpT 4) (bpT 27),
  .xor (bpM 12) (bpM 11), .and (bpT 2) (bpT 10), .xor (bpM 14) (bpM 11), .xor (bpM 3) (bpM 2),
  .xor (bpM 5) (bpT 24), .xor (bpM 8) (bpM 7), .xor (bpM 10) (bpM 15), .xor (bpM 16) (bpM 13),
  .xor (bpM 17) (bpM 15), .xor (bpM 18) (bpM 13), .xor (bpM 19) (bpT 25),
  .xor (bpM 22) (bpM 23), .and (bpM 22) (bpM 20), .xor (bpM 21) (bpM 25),
  .xor (bpM 20) (bpM 21), .xor (bpM 23) (bpM 25), .and (bpM 28) (bpM 27),
  .and (bpM 26) (bpM 24), .and (bpM 20) (bpM 23), .and (bpM 27) (bpM 31),
  .xor (bpM 27) (bpM 25), .and (bpM 21) (bpM 22), .and (bpM 24) (bpM 34),
  .xor (bpM 24) (bpM 25), .xor (bpM 21) (bpM 29), .xor (bpM 32) (bpM 33),
  .xor (bpM 23) (bpM 30), .xor (bpM 35) (bpM 36), .xor (bpM 38) (bpM 40),
  .xor (bpM 37) (bpM 39), .xor (bpM 37) (bpM 38), .xor (bpM 39) (bpM 40),
  .xor (bpM 42) (bpM 41), .and (bpM 44) (bpT 6), .and (bpM 40) (bpT 8), .and (bpM 39) (bpU 7),
  .and (bpM 43) (bpT 16), .and (bpM 38) (bpT 9), .and (bpM 37) (bpT 17),
  .and (bpM 42) (bpT 15), .and (bpM 45) (bpT 27), .and (bpM 41) (bpT 10),
  .and (bpM 44) (bpT 13), .and (bpM 40) (bpT 23), .and (bpM 39) (bpT 19),
  .and (bpM 43) (bpT 3), .and (bpM 38) (bpT 22), .and (bpM 37) (bpT 20), .and (bpM 42) (bpT 1),
  .and (bpM 45) (bpT 4), .and (bpM 41) (bpT 2),
  -- bottom linear layer
  .xor (bpM 61) (bpM 62), .xor (bpM 50) (bpM 56), .xor (bpM 46) (bpM 48),
  .xor (bpM 47) (bpM 55), .xor (bpM 54) (bpM 58), .xor (bpM 49) (bpM 61),
  .xor (bpM 62) (bpL 5), .xor (bpM 46) (bpL 3), .xor (bpM 51) (bpM 59), .xor (bpM 52) (bpM 53),
  .xor (bpM 53) (bpL 4), .xor (bpM 60) (bpL 2), .xor (bpM 48) (bpM 51), .xor (bpM 50) (bpL 0),
  .xor (bpM 52) (bpM 61), .xor (bpM 55) (bpL 1), .xor (bpM 56) (bpL 0), .xor (bpM 57) (bpL 1),
  .xor (bpM 58) (bpL 8), .xor (bpM 63) (bpL 4), .xor (bpL 0) (bpL 1), .xor (bpL 1) (bpL 7),
  .xor (bpL 3) (bpL 12), .xor (bpL 18) (bpL 2), .xor (bpL 15) (bpL 9), .xor (bpL 6) (bpL 10),
  .xor (bpL 7) (bpL 9), .xor (bpL 8) (bpL 10), .xor (bpL 11) (bpL 14), .xor (bpL 11) (bpL 17),
  -- outputs
  .xor (bpL 6) (bpL 24), .xnor (bpL 16) (bpL 26), .xnor (bpL 19) (bpL 28),
  .xor (bpL 6) (bpL 21), .xor (bpL 20) (bpL 22), .xor (bpL 25) (bpL 29),
  .xnor (bpL 13) (bpL 27), .xnor (bpL 6) (bpL 23)]

/-- The wire of bit `b` of the S-box value. -/
def aesSboxOut (b : Nat) : Nat := bpS (7 - b)

/-- Every gate of the S-box circuit reads only the inputs and the gates before it. -/
theorem aesSboxGates_wf : gatesWF 8 aesSboxGates = true := by decide

/-- The S-box circuit has 128 gates. -/
theorem aesSboxGates_length : aesSboxGates.length = 128 := by simp [aesSboxGates]

set_option linter.style.native false in
/-- **The S-box circuit computes the AES S-box**, checked on each of the 256 bytes. -/
theorem aesSboxGates_table : ∀ x : Fin 256, ∀ b : Fin 8,
    (runGates (List.ofFn fun i : Fin 8 => (UInt8.ofNat x.val).toBitVec.getLsbD i.val)
        aesSboxGates).getD (aesSboxOut b.val) false =
      (AES128.sbox (UInt8.ofNat x.val)).toBitVec.getLsbD b.val := by
  native_decide

/-- The S-box circuit on any byte. -/
theorem aesSboxGates_byte (x : UInt8) (b : Nat) (hb : b < 8) :
    (runGates (List.ofFn fun i : Fin 8 => x.toBitVec.getLsbD i.val) aesSboxGates).getD
        (aesSboxOut b) false = (AES128.sbox x).toBitVec.getLsbD b := by
  have h := aesSboxGates_table ⟨x.toNat, x.toNat_lt⟩ ⟨b, hb⟩
  simpa only [UInt8.ofNat_toNat] using h

/-! ## 3. The SubBytes layer -/

/-- The S-box circuit on the byte position `k`: its inputs are the planes `8 k + i`, its gates
    bind the words numbered from `256 + 128 k`. -/
def aesSboxCopy (w k : Nat) : List (WExp w) :=
  aesSboxGates.map (AesGate.toWExp w (relocWire (fun i => 8 * k + i) (256 + 128 * k)))

/-- The S-box circuits on the byte positions below `m`. -/
def aesSubLetsUpTo (w m : Nat) : List (WExp w) :=
  (List.range m).flatMap (aesSboxCopy w)

/-- **The symbolic SubBytes layer**: the S-box circuits on the sixteen byte positions, over
    the input words numbered `0, …, 255`. -/
def aesSubLets (w : Nat) : List (WExp w) := aesSubLetsUpTo w 16

/-- The word of bit `b` of the S-box value at the byte position `k`. -/
def aesSubWire (k b : Nat) : Nat := 256 + 128 * k + (aesSboxOut b - 8)

/-- Each S-box circuit has 128 gates. -/
theorem aesSubLetsUpTo_length (w m : Nat) : (aesSubLetsUpTo w m).length = 128 * m := by
  induction m with
  | zero => simp [aesSubLetsUpTo]
  | succ m ih =>
      simp only [aesSubLetsUpTo, List.range_succ, List.flatMap_append, List.length_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih ⊢
      rw [ih]
      simp [aesSboxCopy, aesSboxGates_length]
      ring

/-- **The SubBytes layer in each lane**: lane `j` of the word of bit `b` of the S-box value at
    the byte position `k` is bit `b` of the S-box at the byte of lane `j` of the planes
    `8 k + i`. -/
theorem aesSubLetsUpTo_getLsbD (w : Nat) (ρ : Nat → BitVec w) (j : Nat) (hj : j < w) :
    ∀ m ≤ 16, ∀ k < m, ∀ o, 8 ≤ o → o < 136 →
      (evalLets ρ 256 (aesSubLetsUpTo w m) (256 + 128 * k + (o - 8))).getLsbD j =
        (runGates (List.ofFn fun i : Fin 8 => (ρ (8 * k + i)).getLsbD j) aesSboxGates).getD
          o false := by
  intro m
  induction m with
  | zero => intro _ k hk; omega
  | succ m ih =>
      intro hm k hk o ho8 ho
      have hsplit : aesSubLetsUpTo w (m + 1) = aesSubLetsUpTo w m ++ aesSboxCopy w m := by
        simp [aesSubLetsUpTo, List.range_succ, List.flatMap_append]
      rw [hsplit, evalLets_append, aesSubLetsUpTo_length]
      by_cases hkm : k < m
      · rw [evalLets_of_lt _ _ _ _ (by omega)]
        exact ih (by omega) k hkm o ho8 ho
      · have hk' : k = m := by omega
        subst hk'
        have hr : relocWire (fun i => 8 * k + i) (256 + 128 * k) o = 256 + 128 * k + (o - 8) := by
          simp [relocWire]; omega
        have h := evalLets_reloc_getLsbD w aesSboxGates aesSboxGates_wf (fun i => 8 * k + i)
          (256 + 128 * k) (fun i hi => by omega) (evalLets ρ 256 (aesSubLetsUpTo w k)) j hj o
          (by rw [aesSboxGates_length]; omega)
        rw [hr] at h
        unfold aesSboxCopy
        rw [h]
        congr 2
        grind [evalLets_of_lt]

/-! ## 4. Blocks and planes -/

/-- The word of width `w` whose lane `j` is `f j`. -/
def aesLanes (w : Nat) (f : Nat → Bool) : BitVec w :=
  (BitVec.ofBoolListLE ((List.range w).map f)).cast (by simp)

/-- Lane `j` of `aesLanes w f` is `f j`. -/
theorem aesLanes_getLsbD (w : Nat) (f : Nat → Bool) (j : Nat) (hj : j < w) :
    (aesLanes w f).getLsbD j = f j := by
  rw [aesLanes, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  simp [hj]

/-- Byte `k` of block `j` of the planes `ρ` from the plane numbered `off`: its bit `b` is lane
    `j` of the plane `off + 8 k + b`. -/
def aesByteAt {w : Nat} (ρ : Nat → BitVec w) (off j k : Nat) : UInt8 :=
  UInt8.ofBitVec (aesLanes 8 fun b => (ρ (off + 8 * k + b)).getLsbD j)

/-- Bit `b` of byte `k` of block `j` is lane `j` of the plane `off + 8 k + b`. -/
theorem aesByteAt_getLsbD {w : Nat} (ρ : Nat → BitVec w) (off j k b : Nat) (hb : b < 8) :
    (aesByteAt ρ off j k).toBitVec.getLsbD b = (ρ (off + 8 * k + b)).getLsbD j := by
  simp [aesByteAt, aesLanes_getLsbD _ _ _ hb]

/-- The state of block `j` in the planes `ρ` from the plane numbered `off`. -/
def aesUnpack {w : Nat} (ρ : Nat → BitVec w) (off j : Nat) : AES128.State :=
  fun k => aesByteAt ρ off j k.val

/-- The 128 planes of the states `B j` of `w` blocks: lane `j` of the plane `8 k + b` is bit
    `b` of byte `k` of `B j`. -/
def aesPack (w : Nat) (B : Nat → AES128.State) : Fin 128 → BitVec w :=
  fun p => aesLanes w fun j => ((B j) ⟨p.val / 8, by omega⟩).toBitVec.getLsbD (p.val % 8)

/-- **SubBytes in each lane**: lane `j` of the word of bit `b` of the S-box value at the byte
    position `k` is bit `b` of the S-box of byte `k` of block `j`. -/
theorem aesSubLets_getLsbD (w : Nat) (ρ : Nat → BitVec w) (j : Nat) (hj : j < w) (k b : Nat)
    (hk : k < 16) (hb : b < 8) :
    (evalLets ρ 256 (aesSubLets w) (aesSubWire k b)).getLsbD j =
      (AES128.sbox (aesByteAt ρ 0 j k)).toBitVec.getLsbD b := by
  have h := aesSubLetsUpTo_getLsbD w ρ j hj 16 le_rfl k hk (aesSboxOut b)
    (by simp only [aesSboxOut, bpS]; omega) (by simp only [aesSboxOut, bpS]; omega)
  rw [← aesSboxGates_byte _ b hb]
  refine h.trans ?_
  congr 2
  grind [aesByteAt_getLsbD]

/-! ## 5. The output planes -/

/-- The exclusive or of the listed words; the zero word for the empty list. -/
def xorAll {w : Nat} : List Nat → WExp w
  | [] => .const 0
  | [i] => .var i
  | i :: is => .bin .xor (.var i) (xorAll is)

/-- The value of `xorAll L` is the exclusive or of the listed words. -/
theorem xorAll_eval {w : Nat} (ρ : Nat → BitVec w) :
    ∀ L : List Nat, (xorAll L : WExp w).eval ρ = L.foldr (fun i acc => ρ i ^^^ acc) 0
  | [] => by simp [xorAll, WExp.eval]
  | [i] => by simp [xorAll, WExp.eval]
  | i :: i' :: is => by
      rw [xorAll.eq_3 i (i' :: is) (by simp)]
      simp only [WExp.eval, JasminBinOp.apply]
      rw [xorAll_eval ρ (i' :: is)]
      rfl

/-- Lane `j` of `xorAll L` is the exclusive or of lane `j` of the listed words. -/
theorem xorAll_eval_getLsbD {w : Nat} (ρ : Nat → BitVec w) (j : Nat) (hj : j < w) :
    ∀ L : List Nat, ((xorAll L : WExp w).eval ρ).getLsbD j =
      L.foldr (fun i acc => (ρ i).getLsbD j ^^ acc) false
  | [] => by simp [xorAll, WExp.eval]
  | [i] => by simp [xorAll, WExp.eval]
  | i :: i' :: is => by
      rw [xorAll.eq_3 i (i' :: is) (by simp)]
      simp only [WExp.eval, JasminBinOp.apply, BitVec.getLsbD_xor]
      rw [xorAll_eval_getLsbD ρ j hj (i' :: is)]
      rfl

/-- Expressions over the words numbered below `n`, bound from the word `n`, take their values
    at the words before them. -/
theorem evalLets_xorAll {w : Nat} : ∀ (Ls : List (List Nat)) (ρ : Nat → BitVec w) (n : Nat),
    (∀ L ∈ Ls, ∀ i ∈ L, i < n) → ∀ p < Ls.length,
      evalLets ρ n (Ls.map xorAll) (n + p) = (xorAll (Ls.getD p [])).eval ρ
  | [], _, _, _, p, hp => by simp at hp
  | L :: Ls, ρ, n, hL, p, hp => by
      have hL' : ∀ L' ∈ Ls, ∀ i ∈ L', i < n + 1 := fun L' h i hi => by
        have := hL L' (List.mem_cons_of_mem _ h) i hi
        omega
      have hc : ∀ L' : List Nat, (∀ i ∈ L', i < n) →
          L'.foldr (fun i acc => (if i = n then (xorAll L : WExp w).eval ρ else ρ i) ^^^ acc) 0 =
            L'.foldr (fun i acc => ρ i ^^^ acc) 0 := by
        intro L' hL''
        induction L' with
        | nil => rfl
        | cons i is ih =>
            have hi := hL'' i List.mem_cons_self
            simp only [List.foldr_cons, Nat.ne_of_lt hi, ite_false]
            rw [ih fun i' h => hL'' i' (List.mem_cons_of_mem _ h)]
      cases p with
      | zero =>
          simp only [List.map_cons, evalLets, Nat.add_zero, List.getD_cons_zero]
          rw [evalLets_of_lt _ _ _ _ (by omega)]
          simp
      | succ q =>
          simp only [List.map_cons, evalLets, List.getD_cons_succ]
          rw [show n + (q + 1) = (n + 1) + q by omega,
            evalLets_xorAll Ls _ (n + 1) hL' q (by simpa using hp),
            xorAll_eval _ (Ls.getD q []), xorAll_eval ρ (Ls.getD q [])]
          refine hc _ fun i hi => ?_
          have hq : q < Ls.length := by simpa using hp
          exact hL _ (List.mem_cons_of_mem _
            (by rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq)) i hi

/-- The byte position read by byte `(r, c)` (row `r mod 4`, column `c`) after ShiftRows. -/
def aesSrc (r c : Nat) : Nat := 4 * ((c + r) % 4) + r % 4

/-- The byte position after ShiftRows is a byte position. -/
theorem aesSrc_lt (r c : Nat) : aesSrc r c < 16 := by
  unfold aesSrc
  omega

/-- The SubBytes words are numbered below the output planes. -/
theorem aesSubWire_lt (k b : Nat) (hk : k < 16) : aesSubWire k b < 2304 := by
  unfold aesSubWire aesSboxOut bpS
  omega

/-- The bits of a byte whose exclusive or is bit `b` of its product by `x` in GF(2⁸). -/
def xtimeSrc (b : Nat) : List Nat :=
  if b = 0 then [7] else if b = 1 ∨ b = 3 ∨ b = 4 then [b - 1, 7] else [b - 1]

/-- The words whose exclusive or is the output plane `p = 8 k + b`, byte `k` at row `r` and
    column `c`: for the round, bit `b` of `xtime (y r c ⊕ y (r+1) c) ⊕ y (r+1) c ⊕ y (r+2) c ⊕
    y (r+3) c` and the key plane, `y` the bytes after SubBytes and ShiftRows; for the final round,
    bit `b` of `y r c` and the key plane. -/
def aesOutWires (final : Bool) (p : Nat) : List Nat :=
  let k := p / 8
  let b := p % 8
  let r := k % 4
  let c := k / 4
  if final then [aesSubWire (aesSrc r c) b, 128 + p]
  else (xtimeSrc b).flatMap (fun b' =>
      [aesSubWire (aesSrc r c) b', aesSubWire (aesSrc (r + 1) c) b']) ++
    [aesSubWire (aesSrc (r + 1) c) b, aesSubWire (aesSrc (r + 2) c) b,
      aesSubWire (aesSrc (r + 3) c) b, 128 + p]

/-- **The symbolic output planes**: plane `p` binds the word numbered `2304 + p`. -/
def aesOutLets (w : Nat) (final : Bool) : List (WExp w) :=
  ((List.range 128).map (aesOutWires final)).map xorAll

/-- The output planes read only the input words and the SubBytes words. -/
theorem aesOutWires_lt (final : Bool) (p : Nat) (hp : p < 128) :
    ∀ i ∈ aesOutWires final p, i < 2304 := by
  intro i hi
  unfold aesOutWires at hi
  have := aesSubWire_lt
  have := aesSrc_lt
  split at hi <;> simp [xtimeSrc] at hi <;> grind

/-! ## 6. The round on bytes -/

/-- The round, or the final round when `final` holds. -/
def aesRoundSpec (final : Bool) (s rk : AES128.State) : AES128.State :=
  if final then AES128.aesFinalRound s rk else AES128.aesRound s rk

/-- Byte `k` of the round, at row `r` and column `c`. -/
theorem aesRound_apply (s' rk' : Nat → UInt8) (k : Fin 16) :
    AES128.aesRound (fun i => s' i.val) (fun i => rk' i.val) k =
      AES128.xtime (AES128.sbox (s' (aesSrc (k.val % 4) (k.val / 4)))) ^^^
        AES128.mul3 (AES128.sbox (s' (aesSrc (k.val % 4 + 1) (k.val / 4)))) ^^^
        AES128.sbox (s' (aesSrc (k.val % 4 + 2) (k.val / 4))) ^^^
        AES128.sbox (s' (aesSrc (k.val % 4 + 3) (k.val / 4))) ^^^ rk' k.val := by
  rw [← UInt8.toBitVec_inj]
  fin_cases k <;>
    simp [AES128.aesRound, AES128.addRoundKey, AES128.mixColumns, AES128.shiftRows,
      AES128.subBytes, AES128.stateGet, AES128.mixColumn, aesSrc] <;> ac_rfl

/-- Byte `k` of the final round, at row `r` and column `c`. -/
theorem aesFinalRound_apply (s' rk' : Nat → UInt8) (k : Fin 16) :
    AES128.aesFinalRound (fun i => s' i.val) (fun i => rk' i.val) k =
      AES128.sbox (s' (aesSrc (k.val % 4) (k.val / 4))) ^^^ rk' k.val := by
  fin_cases k <;>
    simp [AES128.aesFinalRound, AES128.addRoundKey, AES128.shiftRows, AES128.subBytes,
      AES128.stateGet, aesSrc]

/-- Bit `b` of the product of a byte by `x` in GF(2⁸). -/
theorem xtime_getLsbD (u : UInt8) (b : Nat) (hb : b < 8) :
    (AES128.xtime u).toBitVec.getLsbD b =
      (xtimeSrc b).foldr (fun b' acc => u.toBitVec.getLsbD b' ^^ acc) false := by
  obtain ⟨x⟩ := u
  have hc : (UInt8.ofBitVec x &&& 0x80 != 0) = x.getLsbD 7 := by
    rw [show (UInt8.ofBitVec x &&& 0x80 != 0) = (x &&& 0x80 != 0#8) from rfl]
    bv_decide
  unfold AES128.xtime
  have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    split <;> rename_i h <;> simp only [hc] at h <;>
    simp only [xtimeSrc, Nat.reduceEqDiff, ↓reduceIte, or_false, or_true,
      Nat.reduceSub, List.foldr_cons, List.foldr_nil, Bool.xor_false] <;> bv_decide

/-- **The output planes on bits**: at wire values `V` holding, at lane `j`, the bits of the
    S-box values of block `j` and the key planes, the exclusive or of the words of the output
    plane `p` is the bit of the round of block `j` that the plane holds. -/
theorem aesOutWires_bits {w : Nat} (final : Bool) (ρ : Nat → BitVec w) (j : Nat)
    (V : Nat → Bool)
    (hsub : ∀ k < 16, ∀ b < 8,
      V (aesSubWire k b) = (AES128.sbox (aesByteAt ρ 0 j k)).toBitVec.getLsbD b)
    (hkey : ∀ q < 128, V (128 + q) = (ρ (128 + q)).getLsbD j) (p : Nat) (hp : p < 128) :
    (aesOutWires final p).foldr (fun i acc => V i ^^ acc) false =
      ((aesRoundSpec final (aesUnpack ρ 0 j) (aesUnpack ρ 128 j))
        ⟨p / 8, by omega⟩).toBitVec.getLsbD (p % 8) := by
  obtain ⟨k, b, hk, hb, rfl⟩ : ∃ k b, k < 16 ∧ b < 8 ∧ p = 8 * k + b :=
    ⟨p / 8, p % 8, by omega, by omega, by omega⟩
  have hdiv : (8 * k + b) / 8 = k := by omega
  have hmod : (8 * k + b) % 8 = b := by omega
  have hkey' : V (128 + (8 * k + b)) = (aesByteAt ρ 128 j k).toBitVec.getLsbD b := by
    rw [hkey _ hp, aesByteAt_getLsbD _ _ _ _ _ hb, Nat.add_assoc]
  have hbc : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  cases final
  · simp only [aesOutWires, hdiv, hmod, Bool.false_eq_true, ite_false, aesRoundSpec]
    have hr := aesRound_apply (aesByteAt ρ 0 j) (aesByteAt ρ 128 j) ⟨k, hk⟩
    change AES128.aesRound (aesUnpack ρ 0 j) (aesUnpack ρ 128 j) ⟨k, hk⟩ = _ at hr
    rw [hr]
    simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor, AES128.mul3, xtime_getLsbD _ _ hb]
    rcases hbc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [xtimeSrc, Nat.reduceEqDiff, ↓reduceIte, or_false, or_true, Nat.reduceSub,
        List.foldr_cons, List.foldr_nil, List.flatMap_cons,
        List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, Bool.xor_false,
        hsub, aesSrc_lt, Nat.reduceLT, hkey'] <;>
      bv_decide
  · simp only [aesOutWires, hdiv, hmod, ite_true, aesRoundSpec]
    have hr := aesFinalRound_apply (aesByteAt ρ 0 j) (aesByteAt ρ 128 j) ⟨k, hk⟩
    change AES128.aesFinalRound (aesUnpack ρ 0 j) (aesUnpack ρ 128 j) ⟨k, hk⟩ = _ at hr
    rw [hr]
    simp only [List.foldr_cons, List.foldr_nil, Bool.xor_false, hsub _ (aesSrc_lt _ _) _ hb,
      hkey', UInt8.toBitVec_xor, BitVec.getLsbD_xor]

/-- **The let-list in each lane**: lane `j` of the word numbered `2304 + p` after the SubBytes
    layer and the output planes is the bit of the round of block `j` that the plane `p` holds. -/
theorem aesLets_getLsbD (w : Nat) (final : Bool) (ρ : Nat → BitVec w) (p : Nat) (hp : p < 128)
    (j : Nat) (hj : j < w) :
    (evalLets ρ 256 (aesSubLets w ++ aesOutLets w final) (2304 + p)).getLsbD j =
      ((aesRoundSpec final (aesUnpack ρ 0 j) (aesUnpack ρ 128 j))
        ⟨p / 8, by omega⟩).toBitVec.getLsbD (p % 8) := by
  have hlen : (aesSubLets w).length = 2048 := by simp [aesSubLets, aesSubLetsUpTo_length]
  rw [evalLets_append, hlen]
  unfold aesOutLets
  rw [evalLets_xorAll _ _ (256 + 2048) ?_ p (by simpa using hp)]
  · rw [xorAll_eval_getLsbD _ j hj]
    have hget : ((List.range 128).map (aesOutWires final)).getD p [] = aesOutWires final p := by
      simp [hp]
    rw [hget]
    exact aesOutWires_bits final ρ j (fun i => (evalLets ρ 256 (aesSubLets w) i).getLsbD j)
      (fun k hk b hb => aesSubLets_getLsbD w ρ j hj k b hk hb)
      (fun q hq => by rw [evalLets_of_lt _ _ _ _ (by omega)]) p hp
  · intro L hL i hi
    simp only [List.mem_map, List.mem_range] at hL
    obtain ⟨p', hp', rfl⟩ := hL
    exact aesOutWires_lt final p' hp' i hi

/-! ## 7. The program -/

/-- The input context of the round: the input array of the 128 state planes and the 128 key
    planes, and the output array of the 128 planes of the result. -/
abbrev aesInCtxt (w : Nat) : Ctxt jasminDialect := [.stackArr w 256, .stackArr w 128]

/-- The stores of the output planes: the word numbered `2304 + p` at the index `p`. -/
def aesStores : List (Nat × Nat) := (List.range 128).map fun p => (p, 2304 + p)

/-- **The bitsliced round as a `jasminDialect` program**: the loads of the 256 planes of the
    input array as the words numbered `0, …, 255`, the compiled SubBytes layer and output planes
    from the word numbered `256`, and the stores of the 128 output planes into the output array
    at register indices; the final round when `final` holds. -/
def aesBody (w : Nat) (final : Bool) : Com jasminDialect (aesInCtxt w) (.stackArr w 128) :=
  genLoad Var.here 0 fun ρ0 v0 =>
  genLoads (List.range' 1 255) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLetsR (aesSubLets w ++ aesOutLets w final) 256 env1 fun ρ2 env2 =>
  genStoresIdx aesStores (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2

/-- The bitsliced AES round on `w` blocks. -/
def aesRoundBody (w : Nat) : Com jasminDialect (aesInCtxt w) (.stackArr w 128) := aesBody w false

/-- The bitsliced final AES round on `w` blocks. -/
def aesFinalRoundBody (w : Nat) : Com jasminDialect (aesInCtxt w) (.stackArr w 128) :=
  aesBody w true

/-! ## 8. Values -/

/-- The stores write the word numbered `2304 + p` at each index `p` of the output array. -/
theorem aesStores_foldl {w : Nat} (g : Nat → BitVec w) (O : Fin 128 → BitVec w) :
    aesStores.foldl (fun A q => stackSet A q.1 (g q.2)) O = fun p => g (2304 + p.val) := by
  have key : ∀ m ≤ 128, ((List.range m).map fun p => (p, 2304 + p)).foldl
      (fun A q => stackSet A q.1 (g q.2)) O =
        fun p : Fin 128 => if p.val < m then g (2304 + p.val) else O p := by
    intro m
    induction m with
    | zero => intro _; funext p; simp
    | succ m ih =>
        intro hm
        rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        rw [show m = (⟨m, by omega⟩ : Fin 128).val from rfl, stackSet_fin]
        funext p
        by_cases h : p = ⟨m, by omega⟩
        · subst h; simp
        · have : p.val ≠ m := fun h' => h (Fin.ext h')
          simp only [h, ite_false]
          grind
  rw [aesStores, key 128 le_rfl]
  funext p
  simp

/-- `aesLanes w f` reads `f` only below `w`. -/
theorem aesLanes_congr (w : Nat) (f g : Nat → Bool) (h : ∀ j < w, f j = g j) :
    aesLanes w f = aesLanes w g :=
  BitVec.eq_of_getLsbD_eq fun j hj => by
    rw [aesLanes_getLsbD _ _ _ hj, aesLanes_getLsbD _ _ _ hj, h j hj]

/-- **The value of the bitsliced template**: at the input array `S` of the state planes and
    the key planes and any contents `O` of the output array, the program returns the planes of
    the round (the final round when `final` holds) of each of the `w` blocks. -/
theorem aesBody_value (w : Nat) (final : Bool) (S : Fin 256 → BitVec w)
    (O : Fin 128 → BitVec w) :
    (aesBody w final).denote (.cons S (.cons O .nil)) =
      aesPack w fun j =>
        aesRoundSpec final (aesUnpack (stackGet S) 0 j) (aesUnpack (stackGet S) 128 j) := by
  have hL : ∀ q ∈ aesStores, q.1 < 2 ^ 64 := by
    intro q hq
    simp only [aesStores, List.mem_map, List.mem_range] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    simp only
    omega
  unfold aesBody
  refine genLoad_denote _ 0 _ _ S rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 S (hρ0 _ _) (fun _ => stackGet S (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLetsR_denote _ 256 env1 _ V1 _ henv1 _ fun ρ2 V2 env2 hρ2 henv2 => ?_
  refine (genStoresIdx_denote aesStores (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2 V2 O
    ((hρ2 _ _).trans ((hρ1 _ _).trans (hρ0 _ _))) _ henv2 hL).trans ?_
  rw [aesStores_foldl]
  set ρ := loadVals S (fun _ => stackGet S (BitVec.ofNat 64 0).toNat) 1 (List.range' 1 255)
    with hρdef
  have hagree : ∀ i < 256, ρ i = stackGet S i := by
    intro i hi
    rw [hρdef, loadVals_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
  have hun : ∀ off j, off ≤ 128 → aesUnpack ρ off j = aesUnpack (stackGet S) off j := by
    intro off j hoff
    funext k
    simp only [aesUnpack, aesByteAt]
    have hk := k.isLt
    exact congrArg UInt8.ofBitVec
      (aesLanes_congr 8 _ _ fun b hb => by rw [hagree _ (by omega)])
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [aesLets_getLsbD w final ρ p.val p.isLt j hj, aesPack, aesLanes_getLsbD _ _ _ hj,
    hun 0 j (by omega), hun 128 j le_rfl]

/-- **The value of the bitsliced AES round**: the program returns the planes of
    `AES128.aesRound` of each of the `w` blocks of the state planes, at the round key of each
    block in the key planes, whatever the contents `O` of the output array. -/
theorem aesRoundBody_value (w : Nat) (S : Fin 256 → BitVec w) (O : Fin 128 → BitVec w) :
    (aesRoundBody w).denote (.cons S (.cons O .nil)) =
      aesPack w fun j =>
        AES128.aesRound (aesUnpack (stackGet S) 0 j) (aesUnpack (stackGet S) 128 j) :=
  aesBody_value w false S O

/-- **The value of the bitsliced final AES round**: the program returns the planes of
    `AES128.aesFinalRound` of each of the `w` blocks, whatever the contents `O` of the output
    array. -/
theorem aesFinalRoundBody_value (w : Nat) (S : Fin 256 → BitVec w) (O : Fin 128 → BitVec w) :
    (aesFinalRoundBody w).denote (.cons S (.cons O .nil)) =
      aesPack w fun j =>
        AES128.aesFinalRound (aesUnpack (stackGet S) 0 j) (aesUnpack (stackGet S) 128 j) :=
  aesBody_value w true S O

/-! ## 9. Events -/

/-- **The events of the bitsliced template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem aesBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w : Nat)
    (final : Bool) : LeakFixed (jLeakModel Pj) (aesBody w final) := by
  unfold aesBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

/-- The events of the bitsliced AES round are fixed. -/
theorem aesRoundBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w : Nat) :
    LeakFixed (jLeakModel Pj) (aesRoundBody w) :=
  aesBody_events Pj hV w false

/-- The events of the bitsliced final AES round are fixed. -/
theorem aesFinalRoundBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w : Nat) :
    LeakFixed (jLeakModel Pj) (aesFinalRoundBody w) :=
  aesBody_events Pj hV w true

end CatCrypt.Crypto.SecureCompilation.HashTemplate
