/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
public import HaxLean.Value

@[expose] public section

set_option autoImplicit false

/-!
# The System V layout of a compiled function

An `AbiLayout` reads a hax environment and a hax result off address-machine states
(`Ascent.AddrMem.AState`) under the System V calling convention of the v0 route set of the
general compiler theorem: each source parameter is a `u64` scalar held in an argument
register or a word array passed by pointer in an argument register, a list of named
constants completes the environment, and the result is read back from registers and from
the words at the entry pointers after the run.

The layout also states the separation the compiled bytes rely on: the pointer regions are
pairwise disjoint and disjoint from the stack words the body uses below the entry `%rsp`,
and the runtime counts stay within stated bounds.

## Main results

* `wordsAt` — the words at `base + 8 j`, `j < k`, as source integers.
* `ArgKind`, `AbiArg`, `AbiArg.read` — a parameter, its register and the value it denotes.
* `ResultKind`, `ResultKind.read` — the read-back of a result from the entry and exit states.
* `AbiLayout` — parameters, constants, result, count bounds and the stack frame.
* `AbiLayout.Regions` — the count bounds and the separation of the pointer regions and the
  frame at an entry state.
* `AbiLayout.EnvOf` — a hax environment binding each parameter to the value its register
  denotes, each constant to its value, and no other name.
* `AbiLayout.canonEnv`, `AbiLayout.envOf_canonEnv` — the canonical environment of an entry
  state, which `EnvOf` admits when the names of the layout are pairwise distinct.
* `AbiLayout.ResultOf` — a source value equals the read-back of the result.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 Disjoint8)
open _root_.Hax (Value Env)

/-- The `k` words at `base + 8 j`, `j < k`, of the memory `m`, each as a source integer. -/
def wordsAt (m : AMem) (base : BitVec 64) (k : Nat) : List Value :=
  (List.range k).map fun j => .int (read64 m (base + BitVec.ofNat 64 (8 * j))).toNat

/-- How a source parameter is passed: a `u64` scalar in its register, or an array of `n`
    words at the address its register holds. -/
inductive ArgKind where
  /-- A `u64` scalar held in the register. -/
  | scalar
  /-- An array of `n` `u64` words at the address the register holds. -/
  | words (n : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A source parameter: its name in the hax environment, the System V register that
    carries it (`"%rdi"`, `"%rsi"`, `"%rdx"`, `"%rcx"`, `"%r8"`, `"%r9"`) and its kind. -/
structure AbiArg where
  /-- The parameter name in the hax environment. -/
  name : String
  /-- The argument register, in the register naming of `AState.regs`. -/
  reg : String
  /-- Scalar or word array. -/
  kind : ArgKind
  deriving Repr, DecidableEq, Inhabited

/-- The source value a parameter denotes at the state `sa`: the register as an integer for
    a scalar, the words at the register's address for an array. -/
def AbiArg.read (a : AbiArg) (sa : AState) : Value :=
  match a.kind with
  | .scalar => .int (sa.regs a.reg).toNat
  | .words n => .array (wordsAt sa.mem (sa.regs a.reg) n)

/-- The pointer region of a parameter: its register and its length in words, for an
    array parameter. -/
def AbiArg.region (a : AbiArg) : Option (String × Nat) :=
  match a.kind with
  | .scalar => none
  | .words n => some (a.reg, n)

/-- How a result is read back after the run. -/
inductive ResultKind where
  /-- The exit value of a register, as an integer. -/
  | reg (r : String)
  /-- The `n` words at the entry value of the register `r`, read in the exit memory. -/
  | words (r : String) (n : Nat)
  /-- The word at the entry value of `r` plus `8` times the entry value of `i`, read in the
      exit memory. -/
  | wordAt (r i : String)
  /-- A tuple of read-backs. -/
  | tuple (ks : List ResultKind)
  deriving Repr, Inhabited

mutual

/-- The source value a result read-back denotes, from the entry state `sa` and the exit
    state `sa'`. -/
def ResultKind.read (sa sa' : AState) : ResultKind → Value
  | .reg r => .int (sa'.regs r).toNat
  | .words r n => .array (wordsAt sa'.mem (sa.regs r) n)
  | .wordAt r i =>
      .int (read64 sa'.mem (sa.regs r + BitVec.ofNat 64 (8 * (sa.regs i).toNat))).toNat
  | .tuple ks => .tuple (ResultKind.readList sa sa' ks)

/-- `ResultKind.read` on each entry of a list. -/
def ResultKind.readList (sa sa' : AState) : List ResultKind → List Value
  | [] => []
  | k :: ks => ResultKind.read sa sa' k :: ResultKind.readList sa sa' ks

end

/-- The layout of a compiled function under the System V calling convention: its
    parameters, the constants that complete the source environment, the read-back of its
    result, upper bounds on scalar registers, and the stack words its body uses, as the
    offsets `[frameLo, frameHi]` from the entry `%rsp`. -/
structure AbiLayout where
  /-- The parameters, each with its register and kind. -/
  args : List AbiArg
  /-- Names bound to fixed values in the source environment. -/
  consts : List (String × Value)
  /-- The read-back of the result. -/
  result : ResultKind
  /-- Upper bounds on the entry value of registers, such as a runtime count at most the
      length of the arrays it indexes. -/
  bounds : List (String × Nat)
  /-- The lowest stack offset from the entry `%rsp` the body uses. -/
  frameLo : Int
  /-- The highest stack offset from the entry `%rsp` the body uses. -/
  frameHi : Int
  deriving Repr, Inhabited

namespace AbiLayout

/-- The pointer regions of a layout: register and length in words of each array
    parameter, in parameter order. -/
def regions (σ : AbiLayout) : List (String × Nat) := σ.args.filterMap AbiArg.region

/-- The entry conditions of a layout at the state `sa`: every bounded register is within its
    bound; the words of two distinct pointer regions are pairwise disjoint; and every word of
    a pointer region is disjoint from every stack word `%rsp + o`, `frameLo ≤ o ≤ frameHi`. -/
def Regions (σ : AbiLayout) (sa : AState) : Prop :=
  (∀ b ∈ σ.bounds, (sa.regs b.1).toNat ≤ b.2)
    ∧ (∀ (i j : Nat) (p q : String × Nat), i ≠ j → σ.regions[i]? = some p →
        σ.regions[j]? = some q → ∀ k k', k < p.2 → k' < q.2 →
          Disjoint8 (sa.regs p.1 + BitVec.ofNat 64 (8 * k))
            (sa.regs q.1 + BitVec.ofNat 64 (8 * k')))
    ∧ (∀ p ∈ σ.regions, ∀ k, k < p.2 → ∀ o : Int, σ.frameLo ≤ o → o ≤ σ.frameHi →
        Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 o)
          (sa.regs p.1 + BitVec.ofNat 64 (8 * k)))

/-- The names a layout binds in the source environment: the parameters, then the
    constants. -/
def envNames (σ : AbiLayout) : List String := σ.args.map (·.name) ++ σ.consts.map (·.1)

/-- The source environment `env` corresponds to the entry state `sa`: each parameter is
    bound to the value its register denotes (`AbiArg.read`), each constant to its value, and
    no other name is bound. -/
def EnvOf (σ : AbiLayout) (sa : AState) (env : Env) : Prop :=
  (∀ a ∈ σ.args, env a.name = some (a.read sa)) ∧ (∀ c ∈ σ.consts, env c.1 = some c.2) ∧
    ∀ y, (env y).isSome → y ∈ σ.envNames

/-- **The canonical source environment** of the entry state `sa`: the first parameter named
    `y` bound to the value its register denotes, otherwise the value of the first constant
    named `y`. -/
def canonEnv (σ : AbiLayout) (sa : AState) : Env := fun y =>
  match σ.args.find? (·.name == y) with
  | some a => some (a.read sa)
  | none => (σ.consts.find? (·.1 == y)).map (·.2)

/-- Two members of a list with the same image under a map without repeated values are
    equal. -/
private theorem eq_of_mem_of_nodup_map {α β : Type} {f : α → β} : ∀ {l : List α},
    (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | a :: l, h, x, y, hx, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd ⟨y, hy', hxy.symm⟩ h.1
    · exact absurd ⟨x, hx', hxy⟩ h.1
    · exact eq_of_mem_of_nodup_map h.2 hx' hy' hxy

/-- When the names of the layout are pairwise distinct, the canonical environment is the
    one the layout reads off the entry state. -/
theorem envOf_canonEnv (σ : AbiLayout) (h : σ.envNames.Nodup) (sa : AState) :
    σ.EnvOf sa (σ.canonEnv sa) := by
  have hA : (σ.args.map (·.name)).Nodup := (List.nodup_append.mp h).1
  have hC : (σ.consts.map (·.1)).Nodup := (List.nodup_append.mp h).2.1
  have hD := (List.nodup_append.mp h).2.2
  refine ⟨fun a ha => ?_, fun c hc => ?_, fun y hy => ?_⟩
  · have hf : (σ.args.find? (·.name == a.name)).isSome := by
      rw [List.find?_isSome]; exact ⟨a, ha, by simp⟩
    obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hf
    have hn : a'.name = a.name := by simpa using List.find?_some ha'
    have e : a' = a := eq_of_mem_of_nodup_map hA (List.mem_of_find?_eq_some ha') ha hn
    subst e
    simp [canonEnv, ha']
  · have hnone : σ.args.find? (·.name == c.1) = none := by
      rw [List.find?_eq_none]
      intro a ha hac
      exact hD a.name (List.mem_map_of_mem ha) c.1 (List.mem_map_of_mem hc) (by simpa using hac)
    have hf : (σ.consts.find? (·.1 == c.1)).isSome := by
      rw [List.find?_isSome]; exact ⟨c, hc, by simp⟩
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hf
    have hn : c'.1 = c.1 := by simpa using List.find?_some hc'
    have e : c' = c := eq_of_mem_of_nodup_map hC (List.mem_of_find?_eq_some hc') hc hn
    subst e
    simp [canonEnv, hnone, hc']
  · unfold canonEnv at hy
    unfold envNames
    split at hy
    · rename_i a ha
      have hn : a.name = y := by simpa using List.find?_some ha
      exact List.mem_append_left _ (hn ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some ha))
    · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (by simpa using hy :
        (σ.consts.find? (·.1 == y)).isSome)
      have hn : c.1 = y := by simpa using List.find?_some hc
      exact List.mem_append_right _ (hn ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hc))

/-- The source value `v` is the read-back of the result from the entry state `sa` and the
    exit state `sa'`. -/
def ResultOf (σ : AbiLayout) (sa sa' : AState) (v : Value) : Prop :=
  v = σ.result.read sa sa'

end AbiLayout

end CatCrypt.Crypto.SecureCompilation.Haxc
