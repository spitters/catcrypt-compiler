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
general compiler theorem: each source parameter is a `u64` scalar or a word array passed by
pointer, carried in an argument register or in a stack word `%rsp + 8 k` at entry (the
seventh and later integer arguments), a list of named
constants completes the environment, and the result is read back from registers and from
the words at the entry pointers after the run.

The layout also states the separation the compiled bytes rely on: the pointer regions are
pairwise disjoint and disjoint from the stack words the body uses below the entry `%rsp`,
and the runtime counts stay within stated bounds.

## Main results

* `wordsAt` — the words at `base + 8 j`, `j < k`, as source integers.
* `ArgKind`, `AbiArg`, `AbiArg.read` — a parameter, its register and the value it denotes.
* `stackArgReg`, `stackArgReg_inj`, `ne_stackArgReg` — the carrier name of a parameter in
  the stack word `%rsp + 8 k`.
* `AbiLayout.StackIn`, `AbiLayout.StackWF`, `AbiLayout.RegCarried` — the stack parameters
  at an entry state, their placement above the return address and the frame, and the
  layouts without stack parameters, at which both hold (`stackIn_of_regCarried`,
  `stackWF_of_regCarried`), decided by `regCarriedB` (`stackIn_of_regCarriedB`).
* `ResultKind`, `ResultKind.read` — the read-back of a result from the entry and exit states.
* `AbiLayout` — parameters, constants, result, count bounds and the stack frame.
* `AbiLayout.argPub`, `AbiLayout.pubRegions`, `AbiLayout.PubAgree` — the public parameters
  and the public array regions of a layout, and the agreement of two entry states on the
  stack pointer, the public parameter registers and the words of the public arrays.
* `AbiLayout.pubAgree_iff_of_pubWords_nil`, `AbiLayout.PubAgree.of_pubWords_nil` — without
  public arrays, `PubAgree` is agreement on the stack pointer and the public registers.
* `AbiLayout.PubAgree.wordsAt_eq` — equal words on each public array region.
* `AbiLayout.Regions`, `AbiLayout.Regions.stackIn` — the count bounds, the separation of
  the pointer regions and the frame, and the stack parameters at an entry state.
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

/-- **The carrier name of a stack parameter**: the name `"%rsp+8k"` under which a layout
    carries the parameter that the caller passes in the stack word `%rsp + 8 k` at entry, as
    System V passes the seventh and later integer arguments (`k ≥ 1`). No machine register
    has this name: the entry state holds the word in the register file under it, which
    `AbiLayout.StackIn` ties to the memory, and every definition over `AbiArg.reg` reads a
    stack parameter as it reads a register parameter. -/
def stackArgReg (k : Nat) : String := "%rsp+" ++ toString (8 * k)

/-- Distinct stack words have distinct carrier names. -/
theorem stackArgReg_inj {j k : Nat} (h : stackArgReg j = stackArgReg k) : j = k := by
  have h1 := congrArg String.toList h
  simp only [stackArgReg, String.toList_append, Nat.toString_eq_ofList_toDigits,
    String.toList_ofList, List.append_cancel_left_eq] at h1
  have h2 := congrArg (Nat.ofDigitChars 10 · 0) h1
  simp only [Nat.ofDigitChars_ten_toDigits] at h2
  omega

/-- A name whose characters do not begin with `%rsp+` is the carrier name of no stack word;
    every System V register name is such a name. -/
theorem ne_stackArgReg {r : String} (h : ¬ "%rsp+".toList <+: r.toList) (k : Nat) :
    r ≠ stackArgReg k := by
  rintro rfl
  exact h ⟨(toString (8 * k)).toList, by simp [stackArgReg]⟩

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
  /-- The registers of the array parameters whose words are public data, such as a table of
      public indices. -/
  pubWords : List String := []
  deriving Repr, Inhabited

namespace AbiLayout

/-- The pointer regions of a layout: register and length in words of each array
    parameter, in parameter order. -/
def regions (σ : AbiLayout) : List (String × Nat) := σ.args.filterMap AbiArg.region

/-- A parameter is public under the layout `σ`: an array parameter, whose register holds an
    address, or a scalar parameter whose register carries a bound of `σ`. -/
def argPub (σ : AbiLayout) (a : AbiArg) : Bool :=
  match a.kind with
  | .words _ => true
  | .scalar => σ.bounds.any (·.1 == a.reg)

/-- The public array regions of a layout: register and length in words of each array
    parameter whose register is in `pubWords`, in parameter order. -/
def pubRegions (σ : AbiLayout) : List (String × Nat) :=
  (σ.args.filter fun a => σ.pubWords.contains a.reg).filterMap AbiArg.region

/-- Two entry states agree on the public data of the layout: the stack pointer, the
    register of each public parameter, and the words of each public array, read at the
    address its register holds in each state. -/
structure PubAgree (σ : AbiLayout) (s₁ s₂ : AState) : Prop where
  /-- The stack pointers are equal. -/
  rsp : s₁.regs "%rsp" = s₂.regs "%rsp"
  /-- The register of each public parameter is equal. -/
  regs : ∀ a ∈ σ.args, σ.argPub a = true → s₁.regs a.reg = s₂.regs a.reg
  /-- The words of each array parameter whose register is in `pubWords` are equal. -/
  words : ∀ a ∈ σ.args, ∀ n, a.kind = .words n → a.reg ∈ σ.pubWords →
    wordsAt s₁.mem (s₁.regs a.reg) n = wordsAt s₂.mem (s₂.regs a.reg) n

/-- `PubAgree` as a conjunction. -/
theorem pubAgree_iff (σ : AbiLayout) (s₁ s₂ : AState) :
    σ.PubAgree s₁ s₂ ↔ s₁.regs "%rsp" = s₂.regs "%rsp" ∧
      (∀ a ∈ σ.args, σ.argPub a = true → s₁.regs a.reg = s₂.regs a.reg) ∧
      ∀ a ∈ σ.args, ∀ n, a.kind = .words n → a.reg ∈ σ.pubWords →
        wordsAt s₁.mem (s₁.regs a.reg) n = wordsAt s₂.mem (s₂.regs a.reg) n :=
  ⟨fun h => ⟨h.rsp, h.regs, h.words⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- A layout without public arrays: `PubAgree` is agreement on the stack pointer and the
    register of each public parameter. -/
theorem pubAgree_iff_of_pubWords_nil {σ : AbiLayout} (h : σ.pubWords = []) (s₁ s₂ : AState) :
    σ.PubAgree s₁ s₂ ↔ s₁.regs "%rsp" = s₂.regs "%rsp" ∧
      ∀ a ∈ σ.args, σ.argPub a = true → s₁.regs a.reg = s₂.regs a.reg :=
  ⟨fun hp => ⟨hp.rsp, hp.regs⟩,
    fun hp => ⟨hp.1, hp.2, fun _ _ _ _ hm => by simp [h] at hm⟩⟩

/-- `PubAgree` at a layout without public arrays, from the stack pointer and the registers of
    the public parameters. -/
theorem PubAgree.of_pubWords_nil {σ : AbiLayout} (h : σ.pubWords = []) {s₁ s₂ : AState}
    (hrsp : s₁.regs "%rsp" = s₂.regs "%rsp")
    (hregs : ∀ a ∈ σ.args, σ.argPub a = true → s₁.regs a.reg = s₂.regs a.reg) :
    σ.PubAgree s₁ s₂ :=
  (pubAgree_iff_of_pubWords_nil h s₁ s₂).mpr ⟨hrsp, hregs⟩

/-- Under `PubAgree`, each public array region holds equal words at the addresses its
    register holds in the two states. -/
theorem PubAgree.wordsAt_eq {σ : AbiLayout} {s₁ s₂ : AState} (h : σ.PubAgree s₁ s₂)
    {p : String × Nat} (hp : p ∈ σ.pubRegions) :
    wordsAt s₁.mem (s₁.regs p.1) p.2 = wordsAt s₂.mem (s₂.regs p.1) p.2 := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.mp hp
  obtain ⟨ha, hpub⟩ := List.mem_filter.mp ha
  unfold AbiArg.region at hr
  split at hr
  · simp at hr
  · rename_i n hk
    cases hr
    exact h.words a ha n hk (by simpa using hpub)

/-- **The stack parameters at entry**: at the state `sa`, the carrier name `stackArgReg k` of
    every stack parameter holds the word at `%rsp + 8 k` of the memory. -/
def StackIn (σ : AbiLayout) (sa : AState) : Prop :=
  ∀ a ∈ σ.args, ∀ k, a.reg = stackArgReg k →
    sa.regs a.reg = read64 sa.mem (sa.regs "%rsp" + BitVec.ofNat 64 (8 * k))

/-- The entry conditions of a layout at the state `sa`: every bounded register is within its
    bound; the words of two distinct pointer regions are pairwise disjoint; every word of a
    pointer region is disjoint from every stack word `%rsp + o`, `frameLo ≤ o ≤ frameHi`; and
    the stack parameters are at entry (`StackIn`). -/
def Regions (σ : AbiLayout) (sa : AState) : Prop :=
  (∀ b ∈ σ.bounds, (sa.regs b.1).toNat ≤ b.2)
    ∧ (∀ (i j : Nat) (p q : String × Nat), i ≠ j → σ.regions[i]? = some p →
        σ.regions[j]? = some q → ∀ k k', k < p.2 → k' < q.2 →
          Disjoint8 (sa.regs p.1 + BitVec.ofNat 64 (8 * k))
            (sa.regs q.1 + BitVec.ofNat 64 (8 * k')))
    ∧ (∀ p ∈ σ.regions, ∀ k, k < p.2 → ∀ o : Int, σ.frameLo ≤ o → o ≤ σ.frameHi →
        Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 o)
          (sa.regs p.1 + BitVec.ofNat 64 (8 * k)))
    ∧ σ.StackIn sa

/-- The stack parameters at an entry state satisfying `Regions`. -/
theorem Regions.stackIn {σ : AbiLayout} {sa : AState} (h : σ.Regions sa) : σ.StackIn sa :=
  h.2.2.2

/-- Every parameter of the layout is carried in a register: no parameter has the carrier
    name `stackArgReg k` of a stack word. -/
def RegCarried (σ : AbiLayout) : Prop :=
  ∀ a ∈ σ.args, ∀ k, a.reg ≠ stackArgReg k

/-- **The well-formed stack parameters** of a layout: each stack parameter lies in a word
    `%rsp + 8 k` with `k ≥ 1`, above the return address at `%rsp`, at an offset
    `8 k ≤ frameHi` inside the stack words of the layout, so that `Regions` separates every
    pointer region from it. -/
def StackWF (σ : AbiLayout) : Prop :=
  ∀ a ∈ σ.args, ∀ k, a.reg = stackArgReg k → 1 ≤ k ∧ 8 * (k : Int) ≤ σ.frameHi

/-- A layout whose parameters are all register-carried has its stack parameters at every
    entry state. -/
theorem stackIn_of_regCarried {σ : AbiLayout} (h : σ.RegCarried) (sa : AState) :
    σ.StackIn sa :=
  fun a ha k hk => absurd hk (h a ha k)

/-- A layout whose parameters are all register-carried has well-formed stack parameters. -/
theorem stackWF_of_regCarried {σ : AbiLayout} (h : σ.RegCarried) : σ.StackWF :=
  fun a ha k hk => absurd hk (h a ha k)

/-- The check that no parameter register of the layout has a name beginning with `%rsp+`. -/
def regCarriedB (σ : AbiLayout) : Bool :=
  σ.args.all fun a => !("%rsp+".toList.isPrefixOf a.reg.toList)

/-- A layout that passes `regCarriedB` has all its parameters carried in registers. -/
theorem regCarried_of_regCarriedB {σ : AbiLayout} (h : σ.regCarriedB = true) :
    σ.RegCarried := by
  intro a ha k
  apply ne_stackArgReg
  have h1 := List.all_eq_true.mp h a ha
  rw [Bool.not_eq_true'] at h1
  rw [← List.isPrefixOf_iff_prefix, h1]
  exact Bool.false_ne_true

/-- A layout that passes `regCarriedB` has its stack parameters at every entry state. -/
theorem stackIn_of_regCarriedB {σ : AbiLayout} (h : σ.regCarriedB = true) (sa : AState) :
    σ.StackIn sa :=
  stackIn_of_regCarried (regCarried_of_regCarriedB h) sa

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
