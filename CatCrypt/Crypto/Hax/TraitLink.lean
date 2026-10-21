/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.Module
public import HaxLean.ByteWords

/-!
# Trait-bound calls answered by linked word leaves

A call through a trait bound on byte-encoded arguments has a head of the extraction (the bare
head or `T_h`) and is answered by a linked leaf whose arguments and result are arrays of four
`u64` words. A `TraitLink` declares such a head: the leaf, the parameters with their
conversions (`ByteWords.ArgConv`: 32 bytes packed into 4 little-endian words, or the value
kept) and the conversion of the result (`ByteWords.ResConv`: 4 words unpacked into 32 bytes,
or a word read as the flag `r ≠ 0`).

`HaxModule.withTraitLinks ls m` adds to the module `m`, for each declared head, the callee
`ByteWords.traitWrapperTExpr` named by the head, and raises the depth by one. It refuses a
name clash: two links of one head, a head that names a function or a linked function of the
module or a builtin head of the callee, a leaf that names a function of the module or a
declared head, and a link whose parameter names repeat. With no link it returns the module.

`TraitLink.byteSem t T` is the byte-level meaning of the head of `t` read from the word meaning
of the leaf in the table `T`: on admitted arguments it applies the conversions of the
arguments, calls the leaf, and on an admitted result returns the converted result.
`TraitLink.byteTable ls T bi` answers each declared head by its byte-level meaning and every
other call by `bi`.

## Main definitions

* `TraitLink` — a declared trait head, its leaf, the conversions of its parameters and of its
  result.
* `TraitLink.wrapper` — the generated callee of a link as a function of a module.
* `TraitLink.byteSem`, `TraitLink.byteTable` — the byte-level meaning of a declared head, and
  the table extended by those meanings.
* `HaxModule.withTraitLinks` — the module with the callees of the links added.

## Main results

* `HaxModule.withTraitLinks_nil` — with no link the module is unchanged.
* `HaxModule.runs_withTraitLinks` — a run of the source relation of a module over the table
  extended by the byte-level meanings of the declared heads is a run of the module with the
  links added over the base table.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Hax.ImpToNF (paramsEnv dec)
open _root_.Hax (TExpr ImpExpr Builtins Value Env denote' hax64IntWordB hax64WordNat
  hax64IntWordB_int)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open _root_.Hax.ByteWords

/-- **A declared trait head**: the head of the extraction, the linked leaf answering it, the
    parameters with their conversions (`bytes`: 32 bytes, `keep`: a value passed unchanged),
    and the conversion of the leaf's result (`bytes`: 4 words to 32 bytes, `flag`: a word to
    a Boolean). -/
structure TraitLink where
  /-- The head of the trait-bound call in the extraction. -/
  head : String
  /-- The name of the linked leaf, whose arguments and result are words. -/
  leaf : String
  /-- The parameters of the callee, each a name with its conversion. -/
  params : List (String × ArgConv)
  /-- The conversion of the leaf's result. -/
  res : ResConv

namespace TraitLink

/-- The type of a parameter under its conversion: 32 bytes as an array of 32 `u64` words, one
    byte per word (the byte-word convention of `HaxLean.ByteWords` and of the extraction's
    `[u8; 32]` arguments), or a `u64` word. -/
def argTy : ArgConv → NfTy
  | .bytes => .arr 32 (.word 64)
  | .keep => .word 64

/-- The type of the result under its conversion: 32 bytes as an array of 32 `u64` words, one
    byte per word, or a bit. -/
def resTy : ResConv → NfTy
  | .bytes => .arr 32 (.word 64)
  | .flag => .bit

/-- **The generated callee of a link** as a function of a module: named by the head, with the
    typed parameters of the link, and the extraction `traitWrapperTExpr` calling the leaf. -/
def wrapper (t : TraitLink) : ModFn :=
  ⟨t.head, t.params.map fun p => (p.1, argTy p.2), resTy t.res,
    traitWrapperTExpr t.leaf t.params t.res⟩

/-- The decision of `ArgConv.Admits`: 32 integer words for `bytes`, a value that is not a
    control-flow value for `keep`. -/
def argOk : ArgConv → Value → Bool
  | .bytes, .array vs => vs.length == 32 && vs.all hax64IntWordB
  | .bytes, _ => false
  | .keep, v => !v.isControlFlow

/-- The decision of `ResConv.Admits`: 4 integer words for `bytes`, an integer for `flag`. -/
def resOk : ResConv → Value → Bool
  | .bytes, .array vs => vs.length == 4 && vs.all hax64IntWordB
  | .flag, .int _ => true
  | _, _ => false

/-- **The byte-level meaning of a declared head**, read from the word meaning of the leaf in
    the table `T`: on as many arguments as parameters, each admitted by its conversion, the
    leaf is called on the converted arguments (`packLE` of the bytes), and an admitted result
    is returned converted (`unpackLE` of the words, or the flag `r ≠ 0`). -/
def byteSem (t : TraitLink) (T : Builtins) (vals : List Value) : Option Value :=
  if t.params.length == vals.length && (t.params.zip vals).all (fun p => argOk p.1.2 p.2) then
    match T t.leaf (List.zipWith (fun q v => q.2.apply v) t.params vals) with
    | some r => if resOk t.res r then some (t.res.apply r) else none
    | none => none
  else none

/-- **The table extended by the byte-level meanings of the links `ls`**: the first link with a
    head answers a call by its byte-level meaning over `T`; every other call is a call of
    `bi`. -/
def byteTable (ls : List TraitLink) (T bi : Builtins) : Builtins := fun g vals =>
  match ls.find? (·.head == g) with
  | some t => t.byteSem T vals
  | none => bi g vals

/-- With no link the extended table is the base table. -/
theorem byteTable_nil (T bi : Builtins) : byteTable [] T bi = bi :=
  rfl

/-- An array of integer words is the word array of its natural numbers, each below `2^64`. -/
theorem array_eq_wordsVal {vs : List Value} (ha : vs.all hax64IntWordB = true) :
    Value.array vs = wordsVal (vs.map hax64WordNat) ∧ ∀ b ∈ vs.map hax64WordNat, b < 2 ^ 64 := by
  rw [List.all_eq_true] at ha
  refine ⟨?_, ?_⟩
  · simp only [wordsVal, List.map_map]
    congr 1
    conv_lhs => rw [← List.map_id vs]
    apply List.map_congr_left
    intro x hx
    obtain ⟨n, rfl, h0, -⟩ := hax64IntWordB_int (ha x hx)
    simp [hax64WordNat, Int.toNat_of_nonneg h0]
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨n, rfl, h0, h1⟩ := hax64IntWordB_int (ha x hx)
    simp only [hax64WordNat]
    omega

/-- An argument `argOk` accepts is admitted by its conversion. -/
theorem argOk_admits {c : ArgConv} {v : Value} (h : argOk c v = true) : c.Admits v := by
  cases c with
  | bytes =>
    cases v with
    | array vs =>
      simp only [argOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨he, hb⟩ := array_eq_wordsVal h.2
      exact ⟨_, he, by simp [h.1], hb⟩
    | _ => simp [argOk] at h
  | keep => simpa [argOk, ArgConv.Admits] using h

/-- A result `resOk` accepts is admitted by its conversion. -/
theorem resOk_admits {c : ResConv} {r : Value} (h : resOk c r = true) : c.Admits r := by
  cases c with
  | bytes =>
    cases r with
    | array vs =>
      simp only [resOk, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨he, hb⟩ := array_eq_wordsVal h.2
      exact ⟨_, he, by simp [h.1], hb⟩
    | _ => simp [resOk] at h
  | flag =>
    cases r with
    | int z => exact ⟨z, rfl⟩
    | _ => simp [resOk] at h

/-- The integer values of natural numbers below `2^w` decode as `w`-bit words, one per
    number. -/
theorem mapM_dec_word (w : Nat) : ∀ (ns : List Nat), (∀ n ∈ ns, n < 2 ^ w) →
    ∃ ys, (ns.map fun (n : Nat) => Value.int n).mapM (dec (.word w)) = some ys ∧
      ys.length = ns.length := by
  intro ns
  induction ns with
  | nil => intro _; exact ⟨[], rfl, rfl⟩
  | cons n ns ih =>
    intro h
    obtain ⟨ys, hys, hl⟩ := ih (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have hn : (n : Int) < 2 ^ w := by exact_mod_cast h n List.mem_cons_self
    refine ⟨BitVec.ofNat w n :: ys, ?_, by simp [hl]⟩
    simp [List.mapM_cons, hys, dec, hn]

/-- The integer values of natural numbers below `2^8` decode as bytes, one per number. -/
theorem mapM_dec_byte : ∀ (ns : List Nat), (∀ n ∈ ns, n < 2 ^ 8) →
    ∃ ys, (ns.map fun (n : Nat) => Value.int n).mapM (dec (.word 8)) = some ys ∧
      ys.length = ns.length :=
  mapM_dec_word 8

/-- The converted value of a result `resOk` accepts decodes at the result type. -/
theorem dec_resTy_apply {c : ResConv} {r : Value} (h : resOk c r = true) :
    (dec (resTy c) (c.apply r)).isSome = true := by
  cases c with
  | bytes =>
    cases r with
    | array vs =>
      obtain ⟨ys, hys, hl⟩ := mapM_dec_word 64 (unpackLE (vs.map hax64WordNat)) (by
        intro n hn
        simp only [unpackLE, List.mem_map] at hn
        obtain ⟨k, -, rfl⟩ := hn
        exact lt_of_lt_of_le (wordByteLE_lt _ k) (by norm_num))
      have h32 : ys.length = 32 := by simp [hl, unpackLE]
      simp [ResConv.apply, resTy, wordsVal, dec, hys, h32]
    | _ => simp [resOk] at h
  | flag =>
    cases r with
    | int z => simp [ResConv.apply, resTy, dec]
    | _ => simp [resOk] at h

end TraitLink

/-- With distinct names, a name paired with a value in `xs.zip vs` is bound to that value in
    `paramsEnv xs vs`. -/
theorem paramsEnv_of_mem_zip : ∀ (xs : List String) (vs : List Value), xs.Nodup →
    ∀ x v, (x, v) ∈ xs.zip vs → paramsEnv xs vs x = some v := by
  intro xs
  induction xs with
  | nil => intro vs _ x v h; simp at h
  | cons y ys ih =>
    intro vs hnd x v h
    cases vs with
    | nil => simp at h
    | cons w ws =>
      rw [List.nodup_cons] at hnd
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      simp only [paramsEnv]
      rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · have hx : x ≠ y := fun e => hnd.1 (e ▸ (List.of_mem_zip h).1)
        rw [if_neg hx]
        exact ih ws hnd.2 x v h

/-- The reference reading of the callee `traitWrapperTExpr` is its reading by `denote'`. -/
theorem denoteSpine_traitWrapper (bi : Builtins) (fuel : Nat) (leaf : String)
    (params : List (String × ArgConv)) (res : ResConv) :
    denoteSpine bi fuel (traitWrapperTExpr leaf params res).erase =
      denote' bi fuel (traitWrapperTExpr leaf params res).erase := by
  obtain ⟨g, args, hc⟩ : ∃ g args, (resE res).erase = .app g args := by
    cases res <;> exact ⟨_, _, rfl⟩
  have he : (traitWrapperTExpr leaf params res).erase =
      .letBind resVar (.app leaf ((params.map argE).map TExpr.erase)) (.app g args) := by
    rw [← hc]
    simp [traitWrapperTExpr, TExpr.erase]
  rw [he, denoteSpine.eq_2 _ _ _ _ _ (fun _ _ h => by cases h),
    denoteSpine.eq_4 _ _ _ (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
      (fun _ _ h => by cases h)]
  funext env
  rw [_root_.Hax.denote'_letBind_run]
  simp only [bind, StateT.bind]
  rcases denote' bi fuel (.app leaf ((params.map argE).map TExpr.erase)) env with ⟨o, s⟩
  rcases o with (u|u|u|_|u) <;> try rfl
  cases u <;> rfl

/-- **A call of the callee of a link at depth `n + 1` of the reference table** returns the
    byte-level meaning of its head over `T`, when the callee is the function of its head, the
    leaf and the builtin heads of the callee are no function of `fs`, `T` agrees with
    `hax64Builtins` on those heads, and the parameter names are distinct. -/
theorem refBi_wrapper {fs : List ModFn} {T : Builtins} {fuel : Nat} (n : Nat) {t : TraitLink}
    (hf : fs.find? (·.name == t.head) = some t.wrapper)
    (hleaf : fs.find? (·.name == t.leaf) = none)
    (hW : ∀ g ∈ wrapperHeads, fs.find? (·.name == g) = none) (hT : WrapperOps T)
    (hnd : (t.params.map (·.1)).Nodup) {vals : List Value} {v : Value}
    (h : t.byteSem T vals = some v) :
    refBi fs T fuel (n + 1) t.head vals = some v := by
  rw [refBi_succ _ _ _ _ hf]
  unfold TraitLink.byteSem at h
  split at h
  next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
    obtain ⟨hlen, hargs⟩ := hc
    split at h
    next r hr =>
      split at h
      next hok =>
        cases h
        have hbi : WrapperOps (refBi fs T fuel n) := fun g hg => by
          funext ws
          rw [refBi_of_find_none _ _ _ _ (hW g hg)]
          exact congrFun (hT g hg) ws
        have hleaf' : refBi fs T fuel n t.leaf
            (List.zipWith (fun q v => q.2.apply v) t.params vals) = some r := by
          rw [refBi_of_find_none _ _ _ _ hleaf]
          exact hr
        have henv : ∀ q v, (q, v) ∈ t.params.zip vals →
            paramsEnv (t.params.map (·.1)) vals q.1 = some v ∧ q.2.Admits v := by
          intro q w hq
          refine ⟨paramsEnv_of_mem_zip _ vals hnd q.1 w ?_, TraitLink.argOk_admits (hargs _ hq)⟩
          rw [List.zip_map_left]
          exact List.mem_map_of_mem (f := Prod.map (·.1) id) hq
        have hw := denote'_wrapper fuel hbi t.leaf t.params t.res _ vals hlen henv hleaf'
          (TraitLink.resOk_admits hok)
        have hnames : t.wrapper.params.map (·.1) = t.params.map (·.1) := by
          simp [TraitLink.wrapper]
        have hw' : ((denoteSpine (refBi fs T fuel n) fuel t.wrapper.texpr.erase).run
            (paramsEnv (t.wrapper.params.map (·.1)) vals)).1 = .val (t.res.apply r) := by
          rw [hnames]
          simp only [TraitLink.wrapper]
          rw [denoteSpine_traitWrapper]
          exact hw
        rw [hw']
        simp [TraitLink.wrapper, TraitLink.dec_resTy_apply hok]
      next => cases h
    next => cases h
  next => cases h

namespace HaxModule

/-- The links `ls` have no name clash in the module `m`: their heads are distinct; no head
    names a function or a linked function of `m` or a builtin head of the callee; no leaf
    names a function of `m` or a head; the parameter names of each link are distinct. -/
def traitLinksOk (ls : List TraitLink) (m : HaxModule) : Bool :=
  decide (ls.map (·.head)).Nodup &&
    ls.all fun t =>
      decide (t.params.map (·.1)).Nodup &&
        !(m.fns.any (·.name == t.head)) && !(m.linked.any (·.name == t.head)) &&
        !(wrapperHeads.contains t.head) &&
        !(m.fns.any (·.name == t.leaf)) && !((ls.map (·.head)).contains t.leaf)

/-- **The module with the trait links `ls` added**: the callees of the links after the
    functions of the module, and the depth raised by one, so that a call of a declared head
    at depth `n + 1` runs its callee and the leaf at depth `n`. With no link, the module;
    on a name clash (`traitLinksOk`), `none`. -/
def withTraitLinks (ls : List TraitLink) (m : HaxModule) : Option HaxModule :=
  if ls.isEmpty then some m
  else if traitLinksOk ls m then
    some { m with fns := m.fns ++ ls.map TraitLink.wrapper, depth := m.depth + 1 }
  else none

/-- With no link the module is unchanged. -/
theorem withTraitLinks_nil (m : HaxModule) : withTraitLinks [] m = some m :=
  rfl

/-- The facts `traitLinksOk` checks for a link of the list. -/
theorem traitLinksOk_mem {ls : List TraitLink} {m : HaxModule} (hok : traitLinksOk ls m = true)
    {t : TraitLink} (ht : t ∈ ls) :
    (t.params.map (·.1)).Nodup ∧ m.fns.find? (·.name == t.head) = none ∧
      m.linked.find? (·.name == t.head) = none ∧ t.head ∉ wrapperHeads ∧
      m.fns.find? (·.name == t.leaf) = none ∧ ls.find? (·.head == t.leaf) = none := by
  grind only [= traitLinksOk.eq_def, = List.find?_eq_none, = List.all_eq, = List.contains_eq_mem,
    = List.any_eq, = List.mem_map]

/-- **The reference tables of a module over the extended table are below those of the module
    with the links added, one depth higher.** For links without name clash, a base table
    whose linked-function table agrees with `hax64Builtins` on the builtin heads of the
    callee, and a module with no function of those heads: a call the reference table of the
    module over `byteTable ls (m.linkTable bi) bi` answers by a value at depth `n` is answered
    by the same value at depth `n + 1` in the module with the callees of the links added over
    `bi`. -/
theorem refBi_le_withTraitLinks {ls : List TraitLink} {m : HaxModule}
    (hok : traitLinksOk ls m = true) (bi : Builtins) (fuelC : Nat)
    (hW : WrapperOps (m.linkTable bi))
    (hWf : ∀ g ∈ wrapperHeads, m.fns.find? (·.name == g) = none) :
    ∀ n g vals v,
      refBi m.fns (linkBi m.linked (TraitLink.byteTable ls (m.linkTable bi) bi)) fuelC n g vals =
          some v →
        refBi (m.fns ++ ls.map TraitLink.wrapper) (m.linkTable bi) fuelC (n + 1) g vals =
          some v := by
  have hfs : ∀ g, (m.fns ++ ls.map TraitLink.wrapper).find? (·.name == g) =
      (m.fns.find? (·.name == g)).or ((ls.find? (·.head == g)).map TraitLink.wrapper) := by
    intro g
    rw [List.find?_append, List.find?_map]
    rfl
  have hwrap : ∀ k t, t ∈ ls → ls.find? (·.head == t.head) = some t → ∀ vals v,
      t.byteSem (m.linkTable bi) vals = some v →
        refBi (m.fns ++ ls.map TraitLink.wrapper) (m.linkTable bi) fuelC (k + 1) t.head vals =
          some v := by
    intro k t ht hft vals v h
    obtain ⟨hnd, hh, -, -, hl, hll⟩ := traitLinksOk_mem hok ht
    refine refBi_wrapper k ?_ ?_ ?_ hW hnd h
    · rw [hfs, hh, hft]
      rfl
    · rw [hfs, hl, hll]
      rfl
    · intro g hg
      have hn : ls.find? (·.head == g) = none := by
        rw [List.find?_eq_none]
        intro t' ht' he
        have := (traitLinksOk_mem hok ht').2.2.2.1
        rw [beq_iff_eq] at he
        exact this (he ▸ hg)
      rw [hfs, hWf g hg, hn]
      rfl
  have hbase : ∀ k g, m.fns.find? (·.name == g) = none → ∀ vals v,
      linkBi m.linked (TraitLink.byteTable ls (m.linkTable bi) bi) g vals = some v →
        refBi (m.fns ++ ls.map TraitLink.wrapper) (m.linkTable bi) fuelC (k + 1) g vals =
          some v := by
    intro k g hg vals v h
    cases ht : ls.find? (·.head == g) with
    | some t =>
      have htm := List.mem_of_find?_eq_some ht
      have hth : t.head = g := by simpa using List.find?_some ht
      subst hth
      rw [linkBi_of_find_none _ _ (traitLinksOk_mem hok htm).2.2.1] at h
      simp only [TraitLink.byteTable, ht] at h
      exact hwrap k t htm ht vals v h
    | none =>
      rw [refBi_of_find_none _ _ _ _ (by rw [hfs, hg, ht]; rfl)]
      have he : linkBi m.linked (TraitLink.byteTable ls (m.linkTable bi) bi) g vals =
          linkBi m.linked bi g vals := by
        simp only [linkBi]
        split <;> simp [TraitLink.byteTable, ht]
      rw [he] at h
      exact h
  intro n
  induction n with
  | zero =>
    intro g vals v h
    cases hg : m.fns.find? (·.name == g) with
    | some f => simp only [refBi, hg] at h; cases h
    | none =>
      rw [refBi_of_find_none _ _ _ _ hg] at h
      exact hbase 0 g hg vals v h
  | succ k ih =>
    intro g vals v h
    cases hg : m.fns.find? (·.name == g) with
    | none =>
      rw [refBi_of_find_none _ _ _ _ hg] at h
      exact hbase (k + 1) g hg vals v h
    | some f =>
      rw [refBi_succ_refSem _ _ _ _ hg] at h
      rw [refBi_succ_refSem _ _ _ _ (by rw [hfs, hg]; rfl)]
      exact f.refSem_le ih fuelC vals v h

/-- **A run of a module over the byte-level meanings of the declared heads is a run of the
    module with the links added.** When `withTraitLinks ls m = some m'`, the table of the
    linked functions of `m` over `bi` agrees with `hax64Builtins` on the builtin heads of the
    callee and no function of `m` has one of those heads, the source relation of `m` at the
    table `byteTable ls (m.linkTable bi) bi`, from `sa` to `v`, is the source relation of `m'`
    at `bi` from `sa` to `v`. -/
theorem runs_withTraitLinks (bi : Builtins) (σ : AbiLayout) {ls : List TraitLink}
    {m m' : HaxModule} (h : withTraitLinks ls m = some m')
    (hW : WrapperOps (m.linkTable bi))
    (hWf : ∀ g ∈ wrapperHeads, m.fns.find? (·.name == g) = none) {sa : AState} {v : Value}
    (hr : Runs (TraitLink.byteTable ls (m.linkTable bi) bi) σ m sa v) : Runs bi σ m' sa v := by
  unfold withTraitLinks at h
  split at h
  next hls =>
    cases h
    obtain rfl : ls = [] := List.isEmpty_iff.mp hls
    rwa [TraitLink.byteTable_nil] at hr
  next =>
    split at h
    next hok =>
      cases h
      obtain ⟨env, fuel, fuelC, env', henv, hrun, hcf⟩ := hr
      exact ⟨env, fuel, fuelC, env', henv,
        denoteSpine_val_of_le fuel _ _ (refBi_le_withTraitLinks hok bi fuelC hW hWf m.depth)
          _ _ _ hrun, hcf⟩
    next => cases h

end HaxModule

end CatCrypt.Crypto.Hax
