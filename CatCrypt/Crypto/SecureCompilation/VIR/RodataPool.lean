/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import Std.Data.String.ToNat

/-!
# A `.rodata` constant pool for the vector emitters

A pool is a list of constants, each a label, an alignment and a list of 64-bit words,
rendered as the `.rodata` directives

```
	.p2align k
<label>:
	.quad w₀
	.quad w₁
	…
```

one entry after another. The label of the `i`-th entry is `pfx ++ "_c" ++ toString i`
for the pool's prefix `pfx`; with a prefix starting `.L` the labels are assembler-local.
`Pool.intern` returns the label of an existing entry with the same alignment and words
and appends a new entry otherwise, so equal constants share one entry. The spelling of
the directives is the one `ZmmTextValidate.parseData` reads.

The contents of the rendered text are stated over the directive list: `quadsAt ds l`
reads the words that follow the label `l` in `ds`, and `bytesAt` reads them as
little-endian bytes.

## Main definitions

* `Directive`, `Directive.line`: the three directives and their text lines.
* `Pool`, `Pool.push`, `Pool.intern`, `Pool.ofList`: building a pool.
* `Pool.ref`: the label holding a constant, or the sentinel `undefinedRef`.
* `Pool.directives`, `Pool.lines`, `Pool.sectionLines`, `Pool.text`: rendering.
* `quadsAt`, `bytesAt`: the words and bytes at a label of a directive list.
* `qwordsLE`, `leValue`, `bytesLE`, `bytesLEValue`: conversions between a number, its
  64-bit words and its bytes.

## Main results

* `Pool.quadsAt_directives`: in a canonical pool, every entry's label reads back
  exactly that entry's words.
* `Pool.quadsAt_ref`, `Pool.quadsAt_ofList_ref`: the label `ref` returns for a
  constant of the pool reads back the constant's words.
* `Pool.quadsAt_intern`: the label `intern` returns reads back the interned words.
* `Pool.canonical_ofList`, `Pool.canonical_intern`, `Pool.canonical_push`: the
  builders keep the pool canonical.
* `leValue_qwordsLE`: the words `qwordsLE n v` denote `v mod 2^(64 n)`.
* `bytesLE_bytesLEValue`: `bytesLE` inverts `bytesLEValue` on byte lists.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.RodataPool

/-! ## 1. Directives -/

/-- One directive of a `.rodata` constant pool. -/
inductive Directive where
  /-- `.p2align k`: the next address is a multiple of `2^k`. -/
  | align (k : Nat)
  /-- `name:`, the label of the address that follows. -/
  | label (name : String)
  /-- `.quad w`: one 8-byte little-endian word. -/
  | quad (w : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The text line of a directive. -/
def Directive.line : Directive → String
  | .align k => "\t.p2align " ++ toString k
  | .label s => s ++ ":"
  | .quad w => "\t.quad " ++ toString w

/-- The words of the `.quad` directives at the head of a directive list, up to the
    first other directive. -/
def quadRun : List Directive → List Nat
  | .quad w :: ds => w :: quadRun ds
  | _ => []

/-- The words stored at label `l`: the `.quad` run that follows the first `l:` of
    the list, or `none` when `l` is not a label of the list. -/
def quadsAt : List Directive → String → Option (List Nat)
  | [], _ => none
  | .label s :: ds, l => if s = l then some (quadRun ds) else quadsAt ds l
  | _ :: ds, l => quadsAt ds l

/-- The `n` low bytes of `w`, least significant first. -/
def bytesLE : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, w => w % 256 :: bytesLE n (w / 256)

/-- The bytes stored at label `l`: the words `quadsAt` reads, each as its eight
    little-endian bytes. -/
def bytesAt (ds : List Directive) (l : String) : Option (List Nat) :=
  (quadsAt ds l).map (·.flatMap (bytesLE 8))

/-! ## 2. Words and values -/

/-- The `n` 64-bit words of `v mod 2^(64 n)`, least significant first. -/
def qwordsLE : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 2 ^ 64 :: qwordsLE n (v / 2 ^ 64)

/-- The number a list of words denotes read little-endian, each word taken modulo
    `2^64` (the value an 8-byte `.quad` stores). -/
def leValue : List Nat → Nat
  | [] => 0
  | w :: ws => w % 2 ^ 64 + 2 ^ 64 * leValue ws

/-- The number a byte list denotes read little-endian. -/
def bytesLEValue : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * bytesLEValue bs

theorem leValue_qwordsLE (n v : Nat) : leValue (qwordsLE n v) = v % 2 ^ (64 * n) := by
  induction n generalizing v with
  | zero => simp [qwordsLE, leValue, Nat.mod_one]
  | succ n ih =>
    simp only [qwordsLE, leValue, ih, Nat.mod_mod]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (64 * n)) (2 ^ 64), Nat.mod_mul]

theorem bytesLE_bytesLEValue (bs : List Nat) (h : ∀ b ∈ bs, b < 256) :
    bytesLE bs.length (bytesLEValue bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb : b < 256 := h b (by simp)
    have hbs : ∀ c ∈ bs, c < 256 := fun c hc => h c (by simp [hc])
    have hmod : (b + 256 * bytesLEValue bs) % 256 = b := by omega
    have hdiv : (b + 256 * bytesLEValue bs) / 256 = bytesLEValue bs := by omega
    simp only [List.length_cons, bytesLE, bytesLEValue, hmod, hdiv, ih hbs]

/-! ## 3. Pools -/

/-- One constant of a pool: its label, the base-2 logarithm of its alignment, and its
    64-bit words, least significant first. -/
structure Entry where
  /-- The label of the constant's first byte. -/
  label : String
  /-- The alignment of the constant is `2 ^ log2Align` bytes. -/
  log2Align : Nat
  /-- The words stored at the label, least significant first. -/
  words : List Nat
  deriving DecidableEq, Repr, Inhabited

/-- The directives of one entry: its alignment, its label, one `.quad` per word. -/
def Entry.directives (e : Entry) : List Directive :=
  .align e.log2Align :: .label e.label :: e.words.map .quad

/-- A constant pool: the label prefix and the entries in emission order. -/
structure Pool where
  /-- The prefix of every label of the pool. -/
  pfx : String
  /-- The entries, in the order they are emitted. -/
  entries : Array Entry := #[]
  deriving Inhabited

/-- The label of entry `i` of a pool with prefix `pfx`. -/
def labelAt (pfx : String) (i : Nat) : String := pfx ++ "_c" ++ toString i

/-- The pool with prefix `pfx` and no entries. -/
def Pool.empty (pfx : String) : Pool := { pfx }

/-- Append the constant `ws` with alignment `2 ^ k`, returning the pool and the new
    entry's label. -/
def Pool.push (p : Pool) (k : Nat) (ws : List Nat) : Pool × String :=
  let lbl := labelAt p.pfx p.entries.size
  ({ p with entries := p.entries.push ⟨lbl, k, ws⟩ }, lbl)

/-- The label of the first entry with alignment `2 ^ k` and words `ws`. -/
def Pool.find? (p : Pool) (k : Nat) (ws : List Nat) : Option String :=
  (p.entries.find? (fun e => e.log2Align == k && e.words == ws)).map Entry.label

/-- The label of the constant `ws` with alignment `2 ^ k`: an existing entry's when
    the pool holds it, else a new entry's. -/
def Pool.intern (p : Pool) (k : Nat) (ws : List Nat) : Pool × String :=
  match p.find? k ws with
  | some l => (p, l)
  | none => p.push k ws

/-- Intern each `(k, ws)` of `items` in order. -/
def Pool.internAll (p : Pool) (items : List (Nat × List Nat)) : Pool :=
  items.foldl (fun p kw => (p.intern kw.1 kw.2).1) p

/-- The pool with prefix `pfx` holding the constants `items`, equal ones shared. -/
def Pool.ofList (pfx : String) (items : List (Nat × List Nat)) : Pool :=
  (Pool.empty pfx).internAll items

/-- The operand spelling of a constant the pool does not hold; the assembler rejects
    it, and emit checks search for it. -/
def undefinedRef : String := "<UNDEFINED_CONST>"

/-- The label of the constant `ws` with alignment `2 ^ k`, or `undefinedRef`. -/
def Pool.ref (p : Pool) (k : Nat) (ws : List Nat) : String :=
  (p.find? k ws).getD undefinedRef

/-- The directives of the pool, entry after entry. -/
def Pool.directives (p : Pool) : List Directive :=
  p.entries.toList.flatMap Entry.directives

/-- The text lines of the pool's directives. -/
def Pool.lines (p : Pool) : List String :=
  p.directives.map Directive.line

/-- The `.rodata` section of the pool: the section directive and the pool's lines. -/
def Pool.sectionLines (p : Pool) : List String :=
  "\t.section .rodata" :: p.lines

/-- The `.rodata` section of the pool as text, one line per directive, each ended by
    a newline. -/
def Pool.text (p : Pool) : String :=
  String.join (p.sectionLines.map (· ++ "\n"))

/-- Entry `i` of the pool carries the label `labelAt p.pfx i`. -/
def Pool.Canonical (p : Pool) : Prop :=
  ∀ (i : Nat) (h : i < p.entries.size), p.entries[i].label = labelAt p.pfx i

/-! ## 4. Reading a pool back -/

theorem quadRun_map_quad_append (ws : List Nat) (ds : List Directive)
    (h : quadRun ds = []) : quadRun (ws.map .quad ++ ds) = ws := by
  induction ws with
  | nil => simpa using h
  | cons w ws ih => simp [quadRun, ih]

theorem quadsAt_map_quad_append (ws : List Nat) (ds : List Directive) (l : String) :
    quadsAt (ws.map .quad ++ ds) l = quadsAt ds l := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [quadsAt, ih]

theorem quadRun_flatMap_directives (es : List Entry) :
    quadRun (es.flatMap Entry.directives) = [] := by
  cases es with
  | nil => rfl
  | cons e es => simp [Entry.directives, quadRun]

theorem quadsAt_entry_append (e : Entry) (ds : List Directive) (l : String) :
    quadsAt (e.directives ++ ds) l =
      if e.label = l then some (quadRun (e.words.map .quad ++ ds))
      else quadsAt (e.words.map .quad ++ ds) l := by
  simp [Entry.directives, quadsAt]

theorem quadsAt_flatMap_directives (es : List Entry) (h : (es.map Entry.label).Nodup)
    (e : Entry) (he : e ∈ es) :
    quadsAt (es.flatMap Entry.directives) e.label = some e.words := by
  induction es with
  | nil => simp at he
  | cons e' es ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.flatMap_cons, quadsAt_entry_append]
    rcases List.mem_cons.mp he with rfl | he
    · simp [quadRun_map_quad_append _ _ (quadRun_flatMap_directives es)]
    · have hne : e'.label ≠ e.label := fun heq =>
        h.1 (heq ▸ List.mem_map_of_mem he)
      rw [if_neg hne, quadsAt_map_quad_append]
      exact ih h.2 he

theorem labelAt_injective (pfx : String) : Function.Injective (labelAt pfx) := by
  intro i j h
  unfold labelAt at h
  exact Nat.repr_injective ((String.append_right_inj _).mp h)

theorem Pool.labels_nodup (p : Pool) (hp : p.Canonical) :
    (p.entries.toList.map Entry.label).Nodup := by
  have hl : p.entries.toList.map Entry.label =
      (List.range p.entries.size).map (labelAt p.pfx) := by
    apply List.ext_getElem
    · simp
    · intro i h1 _
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_range]
      exact hp i (by simpa using h1)
  rw [hl]
  exact List.Pairwise.map _ (fun _ _ hne heq => hne (labelAt_injective p.pfx heq))
    List.nodup_range

theorem Pool.quadsAt_directives (p : Pool) (hp : p.Canonical) (e : Entry)
    (he : e ∈ p.entries) : quadsAt p.directives e.label = some e.words :=
  quadsAt_flatMap_directives _ (p.labels_nodup hp) e (by simpa using he)

theorem Pool.bytesAt_directives (p : Pool) (hp : p.Canonical) (e : Entry)
    (he : e ∈ p.entries) :
    bytesAt p.directives e.label = some (e.words.flatMap (bytesLE 8)) := by
  simp [bytesAt, p.quadsAt_directives hp e he]

theorem Pool.find?_spec (p : Pool) (k : Nat) (ws : List Nat) (l : String)
    (h : p.find? k ws = some l) :
    ∃ e ∈ p.entries, e.label = l ∧ e.log2Align = k ∧ e.words = ws := by
  unfold Pool.find? at h
  rcases hf : p.entries.find? (fun e => e.log2Align == k && e.words == ws) with _ | e
  · simp [hf] at h
  · rw [hf] at h
    have hp := Array.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨e, Array.mem_of_find?_eq_some hf, by simpa using h, hp.1, hp.2⟩

theorem Pool.find?_isSome (p : Pool) (k : Nat) (ws : List Nat)
    (h : ∃ e ∈ p.entries, e.log2Align = k ∧ e.words = ws) : (p.find? k ws).isSome := by
  obtain ⟨e, he, hk, hw⟩ := h
  simp only [Pool.find?, Option.isSome_map]
  exact Array.find?_isSome.mpr ⟨e, he, by simp [hk, hw]⟩

theorem Pool.quadsAt_ref (p : Pool) (hp : p.Canonical) (k : Nat) (ws : List Nat)
    (h : ∃ e ∈ p.entries, e.log2Align = k ∧ e.words = ws) :
    quadsAt p.directives (p.ref k ws) = some ws := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (p.find?_isSome k ws h)
  obtain ⟨e, he, rfl, -, rfl⟩ := p.find?_spec k ws l hl
  simp only [Pool.ref, hl, Option.getD_some]
  exact p.quadsAt_directives hp e he

/-! ## 5. The builders keep a pool canonical and hold what they were given -/

theorem Pool.canonical_empty (pfx : String) : (Pool.empty pfx).Canonical := by
  intro i h
  simp [Pool.empty] at h

theorem Pool.canonical_push (p : Pool) (hp : p.Canonical) (k : Nat) (ws : List Nat) :
    (p.push k ws).1.Canonical := by
  intro i h
  simp only [Pool.push, Array.size_push] at h ⊢
  rw [Array.getElem_push]
  split
  · exact hp i _
  · have : i = p.entries.size := by omega
    subst this; rfl

theorem Pool.push_pfx (p : Pool) (k : Nat) (ws : List Nat) : (p.push k ws).1.pfx = p.pfx :=
  rfl

theorem Pool.canonical_intern (p : Pool) (hp : p.Canonical) (k : Nat) (ws : List Nat) :
    (p.intern k ws).1.Canonical := by
  unfold Pool.intern
  split
  · exact hp
  · exact p.canonical_push hp k ws

theorem Pool.intern_pfx (p : Pool) (k : Nat) (ws : List Nat) :
    (p.intern k ws).1.pfx = p.pfx := by
  unfold Pool.intern
  split <;> rfl

theorem Pool.mem_push (p : Pool) (k : Nat) (ws : List Nat) :
    (⟨(p.push k ws).2, k, ws⟩ : Entry) ∈ (p.push k ws).1.entries := by
  simp [Pool.push]

theorem Pool.intern_holds (p : Pool) (k : Nat) (ws : List Nat) :
    ∃ e ∈ (p.intern k ws).1.entries,
      e.label = (p.intern k ws).2 ∧ e.log2Align = k ∧ e.words = ws := by
  unfold Pool.intern
  split
  · rename_i l hl
    exact p.find?_spec k ws l hl
  · exact ⟨_, p.mem_push k ws, rfl, rfl, rfl⟩

theorem Pool.entries_subset_intern (p : Pool) (k : Nat) (ws : List Nat) (e : Entry)
    (he : e ∈ p.entries) : e ∈ (p.intern k ws).1.entries := by
  unfold Pool.intern
  split
  · exact he
  · simp [Pool.push, he]

theorem Pool.quadsAt_intern (p : Pool) (hp : p.Canonical) (k : Nat) (ws : List Nat) :
    quadsAt (p.intern k ws).1.directives (p.intern k ws).2 = some ws := by
  obtain ⟨e, he, hl, -, hw⟩ := p.intern_holds k ws
  have h := (p.intern k ws).1.quadsAt_directives (p.canonical_intern hp k ws) e he
  rwa [hl, hw] at h

theorem Pool.canonical_internAll (items : List (Nat × List Nat)) (p : Pool)
    (hp : p.Canonical) : (p.internAll items).Canonical := by
  induction items generalizing p with
  | nil => exact hp
  | cons kw items ih => exact ih _ (p.canonical_intern hp kw.1 kw.2)

theorem Pool.internAll_holds (items : List (Nat × List Nat)) (p : Pool) (k : Nat)
    (ws : List Nat)
    (h : (∃ e ∈ p.entries, e.log2Align = k ∧ e.words = ws) ∨ (k, ws) ∈ items) :
    ∃ e ∈ (p.internAll items).entries, e.log2Align = k ∧ e.words = ws := by
  induction items generalizing p with
  | nil => simpa [Pool.internAll] using h
  | cons kw items ih =>
    apply ih
    rcases h with ⟨e, he, hk, hw⟩ | h
    · exact .inl ⟨e, p.entries_subset_intern kw.1 kw.2 e he, hk, hw⟩
    · rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨e, he, -, hk, hw⟩ := p.intern_holds k ws
        exact .inl ⟨e, he, hk, hw⟩
      · exact .inr h

theorem Pool.canonical_ofList (pfx : String) (items : List (Nat × List Nat)) :
    (Pool.ofList pfx items).Canonical :=
  Pool.canonical_internAll items _ (Pool.canonical_empty pfx)

/-- Every constant of `items` is read back at the label `ref` returns for it. -/
theorem Pool.quadsAt_ofList_ref (pfx : String) (items : List (Nat × List Nat)) (k : Nat)
    (ws : List Nat) (h : (k, ws) ∈ items) :
    quadsAt (Pool.ofList pfx items).directives ((Pool.ofList pfx items).ref k ws) =
      some ws :=
  Pool.quadsAt_ref _ (Pool.canonical_ofList pfx items) k ws
    (Pool.internAll_holds items _ k ws (.inr h))

end CatCrypt.Crypto.SecureCompilation.VIR.RodataPool
