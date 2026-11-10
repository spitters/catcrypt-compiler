/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomResCopy

/-!
# The store-chain shape under the renaming by webs

The pass `arrWebs` renames the array name `r` at a position to `r` or to `r ++ "#w" ++ root`
(`webLook_cases`). On names without `#`, the prefix before the first `#` recovers the name, so
the web names of distinct names are distinct at all positions (`webLook_inj`). The renaming of
the array positions of an instruction with a register, load or store tag, without callee,
renames its reads and its write (`rdArr_wrArr_renArr`). At a body that `webB` accepts, the
liveness certificate covers the reads and propagates backwards past instructions that do not
write, so a web name is constant along a stretch where its array is live and not written
(`webB_const'`). Together these keep the store-chain shape of one chain of stores written once
per array (`chainShape_webRen`).

## Main definitions

* `hashPrefix`: the prefix of a name before its first `#`.
* `PlainTag`: an instruction with a register, load or store tag.

## Main results

* `webLook_inj`: web names of distinct names without `#` are distinct.
* `rdArr_wrArr_renArr`: the reads and the write of a renamed instruction with a plain tag.
* `readAt_webRen`, `wrAt_webRen`, `consumedAt_webRen`: the reads, writes and consumptions of a
  body renamed by a position map are the images of those of the body.
* `chainShape₁₂_webRen`: reads follow writes and consumed names are dead in a body renamed by
  webs, when they are in the body.
* `webB_live`: the liveness that the webs check, at a straight instruction.
* `webB_const`, `webB_const'`: the web name of an array is constant along a stretch where it
  is live and not written.
* `wrAt_webRen_of`, `consumedAt_webRen_of`: writes and consumptions of the body, renamed, are
  those of the renamed body.
* `chainConsume_webRen`: the consumption facts of one chain are kept by the renaming by webs.
* `getD_foldl_webRen`: the alias table of a chain renamed by webs sends its written names to the
  root renamed at the entry and keeps the others.
* `chainShape_webRen`: the store-chain shape of one chain is kept by the renaming by webs.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webLook webLook_cases)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (WebSt)

/-- The prefix of a name before its first `#`. -/
def hashPrefix (s : String) : List Char := s.toList.takeWhile (· ≠ '#')

/-- A list without `#` is its own prefix before `#`, also in front of a `#`. -/
theorem takeWhile_noHash : ∀ (l : List Char), '#' ∉ l → ∀ (l' : List Char),
    (l ++ l').takeWhile (fun c => decide (c ≠ '#')) =
      l ++ l'.takeWhile (fun c => decide (c ≠ '#'))
  | [], _, _ => rfl
  | c :: l, h, l' => by
      have hc : c ≠ '#' := fun e => h (e ▸ List.mem_cons_self)
      have hl : '#' ∉ l := fun e => h (List.mem_cons_of_mem _ e)
      simp only [List.cons_append, List.takeWhile_cons, hc, ne_eq, not_false_eq_true,
        decide_true, ↓reduceIte, takeWhile_noHash l hl l']

/-- A name without `#` is its own prefix. -/
theorem hashPrefix_of_not_mem {a : String} (h : '#' ∉ a.toList) : hashPrefix a = a.toList := by
  have := takeWhile_noHash a.toList h []
  simpa [hashPrefix] using this

/-- The prefix of a web name `a ++ "#w" ++ s` of a name `a` without `#` is `a`. -/
theorem hashPrefix_web {a : String} (h : '#' ∉ a.toList) (s : String) :
    hashPrefix (a ++ "#w" ++ s) = a.toList := by
  unfold hashPrefix
  rw [String.toList_append, String.toList_append, List.append_assoc, takeWhile_noHash _ h]
  simp

/-- **Web names of distinct names without `#` are distinct**: a web name is the name or the
    name followed by `#w` and a root, so its prefix before `#` is the name. -/
theorem webLook_inj (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat) {k k' : Nat}
    {a b : String} (ha : '#' ∉ a.toList) (hb : '#' ∉ b.toList)
    (h : webLook tab k a = webLook tab k' b) : a = b := by
  have hpa : hashPrefix (webLook tab k a) = a.toList := by
    rcases webLook_cases tab k a with e | ⟨r, e⟩ <;> rw [e]
    · exact hashPrefix_of_not_mem ha
    · exact hashPrefix_web ha _
  have hpb : hashPrefix (webLook tab k' b) = b.toList := by
    rcases webLook_cases tab k' b with e | ⟨r, e⟩ <;> rw [e]
    · exact hashPrefix_of_not_mem hb
    · exact hashPrefix_web hb _
  rw [h, hpb] at hpa
  exact String.toList_injective hpa.symm

section Ren

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM storeStruct? loadStruct?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr rdArrA wrArrA
  armOf callArrRegs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renStore renLoad)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite)

/-- No call operand is an array without array positions. -/
theorem callArrRegs_none : ∀ (j : Nat) (os : List LOperand),
    callArrRegs (fun _ => none) j os = []
  | _, [] => rfl
  | j, o :: os => by cases o <;> simp [callArrRegs, callArrRegs_none]

/-- A store-tagged instruction that is not a runtime-indexed store reads and writes no array,
    without callee. -/
theorem rdArr_wrArr_store_none (wire : LinstrR) (w m : Nat) (h : storeStruct? wire = none) :
    rdArr (fun _ _ => none) (wire, .store w m) = [] ∧
      wrArr (fun _ => none) (wire, .store w m) = none := by
  unfold rdArr wrArr
  cases armOf (wire, .store w m) <;>
    simp [rdArrA, wrArrA, arrReads, arrWrite, h, callArrRegs_none]

/-- A load-tagged instruction reads at most its base and writes no array, without callee;
    when it is not a runtime-indexed load it reads no array. -/
theorem rdArr_wrArr_load_none (wire : LinstrR) (w m : Nat) (h : loadStruct? wire = none) :
    rdArr (fun _ _ => none) (wire, .load w m) = [] ∧
      wrArr (fun _ => none) (wire, .load w m) = none := by
  unfold rdArr wrArr
  cases armOf (wire, .load w m) <;>
    simp [rdArrA, wrArrA, arrReads, arrWrite, h, callArrRegs_none]

/-- The wire of a runtime-indexed store. -/
theorem storeStruct?_some {wire : LinstrR} {d b x v : String}
    (h : storeStruct? wire = some (d, b, x, v)) :
    ∃ sc, wire = .Lopn [.reg d] "STOREIDX" [.arrIdx b x sc, .reg v] := by
  unfold storeStruct? at h
  split at h
  · split at h
    · rename_i opn _ _ _ _ _ hop
      subst hop
      cases h
      exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- The wire of a runtime-indexed load. -/
theorem loadStruct?_some {wire : LinstrR} {d b x : String}
    (h : loadStruct? wire = some (d, b, x)) :
    ∃ sc, wire = .Lopn [.reg d] "LOADIDX" [.arrIdx b x sc] := by
  unfold loadStruct? at h
  split at h
  · split at h
    · rename_i opn _ _ _ _ hop
      subst hop
      cases h
      exact ⟨_, rfl⟩
    · cases h
  · cases h

/-- The renaming keeps a wire that is not a runtime-indexed store. -/
theorem renStore_of_none (ρ : String → String) {wire : LinstrR} (h : storeStruct? wire = none) :
    renStore ρ wire = wire := by
  unfold renStore
  split
  · rename_i dst opn b x sc v
    split
    · rename_i hop
      subst hop
      simp [storeStruct?] at h
    · rfl
  · rfl

/-- The renaming keeps a wire that is not a runtime-indexed load. -/
theorem renLoad_of_none (ρ : String → String) {wire : LinstrR} (h : loadStruct? wire = none) :
    renLoad ρ wire = wire := by
  unfold renLoad
  split
  · rename_i dst opn b x sc
    split
    · rename_i hop
      subst hop
      simp [loadStruct?] at h
    · rfl
  · rfl

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (MemTag)

/-- The tags of the exported bindings: a register binding, a runtime-indexed load and a
    runtime-indexed store. -/
def PlainTag (i : LinstrRM) : Prop :=
  match i.2 with
  | .reg _ | .load _ _ | .store _ _ => True
  | _ => False

/-- **The reads and the write of a renamed instruction** with a plain tag, without callee, are
    the renamed reads and write. -/
theorem rdArr_wrArr_renArr (ρ : String → String) (i : LinstrRM) (hi : PlainTag i) :
    rdArr (fun _ _ => none) (renArr ρ i) = (rdArr (fun _ _ => none) i).map ρ ∧
      wrArr (fun _ => none) (renArr ρ i) = (wrArr (fun _ => none) i).map ρ := by
  obtain ⟨wire, tag⟩ := i
  cases tag with
  | reg c =>
      have h1 := FieldDomComplete.rdArr_wrArr_regTag wire c (fun _ _ => none) (fun _ => none)
        (fun _ _ => rfl) (fun _ => rfl)
      have h2 := FieldDomComplete.rdArr_wrArr_regTag
        (X86Backend.ImageCoalesceCfg.renCallW ρ wire) c (fun _ _ => none) (fun _ => none)
        (fun _ _ => rfl) (fun _ => rfl)
      change rdArr _ (X86Backend.ImageCoalesceCfg.renCallW ρ wire, .reg c) = _ ∧
        wrArr _ (X86Backend.ImageCoalesceCfg.renCallW ρ wire, .reg c) = _
      rw [h1.1, h1.2, h2.1, h2.2]
      exact ⟨rfl, rfl⟩
  | load w m =>
      change rdArr _ (renLoad ρ wire, .load w m) = _ ∧ wrArr _ (renLoad ρ wire, .load w m) = _
      cases hs : loadStruct? wire with
      | none =>
          rw [renLoad_of_none ρ hs, (rdArr_wrArr_load_none wire w m hs).1,
            (rdArr_wrArr_load_none wire w m hs).2]
          exact ⟨rfl, rfl⟩
      | some t =>
          obtain ⟨d, b, x⟩ := t
          obtain ⟨sc, rfl⟩ := loadStruct?_some hs
          exact ⟨rfl, rfl⟩
  | store w m =>
      change rdArr _ (renStore ρ wire, .store w m) = _ ∧
        wrArr _ (renStore ρ wire, .store w m) = _
      cases hs : storeStruct? wire with
      | none =>
          rw [renStore_of_none ρ hs, (rdArr_wrArr_store_none wire w m hs).1,
            (rdArr_wrArr_store_none wire w m hs).2]
          exact ⟨rfl, rfl⟩
      | some t =>
          obtain ⟨d, b, x, v⟩ := t
          obtain ⟨sc, rfl⟩ := storeStruct?_some hs
          exact ⟨rfl, rfl⟩
  | _ => exact absurd hi id

end Ren

section WebShape

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainShape rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen stepRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)

variable {w : Nat → String → String} {body : List LinstrRM} {obs : List String}

/-- The instruction of the renamed body at a position. -/
theorem getElem?_webRen (k : Nat) :
    (webRen w (fun _ => none) body)[k]? =
      (body[k]?).map fun i => renArr (stepRen w (fun _ => none) k i) i := by
  unfold webRen
  rw [List.getElem?_mapIdx]

/-- **A read of the renamed body** is the image under `w` of a read of the body at the same
    position, when no instruction reads the array it writes and `w` fixes the names read after
    the body at its end. -/
theorem readAt_webRen (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d →
      d ∉ rdArr (fun _ _ => none) i)
    (hfix : ∀ r ∈ obs, w body.length r = r) {j : Nat} {r' : String}
    (h : ReadAt (webRen w (fun _ => none) body) (fun _ _ => none) obs j r') :
    ∃ r, ReadAt body (fun _ _ => none) obs j r ∧ r' = w j r := by
  rcases h with ⟨i', hi', hr'⟩ | ⟨hj, hr'⟩
  · rw [getElem?_webRen] at hi'
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
    rw [(rdArr_wrArr_renArr _ i (hplain i (List.mem_of_getElem? hi))).1] at hr'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    refine ⟨r, Or.inl ⟨i, hi, hr⟩, ?_⟩
    unfold stepRen
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun hw => hself j i r hi hw hr)]
  · have hl : (webRen w (fun _ => none) body).length = body.length := by
      simp [webRen]
    rw [hl] at hj
    subst hj
    exact ⟨r', Or.inr ⟨rfl, hr'⟩, (hfix r' hr').symm⟩

/-- **A write of the renamed body** is the image under `w` after the instruction of a write
    of the body at the same position. -/
theorem wrAt_webRen (hplain : ∀ i ∈ body, PlainTag i) {k : Nat} {r' : String}
    (h : WrAt (webRen w (fun _ => none) body) (fun _ => none) k r') :
    ∃ d, WrAt body (fun _ => none) k d ∧ r' = w (k + 1) d := by
  obtain ⟨i', hi', hw'⟩ := h
  rw [getElem?_webRen] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  rw [(rdArr_wrArr_renArr _ i (hplain i (List.mem_of_getElem? hi))).2] at hw'
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hw'
  refine ⟨d, ⟨i, hi, hd⟩, ?_⟩
  unfold stepRen
  rw [ite_eq_left_of_eq_true _ _ (eq_true hd)]

/-- **A consumption in the renamed body** is the image under `w` of a consumption in the body
    at the same position. -/
theorem consumedAt_webRen (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d →
      d ∉ rdArr (fun _ _ => none) i) {c : Nat} {r' : String}
    (h : ConsumedAt (webRen w (fun _ => none) body) (fun _ _ => none) (fun _ => none) c r') :
    ∃ r, ConsumedAt body (fun _ _ => none) (fun _ => none) c r ∧ r' = w c r := by
  obtain ⟨i', d', hi', hr', hw', -⟩ := h
  rw [getElem?_webRen] at hi'
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hi'
  have hrw := rdArr_wrArr_renArr (stepRen w (fun _ => none) c i) i
    (hplain i (List.mem_of_getElem? hi))
  rw [hrw.1] at hr'
  rw [hrw.2] at hw'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hw'
  have hne : d ≠ r := fun e => hself c i d hi hd (e ▸ hr)
  refine ⟨r, ⟨i, d, hi, hr, hd, hne⟩, ?_⟩
  unfold stepRen
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun hw => hself c i r hi hw hr)]

/-- **The first two conjuncts of the store-chain shape are kept by the renaming by webs**:
    reads follow writes and consumed names are dead in the renamed body, when its names have no
    `#`, no instruction reads the array it writes, and the webs fix the names read after the
    body at its end. -/
theorem chainShape₁₂_webRen (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat)
    (hw : w = webLook tab) (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i)
    (hfix : ∀ r ∈ obs, w body.length r = r)
    (hhR : ∀ j r, ReadAt body (fun _ _ => none) obs j r → '#' ∉ r.toList)
    (hhW : ∀ k d, WrAt body (fun _ => none) k d → '#' ∉ d.toList)
    (h1 : ∀ j r k, ReadAt body (fun _ _ => none) obs j r → WrAt body (fun _ => none) k r →
      k < j)
    (h2 : ∀ c r j, ConsumedAt body (fun _ _ => none) (fun _ => none) c r →
      ReadAt body (fun _ _ => none) obs j r → j ≤ c) :
    (∀ j r k, ReadAt (webRen w (fun _ => none) body) (fun _ _ => none) obs j r →
        WrAt (webRen w (fun _ => none) body) (fun _ => none) k r → k < j)
      ∧ (∀ c r j,
        ConsumedAt (webRen w (fun _ => none) body) (fun _ _ => none) (fun _ => none) c r →
        ReadAt (webRen w (fun _ => none) body) (fun _ _ => none) obs j r → j ≤ c) := by
  subst hw
  constructor
  · intro j r' k hR hW
    obtain ⟨r, hr, rfl⟩ := readAt_webRen hplain hself hfix hR
    obtain ⟨d, hd, he⟩ := wrAt_webRen hplain hW
    obtain rfl := webLook_inj tab (hhR j r hr) (hhW k d hd) he
    exact h1 j r k hr hd
  · intro c r' j hc hR
    obtain ⟨r, hr, rfl⟩ := consumedAt_webRen hplain hself hc
    obtain ⟨r₁, hr₁, he⟩ := readAt_webRen hplain hself hfix hR
    have hrr : ReadAt body (fun _ _ => none) obs c r := by
      obtain ⟨i, d, hi, hri, -, -⟩ := hr
      exact Or.inl ⟨i, hi, hri⟩
    obtain rfl := webLook_inj tab (hhR c r hrr) (hhR j r₁ hr₁) he
    exact h2 c r j hr hr₁

end WebShape

section Live

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (rdArr wrArr rdArrA wrArrA
  armOf armCheck coInstrB_eq_armCheck CoArm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webB webB_instr webInstrB webSuccs
  webB_live_pred stepRen)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (subB_spec)

/-- An instruction checked by the arm of an array access, of a sequential instruction or of an
    operation: no call and no jump. -/
def StraightArm (i : LinstrRM) : Prop :=
  armOf i = .arr ∨ armOf i = .seq ∨ armOf i = .op

/-- **The liveness that the webs check**: at an accepted body, the arrays an instruction of a
    straight arm reads are live before it, and so is every array live after it that it does not
    write. -/
theorem webB_live {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hacc : webB w body L obs (fun _ _ => none) (fun _ => none) = true)
    {k : Nat} {i : LinstrRM} (hi : body[k]? = some i) (hs : StraightArm i) :
    (∀ r ∈ rdArr (fun _ _ => none) i, r ∈ L k)
      ∧ ∀ r ∈ L (k + 1), wrArr (fun _ => none) i ≠ some r → r ∈ L k := by
  have h := webB_instr hacc hi
  unfold webInstrB at h
  simp only [Bool.and_eq_true] at h
  have hc := h.1.1.1
  rw [coInstrB_eq_armCheck] at hc
  unfold rdArr wrArr
  rcases hs with ha | ha | ha <;> rw [ha] at hc ⊢ <;>
    simp only [armCheck, Bool.and_eq_true] at hc <;> simp only [rdArrA, wrArrA]
  · have hsub := subB_spec hc.2
    refine ⟨fun r hr => hsub r (List.mem_append_left _ hr), fun r hr hw => hsub r
      (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by simpa using fun e => hw e.symm⟩))⟩
  · have hsub := subB_spec hc
    exact ⟨fun r hr => absurd hr List.not_mem_nil, fun r hr _ => hsub r hr⟩
  · have hsub := subB_spec hc.2
    refine ⟨fun r hr => hsub r (List.mem_append_left _ hr), fun r hr hw => hsub r
      (List.mem_append_right _ (List.mem_filter.mpr ⟨hr, by simpa using fun e => hw e.symm⟩))⟩

/-- A straight instruction: an operation checked by a straight arm. -/
def StraightOp (i : LinstrRM) : Prop :=
  StraightArm i ∧ ∃ ds o ss, i.1 = .Lopn ds o ss

/-- **A web name is constant along a stretch where its array is live and not written**: at an
    accepted body of straight instructions, when `r` is live at `b` and no instruction strictly
    between `a` and `b` writes it, the position map renames `r` alike after `a` and at `b`. -/
theorem webB_const {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hacc : webB w body L obs (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → StraightOp i) {r : String}
    {a : Nat} :
    ∀ b, a < b → b ≤ body.length → r ∈ L b →
      (∀ (j : Nat) (i : LinstrRM), a < j → j < b → body[j]? = some i →
        wrArr (fun _ => none) i ≠ some r) →
      w (a + 1) r = w b r
  | 0, hab, _, _, _ => absurd hab (Nat.not_lt_zero _)
  | b + 1, hab, hb, hr, hnw => by
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hab) with rfl | hlt
      · rfl
      · obtain ⟨i, hib⟩ : ∃ i, body[b]? = some i :=
          ⟨body[b], List.getElem?_eq_getElem (by omega)⟩
        have hnb := hnw b i hlt (by omega) hib
        have hrb := (webB_live hacc hib (hst b i hib).1).2 r hr hnb
        have ih := webB_const hacc hst b hlt (by omega) hrb
          (fun j i' hj hjb hi' => hnw j i' hj (by omega) hi')
        obtain ⟨ds, o, ss, hop⟩ := (hst b i hib).2
        have hsucc : b + 1 ∈ webSuccs body b i := by
          unfold webSuccs
          rw [hop]
          exact List.mem_singleton_self _
        exact ih.trans ((webB_live_pred hacc hib hsucc hr).1 hnb)

/-- **A web name is constant, and its array live, along a stretch where it is not written**:
    when `r` is live at `b` and no instruction in `[a, b)` writes it, `r` is live at `a` and
    the position map renames it alike at `a` and at `b`. -/
theorem webB_const' {w : Nat → String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} (hacc : webB w body L obs (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → StraightOp i) {r : String}
    {a : Nat} :
    ∀ b, a ≤ b → b ≤ body.length → r ∈ L b →
      (∀ (j : Nat) (i : LinstrRM), a ≤ j → j < b → body[j]? = some i →
        wrArr (fun _ => none) i ≠ some r) →
      r ∈ L a ∧ w a r = w b r
  | 0, hab, _, hr, _ => by
      obtain rfl : a = 0 := by omega
      exact ⟨hr, rfl⟩
  | b + 1, hab, hb, hr, hnw => by
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact ⟨hr, rfl⟩
      · obtain ⟨i, hib⟩ : ∃ i, body[b]? = some i :=
          ⟨body[b], List.getElem?_eq_getElem (by omega)⟩
        have hnb := hnw b i (by omega) (by omega) hib
        have hrb := (webB_live hacc hib (hst b i hib).1).2 r hr hnb
        have ih := webB_const' hacc hst b (by omega) (by omega) hrb
          (fun j i' hj hjb hi' => hnw j i' hj (by omega) hi')
        obtain ⟨ds, o, ss, hop⟩ := (hst b i hib).2
        have hsucc : b + 1 ∈ webSuccs body b i := by
          unfold webSuccs
          rw [hop]
          exact List.mem_singleton_self _
        exact ⟨ih.1, ih.2.trans ((webB_live_pred hacc hib hsucc hr).1 hnb)⟩

end Live

section Consume

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen stepRen webB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)

variable {body : List LinstrRM}

/-- The write of the body at a position, renamed after the instruction, is a write of the
    renamed body. -/
theorem wrAt_webRen_of {w : Nat → String → String} (hplain : ∀ i ∈ body, PlainTag i)
    {k : Nat}
    {d : String} (h : WrAt body (fun _ => none) k d) :
    WrAt (webRen w (fun _ => none) body) (fun _ => none) k (w (k + 1) d) := by
  obtain ⟨i, hi, hd⟩ := h
  refine ⟨renArr (stepRen w (fun _ => none) k i) i, by rw [getElem?_webRen, hi]; rfl, ?_⟩
  rw [(rdArr_wrArr_renArr _ i (hplain i (List.mem_of_getElem? hi))).2, hd]
  unfold stepRen
  simp [hd]

/-- A consumption in the body is, renamed at its position, a consumption in the body renamed
    by webs. -/
theorem consumedAt_webRen_of (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat)
    (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i)
    {c : Nat} {r : String} (h : ConsumedAt body (fun _ _ => none) (fun _ => none) c r)
    (hr : '#' ∉ r.toList) (hd : ∀ d, WrAt body (fun _ => none) c d → '#' ∉ d.toList) :
    ConsumedAt (webRen (webLook tab) (fun _ => none) body) (fun _ _ => none) (fun _ => none) c
      (webLook tab c r) := by
  obtain ⟨i, d, hi, hri, hdi, hne⟩ := h
  have hrw := rdArr_wrArr_renArr (stepRen (webLook tab) (fun _ => none) c i) i
    (hplain i (List.mem_of_getElem? hi))
  refine ⟨_, webLook tab (c + 1) d, by rw [getElem?_webRen, hi]; rfl, ?_, ?_, ?_⟩
  · rw [hrw.1]
    refine List.mem_map.mpr ⟨r, hri, ?_⟩
    unfold stepRen
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun hw => hself c i r hi hw hri)]
  · rw [hrw.2, hdi]
    unfold stepRen
    simp [hdi]
  · intro he
    exact hne (webLook_inj tab (hd d ⟨i, hi, hdi⟩) hr he)

/-- **The consumption facts of one chain are kept by the renaming by webs**, from the root
    renamed at the entry: at an accepted body of straight instructions with a plain tag whose
    names have no `#`, where no instruction reads the array it writes, every array is written
    at most once, and reads follow writes. -/
theorem chainConsume_webRen (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obs obsW : List String}
    (hacc : webB (webLook tab) body L obsW (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → StraightOp i)
    (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i)
    (hhR : ∀ j r, ReadAt body (fun _ _ => none) obs j r → '#' ∉ r.toList)
    (hhW : ∀ k d, WrAt body (fun _ => none) k d → '#' ∉ d.toList)
    (hssa : ∀ k₁ k₂ d, WrAt body (fun _ => none) k₁ d → WrAt body (fun _ => none) k₂ d →
      k₁ = k₂)
    (h1 : ∀ j r k, ReadAt body (fun _ _ => none) obs j r → WrAt body (fun _ => none) k r →
      k < j)
    {x : String} (hx : '#' ∉ x.toList)
    (hC : ChainConsume body (fun _ _ => none) (fun _ => none) x) :
    ChainConsume (webRen (webLook tab) (fun _ => none) body) (fun _ _ => none) (fun _ => none)
      (webLook tab 0 x) := by
  obtain ⟨hC1, hC2, hC3⟩ := hC
  -- a consumed array is read there, so it is live there
  have hread : ∀ c r, ConsumedAt body (fun _ _ => none) (fun _ => none) c r →
      ReadAt body (fun _ _ => none) obs c r := by
    rintro c r ⟨i, d, hi, hri, -, -⟩
    exact Or.inl ⟨i, hi, hri⟩
  have hlive : ∀ c r, ConsumedAt body (fun _ _ => none) (fun _ => none) c r →
      c < body.length ∧ r ∈ L c := by
    rintro c r ⟨i, d, hi, hri, -, -⟩
    exact ⟨(List.getElem?_eq_some_iff.mp hi).1, (webB_live hacc hi (hst c i hi).1).1 r hri⟩
  have hcons : ∀ c r, ConsumedAt body (fun _ _ => none) (fun _ => none) c r →
      ConsumedAt (webRen (webLook tab) (fun _ => none) body) (fun _ _ => none) (fun _ => none) c
        (webLook tab c r) := fun c r h =>
    consumedAt_webRen_of tab hplain hself h (hhR c r (hread c r h)) (fun d hd => hhW c d hd)
  refine ⟨?_, ?_, ?_⟩
  · intro k hW
    obtain ⟨d, hd, he⟩ := wrAt_webRen hplain hW
    obtain rfl := webLook_inj tab (hhW k d hd) hx he.symm
    exact hC1 k hd
  · intro k d' hW
    obtain ⟨d, hd, -⟩ := wrAt_webRen hplain hW
    obtain ⟨c, hck, hc⟩ := hC2 k d hd
    refine ⟨c, hck, ?_⟩
    have hconst := webB_const' hacc hst (a := 0) (r := x) c (Nat.zero_le _)
      (hlive c x hc).1.le (hlive c x hc).2 (fun j i _ _ hi hw => hC1 j ⟨i, hi, hw⟩)
    rw [hconst.2]
    exact hcons c x hc
  · intro w' r' k d' hwk hW hW'
    obtain ⟨r, hr, rfl⟩ := wrAt_webRen hplain hW
    obtain ⟨d, hd, -⟩ := wrAt_webRen hplain hW'
    obtain ⟨c, hck, hc⟩ := hC3 w' r k d hwk hr hd
    refine ⟨c, hck, ?_⟩
    have hwc := h1 c r w' (hread c r hc) hr
    have hconst := webB_const' hacc hst (a := w' + 1) (r := r) c (by omega)
      (hlive c r hc).1.le (hlive c r hc).2 (fun j i hj _ hi hw => by
        have := hssa j w' r ⟨i, hi, hw⟩ hr
        omega)
    rw [hconst.2]
    exact hcons c r hc

end Consume

section Alias

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume ChainShape chainShape₃_of_consume rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ArrWebs (webRen stepRen webB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO)

variable {body : List LinstrRM}

/-- **The alias table of a chain renamed by webs**: the alias steps of the renamed body send
    every name it writes to the root renamed at the entry, and keep every other name, when each
    instruction that writes no array keeps the table, each store sends its renamed destination
    to the root of its renamed base, and the base of each store is the root or an array written
    before. -/
theorem getD_foldl_webRen (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obsW : List String}
    (hacc : webB (webLook tab) body L obsW (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → StraightOp i)
    (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i)
    (hhW : ∀ k d, WrAt body (fun _ => none) k d → '#' ∉ d.toList)
    (hssa : ∀ k₁ k₂ d, WrAt body (fun _ => none) k₁ d → WrAt body (fun _ => none) k₂ d →
      k₁ = k₂)
    {x : String} (hx : '#' ∉ x.toList) (hxw : ∀ k, ¬ WrAt body (fun _ => none) k x)
    (hA1 : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → wrArr (fun _ => none) i = none →
      ∀ M ρ, aliasStepO [] M (renArr ρ i) = M)
    (hA2 : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → ∃ b, rdArr (fun _ _ => none) i = [b] ∧
        (∀ M ρ, aliasStepO [] M (renArr ρ i) = M.insert (ρ d) (M.getD (ρ b) (ρ b))) ∧
        (b = x ∨ ∃ k₀, k₀ < k ∧ WrAt body (fun _ => none) k₀ b))
    (y : String) :
    (∀ k, WrAt (webRen (webLook tab) (fun _ => none) body) (fun _ => none) k y →
        ((webRen (webLook tab) (fun _ => none) body).foldl (aliasStepO []) {}).getD y y =
          webLook tab 0 x)
      ∧ ((∀ k, ¬ WrAt (webRen (webLook tab) (fun _ => none) body) (fun _ => none) k y) →
        ((webRen (webLook tab) (fun _ => none) body).foldl (aliasStepO []) {}).getD y y = y) := by
  set body' := webRen (webLook tab) (fun _ => none) body with hb'
  have hlen : body'.length = body.length := by simp [hb', webRen]
  have hwlt : ∀ k z, WrAt body' (fun _ => none) k z → k < body.length := by
    rintro k z ⟨i, hi, -⟩
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hi).1
  suffices hP : ∀ n y,
      ((∃ k, k < n ∧ WrAt body' (fun _ => none) k y) →
        ((body'.take n).foldl (aliasStepO []) {}).getD y y = webLook tab 0 x)
      ∧ ((∀ k, k < n → ¬ WrAt body' (fun _ => none) k y) →
        ((body'.take n).foldl (aliasStepO []) {}).getD y y = y) by
    have h := hP body'.length y
    rw [List.take_length] at h
    refine ⟨fun k hk => h.1 ⟨k, by rw [hlen]; exact hwlt k y hk, hk⟩,
      fun hn => h.2 fun k _ => hn k⟩
  intro n
  induction n with
  | zero =>
      intro y
      refine ⟨fun ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero _), fun _ => ?_⟩
      simp
  | succ n ih =>
      intro y
      rcases Nat.lt_or_ge n body.length with hn | hn
      · obtain ⟨i, hi⟩ : ∃ i, body[n]? = some i := ⟨body[n], List.getElem?_eq_getElem hn⟩
        have hi' : body'[n]? = some (renArr (stepRen (webLook tab) (fun _ => none) n i) i) := by
          rw [hb', getElem?_webRen, hi]; rfl
        rw [List.take_add_one, hi', Option.toList_some, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        cases hw : wrArr (fun _ => none) i with
        | none =>
            rw [hA1 n i hi hw]
            have hnot : ¬ WrAt body' (fun _ => none) n y := by
              intro h
              obtain ⟨d, ⟨i₁, hi₁, hd⟩, -⟩ := wrAt_webRen hplain h
              rw [hi] at hi₁
              cases hi₁
              rw [hw] at hd
              cases hd
            refine ⟨fun ⟨k, hk, h⟩ => (ih y).1 ⟨k, ?_, h⟩,
              fun h => (ih y).2 fun k hk => h k (by omega)⟩
            rcases Nat.lt_or_ge k n with h' | h'
            · exact h'
            · obtain rfl : k = n := by omega
              exact absurd h hnot
        | some d =>
            obtain ⟨b, hb, hstep, hbase⟩ := hA2 n i d hi hw
            rw [hstep]
            have hbd : b ≠ d := fun e =>
              hself n i d hi hw (by rw [hb, e]; exact List.mem_singleton_self _)
            have hsb : stepRen (webLook tab) (fun _ => none) n i b = webLook tab n b := by
              unfold stepRen
              rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hbd (Option.some.inj
                (hw.symm.trans h)).symm)]
            have hsd : stepRen (webLook tab) (fun _ => none) n i d = webLook tab (n + 1) d := by
              unfold stepRen
              simp [hw]
            have hbl : b ∈ L n :=
              (webB_live hacc hi (hst n i hi).1).1 b (by rw [hb]; exact List.mem_singleton_self _)
            have hroot : ((body'.take n).foldl (aliasStepO []) {}).getD (webLook tab n b)
                (webLook tab n b) = webLook tab 0 x := by
              rcases hbase with rfl | ⟨k₀, hk₀, hW₀⟩
              · rw [(ih _).2 (fun k _ hk => by
                  obtain ⟨d₀, hd₀, he⟩ := wrAt_webRen hplain hk
                  obtain rfl := webLook_inj tab (hhW k d₀ hd₀) hx he.symm
                  exact hxw k hd₀)]
                exact ((webB_const' hacc hst (a := 0) n (Nat.zero_le _) hn.le hbl
                  (fun j i _ _ hi hw' => hxw j ⟨i, hi, hw'⟩)).2).symm
              · have hc := webB_const' hacc hst (a := k₀ + 1) (r := b) n (by omega) hn.le hbl
                  (fun j i hj _ hi hw' => by
                    have := hssa j k₀ b ⟨i, hi, hw'⟩ hW₀
                    omega)
                rw [← hc.2]
                exact (ih _).1 ⟨k₀, hk₀, wrAt_webRen_of hplain hW₀⟩
            have hWn : WrAt body' (fun _ => none) n (webLook tab (n + 1) d) :=
              wrAt_webRen_of hplain ⟨i, hi, hw⟩
            have hWn' : ∀ z, WrAt body' (fun _ => none) n z → z = webLook tab (n + 1) d := by
              intro z h
              obtain ⟨d₁, ⟨i₁, hi₁, hd₁⟩, he⟩ := wrAt_webRen hplain h
              rw [hi] at hi₁
              cases hi₁
              rw [hw] at hd₁
              cases hd₁
              exact he
            rw [hsb, hsd]
            by_cases hy : y = webLook tab (n + 1) d
            · subst hy
              rw [Std.HashMap.getD_insert_self]
              exact ⟨fun _ => hroot, fun h => absurd hWn (h n (by omega))⟩
            · rw [Std.HashMap.getD_insert,
                ite_eq_right_of_eq_false _ _ (eq_false (by simpa using Ne.symm hy))]
              refine ⟨fun ⟨k, hk, h⟩ => (ih y).1 ⟨k, ?_, h⟩,
                fun h => (ih y).2 fun k hk => h k (by omega)⟩
              rcases Nat.lt_or_ge k n with h' | h'
              · exact h'
              · obtain rfl : k = n := by omega
                exact absurd (hWn' y h) hy
      · have hk : body'.take (n + 1) = body'.take n := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [hk]
        refine ⟨fun ⟨k, hk, h⟩ => (ih y).1 ⟨k, by have := hwlt k y h; omega, h⟩,
          fun h => (ih y).2 fun k hk => h k (by omega)⟩

/-- **The store-chain shape is kept by the renaming by webs.** At a body accepted by `webB` at
    the position map of the web tables, of straight instructions with a plain tag whose names
    have no `#`, where no instruction reads the array it writes, every array is written at most
    once, and the webs fix the names read after the body at its end: a body of one chain of
    stores from the root `x` (its consumption facts, reads following writes, consumed names
    dead, the alias steps of its stores and of its other instructions, and the base of each
    store the root or an array written before) has, renamed by the webs, the store-chain shape
    under the alias table of the renamed body. -/
theorem chainShape_webRen (tab : WebSt × Std.HashSet Nat × Std.HashSet Nat)
    {L : Nat → List String} {obs obsW : List String}
    (hacc : webB (webLook tab) body L obsW (fun _ _ => none) (fun _ => none) = true)
    (hst : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → StraightOp i)
    (hplain : ∀ i ∈ body, PlainTag i)
    (hself : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → d ∉ rdArr (fun _ _ => none) i)
    (hfix : ∀ r ∈ obs, webLook tab body.length r = r)
    (hhR : ∀ j r, ReadAt body (fun _ _ => none) obs j r → '#' ∉ r.toList)
    (hhW : ∀ k d, WrAt body (fun _ => none) k d → '#' ∉ d.toList)
    (hssa : ∀ k₁ k₂ d, WrAt body (fun _ => none) k₁ d → WrAt body (fun _ => none) k₂ d →
      k₁ = k₂)
    (h1 : ∀ j r k, ReadAt body (fun _ _ => none) obs j r → WrAt body (fun _ => none) k r →
      k < j)
    (h2 : ∀ c r j, ConsumedAt body (fun _ _ => none) (fun _ => none) c r →
      ReadAt body (fun _ _ => none) obs j r → j ≤ c)
    {x : String} (hx : '#' ∉ x.toList)
    (hC : ChainConsume body (fun _ _ => none) (fun _ => none) x)
    (hA1 : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → wrArr (fun _ => none) i = none →
      ∀ M ρ, aliasStepO [] M (renArr ρ i) = M)
    (hA2 : ∀ (k : Nat) (i : LinstrRM) (d : String), body[k]? = some i →
      wrArr (fun _ => none) i = some d → ∃ b, rdArr (fun _ _ => none) i = [b] ∧
        (∀ M ρ, aliasStepO [] M (renArr ρ i) = M.insert (ρ d) (M.getD (ρ b) (ρ b))) ∧
        (b = x ∨ ∃ k₀, k₀ < k ∧ WrAt body (fun _ => none) k₀ b)) :
    ChainShape
      (fun y => ((webRen (webLook tab) (fun _ => none) body).foldl (aliasStepO []) {}).getD y y)
      (webRen (webLook tab) (fun _ => none) body) (fun _ _ => none) (fun _ => none) obs := by
  obtain ⟨g1, g2⟩ := chainShape₁₂_webRen tab rfl hplain hself hfix hhR hhW h1 h2
  have hcons := chainConsume_webRen tab hacc hst hplain hself hhR hhW hssa h1 hx hC
  have hal := getD_foldl_webRen tab hacc hst hplain hself hhW hssa hx hC.1 hA1 hA2
  exact ⟨g1, g2, chainShape₃_of_consume hcons (fun w n hw => (hal n).1 w hw)
    (fun n hn => (hal n).2 hn)⟩

end Alias

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
