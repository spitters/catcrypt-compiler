/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr
public import CatCrypt.Crypto.Hax.Module

@[expose] public section

set_option autoImplicit false

/-!
# The image-call reading of a linked function

A linked function `Hax.LinkedFn` carries a meaning `sem` on source values, a layout that reads
source values off an entry state, and a machine contract whose postcondition gives, in the
result read-back of the layout, the value of `sem` at the values the layout reads
(`LinkedFn.post_sem`). This module reads such a record as a callee of the image call step:
for a layout of word arguments with the result in a register, as `ImageAddrCall.WordCallee`,
and for a layout of word arguments followed by one read-only word array, as
`ImageAddrCallArr.ArrCallee`. The procedure summary applies `sem` to the argument words as
source integers (and the array words as a source array) and decodes the value as a word. The
interface has the footprint, postcondition, public relation and clobbered registers of the
record; its precondition is the precondition of the record at an entry state at whose
argument words the summary is defined, and `CalleeSpec.restrictPre` carries a specification
of the record's interface to it.

## Main definitions

* `wordVal`: a word as a source integer.
* `wordSummary`, `arrSummary`: the procedure summaries of a linked function on words, and on
  words followed by an array.
* `wordSig`, `arrSig`: the interfaces of a linked function for the two readings.
* `WordLayout`, `ArrLayout`: the layout passes the argument words in the registers of the
  names, then (for `ArrLayout`) the array at the register of the pointer name, and returns
  the result in the register of the result name.

## Main results

* `CalleeSpec.restrictPre`: a specification of an interface is a specification of the same
  interface with a stronger precondition.
* `wordCallee_of_linkedFn`: a linked function with a word layout is a `WordCallee`.
* `arrCallee_of_linkedFn`: a linked function with an array layout is an `ArrCallee`.
* `pub_of_ptrArg`: under an array layout, agreement on `%rsp`, the bounded word arguments and
  the array pointer register gives the public relation of the record.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr (arrWords readArgs ArrCallee)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiArg ArgKind ResultKind wordsAt)
open CatCrypt.Crypto.Hax (LinkedFn)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax (Value)

/-! ## 1. Restricting the precondition of an interface -/

/-- **A specification under a stronger precondition.** If `X` meets the interface `c` and
    `P` implies the precondition of `c`, then `X` meets `c` with the precondition `P`. -/
theorem CalleeSpec.restrictPre {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {P : AState → Prop} (hP : ∀ s, P s → c.pre s) : CalleeSpec X { c with pre := P } where
  halts s h := hX.halts s (hP s h)
  rsp s t s' h := hX.rsp s t s' (hP s h)
  keep s t s' h := hX.keep s t s' (hP s h)
  frame s t s' h := hX.frame s t s' (hP s h)
  post s t s' h := hX.post s t s' (hP s h)
  ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ := hX.ct s₁ s₂ t₁ t₂ s₁' s₂' (hP s₁ h₁) (hP s₂ h₂)

/-! ## 2. Procedure summaries and interfaces of a linked function -/

/-- A word as a source integer. -/
def wordVal (x : BitVec 64) : Value := .int x.toNat

/-- The word decoding of a word as a source integer is the word. -/
theorem dec_wordVal (x : BitVec 64) : dec (.word 64) (wordVal x) = some x := by
  have h : ((x.toNat : Int)).toNat = x.toNat := Int.toNat_natCast _
  simp only [wordVal, dec, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [if_pos ⟨Int.natCast_nonneg _, by exact_mod_cast x.isLt⟩]

/-- **The procedure summary of a linked function on words**: the meaning at the argument
    words as source integers, decoded as a word. -/
def wordSummary (l : LinkedFn) : LprogIsa.ProcSummary where
  arity := l.params.length
  run xs := (l.sem (xs.map wordVal)).bind (dec (.word 64))

/-- **The procedure summary of a linked function on `k` words and an array**: the meaning at
    the first `k` words as source integers followed by the remaining words as a source array,
    decoded as a word. -/
def arrSummary (l : LinkedFn) (k : Nat) : LprogIsa.ProcSummary where
  arity := l.params.length
  run xs := (l.sem ((xs.take k).map wordVal ++ [.array ((xs.drop k).map wordVal)])).bind
    (dec (.word 64))

/-- **The interface of a linked function read on words**: the argument names `ws`, the
    result name `res`, the clobbered registers, footprint, postcondition and public relation
    of the record, and as precondition the precondition of the record at an entry state at
    whose argument words `wordSummary` is defined. -/
def wordSig (l : LinkedFn) (ws : List String) (res : String) : CalleeSig where
  args := ws
  res := some res
  clob := fun x => l.clob.contains x
  pre := fun s => l.pre s ∧ ((wordSummary l).run (ws.map fun a => s.regs (phys a))).isSome
  foot := l.foot
  post := l.post
  pub := l.pub

/-- **The interface of a linked function read on words and an array**: the argument names
    `ws` followed by the pointer name `pa`, the result name `res`, the clobbered registers,
    footprint, postcondition and public relation of the record, and as precondition the
    precondition of the record at an entry state at whose `readArgs` the summary
    `arrSummary` is defined. -/
def arrSig (l : LinkedFn) (ws : List String) (pa : String) (n : Nat) (res : String) :
    CalleeSig where
  args := ws ++ [pa]
  res := some res
  clob := fun x => l.clob.contains x
  pre := fun s => l.pre s ∧ ((arrSummary l ws.length).run (readArgs ws pa n s)).isSome
  foot := l.foot
  post := l.post
  pub := l.pub

/-- The interface of a linked function with its own precondition and the argument names
    `args` and result name `res`. -/
def baseSig (l : LinkedFn) (args : List String) (res : String) : CalleeSig where
  args := args
  res := some res
  clob := fun x => l.clob.contains x
  pre := l.pre
  foot := l.foot
  post := l.post
  pub := l.pub

/-- A specification of the interface of a linked function on the names `ws` is a
    specification of its word interface. -/
theorem calleeSpec_wordSig {X : CalleeRun} {l : LinkedFn} {ws : List String} {res : String}
    (hX : CalleeSpec X (baseSig l ws res)) : CalleeSpec X (wordSig l ws res) :=
  CalleeSpec.restrictPre hX fun _ h => h.1

/-- A specification of the interface of a linked function on the names `ws ++ [pa]` is a
    specification of its array interface. -/
theorem calleeSpec_arrSig {X : CalleeRun} {l : LinkedFn} {ws : List String} {pa : String}
    {n : Nat} {res : String} (hX : CalleeSpec X (baseSig l (ws ++ [pa]) res)) :
    CalleeSpec X (arrSig l ws pa n res) :=
  CalleeSpec.restrictPre hX fun _ h => h.1

/-! ## 3. Layouts -/

/-- **A word layout**: the parameters of the layout are, in order, scalars in the registers of
    the general-purpose names `ws`; the result is read back from the register of the
    general-purpose name `res`, which the record clobbers. -/
structure WordLayout (l : LinkedFn) (ws : List String) (res : String) : Prop where
  /-- The parameters: a scalar in the register of each name of `ws`. -/
  args : l.layout.args.map (fun a => (a.reg, a.kind)) = ws.map fun w => (phys w, ArgKind.scalar)
  /-- The result is the register of `res`. -/
  result : l.layout.result = .reg (phys res)
  /-- The word argument names are general-purpose names. -/
  ws_gp : ∀ a ∈ ws, gpOk a = true
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is clobbered. -/
  res_clob : l.clob.contains (phys res) = true

/-- **An array layout**: the parameters of the layout are, in order, scalars in the registers
    of the general-purpose names `ws`, then an array of `n` words at the register of the
    general-purpose name `pa`; the result is read back from the register of the
    general-purpose name `res`, which the record clobbers. -/
structure ArrLayout (l : LinkedFn) (ws : List String) (pa : String) (n : Nat) (res : String) :
    Prop where
  /-- The parameters: a scalar in the register of each name of `ws`, then the array. -/
  args : l.layout.args.map (fun a => (a.reg, a.kind)) =
    ws.map (fun w => (phys w, ArgKind.scalar)) ++ [(phys pa, ArgKind.words n)]
  /-- The result is the register of `res`. -/
  result : l.layout.result = .reg (phys res)
  /-- The word argument names are general-purpose names. -/
  ws_gp : ∀ a ∈ ws, gpOk a = true
  /-- The pointer name is a general-purpose name. -/
  pa_gp : gpOk pa = true
  /-- The result name is a general-purpose name. -/
  res_gp : gpOk res = true
  /-- The register of the result name is clobbered. -/
  res_clob : l.clob.contains (phys res) = true

/-- The source value of a register and a parameter kind at a state, as `AbiArg.read`. -/
def readRK (p : String × ArgKind) (s : AState) : Value :=
  match p.2 with
  | .scalar => .int (s.regs p.1).toNat
  | .words n => .array (wordsAt s.mem (s.regs p.1) n)

/-- The values a list of parameters reads depend only on their registers and kinds. -/
theorem map_read_eq (as : List AbiArg) (s : AState) :
    as.map (·.read s) = (as.map fun a => (a.reg, a.kind)).map (readRK · s) := by
  rw [List.map_map]
  refine List.map_congr_left fun a _ => ?_
  cases h : a.kind <;> simp [AbiArg.read, readRK, h]

/-- The source array of the words at an address is the source array of `arrWords`. -/
theorem wordsAt_eq (s : AState) (p : BitVec 64) (n : Nat) :
    wordsAt s.mem p n = (arrWords s.mem p n).map wordVal := by
  simp [wordsAt, arrWords, wordVal, cellAt, List.map_map, Function.comp_def]

/-- Under a word layout, the values the layout reads are the argument words as source
    integers. -/
theorem read_wordLayout {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res) (s : AState) :
    l.layout.args.map (·.read s) = (ws.map fun a => s.regs (phys a)).map wordVal := by
  rw [map_read_eq, hL.args]
  simp [readRK, wordVal, Function.comp_def]

/-- Under an array layout, the values the layout reads are the argument words of `readArgs`
    as source integers followed by its array words as a source array. -/
theorem read_arrLayout {l : LinkedFn} {ws : List String} {pa : String} {n : Nat}
    {res : String} (hL : ArrLayout l ws pa n res) (s : AState) :
    l.layout.args.map (·.read s) =
      ((readArgs ws pa n s).take ws.length).map wordVal ++
        [.array (((readArgs ws pa n s).drop ws.length).map wordVal)] := by
  rw [map_read_eq, hL.args]
  simp [readArgs, readRK, wordVal, wordsAt_eq, Function.comp_def]

/-- The value of a word summary from a value of the meaning: the result read-back of a
    register is the word of the register. -/
theorem run_of_post {l : LinkedFn} {r : String} (hr : l.layout.result = .reg r) {s s' : AState}
    {vals : List Value} (hs : l.layout.args.map (·.read s) = vals) (hp : l.pre s)
    (hpost : l.post s s') (hd : ((l.sem vals).bind (dec (.word 64))).isSome = true) :
    (l.sem vals).bind (dec (.word 64)) = some (s'.regs r) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hd)
  have h := l.post_sem s s' v hp hpost (by rw [hs]; exact hv)
  simp only [CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout.ResultOf, hr,
    ResultKind.read] at h
  rw [hv, h, Option.bind_some]
  exact dec_wordVal (s'.regs r)

/-! ## 4. The readings -/

/-- **A linked function with a word layout is a word callee.** Under `WordLayout`, the word
    interface `wordSig` has the reading `wordSummary` on the precondition of the record. -/
theorem wordCallee_of_linkedFn {l : LinkedFn} {ws : List String} {res : String}
    (hL : WordLayout l ws res) : WordCallee (wordSig l ws res) res (wordSummary l) l.pre where
  args_gp := hL.ws_gp
  res_eq := rfl
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  pre _ h hd := ⟨h, hd⟩
  post _ _ h hpost := run_of_post hL.result (read_wordLayout hL _) h.1 hpost h.2

/-- **A linked function with an array layout is an array callee.** Under `ArrLayout`, the
    array interface `arrSig` has the reading `arrSummary` on the argument words of `ws` and
    the `n` words at the pointer `pa`, on the precondition of the record. -/
theorem arrCallee_of_linkedFn {l : LinkedFn} {ws : List String} {pa : String} {n : Nat}
    {res : String} (hL : ArrLayout l ws pa n res) :
    ArrCallee (arrSig l ws pa n res) ws pa n res (arrSummary l ws.length) l.pre where
  args_eq := rfl
  ws_gp := hL.ws_gp
  pa_gp := hL.pa_gp
  res_eq := rfl
  res_gp := hL.res_gp
  res_clob := hL.res_clob
  pre _ h hd := ⟨h, hd⟩
  post _ _ h hpost := run_of_post hL.result (read_arrLayout hL _) h.1 hpost h.2

/-- **The public relation of an array layout from register agreement.** Under `ArrLayout`,
    two entry states that agree on `%rsp`, on the register of each word argument of `ws` that
    carries a bound of the layout, and on the register of the pointer name `pa` are related
    by the public relation of the record: the array parameter is public under the layout
    (`AbiLayout.argPub` of `.words n` is `true`). -/
theorem pub_of_ptrArg {l : LinkedFn} {ws : List String} {pa : String} {n : Nat}
    {res : String} (hL : ArrLayout l ws pa n res) {s₁ s₂ : AState}
    (hrsp : s₁.regs "%rsp" = s₂.regs "%rsp")
    (hws : ∀ w ∈ ws, l.layout.bounds.any (·.1 == phys w) = true →
      s₁.regs (phys w) = s₂.regs (phys w))
    (hpa : s₁.regs (phys pa) = s₂.regs (phys pa)) : l.pub s₁ s₂ := by
  refine l.pub_of_regs s₁ s₂ hrsp fun a ha hp => ?_
  have hm : (a.reg, a.kind) ∈
      ws.map (fun w => (phys w, ArgKind.scalar)) ++ [(phys pa, ArgKind.words n)] :=
    hL.args ▸ List.mem_map.mpr ⟨a, ha, rfl⟩
  simp only [List.mem_append, List.mem_map, List.mem_singleton, Prod.mk.injEq] at hm
  rcases hm with ⟨w, hw, hr, hk⟩ | ⟨hr, -⟩
  · rw [CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout.argPub, ← hk, ← hr] at hp
    rw [← hr]
    exact hws w hw hp
  · rw [hr]
    exact hpa

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
