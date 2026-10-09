/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallOut
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
`ImageAddrCallArr.ArrCallee`, and for a layout whose result is a word array the record writes
at a pointer register, as `ImageAddrCallOut.OutCallee`. The procedure summary applies `sem` to the argument words as
source integers (and the array words as a source array) and decodes the value as a word. The
interface has the footprint, postcondition, public relation and clobbered registers of the
record; its precondition is the precondition of the record at an entry state at whose
argument words the summary is defined, and `CalleeSpec.restrictPre` carries a specification
of the record's interface to it.

## Main definitions

* `wordSummary`, `arrSummary`: the procedure summaries of a linked function on words, and on
  words followed by an array.
* `wordSig`, `arrSig`: the interfaces of a linked function for the two readings.
* `WordLayout`, `ArrLayout`: the layout passes the argument words in the registers of the
  names, then (for `ArrLayout`) the array at the register of the pointer name, and returns
  the result in the register of the result name.
* `readIns`: the summary input of a list of parameters, each a scalar or a word array.
* `outSummary`, `outSig`, `OutLayout`: the summary, interface and layout of a linked function
  whose result is the `n` words of its first parameter, the destination, at the register of
  a pointer name.

## Main results

* `CalleeSpec.restrictPre`: a specification of an interface is a specification of the same
  interface with a stronger precondition.
* `wordCallee_of_linkedFn`: a linked function with a word layout is a `WordCallee`.
* `arrCallee_of_linkedFn`: a linked function with an array layout is an `ArrCallee`.
* `pub_of_ptrArg`: under an array layout, agreement on `%rsp`, the bounded word arguments and
  the array pointer register gives the public relation of the record.
* `outCallee_of_linkedFn`: a linked function with an out layout is an `OutCallee`.
* `pub_of_outPtr`: under an out layout, agreement on `%rsp` and the public parameters, the
  destination among them, gives the public relation of the record.
* `readIns_arr`: the summary input of scalars followed by one array is `readArgs`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk phys)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (cellAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun CalleeSig CalleeSpec InFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCall (WordCallee)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallArr (arrWords readArgs ArrCallee)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 InRange8)
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiArg ArgKind ResultKind wordsAt)
open CatCrypt.Crypto.Hax (LinkedFn wordVal dec_wordVal insVals insArrArgs)
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

/-! ## 5. A linked function with a word-array result -/

/-- The argument words of a parameter at a state: the word of the register of the name for
    a scalar, the `m` words at the address in that register for an array of `m` words. -/
def readIn (p : String × ArgKind) (s : AState) : List (BitVec 64) :=
  match p.2 with
  | .scalar => [s.regs (phys p.1)]
  | .words m => arrWords s.mem (s.regs (phys p.1)) m

/-- **The summary input of a list of parameters at a state**: the argument words of each
    parameter, in order. -/
def readIns (ins : List (String × ArgKind)) (s : AState) : List (BitVec 64) :=
  ins.flatMap (readIn · s)

/-- The summary input of scalars of the names `ws` followed by an array of `n` words at
    `pa` is `readArgs ws pa n`. -/
theorem readIns_arr (ws : List String) (pa : String) (n : Nat) (s : AState) :
    readIns (ws.map (fun w => (w, ArgKind.scalar)) ++ [(pa, ArgKind.words n)]) s =
      readArgs ws pa n s := by
  simp only [readIns, readIn, readArgs, List.flatMap_append, List.flatMap_map,
    List.flatMap_singleton]
  induction ws <;> simp_all

/-- The source values of the summary input of a list of parameters are the values the
    parameters read. -/
theorem insVals_readIns (s : AState) :
    ∀ ins : List (String × ArgKind),
      insVals (ins.map (·.2)) (readIns ins s) = ins.map fun p => readRK (phys p.1, p.2) s
  | [] => rfl
  | (w, .scalar) :: ins => by
      have ih := insVals_readIns s ins
      simp only [readIns, List.flatMap_cons, readIn] at ih ⊢
      simp [insVals, readRK, wordVal, ih]
  | (w, .words m) :: ins => by
      have ih := insVals_readIns s ins
      have hl : (arrWords s.mem (s.regs (phys w)) m).length = m := by simp [arrWords]
      simp only [readIns, List.flatMap_cons, readIn] at ih ⊢
      simp only [List.map_cons, insVals, List.take_left' hl, List.drop_left' hl, ih, readRK,
        wordsAt_eq]

/-- **An out layout**: the parameters of the layout are, in order, the parameters `ins`, each
    a name with its kind, in the registers of the names; the first parameter is the
    destination, an array of `n` words at the register of the general-purpose name `po`; the
    result is read back as the `n` words at the entry value of that register; and the
    footprint of the record is among the `l.frame` bytes below its entry stack register and
    those `n` words. -/
structure OutLayout (l : LinkedFn) (ins : List (String × ArgKind)) (po : String) (n : Nat) :
    Prop where
  /-- The parameters: the kind of each parameter of `ins` in the register of its name. -/
  args : l.layout.args.map (fun a => (a.reg, a.kind)) = ins.map fun p => (phys p.1, p.2)
  /-- The first parameter is the destination: `n` words at the register of `po`. -/
  dest : ins.head? = some (po, ArgKind.words n)
  /-- The result is the `n` words at the register of `po`. -/
  result : l.layout.result = .words (phys po) n
  /-- The parameter names are general-purpose names. -/
  ins_gp : ∀ p ∈ ins, gpOk p.1 = true
  /-- The footprint is among the frame bytes and the `n` words at the pointer of `po`. -/
  foot : ∀ s x, l.foot s x →
    InFrame (s.regs "%rsp") l.frame x ∨ ∃ j < n, InRange8 (cellAt (s.regs (phys po)) j) x

/-- Under an out layout the pointer name of the destination is a general-purpose name. -/
theorem OutLayout.po_gp {l : LinkedFn} {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) : gpOk po = true :=
  hL.ins_gp (po, ArgKind.words n) (List.mem_of_head? hL.dest)

/-- **The procedure summary of a linked function with a word-array result of length `n`**:
    the array positions of the kinds of `ins`, no word result, and as array result the
    meaning at the source values of the argument words under the kinds of `ins`, decoded as
    an array of words. -/
def outSummary (l : LinkedFn) (ins : List (String × ArgKind)) (n : Nat) :
    LprogIsa.ProcSummary where
  arity := l.params.length
  run := fun _ => none
  arrArgs := insArrArgs (ins.map (·.2))
  out := some n
  runOut m xs := (l.sem (insVals (ins.map (·.2)) xs)).bind (dec (.arr m (.word 64)))

/-- **The interface of a linked function with a word-array result**: the parameter names of
    `ins`, the destination first, no result register, the clobbered registers, footprint,
    postcondition and public relation of the record, and as precondition the precondition of
    the record at an entry state at whose `readIns` the array result of `outSummary` is
    defined. -/
def outSig (l : LinkedFn) (ins : List (String × ArgKind)) (n : Nat) : CalleeSig where
  args := ins.map (·.1)
  res := none
  clob := fun x => l.clob.contains x
  pre := fun s => l.pre s ∧ ((outSummary l ins n).runOut n (readIns ins s)).isSome
  foot := l.foot
  post := l.post
  pub := l.pub

/-- The footprint of the out interface is a footprint of `FootBelowOut` at the frame size of
    the record. -/
theorem footBelowOut_outSig {l : LinkedFn} {ins : List (String × ArgKind)} {po : String}
    {n : Nat} (hL : OutLayout l ins po n) :
    ImageAddrCallOut.FootBelowOut (outSig l ins n) l.frame po n :=
  hL.foot

/-- Under an out layout, the values the layout reads are the source values of `readIns`. -/
theorem read_outLayout {l : LinkedFn} {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) (s : AState) :
    l.layout.args.map (·.read s) = insVals (ins.map (·.2)) (readIns ins s) := by
  rw [map_read_eq, hL.args, insVals_readIns, List.map_map]
  rfl

/-- The source array of the words at an address decodes as the function of those words. -/
theorem dec_arr_wordsAt (m : AMem) (p : BitVec 64) (n : Nat) :
    dec (.arr n (.word 64)) (.array (wordsAt m p n)) =
      some fun j : Fin n => read64 m (cellAt p j.val) := by
  have hm : ∀ xs : List (BitVec 64), (xs.map wordVal).mapM (dec (.word 64)) = some xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [List.mapM_cons, dec_wordVal, ih]
  have hl : (arrWords m p n).length = n := by simp [arrWords]
  have hw : wordsAt m p n = (arrWords m p n).map wordVal := by
    simp [wordsAt, arrWords, wordVal, cellAt, List.map_map, Function.comp_def]
  rw [hw]
  simp only [dec, hm, Option.bind_some, dif_pos hl]
  congr 1
  funext j
  simp [arrWords]

/-- **A linked function with an out layout is an out callee.** Under `OutLayout`, the out
    interface `outSig` has the reading `outSummary` on the summary input `readIns ins`: the
    words the record writes at the pointer of `po` are the array result. -/
theorem outCallee_of_linkedFn {l : LinkedFn} {ins : List (String × ArgKind)} {po : String}
    {n : Nat} (hL : OutLayout l ins po n) :
    ImageAddrCallOut.OutCallee (outSig l ins n) (readIns ins) po n (outSummary l ins n)
      l.pre where
  po_gp := hL.po_gp
  res_none := rfl
  len := rfl
  pre _ h hd := ⟨h, hd⟩
  post s s' h hpost := by
    obtain ⟨hp, hd⟩ := h
    change ((l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind
      (dec (.arr n (.word 64)))).isSome = true at hd
    change (l.sem (insVals (ins.map (·.2)) (readIns ins s))).bind
      (dec (.arr n (.word 64))) = _
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind hd)
    have h := l.post_sem s s' v hp hpost (by rw [read_outLayout hL]; exact hv)
    simp only [CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout.ResultOf, hL.result,
      ResultKind.read] at h
    rw [hv, h, Option.bind_some]
    exact dec_arr_wordsAt _ _ _

/-- **The public relation of an out layout from register agreement.** Under `OutLayout`, two
    entry states that agree on `%rsp` and on the register of each parameter of `ins` that is
    public (an array, among them the destination, or a scalar whose register carries a bound
    of the layout) are related by the public relation of the record
    (`LinkedFn.pub_of_regs`). -/
theorem pub_of_outPtr {l : LinkedFn} {ins : List (String × ArgKind)} {po : String} {n : Nat}
    (hL : OutLayout l ins po n) {s₁ s₂ : AState}
    (hrsp : s₁.regs "%rsp" = s₂.regs "%rsp")
    (hins : ∀ p ∈ ins, l.layout.argPub ⟨p.1, phys p.1, p.2⟩ = true →
      s₁.regs (phys p.1) = s₂.regs (phys p.1)) : l.pub s₁ s₂ := by
  refine l.pub_of_regs s₁ s₂ hrsp fun a ha hp => ?_
  have hm : (a.reg, a.kind) ∈ ins.map fun p => (phys p.1, p.2) :=
    hL.args ▸ List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨p, hp', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨hr, hk⟩ := he
  rw [← hr]
  refine hins p hp' ?_
  have e : l.layout.argPub ⟨p.1, phys p.1, p.2⟩ = l.layout.argPub a := by
    simp only [CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout.argPub, hk, hr]
  rw [e]
  exact hp

end CatCrypt.Crypto.SecureCompilation.X86Backend.LinkedFnCallee
