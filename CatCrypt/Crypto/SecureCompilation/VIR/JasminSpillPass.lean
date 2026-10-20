/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JazzRoundTrip
public meta import CatCrypt.Crypto.Jasmin.JazzRoundTrip
public import CatCryptCore.Tactics.KatGuard
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.MinMax
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# The spill pass for straight-line Jasmin functions

Jasmin does not spill: every `reg` variable of a function is assigned a register, and
register allocation fails when more `reg` variables are live at an instruction than there
are registers. `spillFn k` rewrites a function whose body is straight line (assignments and
asm operations with register or discarded outputs) so that at most `k` register variables
of a general-purpose word type are live at each instruction.

This module holds the definitions of the pass; the lowering `NFToJasmin.nfToJasmin` applies
it, and `JasminSpill` proves its properties (well-formedness, translation to the `psem.v`
mirror, semantic preservation, the liveness bound).

The pass walks the body once and keeps a set of register holders: for each original
variable `x` whose value is in a register, the variable `h` holding it (`x` itself after its
definition, or a reload variable). Before an instruction it reloads each register operand
that has no holder, making room by evicting the holder whose variable is read furthest in
the future (Belady); it then renames the operands of the instruction to their holders.
An evicted value `x` that is still live gets a `stack` variable and a store `s = h`; a later
reload is `f = s` into a fresh `reg` variable `f`. A value defined by an assignment whose
right-hand side reads only variables the rest of the body never writes (a constant, or a
load `x = inp[i]` from a parameter array with a constant index register `i`) is not stored:
it is reloaded by evaluating that right-hand side again (rematerialisation). Parameters and
results keep their storage; after the body each register result is moved or reloaded into
itself.

Fresh variables are named `spl_n` from a counter `n`; the pass leaves a function whose names
start with `spl_` unchanged.

## Main definitions

* `readsI`, `writesI`, `liveB`: the variables an instruction reads and writes, and liveness
  of a variable before a command.
* `regWordB fn x`: `x` is a `reg` variable of `fn` of a word type of at most 64 bits.
* `liveRegsB k fn`: at most `k` such variables are live at each instruction of the
  straight-line body of `fn`.
* `spillFn k`, `spillUnit k`: the pass on a function and on a unit.
* `runF`: the pass computed from a table of the occurrences of each variable, built once per
  body, a table of storage classes and an index of reload sources; `runF_eq_run` and
  `spillFn_eq_spillFnRef` state that it computes `run`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.Jazz

/-- A Jasmin variable. -/
abbrev JVar := CatCrypt.Crypto.Jasmin.Var

/-! ## 1. Reads, writes and renaming -/

mutual
/-- The local variables an expression reads. -/
def readsE : PExpr → List JVar
  | .Pconst _ => []
  | .Pbool _ => []
  | .Parr_init _ => []
  | .Pvar g => if g.gs then [] else [g.gv.var]
  | .Pget _ _ x i => (if x.gs then [] else [x.gv.var]) ++ readsE i
  | .Psub _ _ _ x i => (if x.gs then [] else [x.gv.var]) ++ readsE i
  | .Pload _ x o => x.var :: readsE o
  | .Papp1 _ e => readsE e
  | .Papp2 _ a b => readsE a ++ readsE b
  | .PappN _ es => readsEs es
  | .Pif _ c a b => readsE c ++ readsE a ++ readsE b

/-- The local variables a list of expressions reads. -/
def readsEs : List PExpr → List JVar
  | [] => []
  | e :: es => readsE e ++ readsEs es
end

/-- A global variable unchanged, a local one renamed by `r`. -/
def renG (r : JVar → JVar) (g : GVar) : GVar :=
  if g.gs then g else { g with gv := { g.gv with var := r g.gv.var } }

mutual
/-- The expression with each local variable read `x` replaced by `r x`. -/
def renE (r : JVar → JVar) : PExpr → PExpr
  | .Pconst z => .Pconst z
  | .Pbool b => .Pbool b
  | .Parr_init n => .Parr_init n
  | .Pvar g => .Pvar (renG r g)
  | .Pget aa ws x i => .Pget aa ws (renG r x) (renE r i)
  | .Psub aa ws n x i => .Psub aa ws n (renG r x) (renE r i)
  | .Pload ws x o => .Pload ws { x with var := r x.var } (renE r o)
  | .Papp1 op e => .Papp1 op (renE r e)
  | .Papp2 op a b => .Papp2 op (renE r a) (renE r b)
  | .PappN op es => .PappN op (renEs r es)
  | .Pif ty c a b => .Pif ty (renE r c) (renE r a) (renE r b)

/-- `renE` on a list of expressions. -/
def renEs (r : JVar → JVar) : List PExpr → List PExpr
  | [] => []
  | e :: es => renE r e :: renEs r es
end

/-- The variables an l-value reads: the address of a memory write, the array and index of
an array write. -/
def readsLv : LVal → List JVar
  | .Lnone _ _ => []
  | .Lvar _ => []
  | .Lmem _ x o => x.var :: readsE o
  | .Laset _ _ x i => x.var :: readsE i
  | .Lasub _ _ _ x i => x.var :: readsE i

/-- The variables an l-value writes. -/
def writesLv : LVal → List JVar
  | .Lvar x => [x.var]
  | .Laset _ _ x _ => [x.var]
  | .Lasub _ _ _ x _ => [x.var]
  | _ => []

/-- The l-value with the variables it only reads renamed by `r`. -/
def renLv (r : JVar → JVar) : LVal → LVal
  | .Lmem ws x o => .Lmem ws { x with var := r x.var } (renE r o)
  | .Laset aa ws x i => .Laset aa ws x (renE r i)
  | .Lasub aa ws n x i => .Lasub aa ws n x (renE r i)
  | lv => lv

/-- A register or discarded output. -/
def simpleLv : LVal → Bool
  | .Lnone _ _ => true
  | .Lvar _ => true
  | _ => false

/-- A straight-line instruction: an assignment, or an asm operation whose outputs are
registers or discarded. -/
def straightI : InstrR → Bool
  | .Cassgn _ _ _ _ => true
  | .Copn lvs _ _ _ => lvs.all simpleLv
  | _ => false

/-- The variables a straight-line instruction reads. -/
def readsI : InstrR → List JVar
  | .Cassgn lv _ _ e => readsE e ++ readsLv lv
  | .Copn _ _ _ es => readsEs es
  | _ => []

/-- The variables a straight-line instruction writes. -/
def writesI : InstrR → List JVar
  | .Cassgn lv _ _ _ => writesLv lv
  | .Copn lvs _ _ _ => lvs.flatMap writesLv
  | _ => []

/-- The instruction with the variables it reads renamed by `r`. -/
def renI (r : JVar → JVar) : InstrR → InstrR
  | .Cassgn lv tag ty e => .Cassgn (renLv r lv) tag ty (renE r e)
  | .Copn lvs tag op es => .Copn lvs tag op (renEs r es)
  | i => i

/-- `x` is live before the command `c` with results `res`: `c` reads `x` before writing it,
or does not write it and `x` is a result. -/
def liveB (res : List JVar) (x : JVar) : List InstrR → Bool
  | [] => res.contains x
  | i :: c => (readsI i).contains x || (!(writesI i).contains x && liveB res x c)

/-! ## 2. Register variables and the liveness check -/

/-- A word type of at most 64 bits, the type of a general-purpose register. -/
def isGprTy : SType → Bool
  | .sword .U8 => true
  | .sword .U16 => true
  | .sword .U32 => true
  | .sword .U64 => true
  | _ => false

/-- The storage class of the name `n` in `fn`: that of the parameter of that name, else
that of the first declaration of the name. -/
def storageOf (fn : JazzFn) (n : String) : Option Storage :=
  match (fn.fd.params.zip fn.paramTys).find? (fun p => p.1.var.var.vname == n) with
  | some p => some p.2.1
  | none => (fn.decls.find? (fun d => d.names.contains n)).map (·.storage)

/-- `x` is a `reg` variable of `fn` of a general-purpose word type. -/
def regWordB (fn : JazzFn) (x : JVar) : Bool :=
  isGprTy x.vtype && storageOf fn x.vname == some .reg

/-- The variables of `reg` live before `c` (those of the results `res` at the end), and
whether at each instruction of `c` at most `k` variables of `reg` are live before it or
written by it. -/
def liveScan (k : Nat) (reg : JVar → Bool) (res : List JVar) :
    List InstrR → List JVar × Bool
  | [] => ((res.filter reg).dedup, true)
  | i :: c =>
      let r := liveScan k reg res c
      let lin := ((readsI i).filter reg ++ r.1.filter (fun x => !(writesI i).contains x)).dedup
      (lin, r.2 && decide ((lin ++ (writesI i).filter reg).dedup.length ≤ k))

/-- The results of a function as variables. -/
def resOf (fn : JazzFn) : List JVar := fn.fd.results.map (·.var)

/-- **The liveness check.** The body of `fn` is straight line and at each instruction at
most `k` register variables (`regWordB`) are live before it or written by it. -/
def liveRegsB (k : Nat) (fn : JazzFn) : Bool :=
  fn.fd.body.all straightI && (liveScan k (regWordB fn) (resOf fn) fn.fd.body).2

/-- At each instruction `i` of the straight-line body of `fn`, every duplicate-free list of
register variables, each written by `i` or live before `i`, has at most `k` elements. -/
def LiveRegs (k : Nat) (fn : JazzFn) : Prop :=
  (∀ i ∈ fn.fd.body, straightI i = true) ∧
  ∀ (p : Nat) (i : InstrR) (rest : List InstrR), fn.fd.body.drop p = i :: rest →
    ∀ S : List JVar, S.Nodup →
      (∀ x ∈ S, regWordB fn x = true ∧ (x ∈ writesI i ∨ liveB (resOf fn) x (i :: rest) = true)) →
      S.length ≤ k

/-! ## 3. The pass -/

/-- Where an evicted value is reloaded from: a stack variable, or the right-hand side `e`
at type `ty` of its definition. -/
inductive Src where
  | slot (s : JVar)
  | remat (ty : SType) (e : PExpr)

/-- The variables a reload reads. -/
def Src.reads : Src → List JVar
  | .slot s => [s]
  | .remat _ e => readsE e

/-- The state of the pass: the register holders `rho` (original variable, holder), the
reload sources `sig`, the counter of fresh names, and the fresh `stack` and `reg`
variables created so far. -/
structure St where
  rho : List (JVar × JVar)
  sig : List (JVar × Src)
  cnt : Nat
  slots : List JVar
  regs : List JVar

/-- The prefix of fresh names. -/
def pfx : String := "spl_"

/-- The fresh name of number `n`. -/
def freshName (n : Nat) : String := pfx ++ toString n

/-- A name starting with the prefix of fresh names. -/
def isFreshName (n : String) : Bool := pfx.toList.isPrefixOf n.toList

/-- The holder of `x`. -/
def lookR (rho : List (JVar × JVar)) (x : JVar) : Option JVar :=
  (rho.find? (fun p => p.1 == x)).map (·.2)

/-- The reload source of `x`. -/
def lookS (sig : List (JVar × Src)) (x : JVar) : Option Src :=
  (sig.find? (fun p => p.1 == x)).map (·.2)

/-- The renaming of reads to holders. -/
def renOf (rho : List (JVar × JVar)) (x : JVar) : JVar := (lookR rho x).getD x

/-- A variable with default information. -/
def vi (x : JVar) : VarI := { var := x }

/-- A local read. -/
def lpv (x : JVar) : PExpr := .Pvar { gv := vi x, gs := false }

/-- The move `d = s`. -/
def mv (d s : JVar) : InstrR := .Cassgn (.Lvar (vi d)) .AT_none d.vtype (lpv s)

/-- The register variables an expression reads, without duplicates. -/
def candReads (cand : JVar → Bool) (e : PExpr) : List JVar := ((readsE e).filter cand).dedup

/-- The distance to the next read of `x` in `c`, `none` when `x` is dead. -/
def nextUse (res : List JVar) (x : JVar) : List InstrR → Option Nat
  | [] => if res.contains x then some 0 else none
  | i :: c =>
      if (readsI i).contains x then some 0
      else if (writesI i).contains x then none
      else (nextUse res x c).map (· + 1)

/-- The eviction score of a holder: twice the distance to the next read (`c.length + 1`
when dead), plus one when the value already has a reload source. -/
def score (st : St) (res : List JVar) (c : List InstrR) (p : JVar × JVar) : Nat :=
  2 * (nextUse res p.1 c).getD (c.length + 1) + (if (lookS st.sig p.1).isSome then 1 else 0)

/-- The element of `l` of maximal `f`, the first one on ties; `none` on the empty list. A
fold, so the pass evaluates without Mathlib's compiled code. -/
def maxBy {α : Type} (f : α → Nat) : List α → Option α
  | [] => none
  | a :: l => some (l.foldl (fun b x => if f b < f x then x else b) a)

theorem foldl_maxBy_mem {α : Type} (f : α → Nat) (l : List α) (a : α) :
    l.foldl (fun b x => if f b < f x then x else b) a ∈ a :: l := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    split
    · rcases List.mem_cons.mp (ih x) with h | h
      · rw [h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp (ih a) with h | h
      · rw [h]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

/-- An element `maxBy` returns is an element of the list. -/
theorem maxBy_mem {α : Type} {f : α → Nat} {l : List α} {p : α} (h : maxBy f l = some p) :
    p ∈ l := by
  cases l with
  | nil => simp [maxBy] at h
  | cons a l =>
    simp only [maxBy, Option.some.injEq] at h
    exact h ▸ foldl_maxBy_mem f l a

/-- `maxBy` returns `none` exactly on the empty list. -/
theorem maxBy_eq_none {α : Type} {f : α → Nat} {l : List α} : maxBy f l = none ↔ l = [] := by
  cases l <;> simp [maxBy]

/-- The holder to evict: the unprotected one of maximal score (Belady). -/
def pickVictim (st : St) (prot : List JVar) (res : List JVar) (c : List InstrR) :
    Option (JVar × JVar) :=
  maxBy (score st res c) (st.rho.filter (fun p => !prot.contains p.1))

/-- The removal of the holders of variables not live before `c`. -/
def pruneDeadHolders (res : List JVar) (c : List InstrR) (st : St) : St :=
  { st with rho := st.rho.filter (fun p => liveB res p.1 c) }

/-- Evict the holder `p.2` of `p.1`: a value live before `c` without a reload source gets a
fresh `stack` variable `s` and the store `s = p.2`. -/
def evict (res : List JVar) (c : List InstrR) (st : St) (p : JVar × JVar) :
    St × List InstrR :=
  let st1 := { st with rho := st.rho.filter (fun q => q.1 != p.1) }
  if liveB res p.1 c && (lookS st.sig p.1).isNone then
    let s : JVar := ⟨freshName st.cnt, p.1.vtype⟩
    ({ st1 with sig := (p.1, .slot s) :: st1.sig, cnt := st.cnt + 1, slots := s :: st.slots },
      [mv s p.2])
  else (st1, [])

/-- Evict holders until `need` more fit among `k`, never one of `prot`. -/
def makeRoom (k need : Nat) (prot res : List JVar) (c : List InstrR) :
    Nat → St → St × List InstrR
  | 0, st => (st, [])
  | fuel + 1, st =>
      if st.rho.length + need ≤ k then (st, [])
      else
        match pickVictim st prot res c with
        | none => (st, [])
        | some p =>
            let r1 := evict res c st p
            let r2 := makeRoom k need prot res c fuel r1.1
            (r2.1, r1.2 ++ r2.2)

/-- The reload of `x` from `src` into `d`. -/
def reloadSrc (rho : List (JVar × JVar)) (d : JVar) : Src → InstrR
  | .slot s => mv d s
  | .remat ty e => .Cassgn (.Lvar (vi d)) .AT_none ty (renE (renOf rho) e)

/-- The reload of `x` into a fresh `reg` variable, which becomes its holder. -/
def reloadFresh (st : St) (x : JVar) (src : Src) : St × List InstrR :=
  let f : JVar := ⟨freshName st.cnt, x.vtype⟩
  ({ st with rho := (x, f) :: st.rho, cnt := st.cnt + 1, regs := f :: st.regs },
    [reloadSrc st.rho f src])

/-- The reload of a variable read by a rematerialised right-hand side: only one without a
holder whose own source reads no register variable. -/
def helper (cand : JVar → Bool) (st : St) (y : JVar) : St × List InstrR :=
  if (lookR st.rho y).isSome then (st, [])
  else
    match lookS st.sig y with
    | some (.remat ty e) =>
        if (candReads cand e).isEmpty then reloadFresh st y (.remat ty e) else (st, [])
    | _ => (st, [])

/-- `helper` over a list. -/
def helpers (cand : JVar → Bool) : St → List JVar → St × List InstrR
  | st, [] => (st, [])
  | st, y :: ys =>
      let r1 := helper cand st y
      let r2 := helpers cand r1.1 ys
      (r2.1, r1.2 ++ r2.2)

/-- The registers a reload from `src` needs. -/
def needOf (cand : JVar → Bool) : Src → Nat
  | .remat _ e => 1 + (candReads cand e).length
  | .slot _ => 1

/-- The helpers of a reload source. -/
def helpersOf (cand : JVar → Bool) (st : St) : Src → St × List InstrR
  | .remat _ e => helpers cand st (candReads cand e)
  | .slot _ => (st, [])

/-- Give `x` a holder before the command `c`: make room, reload the helpers and `x`, and drop
the holders of variables not live before `c`. -/
def loadOne (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR)
    (st : St) (x : JVar) : St × List InstrR :=
  if (lookR st.rho x).isSome then (st, [])
  else
    match lookS st.sig x with
    | none => (st, [])
    | some src =>
        let r1 := makeRoom k (needOf cand src) prot res c st.rho.length st
        let r2 := helpersOf cand r1.1 src
        let r3 := reloadFresh r2.1 x src
        (pruneDeadHolders res c r3.1, r1.2 ++ r2.2 ++ r3.2)

/-- `loadOne` over a list. -/
def loadAll (k : Nat) (cand : JVar → Bool) (prot res : List JVar) (c : List InstrR) :
    St → List JVar → St × List InstrR
  | st, [] => (st, [])
  | st, x :: xs =>
      let r1 := loadOne k cand prot res c st x
      let r2 := loadAll k cand prot res c r1.1 xs
      (r2.1, r1.2 ++ r2.2)

/-- The register variables an instruction writes, without duplicates. -/
def defsOf (cand : JVar → Bool) (i : InstrR) : List JVar := ((writesI i).filter cand).dedup

/-- The register variables an instruction reads, without duplicates. -/
def usesOf (cand : JVar → Bool) (i : InstrR) : List JVar := ((readsI i).filter cand).dedup

/-- No instruction of `c` writes `x`. -/
def stableB (c : List InstrR) (x : JVar) : Bool := !(c.any (fun j => (writesI j).contains x))

/-- The definition `x = e` at type `ty` before `c` can be rematerialised: `ty` is the type
of `x`, `e` does not read `x`, `c` writes no variable `e` reads, and each register variable
`e` reads is rematerialised by a right-hand side reading no register variable. -/
def rematOK (cand : JVar → Bool) (sig : List (JVar × Src)) (c : List InstrR) (x : JVar)
    (ty : SType) (e : PExpr) : Bool :=
  ty == x.vtype && !(readsE e).contains x && (readsE e).all (stableB c) &&
    (candReads cand e).all (fun y => match lookS sig y with
      | some (.remat _ e') => (candReads cand e').isEmpty
      | _ => false)

/-- The state after the instruction `i`, followed by `c`: holders and sources involving a
written variable are dropped, each register variable written becomes its own holder, and a
definition that can be rematerialised records its right-hand side. -/
def afterDef (cand : JVar → Bool) (c : List InstrR) (st : St) (i : InstrR) : St :=
  let w := writesI i
  let rho := st.rho.filter (fun p => !w.contains p.1 && !w.contains p.2)
  let sig := st.sig.filter (fun p => !w.contains p.1 && !(p.2.reads.any w.contains))
  let sig' := match i with
    | .Cassgn (.Lvar x) _ ty e =>
        if cand x.var && rematOK cand sig c x.var ty e then (x.var, .remat ty e) :: sig else sig
    | _ => sig
  { st with rho := (defsOf cand i).map (fun x => (x, x)) ++ rho, sig := sig' }

/-- One instruction `i` followed by `c`: drop dead holders, load the register operands of
`i`, make room for its register outputs, and emit `i` reading the holders. -/
def stepI (k : Nat) (cand : JVar → Bool) (res : List JVar) (st : St) (i : InstrR)
    (c : List InstrR) : St × List InstrR :=
  let st0 := pruneDeadHolders res (i :: c) st
  let U := usesOf cand i
  let r1 := loadAll k cand U res (i :: c) st0 U
  let r2 := makeRoom k (defsOf cand i).length U res (i :: c) r1.1.rho.length r1.1
  (afterDef cand c r2.1 i, r1.2 ++ r2.2 ++ [renI (renOf r2.1.rho) i])

/-- The pass over a body. -/
def goBody (k : Nat) (cand : JVar → Bool) (res : List JVar) :
    St → List InstrR → St × List InstrR
  | st, [] => (st, [])
  | st, i :: c =>
      let r1 := stepI k cand res st i c
      let r2 := goBody k cand res r1.1 c
      (r2.1, r1.2 ++ r2.2)

/-- Bring the result `r` into itself at the end of the body. -/
def fixOne (k : Nat) (cand : JVar → Bool) (res : List JVar) (st : St) (r : JVar) :
    St × List InstrR :=
  match lookR st.rho r with
  | some h =>
      if h == r then (st, [])
      else
        let r1 := makeRoom k 1 res res [] st.rho.length st
        ({ r1.1 with rho := (r, r) :: r1.1.rho.filter (fun q => q.1 != r) }, r1.2 ++ [mv r h])
  | none =>
      match lookS st.sig r with
      | none => (st, [])
      | some src =>
          let r1 := makeRoom k (needOf cand src) res res [] st.rho.length st
          let r2 := helpersOf cand r1.1 src
          (pruneDeadHolders res [] { r2.1 with rho := (r, r) :: r2.1.rho },
            r1.2 ++ r2.2 ++ [reloadSrc r2.1.rho r src])

/-- `fixOne` over a list. -/
def fixAll (k : Nat) (cand : JVar → Bool) (res : List JVar) :
    St → List JVar → St × List InstrR
  | st, [] => (st, [])
  | st, r :: rs =>
      let r1 := fixOne k cand res st r
      let r2 := fixAll k cand res r1.1 rs
      (r2.1, r1.2 ++ r2.2)

/-- The initial state: each register variable live before the body is its own holder. -/
def initSt (cand : JVar → Bool) (res : List JVar) (body : List InstrR) : St :=
  { rho := ((cmdVars body ++ res).filter (fun x => cand x && liveB res x body)).dedup.map
      (fun x => (x, x)),
    sig := [], cnt := 0, slots := [], regs := [] }

/-- No name of `fn` starts with the prefix of fresh names. -/
def noFreshB (fn : JazzFn) : Bool :=
  (fn.env.map Prod.fst ++ (cmdVars fn.fd.body ++ resOf fn).map (·.vname)).all
    (fun n => !isFreshName n)

/-- The surface type of a fresh variable. -/
def ptyOf : SType → PType
  | .sword ws => .word ws
  | .sbool => .bool
  | .sint => .int
  | .sarr n => .arr .U8 n

/-- The declarations of the fresh variables of a final state. -/
def declsOf (st : St) : List Decl :=
  st.slots.map (fun s => { storage := .stack, ty := ptyOf s.vtype, names := [s.vname] }) ++
  st.regs.map (fun f => { storage := .reg, ty := ptyOf f.vtype, names := [f.vname] })

/-- The final state and the body of the pass. -/
def run (k : Nat) (fn : JazzFn) : St × List InstrR :=
  let cand := regWordB fn
  let res := resOf fn
  let r1 := goBody k cand res (initSt cand res fn.fd.body) fn.fd.body
  let r2 := fixAll k cand res r1.1 ((res.filter cand).dedup)
  (r2.1, r1.2 ++ r2.2)

/-! ## 4. The pass with precomputed next uses

`run` answers each next-use, liveness and stability query by scanning the rest of the body,
and keeps the reload sources in a list it filters at every instruction. `runF` computes the
same state and body from a table, built once per body, of the positions at which each
variable is read or written, from a hash map of the storage classes, and from an index of
the reload sources; `runF_eq_run` states the equality. -/

/-- An occurrence of a variable in a body: the position of the instruction, whether the
instruction reads the variable, and whether it writes it. -/
abbrev Event := Nat × Bool × Bool

/-- The occurrences of `x` in `c`, whose first instruction is at position `j`, in order. -/
def evs (x : JVar) : Nat → List InstrR → List Event
  | _, [] => []
  | j, i :: c =>
      if (readsI i).contains x || (writesI i).contains x then
        (j, (readsI i).contains x, (writesI i).contains x) :: evs x (j + 1) c
      else evs x (j + 1) c

/-- The distance from position `p` to the next read of `x`, from the occurrences `l` of `x` in
a body of length `n` with results `res`; `none` when `x` is dead at `p`. -/
def nuEv (res : List JVar) (x : JVar) (n p : Nat) : List Event → Option Nat
  | [] => if res.contains x then some (n - p) else none
  | e :: l =>
      if e.1 < p then nuEv res x n p l
      else if e.2.1 then some (e.1 - p) else if e.2.2 then none else nuEv res x n p l

/-- No occurrence in `l` at position `p` or later writes the variable. -/
def stabEv (p : Nat) (l : List Event) : Bool := l.all (fun e => decide (e.1 < p) || !e.2.2)

/-- Variables hashed by name. -/
instance hashableJVar : Hashable JVar := ⟨fun x => hash x.vname⟩

instance lawfulHashableJVar : LawfulHashable JVar where
  hash_eq a b h := by rw [eq_of_beq h]

/-- The table of occurrences of the variables of a body. -/
abbrev EventTab := Std.HashMap JVar (List Event)

/-- Record that the instruction `i` at position `j` reads or writes `x`, once. -/
def addEv (j : Nat) (i : InstrR) (m : EventTab) (x : JVar) : EventTab :=
  if (m.getD x []).head?.map (·.1) = some j then m
  else m.insert x ((j, (readsI i).contains x, (writesI i).contains x) :: m.getD x [])

/-- The table of occurrences of the variables of `c`, whose first instruction is at
position `j`; built from the last instruction to the first. -/
def evTab (j : Nat) (c : List InstrR) : EventTab :=
  (c.zipIdx j).foldr (fun p m => (readsI p.1 ++ writesI p.1).foldl (addEv p.2 p.1) m) ∅

/-- The queries of the pass about the rest `c` of a body: the distance to the next read of a
variable, the length of `c`, and whether `c` writes no variable of a given name. -/
structure UseQ where
  nu : JVar → Option Nat
  len : Nat
  stab : JVar → Bool

/-- The queries at position `p` of a body of length `n` with results `res`, from its table. -/
def qAt (tab : EventTab) (res : List JVar) (n p : Nat) : UseQ :=
  ⟨fun x => nuEv res x n p (tab.getD x []), n - p, fun x => stabEv p (tab.getD x [])⟩

/-- The queries `q` answer as the rest `c` of the body with results `res` does. -/
structure UseQ.Agree (q : UseQ) (res : List JVar) (c : List InstrR) : Prop where
  nu : ∀ x, q.nu x = nextUse res x c
  len : q.len = c.length
  stab : ∀ x, q.stab x = stableB c x

/-- The state of `runF`: the state of the pass, an index of its reload sources, and a set
containing every variable a reload source is keyed by or reads. -/
structure StIx where
  st : St
  idx : Std.HashMap JVar Src
  men : Std.HashSet JVar

/-- The index of `S` agrees with the reload sources, and every variable a source is keyed by
or reads is in `S.men`. -/
structure StIx.Inv (S : StIx) : Prop where
  idx : ∀ y, S.idx[y]? = lookS S.st.sig y
  men : ∀ p ∈ S.st.sig, p.1 ∈ S.men ∧ ∀ y ∈ p.2.reads, y ∈ S.men

/-- `scoreF` is `score` with queries and an index. -/
def scoreF (S : StIx) (q : UseQ) (p : JVar × JVar) : Nat :=
  2 * (q.nu p.1).getD (q.len + 1) + (if (S.idx[p.1]?).isSome then 1 else 0)

/-- `pickVictim` with queries and an index. -/
def pickVictimF (S : StIx) (prot : List JVar) (q : UseQ) : Option (JVar × JVar) :=
  maxBy (scoreF S q) (S.st.rho.filter (fun p => !prot.contains p.1))

/-- `pruneDeadHolders` with queries. -/
def pruneF (q : UseQ) (S : StIx) : StIx :=
  { S with st := { S.st with rho := S.st.rho.filter (fun p => (q.nu p.1).isSome) } }

/-- `evict` with queries and an index. -/
def evictF (q : UseQ) (S : StIx) (p : JVar × JVar) : StIx × List InstrR :=
  let st1 := { S.st with rho := S.st.rho.filter (fun q => q.1 != p.1) }
  if (q.nu p.1).isSome && (S.idx[p.1]?).isNone then
    let s : JVar := ⟨freshName S.st.cnt, p.1.vtype⟩
    let st2 : St :=
      { st1 with sig := (p.1, .slot s) :: st1.sig, cnt := S.st.cnt + 1, slots := s :: S.st.slots }
    (⟨st2, S.idx.insert p.1 (.slot s), (S.men.insert p.1).insert s⟩, [mv s p.2])
  else (⟨st1, S.idx, S.men⟩, [])

/-- `makeRoom` with queries and an index. -/
def makeRoomF (k need : Nat) (prot : List JVar) (q : UseQ) : Nat → StIx → StIx × List InstrR
  | 0, S => (S, [])
  | fuel + 1, S =>
      if S.st.rho.length + need ≤ k then (S, [])
      else
        match pickVictimF S prot q with
        | none => (S, [])
        | some p =>
            let r1 := evictF q S p
            let r2 := makeRoomF k need prot q fuel r1.1
            (r2.1, r1.2 ++ r2.2)

/-- `reloadFresh` on the state of `S`. -/
def reloadFreshF (S : StIx) (x : JVar) (src : Src) : StIx × List InstrR :=
  (⟨(reloadFresh S.st x src).1, S.idx, S.men⟩, (reloadFresh S.st x src).2)

/-- `helper` with an index. -/
def helperF (cand : JVar → Bool) (S : StIx) (y : JVar) : StIx × List InstrR :=
  if (lookR S.st.rho y).isSome then (S, [])
  else
    match S.idx[y]? with
    | some (.remat ty e) =>
        if (candReads cand e).isEmpty then reloadFreshF S y (.remat ty e) else (S, [])
    | _ => (S, [])

/-- `helpers` with an index. -/
def helpersF (cand : JVar → Bool) : StIx → List JVar → StIx × List InstrR
  | S, [] => (S, [])
  | S, y :: ys =>
      let r1 := helperF cand S y
      let r2 := helpersF cand r1.1 ys
      (r2.1, r1.2 ++ r2.2)

/-- `helpersOf` with an index. -/
def helpersOfF (cand : JVar → Bool) (S : StIx) : Src → StIx × List InstrR
  | .remat _ e => helpersF cand S (candReads cand e)
  | .slot _ => (S, [])

/-- `loadOne` with queries and an index. -/
def loadOneF (k : Nat) (cand : JVar → Bool) (prot : List JVar) (q : UseQ)
    (S : StIx) (x : JVar) : StIx × List InstrR :=
  if (lookR S.st.rho x).isSome then (S, [])
  else
    match S.idx[x]? with
    | none => (S, [])
    | some src =>
        let r1 := makeRoomF k (needOf cand src) prot q S.st.rho.length S
        let r2 := helpersOfF cand r1.1 src
        let r3 := reloadFreshF r2.1 x src
        (pruneF q r3.1, r1.2 ++ r2.2 ++ r3.2)

/-- `loadAll` with queries and an index. -/
def loadAllF (k : Nat) (cand : JVar → Bool) (prot : List JVar) (q : UseQ) :
    StIx → List JVar → StIx × List InstrR
  | S, [] => (S, [])
  | S, x :: xs =>
      let r1 := loadOneF k cand prot q S x
      let r2 := loadAllF k cand prot q r1.1 xs
      (r2.1, r1.2 ++ r2.2)

/-- `rematOK` with queries and an index. -/
def rematOKF (cand : JVar → Bool) (idx : Std.HashMap JVar Src) (q : UseQ) (x : JVar)
    (ty : SType) (e : PExpr) : Bool :=
  ty == x.vtype && !(readsE e).contains x && (readsE e).all q.stab &&
    (candReads cand e).all (fun y => match idx[y]? with
      | some (.remat _ e') => (candReads cand e').isEmpty
      | _ => false)

/-- The index of a list of reload sources. -/
def idxOf (sig : List (JVar × Src)) : Std.HashMap JVar Src :=
  sig.foldr (fun p m => m.insert p.1 p.2) ∅

/-- The state after the instruction `i`, from the reload sources `sig` that survive it, their
index `idx` and the set `men`: `afterDef` with queries and an index. -/
def afterDefIx (cand : JVar → Bool) (q : UseQ) (st : St) (sig : List (JVar × Src))
    (idx : Std.HashMap JVar Src) (men : Std.HashSet JVar) (i : InstrR) : StIx :=
  let w := writesI i
  let rho' := (defsOf cand i).map (fun x => (x, x)) ++
    st.rho.filter (fun p => !w.contains p.1 && !w.contains p.2)
  match i with
  | .Cassgn (.Lvar x) _ ty e =>
      if cand x.var && rematOKF cand idx q x.var ty e then
        ⟨{ st with rho := rho', sig := (x.var, .remat ty e) :: sig },
          idx.insert x.var (.remat ty e),
          (readsE e).foldl (fun m y => m.insert y) (men.insert x.var)⟩
      else ⟨{ st with rho := rho', sig := sig }, idx, men⟩
  | _ => ⟨{ st with rho := rho', sig := sig }, idx, men⟩

/-- `afterDef` with queries and an index: the reload sources are filtered, and the index
rebuilt, only when the instruction writes a variable of `S.men`. -/
def afterDefF (cand : JVar → Bool) (q : UseQ) (S : StIx) (i : InstrR) : StIx :=
  let w := writesI i
  let hit := w.any S.men.contains
  let sig := if hit then S.st.sig.filter (fun p => !w.contains p.1 && !(p.2.reads.any w.contains))
    else S.st.sig
  afterDefIx cand q S.st sig (if hit then idxOf sig else S.idx) S.men i

/-- `stepI` with the queries `q` before the instruction and `q'` after it. -/
def stepIF (k : Nat) (cand : JVar → Bool) (q q' : UseQ) (S : StIx) (i : InstrR) :
    StIx × List InstrR :=
  let S0 := pruneF q S
  let U := usesOf cand i
  let r1 := loadAllF k cand U q S0 U
  let r2 := makeRoomF k (defsOf cand i).length U q r1.1.st.rho.length r1.1
  (afterDefF cand q' r2.1 i, r1.2 ++ r2.2 ++ [renI (renOf r2.1.st.rho) i])

/-- `goBody` with the queries `qs p` at each position `p`. -/
def goBodyF (k : Nat) (cand : JVar → Bool) (qs : Nat → UseQ) :
    Nat → StIx → List InstrR → StIx × List InstrR
  | _, S, [] => (S, [])
  | p, S, i :: c =>
      let r1 := stepIF k cand (qs p) (qs (p + 1)) S i
      let r2 := goBodyF k cand qs (p + 1) r1.1 c
      (r2.1, r1.2 ++ r2.2)

/-- `initSt` with the queries `q` at the start of the body. -/
def initStF (cand : JVar → Bool) (q : UseQ) (res : List JVar) (body : List InstrR) : St :=
  { rho := ((cmdVars body ++ res).filter (fun x => cand x && (q.nu x).isSome)).dedup.map
      (fun x => (x, x)),
    sig := [], cnt := 0, slots := [], regs := [] }

/-- The storage classes of the names of `fn`, as `storageOf` gives them. -/
def stoTab (fn : JazzFn) : Std.HashMap String Storage :=
  (fn.fd.params.zip fn.paramTys).foldr (fun p m => m.insert p.1.var.var.vname p.2.1)
    (fn.decls.foldr (fun d m => d.names.foldl (fun m n => m.insert n d.storage) m) ∅)

/-- `regWordB` from a table of storage classes. -/
def regWordT (t : Std.HashMap String Storage) (x : JVar) : Bool :=
  isGprTy x.vtype && t[x.vname]? == some .reg

/-- The final state and the body of the pass, computed with the table of occurrences, the
table of storage classes and the index of reload sources. -/
def runF (k : Nat) (fn : JazzFn) : St × List InstrR :=
  let cand := regWordT (stoTab fn)
  let res := resOf fn
  let body := fn.fd.body
  let qs := qAt (evTab 0 body) res body.length
  let r1 := goBodyF k cand qs 0 ⟨initStF cand (qs 0) res body, ∅, ∅⟩ body
  let r2 := fixAll k cand res r1.1.st ((res.filter cand).dedup)
  (r2.1, r1.2 ++ r2.2)

/-! ### `runF` computes `run` -/

theorem liveB_eq_isSome_nextUse (res : List JVar) (x : JVar) (c : List InstrR) :
    liveB res x c = (nextUse res x c).isSome := by
  induction c with
  | nil => cases h : res.contains x <;> simp only [liveB, nextUse, h] <;> rfl
  | cons i c ih =>
    cases hr : (readsI i).contains x <;> cases hw : (writesI i).contains x <;>
      simp only [liveB, nextUse, hr, hw, ih, Bool.true_or, Bool.false_or, Bool.not_true,
        Bool.not_false, Bool.true_and, Bool.false_and, ↓reduceIte, Bool.false_eq_true,
        Option.isSome_some, Option.isSome_none, Option.isSome_map]

theorem evs_ge (x : JVar) (c : List InstrR) (j : Nat) : ∀ e ∈ evs x j c, j ≤ e.1 := by
  induction c generalizing j with
  | nil => simp [evs]
  | cons i c ih =>
    intro e he
    simp only [evs] at he
    split at he
    · rcases List.mem_cons.mp he with rfl | h
      · exact le_refl _
      · have := ih (j + 1) e h; omega
    · have := ih (j + 1) e he; omega

theorem nuEv_evs_le (res : List JVar) (x : JVar) (c : List InstrR) (j p : Nat) (h : p ≤ j) :
    nuEv res x (j + c.length) p (evs x j c) = (nextUse res x c).map (· + (j - p)) := by
  induction c generalizing j with
  | nil => simp [evs, nuEv, nextUse]
  | cons i c ih =>
    have ih' := ih (j + 1) (by omega)
    have e1 : j + (i :: c).length = (j + 1) + c.length := by simp; omega
    have hnl : ¬ j < p := by omega
    rw [e1]
    cases hr : (readsI i).contains x <;> cases hw : (writesI i).contains x <;>
      simp only [evs, nextUse, hr, hw, Bool.true_or, Bool.false_or, ↓reduceIte,
        Bool.false_eq_true, nuEv, hnl, Option.map_some, Option.map_none, Nat.zero_add, ih']
    cases nextUse res x c <;> simp; omega

theorem nuEv_evs_ge (res : List JVar) (x : JVar) (c : List InstrR) (j p : Nat) (h : j ≤ p) :
    nuEv res x (j + c.length) p (evs x j c) = nextUse res x (c.drop (p - j)) := by
  induction c generalizing j with
  | nil =>
    have h0 : j - p = 0 := by omega
    simp [evs, nuEv, nextUse, h0]
  | cons i c ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · simpa using nuEv_evs_le res x (i :: c) j j le_rfl
    · have e1 : j + (i :: c).length = (j + 1) + c.length := by simp; omega
      have e2 : p - j = (p - (j + 1)) + 1 := by omega
      rw [e1, e2, List.drop_succ_cons, ← ih (j + 1) (by omega)]
      simp only [evs]
      split <;> simp [nuEv, hlt]

theorem stabEv_cons (p : Nat) (e : Event) (l : List Event) :
    stabEv p (e :: l) = ((decide (e.1 < p) || !e.2.2) && stabEv p l) := rfl

theorem stabEv_evs_le (x : JVar) (c : List InstrR) (j p : Nat) (h : p ≤ j) :
    stabEv p (evs x j c) = stableB c x := by
  induction c generalizing j with
  | nil => simp [evs, stabEv, stableB]
  | cons i c ih =>
    have ih' := ih (j + 1) (by omega)
    have hnl : ¬ j < p := by omega
    simp only [stableB] at ih' ⊢
    cases hr : (readsI i).contains x <;> cases hw : (writesI i).contains x <;>
      simp only [evs, hr, hw, Bool.true_or, Bool.false_or, ↓reduceIte, Bool.false_eq_true,
        stabEv_cons, hnl, decide_false, Bool.not_true, Bool.not_false, Bool.false_and,
        Bool.true_and, ih', List.any_cons, Bool.true_or, Bool.false_or]

theorem stabEv_evs_ge (x : JVar) (c : List InstrR) (j p : Nat) (h : j ≤ p) :
    stabEv p (evs x j c) = stableB (c.drop (p - j)) x := by
  induction c generalizing j with
  | nil => simp [evs, stabEv, stableB]
  | cons i c ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · simpa using stabEv_evs_le x (i :: c) j j le_rfl
    · have e2 : p - j = (p - (j + 1)) + 1 := by omega
      rw [e2, List.drop_succ_cons, ← ih (j + 1) (by omega)]
      simp only [evs]
      split <;> simp [stabEv, hlt]

/-- Recording the occurrences at position `j` of the variables of `L` in a table with no
occurrence at `j`. -/
theorem foldl_addEv (j : Nat) (i : InstrR) (m : EventTab)
    (hm : ∀ y, (m.getD y []).head?.map (·.1) ≠ some j) :
    ∀ (L S : List JVar) (m' : EventTab),
      (∀ y, m'.getD y [] = if y ∈ S then
        (j, (readsI i).contains y, (writesI i).contains y) :: m.getD y [] else m.getD y []) →
      ∀ y, (L.foldl (addEv j i) m').getD y [] = if y ∈ S ++ L then
        (j, (readsI i).contains y, (writesI i).contains y) :: m.getD y [] else m.getD y []
  | [], S, m', h => by simpa using h
  | x :: L, S, m', h => by
    rw [List.foldl_cons]
    have hstep : ∀ y, (addEv j i m' x).getD y [] = if y ∈ S ++ [x] then
        (j, (readsI i).contains y, (writesI i).contains y) :: m.getD y [] else m.getD y [] := by
      intro y
      unfold addEv
      by_cases hx : x ∈ S
      · have hh : (m'.getD x []).head?.map (·.1) = some j := by rw [h x, if_pos hx]; rfl
        rw [if_pos hh, h y]
        by_cases hy : y = x
        · subst hy; simp [hx]
        · simp [hy]
      · have hh : ¬ (m'.getD x []).head?.map (·.1) = some j := by
          rw [h x, if_neg hx]; exact hm x
        rw [if_neg hh, Std.HashMap.getD_insert]
        by_cases hy : y = x
        · subst hy; simp [hx, h]
        · have hxy : (x == y) = false := by simpa using Ne.symm hy
          simp [hxy, h y, hy]
    have := foldl_addEv j i m hm L (S ++ [x]) (addEv j i m' x) hstep
    intro y; rw [this y]; simp [List.append_assoc]

theorem evTab_getD (x : JVar) (c : List InstrR) (j : Nat) :
    (evTab j c).getD x [] = evs x j c := by
  induction c generalizing j x with
  | nil => simp [evTab, evs]
  | cons i c ih =>
    have h0 : evTab j (i :: c) =
        (readsI i ++ writesI i).foldl (addEv j i) (evTab (j + 1) c) := by
      simp [evTab, List.zipIdx_cons]
    have hm : ∀ y, ((evTab (j + 1) c).getD y []).head?.map (·.1) ≠ some j := by
      intro y
      rw [ih]
      have := evs_ge y c (j + 1)
      cases hl : evs y (j + 1) c with
      | nil => simp
      | cons e l =>
        have := this e (by simp [hl])
        simp; omega
    rw [h0, foldl_addEv j i (evTab (j + 1) c) hm (readsI i ++ writesI i) [] _ (by simp) x, ih]
    simp only [evs, List.nil_append, List.mem_append]
    by_cases hr : x ∈ readsI i <;> by_cases hw : x ∈ writesI i <;> simp [hr, hw]

theorem qAt_agree (res : List JVar) (body : List InstrR) (p : Nat) :
    (qAt (evTab 0 body) res body.length p).Agree res (body.drop p) := by
  refine ⟨fun x => ?_, ?_, fun x => ?_⟩
  · simpa [qAt, evTab_getD] using nuEv_evs_ge res x body 0 p (Nat.zero_le _)
  · simp [qAt]
  · simpa [qAt, evTab_getD] using stabEv_evs_ge x body 0 p (Nat.zero_le _)

theorem foldl_insert_getElem? (s : Storage) (n : String) :
    ∀ (names : List String) (m : Std.HashMap String Storage),
      (names.foldl (fun m n => m.insert n s) m)[n]? = if names.contains n then some s else m[n]?
  | [], m => by simp
  | a :: l, m => by
    rw [List.foldl_cons, foldl_insert_getElem? s n l, Std.HashMap.getElem?_insert]
    by_cases h : a = n
    · subst h; simp
    · have h' : (a == n) = false := by simpa using h
      have h'' : ¬ n = a := Ne.symm h
      simp [h', h'']

theorem decls_getElem? (n : String) : ∀ (ds : List Decl),
    (ds.foldr (fun d (m : Std.HashMap String Storage) =>
      d.names.foldl (fun (m : Std.HashMap String Storage) n => m.insert n d.storage) m) ∅)[n]? =
      (ds.find? (fun d => d.names.contains n)).map (·.storage)
  | [] => by simp
  | d :: ds => by
    rw [List.foldr_cons, foldl_insert_getElem?, decls_getElem? n ds, List.find?_cons]
    cases d.names.contains n <;> simp

theorem foldr_insert_getElem? {α : Type} (key : α → String) (val : α → Storage)
    (m0 : Std.HashMap String Storage) (n : String) : ∀ L : List α,
    (L.foldr (fun p m => m.insert (key p) (val p)) m0)[n]? =
      match L.find? (fun p => key p == n) with
      | some p => some (val p)
      | none => m0[n]?
  | [] => by simp
  | a :: l => by
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, foldr_insert_getElem? key val m0 n l,
      List.find?_cons]
    cases key a == n <;> simp

theorem regWordT_stoTab (fn : JazzFn) : regWordT (stoTab fn) = regWordB fn := by
  funext x
  simp only [regWordT, regWordB, storageOf, stoTab, foldr_insert_getElem?, decls_getElem?]
  split <;> split <;> simp_all

/-- `r` is the run of `r'` with an index satisfying the invariant. -/
def Sim (r : StIx × List InstrR) (r' : St × List InstrR) : Prop :=
  r.1.st = r'.1 ∧ r.2 = r'.2 ∧ r.1.Inv

theorem lookS_cons (a : JVar) (v : Src) (sig : List (JVar × Src)) (y : JVar) :
    lookS ((a, v) :: sig) y = if a == y then some v else lookS sig y := by
  simp only [lookS, List.find?_cons]
  cases a == y <;> rfl

theorem idxOf_getElem? (sig : List (JVar × Src)) (y : JVar) : (idxOf sig)[y]? = lookS sig y := by
  induction sig with
  | nil => simp [idxOf, lookS]
  | cons p sig ih =>
    obtain ⟨a, v⟩ := p
    simp only [idxOf, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, ih, lookS_cons]

/-- Adding the reload source `v` of `a` keeps the invariant. -/
theorem StIx.Inv.cons {S : StIx} (h : S.Inv) {st' : St} {a : JVar} {v : Src}
    {men' : Std.HashSet JVar} (hsig : st'.sig = (a, v) :: S.st.sig)
    (hmen : ∀ y ∈ S.men, y ∈ men') (ha : a ∈ men') (hv : ∀ y ∈ v.reads, y ∈ men') :
    StIx.Inv ⟨st', S.idx.insert a v, men'⟩ := by
  refine ⟨fun y => ?_, fun p hp => ?_⟩
  · simp only [hsig, Std.HashMap.getElem?_insert, lookS_cons, h.idx]
  · simp only [hsig, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨ha, hv⟩
    · exact ⟨hmen _ (h.men p hp).1, fun y hy => hmen _ ((h.men p hp).2 y hy)⟩

theorem pickVictimF_eq {S : StIx} {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (hS : S.Inv) (prot : List JVar) :
    pickVictimF S prot q = pickVictim S.st prot res c := by
  unfold pickVictimF pickVictim
  congr 1
  funext p
  simp [scoreF, score, hq.nu, hq.len, hS.idx]

theorem pruneF_eq {S : StIx} {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (hS : S.Inv) :
    (pruneF q S).st = pruneDeadHolders res c S.st ∧ (pruneF q S).Inv := by
  refine ⟨?_, ⟨hS.idx, hS.men⟩⟩
  simp [pruneF, pruneDeadHolders, liveB_eq_isSome_nextUse, hq.nu]

theorem evictF_sim {S : StIx} {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (hS : S.Inv) (p : JVar × JVar) :
    Sim (evictF q S p) (evict res c S.st p) := by
  unfold evictF evict
  simp only [hq.nu, hS.idx, ← liveB_eq_isSome_nextUse]
  split
  · refine ⟨rfl, rfl, ?_⟩
    exact StIx.Inv.cons (S := ⟨{ S.st with rho := S.st.rho.filter (fun q => q.1 != p.1) },
        S.idx, S.men⟩) ⟨hS.idx, hS.men⟩ rfl
      (fun y hy => Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr hy))))
      (Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr (Or.inl (by simp)))))
      (fun y hy => by
        simp only [Src.reads, List.mem_singleton] at hy
        subst hy
        exact Std.HashSet.mem_insert.mpr (Or.inl (by simp)))
  · exact ⟨rfl, rfl, hS.idx, hS.men⟩

theorem makeRoomF_sim {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (k need : Nat) (prot : List JVar) :
    ∀ (fuel : Nat) (S : StIx), S.Inv →
      Sim (makeRoomF k need prot q fuel S) (makeRoom k need prot res c fuel S.st) := by
  intro fuel
  induction fuel with
  | zero => intro S hS; exact ⟨rfl, rfl, hS⟩
  | succ fuel ih =>
    intro S hS
    simp only [makeRoomF, makeRoom]
    split
    · exact ⟨rfl, rfl, hS⟩
    · rw [pickVictimF_eq hq hS]
      split
      · exact ⟨rfl, rfl, hS⟩
      · rename_i p _
        obtain ⟨h1, h2, h3⟩ := evictF_sim hq hS p
        obtain ⟨g1, g2, g3⟩ := ih _ h3
        exact ⟨by simp only [g1, h1], by simp only [g2, h2, h1], g3⟩

theorem reloadFreshF_sim {S : StIx} (hS : S.Inv) (x : JVar) (src : Src) :
    Sim (reloadFreshF S x src) (reloadFresh S.st x src) :=
  ⟨rfl, rfl, hS.idx, hS.men⟩

theorem helperF_sim (cand : JVar → Bool) {S : StIx} (hS : S.Inv) (y : JVar) :
    Sim (helperF cand S y) (helper cand S.st y) := by
  unfold helperF helper
  rw [hS.idx]
  split
  · exact ⟨rfl, rfl, hS⟩
  · split
    · split
      · exact reloadFreshF_sim hS _ _
      · exact ⟨rfl, rfl, hS⟩
    · exact ⟨rfl, rfl, hS⟩

theorem helpersF_sim (cand : JVar → Bool) :
    ∀ (ys : List JVar) (S : StIx), S.Inv → Sim (helpersF cand S ys) (helpers cand S.st ys)
  | [], S, hS => ⟨rfl, rfl, hS⟩
  | y :: ys, S, hS => by
    obtain ⟨h1, h2, h3⟩ := helperF_sim cand hS y
    obtain ⟨g1, g2, g3⟩ := helpersF_sim cand ys _ h3
    exact ⟨by simp only [helpersF, helpers, g1, h1], by simp only [helpersF, helpers, g2, h2, h1], g3⟩

theorem helpersOfF_sim (cand : JVar → Bool) {S : StIx} (hS : S.Inv) (src : Src) :
    Sim (helpersOfF cand S src) (helpersOf cand S.st src) := by
  cases src with
  | slot s => exact ⟨rfl, rfl, hS⟩
  | remat ty e => exact helpersF_sim cand _ S hS

theorem loadOneF_sim {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (k : Nat) (cand : JVar → Bool) (prot : List JVar) {S : StIx}
    (hS : S.Inv) (x : JVar) :
    Sim (loadOneF k cand prot q S x) (loadOne k cand prot res c S.st x) := by
  unfold loadOneF loadOne
  rw [hS.idx]
  split
  · exact ⟨rfl, rfl, hS⟩
  · split
    · exact ⟨rfl, rfl, hS⟩
    · rename_i src _
      obtain ⟨a1, a2, a3⟩ := makeRoomF_sim hq k (needOf cand src) prot S.st.rho.length S hS
      obtain ⟨b1, b2, b3⟩ := helpersOfF_sim cand a3 src
      obtain ⟨c1, c2, c3⟩ := reloadFreshF_sim b3 x src
      obtain ⟨d1, d3⟩ := pruneF_eq hq c3
      exact ⟨by simp only [d1, c1, b1, a1], by simp only [c2, b2, a2, b1, a1], d3⟩

theorem loadAllF_sim {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (k : Nat) (cand : JVar → Bool) (prot : List JVar) :
    ∀ (xs : List JVar) (S : StIx), S.Inv →
      Sim (loadAllF k cand prot q S xs) (loadAll k cand prot res c S.st xs)
  | [], S, hS => ⟨rfl, rfl, hS⟩
  | x :: xs, S, hS => by
    obtain ⟨h1, h2, h3⟩ := loadOneF_sim hq k cand prot hS x
    obtain ⟨g1, g2, g3⟩ := loadAllF_sim hq k cand prot xs _ h3
    exact ⟨by simp only [loadAllF, loadAll, g1, h1],
      by simp only [loadAllF, loadAll, g2, h2, h1], g3⟩

theorem mem_foldl_insert (y : JVar) : ∀ (l : List JVar) (M : Std.HashSet JVar),
    y ∈ l.foldl (fun m y => m.insert y) M ↔ y ∈ l ∨ y ∈ M
  | [], M => by simp
  | a :: l, M => by
    rw [List.foldl_cons, mem_foldl_insert y l, Std.HashSet.mem_insert, List.mem_cons]
    simp only [beq_iff_eq]
    constructor
    · rintro (h | rfl | h) <;> simp_all
    · rintro ((rfl | h) | h) <;> simp_all

theorem afterDefIx_eq {q : UseQ} {res : List JVar} {c : List InstrR} (hq : q.Agree res c)
    (cand : JVar → Bool) (st : St) (i : InstrR) (idx : Std.HashMap JVar Src)
    (men : Std.HashSet JVar)
    (hidx : ∀ y, idx[y]? = lookS (st.sig.filter (fun p => !(writesI i).contains p.1 &&
      !(p.2.reads.any (writesI i).contains))) y)
    (hmen : ∀ p ∈ st.sig, p.1 ∈ men ∧ ∀ y ∈ p.2.reads, y ∈ men) :
    let r := afterDefIx cand q st (st.sig.filter (fun p => !(writesI i).contains p.1 &&
      !(p.2.reads.any (writesI i).contains))) idx men i
    r.st = afterDef cand c st i ∧ r.Inv := by
  have hmen' : ∀ p ∈ st.sig.filter (fun p => !(writesI i).contains p.1 &&
      !(p.2.reads.any (writesI i).contains)), p.1 ∈ men ∧ ∀ y ∈ p.2.reads, y ∈ men :=
    fun p hp => hmen p (List.mem_filter.mp hp).1
  have hstab : q.stab = stableB c := funext hq.stab
  have base : ∀ rho', StIx.Inv ⟨{ st with rho := rho', sig := (st.sig.filter
      (fun p => !(writesI i).contains p.1 && !(p.2.reads.any (writesI i).contains))) }, idx, men⟩ :=
    fun _ => ⟨hidx, hmen'⟩
  cases i with
  | Cassgn lv tag ty e =>
    cases lv with
    | Lvar x =>
      have hR : rematOKF cand idx q x.var ty e = rematOK cand (st.sig.filter
          (fun p => !(writesI (.Cassgn (.Lvar x) tag ty e)).contains p.1 &&
            !(p.2.reads.any (writesI (.Cassgn (.Lvar x) tag ty e)).contains))) c x.var ty e := by
        simp only [rematOKF, rematOK, hidx, hstab]
      simp only [afterDefIx, afterDef, hR]
      by_cases hc : (cand x.var && rematOK cand (st.sig.filter
          (fun p => !(writesI (.Cassgn (.Lvar x) tag ty e)).contains p.1 &&
            !(p.2.reads.any (writesI (.Cassgn (.Lvar x) tag ty e)).contains))) c x.var ty e) = true
      · simp only [hc, ↓reduceIte]
        refine ⟨trivial, StIx.Inv.cons (base []) rfl ?_ ?_ ?_⟩
        · intro y hy
          exact (mem_foldl_insert y _ _).mpr (Or.inr (Std.HashSet.mem_insert.mpr (Or.inr hy)))
        · exact (mem_foldl_insert _ _ _).mpr (Or.inr (Std.HashSet.mem_insert.mpr (Or.inl (by simp))))
        · intro y hy
          exact (mem_foldl_insert y _ _).mpr (Or.inl hy)
      · simp only [hc, ↓reduceIte, Bool.false_eq_true]
        exact ⟨trivial, base _⟩
    | _ => exact ⟨rfl, base _⟩
  | _ => exact ⟨rfl, base _⟩

theorem afterDefF_eq {S : StIx} {q : UseQ} {res : List JVar} {c : List InstrR}
    (hq : q.Agree res c) (hS : S.Inv) (cand : JVar → Bool) (i : InstrR) :
    (afterDefF cand q S i).st = afterDef cand c S.st i ∧ (afterDefF cand q S i).Inv := by
  have hF : (if (writesI i).any S.men.contains = true then S.st.sig.filter
      (fun p => !(writesI i).contains p.1 && !(p.2.reads.any (writesI i).contains))
      else S.st.sig) = S.st.sig.filter
      (fun p => !(writesI i).contains p.1 && !(p.2.reads.any (writesI i).contains)) := by
    split
    · rfl
    · rename_i hh
      symm
      rw [List.filter_eq_self]
      intro p hp
      have ⟨h1, h2⟩ := hS.men p hp
      have hn : ∀ y, y ∈ S.men → (writesI i).contains y = false := by
        intro y hy
        cases hc : (writesI i).contains y with
        | false => rfl
        | true =>
          exact absurd (List.any_eq_true.mpr
            ⟨y, by simpa using hc, Std.HashSet.contains_iff_mem.mpr hy⟩) hh
      have h3 : p.2.reads.any (writesI i).contains = false := by
        rw [List.any_eq_false]
        intro y hy
        rw [hn y (h2 y hy)]
        simp
      simp only [hn _ h1, h3, Bool.not_false, Bool.and_self]
  have hI : ∀ y, (if (writesI i).any S.men.contains = true then idxOf (if (writesI i).any
      S.men.contains = true then S.st.sig.filter (fun p => !(writesI i).contains p.1 &&
      !(p.2.reads.any (writesI i).contains)) else S.st.sig) else S.idx)[y]? =
      lookS (S.st.sig.filter (fun p => !(writesI i).contains p.1 &&
        !(p.2.reads.any (writesI i).contains))) y := by
    intro y
    rw [hF]
    split
    · exact idxOf_getElem? _ y
    · rename_i hh
      rw [← hF, if_neg hh, hS.idx]
  have hI' : ∀ y, (if (writesI i).any S.men.contains = true then idxOf (S.st.sig.filter
      (fun p => !(writesI i).contains p.1 && !(p.2.reads.any (writesI i).contains)))
      else S.idx)[y]? = lookS (S.st.sig.filter (fun p => !(writesI i).contains p.1 &&
        !(p.2.reads.any (writesI i).contains))) y := by
    intro y
    have := hI y
    rwa [hF] at this
  unfold afterDefF
  simp only
  rw [hF]
  exact afterDefIx_eq hq cand S.st i _ S.men hI' hS.men

theorem stepIF_sim (k : Nat) (cand : JVar → Bool) {res : List JVar} {i : InstrR}
    {c : List InstrR} {q q' : UseQ} (hq : q.Agree res (i :: c)) (hq' : q'.Agree res c)
    {S : StIx} (hS : S.Inv) :
    Sim (stepIF k cand q q' S i) (stepI k cand res S.st i c) := by
  obtain ⟨p1, p3⟩ := pruneF_eq hq hS
  obtain ⟨a1, a2, a3⟩ := loadAllF_sim hq k cand (usesOf cand i) (usesOf cand i) _ p3
  obtain ⟨b1, b2, b3⟩ := makeRoomF_sim hq k (defsOf cand i).length (usesOf cand i)
    (loadAllF k cand (usesOf cand i) q (pruneF q S) (usesOf cand i)).1.st.rho.length _ a3
  obtain ⟨e1, e3⟩ := afterDefF_eq hq' b3 cand i
  refine ⟨?_, ?_, e3⟩
  · simp only [stepIF, stepI]
    rw [e1, b1, a1, p1]
  · simp only [stepIF, stepI]
    rw [b2, b1, a2, a1, p1]

theorem goBodyF_sim (k : Nat) (cand : JVar → Bool) (res : List JVar) (qs : Nat → UseQ) :
    ∀ (c : List InstrR) (p : Nat) (S : StIx), S.Inv →
      (∀ j, (qs (p + j)).Agree res (c.drop j)) →
      Sim (goBodyF k cand qs p S c) (goBody k cand res S.st c)
  | [], _, S, hS, _ => ⟨rfl, rfl, hS⟩
  | i :: c, p, S, hS, hqs => by
    have hq : (qs p).Agree res (i :: c) := by simpa using hqs 0
    have hq' : (qs (p + 1)).Agree res c := by simpa using hqs 1
    obtain ⟨s1, s2, s3⟩ := stepIF_sim k cand hq hq' hS
    obtain ⟨g1, g2, g3⟩ := goBodyF_sim k cand res qs c (p + 1) _ s3
      (fun j => by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hqs (j + 1))
    exact ⟨by simp only [goBodyF, goBody, g1, s1], by simp only [goBodyF, goBody, g2, s2, s1], g3⟩

theorem runF_eq_run (k : Nat) (fn : JazzFn) : runF k fn = run k fn := by
  have hq : ∀ j, (qAt (evTab 0 fn.fd.body) (resOf fn) fn.fd.body.length (0 + j)).Agree
      (resOf fn) (fn.fd.body.drop j) := fun j => by simpa using qAt_agree (resOf fn) fn.fd.body j
  have hinit : initStF (regWordB fn) (qAt (evTab 0 fn.fd.body) (resOf fn) fn.fd.body.length 0)
      (resOf fn) fn.fd.body = initSt (regWordB fn) (resOf fn) fn.fd.body := by
    have h0 := (hq 0).nu
    simp only [Nat.zero_add, List.drop_zero] at h0
    simp [initStF, initSt, h0, liveB_eq_isSome_nextUse]
  have h0 : StIx.Inv ⟨initStF (regWordB fn) (qAt (evTab 0 fn.fd.body) (resOf fn)
      fn.fd.body.length 0) (resOf fn) fn.fd.body, ∅, ∅⟩ :=
    ⟨fun y => by simp [initStF, lookS], fun p hp => by simp [initStF] at hp⟩
  obtain ⟨g1, g2, -⟩ := goBodyF_sim k (regWordB fn) (resOf fn) _ fn.fd.body 0 _ h0 hq
  simp only [runF, run, regWordT_stoTab]
  rw [g1, g2]
  simp only [hinit]

/-- The pass as `run` computes it; `spillFn` is equal to it (`spillFn_eq_spillFnRef`). -/
def spillFnRef (k : Nat) (fn : JazzFn) : JazzFn :=
  if fn.fd.body.all straightI && noFreshB fn then
    let r := run k fn
    { fn with fd := { fn.fd with body := r.2 }, decls := fn.decls ++ declsOf r.1 }
  else fn

/-- **The pass.** On a straight-line body without names of the fresh prefix, the body of
`run` and the declarations of its fresh variables; the identity otherwise. It is computed by
`runF`. -/
def spillFn (k : Nat) (fn : JazzFn) : JazzFn :=
  if fn.fd.body.all straightI && noFreshB fn then
    let r := runF k fn
    { fn with fd := { fn.fd with body := r.2 }, decls := fn.decls ++ declsOf r.1 }
  else fn

theorem spillFn_eq_spillFnRef (k : Nat) (fn : JazzFn) : spillFn k fn = spillFnRef k fn := by
  simp only [spillFn, spillFnRef, runF_eq_run]

/-- The pass on each function of a unit. -/
def spillUnit (k : Nat) (u : JazzUnit) : JazzUnit := { u with fns := u.fns.map (spillFn k) }

namespace Example

/-- A `u64` variable. -/
def u (s : String) : JVar := { vname := s, vtype := .sword .U64 }

/-- `x = a + n`. -/
def addc (x a : String) (n : Int) : InstrR :=
  .Cassgn (.Lvar (vi (u x))) .AT_none (.sword .U64) (.Papp2 (.Oadd .U64) (lpv (u a)) (.Pconst n))

/-- A function of one parameter `a` whose values `a`, `x` and `y` are live at once. -/
def fn : JazzFn where
  kind := .exportFn
  fd := { name := { name := "f" }, params := [⟨vi (u "a")⟩],
          body := [addc "x" "a" 1, addc "y" "x" 2, addc "z" "y" 3, addc "p" "x" 4,
            addc "r" "a" 5],
          results := [vi (u "r")] }
  paramTys := [(.reg, .word .U64)]
  resultTys := [(.reg, .word .U64)]
  decls := [{ storage := .reg, ty := .word .U64, names := ["x", "y", "z", "p", "r"] }]

/-- The unit of `fn`. -/
def unit : JazzUnit := { fns := [fn] }

/-- `x = a ^ b` at `u64`. -/
def xorI (x a b : String) : InstrR :=
  .Cassgn (.Lvar (vi (u x))) .AT_none (.sword .U64) (.Papp2 (.Olxor .U64) (lpv (u a)) (lpv (u b)))

/-- The name of input `j`. -/
def inName (j : Nat) : String := "a" ++ toString j

/-- The name of temporary `j`. -/
def tName (j : Nat) : String := "t" ++ toString j

/-- A chain of `n` xors over 40 inputs: `t_j` is `t_(j-1)` xor an input when `j` is even or
below 20, and `t_(j-1)` xor `t_(j-20)` otherwise. -/
def chainBody (n : Nat) : List InstrR := (List.range n).map fun j =>
  if j = 0 then xorI (tName 0) (inName 0) (inName 1)
  else if j % 2 = 0 ∨ j < 20 then xorI (tName j) (tName (j - 1)) (inName (7 * j % 40))
  else xorI (tName j) (tName (j - 1)) (tName (j - 20))

/-- The function of 40 register inputs whose body is `chainBody n` and whose result is the last
temporary. -/
def chainFn (n : Nat) : JazzFn where
  kind := .exportFn
  fd := { name := { name := "chain" },
          params := (List.range 40).map (fun j => ⟨vi (u (inName j))⟩),
          body := chainBody n, results := [vi (u (tName (n - 1)))] }
  paramTys := (List.range 40).map fun _ => (.reg, .word .U64)
  resultTys := [(.reg, .word .U64)]
  decls := (List.range n).map fun j => { storage := .reg, ty := .word .U64, names := [tName j] }

end Example

-- The pass on a chain of 2,000 xors over 40 inputs with 12 registers finishes within the
-- budget and declares fresh `stack` and `reg` variables.
set_option kat.ms 1000 in
#kat (spillFn 12 (Example.chainFn 2000)).decls.length > 2000
-- With two registers one value is spilled to a `stack` variable; the text parses back.
#kat match printChecked (spillUnit 2 Example.unit) with
  | some s => (s.splitOn "stack").length > 1
  | none => false

end CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill
