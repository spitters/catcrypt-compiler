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
def dropDead (res : List JVar) (c : List InstrR) (st : St) : St :=
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
        (dropDead res c r3.1, r1.2 ++ r2.2 ++ r3.2)

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
  let st0 := dropDead res (i :: c) st
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
          (dropDead res [] { r2.1 with rho := (r, r) :: r2.1.rho },
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

/-- **The pass.** On a straight-line body without names of the fresh prefix, the body of
`run` and the declarations of its fresh variables; the identity otherwise. -/
def spillFn (k : Nat) (fn : JazzFn) : JazzFn :=
  if fn.fd.body.all straightI && noFreshB fn then
    let r := run k fn
    { fn with fd := { fn.fd with body := r.2 }, decls := fn.decls ++ declsOf r.1 }
  else fn

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

end Example

-- With two registers one value is spilled to a `stack` variable; the text parses back.
#kat match printChecked (spillUnit 2 Example.unit) with
  | some s => (s.splitOn "stack").length > 1
  | none => false

end CatCrypt.Crypto.SecureCompilation.VIR.JasminSpill
