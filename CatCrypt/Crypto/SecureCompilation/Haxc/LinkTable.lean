/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls
public import CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes
public import CatCrypt.Crypto.SecureCompilation.Haxc.LinkStepsTyped

/-!
# Tables of linkable kernels

A table of linkable kernels is a list of linked functions, each with the proof that it is a
linked kernel (`LinkedKernel`), with distinct names. A crate declares as linked some names of
its functions. The selection `select` gives the list of linked functions of these names in
the table, or an error for the first declared name that the table does not have, that is the
name of no function of the crate, or whose function in the module has another signature
than the kernel. The signature of a function is the list of the types of its parameters and
its result type, as the module gives them (`ModFn`); the names of the parameters are not
compared.

The selection produces the list of linked functions of a crate. The module linked from it is
the fold of `HaxModule.linkFn` over the functions of the list whose name is the name of a
function of the module, which is the module the linking of a crate makes. On this module the
two hypotheses of `haxc_correct_auto_access` on the linked functions, distinct names and
`LinkedKernel`, are theorems (`select_linked_nodup`, `select_linked_kernel`).

The run in the correctness theorem `haxc_correct_table` is a run of the linked module, in
which a replaced function has the meaning of its kernel. The theorem
`haxc_correct_table_source` takes a run of the module before linking. It assumes that each
replaced function has the result type of its kernel and that on arguments of the parameter
types of the kernel the meaning of the kernel returns the values of the source body
(`LinkStepsTyped.LinkAgrees`). The table does not prove this relation.

The conclusion of both theorems has two cases, a program without calls and a program that
calls the linked kernels. The bound on memory accesses covers programs without calls: every
access of the run of the decoded bytes lies in the memory of the layout
(`AccessBytes.HaltsIn`). For a program with calls both theorems state halting and the result,
and no bound on accesses.

The table is a parameter: no definition or theorem of this module names a kernel.

## Main definitions

* `Entry`, `Table`: a linkable kernel with its proof, and a table of them with distinct names.
* `sigAgrees`: a function of a module and a linked function have the same signature.
* `LinkError`, `LinkError.toString`: the refusal of a declared name and its message.
* `select`: the linked functions of the declared names, or a refusal.

## Main results

* `select_declared`, `select_agrees`, `select_replaced_iff`: every declared name is a name of
  the crate and of a selected kernel, and a function of the module is replaced exactly when
  its name is declared, in which case its signature is that of the kernel.
* `select_linked_nodup`, `select_linked_kernel`: the linked functions of the linked module
  have distinct names and are linked kernels.
* `haxc_correct_table`: `haxc_correct_auto_access` on the linked module, with no kernel
  hypothesis.
* `haxc_correct_table_source`: the same conclusion from a run of the module before linking.
* `select_empty`, `select_all`: the selection succeeds at the empty table, and at every table
  on a module with a function of the name and signature of each kernel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LinkTable

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog RInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (HaltsO)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.SepLogic.X86 (wordsLocs frameWords regionWords)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (tabOracle LinkedKernel)
open CatCrypt.Crypto.SecureCompilation.Haxc.ModuleCalls (foldl_linkFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.AccessBytes (HaltsIn)
open CatCrypt.Crypto.SecureCompilation.Haxc.LinkStepsTyped
  (LinkAgrees haxc_correct_linked_source)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn ModFn)

/-! ## The table -/

/-- **A linkable kernel**: a linked function with the proof that it is a linked kernel. -/
structure Entry where
  /-- The linked function. -/
  fn : LinkedFn
  /-- The linked function is a linked kernel. -/
  kernel : LinkedKernel fn

/-- **A table of linkable kernels**: linkable kernels with distinct names. -/
structure Table where
  /-- The kernels. -/
  entries : List Entry
  /-- No two kernels have one name. -/
  nodup : (entries.map (·.fn.name)).Nodup

/-- The table without kernels. -/
def Table.empty : Table := ⟨[], List.nodup_nil⟩

/-- The linked functions of a table. -/
def Table.fns (T : Table) : List LinkedFn := T.entries.map (·.fn)

/-- The names of the kernels of a table. -/
def Table.names (T : Table) : List String := T.fns.map (·.name)

/-- The names of a table are distinct. -/
theorem Table.names_nodup (T : Table) : T.names.Nodup := by
  simpa [Table.names, Table.fns, List.map_map, Function.comp_def] using T.nodup

/-- Each linked function of a table is a linked kernel. -/
theorem Table.kernel_of_mem {T : Table} {l : LinkedFn} (h : l ∈ T.fns) : LinkedKernel l := by
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp h
  exact e.kernel

/-- A linked function of a table is the one the table has at its name. -/
theorem Table.find?_of_mem {T : Table} {l : LinkedFn} (h : l ∈ T.fns) :
    T.fns.find? (·.name == l.name) = some l := by
  obtain ⟨l', hl'⟩ : ∃ l', T.fns.find? (·.name == l.name) = some l' :=
    Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨l, h, beq_self_eq_true _⟩)
  rw [hl', List.inj_on_of_nodup_map T.names_nodup (List.mem_of_find?_eq_some hl') h
    (by simpa using List.find?_some hl')]

/-! ## The selection -/

/-- **The signature of a function of a module agrees with that of a linked function**: the
    same parameter types, in order, and the same result type. -/
def sigAgrees (f : ModFn) (l : LinkedFn) : Bool :=
  decide (f.params.map (·.2) = l.params.map (·.2) ∧ f.res = l.res)

/-- The refusal of a name that a crate declares as linked. -/
inductive LinkError where
  /-- The table has no kernel of the name; `known` are the names of the table. -/
  | noKernel (name : String) (known : List String)
  /-- The crate has no function of the name. -/
  | noFunction (name : String)
  /-- The function of the module of the name has the parameter types `params` and the result
      type `res`; the kernel has `kernelParams` and `kernelRes`. -/
  | signature (name : String) (params : List NfTy) (res : NfTy)
      (kernelParams : List NfTy) (kernelRes : NfTy)

/-- The message of a refusal of a declared name. -/
def LinkError.toString : LinkError → String
  | .noKernel g known =>
      s!"cannot link {g}: no kernel of this name; kernels: {" ".intercalate known}"
  | .noFunction g => s!"cannot link {g}: the crate has no function of this name"
  | .signature g ps r kps kr =>
      s!"cannot link {g}: the function has the signature {repr ps} -> {repr r}, " ++
        s!"the kernel {repr kps} -> {repr kr}"

instance : ToString LinkError := ⟨LinkError.toString⟩

/-- **The refusal of the declared name `g`**, at the names `crate` of the functions of the
    crate and the module `m` before linking: the table has no kernel of the name, the crate
    has no function of the name, or a function of the module of the name has another
    signature than the kernel. -/
def refusal? (T : Table) (crate : List String) (m : HaxModule) (g : String) :
    Option LinkError :=
  match T.fns.find? (·.name == g) with
  | none => some (.noKernel g T.names)
  | some l =>
      if crate.contains g then
        (m.fns.find? fun f => f.name == g && !sigAgrees f l).map fun f =>
          .signature g (f.params.map (·.2)) f.res (l.params.map (·.2)) l.res
      else some (.noFunction g)

/-- **The selection of the names `declared` in the table `T`**: the kernels of the table of
    these names, in the order of the table, or the refusal of the first declared name that
    has one (`refusal?`). A declared function of the crate that the module does not reach is
    selected and replaces no function of this module. -/
def select (T : Table) (crate : List String) (m : HaxModule) (declared : List String) :
    Except LinkError (List LinkedFn) :=
  match declared.findSome? (refusal? T crate m) with
  | some e => .error e
  | none => .ok (T.fns.filter fun l => declared.contains l.name)

variable {T : Table} {crate declared : List String} {m : HaxModule} {ls : List LinkedFn}

/-- **The selection returns a list exactly when no declared name has a refusal**, and the list
    is that of the kernels of the declared names. -/
theorem select_ok_iff :
    select T crate m declared = .ok ls ↔
      (∀ g ∈ declared, refusal? T crate m g = none)
        ∧ ls = T.fns.filter fun l => declared.contains l.name := by
  grind [select, List.findSome?_eq_none_iff]

/-- **Every declared name is the name of a function of the crate and of a selected kernel.** -/
theorem select_declared (hs : select T crate m declared = .ok ls) {g : String}
    (hg : g ∈ declared) : g ∈ crate ∧ ∃ l ∈ ls, l.name = g := by
  obtain ⟨hno, rfl⟩ := select_ok_iff.mp hs
  have h := hno g hg
  grind [refusal?]

/-- **A function of the module with a declared name has the signature of the selected kernel
    of this name.** -/
theorem select_agrees (hs : select T crate m declared = .ok ls) {f : ModFn} (hf : f ∈ m.fns)
    (hd : f.name ∈ declared) : ∃ l ∈ ls, l.name = f.name ∧ sigAgrees f l = true := by
  obtain ⟨hno, rfl⟩ := select_ok_iff.mp hs
  have h := hno f.name hd
  grind [refusal?, Option.map_eq_none_iff, List.find?_eq_none]

/-- **A function of the module is replaced exactly when its name is declared**; with
    `select_agrees`, only a function whose name and signature agree with a kernel of the
    table is replaced. -/
theorem select_replaced_iff (hs : select T crate m declared = .ok ls) {f : ModFn}
    (hf : f ∈ m.fns) :
    f ∉ ((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m).fns
      ↔ f.name ∈ declared := by
  have hdecl := @select_declared _ _ _ _ _ hs f.name
  obtain ⟨-, rfl⟩ := select_ok_iff.mp hs
  rw [foldl_linkFn]
  grind

/-! ## The linked module -/

/-- **The linked functions of the module linked from the table have distinct names.** -/
theorem select_linked_nodup (hs : select T crate m declared = .ok ls) (hm : m.linked = []) :
    (((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m).linked.map
      (·.name)).Nodup := by
  obtain ⟨-, rfl⟩ := select_ok_iff.mp hs
  simp only [foldl_linkFn, hm, List.append_nil, List.map_reverse, List.nodup_reverse]
  exact T.names_nodup.sublist ((List.filter_sublist.trans List.filter_sublist).map _)

/-- **The linked functions of the module linked from the table are linked kernels.** -/
theorem select_linked_kernel (hs : select T crate m declared = .ok ls) (hm : m.linked = []) :
    ∀ l ∈ ((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m).linked,
      LinkedKernel l := by
  obtain ⟨-, rfl⟩ := select_ok_iff.mp hs
  simp only [foldl_linkFn, hm, List.append_nil, List.mem_reverse, List.mem_filter]
  exact fun l hl => Table.kernel_of_mem hl.1.1

/-! ## Correctness -/

/-- **The compiler theorem on a module linked from a table.** For every table `T`, every
    module `m` without linked functions and every selection `ls` of declared names in `T`,
    when `compileA` returns `(P, bytes)` on the module with the selected kernels that it
    reaches linked, the conclusion of `haxc_correct_auto_access` holds on this module: in its
    case without calls every memory access of the decoded bytes lies in `layoutMem σ sa`
    (`HaltsIn`), and its case with calls has no bound on accesses. Distinct names and
    `LinkedKernel` follow from the table and the selection, so no hypothesis on a kernel
    remains. The run is one of the linked module, in which a replaced function has the
    meaning of its kernel; `haxc_correct_table_source` takes a run of `m`. -/
theorem haxc_correct_table (T : Table) (crate declared : List String) (m : HaxModule)
    (hm : m.linked = []) (ls : List LinkedFn) (hs : select T crate m declared = .ok ls)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA ((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m)
      σ fname = some (P, bytes))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value)
    (hrun : haxRuns σ
      ((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m) sa v) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData,
          cs.Sublist
            (((ls.filter fun l => m.fns.any (·.name == l.name)).foldl
              HaxModule.linkFn m).linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) :=
  haxc_correct_auto_access _ σ fname P bytes hc sa hsep v hrun
    (select_linked_nodup hs hm) (select_linked_kernel hs hm)

/-- **The compiler theorem on a module linked from a table, against the source runs of the
    module before linking.** The hypotheses are those of `haxc_correct_table` with the run
    taken in `m`, and the remaining relation between the source body of a replaced function
    and its kernel: `LinkStepsTyped.LinkAgrees`, which asks that the replaced function has the
    result type of the kernel and that on arguments of the parameter types of the kernel the
    meaning of the kernel returns every value the reference meaning of the function returns.
    The table and the selection do not prove this relation. The conclusion is that of
    `haxc_correct_table`. -/
theorem haxc_correct_table_source (T : Table) (crate declared : List String) (m : HaxModule)
    (hm : m.linked = []) (ls : List LinkedFn) (hs : select T crate m declared = .ok ls)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA ((ls.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m)
      σ fname = some (P, bytes))
    (hagree : LinkAgrees CatCrypt.Crypto.Hax.hax64WExit m
      (ls.filter fun l => m.fns.any (·.name == l.name)))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : haxRuns σ m sa v) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v
        ∧ sa'.regs "%rsp" = sa.regs "%rsp"
        ∧ (∀ x, SepLogic.X86.Loc.mem x
            ∉ wordsLocs (frameWords (sa.regs "%rsp") σ.frameLo σ.frameHi) →
          (∀ p ∈ σ.regions, SepLogic.X86.Loc.mem x ∉ wordsLocs (regionWords (sa.regs p.1) p.2)) →
          sa'.mem x = sa.mem x)
        ∧ HaltsIn (layoutMem σ sa) prog 0 sa sa')
      ∨ ∃ cs : List CalleeData,
          cs.Sublist
            (((ls.filter fun l => m.fns.any (·.name == l.name)).foldl
              HaxModule.linkFn m).linked.filterMap LinkedFn.calleeData)
          ∧ cs ≠ [] ∧ (cs.map (·.name)).Nodup
          ∧ ∃ (pc Q : List RInstr) (k : String → Nat) (q : String → List RInstr),
            (∀ c ∈ cs, decodeLprog c.bytes = some (q c.name))
            ∧ decodeLprog (cs.flatMap (·.bytes)) = some Q
            ∧ (∀ c ∈ cs, ∃ A B, Q = A ++ shiftProg A.length (q c.name) ++ B ∧ A.length = k c.name)
            ∧ prog = pc ++ shiftProg pc.length Q
            ∧ (∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' v)
            ∧ ∃ sa', HaltsO aMachine (tabOracle cs pc.length k q) pc 0 sa sa'
              ∧ σ.ResultOf sa sa' v) :=
  haxc_correct_linked_source m _ σ fname P bytes hc (select_linked_nodup hs hm)
    (select_linked_kernel hs hm) hagree sa hsep v hrun

/-! ## Satisfiability -/

/-- **The selection at the empty table**: it returns a list exactly when no name is declared,
    and the list is empty. -/
theorem select_empty :
    select Table.empty crate m declared = .ok ls ↔ declared = [] ∧ ls = [] := by
  cases declared <;> simp [select, refusal?, Table.empty, Table.fns, eq_comm]

/-- **The selection at a table parameter**: on the module with, for each kernel of `T`, one
    function of its name and signature, all names of the table are selected, and linking
    replaces every function. At a table of one entry this is a module with one function,
    replaced by the kernel of the entry. -/
theorem select_all (T : Table) (te : _root_.Hax.TExpr) :
    let m : HaxModule :=
      { entry := te, fns := T.fns.map fun l => ⟨l.name, l.params, l.res, te⟩, depth := 1 }
    select T T.names m T.names = .ok T.fns
      ∧ (T.fns.filter fun l => m.fns.any (·.name == l.name)).foldl HaxModule.linkFn m
        = { m with fns := [], linked := T.fns.reverse } := by
  intro m
  constructor
  · refine select_ok_iff.mpr ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
      have hfind := Table.find?_of_mem hl
      have huniq := fun l' (hl' : l' ∈ T.fns) =>
        List.inj_on_of_nodup_map T.names_nodup hl' hl
      grind [refusal?, sigAgrees, Table.names]
    · exact (List.filter_eq_self.mpr (by grind [Table.names])).symm
  · have hall : (T.fns.filter fun l => m.fns.any (·.name == l.name)) = T.fns :=
      List.filter_eq_self.mpr (by grind [List.any_map, List.any_eq_true])
    have hnone : m.fns.filter (fun f => T.fns.all fun l => f.name != l.name) = [] :=
      List.filter_eq_nil_iff.mpr (by grind)
    rw [hall, foldl_linkFn, hnone, List.append_nil]

end CatCrypt.Crypto.SecureCompilation.Haxc.LinkTable
