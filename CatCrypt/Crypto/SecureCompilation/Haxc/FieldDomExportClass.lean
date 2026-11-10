/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomWebs
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg

/-!
# The instructions of the export of one chain of stores

The export of a program of the shape `LoadsChain` is one instruction per binding. The exported
memory-free binding has a register tag, the exported load a load tag and the exported store a
store tag; each is an operation, and none zeroes an array. Under every renaming of its array
positions, an instruction that writes no array keeps the alias table, and the store of the slot
`regName d` inserts its renamed destination with the root of its renamed base. The base of each
store is the root of the chain or the array that an earlier store wrote, and when the export
writes an array its returned operand names the last one.

## Main definitions

* `ExportClass`: the classification of the instructions of a body as the instructions of one
  chain of stores from a root.

## Main results

* `aliasStepO_renArr_reg`: an instruction with a register tag that keeps every alias table
  keeps it under every renaming of its array positions.
* `bindOps_memFree_class`, `bindOps_load_class`, `bindOps_store_class`: the exported
  memory-free bindings, loads and stores, with their alias steps under every renaming.
* `chainTail_export_class`, `loadsChain_export_class`: the export of a chain tail and of a
  program of the shape `LoadsChain` is classified by `ExportClass`, from the name of the
  current version and from a root without `#`, together with the consumption and alias facts
  of the chain and the name of its returned operand.
* `hash_not_mem_argName`, `hash_not_mem_regName`, `InScope.hash_not_mem`: the argument and
  slot names have no `#`.
* `straightOp_of_lopn`: an operation that is no shadow of a call is a straight operation.
* `zeroDst?_renArr`: a renaming of the array positions of an instruction with a load, store or
  register tag that zeroes no array zeroes none.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideLeak (jMemFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (aliasStepO zeroDst?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg (renArr renLoad renStore
  renCallW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (ReadAt WrAt ConsumedAt
  ChainConsume rdArr wrArr)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation (regName_injective)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgArg (arrInitB bindOps_noArrImm
  zeroDst?_of_noArrImm)

/-! ## 1. The exported instructions under a renaming -/

/-- **An instruction with a register tag that keeps every alias table keeps it under every
    renaming of its array positions**: the renaming changes only a shadow of a call, whose
    alias step at no out symbol keeps the table. -/
theorem aliasStepO_renArr_reg {w : LinstrR} {c : Option Nat}
    (h : ∀ M, aliasStepO [] M (w, .reg c) = M) :
    ∀ M ρ, aliasStepO [] M (renArr ρ (w, .reg c)) = M := by
  intro M ρ
  have hr : renArr ρ (w, .reg c) = (renCallW ρ w, .reg c) := rfl
  rw [hr]
  unfold renCallW
  cases hs : LprogIsa.shadowCall? w with
  | none => exact h M
  | some t =>
      obtain ⟨dst, f, srcs⟩ := t
      simp [aliasStepO, LprogIsa.shadowCall?_callShadow]

/-- No memory-free operation initialises an array. -/
theorem arrInitB_of_memFree {op : JasminOp} (he : jMemFree op = true) : arrInitB op = false := by
  cases op <;> simp_all [jMemFree, arrInitB]

/-- An instruction of an exported binding of an operation that initialises no array is no
    zeroing. -/
theorem zeroDst?_bindOps (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hz : arrInitB e.op = false) :
    ∀ i ∈ bindOps nArgs e d, zeroDst? i = none :=
  fun i hi => zeroDst?_of_noArrImm (bindOps_noArrImm nArgs e hz d i hi)

/-- **The exported memory-free binding** is one operation with a register tag, which reads and
    writes no array, zeroes none, and keeps every alias table under every renaming. -/
theorem bindOps_memFree_class (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (he : jMemFree e.op = true) :
    ∃ ins, bindOps nArgs e d = [ins] ∧ PlainTag ins ∧ JasminLsemMemLoop.IsLopn ins
      ∧ zeroDst? ins = none ∧ rdArr (fun _ _ => none) ins = []
      ∧ wrArr (fun _ => none) ins = none
      ∧ ∀ M ρ, aliasStepO [] M (renArr ρ ins) = M := by
  obtain ⟨ins, hb, hins⟩ := aliasStepO_bindOps_memFree nArgs d e he
  obtain ⟨ins', hb', hrd, hwr⟩ := bindOps_memFree nArgs d e he (fun _ _ => none) (fun _ => none)
    (fun _ _ => rfl) (fun _ => rfl)
  rw [hb] at hb'
  obtain rfl : ins = ins' := List.singleton_inj.mp hb'
  have hmem : ins ∈ bindOps nArgs e d := by rw [hb]; exact List.mem_singleton_self _
  obtain ⟨w, c, rfl⟩ : ∃ w c, ins = (w, JasminLsemMem.MemTag.reg c) := by
    obtain ⟨op, rfl, args⟩ := e
    revert hb
    cases op <;> simp only [jMemFree, Bool.false_eq_true] at he <;>
      intro hb <;> exact ⟨_, _, (List.singleton_inj.mp hb).symm⟩
  exact ⟨_, hb, trivial, isLopn_bindOps nArgs e d _ hmem,
    zeroDst?_bindOps nArgs d e (arrInitB_of_memFree he) _ hmem, hrd, hwr,
    aliasStepO_renArr_reg hins⟩

/-- **The exported load** is one operation with a load tag, which reads the array named by the
    operand of its base, writes none, zeroes none, and keeps every alias table under every
    renaming. -/
theorem bindOps_load_class (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (a : Ctxt.Var Γ (.stackArr w m)) (i : Ctxt.Var Γ (.reg 64)) :
    ∃ ins, bindOps nArgs (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
        Expr jasminDialect Γ (.reg w)) d = [ins] ∧ PlainTag ins ∧ JasminLsemMemLoop.IsLopn ins
      ∧ zeroDst? ins = none ∧ rdArr (fun _ _ => none) ins = [curNameAt d nArgs a]
      ∧ wrArr (fun _ => none) ins = none ∧ ∀ M ρ, aliasStepO [] M (renArr ρ ins) = M := by
  obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_load nArgs d a i (fun _ _ => none) (fun _ => none)
  have hmem : ins ∈ bindOps nArgs (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ :
      Expr jasminDialect Γ (.reg w)) d := by rw [hb]; exact List.mem_singleton_self _
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons a (HVector.cons i HVector.nil)) =
      [resolveVar d nArgs argName (fun _ => none) a,
        resolveVar d nArgs argName (fun _ => none) i] := rfl
  have hm : isMemStore "LOADIDX" = false := by decide
  have hins := List.singleton_inj.mp (hb.symm.trans (rfl : bindOps nArgs
    (⟨.stackLoad w m, rfl, .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) d = [_]))
  refine ⟨ins, hb, ?_, isLopn_bindOps nArgs _ d _ hmem,
    zeroDst?_bindOps nArgs d _ rfl _ hmem, hrd, hwr, fun M ρ => ?_⟩
  · rw [hins]
    trivial
  · rw [hins]
    simp only [exprArgs, hgo]
    rw [resolveVar_reg d nArgs a, resolveVar_reg d nArgs i]
    simp [aliasStepO, opToLinstrR, renArr, renLoad, LprogIsa.shadowCall?, hm]

/-- **The exported store of the slot `regName d`** is one operation with a store tag, which
    writes `regName d`, reads the array named by the operand of its base, zeroes none, and
    under every renaming inserts its renamed destination with the root of its renamed base. -/
theorem bindOps_store_class (nArgs d : Nat) {Γ : Ctxt jasminDialect} {w m : Nat}
    (v : Ctxt.Var Γ (.stackArr w m)) (i : Ctxt.Var Γ (.reg 64)) (x : Ctxt.Var Γ (.reg w)) :
    ∃ ins, bindOps nArgs (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
        Expr jasminDialect Γ (.stackArr w m)) d = [ins] ∧ PlainTag ins
      ∧ JasminLsemMemLoop.IsLopn ins ∧ zeroDst? ins = none
      ∧ wrArr (fun _ => none) ins = some (regName d)
      ∧ rdArr (fun _ _ => none) ins = [curNameAt d nArgs v]
      ∧ ∀ M ρ, aliasStepO [] M (renArr ρ ins) =
          M.insert (ρ (regName d))
            (M.getD (ρ (curNameAt d nArgs v)) (ρ (curNameAt d nArgs v))) := by
  obtain ⟨ins, hb, hwr, hrd⟩ := bindOps_store nArgs d v i x (fun _ _ => none) (fun _ => none)
  have hmem : ins ∈ bindOps nArgs (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Γ (.stackArr w m)) d := by rw [hb]; exact List.mem_singleton_self _
  have hgo : exprArgs.go d nArgs argName (fun _ => none)
      (HVector.cons v (HVector.cons i (HVector.cons x HVector.nil))) =
      [resolveVar d nArgs argName (fun _ => none) v, resolveVar d nArgs argName (fun _ => none) i,
        resolveVar d nArgs argName (fun _ => none) x] := rfl
  have hm : isMemStore "STOREIDX" = true := by decide
  have hins := List.singleton_inj.mp (hb.symm.trans (rfl : bindOps nArgs
    (⟨.stackStore w m, rfl, .cons v (.cons i (.cons x .nil))⟩ :
      Expr jasminDialect Γ (.stackArr w m)) d = [_]))
  refine ⟨ins, hb, ?_, isLopn_bindOps nArgs _ d _ hmem,
    zeroDst?_bindOps nArgs d _ rfl _ hmem, hwr, hrd, fun M ρ => ?_⟩
  · rw [hins]
    trivial
  · rw [hins]
    simp only [exprArgs, hgo]
    rw [resolveVar_reg d nArgs v, resolveVar_reg d nArgs i, resolveVar_reg d nArgs x]
    simp [aliasStepO, opToLinstrR, renArr, renStore, LprogIsa.shadowCall?, hm]

/-! ## 2. The classification of the instructions of one chain -/

/-- **The instructions of a body as those of one chain of stores from the root `x`**: every
    instruction is an operation with a load, store or register tag that zeroes no array; one
    that writes no array keeps every alias table under every renaming of its array positions;
    one that writes `d` reads one array `b`, its renamed alias step inserts the renamed `d` with
    the root of the renamed `b`, and `b` is the root or was written before. -/
def ExportClass (body : List LinstrRM) (x : String) : Prop :=
  ∀ k i, body[k]? = some i → PlainTag i ∧ JasminLsemMemLoop.IsLopn i ∧ zeroDst? i = none
    ∧ (wrArr (fun _ => none) i = none → ∀ M ρ, aliasStepO [] M (renArr ρ i) = M)
    ∧ ∀ d, wrArr (fun _ => none) i = some d → ∃ b, rdArr (fun _ _ => none) i = [b]
      ∧ (∀ M ρ, aliasStepO [] M (renArr ρ i) = M.insert (ρ d) (M.getD (ρ b) (ρ b)))
      ∧ (b = x ∨ ∃ k₀, k₀ < k ∧ WrAt body (fun _ => none) k₀ b)

/-- The classification of a body with an instruction in front that writes no array. -/
theorem exportClass_cons_fix {ins : LinstrRM} {body : List LinstrRM} {x : String}
    (h : ExportClass body x) (hp : PlainTag ins) (hl : JasminLsemMemLoop.IsLopn ins)
    (hz : zeroDst? ins = none) (hw : wrArr (fun _ => none) ins = none)
    (hA : ∀ M ρ, aliasStepO [] M (renArr ρ ins) = M) : ExportClass (ins :: body) x := by
  intro k i hi
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact ⟨hp, hl, hz, fun _ => hA, fun d hd => by rw [hw] at hd; cases hd⟩
  | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨h1, h2, h3, h4, h5⟩ := h k i hi
      refine ⟨h1, h2, h3, h4, fun d hd => ?_⟩
      obtain ⟨b, hb, hs, hx⟩ := h5 d hd
      exact ⟨b, hb, hs, hx.imp id fun ⟨k₀, hk₀, hW⟩ =>
        ⟨k₀ + 1, by omega, wrAt_cons_succ.mpr hW⟩⟩

/-- The classification of a store in front of the rest of its chain: the store writes `y`
    from the base `x`, and the rest is classified from `y`. -/
theorem exportClass_cons_store {ins : LinstrRM} {body : List LinstrRM} {x y : String}
    (h : ExportClass body y) (hp : PlainTag ins) (hl : JasminLsemMemLoop.IsLopn ins)
    (hz : zeroDst? ins = none) (hwr : wrArr (fun _ => none) ins = some y)
    (hrd : rdArr (fun _ _ => none) ins = [x])
    (hA : ∀ M ρ, aliasStepO [] M (renArr ρ ins) = M.insert (ρ y) (M.getD (ρ x) (ρ x))) :
    ExportClass (ins :: body) x := by
  intro k i hi
  cases k with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      refine ⟨hp, hl, hz, fun h' => (by rw [hwr] at h'; cases h'), fun d hd => ?_⟩
      rw [hwr] at hd
      cases hd
      exact ⟨x, hrd, hA, .inl rfl⟩
  | succ k =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨h1, h2, h3, h4, h5⟩ := h k i hi
      refine ⟨h1, h2, h3, h4, fun d hd => ?_⟩
      obtain ⟨b, hb, hs, hx⟩ := h5 d hd
      refine ⟨b, hb, hs, .inr ?_⟩
      rcases hx with rfl | ⟨k₀, hk₀, hW⟩
      · exact ⟨0, by omega, wrAt_cons_zero.mpr hwr⟩
      · exact ⟨k₀ + 1, by omega, wrAt_cons_succ.mpr hW⟩

section ExportClassChain

variable {nArgs : Nat} {fn : String}

/-- The returned name of a body that writes no array or returns a written name, with an
    instruction in front that writes no array. -/
theorem retWritten_cons_fix {ins : LinstrRM} {body : List LinstrRM} {ys : List String}
    (h : (∀ w d, ¬ WrAt body (fun _ => none) w d) ∨
      ∃ y, ys = [y] ∧ ∃ w, WrAt body (fun _ => none) w y)
    (hw : wrArr (fun _ => none) ins = none) :
    (∀ w d, ¬ WrAt (ins :: body) (fun _ => none) w d) ∨
      ∃ y, ys = [y] ∧ ∃ w, WrAt (ins :: body) (fun _ => none) w y := by
  rcases h with h | ⟨y, hy, w, hW⟩
  · left
    intro w d hW
    cases w with
    | zero => rw [wrAt_cons_zero, hw] at hW; cases hW
    | succ w => exact h w d (wrAt_cons_succ.mp hW)
  · exact .inr ⟨y, hy, w + 1, wrAt_cons_succ.mpr hW⟩

/-- **The export of a chain tail is classified from the name of its current version**, and it
    returns that name or a name it writes. -/
theorem chainTail_export_class {Γ : Ctxt jasminDialect} {w m : Nat} {ts : List JasminTy}
    {v : Ctxt.Var Γ (.stackArr w m)} {k : NFProg jasminDialect Γ ts} (h : ChainTail v k)
    (hn : nArgs ≤ Γ.length) {n : Nat} {r : Exported}
    (hr : exportR nArgs fn k Γ.length n = some r) :
    ExportClass r.code (curName nArgs v) ∧
      ∃ y, r.res.map JasminLsemWidthN.operandName = [y] ∧
        (y = curName nArgs v ∨ ∃ w, WrAt r.code (fun _ => none) w y) := by
  induction h generalizing n r with
  | @free Γ w m t ts v e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hp, hl, hz, -, hwr, hA⟩ := bindOps_memFree_class nArgs Γ.length e he
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName, List.length_cons, resolveVar_there] at this
      obtain ⟨hE, y, hy, hy'⟩ := this
      refine ⟨exportClass_cons_fix hE hp hl hz hwr hA, y, hy, ?_⟩
      rcases hy' with h | ⟨w', hW⟩
      · exact .inl h
      · exact .inr ⟨w' + 1, wrAt_cons_succ.mpr hW⟩
  | @store Γ w m ts v i x k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hp, hl, hz, hwr, hrd, hA⟩ := bindOps_store_class nArgs Γ.length v i x
      have hrest := ih (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hE, y, hy, hy'⟩ := hrest
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length)
            rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      refine ⟨exportClass_cons_store hE hp hl hz hwr hrd hA, y, hy, .inr ?_⟩
      rcases hy' with rfl | ⟨w', hW⟩
      · exact ⟨0, wrAt_cons_zero.mpr hwr⟩
      · exact ⟨w' + 1, wrAt_cons_succ.mpr hW⟩
  | @ret Γ w m v =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨fun k i hi => by simp at hi, curName nArgs v, rfl, .inl rfl⟩

/-- No character of the decimal representation of a number is `#`. -/
theorem hash_not_mem_toString (s : Nat) : '#' ∉ (toString s).toList := by
  intro h
  simp only [toString, Nat.repr, String.toList_ofList] at h
  have := Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) h
  exact absurd this (by decide)

/-- The argument names have no `#`. -/
theorem hash_not_mem_argName (s : Nat) : '#' ∉ (argName s).toList := by
  simp only [argName, String.toList_append, List.mem_append]
  rintro (h | h)
  · exact absurd h (by decide)
  · exact hash_not_mem_toString s h

/-- The slot names have no `#`. -/
theorem hash_not_mem_regName (s : Nat) : '#' ∉ (regName s).toList := by
  simp only [regName, String.toList_append, List.mem_append]
  rintro (h | h)
  · exact absurd h (by decide)
  · exact hash_not_mem_toString s h

/-- A name in scope has no `#`. -/
theorem InScope.hash_not_mem {D : Nat} {x : String} (h : InScope nArgs D x) :
    '#' ∉ x.toList := by
  rcases h with ⟨s, -, rfl⟩ | ⟨s, -, -, rfl⟩
  · exact hash_not_mem_argName s
  · exact hash_not_mem_regName s

/-- **The classification of the export of a program of the shape `LoadsChain`**: from a root
    `x` without `#`, the export has the consumption and the alias facts of one chain and its
    instructions are classified by `ExportClass`; and it writes no array, or it returns one
    operand naming an array it writes. -/
theorem loadsChain_export_class {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (h : LoadsChain p) (hn : nArgs ≤ Γ.length) {n : Nat}
    {r : Exported} (hr : exportR nArgs fn p Γ.length n = some r) :
    ∃ x, '#' ∉ x.toList ∧ ChainConsume r.code (fun _ _ => none) (fun _ => none) x
      ∧ AliasFacts r.code (fun _ => none) x ∧ ExportClass r.code x
      ∧ ((∀ w d, ¬ WrAt r.code (fun _ => none) w d) ∨
        ∃ y, r.res.map JasminLsemWidthN.operandName = [y] ∧
          ∃ w, WrAt r.code (fun _ => none) w y) := by
  induction h generalizing n r with
  | @free Γ t ts e k he hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hp, hl, hz, -, hwr, hA⟩ := bindOps_memFree_class nArgs Γ.length e he
      obtain ⟨ins', hb', hins⟩ := aliasStepO_bindOps_memFree nArgs Γ.length e he
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hcode : (Exported.prepend (bindOps nArgs e Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx, hC, hAl, hE, hR⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, hx, chainConsume_cons_noWrite hC hwr, aliasFacts_cons_fix hAl hins hwr,
        exportClass_cons_fix hE hp hl hz hwr hA, retWritten_cons_fix hR hwr⟩
  | @load Γ w m ts a i k hk ih =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hp, hl, hz, -, hwr, hA⟩ := bindOps_load_class nArgs Γ.length a i
      obtain ⟨ins', hb', hins⟩ := aliasStepO_bindOps_load nArgs Γ.length a i
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackLoad w m, rfl,
          .cons a (.cons i .nil)⟩ : Expr jasminDialect Γ (.reg w)) Γ.length) rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      obtain ⟨x, hx, hC, hAl, hE, hR⟩ := ih (by simp only [List.length_cons]; omega) hk'
      exact ⟨x, hx, chainConsume_cons_noWrite hC hwr, aliasFacts_cons_fix hAl hins hwr,
        exportClass_cons_fix hE hp hl hz hwr hA, retWritten_cons_fix hR hwr⟩
  | @store Γ w m ts v i x k hk =>
      simp only [exportR, Option.map_eq_some_iff] at hr
      obtain ⟨rk, hk', rfl⟩ := hr
      obtain ⟨ins, hb, hp, hl, hz, hwr, hrd, hA⟩ := bindOps_store_class nArgs Γ.length v i x
      obtain ⟨ins', hb', hins⟩ := aliasStepO_bindOps_store nArgs Γ.length v i x
      rw [hb] at hb'
      obtain rfl : ins = ins' := List.singleton_inj.mp hb'
      have hrest := chainTail_export_alias (fn := fn) (ao := fun _ => none) (fun _ => rfl) hk
        (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hrest
      obtain ⟨hF, -⟩ := chainTail_export (fn := fn) (aa := fun _ _ => none)
        (ao := fun _ => none)
        (fun _ _ => rfl) (fun _ => rfl) hk (by simp only [List.length_cons]; omega) hk'
      have hcons := chainTail_export_consume (fn := fn) (aa := fun _ _ => none)
        (ao := fun _ => none) (fun _ _ => rfl) (fun _ => rfl) hk
        (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hcons
      obtain ⟨hE, y, hy, hy'⟩ := chainTail_export_class (fn := fn) hk
        (by simp only [List.length_cons]; omega) hk'
      rw [curName_here hn] at hE hy'
      have hcode : (Exported.prepend (bindOps nArgs (⟨.stackStore w m, rfl,
          .cons v (.cons i (.cons x .nil))⟩ : Expr jasminDialect Γ (.stackArr w m)) Γ.length)
            rk) =
          { rk with code := ins :: rk.code } := by
        simp [Exported.prepend, hb]
      rw [hcode]
      have hv := inScope_resolveVar (nArgs := nArgs) v
      have hnw : ∀ w', ¬ WrAt rk.code (fun _ => none) w' (regName Γ.length) := fun w' hw' => by
        have h1 := hF.2.1 w' _ hw'
        have := regName_injective h1
        simp only [List.length_cons] at this
        omega
      refine ⟨curName nArgs v, hv.hash_not_mem, chainConsume_cons_store hcons ?_ hwr
        (fun h => hv.ne_regName le_rfl h.symm) (fun w' hw' => ?_),
        aliasFacts_cons_store hrest hins hwr hnw,
        exportClass_cons_store hE hp hl hz hwr hrd hA, .inr ⟨y, hy, ?_⟩⟩
      · rw [hrd]
        exact List.mem_singleton_self _
      · have h1 := hF.2.1 w' _ hw'
        exact hv.ne_regName (by simp only [List.length_cons]; omega) h1
      · rcases hy' with rfl | ⟨w', hW⟩
        · exact ⟨0, wrAt_cons_zero.mpr hwr⟩
        · exact ⟨w' + 1, wrAt_cons_succ.mpr hW⟩
  | @ret Γ ts vs =>
      simp only [exportR, Option.some.injEq] at hr
      subst hr
      refine ⟨"", by simp, ⟨fun w h => ?_, fun k d h => ?_, fun w r k d _ h => ?_⟩,
        fun M => ⟨fun w n h => ?_, fun n _ => rfl⟩, fun k i hi => by simp at hi,
        .inl fun w d h => ?_⟩ <;>
        · obtain ⟨_, h, -⟩ := h
          simp at h

end ExportClassChain

/-! ## 3. Straight operations and zeroings under a renaming -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete (armOf)

/-- **An operation that is no shadow of a call is a straight operation**: its arm is that of
    an array access, of a sequential instruction or of an operation. -/
theorem straightOp_of_lopn {i : LinstrRM} (hsh : LprogIsa.shadowCall? i.1 = none)
    (hl : JasminLsemMemLoop.IsLopn i) : StraightOp i := by
  refine ⟨?_, hl⟩
  obtain ⟨ds, o, ss, h⟩ := hl
  unfold StraightArm armOf
  rw [hsh]
  dsimp only
  split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · have hf : JasminLsemMemFlagGuard.flagCondCC? i = none := by
        unfold JasminLsemMemFlagGuard.flagCondCC?
        rw [h]
      rw [hf]
      dsimp only
      rw [h]
      dsimp only
      split
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)

/-- **A renaming of the array positions zeroes no array** at an instruction with a load, store
    or register tag that is no shadow of a call and zeroes none. -/
theorem zeroDst?_renArr (ρ : String → String) {i : LinstrRM} (hp : PlainTag i)
    (hsh : LprogIsa.shadowCall? i.1 = none) (hz : zeroDst? i = none) :
    zeroDst? (renArr ρ i) = none := by
  obtain ⟨w, tag⟩ := i
  cases tag with
  | reg c =>
      have hr : renArr ρ (w, .reg c) = (renCallW ρ w, .reg c) := rfl
      rw [hr, X86Backend.ImageCoalesceCfg.renCallW_of_none hsh]
      exact hz
  | load b n =>
      have hr : renArr ρ (w, .load b n) = (renLoad ρ w, .load b n) := rfl
      rw [hr]
      unfold renLoad
      split
      · split <;> exact hz
      · exact hz
  | store b n =>
      have hr : renArr ρ (w, .store b n) = (renStore ρ w, .store b n) := rfl
      rw [hr]
      unfold renStore
      split
      · split
        · simp_all [zeroDst?]
        · exact hz
      · exact hz
  | _ => exact absurd hp id

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
