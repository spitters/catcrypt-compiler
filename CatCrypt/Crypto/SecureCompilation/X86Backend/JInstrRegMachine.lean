/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.GenericRegAlloc
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-!
# The x86 multi-write `MachineModel`/`RegMachine` data (the D3 `writtenNames` payoff, #552)

`GenericRegAlloc.RegMachine` was generalized (D3) from a single-output
`evalInst s i = set (writtenName i) (instVal s i)` shape to a **multi-write,
register-observable** interface: `writes : S → I → List (String × Val)` (one pair
per destination) and a *register-projected* step law

```
evalInst_eq_set : get (runBlock s [i]) r = get ((writes s i).foldl set s) r
```

This unblocks exactly the x86 scalar shapes the old single-write form could not
express:

* `mulx dh dl a b` writes **two** registers (`[(dl, lo), (dh, hi)]`);
* `adcx`/`adox` write their destination register **and a flag** (`cf`/`of`). The
  flag write is invisible to `get` (which reads only `regs`), so the
  register-observable `get`-form of `evalInst_eq_set` holds even though the whole
  states differ in the flag field.

This file builds, at the x86 `JInstr 64`/`JState 64` types and against
`Jasmin.evalInstr` arm-by-arm:

* the total `MachineModel (JInstr 64)` instance (`instMachineModelJInstr`);
* the multi-write register-effect list `writesJ` (two pairs for `mulx`, one for the
  scalar/ADX ops, none for the two stores), its names law `writesJ_names`, and its
  register-observable step law `evalInst_eq_setJ` — the data `RegMachine` needs, all
  **unconditional** over every constructor (`jinstr_regmachine_step_data`);
* the renaming-commutation `writesJ_rename` over every constructor.

**Scope of the `RegMachine` instance.** The full `RegMachine (JInstr 64)
(JState 64)` instance is *not* declared here: its `writes_rename` field supplies only
register read-agreement, whereas x86's flag-reading ops (`adc`/`adcx`/…) and
memory-reading load ops (`loadMem`/`mulxMem`/`loadMemIdx`) write values that also
depend on the global flag map / frame memory. `writesJ_rename` makes those two extra
agreement hypotheses (`hflag`, `hmem`) explicit and proves all arms with them; the
register-only generic field is provable only for the flag- and memory-free subset
(the `RInst`-shaped register-to-register ops). The §4 docstring details this — it is
the same non-register state the x86 `JInstrRegAllocScoped.StateRelOn` (flags + memOn)
and the ARM `BInst` theorem (`t.cf = s.cf`) carry over the register-only generic
`Reindexed`. So the multi-output `writtenNames` generalization is fully realized for
x86 here (`mulx`'s two writes are first-class), independently of the orthogonal
non-register-read limitation of the register-only renaming hypothesis.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-! ## 1. The per-instruction register write list

`writesJ s i` is the `(name, value)` list of register writes one `JInstr` performs,
transcribing the *register effect* of `Jasmin.evalInstr` arm-by-arm. Each single-
output op gives a singleton `[(d, v)]` whose `v` is `evalInstr`'s written word; `mulx`
gives the two pairs `[(dl, lo), (dh, hi)]` (lo to `dstLo` first, matching the two
`setReg`s); the `storeMem`/`storeMemIdx` ops and the flag-only `test`/`cmp` write no
register (`[]`). The flag writes of `adcx`/`adox`/`test`/`cmp`/`rol`/`ror`/the B5W ops
do not appear: they are not register writes. -/

/-- The register `(name, value)` pairs one `JInstr 64` writes — the register effect of
    `Jasmin.evalInstr`. Used as `RegMachine.writes`; its names are `writtenNames i`
    (`writesJ_names`) and it matches `evalInstr` on every register read
    (`evalInst_eq_set`). -/
def writesJ (s : JState 64) : JInstr 64 → List (String × BitVec 64)
  | .mov dst src  => [(dst, x86_MOV (src.eval s))]
  | .add dst src  => [(dst, (x86_ADD (s.get dst) (src.eval s)).word)]
  | .sub dst src  => [(dst, (x86_SUB (s.get dst) (src.eval s)).word)]
  | .adc dst src  => [(dst, (x86_ADC (s.get dst) (src.eval s) (s.flagB (·.cf))).word)]
  | .sbb dst src  => [(dst, (x86_SBB (s.get dst) (src.eval s) (s.flagB (·.cf))).word)]
  | .imul dst src => [(dst, (x86_IMULt (s.get dst) (src.eval s)).word)]
  | .neg dst      => [(dst, (x86_NEG (s.get dst)).word)]
  | .setc dst     => [(dst, if s.flagB (·.cf) then 1 else 0)]
  | .and_ dst src => [(dst, (x86_AND (s.get dst) (src.eval s)).word)]
  | .test _ _     => []
  -- `cmp` writes the five flags and no register: its first operand is a read.
  | .cmp _ _      => []
  | .not_ dst     => [(dst, x86_NOT (s.get dst))]
  | .andn d a b   => [(d, (x86_ANDN (s.get a) (s.get b)).word)]
  | .rol dst amt  => [(dst, (x86_ROL (s.get dst) (amt.eval s)).word)]
  | .ror dst amt  => [(dst, (x86_ROR (s.get dst) (amt.eval s)).word)]
  | .rorx d src amt => [(d, x86_RORX (s.get src) (amt.eval s))]
  | .shlx d src cnt => [(d, x86_SHLX (s.get src) (s.get cnt))]
  | .shrx d src cnt => [(d, x86_SHRX (s.get src) (s.get cnt))]
  | .sarx d src cnt => [(d, x86_SARX (s.get src) (s.get cnt))]
  | .movzx d sw src => [(d, x86_MOVZX sw (s.get src))]
  | .movsx d sw src => [(d, x86_MOVSX sw (s.get src))]
  | .lea d base idx scale off =>
      [(d, x86_LEA (s.get base + (s.get idx) * BitVec.ofNat _ scale
        + BitVec.ofInt _ off))]
  | .or_ dst src  => [(dst, (x86_OR (s.get dst) (src.eval s)).word)]
  | .xor_ dst src => [(dst, (x86_XOR (s.get dst) (src.eval s)).word)]
  | .shl dst src  => [(dst, (x86_SHL (s.get dst) (src.eval s)).word)]
  | .shr dst src  => [(dst, (x86_SHR (s.get dst) (src.eval s)).word)]
  | .sar dst src  => [(dst, (x86_SAR (s.get dst) (src.eval s)).word)]
  | .cmove dst src  => [(dst, x86_CMOVcc (s.flagB (·.zf)) (src.eval s) (s.get dst))]
  | .cmovne dst src => [(dst, x86_CMOVcc (! s.flagB (·.zf)) (src.eval s) (s.get dst))]
  | .cmovb dst src  => [(dst, x86_CMOVcc (s.flagB (·.cf)) (src.eval s) (s.get dst))]
  | .mulx dstHi dstLo a b =>
      let (lo, hi) := x86_MULX_lo_hi (a.eval s) (b.eval s)
      [(dstLo, lo), (dstHi, hi)]
  | .mulxMem dstHi dstLo a base off =>
      let (lo, hi) := x86_MULX_lo_hi (a.eval s) (s.load base off)
      [(dstLo, lo), (dstHi, hi)]
  | .adcx dst src =>
      let (_co, res) := x86_ADCX (s.get dst) (src.eval s) (s.flagB (·.cf))
      [(dst, res)]
  | .adox dst src =>
      let (_co, res) := x86_ADCX (s.get dst) (src.eval s) (s.flagB (·.of))
      [(dst, res)]
  | .loadMem dst base off  => [(dst, x86_MOV (s.load base off))]
  | .storeMem _ _ _        => []
  | .loadMemIdx dst base idx scale => [(dst, x86_MOV (s.loadIdx base idx scale))]
  | .storeMemIdx _ _ _ _   => []
  | .loadSym dst _sym      => [(dst, BitVec.ofNat 64 1)]

/-- The written register names of one `JInstr`, **in the order `writesJ` applies them**.
    Identical to `SpillingRegAlloc.writtenNames` for every constructor except the two
    `mulx` arms, where the write order is `dstLo` then `dstHi` (matching `evalInstr`'s
    two `setReg`s and so the `evalInst_eq_set` fold), so the list is `[dstLo, dstHi]`
    rather than `SpillingRegAlloc`'s liveness-order `[dstHi, dstLo]`. Order is immaterial
    to the allocator (live-range analysis uses `List.contains`), so this is an
    order-permutation of the same def set — but `writes_names` (a *list* equality) forces
    the write order, which the register-observable `evalInst_eq_set` pins to `evalInstr`'s
    `(setReg dstLo …).setReg dstHi …`. -/
def writtenNamesJ : JInstr 64 → List String
  | .mulx dh dl _ _ => [dl, dh]
  | .mulxMem dh dl _ _ _ => [dl, dh]
  | i => CatCrypt.Crypto.Optimizer.SpillingRegAlloc.writtenNames i

/-- The names `writesJ` writes are exactly `writtenNamesJ`. By cases; `rfl` on every arm
    (the destinations are literal, independent of the values). -/
theorem writesJ_names (s : JState 64) (i : JInstr 64) :
    (writesJ s i).map Prod.fst = writtenNamesJ i := by
  cases i <;> rfl

/-! ## 2. The register-observable step law

`get (runBlock s [i]) r = get ((writesJ s i).foldl set s) r` for every `r`. Per
constructor this is a `simp` against `runBlock`/`evalInstr`/`writesJ` and the
register-file laws. The B5W ops fold to `setReg dst _` because `get` reads only
`regs` (so `writeB5W`'s flag fields are invisible); `adcx`/`adox` likewise — their
explicit `regs := if · = dst …` matches `setReg dst res` on `get`, and the
`flags`/`mem` fields never reach `get`. `test` folds the empty write list, its
`writeB5` leaving `regs` untouched. `mulx` folds two `setReg`s in the same
left-to-right order as `evalInstr`. -/

/-- The register-observable single-step law for x86: reading any register `r` after one
    `evalInstr` step equals reading it after folding `writesJ`'s `setReg`s. Closes by
    `cases i <;> simp` — the flag/memory side effects of `writeB5W`/`adcx`/`adox` are
    invisible to `JState.get`. -/
theorem evalInst_eq_setJ (s : JState 64) (i : JInstr 64) (r : String) :
    (runBlock s [i]).get r
      = ((writesJ s i).foldl (fun st p => JState.setReg st p.1 p.2) s).get r := by
  cases i <;>
    simp [runBlock, evalInstr, writesJ, JState.get, JState.setReg, JState.writeB5,
      JState.writeB5W, JState.writeB2W, JState.store, JState.storeIdx, JState.load,
      JState.loadIdx]

/-! ## 3. The renaming agreement: `writesJ` commutes with `ρ` under read-agreement

`writes_rename`: if reading every read-name `a` in the renamed state `t` at `ρ a`
equals reading it in `s` at `a`, then the renamed instruction writes the SAME values
to the `ρ`-renamed destinations. The values match because every value is built from
operand evals / `s.get dst` / `s.load base off`, each of which reads only the
read-names — so the agreement hypothesis carries it. The names map by `ρ`. -/

/-- An operand evaluated in `t` after renaming equals it in `s`, given read-agreement on
    its source names. The x86 analogue of `instValR_rename`'s operand step. -/
theorem renameOperand_eval_rename {ρ : String → String} {s t : JState 64} (op : JOperand)
    (h : ∀ a ∈ srcNames op, t.get (ρ a) = s.get a) :
    (renameOperand ρ op).eval t = op.eval s := by
  cases op with
  | reg r => simpa [renameOperand, JOperand.eval, JState.get] using h r (by simp [srcNames])
  | imm v => rfl

open CatCrypt.Crypto.Optimizer.SpillingRegAlloc in
/-- **`writesJ` commutes with the renaming, with a flag-agreement side hypothesis.**
    Under register read-agreement (`get t (ρ a) = get s a` for every read-name `a`)
    **and flag agreement** (`t.flags = s.flags`), the renamed instruction's writes are
    the `ρ`-image of the original's writes. By `cases i`; for every constructor each
    written value is rebuilt from operand evals / `get dst` / `load base off` (carried by
    the register agreement) and, for the eight **flag-reading** ops (`adc`/`sbb`/`adcx`/
    `adox`/`cmove`/`cmovne`/`cmovb`/`setc`), from the global carry/zero flag (carried by
    `hflag`). The destinations rename by `ρ`.

    **The two extra hypotheses `hflag`/`hmem` are exactly the obstruction to the generic
    `RegMachine.writes_rename` field** (which supplies *only* register read-agreement):
    the carry-in flag (for `adc`/`adcx`/…) and the loaded memory cell (for `loadMem`/
    `mulxMem`/`loadMemIdx`) are hidden inputs outside `SpillingRegAlloc.readNames`, so
    without `hflag`/`hmem` the value-equalities `(x86_ADCX … (t.flagB ·.cf)).snd =
    (… (s.flagB ·.cf)).snd` and `x86_MOV (t.mem (ρ base) off) = x86_MOV (s.mem base off)`
    are unprovable for arbitrary register-related `s t`. This is the same non-register
    state the ARM `BInst` backend threads through its bespoke `Reindexed` theorem
    (`t.cf = s.cf`) and the x86 `JInstrRegAllocScoped.StateRelOn` carries explicitly
    (`flags`, `memOn`) — both *over and above* the register-only generic `Reindexed`. -/
theorem writesJ_rename (ρ : String → String) (s t : JState 64) (i : JInstr 64)
    (h : ∀ a ∈ readNames i, t.get (ρ a) = s.get a) (hflag : t.flags = s.flags)
    (hmem : ∀ b o, t.mem (ρ b) o = s.mem b o) :
    writesJ t (renameInstr ρ i)
      = (writesJ s i).map (fun p => (ρ p.1, p.2)) := by
  cases i with
  | mov dst src =>
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha => h a ha
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, List.map_cons,
      List.map_nil]
  | add dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | sub dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | imul dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | neg dst =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    simp only [writesJ, renameInstr, hd, List.map_cons, List.map_nil]
  | and_ dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | or_ dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | xor_ dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | shl dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | shr dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | sar dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, List.map_cons,
      List.map_nil]
  | mulx dstHi dstLo a b =>
    have ha : ∀ x ∈ srcNames a, t.get (ρ x) = s.get x := fun x hx =>
      h x (List.mem_append_left _ hx)
    have hb : ∀ x ∈ srcNames b, t.get (ρ x) = s.get x := fun x hx =>
      h x (List.mem_append_right _ hx)
    simp only [writesJ, renameInstr, renameOperand_eval_rename a ha,
      renameOperand_eval_rename b hb, List.map_cons, List.map_nil]
  | mulxMem dstHi dstLo a base off =>
    have ha : ∀ x ∈ srcNames a, t.get (ρ x) = s.get x := fun x hx =>
      h x (List.mem_cons_of_mem _ hx)
    have hload : t.mem (ρ base) off = s.mem base off := hmem base off
    simp only [writesJ, renameInstr, renameOperand_eval_rename a ha, JState.load, hload,
      List.map_cons, List.map_nil]
  | loadMem dst base off =>
    have hload : t.mem (ρ base) off = s.mem base off := hmem base off
    simp only [writesJ, renameInstr, JState.load, hload, List.map_cons, List.map_nil]
  | test a b => simp only [writesJ, renameInstr, List.map_nil]
  | storeMem base off src => simp only [writesJ, renameInstr, List.map_nil]
  | loadMemIdx dst base idx scale =>
    have hidx : (t.get (ρ idx)).toNat = (s.get idx).toNat :=
      congrArg _ (h idx (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have hload : t.load (ρ base) ((scale : Int) * ((t.get (ρ idx)).toNat : Int))
        = s.load base ((scale : Int) * ((s.get idx).toNat : Int)) := by
      rw [hidx]; exact hmem base _
    simp only [writesJ, renameInstr, JState.loadIdx, hload, List.map_cons, List.map_nil]
  | storeMemIdx base idx scale src => simp only [writesJ, renameInstr, List.map_nil]
  | loadSym dst sym => simp only [writesJ, renameInstr, List.map_cons, List.map_nil]
  -- The flag-reading constructors: their written value depends on the global carry/zero
  -- flag (`s.flagB ·.cf` / `·.of` / `·.zf`), a hidden input outside `readNames`, so the
  -- register agreement `h` alone is insufficient — `hflag : t.flags = s.flags` supplies
  -- the flag-value agreement (`t.flagB f = s.flagB f`) the value-equality needs.
  | adc dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | sbb dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | adcx dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | adox dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | cmove dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | cmovne dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | cmovb dst src =>
    have hd : t.get (ρ dst) = s.get dst := h dst (List.mem_cons_self ..)
    have hs : ∀ a ∈ srcNames src, t.get (ρ a) = s.get a := fun a ha =>
      h a (List.mem_cons_of_mem _ ha)
    simp only [writesJ, renameInstr, renameOperand_eval_rename src hs, hd, JState.flagB,
      hflag, List.map_cons, List.map_nil]
  | setc dst =>
    simp only [writesJ, renameInstr, JState.flagB, hflag, List.map_cons, List.map_nil]
    rfl
  -- `cmp` writes no register, so both sides are the empty write list.
  | cmp a b => simp only [writesJ, renameInstr, List.map_nil]
  | not_ d =>
    have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
    simp only [writesJ, renameInstr, hd, List.map_cons, List.map_nil]
  | andn d a b =>
    have ha : t.get (ρ a) = s.get a := h a (List.mem_cons_self ..)
    have hb : t.get (ρ b) = s.get b := h b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [writesJ, renameInstr, ha, hb, List.map_cons, List.map_nil]
  | rol d amt | ror d amt =>
    have hd : t.get (ρ d) = s.get d := h d (List.mem_cons_self ..)
    have hs : ∀ x ∈ srcNames amt, t.get (ρ x) = s.get x := fun x hx =>
      h x (List.mem_cons_of_mem _ hx)
    simp only [writesJ, renameInstr, renameOperand_eval_rename amt hs, hd, List.map_cons,
      List.map_nil]
  | rorx d src amt =>
    have hsrc : t.get (ρ src) = s.get src := h src (List.mem_cons_self ..)
    have hs : ∀ x ∈ srcNames amt, t.get (ρ x) = s.get x := fun x hx =>
      h x (List.mem_cons_of_mem _ hx)
    simp only [writesJ, renameInstr, renameOperand_eval_rename amt hs, hsrc, List.map_cons,
      List.map_nil]
  | shlx d src cnt | shrx d src cnt | sarx d src cnt =>
    have hsrc : t.get (ρ src) = s.get src := h src (List.mem_cons_self ..)
    have hcnt : t.get (ρ cnt) = s.get cnt :=
      h cnt (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [writesJ, renameInstr, hsrc, hcnt, List.map_cons, List.map_nil]
  | movzx d sw src | movsx d sw src =>
    have hsrc : t.get (ρ src) = s.get src := h src (List.mem_cons_self ..)
    simp only [writesJ, renameInstr, hsrc, List.map_cons, List.map_nil]
  -- `lea`'s value is built from the two address registers, both of them read-names; it
  -- performs no memory access, so `hmem` is not needed.
  | lea d base idx scale off =>
    have hbase : t.get (ρ base) = s.get base := h base (List.mem_cons_self ..)
    have hidx : t.get (ρ idx) = s.get idx :=
      h idx (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [writesJ, renameInstr, hbase, hidx, List.map_cons, List.map_nil]

/-! ## 4. The `MachineModel` instance and the `RegMachine` near-miss

The `MachineModel (JInstr 64)` instance — the *syntactic* interface — is total and
unconditional. The multi-write *semantic* data (`writesJ`, `evalInst_eq_setJ`,
`writesJ_names`) is exactly what `GenericRegAlloc.RegMachine` needs, and the D3
`writtenNames`-as-`List` generalization makes the `mulx`/`mulxMem` two-register writes
expressible (the payoff that the old single-output shape blocked) and the `adcx`/`adox`
flag-write invisible to the register-observable `evalInst_eq_set`.

**The one field that does not specialize to x86 is `RegMachine.writes_rename`.** Its
hypothesis is *register* read-agreement only (`get t (ρ a) = get s a` for
`a ∈ readNames i`), but two x86 instruction families write a value that depends on
**non-register** state, a hidden input outside `readNames`:

* the eight **flag-reading** ops (`adc`/`sbb`/`adcx`/`adox`/`cmove`/`cmovne`/`cmovb`/
  `setc`) read the global carry/zero flag — they commute with `ρ` only under the
  additional flag agreement `t.flags = s.flags`;
* the three **memory-reading** ops (`loadMem`/`mulxMem`/`loadMemIdx`) read a frame cell
  `[base + off]` — they commute only under memory agreement
  `∀ b o, t.mem (ρ b) o = s.mem b o`.

`writesJ_rename` above carries exactly those two extra hypotheses (`hflag`, `hmem`) and
proves **every constructor** with them — including the `mulx`/`mulxMem` two-register
writes, the central payoff of the multi-output `writtenNames` (D3) generalization. The
generic field, lacking `hflag`/`hmem`, is *not* provable for those eleven arms over
arbitrary register-related `s t`. This is the same non-register state the ARM `BInst`
register allocator threads through its **bespoke** `Reindexed` theorem (`t.cf = s.cf`),
and the x86 `JInstrRegAllocScoped.StateRelOn` carries explicitly (`flags`, `memOn`):
the register-only generic `RegMachine` is the right home for **flag- and memory-free**
ISAs (RV64 `RInst`, and the x86 `mov`/`mulx`/scalar-ALU register-to-register subset),
while flag-carrying ADX and the reg-ptr memory ABI need those components in the
simulation relation — which is precisely what the x86 scoped simulation already does. -/

/-- **`MachineModel (JInstr 64)`**: the syntactic interface — the (write-order)
    `writtenNamesJ`, `SpillingRegAlloc.readNames`, the GP pool, and `storeMem`/`loadMem`
    against the `%rsp` frame base as the spill/reload constructors. -/
instance instMachineModelJInstr : MachineModel (JInstr 64) where
  writtenNames := writtenNamesJ
  readNames := CatCrypt.Crypto.Optimizer.SpillingRegAlloc.readNames
  physRegs := gpPool
  mkSpill r off := .storeMem "%rsp" off (.reg r)
  mkReload r off := .loadMem r "%rsp" off

/-- The multi-write semantic data the generic `RegMachine` step needs, bundled and
    proved at the x86 types: the register write list (`writesJ`), its register-observable
    step law (`evalInst_eq_setJ`), and that its names are the model's `writtenNames`
    (`writesJ_names`). Holds **unconditionally** for every constructor — including the
    `mulx` two-register write and the `adcx`/`adox` flag-bearing write, which the
    register-projected `evalInst_eq_set` admits. This is the part of the `RegMachine`
    interface the multi-output `writtenNames` generalization (D3) unblocks for x86. -/
theorem jinstr_regmachine_step_data :
    (∀ (s : JState 64) (i : JInstr 64), (writesJ s i).map Prod.fst = writtenNames i) ∧
    (∀ (s : JState 64) (i : JInstr 64) (r : String),
      (runBlock s [i]).get r
        = ((writesJ s i).foldl (fun st p => JState.setReg st p.1 p.2) s).get r) :=
  ⟨writesJ_names, evalInst_eq_setJ⟩

/-- **x86 rewrite-length decomposition** — `GenericRegAlloc.rewriteBlock_length` at
    `JInstr 64` (needs only `MachineModel`, which is fully instantiated): the
    register-allocated block is one machine instruction per op plus exactly the inserted
    spill traffic. -/
theorem jinstr_rewriteBlock_length (decisions : List (String × Slot))
    (block : List (JInstr 64)) :
    (rewriteBlock decisions block).length
      = block.length + reloadCount decisions block + storeCount decisions block :=
  rewriteBlock_length decisions block

end CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrRegMachine
