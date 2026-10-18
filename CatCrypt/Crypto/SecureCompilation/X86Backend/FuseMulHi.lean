/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# The MULX-fusion post-pass on physical `Lprog` bodies

A `64×64→128` widening multiply reaches the physical, two-address `Lprog` as a low
`MUL` binding followed by a `MULXHI` binding for the high word, which the GP-linear
printer does not render. `fuseMulHiLprog` rewrites each such pair into the
printer's two-output `MULX` (multiplicand pinned into `%rdx`), so the emitted
assembly materialises both product words. The pass is a structural
`Lprog → Lprog` rewrite on the already-allocated body; `saveRdx := true` is the
looped-body mode that saves and restores `%rdx` around each fused site.

The soundness facts are stated against the `JasminModel` machine semantics
(`evalInstr`, `runBlock`, `x86_MULX_lo_hi`), the machine model that carries the
two-output `MULX`.

## Main results

* `fuseMulHiLprog`: the fusion over every function body of an `Lprog`.
* `fuseMulHiStep_sound`: the fused fragment `MOV RDX, s1 ; MULX hiDst loDst RDX s2`
  writes the low and high words of `s1 · s2` to `loDst` and `hiDst`, and writes no
  flag and no memory.
* `fuseSquareStep_sound`: the same for the squaring fragment of `squareSite`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog Lfundef Lcmd Linstr LinstrR LOperand stripWidthTag)

/-! ## 1. The MULX-fusion post-pass (byte-faithful `Lprog → Lprog`)

The `64×64→128` widening multiply is split, at the thirDialect-front level, into
a low `thBin .mul` (→ a low `MUL`/`imul`, single dst) and a separate `thMulHi`
(→ a `MULXHI` binding the GP-linear printer DROPS, §6 of the older shell). They
are never fused, so the emitted `.s` loses the high words `hi`/`mqHi` — the
pipeline gap. This post-pass mirrors `NttBflyThirEmit.legalizeShiftImmLprog`
(a structural, byte-faithful `Lprog → Lprog` rewrite that runs on the
already-physical, two-address body) and closes the gap by coalescing each
`MUL`+`MULXHI` pair into the printer's two-output `MULX` arm
(`LprogAsmPrinter` `[dl, dh] "MULX" [s]` ⟹ `mulx s, dl, dh`).

### What it matches

After physical/two-address lowering the FHE REDC body holds, per
`64×64→128` product, the consecutive pair (`s2` is the *shared* multiplicand,
`s1` the other):

```
  Lopn [loDst]  "MUL:64"    [loDst, s2]      -- low word  (two-address: loDst = a·b)
  Lopn [hiDst]  "MULXHI:64" [s1,    s2]      -- high word (dropped by the printer)
```

Both products read the same `s2` (`b` for `a·b`; `q` for `m·q`); the low op's
first source is its own destination (the two-address form), and the `MULXHI`'s
first source `s1` is the *other* multiplicand (`a` resp. `m`). The pass keys the
pair on the **shared second source `s2`** of an immediately-following `MULXHI`
matching a just-seen low `MUL`, taken up to the reload-scratch alias: the low
`MUL` is a binop and is re-lowered by the two-address legalizer, so a spilled
`s2` reaches it as the reserved scratch the legalizer reloaded it into, while the
`MULXHI` — not a binop — keeps the slot name. Resolving each reserved scratch to
the name last moved into it makes the two sides of such a pair name the same
value.

### How it rewrites (rdx pinning)

Intel `MULX dst_hi, dst_lo, src2` reads the implicit multiplicand from `%rdx`
(see `MpnRaEmit`'s "MULX coalesce" / the printer's `[dl,dh] MULX [s]` arm). The
pass emits, in place of the `MULXHI` line, an explicit `MOV:64 RDX, s1` (pin the
other multiplicand into `%rdx`) followed by `Lopn [loDst, hiDst] "MULX" [s2]`
(re-deriving the low word into `loDst` — identical value — and the high word
into `hiDst`). The standalone low `MUL` is left in place: its low word is read
*before* this point (the REDC computes `m = lo·qinv` from `loDst` between the two
mul sites), and the `MULX` recomputes the same low word, so the value is
unchanged.

### Why `%rdx` is free at both mul sites (and the relocation)

`%rdx` is the *allocated home* of the FIRST product's high word `hi`
(the allocator placed `mulhi(a,b) → RDX`), and `hi` is live until the final
`ADCX` (`u = hi + mqHi + cout`). The SECOND mul site's `MOV RDX, m` would
clobber that live `hi`. To keep the rewrite value-faithful the pass **relocates
any high word the pass itself assigns to `RDX`** into the caller-saved scratch
`R8` — which is unused anywhere in this straight-line REDC body (it is not in
the prologue's callee-saved `qsave` set, and never read/written by the core) —
and records a `RDX → R8` rename applied to every *subsequent* instruction (so
the final `ADCX` reads `hi` from `R8`). With `hi` evacuated to `R8`, `%rdx` is
free to carry the second multiplicand `m`; the second product's high word
`mqHi` lands in its own allocated `RDI` (no further conflict). Both mul sites
therefore get a clean `%rdx`.

The `R8` evacuation register is the one caller-saved GP register
(`R8 R9 R10 R11`) the REDC body never touches; the pass also renames any later
`RDX` use, so no live value is lost. -/

/-- The scratch register used to evacuate a high word the fusion would otherwise
    leave in `%rdx` (caller-saved, unused by the straight-line REDC core). -/
def fuseScratch : String := "R8"

/-- Recognise a low widening-multiply binding (`MUL`, optionally `:64`-tagged),
    the producer of the low word whose paired high word is a `MULXHI`. -/
def isLowMulMnem (opn : String) : Bool := stripWidthTag opn == "MUL"

/-- Recognise the high-word binding mnemonic (`MULXHI`, optionally `:64`). -/
def isMulHiMnem (opn : String) : Bool := stripWidthTag opn == "MULXHI"

/-- Apply a single `oldReg → newReg` rename to an operand. -/
def renameOperand (oldR newR : String) : LOperand → LOperand
  | .reg n => if n == oldR then .reg newR else .reg n
  | o => o

/-- Apply a single `oldReg → newReg` rename across an instruction's operands. -/
def renameInstr (oldR newR : String) (i : Linstr) : Linstr :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      ⟨i.li_ii, .Lopn (dsts.map (renameOperand oldR newR)) opn
        (srcs.map (renameOperand oldR newR))⟩
  | _ => i

/-! ### The reload-scratch alias

The two-address legalizer (`JasminLprogExport.legalizeBinop`) rewrites a binop
whose source is a red-zone spill slot into `MOV R15, k.N ; op dst, R15`, so a low
`MUL` whose multiplicand the allocator spilled carries the reserved scratch `R15`
(or `R14`, when the destination is spilled too) as its second source, while the
matching `MULXHI` — not a binop, hence not re-lowered — carries the slot name
`k.N`. Matching the pair on the raw operand name therefore misses exactly the
spilled multiplicands. Resolving each reserved scratch back to the name last
moved into it makes both sides of a pair name the same value. -/

/-- The reserved reload scratches (`R15` primary, `R14` secondary): never
    allocated to a value by the owned linear scan, so anything they hold is the
    two-address legalizer's transient reload of another operand. -/
def fuseReloadScratches : List String := [reloadScratch, reloadScratch2]

/-- The name each reserved reload scratch currently holds. -/
abbrev ScratchEnv := List (String × String)

/-- The pre-reload name of a register: a reserved reload scratch resolves to the
    name last moved into it, every other register to itself. -/
def scratchResolve (env : ScratchEnv) (r : String) : String :=
  match env.find? (fun p => p.1 == r) with
  | some (_, v) => v
  | none => r

/-- Record that reserved scratch `dst` holds `src`. -/
def scratchBind (env : ScratchEnv) (dst src : String) : ScratchEnv :=
  (dst, src) :: env.filter (fun p => p.1 != dst)

/-- Forget what reserved scratch `dst` holds. -/
def scratchKill (env : ScratchEnv) (dst : String) : ScratchEnv :=
  env.filter (fun p => p.1 != dst)

/-- The scratch environment after an instruction: a `MOV` into a reserved reload
    scratch records its source's pre-reload name; any other write to a reserved
    scratch forgets that scratch's content. -/
def scratchStep (env : ScratchEnv) (i : Linstr) : ScratchEnv :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      dsts.foldl (fun e d =>
        match d with
        | .reg dn =>
            if fuseReloadScratches.contains dn then
              match srcs with
              | [.reg sn] =>
                  if "MOV".isPrefixOf (stripWidthTag opn) then
                    scratchBind e dn (scratchResolve env sn)
                  else scratchKill e dn
              | _ => scratchKill e dn
            else e
        | _ => e) env
  | _ => env

/-- The home of the destination `d` of a low `MUL` with second source `s2`: when both are
    reserved reload scratches, the two-address legalizer has reloaded a spilled destination
    into `d`, and the home is the name last moved into `d`; otherwise `d` itself. -/
def lowHome (env : ScratchEnv) (d s2 : String) : String :=
  if fuseReloadScratches.contains d && fuseReloadScratches.contains s2 then scratchResolve env d
  else d

/-- Under the empty scratch environment the home of a low destination is the destination. -/
theorem lowHome_nil (d s2 : String) : lowHome [] d s2 = d := by
  simp [lowHome, scratchResolve]

/-- A low destination that is no reserved reload scratch is its own home. -/
theorem lowHome_of_not_scratch (env : ScratchEnv) {d s2 : String}
    (h : fuseReloadScratches.contains s2 = false) : lowHome env d s2 = d := by
  simp only [lowHome, h, Bool.and_false, Bool.false_eq_true, if_false]

/-- The fused site of a squaring `MULXHI d, [s1, s1]` with a spilled high destination `d` in
    the looped-body mode: the save of `RDX` in `R15`, the pin of `s1` in `RDX`, the two-output
    `MULX` with `RDX` as its explicit source and the reserved scratch `R14` as its high
    destination, the store of the high word to `d` and the restore of `RDX`. A register low
    destination `loDst` receives the low word from the `MULX`; a spilled one receives it
    through `RDX`, stored before the high word. -/
def squareSite (ii : Nat) (loDst d s1 : String) : List Linstr :=
  let pin : List Linstr :=
    [⟨ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩, ⟨ii, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩]
  let fin : List Linstr :=
    [⟨ii, .Lopn [.reg d] "MOV:64" [.reg reloadScratch2]⟩,
     ⟨ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
  if (LOperand.reg loDst).isSpill then
    pin ++ ⟨ii, .Lopn [.reg "RDX", .reg reloadScratch2] "MULX" [.reg "RDX"]⟩
      :: ⟨ii, .Lopn [.reg loDst] "MOV:64" [.reg "RDX"]⟩ :: fin
  else
    pin ++ ⟨ii, .Lopn [.reg loDst, .reg reloadScratch2] "MULX" [.reg "RDX"]⟩ :: fin

/-- The fusion worker over a body, carrying the reload-scratch environment and
    the list of pending low-`MUL` bindings seen so far (each as
    `(loDst, multiplicand)`) head-most-recent.

    A low `MUL`'s pending key is its second source resolved through the
    reload-scratch environment, so a multiplicand the allocator spilled is keyed
    on its slot name rather than on the transient scratch the two-address
    legalizer reloaded it into. On a `MULXHI [hiDst] [s1, s2]` whose resolved
    `s2` matches a pending key, emit the printer's fused `MULX`:
    `MOV:64 RDX, s1 ; MULX [loDst, hiDst'] [s2']`, where `hiDst'` is `hiDst`
    unless `hiDst = RDX` (then it is relocated to `fuseScratch` and a
    `RDX → fuseScratch` rename is threaded through the *rest* of the body, so
    the high word survives the next site's `MOV RDX, …`). Every other
    instruction passes through unchanged (after any active rename).

    `MULX` reads its explicit multiplicand from a register and writes two
    register destinations, so a spilled `s2` is reloaded into a reserved scratch
    (`s2'`) immediately before the `MULX`, a spilled `hiDst` is written through a
    reserved scratch and stored back, and a spilled `loDst` shares the high
    destination (the printer's coincident-destination arm routes the redundant
    low word — already materialised by the standalone low `MUL` — to a
    red-zone-saved scratch). A pair whose operands are all registers emits the
    plain three-instruction sequence.

    `saveRdx` (the LOOPED-body mode): this pass runs POST-RA, so its `MOV RDX,
    s1` pin silently clobbers whatever live range the allocator homed in
    `%rdx` — in a rolled loop that is the LOOP COUNTER (the fri_proof phase-2
    runaway). With `saveRdx := true` each fused site brackets the pin with
    `MOV R15, RDX … MOV RDX, R15` (`R15` = `reloadScratch`, reserved — never
    RA-allocated, and dead between its transient reload uses); an `s2 = RDX`
    source reads the saved copy, and the restore is skipped when the fused op
    itself redefines `RDX` (its old value is dead there). In this mode a pending
    low destination is recorded at its home (`lowHome`), and a squaring pair
    (`s1 = s2`) whose high destination is spilled becomes `squareSite`: `R15`
    holds the saved `RDX`, the `MULX` reads its multiplicand from `RDX`, and the
    high word goes through `R14`. Every other pair with a spilled high
    destination is left unfused. `false` (every straight-line caller) emits the
    original sequence byte-identically. -/
def fuseMulHiAux (saveRdx : Bool) :
    ScratchEnv → List (String × String) → Lcmd → Lcmd
  | _, _, [] => []
  | env, pend, i :: rest =>
    let env' := scratchStep env i
    match i.li_i with
    | .Lopn [.reg d] opn [.reg s1, .reg s2] =>
        if isLowMulMnem opn then
          -- Remember this low MUL (dst + resolved multiplicand) for a later
          -- MULXHI. (`s1` is the low op's own dst in two-address form.)
          i :: fuseMulHiAux saveRdx env'
            ((if saveRdx then lowHome env d s2 else d, scratchResolve env s2) :: pend) rest
        else if isMulHiMnem opn then
          -- Match the MOST-RECENT pending low `MUL` with the same multiplicand and
          -- CONSUME it (remove from `pend`), so a later `MULXHI` with the same
          -- operand (register reuse across butterflies) pairs with a DISTINCT
          -- low `MUL`.
          let key := scratchResolve env s2
          -- Under `saveRdx` the primary scratch carries the saved `%rdx`. A
          -- spilled high destination of a square goes through `R14`, which the
          -- `MULX` does not read (its explicit source is `%rdx`); any other pair
          -- with a spilled high destination is left unfused (the printer's
          -- sentinel).
          match pend.span (fun p => p.2 != key) with
          | (before, (loDst, _) :: after) =>
            if saveRdx && (LOperand.reg d).isSpill then
              if s1 == s2 && s1 != reloadScratch && loDst != "RDX"
                  && !fuseReloadScratches.contains loDst then
                squareSite i.li_ii loDst d s1
                  ++ fuseMulHiAux saveRdx ([reloadScratch, reloadScratch2].foldl scratchKill env')
                    (before ++ after) rest
              else
                i :: fuseMulHiAux saveRdx env' pend rest
            else
              let pend' := before ++ after          -- pend minus the matched entry
              -- `s1` is the OTHER multiplicand (pin into %rdx); `loDst` is the
              -- matched low word's home (re-derived, same value).
              let save : List Linstr :=
                if saveRdx then [⟨i.li_ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩]
                else []
              let rdxSaved := saveRdx && s2 == "RDX"
              let s2Spill := (LOperand.reg s2).isSpill
              let s2r :=
                if rdxSaved then reloadScratch
                else if s2Spill then reloadScratch2 else s2
              let srcReload : List Linstr :=
                if !rdxSaved && s2Spill then
                  [⟨i.li_ii, .Lopn [.reg s2r] "MOV:64" [.reg s2]⟩]
                else []
              let movRdx : Linstr := ⟨i.li_ii, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩
              if d == "RDX" then
                -- `bodyReservedGP` keeps `%rdx` out of the allocatable pool for
                -- any body holding a `MULXHI`, so an allocated high destination
                -- is never `%rdx`. Evacuating one would need a scratch outside
                -- the pool, and both reload scratches are already live here, so
                -- the pair is left unfused (the printer's sentinel) rather than
                -- rewritten through an allocatable register.
                i :: fuseMulHiAux saveRdx env' pend rest
              else
                let hiReg :=
                  if (LOperand.reg d).isSpill then
                    (if s2r == reloadScratch then reloadScratch2 else reloadScratch)
                  else d
                let loReg := if (LOperand.reg loDst).isSpill then hiReg else loDst
                let mulx : Linstr :=
                  ⟨i.li_ii, .Lopn [.reg loReg, .reg hiReg] "MULX" [.reg s2r]⟩
                let hiStore : List Linstr :=
                  if (LOperand.reg d).isSpill then
                    [⟨i.li_ii, .Lopn [.reg d] "MOV:64" [.reg hiReg]⟩]
                  else []
                let restore : List Linstr :=
                  if saveRdx && loDst != "RDX" then
                    [⟨i.li_ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
                  else []
                let envF :=
                  [reloadScratch, reloadScratch2, loReg, hiReg].foldl
                    scratchKill env'
                save ++ movRdx :: (srcReload ++ mulx :: (hiStore ++ restore
                  ++ fuseMulHiAux saveRdx envF pend' rest))
          | (_, []) => i :: fuseMulHiAux saveRdx env' pend rest
        else
          i :: fuseMulHiAux saveRdx env' pend rest
    | _ => i :: fuseMulHiAux saveRdx env' pend rest
  termination_by _ _ body => body.length
  decreasing_by all_goals simp_wf


/-- Fuse every paired low-`MUL` + `MULXHI` in a body into the printer's
    two-output `MULX`, pinning the multiplicand into `%rdx` and evacuating any
    `%rdx`-homed high word into `fuseScratch`. `saveRdx := true` is the
    looped-body mode (see `fuseMulHiAux`). -/
def fuseMulHiBody (body : Lcmd) (saveRdx : Bool := false) : Lcmd :=
  fuseMulHiAux saveRdx [] [] body

/-- **The squaring site in the looped-body mode.** A `MULXHI d, [s1, s1]` with a spilled high
    destination whose resolved multiplicand matches a pending low `MUL` with home `loDst`, a
    multiplicand other than `R15` and a home that is neither `RDX` nor a reload scratch,
    becomes `squareSite`. -/
theorem fuseMulHiAux_cons_square (env : ScratchEnv) (pend before after : List (String × String))
    (loDst k : String) (jj : Nat) (d opn s1 : String) (rest : Lcmd)
    (hnlo : isLowMulMnem opn = false) (hhi : isMulHiMnem opn = true)
    (hspan : pend.span (fun p => p.2 != scratchResolve env s1)
      = (before, (loDst, k) :: after))
    (hd : (LOperand.reg d).isSpill = true) (hs1 : (s1 != reloadScratch) = true)
    (hloR : (loDst != "RDX") = true) (hlo : fuseReloadScratches.contains loDst = false) :
    fuseMulHiAux true env pend (⟨jj, .Lopn [.reg d] opn [.reg s1, .reg s1]⟩ :: rest)
      = squareSite jj loDst d s1
        ++ fuseMulHiAux true ([reloadScratch, reloadScratch2].foldl scratchKill
          (scratchStep env ⟨jj, .Lopn [.reg d] opn [.reg s1, .reg s1]⟩)) (before ++ after) rest := by
  have hlo' : loDst ∉ fuseReloadScratches := by simpa using hlo
  rw [fuseMulHiAux]
  simp only [hspan]
  simp [hnlo, hhi, hd, hs1, hloR, hlo']

/-- Apply the MULX fusion to every function body of an `Lprog`. `saveRdx :=
    true` is the looped-body mode (see `fuseMulHiAux`); the default keeps every
    straight-line caller byte-identical. -/
def fuseMulHiLprog (p : Lprog) (saveRdx : Bool := false) : Lprog :=
  { p with
    lp_funcs := p.lp_funcs.map (fun (n, f) =>
      (n, { f with lfd_body := fuseMulHiBody f.lfd_body saveRdx })) }

/-! ## 2. MULX-fusion step soundness (model semantics)

The fusion coalesces the split low `MUL` + dropped-`MULXHI` pair — whose intended
denotation is the low product in `loDst` and the high product in `hiDst` — into
the single two-output `MOV RDX, s1 ; MULX hiDst loDst RDX s2`. Its correctness is
the fact that the fused `MULX` computes **both** product words the pair intended,
proved against the faithful `JasminModel` machine semantics (`evalInstr`,
`x86_MULX_lo_hi`, `runBlock`) — the only machine model that carries the
two-output `MULX` (`JasminLsem`'s single-output word-op fragment models neither
`MULX` nor `MULXHI`). -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
  (JInstr JState JOperand evalInstr runBlock x86_MULX_lo_hi x86_MOV)

/-- **The two-output `MULX` computes both product words.** From every start
    state, `mulx hiDst loDst a b` writes the low product `(x86_MULX_lo_hi ⟦a⟧ ⟦b⟧).1`
    to `loDst` and the high product `(x86_MULX_lo_hi ⟦a⟧ ⟦b⟧).2` to `hiDst`, and
    writes no flag and no memory. `loDst ≠ hiDst` is required for both words to
    land in distinct registers. -/
theorem mulx_computes (s : JState 64) (hiDst loDst : String) (a b : JOperand)
    (hlh : loDst ≠ hiDst) :
    (evalInstr s (.mulx hiDst loDst a b)).get loDst = (x86_MULX_lo_hi (a.eval s) (b.eval s)).1
    ∧ (evalInstr s (.mulx hiDst loDst a b)).get hiDst = (x86_MULX_lo_hi (a.eval s) (b.eval s)).2
    ∧ (evalInstr s (.mulx hiDst loDst a b)).flags = s.flags
    ∧ (evalInstr s (.mulx hiDst loDst a b)).mem = s.mem := by
  cases hp : x86_MULX_lo_hi (a.eval s) (b.eval s) with
  | mk lo hi =>
    have hev : evalInstr s (.mulx hiDst loDst a b) = (s.setReg loDst lo).setReg hiDst hi := by
      simp only [evalInstr, hp]
    rw [hev]
    refine ⟨?_, ?_, rfl, rfl⟩
    · simp only [Jasmin.JState.get, Jasmin.JState.setReg]
      rw [if_neg hlh]; simp
    · simp only [Jasmin.JState.get, Jasmin.JState.setReg]; simp

/-- The fused `MULX`'s low word is exactly the low product `v1 · v2` the
    standalone low-`MUL` already materialised, so re-deriving it in the fused op
    is value-neutral. Ties the fused low word (`x86_MULX_lo_hi …).1`) to the
    two-address low-`MUL` value. -/
theorem mulx_lo_eq_mul (v1 v2 : BitVec 64) : (x86_MULX_lo_hi v1 v2).1 = v1 * v2 := by
  apply BitVec.eq_of_toNat_eq
  simp [x86_MULX_lo_hi, Jasmin.wumul, BitVec.toNat_ofNat, BitVec.toNat_mul]

/-- **The MULX-fusion fragment is value-sound.** The fused two-instruction
    fragment `MOV RDX, s1 ; MULX hiDst loDst RDX s2` reaches the low product
    `s1·s2` in `loDst` and the high product `mulhi(s1, s2)` in `hiDst`, writing no
    flag and no memory — the two words the dropped low-`MUL` + `MULXHI` pair
    intended. `s2 ≠ "RDX"` (the multiplicand is not clobbered by the `%rdx` pin)
    and `loDst ≠ hiDst` (the products land in distinct registers) are the pass's
    allocation invariants. -/
theorem fuseMulHiStep_sound (s : JState 64) (s1 s2 hiDst loDst : String)
    (hs2 : s2 ≠ "RDX") (hlh : loDst ≠ hiDst) :
    (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg s2)]).get loDst
        = (x86_MULX_lo_hi (s.get s1) (s.get s2)).1
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg s2)]).get hiDst
        = (x86_MULX_lo_hi (s.get s1) (s.get s2)).2
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg s2)]).flags = s.flags
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg s2)]).mem = s.mem := by
  -- After `MOV RDX, s1`, `RDX = s1`; `s2 ≠ RDX` keeps the multiplicand intact.
  have hmov : evalInstr s (.mov "RDX" (.reg s1)) = s.setReg "RDX" (s.get s1) := by
    simp only [evalInstr, JOperand.eval, x86_MOV]
  obtain ⟨hlo, hhi, hfl, hmem⟩ :=
    mulx_computes (evalInstr s (.mov "RDX" (.reg s1))) hiDst loDst (.reg "RDX") (.reg s2) hlh
  have ha : (JOperand.reg "RDX").eval (evalInstr s (.mov "RDX" (.reg s1))) = s.get s1 := by
    rw [hmov]; simp [JOperand.eval, Jasmin.JState.get, Jasmin.JState.setReg]
  have hb : (JOperand.reg s2).eval (evalInstr s (.mov "RDX" (.reg s1))) = s.get s2 := by
    rw [hmov]; simp only [JOperand.eval, Jasmin.JState.get, Jasmin.JState.setReg, if_neg hs2]
  have hflmov : (evalInstr s (.mov "RDX" (.reg s1))).flags = s.flags := by rw [hmov]; rfl
  have hmemmov : (evalInstr s (.mov "RDX" (.reg s1))).mem = s.mem := by rw [hmov]; rfl
  simp only [runBlock]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlo, ha, hb]
  · rw [hhi, ha, hb]
  · rw [hfl, hflmov]
  · rw [hmem, hmemmov]

/-- **The squaring fragment of `squareSite` is value-sound.** `MOV RDX, s1 ; MULX hiDst loDst
    RDX RDX` reaches the low word of `s1 · s1` in `loDst` and the high word in `hiDst`,
    writing no flag and no memory. -/
theorem fuseSquareStep_sound (s : JState 64) (s1 hiDst loDst : String) (hlh : loDst ≠ hiDst) :
    (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg "RDX")]).get loDst
        = (x86_MULX_lo_hi (s.get s1) (s.get s1)).1
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg "RDX")]).get hiDst
        = (x86_MULX_lo_hi (s.get s1) (s.get s1)).2
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg "RDX")]).flags
        = s.flags
    ∧ (runBlock s [.mov "RDX" (.reg s1), .mulx hiDst loDst (.reg "RDX") (.reg "RDX")]).mem
        = s.mem := by
  have hmov : evalInstr s (.mov "RDX" (.reg s1)) = s.setReg "RDX" (s.get s1) := by
    simp only [evalInstr, JOperand.eval, x86_MOV]
  obtain ⟨hlo, hhi, hfl, hmem⟩ :=
    mulx_computes (evalInstr s (.mov "RDX" (.reg s1))) hiDst loDst (.reg "RDX") (.reg "RDX") hlh
  have ha : (JOperand.reg "RDX").eval (evalInstr s (.mov "RDX" (.reg s1))) = s.get s1 := by
    rw [hmov]; simp [JOperand.eval, Jasmin.JState.get, Jasmin.JState.setReg]
  have hflmov : (evalInstr s (.mov "RDX" (.reg s1))).flags = s.flags := by rw [hmov]; rfl
  have hmemmov : (evalInstr s (.mov "RDX" (.reg s1))).mem = s.mem := by rw [hmov]; rfl
  simp only [runBlock]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlo, ha]
  · rw [hhi, ha]
  · rw [hfl, hflmov]
  · rw [hmem, hmemmov]

end CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
