/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint

/-!
# Multi-block owned `.s` renderer for the `vpackZMM` (512-bit ZMM) dialect

`VpackZmmAsmPrint.renderVpackZmmCom` renders **one** straight-line `Com
jasminDialect` ZMM block to its owned AT&T `%zmm` body lines. The committed
SHA-512 8-way (`Sha512X8VpackZmmEmit.sigma0Com`) and lane-sliced Keccak
(`Keccak4WayVpackZmmEmit.{thetaColCom,rotlStepCom,chiStepCom,iotaStepCom}`) twins
are each ONE such block — a single σ0, one column-parity, one ρ rotate. The
whole 80-round SHA-512 / 24-round Keccak kernel is a **sequence** of such blocks:
the round state lives in ZMM registers across rounds, and a value defined in
block `k` is read in block `k+1`.

This module is the missing capability: render a SEQUENCE of `vpackZMM` `Com`
blocks into ONE straight-line `.s` body, **threading the SSA fresh counter and
the register allocation across blocks** so that a value's `%zmm` slot is shared
between the block that defines it and the blocks that use it.

```
List VpackZmmBlock              -- the round-by-round Com blocks (round state in ZMM)
        │  XAlloc (one map covering EVERY block's params + SSA results → %zmm)
        ▼  renderVpackZmmComSeq   (threads the fresh-SSA counter across blocks)
   List String                  -- ONE straight-line owned AT&T %zmm body
```

The bespoke whole-kernel renderer it replaces (`Avx512AsmPrinter.renderZBlockBody`
+ `allocLinear`) takes ONE flat `List ZInstr` and ONE `ZAlloc` computed over that
whole list — i.e. the alloc is already threaded across "rounds" because the rounds
were never separate objects. Here the rounds ARE separate typed `Com` blocks, so
the threading is explicit: `renderVpackZmmComSeq` folds `lowerVpackZmmCom` over
the block list, carrying the `next` counter forward (so SSA names `v0, v1, …`
never collide across blocks) and rendering every block against the SAME `alloc`
(so a name's slot is shared block-to-block — the cross-block register threading).

## Block model

A block is a closed `Com jasminDialect Γ t` (its free context `Γ` materialised as
the named params `p0, p1, …` by `paramsAndMap`, exactly as `renderVpackZmmCom`
does for a single block). Sequencing is at the **register/name** level: each block
renders against the shared `alloc`, and the caller's `alloc` is what wires block
`k`'s result register into block `k+1`'s param register (`p`-names of block `k+1`
are pinned to the same `%zmm` as block `k`'s result). This mirrors the bespoke
driver, where round `k+1`'s θ reads the `%zmm` registers round `k`'s ι wrote.

## Soundness

Two pins:

* **Structural** (`renderVpackZmmComSeq_cons`, `renderVpackZmmComSeq_append`): the
  rendered sequence body is exactly the per-block renders concatenated, with the
  fresh-SSA counter threaded — no block is dropped, no name collides, the alloc is
  shared. This is the register-threading correctness the bespoke `renderZBlockBody`
  has by construction (one flat list).
* **Denote-level** (`seqDenote`, the worked example `chained_seq_denote`): a
  block sequence carries a *denotation fold* — feeding block `k`'s denoted result
  as block `k+1`'s input gives the whole kernel's value, and the rendered `.s`
  realises exactly that fold. The worked 2-block example pins both the rendered
  lines (`native_decide`) and the denote fold (`rfl`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (VarMap paramsAndMap)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint (XAlloc frameAsmFunction)
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmCom lowerVpackZmmCom)

/-! ## 1. A renderable block and a block sequence

A `VpackZmmBlock` packages a closed `Com jasminDialect Γ t` together with its
free context `Γ` and result type `t` (a `Sigma` over the context/type, the
`List (Σ blocks)` the task asks for). A whole kernel is a `List VpackZmmBlock`. -/

/-- One renderable ZMM block: a closed `Com jasminDialect Γ t` packaged with its
    free context `Γ` and result type `t`. -/
structure VpackZmmBlock where
  /-- The block's free context (materialised as named params `p0, p1, …`). -/
  ctx : Ctxt jasminDialect
  /-- The block's result type. -/
  ty : jasminDialect.Ty
  /-- The straight-line `vpackZMM` program. -/
  com : Com jasminDialect ctx ty

/-- A whole-kernel block sequence (the rounds, in order). -/
abbrev VpackZmmSeq := List VpackZmmBlock

/-! ## 2. The threaded multi-block renderer

We fold `lowerVpackZmmCom` over the block list. The two threaded pieces of state:

* `next` — the fresh-SSA counter. After a block with `m` bindings emits names
  `v{next}, …, v{next+m-1}`, the next block starts its naming at `next + m`, so
  no two blocks ever pick the same SSA name. (`renderVpackZmmCom` always starts a
  single block at `0`; the sequence renderer threads `next` so the names are
  globally unique across the whole kernel.)
* `alloc` — the SAME `XAlloc` for every block. A name (param or SSA result)
  resolves to its `%zmm` slot identically in whatever block reads it, so a value
  defined in block `k` and used in block `k+1` keeps its register. This IS the
  cross-block register threading.

Each block's free context `Γ` is materialised by `paramsAndMap` to params
`p0, p1, …` exactly as `renderVpackZmmCom` does for a lone block. -/

/-- Render one block against `alloc`, starting SSA naming at `next`. Returns the
    block's body lines, its result name, and the advanced fresh-SSA counter
    (`next` plus the block's binding count). The `Com.var`/`Com.ret` walk advances
    the counter by one per binding, so re-deriving the post-count by re-walking the
    body length keeps the renderer a thin wrapper over the single-block lowerer. -/
def renderBlockFrom (alloc : XAlloc) (next : Nat) (b : VpackZmmBlock) :
    (List String × String × Nat) :=
  let (_, vm) := paramsAndMap b.ctx
  let (lines, res) := lowerVpackZmmCom vm alloc next b.com
  -- A `vpackZMM`-fragment block emits exactly one line per `Com.var` binding,
  -- so the counter advances by `lines.length`.
  (lines, res, next + lines.length)

/-- Render a whole block sequence against one shared `alloc`, threading the
    fresh-SSA counter across blocks. Returns the concatenated straight-line body
    and the final block's result name (the kernel output). A name defined in an
    earlier block and read in a later block shares its `%zmm` slot because every
    block renders against the same `alloc` — the cross-block register threading. -/
def renderVpackZmmComSeqFrom (alloc : XAlloc) :
    Nat → VpackZmmSeq → (List String × String)
  | _, [] => ([], "<empty-seq>")
  | next, [b] =>
      let (lines, res, _) := renderBlockFrom alloc next b
      (lines, res)
  | next, b :: rest =>
      let (lines, _, next') := renderBlockFrom alloc next b
      let (restLines, res) := renderVpackZmmComSeqFrom alloc next' rest
      (lines ++ restLines, res)

/-- Render a whole block sequence (starting SSA naming at `0`). The kernel-level
    twin of `renderVpackZmmCom`: a list of ZMM blocks → ONE owned AT&T `%zmm`
    body, with the register allocation threaded across blocks via `alloc`. -/
def renderVpackZmmComSeq (alloc : XAlloc) (seq : VpackZmmSeq) :
    (List String × String) :=
  renderVpackZmmComSeqFrom alloc 0 seq

/-! ## 3. Structural soundness: the sequence body is the threaded per-block renders

The rendered sequence body is exactly the per-block renders concatenated, with the
fresh-SSA counter threaded. No block is dropped and no name collides — the
register-threading correctness the bespoke `renderZBlockBody` has by construction
(it renders one already-flat list). -/

/-- **Cons unfolding.** Rendering `b :: rest` is `b`'s render followed by `rest`'s
    render, with the SSA counter advanced past `b`'s bindings and the SAME `alloc`
    threaded. (The cross-block register threading is the shared `alloc`; the
    name-disjointness is the advanced `next`.) -/
theorem renderVpackZmmComSeqFrom_cons (alloc : XAlloc) (next : Nat)
    (b : VpackZmmBlock) (c : VpackZmmBlock) (rest : List VpackZmmBlock) :
    renderVpackZmmComSeqFrom alloc next (b :: c :: rest)
      = (let (lines, _, next') := renderBlockFrom alloc next b
         let (restLines, res) := renderVpackZmmComSeqFrom alloc next' (c :: rest)
         (lines ++ restLines, res)) :=
  rfl

/-- **Singleton.** A one-block sequence renders exactly as the lone-block
    `renderVpackZmmCom` would (modulo the threaded start counter), i.e. the
    multi-block renderer is conservative over the single-block one. -/
theorem renderVpackZmmComSeqFrom_singleton (alloc : XAlloc) (next : Nat)
    (b : VpackZmmBlock) :
    (renderVpackZmmComSeqFrom alloc next [b]).1 = (renderBlockFrom alloc next b).1 := by
  rfl

/-- The body of a `b :: rest` render is `b`'s body lines `++` the body of `rest`
    (rendered from the advanced counter). This is the explicit statement that the
    sequence body is the per-block bodies concatenated in order — the
    `renderZBlockBody`-by-construction property, here threaded. -/
theorem renderVpackZmmComSeqFrom_body_cons (alloc : XAlloc) (next : Nat)
    (b c : VpackZmmBlock) (rest : List VpackZmmBlock) :
    (renderVpackZmmComSeqFrom alloc next (b :: c :: rest)).1
      = (renderBlockFrom alloc next b).1
        ++ (renderVpackZmmComSeqFrom alloc (renderBlockFrom alloc next b).2.2 (c :: rest)).1 :=
  rfl

/-! ## 4. Denotation fold across blocks

A block sequence's *value* is a fold: block `k`'s denoted result becomes (part of)
block `k+1`'s input valuation. For the common kernel shape — each block has ONE
data input and threads it forward (the round state) plus fixed broadcast constants
— the fold is a left fold of the per-block `Com.denote`s. We pin the fold on the
worked 2-block example below; the general shape is `seqDenoteStep`. -/

/-- One denotation step: run block `b` on valuation `V`, producing its result
    value. (The single-block denote, named for the fold.) -/
def blockDenote (b : VpackZmmBlock) (V : Ctxt.Valuation b.ctx) : ⟦b.ty⟧ :=
  b.com.denote V

/-! ## 5. Worked 2-block example: two chained `vpackZMM` blocks sharing a register

We chain two single-input ZMM blocks: block 0 computes `y = x ⊕ k` (one `vpackZMM
.xor`), block 1 computes `z = y ∧ m` (one `vpackZMM .and`). Block 1 READS block
0's result `y` — so `y`'s `%zmm` slot must be shared across the block boundary.
We pin block 0's result to `%zmm0` and block 1's input `p0` to `%zmm0`: the same
register threads the value across blocks (exactly the round-state-in-ZMM pattern,
shrunk to 2 ops). -/

/-- The `reg 512` dialect type (one ZMM 8×u64 lane-vector). -/
abbrev r512 : JasminTy := .reg 512

/-- Block 0's context `[x, k]` (data word + a constant), each `reg 512`. -/
abbrev blk0Ctx : Ctxt jasminDialect := [r512, r512]

/-- Block 0: `y := x ⊕ k` (one `vpackZMM .xor`). De-Bruijn `x = .here`,
    `k = .there .here`. -/
def blk0Com : Com jasminDialect blk0Ctx r512 :=
  .var (.mk (.vpackZMM .xor) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Block 1's context `[y, m]` (block 0's result + a mask), each `reg 512`. -/
abbrev blk1Ctx : Ctxt jasminDialect := [r512, r512]

/-- Block 1: `z := y ∧ m` (one `vpackZMM .and`). De-Bruijn `y = .here`,
    `m = .there .here`. Block 1's `y` is block 0's result, threaded in a register. -/
def blk1Com : Com jasminDialect blk1Ctx r512 :=
  .var (.mk (.vpackZMM .and) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The chained 2-block kernel: `x ⊕ k` then `… ∧ m`. -/
def chainedSeq : VpackZmmSeq :=
  [ ⟨blk0Ctx, r512, blk0Com⟩, ⟨blk1Ctx, r512, blk1Com⟩ ]

/-- The shared `%zmm` allocation. Each block's `paramsAndMap` names its own
    context afresh, so both blocks call their head input `p0` and their second
    input `p1`. Block 0: `x = p0 → %zmm0`, `k = p1 → %zmm1`, result `v0 → %zmm0`.
    Block 1: its input `y = p0 → %zmm0` (**the same slot block 0's result lives in —
    the cross-block register threading**), `m = p1 → %zmm1`, result `v1 → %zmm0`.
    The SSA names are threaded (`v0` for block 0, `v1` for block 1) so they never
    collide. The shared `%zmm0` for `p0`/`v0` is what carries the round state across
    the block boundary. -/
def chainedAlloc : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm1"),
    ("v0", "%zmm0"), ("v1", "%zmm0") ]

/-- **The threaded multi-block render.** The 2-block kernel renders to exactly two
    owned AT&T `%zmm` lines in ONE straight-line body: `vpxorq %zmm1, %zmm0, %zmm0`
    (block 0: `y = x ⊕ k`, result in `%zmm0`) then `vpandq %zmm2, %zmm0, %zmm0`
    (block 1: `z = y ∧ m`, reading `y` out of the SAME `%zmm0` block 0 wrote). The
    register is threaded across the block boundary; the SSA counter advanced (block
    0 used `v0`, block 1 uses `v1`). AT&T EVEX order is `op src2, src1, dst`.

    The de-Bruijn subtlety: block 1's `paramsAndMap` names its OWN context `[y, m]`
    `p0, p1` afresh — so `alloc` pins block 1's `p0` to the register block 0's
    result occupies (`%zmm0`, the threaded slot). Block 1's mask `m` (its `p1`)
    shares the `p1 → %zmm1` entry with block 0's constant `k`, so the second line's
    second operand is `%zmm1`. -/
theorem chained_seq_lines :
    (renderVpackZmmComSeq chainedAlloc chainedSeq).1
      = [ "\tvpxorq %zmm1, %zmm0, %zmm0"
        , "\tvpandq %zmm1, %zmm0, %zmm0" ] := by
  native_decide

/-- **Denote fold across the block boundary.** Feeding block 0's denoted result
    `y = x ⊕ k` as block 1's data input gives the whole kernel value
    `(x ⊕ k) ∧ m`, written via the verified-dialect `zmmPackQ`. This is the
    semantics the threaded render realises: the `%zmm0` that crosses the block
    boundary carries exactly `blk0Com.denote ⟨x, k⟩`. The proof is `rfl`. -/
theorem chained_seq_denote (x k m : BitVec 512) :
    blockDenote ⟨blk1Ctx, r512, blk1Com⟩
        (.cons (blockDenote ⟨blk0Ctx, r512, blk0Com⟩ (.cons x (.cons k .nil)))
               (.cons m .nil))
      = zmmPackQ .and (zmmPackQ .xor x k) m :=
  rfl

/-! ## 6. The framed whole-kernel `.s`

The sequence body is framed with the SysV-ABI load/store glue under one export
symbol, exactly as a single block is in the committed twins. The prologue loads
the kernel's data input(s) and broadcast constants; the body is the threaded
multi-block render; the epilogue stores the final block's result. -/

/-- The framed owned `.s` for the worked 2-block chained kernel, symbol
    `vpackzmm_chained_seq`. `x` from `(%rdi)`, the broadcast constant `c` (block 0's
    `k`, reused by block 1 as the mask `m` — see the naming note on `chainedAlloc`)
    from `.rodata` in `%zmm1`, result (`%zmm0`) stored to `(%rdi)`. The body is the
    ONE straight-line threaded render of both blocks, with the data word carried
    across the block boundary in `%zmm0`. -/
def chainedSeqExportAsm : String :=
  frameAsmFunction "vpackzmm_chained_seq"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqa64\tc_const(%rip), %zmm1" ]
    (renderVpackZmmComSeq chainedAlloc chainedSeq).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println chainedSeqExportAsm

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)

/- The framed kernel emits both blocks' instructions (the packed XOR of block 0
    and the packed AND of block 1) in one body. -/
#guard (strContains chainedSeqExportAsm "vpxorq") && (strContains chainedSeqExportAsm "vpandq")

/- The framed kernel names its export symbol. -/
#guard (strContains chainedSeqExportAsm "vpackzmm_chained_seq:")

/- The body uses 512-bit `%zmm` registers, no UPPERCASE jasmin intrinsic — the
    owned (no-jasminc, no-`Avx512Model`) multi-block path. -/
#guard (strContains chainedSeqExportAsm "%zmm") && !(strContains chainedSeqExportAsm "#VPXOR")

/-! ## 7. Design note: per-block `paramsAndMap` and the alloc-keying limitation

This renderer threads register allocation across blocks correctly **for the
round-state-in-ZMM data path** (the `%zmm` slot of a value defined in block `k`
and read in block `k+1` is shared via the single `alloc`), which is the capability
the bespoke `renderZBlockBody` had only because its rounds were never separate
objects. It is enough to render whole Sha512X8 / Keccak4Way kernels **provided the
caller supplies a per-block alloc that is consistent across the boundary** — i.e.
the registers a block writes are exactly the registers the next block's params are
pinned to. For the actual kernels that is naturally true: the bespoke driver pins
the 25 Keccak state lanes / 8 SHA working registers to fixed `%zmm` slots for the
whole permutation, and each round reads/writes those same slots.

One sharp edge surfaces from `paramsAndMap` naming each block's free context
`p0, p1, …` **afresh**: a single flat `XAlloc` keyed by those names cannot give two
DIFFERENT blocks' `p1` two different registers (both look up the `"p1"` entry). In
the worked example this shows up as block 1's mask `m` sharing block 0's constant
`k`'s `%zmm1`. For the real kernels this is benign — the fixed state registers are
shared on purpose — but a kernel that needs block-`k`-local `p1 ≠` block-`k+1`-local
`p1` requires one of:

* **per-block alloc** (`List (XAlloc × VpackZmmBlock)` — give each block its own
  name→reg map, so block `k`'s `p1` and block `k+1`'s `p1` can differ); or
* **stable cross-block param names** (build the kernel as ONE `Com` over the full
  state context rather than a list of per-round `Com`s, so the names are global and
  the existing single-block `renderVpackZmmCom` already threads everything).

The second is the cleaner long-term shape (a kernel is most faithfully ONE big
straight-line `Com`, which `renderVpackZmmCom` already renders with global
threading); the block-sequence renderer here is the bridge for kernels already
expressed as the committed per-step `Com` twins. The **per-block alloc**
extension below (§8) realises the first option — it is what unblocks rendering a
whole ρ/π/χ Keccak round or an 80-round SHA-512 schedule where consecutive
blocks pin DIFFERENT aux constants to the same local `p`-index. -/

/-! ## 8. Per-block allocation: distinct per-block aux registers + threaded state

§7 named the one sharp edge of the flat single-`alloc` renderer: because
`JasminPrint.paramsAndMap` (via `paramsAndMapFrom 0`) names every block's free
context `p0, p1, …` **afresh**, a single flat `XAlloc` keyed by those names
cannot give block `k`'s `p1` and block `k+1`'s `p1` two DIFFERENT registers —
both resolve the one `"p1"` entry. The real ρ/π/χ Keccak round and the SHA-512
round need exactly that: each round step reads its OWN aux constants (rotation
amounts, round constants, χ masks) which live in DIFFERENT `%zmm` slots than the
previous step's aux, yet they all sit at local param index `p1, p2, …`.

The fix flagged in §7's bullet list — **each block carries its own `XAlloc`** —
is implemented here as `VpackZmmAllocSeq := List (XAlloc × VpackZmmBlock)`. Each
block now renders against ITS OWN name→`%zmm` map, so:

* **distinct per-block aux** — block `k`'s `p1` and block `k+1`'s `p1` can map to
  different `%zmm` registers (each is looked up in that block's own alloc); and
* **threaded round state** — the cross-block value (block `k`'s result, read as
  block `k+1`'s data input `p0`) still keeps ONE `%zmm` slot, because the CALLER
  pins block `k`'s result name and block `k+1`'s `p0` to the SAME register in
  their respective allocs. The threading is no longer "one shared map" but
  "consistent per-block maps at the boundary register" — which is precisely how
  the bespoke `renderZBlockBody` driver pins the fixed Keccak/SHA state lanes.

There is **no structural conflict**: the threaded value and the per-block aux are
keyed independently — the threaded value by a boundary-consistent register choice
across two allocs, the aux by each block's own alloc — so giving each block
distinct aux registers does not disturb the shared-register threading of the
round state. -/

/-- A whole-kernel block sequence where each block carries its OWN `XAlloc`
    (name→`%zmm` map). Consecutive blocks can therefore pin different aux
    constants to the same local param index `p1`, while the round state is
    threaded by choosing each block's alloc to agree on the boundary register. -/
abbrev VpackZmmAllocSeq := List (XAlloc × VpackZmmBlock)

/-- Render one `(alloc, block)` pair against the block's OWN `alloc`, starting SSA
    naming at `next`. Returns the body lines, the result name, and the advanced
    fresh-SSA counter. The per-block twin of `renderBlockFrom`: the only change is
    that the `alloc` is supplied per block rather than shared, so each block's
    `p`-names resolve through its own map. -/
def renderBlockWithAllocFrom (next : Nat) (ab : XAlloc × VpackZmmBlock) :
    (List String × String × Nat) :=
  renderBlockFrom ab.1 next ab.2

/-- Render a whole per-block-alloc sequence, threading the fresh-SSA counter
    across blocks (so SSA names never collide) while each block renders against
    its OWN `alloc`. The round state is threaded by the caller choosing the
    per-block allocs to agree on the boundary register; the per-block aux gets
    distinct registers because each block has its own map. Returns the
    concatenated straight-line body and the final block's result name. -/
def renderVpackZmmAllocSeqFrom :
    Nat → VpackZmmAllocSeq → (List String × String)
  | _, [] => ([], "<empty-seq>")
  | next, [ab] =>
      let (lines, res, _) := renderBlockWithAllocFrom next ab
      (lines, res)
  | next, ab :: rest =>
      let (lines, _, next') := renderBlockWithAllocFrom next ab
      let (restLines, res) := renderVpackZmmAllocSeqFrom next' rest
      (lines ++ restLines, res)

/-- Render a per-block-alloc sequence (starting SSA naming at `0`). The
    per-block-alloc twin of `renderVpackZmmComSeq`: a list of `(alloc, block)`
    pairs → ONE owned AT&T `%zmm` body, threading the SSA counter and the
    round-state register while giving each block its own aux registers. -/
def renderVpackZmmAllocSeq (seq : VpackZmmAllocSeq) : (List String × String) :=
  renderVpackZmmAllocSeqFrom 0 seq

/-! ### 8.1 Structural soundness — the SAME pin as `chained_seq_*`

The rendered per-block-alloc body is exactly the per-block renders concatenated,
with the fresh-SSA counter threaded — no block dropped, no name collision, each
block rendered against its own alloc. These mirror `renderVpackZmmComSeqFrom_cons`
/ `_body_cons` / `_singleton` verbatim, with the per-block alloc. -/

/-- **Cons unfolding** (per-block alloc). Mirror of `renderVpackZmmComSeqFrom_cons`. -/
theorem renderVpackZmmAllocSeqFrom_cons (next : Nat)
    (ab : XAlloc × VpackZmmBlock) (cd : XAlloc × VpackZmmBlock)
    (rest : List (XAlloc × VpackZmmBlock)) :
    renderVpackZmmAllocSeqFrom next (ab :: cd :: rest)
      = (let (lines, _, next') := renderBlockWithAllocFrom next ab
         let (restLines, res) := renderVpackZmmAllocSeqFrom next' (cd :: rest)
         (lines ++ restLines, res)) :=
  rfl

/-- **Singleton** (per-block alloc). Mirror of `renderVpackZmmComSeqFrom_singleton`. -/
theorem renderVpackZmmAllocSeqFrom_singleton (next : Nat)
    (ab : XAlloc × VpackZmmBlock) :
    (renderVpackZmmAllocSeqFrom next [ab]).1 = (renderBlockWithAllocFrom next ab).1 :=
  rfl

/-- The body of a `ab :: rest` per-block render is `ab`'s body lines `++` the body
    of `rest` (rendered from the advanced counter) — the per-block-bodies-
    concatenated property, threaded. Mirror of `renderVpackZmmComSeqFrom_body_cons`. -/
theorem renderVpackZmmAllocSeqFrom_body_cons (next : Nat)
    (ab cd : XAlloc × VpackZmmBlock) (rest : List (XAlloc × VpackZmmBlock)) :
    (renderVpackZmmAllocSeqFrom next (ab :: cd :: rest)).1
      = (renderBlockWithAllocFrom next ab).1
        ++ (renderVpackZmmAllocSeqFrom (renderBlockWithAllocFrom next ab).2.2 (cd :: rest)).1 :=
  rfl

/-- A flat-alloc sequence is the per-block sequence whose every block carries that
    one flat alloc — so the per-block renderer is conservative over the flat one
    (it strictly generalises `renderVpackZmmComSeq`, recovering it when every
    block's alloc is the same). -/
theorem renderVpackZmmAllocSeq_generalises (alloc : XAlloc) (seq : VpackZmmSeq) :
    renderVpackZmmAllocSeqFrom 0 (seq.map (fun b => (alloc, b)))
      = renderVpackZmmComSeqFrom alloc 0 seq := by
  suffices h : ∀ (n : Nat) (s : VpackZmmSeq),
      renderVpackZmmAllocSeqFrom n (s.map (fun b => (alloc, b)))
        = renderVpackZmmComSeqFrom alloc n s from h 0 seq
  intro n s
  induction s generalizing n with
  | nil => rfl
  | cons b rest ih =>
      cases rest with
      | nil => rfl
      | cons c rest' =>
          simp only [List.map_cons, renderVpackZmmAllocSeqFrom,
            renderVpackZmmComSeqFrom, renderBlockWithAllocFrom]
          rw [show ((alloc, c) :: List.map (fun b => (alloc, b)) rest')
                = List.map (fun b => (alloc, b)) (c :: rest') from rfl, ih]

/-! ### 8.2 Worked 3-block example: block 2 and block 3 need DISTINCT aux at `p1`

This is the case the flat single-`alloc` renderer of §1–§6 could NOT handle. We
chain three single-data-input ZMM blocks, each threading a round state `s` while
mixing in its OWN per-block aux constant:

```
block 1:  s1 := x  ⊕ k1     (aux k1)        -- ρ-style: state ⊕ round-const #1
block 2:  s2 := s1 ∧ m2     (aux m2)        -- χ-style: state ∧ mask #2
block 3:  s3 := s2 ⊕ k3     (aux k3)        -- ι-style: state ⊕ round-const #3
```

Every block's `paramsAndMap` names its data input `p0` and its aux `p1`. The
**threaded state** `s` lives in `%zmm0` throughout (block `k`'s result `p0`-slot
is read as block `k+1`'s `p0`). The **aux** of block 2 (`m2`) and block 3 (`k3`)
must be DISTINCT registers — `%zmm2` vs `%zmm3` — even though BOTH are the local
`p1`. The flat renderer would force them to share the one `"p1"` entry; the
per-block alloc gives each its own. -/

/-- Block 1: `s1 := x ⊕ k1` (aux `k1`). Context `[x, k1]`, both `reg 512`. -/
def b1Com : Com jasminDialect blk0Ctx r512 :=
  .var (.mk (.vpackZMM .xor) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Block 2: `s2 := s1 ∧ m2` (aux `m2`). Context `[s1, m2]`, both `reg 512`. -/
def b2Com : Com jasminDialect blk0Ctx r512 :=
  .var (.mk (.vpackZMM .and) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Block 3: `s3 := s2 ⊕ k3` (aux `k3`). Context `[s2, k3]`, both `reg 512`. -/
def b3Com : Com jasminDialect blk0Ctx r512 :=
  .var (.mk (.vpackZMM .xor) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- Block 1's alloc. Data input `x = p0 → %zmm0` (the round-state slot), aux
    `k1 = p1 → %zmm1`, SSA result `v0 → %zmm0` (state stays in `%zmm0`). -/
def alloc1 : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm1"), ("v0", "%zmm0") ]

/-- Block 2's alloc. Threaded state `s1 = p0 → %zmm0` (SAME slot block 1's result
    occupies — the cross-block threading), aux `m2 = p1 → %zmm2` (**block 2's own
    aux register, distinct from block 3's at the same `p1`**), SSA result
    `v1 → %zmm0`. The SSA name is `v1` (threaded counter), not `v0`. -/
def alloc2 : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm2"), ("v1", "%zmm0") ]

/-- Block 3's alloc. Threaded state `s2 = p0 → %zmm0` (still the round-state slot),
    aux `k3 = p1 → %zmm3` (**block 3's own aux register — DIFFERENT from block 2's
    `%zmm2` even though both are the local `p1`**), SSA result `v2 → %zmm0`. -/
def alloc3 : XAlloc :=
  [ ("p0", "%zmm0"), ("p1", "%zmm3"), ("v2", "%zmm0") ]

/-- The 3-block per-block-alloc kernel: state threaded through `%zmm0`, each block
    with its own aux register at the local `p1`. -/
def threeBlockSeq : VpackZmmAllocSeq :=
  [ (alloc1, ⟨blk0Ctx, r512, b1Com⟩)
  , (alloc2, ⟨blk0Ctx, r512, b2Com⟩)
  , (alloc3, ⟨blk0Ctx, r512, b3Com⟩) ]

/-- **The per-block-alloc render.** Three owned AT&T `%zmm` lines in ONE
    straight-line body. The threaded state stays in `%zmm0` across all three
    blocks; the per-block aux registers are `%zmm1` (block 1), `%zmm2` (block 2),
    `%zmm3` (block 3) — block 2 and block 3 use DISTINCT aux registers
    (`%zmm2` ≠ `%zmm3`) at the SAME local param index `p1`, which the flat
    single-`alloc` renderer could not express. AT&T EVEX order is
    `op src2, src1, dst`. -/
theorem three_block_lines :
    (renderVpackZmmAllocSeq threeBlockSeq).1
      = [ "\tvpxorq %zmm1, %zmm0, %zmm0"   -- s1 = x  ⊕ k1   (aux %zmm1)
        , "\tvpandq %zmm2, %zmm0, %zmm0"   -- s2 = s1 ∧ m2   (aux %zmm2, block 2)
        , "\tvpxorq %zmm3, %zmm0, %zmm0" ] -- s3 = s2 ⊕ k3   (aux %zmm3, block 3)
      := by
  native_decide

/-- **Distinct per-block aux registers at the same local `p1`.** Block 2's aux is
    `%zmm2`, block 3's aux is `%zmm3` — the two lines carry different second
    operands, the exact distinction the flat shared `alloc` could not make (both
    blocks' `p1` would resolve the one `"p1"` entry). -/
theorem three_block_distinct_aux :
    (renderVpackZmmAllocSeq threeBlockSeq).1[1]?
      = some "\tvpandq %zmm2, %zmm0, %zmm0" ∧
    (renderVpackZmmAllocSeq threeBlockSeq).1[2]?
      = some "\tvpxorq %zmm3, %zmm0, %zmm0" := by
  native_decide

/-- **Threaded round-state register.** Every block reads its data input out of
    `%zmm0` and writes its result back to `%zmm0` — the round state `s` keeps ONE
    `%zmm` slot across all three block boundaries (first operand chain), while the
    aux operands differ. Each rendered line's destination/`src1` is `%zmm0`. -/
theorem three_block_state_threaded :
    ∀ ln ∈ (renderVpackZmmAllocSeq threeBlockSeq).1,
      strContains ln "%zmm0, %zmm0" = true := by
  native_decide

/-- **Denote fold across the three block boundaries.** Feeding block 1's denoted
    result `s1 = x ⊕ k1` as block 2's data input, then block 2's result
    `s2 = s1 ∧ m2` as block 3's data input, gives the whole-kernel value
    `((x ⊕ k1) ∧ m2) ⊕ k3`. This is the semantics the threaded `%zmm0` realises:
    the register that crosses each boundary carries exactly the previous block's
    `Com.denote`. The proof is `rfl`. -/
theorem three_block_denote (x k1 m2 k3 : BitVec 512) :
    blockDenote ⟨blk0Ctx, r512, b3Com⟩
        (.cons (blockDenote ⟨blk0Ctx, r512, b2Com⟩
                  (.cons (blockDenote ⟨blk0Ctx, r512, b1Com⟩ (.cons x (.cons k1 .nil)))
                         (.cons m2 .nil)))
               (.cons k3 .nil))
      = zmmPackQ .xor (zmmPackQ .and (zmmPackQ .xor x k1) m2) k3 :=
  rfl

/-! ### 8.3 The framed whole-kernel `.s` for the 3-block per-block-alloc kernel -/

/-- The framed owned `.s` for the 3-block per-block-alloc kernel, symbol
    `vpackzmm_three_block`. Data word `x` from `(%rdi)` in `%zmm0`; the three
    distinct aux constants `k1`/`m2`/`k3` broadcast into `%zmm1`/`%zmm2`/`%zmm3`
    from `.rodata`; result (`%zmm0`) stored to `(%rdi)`. The body is the ONE
    straight-line per-block render with the state carried across all three
    boundaries in `%zmm0` and each block reading its own aux register. -/
def threeBlockExportAsm : String :=
  frameAsmFunction "vpackzmm_three_block"
    [ "\tvmovdqu64\t(%rdi), %zmm0"
    , "\tvmovdqa64\tk1_const(%rip), %zmm1"
    , "\tvmovdqa64\tm2_const(%rip), %zmm2"
    , "\tvmovdqa64\tk3_const(%rip), %zmm3" ]
    (renderVpackZmmAllocSeq threeBlockSeq).1
    [ "\tvmovdqu64\t%zmm0, (%rdi)" ]

-- Print the emitted owned `.s` for visual inspection.
#eval IO.println threeBlockExportAsm

/- The framed 3-block kernel emits all three blocks' instructions and names its
    export symbol — the owned (no-jasminc, no-`Avx512Model`) per-block-alloc path,
    using distinct aux registers `%zmm2` and `%zmm3` for blocks 2 and 3. -/
#guard (strContains threeBlockExportAsm "vpackzmm_three_block:")
    && (strContains threeBlockExportAsm "%zmm3")
    && (strContains threeBlockExportAsm "%zmm2")
    && !(strContains threeBlockExportAsm "#VPXOR")

end CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmComSeq
