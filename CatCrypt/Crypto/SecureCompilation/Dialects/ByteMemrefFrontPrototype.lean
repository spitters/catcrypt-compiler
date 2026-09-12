/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# (retired stub) Byte-cell dynamic-memref front

The byte-cell dynamic-index memref front already exists and is validated
end-to-end. See instead:

* `Dialects/ByteMemrefFrontValidate.lean` — `uint8_t out[N]` byte buffer,
  runtime index, `movb`-granular store + read-back load (width-parametric
  machinery, no new op constructor).
* `Dialects/MemrefArrayFrontValidate.lean` — `RArrLoad`/`RArrStore` →
  `translateDialectControl` `arrLoadCont`/`arrStoreCont` →
  `memrefGetDyn`/`memrefSetDyn` → real `stackLoad`/`LOADIDX`.
* `Dialects/TranslateDialectRuntimeLoop.lean` +
  `NestedRuntimeLoopFrontValidate.lean` — the runtime-`n` loop front.

This file intentionally carries no content beyond this pointer.
-/

@[expose] public section
