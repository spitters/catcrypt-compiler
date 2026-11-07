/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# A parallel list map

`parMap f l` cuts `l` into chunks of `32` elements (`chunks`), spawns one task
`Task.spawn fun _ => c.map f` per chunk `c` and then reads the tasks back in order with
`Task.get`. In compiled code the chunks are mapped on the task thread pool; in the logic
`Task.get (Task.spawn g) = g ()` holds by definition, so the value is the sequential map.

## Main results

* `flatten_chunks` — the chunks of `l` concatenate to `l`.
* `parMap_eq_map` — `parMap f l = l.map f`.
-/

@[expose] public section

namespace CatCrypt.Quantum.Synthesis

universe u v

variable {α : Type u} {β : Type v}

/-- The consecutive chunks of `l` of length `k + 1`, the last one possibly shorter. -/
def chunks (k : Nat) (l : List α) : List (List α) :=
  if h : l = [] then [] else l.take (k + 1) :: chunks k (l.drop (k + 1))
termination_by l.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < l.length := List.length_pos_iff.mpr h
  omega

/-- The chunks of `l` concatenate to `l`. -/
theorem flatten_chunks (k : Nat) (l : List α) : (chunks k l).flatten = l := by
  fun_induction chunks k l <;> simp_all

/-- The list map with one task per chunk of `32` elements: every task is spawned before the
first is read back, so the chunks are mapped concurrently in compiled code. -/
def parMap (f : α → β) (l : List α) : List β :=
  ((chunks 31 l).map fun c => Task.spawn fun _ => c.map f).flatMap Task.get

/-- The parallel map is the list map. -/
@[simp] theorem parMap_eq_map (f : α → β) (l : List α) : parMap f l = l.map f := by
  have h : ((chunks 31 l).map fun c => Task.spawn fun _ => c.map f).flatMap Task.get =
      ((chunks 31 l).map (List.map f)).flatten := by
    simp only [List.flatMap_map]
    rfl
  rw [parMap, h, ← List.map_flatten, flatten_chunks]

end CatCrypt.Quantum.Synthesis
