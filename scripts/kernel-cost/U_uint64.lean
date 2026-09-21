set_option maxRecDepth 1000000

/-- `A_direct`'s recurrence on `UInt64` rather than `BitVec 64`: does the
    kernel have a faster path for the machine-word type? -/
def runU : Nat → UInt64 → UInt64 → UInt64
  | 0, a, _ => a
  | n + 1, a, b => runU n (a + b) ((a ^^^ b) + 1)

theorem tU : decide (runU 3000 1 2 = 0) = false := rfl
