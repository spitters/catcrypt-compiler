set_option maxRecDepth 1000000

/-- `A_direct`'s recurrence on `Nat` with an explicit wrap, instead of
    `BitVec 64`.  Isolates what the `BitVec` wrapper costs the kernel. -/
def runN : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => runN n ((a + b) % 18446744073709551616) ((a ^^^ b) + 1)

theorem tN : decide (runN 3000 1 2 = 0) = false := rfl
