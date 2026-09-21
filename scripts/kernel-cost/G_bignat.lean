set_option maxRecDepth 1000000

/-- 3000 additions on unbounded `Nat`s (Fibonacci), each one a single GMP call
    in the kernel.  The same computation as machine code would need a
    multi-limb add loop per step. -/
def fib : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => fib n b (a + b)

theorem tG : decide (fib 3000 0 1 = 0) = false := rfl
