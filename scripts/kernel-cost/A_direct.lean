set_option maxRecDepth 1000000

abbrev W := BitVec 64

/-- Direct Lean recursion on `BitVec 64`: the shape a plain `Submission.impl`
    would have.  Three arithmetic operations per iteration, no duplicated
    subterm. -/
def runA : Nat → W → W → W
  | 0, a, _ => a
  | n + 1, a, b => runA n (a + b) ((a ^^^ b) + 1)

theorem tA : decide (runA 3000 1 2 = 0) = false := rfl
