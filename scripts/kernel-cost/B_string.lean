set_option maxRecDepth 1000000

abbrev W := BitVec 64

/-- A register file keyed by `String`, as `RState64` and `JState` are. -/
structure SB where
  regs : String → W

def SB.get (s : SB) (r : String) : W := s.regs r

def SB.set (s : SB) (r : String) (v : W) : SB :=
  ⟨fun r' => if r' = r then v else s.regs r'⟩

inductive IB where
  | add (d a b : String)
  | xor (d a b : String)
  | addi (d a : String) (i : Nat)
  | mov (d a : String)

def evalB (s : SB) : IB → SB
  | .add d a b => s.set d (s.get a + s.get b)
  | .xor d a b => s.set d (s.get a ^^^ s.get b)
  | .addi d a i => s.set d (s.get a + BitVec.ofNat 64 i)
  | .mov d a => s.set d (s.get a)

def runB (s : SB) : List IB → SB
  | [] => s
  | i :: is => runB (evalB s i) is

def bodyB : List IB :=
  [.add "t" "a" "b", .xor "b" "a" "b", .addi "b" "b" 1, .mov "a" "t"]

def loopB : Nat → SB → SB
  | 0, s => s
  | n + 1, s => loopB n (runB s bodyB)

def s0B : SB := ⟨fun r => if r = "a" then 1 else 2⟩

theorem tB : decide ((loopB 3000 s0B).get "a" = 0) = false := rfl
