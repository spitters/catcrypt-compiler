set_option maxRecDepth 1000000

abbrev W := BitVec 64

/-- `B_string` with sixteen live registers instead of three: the working-set
    size a real kernel (SHA-256 message schedule, a field multiplication)
    has.  Tests how the closure-chain register file scales with live state. -/
structure SB where
  regs : String → W

def SB.get (s : SB) (r : String) : W := s.regs r

def SB.set (s : SB) (r : String) (v : W) : SB :=
  ⟨fun r' => if r' = r then v else s.regs r'⟩

inductive IB where
  | add (d a b : String)
  | xor (d a b : String)

def evalB (s : SB) : IB → SB
  | .add d a b => s.set d (s.get a + s.get b)
  | .xor d a b => s.set d (s.get a ^^^ s.get b)

def runB (s : SB) : List IB → SB
  | [] => s
  | i :: is => runB (evalB s i) is

/-- Sixteen registers `r0 … r15`, each written once per body, each reading two
    others.  Reading `r0` after the body has written `r15` walks fifteen frames
    of the closure. -/
def bodyB : List IB :=
  [ .add "r0" "r0" "r1", .xor "r1" "r1" "r2", .add "r2" "r2" "r3", .xor "r3" "r3" "r4"
  , .add "r4" "r4" "r5", .xor "r5" "r5" "r6", .add "r6" "r6" "r7", .xor "r7" "r7" "r8"
  , .add "r8" "r8" "r9", .xor "r9" "r9" "r10", .add "r10" "r10" "r11", .xor "r11" "r11" "r12"
  , .add "r12" "r12" "r13", .xor "r13" "r13" "r14", .add "r14" "r14" "r15", .xor "r15" "r15" "r0" ]

def loopB : Nat → SB → SB
  | 0, s => s
  | n + 1, s => loopB n (runB s bodyB)

def s0B : SB := ⟨fun r => if r = "r0" then 1 else 2⟩

theorem tE : decide ((loopB 750 s0B).get "r0" = 0) = false := rfl
