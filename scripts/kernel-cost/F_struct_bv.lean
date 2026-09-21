set_option maxRecDepth 1000000

abbrev W := BitVec 64

/-- The same 16-register machine as `E_wide`, with the register file as a
    flat 16-field structure instead of a `String → W` closure.  A write
    rebuilds one constructor application whose other fields reduce to the
    literals already there, so nothing accumulates. -/
structure RF where
  r0 : W; r1 : W; r2 : W; r3 : W; r4 : W; r5 : W; r6 : W; r7 : W
  r8 : W; r9 : W; r10 : W; r11 : W; r12 : W; r13 : W; r14 : W; r15 : W

def RF.get (s : RF) : Nat → W
  | 0 => s.r0 | 1 => s.r1 | 2 => s.r2 | 3 => s.r3
  | 4 => s.r4 | 5 => s.r5 | 6 => s.r6 | 7 => s.r7
  | 8 => s.r8 | 9 => s.r9 | 10 => s.r10 | 11 => s.r11
  | 12 => s.r12 | 13 => s.r13 | 14 => s.r14 | _ => s.r15

def RF.set (s : RF) (i : Nat) (v : W) : RF :=
  match i with
  | 0 => { s with r0 := v } | 1 => { s with r1 := v }
  | 2 => { s with r2 := v } | 3 => { s with r3 := v }
  | 4 => { s with r4 := v } | 5 => { s with r5 := v }
  | 6 => { s with r6 := v } | 7 => { s with r7 := v }
  | 8 => { s with r8 := v } | 9 => { s with r9 := v }
  | 10 => { s with r10 := v } | 11 => { s with r11 := v }
  | 12 => { s with r12 := v } | 13 => { s with r13 := v }
  | 14 => { s with r14 := v } | _ => { s with r15 := v }

inductive IF where
  | add (d a b : Nat)
  | xor (d a b : Nat)

def evalF (s : RF) : IF → RF
  | .add d a b => s.set d (s.get a + s.get b)
  | .xor d a b => s.set d (s.get a ^^^ s.get b)

def runF (s : RF) : List IF → RF
  | [] => s
  | i :: is => runF (evalF s i) is

def bodyF : List IF :=
  [ .add 0 0 1, .xor 1 1 2, .add 2 2 3, .xor 3 3 4
  , .add 4 4 5, .xor 5 5 6, .add 6 6 7, .xor 7 7 8
  , .add 8 8 9, .xor 9 9 10, .add 10 10 11, .xor 11 11 12
  , .add 12 12 13, .xor 13 13 14, .add 14 14 15, .xor 15 15 0 ]

def loopF : Nat → RF → RF
  | 0, s => s
  | n + 1, s => loopF n (runF s bodyF)

def s0F : RF := ⟨1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2⟩

theorem tF : decide ((loopF 750 s0F).get 0 = 0) = false := rfl
