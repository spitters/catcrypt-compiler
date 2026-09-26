module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit

@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit (bbAdd bbSub bbMul bbPow bbRootOfUnity bbGen)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit (bbInv)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit (Digest digestBytes merkleHashFieldElem merkleBuildRoot)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit (fibTrace FIB_WIDTH)
def bitReverse (i logN : ℕ) : ℕ := (List.range logN).foldl (fun (st : ℕ × ℕ) _ => (st.1 * 2 + st.2 % 2, st.2 / 2)) (0, i) |>.1
def bitReversePermute (vals : List (BitVec 64)) (logN : ℕ) : List (BitVec 64) := (List.range vals.length).map (fun i => vals.getD (bitReverse i logN) 0)
def nttLayer (vals : List (BitVec 64)) (omega : BitVec 64) (n layer : ℕ) : List (BitVec 64) :=
  let size := 2 ^ (layer + 1); let half := size / 2; let wSize := bbPow omega (BitVec.ofNat 64 (n / size))
  (List.range n).map (fun idx => let block := (idx / size) * size; let off := idx % size
    if off < half then let wPow := bbPow wSize (BitVec.ofNat 64 off)
      bbAdd (vals.getD (block + off) 0) (bbMul wPow (vals.getD (block + off + half) 0))
    else let j := off - half; let wPow := bbPow wSize (BitVec.ofNat 64 j)
      bbSub (vals.getD (block + j) 0) (bbMul wPow (vals.getD (block + j + half) 0)))
def bbNtt (vals : List (BitVec 64)) (omega : BitVec 64) : List (BitVec 64) :=
  let n := vals.length
  if n ≤ 1 then vals else (List.range (Nat.log2 n)).foldl (fun acc layer => nttLayer acc omega n layer) (bitReversePermute vals (Nat.log2 n))
def bbIntt (vals : List (BitVec 64)) (omega : BitVec 64) : List (BitVec 64) :=
  let n := vals.length
  if n ≤ 1 then vals else (bbNtt vals (bbInv omega)).map (fun v => bbMul v (bbInv (BitVec.ofNat 64 n)))
def traceColumn (trace : List (BitVec 64 × BitVec 64)) (col : ℕ) : List (BitVec 64) := trace.map (fun r => if col = 0 then r.1 else r.2)
def cosetTwist (coeffs : List (BitVec 64)) (shift : BitVec 64) : List (BitVec 64) := (coeffs.zipIdx).map (fun (c, i) => bbMul c (bbPow shift (BitVec.ofNat 64 i)))
def computeColumnLde (colEvals : List (BitVec 64)) (traceLog2 domainLog2 : ℕ) (shift : BitVec 64) : List (BitVec 64) :=
  let h := 2 ^ traceLog2; let n := 2 ^ domainLog2
  bbNtt (cosetTwist ((bbIntt (colEvals.take h) (bbRootOfUnity traceLog2)) ++ List.replicate (n - h) (0 : BitVec 64)) shift) (bbRootOfUnity domainLog2)
def computeTraceLde (trace : List (BitVec 64 × BitVec 64)) (traceLog2 domainLog2 : ℕ) (shift : BitVec 64) : List (BitVec 64) :=
  let n := 2 ^ domainLog2; let col0 := computeColumnLde (traceColumn trace 0) traceLog2 domainLog2 shift; let col1 := computeColumnLde (traceColumn trace 1) traceLog2 domainLog2 shift
  (List.range n).flatMap (fun i => [col0.getD i 0, col1.getD i 0])
-- n=8 domain: trace height 4 (traceLog2=2), domainLog2=3
#eval (computeTraceLde (fibTrace 4) 2 3 bbGen).length
theorem t : (computeTraceLde (fibTrace 4) 2 3 bbGen).length = 16 := by native_decide
