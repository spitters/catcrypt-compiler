module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit


@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
  (bbAdd bbSub bbMul bbPow bbRootOfUnity)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit (bbInv)

def bitReverse (i logN : ℕ) : ℕ :=
  (List.range logN).foldl (fun (st : ℕ × ℕ) _ => (st.1 * 2 + st.2 % 2, st.2 / 2)) (0, i) |>.1
def bitReversePermute (vals : List (BitVec 64)) (logN : ℕ) : List (BitVec 64) :=
  (List.range vals.length).map (fun i => vals.getD (bitReverse i logN) 0)
def nttLayer (vals : List (BitVec 64)) (omega : BitVec 64) (n layer : ℕ) : List (BitVec 64) :=
  let size := 2 ^ (layer + 1); let half := size / 2
  let wSize := bbPow omega (BitVec.ofNat 64 (n / size))
  (List.range n).map (fun idx =>
    let block := (idx / size) * size; let off := idx % size
    if off < half then
      let wPow := bbPow wSize (BitVec.ofNat 64 off)
      bbAdd (vals.getD (block + off) 0) (bbMul wPow (vals.getD (block + off + half) 0))
    else
      let j := off - half
      let wPow := bbPow wSize (BitVec.ofNat 64 j)
      bbSub (vals.getD (block + j) 0) (bbMul wPow (vals.getD (block + j + half) 0)))
def bbNtt (vals : List (BitVec 64)) (omega : BitVec 64) : List (BitVec 64) :=
  let n := vals.length
  if n ≤ 1 then vals else
    (List.range (Nat.log2 n)).foldl (fun acc layer => nttLayer acc omega n layer)
      (bitReversePermute vals (Nat.log2 n))

-- reference test_ntt_constant_polynomial: ntt([42,0,0,0], root4) = [42,42,42,42]
theorem ntt_const : bbNtt [42, 0, 0, 0] (bbRootOfUnity 2) = [42, 42, 42, 42] := by
  native_decide
-- reference test_ntt_dirac_at_zero: ntt([1,0,...,0], root8) = [1;8]
theorem ntt_dirac : bbNtt [1,0,0,0,0,0,0,0] (bbRootOfUnity 3) = [1,1,1,1,1,1,1,1] := by
  native_decide

-- n=32 forward NTT of a dirac: ntt([1,0,...]) over 32 = all-ones
theorem ntt32_dirac :
    bbNtt (1 :: List.replicate 31 (0:BitVec 64)) (bbRootOfUnity 5)
      = List.replicate 32 (1:BitVec 64) := by native_decide

-- Now the full commitment pipeline reusing the compiled bbNtt above.
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3MerkleEmit
  (Digest digestBytes merkleHashFieldElem merkleBuildRoot)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit (bbGen)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3AirEmit (fibTrace FIB_WIDTH)

def bbIntt (vals : List (BitVec 64)) (omega : BitVec 64) : List (BitVec 64) :=
  let n := vals.length
  if n ≤ 1 then vals else
    (bbNtt vals (bbInv omega)).map (fun v => bbMul v (bbInv (BitVec.ofNat 64 n)))
def traceColumn (trace : List (BitVec 64 × BitVec 64)) (col : ℕ) : List (BitVec 64) :=
  trace.map (fun r => if col = 0 then r.1 else r.2)
def cosetTwist (coeffs : List (BitVec 64)) (shift : BitVec 64) : List (BitVec 64) :=
  (coeffs.zipIdx).map (fun (c, i) => bbMul c (bbPow shift (BitVec.ofNat 64 i)))
def computeColumnLde (colEvals : List (BitVec 64)) (traceLog2 domainLog2 : ℕ) (shift : BitVec 64) : List (BitVec 64) :=
  let h := 2 ^ traceLog2; let n := 2 ^ domainLog2
  let coeffsH := bbIntt (colEvals.take h) (bbRootOfUnity traceLog2)
  let coeffsN := coeffsH ++ List.replicate (n - h) (0 : BitVec 64)
  bbNtt (cosetTwist coeffsN shift) (bbRootOfUnity domainLog2)
def computeTraceLde (trace : List (BitVec 64 × BitVec 64)) (traceLog2 domainLog2 : ℕ) (shift : BitVec 64) : List (BitVec 64) :=
  let n := 2 ^ domainLog2
  let col0 := computeColumnLde (traceColumn trace 0) traceLog2 domainLog2 shift
  let col1 := computeColumnLde (traceColumn trace 1) traceLog2 domainLog2 shift
  (List.range n).flatMap (fun i => [col0.getD i 0, col1.getD i 0])
def commitTraceLde (lde : List (BitVec 64)) (width domainLog2 : ℕ) : Digest :=
  merkleBuildRoot domainLog2 (fun i =>
    merkleHashFieldElem ((List.range width).foldl
      (fun acc col => bbAdd (bbMul acc 31) (lde.getD (i.val * width + col) 0)) (0 : BitVec 64)))
def fibTraceCommitment (height traceLog2 : ℕ) : Digest :=
  commitTraceLde (computeTraceLde (fibTrace height) traceLog2 5 bbGen) FIB_WIDTH 5

theorem probe_h8 :
    digestBytes (fibTraceCommitment 8 3) =
      [0x00,0xfa,0xf6,0x42,0x86,0x60,0x28,0xe8,0x30,0xca,0x7e,0xea,0x66,0x30,0xa0,0xb0,
       0xc0,0x5a,0x86,0xd2,0xe6,0x60,0x38,0xf8,0xd0,0x2a,0x0b,0x3b,0x3a,0x14,0x79,0x3d] := by
  native_decide
