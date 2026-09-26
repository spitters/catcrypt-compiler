module

public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit


@[expose] public section
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3LdeEmit (bbRootOfUnity bbPow)
open CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FriEmit (bbInv)

-- reference: bb_root_of_unity(3) primitive 8th root; bb_root_of_unity(8)=1732600167
theorem t1 : bbRootOfUnity 8 = 1732600167 := by native_decide
theorem t2 : (bbPow (bbRootOfUnity 3) 8) = 1 := by native_decide
theorem t3 : bbInv 7 = 862828252 := by native_decide
