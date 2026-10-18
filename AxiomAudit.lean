import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
import CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
import CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine
import CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo

#print axioms CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline.robustCompilation_source_to_x86
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine.compile_correct_all_genuine
-- The concrete machine-execution headline: runs `x86Target.compile`/`runOps` on the
-- emitted ops and proves the result register equals `Com.denote`, over the
-- straight-line all-`reg 64` fragment.
#print axioms CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo.com_x86_e2e
