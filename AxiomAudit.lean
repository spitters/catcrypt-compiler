import CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
import CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline
import CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine
import CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo
import CatCrypt.Crypto.SecureCompilation.Haxc.RCInstance

#print axioms CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted.rustToJasminCom_endToEnd
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.RobustCompilationPipeline.robustCompilation_source_to_x86
#print axioms CatCrypt.Crypto.SecureCompilation.VIR.CompileCorrectAllGenuine.compile_correct_all_genuine
-- The concrete machine-execution headline: runs `x86Target.compile`/`runOps` on the
-- emitted ops and proves the result register equals `Com.denote`, over the
-- straight-line all-`reg 64` fragment.
#print axioms CatCrypt.Crypto.SecureCompilation.ScalarLinX86Demo.com_x86_e2e
-- The hax compiler `haxc`: correctness, constant time, the gate, robust compilation.
#print axioms CatCrypt.Crypto.SecureCompilation.Haxc.haxc_correct_auto
#print axioms CatCrypt.Crypto.SecureCompilation.Haxc.haxc_ct_proved_all
#print axioms CatCrypt.Crypto.SecureCompilation.Haxc.haxc_ct_proved_all_of_check
#print axioms CatCrypt.Crypto.SecureCompilation.Haxc.haxc_gate_proved_all
#print axioms CatCrypt.Crypto.SecureCompilation.Haxc.haxc_rc_proved_all
