import LeanSlang
open LeanSlang

/-- End-to-end: emit lean-slang fixtures and compile each to SPIR-V via libslang
(in-process FFI, no `slangc` CLI). -/
def check (name : String) (m : SlangShaderModule) : IO Unit := do
  let n := spirvSize m
  if n ≤ 0 then throw (IO.userError s!"{name}: slang compile failed (code {n})")
  IO.println s!"  {name} → {n} bytes SPIR-V"

def main : IO Unit := do
  IO.println "lean-slang → SPIR-V (in-process via libslang):"
  check "trivialShader" trivialShader
  check "writeOneShader" writeOneShader
  check "whileLoopShader" whileLoopShader
  IO.println "OK: all fixtures compiled to SPIR-V end-to-end."
