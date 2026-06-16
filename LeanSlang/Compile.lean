import LeanSlang.AST
import LeanSlang.Emit

/-! # `LeanSlang.Compile` — in-process Slang → SPIR-V via `libslang` (FFI)

Replaces any notion of shelling out to the `slangc` CLI: the emitted Slang text
is compiled to SPIR-V *in-process* through `libslang`'s modern API (a small
C++ shim, `ffi/slang_shim.cpp`, bound via `@[extern]`). `spirvSize` returns the
SPIR-V byte size for the given compute entry point, or a negative error code —
so `m` round-trips AST → text → real SPIR-V, end to end. -/

namespace LeanSlang

/-- Compile a Slang source string for compute `entry` to SPIR-V; returns the
SPIR-V byte size, or a negative code on failure. Backed by `libslang`. -/
@[extern "leanslang_spirv_size"]
opaque slangSpirvSize (src entry : String) : Int64

/-- Emit `m` and compile its entry point to SPIR-V; returns the SPIR-V size. -/
def spirvSize (m : SlangShaderModule) : Int64 :=
  slangSpirvSize (emit m) m.entryPointName

/-- The module compiles to a non-empty SPIR-V blob. -/
def compiles (m : SlangShaderModule) : Bool := spirvSize m > 0

end LeanSlang
