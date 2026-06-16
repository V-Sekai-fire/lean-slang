import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit
import LeanSlang.Compile
import LeanSlang.SIMT
import LeanSlang.Semantics
import LeanSlang.Test

/-!
# `LeanSlang` — Lean 4 → Slang shader codegen

A small Lean library that builds an in-memory Slang AST and pretty-
prints it to source text accepted by `slangc -target spirv`. Pure
Lean; no FFI in this v0.0.x line. The follow-up v0.1.x adds an
extern_lib that round-trips the emitted text through `libslang` to
SPIR-V at lake build time.

## Usage

```
import LeanSlang
open LeanSlang

def trivialShader : SlangShaderModule :=
  { functions := [{
      attrs := [.shaderCompute, .numthreads 1 1 1]
      name  := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none⟩]
      body := [.ret none]
    }] }

#eval IO.println (LeanSlang.emit trivialShader)
```

Yields a Slang source equivalent to:

```
[shader("compute")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}
```

## License

MIT.
-/
