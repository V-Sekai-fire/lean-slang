# lean-slang

Lean 4 → [Slang](https://shader-slang.com) shader codegen.

A small Lean library that builds an in-memory Slang AST and pretty-
prints it to source text accepted by `slangc -target spirv`. Pure
Lean in this v0.0.x line; v0.1.x adds an `extern_lib` that
round-trips the emitted text through `libslang` to SPIR-V at lake
build time.

The Slang language reference is at
<https://github.com/shader-slang/spec> — extend the AST in
`LeanSlang/AST.lean` to cover features you need.

## Usage

```
require LeanSlang from git
  "https://github.com/V-Sekai-fire/lean-slang.git" @ "v0.0.1"
```

Then in Lean:

```lean
import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

open LeanSlang

def trivialShader : SlangShaderModule :=
  { functions := [{
      attrs  := [.shaderCompute, .numthreads 1 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none⟩]
      body   := [.ret none]
    }] }

#eval IO.println (LeanSlang.emit trivialShader)
```

emits

```
[shader("compute")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}
```

## Layout

- `LeanSlang/Types.lean` — `Scalar`, `SlangType`, `Semantic`,
  `SlangBinding`. Pure data; small Slang subset.
- `LeanSlang/AST.lean` — `SlangExpr`, `SlangStmt`,
  `SlangFunctionDecl`, `SlangShaderModule`. Smart constructors
  alongside.
- `LeanSlang/Emit.lean` — `emit : SlangShaderModule → String`
  pretty-printer.
- `LeanSlang/Test.lean` — pinned reference fixtures, asserted via
  `native_decide`. Drift in the pretty-printer trips here.

## Roadmap

- v0.0.1 — pure-Lean AST + emitter, native_decide fixtures green.
- v0.1.x — FFI to `libslang-compiler` (compile emitted Slang to
  SPIR-V at lake build time, magic-byte / size-floor assertions).
- v0.2.x — coverage for the DDM matvec compute kernel needed by
  [V-Sekai-fire/TOOL_godot_curvenet](https://github.com/V-Sekai-fire/TOOL_godot_curvenet).
- v0.3.x — extend AST to a useful subset of the
  [Slang spec](https://github.com/shader-slang/spec).

## License

MIT.
