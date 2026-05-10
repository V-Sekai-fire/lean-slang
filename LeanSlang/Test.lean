import LeanSlang.Types
import LeanSlang.AST
import LeanSlang.Emit

open LeanSlang

/-! ## Reference fixtures pinned by `native_decide`

If the pretty-printer drifts, lake build fails on the fixture
mismatch. Adding new fixtures here is the cheapest regression test.
-/

/-- Tiny shader: empty compute kernel with one thread. -/
def trivialShader : SlangShaderModule :=
  { functions := [{
      attrs  := [.shaderCompute, .numthreads 1 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none⟩]
      body   := [.ret none]
    }] }

/-- Pinned reference text for `trivialShader`. Any change to
    `LeanSlang.Emit` that affects this output trips the test. -/
def trivialShaderExpected : String :=
"[shader(\"compute\")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}"

example : LeanSlang.emit trivialShader = trivialShaderExpected := by
  native_decide

/-- A slightly bigger fixture: one global RW buffer, kernel writes
    a literal at index 0. -/
def writeOneShader : SlangShaderModule :=
  { globals :=
      [⟨"buf", .rwBuf (.scalar .float), Semantic.none, some 0, some 0⟩]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 64 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none⟩]
      body   :=
        [ .assign (.index (.var "buf") (.member (.var "tid") "x")) (.litFloat 1.0)
        , .ret none
        ]
    }] }

def writeOneShaderExpected : String :=
"[[vk::binding(0, 0)]]
RWStructuredBuffer<float> buf;

[shader(\"compute\")] [numthreads(64, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  buf[tid.x] = 1.000000;
  return;
}"

example : LeanSlang.emit writeOneShader = writeOneShaderExpected := by
  native_decide

/-- Entry-point name accessor. -/
example : trivialShader.entryPointName = "main" := by native_decide
example : writeOneShader.entryPointName = "main" := by native_decide
