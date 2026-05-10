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
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
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
      [⟨"buf", .rwBuf (.scalar .float), Semantic.none, some 0, some 0, .qIn⟩]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 64 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
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

/-- Fixture exercising struct decls + ConstantBuffer global. -/
def structAndCBufferShader : SlangShaderModule :=
  { structs :=
      [ { name := "Params"
        , fields :=
            [ { name := "n",     type := .scalar .uint,  semantic := Semantic.none }
            , { name := "alpha", type := .scalar .float, semantic := Semantic.none } ] } ]
  , globals :=
      [ ⟨"gParams", .const "Params", Semantic.none, some 0, some 0, .qIn⟩ ]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 256 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   := [.ret none]
    }] }

def structAndCBufferShaderExpected : String :=
"struct Params {
  uint n;
  float alpha;
};

[[vk::binding(0, 0)]]
ConstantBuffer<Params> gParams;

[shader(\"compute\")] [numthreads(256, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}"

example :
    LeanSlang.emit structAndCBufferShader = structAndCBufferShaderExpected := by
  native_decide

/-- Fixture: a 256-thread reduce-style kernel with a groupshared scratch
    array and a barrier call. -/
def groupSharedShader : SlangShaderModule :=
  { groupShared :=
      [ { name := "scratch", elemType := .scalar .float, arraySize := some 256 } ]
  , functions := [{
      attrs  := [.shaderCompute, .numthreads 256 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   :=
        [ .assign (.index (.var "scratch") (.member (.var "tid") "x"))
                  (.litFloat 0.0)
        , .expr (.call "GroupMemoryBarrierWithGroupSync" [])
        , .ret none ]
    }] }

def groupSharedShaderExpected : String :=
"groupshared float scratch[256];

[shader(\"compute\")] [numthreads(256, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  scratch[tid.x] = 0.000000;
  GroupMemoryBarrierWithGroupSync();
  return;
}"

example :
    LeanSlang.emit groupSharedShader = groupSharedShaderExpected := by
  native_decide

/-- Fixture: a helper function `mul2` plus an entry point. Verifies
    multiple `SlangFunctionDecl`s in one module emit in order, and
    that `entryPoint` correctly picks the one with shaderCompute. -/
def helperFnShader : SlangShaderModule :=
  { functions :=
      [ { attrs   := []
        , retType := .scalar .float
        , name    := "mul2"
        , params  :=
            [ ⟨"a", .scalar .float, Semantic.none, none, none, .qIn⟩
            , ⟨"b", .scalar .float, Semantic.none, none, none, .qIn⟩ ]
        , body    := [.retExpr (.bin "*" (.var "a") (.var "b"))] }
      , { attrs  := [.shaderCompute, .numthreads 1 1 1]
        , name   := "main"
        , params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
        , body   := [.ret none] } ] }

def helperFnShaderExpected : String :=
"float mul2(float a, float b) {
  return (a * b);
}

[shader(\"compute\")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}"

example :
    LeanSlang.emit helperFnShader = helperFnShaderExpected := by
  native_decide

example : helperFnShader.entryPointName = "main" := by native_decide

/-- Fixture: helper function with `out` parameters. Models the
    `two_sum(a, b, out hi, out lo)` Knuth EFT primitive used by
    dot_reduce.comp. -/
def outParamShader : SlangShaderModule :=
  { functions :=
      [ { attrs   := []
        , retType := .named "void"
        , name    := "two_sum"
        , params  :=
            [ ⟨"a",  .scalar .float, Semantic.none, none, none, .qIn⟩
            , ⟨"b",  .scalar .float, Semantic.none, none, none, .qIn⟩
            , ⟨"hi", .scalar .float, Semantic.none, none, none, .qOut⟩
            , ⟨"lo", .scalar .float, Semantic.none, none, none, .qOut⟩ ]
        , body    :=
            [ .assign (.var "hi") (.bin "+" (.var "a") (.var "b"))
            , .assign (.var "lo") (.litFloat 0.0)
            , .ret none ] }
      , { attrs  := [.shaderCompute, .numthreads 1 1 1]
        , name   := "main"
        , params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
        , body   := [.ret none] } ] }

def outParamShaderExpected : String :=
"void two_sum(float a, float b, out float hi, out float lo) {
  hi = (a + b);
  lo = 0.000000;
  return;
}

[shader(\"compute\")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}"

example :
    LeanSlang.emit outParamShader = outParamShaderExpected := by
  native_decide

/-- Fixture: function with `precise` local declarations (Knuth two_sum). -/
def preciseShader : SlangShaderModule :=
  { functions :=
      [ { attrs   := []
        , retType := .scalar .float
        , name    := "two_sum_hi"
        , params  :=
            [ ⟨"a", .scalar .float, Semantic.none, none, none, .qIn⟩
            , ⟨"b", .scalar .float, Semantic.none, none, none, .qIn⟩ ]
        , body    :=
            [ .declPreciseInit (.scalar .float) "h"
                (.bin "+" (.var "a") (.var "b"))
            , .retExpr (.var "h") ] }
      , { attrs  := [.shaderCompute, .numthreads 1 1 1]
        , name   := "main"
        , params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
        , body   := [.ret none] } ] }

def preciseShaderExpected : String :=
"float two_sum_hi(float a, float b) {
  precise float h = (a + b);
  return h;
}

[shader(\"compute\")] [numthreads(1, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  return;
}"

example :
    LeanSlang.emit preciseShader = preciseShaderExpected := by
  native_decide

/-- Fixture: tree reduce-style while loop with bit-shift step
    (mirrors `for (step = 128; step > 0; step >>= 1)` from
    dot_reduce.comp's intra-workgroup reduction). -/
def whileLoopShader : SlangShaderModule :=
  { functions := [{
      attrs  := [.shaderCompute, .numthreads 256 1 1]
      name   := "main"
      params := [⟨"tid", .vec .uint 3, .svDispatchThreadId, none, none, .qIn⟩]
      body   :=
        [ .declInit (.scalar .uint) "step" (.litUint 128)
        , .whileLoop (.bin ">" (.var "step") (.litUint 0))
            [ .assign (.var "step") (.bin ">>" (.var "step") (.litUint 1)) ]
        , .ret none ] }] }

def whileLoopShaderExpected : String :=
"[shader(\"compute\")] [numthreads(256, 1, 1)]
void main(uint3 tid : SV_DispatchThreadID) {
  uint step = 128u;
  while ((step > 0u)) {
    step = (step >> 1u);
  }
  return;
}"

example :
    LeanSlang.emit whileLoopShader = whileLoopShaderExpected := by
  native_decide
