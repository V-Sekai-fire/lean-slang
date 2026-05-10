import LeanSlang.AST

/-!
# `LeanSlang.Emit` — pretty-printer to Slang source text.

Pure-Lean string builder. Output is intended to be syntactically
valid Slang accepted by `slangc -target spirv`. Layout choices
(indentation, semicolons, attribute order) are pinned by the
native_decide reference fixtures.
-/

namespace LeanSlang

/-! ## Scalar / SlangType / Semantic / SlangBinding -/

def emitScalar : Scalar → String
  | .float => "float"
  | .uint  => "uint"
  | .int   => "int"
  | .bool  => "bool"

partial def emitSlangType : SlangType → String
  | .scalar s    => emitScalar s
  | .vec s n     => emitScalar s ++ toString n
  | .mat s r c   => emitScalar s ++ toString r ++ "x" ++ toString c
  | .rwBuf t     => "RWStructuredBuffer<" ++ emitSlangType t ++ ">"
  | .roBuf t     =>   "StructuredBuffer<" ++ emitSlangType t ++ ">"
  | .const sName => "ConstantBuffer<" ++ sName ++ ">"
  | .named n     => n

def emitSemantic : Semantic → String
  | .svDispatchThreadId => "SV_DispatchThreadID"
  | .svGroupThreadId    => "SV_GroupThreadID"
  | .svGroupId          => "SV_GroupID"
  | .none               => ""

/-- Emit a function-parameter binding. -/
def emitParamBinding (b : SlangBinding) : String :=
  let qual := match b.qualifier with
    | .qIn    => ""
    | .qOut   => "out "
    | .qInOut => "inout "
  let core := qual ++ emitSlangType b.type ++ " " ++ b.name
  match b.semantic with
  | .none => core
  | s     => core ++ " : " ++ emitSemantic s

/-- Emit a top-level / global binding. Adds the
    `[[vk::binding(b, space)]]` attribute when `binding` is set. -/
def emitGlobalBinding (b : SlangBinding) : String :=
  let attr :=
    match b.binding with
    | none   => ""
    | some i =>
        let space := b.space.getD 0
        "[[vk::binding(" ++ toString i ++ ", " ++ toString space ++ ")]]\n"
  attr ++ emitSlangType b.type ++ " " ++ b.name ++ ";"

/-! ## Expressions -/

partial def emitExpr : SlangExpr → String
  | .litFloat v        =>
      let s := toString v
      if s.contains '.' || s.contains 'e' || s.contains 'E' then s
      else s ++ ".0"
  | .litUint v         => toString v ++ "u"
  | .litBool true      => "true"
  | .litBool false     => "false"
  | .var name          => name
  | .index buf idx     => emitExpr buf ++ "[" ++ emitExpr idx ++ "]"
  | .member recv field => emitExpr recv ++ "." ++ field
  | .bin op l r        => "(" ++ emitExpr l ++ " " ++ op ++ " " ++ emitExpr r ++ ")"
  | .un op e           => "(" ++ op ++ emitExpr e ++ ")"
  | .call fn args      =>
      let argsStr := String.intercalate ", " (args.map emitExpr)
      fn ++ "(" ++ argsStr ++ ")"

/-! ## Statements -/

private def indent (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

private def openBrace : String := "{"
private def closeBrace : String := "}"

partial def emitStmt : Nat → SlangStmt → String
  | depth, .declare ty name init =>
      let lhs := indent depth ++ emitSlangType ty ++ " " ++ name
      match init with
      | some e => lhs ++ " = " ++ emitExpr e ++ ";"
      | none   => lhs ++ ";"
  | depth, .declarePrecise ty name init =>
      let lhs := indent depth ++ "precise " ++ emitSlangType ty ++ " " ++ name
      match init with
      | some e => lhs ++ " = " ++ emitExpr e ++ ";"
      | none   => lhs ++ ";"
  | depth, .assign lhs rhs =>
      indent depth ++ emitExpr lhs ++ " = " ++ emitExpr rhs ++ ";"
  | depth, .expr e =>
      indent depth ++ emitExpr e ++ ";"
  | depth, .ret none =>
      indent depth ++ "return;"
  | depth, .ret (some e) =>
      indent depth ++ "return " ++ emitExpr e ++ ";"
  | depth, .ifThen cond thenS elseS =>
      let head := indent depth ++ "if (" ++ emitExpr cond ++ ") " ++ openBrace
      let thenBody := String.intercalate "\n" (thenS.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      let elseBlock :=
        if elseS.isEmpty then ""
        else
          let elseBody := String.intercalate "\n" (elseS.map (emitStmt (depth + 1)))
          " else " ++ openBrace ++ "\n" ++ elseBody ++ "\n" ++ close
      head ++ "\n" ++ thenBody ++ "\n" ++ close ++ elseBlock
  | depth, .forCount name initE boundE body =>
      let head :=
        indent depth ++ "for (uint " ++ name ++ " = " ++ emitExpr initE
        ++ "; " ++ name ++ " < " ++ emitExpr boundE
        ++ "; ++" ++ name ++ ") " ++ openBrace
      let bodyStr := String.intercalate "\n" (body.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      head ++ "\n" ++ bodyStr ++ "\n" ++ close
  | depth, .whileLoop cond body =>
      let head := indent depth ++ "while (" ++ emitExpr cond ++ ") " ++ openBrace
      let bodyStr := String.intercalate "\n" (body.map (emitStmt (depth + 1)))
      let close := indent depth ++ closeBrace
      head ++ "\n" ++ bodyStr ++ "\n" ++ close

/-! ## Function attributes / declarations / module -/

def emitFnAttr : FnAttr → String
  | .shaderCompute        => "[shader(\"compute\")]"
  | .numthreads x y z     =>
      "[numthreads(" ++ toString x ++ ", " ++ toString y ++ ", " ++ toString z ++ ")]"

def emitFunction (f : SlangFunctionDecl) : String :=
  let attrLine :=
    if f.attrs.isEmpty then ""
    else (String.intercalate " " (f.attrs.map emitFnAttr)) ++ "\n"
  let paramsStr := String.intercalate ", " (f.params.map emitParamBinding)
  let header :=
    attrLine ++ emitSlangType f.retType ++ " " ++ f.name
    ++ "(" ++ paramsStr ++ ") " ++ openBrace
  let bodyStr := String.intercalate "\n" (f.body.map (emitStmt 1))
  header ++ "\n" ++ bodyStr ++ "\n" ++ closeBrace

/-- Emit a struct declaration. Fields are indented two spaces. -/
def emitStruct (s : SlangStructDecl) : String :=
  let header := "struct " ++ s.name ++ " " ++ openBrace
  let fieldsStr := String.intercalate "\n"
    (s.fields.map (fun b => "  " ++ emitSlangType b.type ++ " " ++ b.name ++ ";"))
  header ++ "\n" ++ fieldsStr ++ "\n" ++ closeBrace ++ ";"

/-- Emit a `groupshared` workgroup-local declaration. -/
def emitGroupShared (g : SlangGroupSharedDecl) : String :=
  let head := "groupshared " ++ emitSlangType g.elemType ++ " " ++ g.name
  match g.arraySize with
  | some n => head ++ "[" ++ toString n ++ "];"
  | none   => head ++ ";"

/-- Emit a complete shader module. Order: structs, groupshared,
    globals, functions — each non-empty section separated from the
    next by a blank line. -/
def emit (m : SlangShaderModule) : String :=
  let s := String.intercalate "\n\n" (m.structs.map emitStruct)
  let gs := String.intercalate "\n" (m.groupShared.map emitGroupShared)
  let g := String.intercalate "\n" (m.globals.map emitGlobalBinding)
  let f := String.intercalate "\n\n" (m.functions.map emitFunction)
  let parts := [s, gs, g, f].filter (fun p => !p.isEmpty)
  String.intercalate "\n\n" parts

end LeanSlang
