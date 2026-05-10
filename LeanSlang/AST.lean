import LeanSlang.Types

/-!
# `LeanSlang.AST` — expressions, statements, function declarations,
shader modules.

Smallest AST that can express the DDM matvec kernel:

- Literals + identifiers + indexing + member access.
- Binary arithmetic and comparison.
- Function call, including the Slang built-ins `mul`, `float3`, `float4`.
- Assignment, `if`, `for` (counted), `return`.
- A single function declaration with optional `[shader("compute")]`
  and `[numthreads(x, y, z)]` attributes.
- A shader module = a list of global bindings + a list of functions.

`SlangExpr` and `SlangStmt` are NOT mutually recursive — `SlangStmt`
uses `SlangExpr` but not the other way — so we declare them
sequentially. Defaults / smart constructors live as functions
afterwards, which keeps the inductive declarations clean.
-/

namespace LeanSlang

/-- Slang expressions. -/
inductive SlangExpr
  | litFloat (v : Float)
  | litUint  (v : Nat)
  | litBool  (v : Bool)
  | var      (name : String)
  | index    (buf : SlangExpr) (idx : SlangExpr)
  | member   (recv : SlangExpr) (field : String)
  | bin      (op : String) (lhs rhs : SlangExpr)
  | un       (op : String) (e : SlangExpr)
  | call     (fn : String) (args : List SlangExpr)
deriving Inhabited

/-- Slang statements. -/
inductive SlangStmt
  /-- Local declaration: `<type> <name> [= <expr>];` -/
  | declare        (ty : SlangType) (name : String) (init : Option SlangExpr)
  /-- `precise <type> <name> [= <expr>];` — prevents fp-contraction.
      Maps to SPIR-V NoContraction. Required on every intermediate
      in an error-free transformation (Knuth two_sum, FMA two_prod,
      etc.) so optimisers cannot rewrite `(a + b) - a` as `b`. -/
  | declarePrecise (ty : SlangType) (name : String) (init : Option SlangExpr)
  /-- Assignment: `lhs = rhs;`. -/
  | assign   (lhs rhs : SlangExpr)
  /-- `expr;` — usually a function call with side effects. -/
  | expr     (e : SlangExpr)
  /-- `return [e];`. -/
  | ret      (e : Option SlangExpr)
  /-- `if (cond) { then } [else { else }]`. -/
  | ifThen   (cond : SlangExpr) (thenS : List SlangStmt) (elseS : List SlangStmt)
  /-- `for (uint <name> = <init>; <name> < <bound>; ++<name>) { body }`. -/
  | forCount  (name : String) (init bound : SlangExpr) (body : List SlangStmt)
  /-- `while (cond) { body }` — caller supplies the termination
      condition. Used for solver convergence loops and tree
      reductions where the step isn't a simple `++`. -/
  | whileLoop (cond : SlangExpr) (body : List SlangStmt)
deriving Inhabited

/-- Convenience: declare with no initializer. -/
def SlangStmt.decl (ty : SlangType) (name : String) : SlangStmt :=
  .declare ty name none

/-- Convenience: declare with an initializer. -/
def SlangStmt.declInit (ty : SlangType) (name : String) (init : SlangExpr) : SlangStmt :=
  .declare ty name (some init)

/-- Convenience: `precise` declaration with an initializer. -/
def SlangStmt.declPreciseInit (ty : SlangType) (name : String) (init : SlangExpr) : SlangStmt :=
  .declarePrecise ty name (some init)

/-- `return;` -/
def SlangStmt.retVoid : SlangStmt := .ret none

/-- `return e;` -/
def SlangStmt.retExpr (e : SlangExpr) : SlangStmt := .ret (some e)

/-- `if (cond) { then }` (no else). -/
def SlangStmt.ifNoElse (cond : SlangExpr) (thenS : List SlangStmt) : SlangStmt :=
  .ifThen cond thenS []

/-- Function attribute. -/
inductive FnAttr
  | shaderCompute
  | numthreads (x y z : Nat)
deriving BEq, Inhabited

/-- A function declaration. -/
structure SlangFunctionDecl where
  attrs   : List FnAttr := []
  retType : SlangType   := SlangType.named "void"
  name    : String
  params  : List SlangBinding := []
  body    : List SlangStmt    := []
deriving Inhabited

/-- A struct declaration: `struct Name { type1 field1; ... };`. Field
    semantics / bindings on `SlangBinding` are ignored — only `name`
    and `type` are used inside a struct body. -/
structure SlangStructDecl where
  name   : String
  fields : List SlangBinding := []
deriving Inhabited

/-- A `groupshared` workgroup-local declaration. When `arraySize` is
    `some n`, emits `groupshared <elemType> <name>[n];`; when `none`,
    emits `groupshared <elemType> <name>;`. -/
structure SlangGroupSharedDecl where
  name      : String
  elemType  : SlangType
  arraySize : Option Nat := none
deriving Inhabited

/-- A shader module. -/
structure SlangShaderModule where
  structs     : List SlangStructDecl       := []
  groupShared : List SlangGroupSharedDecl  := []
  globals     : List SlangBinding          := []
  functions   : List SlangFunctionDecl     := []
deriving Inhabited

namespace SlangShaderModule

/-- The first function with a `shaderCompute` attribute, if any. -/
def entryPoint (m : SlangShaderModule) : Option SlangFunctionDecl :=
  m.functions.find? (fun f => f.attrs.contains FnAttr.shaderCompute)

/-- The entry-point name, or `""` if there isn't one. -/
def entryPointName (m : SlangShaderModule) : String :=
  match m.entryPoint with
  | some f => f.name
  | none   => ""

end SlangShaderModule

end LeanSlang
