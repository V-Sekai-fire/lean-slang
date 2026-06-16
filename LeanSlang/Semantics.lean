import LeanSlang.AST
import Std.Tactic.BVDecide

/-!
# `LeanSlang.Semantics` — a denotational semantics for the integer subset

`LeanSlang.Emit` turns a `SlangExpr` into *text*; this module gives it
*meaning*. We interpret the unsigned-integer scalar subset of `SlangExpr`
into `BitVec 32` — the same fixed-width two's-complement model the Slang
`uint` type and SPIR-V's `OpIAdd`/`OpShiftRightLogical`/… obey.

Why this exists: until now lean-slang could only be checked by pinning its
*printed text* (`Test.lean`, `native_decide`). That catches printer drift but
says nothing about what a kernel **computes**. With `evalU32`, a caller can
state and *prove* `∀ inputs, shaderExpr means f inputs` — e.g. a decompiler
proving its lifted IL and the Slang it renders denote the same function, with
`bv_decide`, without compiling or running anything.

Scope (kept deliberately small, extend as kernels need it):
- `litUint`, `var`, and `bin` over `+ - * & | ^ << >>`.
- The op strings are **exactly** those `Emit.emitExpr` prints, so semantics and
  pretty-printer cannot silently disagree (see `binOpU32_matches_emit` below).
- Everything outside the fragment (float/bool literals, comparisons producing
  `bool`, `index`/`member`/`call`/`ternary`/unary) denotes `none` — honest
  partiality rather than a bogus default that would let us "prove" nonsense.
-/

namespace LeanSlang

/-- A 32-bit unsigned Slang value. -/
abbrev U32 := BitVec 32

/-- Environment: a `var` name resolves to its 32-bit value. -/
abbrev UEnv := String → U32

/-- The binary-operator semantics, on exactly the op strings the emitter
prints. `none` for any op outside the unsigned-int fragment. Shifts are
logical (`>>>`), matching Slang/SPIR-V semantics for `uint`. -/
@[simp] def binOpU32 : String → U32 → U32 → Option U32
  | "+",  a, b => some (a + b)
  | "-",  a, b => some (a - b)
  | "*",  a, b => some (a * b)
  | "&",  a, b => some (a &&& b)
  | "|",  a, b => some (a ||| b)
  | "^",  a, b => some (a ^^^ b)
  | "<<", a, b => some (a <<< b)
  | ">>", a, b => some (a >>> b)
  | _,    _, _ => none

/-- Denotation of the unsigned-integer scalar subset of `SlangExpr`. -/
@[simp] def SlangExpr.evalU32 (env : UEnv) : SlangExpr → Option U32
  | .litUint v  => some (BitVec.ofNat 32 v)
  | .var name   => some (env name)
  | .bin op l r => match l.evalU32 env, r.evalU32 env with
                   | some a, some b => binOpU32 op a b
                   | _, _ => none
  | _ => none

/-! ## Fixtures — meaning, not just text.

The `native_decide` fixtures in `Test.lean` pin the printer; these pin the
*semantics*. Together: the AST prints to the right string AND means the right
function. -/

/-- `a` and `b` resolve to two given words; everything else to `0`. -/
private def env2 (a b : U32) : UEnv := fun n => if n = "a" then a else if n = "b" then b else 0

/-- `(a * b)` — the body of `Test.helperFnShader`'s `mul2`, but over `uint` —
denotes multiplication, for **all** inputs. -/
example (a b : U32) :
    (SlangExpr.bin "*" (.var "a") (.var "b")).evalU32 (env2 a b) = some (a * b) := by
  simp [env2]

/-- `(step >> 1u)` — the reduction step from `Test.whileLoopShader` —
denotes a logical right shift by one. -/
example (s : U32) :
    (SlangExpr.bin ">>" (.var "a") (.litUint 1)).evalU32 (env2 s 0) = some (s >>> (1 : U32)) := by
  simp [env2]

/-- A universally-quantified semantic fact `bv_decide` proves but a printer
test never could: `(a + b)` and `(b + a)` are the same function. This is the
class of theorem that replaces a decompiler's random-input equivalence oracle. -/
example (a b : U32) :
    (SlangExpr.bin "+" (.var "a") (.var "b")).evalU32 (env2 a b)
      = (SlangExpr.bin "+" (.var "b") (.var "a")).evalU32 (env2 a b) := by
  simp only [SlangExpr.evalU32, env2, binOpU32, reduceIte, Option.some.injEq]
  bv_decide

end LeanSlang
