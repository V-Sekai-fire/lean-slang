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

/-! ## Memory-aware semantics: buffer reads

`evalU32` is pure (no memory). `evalU32M` adds read-only buffer access: a
`buf[idx]` expression (`SlangExpr.index (.var buf) idx`) — exactly how Slang
reads a `StructuredBuffer` — denotes `mem buf (⟦idx⟧)`. This lets a caller prove
that emitted Slang reading memory means a specific function of (vars, memory) —
e.g. a decompiler's lifted load and the `buf[i]` it renders denote the same
value, with the buffer left fully abstract so the proof holds for all memories. -/

/-- Buffer environment: a buffer name + a 32-bit address resolve to a value. -/
abbrev MEnv := String → U32 → U32

/-- Memory-aware denotation: like `evalU32`, plus `buf[idx]` buffer reads. -/
@[simp] def SlangExpr.evalU32M (env : UEnv) (mem : MEnv) : SlangExpr → Option U32
  | .litUint v  => some (BitVec.ofNat 32 v)
  | .var name   => some (env name)
  | .index (.var buf) idx => match idx.evalU32M env mem with
                             | some i => some (mem buf i)
                             | none   => none
  | .bin op l r => match l.evalU32M env mem, r.evalU32M env mem with
                   | some a, some b => binOpU32 op a b
                   | _, _ => none
  | _ => none

/-- `buf[i]` denotes the buffer read `mem "buf" i`, for **all** memories. -/
example (mem : MEnv) (i : U32) :
    (SlangExpr.index (.var "buf") (.var "i")).evalU32M (fun _ => i) mem
      = some (mem "buf" i) := by
  simp

/-- `(buf[0] + buf[1])` and `(buf[1] + buf[0])` are the same function of memory —
`bv_decide` with both buffer reads abstracted as opaque bitvector atoms. The
memory analogue of the commutativity fixture above; the shape a decompiler uses
to prove a lifted memory-reading leaf equivalent without running it. -/
example (mem : MEnv) :
    (SlangExpr.bin "+" (.index (.var "buf") (.litUint 0)) (.index (.var "buf") (.litUint 1))).evalU32M (fun _ => 0) mem
      = (SlangExpr.bin "+" (.index (.var "buf") (.litUint 1)) (.index (.var "buf") (.litUint 0))).evalU32M (fun _ => 0) mem := by
  simp only [SlangExpr.evalU32M, binOpU32, Option.some.injEq]
  bv_decide

end LeanSlang
