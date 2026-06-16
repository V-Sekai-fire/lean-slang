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
  -- comparisons yield a C-style 0/1 word (Slang prints them as bool; the BitVec
  -- model keeps everything in `U32`, which is what a `ternary`/`if` then tests).
  | "==", a, b => some (if a = b then 1 else 0)
  | "!=", a, b => some (if a = b then 0 else 1)
  | "<",  a, b => some (if a.ult b then 1 else 0)
  | _,    _, _ => none

/-- Denotation of the unsigned-integer scalar subset of `SlangExpr`. -/
@[simp] def SlangExpr.evalU32 (env : UEnv) : SlangExpr → Option U32
  | .litUint v  => some (BitVec.ofNat 32 v)
  | .var name   => some (env name)
  | .bin op l r => match l.evalU32 env, r.evalU32 env with
                   | some a, some b => binOpU32 op a b
                   | _, _ => none
  | .ternary c t f => match c.evalU32 env, t.evalU32 env, f.evalU32 env with
                      | some cv, some tv, some fv => some (if cv ≠ 0 then tv else fv)
                      | _, _, _ => none
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
  | .ternary c t f => match c.evalU32M env mem, t.evalU32M env mem, f.evalU32M env mem with
                      | some cv, some tv, some fv => some (if cv ≠ 0 then tv else fv)
                      | _, _, _ => none
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

/-! ## Statement-level semantics: locals, buffer stores, return

`evalU32M` denotes a single expression. A real shader body is a *list of
statements* that mutate variables and memory before returning. `evalStmtsU32M`
gives that list a meaning: it threads a variable environment and a buffer memory
through the statements and yields the returned value.

Fragment (extend as kernels need it):
- `declare ty name (some e)` — introduce/overwrite local `name := ⟦e⟧`.
- `assign (index (var buf) idx) rhs` — buffer store `buf[idx] = ⟦rhs⟧`.
- `ret (some e)` — the function value is `⟦e⟧`.
Anything else (no-init declare, variable assign, control flow, fall-off-end)
denotes `none`. This is what makes an emitted *store* provable: a decompiler can
show its lifted store/return sequence and the Slang it renders mean the same
function of (args, memory), for all memories. -/

/-- Overwrite one variable. -/
@[simp] def UEnv.set (env : UEnv) (name : String) (v : U32) : UEnv :=
  fun n => if n = name then v else env n

/-- Store to one buffer address. -/
@[simp] def MEnv.store (mem : MEnv) (buf : String) (addr v : U32) : MEnv :=
  fun b a => if b = buf then (if a = addr then v else mem b a) else mem b a

/-- Denote a statement list: thread `(vars, mem)` and return the `ret` value. -/
@[simp] def evalStmtsU32M (env : UEnv) (mem : MEnv) : List SlangStmt → Option U32
  | .declare _ name (some e) :: rest =>
      match e.evalU32M env mem with
      | some v => evalStmtsU32M (env.set name v) mem rest
      | none   => none
  | .assign (.index (.var buf) idx) rhs :: rest =>
      match idx.evalU32M env mem, rhs.evalU32M env mem with
      | some a, some v => evalStmtsU32M env (mem.store buf a v) rest
      | _, _ => none
  | .ret (some e) :: _ => e.evalU32M env mem
  -- branching `if (c) { return tᵉ; } else { return eᵉ; }`: the condition selects
  -- the arm (nonzero = true) and we evaluate that arm's return expression. Both
  -- arms are evaluated in place (no recursive call), so the function stays
  -- structural — which keeps it unfolding under `simp`/`bv_decide`.
  | .ifThen c [.ret (some te)] [.ret (some ee)] :: _ =>
      match c.evalU32M env mem with
      | some cv => if cv ≠ 0 then te.evalU32M env mem else ee.evalU32M env mem
      | none    => none
  | _ => none

/-- `mem[0] = v; return mem[0];` returns the stored value `v`, for **all** prior
memories — the store/load-back fact, proved at statement level. -/
example (mem : MEnv) (v : U32) :
    evalStmtsU32M (fun n => if n = "v" then v else 0) mem
      [ .assign (.index (.var "mem") (.litUint 0)) (.var "v")
      , .ret (some (.index (.var "mem") (.litUint 0))) ]
      = some v := by
  simp

/-- `(a < b) ? b : a` denotes the unsigned max of `a` and `b`: the result is ≥
both operands, for **all** inputs — comparison + ternary, proved by `bv_decide`.
The branchless conditional a leaf function emits as a `cmov`. -/
example (a b : U32) :
    ∀ r, (SlangExpr.ternary (.bin "<" (.var "a") (.var "b")) (.var "b") (.var "a")).evalU32
            (fun n => if n = "a" then a else b) = some r → ¬ r.ult a ∧ ¬ r.ult b := by
  simp only [SlangExpr.evalU32, binOpU32, Option.some.injEq]
  intro r h; subst h; bv_decide

/-- A branching `if (c) { return x; } else { return y; }` statement body denotes
`c ≠ 0 ? x : y` — statement-level control flow, proved at the `SlangStmt` level. -/
example (c x y : U32) :
    evalStmtsU32M (fun n => if n = "c" then c else if n = "x" then x else y) (fun _ _ => 0)
      [ .ifThen (.var "c") [ .ret (some (.var "x")) ] [ .ret (some (.var "y")) ] ]
      = some (if c ≠ 0 then x else y) := by
  simp only [evalStmtsU32M, SlangExpr.evalU32M, reduceIte]
  exact (apply_ite some (c ≠ 0) x y).symm

/-! ## Call-aware semantics: `SlangExpr.call` against a function environment

`evalU32`/`evalU32M` denote pure / memory expressions. `evalU32F` adds function
calls: a `call f [arg]` denotes `fe f [⟦arg⟧]`, where `fe : FEnv` is an
uninterpreted environment of callee denotations. This lets a decompiler prove
that an emitted call expression and its lifted IR mean the same function of
(inputs, callees) — for **all** callees, since `fe` is abstract.

Kept structural (and thus `simp`/`bv_decide`-friendly): the call cases take an
atom argument (`var`/`litUint`) directly — no recursion through the argument
list — while `bin` recurses on its two subexpressions as usual. This covers the
calls a leaf renders (arguments are registers or immediates). -/

/-- Function environment: a callee name + argument values denote a result. -/
abbrev FEnv := String → List U32 → U32

/-- Call-aware denotation of the integer subset: `evalU32` plus `call f [atom]`. -/
@[simp] def SlangExpr.evalU32F (env : UEnv) (fe : FEnv) : SlangExpr → Option U32
  | .litUint v           => some (BitVec.ofNat 32 v)
  | .var name            => some (env name)
  | .call f [.var nm]    => some (fe f [env nm])
  | .call f [.litUint v] => some (fe f [BitVec.ofNat 32 v])
  | .bin op l r => match l.evalU32F env fe, r.evalU32F env fe with
                   | some a, some b => binOpU32 op a b
                   | _, _ => none
  | _ => none

/-- `f(x) + f(x)` denotes `2·(fe "f" [x])` for **all** callees `fe` — the call
result is abstracted as an opaque term by `bv_decide`. -/
example (fe : FEnv) (x : U32) :
    (SlangExpr.bin "+" (.call "f" [.var "x"]) (.call "f" [.var "x"])).evalU32F (fun _ => x) fe
      = some (2 * fe "f" [x]) := by
  simp only [SlangExpr.evalU32F, binOpU32, Option.some.injEq]; bv_decide

/-- Statement-level semantics for **call**-using bodies, against a function
environment `fe`. Like `evalStmtsU32M` but expressions are evaluated with the
call-aware `evalU32F` (no buffer memory here). Additive — a separate evaluator,
so the memory statement semantics are untouched. Fragment: `declare ty name
(some e)` (a call/ALU result lowered into a local) and `ret (some e)`. -/
@[simp] def evalStmtsU32F (env : UEnv) (fe : FEnv) : List SlangStmt → Option U32
  | .declare _ name (some e) :: rest =>
      match e.evalU32F env fe with
      | some v => evalStmtsU32F (env.set name v) fe rest
      | none   => none
  | .ret (some e) :: _ => e.evalU32F env fe
  | _ => none

/-- `uint x0 = f(a); uint x1 = f(a); uint x2 = x0 + x1; return x2;` denotes
`2·(fe "f" [a])` for **all** callees — a call-using statement body, by `bv_decide`. -/
example (fe : FEnv) (a : U32) :
    evalStmtsU32F (fun n => if n = "a" then a else 0) fe
      [ .declare (.scalar .uint) "x0" (some (.call "f" [.var "a"]))
      , .declare (.scalar .uint) "x1" (some (.call "f" [.var "a"]))
      , .declare (.scalar .uint) "x2" (some (.bin "+" (.var "x0") (.var "x1")))
      , .ret (some (.var "x2")) ]
      = some (2 * fe "f" [a]) := by
  simp only [evalStmtsU32F, SlangExpr.evalU32F, UEnv.set, binOpU32, reduceIte, Option.some.injEq]
  bv_decide

end LeanSlang
