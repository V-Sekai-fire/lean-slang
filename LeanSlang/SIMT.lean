import LeanSlang.Semantics

/-! # `LeanSlang.SIMT` — minimal correctness for data-parallel compute kernels

A compute kernel emitted by lean-slang runs the *same* body across a grid of
threads in a hardware-chosen, unspecified order. Two things make such a kernel
correct, and they factor cleanly:

1. **Per-thread body** — thread `t` computes the intended scalar value. This is
   exactly `SlangExpr.evalU32` (the semantics flowref's render-correctness already
   targets): `body.evalU32 (env t) = some (f t)`.
2. **Non-interference** — distinct threads write distinct addresses (*race-free*).
   Then the parallel result is **independent of the thread schedule** and equals
   the elementwise map `t ↦ f t`.

This module proves part 2 (the SIMT-specific obligation) and composes it with
part 1 into whole-kernel correctness. Mathlib-free: Lean core + `BitVec`. -/

namespace LeanSlang.SIMT

/-- A global (address → value) memory; addresses and values are 32-bit. -/
abbrev GMem := U32 → U32
abbrev Tid  := Nat

/-- Point update. -/
@[simp] def upd (m : GMem) (a v : U32) : GMem := fun x => if x = a then v else m x

/-- Apply a schedule's writes left-to-right (later writes win on a clash). -/
def run : List (U32 × U32) → GMem → GMem
  | [],           m => m
  | (a, v) :: ws, m => run ws (upd m a v)

/-- `map` of a function injective on `l` preserves `Nodup` (core-only helper). -/
theorem nodup_map_inj {α β : Type} {l : List α} {f : α → β}
    (hl : l.Nodup) (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 (fun a ha b hb => hf a (.tail _ ha) b (.tail _ hb))⟩
    intro hmem
    obtain ⟨a, ha, hfa⟩ := List.mem_map.1 hmem
    exact hl.1 (hf x (.head _) a (.tail _ ha) hfa.symm ▸ ha)

/-- An address untouched by a schedule keeps its prior value. -/
theorem run_not_mem (ws : List (U32 × U32)) (m : GMem) (x : U32)
    (h : x ∉ ws.map Prod.fst) : run ws m x = m x := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨a, v⟩ := w
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [run, ih (upd m a v) h.2]; simp [upd, h.1]

/-- **Each thread's write is read back**, in any schedule order — given the
addresses are distinct (race-free). -/
theorem run_get (ws : List (U32 × U32)) (m : GMem) (a v : U32)
    (hmem : (a, v) ∈ ws) (hd : (ws.map Prod.fst).Nodup) : run ws m a = v := by
  induction ws generalizing m with
  | nil => simp at hmem
  | cons w ws ih =>
    obtain ⟨b, u⟩ := w
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.1 hmem with he | htl
    · injection he with h1 h2; subst h1; subst h2
      rw [run, run_not_mem ws (upd m a v) a hd.1]; simp [upd]
    · rw [run]; exact ih (upd m b u) htl hd.2

/-- **Schedule-independence (determinism).** Any two permutations of a race-free
kernel's threads yield the same final memory — the SIMT hardware may interleave
threads however it likes; the observable result is fixed. -/
theorem run_perm (ws₁ ws₂ : List (U32 × U32)) (m : GMem)
    (hp : ws₁.Perm ws₂) (hd : (ws₁.map Prod.fst).Nodup) : run ws₁ m = run ws₂ m := by
  funext x
  by_cases hx : x ∈ ws₁.map Prod.fst
  · obtain ⟨⟨a, v⟩, hin, rfl⟩ := List.mem_map.1 hx
    rw [run_get ws₁ m a v hin hd,
        run_get ws₂ m a v (hp.mem_iff.1 hin) ((hp.map Prod.fst).nodup_iff.1 hd)]
  · rw [run_not_mem ws₁ m x hx,
        run_not_mem ws₂ m x (fun h => hx ((hp.map Prod.fst).mem_iff.2 h))]

/-! ## Kernel level: race-free ⇒ computes the map -/

/-- Writes performed by a thread schedule (`addr`/`val` per thread). -/
def kernelWrites (sched : List Tid) (addr val : Tid → U32) : List (U32 × U32) :=
  sched.map (fun t => (addr t, val t))

/-- Race-free: distinct scheduled threads write distinct addresses. -/
def RaceFree (sched : List Tid) (addr : Tid → U32) : Prop :=
  ∀ s ∈ sched, ∀ t ∈ sched, addr s = addr t → s = t

theorem kernel_nodup {sched : List Tid} {addr val : Tid → U32}
    (hs : sched.Nodup) (hrf : RaceFree sched addr) :
    ((kernelWrites sched addr val).map Prod.fst).Nodup := by
  unfold kernelWrites; rw [List.map_map]
  exact nodup_map_inj hs (fun a ha b hb h => hrf a ha b hb h)

/-- **Minimal SIMT correctness.** Under any schedule (each thread once, any
order) of a race-free kernel, thread `t`'s output is exactly `val t`. -/
theorem simt_correct {sched : List Tid} {addr val : Tid → U32}
    (hs : sched.Nodup) (hrf : RaceFree sched addr) {t : Tid} (ht : t ∈ sched) (m : GMem) :
    run (kernelWrites sched addr val) m (addr t) = val t :=
  run_get _ m (addr t) (val t) (List.mem_map.2 ⟨t, ht, rfl⟩) (kernel_nodup hs hrf)

/-! ## Composition: scalar body (`evalU32`) ∘ non-interference = whole kernel

The payoff. If each thread's *body* denotes `f t` (the per-thread scalar
obligation — `SlangExpr.evalU32`, the very thing flowref proves its render
against) and the kernel is race-free, then the grid computes `t ↦ f t`,
whatever order the SIMT hardware runs the threads in. -/

theorem simt_kernel_correct
    {sched : List Tid} {addr : Tid → U32} {body : SlangExpr} {env : Tid → UEnv} {f : Tid → U32}
    (hs : sched.Nodup) (hrf : RaceFree sched addr)
    (hbody : ∀ t ∈ sched, body.evalU32 (env t) = some (f t))
    {t : Tid} (ht : t ∈ sched) (m : GMem) :
    run (kernelWrites sched addr (fun t => (body.evalU32 (env t)).getD 0)) m (addr t) = f t := by
  rw [simt_correct hs hrf ht m, hbody t ht]; rfl

end LeanSlang.SIMT
