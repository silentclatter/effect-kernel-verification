import EffectKernel.PhaseD.T4_5_TraceHistory

namespace EffectKernel.PhaseD

open EffectKernel

private def PostLinearizedLifecycle : LifecycleState → Prop
  | .dispatching => True
  | .committed => True
  | .aborted => True
  | .unknown => True
  | .unseen => False
  | .reserved => False

private theorem lifecycleEdge_preserves_postLinearized
    {a b : LifecycleState}
    (ha : PostLinearizedLifecycle a)
    (he : LifecycleEdge a b) : PostLinearizedLifecycle b := by
  cases he <;> simp [PostLinearizedLifecycle] at ha ⊢

private theorem lifecycleReach_preserves_postLinearized
    {a b : LifecycleState}
    (ha : PostLinearizedLifecycle a)
    (hr : LifecycleReach a b) : PostLinearizedLifecycle b := by
  induction hr with
  | refl => exact ha
  | tail hxy hyz ih =>
      exact lifecycleEdge_preserves_postLinearized ih hyz

private theorem dispatching_cannot_reach_reserved
    {b : LifecycleState}
    (hr : LifecycleReach .dispatching b) : b ≠ .reserved := by
  have hp : PostLinearizedLifecycle b :=
    lifecycleReach_preserves_postLinearized (by trivial) hr
  intro hb
  subst b
  exact hp

private theorem commitStart_reach_terminal
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {k : EffectKey} {now : Nat} {a b : State}
    (ho : StepAt h i (.commitStart k now) a b) :
    LifecycleReach .dispatching (z.lifecycle k).state := by
  have hs : FullStep E (.commitStart k now) a b := StepAt.fullStep ho
  have hr := StepAt.lifecycle_from_successor ho k
  rw [hs.base.lifecycleUpdate.update.postState] at hr
  exact hr

/-- Two COMMIT_START occurrences for the same effect key in one full trace must
have the same trace index.  The proof uses the Phase-C/T9 lifecycle direction:
a prior COMMIT_START puts the key in DISPATCHING, from which RESERVED is
unreachable, while every later COMMIT_START requires RESERVED as predecessor. -/
private theorem commitStart_index_unique
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    {i j nowI nowJ : Nat} {a b c d : State}
    (hi : StepAt h i (.commitStart k nowI) a b)
    (hj : StepAt h j (.commitStart k nowJ) c d) : i = j := by
  induction h with
  | refl =>
      cases hi
  | @step _ _ _ hp hsEnd ih =>
      cases hi with
      | last hp1 hs1 =>
          cases hj with
          | last hp2 hs2 => rfl
          | earlier hsEnd2 hjp =>
              have hr := commitStart_reach_terminal hjp
              have hnot := dispatching_cannot_reach_reserved hr
              exact False.elim (hnot hs1.base.lifecycleUpdate.update.preState)
      | earlier hsEnd1 hip =>
          cases hj with
          | last hp2 hs2 =>
              have hr := commitStart_reach_terminal hip
              have hnot := dispatching_cannot_reach_reserved hr
              exact False.elim (hnot hs2.base.lifecycleUpdate.update.preState)
          | earlier hsEnd2 hjp =>
              exact ih hip hjp

/-- T6 — Unique Authorization Linearization.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

For an initially fresh effect key, COMMIT_START has at most one trace index. If
it exists, that index is `ell_H(k)`; the successor is DISPATCHING with the
linearized bit set, and no later in-epoch step can create another COMMIT_START
for the same key. -/
theorem T6_uniqueAuthorizationLinearization
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false) :
    (∀ {i j nowI nowJ : Nat} {a b c d : State},
      StepAt h i (.commitStart k nowI) a b →
      StepAt h j (.commitStart k nowJ) c d → i = j) ∧
    (∀ {j now : Nat} {before after : State},
      StepAt h j (.commitStart k now) before after →
      (after.lifecycle k).state = .dispatching ∧
      (after.lifecycle k).linearized = true) := by
  clear hinitState hinitUsed
  constructor
  · intro i j nowI nowJ a b c d hi hj
    exact commitStart_index_unique hi hj
  · intro j now before after ho
    have hs : FullStep E (.commitStart k now) before after := StepAt.fullStep ho
    exact ⟨hs.base.lifecycleUpdate.update.postState,
      hs.base.lifecycleUpdate.postLinearized⟩

end EffectKernel.PhaseD
