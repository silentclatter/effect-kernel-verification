import EffectKernel.PhaseD.FullSemantics

namespace EffectKernel.PhaseD

open EffectKernel

/-- T9 lifted to the proof-only full trace. This adds no transition premise. -/
theorem fullTrace_lifecycle_reach {E : FullEnv} {s0 s : State}
    (h : FullTrace E s0 s) :
    ∀ k, LifecycleReach (s0.lifecycle k).state (s.lifecycle k).state := by
  induction h with
  | refl =>
      intro k
      exact .refl _
  | step hprev hstep ih =>
      intro k
      exact LifecycleReach.trans (ih k)
        (trustedStep_lifecycle_one (fullStep_to_trusted hstep) k)

/-- From UNKNOWN the frozen lifecycle graph can only remain UNKNOWN or reconcile
terminally to COMMITTED/ABORTED. In particular it cannot return to a fresh
pre-dispatch state. -/
theorem lifecycleReach_from_unknown_cases {dst : LifecycleState}
    (h : LifecycleReach .unknown dst) :
    dst = .unknown ∨ dst = .committed ∨ dst = .aborted := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hprev hedge ih =>
      rcases ih with hunk | hcommit | habort
      · subst hunk
        cases hedge with
        | unknown_unknown => exact Or.inl rfl
        | unknown_committed => exact Or.inr (Or.inl rfl)
        | unknown_aborted => exact Or.inr (Or.inr rfl)
      · subst hcommit
        cases hedge
      · subst habort
        cases hedge

/-- T10 — Uncertain-Outcome Conservatism.

A valid fault-unknown transition moves DISPATCHING to UNKNOWN and burns the full
outstanding reservation into consumed quantity without refund. Any later
in-epoch full trace for the same effect key can only remain UNKNOWN or reconcile
to COMMITTED/ABORTED; it cannot return to RESERVED/DISPATCHING. The final
conjunct is the explicit T4 bridge: appending this fault step to any valid budget
history preserves the history-derived conservation ceiling.

This theorem does not assert that UNKNOWN means that no physical effect occurred. -/
theorem T10_uncertainOutcomeConservatism
    {E : FullEnv} {s t u : State} {k : EffectKey} {g : GrantID}
    {q : BudgetDim → Nat}
    (hfault : FullStep E (.commitFaultUnknown k g q) s t)
    (hlater : FullTrace E t u) :
    (s.lifecycle k).state = .dispatching ∧
    (t.lifecycle k).state = .unknown ∧
    (∀ d,
      (t.budget g d).avail = (s.budget g d).avail ∧
      (t.budget g d).resv = (s.budget g d).resv - q d ∧
      (t.budget g d).cons = (s.budget g d).cons + q d) ∧
    ((u.lifecycle k).state = .unknown ∨
      (u.lifecycle k).state = .committed ∨
      (u.lifecycle k).state = .aborted) ∧
    (∀ {s0 : State} {ids0 : List GrantID} {alloc : InitialAllocation}
        {n : Nat} {ids : List GrantID} {es : List ProvisionEvent},
      WellFormed s0 →
      BudgetHistory E.provisionJudge s0 ids0 alloc n s ids es →
      GammaSupportExact t ids →
      ∀ r d, CanonicalRoot t r →
        LineageMass ids t r d ≤
          Provisioned (InitialProvision ids0 s0 alloc) es r d) := by
  have hbase : CommitFaultUnknown s t k g q := hfault.base
  have hreach : LifecycleReach .unknown (u.lifecycle k).state := by
    have h := fullTrace_lifecycle_reach hlater k
    rw [hbase.lifecycleUpdate.postState] at h
    exact h
  refine ⟨hbase.lifecycleUpdate.preState, hbase.lifecycleUpdate.postState, ?_,
    lifecycleReach_from_unknown_cases hreach, ?_⟩
  · intro d
    have hb := hbase.budgetUpdate.atOwner d
    have hav := congrArg BudgetCell.avail hb
    have hresv := congrArg BudgetCell.resv hb
    have hcons := congrArg BudgetCell.cons hb
    exact ⟨hav, hresv, hcons⟩
  · intro s0 ids0 alloc n ids es h0wf hhist hsupport r d hroot
    have hhist' :
        BudgetHistory E.provisionJudge s0 ids0 alloc (n + 1) t ids es :=
      .commitFaultUnknown hhist hbase hsupport
    exact T4_budgetConservation h0wf hhist' r d hroot

end EffectKernel.PhaseD
