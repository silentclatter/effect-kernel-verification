import EffectKernel.PhaseD.FullSemantics

namespace EffectKernel.PhaseD

open EffectKernel

/-- T9 lifecycle persistence lifted locally over a full in-epoch trace. -/
theorem fullTrace_lifecycle_reach_T11 {E : FullEnv} {s0 s : State}
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

/-- T9 used-bit persistence lifted over a full in-epoch trace. -/
theorem fullTrace_used_monotone {E : FullEnv} {s0 s : State}
    (h : FullTrace E s0 s) :
    ∀ k, (s0.lifecycle k).used = true → (s.lifecycle k).used = true := by
  induction h with
  | refl =>
      intro k hk
      exact hk
  | step hprev hstep ih =>
      intro k hk
      exact trustedStep_used_one (fullStep_to_trusted hstep) k (ih k hk)

/-- Meta-authorization consumption is independently monotone over all full
in-epoch steps. It is not inferred from the effect-key used bit. -/
theorem fullTrace_metaAuth_monotone {E : FullEnv} {s0 s : State}
    (h : FullTrace E s0 s) :
    ∀ m, s0.metaAuth m = true → s.metaAuth m = true := by
  induction h with
  | refl =>
      intro m hm
      exact hm
  | step hprev hstep ih =>
      intro m hm
      exact hstep.metaMonotone m (ih m hm)

/-- Once DISPATCHING has been reached, the frozen lifecycle graph never returns
to RESERVED. -/
theorem lifecycleReach_from_dispatching_cases {dst : LifecycleState}
    (h : LifecycleReach .dispatching dst) :
    dst = .dispatching ∨ dst = .committed ∨ dst = .aborted ∨ dst = .unknown := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hprev hedge ih =>
      rcases ih with hdisp | hcommit | habort | hunk
      · subst hdisp
        cases hedge with
        | dispatching_committed => exact Or.inr (Or.inl rfl)
        | dispatching_aborted => exact Or.inr (Or.inr (Or.inl rfl))
        | dispatching_unknown => exact Or.inr (Or.inr (Or.inr rfl))
      · subst hcommit
        cases hedge
      · subst habort
        cases hedge
      · subst hunk
        cases hedge with
        | unknown_unknown => exact Or.inr (Or.inr (Or.inr rfl))
        | unknown_committed => exact Or.inr (Or.inl rfl)
        | unknown_aborted => exact Or.inr (Or.inr (Or.inl rfl))

/-- T11 — Replay Exclusion and Non-Resurrection.

After the first successful PREPARE of an initially unused effect key, its durable
used bit stays true through every in-epoch continuation. Hence the same key can
never satisfy PREPARE freshness again. If a COMMIT_START occurs, the same
lifecycle cannot later permit a second COMMIT_START because DISPATCHING cannot
return to RESERVED. Independently, any consumed meta-authorization remains
consumed and therefore cannot authorize a second positive-provision update.
The final conjunct exposes the T4 conservation bound for any valid history ending
at the continuation state.

This theorem is intentionally in-epoch. It makes no deployment anti-rollback or
cross-E3 persistence claim beyond the R1 abstract epoch boundary. -/
theorem T11_replayExclusionNonResurrection
    {E : FullEnv} {s t u : State} {k : EffectKey} {g : GrantID}
    {q : BudgetDim → Nat} {now : Nat}
    (hprep : FullStep E (.prepare k g q now) s t)
    (hlater : FullTrace E t u) :
    (s.lifecycle k).used = false ∧
    (t.lifecycle k).used = true ∧
    (u.lifecycle k).used = true ∧
    (∀ {v : State} {g' : GrantID} {q' : BudgetDim → Nat} {now' : Nat},
      FullStep E (.prepare k g' q' now') u v → False) ∧
    (∀ {v w x : State} {now1 now2 : Nat},
      FullStep E (.commitStart k now1) u v →
      FullTrace E v w →
      FullStep E (.commitStart k now2) w x → False) ∧
    (∀ m, t.metaAuth m = true →
      u.metaAuth m = true ∧
      ∀ {v : State} {r : GrantID} {delta : BudgetDim → Nat}
          {newPolicy : GovernancePolicy},
        FullStep E (.updatePolicy (.positiveProvision r delta) newPolicy m) u v → False) ∧
    (∀ {s0 : State} {ids0 : List GrantID} {alloc : InitialAllocation}
        {n : Nat} {ids : List GrantID} {es : List ProvisionEvent},
      WellFormed s0 →
      BudgetHistory E.provisionJudge s0 ids0 alloc n u ids es →
      ∀ r d, CanonicalRoot u r →
        LineageMass ids u r d ≤
          Provisioned (InitialProvision ids0 s0 alloc) es r d) := by
  have hp : Prepare s t k g q := hprep.base
  have husedU : (u.lifecycle k).used = true :=
    fullTrace_used_monotone hlater k hp.lifecycleUpdate.postUsed
  refine ⟨hp.lifecycleUpdate.preUnused, hp.lifecycleUpdate.postUsed, husedU, ?_, ?_, ?_, ?_⟩
  · intro v g' q' now' hsecond
    have hfresh := hsecond.base.lifecycleUpdate.preUnused
    rw [husedU] at hfresh
    cases hfresh
  · intro v w x now1 now2 hstart hafter hsecond
    have hs : CommitStart u v k := hstart.base
    have hreach := fullTrace_lifecycle_reach_T11 hafter k
    rw [hs.lifecycleUpdate.update.postState] at hreach
    have hcases := lifecycleReach_from_dispatching_cases hreach
    have hpre := hsecond.base.lifecycleUpdate.update.preState
    rcases hcases with hdisp | hcommit | habort | hunk
    · rw [hdisp] at hpre
      cases hpre
    · rw [hcommit] at hpre
      cases hpre
    · rw [habort] at hpre
      cases hpre
    · rw [hunk] at hpre
      cases hpre
  · intro m hm
    have hmu := fullTrace_metaAuth_monotone hlater m hm
    refine ⟨hmu, ?_⟩
    intro v r delta newPolicy hpos
    have hfresh := hpos.base.metaAuthUpdate.fresh
    rw [hmu] at hfresh
    cases hfresh
  · intro s0 ids0 alloc n ids es h0wf hhist r d hroot
    exact T4_budgetConservation h0wf hhist r d hroot

end EffectKernel.PhaseD
