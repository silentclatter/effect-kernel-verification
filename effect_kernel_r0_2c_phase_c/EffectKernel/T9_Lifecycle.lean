import EffectKernel.T0_WellFormed

namespace EffectKernel

private theorem lifecycleUpdate_reach {s t : State} {k : EffectKey}
    {src dst : LifecycleState} (hu : LifecycleUpdate s t k src dst)
    (hedge : LifecycleEdge src dst) :
    ∀ j, LifecycleReach (s.lifecycle j).state (t.lifecycle j).state := by
  intro j
  by_cases hj : j = k
  · subst j
    rw [hu.preState, hu.postState]
    exact .tail (.refl _) hedge
  · rw [hu.other j hj]
    exact .refl _

private theorem lifecycleUpdate_used {s t : State} {k : EffectKey}
    {src dst : LifecycleState} (hu : LifecycleUpdate s t k src dst) :
    ∀ j, (s.lifecycle j).used = true → (t.lifecycle j).used = true := by
  intro j hj
  by_cases hkey : j = k
  · subst j
    exact hu.postUsed
  · rw [hu.other j hkey]
    exact hj

private theorem prepare_reach {s t : State} {k : EffectKey} {g : GrantID}
    {q : BudgetDim → Nat} (h : PrepareLifecycle s t k g q) :
    ∀ j, LifecycleReach (s.lifecycle j).state (t.lifecycle j).state := by
  intro j
  by_cases hj : j = k
  · subst j
    rw [h.preState, h.postState]
    exact .tail (.refl _) .unseen_reserved
  · rw [h.other j hj]
    exact .refl _

private theorem prepare_used {s t : State} {k : EffectKey} {g : GrantID}
    {q : BudgetDim → Nat} (h : PrepareLifecycle s t k g q) :
    ∀ j, (s.lifecycle j).used = true → (t.lifecycle j).used = true := by
  intro j hj
  by_cases hkey : j = k
  · subst j
    exact h.postUsed
  · rw [h.other j hkey]
    exact hj

private theorem reconcile_reach {s t : State} {k : EffectKey} {g : GrantID}
    {outcome : ReconcileOutcome} (h : Reconcile s t k g outcome) :
    ∀ j, LifecycleReach (s.lifecycle j).state (t.lifecycle j).state := by
  cases outcome with
  | unknown => exact lifecycleUpdate_reach h.lifecycleUpdate .unknown_unknown
  | committed => exact lifecycleUpdate_reach h.lifecycleUpdate .unknown_committed
  | aborted => exact lifecycleUpdate_reach h.lifecycleUpdate .unknown_aborted

/-- One-step lifecycle monotonicity derived by cases from actual transition updates. -/
theorem trustedStep_lifecycle_one {s t : State} {kind : TransitionKind}
    (hs : TrustedStep kind s t) :
    ∀ k, LifecycleReach (s.lifecycle k).state (t.lifecycle k).state := by
  cases hs with
  | prepare h => exact prepare_reach h.lifecycleUpdate
  | commitStart h =>
      exact lifecycleUpdate_reach h.lifecycleUpdate.update .reserved_dispatching
  | commitSuccess h =>
      exact lifecycleUpdate_reach h.lifecycleUpdate .dispatching_committed
  | commitAbort h =>
      exact lifecycleUpdate_reach h.lifecycleUpdate .dispatching_aborted
  | commitFaultUnknown h =>
      exact lifecycleUpdate_reach h.lifecycleUpdate .dispatching_unknown
  | reconcile h => exact reconcile_reach h
  | delegate h =>
      intro k
      rw [h.lifecycleSame]
      exact .refl _
  | revoke h =>
      intro k
      rw [h.lifecycleSame]
      exact .refl _
  | selfAttenuate h =>
      intro k
      rw [h.lifecycleSame]
      exact .refl _
  | updatePolicy h =>
      intro k
      rw [h.lifecycleSame]
      exact .refl _
  | expireReservation h =>
      exact lifecycleUpdate_reach h.lifecycleUpdate .reserved_aborted
  | expireGrant h =>
      intro k
      rw [h.lifecycleSame]
      exact .refl _

/-- One-step used-key history preservation derived from exact lifecycle updates. -/
theorem trustedStep_used_one {s t : State} {kind : TransitionKind}
    (hs : TrustedStep kind s t) :
    ∀ k, (s.lifecycle k).used = true → (t.lifecycle k).used = true := by
  cases hs with
  | prepare h => exact prepare_used h.lifecycleUpdate
  | commitStart h => exact lifecycleUpdate_used h.lifecycleUpdate.update
  | commitSuccess h => exact lifecycleUpdate_used h.lifecycleUpdate
  | commitAbort h => exact lifecycleUpdate_used h.lifecycleUpdate
  | commitFaultUnknown h => exact lifecycleUpdate_used h.lifecycleUpdate
  | reconcile h => exact lifecycleUpdate_used h.lifecycleUpdate
  | delegate h =>
      intro k hk
      rw [h.lifecycleSame]
      exact hk
  | revoke h =>
      intro k hk
      rw [h.lifecycleSame]
      exact hk
  | selfAttenuate h =>
      intro k hk
      rw [h.lifecycleSame]
      exact hk
  | updatePolicy h =>
      intro k hk
      rw [h.lifecycleSame]
      exact hk
  | expireReservation h => exact lifecycleUpdate_used h.lifecycleUpdate
  | expireGrant h =>
      intro k hk
      rw [h.lifecycleSame]
      exact hk

/-- T9 — along any arbitrary-length in-epoch trusted run, each key advances only
through the frozen primary/expiry/reconciliation DAG and a used key never becomes
fresh. UNKNOWN therefore cannot reopen RESERVED/DISPATCHING, and EXPIRE_RESERVATION
is exactly RESERVED -> ABORTED. -/
theorem T9_lifecycle {s0 s : State}
    (h0 : WellFormed s0) (hr : ReachableFrom s0 s) :
    (∀ k, LifecycleReach (s0.lifecycle k).state (s.lifecycle k).state) ∧
    (∀ k, (s0.lifecycle k).used = true → (s.lifecycle k).used = true) := by
  clear h0
  induction hr with
  | refl =>
      exact ⟨(fun _ => .refl _), (fun _ h => h)⟩
  | step hr hs ih =>
      rcases ih with ⟨hlife, hused⟩
      constructor
      · intro k
        exact LifecycleReach.trans (hlife k) (trustedStep_lifecycle_one hs k)
      · intro k hk
        exact trustedStep_used_one hs k (hused k hk)

end EffectKernel
