import EffectKernel.T0_WellFormed

namespace EffectKernel

theorem lifecycleSafe_one {s t : State} (h : LifecycleSafe s t) (k : EffectKey) :
    LifecycleReach (s.lifecycle k).state (t.lifecycle k).state := by
  rcases h k with hsame | hedge
  · rw [hsame]
    exact .refl _
  · exact .tail (.refl _) hedge

/-- T9 — Lifecycle Monotonicity and History Preservation. Along any arbitrary-length
trusted run, every effect key advances only through the frozen primary/reconciliation
lifecycle relation, and a used key never becomes fresh. -/
theorem T9_lifecycle {f0 f : ProofFrame}
    (h0 : WellFormed f0.state) (hr : ReachableFrom f0 f) :
    (∀ k, LifecycleReach (f0.state.lifecycle k).state (f.state.lifecycle k).state) ∧
    (∀ k, (f0.state.lifecycle k).used = true → (f.state.lifecycle k).used = true) := by
  have _ := h0
  induction hr with
  | refl =>
      constructor
      · intro k
        exact .refl _
      · intro k hk
        exact hk
  | step hr hs ih =>
      rcases ih with ⟨hlife, hused⟩
      constructor
      · intro k
        exact LifecycleReach.trans (hlife k) (lifecycleSafe_one hs.lifecycle k)
      · intro k hk
        exact hs.usedHistory k (hused k hk)

end EffectKernel
