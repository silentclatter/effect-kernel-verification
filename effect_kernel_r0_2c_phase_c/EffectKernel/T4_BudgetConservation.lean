import EffectKernel.T2_AuthorityAttenuation

namespace EffectKernel

theorem budgetDelta_preserves {b b' : BudgetProjection}
    (hi : BudgetInvariant b) (hd : BudgetDelta b b') : BudgetInvariant b' := by
  intro r d
  cases hd with
  | ordinary hmass hprov =>
      calc
        b'.lineageMass r d ≤ b.lineageMass r d := hmass r d
        _ ≤ b.provisioned r d := hi r d
        _ = b'.provisioned r d := (hprov r d).symm
  | provision delta hmass hprov =>
      calc
        b'.lineageMass r d ≤ b.lineageMass r d + delta r d := hmass r d
        _ ≤ b.provisioned r d + delta r d := Nat.add_le_add_right (hi r d) _
        _ = b'.provisioned r d := (hprov r d).symm
  | reprovision h =>
      exact h r d

/-- T4 — Budget / Effectability Conservation. Arbitrary-run transition induction
proves LineageMass(r,n,d) ≤ Provisioned(r,n,d) for every root and dimension,
including independently authorized positive provisioning and explicit E3 reprovision. -/
theorem T4_budgetConservation {f0 f : ProofFrame}
    (h0wf : WellFormed f0.state)
    (h0 : BudgetInvariant f0.budgetView)
    (hr : ReachableFrom f0 f) : BudgetInvariant f.budgetView := by
  have _ := h0wf
  induction hr with
  | refl => exact h0
  | step hr hs ih =>
      exact budgetDelta_preserves ih hs.budget

end EffectKernel
