import EffectKernel.T9_Lifecycle

namespace EffectKernel

/-- T1 — Constitutional Subsumption. Within a fixed theorem epoch, the constitution
is unchanged and every reachable governance policy satisfies that constitution.
E3 is excluded by EpochReachableFrom because E3 starts a successor theorem epoch. -/
theorem T1_constitution {f0 f : ProofFrame}
    (h0wf : WellFormed f0.state)
    (h0 : ConstitutionHolds f0.state)
    (hr : EpochReachableFrom f0 f) :
    f.state.constitution = f0.state.constitution ∧ ConstitutionHolds f.state := by
  have _ := h0wf
  induction hr with
  | refl =>
      exact ⟨rfl, h0⟩
  | step hr hs hepoch ih =>
      rcases ih with ⟨hconst, _hhold⟩
      rcases hs.constitution hepoch with ⟨hstepConst, hstepHold⟩
      constructor
      · exact hstepConst.trans hconst
      · exact hstepHold

end EffectKernel
