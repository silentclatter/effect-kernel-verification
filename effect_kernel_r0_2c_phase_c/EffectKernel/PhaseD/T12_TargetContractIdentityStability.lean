import EffectKernel.PhaseD.FullSemantics

namespace EffectKernel.PhaseD

open EffectKernel

/-- Exact TCID projection of the frozen `SameEffectBinding` relation. -/
theorem sameEffectBinding_tcid {a b : LifecycleRecord}
    (h : SameEffectBinding a b) : a.tcid = b.tcid := by
  exact h.2.2.2.2.2.1

/-- T12 — Target-Contract Identity Stability.

For a fixed effect key, every post-reservation lifecycle transition named by R1
preserves the exact Phase C `tcid` field. The theorem ranges over the actual
`FullStep` transition relation; TCID equality is derived from the frozen
`SameEffectBinding` equations and is not carried as an added transition premise.

Consequently, if the predecessor and successor TCIDs differ, none of these
same-key lifecycle transitions can be the transition between them. A changed
target contract therefore requires a distinct effect admission rather than
mutation of the already-reserved effect.

No target-contract truth, sufficiency, implementation correctness, or
cryptographic collision-resistance property is asserted here. -/
theorem T12_targetContractIdentityStability
    {E : FullEnv} {s t : State} {k : EffectKey}
    (hstep :
      (∃ now, FullStep E (.commitStart k now) s t) ∨
      (∃ g q refund spent,
        FullStep E (.commitSuccess k g q refund spent) s t) ∨
      (∃ g q refund burned,
        FullStep E (.commitAbort k g q refund burned) s t) ∨
      (∃ g q, FullStep E (.commitFaultUnknown k g q) s t) ∨
      (∃ g outcome, FullStep E (.reconcile k g outcome) s t)) :
    (s.lifecycle k).tcid = (t.lifecycle k).tcid := by
  rcases hstep with hstart | hsuccess | habort | hunknown | hreconcile
  · rcases hstart with ⟨now, h⟩
    exact sameEffectBinding_tcid h.base.lifecycleUpdate.update.binding
  · rcases hsuccess with ⟨g, q, refund, spent, h⟩
    exact sameEffectBinding_tcid h.base.lifecycleUpdate.binding
  · rcases habort with ⟨g, q, refund, burned, h⟩
    exact sameEffectBinding_tcid h.base.lifecycleUpdate.binding
  · rcases hunknown with ⟨g, q, h⟩
    exact sameEffectBinding_tcid h.base.lifecycleUpdate.binding
  · rcases hreconcile with ⟨g, outcome, h⟩
    exact sameEffectBinding_tcid h.base.lifecycleUpdate.binding

/-- Explicit no-mutation corollary: a TCID change cannot occur through any R1
post-reservation same-key lifecycle transition. -/
theorem T12_tcidChange_requiresDistinctAdmission
    {E : FullEnv} {s t : State} {k : EffectKey}
    (hne : (s.lifecycle k).tcid ≠ (t.lifecycle k).tcid) :
    ¬ ((∃ now, FullStep E (.commitStart k now) s t) ∨
       (∃ g q refund spent,
         FullStep E (.commitSuccess k g q refund spent) s t) ∨
       (∃ g q refund burned,
         FullStep E (.commitAbort k g q refund burned) s t) ∨
       (∃ g q, FullStep E (.commitFaultUnknown k g q) s t) ∨
       (∃ g outcome, FullStep E (.reconcile k g outcome) s t)) := by
  intro h
  exact hne (T12_targetContractIdentityStability h)

end EffectKernel.PhaseD
