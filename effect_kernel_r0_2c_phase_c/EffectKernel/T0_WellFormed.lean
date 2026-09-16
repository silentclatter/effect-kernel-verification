import EffectKernel.Reachability

namespace EffectKernel

private theorem option_some_inj {α : Type} {a b : α} (h : some a = some b) : a = b := by
  cases h
  rfl

theorem sameGrantStructure_preserves_wf {s t : State}
    (hs : SameGrantStructure s t) (hw : WellFormed s) : WellFormed t := by
  constructor
  · exact hs.post_interval_ok
  · intro g tgr p htg hparent
    rcases hs.from_post g tgr htg with ⟨sgr, hsg, hparEq, _hpvEq, hgenEq⟩
    have hsparent : sgr.parent = some p := by
      rw [hparEq]
      exact hparent
    rcases hw.parent_ok g sgr p hsg hsparent with ⟨spgr, hsp, hlt⟩
    rcases hs.to_post p spgr hsp with ⟨tpgr, htp, _hpar2, _hpv2, hpgenEq⟩
    refine ⟨tpgr, htp, ?_⟩
    rw [← hpgenEq, ← hgenEq]
    exact hlt

theorem delegateGamma_preserves_wf {s t : State} {child parent : GrantID} {rec : GrantRecord}
    (hd : DelegateGamma s t child parent rec) (hw : WellFormed s) : WellFormed t := by
  constructor
  · intro g gr htg
    by_cases hgc : g = child
    · subst g
      have heq : gr = rec := option_some_inj (htg.symm.trans hd.child_post)
      subst gr
      exact hd.interval_ok
    · rw [hd.preserve_other g hgc] at htg
      exact hw.interval_ok g gr htg
  · intro g gr p htg hparent
    by_cases hgc : g = child
    · subst g
      have heq : gr = rec := option_some_inj (htg.symm.trans hd.child_post)
      subst gr
      have hpEq : p = parent := by
        have h : some p = some parent := hparent.symm.trans hd.parent_link
        exact option_some_inj h
      subst p
      rcases hd.parent_pre with ⟨pgr, hsp, hlt⟩
      have hpne : parent ≠ child := by
        intro hpc
        subst parent
        rw [hd.fresh] at hsp
        contradiction
      refine ⟨pgr, ?_, hlt⟩
      rw [hd.preserve_other parent hpne]
      exact hsp
    · have hsg : s.gamma g = some gr := by
        rw [← hd.preserve_other g hgc]
        exact htg
      rcases hw.parent_ok g gr p hsg hparent with ⟨pgr, hsp, hlt⟩
      have hpne : p ≠ child := by
        intro hpc
        subst p
        rw [hd.fresh] at hsp
        contradiction
      refine ⟨pgr, ?_, hlt⟩
      rw [hd.preserve_other p hpne]
      exact hsp

theorem structuralStep_preserves_wf {s t : State}
    (hstep : StructuralStep s t) (hw : WellFormed s) : WellFormed t := by
  cases hstep with
  | preserve h =>
      constructor
      · intro g gr htg
        apply hw.interval_ok g gr
        rw [← h]
        exact htg
      · intro g gr p htg hparent
        apply hw.parent_ok g gr p
        · rw [← h]
          exact htg
        · exact hparent
  | authorityOnly h =>
      exact sameGrantStructure_preserves_wf h hw
  | delegate h =>
      exact delegateGamma_preserves_wf h hw
  | reprovision h =>
      exact h

/-- T0 — Well-Formed Trusted State. Every state reachable from a well-formed
initial trusted state by the frozen abstract trusted transition projection is well formed. -/
theorem T0_wellFormed {f0 f : ProofFrame}
    (h0 : WellFormed f0.state) (hr : ReachableFrom f0 f) : WellFormed f.state := by
  induction hr with
  | refl => exact h0
  | step hr hs ih =>
      exact structuralStep_preserves_wf hs.structural ih

end EffectKernel
