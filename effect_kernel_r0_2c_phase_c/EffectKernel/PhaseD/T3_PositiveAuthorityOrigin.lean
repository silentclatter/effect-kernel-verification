import EffectKernel.PhaseD.FullSemantics

namespace EffectKernel.PhaseD

open EffectKernel

private theorem noNew_of_gammaEq {s t : State} {g : GrantID} {gr : GrantRecord}
    (hgamma : t.gamma = s.gamma)
    (hpre : s.gamma g = none)
    (hpost : t.gamma g = some gr) : False := by
  have hv : t.gamma g = s.gamma g := congrFun hgamma g
  have hsg : s.gamma g = some gr := hv.symm.trans hpost
  have hbad : (none : Option GrantRecord) = some gr := hpre.symm.trans hsg
  cases hbad

/-- T3 — Positive Authority Origin.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

For an in-epoch full step, any grant absent in the predecessor and present in the
successor can only be the fresh child of the frozen delegation transition. The
witness exposes the predecessor parent, attenuation guards, and transfer budget.
Cross-epoch root provisioning is deliberately outside this theorem. -/
theorem T3_positiveAuthorityOrigin
    {E : FullEnv} {lbl : StepLabel} {s t : State}
    {g : GrantID} {gr : GrantRecord}
    (h : FullStep E lbl s t)
    (hpre : s.gamma g = none)
    (hpost : t.gamma g = some gr) :
    ∃ p q,
      lbl = .delegate p g gr q ∧
      Delegate s t p g gr q ∧
      GrantExists s p ∧
      gr.parent = some p ∧
      gr.permission.le (P_eff s p) ∧
      (∀ now, gr.validity.Contains now → EffectiveValid s p now) ∧
      (gr.delegable = true → EffectiveDelegable s p) ∧
      DelegateBudget s t p g q := by
  rcases h with ⟨hbase, _hguard, _hmeta⟩
  cases lbl with
  | prepare k g0 q now =>
      change Prepare s t k g0 q at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | commitStart k now =>
      change CommitStart s t k at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | commitSuccess k g0 q refund spent =>
      change CommitSuccess s t k g0 q refund spent at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | commitAbort k g0 q refund burned =>
      change CommitAbort s t k g0 q refund burned at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | commitFaultUnknown k g0 q =>
      change CommitFaultUnknown s t k g0 q at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | reconcile k g0 outcome =>
      change Reconcile s t k g0 outcome at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | delegate parent child rec q =>
      change Delegate s t parent child rec q at hbase
      by_cases hc : child = g
      · subst child
        have hrec : rec = gr := some_inj (hbase.gammaUpdate.childPost.symm.trans hpost)
        subst rec
        rcases hbase.gammaUpdate.parentPre with ⟨pgr, hp, _hgen, _hver, _hroot⟩
        refine ⟨parent, q, rfl, hbase, ⟨pgr, hp⟩, hbase.gammaUpdate.parentLink, ?_, ?_, ?_, hbase.budgetUpdate⟩
        · exact hbase.gammaUpdate.permissionGuard pgr hp
        · exact hbase.gammaUpdate.validityGuard
        · exact hbase.gammaUpdate.delegabilityGuard
      · have hgamma : t.gamma g = s.gamma g := hbase.gammaUpdate.preserveOther g hc
        have hsg : s.gamma g = some gr := hgamma.symm.trans hpost
        have hbad : (none : Option GrantRecord) = some gr := hpre.symm.trans hsg
        cases hbad
  | revoke g0 =>
      change Revoke s t g0 at hbase
      by_cases hg : g = g0
      · subst g0
        rcases hbase.gammaUpdate.pre with ⟨old, hold⟩
        have hbad : (none : Option GrantRecord) = some old := hpre.symm.trans hold
        cases hbad
      · have hgamma : t.gamma g = s.gamma g := hbase.gammaUpdate.preserveOther g hg
        have hsg : s.gamma g = some gr := hgamma.symm.trans hpost
        have hbad : (none : Option GrantRecord) = some gr := hpre.symm.trans hsg
        cases hbad
  | selfAttenuate g0 q =>
      change SelfAttenuate s t g0 q at hbase
      by_cases hg : g = g0
      · subst g0
        rcases hbase.gammaUpdate.post with ⟨old, _new, hold, _⟩
        have hbad : (none : Option GrantRecord) = some old := hpre.symm.trans hold
        cases hbad
      · have hgamma : t.gamma g = s.gamma g := hbase.gammaUpdate.preserveOther g hg
        have hsg : s.gamma g = some gr := hgamma.symm.trans hpost
        have hbad : (none : Option GrantRecord) = some gr := hpre.symm.trans hsg
        cases hbad
  | updatePolicy cls newPolicy mid =>
      change UpdatePolicy cls s t newPolicy mid at hbase
      exact False.elim (noNew_of_gammaEq hbase.gammaSame hpre hpost)
  | expireReservation k g0 q refund burned now =>
      change ExpireReservation s t k g0 q refund burned now at hbase
      exact False.elim (noNew_of_gammaEq hbase.same.gamma hpre hpost)
  | expireGrant g0 now =>
      change ExpireGrant s t g0 now at hbase
      exact False.elim (noNew_of_gammaEq hbase.gammaSame hpre hpost)

end EffectKernel.PhaseD
