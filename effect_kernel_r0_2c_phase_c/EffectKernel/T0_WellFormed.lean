import EffectKernel.Reachability

namespace EffectKernel

private theorem option_some_inj {α : Type} {a b : α} (h : some a = some b) : a = b := by
  cases h
  rfl

private theorem grantExists_of_gamma_eq {s t : State} (h : t.gamma = s.gamma) {g : GrantID}
    (hex : GrantExists s g) : GrantExists t g := by
  rcases hex with ⟨gr, hgr⟩
  refine ⟨gr, ?_⟩
  rw [h]
  exact hgr

private theorem grantWF_gamma_eq {s t : State} (h : t.gamma = s.gamma)
    (hw : GrantWellFormed s) : GrantWellFormed t := by
  constructor
  · intro g gr htg
    have hsg : s.gamma g = some gr := by
      rw [← h]
      exact htg
    exact hw.interval_ok g gr hsg
  · intro g gr htg hroot
    have hsg : s.gamma g = some gr := by
      rw [← h]
      exact htg
    exact hw.root_ok g gr hsg hroot
  · intro g gr p htg hparent
    have hsg : s.gamma g = some gr := by
      rw [← h]
      exact htg
    rcases hw.parent_ok g gr p hsg hparent with ⟨pgr, hp, hgen, hpv, hroot⟩
    refine ⟨pgr, ?_, hgen, hpv, hroot⟩
    rw [h]
    exact hp

private theorem budgetOwners_one_changed {s t : State} {g : GrantID}
    (hgamma : t.gamma = s.gamma)
    (hex : GrantExists s g)
    (hother : ∀ x, x ≠ g → t.budget x = s.budget x)
    (hw : BudgetOwnersWellFormed s) : BudgetOwnersWellFormed t := by
  intro x d hpos
  by_cases hx : x = g
  · subst x
    exact grantExists_of_gamma_eq hgamma hex
  · have hspos : (s.budget x d).total > 0 := by
      rw [← hother x hx]
      exact hpos
    exact grantExists_of_gamma_eq hgamma (hw x d hspos)

private theorem budgetOwners_same {s t : State}
    (hgamma : t.gamma = s.gamma) (hbudget : t.budget = s.budget)
    (hw : BudgetOwnersWellFormed s) : BudgetOwnersWellFormed t := by
  intro g d hpos
  have hspos : (s.budget g d).total > 0 := by
    rw [← hbudget]
    exact hpos
  exact grantExists_of_gamma_eq hgamma (hw g d hspos)

private theorem delegate_grantWF {s t : State} {parent child : GrantID} {rec : GrantRecord}
    (hd : DelegateGamma s t parent child rec) (hw : GrantWellFormed s) : GrantWellFormed t := by
  have hpc : parent ≠ child := by
    intro h
    subst parent
    rcases hd.parentPre with ⟨pgr, hp, _⟩
    rw [hd.fresh] at hp
  constructor
  · intro g gr htg
    by_cases hgc : g = child
    · subst g
      have heq : gr = rec := option_some_inj (htg.symm.trans hd.childPost)
      subst gr
      exact hd.intervalOk
    · have hsg : s.gamma g = some gr := by
        rw [← hd.preserveOther g hgc]
        exact htg
      exact hw.interval_ok g gr hsg
  · intro g gr htg hroot
    by_cases hgc : g = child
    · subst g
      have heq : gr = rec := option_some_inj (htg.symm.trans hd.childPost)
      subst gr
      rw [hd.parentLink] at hroot
    · have hsg : s.gamma g = some gr := by
        rw [← hd.preserveOther g hgc]
        exact htg
      exact hw.root_ok g gr hsg hroot
  · intro g gr p htg hparent
    by_cases hgc : g = child
    · subst g
      have heq : gr = rec := option_some_inj (htg.symm.trans hd.childPost)
      subst gr
      have hpEq : p = parent := by
        exact option_some_inj (hparent.symm.trans hd.parentLink)
      subst p
      rcases hd.parentPre with ⟨pgr, hp, hgen, hpv, hrootEq⟩
      refine ⟨pgr, ?_, hgen, hpv, hrootEq⟩
      rw [hd.preserveOther parent hpc]
      exact hp
    · have hsg : s.gamma g = some gr := by
        rw [← hd.preserveOther g hgc]
        exact htg
      rcases hw.parent_ok g gr p hsg hparent with ⟨pgr, hp, hgen, hpv, hrootEq⟩
      have hpc' : p ≠ child := by
        intro h
        subst p
        rw [hd.fresh] at hp
      refine ⟨pgr, ?_, hgen, hpv, hrootEq⟩
      rw [hd.preserveOther p hpc']
      exact hp

private theorem delegate_budgetOwners {s t : State} {parent child : GrantID} {rec : GrantRecord}
    {q : BudgetDim → Nat}
    (hdg : DelegateGamma s t parent child rec)
    (hdb : DelegateBudget s t parent child q)
    (hw : BudgetOwnersWellFormed s) : BudgetOwnersWellFormed t := by
  have hpc : parent ≠ child := by
    intro h
    subst parent
    rcases hdg.parentPre with ⟨pgr, hp, _⟩
    rw [hdg.fresh] at hp
  intro g d hpos
  by_cases hgp : g = parent
  · subst g
    rcases hdg.parentPre with ⟨pgr, hp, _⟩
    refine ⟨pgr, ?_⟩
    rw [hdg.preserveOther parent hpc]
    exact hp
  · by_cases hgc : g = child
    · subst g
      exact ⟨rec, hdg.childPost⟩
    · have hspos : (s.budget g d).total > 0 := by
        rw [← hdb.other g hgp hgc]
        exact hpos
      rcases hw g d hspos with ⟨gr, hgr⟩
      refine ⟨gr, ?_⟩
      rw [hdg.preserveOther g hgc]
      exact hgr

private theorem revoke_grantWF {s t : State} {g : GrantID}
    (hr : RevokeGamma s t g) (hw : GrantWellFormed s) : GrantWellFormed t := by
  rcases hr.post with ⟨old, new, hsold, htnew, hroot, hpar, hpv, hgen, _hver,
    _hsub, _hperm, hvalid, _hdel, _hactive⟩
  have hne_parent : ∀ p, old.parent = some p → p ≠ g := by
    intro p hp hpg
    subst p
    rcases hw.parent_ok g old g hsold hp with ⟨pgr, hpgamma, hlt, _⟩
    have heq : pgr = old := option_some_inj (hpgamma.symm.trans hsold)
    subst pgr
    exact (Nat.lt_irrefl _ hlt)
  constructor
  · intro x gr htx
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      rw [hvalid]
      exact hw.interval_ok g old hsold
    · have hsx : s.gamma x = some gr := by
        rw [← hr.preserveOther x hx]
        exact htx
      exact hw.interval_ok x gr hsx
  · intro x gr htx hnone
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      have holdnone : old.parent = none := by
        rw [← hpar]
        exact hnone
      have holdroot := hw.root_ok g old hsold holdnone
      exact hroot.trans holdroot
    · have hsx : s.gamma x = some gr := by
        rw [← hr.preserveOther x hx]
        exact htx
      exact hw.root_ok x gr hsx hnone
  · intro x gr p htx hparent
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      have holdpar : old.parent = some p := by
        rw [← hpar]
        exact hparent
      rcases hw.parent_ok g old p hsold holdpar with ⟨pgr, hp, hlt, hpver, hrootEq⟩
      have hpg : p ≠ g := hne_parent p holdpar
      refine ⟨pgr, ?_, ?_, ?_, ?_⟩
      · rw [hr.preserveOther p hpg]
        exact hp
      · rw [hgen]
        exact hlt
      · rw [hpv]
        exact hpver
      · rw [hroot]
        exact hrootEq
    · have hsx : s.gamma x = some gr := by
        rw [← hr.preserveOther x hx]
        exact htx
      rcases hw.parent_ok x gr p hsx hparent with ⟨pgr, hp, hlt, hpver, hrootEq⟩
      have hpg : p ≠ g := by
        intro hpg
        subst p
        rw [hsold] at hp
        have heq : pgr = old := option_some_inj hp
        subst pgr
        have hself : old.parent = some g := hparent
        exact (hne_parent g hself rfl)
      refine ⟨pgr, ?_, hlt, hpver, hrootEq⟩
      rw [hr.preserveOther p hpg]
      exact hp

private theorem attenuate_grantWF {s t : State} {g : GrantID}
    (ha : AttenuateGamma s t g) (hw : GrantWellFormed s) : GrantWellFormed t := by
  rcases ha.post with ⟨old, new, hsold, htnew, hroot, hpar, hpv, hgen, _hsub,
    _hperm, _hsubset, hvalidwf, _hdel, _hactive⟩
  have hne_parent : ∀ p, old.parent = some p → p ≠ g := by
    intro p hp hpg
    subst p
    rcases hw.parent_ok g old g hsold hp with ⟨pgr, hpgamma, hlt, _⟩
    have heq : pgr = old := option_some_inj (hpgamma.symm.trans hsold)
    subst pgr
    exact (Nat.lt_irrefl _ hlt)
  constructor
  · intro x gr htx
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      exact hvalidwf
    · have hsx : s.gamma x = some gr := by
        rw [← ha.preserveOther x hx]
        exact htx
      exact hw.interval_ok x gr hsx
  · intro x gr htx hnone
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      have holdnone : old.parent = none := by
        rw [← hpar]
        exact hnone
      have holdroot := hw.root_ok g old hsold holdnone
      exact hroot.trans holdroot
    · have hsx : s.gamma x = some gr := by
        rw [← ha.preserveOther x hx]
        exact htx
      exact hw.root_ok x gr hsx hnone
  · intro x gr p htx hparent
    by_cases hx : x = g
    · subst x
      have heq : gr = new := option_some_inj (htx.symm.trans htnew)
      subst gr
      have holdpar : old.parent = some p := by
        rw [← hpar]
        exact hparent
      rcases hw.parent_ok g old p hsold holdpar with ⟨pgr, hp, hlt, hpver, hrootEq⟩
      have hpg : p ≠ g := hne_parent p holdpar
      refine ⟨pgr, ?_, ?_, ?_, ?_⟩
      · rw [ha.preserveOther p hpg]
        exact hp
      · rw [hgen]
        exact hlt
      · rw [hpv]
        exact hpver
      · rw [hroot]
        exact hrootEq
    · have hsx : s.gamma x = some gr := by
        rw [← ha.preserveOther x hx]
        exact htx
      rcases hw.parent_ok x gr p hsx hparent with ⟨pgr, hp, hlt, hpver, hrootEq⟩
      have hpg : p ≠ g := by
        intro hpg
        subst p
        rw [hsold] at hp
        have heq : pgr = old := option_some_inj hp
        subst pgr
        have hself : old.parent = some g := hparent
        exact (hne_parent g hself rfl)
      refine ⟨pgr, ?_, hlt, hpver, hrootEq⟩
      rw [ha.preserveOther p hpg]
      exact hp

private theorem budgetOwners_revoke {s t : State} {g : GrantID}
    (hr : RevokeGamma s t g) (hbudget : t.budget = s.budget)
    (hw : BudgetOwnersWellFormed s) : BudgetOwnersWellFormed t := by
  intro x d hpos
  have hspos : (s.budget x d).total > 0 := by
    rw [← hbudget]
    exact hpos
  rcases hw x d hspos with ⟨gr, hgr⟩
  by_cases hx : x = g
  · subst x
    rcases hr.post with ⟨old, new, hsold, htnew, _⟩
    exact ⟨new, htnew⟩
  · exact ⟨gr, by rw [hr.preserveOther x hx]; exact hgr⟩

private theorem budgetOwners_attenuate {s t : State} {g : GrantID} {q : BudgetDim → Nat}
    (ha : AttenuateGamma s t g) (hb : DestroyBudget s t g q)
    (hw : BudgetOwnersWellFormed s) : BudgetOwnersWellFormed t := by
  intro x d hpos
  by_cases hx : x = g
  · subst x
    rcases ha.post with ⟨old, new, hsold, htnew, _⟩
    exact ⟨new, htnew⟩
  · have hspos : (s.budget x d).total > 0 := by
      rw [← hb.other x hx]
      exact hpos
    rcases hw x d hspos with ⟨gr, hgr⟩
    exact ⟨gr, by rw [ha.preserveOther x hx]; exact hgr⟩

/-- T0 one-step preservation is derived by case analysis on the actual frozen
transition semantics. No TrustedStep constructor carries `WellFormed t`. -/
theorem trustedStep_preserves_wf {s t : State} {kind : TransitionKind}
    (hs : TrustedStep kind s t) (hw : WellFormed s) : WellFormed t := by
  cases hs with
  | prepare h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | commitStart h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_same h.same.gamma h.budgetSame hw.budgetOwners⟩
  | commitSuccess h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | commitAbort h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | commitFaultUnknown h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | reconcile h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | delegate h =>
      exact ⟨delegate_grantWF h.gammaUpdate hw.grants,
        delegate_budgetOwners h.gammaUpdate h.budgetUpdate hw.budgetOwners⟩
  | revoke h =>
      exact ⟨revoke_grantWF h.gammaUpdate hw.grants,
        budgetOwners_revoke h.gammaUpdate h.budgetSame hw.budgetOwners⟩
  | selfAttenuate h =>
      exact ⟨attenuate_grantWF h.gammaUpdate hw.grants,
        budgetOwners_attenuate h.gammaUpdate h.budgetUpdate hw.budgetOwners⟩
  | updatePolicy h =>
      cases cls with
      | nonExpanding =>
          have hb : t.budget = s.budget := by
            simpa using h.budgetRule
          exact ⟨grantWF_gamma_eq h.gammaSame hw.grants,
            budgetOwners_same h.gammaSame hb hw.budgetOwners⟩
      | positiveProvision r delta =>
          have hb : ProvisionBudget s t r delta := by
            simpa using h.budgetRule
          exact ⟨grantWF_gamma_eq h.gammaSame hw.grants,
            budgetOwners_one_changed h.gammaSame hb.rootExists hb.other hw.budgetOwners⟩
  | expireReservation h =>
      exact ⟨grantWF_gamma_eq h.same.gamma hw.grants,
        budgetOwners_one_changed h.same.gamma h.grantExists h.budgetUpdate.other hw.budgetOwners⟩
  | expireGrant h =>
      exact ⟨grantWF_gamma_eq h.gammaSame hw.grants,
        budgetOwners_same h.gammaSame h.budgetSame hw.budgetOwners⟩

/-- T0 — every state reachable in one fixed theorem epoch from a structurally
well-formed initial trusted state remains structurally well formed. -/
theorem T0_wellFormed {s0 s : State}
    (h0 : WellFormed s0) (hr : ReachableFrom s0 s) : WellFormed s := by
  induction hr with
  | refl => exact h0
  | step hr hs ih => exact trustedStep_preserves_wf hs ih

/-- Strict generation decrease along ancestry discharges the acyclicity/well-founded
portion of Phase-A WF without placing attenuation in the type. -/
theorem ancestor_generation_decreases {s : State} (hw : WellFormed s)
    {a c : GrantID} (h : Ancestor s a c) :
    ∃ agr cgr, s.gamma a = some agr ∧ s.gamma c = some cgr ∧ agr.generation < cgr.generation := by
  induction h with
  | direct hchild hparent =>
      rcases hw.grants.parent_ok _ _ _ hchild hparent with ⟨pgr, hp, hlt, _⟩
      exact ⟨pgr, _, hp, hchild, hlt⟩
  | extend hprefix hchild hparent ih =>
      rcases ih with ⟨agr, pgr, ha, hp, hap⟩
      rcases hw.grants.parent_ok _ _ _ hchild hparent with ⟨pgr2, hp2, hpc, _⟩
      have heq : pgr2 = pgr := option_some_inj (hp2.symm.trans hp)
      subst pgr2
      exact ⟨agr, _, ha, hchild, Nat.lt_trans hap hpc⟩

theorem ancestor_irrefl {s : State} (hw : WellFormed s) (g : GrantID) : ¬ Ancestor s g g := by
  intro h
  rcases ancestor_generation_decreases hw h with ⟨a, c, ha, hc, hlt⟩
  have heq : a = c := option_some_inj (ha.symm.trans hc)
  subst c
  exact Nat.lt_irrefl _ hlt

end EffectKernel
