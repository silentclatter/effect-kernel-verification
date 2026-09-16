import EffectKernel.T1_Constitution

namespace EffectKernel

/-- Definitional correspondence with the frozen Phase-A five-component order. -/
theorem permission_le_components_iff (p q : Permission) :
    p.le q ↔
      (∀ op, p.ops op → q.ops op) ∧
      (∀ ec, p.effectClasses ec → q.effectClasses ec) ∧
      (∀ x, p.targetPred x → q.targetPred x) ∧
      (∀ a, p.paramPred a → q.paramPred a) ∧
      (∀ ec n, p.perEffectCaps ec n → q.perEffectCaps ec n) := by
  rfl

/-- Arbitrary-depth ancestry composition. The proof is induction over the actual
ancestry derivation, not a bounded depth parameter. -/
theorem ancestor_transitive {s : State} {a p c : GrantID}
    (hap : Ancestor s a p) (hpc : Ancestor s p c) : Ancestor s a c := by
  induction hpc with
  | direct hchild hparent =>
      exact .extend hap hchild hparent
  | extend hprefix hchild hparent ih =>
      exact .extend ih hchild hparent

theorem ancestorOrSelf_lift {s : State} {a p c : GrantID}
    (hap : AncestorOrSelf s a p) (hpc : Ancestor s p c) : AncestorOrSelf s a c := by
  rcases hap with rfl | ha
  · exact Or.inr hpc
  · exact Or.inr (ancestor_transitive ha hpc)

/-- Frozen T0 generation discipline makes every ancestry path strictly descend in
`generation` when followed from child toward ancestor. Since Nat `<` is
well-founded, this is the load-bearing well-foundedness evidence for ancestry. -/
theorem ancestor_generation_descent {s : State} {a c : GrantID}
    (hw : GrantWellFormed s) (hac : Ancestor s a c) :
    ∃ agr cgr,
      s.gamma a = some agr ∧ s.gamma c = some cgr ∧
      agr.generation < cgr.generation := by
  induction hac with
  | direct hchild hparent =>
      rcases hw.parent_ok _ _ _ hchild hparent with ⟨pgr, hp, hlt, _hroot⟩
      exact ⟨pgr, _, hp, hchild, hlt⟩
  | extend hprefix hchild hparent ih =>
      rcases ih with ⟨agr, pgr, ha, hp, haplt⟩
      rcases hw.parent_ok _ _ _ hchild hparent with ⟨pgr', hp', hpclt, _hroot⟩
      have hpeq : pgr' = pgr := by
        have hsome : some pgr' = some pgr := hp'.symm.trans hp
        cases hsome
        rfl
      subst pgr'
      exact ⟨agr, _, ha, hchild, Nat.lt_trans haplt hpclt⟩

/-- No ancestry cycle is compatible with structural well-formedness. -/
theorem ancestor_irrefl_of_wf {s : State} {g : GrantID}
    (hw : GrantWellFormed s) : ¬ Ancestor s g g := by
  intro hgg
  rcases ancestor_generation_descent hw hgg with ⟨agr, ggr, ha, hg, hlt⟩
  have heq : agr = ggr := by
    have hsome : some agr = some ggr := ha.symm.trans hg
    cases hsome
    rfl
  subst ggr
  exact (Nat.lt_irrefl _ hlt)

/-- Immediate child permission attenuation is an actual frozen DELEGATE guard,
not a theorem conclusion stored on TrustedStep. -/
theorem delegate_immediate_permission {s t : State} {parent child : GrantID}
    {rec : GrantRecord}
    (hd : DelegateGamma s t parent child rec) :
    rec.permission.le (P_eff s parent) := by
  rcases hd.parentPre with ⟨pgr, hp, _hgen, _hpv, _hroot⟩
  exact hd.permissionGuard pgr hp

/-- Immediate temporal attenuation is likewise the frozen delegation guard. -/
theorem delegate_immediate_temporal {s t : State} {parent child : GrantID}
    {rec : GrantRecord}
    (hd : DelegateGamma s t parent child rec) :
    ∀ now, rec.validity.Contains now → EffectiveValid s parent now := by
  exact hd.validityGuard

/-- Immediate delegability cannot amplify the effective parent. -/
theorem delegate_immediate_delegability {s t : State} {parent child : GrantID}
    {rec : GrantRecord}
    (hd : DelegateGamma s t parent child rec) :
    rec.delegable = true → EffectiveDelegable s parent := by
  exact hd.delegabilityGuard

/-- Five-component effective permission attenuation for arbitrary ancestry depth. -/
theorem T2_permission {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    (P_eff s c).le (P_eff s p) := by
  unfold Permission.le
  exact ⟨
    (by
      intro op hc a hap
      exact hc a (ancestorOrSelf_lift hap hpc)),
    (by
      intro ec hc a hap
      exact hc a (ancestorOrSelf_lift hap hpc)),
    (by
      intro x hc a hap
      exact hc a (ancestorOrSelf_lift hap hpc)),
    (by
      intro prm hc a hap
      exact hc a (ancestorOrSelf_lift hap hpc)),
    (by
      intro ec n hc a hap
      exact hc a (ancestorOrSelf_lift hap hpc))⟩

/-- Effective temporal validity of a descendant is contained in every ancestor's
validity at every trusted time. -/
theorem T2_temporal {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    ∀ now, EffectiveValid s c now → EffectiveValid s p now := by
  intro now hc a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Effective delegability cannot be broader than an ancestor's. -/
theorem T2_delegability {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    EffectiveDelegable s c → EffectiveDelegable s p := by
  intro hc a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Effective version freshness is ancestry-local and propagates over arbitrary
depth. -/
theorem T2_versionFresh {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    EffectiveVersionFresh s c → EffectiveVersionFresh s p := by
  intro hc child parent hchild hpar
  exact hc child parent (ancestorOrSelf_lift hchild hpc) hpar

/-- Descendant effective activity implies effective activity of every ancestor,
including activity, time validity, and version freshness. -/
theorem T2_effectiveActive {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    ∀ now, EffectiveActive s now c → EffectiveActive s now p := by
  intro now hc
  rcases hc with ⟨hactive, hfresh⟩
  constructor
  · intro a hap
    exact hactive a (ancestorOrSelf_lift hap hpc)
  · exact T2_versionFresh hpc hfresh

/-- A required ancestor that is inactive makes the descendant ineffective. -/
theorem inactive_ancestor_disables_descendant {s : State} {p c : GrantID}
    {pgr : GrantRecord} {now : Nat}
    (hpc : Ancestor s p c) (hp : s.gamma p = some pgr)
    (hinactive : pgr.active = false) :
    ¬ EffectiveActive s now c := by
  intro hc
  rcases hc.1 p (Or.inr hpc) with ⟨gr, hg, hactive, _hvalid⟩
  have heq : gr = pgr := by
    have hsome : some gr = some pgr := hg.symm.trans hp
    cases hsome
    rfl
  subst gr
  simp [hinactive] at hactive

/-- A required ancestor outside its trusted validity interval makes the descendant
ineffective at that trusted time. -/
theorem expired_ancestor_disables_descendant {s : State} {p c : GrantID}
    {pgr : GrantRecord} {now : Nat}
    (hpc : Ancestor s p c) (hp : s.gamma p = some pgr)
    (hexpired : pgr.validity.last < now) :
    ¬ EffectiveActive s now c := by
  intro hc
  rcases hc.1 p (Or.inr hpc) with ⟨gr, hg, _hactive, hvalid⟩
  have heq : gr = pgr := by
    have hsome : some gr = some pgr := hg.symm.trans hp
    cases hsome
    rfl
  subst gr
  exact (Nat.not_le_of_lt hexpired) hvalid.2

/-- A stale required parent-version link cannot serve as a current effective
authorization basis. -/
theorem stale_required_link_disables {s : State} {g child parent : GrantID}
    {now : Nat}
    (hchild : AncestorOrSelf s child g)
    (hparent : Parent s parent child)
    (hstale : ¬ LinkFresh s child parent) :
    ¬ EffectiveActive s now g := by
  intro hc
  exact hstale (hc.2 child parent hchild hparent)

/-- REVOKE derives descendant ineffectiveness from the actual post-state grant
update; it is not a TrustedStep certificate. -/
theorem revoke_ancestor_disables {s t : State} {p c : GrantID} {now : Nat}
    (hr : Revoke s t p) (hpc : Ancestor t p c) :
    ¬ EffectiveActive t now c := by
  rcases hr.gammaUpdate.post with
    ⟨old, new, _hs, ht, _hroot, _hparent, _hpv, _hgen, _hver, _hsubj,
      _hperm, _hvalidity, _hdelegable, hinactive⟩
  exact inactive_ancestor_disables_descendant hpc ht hinactive

/-- EXPIRE_GRANT is semantic under external trusted time: once a required ancestor
is expired at `now`, descendant effective authority is false at `now`. -/
theorem expire_ancestor_disables {s t : State} {p c : GrantID} {now : Nat}
    (he : ExpireGrant s t p now) (hpc : Ancestor t p c) :
    ¬ EffectiveActive t now c := by
  rcases he.grantExists with ⟨pgr, hp, hexpired⟩
  have htp : t.gamma p = some pgr := by
    rw [he.gammaSame]
    exact hp
  exact expired_ancestor_disables_descendant hpc htp hexpired

/-- T2 — Transitive Authority Attenuation. This is arbitrary-depth because every
ancestry lifting used below is proved by induction over the unbounded `Ancestor`
derivation. All five permission components are included, while temporal validity,
delegability, activity and version freshness remain distinct frozen dimensions. -/
theorem T2_transitiveAuthorityAttenuation {s : State} {p c : GrantID}
    (hpc : Ancestor s p c) :
    (P_eff s c).le (P_eff s p) ∧
    (∀ now, EffectiveValid s c now → EffectiveValid s p now) ∧
    (EffectiveDelegable s c → EffectiveDelegable s p) ∧
    (∀ now, EffectiveActive s now c → EffectiveActive s now p) ∧
    (EffectiveVersionFresh s c → EffectiveVersionFresh s p) := by
  exact ⟨T2_permission hpc, T2_temporal hpc, T2_delegability hpc,
    T2_effectiveActive hpc, T2_versionFresh hpc⟩

end EffectKernel
