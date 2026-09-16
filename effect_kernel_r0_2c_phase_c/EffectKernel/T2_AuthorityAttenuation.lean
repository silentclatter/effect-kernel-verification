import EffectKernel.T1_Constitution

namespace EffectKernel

/-- Arbitrary-depth ancestry composition. The proof is induction over the second
ancestry derivation, so it is not bounded to a fixed delegation depth. -/
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

/-- Permission attenuation for arbitrary ancestry depth. -/
theorem T2_permission {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    (P_eff s c).le (P_eff s p) := by
  intro op hc
  intro a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Effective temporal validity of a descendant is contained in every ancestor's
validity at every trusted time. -/
theorem T2_temporal {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    ∀ t, EffectiveValid s c t → EffectiveValid s p t := by
  intro t hc a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Effective delegability cannot be broader than an ancestor's. -/
theorem T2_delegability {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    EffectiveDelegable s c → EffectiveDelegable s p := by
  intro hc a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Revocation or expiry of any required ancestor prevents a descendant from being
effectively active: equivalently, descendant activity implies ancestor activity. -/
theorem T2_effectiveActive {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    EffectiveActive s c → EffectiveActive s p := by
  intro hc a hap
  exact hc a (ancestorOrSelf_lift hap hpc)

/-- Version freshness is ancestry-local and propagates over arbitrary depth: if all
links needed by c are fresh, every link needed by ancestor p is also fresh. -/
def EffectiveVersionFresh (s : State) (g : GrantID) : Prop :=
  ∀ child parent, AncestorOrSelf s child g → Parent s parent child → LinkFresh s child parent

theorem T2_versionFresh {s : State} {p c : GrantID} (hpc : Ancestor s p c) :
    EffectiveVersionFresh s c → EffectiveVersionFresh s p := by
  intro hc child parent hchild hpar
  exact hc child parent (ancestorOrSelf_lift hchild hpc) hpar

/-- Combined T2 statement over all frozen authority dimensions represented by the
Phase C-R abstraction. -/
theorem T2_transitiveAuthorityAttenuation {s : State} {p c : GrantID}
    (hpc : Ancestor s p c) :
    (P_eff s c).le (P_eff s p) ∧
    (∀ t, EffectiveValid s c t → EffectiveValid s p t) ∧
    (EffectiveDelegable s c → EffectiveDelegable s p) ∧
    (EffectiveActive s c → EffectiveActive s p) ∧
    (EffectiveVersionFresh s c → EffectiveVersionFresh s p) := by
  exact ⟨T2_permission hpc, T2_temporal hpc, T2_delegability hpc,
    T2_effectiveActive hpc, T2_versionFresh hpc⟩

end EffectKernel
