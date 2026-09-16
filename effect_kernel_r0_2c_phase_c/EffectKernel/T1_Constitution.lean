import EffectKernel.T9_Lifecycle

namespace EffectKernel

private theorem holds_of_preserved {s t : State}
    (hc : t.constitution = s.constitution)
    (hg : t.governance = s.governance)
    (hs : ConstitutionHolds s) : ConstitutionHolds t := by
  unfold ConstitutionHolds at hs ⊢
  rw [hc, hg]
  exact hs

/-- One-step constitutional preservation is derived from actual component equations.
The only policy-writing transition, UPDATE_POLICY (ordinary or positive E2+
classification), uses the frozen successor-policy constitutional guard. -/
theorem trustedStep_constitution_one {s t : State} {kind : TransitionKind}
    (hs : TrustedStep kind s t) (hholds : ConstitutionHolds s) :
    t.constitution = s.constitution ∧ ConstitutionHolds t := by
  cases hs with
  | prepare h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | commitStart h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | commitSuccess h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | commitAbort h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | commitFaultUnknown h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | reconcile h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | delegate h =>
      exact ⟨h.constitutionSame,
        holds_of_preserved h.constitutionSame h.governanceSame hholds⟩
  | revoke h =>
      exact ⟨h.constitutionSame,
        holds_of_preserved h.constitutionSame h.governanceSame hholds⟩
  | selfAttenuate h =>
      exact ⟨h.constitutionSame,
        holds_of_preserved h.constitutionSame h.governanceSame hholds⟩
  | updatePolicy h =>
      constructor
      · exact h.constitutionSame
      · unfold ConstitutionHolds
        rw [h.constitutionSame, h.governancePost]
        exact h.constitutionalGuard
  | expireReservation h =>
      exact ⟨h.same.constitution,
        holds_of_preserved h.same.constitution h.same.governance hholds⟩
  | expireGrant h =>
      exact ⟨h.constitutionSame,
        holds_of_preserved h.constitutionSame h.governanceSame hholds⟩

/-- T1 — within a fixed theorem epoch every reachable policy satisfies the fixed
constitution. E3 is an explicit theorem-epoch boundary (`ReprovisionTCB`) and is
not an in-epoch TrustedStep. -/
theorem T1_constitution {s0 s : State}
    (h0wf : WellFormed s0)
    (h0 : ConstitutionHolds s0)
    (hr : ReachableFrom s0 s) :
    s.constitution = s0.constitution ∧ ConstitutionHolds s := by
  clear h0wf
  induction hr with
  | refl => exact ⟨rfl, h0⟩
  | step hr hs ih =>
      rcases ih with ⟨hconst, hhold⟩
      rcases trustedStep_constitution_one hs hhold with ⟨hstepConst, hstepHold⟩
      exact ⟨hstepConst.trans hconst, hstepHold⟩

end EffectKernel
