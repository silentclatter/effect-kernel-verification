import EffectKernel.PhaseD.T4_5_TraceHistory

namespace EffectKernel.PhaseD

open EffectKernel

/-- If the successor of a full step is RESERVED for `k`, either that full
lifecycle record was preserved from the predecessor or the step itself is the
PREPARE that created the durable reservation for `k`. -/
private theorem reserved_successor_decompose
    {E : FullEnv} {lbl : StepLabel} {s t : State} {k : EffectKey}
    (h : FullStep E lbl s t)
    (hres : (t.lifecycle k).state = .reserved) :
    ((s.lifecycle k).state = .reserved ∧ t.lifecycle k = s.lifecycle k) ∨
      ∃ g q now,
        lbl = .prepare k g q now ∧
        (t.lifecycle k).state = .reserved ∧
        (t.lifecycle k).grantId = g ∧
        (t.lifecycle k).reserved = q := by
  rcases h with ⟨hbase, _hguard, _hmeta⟩
  cases lbl with
  | prepare k0 g q now =>
      change Prepare s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        exact Or.inr ⟨g, q, now, rfl, hbase.lifecycleUpdate.postState,
          hbase.lifecycleUpdate.postGrant, hbase.lifecycleUpdate.postReserve⟩
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | commitStart k0 now =>
      change CommitStart s t k0 at hbase
      by_cases hk : k0 = k
      · subst k0
        have hstate : (t.lifecycle k).state = .dispatching :=
          hbase.lifecycleUpdate.update.postState
        rw [hres] at hstate
        cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.update.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | commitSuccess k0 g q refund spent =>
      change CommitSuccess s t k0 g q refund spent at hbase
      by_cases hk : k0 = k
      · subst k0
        have hstate : (t.lifecycle k).state = .committed := hbase.lifecycleUpdate.postState
        rw [hres] at hstate
        cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | commitAbort k0 g q refund burned =>
      change CommitAbort s t k0 g q refund burned at hbase
      by_cases hk : k0 = k
      · subst k0
        have hstate : (t.lifecycle k).state = .aborted := hbase.lifecycleUpdate.postState
        rw [hres] at hstate
        cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | commitFaultUnknown k0 g q =>
      change CommitFaultUnknown s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        have hstate : (t.lifecycle k).state = .unknown := hbase.lifecycleUpdate.postState
        rw [hres] at hstate
        cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | reconcile k0 g outcome =>
      change Reconcile s t k0 g outcome at hbase
      by_cases hk : k0 = k
      · subst k0
        cases outcome with
        | unknown =>
            have hstate : (t.lifecycle k).state = .unknown := hbase.lifecycleUpdate.postState
            rw [hres] at hstate
            cases hstate
        | committed =>
            have hstate : (t.lifecycle k).state = .committed := hbase.lifecycleUpdate.postState
            rw [hres] at hstate
            cases hstate
        | aborted =>
            have hstate : (t.lifecycle k).state = .aborted := hbase.lifecycleUpdate.postState
            rw [hres] at hstate
            cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | delegate parent child rec q =>
      change Delegate s t parent child rec q at hbase
      have heq : t.lifecycle k = s.lifecycle k := congrFun hbase.lifecycleSame k
      exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | revoke g =>
      change Revoke s t g at hbase
      have heq : t.lifecycle k = s.lifecycle k := congrFun hbase.lifecycleSame k
      exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | selfAttenuate g q =>
      change SelfAttenuate s t g q at hbase
      have heq : t.lifecycle k = s.lifecycle k := congrFun hbase.lifecycleSame k
      exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | updatePolicy cls newPolicy mid =>
      change UpdatePolicy cls s t newPolicy mid at hbase
      have heq : t.lifecycle k = s.lifecycle k := congrFun hbase.lifecycleSame k
      exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | expireReservation k0 g q refund burned now =>
      change ExpireReservation s t k0 g q refund burned now at hbase
      by_cases hk : k0 = k
      · subst k0
        have hstate : (t.lifecycle k).state = .aborted := hbase.lifecycleUpdate.postState
        rw [hres] at hstate
        cases hstate
      · have heq : t.lifecycle k = s.lifecycle k :=
          hbase.lifecycleUpdate.other k (Ne.symm hk)
        exact Or.inl ⟨by simpa [heq] using hres, heq⟩
  | expireGrant g now =>
      change ExpireGrant s t g now at hbase
      have heq : t.lifecycle k = s.lifecycle k := congrFun hbase.lifecycleSame k
      exact Or.inl ⟨by simpa [heq] using hres, heq⟩

/-- A RESERVED terminal record for an initially fresh key has an actual PREPARE
origin in the trace, and the full reserved lifecycle record is unchanged from
that PREPARE successor to the terminal RESERVED state. -/
private theorem reserved_has_prepare
    {E : FullEnv} {s0 s : State} {h : FullTrace E s0 s} {k : EffectKey}
    (hinit : (s0.lifecycle k).state = .unseen)
    (hres : (s.lifecycle k).state = .reserved) :
    ∃ i g q now a b,
      StepAt h i (.prepare k g q now) a b ∧
      i < h.length ∧
      (b.lifecycle k).state = .reserved ∧
      (b.lifecycle k).grantId = g ∧
      (b.lifecycle k).reserved = q ∧
      s.lifecycle k = b.lifecycle k := by
  induction h with
  | refl =>
      rw [hinit] at hres
      cases hres
  | @step p t lbl hp hs ih =>
      rcases reserved_successor_decompose hs hres with hkeep | hprep
      · rcases hkeep with ⟨hprevRes, heq⟩
        rcases ih hprevRes with ⟨i, g, q, now, a, b, ho, hlt, hbstate,
          hbgrant, hbres, hpEq⟩
        refine ⟨i, g, q, now, a, b, StepAt.earlier hs ho, ?_, hbstate,
          hbgrant, hbres, ?_⟩
        · exact Nat.lt_trans hlt (by simp [FullTrace.length])
        · exact heq.trans hpEq
      · rcases hprep with ⟨g, q, now, hlbl, htstate, htgrant, htres⟩
        subst lbl
        refine ⟨hp.length, g, q, now, p, t, StepAt.last hp hs, ?_, htstate,
          htgrant, htres, rfl⟩
        simp [FullTrace.length]

/-- T5 — Reservation Precedes Release.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

For an initially fresh effect key, every protected release observed in a full
in-epoch trace is a COMMIT_START whose predecessor is the durable RESERVED
record created by an earlier PREPARE for that same key and reservation vector. -/
theorem T5_reservationPrecedesRelease
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false)
    {j : Nat} {lbl : StepLabel} {before after : State}
    (ho : StepAt h j lbl before after)
    (hrelease : ProtectedRelease lbl k) :
    ∃ i g q prepNow releaseNow prepBefore prepAfter,
      i < j ∧
      StepAt h i (.prepare k g q prepNow) prepBefore prepAfter ∧
      lbl = .commitStart k releaseNow ∧
      (prepAfter.lifecycle k).state = .reserved ∧
      (prepAfter.lifecycle k).grantId = g ∧
      (prepAfter.lifecycle k).reserved = q ∧
      before.lifecycle k = prepAfter.lifecycle k ∧
      (after.lifecycle k).state = .dispatching ∧
      (after.lifecycle k).linearized = true := by
  clear hinitUsed
  induction ho with
  | @last p t lbl hp hs =>
      cases hrelease with
      | commitStart _ releaseNow =>
          change FullStep E (.commitStart k releaseNow) p t at hs
          have hpred : (p.lifecycle k).state = .reserved :=
            hs.base.lifecycleUpdate.update.preState
          rcases reserved_has_prepare hinitState hpred with
            ⟨i, g, q, prepNow, prepBefore, prepAfter, hprep, hlt,
              hpstate, hpgrant, hpres, hpEq⟩
          refine ⟨i, g, q, prepNow, releaseNow, prepBefore, prepAfter,
            hlt, StepAt.earlier hs hprep, rfl, hpstate, hpgrant, hpres,
            hpEq, hs.base.lifecycleUpdate.update.postState,
            hs.base.lifecycleUpdate.postLinearized⟩
  | @earlier p t lblEnd hp hsEnd i lbl a b ho ih =>
      rcases ih hrelease with
        ⟨ip, g, q, prepNow, releaseNow, prepBefore, prepAfter,
          hlt, hprep, hlbl, hpstate, hpgrant, hpres, hbefore,
          hafterState, hafterLin⟩
      exact ⟨ip, g, q, prepNow, releaseNow, prepBefore, prepAfter,
        hlt, StepAt.earlier hsEnd hprep, hlbl, hpstate, hpgrant, hpres,
        hbefore, hafterState, hafterLin⟩

end EffectKernel.PhaseD
