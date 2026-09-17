import EffectKernel.PhaseD.T7_AuthorizationSnapshotSufficiency
import EffectKernel.PhaseD.T11_ReplayExclusionNonResurrection

namespace EffectKernel.PhaseD

open EffectKernel

/-- Proof view of every authorization-relevant binding named by the R1 T14
statement.  It is derived from the existing lifecycle record and immutable
semantic decoder; it is not trusted runtime state. -/
structure AuthorizationBoundDescriptor where
  effectKey : EffectKey
  effectAstId : Nat
  canonicalEffect : CanonicalEffect
  subject : SubjectID
  grantId : GrantID
  grantVersion : Nat
  policyVersion : Nat
  tcid : TCID
  reserved : BudgetDim → Nat
  expiry : Nat

/-- Canonical descriptor bound to one effect key in one trusted state. -/
def boundDescriptor (E : FullEnv) (k : EffectKey) (s : State) :
    AuthorizationBoundDescriptor where
  effectKey := k
  effectAstId := (s.lifecycle k).effectAstId
  canonicalEffect := E.decodeEffect (s.lifecycle k).effectAstId
  subject := (s.lifecycle k).subject
  grantId := (s.lifecycle k).grantId
  grantVersion := (s.lifecycle k).grantVersion
  policyVersion := (s.lifecycle k).policyVersion
  tcid := (s.lifecycle k).tcid
  reserved := (s.lifecycle k).reserved
  expiry := (s.lifecycle k).expiry

private theorem sameEffectBinding_refl_T14 (r : LifecycleRecord) :
    SameEffectBinding r r := by
  simp [SameEffectBinding]

private theorem sameEffectBinding_trans_T14 {a b c : LifecycleRecord}
    (hab : SameEffectBinding a b) (hbc : SameEffectBinding b c) :
    SameEffectBinding a c := by
  rcases hab with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  rcases hbc with ⟨j1,j2,j3,j4,j5,j6,j7,j8⟩
  exact ⟨h1.trans j1, h2.trans j2, h3.trans j3, h4.trans j4,
    h5.trans j5, h6.trans j6, h7.trans j7, h8.trans j8⟩

private theorem sameEffectBinding_of_eq_T14 {a b : LifecycleRecord}
    (h : b = a) : SameEffectBinding a b := by
  rw [h]
  exact sameEffectBinding_refl_T14 a

/-- Exact correspondence bridge from the Phase-C binding relation to the R1
canonical descriptor. Equality of the raw effect-AST identity forces equality
of the decoded operation/effect-class/target/parameter/cap/payload/state-binding/
adapter tuple as well as every lifecycle authorization identifier and reserve. -/
theorem sameEffectBinding_boundDescriptor_eq
    (E : FullEnv) (k : EffectKey) {s t : State}
    (h : SameEffectBinding (s.lifecycle k) (t.lifecycle k)) :
    boundDescriptor E k s = boundDescriptor E k t := by
  rcases h with ⟨heffect,hsubject,hgrant,hgrantVersion,hpolicy,htcid,hreserved,hexpiry⟩
  unfold boundDescriptor
  cases heffect
  cases hsubject
  cases hgrant
  cases hgrantVersion
  cases hpolicy
  cases htcid
  cases hreserved
  cases hexpiry
  rfl

/-- Once a key is used, every actual full step preserves its authorization-bound
record for that key. A second PREPARE on the same key is impossible because its
real source relation requires `used = false`; no no-substitution certificate is
added to the transition. -/
private theorem fullStep_preserves_binding_of_used_T14
    {E : FullEnv} {lbl : StepLabel} {s t : State} {k : EffectKey}
    (h : FullStep E lbl s t) (hused : (s.lifecycle k).used = true) :
    SameEffectBinding (s.lifecycle k) (t.lifecycle k) := by
  rcases h with ⟨hbase, _hguard, _hmeta⟩
  cases lbl with
  | prepare k0 g q now =>
      change Prepare s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        have hfresh := hbase.lifecycleUpdate.preUnused
        rw [hused] at hfresh
        cases hfresh
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitStart k0 now =>
      change CommitStart s t k0 at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.update.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.update.other k (Ne.symm hk))
  | commitSuccess k0 g q refund spent =>
      change CommitSuccess s t k0 g q refund spent at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitAbort k0 g q refund burned =>
      change CommitAbort s t k0 g q refund burned at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitFaultUnknown k0 g q =>
      change CommitFaultUnknown s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | reconcile k0 g outcome =>
      change Reconcile s t k0 g outcome at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | delegate parent child rec q =>
      change Delegate s t parent child rec q at hbase
      exact sameEffectBinding_of_eq_T14 (congrFun hbase.lifecycleSame k)
  | revoke g =>
      change Revoke s t g at hbase
      exact sameEffectBinding_of_eq_T14 (congrFun hbase.lifecycleSame k)
  | selfAttenuate g q =>
      change SelfAttenuate s t g q at hbase
      exact sameEffectBinding_of_eq_T14 (congrFun hbase.lifecycleSame k)
  | updatePolicy cls newPolicy mid =>
      change UpdatePolicy cls s t newPolicy mid at hbase
      exact sameEffectBinding_of_eq_T14 (congrFun hbase.lifecycleSame k)
  | expireReservation k0 g q refund burned now =>
      change ExpireReservation s t k0 g q refund burned now at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq_T14
          (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | expireGrant g now =>
      change ExpireGrant s t g now at hbase
      exact sameEffectBinding_of_eq_T14 (congrFun hbase.lifecycleSame k)

private theorem fullTrace_preserves_binding_from_used_T14
    {E : FullEnv} {s t : State} {k : EffectKey}
    (h : FullTrace E s t) (hused : (s.lifecycle k).used = true) :
    SameEffectBinding (s.lifecycle k) (t.lifecycle k) := by
  induction h with
  | refl => exact sameEffectBinding_refl_T14 _
  | @step p u lbl hp hs ih =>
      have husedP : (p.lifecycle k).used = true :=
        fullTrace_used_monotone hp k hused
      exact sameEffectBinding_trans_T14 ih
        (fullStep_preserves_binding_of_used_T14 hs husedP)

/-- Prepend one already-admitted full step to a later full trace. This is proof
infrastructure only; it does not add a transition kind or trusted state. -/
private def prependFullStep
    {E : FullEnv} {s t u : State} {lbl : StepLabel}
    (hs : FullStep E lbl s t) : FullTrace E t u → FullTrace E s u
  | .refl => .step .refl hs
  | .step hp hn => .step (prependFullStep hs hp) hn

/-- T14 — Exact Effect Binding.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

Once PREPARE binds a canonical authorization-relevant descriptor for effect key
`k`, every later actual full step preserves that exact descriptor: raw effect AST
identity and its decoded operation/effect class/target/parameters/cap/payload/
state-binding/adapter meaning, subject, grant/version, policy/version, TCID,
reserved budget, expiry, and the fixed effect key. At any later COMMIT_START the
same descriptor is bound to the immutable T7 authorization snapshot. T11 rules
out obtaining a second fresh PREPARE for the same key; a changed descriptor must
therefore use a distinct fresh effect identity/admission.

No dispatcher-fidelity or physical-world equality claim is made here. -/
theorem T14_exactEffectBinding
    {E : FullEnv} {s t u : State} {k : EffectKey} {g : GrantID}
    {q : BudgetDim → Nat} {prepNow : Nat}
    (hprep : FullStep E (.prepare k g q prepNow) s t)
    (hlater : FullTrace E t u) :
    (∀ {p v : State} {lbl : StepLabel},
      FullTrace E t p → FullStep E lbl p v →
      boundDescriptor E k t = boundDescriptor E k p ∧
      boundDescriptor E k p = boundDescriptor E k v) ∧
    (∀ {p v : State} {now : Nat},
      FullTrace E t p → FullStep E (.commitStart k now) p v →
      AuthorizedFromSnapshot E (snapshotOf p k now) ∧
      SnapshotBinding (snapshotOf p k now) v ∧
      boundDescriptor E k p = boundDescriptor E k v) ∧
    (∀ {v : State} {g' : GrantID} {q' : BudgetDim → Nat} {now' : Nat},
      FullStep E (.prepare k g' q' now') u v → False) := by
  have hprepBase : Prepare s t k g q := hprep.base
  have husedT : (t.lifecycle k).used = true :=
    hprepBase.lifecycleUpdate.postUsed
  have h11 := T11_replayExclusionNonResurrection hprep hlater
  refine ⟨?_, ?_, h11.2.2.2.1⟩
  · intro p v lbl hprefix hstep
    have hbPrefix : SameEffectBinding (t.lifecycle k) (p.lifecycle k) :=
      fullTrace_preserves_binding_from_used_T14 hprefix husedT
    have husedP : (p.lifecycle k).used = true :=
      fullTrace_used_monotone hprefix k husedT
    have hbStep : SameEffectBinding (p.lifecycle k) (v.lifecycle k) :=
      fullStep_preserves_binding_of_used_T14 hstep husedP
    exact ⟨sameEffectBinding_boundDescriptor_eq E k hbPrefix,
      sameEffectBinding_boundDescriptor_eq E k hbStep⟩
  · intro p v now hprefix hstart
    let hp : FullTrace E s p := prependFullStep hprep hprefix
    let hall : FullTrace E s v := FullTrace.step hp hstart
    have ho : StepAt hall hp.length (.commitStart k now) p v :=
      StepAt.last hp hstart
    have h7 := T7_authorizationSnapshotSufficiency
      (E := E) (s0 := s) (z := v) (h := hall) (k := k)
      hprepBase.lifecycleUpdate.preState hprepBase.lifecycleUpdate.preUnused ho
    have hsnap : AuthorizedFromSnapshot E (snapshotOf p k now) :=
      h7.2.2.1
    have hsnapBind : SnapshotBinding (snapshotOf p k now) v :=
      h7.2.2.2.1
    have hb : SameEffectBinding (p.lifecycle k) (v.lifecycle k) :=
      hstart.base.lifecycleUpdate.update.binding
    exact ⟨hsnap, hsnapBind, sameEffectBinding_boundDescriptor_eq E k hb⟩

end EffectKernel.PhaseD
