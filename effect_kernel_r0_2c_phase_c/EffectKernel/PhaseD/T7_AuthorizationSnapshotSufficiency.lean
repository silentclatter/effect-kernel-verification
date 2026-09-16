import EffectKernel.PhaseD.T6_UniqueAuthorizationLinearization

namespace EffectKernel.PhaseD

open EffectKernel

/-- Extract the actual continuation after an observed step. This is proof-only
trace structure; no runtime state or transition is added. -/
private def suffixFromStepAt
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {lbl : StepLabel} {a b : State}
    (ho : StepAt h i lbl a b) : FullTrace E b z := by
  induction ho with
  | last hp hs => exact .refl
  | earlier hsEnd ho ih => exact .step ih hsEnd

private theorem sameEffectBinding_refl (r : LifecycleRecord) :
    SameEffectBinding r r := by
  simp [SameEffectBinding]

private theorem sameEffectBinding_trans {a b c : LifecycleRecord}
    (hab : SameEffectBinding a b) (hbc : SameEffectBinding b c) :
    SameEffectBinding a c := by
  rcases hab with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  rcases hbc with ⟨j1,j2,j3,j4,j5,j6,j7,j8⟩
  exact ⟨h1.trans j1, h2.trans j2, h3.trans j3, h4.trans j4,
    h5.trans j5, h6.trans j6, h7.trans j7, h8.trans j8⟩

private theorem sameEffectBinding_of_eq {a b : LifecycleRecord}
    (h : b = a) : SameEffectBinding a b := by
  rw [h]
  exact sameEffectBinding_refl a

private def PostLinearized : LifecycleState → Prop
  | .dispatching => True
  | .committed => True
  | .aborted => True
  | .unknown => True
  | .unseen => False
  | .reserved => False

private theorem postLinearized_edge {a b : LifecycleState}
    (ha : PostLinearized a) (he : LifecycleEdge a b) : PostLinearized b := by
  cases he <;> simp [PostLinearized] at ha ⊢

private theorem postLinearized_reach {a b : LifecycleState}
    (ha : PostLinearized a) (hr : LifecycleReach a b) : PostLinearized b := by
  induction hr with
  | refl => exact ha
  | tail hxy hyz ih => exact postLinearized_edge ih hyz

private theorem fullStep_preserves_postLinearized
    {E : FullEnv} {lbl : StepLabel} {s t : State} {k : EffectKey}
    (h : FullStep E lbl s t) (hp : PostLinearized (s.lifecycle k).state) :
    PostLinearized (t.lifecycle k).state := by
  exact postLinearized_reach hp
    (trustedStep_lifecycle_one (fullStep_to_trusted h) k)

/-- Once `k` is past its authorization linearization, every later full step
preserves the Phase-C `SameEffectBinding` projection for `k`. Attempts to reuse
PREPARE/COMMIT_START/EXPIRE_RESERVATION on the same key are rejected here by the
one-way lifecycle source-state equations, not by a snapshot certificate. -/
private theorem fullStep_preserves_binding_after_linearization
    {E : FullEnv} {lbl : StepLabel} {s t : State} {k : EffectKey}
    (h : FullStep E lbl s t) (hp : PostLinearized (s.lifecycle k).state) :
    SameEffectBinding (s.lifecycle k) (t.lifecycle k) := by
  rcases h with ⟨hbase, _hguard, _hmeta⟩
  cases lbl with
  | prepare k0 g q now =>
      change Prepare s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        have hs : (s.lifecycle k).state = .unseen := hbase.lifecycleUpdate.preState
        rw [hs] at hp
        exact False.elim (by simpa [PostLinearized] using hp)
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitStart k0 now =>
      change CommitStart s t k0 at hbase
      by_cases hk : k0 = k
      · subst k0
        have hs : (s.lifecycle k).state = .reserved :=
          hbase.lifecycleUpdate.update.preState
        rw [hs] at hp
        exact False.elim (by simpa [PostLinearized] using hp)
      · exact sameEffectBinding_of_eq
          (hbase.lifecycleUpdate.update.other k (Ne.symm hk))
  | commitSuccess k0 g q refund spent =>
      change CommitSuccess s t k0 g q refund spent at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitAbort k0 g q refund burned =>
      change CommitAbort s t k0 g q refund burned at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | commitFaultUnknown k0 g q =>
      change CommitFaultUnknown s t k0 g q at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | reconcile k0 g outcome =>
      change Reconcile s t k0 g outcome at hbase
      by_cases hk : k0 = k
      · subst k0
        exact hbase.lifecycleUpdate.binding
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | delegate parent child rec q =>
      change Delegate s t parent child rec q at hbase
      exact sameEffectBinding_of_eq (congrFun hbase.lifecycleSame k)
  | revoke g =>
      change Revoke s t g at hbase
      exact sameEffectBinding_of_eq (congrFun hbase.lifecycleSame k)
  | selfAttenuate g q =>
      change SelfAttenuate s t g q at hbase
      exact sameEffectBinding_of_eq (congrFun hbase.lifecycleSame k)
  | updatePolicy cls newPolicy mid =>
      change UpdatePolicy cls s t newPolicy mid at hbase
      exact sameEffectBinding_of_eq (congrFun hbase.lifecycleSame k)
  | expireReservation k0 g q refund burned now =>
      change ExpireReservation s t k0 g q refund burned now at hbase
      by_cases hk : k0 = k
      · subst k0
        have hs : (s.lifecycle k).state = .reserved := hbase.lifecycleUpdate.preState
        rw [hs] at hp
        exact False.elim (by simpa [PostLinearized] using hp)
      · exact sameEffectBinding_of_eq (hbase.lifecycleUpdate.other k (Ne.symm hk))
  | expireGrant g now =>
      change ExpireGrant s t g now at hbase
      exact sameEffectBinding_of_eq (congrFun hbase.lifecycleSame k)

/-- The snapshot binding is a proof view over the immutable predecessor record;
it is not a field of trusted state. -/
def SnapshotBinding (σ : AuthSnapshot) (s : State) : Prop :=
  SameEffectBinding (σ.predecessor.lifecycle σ.effectKey) (s.lifecycle σ.effectKey)

/-- Along an actual continuation that begins after linearization, every later
step endpoint preserves the same frozen authorization binding. -/
private theorem continuation_snapshot_invariant
    {E : FullEnv} {start z : State} {h : FullTrace E start z}
    {σ : AuthSnapshot}
    (hkey : σ.effectKey = σ.effectKey)
    (hstartPost : PostLinearized (start.lifecycle σ.effectKey).state)
    (hstartBind : SnapshotBinding σ start) :
    SnapshotBinding σ z ∧
    ∀ {i : Nat} {lbl : StepLabel} {a b : State},
      StepAt h i lbl a b → SnapshotBinding σ a ∧ SnapshotBinding σ b := by
  clear hkey
  induction h with
  | refl =>
      constructor
      · exact hstartBind
      · intro i lbl a b ho
        cases ho
  | @step s t lbl hp hs ih =>
      rcases ih with ⟨hbindS, hinv⟩
      have hpostS : PostLinearized (s.lifecycle σ.effectKey).state := by
        exact postLinearized_reach hstartPost
          (trustedStep_lifecycle_one (FullTrace.toReachable hp |> fun hr => by
            cases hr with
            | refl => exact TrustedStep.expireGrant {
                grantExists := by
                  exact ⟨0, by simp [GrantExists]⟩
                constitutionSame := rfl
                governanceSame := rfl
                gammaSame := rfl
                budgetSame := rfl
                lifecycleSame := rfl
                metaAuthSame := rfl
                epochSame := rfl
              }
            | step _ hs0 => exact hs0) σ.effectKey)
      have hstepBind :=
        fullStep_preserves_binding_after_linearization hs hpostS
      have hbindT : SnapshotBinding σ t :=
        sameEffectBinding_trans hbindS hstepBind
      constructor
      · exact hbindT
      · intro i lbl0 a b ho
        cases ho with
        | last hp0 hs0 => exact ⟨hbindS, hbindT⟩
        | earlier hs0 hop => exact hinv hop

/-- T7 — Authorization Snapshot Sufficiency.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

At the unique COMMIT_START linearization, authorization is evaluated from the
actual predecessor trusted state and is extensionally identical to evaluation
from `snapshotOf` that predecessor.  The Phase-C binding projection is then
preserved across every later step in the actual continuation; later mutable
trusted state is not consulted to re-evaluate the frozen authorization. -/
theorem T7_authorizationSnapshotSufficiency
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false)
    {j now : Nat} {before after : State}
    (ho : StepAt h j (.commitStart k now) before after) :
    let σ := snapshotOf before k now
    (∀ {i now' : Nat} {a b : State},
      StepAt h i (.commitStart k now') a b → i = j) ∧
    (AuthorizedAt E now before k ↔ AuthorizedFromSnapshot E σ) ∧
    AuthorizedFromSnapshot E σ ∧
    SnapshotBinding σ after ∧
    (∀ {i : Nat} {lbl : StepLabel} {a b : State},
      StepAt (suffixFromStepAt ho) i lbl a b →
        SnapshotBinding σ a ∧ SnapshotBinding σ b) := by
  let σ := snapshotOf before k now
  have hs : FullStep E (.commitStart k now) before after := StepAt.fullStep ho
  have hauth : AuthorizedAt E now before k := by
    simpa [FullGuard] using hs.guard
  have hequiv : AuthorizedAt E now before k ↔ AuthorizedFromSnapshot E σ := by
    simpa [σ] using authorizedAt_snapshot_iff E before k now
  have hsnap : AuthorizedFromSnapshot E σ := hequiv.mp hauth
  have hbind : SnapshotBinding σ after := by
    simpa [SnapshotBinding, σ, snapshotOf] using hs.base.lifecycleUpdate.update.binding
  have hpost : PostLinearized (after.lifecycle k).state := by
    rw [hs.base.lifecycleUpdate.update.postState]
    trivial
  have hinv := continuation_snapshot_invariant
    (σ := σ) (h := suffixFromStepAt ho) (by rfl) hpost hbind
  have huniq := (T6_uniqueAuthorizationLinearization hinitState hinitUsed).1
  refine ⟨?_, hequiv, hsnap, hbind, ?_⟩
  · intro i now' a b hi
    exact huniq hi ho
  · exact hinv.2

end EffectKernel.PhaseD
