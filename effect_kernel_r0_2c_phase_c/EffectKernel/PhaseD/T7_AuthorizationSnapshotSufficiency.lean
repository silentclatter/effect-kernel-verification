import EffectKernel.PhaseD.T6_UniqueAuthorizationLinearization

namespace EffectKernel.PhaseD

open EffectKernel

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
PREPARE/COMMIT_START/EXPIRE_RESERVATION on the same key are rejected by their
actual lifecycle source-state equations, not by a snapshot certificate. -/
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

/-- A linearization occurrence fixes the same binding at the terminal state of
its containing trace.  This is proved by following the actual later full steps. -/
private theorem snapshot_binding_at_terminal
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    {j now : Nat} {before after : State}
    (ho : StepAt h j (.commitStart k now) before after) :
    PostLinearized (z.lifecycle k).state ∧
    SnapshotBinding (snapshotOf before k now) z := by
  induction h generalizing j now before after with
  | refl =>
      cases ho
  | @step s t lbl hp hsEnd ih =>
      cases ho with
      | last hp0 hs0 =>
          have hpost : PostLinearized (t.lifecycle k).state := by
            rw [hs0.base.lifecycleUpdate.update.postState]
            trivial
          have hbind : SnapshotBinding (snapshotOf s k now) t := by
            simpa [SnapshotBinding, snapshotOf] using
              hs0.base.lifecycleUpdate.update.binding
          exact ⟨hpost, hbind⟩
      | earlier hsEnd0 hop =>
          rcases ih hop with ⟨hpostS, hbindS⟩
          have hpostT : PostLinearized (t.lifecycle k).state :=
            fullStep_preserves_postLinearized hsEnd hpostS
          have hstepBind : SameEffectBinding (s.lifecycle k) (t.lifecycle k) :=
            fullStep_preserves_binding_after_linearization hsEnd hpostS
          have hbindT : SnapshotBinding (snapshotOf before k now) t := by
            exact sameEffectBinding_trans hbindS hstepBind
          exact ⟨hpostT, hbindT⟩

/-- Any strictly later full-step occurrence has both endpoints bound to the
snapshot from the unique earlier COMMIT_START. -/
private theorem snapshot_binding_at_later_step
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    {j now : Nat} {before after : State}
    (hlin : StepAt h j (.commitStart k now) before after)
    {i : Nat} {lbl : StepLabel} {a b : State}
    (hlater : StepAt h i lbl a b)
    (hji : j < i) :
    SnapshotBinding (snapshotOf before k now) a ∧
    SnapshotBinding (snapshotOf before k now) b := by
  induction h generalizing j now before after i lbl a b with
  | refl =>
      cases hlin
  | @step s t lblEnd hp hsEnd ih =>
      cases hlin with
      | last hpLin hsLin =>
          cases hlater with
          | last hpLater hsLater =>
              exact False.elim (Nat.lt_irrefl _ hji)
          | earlier hsLater hprev =>
              have hiLt : i < hp.length := StepAt.index_lt_length hprev
              exact False.elim ((Nat.lt_asymm hji) hiLt)
      | earlier hsLin hlinPrev =>
          cases hlater with
          | earlier hsLater hlaterPrev =>
              exact ih hlinPrev hlaterPrev hji
          | last hpLater hsLater =>
              rcases snapshot_binding_at_terminal hlinPrev with
                ⟨hpostS, hbindS⟩
              have hstepBind : SameEffectBinding (s.lifecycle k) (t.lifecycle k) :=
                fullStep_preserves_binding_after_linearization hsEnd hpostS
              have hbindT : SnapshotBinding (snapshotOf before k now) t := by
                exact sameEffectBinding_trans hbindS hstepBind
              exact ⟨hbindS, hbindT⟩

/-- T7 — Authorization Snapshot Sufficiency.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

At the unique COMMIT_START linearization, authorization is evaluated from the
actual predecessor trusted state and is extensionally identical to evaluation
from `snapshotOf` that predecessor. The Phase-C binding projection is preserved
at both endpoints of every strictly later trusted step; later mutable trusted
state is not consulted to re-evaluate the frozen authorization. -/
theorem T7_authorizationSnapshotSufficiency
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false)
    {j now : Nat} {before after : State}
    (ho : StepAt h j (.commitStart k now) before after) :
    (∀ {i now' : Nat} {a b : State},
      StepAt h i (.commitStart k now') a b → i = j) ∧
    (AuthorizedAt E now before k ↔
      AuthorizedFromSnapshot E (snapshotOf before k now)) ∧
    AuthorizedFromSnapshot E (snapshotOf before k now) ∧
    SnapshotBinding (snapshotOf before k now) after ∧
    (∀ {i : Nat} {lbl : StepLabel} {a b : State},
      StepAt h i lbl a b → j < i →
        SnapshotBinding (snapshotOf before k now) a ∧
        SnapshotBinding (snapshotOf before k now) b) := by
  have hs : FullStep E (.commitStart k now) before after := StepAt.fullStep ho
  have hauth : AuthorizedAt E now before k := by
    simpa [FullGuard] using hs.guard
  have hequiv : AuthorizedAt E now before k ↔
      AuthorizedFromSnapshot E (snapshotOf before k now) := by
    exact authorizedAt_snapshot_iff E before k now
  have hsnap : AuthorizedFromSnapshot E (snapshotOf before k now) :=
    hequiv.mp hauth
  have hbind : SnapshotBinding (snapshotOf before k now) after := by
    simpa [SnapshotBinding, snapshotOf] using hs.base.lifecycleUpdate.update.binding
  have huniq :=
    (T6_uniqueAuthorizationLinearization
      (E := E) (s0 := s0) (z := z) (h := h) (k := k)
      hinitState hinitUsed).1
  refine ⟨?_, hequiv, hsnap, hbind, ?_⟩
  · intro i now' a b hi
    exact huniq hi ho
  · intro i lbl a b hi hji
    exact snapshot_binding_at_later_step ho hi hji

end EffectKernel.PhaseD
