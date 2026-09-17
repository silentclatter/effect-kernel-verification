import EffectKernel.PhaseD.T7_AuthorizationSnapshotSufficiency
import EffectKernel.PhaseD.T12_TargetContractIdentityStability

namespace EffectKernel.PhaseD

open EffectKernel

/-- The R1 target-guarantee inclusion obligation evaluated at the trusted
predecessor of the authorization linearization. -/
def RequiredGuaranteesIncluded (E : FullEnv) (s : State) (k : EffectKey) : Prop :=
  let lr := s.lifecycle k
  let a := E.decodeEffect lr.effectAstId
  ∀ r, E.req a s.governance r → E.guarantees lr.tcid r

/-- T13 — Target-Contract Compliance.

For a valid protected release at the unique COMMIT_START linearization of an
initially fresh effect key, the frozen T7 authorization snapshot entails the R1
requirement inclusion `Req(a,G_ell) ⊆ Guarantees(TCID(k))`. T12 supplies the
identity bridge showing that the same TCID is bound on the DISPATCHING successor.
The target-assumption predicate is therefore indexed by that same identity on
both sides of linearization; its truth is not asserted here.

This is an admission-compatibility theorem only. Physical target truth remains a
separate A11/T15 obligation. -/
theorem T13_targetContractCompliance
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false)
    {j now : Nat} {before after : State}
    (ho : StepAt h j (.commitStart k now) before after) :
    AuthorizedFromSnapshot E (snapshotOf before k now) ∧
    RequiredGuaranteesIncluded E before k ∧
    (before.lifecycle k).tcid = (after.lifecycle k).tcid ∧
    E.targetAssumptions (before.lifecycle k).tcid =
      E.targetAssumptions (after.lifecycle k).tcid := by
  have h7 := T7_authorizationSnapshotSufficiency
    (E := E) (s0 := s0) (z := z) (h := h) (k := k)
    hinitState hinitUsed ho
  have hsnap : AuthorizedFromSnapshot E (snapshotOf before k now) :=
    h7.2.2.1
  have hauth : AuthorizedAt E now before k := by
    simpa [AuthorizedFromSnapshot, snapshotOf] using hsnap
  have hinc : RequiredGuaranteesIncluded E before k := by
    rcases hauth with ⟨gr, hgamma, hstate, hused, hepoch, hsubject,
      hversion, hactive, hperm, hconstitution, hpolicy, hexpiry, hguarantees⟩
    simpa [RequiredGuaranteesIncluded] using hguarantees
  have htcid : (before.lifecycle k).tcid = (after.lifecycle k).tcid := by
    exact T12_targetContractIdentityStability
      (E := E) (s := before) (t := after) (k := k)
      (Or.inl ⟨now, StepAt.fullStep ho⟩)
  exact ⟨hsnap, hinc, htcid, congrArg E.targetAssumptions htcid⟩

/-- If the R1 target-guarantee inclusion fails at a proposed COMMIT_START
predecessor, that COMMIT_START is not a valid full transition. This derives
inadmissibility from the frozen authorization guard; no target-success premise
is used. -/
theorem T13_failedInclusion_blocksCommitStart
    {E : FullEnv} {s t : State} {k : EffectKey} {now : Nat}
    (hfail : ¬ RequiredGuaranteesIncluded E s k) :
    ¬ FullStep E (.commitStart k now) s t := by
  intro hs
  have hauth : AuthorizedAt E now s k := by
    simpa [FullGuard] using hs.guard
  apply hfail
  rcases hauth with ⟨gr, hgamma, hstate, hused, hepoch, hsubject,
    hversion, hactive, hperm, hconstitution, hpolicy, hexpiry, hguarantees⟩
  simpa [RequiredGuaranteesIncluded] using hguarantees

end EffectKernel.PhaseD
