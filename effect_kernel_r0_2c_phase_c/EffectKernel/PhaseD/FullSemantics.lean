import EffectKernel.T4_BudgetConservation
import EffectKernel.T9_Lifecycle

namespace EffectKernel.PhaseD

open EffectKernel

/-- Proof-only identifier for a target-contract guarantee proposition. -/
abbrev GuaranteeID := Nat

/-- Authorization-relevant canonical effect meaning. The frozen runtime stores
`effectAstId`; Phase D interprets that identifier through an immutable semantic
decoder rather than adding fields to trusted state. -/
structure CanonicalEffect where
  operation : Operation
  effectClass : EffectClass
  target : TargetID
  parameter : ActionParam
  cap : Nat
  payloadDigest : Nat
  stateBinding : Nat
  adapter : Nat
  deriving DecidableEq

/-- Proof environment for the already-frozen semantic functions that are not
trusted runtime state. In particular, this contains no mutable authority. -/
structure FullEnv where
  decodeEffect : Nat → CanonicalEffect
  req : CanonicalEffect → GovernancePolicy → GuaranteeID → Prop
  guarantees : TCID → GuaranteeID → Prop
  targetAssumptions : TCID → Prop
  provisionJudge : ProvisionJudge
  metaAuthorizesE2 : State → MetaAuthID → GrantID → (BudgetDim → Nat) → Prop
  e3Authorizes : State → Nat → Prop

/-- Five-component permission product applied to the canonical effect meaning. -/
def PermissionAllows (p : Permission) (a : CanonicalEffect) : Prop :=
  p.ops a.operation ∧
  p.effectClasses a.effectClass ∧
  p.targetPred a.target ∧
  p.paramPred a.parameter ∧
  p.perEffectCaps a.effectClass a.cap

/-- Frozen abstract authorization judgment at the unique release point. Trusted
clock is an argument, not an eighth trusted-state field. -/
def AuthorizedAt (E : FullEnv) (now : Nat) (s : State) (k : EffectKey) : Prop :=
  let lr := s.lifecycle k
  let a := E.decodeEffect lr.effectAstId
  ∃ gr,
    s.gamma lr.grantId = some gr ∧
    lr.state = .reserved ∧
    lr.used = true ∧
    k.1 = s.epoch ∧
    gr.subject = lr.subject ∧
    gr.version = lr.grantVersion ∧
    EffectiveActive s now lr.grantId ∧
    PermissionAllows (P_eff s lr.grantId) a ∧
    ConstitutionHolds s ∧
    lr.policyVersion = s.governance ∧
    now ≤ lr.expiry ∧
    (∀ r, E.req a s.governance r → E.guarantees lr.tcid r)

/-- Authorization-relevant immutable snapshot. This is proof/history material,
not an added component of `State`. -/
structure AuthSnapshot where
  constitution : Constitution
  governance : GovernancePolicy
  gamma : GrantID → Option GrantRecord
  record : LifecycleRecord
  epoch : EpochID
  now : Nat
  effectKey : EffectKey

/-- Snapshot captured from the predecessor trusted state at linearization. -/
def snapshotOf (s : State) (k : EffectKey) (now : Nat) : AuthSnapshot where
  constitution := s.constitution
  governance := s.governance
  gamma := s.gamma
  record := s.lifecycle k
  epoch := s.epoch
  now := now
  effectKey := k

/-- Reconstruct only the authorization projection from a snapshot. Dummy budget,
meta-authorization, and non-selected lifecycle entries are semantically irrelevant
to `AuthorizedAt`; they are deliberately not consulted. -/
def snapshotState (σ : AuthSnapshot) : State where
  constitution := σ.constitution
  governance := σ.governance
  gamma := σ.gamma
  budget := fun _ _ => BudgetCell.zero
  lifecycle := fun _ => σ.record
  metaAuth := fun _ => false
  epoch := σ.epoch

def AuthorizedFromSnapshot (E : FullEnv) (σ : AuthSnapshot) : Prop :=
  AuthorizedAt E σ.now (snapshotState σ) σ.effectKey

/-- Explicit source-to-snapshot equivalence used by T7. -/
theorem authorizedAt_snapshot_iff (E : FullEnv) (s : State) (k : EffectKey) (now : Nat) :
    AuthorizedAt E now s k ↔ AuthorizedFromSnapshot E (snapshotOf s k now) := by
  rfl

/-- Proof-only labels refine, but do not extend, the frozen `TransitionKind` set. -/
inductive StepLabel where
  | prepare (k : EffectKey) (g : GrantID) (q : BudgetDim → Nat) (now : Nat)
  | commitStart (k : EffectKey) (now : Nat)
  | commitSuccess (k : EffectKey) (g : GrantID)
      (q refund spent : BudgetDim → Nat)
  | commitAbort (k : EffectKey) (g : GrantID)
      (q refund burned : BudgetDim → Nat)
  | commitFaultUnknown (k : EffectKey) (g : GrantID) (q : BudgetDim → Nat)
  | reconcile (k : EffectKey) (g : GrantID) (outcome : ReconcileOutcome)
  | delegate (parent child : GrantID) (rec : GrantRecord) (q : BudgetDim → Nat)
  | revoke (g : GrantID)
  | selfAttenuate (g : GrantID) (q : BudgetDim → Nat)
  | updatePolicy (cls : PolicyMutation) (newPolicy : GovernancePolicy) (mid : MetaAuthID)
  | expireReservation (k : EffectKey) (g : GrantID)
      (q refund burned : BudgetDim → Nat) (now : Nat)
  | expireGrant (g : GrantID) (now : Nat)

namespace StepLabel

def kind : StepLabel → TransitionKind
  | .prepare .. => .prepare
  | .commitStart .. => .commitStart
  | .commitSuccess .. => .commitSuccess
  | .commitAbort .. => .commitAbort
  | .commitFaultUnknown .. => .commitFaultUnknown
  | .reconcile .. => .reconcile
  | .delegate .. => .delegate
  | .revoke .. => .revoke
  | .selfAttenuate .. => .selfAttenuate
  | .updatePolicy .. => .updatePolicy
  | .expireReservation .. => .expireReservation
  | .expireGrant .. => .expireGrant

end StepLabel

/-- Exact Phase C transition relation selected by a proof-only label. -/
def BaseStep : StepLabel → State → State → Prop
  | .prepare k g q _, s, t => Prepare s t k g q
  | .commitStart k _, s, t => CommitStart s t k
  | .commitSuccess k g q refund spent, s, t => CommitSuccess s t k g q refund spent
  | .commitAbort k g q refund burned, s, t => CommitAbort s t k g q refund burned
  | .commitFaultUnknown k g q, s, t => CommitFaultUnknown s t k g q
  | .reconcile k g outcome, s, t => Reconcile s t k g outcome
  | .delegate parent child rec q, s, t => Delegate s t parent child rec q
  | .revoke g, s, t => Revoke s t g
  | .selfAttenuate g q, s, t => SelfAttenuate s t g q
  | .updatePolicy cls newPolicy mid, s, t => UpdatePolicy cls s t newPolicy mid
  | .expireReservation k g q refund burned now, s, t =>
      ExpireReservation s t k g q refund burned now
  | .expireGrant g now, s, t => ExpireGrant s t g now

/-- Meta-authorization consumption is monotone: a consumed identifier cannot
become fresh again in an in-epoch conforming successor. -/
def MetaAuthMonotone (s t : State) : Prop :=
  ∀ m, s.metaAuth m = true → t.metaAuth m = true

/-- Full PREPARE guards restored from the frozen architecture. This predicate is
strictly an admission condition; it does not assert any target theorem. -/
def PrepareAdmissible (E : FullEnv) (now : Nat) (s : State)
    (k : EffectKey) (g : GrantID) : Prop :=
  let lr := s.lifecycle k
  ∃ gr,
    s.gamma g = some gr ∧
    EffectiveActive s now g ∧
    ConstitutionHolds s ∧
    k.1 = s.epoch ∧
    gr.subject = lr.subject ∧
    PermissionAllows (P_eff s g) (E.decodeEffect lr.effectAstId) ∧
    now ≤ lr.expiry

/-- Extra guards missing from the foundational projection but frozen before R1. -/
def FullGuard (E : FullEnv) (lbl : StepLabel) (s t : State) : Prop :=
  match lbl with
  | .prepare k g _ now => PrepareAdmissible E now s k g
  | .commitStart k now => AuthorizedAt E now s k
  | .updatePolicy (.positiveProvision r delta) _ mid =>
      (∃ d, 0 < delta d) ∧
      CanonicalRoot s r ∧
      E.provisionJudge s r delta ∧
      E.metaAuthorizesE2 s mid r delta
  | _ => True

/-- Phase D full in-epoch semantics: same trusted state, same transition kinds,
with only already-frozen guards restored. -/
structure FullStep (E : FullEnv) (lbl : StepLabel) (s t : State) : Prop where
  base : BaseStep lbl s t
  guard : FullGuard E lbl s t
  metaMonotone : MetaAuthMonotone s t

/-- Every full step projects to the immutable Phase C `TrustedStep`. -/
theorem baseStep_to_trusted {lbl : StepLabel} {s t : State}
    (h : BaseStep lbl s t) : TrustedStep lbl.kind s t := by
  cases lbl with
  | prepare k g q now => exact .prepare h
  | commitStart k now => exact .commitStart h
  | commitSuccess k g q refund spent => exact .commitSuccess h
  | commitAbort k g q refund burned => exact .commitAbort h
  | commitFaultUnknown k g q => exact .commitFaultUnknown h
  | reconcile k g outcome => exact .reconcile h
  | delegate parent child rec q => exact .delegate h
  | revoke g => exact .revoke h
  | selfAttenuate g q => exact .selfAttenuate h
  | updatePolicy cls newPolicy mid => exact .updatePolicy h
  | expireReservation k g q refund burned now => exact .expireReservation h
  | expireGrant g now => exact .expireGrant h

theorem fullStep_to_trusted {E : FullEnv} {lbl : StepLabel} {s t : State}
    (h : FullStep E lbl s t) : TrustedStep lbl.kind s t :=
  baseStep_to_trusted h.base

/-- Arbitrary-length proof-only full trace. It records no additional trusted
runtime state. -/
inductive FullTrace (E : FullEnv) (s0 : State) : State → Type where
  | refl : FullTrace E s0 s0
  | step {s t : State} {lbl : StepLabel} :
      FullTrace E s0 s → FullStep E lbl s t → FullTrace E s0 t

namespace FullTrace

def length {E : FullEnv} {s0 s : State} : FullTrace E s0 s → Nat
  | .refl => 0
  | .step h _ => length h + 1

/-- D0/D1 projection: full traces are actual Phase C trusted reachability. -/
theorem toReachable {E : FullEnv} {s0 s : State} (h : FullTrace E s0 s) :
    ReachableFrom s0 s := by
  induction h with
  | refl => exact .refl
  | step hstep hfull ih => exact .step ih (fullStep_to_trusted hfull)

end FullTrace

/-- Positive E2+ full steps produce the exact Phase C/T4 positive-provision event. -/
theorem positiveFullStep_to_event {E : FullEnv} {s t : State}
    {r : GrantID} {delta : BudgetDim → Nat} {newPolicy : GovernancePolicy}
    {mid : MetaAuthID}
    (h : FullStep E (.updatePolicy (.positiveProvision r delta) newPolicy mid) s t) :
    PositiveProvisioningEvent E.provisionJudge s t r delta newPolicy mid := by
  rcases h.guard with ⟨hnz, hroot, hjudge, _hmeta⟩
  exact {
    update := h.base
    deltaNonzero := hnz
    canonicalRoot := hroot
    predecessorJudge := hjudge
  }

/-- Predecessor-only E2+ judgment, including independently existing meta-authorization. -/
def E2PredJudge (E : FullEnv) (s : State) (mid : MetaAuthID)
    (r : GrantID) (delta : BudgetDim → Nat) : Prop :=
  E.provisionJudge s r delta ∧
  s.metaAuth mid = false ∧
  E.metaAuthorizesE2 s mid r delta

/-- Full E3 proof object remains outside in-epoch `FullStep`, exactly as E3 remains
outside Phase C `TrustedStep`. Successor provision is explicit proof material. -/
structure FullE3 (E : FullEnv) (proposalDigest : Nat) (s t : State)
    (ids : List GrantID) (alloc : InitialAllocation) : Prop where
  replacement : ReprovisionTCB s t
  predecessorAuthorized : E.e3Authorizes s proposalDigest
  successorSupport : GammaSupportExact t ids
  successorLedger : InitialLedger t alloc

end EffectKernel.PhaseD
