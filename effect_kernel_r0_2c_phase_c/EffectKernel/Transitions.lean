import EffectKernel.State

namespace EffectKernel

/-- Frozen in-epoch transition names. E2+ is not a separate transition kind; it
is a classification of `updatePolicy`. E3 is an epoch boundary below. -/
inductive TransitionKind where
  | prepare
  | commitStart
  | commitSuccess
  | commitAbort
  | commitFaultUnknown
  | reconcile
  | delegate
  | revoke
  | selfAttenuate
  | updatePolicy
  | expireReservation
  | expireGrant
  deriving DecidableEq, Repr

/-- Exact preservation equations for the components not written by a normal
lifecycle/budget operation. -/
structure PreserveAuthorityCore (s t : State) : Prop where
  constitution : t.constitution = s.constitution
  governance : t.governance = s.governance
  gamma : t.gamma = s.gamma
  metaAuth : t.metaAuth = s.metaAuth
  epoch : t.epoch = s.epoch

structure PreserveLifecycle (s t : State) : Prop where
  eq : t.lifecycle = s.lifecycle

structure PreserveBudget (s t : State) : Prop where
  eq : t.budget = s.budget

/-- Fields that identify the one previously prepared effect remain bound across
post-PREPARE lifecycle transitions. -/
def SameEffectBinding (a b : LifecycleRecord) : Prop :=
  a.effectAstId = b.effectAstId ∧
  a.subject = b.subject ∧
  a.grantId = b.grantId ∧
  a.grantVersion = b.grantVersion ∧
  a.policyVersion = b.policyVersion ∧
  a.tcid = b.tcid ∧
  a.reserved = b.reserved ∧
  a.expiry = b.expiry

/-- Exact single-key lifecycle update relation. Other effect records are unchanged. -/
structure LifecycleUpdate (s t : State) (k : EffectKey)
    (from to : LifecycleState) : Prop where
  preState : (s.lifecycle k).state = from
  postState : (t.lifecycle k).state = to
  postUsed : (t.lifecycle k).used = true
  binding : SameEffectBinding (s.lifecycle k) (t.lifecycle k)
  other : ∀ j, j ≠ k → t.lifecycle j = s.lifecycle j

/-- PREPARE creates the durable RESERVED record for a previously unused key. -/
structure PrepareLifecycle (s t : State) (k : EffectKey) (g : GrantID)
    (q : BudgetDim → Nat) : Prop where
  preState : (s.lifecycle k).state = .unseen
  preUnused : (s.lifecycle k).used = false
  postState : (t.lifecycle k).state = .reserved
  postUsed : (t.lifecycle k).used = true
  postGrant : (t.lifecycle k).grantId = g
  postReserve : (t.lifecycle k).reserved = q
  postUnlinearized : (t.lifecycle k).linearized = false
  other : ∀ j, j ≠ k → t.lifecycle j = s.lifecycle j

/-- COMMIT_START changes only lifecycle classification/bound snapshot metadata;
its transition-specific binding fields remain identical. -/
structure CommitStartLifecycle (s t : State) (k : EffectKey) : Prop where
  update : LifecycleUpdate s t k .reserved .dispatching
  postLinearized : (t.lifecycle k).linearized = true

inductive ReconcileOutcome where
  | unknown
  | committed
  | aborted
  deriving DecidableEq, Repr

def ReconcileOutcome.state : ReconcileOutcome → LifecycleState
  | .unknown => .unknown
  | .committed => .committed
  | .aborted => .aborted

/-- Exact PREPARE accounting: available -> reserved, same owner/cell. -/
structure ReserveBudget (s t : State) (g : GrantID) (q : BudgetDim → Nat) : Prop where
  enough : ∀ d, q d ≤ (s.budget g d).avail
  atOwner : ∀ d, t.budget g d =
    { avail := (s.budget g d).avail - q d
      resv := (s.budget g d).resv + q d
      cons := (s.budget g d).cons }
  other : ∀ h, h ≠ g → t.budget h = s.budget h

/-- Terminal settlement partitions the exact unsettled reserved quantity into an
authenticated refund and conservative consumed/spent quantity. -/
structure SettleBudget (s t : State) (g : GrantID) (q refund consumed : BudgetDim → Nat) : Prop where
  split : ∀ d, refund d + consumed d = q d
  enough : ∀ d, q d ≤ (s.budget g d).resv
  atOwner : ∀ d, t.budget g d =
    { avail := (s.budget g d).avail + refund d
      resv := (s.budget g d).resv - q d
      cons := (s.budget g d).cons + consumed d }
  other : ∀ h, h ≠ g → t.budget h = s.budget h

/-- UNKNOWN burns the full outstanding reserve: no refund. -/
structure BurnOutstanding (s t : State) (g : GrantID) (q : BudgetDim → Nat) : Prop where
  enough : ∀ d, q d ≤ (s.budget g d).resv
  atOwner : ∀ d, t.budget g d =
    { avail := (s.budget g d).avail
      resv := (s.budget g d).resv - q d
      cons := (s.budget g d).cons + q d }
  other : ∀ h, h ≠ g → t.budget h = s.budget h

/-- Reconciliation default/exceptional accounting may reclassify quantities only
under the frozen trusted rule. The local ledger total is preserved exactly; this
is the source transition rule, not the global conservation theorem. -/
structure ReconcileBudget (s t : State) (g : GrantID) : Prop where
  atOwner : ∀ d, (t.budget g d).total = (s.budget g d).total
  other : ∀ h, h ≠ g → t.budget h = s.budget h

/-- Exact delegation allocation: a fresh child begins with zero ledger quantity;
q transfers from parent available to child available. -/
structure DelegateBudget (s t : State) (parent child : GrantID) (q : BudgetDim → Nat) : Prop where
  enough : ∀ d, q d ≤ (s.budget parent d).avail
  childZero : ∀ d, s.budget child d = BudgetCell.zero
  parentPost : ∀ d, t.budget parent d =
    { avail := (s.budget parent d).avail - q d
      resv := (s.budget parent d).resv
      cons := (s.budget parent d).cons }
  childPost : ∀ d, t.budget child d =
    { avail := q d, resv := 0, cons := 0 }
  other : ∀ g, g ≠ parent → g ≠ child → t.budget g = s.budget g

/-- SELF_ATTENUATE may intentionally destroy spendable quantity; it cannot move
that quantity elsewhere. -/
structure DestroyBudget (s t : State) (g : GrantID) (q : BudgetDim → Nat) : Prop where
  enough : ∀ d, q d ≤ (s.budget g d).avail
  atOwner : ∀ d, t.budget g d =
    { avail := (s.budget g d).avail - q d
      resv := (s.budget g d).resv
      cons := (s.budget g d).cons }
  other : ∀ h, h ≠ g → t.budget h = s.budget h

/-- Positive E2+ budget provisioning writes exactly the independently authorized
new quantity into the existing root ledger as spendable availability. -/
structure ProvisionBudget (s t : State) (r : GrantID) (delta : BudgetDim → Nat) : Prop where
  rootExists : GrantExists s r
  atRoot : ∀ d, t.budget r d =
    { avail := (s.budget r d).avail + delta d
      resv := (s.budget r d).resv
      cons := (s.budget r d).cons }
  other : ∀ g, g ≠ r → t.budget g = s.budget g

/-- Exact fresh-child grant insertion and frozen delegation guards. -/
structure DelegateGamma (s t : State) (parent child : GrantID) (rec : GrantRecord) : Prop where
  fresh : s.gamma child = none
  childPost : t.gamma child = some rec
  parentLink : rec.parent = some parent
  parentPre : ∃ pgr, s.gamma parent = some pgr ∧
    pgr.generation < rec.generation ∧
    rec.parentVersion = some pgr.version ∧
    rec.rootAllocation = pgr.rootAllocation
  intervalOk : rec.validity.WellFormed
  permissionGuard : ∀ pgr, s.gamma parent = some pgr → rec.permission.le (P_eff s parent)
  validityGuard : ∀ now, rec.validity.Contains now → EffectiveValid s parent now
  delegabilityGuard : rec.delegable = true → EffectiveDelegable s parent
  preserveOther : ∀ g, g ≠ child → t.gamma g = s.gamma g

/-- REVOKE changes only activity/future effectiveness of the selected grant. -/
structure RevokeGamma (s t : State) (g : GrantID) : Prop where
  pre : ∃ old, s.gamma g = some old
  post : ∃ old new,
    s.gamma g = some old ∧ t.gamma g = some new ∧
    new.rootAllocation = old.rootAllocation ∧
    new.parent = old.parent ∧
    new.parentVersion = old.parentVersion ∧
    new.generation = old.generation ∧
    new.version = old.version ∧
    new.subject = old.subject ∧
    new.permission = old.permission ∧
    new.validity = old.validity ∧
    new.delegable = old.delegable ∧
    new.active = false
  preserveOther : ∀ h, h ≠ g → t.gamma h = s.gamma h

/-- SELF_ATTENUATE changes only authority dimensions monotonically downward while
preserving lineage structure. -/
structure AttenuateGamma (s t : State) (g : GrantID) : Prop where
  post : ∃ old new,
    s.gamma g = some old ∧ t.gamma g = some new ∧
    new.rootAllocation = old.rootAllocation ∧
    new.parent = old.parent ∧
    new.parentVersion = old.parentVersion ∧
    new.generation = old.generation ∧
    new.subject = old.subject ∧
    new.permission.le old.permission ∧
    new.validity.Subset old.validity ∧
    new.validity.WellFormed ∧
    (new.delegable = true → old.delegable = true) ∧
    (new.active = true → old.active = true)
  preserveOther : ∀ h, h ≠ g → t.gamma h = s.gamma h

structure ConsumeMetaAuth (s t : State) (m : MetaAuthID) : Prop where
  fresh : s.metaAuth m = false
  consumed : t.metaAuth m = true
  other : ∀ x, x ≠ m → t.metaAuth x = s.metaAuth x

inductive PolicyMutation where
  | nonExpanding
  | positiveProvision (root : GrantID) (delta : BudgetDim → Nat)

/-- UPDATE_POLICY semantic judgment for the two frozen in-epoch classes relevant
here. The constitutional successor-policy test is an explicit frozen guard. -/
structure UpdatePolicy (m : PolicyMutation) (s t : State)
    (newPolicy : GovernancePolicy) (meta : MetaAuthID) : Prop where
  constitutionSame : t.constitution = s.constitution
  governancePost : t.governance = newPolicy
  constitutionalGuard : s.constitution newPolicy
  gammaSame : t.gamma = s.gamma
  lifecycleSame : t.lifecycle = s.lifecycle
  metaAuthUpdate : ConsumeMetaAuth s t meta
  epochSame : t.epoch = s.epoch
  budgetRule : match m with
    | .nonExpanding => t.budget = s.budget
    | .positiveProvision r delta => ProvisionBudget s t r delta

/-- PREPARE semantic relation. Guards included here are only those load-bearing for
T0/T9/T4; omitted admission guards remain orthogonal to these five theorems. -/
structure Prepare (s t : State) (k : EffectKey) (g : GrantID)
    (q : BudgetDim → Nat) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  lifecycleUpdate : PrepareLifecycle s t k g q
  budgetUpdate : ReserveBudget s t g q

structure CommitStart (s t : State) (k : EffectKey) : Prop where
  same : PreserveAuthorityCore s t
  lifecycleUpdate : CommitStartLifecycle s t k
  budgetSame : t.budget = s.budget

structure CommitSuccess (s t : State) (k : EffectKey) (g : GrantID)
    (q refund spent : BudgetDim → Nat) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  boundGrant : (s.lifecycle k).grantId = g
  boundReserve : (s.lifecycle k).reserved = q
  lifecycleUpdate : LifecycleUpdate s t k .dispatching .committed
  budgetUpdate : SettleBudget s t g q refund spent

structure CommitAbort (s t : State) (k : EffectKey) (g : GrantID)
    (q refund burned : BudgetDim → Nat) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  boundGrant : (s.lifecycle k).grantId = g
  boundReserve : (s.lifecycle k).reserved = q
  lifecycleUpdate : LifecycleUpdate s t k .dispatching .aborted
  budgetUpdate : SettleBudget s t g q refund burned

structure CommitFaultUnknown (s t : State) (k : EffectKey) (g : GrantID)
    (q : BudgetDim → Nat) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  boundGrant : (s.lifecycle k).grantId = g
  outstanding : (s.lifecycle k).reserved = q
  lifecycleUpdate : LifecycleUpdate s t k .dispatching .unknown
  budgetUpdate : BurnOutstanding s t g q

structure Reconcile (s t : State) (k : EffectKey) (g : GrantID)
    (outcome : ReconcileOutcome) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  boundGrant : (s.lifecycle k).grantId = g
  lifecycleUpdate : LifecycleUpdate s t k .unknown outcome.state
  budgetUpdate : ReconcileBudget s t g

structure Delegate (s t : State) (parent child : GrantID) (rec : GrantRecord)
    (q : BudgetDim → Nat) : Prop where
  constitutionSame : t.constitution = s.constitution
  governanceSame : t.governance = s.governance
  gammaUpdate : DelegateGamma s t parent child rec
  budgetUpdate : DelegateBudget s t parent child q
  lifecycleSame : t.lifecycle = s.lifecycle
  epochSame : t.epoch = s.epoch

structure Revoke (s t : State) (g : GrantID) : Prop where
  constitutionSame : t.constitution = s.constitution
  governanceSame : t.governance = s.governance
  gammaUpdate : RevokeGamma s t g
  budgetSame : t.budget = s.budget
  lifecycleSame : t.lifecycle = s.lifecycle
  epochSame : t.epoch = s.epoch

structure SelfAttenuate (s t : State) (g : GrantID) (q : BudgetDim → Nat) : Prop where
  constitutionSame : t.constitution = s.constitution
  governanceSame : t.governance = s.governance
  gammaUpdate : AttenuateGamma s t g
  budgetUpdate : DestroyBudget s t g q
  lifecycleSame : t.lifecycle = s.lifecycle
  epochSame : t.epoch = s.epoch

structure ExpireReservation (s t : State) (k : EffectKey) (g : GrantID)
    (q refund burned : BudgetDim → Nat) (now : Nat) : Prop where
  same : PreserveAuthorityCore s t
  grantExists : GrantExists s g
  expired : (s.lifecycle k).expiry < now
  boundGrant : (s.lifecycle k).grantId = g
  boundReserve : (s.lifecycle k).reserved = q
  lifecycleUpdate : LifecycleUpdate s t k .reserved .aborted
  budgetUpdate : SettleBudget s t g q refund burned

/-- Grant expiry is semantic under external trusted time; no new status value or
runtime clock field is introduced. -/
structure ExpireGrant (s t : State) (g : GrantID) (now : Nat) : Prop where
  grantExists : ∃ gr, s.gamma g = some gr ∧ gr.validity.last < now
  constitutionSame : t.constitution = s.constitution
  governanceSame : t.governance = s.governance
  gammaSame : t.gamma = s.gamma
  budgetSame : t.budget = s.budget
  lifecycleSame : t.lifecycle = s.lifecycle
  metaAuthSame : t.metaAuth = s.metaAuth
  epochSame : t.epoch = s.epoch

/-- Actual in-epoch frozen transition relation. No constructor carries any target
theorem as a field. -/
inductive TrustedStep : TransitionKind → State → State → Prop where
  | prepare (h : Prepare s t k g q) : TrustedStep .prepare s t
  | commitStart (h : CommitStart s t k) : TrustedStep .commitStart s t
  | commitSuccess (h : CommitSuccess s t k g q refund spent) : TrustedStep .commitSuccess s t
  | commitAbort (h : CommitAbort s t k g q refund burned) : TrustedStep .commitAbort s t
  | commitFaultUnknown (h : CommitFaultUnknown s t k g q) : TrustedStep .commitFaultUnknown s t
  | reconcile (h : Reconcile s t k g outcome) : TrustedStep .reconcile s t
  | delegate (h : Delegate s t parent child rec q) : TrustedStep .delegate s t
  | revoke (h : Revoke s t g) : TrustedStep .revoke s t
  | selfAttenuate (h : SelfAttenuate s t g q) : TrustedStep .selfAttenuate s t
  | updatePolicy (h : UpdatePolicy cls s t newPolicy meta) : TrustedStep .updatePolicy s t
  | expireReservation (h : ExpireReservation s t k g q refund burned now) : TrustedStep .expireReservation s t
  | expireGrant (h : ExpireGrant s t g now) : TrustedStep .expireGrant s t

/-- E3 is deliberately outside in-epoch TrustedStep: it closes the predecessor
theorem epoch and constructs a successor epoch under predecessor authorization.
No successor invariant is carried here. -/
structure ReprovisionTCB (s t : State) : Prop where
  epochChanged : t.epoch ≠ s.epoch

end EffectKernel
