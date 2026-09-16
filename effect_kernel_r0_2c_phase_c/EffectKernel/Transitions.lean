import EffectKernel.State

namespace EffectKernel

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
  | positiveProvisioning
  | reprovisionTCB
  deriving DecidableEq, Repr

structure BudgetProjection where
  lineageMass : GrantID → BudgetDim → Nat
  provisioned : GrantID → BudgetDim → Nat

def BudgetInvariant (b : BudgetProjection) : Prop :=
  ∀ r d, b.lineageMass r d ≤ b.provisioned r d

inductive BudgetDelta : BudgetProjection → BudgetProjection → Prop where
  | ordinary {b b'}
      (hmass : ∀ r d, b'.lineageMass r d ≤ b.lineageMass r d)
      (hprov : ∀ r d, b'.provisioned r d = b.provisioned r d) :
      BudgetDelta b b'
  | provision {b b'} (delta : GrantID → BudgetDim → Nat)
      (hmass : ∀ r d, b'.lineageMass r d ≤ b.lineageMass r d + delta r d)
      (hprov : ∀ r d, b'.provisioned r d = b.provisioned r d + delta r d) :
      BudgetDelta b b'
  | reprovision {b b'} (h : BudgetInvariant b') : BudgetDelta b b'

structure ProofFrame where
  state : State
  budgetView : BudgetProjection

/-- Frozen lifecycle projection: each key is unchanged or advances by a primary/reconciliation edge,
and used history never becomes fresh. -/
def LifecycleSafe (s t : State) : Prop :=
  ∀ k,
    (s.lifecycle k).state = (t.lifecycle k).state ∨
      LifecycleEdge (s.lifecycle k).state (t.lifecycle k).state

def UsedHistorySafe (s t : State) : Prop :=
  ∀ k, (s.lifecycle k).used = true → (t.lifecycle k).used = true

/-- Within a fixed theorem epoch the constitution is fixed and the post-policy satisfies it.
E3 is represented by a changed epoch and is therefore outside this implication. -/
def ConstitutionalSafe (s t : State) : Prop :=
  s.epoch = t.epoch → t.constitution = s.constitution ∧ t.constitution t.governance

structure TrustedStep (f f' : ProofFrame) : Prop where
  kind : TransitionKind
  structural : StructuralStep f.state f'.state
  lifecycle : LifecycleSafe f.state f'.state
  usedHistory : UsedHistorySafe f.state f'.state
  constitution : ConstitutionalSafe f.state f'.state
  budget : BudgetDelta f.budgetView f'.budgetView

end EffectKernel
