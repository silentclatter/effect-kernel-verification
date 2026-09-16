namespace EffectKernel

abbrev GrantID := Nat
abbrev BudgetDim := Nat
abbrev EffectKey := Nat
abbrev EpochID := Nat
abbrev SubjectID := Nat
abbrev MetaAuthID := Nat
abbrev Operation := Nat
abbrev GovernancePolicy := Nat
abbrev Constitution := GovernancePolicy → Prop

structure Permission where
  allows : Operation → Prop

def Permission.le (p q : Permission) : Prop :=
  ∀ op, p.allows op → q.allows op

namespace Permission

theorem le_refl (p : Permission) : p.le p := by
  intro op h
  exact h

theorem le_trans {p q r : Permission} (hpq : p.le q) (hqr : q.le r) : p.le r := by
  intro op hop
  exact hqr op (hpq op hop)

end Permission

structure Interval where
  first : Nat
  last : Nat

namespace Interval

def WellFormed (i : Interval) : Prop := i.first ≤ i.last

def Contains (i : Interval) (t : Nat) : Prop := i.first ≤ t ∧ t ≤ i.last

end Interval

inductive LifecycleState where
  | unseen
  | reserved
  | dispatching
  | committed
  | aborted
  | unknown
  deriving DecidableEq, Repr

inductive LifecycleEdge : LifecycleState → LifecycleState → Prop where
  | unseen_reserved : LifecycleEdge .unseen .reserved
  | reserved_dispatching : LifecycleEdge .reserved .dispatching
  | dispatching_committed : LifecycleEdge .dispatching .committed
  | dispatching_aborted : LifecycleEdge .dispatching .aborted
  | dispatching_unknown : LifecycleEdge .dispatching .unknown
  | unknown_unknown : LifecycleEdge .unknown .unknown
  | unknown_committed : LifecycleEdge .unknown .committed
  | unknown_aborted : LifecycleEdge .unknown .aborted

inductive LifecycleReach : LifecycleState → LifecycleState → Prop where
  | refl (s) : LifecycleReach s s
  | tail {a b c} : LifecycleReach a b → LifecycleEdge b c → LifecycleReach a c

namespace LifecycleReach

theorem trans {a b c : LifecycleState} (hab : LifecycleReach a b) (hbc : LifecycleReach b c) : LifecycleReach a c := by
  induction hbc with
  | refl _ => exact hab
  | tail hxy hyz ih => exact .tail ih hyz

end LifecycleReach

structure BudgetCell where
  avail : Nat
  resv : Nat
  cons : Nat

def BudgetCell.total (b : BudgetCell) : Nat := b.avail + b.resv + b.cons

structure GrantRecord where
  parent : Option GrantID
  parentVersion : Option Nat
  generation : Nat
  version : Nat
  subject : SubjectID
  permission : Permission
  validity : Interval
  delegable : Bool
  active : Bool

structure LifecycleRecord where
  state : LifecycleState
  used : Bool
  effectAstId : Nat
  grantVersion : Nat
  policyVersion : Nat
  tcid : Nat
  reserved : BudgetDim → Nat

end EffectKernel
