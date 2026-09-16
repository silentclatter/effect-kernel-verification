namespace EffectKernel

abbrev GrantID := Nat
abbrev BudgetDim := Nat
abbrev EpochID := Nat
abbrev EffectID := Nat
abbrev EffectKey := EpochID × EffectID
abbrev SubjectID := Nat
abbrev MetaAuthID := Nat
abbrev TCID := Nat
abbrev Operation := Nat
abbrev EffectClass := Nat
abbrev TargetID := Nat
abbrev ActionParam := Nat
abbrev PolicyID := Nat

/-- Frozen five-component qualitative permission product.  The per-effect-cap
component is represented extensionally: `perEffectCaps ec n` means cap value `n`
is admitted for effect class `ec`.  Numeric caps embed by `n ≤ cap ec`. -/
structure Permission where
  ops : Operation → Prop
  effectClasses : EffectClass → Prop
  targetPred : TargetID → Prop
  paramPred : ActionParam → Prop
  perEffectCaps : EffectClass → Nat → Prop

/-- Componentwise Phase-A attenuation order. -/
def Permission.le (p q : Permission) : Prop :=
  (∀ op, p.ops op → q.ops op) ∧
  (∀ ec, p.effectClasses ec → q.effectClasses ec) ∧
  (∀ x, p.targetPred x → q.targetPred x) ∧
  (∀ a, p.paramPred a → q.paramPred a) ∧
  (∀ ec n, p.perEffectCaps ec n → q.perEffectCaps ec n)

namespace Permission

theorem le_refl (p : Permission) : p.le p := by
  exact ⟨(fun _ h => h), (fun _ h => h), (fun _ h => h), (fun _ h => h), (fun _ _ h => h)⟩

theorem le_trans {p q r : Permission} (hpq : p.le q) (hqr : q.le r) : p.le r := by
  rcases hpq with ⟨hops1, hcls1, htgt1, hpar1, hcap1⟩
  rcases hqr with ⟨hops2, hcls2, htgt2, hpar2, hcap2⟩
  exact ⟨
    (fun op h => hops2 op (hops1 op h)),
    (fun ec h => hcls2 ec (hcls1 ec h)),
    (fun x h => htgt2 x (htgt1 x h)),
    (fun a h => hpar2 a (hpar1 a h)),
    (fun ec n h => hcap2 ec n (hcap1 ec n h))⟩

/-- Numeric cap maps and the extensional cap-predicate representation induce the
same attenuation order.  This is the correspondence lemma for Phase-A
`PerEffectCaps` pointwise order. -/
theorem numericCap_order_equiv (a b : EffectClass → Nat) :
    (∀ ec, a ec ≤ b ec) ↔
    (∀ ec n, n ≤ a ec → n ≤ b ec) := by
  constructor
  · intro h ec n hn
    exact Nat.le_trans hn (h ec)
  · intro h ec
    exact h ec (a ec) (Nat.le_refl _)

end Permission

structure Interval where
  first : Nat
  last : Nat

namespace Interval

def WellFormed (i : Interval) : Prop := i.first ≤ i.last

def Contains (i : Interval) (t : Nat) : Prop := i.first ≤ t ∧ t ≤ i.last

def Subset (a b : Interval) : Prop := ∀ t, a.Contains t → b.Contains t

end Interval

inductive LifecycleState where
  | unseen
  | reserved
  | dispatching
  | committed
  | aborted
  | unknown
  deriving DecidableEq, Repr

/-- Exact frozen primary + expiry + reconciliation lifecycle edges. -/
inductive LifecycleEdge : LifecycleState → LifecycleState → Prop where
  | unseen_reserved : LifecycleEdge .unseen .reserved
  | reserved_dispatching : LifecycleEdge .reserved .dispatching
  | reserved_aborted : LifecycleEdge .reserved .aborted
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
  | refl => exact hab
  | tail hxy hyz ih => exact .tail ih hyz

end LifecycleReach

structure BudgetCell where
  avail : Nat
  resv : Nat
  cons : Nat

def BudgetCell.total (b : BudgetCell) : Nat := b.avail + b.resv + b.cons

def BudgetCell.zero : BudgetCell := ⟨0, 0, 0⟩

/-- R0.2c grant record projection. `rootAllocation` represents the frozen
`r_kappa` root-allocation reference, not new trusted state. -/
structure GrantRecord where
  rootAllocation : GrantID
  parent : Option GrantID
  parentVersion : Option Nat
  generation : Nat
  version : Nat
  subject : SubjectID
  permission : Permission
  validity : Interval
  delegable : Bool
  active : Bool

/-- Durable effect record fields needed by T0/T9 and exact transition bindings. -/
structure LifecycleRecord where
  state : LifecycleState
  used : Bool
  effectAstId : Nat
  subject : SubjectID
  grantId : GrantID
  grantVersion : Nat
  policyVersion : Nat
  tcid : TCID
  reserved : BudgetDim → Nat
  expiry : Nat
  linearized : Bool

end EffectKernel
