import EffectKernel.Base

namespace EffectKernel

abbrev GovernancePolicy := PolicyID
abbrev Constitution := GovernancePolicy → Prop

/-- Exact seven-component trusted runtime state. Trusted clock is external. -/
structure State where
  constitution : Constitution
  governance : GovernancePolicy
  gamma : GrantID → Option GrantRecord
  budget : GrantID → BudgetDim → BudgetCell
  lifecycle : EffectKey → LifecycleRecord
  metaAuth : MetaAuthID → Bool
  epoch : EpochID

def GrantExists (s : State) (g : GrantID) : Prop := ∃ gr, s.gamma g = some gr

def Parent (s : State) (parent child : GrantID) : Prop :=
  ∃ gr, s.gamma child = some gr ∧ gr.parent = some parent

inductive Ancestor (s : State) : GrantID → GrantID → Prop where
  | direct {parent child gr} :
      s.gamma child = some gr → gr.parent = some parent → Ancestor s parent child
  | extend {a parent child gr} :
      Ancestor s a parent → s.gamma child = some gr → gr.parent = some parent → Ancestor s a child

def AncestorOrSelf (s : State) (a g : GrantID) : Prop := a = g ∨ Ancestor s a g

/-- Grant-graph part of structural/type/canonical well-formedness. -/
structure GrantWellFormed (s : State) : Prop where
  interval_ok : ∀ g gr, s.gamma g = some gr → gr.validity.WellFormed
  root_ok : ∀ g gr, s.gamma g = some gr → gr.parent = none → gr.rootAllocation = g
  parent_ok : ∀ g gr p, s.gamma g = some gr → gr.parent = some p →
    ∃ pgr, s.gamma p = some pgr ∧
      pgr.generation < gr.generation ∧
      gr.parentVersion = some pgr.version ∧
      gr.rootAllocation = pgr.rootAllocation

def BudgetOwnersWellFormed (s : State) : Prop :=
  ∀ g d, (s.budget g d).total > 0 → GrantExists s g

/-- Structural/type/canonical well-formedness only. Nat/function/product types
carry nonnegativity, map-key uniqueness, lifecycle-domain typing, EffectKey epoch
namespacing shape, version/TCID/meta-auth typing. No substantive invariant is included. -/
structure WellFormed (s : State) : Prop where
  grants : GrantWellFormed s
  budgetOwners : BudgetOwnersWellFormed s

def ConstitutionHolds (s : State) : Prop := s.constitution s.governance

/-- Effective permission is exactly the meet/intersection of all raw permission
components across self + ancestry. -/
def P_eff (s : State) (g : GrantID) : Permission where
  ops := fun op => ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.ops op
  effectClasses := fun ec => ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.effectClasses ec
  targetPred := fun x => ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.targetPred x
  paramPred := fun p => ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.paramPred p
  perEffectCaps := fun ec n => ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.perEffectCaps ec n

/-- Effective temporal validity is ancestry intersection. -/
def EffectiveValid (s : State) (g : GrantID) (now : Nat) : Prop :=
  ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.validity.Contains now

/-- Effective delegability is ancestry conjunction under Boolean attenuation. -/
def EffectiveDelegable (s : State) (g : GrantID) : Prop :=
  ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.delegable = true

def LinkFresh (s : State) (child parent : GrantID) : Prop :=
  ∃ cgr pgr, s.gamma child = some cgr ∧ s.gamma parent = some pgr ∧
    cgr.parent = some parent ∧ cgr.parentVersion = some pgr.version

def EffectiveVersionFresh (s : State) (g : GrantID) : Prop :=
  ∀ child parent, AncestorOrSelf s child g → Parent s parent child → LinkFresh s child parent

/-- Effective activity derives from actual ancestry: every required grant exists,
is active and temporally valid, and every ancestry link is version-fresh. -/
def EffectiveActive (s : State) (now : Nat) (g : GrantID) : Prop :=
  (∀ a, AncestorOrSelf s a g →
    ∃ gr, s.gamma a = some gr ∧ gr.active = true ∧ gr.validity.Contains now) ∧
  EffectiveVersionFresh s g

/-- Proof-level root-lineage membership is ancestry, not a stored runtime list. -/
def InLineage (s : State) (r g : GrantID) : Prop := AncestorOrSelf s r g

end EffectKernel
