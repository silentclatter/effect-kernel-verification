import EffectKernel.Base

namespace EffectKernel

structure State where
  constitution : Constitution
  governance : GovernancePolicy
  gamma : GrantID → Option GrantRecord
  budget : GrantID → BudgetDim → BudgetCell
  lifecycle : EffectKey → LifecycleRecord
  metaAuth : MetaAuthID → Bool
  epoch : EpochID
  clock : Nat

def GrantExists (s : State) (g : GrantID) : Prop := ∃ gr, s.gamma g = some gr

def Parent (s : State) (parent child : GrantID) : Prop :=
  ∃ gr, s.gamma child = some gr ∧ gr.parent = some parent

inductive Ancestor (s : State) : GrantID → GrantID → Prop where
  | direct {parent child gr} :
      s.gamma child = some gr → gr.parent = some parent → Ancestor s parent child
  | extend {a parent child gr} :
      Ancestor s a parent → s.gamma child = some gr → gr.parent = some parent → Ancestor s a child

def AncestorOrSelf (s : State) (a g : GrantID) : Prop := a = g ∨ Ancestor s a g

structure WellFormed (s : State) : Prop where
  interval_ok : ∀ g gr, s.gamma g = some gr → gr.validity.WellFormed
  parent_ok : ∀ g gr p, s.gamma g = some gr → gr.parent = some p →
    ∃ pgr, s.gamma p = some pgr ∧ pgr.generation < gr.generation

structure SameGrantStructure (s t : State) : Prop where
  from_post : ∀ g tgr, t.gamma g = some tgr →
    ∃ sgr, s.gamma g = some sgr ∧
      sgr.parent = tgr.parent ∧ sgr.parentVersion = tgr.parentVersion ∧
      sgr.generation = tgr.generation
  to_post : ∀ g sgr, s.gamma g = some sgr →
    ∃ tgr, t.gamma g = some tgr ∧
      sgr.parent = tgr.parent ∧ sgr.parentVersion = tgr.parentVersion ∧
      sgr.generation = tgr.generation
  post_interval_ok : ∀ g gr, t.gamma g = some gr → gr.validity.WellFormed

structure DelegateGamma (s t : State) (child parent : GrantID) (rec : GrantRecord) : Prop where
  fresh : s.gamma child = none
  child_post : t.gamma child = some rec
  parent_link : rec.parent = some parent
  parent_pre : ∃ pgr, s.gamma parent = some pgr ∧ pgr.generation < rec.generation
  interval_ok : rec.validity.WellFormed
  preserve_other : ∀ g, g ≠ child → t.gamma g = s.gamma g

inductive StructuralStep : State → State → Prop where
  | preserve {s t} (h : t.gamma = s.gamma) : StructuralStep s t
  | authorityOnly {s t} (h : SameGrantStructure s t) : StructuralStep s t
  | delegate {s t child parent rec} (h : DelegateGamma s t child parent rec) : StructuralStep s t
  | reprovision {s t} (h : WellFormed t) : StructuralStep s t

def ConstitutionHolds (s : State) : Prop := s.constitution s.governance

def EffectiveAllows (s : State) (g : GrantID) (op : Operation) : Prop :=
  ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.permission.allows op

def P_eff (s : State) (g : GrantID) : Permission := ⟨EffectiveAllows s g⟩

def EffectiveValid (s : State) (g : GrantID) (t : Nat) : Prop :=
  ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.validity.Contains t

def EffectiveDelegable (s : State) (g : GrantID) : Prop :=
  ∀ a, AncestorOrSelf s a g → ∃ gr, s.gamma a = some gr ∧ gr.delegable = true

def LinkFresh (s : State) (child parent : GrantID) : Prop :=
  ∃ cgr pgr, s.gamma child = some cgr ∧ s.gamma parent = some pgr ∧
    cgr.parent = some parent ∧ cgr.parentVersion = some pgr.version

def EffectiveActive (s : State) (g : GrantID) : Prop :=
  ∀ a, AncestorOrSelf s a g →
    ∃ gr, s.gamma a = some gr ∧ gr.active = true ∧ gr.validity.Contains s.clock

end EffectKernel
