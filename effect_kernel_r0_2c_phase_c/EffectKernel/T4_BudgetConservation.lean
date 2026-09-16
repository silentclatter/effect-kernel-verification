import EffectKernel.T2_AuthorityAttenuation
import EffectKernel.OmegaCompat

namespace EffectKernel

private theorem some_inj {α : Type} {a b : α} (h : some a = some b) : a = b := by
  cases h
  rfl

/-- Proof-only exact finite enumeration of the current finite support of Gamma.
This is not trusted runtime state. -/
structure GammaSupportExact (s : State) (ids : List GrantID) : Prop where
  nodup : ids.Nodup
  member_iff : ∀ g, g ∈ ids ↔ GrantExists s g

/-- Canonical root-lineage witness from the frozen grant structure. -/
def CanonicalRoot (s : State) (r : GrantID) : Prop :=
  ∃ gr, s.gamma r = some gr ∧ gr.parent = none ∧ gr.rootAllocation = r

/-- Executable root-allocation membership used for finite summation. -/
def RootAllocated (s : State) (r g : GrantID) : Prop :=
  ∃ gr, s.gamma g = some gr ∧ gr.rootAllocation = r

/-- One actual Gamma/B contribution: Available + Reserved + Consumed. -/
def LineageContribution (s : State) (r : GrantID) (d : BudgetDim) (g : GrantID) : Nat :=
  match s.gamma g with
  | none => 0
  | some gr => if gr.rootAllocation = r then (s.budget g d).total else 0

/-- Actual finite lineage mass computed from Gamma and B. `ids` is proof-only
finite-support infrastructure and must satisfy `GammaSupportExact`. -/
def LineageMass : List GrantID → State → GrantID → BudgetDim → Nat
  | [], _, _, _ => 0
  | g :: gs, s, r, d =>
      LineageContribution s r d g + LineageMass gs s r d

/-- Explicit initial allocation map used only to define the history-derived base
provisioning quantity. -/
abbrev InitialAllocation := GrantID → BudgetDim → BudgetCell

def InitialContribution (s0 : State) (alloc : InitialAllocation)
    (r : GrantID) (d : BudgetDim) (g : GrantID) : Nat :=
  match s0.gamma g with
  | none => 0
  | some gr => if gr.rootAllocation = r then (alloc g d).total else 0

def InitialProvision : List GrantID → State → InitialAllocation → GrantID → BudgetDim → Nat
  | [], _, _, _, _ => 0
  | g :: gs, s0, alloc, r, d =>
      InitialContribution s0 alloc r d g + InitialProvision gs s0 alloc r d

/-- Frozen successor/initial-state construction premise: the trusted B ledger is
exactly the explicitly provisioned allocation. This is not a conservation premise. -/
def InitialLedger (s0 : State) (alloc : InitialAllocation) : Prop :=
  ∀ g d, s0.budget g d = alloc g d

structure ProvisionEvent where
  root : GrantID
  delta : BudgetDim → Nat

/-- History-derived Provisioned(r,n,d): initial provision plus all valid prior
positive-provision events that have occurred before the represented state. -/
def Provisioned (initial : GrantID → BudgetDim → Nat) :
    List ProvisionEvent → GrantID → BudgetDim → Nat
  | [], r, d => initial r d
  | e :: es, r, d =>
      Provisioned initial es r d + if e.root = r then e.delta d else 0

/-- The theorem-epoch predecessor JudgeSem projection relevant to positive
provisioning. It receives only the predecessor trusted state, root and proposed
delta, so post-state quantity cannot be used as the authorization basis. -/
abbrev ProvisionJudge := State → GrantID → (BudgetDim → Nat) → Prop

/-- Exact proof classification predicate over an existing UPDATE_POLICY E2+
transition. It does not introduce a runtime transition class. -/
structure PositiveProvisioningEvent (judge : ProvisionJudge)
    (s t : State) (r : GrantID) (delta : BudgetDim → Nat)
    (newPolicy : GovernancePolicy) (mid : MetaAuthID) : Prop where
  update : UpdatePolicy (.positiveProvision r delta) s t newPolicy mid
  deltaNonzero : ∃ d, 0 < delta d
  canonicalRoot : CanonicalRoot s r
  predecessorJudge : judge s r delta

/-- Arbitrary-length in-epoch history with proof-only exact Gamma support and the
history list of valid positive provisioning events. No mass bound is stored here. -/
inductive BudgetHistory (judge : ProvisionJudge)
    (s0 : State) (ids0 : List GrantID) (alloc : InitialAllocation) :
    Nat → State → List GrantID → List ProvisionEvent → Prop where
  | init
      (hsupport : GammaSupportExact s0 ids0)
      (hledger : InitialLedger s0 alloc) :
      BudgetHistory judge s0 ids0 alloc 0 s0 ids0 []
  | prepare {n s t ids es k g q}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : Prepare s t k g q)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | commitStart {n s t ids es k}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : CommitStart s t k)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | commitSuccess {n s t ids es k g q refund spent}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : CommitSuccess s t k g q refund spent)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | commitAbort {n s t ids es k g q refund burned}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : CommitAbort s t k g q refund burned)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | commitFaultUnknown {n s t ids es k g q}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : CommitFaultUnknown s t k g q)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | reconcile {n s t ids es k g outcome}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : Reconcile s t k g outcome)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | delegate {n s t ids es parent child rec q}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : Delegate s t parent child rec q)
      (hsupport : GammaSupportExact t (child :: ids)) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t (child :: ids) es
  | revoke {n s t ids es g}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : Revoke s t g)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | selfAttenuate {n s t ids es g q}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : SelfAttenuate s t g q)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | updatePolicyOrdinary {n s t ids es newPolicy mid}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : UpdatePolicy .nonExpanding s t newPolicy mid)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | updatePolicyPositive {n s t ids es r delta newPolicy mid}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : PositiveProvisioningEvent judge s t r delta newPolicy mid)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids
        ({ root := r, delta := delta } :: es)
  | expireReservation {n s t ids es k g q refund burned now}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : ExpireReservation s t k g q refund burned now)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es
  | expireGrant {n s t ids es g now}
      (hprev : BudgetHistory judge s0 ids0 alloc n s ids es)
      (h : ExpireGrant s t g now)
      (hsupport : GammaSupportExact t ids) :
      BudgetHistory judge s0 ids0 alloc (n + 1) t ids es

namespace BudgetHistory

theorem support {judge s0 ids0 alloc n s ids es}
    (h : BudgetHistory judge s0 ids0 alloc n s ids es) :
    GammaSupportExact s ids := by
  cases h <;> assumption

theorem reachable {judge s0 ids0 alloc n s ids es}
    (h : BudgetHistory judge s0 ids0 alloc n s ids es) :
    ReachableFrom s0 s := by
  induction h with
  | init => exact .refl
  | prepare hprev h _ ih => exact .step ih (.prepare h)
  | commitStart hprev h _ ih => exact .step ih (.commitStart h)
  | commitSuccess hprev h _ ih => exact .step ih (.commitSuccess h)
  | commitAbort hprev h _ ih => exact .step ih (.commitAbort h)
  | commitFaultUnknown hprev h _ ih => exact .step ih (.commitFaultUnknown h)
  | reconcile hprev h _ ih => exact .step ih (.reconcile h)
  | delegate hprev h _ ih => exact .step ih (.delegate h)
  | revoke hprev h _ ih => exact .step ih (.revoke h)
  | selfAttenuate hprev h _ ih => exact .step ih (.selfAttenuate h)
  | updatePolicyOrdinary hprev h _ ih => exact .step ih (.updatePolicy h)
  | updatePolicyPositive hprev h _ ih => exact .step ih (.updatePolicy h.update)
  | expireReservation hprev h _ ih => exact .step ih (.expireReservation h)
  | expireGrant hprev h _ ih => exact .step ih (.expireGrant h)

end BudgetHistory

/-- Root allocation follows parent links under the frozen structural WF. -/
theorem ancestor_same_rootAllocation {s : State} (hw : GrantWellFormed s)
    {a c : GrantID} (hac : Ancestor s a c) :
    ∀ agr cgr,
      s.gamma a = some agr → s.gamma c = some cgr →
      cgr.rootAllocation = agr.rootAllocation := by
  induction hac with
  | direct hchild hparent =>
      intro agr cgr ha hc
      have hceq : cgr = _ := some_inj (hc.symm.trans hchild)
      subst cgr
      rcases hw.parent_ok _ _ _ hchild hparent with ⟨pgr, hp, _hlt, hroot⟩
      have hpeq : pgr = agr := some_inj (hp.symm.trans ha)
      subst pgr
      exact hroot
  | extend hprefix hchild hparent ih =>
      intro agr cgr ha hc
      have hceq : cgr = _ := some_inj (hc.symm.trans hchild)
      subst cgr
      rcases hw.parent_ok _ _ _ hchild hparent with ⟨pgr, hp, _hlt, hroot⟩
      have hprefixRoot := ih agr pgr ha hp
      exact hroot.trans hprefixRoot

/-- A record carrying root-allocation r is in r's ancestry lineage. The recursion
is justified by strict generation decrease; there is no fixed ancestry depth. -/
theorem rootAllocated_implies_lineage {s : State} (hw : GrantWellFormed s)
    {r g : GrantID} {gr : GrantRecord}
    (hg : s.gamma g = some gr) (hroot : gr.rootAllocation = r) :
    InLineage s r g := by
  generalize hgen : gr.generation = n
  induction n using Nat.strongRecOn generalizing g gr with
  | ind n ih =>
      by_cases hnone : gr.parent = none
      · have hself := hw.root_ok g gr hg hnone
        exact Or.inl (hroot.symm.trans hself)
      · cases hpar : gr.parent with
        | none => exact False.elim (hnone hpar)
        | some p =>
            rcases hw.parent_ok g gr p hg hpar with ⟨pgr, hp, hlt, halloc⟩
            have hproot : pgr.rootAllocation = r := halloc.symm.trans hroot
            have hlt' : pgr.generation < n := by simpa only [← hgen] using hlt
            have hpLine : InLineage s r p := ih pgr.generation hlt' hp hproot rfl
            rcases hpLine with hself | hanc
            · subst p
              exact Or.inr (.direct hg hpar)
            · exact Or.inr (.extend hanc hg hpar)

/-- Correspondence lemma: for a canonical root, executable root-allocation
membership is semantically equivalent to actual ancestry-lineage membership. -/
theorem rootAllocated_iff_lineage {s : State} (hw : GrantWellFormed s)
    {r g : GrantID} (hcanon : CanonicalRoot s r) :
    RootAllocated s r g ↔ (GrantExists s g ∧ InLineage s r g) := by
  constructor
  · intro h
    rcases h with ⟨gr, hg, hroot⟩
    exact ⟨⟨gr, hg⟩, rootAllocated_implies_lineage hw hg hroot⟩
  · intro h
    rcases h with ⟨⟨gr, hg⟩, hline⟩
    rcases hcanon with ⟨rgr, hr, _hrparent, hrroot⟩
    rcases hline with rfl | hanc
    · exact ⟨gr, hg, by
        have heq : gr = rgr := some_inj (hg.symm.trans hr)
        subst gr
        exact hrroot⟩
    · have hsame := ancestor_same_rootAllocation hw hanc rgr gr hr hg
      exact ⟨gr, hg, hsame.trans hrroot⟩

/-- Exact finite-support membership correspondence required by C3. -/
theorem support_membership_exact {s : State} {ids : List GrantID}
    (hs : GammaSupportExact s ids) (g : GrantID) :
    g ∈ ids ↔ GrantExists s g := hs.member_iff g

private theorem lineageMass_congr {ids : List GrantID} {s t : State} {r d}
    (h : ∀ g, g ∈ ids → LineageContribution t r d g = LineageContribution s r d g) :
    LineageMass ids t r d = LineageMass ids s r d := by
  induction ids with
  | nil => rfl
  | cons g gs ih =>
      simp only [LineageMass]
      rw [h g (by simp)]
      rw [ih]
      intro x hx
      exact h x (by simp [hx])

private theorem lineageMass_mono {ids : List GrantID} {s t : State} {r d}
    (h : ∀ g, g ∈ ids → LineageContribution t r d g ≤ LineageContribution s r d g) :
    LineageMass ids t r d ≤ LineageMass ids s r d := by
  induction ids with
  | nil => exact Nat.le_refl 0
  | cons g gs ih =>
      simp only [LineageMass]
      exact Nat.add_le_add (h g (by simp)) (ih (by
        intro x hx
        exact h x (by simp [hx])))

private theorem initial_mass_eq {ids : List GrantID} {s0 : State}
    {alloc : InitialAllocation} (hledger : InitialLedger s0 alloc) (r d) :
    LineageMass ids s0 r d = InitialProvision ids s0 alloc r d := by
  induction ids with
  | nil => rfl
  | cons g gs ih =>
      simp only [LineageMass, InitialProvision]
      unfold LineageContribution InitialContribution
      cases hgr : s0.gamma g with
      | none => simp [hgr, ih]
      | some gr =>
          simp [hgr, hledger g d, ih]

private theorem reserve_total_eq {s t : State} {g q}
    (h : ReserveBudget s t g q) (x : GrantID) (d : BudgetDim) :
    (t.budget x d).total = (s.budget x d).total := by
  by_cases hx : x = g
  · subst x
    rw [h.atOwner d]
    simp only [BudgetCell.total]
    have he := h.enough d
    omega
  · rw [h.other x hx]

private theorem settle_total_eq {s t : State} {g q refund consumed}
    (h : SettleBudget s t g q refund consumed) (x : GrantID) (d : BudgetDim) :
    (t.budget x d).total = (s.budget x d).total := by
  by_cases hx : x = g
  · subst x
    rw [h.atOwner d]
    simp only [BudgetCell.total]
    have hs := h.split d
    have he := h.enough d
    omega
  · rw [h.other x hx]

private theorem burn_total_eq {s t : State} {g q}
    (h : BurnOutstanding s t g q) (x : GrantID) (d : BudgetDim) :
    (t.budget x d).total = (s.budget x d).total := by
  by_cases hx : x = g
  · subst x
    rw [h.atOwner d]
    simp only [BudgetCell.total]
    have he := h.enough d
    omega
  · rw [h.other x hx]

private theorem reconcile_total_eq {s t : State} {g}
    (h : ReconcileBudget s t g) (x : GrantID) (d : BudgetDim) :
    (t.budget x d).total = (s.budget x d).total := by
  by_cases hx : x = g
  · subst x
    exact h.atOwner d
  · rw [h.other x hx]

private theorem destroy_total_le {s t : State} {g q}
    (h : DestroyBudget s t g q) (x : GrantID) (d : BudgetDim) :
    (t.budget x d).total ≤ (s.budget x d).total := by
  by_cases hx : x = g
  · subst x
    rw [h.atOwner d]
    simp only [BudgetCell.total]
    have he := h.enough d
    omega
  · rw [h.other x hx]
    exact Nat.le_refl _

private theorem contribution_eq_of_gamma_total {s t : State} {r d}
    (hgamma : t.gamma = s.gamma)
    (htotal : ∀ g, (t.budget g d).total = (s.budget g d).total)
    (g : GrantID) :
    LineageContribution t r d g = LineageContribution s r d g := by
  unfold LineageContribution
  rw [hgamma]
  cases hgr : s.gamma g with
  | none => simp [hgr]
  | some gr => simp [hgr, htotal g]

private theorem lineage_eq_of_gamma_total {ids : List GrantID} {s t : State} {r d}
    (hgamma : t.gamma = s.gamma)
    (htotal : ∀ g, (t.budget g d).total = (s.budget g d).total) :
    LineageMass ids t r d = LineageMass ids s r d := by
  apply lineageMass_congr
  intro g _
  exact contribution_eq_of_gamma_total hgamma htotal g

private theorem lineage_eq_of_state_budget {ids : List GrantID} {s t : State} {r d}
    (hgamma : t.gamma = s.gamma) (hbudget : t.budget = s.budget) :
    LineageMass ids t r d = LineageMass ids s r d := by
  apply lineage_eq_of_gamma_total hgamma
  intro g
  rw [hbudget]

private theorem revoke_mass_eq {ids : List GrantID} {s t : State} {r d g}
    (h : Revoke s t g) : LineageMass ids t r d = LineageMass ids s r d := by
  rcases h.gammaUpdate.post with
    ⟨old, new, hsold, htnew, hroot, _hp, _hpv, _hgen, _hver, _hsubj,
      _hperm, _hvalid, _hdel, _hactive⟩
  apply lineageMass_congr
  intro x _
  by_cases hx : x = g
  · subst x
    unfold LineageContribution
    rw [hsold, htnew, h.budgetSame]
    simp [hroot]
  · have hg := h.gammaUpdate.preserveOther x hx
    unfold LineageContribution
    rw [hg, h.budgetSame]

private theorem attenuate_mass_le {ids : List GrantID} {s t : State} {r d g q}
    (h : SelfAttenuate s t g q) : LineageMass ids t r d ≤ LineageMass ids s r d := by
  rcases h.gammaUpdate.post with
    ⟨old, new, hsold, htnew, hroot, _hp, _hpv, _hgen, _hsubj,
      _hperm, _hvalid, _hwf, _hdel, _hactive⟩
  apply lineageMass_mono
  intro x _
  by_cases hx : x = g
  · subst x
    unfold LineageContribution
    rw [hsold, htnew]
    have htot := destroy_total_le h.budgetUpdate g d
    by_cases hr : old.rootAllocation = r
    · have hrn : new.rootAllocation = r := hroot.trans hr
      simp [hr, hrn, htot]
    · have hrn : new.rootAllocation ≠ r := by
        intro hnr
        exact hr (hroot.symm.trans hnr)
      simp [hr, hrn]
  · have hg := h.gammaUpdate.preserveOther x hx
    have hb := h.budgetUpdate.other x hx
    unfold LineageContribution
    rw [hg, hb]
    exact Nat.le_refl _

private theorem provision_mass_eq_aux {ids : List GrantID} {s t : State}
    {key query : GrantID} {d : BudgetDim} {delta : BudgetDim → Nat}
    (hn : ids.Nodup) (hmem : key ∈ ids)
    (hgamma : t.gamma = s.gamma)
    (hkey : ∃ gr, s.gamma key = some gr ∧ gr.rootAllocation = key)
    (hrootTotal : (t.budget key d).total = (s.budget key d).total + delta d)
    (hother : ∀ g, g ≠ key → t.budget g = s.budget g) :
    LineageMass ids t query d =
      LineageMass ids s query d + if key = query then delta d else 0 := by
  induction ids with
  | nil => simp at hmem
  | cons g gs ih =>
      have hnodupTail : gs.Nodup := (List.nodup_cons.mp hn).2
      have hkeyNotTail : g = key → key ∉ gs := by
        intro hgeq
        subst g
        exact (List.nodup_cons.mp hn).1
      by_cases hgk : g = key
      · subst g
        have htailEq : LineageMass gs t query d = LineageMass gs s query d := by
          apply lineageMass_congr
          intro x hx
          have hxk : x ≠ key := by
            intro heq
            subst x
            exact (List.nodup_cons.mp hn).1 hx
          unfold LineageContribution
          rw [hgamma, hother x hxk]
        rcases hkey with ⟨gr, hgr, halloc⟩
        simp only [LineageMass]
        unfold LineageContribution
        rw [hgamma]
        rw [hgr]
        simp only
        rw [htailEq]
        by_cases hkq : key = query
        · subst query
          simp only [halloc, if_pos]
          rw [hrootTotal]
          exact Nat.add_right_comm _ _ _
        · have hneq : gr.rootAllocation ≠ query := by
            intro heq
            exact hkq (halloc.symm.trans heq)
          simp [hneq, hkq]
      · have hmemTail : key ∈ gs := by
          rcases List.mem_cons.mp hmem with hkg | htail
          · exact False.elim (hgk hkg.symm)
          · exact htail
        have hheadEq : LineageContribution t query d g = LineageContribution s query d g := by
          unfold LineageContribution
          rw [hgamma, hother g hgk]
        simp only [LineageMass]
        rw [hheadEq]
        rw [ih hnodupTail hmemTail]
        omega

private theorem provision_mass_eq {ids : List GrantID} {s t : State}
    {key query : GrantID} {d : BudgetDim} {delta : BudgetDim → Nat}
    (hsupport : GammaSupportExact s ids)
    (hgamma : t.gamma = s.gamma)
    (hb : ProvisionBudget s t key delta)
    (hcanon : CanonicalRoot s key) :
    LineageMass ids t query d =
      LineageMass ids s query d + if key = query then delta d else 0 := by
  have hmem : key ∈ ids := (hsupport.member_iff key).2 hb.rootExists
  rcases hcanon with ⟨gr, hgr, _hparent, halloc⟩
  have htot : (t.budget key d).total = (s.budget key d).total + delta d := by
    rw [hb.atRoot d]
    simp [BudgetCell.total]
    omega
  exact provision_mass_eq_aux hsupport.nodup hmem hgamma
    ⟨gr, hgr, halloc⟩ htot hb.other

private theorem delegate_mass_eq_aux {ids : List GrantID} {s t : State}
    {parent child : GrantID} {rec : GrantRecord} {q : BudgetDim → Nat}
    (hn : ids.Nodup)
    (hparentMem : parent ∈ ids)
    (hchildNot : child ∉ ids)
    (h : Delegate s t parent child rec q)
    (query : GrantID) (d : BudgetDim) :
    LineageMass (child :: ids) t query d = LineageMass ids s query d := by
  rcases h.gammaUpdate.parentPre with
    ⟨pgr, hp, _hgen, _hpv, hrootEq⟩
  have hpne : parent ≠ child := by
    intro heq
    subst parent
    rw [h.gammaUpdate.fresh] at hp
    contradiction
  have hchildTotal : (t.budget child d).total = q d := by
    rw [h.budgetUpdate.childPost d]
    simp [BudgetCell.total]
  have hparentTotal : (t.budget parent d).total + q d = (s.budget parent d).total := by
    rw [h.budgetUpdate.parentPost d]
    simp only [BudgetCell.total]
    have he := h.budgetUpdate.enough d
    omega
  have hparentGamma : t.gamma parent = s.gamma parent :=
    h.gammaUpdate.preserveOther parent hpne
  have hchildGamma : t.gamma child = some rec := h.gammaUpdate.childPost
  induction ids with
  | nil => simp at hparentMem
  | cons g gs ih =>
      have hnodupTail : gs.Nodup := (List.nodup_cons.mp hn).2
      by_cases hgp : g = parent
      · subst g
        have htailEq : LineageMass gs t query d = LineageMass gs s query d := by
          apply lineageMass_congr
          intro x hx
          have hxp : x ≠ parent := by
            intro heq
            subst x
            exact (List.nodup_cons.mp hn).1 hx
          have hxc : x ≠ child := by
            intro heq
            subst x
            exact hchildNot (by simp [hx])
          unfold LineageContribution
          rw [h.gammaUpdate.preserveOther x hxc, h.budgetUpdate.other x hxp hxc]
        simp only [LineageMass]
        unfold LineageContribution
        rw [hchildGamma, hparentGamma, hp]
        rw [hchildTotal]
        rw [htailEq]
        by_cases hqr : pgr.rootAllocation = query
        · have hcr : rec.rootAllocation = query := hrootEq.trans hqr
          simp [hqr, hcr]
          omega
        · have hcr : rec.rootAllocation ≠ query := by
            intro heq
            exact hqr (hrootEq.symm.trans heq)
          simp [hqr, hcr]
      · have hparentTail : parent ∈ gs := by
          rcases List.mem_cons.mp hparentMem with hpg | htail
          · exact False.elim (hgp hpg.symm)
          · exact htail
        have hgc : g ≠ child := by
          intro heq
          subst g
          exact hchildNot (by simp)
        have hheadEq : LineageContribution t query d g = LineageContribution s query d g := by
          unfold LineageContribution
          rw [h.gammaUpdate.preserveOther g hgc, h.budgetUpdate.other g hgp hgc]
        have hchildNotTail : child ∉ gs := by
          intro hc
          exact hchildNot (by simp [hc])
        have hi := ih hnodupTail hparentTail hchildNotTail
        simp only [LineageMass] at hi ⊢
        rw [hheadEq]
        omega

private theorem delegate_mass_eq {ids : List GrantID} {s t : State}
    {parent child : GrantID} {rec : GrantRecord} {q : BudgetDim → Nat}
    (hsupport : GammaSupportExact s ids)
    (h : Delegate s t parent child rec q)
    (query : GrantID) (d : BudgetDim) :
    LineageMass (child :: ids) t query d = LineageMass ids s query d := by
  rcases h.gammaUpdate.parentPre with ⟨pgr, hp, _hgen, _hpv, _hrootEq⟩
  have hparentMem : parent ∈ ids :=
    (hsupport.member_iff parent).2 ⟨pgr, hp⟩
  have hchildNot : child ∉ ids := by
    intro hm
    rcases (hsupport.member_iff child).1 hm with ⟨cgr, hc⟩
    rw [h.gammaUpdate.fresh] at hc
    contradiction
  exact delegate_mass_eq_aux hsupport.nodup hparentMem hchildNot h query d

private theorem delegate_canonicalRoot_pre
    {s t : State} {parent child : GrantID} {rec : GrantRecord} {q : BudgetDim → Nat}
    (h : Delegate s t parent child rec q) {r : GrantID}
    (hroot : CanonicalRoot t r) : CanonicalRoot s r := by
  rcases hroot with ⟨gr, ht, hp, hra⟩
  by_cases hrc : r = child
  · rw [hrc] at ht
    have hreceq : gr = rec := some_inj (ht.symm.trans h.gammaUpdate.childPost)
    subst gr
    rw [h.gammaUpdate.parentLink] at hp
    contradiction
  · have hEq := h.gammaUpdate.preserveOther r hrc
    rw [hEq] at ht
    exact ⟨gr, ht, hp, hra⟩

private theorem revoke_canonicalRoot_pre
    {s t : State} {g r : GrantID}
    (h : Revoke s t g) (hroot : CanonicalRoot t r) : CanonicalRoot s r := by
  rcases hroot with ⟨gr, ht, hp, hra⟩
  rcases h.gammaUpdate.post with
    ⟨old, new, hsold, htnew, hrootEq, hparentEq, _hpv, _hgen, _hver,
      _hsubj, _hperm, _hvalid, _hdel, _hactive⟩
  by_cases hrg : r = g
  · rw [hrg] at ht
    have hneweq : gr = new := some_inj (ht.symm.trans htnew)
    subst gr
    exact ⟨old, by simpa [hrg] using hsold,
      by simpa [hparentEq] using hp, by simpa [hrootEq] using hra⟩
  · have hEq := h.gammaUpdate.preserveOther r hrg
    rw [hEq] at ht
    exact ⟨gr, ht, hp, hra⟩

private theorem attenuate_canonicalRoot_pre
    {s t : State} {g r : GrantID} {q : BudgetDim → Nat}
    (h : SelfAttenuate s t g q) (hroot : CanonicalRoot t r) : CanonicalRoot s r := by
  rcases hroot with ⟨gr, ht, hp, hra⟩
  rcases h.gammaUpdate.post with
    ⟨old, new, hsold, htnew, hrootEq, hparentEq, _hpv, _hgen,
      _hsubj, _hperm, _hvalid, _hwf, _hdel, _hactive⟩
  by_cases hrg : r = g
  · rw [hrg] at ht
    have hneweq : gr = new := some_inj (ht.symm.trans htnew)
    subst gr
    exact ⟨old, by simpa [hrg] using hsold,
      by simpa [hparentEq] using hp, by simpa [hrootEq] using hra⟩
  · have hEq := h.gammaUpdate.preserveOther r hrg
    rw [hEq] at ht
    exact ⟨gr, ht, hp, hra⟩

/-- Every final state of a BudgetHistory is an ordinary ReachableFrom state; the
history adds only proof-level support/provision indexing. -/
theorem budgetHistory_to_reachable {judge s0 ids0 alloc n s ids es}
    (h : BudgetHistory judge s0 ids0 alloc n s ids es) : ReachableFrom s0 s :=
  h.reachable

/-- T4 — Budget / Effectability Conservation. For every arbitrary-length frozen
in-epoch history, every root-lineage bucket and every budget dimension, actual
Gamma/B lineage mass is bounded by the history-derived Provisioned ceiling. -/
theorem T4_budgetConservation {judge : ProvisionJudge}
    {s0 : State} {ids0 : List GrantID} {alloc : InitialAllocation}
    {n : Nat} {s : State} {ids : List GrantID} {es : List ProvisionEvent}
    (h0wf : WellFormed s0)
    (h : BudgetHistory judge s0 ids0 alloc n s ids es) :
    ∀ r d, CanonicalRoot s r →
      LineageMass ids s r d ≤
        Provisioned (InitialProvision ids0 s0 alloc) es r d := by
  induction h with
  | init hsupport hledger =>
      intro r d _hroot
      rw [initial_mass_eq hledger r d]
      exact Nat.le_refl _
  | prepare hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => reserve_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | commitStart hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_state_budget (ids := _) hs.same.gamma hs.budgetSame (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | commitSuccess hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => settle_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | commitAbort hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => settle_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | commitFaultUnknown hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => burn_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | reconcile hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => reconcile_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | delegate hprev hs hsupport ih =>
      intro r d hroot
      have hpreSupport := hprev.support
      have hmass := delegate_mass_eq hpreSupport hs r d
      rw [hmass]
      exact ih r d (delegate_canonicalRoot_pre hs hroot)
  | revoke hprev hs hsupport ih =>
      intro r d hroot
      rw [revoke_mass_eq hs]
      exact ih r d (revoke_canonicalRoot_pre hs hroot)
  | selfAttenuate hprev hs hsupport ih =>
      intro r d hroot
      exact Nat.le_trans (attenuate_mass_le hs (r := r) (d := d))
        (ih r d (attenuate_canonicalRoot_pre hs hroot))
  | updatePolicyOrdinary hprev hs hsupport ih =>
      intro r d hroot
      have hb := hs.budgetRule
      rw [lineage_eq_of_state_budget (ids := _) hs.gammaSame hb (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.gammaSame] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | updatePolicyPositive hprev hevent hsupport ih =>
      intro r d hroot
      have hpreSupport := hprev.support
      have hb : ProvisionBudget _ _ _ _ := by
        simpa using hevent.update.budgetRule
      rw [provision_mass_eq hpreSupport hevent.update.gammaSame hb
        hevent.canonicalRoot (query := r) (d := d)]
      simp only [Provisioned]
      have hprevBound := ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hevent.update.gammaSame] at ht
        exact ⟨gr, ht, hp, hra⟩)
      by_cases hrr : _ = r
      · simp [hrr]
        exact Nat.add_le_add_right hprevBound _
      · simp [hrr]
        exact hprevBound
  | expireReservation hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_gamma_total hs.same.gamma
        (fun g => settle_total_eq hs.budgetUpdate g d) (ids := _) (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.same.gamma] at ht
        exact ⟨gr, ht, hp, hra⟩)
  | expireGrant hprev hs hsupport ih =>
      intro r d hroot
      rw [lineage_eq_of_state_budget (ids := _) hs.gammaSame hs.budgetSame (r := r) (d := d)]
      exact ih r d (by
        rcases hroot with ⟨gr, ht, hp, hra⟩
        rw [hs.gammaSame] at ht
        exact ⟨gr, ht, hp, hra⟩)

/-- E3 does not conserve across incompatible theorem epochs. Instead an explicit
successor allocation establishes the new epoch's n=0 T4 base exactly. -/
theorem T4_e3_successor_epoch_start {s t : State} {ids : List GrantID}
    {alloc : InitialAllocation}
    (he3 : ReprovisionTCB s t)
    (hsupport : GammaSupportExact t ids)
    (hledger : InitialLedger t alloc) :
    ∀ r d, CanonicalRoot t r →
      LineageMass ids t r d ≤ InitialProvision ids t alloc r d := by
  have _ := he3.epochChanged
  have _ := hsupport
  intro r d _hroot
  rw [initial_mass_eq hledger r d]
  exact Nat.le_refl _

end EffectKernel
