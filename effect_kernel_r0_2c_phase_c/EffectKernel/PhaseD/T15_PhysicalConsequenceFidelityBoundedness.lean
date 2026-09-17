import EffectKernel.PhaseD.T5_ReservationPrecedesRelease
import EffectKernel.PhaseD.T6_UniqueAuthorizationLinearization
import EffectKernel.PhaseD.T7_AuthorizationSnapshotSufficiency
import EffectKernel.PhaseD.T13_TargetContractCompliance
import EffectKernel.PhaseD.T14_ExactEffectBinding

namespace EffectKernel.PhaseD

open EffectKernel

/-- Proof-only abstract physical layer for the R1 A8-A11 boundary. None of
these fields is trusted Effect Kernel state. `occurred` and `downstream` are
independent observations; the separately named obligations relate them to a
trusted release, consequence denotation, cost, and target assumptions. -/
structure AbstractPhysicalLayer (E : FullEnv) where
  occurred : EffectKey → Nat → Nat → Prop
  downstream : {s0 z : State} → FullTrace E s0 z → EffectKey → Nat → Nat → Prop
  denotes : CanonicalEffect → Nat → Nat → Prop
  cost : Nat → BudgetDim → Nat
  projectionAdequate : CanonicalEffect → Nat → Prop
  a8Projection : ∀ a rho, projectionAdequate a rho
  a9DispatcherFidelity :
    ∀ {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey} {e rho : Nat},
      occurred k e rho → downstream h k e rho →
      ∃ j now before after,
        StepAt h j (.commitStart k now) before after ∧
        (projectionAdequate (E.decodeEffect (after.lifecycle k).effectAstId) rho →
          denotes (E.decodeEffect (after.lifecycle k).effectAstId) e rho)
  a10CostSoundness :
    ∀ {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey} {e rho : Nat}
      {j now : Nat} {before after : State},
      occurred k e rho → downstream h k e rho →
      StepAt h j (.commitStart k now) before after →
      ∀ d, cost e d ≤ (after.lifecycle k).reserved d
  a11TargetTruth : ∀ tcid, E.targetAssumptions tcid

/-- A step occurrence has a real suffix trace from its successor to the
terminal state. The existential keeps proof observations in Prop while the
trace witness itself remains proof-only data. -/
private theorem stepAt_suffix_exists
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {lbl : StepLabel} {a b : State}
    (ho : StepAt h i lbl a b) :
    ∃ hs : FullTrace E b z, True := by
  induction ho with
  | last hp hs =>
      exact ⟨.refl, True.intro⟩
  | @earlier s t lblEnd hp hsEnd i lbl a b ho ih =>
      rcases ih with ⟨tail, _⟩
      exact ⟨.step tail hsEnd, True.intro⟩

/-- If one observed step strictly precedes another, the first successor reaches
the second predecessor through the actual full trace. -/
private theorem trace_between_exists
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i j : Nat} {lblI lblJ : StepLabel} {a b c d : State}
    (hi : StepAt h i lblI a b)
    (hj : StepAt h j lblJ c d)
    (hij : i < j) :
    ∃ hm : FullTrace E b c, True := by
  induction hj generalizing i lblI a b with
  | @last c d lblJ hp hsJ =>
      cases hi with
      | last hpI hsI =>
          exact False.elim (Nat.lt_irrefl _ hij)
      | earlier hsEnd hiPrev =>
          exact stepAt_suffix_exists hiPrev
  | @earlier cEnd dEnd lblEnd hp hsEnd j lblJ c d hjPrev ih =>
      cases hi with
      | last hpI hsI =>
          have hjlt : j < hp.length := StepAt.index_lt_length hjPrev
          exact False.elim ((Nat.not_lt_of_ge (Nat.le_of_lt hjlt)) hij)
      | earlier hsEndI hiPrev =>
          exact ih hiPrev hij

/-- T15 — Physical Consequence Fidelity and Boundedness.

SUCCESSOR RESTATEMENT — ORIGINAL PHASE A BYTES NOT RECOVERED.

For a protected physical occurrence that is independently observed and declared
causally downstream of the trusted dispatcher, the separately named A8-A11
abstract obligations identify an actual COMMIT_START release. T5-T7 provide the
earlier reservation, unique linearization, and immutable predecessor snapshot;
T13 supplies target requirement inclusion; T14 proves that the dispatched
binding is exactly the binding authorized by that snapshot. The physical
occurrence is then within the declared consequence denotation and measured cost
is bounded by the reserved snapshot vector under the declared obligations.

This theorem applies only to mediated occurrences. It does not establish
complete mediation, deployment isolation, universal external exactly-once
behavior, or physical safety beyond the declared abstract bound. -/
theorem T15_physicalConsequenceFidelityBoundedness
    {E : FullEnv} (P : AbstractPhysicalLayer E)
    {s0 z : State} {h : FullTrace E s0 z} {k : EffectKey} {e rho : Nat}
    (hinitState : (s0.lifecycle k).state = .unseen)
    (hinitUsed : (s0.lifecycle k).used = false)
    (hocc : P.occurred k e rho)
    (hdown : P.downstream h k e rho) :
    ∃ j now before after σ,
      StepAt h j (.commitStart k now) before after ∧
      (∀ {i now' : Nat} {a b : State},
        StepAt h i (.commitStart k now') a b → i = j) ∧
      σ = snapshotOf before k now ∧
      AuthorizedFromSnapshot E σ ∧
      E.decodeEffect (after.lifecycle k).effectAstId =
        E.decodeEffect (σ.predecessor.lifecycle σ.effectKey).effectAstId ∧
      P.denotes (E.decodeEffect (σ.predecessor.lifecycle σ.effectKey).effectAstId) e rho ∧
      (∀ d, P.cost e d ≤ (σ.predecessor.lifecycle σ.effectKey).reserved d) ∧
      RequiredGuaranteesIncluded E σ.predecessor σ.effectKey ∧
      E.targetAssumptions (σ.predecessor.lifecycle σ.effectKey).tcid := by
  rcases P.a9DispatcherFidelity hocc hdown with
    ⟨j, now, before, after, ho, hdenIf⟩
  have hrelease : ProtectedRelease (.commitStart k now) k :=
    .commitStart k now
  rcases T5_reservationPrecedesRelease
      (E := E) (s0 := s0) (z := z) (h := h) (k := k)
      hinitState hinitUsed ho hrelease with
    ⟨i, g, q, prepNow, releaseNow, prepBefore, prepAfter,
      hij, hprep, hlbl, hpState, hpGrant, hpRes, hbeforeEq,
      hafterState, hafterLin⟩
  have hstart : FullStep E (.commitStart k now) before after :=
    StepAt.fullStep ho
  have hprepStep : FullStep E (.prepare k g q prepNow) prepBefore prepAfter :=
    StepAt.fullStep hprep
  rcases trace_between_exists hprep ho hij with ⟨hbetween, _⟩
  have h14 := T14_exactEffectBinding
    (E := E) (s := prepBefore) (t := prepAfter) (u := before)
    (k := k) (g := g) (q := q) (prepNow := prepNow)
    hprepStep hbetween
  have hdescPair := h14.1 hbetween hstart
  have hdesc : boundDescriptor E k before = boundDescriptor E k after :=
    hdescPair.2
  have heffect : E.decodeEffect (after.lifecycle k).effectAstId =
      E.decodeEffect (before.lifecycle k).effectAstId := by
    have hc := congrArg AuthorizationBoundDescriptor.canonicalEffect hdesc
    simpa [boundDescriptor] using hc.symm
  have hreserved : (after.lifecycle k).reserved = (before.lifecycle k).reserved := by
    have hr := congrArg AuthorizationBoundDescriptor.reserved hdesc
    simpa [boundDescriptor] using hr.symm
  have hproj := P.a8Projection
    (E.decodeEffect (after.lifecycle k).effectAstId) rho
  have hdenAfter : P.denotes
      (E.decodeEffect (after.lifecycle k).effectAstId) e rho :=
    hdenIf hproj
  have hdenBefore : P.denotes
      (E.decodeEffect (before.lifecycle k).effectAstId) e rho := by
    simpa [heffect] using hdenAfter
  have hcostAfter := P.a10CostSoundness hocc hdown ho
  have hcostBefore : ∀ d, P.cost e d ≤ (before.lifecycle k).reserved d := by
    intro d
    simpa [hreserved] using hcostAfter d
  have h6 := T6_uniqueAuthorizationLinearization
    (E := E) (s0 := s0) (z := z) (h := h) (k := k)
    hinitState hinitUsed
  have h7 := T7_authorizationSnapshotSufficiency
    (E := E) (s0 := s0) (z := z) (h := h) (k := k)
    hinitState hinitUsed ho
  have h13 := T13_targetContractCompliance
    (E := E) (s0 := s0) (z := z) (h := h) (k := k)
    hinitState hinitUsed ho
  let σ := snapshotOf before k now
  refine ⟨j, now, before, after, σ, ho, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i' now' a b hi'
    exact h6.1 hi' ho
  · exact h7.2.2.1
  · simpa [σ, snapshotOf] using heffect
  · simpa [σ, snapshotOf] using hdenBefore
  · intro d
    simpa [σ, snapshotOf] using hcostBefore d
  · simpa [σ, snapshotOf] using h13.2.1
  · simpa [σ, snapshotOf] using P.a11TargetTruth (before.lifecycle k).tcid

end EffectKernel.PhaseD
