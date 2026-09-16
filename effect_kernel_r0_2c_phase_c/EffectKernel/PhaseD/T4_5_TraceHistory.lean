import EffectKernel.PhaseD.FullSemantics

namespace EffectKernel.PhaseD

open EffectKernel

/-- A proof-only observation that one concrete full-semantics step occurs at a
zero-based index in an arbitrary-length `FullTrace`.  This records no trusted
runtime state and adds no transition kind. -/
inductive StepAt {E : FullEnv} {s0 : State} :
    {z : State} → FullTrace E s0 z → Nat → StepLabel → State → State → Prop where
  | last {s t : State} {lbl : StepLabel}
      (h : FullTrace E s0 s) (hs : FullStep E lbl s t) :
      StepAt (.step h hs) h.length lbl s t
  | earlier {s t : State} {lblEnd : StepLabel}
      {h : FullTrace E s0 s} (hsEnd : FullStep E lblEnd s t)
      {i : Nat} {lbl : StepLabel} {a b : State}
      (ho : StepAt h i lbl a b) :
      StepAt (.step h hsEnd) i lbl a b

namespace StepAt

/-- Every observed step index is strictly below trace length. -/
theorem index_lt_length
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {lbl : StepLabel} {a b : State}
    (ho : StepAt h i lbl a b) : i < h.length := by
  induction ho with
  | last hp hs =>
      simp [FullTrace.length]
  | earlier hsEnd ho ih =>
      exact Nat.lt_trans ih (by simp [FullTrace.length])

/-- The observed transition is an actual full-semantics step. -/
theorem fullStep
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {lbl : StepLabel} {a b : State}
    (ho : StepAt h i lbl a b) : FullStep E lbl a b := by
  induction ho with
  | last hp hs => exact hs
  | earlier hsEnd ho ih => exact ih

/-- Lifecycle reachability from the observed step's successor to the terminal
state of the containing trace.  This is the trace-indexed form of the Phase C
T9 monotonic lifecycle proposition. -/
theorem lifecycle_from_successor
    {E : FullEnv} {s0 z : State} {h : FullTrace E s0 z}
    {i : Nat} {lbl : StepLabel} {a b : State}
    (ho : StepAt h i lbl a b) (k : EffectKey) :
    LifecycleReach (b.lifecycle k).state (z.lifecycle k).state := by
  induction ho with
  | last hp hs =>
      exact .refl _
  | @earlier s t lblEnd hp hsEnd i lbl a b ho ih =>
      exact LifecycleReach.trans ih
        (trustedStep_lifecycle_one (fullStep_to_trusted hsEnd) k)

end StepAt

/-- Independent semantic definition of the sole in-epoch release-bearing step.
It is not a certificate stored in `FullStep`: it classifies an already existing
frozen transition label. -/
inductive ProtectedRelease : StepLabel → EffectKey → Prop where
  | commitStart (k : EffectKey) (now : Nat) :
      ProtectedRelease (.commitStart k now) k

end EffectKernel.PhaseD
