import EffectKernel.Transitions

namespace EffectKernel

/-- Reflexive/transitive closure of the actual in-epoch trusted transition relation. -/
inductive ReachableFrom (s0 : State) : State → Prop where
  | refl : ReachableFrom s0 s0
  | step {s t} {kind : TransitionKind} : ReachableFrom s0 s → TrustedStep kind s t → ReachableFrom s0 t

end EffectKernel
