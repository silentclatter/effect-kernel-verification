import EffectKernel.Transitions

namespace EffectKernel

inductive ReachableFrom (f0 : ProofFrame) : ProofFrame → Prop where
  | refl : ReachableFrom f0 f0
  | step {f f'} {kind : TransitionKind} : ReachableFrom f0 f → TrustedStep kind f f' → ReachableFrom f0 f'

inductive EpochReachableFrom (f0 : ProofFrame) : ProofFrame → Prop where
  | refl : EpochReachableFrom f0 f0
  | step {f f'} {kind : TransitionKind} : EpochReachableFrom f0 f → TrustedStep kind f f' →
      f.state.epoch = f'.state.epoch → EpochReachableFrom f0 f'

end EffectKernel
