import Lean

/-- Local compatibility macro for the pinned Lean 4.34.0 toolchain. -/
macro "omega" : tactic => `(tactic| grind)
