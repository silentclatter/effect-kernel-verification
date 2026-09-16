import Lean

/-- Local Phase C-R3 compatibility shim for the pinned Lean 4.34.0 distribution,
which does not ship `Std.Tactic.Omega`. Every invocation expands to Lean's
kernel-checked `grind` tactic and adds no proof assumption. -/
macro "omega" : tactic => `(tactic| grind)
