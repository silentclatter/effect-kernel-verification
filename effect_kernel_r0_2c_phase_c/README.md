# Effect Kernel R0.2c — Phase C-R Lean 4

Status: prover-enabled re-execution source for T0, T9, T1, T2, and T4 only.

Pinned toolchain: `leanprover/lean4:v4.34.0`.

This project formalizes only the frozen R0.2c abstract semantics required for the five authorized foundational obligations. It does not begin T16, T18, T19, T20, T21, T22, T23, or T25 and does not modify the frozen architecture.

Trusted runtime state remains the seven-component tuple represented by `State`:

`(C_e, G_n, Gamma_n, B_n, L_n, M_auth_n, e_n)`

The trusted monotonic clock is intentionally **not** a field of `State`; theorem statements quantify the relevant trusted time value separately, matching frozen `clock(K_n)` semantics and avoiding any added runtime state.

`EffectKey` is represented exactly as `EpochID × EffectID`. The frozen proof-level `EXPIRE_RESERVATION` classification `RESERVED → ABORTED` is included explicitly in the lifecycle relation.

`ProofFrame.budgetView` is not trusted runtime state. It is a proof-only projection of the frozen Phase A history-derived functions `LineageMass(r,n,d)` and `Provisioned(r,n,d)`. `BudgetDelta` encodes the exact conservation classes required by the frozen transition signatures: ordinary non-increase with unchanged provisioned ceiling, independently authorized E2+ provisioning with matched ceiling increase, and explicit E3 successor reprovision.

The trusted transition relation is intentionally represented as a theorem-relevant over-approximation of the frozen transition signatures. `TransitionKind` contains only the frozen transition classes. `TrustedStep` requires all theorem-relevant semantic projections simultaneously: structural grant safety, lifecycle monotonicity/history preservation, fixed-epoch constitutional safety, and budget conservation. This adds no runtime field and does not authorize any transition absent from the frozen architecture; it is a proof relation over the frozen semantic effects.

Promotion rule: no theorem is `PROVED` merely because source exists. Promotion requires a clean GitHub Actions replay on branch `r0-2c-phase-c-lean`, Lean 4.34.0, `lake build` success, and a clean proof-hole scan with no `sorry`, `admit`, `axiom`, or `unsafe` in Lean proof sources.

Controlling predecessor source hashes recovered from the frozen Phase B package:

- `R0.2C_DEFINITION_TYPE_CLOSURE.md`: `6962942a047d40ea7bf2237bc2fa3b73f1b962c27cec4d3cbd2c4aa4c71caa5d`
- `R0.2C_TRANSITION_SIGNATURES.md`: `5d1f01a3d78aa7a9d16fc1216519efcfbbb28296bc683787c2c1adb1f017df4d`
- `R0.2C_PROOF_ABSTRACTION_BINDINGS.md`: `1e8d52fe79201c75c1394e7da09f39cde2982ea74d2fa326a056231c444202e2`
- `THEOREM_OBLIGATION_LEDGER_R0.2C.md`: `8c6ca17a77b70d1942305db45232a19413ba7ccd510e39b117074668248a2d98`
- `EFFECT_KERNEL_SPEC_R0.2c_FORMAL_CLOSURE_PATCH.md`: `95c7e859f46b43ed83c8f04fda3ec4770ce56d70a51118e978c9877f5c440950`

Mandatory predecessor limitation remains unchanged: the Phase B export did not retain the final patched R0.2c `.tla`, B0-B15 `.cfg` files, or individual stage logs. Those bytes are not reconstructed here.
