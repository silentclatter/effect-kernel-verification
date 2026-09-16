# Effect Kernel R0.2c — Phase C-R Lean 4

Status: final Phase C prover source for T0, T9, T1, T2, and T4 only.

Pinned toolchain: `leanprover/lean4:v4.34.0`.

This project formalizes only the frozen R0.2c abstract semantics required for the five authorized foundational obligations. It does not begin T16, T18, T19, T20, T21, T22, T23, or T25 and does not modify the frozen architecture.

Trusted runtime state remains the exact seven-component tuple represented by `State`:

`(C_e, G_n, Gamma_n, B_n, L_n, M_auth_n, e_n)`

The trusted monotonic clock is intentionally **not** a field of `State`; theorem statements quantify the relevant trusted time separately, matching frozen `clock(K_n)` semantics without adding runtime state.

`EffectKey` is represented exactly as `EpochID × EffectID`. `EXPIRE_RESERVATION` is represented explicitly as `RESERVED → ABORTED`, and reconciliation uses only the frozen `UNKNOWN → UNKNOWN | COMMITTED | ABORTED` outcomes.

`TrustedStep` is the actual in-epoch theorem-relevant transition relation. Its constructors carry only the corresponding transition-semantic witnesses; no constructor carries T0, T9, T1, T2, T4, a global conservation conclusion, or a free-standing budget certificate. E3 is represented separately by `ReprovisionTCB` and is not an in-epoch `TrustedStep`.

T4 uses actual Gamma/B/history semantics. `LineageMass` sums `BudgetCell.total = avail + resv + cons` over the exact proof-only finite support of Gamma for the relevant root allocation. `Provisioned` is derived from the initial ledger plus prior valid positive-provision events recorded by `BudgetHistory`. `GammaSupportExact` is proof infrastructure only. The checked lemma `rootAllocated_iff_lineage` establishes the semantic equivalence between root-allocation membership and actual ancestry-lineage membership under structural grant well-formedness; `support_membership_exact` establishes exact support enumeration.

Positive E2+ provisioning is an `UpdatePolicy (.positiveProvision r delta)` classification. Its `PositiveProvisioningEvent` records a predecessor-only `ProvisionJudge s r delta`; newly provisioned quantity therefore does not authorize its own creation. Ordinary in-epoch transitions leave the provisioning event history unchanged. E3 starts a successor theorem epoch only through explicit successor provisioning, formalized by `T4_e3_successor_epoch_start`.

Promotion rule: no theorem is `PROVED` merely because source compiles. Final promotion additionally requires closed source-to-frozen correspondence, an assumption ledger reconciled against `#print axioms`, a clean strengthened proof-hole/unsafe scan, successful `lake build`, explicit declaration checks, and one fresh integrated GitHub Actions replay on the exact final commit.

Controlling predecessor source hashes recovered from the frozen Phase B package:

- `R0.2C_DEFINITION_TYPE_CLOSURE.md`: `6962942a047d40ea7bf2237bc2fa3b73f1b962c27cec4d3cbd2c4aa4c71caa5d`
- `R0.2C_TRANSITION_SIGNATURES.md`: `5d1f01a3d78aa7a9d16fc1216519efcfbbb28296bc683787c2c1adb1f017df4d`
- `R0.2C_PROOF_ABSTRACTION_BINDINGS.md`: `1e8d52fe79201c75c1394e7da09f39cde2982ea74d2fa326a056231c444202e2`
- `THEOREM_OBLIGATION_LEDGER_R0.2C.md`: `8c6ca17a77b70d1942305db45232a19413ba7ccd510e39b117074668248a2d98`
- `EFFECT_KERNEL_SPEC_R0.2c_FORMAL_CLOSURE_PATCH.md`: `95c7e859f46b43ed83c8f04fda3ec4770ce56d70a51118e978c9877f5c440950`

Mandatory predecessor limitation remains unchanged: the Phase B export did not retain the final patched R0.2c `.tla`, B0-B15 `.cfg` files, or individual stage logs. Those bytes are not reconstructed here.
