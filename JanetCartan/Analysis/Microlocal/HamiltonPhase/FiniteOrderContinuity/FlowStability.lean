module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Joint
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability.Symbols

/-!
# Finite-order comparison of common Hamilton flows

The flow continuity assertion in `app:lem:common-hamilton-phase` is proved for
any actual `ODE.IsSmoothFlowOn` flows. On each fixed compact inner joint
cylinder, `ODE.exists_cNorm_flow_sub_lt` gives a positive scalar tolerance in
the order-`m` field seminorm for any requested order-`m` flow accuracy.
`HamiltonPhase.exists_cNorm_hamiltonFlow_sub_lt` transfers this estimate to
scalar-symbol order `m + 1`.

The proof subtracts differentiated variational equations, bounds lower jets
inductively, and recovers joint derivatives by autonomous time augmentation.
No perturbation derivative above the requested field order is used. The
imported uniqueness results identify different common-flow construction
choices on the closed cylinder and all their interior jets.

The parent Hamilton-phase construction supplies the actual common flows from
the fixed low neighborhood and performs initial-section composition, inversion,
and phase recovery. Those remaining operations are outside this flow theorem.
-/
