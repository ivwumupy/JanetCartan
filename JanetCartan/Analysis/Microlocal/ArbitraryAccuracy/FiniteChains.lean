module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Observation

/-!
# Quantitative deduction for a finite localized chain

For `app:ch_regular:lem:finite-chain`, the original source tail, polynomial
L² bounds for the near factors, polynomial Sobolev costs for the full factors,
and individual factor-localization estimates imply arbitrary decay of the
complete observed chain. Constants in the individual estimates may depend on
accuracy; their losses, operators and proof masks do not.

The proof reuses `ResponseTransfer.factorChain_sub_near_rapidDecayAt` and the
finite-Neumann scalar absorption. It derives all near-prefix bounds and
complementary errors rather than assuming a successful chain estimate.
`finiteChain_observation_rapidDecayAt` keeps an estimate for the full terminal
observation, including its identity and bounded-frequency discrepancy.

These are conditional deductions. The actual common finite residual family,
its nested masks and the individual estimates on those masks are not
constructed here. Their producers are `RegularSector`, `EvolutionProtection`,
`FiniteChain.Graph`, and `EvolutionIntegratedLocalization`; the full response
parent must match the same geometry, cutoffs, spaces and operators before
using this result in `rapidDecayAt_inverse_of_finite_chains`.
-/
