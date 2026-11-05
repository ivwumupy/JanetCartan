module

public import JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
public import JanetCartan.Iteration.PhysicalMean.OriginalWeightBridgeTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalWeightBridgeTemplate

/-!
# Original physical angular restoration and one-sample normal benchmark

Apply the literal complete-wave identities to the SAME original22 incidence
selection, masks, transverse direction and detector radii. The full physical
source uses the original angular mask, while the retained inner normal uses
its detector-only realization. The external χ is task74's ONE protected cutoff;
it is never replaced by the square root of the inner carrier weight.

The direct positive-τ Graw identity is proved through the actual full primary
wave and entire fixed source response, NOT inferred from a Gram equality.
The canonical consequences in the imported template retain the SAME uncut Q₀:
Afull=a Adetector, Dfull=a² Ddetector, linear mean mass μouter*a² and quadratic
mass μouter*a⁴. The full positive baseline and its zero atom remain UNSCALED
and retain μouter. Finite inner labels extend by zero into the actual outer
labels on one window/mesh/global shift; the continuum normal comparison uses
full-lattice block integrals, even when the bounding cubes differ.

These exact physical/algebraic identities do not discharge the parent analytic
realization, joint source-parameter profiles, positive initialization, forcing
or Picard construction. In particular, the equality of the linear normal
benchmark is NOT an identification of the full quadratic physical mean.

Consumers: the original physical fixed-source mean, the retained native prefix
comparison and `app:ch_mean_pairs:eq:mean-current-canonical`,
`app:ch_mean_pairs:eq:mean-exact-self-change`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

construct_original_weight_bridge
