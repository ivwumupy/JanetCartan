module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalDataBounds.Variation

/-!
# Individual canonical data and their Fourier variation

Checked conditional deductions of `app:ch_mean_pairs:eq:mean-current-canonical`,
`app:ch_mean_pairs:eq:mean-canonical-bounds`, `main:eq:old-canonical`, and
`main:eq:variation`. The initial datum is the shared Lebesgue inverse Fourier
synthesis of the real Hilbert adjoint `A* Q0 r`, and the physical change applies
the current wave map to precisely that datum. Initial cutoffs remain inside the
physical map; the separate original zero atom is untouched.

The leaves prove support below `C K`, Fourier `L¹` bounded by `C' K^p ‖r‖₂`,
and the sum of initial and physical `C^m` norms bounded by `C_m K^(m+p) ‖r‖₂`,
where `p=(n+1)/2`. Constants are explicit and independent of band count and
sample weights. The raw `n/2` exponent and individual adjoint's extra `1/2`
are kept separate. Finite accumulation preserves support and obeys the summed
Fourier variation estimate, without dividing by sample weights.

For `jc-current-canonical` and `jc-current-mean`, the remaining instantiation
inputs are: measurable bounded masks and dyadic ceilings from the raw-primary
construction; `‖A‖ ≤ C_A √K` from the actual corrected atoms; `‖Q0‖ ≤ C_Q`
from the continuum L² inverse; and the current physical wave estimate
`‖G(f)‖_{C^m} ≤ P_m (K+L)^m ‖f̂‖₁`, with `0 ≤ L ≤ K` and `K ≥ 1`.
The finite variation corollary additionally consumes the mean recurrence's
residual sum budget. No unconditional geometric construction is asserted.
-/
