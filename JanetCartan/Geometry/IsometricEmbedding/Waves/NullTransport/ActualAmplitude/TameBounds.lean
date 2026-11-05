module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.TameBounds.Joint

/-!
# Joint tame bounds for the constructed positive null amplitude

`exists_carrierScalarAmplitude_joint_tame` proves the scalar and nullvector
amplitude part of `app:ch_waves:eq:joint-tame` on the fixed physical image of
`Icc (-τ/2) (τ/2) ×ˢ closedBall p₀ (R/64)`. The reserve is `D = 13`.
Fixed primitive `C¹²` immersion and `C⁵` initial-data budgets supply every low
bound; the literal time integral, exponential and scalar are estimated here.

Its coefficient, flow, smoothness and range hypotheses are the retained outputs
of `exists_projected_local_positive_amplitude`. The final null-transport
assembly must instantiate this conditional analytic deduction with that
producer's SAME projected frame and maps, retaining its finite coverage and
uniform positivity. This helper does not assert unconditional existence.
-/
