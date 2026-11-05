module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers.StrongLimit
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Multipliers.Schwartz

/-!
# Physical-frequency multipliers on the graph's vector L²

For `app:ch_regular_base:thm:actual-calculus`, Step 1, `multiplier j` is the
actual contraction `𝓕⁻ χ_j(2π·) 𝓕` on Euclidean-fiber Lebesgue L². It is
self-adjoint and converges strongly to the identity. `multiplier_toLp` and
`multiplier_toEuclideanSchwartz_toLp` identify its Schwartz action exactly;
`graphOperator_eq_graphOperator_schwartzMultiplier` proves the literal
source-first graph factorization without a bounded uncut graph assumption.

These results supply the parent construction's conditional `T_j = T.comp P_j`
and strong adjoint limit. Existence of the uncut bounded graph belongs to that
parent construction.
-/
