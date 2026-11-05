module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.FrequencyRealization
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WeightedPrincipalLocalization.CommutatorBounds.SourceIndependentBounds.KernelSobolev.Forward.Coordinates

/-!
# Sobolev control of the original angular frequency factor

The scalar factor in the terminal physical-tail identity preserves the actual
Fourier Sobolev scale. The proof uses its literal Fourier action and the
already proved exact identification of the vector Sobolev norm; it does not
introduce a surrogate norm or discard low frequencies. Consumer: the source
tail in `actualAngularPDO_sub_identity_comp_rightLocalizer_eq_tails`, for
`app:ch_regular:eq:resolved-angular-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory FourierTransform

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral LowBounds Pseudodifferential
open FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds

variable {d r : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The original real angular frequency multiplier is contractive on every
actual Fourier Sobolev order. Its only analytic input is the primitive
pointwise scalar bound, supplied for the finite symbol (including the fixed
low bump) by `actualFamily_sum_dilatedConicMask_mem_Icc`. This propagates the
physical source tail without an accuracy-dependent loss
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem scalarPhysicalFrequencyOperator_fourierSobolev_bound
    (b : E → ℝ) (hb : Continuous b) (hbound : ∀ ξ, ‖b ξ‖ ≤ 1)
    (s : ℝ) (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (scalarPhysicalFrequencyOperator b hb hbound u) ∧
      vectorFourierSobolevNorm s (scalarPhysicalFrequencyOperator b hb hbound u) ≤
        vectorFourierSobolevNorm s u := by
  let w := fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 u : H) ξ
  have hw : MemLp w 2 volume := (frequencyKernel_memLp_weighted_fourier_iff s u).mpr hu
  let T := sourceCutMultiplier (r := r) (fun ξ ↦ b ((2 * Real.pi) • ξ))
    (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ))
  let v := scalarPhysicalFrequencyOperator b hb hbound u
  have hfourier : (𝓕 v : H) = T (𝓕 u) := by
    simp only [v, scalarPhysicalFrequencyOperator, ContinuousLinearMap.comp_apply,
      fourierInvCLM_apply, fourierCLM_apply, fourier_fourierInv_eq]
    rfl
  have he : T (hw.toLp w) =ᵐ[volume] fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 v : H) ξ := by
    rw [hfourier]
    filter_upwards [sourceCutMultiplier_coeFn (fun ξ ↦ b ((2 * Real.pi) • ξ))
      (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ)) (hw.toLp w),
      hw.coeFn_toLp,
      sourceCutMultiplier_coeFn (fun ξ ↦ b ((2 * Real.pi) • ξ))
        (hb.comp (by fun_prop)) (fun ξ ↦ hbound ((2 * Real.pi) • ξ)) (𝓕 u)]
      with ξ ht hwξ huξ
    rw [show T (hw.toLp w) ξ = (b ((2 * Real.pi) • ξ) : ℂ) • (hw.toLp w) ξ from ht,
      hwξ, show T (𝓕 u) ξ = (b ((2 * Real.pi) • ξ) : ℂ) • (𝓕 u : H) ξ from huξ]
    exact smul_comm _ _ _
  have hv : MemVectorFourierSobolev s v :=
    (frequencyKernel_memLp_weighted_fourier_iff s v).mp
      ((Lp.memLp (T (hw.toLp w))).ae_eq he)
  refine ⟨hv, ?_⟩
  change vectorFourierSobolevNorm s v ≤ _
  rw [← frequencyKernel_eLpNorm_weighted_fourier s v hv, ← eLpNorm_congr_ae he,
    ← Lp.norm_def]
  calc
    ‖T (hw.toLp w)‖ ≤ ‖T‖ * ‖hw.toLp w‖ := T.le_opNorm _
    _ ≤ 1 * ‖hw.toLp w‖ := mul_le_mul_of_nonneg_right
      (norm_sourceCutMultiplier_le _ _ _) (norm_nonneg _)
    _ = vectorFourierSobolevNorm s u := by
      rw [one_mul, Lp.norm_toLp, frequencyKernel_eLpNorm_weighted_fourier s u hu]

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
