module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.BoundedMultiplier
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.RemainderOperator
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.Convolution

/-!
# Reality of the Euclidean image operators

The real kernels prove that the actual bounded image inverse and local
remainder commute with real projection (`app:ch_background:prop:bg-frame`,
Step 1). For the inverse the Schwartz identity extends by L² density.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped SchwartzMap ContDiff
open JanetCartan.Pseudodifferential

namespace JanetCartan.ContinuumNormalReduction.ImageNormal

/-- Scalar real projection for the real image channel
(`app:ch_background:defn:bg-row`). -/
def imageScalarRealProjection : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "P" => imageScalarRealProjection.compLpL 2 (volume : Measure E)

private theorem projection_toLp (u : 𝓢(E, ℂ)) :
    P (u.toLp 2) = (u.postcompCLM imageScalarRealProjection).toLp 2 := by
  apply Lp.ext
  filter_upwards [imageScalarRealProjection.coeFn_compLpL (u.toLp 2), u.coeFn_toLp 2,
    (u.postcompCLM imageScalarRealProjection).coeFn_toLp 2] with x hx hy hz
  rw [hx, hy, hz, SchwartzMap.postcompCLM_apply]

private theorem projection_schwartz_multiplier (u : 𝓢(E, ℂ)) :
    (schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u).postcompCLM
      imageScalarRealProjection =
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
      (u.postcompCLM imageScalarRealProjection) := by
  ext x
  rw [SchwartzMap.postcompCLM_apply, imageBesselMultiplier_eq_convolution,
    imageBesselMultiplier_eq_convolution,
    ← imageScalarRealProjection.integral_comp_comm (integrable_imageBesselKernel_mul_schwartz u x)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [imageScalarRealProjection, SchwartzMap.postcompCLM_apply, Complex.mul_re]

/-- The actual Euclidean image inverse preserves real data, proved from the
real convolution kernel and density (`app:ch_background:defn:bg-row`). -/
theorem imageBesselL2Operator_realProjection (f : L²) :
    P (imageBesselL2Operator f) = imageBesselL2Operator (P f) := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  refine hdense.induction_on f ?_ ?_
  · exact isClosed_eq ((P).continuous.comp imageBesselL2Operator.continuous)
      (imageBesselL2Operator.continuous.comp (P).continuous)
  · intro u
    simp only [SchwartzMap.toLpCLM_apply]
    rw [imageBesselL2Operator_toLp, projection_toLp, projection_toLp,
      imageBesselL2Operator_toLp, projection_schwartz_multiplier]

/-- The local remainder preserves real data by its literal real kernel
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem localizedImageBesselRemainderOperator_realProjection
    {r : ℝ} (hr : r < 1 / 2) (χ ψ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hχs : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ r)
    (hψs : ∀ y, ψ y ≠ 0 → ∀ i, |y i| ≤ r)
    (f : L²) :
    P (localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs f) =
      localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs (P f) := by
  exact Lp.ext (by
    filter_upwards [imageScalarRealProjection.coeFn_compLpL
      (localizedImageBesselRemainderOperator hr χ ψ hχ hψ hχs hψs f),
      localizedImageBesselRemainderOperator_ae_integral hr χ ψ hχ hψ hχs hψs f,
      localizedImageBesselRemainderOperator_ae_integral hr χ ψ hχ hψ hχs hψs (P f)]
      with x hx hy hz
    rw [hx, hy, hz, ← imageScalarRealProjection.integral_comp_comm
      (integrable_localizedImageBesselRemainder_mul_L2 hr χ ψ hχ hψ hχs hψs f x)]
    apply integral_congr_ae
    filter_upwards [imageScalarRealProjection.coeFn_compLpL f] with y hy
    change imageScalarRealProjection ((localizedImageBesselRemainder χ ψ x y : ℂ) * f y) =
      (localizedImageBesselRemainder χ ψ x y : ℂ) * (P f) y
    rw [hy]
    simp [imageScalarRealProjection, Complex.mul_re]
  )

end JanetCartan.ContinuumNormalReduction.ImageNormal
