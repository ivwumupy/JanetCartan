module

public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.RealResponse
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.Periodization.Cutoff
public import JanetCartan.Analysis.Fourier.Periodic.Coefficient
public import JanetCartan.Analysis.Fourier.Periodic.Sobolev

/-!
# Physical cut-response size and the same real quadrature

The physical cutoff in `app:ch_pairs:eq:pairs-lag-sum-size` is applied to the
same response before periodization. Taking the real quadrature contracts the
actual periodic Fourier–Sobolev norm, with no derivative or frequency cost.
This transfers the complex response producer's size estimate to the exact
physical output consumed by `UniformStep.ProductProfiles`; it does not assume
or assert the still-missing complex size estimate.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.SignedProductEstimates

open ResponseSourceExtension UniformStep.Periodization

variable {n N : ℕ}

/-- Realification contracts the actual periodic Fourier–Sobolev norm at the
SAME derivative order (`app:ch_pairs:eq:pairs-lag-sum-size`). This preserves
the required carrier power when transferring the complex physical response
bound to `UniformStep.ProductProfiles`; smoothness supplies summability. -/
theorem periodicSobolevNorm_realPart_le
    {f : Torus n → EuclideanSpace ℂ (Fin N)} (hf : IsSmoothPeriodic f) (r : ℕ) :
    periodicSobolevNorm r (fun z ↦ euclideanRealPart (f z)) ≤ periodicSobolevNorm r f := by
  have hr := hf.comp_clm (euclideanRealPart (ι := Fin N))
  have hn (v : EuclideanSpace ℂ (Fin N)) : ‖euclideanRealPart v‖ ≤ ‖v‖ :=
    ((euclideanRealPart (ι := Fin N)).le_opNorm v).trans
      ((mul_le_mul_of_nonneg_right (euclideanRealPart_norm_le (ι := Fin N))
        (norm_nonneg v)).trans_eq (one_mul _))
  apply Real.sqrt_le_sqrt
  apply (hr.summable_periodicSobolevNorm r).tsum_le_tsum _
    (hf.summable_periodicSobolevNorm r)
  intro k
  rw [periodicFourierCoeff_map (euclideanRealPart (ι := Fin N)) hf.1]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hn _) 2)
    (pow_le_pow_left₀ (norm_nonneg _) (hn _) 2)

/-- The original output cutoff and centered representative commute with
the SAME response's real quadrature (`app:ch_pairs:eq:pairs-lag-sum-size`).
The statement is an exact identity for every source; it makes no new choice
of response, cutoff or representative. -/
theorem cut_real_response_eq_realPart
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) :
    cutToTorus χ (B (tensorFieldRealPart h)) = fun z ↦
      euclideanRealPart (χ (AmplitudeBound.centeredTorusRepresentative z) •
        complexifyResponse B h (AmplitudeBound.centeredTorusRepresentative z)) := by
  ext z i
  simp [cutToTorus, vectorPeriodization, cutField, complexifyResponse_re]

/-- The literal physical cut response has no size loss when passing from
the complex source to its real quadrature (`app:ch_pairs:eq:pairs-lag-sum-size`).
Its periodic smoothness is proved from the original two smooth response
quadratures and output support. Combined with `Sources`, this applies directly
to every actual plus/minus tensor, including doubled carriers. The missing
complex response estimate must still be supplied by `both-response-transfer`. -/
theorem cut_response_sobolev_le_complex
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (χ : Euclidean n → ℝ) (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    {b : ℝ} (hb : b < 1 / 2) (hs : tsupport χ ⊆ {x | ∀ i, |x i| ≤ b})
    (hχ : ContDiff ℝ ∞ χ)
    (hR : ContDiff ℝ ∞ (B (tensorFieldRealPart h)))
    (hI : ContDiff ℝ ∞ (B (tensorFieldImagPart h))) (r : ℕ) :
    periodicSobolevNorm r (cutToTorus χ (B (tensorFieldRealPart h))) ≤
      periodicSobolevNorm r (fun z ↦ χ (AmplitudeBound.centeredTorusRepresentative z) •
        complexifyResponse B h (AmplitudeBound.centeredTorusRepresentative z)) := by
  let p := cutToTorus χ (B (tensorFieldRealPart h))
  let m := cutToTorus χ (B (tensorFieldImagPart h))
  have hp : IsSmoothPeriodic p := isSmoothPeriodic_cutToTorus hb hs hχ hR
  have hm : IsSmoothPeriodic m := isSmoothPeriodic_cutToTorus hb hs hχ hI
  have hsplit : (fun z ↦ χ (AmplitudeBound.centeredTorusRepresentative z) •
      complexifyResponse B h (AmplitudeBound.centeredTorusRepresentative z)) =
      fun z ↦ euclideanComplexInclusion (p z) + Complex.I • euclideanComplexInclusion (m z) := by
    ext z i
    simp [p, m, cutToTorus, vectorPeriodization, cutField, complexifyResponse,
      mul_left_comm]
  have hf : IsSmoothPeriodic (fun z ↦ χ (AmplitudeBound.centeredTorusRepresentative z) •
      complexifyResponse B h (AmplitudeBound.centeredTorusRepresentative z)) := by
    rw [hsplit]
    exact ⟨(euclideanComplexInclusion.continuous.comp hp.1).add
        ((euclideanComplexInclusion.continuous.comp hm.1).const_smul Complex.I),
      (euclideanComplexInclusion.contDiff.comp hp.2).add
        ((euclideanComplexInclusion.contDiff.comp hm.2).const_smul Complex.I)⟩
  rw [cut_real_response_eq_realPart]
  exact periodicSobolevNorm_realPart_le hf r

end JanetCartan.SignedProductEstimates
