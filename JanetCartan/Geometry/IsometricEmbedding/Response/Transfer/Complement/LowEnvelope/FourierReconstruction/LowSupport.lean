module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel
public import JanetCartan.Analysis.Microlocal.Localization.NormalizedEstimates
/-!
# Fourier L¹ control for the low envelope

The finite-frequency Cauchy–Schwarz estimate consumed by the source-kernel
integration in `app:ch_response:thm:response-literal-transfer`.
-/

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization
variable {n r : ℕ}
/-- The square-root ball-volume loss for the low envelope in
`app:ch_response:thm:response-literal-transfer`. The support condition is almost
everywhere, and the values have their Euclidean Hilbert norm. -/
theorem integrable_and_integral_norm_le_of_lowSupport {H : Euclidean n → EuclideanSpace ℂ (Fin r)} (hH : MemLp H 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → H θ = 0) :
    Integrable H ∧ (∫ θ, ‖H θ‖) ≤
      Real.sqrt (volume.real (Metric.ball (0 : Euclidean n) 1)) *
        Λ ^ ((n : ℝ) / 2) * Real.sqrt (∫ θ, ‖H θ‖ ^ 2) := by
  let B := Metric.closedBall (0 : Euclidean n) Λ
  have hB : MeasurableSet B := measurableSet_closedBall
  have hfin : volume B < ⊤ := measure_closedBall_lt_top
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hfin⟩
  have he : B.indicator H =ᵐ[volume] H := by
    filter_upwards [hs] with θ hθ
    by_cases hb : θ ∈ B
    · simp [hb]
    · have hlt : Λ < ‖θ‖ := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hb
      simp [hb, hθ hlt]
  have hi : Integrable H :=
    ((integrable_indicator_iff hB).mpr
      ((hH.mono_measure Measure.restrict_le_self).integrable (by norm_num))).congr he
  refine ⟨hi, ?_⟩
  have hn : (∫ θ, ‖H θ‖) = ∫ θ in B, ‖H θ‖ := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [he] with θ hθ
    by_cases hb : θ ∈ B
    · simp [hb]
    · simpa [hb] using congrArg norm hθ.symm
  have hsq : (∫ θ in B, ‖H θ‖ ^ 2) = ∫ θ, ‖H θ‖ ^ 2 := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [he] with θ hθ
    by_cases hb : θ ∈ B
    · simp [hb]
    · have hz : H θ = 0 := by simpa [hb] using hθ.symm
      simp [hb, hz]
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)))
    (Filter.Eventually.of_forall (fun θ ↦ norm_nonneg (H θ)))
    (memLp_const (μ := volume.restrict B) (p := ENNReal.ofReal 2) (1 : ℝ))
    (by simpa using (hH.mono_measure Measure.restrict_le_self).norm)
  simp only [one_mul, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    Measure.real, Measure.restrict_apply_univ, ← Real.sqrt_eq_rpow, hsq] at hcs
  rw [hn]
  convert hcs using 1
  change _ = Real.sqrt (volume.real (Metric.closedBall (0 : Euclidean n) Λ)) * _
  rw [volume.addHaar_real_closedBall _ hΛ, Real.sqrt_mul (by positivity)]
  simp only [finrank_euclideanSpace_fin]
  rw [Real.sqrt_eq_rpow (Λ ^ n), ← Real.rpow_natCast, ← Real.rpow_mul hΛ]
  ring_nf
end JanetCartan.ResponseTransfer.LowEnvelope
