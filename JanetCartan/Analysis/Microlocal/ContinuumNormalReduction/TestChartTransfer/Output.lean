module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Pairing

/-!
# Compact output tests for physical distributional convergence

For `app:ch_background:eq:bg-real-symbol`, the normalized torus output pairing
is transported only after retaining its actual chart indicator. Both the finite
kernel action and the limiting source-first action inherit measurement support.
Thus the physical distributional convergence producer can use a compact smooth
output profile as well as the compact smooth source profiles.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound TransportKernel ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

/-- Exact transport of the chart-indicated output pairing. Only support and
actual coordinate identities are inputs (`app:ch_background:eq:bg-real-symbol`). -/
theorem integral_output_eq_physicalProfile
    (d : CarrierData n N) {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (v : Torus n → EuclideanSpace ℂ (Fin n))
    (G : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hG : ∀ y, G y ≠ 0 → χ y = 1) :
    (∫ z : Torus n, inner ℂ (v z) (d.outputChart.indicator (fun z ↦ G (d.chartPoint z)) z)) =
      ∫ y, inner ℂ (physicalSourceProfile χ v y) (G y) := by
  calc
    _ = ∫ z : Torus n, inner ℂ
        (physicalSourceProfile χ v (centeredTorusRepresentative z))
        (G (centeredTorusRepresentative z)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [physicalSourceProfile_representative]
      by_cases hz : z ∈ d.outputChart
      · rw [indicator_of_mem hz, hpoint z hz]
        by_cases hzero : G (centeredTorusRepresentative z) = 0
        · simp [hzero]
        · rw [hG _ hzero, one_smul]
      · rw [indicator_of_notMem hz]
        have hKz : centeredTorusRepresentative z ∉ K := by
          simpa only [hchart, torusChart, mem_preimage] using hz
        have hzero : G (centeredTorusRepresentative z) = 0 := by
          by_contra hn
          have hh := hG _ hn
          rw [hχ _ hKz] at hh
          exact zero_ne_one hh
        simp [hzero]
    _ = _ := integral_representative_of_supported hcell
      (fun y ↦ inner ℂ (physicalSourceProfile χ v y) (G y)) (fun y hy ↦ by
        rw [physicalSourceProfile_eq_zero hχ v hy, inner_zero_left])

section Support
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))

/-- The original reflected amplitude retains the output measurement cutoff
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedAmplitude_eq_zero_of_output_measurement (x y k : Euclidean n)
    (hx : a.measurement x = 0) : reflectedSymbolAmplitude a J u Ω S (x, y, k) = 0 := by
  have hz (k : Euclidean n) : TransportSymbol.amplitude a J u Ω S (x, y, k) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with v
    by_cases hv : ((x, y, k), v) ∈ Ω
    · simp [TransportSymbol.extendedDensity, hv, TransportSymbol.inputDensity,
        TransportSymbol.inputWeight, TransportSymbol.inverseCoordinates, hx]
    · simp [TransportSymbol.extendedDensity, hv]
  simp [reflectedSymbolAmplitude, hz]

/-- Finite kernel actions retain output measurement support
(`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedMatrixKernelAction_eq_zero_of_output_measurement
    (f : Fin n → Euclidean n → ℂ) {x : Euclidean n} (hx : a.measurement x = 0) :
    reflectedMatrixKernelAction a J u Ω S f x = 0 := by
  apply PiLp.ext
  intro i
  simp [reflectedMatrixKernelAction, amplitudeKernel, Real.fourier_eq,
    reflectedAmplitude_eq_zero_of_output_measurement a J u Ω S x _ _ hx]

/-- The source-first limiting action has the same output support, without any
assumption of Fourier integrability (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedMatrixTestAction_eq_zero_of_output_measurement
    (f : Fin n → Euclidean n → ℂ) {x : Euclidean n} (hx : a.measurement x = 0) :
    reflectedMatrixTestAction a J u Ω S f x = 0 := by
  apply PiLp.ext
  intro i
  simp [reflectedMatrixTestAction, fullAmplitudeOperator, sourceAmplitudeTransform,
    Real.fourierInv_eq, Real.fourier_eq,
    reflectedAmplitude_eq_zero_of_output_measurement a J u Ω S x _ _ hx]

end Support
end JanetCartan.ContinuumRow.TestChartTransfer
