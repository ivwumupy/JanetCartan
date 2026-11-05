module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Profiles
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.TestReduction

/-!
# Physical source integration of the literal reflected normal

The support and source identities below connect the chart measure comparison to
`TransportKernel.TestReduction` for `app:ch_background:eq:bg-real-symbol`.
The amplitude is the original reflected full amplitude, including its spectator
integral and high-frequency coefficient. The source cutoff is inserted only
where it is one on the measurement support.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff FourierTransform Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound TransportKernel ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

section Symbol
variable (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))

/-- The original spectator amplitude vanishes where its source measurement
cutoff vanishes (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_eq_zero_of_source_measurement (x y k : Euclidean n)
    (hy : a.measurement y = 0) : TransportSymbol.amplitude a J u Ω S (x, y, k) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases hv : ((x, y, k), v) ∈ Ω
  · simp [TransportSymbol.extendedDensity, hv, TransportSymbol.inputDensity,
      TransportSymbol.inputWeight, TransportSymbol.inverseCoordinates, hy]
  · simp [TransportSymbol.extendedDensity, hv]

/-- Frequency reflection preserves source measurement support, with the
normalization `2 (2π)^n` retained (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedAmplitude_eq_zero_of_source_measurement (x y k : Euclidean n)
    (hy : a.measurement y = 0) : reflectedSymbolAmplitude a J u Ω S (x, y, k) = 0 := by
  simp [reflectedSymbolAmplitude, amplitude_eq_zero_of_source_measurement a J u Ω S x y k hy,
    amplitude_eq_zero_of_source_measurement a J u Ω S x y (-k) hy]

/-- The literal reflected physical kernel retains source measurement support
(`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedKernel_eq_zero_of_source_measurement (x y : Euclidean n)
    (hy : a.measurement y = 0) (i j : Fin n) :
    amplitudeKernel (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ)) x y = 0 := by
  simp [amplitudeKernel, Real.fourier_eq,
    reflectedAmplitude_eq_zero_of_source_measurement a J u Ω S x y _ hy]

/-- Exact Haar-to-Lebesgue transfer for the literal reflected physical kernel.
It needs no interchange of the source and frequency integrals
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integral_reflectedKernel_eq_physicalSourceProfile
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (w : Torus n → ℂ) (x : Euclidean n) (i j : Fin n) :
    (∫ z : Torus n, amplitudeKernel (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ))
        x (centeredTorusRepresentative z) * w z) =
      ∫ y, amplitudeKernel (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ)) x y *
          physicalSourceProfile χ w y := by
  apply integral_source_eq_physicalSourceProfile hcell χ hχ
  intro y hy
  apply hχone y
  intro hzero
  exact hy (reflectedKernel_eq_zero_of_source_measurement a J u Ω S x y hzero i j)

/-- The source Fourier transform of the compact profile is exactly the source
integral on normalized torus volume. Frequency remains in the unit convention
`k = 2πξ`; no source-Fourier integrability is an input
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem sourceAmplitudeTransform_eq_torus_source
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (w : Torus n → ℂ) (x ξ : Euclidean n) (i j : Fin n) :
    sourceAmplitudeTransform (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ))
        (physicalSourceProfile χ w) x ξ =
      ∫ z : Torus n, (Real.fourierChar (-inner ℝ (centeredTorusRepresentative z) ξ) : ℂ) *
        (reflectedSymbolAmplitude a J u Ω S
          (x, centeredTorusRepresentative z, (2 * Real.pi) • ξ) i j : ℂ) * w z := by
  have ht := integral_source_eq_physicalSourceProfile hcell χ hχ
    (fun y ↦ (Real.fourierChar (-inner ℝ y ξ) : ℂ) *
      (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ))
    (fun y hy ↦ hχone y (fun hz ↦ hy (by
      simp [reflectedAmplitude_eq_zero_of_source_measurement a J u Ω S x y _ hz]))) w
  rw [ht]
  simp only [sourceAmplitudeTransform, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

end Symbol

/-- Finite-band bounds justify the source integral of each literal normal
entry. This is the integrability needed to take real quadratures before the
chart change (`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_normalEntry_source {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    (h : FiniteCarrierKernelBounds d m) (x : Torus n) (i j : Fin n)
    {w : Torus n → ℂ} (hw : Integrable w) :
    Integrable (fun y ↦ regularizedNormalEntry d m x y i j * w y) := by
  have hi := (integrable_carrierNormalDensity_mul h x i j hw).integral_prod_left
  simpa only [integral_mul_const, regularizedNormalEntry_eq_integral_carrierNormalDensity] using hi

section FiniteMatching
variable {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    (h : FiniteCarrierKernelBounds d m)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    {x : Torus n} (hx : x ∈ d.outputChart)
    (charts : ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (symbols : ∀ y hy, SymbolInputs (charts y hy))
    (ha : ∀ y hy, (symbols y hy).coefficients = a)
    (hJ : ∀ y hy, (symbols y hy).jacobian = J)
    (hu : ∀ y hy, (symbols y hy).inverse = u)
    (hΩ : ∀ y hy, (symbols y hy).domain = Ω)
    (hS : ∀ y hy, (symbols y hy).spectatorSupport = S)

include h hchart hpoint hχ hχone hx ha hJ hu hΩ hS in
/-- Pointwise finite-cutoff matching, including the zero extension outside the
source chart. The hypotheses identify primitive coefficient and chart data,
never kernels or integrals. The spectator integral, squared carrier mask and
factor four come from `SymbolInputs.realNormalEntry_eq_amplitudeKernel`
(`app:ch_background:eq:bg-real-symbol`). -/
theorem realNormalEntry_eq_physicalKernel (y : Torus n) (i j : Fin n) :
    ((4 * (regularizedNormalEntry d m x y i j).re : ℝ) : ℂ) =
      amplitudeKernel (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ))
        (d.chartPoint x) (centeredTorusRepresentative y) := by
  by_cases hy : y ∈ d.outputChart
  · have he := (symbols y hy).realNormalEntry_eq_amplitudeKernel h hx hy i j
    unfold SymbolInputs.unitReflectedEntry at he
    simpa only [ha y hy, hJ y hy, hu y hy,
      hΩ y hy, hS y hy, hpoint y hy] using he
  · rw [regularizedNormalEntry_eq_zero_outside_right x hy]
    have hKy : centeredTorusRepresentative y ∉ K := by
      simpa only [hchart, torusChart, mem_preimage] using hy
    have hm : a.measurement (centeredTorusRepresentative y) = 0 := by
      by_contra hn
      have hone := hχone _ hn
      rw [hχ _ hKy] at hone
      exact zero_ne_one hone
    simp [reflectedKernel_eq_zero_of_source_measurement a J u Ω S _ _ hm i j]

include h hcell hchart hpoint hχ hχone hx ha hJ hu hΩ hS in
/-- Exact finite-cutoff source matching for real tests. The left side is the
literal torus normal; the right side is its reflected physical kernel acting
on the constructed compact profile. Source integration is transported with
normalized Haar measure, and the real quadrature factor remains four
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem integral_realNormalEntry_eq_physicalSourceProfile
    (w : Torus n → ℝ) (hw : Integrable w) (i j : Fin n) :
    ((4 * (∫ y : Torus n, regularizedNormalEntry d m x y i j * (w y : ℂ)).re : ℝ) : ℂ) =
      ∫ y, amplitudeKernel (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ))
        (d.chartPoint x) y * physicalSourceProfile χ (fun z ↦ (w z : ℂ)) y := by
  rw [← integral_reflectedKernel_eq_physicalSourceProfile a J u Ω S hcell χ hχ hχone]
  have hi := integrable_normalEntry_source h x i j (hw.ofReal)
  have hre : (∫ y : Torus n, (regularizedNormalEntry d m x y i j * (w y : ℂ)).re) =
      (∫ y : Torus n, regularizedNormalEntry d m x y i j * (w y : ℂ)).re := integral_re hi
  rw [← hre, ← integral_const_mul]
  have hcoe : (∫ y : Torus n, ((4 *
      (regularizedNormalEntry d m x y i j * (w y : ℂ)).re : ℝ) : ℂ)) =
      ((∫ y : Torus n, 4 *
      (regularizedNormalEntry d m x y i j * (w y : ℂ)).re : ℝ) : ℂ) := integral_ofReal
  rw [← hcoe]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← realNormalEntry_eq_physicalKernel h hchart hpoint χ hχ a J u Ω S hχone hx
    charts symbols ha hJ hu hΩ hS y i j]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.ofReal_mul]
  ring

end FiniteMatching
end JanetCartan.ContinuumRow.TestChartTransfer
