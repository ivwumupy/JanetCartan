module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Output

/-!
# Transfer of the physical normal limit to smooth torus tests

For `app:ch_background:eq:bg-full-complex-amplitude` and
`app:ch_background:eq:bg-real-symbol`, the compact physical profiles are the
cutoff periodic lifts of the actual smooth torus tests. The finite equality is
proved in `TestChartTransfer.Pairing`, including the conic spectator integral,
the squared mask, the Haar normalization and the factor four.

The theorem below consumes distributional convergence of the ORIGINAL physical
full-amplitude kernels to the source-first `reflectedMatrixTestAction`. This is
the input produced by `jc-normal-source-fourier-convergence`; it is not a torus
integral identity or the desired normal identity. No scheduler dependency on that
producer is needed to prove this implication. The parent normal construction
still instantiates the actual charts, mask family and physical convergence.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound TransportKernel ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

/-- Transfer actual physical distributional convergence to the precise torus
limit required by `TransportKernel.realNormal_principal_reduction_of_test_limit`.
The finite equalities and both chart measure transports are proved internally.
The only limit premise concerns the Euclidean full kernels against the explicitly
constructed compact source and output profiles. Their smoothness and compact
support follow from `physicalSourceProfile_contDiff`,
`physicalSourceProfile_hasCompactSupport` and `real_source_profiles_regular`.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`. -/
theorem fullAmplitudeTestPairing_tendsto_of_physical_distributional_limit
    {d : CarrierData n N} {m : ℕ → CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {R : ℕ → ℝ} {M C : ℝ}
    (hmask : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Z (R r) M C)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (ar : ℕ → TransportSymbol.Coefficients n N) (a : TransportSymbol.Coefficients n N)
    (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχr : ∀ r y, (ar r).measurement y ≠ 0 → χ y = 1)
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ r x, x ∈ d.outputChart → ∀ y, y ∈ d.outputChart → ChartInputs d (m r) x y)
    (symbols : ∀ r x hx y hy, SymbolInputs (charts r x hx y hy))
    (ha : ∀ r x hx y hy, (symbols r x hx y hy).coefficients = ar r)
    (hJ : ∀ r x hx y hy, (symbols r x hx y hy).jacobian = J)
    (hu : ∀ r x hx y hy, (symbols r x hx y hy).inverse = u)
    (hΩ : ∀ r x hx y hy, (symbols r x hx y hy).domain = Ω)
    (hS : ∀ r x hx y hy, (symbols r x hx y hy).spectatorSupport = S)
    (v w : OutputL2 n) (v₀ w₀ : Torus n → Euclidean n)
    (hw₀ : IsSmoothPeriodic w₀) (hv : v =ᵐ[volume] v₀) (hw : w =ᵐ[volume] w₀)
    (hphysical : Tendsto (fun r ↦ ∫ x : Euclidean n,
        inner ℂ (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
          (reflectedMatrixKernelAction (ar r) J u Ω S
            (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) x)) atTop
      (𝓝 (∫ x : Euclidean n,
        inner ℂ (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
          (reflectedMatrixTestAction a J u Ω S
            (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) x)))) :
    Tendsto (fun r ↦ 4 * (fullAmplitudeTestPairing (charts r)
      (l2ComplexInclusion volume v) (l2ComplexInclusion volume w)).re) atTop
      (𝓝 ((∫ x : Torus n, inner ℂ (l2ComplexInclusion volume v x)
        (d.outputChart.indicator (fun x ↦ reflectedMatrixTestAction a J u Ω S
          (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) (d.chartPoint x)) x)).re)) := by
  have hvc : l2ComplexInclusion volume v =ᵐ[volume]
      fun z ↦ euclideanComplexInclusion (v₀ z) := by
    filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL v, hv] with z hz hvz
    exact hz.trans (congrArg euclideanComplexInclusion hvz)
  have htransfer (G : Euclidean n → EuclideanSpace ℂ (Fin n))
      (hG : ∀ y, G y ≠ 0 → χ y = 1) :
      (∫ x : Torus n, inner ℂ (l2ComplexInclusion volume v x)
        (d.outputChart.indicator (fun x ↦ G (d.chartPoint x)) x)) =
        ∫ x : Euclidean n,
          inner ℂ (physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (v₀ z)) x)
            (G x) := by
    rw [← integral_output_eq_physicalProfile d hcell hchart hpoint χ hχ _ G hG]
    apply integral_congr_ae
    filter_upwards [hvc] with x hx
    rw [hx]
  have hfinite (r : ℕ) := fullAmplitudeTestPairing_eq_physicalKernelPairing
    (hmask r) hcell hchart hpoint χ hχ (ar r) J u Ω S (hχr r) (charts r)
    (symbols r) (ha r) (hJ r) (hu r) (hΩ r) (hS r) v w w₀ hw₀ hw
  have hfiniteTransport (r : ℕ) := htransfer
    (reflectedMatrixKernelAction (ar r) J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))))
    (fun y hy ↦ hχr r y (fun hz ↦ hy
      (reflectedMatrixKernelAction_eq_zero_of_output_measurement (ar r) J u Ω S _ hz)))
  have hlimitTransport := htransfer
    (reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))))
    (fun y hy ↦ hχone y (fun hz ↦ hy
      (reflectedMatrixTestAction_eq_zero_of_output_measurement a J u Ω S _ hz)))
  have ht := (Complex.continuous_re.tendsto _).comp hphysical
  simpa only [Function.comp_def, hfinite, hfiniteTransport, hlimitTransport] using ht

end JanetCartan.ContinuumRow.TestChartTransfer
