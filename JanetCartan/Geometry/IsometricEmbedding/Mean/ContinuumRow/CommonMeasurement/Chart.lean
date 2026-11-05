module

public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.ChartMeasure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Radius
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CommonMeasurement.Restriction

/-!
# The canonical functions on the common output chart

The smaller output chart uses exactly the original transport, covector, normal,
stress frame and initial cutoffs. Its kernel equals restriction of the local
kernel, not a newly postulated carrier (`app:ch_background:eq:bg-T`).
-/

@[expose] public noncomputable section
open MeasureTheory Set Metric
namespace JanetCartan.ContinuumRow.CommonMeasurement
open PeriodicLocalL2 AmplitudeBound
variable {n N : ℕ}

/-- The same canonical functions, measured on a smaller common physical chart
(`app:ch_background:defn:bg-row`). -/
def commonChartData (d : CarrierData n N) (K : Set (Euclidean n))
    (χ : Torus n → ℝ) : CarrierData n N :=
  { d with outputChart := torusChart K
           chartPoint := centeredTorusRepresentative
           measurementCutoff := χ }

/-- A zero measurement factor kills the entire charted kernel
(`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_zero_of_measurement (d : CarrierData n N)
    {x : Torus n} (hx : d.measurementCutoff x = 0) (u : CarrierVariable n) :
    carrierKernel d x u = 0 := by
  classical
  by_cases hchart : x ∈ d.outputChart <;>
    simp [carrierKernel, carrierAmplitude, hchart, hx]

/-- Kernel equality on the smaller common chart, including the original
zero extensions and SAME canonical functions (`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_commonChartData (d : CarrierData n N) (K : Set (Euclidean n))
    (χ : Torus n → ℝ)
    (hs : ∀ x, χ x ≠ 0 → x ∈ torusChart K)
    (hK : torusChart K ⊆ d.outputChart)
    (hp : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hplateau : ∀ x, χ x ≠ 0 → d.measurementCutoff x = 1)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel (restrictData d χ) x u = carrierKernel (commonChartData d K χ) x u := by
  classical
  by_cases hx : χ x = 0
  · rw [carrierKernel_restrictData, hx, zero_smul]
    exact (carrierKernel_zero_of_measurement _ hx u).symm
  · have hxK := hs x hx
    have hxd := hK hxK
    simp only [carrierKernel, restrictData, commonChartData, indicator_of_mem hxK,
      indicator_of_mem hxd, carrierPhase, carrierAmplitude, reducedCovector,
      hp x hxd, hplateau x hx, mul_one]

/-- For the existing fixed cutoff system, the common measurement support lies
inside its own common chart (`app:ch_background:defn:bg-row`). -/
theorem fixed_measurement_mem_chart {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    {x : Torus n} (hx : FixedCutoffs.periodic hr hcell 1 x ≠ 0) :
    x ∈ torusChart (closedBall (0 : Euclidean n) (4 * r)) :=
  FixedCutoffs.physical_tsupport_four hr 1 (subset_tsupport _ hx)

/-- A local fixed-cutoff carrier restricts to the same canonical functions on
the common output chart. These hypotheses are the chart fields of
`CanonicalCarrier.data` and the finite-radius deduction above
(`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_fixed_common_chart (d : CarrierData n N)
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hrcell : 4 * r < 1 / 2) (hacell : 4 * a < 1 / 2) (hra : 6 * r < a)
    (hchart : d.outputChart = torusChart (closedBall 0 (4 * a)))
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic ha hacell 1)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel (restrictData d (FixedCutoffs.periodic hr hrcell 1)) x u =
      carrierKernel (commonChartData d (closedBall 0 (4 * r))
        (FixedCutoffs.periodic hr hrcell 1)) x u := by
  apply carrierKernel_commonChartData
  · exact fun _ hx ↦ fixed_measurement_mem_chart hr hrcell hx
  · rw [hchart]
    exact fun _ hx ↦ closedBall_subset_closedBall (by linarith : 4 * r ≤ 4 * a) hx
  · exact hpoint
  · intro y hy
    rw [hmeas]
    have he := physical_measurement_mul hr ha (by linarith : 3 * r ≤ 2 * a)
      (centeredTorusRepresentative y)
    have hy' : FixedCutoffs.physical hr 1 (centeredTorusRepresentative y) ≠ 0 := hy
    exact (mul_eq_left₀ hy').mp he

/-- The restricted SAME carrier realizes the literal common-chart data on
initial tests (`app:ch_background:eq:bg-T`). -/
theorem restrictCarrier_test_common_chart (d : CarrierData n N)
    (χ : C(Torus n, ℝ)) (K : Set (Euclidean n))
    (hs : ∀ x, χ x ≠ 0 → x ∈ torusChart K) (hK : torusChart K ⊆ d.outputChart)
    (hp : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hplateau : ∀ x, χ x ≠ 0 → d.measurementCutoff x = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hU : ∀ v : carrierInitialTestSpace n,
      U (carrierInitialTestToLp v) =ᵐ[volume] carrierTestIntegral d v.val)
    (v : carrierInitialTestSpace n) :
    restrictCarrier χ U (carrierInitialTestToLp v) =ᵐ[volume]
      carrierTestIntegral (commonChartData d K χ) v.val := by
  have he : carrierTestIntegral (restrictData d χ) v.val =
      carrierTestIntegral (commonChartData d K χ) v.val := by
    funext x
    simp only [carrierTestIntegral, carrierKernel_commonChartData d K χ hs hK hp hplateau]
  rw [← he]
  exact restrictCarrier_test χ d U hU v

/-- The same common-chart kernel also identifies the literal adjoint on the
original carrier measure (`app:ch_background:eq:bg-realification`). -/
theorem restrictCarrier_adjoint_common_chart (d : CarrierData n N)
    (χ : C(Torus n, ℝ)) (K : Set (Euclidean n))
    (hs : ∀ x, χ x ≠ 0 → x ∈ torusChart K) (hK : torusChart K ⊆ d.outputChart)
    (hp : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (hplateau : ∀ x, χ x ≠ 0 → d.measurementCutoff x = 1)
    (U : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hUadj : ∀ w : ComplexOutputL2 n,
      MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n) ∧
      U.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w)
    (w : ComplexOutputL2 n) :
    MemLp (carrierAdjointIntegral (commonChartData d K χ) w) 2 (carrierMeasure n) ∧
      (restrictCarrier χ U).adjoint w =ᵐ[carrierMeasure n]
        carrierAdjointIntegral (commonChartData d K χ) w := by
  have he : carrierAdjointIntegral (restrictData d χ) w =
      carrierAdjointIntegral (commonChartData d K χ) w := by
    funext u
    simp only [carrierAdjointIntegral, carrierKernel_commonChartData d K χ hs hK hp hplateau]
  rw [← he]
  exact restrictCarrier_literal_adjoint χ d U hUadj w

end JanetCartan.ContinuumRow.CommonMeasurement
