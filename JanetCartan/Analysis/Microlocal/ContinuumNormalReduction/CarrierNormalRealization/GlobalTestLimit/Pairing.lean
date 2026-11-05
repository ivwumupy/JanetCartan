module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# Physical pairings for the global carrier test limit

The finite normal uses the parameter-truncated operator and the original radial
chart data. Compact frequency support justifies its source-first action. The
output pairing then uses the actual normalized torus chart transfer.
Consumer: `regularized_realNormal_pairing_tendsto_global_fullReflectedMatrixOperator`,
for `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction
  TransportKernel TestChartTransfer
variable {n N : ℕ}

/-- The finite real normal on an actual smooth torus representative equals the
source-first full reflected action. Compact radial support and the inverse
frequency comparison supply Fubini; no Fourier integrability is assumed.
Source: `app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`. -/
theorem regularized_realNormal_ae_physicalTestAction
    {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {Rmask M Cmask : ℝ}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (h : CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z Rmask M Cmask)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (hχsmooth : ContDiff ℝ ∞ χ) (hχcompact : HasCompactSupport χ)
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hχone : ∀ y, a.measurement y ≠ 0 → χ y = 1)
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (symbols : ∀ x hx y hy, SymbolInputs (charts x hx y hy))
    (ha : ∀ x hx y hy, (symbols x hx y hy).coefficients = a)
    (hJ : ∀ x hx y hy, (symbols x hx y hy).jacobian = J)
    (hu : ∀ x hx y hy, (symbols x hx y hy).inverse = u)
    (hΩ : ∀ x hx y hy, (symbols x hx y hy).domain = Ω)
    (hS : ∀ x hx y hy, (symbols x hx y hy).spectatorSupport = S)
    (hhigh : HasCompactSupport a.high) {Cfreq : ℝ} (hCfreq : 0 ≤ Cfreq)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ Cfreq * ‖(u p).2‖)
    (Rbox : ℝ)
    (hs : ∀ ξ i j, SupportedInCenteredBox Rbox
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (hb : Continuous (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (w : OutputL2 n) (w₀ : Torus n → Euclidean n)
    (hw₀ : IsSmoothPeriodic w₀) (hw : w =ᵐ[volume] w₀) :
    l2ComplexInclusion volume
      (realQuadratureChannel h.operator ((realQuadratureChannel h.operator).adjoint w))
      =ᵐ[volume] d.outputChart.indicator (fun x ↦ reflectedMatrixTestAction a J u Ω S
        (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) (d.chartPoint x)) := by
  have hnormal := regularized_realNormal_ae_physicalKernelAction hZ h hcell hchart hpoint
    χ hχ a J u Ω S hχone charts symbols ha hJ hu hΩ hS w
  let f := physicalSourceProfile χ (fun z ↦ euclideanComplexInclusion (w₀ z))
  have hc : ContDiff ℝ ∞ f := physicalSourceProfile_contDiff hχsmooth
    ⟨euclideanComplexInclusion.continuous.comp hw₀.1,
      (euclideanComplexInclusion (ι := Fin n)).contDiff.comp hw₀.2⟩
  have hfc : HasCompactSupport f := physicalSourceProfile_hasCompactSupport hχcompact _
  have hswap (x : Euclidean n) : reflectedMatrixKernelAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) x =
      reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) x :=
    reflectedMatrixKernelAction_eq_testAction_of_compact_high a J u Ω S hhigh hCfreq
      hcomparison Rbox hs hb f hc.continuous hfc x
  have hprofile (j : Fin n) : physicalSourceProfile χ (fun z ↦ (w z j : ℂ)) =ᵐ[volume]
      physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ)) := by
    have hp := (ae_restrict_iff' measurableSet_halfOpenCell).mp
      (measurePreserving_quotient.quasiMeasurePreserving.ae hw)
    filter_upwards [hp] with y hy
    by_cases hyK : y ∈ K
    · simp only [physicalSourceProfile, periodicLift, Function.comp_apply, hy (hcell hyK)]
    · simp [physicalSourceProfile, hχ y hyK]
  have hkernel (x : Euclidean n) : reflectedMatrixKernelAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) x =
      reflectedMatrixTestAction a J u Ω S
      (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) x := by
    rw [← hswap]
    apply PiLp.ext
    intro i
    change (∑ j : Fin n, _) = _
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hprofile j] with y hy
    rw [hy]
  filter_upwards [hnormal] with x hx
  rw [hx]
  by_cases hxc : x ∈ d.outputChart
  · simp only [indicator_of_mem hxc, hkernel]
  · simp only [indicator_of_notMem hxc]

/-- Real L² pairing with a chart-indicated complex action equals the real
part of its physical pairing. This retains conjugation in the output test and
introduces no quadrature prefactor (`app:ch_background:eq:bg-real-symbol`). -/
theorem inner_realPart_eq_re_physicalProfile_pairing
    (d : CarrierData n N) {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ x ∈ d.outputChart, d.chartPoint x = centeredTorusRepresentative x)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
    (v : OutputL2 n) (v₀ : Torus n → Euclidean n) (hv : v =ᵐ[volume] v₀)
    (z : ComplexOutputL2 n) (G : Euclidean n → EuclideanSpace ℂ (Fin n))
    (hz : z =ᵐ[volume] d.outputChart.indicator (fun x ↦ G (d.chartPoint x)))
    (hG : ∀ y, G y ≠ 0 → χ y = 1) :
    inner ℝ v (l2RealPart volume z) =
      (∫ y, inner ℂ
        (physicalSourceProfile χ (fun x ↦ euclideanComplexInclusion (v₀ x)) y) (G y)).re := by
  rw [real_inner_comm, l2RealPart_inner, real_inner_comm, real_inner_eq_complex_re,
    L2.inner_def]
  congr 1
  rw [← integral_output_eq_physicalProfile d hcell hchart hpoint χ hχ _ G hG]
  apply integral_congr_ae
  filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL v, hv, hz]
    with x hinc hvx hzx
  change l2ComplexInclusion volume v x = euclideanComplexInclusion (v x) at hinc
  rw [hinc, hvx, hzx]

end JanetCartan.ContinuumRow.CarrierNormalRealization
