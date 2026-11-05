module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Matrix

/-!
# Finite normal test pairing on physical source profiles

The finite matching theorem for `app:ch_background:eq:bg-real-symbol` combines
the constructed masked carrier operator with the scalar chart integral proofs.
The actual smooth torus representative is used to form each physical source.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound TransportKernel ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

/-- Finite-cutoff matching of the original torus full-amplitude test pairing
with the literal reflected physical kernel on the constructed source profiles.
The only matching assumptions are on primitive chart and coefficient data.
The source integral, its measure transport and the real factor four are proved.
The output chart indicator and normalized torus output measure remain present
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem fullAmplitudeTestPairing_eq_physicalKernelPairing
    {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {R M C : ℝ}
    (h : CarrierRegularization.MaskHypotheses d m Z R M C)
    {K : Set (Euclidean n)} (hcell : K ⊆ halfOpenCell n)
    (hchart : d.outputChart = torusChart K)
    (hpoint : ∀ z ∈ d.outputChart, d.chartPoint z = centeredTorusRepresentative z)
    (χ : Euclidean n → ℝ) (hχ : ∀ y ∉ K, χ y = 0)
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
    (v w : OutputL2 n) (w₀ : Torus n → Euclidean n) (hw₀ : IsSmoothPeriodic w₀)
    (hw : w =ᵐ[volume] w₀) :
    4 * (fullAmplitudeTestPairing charts
      (l2ComplexInclusion volume v) (l2ComplexInclusion volume w)).re =
      (∫ x : Torus n, inner ℂ (l2ComplexInclusion volume v x)
        (d.outputChart.indicator (fun x ↦ reflectedMatrixKernelAction a J u Ω S
          (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) (d.chartPoint x)) x)).re := by
  let wc := l2ComplexInclusion volume w
  let vc := l2ComplexInclusion volume v
  let nw := h.operator (h.operator.adjoint wc)
  have hwc : wc =ᵐ[volume] fun z ↦ euclideanComplexInclusion (w₀ z) := by
    filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL w, hw] with z hz hwz
    exact hz.trans (congrArg euclideanComplexInclusion hwz)
  have hn : nw =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y : Torus n,
      regularizedNormalEntry d m x y i j * (w₀ y j : ℂ)) := by
    filter_upwards [regularizedOperator_normal_eq_matrix h wc] with x hx
    apply PiLp.ext
    intro i
    change nw x i = ∑ j : Fin n, _
    rw [hx i]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [hwc] with y hy
    rw [hy, euclideanComplexInclusion_apply]
  have hi := L2.integrable_inner (𝕜 := ℂ) vc nw
  have he : (∫ x : Torus n, inner ℂ (vc x)
      (d.outputChart.indicator (fun x ↦ reflectedMatrixKernelAction a J u Ω S
        (fun j ↦ physicalSourceProfile χ (fun z ↦ (w₀ z j : ℂ))) (d.chartPoint x)) x)) =
      ((4 * (∫ x : Torus n, inner ℂ (vc x) (nw x)).re : ℝ) : ℂ) := by
    calc
      _ = ∫ x : Torus n, ((4 * (inner ℂ (vc x) (nw x)).re : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [hn, (euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL v]
          with x hnx hvx
        rw [← realNormalMatrix_eq_physicalKernelAction (finiteCarrierKernelBoundsOfMask h)
          hcell hchart hpoint χ hχ a J u Ω S hχone charts symbols ha hJ hu hΩ hS
          w₀ (hw₀.1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w₀)) x,
          ← hnx]
        change vc x = euclideanComplexInclusion (v x) at hvx
        rw [hvx, inner_realified_action]
      _ = _ := by
        have hr : (∫ x : Torus n, (inner ℂ (vc x) (nw x)).re) =
          (∫ x : Torus n, inner ℂ (vc x) (nw x)).re := integral_re hi
        have hc : (∫ x : Torus n, ((4 * (inner ℂ (vc x) (nw x)).re : ℝ) : ℂ)) =
          ((∫ x : Torus n, 4 * (inner ℂ (vc x) (nw x)).re : ℝ) : ℂ) := integral_ofReal
        rw [hc, integral_const_mul, hr]
  rw [fullAmplitudeTestPairing_eq_normalTestPairing (finiteCarrierKernelBoundsOfMask h),
    regularizedOperator_normalTestPairing h, h.operator.adjoint_inner_left, L2.inner_def]
  exact (congrArg Complex.re he).symm

end JanetCartan.ContinuumRow.TestChartTransfer
