module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.Amplitude
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.QuadratureComparison
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.ParameterSupport

/-!
# The finite carrier normal on every real output

The full real normal has the physical kernel action on all of `OutputL2`,
including the output chart indicator. Only primitive finite-mask and genuine
chart/coefficient matching data are hypotheses. No normal identity, source
integrability, or norm bound is assumed. Consumer: identification with the
transferred full PDO in `app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open PeriodicLocalL2 TransportKernel ContinuumNormalReduction TestChartTransfer AmplitudeBound
variable {n N : ℕ}

/-- Global physical action of the actual finite real-quadrature normal on
every L² output. The reflected kernel ALREADY contains the factor four; the
right-hand side has no further scalar prefactor. Source and output use exactly
the original normalized torus measure and its proved chart transfer
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem regularized_realNormal_ae_physicalKernelAction
    {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {Z : Set CarrierParameter} {R M C : ℝ}
    (hZ : ∀ z ∉ Z, ∀ η, d.angularCutoff z η = 0)
    (h : CarrierRegularization.MaskHypotheses d (parameterTruncatedMask Z m) Z R M C)
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
    (w : OutputL2 n) :
    l2ComplexInclusion volume
      (realQuadratureChannel h.operator ((realQuadratureChannel h.operator).adjoint w))
      =ᵐ[volume] d.outputChart.indicator (fun x ↦ reflectedMatrixKernelAction a J u Ω S
        (fun j ↦ physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) (d.chartPoint x)) := by
  let wc := l2ComplexInclusion volume w
  let nw := h.operator (h.operator.adjoint wc)
  have hnormal : realQuadratureChannel h.operator
      ((realQuadratureChannel h.operator).adjoint w) = (4 : ℝ) • l2RealPart volume nw := by
    have he := congrArg (fun A : OutputL2 n →L[ℝ] OutputL2 n ↦ A w)
      (realQuadratureChannel_normal_eq_four_realPart h.operator)
    exact he
  have hn : nw =ᵐ[volume] fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y : Torus n,
      regularizedNormalEntry d m x y i j * (w y j : ℂ)) := by
    filter_upwards [parameterRegularizedOperator_normal_eq_matrix hZ h wc] with x hx
    apply PiLp.ext
    intro i
    change nw x i = ∑ j : Fin n, _
    rw [hx i]
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL w] with y hy
    change wc y = euclideanComplexInclusion (w y) at hy
    rw [hy, euclideanComplexInclusion_apply]
  rw [hnormal]
  filter_upwards [(euclideanComplexInclusion (ι := Fin n)).coeFn_compLpL
      ((4 : ℝ) • l2RealPart volume nw),
    Lp.coeFn_smul (4 : ℝ) (l2RealPart volume nw),
    (euclideanRealPart (ι := Fin n)).coeFn_compLpL nw, hn] with x hc hs hr hx
  change l2ComplexInclusion volume ((4 : ℝ) • l2RealPart volume nw) x = _ at hc
  change l2RealPart volume nw x = _ at hr
  rw [hc, hs, Pi.smul_apply, hr, hx]
  exact realNormalMatrix_eq_physicalKernelAction (finiteCarrierKernelBoundsOfParameterMask hZ h)
    hcell hchart hpoint χ hχ a J u Ω S hχone charts symbols ha hJ hu hΩ hS
    w ((Lp.memLp w).integrable (by norm_num)) x

end JanetCartan.ContinuumRow.CarrierNormalRealization
