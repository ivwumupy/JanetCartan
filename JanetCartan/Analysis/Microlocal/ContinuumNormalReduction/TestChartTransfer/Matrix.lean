module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TestChartTransfer.Kernels

/-!
# Finite matrix matching on the original output measure

For `app:ch_background:eq:bg-real-symbol`, sum the checked scalar source
identities. The output chart indicator stays in the action, and the output
test pairing stays on normalized torus volume.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.TestChartTransfer
open PeriodicLocalL2 AmplitudeBound TransportKernel ContinuumNormalReduction Pseudodifferential
variable {n N : ℕ}

/-- The literal physical kernel action before source-first convergence, with
the original full reflected amplitude (`app:ch_background:eq:bg-real-symbol`). -/
def reflectedMatrixKernelAction
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (f : Fin n → Euclidean n → ℂ) (x : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y,
    amplitudeKernel (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω S (x, y, (2 * Real.pi) • ξ) i j : ℂ)) x y * f j y)

/-- Real smooth vector tests give exactly the scalar complex profiles needed
by `reflectedMatrixTestAction`, with regularity proved from the test and cutoff
(`app:ch_background:eq:bg-real-symbol`). -/
theorem real_source_profiles_regular
    {χ : Euclidean n → ℝ} {w : Torus n → Euclidean n}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hw : IsSmoothPeriodic w)
    (j : Fin n) :
    ContDiff ℝ ∞ (physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) ∧
      HasCompactSupport (physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) := by
  apply physicalSourceProfile_coordinate_regular hχ hχc
    (w := fun z ↦ euclideanComplexInclusion (w z)) _ j
  refine ⟨euclideanComplexInclusion.continuous.comp hw.1, ?_⟩
  change ContDiff ℝ ∞ (fun x ↦ euclideanComplexInclusion (periodicLift w x))
  exact (euclideanComplexInclusion (ι := Fin n)).contDiff.comp hw.2

section Matching
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
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (symbols : ∀ x hx y hy, SymbolInputs (charts x hx y hy))
    (ha : ∀ x hx y hy, (symbols x hx y hy).coefficients = a)
    (hJ : ∀ x hx y hy, (symbols x hx y hy).jacobian = J)
    (hu : ∀ x hx y hy, (symbols x hx y hy).inverse = u)
    (hΩ : ∀ x hx y hy, (symbols x hx y hy).domain = Ω)
    (hS : ∀ x hx y hy, (symbols x hx y hy).spectatorSupport = S)

include h hcell hchart hpoint hχ hχone ha hJ hu hΩ hS in
/-- Finite matrix matching of the real torus normal and the literal physical
source action. Both matrix sums and the output chart indicator remain explicit
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem realNormalMatrix_eq_physicalKernelAction
    (w : Torus n → Euclidean n) (hw : Integrable w) (x : Torus n) :
    euclideanComplexInclusion ((4 : ℝ) • euclideanRealPart
      (WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y : Torus n,
        regularizedNormalEntry d m x y i j * (w y j : ℂ)))) =
      d.outputChart.indicator (fun x ↦ reflectedMatrixKernelAction a J u Ω S
        (fun j ↦ physicalSourceProfile χ (fun z ↦ (w z j : ℂ))) (d.chartPoint x)) x := by
  by_cases hx : x ∈ d.outputChart
  · rw [indicator_of_mem hx]
    apply PiLp.ext
    intro i
    change ((4 * (∑ j, ∫ y : Torus n,
      regularizedNormalEntry d m x y i j * (w y j : ℂ)).re : ℝ) : ℂ) = ∑ j : Fin n, _
    rw [show (∑ j : Fin n, ∫ y : Torus n,
      regularizedNormalEntry d m x y i j * (w y j : ℂ)).re =
      ∑ j : Fin n, (∫ y : Torus n,
      regularizedNormalEntry d m x y i j * (w y j : ℂ)).re from
      map_sum Complex.reCLM _ _]
    simp only [Finset.mul_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_realNormalEntry_eq_physicalSourceProfile h hcell hchart hpoint χ hχ
      a J u Ω S hχone hx (charts x hx) (symbols x hx) (ha x hx) (hJ x hx)
      (hu x hx) (hΩ x hx) (hS x hx) (fun z ↦ w z j) (hw.eval_piLp j) i j
  · rw [indicator_of_notMem hx]
    have hz : ∀ y i j, regularizedNormalEntry d m x y i j = 0 := by
      intro y i j
      simp [regularizedNormalEntry, carrierKernel_eq_zero_outside d hx]
    apply PiLp.ext
    intro i
    simp [hz, PiLp.smul_apply]

end Matching

/-- Realification of a complex matrix action pairs with a real test by four
times the real part, with Mathlib's conjugate-linear first argument
(`app:ch_background:eq:bg-real-symbol`). -/
theorem inner_realified_action (v : Euclidean n) (z : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (euclideanComplexInclusion v)
      (euclideanComplexInclusion ((4 : ℝ) • euclideanRealPart z)) =
        ((4 * (inner ℂ (euclideanComplexInclusion v) z).re : ℝ) : ℂ) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum, mul_comm, mul_left_comm]

end JanetCartan.ContinuumRow.TestChartTransfer
