module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Assembly
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the carrier cutoff on output tests

For `app:ch_background:eq:bg-full-complex-amplitude`, bounded masks tending to
one give strong convergence of each constructed adjoint on every output test
whose literal uncut adjoint is square integrable. No unregularized carrier or
uniform operator bound is used. The resulting limit identifies the actual
spectator-amplitude pairings and their real quadratures.

The phase-chart and leading-wave producers supply the finite mask and chart
inputs. The continuum-row consumer must establish the stated square integrability
of its chosen uncut adjoint tests. A distributional limit is identified only when
its convergence on those tests is supplied explicitly.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate Classical

namespace JanetCartan.ContinuumRow.TransportKernel
variable {n N : ℕ} {d : CarrierData n N}

/-- Dominated convergence removes the finite-frequency mask from an individual
literal adjoint test. This discharges the strong-limit premise of
`tendsto_normalTestPairing_of_adjoint_limits` from a testwise L² input, not an
uncut operator bound (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedOperator_adjoint_tendsto
    {m : ℕ → CarrierVariable n → ℝ} {Z : Set CarrierParameter}
    {R : ℕ → ℝ} {M C : ℝ}
    (h : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Z (R r) M C)
    (hm : ∀ᵐ u ∂carrierMeasure n, Tendsto (fun r ↦ m r u) atTop (𝓝 1))
    (w : ComplexOutputL2 n)
    (hw : MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n)) :
    Tendsto (fun r ↦ (h r).operator.adjoint w) atTop
      (𝓝 (hw.toLp (carrierAdjointIntegral d w))) := by
  let a := hw.toLp (carrierAdjointIntegral d w)
  have he (r) :
      (fun u ↦ ((h r).operator.adjoint w - a) u) =ᵐ[carrierMeasure n]
        fun u ↦ ((m r u : ℂ) - 1) * carrierAdjointIntegral d w u := by
    filter_upwards [Lp.coeFn_sub ((h r).operator.adjoint w) a,
      (h r).operator_adjoint_ae w, hw.coeFn_toLp] with u hs ht ha
    dsimp [a] at hs ⊢
    rw [hs, ht, ha]
    ring
  have hsq (r) : ‖(h r).operator.adjoint w - a‖ ^ 2 =
      ∫ u, ‖((m r u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2
        ∂carrierMeasure n := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
      ← integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [he r] with u hu
    rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hu]
  have hlim : Tendsto (fun r ↦ ∫ u,
      ‖((m r u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2 ∂carrierMeasure n)
      atTop (𝓝 0) := by
    have hi := (hw.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul
      ((M + 1) ^ 2)
    have ht := tendsto_integral_of_dominated_convergence
      (μ := carrierMeasure n) (f := fun _ ↦ (0 : ℝ))
      (F := fun r u ↦ ‖((m r u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2)
      (fun u ↦ (M + 1) ^ 2 * ‖carrierAdjointIntegral d w u‖ ^ 2)
      (fun r ↦ (((Lp.aestronglyMeasurable ((h r).operator.adjoint w - a)).congr
        (he r)).norm.fun_pow 2)) hi ?_ ?_
    · simpa only [integral_zero] using ht
    · intro r
      apply Eventually.of_forall
      intro u
      have hb : ‖(m r u : ℂ) - 1‖ ≤ M + 1 := by
        calc
          ‖(m r u : ℂ) - 1‖ ≤ ‖(m r u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ M + 1 := by simpa [Complex.norm_real, Real.norm_eq_abs] using
            add_le_add_right ((h r).mask_bound u) 1
      simp only [Real.norm_eq_abs, abs_sq, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg _)
    · filter_upwards [hm] with u hu
      have ht := (((Complex.continuous_ofReal.tendsto 1).comp hu).sub
        (tendsto_const_nhds (x := (1 : ℂ)))).mul_const (carrierAdjointIntegral d w u)
      simpa [Function.comp_def] using ht.norm.pow 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  change Tendsto (fun r ↦ Real.sqrt (∫ u,
    ‖((m r u : ℂ) - 1) * carrierAdjointIntegral d w u‖ ^ 2 ∂carrierMeasure n))
    atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [← hsq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- The original torus test pairing written with the full conic spectator
amplitude. Both physical positions are zero-extended outside the output chart;
no output measure is transported (`app:ch_background:eq:bg-full-complex-amplitude`). -/
def fullAmplitudeTestPairing {m : CarrierVariable n → ℝ}
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (v w : ComplexOutputL2 n) : ℂ :=
  ∫ x, inner ℂ (v x) (WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y,
    (if hx : x ∈ d.outputChart then if hy : y ∈ d.outputChart then
      ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          ((charts x hx y hy).amplitude k i j : ℂ)
      else 0 else 0) * w y j))

/-- Exact identification of the source-tested conic amplitude, including every
finite matrix sum and the original output measure
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeTestPairing_eq_normalTestPairing
    {m : CarrierVariable n → ℝ} (h : FiniteCarrierKernelBounds d m)
    (charts : ∀ x ∈ d.outputChart, ∀ y ∈ d.outputChart, ChartInputs d m x y)
    (v w : ComplexOutputL2 n) :
    fullAmplitudeTestPairing charts v w = normalTestPairing d m v w := by
  unfold fullAmplitudeTestPairing normalTestPairing
  congr 1
  funext x
  congr 1
  apply PiLp.ext
  intro i
  change (∑ j : Fin n, _) = ∑ j : Fin n, _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  by_cases hx : x ∈ d.outputChart
  · rw [dite_eq_left hx]
    by_cases hy : y ∈ d.outputChart
    · rw [dite_eq_left hy, (charts x hx y hy).normalEntry_eq h hx hy i j]
    · rw [dite_eq_right hy, regularizedNormalEntry_eq_zero_outside_right x hy i j]
  · simp [hx, regularizedNormalEntry, carrierKernel_eq_zero_outside d hx]

/-- The limiting adjoint pairing is an absolutely convergent integral on the
literal initial measure, by Cauchy–Schwarz for the two supplied L² tests
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_carrierAdjoint_pairing (v w : ComplexOutputL2 n)
    (hv : MemLp (carrierAdjointIntegral d v) 2 (carrierMeasure n))
    (hw : MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n)) :
    Integrable (fun u ↦ inner ℂ (carrierAdjointIntegral d v u)
      (carrierAdjointIntegral d w u)) (carrierMeasure n) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hv.toLp _) (hw.toLp _)).congr
  filter_upwards [hv.coeFn_toLp, hw.coeFn_toLp] with u hu hv
  rw [hu, hv]

/-- The full-amplitude test pairings converge to the literal uncut adjoint
pairing. Strong convergence is proved from mask exhaustion and square
integrability of these two tests, without any bound on the uncut carrier
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeTestPairing_tendsto
    {m : ℕ → CarrierVariable n → ℝ} {Z : Set CarrierParameter}
    {R : ℕ → ℝ} {M C : ℝ}
    (h : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Z (R r) M C)
    (hm : ∀ᵐ u ∂carrierMeasure n, Tendsto (fun r ↦ m r u) atTop (𝓝 1))
    (charts : ∀ r x, x ∈ d.outputChart → ∀ y, y ∈ d.outputChart → ChartInputs d (m r) x y)
    (v w : ComplexOutputL2 n)
    (hv : MemLp (carrierAdjointIntegral d v) 2 (carrierMeasure n))
    (hw : MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n)) :
    Tendsto (fun r ↦ fullAmplitudeTestPairing (charts r) v w) atTop
      (𝓝 (∫ u, inner ℂ (carrierAdjointIntegral d v u) (carrierAdjointIntegral d w u)
        ∂carrierMeasure n)) := by
  have ht := (regularizedOperator_adjoint_tendsto h hm v hv).inner
    (𝕜 := ℂ) (regularizedOperator_adjoint_tendsto h hm w hw)
  have he : inner ℂ (hv.toLp _) (hw.toLp _) = ∫ u,
      inner ℂ (carrierAdjointIntegral d v u) (carrierAdjointIntegral d w u)
        ∂carrierMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, hw.coeFn_toLp] with u hu hv
    rw [hu, hv]
  simpa only [he, fullAmplitudeTestPairing_eq_normalTestPairing
    (finiteCarrierKernelBoundsOfMask (h _)), regularizedOperator_normalTestPairing (h _) v w] using ht

/-- A separately supplied distributional limit of the full spectator kernels
is the literal uncut adjoint pairing. The mask square is present at every finite
stage, and disappears by dominated convergence on the initial measure
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullAmplitudeTestPairing_limit_identification
    {m : ℕ → CarrierVariable n → ℝ} {Z : Set CarrierParameter}
    {R : ℕ → ℝ} {M C : ℝ}
    (h : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Z (R r) M C)
    (hm : ∀ᵐ u ∂carrierMeasure n, Tendsto (fun r ↦ m r u) atTop (𝓝 1))
    (charts : ∀ r x, x ∈ d.outputChart → ∀ y, y ∈ d.outputChart → ChartInputs d (m r) x y)
    (v w : ComplexOutputL2 n)
    (hv : MemLp (carrierAdjointIntegral d v) 2 (carrierMeasure n))
    (hw : MemLp (carrierAdjointIntegral d w) 2 (carrierMeasure n))
    (L : ℂ) (hL : Tendsto (fun r ↦ fullAmplitudeTestPairing (charts r) v w)
      atTop (𝓝 L)) :
    L = ∫ u, inner ℂ (carrierAdjointIntegral d v u) (carrierAdjointIntegral d w u)
      ∂carrierMeasure n :=
  tendsto_nhds_unique hL (fullAmplitudeTestPairing_tendsto h hm charts v w hv hw)

/-- The real finite carrier normals have the factor-four literal test limit.
This uses the checked quadrature adjoint identity, and therefore retains both
complex input quadratures (`app:ch_background:eq:bg-real-symbol`). -/
theorem regularizedOperator_realNormal_tendsto
    {m : ℕ → CarrierVariable n → ℝ} {Z : Set CarrierParameter}
    {R : ℕ → ℝ} {M C : ℝ}
    (h : ∀ r, CarrierRegularization.MaskHypotheses d (m r) Z (R r) M C)
    (hm : ∀ᵐ u ∂carrierMeasure n, Tendsto (fun r ↦ m r u) atTop (𝓝 1))
    (v w : OutputL2 n)
    (hv : MemLp (carrierAdjointIntegral d (l2ComplexInclusion volume v)) 2 (carrierMeasure n))
    (hw : MemLp (carrierAdjointIntegral d (l2ComplexInclusion volume w)) 2 (carrierMeasure n)) :
    Tendsto (fun r ↦ inner ℝ v (realQuadratureChannel (h r).operator
      ((realQuadratureChannel (h r).operator).adjoint w))) atTop
      (𝓝 (4 * (∫ u, inner ℂ
        (carrierAdjointIntegral d (l2ComplexInclusion volume v) u)
        (carrierAdjointIntegral d (l2ComplexInclusion volume w) u)
          ∂carrierMeasure n).re)) := by
  have ht := (regularizedOperator_adjoint_tendsto h hm (l2ComplexInclusion volume v) hv).inner
    (𝕜 := ℂ) (regularizedOperator_adjoint_tendsto h hm (l2ComplexInclusion volume w) hw)
  have he : inner ℂ (hv.toLp _) (hw.toLp _) = ∫ u, inner ℂ
      (carrierAdjointIntegral d (l2ComplexInclusion volume v) u)
      (carrierAdjointIntegral d (l2ComplexInclusion volume w) u) ∂carrierMeasure n := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv.coeFn_toLp, hw.coeFn_toLp] with u hu hv
    rw [hu, hv]
  have hr := (Complex.continuous_re.tendsto _).comp ht
  simpa only [Function.comp_def, regularizedOperator_realNormal_pairing (h _) v w,
    regularizedOperator_normalTestPairing (h _) (l2ComplexInclusion volume v)
      (l2ComplexInclusion volume w), he] using hr.const_mul 4

end JanetCartan.ContinuumRow.TransportKernel
