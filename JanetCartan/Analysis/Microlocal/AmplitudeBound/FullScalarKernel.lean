module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.FullScalarKernel.PhysicalLimit
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The full scalar amplitude kernel

The literal compact-frequency integral in `app:ch_osc:lem:osc-amplitude`
agrees almost everywhere with the full physical operator series. It belongs to
L² with a bound independent of the frequency radius, and converges strongly
and as a tempered distribution when that radius tends to infinity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

/-- The full physical operator series with compact frequency support equals
the original oscillatory integral almost everywhere on every L² input
(`app:ch_osc:lem:osc-amplitude`). The finite kernels converge pointwise by their
summable Fourier expansion and in L² by operator norm convergence; an almost
everywhere convergent subsequence identifies the two limits. -/
theorem boxCompactFrequencyAmplitudeOperator_ae_kernel (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ f =ᵐ[volume]
      boxScalarAmplitudeKernel b ρ f := by
  obtain ⟨s, hsexhaust, hsae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      (tendsto_boxFiniteAmplitudeKernelLp_fixed_frequency
        b hb hd hℓ hR hs hf A hzero hderiv ρ f)).exists_seq_tendsto_ae'
  have heq : ∀ᵐ x, ∀ n : ℕ,
      boxFiniteAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv (s n) ρ f x =
        boxFiniteAmplitudeKernel b ℓ (s n) ρ f x :=
    ae_all_iff.mpr (fun n ↦ MemLp.coeFn_toLp
      (memLp_boxFiniteAmplitudeKernel b hb hd hℓ hR hs hf A hzero hderiv (s n) ρ f))
  filter_upwards [hsae, heq] with x hx hx'
  have hp := (tendsto_boxFiniteAmplitudeKernel_fixed_frequency
    b hb hd hℓ hR hs hf A hzero hderiv ρ f x).comp hsexhaust
  exact tendsto_nhds_unique (hx.congr (fun n ↦ hx' n)) hp

include hb hd hℓ hR hs hf A hzero hderiv

/-- The original compact-frequency integral belongs to L² on every L² input
(`app:ch_osc:lem:osc-amplitude`). -/
theorem memLp_boxScalarAmplitudeKernel (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    MemLp (boxScalarAmplitudeKernel b ρ f) 2 :=
  (Lp.memLp _).ae_eq
    (boxCompactFrequencyAmplitudeOperator_ae_kernel b hb hd hℓ hR hs hf A hzero hderiv ρ f)

/-- The L² class of the original compact-frequency oscillatory integral
(`app:ch_osc:lem:osc-amplitude`), with no physical Fourier truncation. -/
def boxScalarAmplitudeKernelLp (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  (memLp_boxScalarAmplitudeKernel b hb hd hℓ hR hs hf A hzero hderiv ρ f).toLp _

/-- The L² realization of the original integral is the full physical operator
series with compact frequency support (`app:ch_osc:lem:osc-amplitude`). -/
theorem boxScalarAmplitudeKernelLp_eq (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    boxScalarAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv ρ f =
      boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv ρ f := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (boxCompactFrequencyAmplitudeOperator_ae_kernel
      b hb hd hℓ hR hs hf A hzero hderiv ρ f).symm

/-- The original compact-frequency integral has a uniform L² bound independent
of the frequency radius (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxScalarAmplitudeKernelLp_le (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖boxScalarAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv ρ f‖ ≤
      (boxAmplitudeConstant d ℓ * A) * ‖f‖ := by
  rw [boxScalarAmplitudeKernelLp_eq]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (norm_boxCompactFrequencyAmplitudeOperator_le
      b hb hd hℓ hR hs hf A hzero hderiv ρ) (norm_nonneg f))

/-- The original compact-frequency integrals converge strongly to the scalar
amplitude operator as the frequency radius tends to infinity
(`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxScalarAmplitudeKernelLp
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦
      boxScalarAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv ρ f) atTop
      (𝓝 (boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f)) := by
  simp_rw [boxScalarAmplitudeKernelLp_eq]
  exact tendsto_boxCompactFrequencyAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f

/-- Compact frequency regularization of the original oscillatory integral
converges to the scalar amplitude operator as a tempered distribution
(`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxScalarAmplitudeKernel_temperedDistribution
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun ρ : ℝ ↦ Lp.toTemperedDistribution
      (boxScalarAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv ρ f)) atTop
      (𝓝 (Lp.toTemperedDistribution
        (boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f))) := by
  exact (Lp.toTemperedDistributionCLM ℂ
    (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).continuous.continuousAt.tendsto.comp
      (tendsto_boxScalarAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv f)

end JanetCartan.AmplitudeBound
