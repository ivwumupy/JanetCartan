module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.BoxOperators

/-!
# Finite oscillatory kernels on arbitrary physical boxes

Exact Fourier reconstruction, finite integral realization, and distributional
convergence for `app:ch_osc:lem:osc-amplitude`. Removing the physical Fourier
truncation inside a fixed-frequency integral is still a separate step.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace JanetCartan.AmplitudeBound

variable {d : ℕ}

/-- The actual compact amplitude has its exact cutoff Fourier expansion on
any fixed physical box (`app:ch_osc:lem:osc-amplitude`). -/
theorem hasSum_boxAmplitude_expansion (hd : 0 < d)
    {b : EuclideanSpace ℝ (Fin (2 * d)) → ℂ} {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2) (hs : SupportedInCenteredBox R b)
    (hf : ContDiff ℝ ∞ b) {A : ℝ} (hzero : ∀ z, ‖b z‖ ≤ A)
    (hderiv : ∀ i z,
      ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) b z‖ ≤ A)
    (x y : EuclideanSpace ℝ (Fin d)) :
    HasSum (fun k ↦
      (boxCellCutoff ℓ x * UnitAddTorus.mFourier k (leftPositionChart ℓ x)) *
      UnitAddTorus.mFourierCoeff (boxAmplitudePeriodization ℓ b) k *
      (boxCellCutoff ℓ y * UnitAddTorus.mFourier k (rightPositionChart ℓ y)))
      (b (pairedPosition x y)) := by
  simpa only [boxCellCutoff_boxAmplitudePeriodization_eq hℓ hR hs] using
    hasSum_cutoff_twoPosition_expansion hd
      (isSmoothPeriodic_boxAmplitudePeriodization hℓ hR hs hf)
      (norm_boxAmplitudePeriodization_le_factor hzero ℓ)
      (norm_pureDeriv_boxAmplitudePeriodization_le_factor hℓ hR hs hf
        ((norm_nonneg (b 0)).trans (hzero 0)) hderiv)
      ℓ (boxCellCutoff ℓ) (boxCellCutoff ℓ) x y

variable (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : StronglyMeasurable (Function.uncurry b)) (hd : 0 < d)
  {R ℓ : ℝ} (hℓ : 0 < ℓ) (hR : R / ℓ < 1 / 2)
  (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (hf : ∀ ξ, ContDiff ℝ ∞ (b ξ))
  (A : ℝ) (hzero : ∀ ξ z, ‖b ξ z‖ ≤ A)
  (hderiv : ∀ ξ i z,
    ‖euclideanCoordinateDerivList (List.replicate (2 * (d + 1)) i) (b ξ) z‖ ≤ A)

/-- The literal finite oscillatory integral on an arbitrary fixed box
(`app:ch_osc:lem:osc-amplitude`). -/
def boxFiniteAmplitudeKernel (ℓ : ℝ) (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) : EuclideanSpace ℝ (Fin d) → ℂ :=
  regularizedPhysicalAmplitudeKernel (fun ξ ↦ boxAmplitudePeriodization ℓ (b ξ))
    ℓ (boxCellCutoff ℓ) (boxCellCutoff ℓ) s ρ f

/-- The finite operator equals its literal integral on every L² input
(`app:ch_osc:lem:osc-amplitude`). Compactness of the outer input cutoff
supplies the required integrability. -/
theorem boxRegularizedAmplitudeOperator_ae_kernel
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv s ρ f =ᵐ[volume]
      boxFiniteAmplitudeKernel b ℓ s ρ f :=
  regularizedPhysicalAmplitudeOperator_ae_kernel
    (fun ξ ↦ boxAmplitudePeriodization ℓ (b ξ))
    (stronglyMeasurable_boxAmplitudePeriodization hb ℓ) hd
    (fun ξ ↦ isSmoothPeriodic_boxAmplitudePeriodization hℓ hR (hs ξ) (hf ξ))
    (boxDerivativeFactor d ℓ * A)
    (fun ξ ↦ norm_boxAmplitudePeriodization_le_factor (hzero ξ) ℓ)
    (fun ξ ↦ norm_pureDeriv_boxAmplitudePeriodization_le_factor hℓ hR (hs ξ) (hf ξ)
      ((norm_nonneg (b 0 0)).trans (hzero 0 0)) (hderiv ξ))
    ℓ (boxCellCutoff ℓ) (boxCellCutoff ℓ)
    (aestronglyMeasurable_boxCellCutoff ℓ) (aestronglyMeasurable_boxCellCutoff ℓ)
    (Eventually.of_forall (norm_boxCellCutoff_le ℓ))
    (Eventually.of_forall (norm_boxCellCutoff_le ℓ))
    (hasCompactSupport_boxCellCutoff hℓ.ne') s ρ f

include hb hd hℓ hR hs hf A hzero hderiv

/-- The finite literal integrals belong to L² (`app:ch_osc:lem:osc-amplitude`). -/
theorem memLp_boxFiniteAmplitudeKernel
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    MemLp (boxFiniteAmplitudeKernel b ℓ s ρ f) 2 :=
  (Lp.memLp _).ae_eq
    (boxRegularizedAmplitudeOperator_ae_kernel b hb hd hℓ hR hs hf A hzero hderiv s ρ f)

/-- The L² class of the literal finite integral on the physical box
(`app:ch_osc:lem:osc-amplitude`). -/
def boxFiniteAmplitudeKernelLp (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2 :=
  (memLp_boxFiniteAmplitudeKernel b hb hd hℓ hR hs hf A hzero hderiv s ρ f).toLp _

/-- The L² realization equals the constructed regularization
(`app:ch_osc:lem:osc-amplitude`). -/
theorem boxFiniteAmplitudeKernelLp_eq
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    boxFiniteAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv s ρ f =
      boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv s ρ f := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans
    (boxRegularizedAmplitudeOperator_ae_kernel b hb hd hℓ hR hs hf A hzero hderiv s ρ f).symm

/-- The norm bound on literal finite integrals is independent of both
truncations (`app:ch_osc:lem:osc-amplitude`). -/
theorem norm_boxFiniteAmplitudeKernelLp_le
    (s : Finset (Fin (2 * d) → ℤ)) (ρ : ℝ)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    ‖boxFiniteAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv s ρ f‖ ≤
      (boxAmplitudeConstant d ℓ * A) * ‖f‖ := by
  rw [boxFiniteAmplitudeKernelLp_eq]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (norm_boxRegularizedAmplitudeOperator_le b hb hd hℓ hR
      hs hf A hzero hderiv s ρ) (norm_nonneg f))

/-- The literal finite kernels converge distributionally to the constructed
scalar operator (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_boxFiniteAmplitudeKernel_temperedDistribution
    {β : Type*} {m : Filter β} (s : β → Finset (Fin (2 * d) → ℤ)) (ρ : β → ℝ)
    (hsexhaust : ∀ k, ∀ᶠ j in m, k ∈ s j) (hρ : Tendsto ρ m atTop)
    (f : Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) :
    Tendsto (fun j ↦ Lp.toTemperedDistribution
      (boxFiniteAmplitudeKernelLp b hb hd hℓ hR hs hf A hzero hderiv (s j) (ρ j) f)) m
      (𝓝 (Lp.toTemperedDistribution
        (boxScalarAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv f))) := by
  simp_rw [boxFiniteAmplitudeKernelLp_eq]
  exact (Lp.toTemperedDistributionCLM ℂ (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).continuous.continuousAt.tendsto.comp
    (tendsto_boxRegularizedAmplitudeOperator b hb hd hℓ hR hs hf A hzero hderiv
      s ρ hsexhaust hρ f)

end JanetCartan.AmplitudeBound
