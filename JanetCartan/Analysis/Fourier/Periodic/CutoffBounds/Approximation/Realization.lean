module

public import JanetCartan.Analysis.Fourier.Periodic.CutoffBounds.Approximation.Realization.Scalar

/-!
# Euclidean realization of the fixed periodic cutoff

For `paper.tex`, `main:lem:smoothing` and `main:eq:smoothing-high`, the actual
periodic multiplier is convolution with the inverse transform of the fixed symbol,
at displacement `(2π / R) y`. Scalar Fourier reconstruction and continuous linear
functionals give the identity for real Banach-valued fields, in particular every
finite-dimensional real normed codomain.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- `main:eq:smoothing-high`: continuous real linear maps commute with the
integrable Euclidean cutoff convolution. -/
theorem cutoffEuclideanConvolution_comp_clm (A : F →L[ℝ] G) {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    cutoffEuclideanConvolution R (A ∘ f) x = A (cutoffEuclideanConvolution R f x) := by
  unfold cutoffEuclideanConvolution
  change (∫ y, cutoffSchwartzKernel n y • A (periodicLift f
    (x - (2 * Real.pi / R) • y))) = _
  simp_rw [← A.map_smul]
  exact A.integral_comp_comm (integrable_cutoffEuclideanConvolution hf R x)

/-- `main:lem:smoothing`, `main:eq:smoothing-high`: the fixed periodic Fourier
cutoff is exactly Euclidean convolution with the real inverse transform of its
symbol. All integrability and reconstruction inputs are discharged by smoothness.
This Banach-valued statement includes finite-dimensional real normed spaces. -/
theorem cutoffEuclideanConvolution_eq_periodicCutoff {f : Torus n → F}
    (hf : IsSmoothPeriodic f) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin n)) :
    cutoffEuclideanConvolution R f x = periodicLift (periodicCutoff R f) x := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro A
  have h := cutoffEuclideanConvolution_eq_periodicCutoff_scalar (hf.comp_clm A) hR x
  change cutoffEuclideanConvolution R (A ∘ f) x =
    periodicLift (periodicCutoff R (A ∘ f)) x at h
  rw [cutoffEuclideanConvolution_comp_clm A hf, periodicCutoff_comp_clm A hf.1] at h
  exact h

end JanetCartan
