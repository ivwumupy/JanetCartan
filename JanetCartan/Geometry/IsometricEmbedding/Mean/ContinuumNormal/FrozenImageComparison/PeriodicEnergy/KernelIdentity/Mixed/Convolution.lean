module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.PeriodicEnergy.KernelIdentity.Mixed.Source
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Transferring the mixed Bessel derivative to its compact input

For `paper-v2.tex`, `app:ch_background:prop:bg-frame`, differentiation
of the Euclidean inverse is transferred to the smooth compact source. The
literal Bessel kernel remains an undifferentiated L¹ factor. The consumer
is the forward mixed composition `B D*`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ContDiff SchwartzMap Convolution
open JanetCartan.ContinuumNormalReduction.ImageNormal

namespace JanetCartan.ContinuumNormal.FrozenImageComparison.KernelIdentity

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The differentiated Euclidean inverse differentiates only the compact
Schwartz source. This is the derivative transfer used for the actual mixed
term in `app:ch_background:prop:bg-frame`. -/
theorem partialDeriv_imageBesselSchwartz_compact (w : 𝓢(E, ℂ))
    (hw : HasCompactSupport (w : E → ℂ)) (x : E) (a : Fin n) :
    partialDeriv (imageBesselSchwartzCLM w) x a =
      ∫ t : E, (imageBesselKernel t : ℂ) *
        fderiv ℝ (w : E → ℂ) (x - t) (EuclideanSpace.single a 1) := by
  let L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  let K : E → ℂ := fun t ↦ (imageBesselKernel t : ℂ)
  have hK : LocallyIntegrable K := integrable_imageBesselKernel.ofReal.locallyIntegrable
  have he : (imageBesselSchwartzCLM w : E → ℂ) = K ⋆[L] (w : E → ℂ) := by
    funext z
    rw [imageBesselSchwartzCLM_apply, imageBesselMultiplier_eq_convolution,
      convolution_eq_swap]
    rfl
  rw [partialDeriv, he, (hw.hasFDerivAt_convolution_right L hK
    (w.smooth 1) x).fderiv, convolution_precompR_apply L hK
      (hw.fderiv ℝ) (w.smooth 1 |>.continuous_fderiv one_ne_zero)]
  rfl

end JanetCartan.ContinuumNormal.FrozenImageComparison.KernelIdentity
