module
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.LocalComparison.EuclideanKernel.Fourier
public import Mathlib.Analysis.Fourier.Convolution
/-!
# Convolution realization of the image Bessel multiplier

For `app:ch_background:defn:bg-row` and `app:ch_background:prop:bg-frame`,
Step 1, the actual heat kernel realizes the complex Schwartz multiplier.
Its already proved L¹ integrability and Fourier formula give the identity by
Fourier inversion for the continuous convolution. This pointwise formula is
consumed by the identification of the nonzero lattice tail as a kernel error.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped FourierTransform SchwartzMap Convolution
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The convolution formula is absolutely convergent at every evaluation point,
as required for the kernel error in `app:ch_background:prop:bg-frame`, Step 1. -/
theorem integrable_imageBesselKernel_mul_schwartz (u : 𝓢(E, ℂ)) (x : E) :
    Integrable (fun y : E ↦ (imageBesselKernel (x - y) : ℂ) * u y) := by
  apply (integrable_imageBesselKernel.ofReal.comp_sub_left x).mul_bdd
    u.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ u)

/-- The complex Schwartz image inverse is convolution with the literal heat
kernel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBesselMultiplier_eq_convolution (u : 𝓢(E, ℂ)) (x : E) :
    schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u x =
      ∫ y : E, (imageBesselKernel (x - y) : ℂ) * u y := by
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  let K : E → ℂ := fun x ↦ (imageBesselKernel x : ℂ)
  let v := schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ)) u
  have hi : Integrable K := integrable_imageBesselKernel.ofReal
  have hb : BddAbove (Set.range (fun y ↦ ‖u y‖)) :=
    ⟨SchwartzMap.seminorm ℝ 0 0 u, fun _ ⟨y, hy⟩ ↦ hy ▸ SchwartzMap.norm_le_seminorm ℝ u y⟩
  have hc : Continuous (K ⋆[B] (u : E → ℂ)) :=
    hb.continuous_convolution_right_of_integrable B hi u.continuous
  have hF : 𝓕 (K ⋆[B] (u : E → ℂ)) = (𝓕 v : 𝓢(E, ℂ)) := by
    ext ξ
    rw [Real.fourier_bilin_convolution_eq B hi u.integrable]
    change (𝓕 K ξ) * (𝓕 (u : E → ℂ) ξ) = _
    rw [fourier_imageBesselKernel, ← SchwartzMap.fourier_coe]
    exact (fourier_imageBesselMultiplier u ξ).symm
  have hiF : Integrable (𝓕 (K ⋆[B] (u : E → ℂ))) := by
    rw [hF]
    exact (𝓕 v : 𝓢(E, ℂ)).integrable
  calc
    _ = 𝓕⁻ (𝓕 v : 𝓢(E, ℂ)) x := by simp [v]
    _ = 𝓕⁻ (𝓕 (K ⋆[B] (u : E → ℂ))) x := by rw [SchwartzMap.fourierInv_coe, hF]
    _ = (K ⋆[B] (u : E → ℂ)) x :=
      congrFun (hc.fourierInv_fourier_eq (hi.integrable_convolution B u.integrable) hiF) x
    _ = _ := convolution_eq_swap B
end JanetCartan.ContinuumNormalReduction.ImageNormal
