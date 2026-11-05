module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FiniteNormal

/-!
# Matching the frozen image and carrier energies

The frozen coercivity assembly for `app:ch_background:prop:bg-frame` uses
the same Euclidean Fourier energy for the ideal image and the realized
carriers. These identities preserve the physical frequency `2πξ`, the cell
zero extension, and the original fixed outer measurement mask.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Metric Matrix
open scoped FourierTransform

namespace JanetCartan.ContinuumNormal.FrozenCoercivity

open ContinuumRow PeriodicLocalL2 FrozenModel FrozenImageComparison

variable {n : ℕ}

/-- Constant first-order arrays of the frozen stress pencil, with zero
connection term supplied by `constantImageCoefficients`
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
def frozenImageArrays (Q : Fin n → MetricTensor n) :
    Fin n → Matrix (Fin n) (Fin n) ℝ := fun a i j ↦ Q i j a

/-- The image comparison uses the literal pencil of the frozen carrier model
(`app:ch_background:prop:bg-frame`). -/
theorem principalMatrix_frozenImageArrays (Q : Fin n → MetricTensor n) (k : Euclidean n) :
    principalMatrix (frozenImageArrays Q) k = ActualCarriers.pencil Q k := by
  ext i j
  simp only [principalMatrix, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    frozenImageArrays, ActualCarriers.pencil, mul_comm]

/-- The two frozen image normal matrices agree at every physical covector
(`app:ch_background:prop:bg-frame`). -/
theorem normalMatrix_frozenImageArrays (Q : Fin n → MetricTensor n) (k : Euclidean n) :
    normalMatrix (frozenImageArrays Q) k = frozenImageSymbol Q k := by
  simp only [normalMatrix, principalMatrix_frozenImageArrays, frozenImageSymbol]

/-- Exact energy identification for the real cell zero extension, including
both Fourier quadratures (`app:ch_background:prop:bg-frame`). -/
theorem fourierEnergy_eq_euclideanFrozenImageEnergy
    (Q : Fin n → MetricTensor n) (f : OutputL2 n) :
    fourierEnergy (frozenImageArrays Q) (toEuclidean (𝕜 := ℝ) f) =
      euclideanFrozenEnergy (frozenImageSymbol Q)
        (fun x ↦ euclideanComplexInclusion (toEuclidean (𝕜 := ℝ) f x)) := by
  rw [fourierEnergy_zeroExtension_eq_fourierIntegral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  dsimp only
  rw [← re_inner_complexifyMatrix_eq_realifiedMatrixQuadraticForm]
  congr 2
  simp only [normalComplexAction, normalMatrix_frozenImageArrays]
  rfl

/-- On inner-supported inputs the fixed physical measurement is exactly one
on the zero extension (`app:ch_background:prop:bg-frame`). -/
theorem measured_eq_zeroExtension {r R : ℝ}
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (f : OutputL2 n)
    (hf : ∀ᵐ z ∂volume, z ∉ torusQuotient '' ball (0 : Euclidean n) r → f z = 0) :
    (fun x ↦ FixedCutoffs.physical hR 1 x • toEuclidean (𝕜 := ℝ) f x)
      =ᵐ[volume] toEuclidean (𝕜 := ℝ) f := by
  filter_upwards [toEuclidean_supported_innerBall hR hcell hrR f hf] with x hx
  by_cases hxr : x ∈ ball (0 : Euclidean n) r
  · have hp : FixedCutoffs.physical hR 1 x = 1 := by
      apply interior_subset (FixedCutoffs.physical_plateau hR 1 _)
      apply (closedBall_subset_closedBall (show r ≤ (((1 : Fin 3) + 1 : ℝ) * R) by
        norm_num
        linarith)) (ball_subset_closedBall hxr)
    rw [hp, one_smul]
  · rw [hx hxr, smul_zero]

/-- Real-to-complex inclusion and cell zero extension preserve the squared
norm used in the Euclidean small-support gap
(`app:ch_background:prop:bg-frame`). -/
theorem complex_zeroExtension_norm_sq (f : OutputL2 n) :
    ‖l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f)‖ ^ 2 = ‖f‖ ^ 2 := by
  rw [← SingleChannel.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ x, ‖toEuclidean (𝕜 := ℝ) f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [euclideanComplexInclusion.coeFn_compLpL
        (toEuclidean (𝕜 := ℝ) f)] with x hx
      rw [show l2ComplexInclusion volume (toEuclidean (𝕜 := ℝ) f) x =
        euclideanComplexInclusion (toEuclidean (𝕜 := ℝ) f x) from hx,
        euclideanComplexInclusion_norm]
    _ = ‖toEuclidean (𝕜 := ℝ) f‖ ^ 2 := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ) (toEuclidean (𝕜 := ℝ) f) (toEuclidean (𝕜 := ℝ) f)).symm
    _ = _ := by rw [norm_zeroExtension]

/-- The actual physical row energy is the sum of its image and carrier
energies; the carrier summands already contain both quadratures and factor
four (`app:ch_background:eq:bg-realification`). -/
theorem physicalRow_adjoint_norm_sq {ι : Type*} [Fintype ι]
    (image : OutputL2 n →L[ℝ] OutputL2 n)
    (V : ι → CarrierL2 n →L[ℂ] ComplexOutputL2 n) (f : OutputL2 n) :
    ‖(physicalRow image V).adjoint f‖ ^ 2 =
      ‖image.adjoint f‖ ^ 2 + ∑ i, ‖(realQuadratureChannel (V i)).adjoint f‖ ^ 2 := by
  rw [physicalRow_adjoint_apply, WithLp.prod_norm_sq_eq_of_L2,
    carrierRow_adjoint_apply]
  simp only [PiLp.norm_sq_eq_of_L2]
  rfl

end JanetCartan.ContinuumNormal.FrozenCoercivity
