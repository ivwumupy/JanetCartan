module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Basic
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.EuclideanChannel.Multipliers
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.Freezing.AllData.Multipliers

/-!
# The actual bounded Euclidean image channel

Construct the finite matrix of compact coefficient multipliers and bounded
Fourier multipliers in `app:ch_background:prop:bg-frame`, Step 1. Only `μ A`
and `μ Z` enter the multiplication operators. Neither the original coefficients
nor the differential operator `P` are assumed bounded. The consumers are the
two Schwartz actions in `normal_schwartz_action_of_channel_actions` and the
Sobolev input of `normalCrossTerms_sobolev_one_bounds`.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
open JanetCartan.ContinuumNormal JanetCartan.PeriodicLocalL2

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L²" => Lp ℂ 2 (volume : Measure E)
local notation "C²" => Lp (EuclideanSpace ℂ (Fin d)) 2 (volume : Measure E)
local notation "R²" => EuclideanL2 d E

/-- A scalar matrix entry of `μ P J χ`, as a sum of actual bounded
operators (`app:ch_background:prop:bg-frame`, Step 1). -/
def euclideanChannelBlock
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (i j : Fin d) : L² →L[ℂ] L² :=
  ((∑ a, (freezingPhysicalMultiplier (fun x ↦ μ x * A x a i j)
      (hμ.continuous.mul (hA a i j).continuous) hμc.mul_right).comp
        (imageDerivativeBesselL2Operator a)) +
    (freezingPhysicalMultiplier (fun x ↦ μ x * Z x i j)
      (hμ.continuous.mul (hZ i j).continuous) hμc.mul_right).comp
        imageBesselL2Operator).comp
    (freezingPhysicalMultiplier χ hχ.continuous hχc)

/-- The bounded complex matrix channel on Euclidean Lebesgue L²
(`app:ch_background:prop:bg-frame`, Step 1). -/
def complexEuclideanChannel
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) : C² →L[ℂ] C² :=
  vectorMatrixL2Operator (euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc)

/-- The actual bounded real Euclidean channel for the image normal
(`app:ch_background:prop:bg-frame`, Step 1). Its reality and test actions are
proved for this same concrete operator, rather than supplied as data. -/
def euclideanChannel
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) : R² →L[ℝ] R² :=
  realOutputCompression (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc)

private theorem supported_add (s : Set E) (f g : L²)
    (hf : ∀ᵐ x ∂volume, x ∉ s → f x = 0)
    (hg : ∀ᵐ x ∂volume, x ∉ s → g x = 0) :
    ∀ᵐ x ∂volume, x ∉ s → (f + g) x = 0 := by
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hf hg
  intro hxs
  simpa only [Pi.add_apply, hf hxs, hg hxs, add_zero] using hx

private theorem supported_sum {ι : Type*} (t : Finset ι) (s : Set E) (f : ι → L²)
    (hf : ∀ i ∈ t, ∀ᵐ x ∂volume, x ∉ s → f i x = 0) :
    ∀ᵐ x ∂volume, x ∉ s → (∑ i ∈ t, f i) x = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx
    exact fun _ ↦ hx
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact supported_add s _ _ (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem supported_maskedMultiplier (μ c : E → ℝ)
    (hμ : Continuous μ) (hc : Continuous c) (hμc : HasCompactSupport μ) (f : L²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ →
      freezingPhysicalMultiplier (fun x ↦ μ x * c x) (hμ.mul hc) hμc.mul_right f x = 0 := by
  filter_upwards [freezingPhysicalMultiplier_coeFn (fun x ↦ μ x * c x)
    (hμ.mul hc) hμc.mul_right f] with x hx
  intro hxs
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, zero_mul, zero_smul]

/-- Every scalar block retains the measurement support on arbitrary L²
inputs (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannelBlock_support
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (i j : Fin d) (f : L²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ →
      euclideanChannelBlock A Z χ μ hA hZ hχ hχc hμ hμc i j f x = 0 := by
  simp only [euclideanChannelBlock, ContinuousLinearMap.comp_apply, add_apply, sum_apply]
  exact supported_add (tsupport μ) _ _
    (supported_sum Finset.univ (tsupport μ) _ (fun a _ ↦
      supported_maskedMultiplier μ _ hμ.continuous (hA a i j).continuous hμc _))
    (supported_maskedMultiplier μ _ hμ.continuous (hZ i j).continuous hμc _)

/-- The actual complex matrix channel retains the measurement support
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem complexEuclideanChannel_support
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (f : C²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ →
      complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f x = 0 := by
  let B := complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc
  have hs (i : Fin d) : ∀ᵐ x ∂volume, x ∉ tsupport μ →
      finiteL2CoordinateIsometry volume (B f) i x = 0 := by
    simp only [B, complexEuclideanChannel,
      finiteL2CoordinateIsometry_vectorMatrixL2Operator, matrixOperator_apply]
    exact supported_sum Finset.univ (tsupport μ) _ (fun j _ ↦
      euclideanChannelBlock_support A Z χ μ hA hZ hχ hχc hμ hμc i j _)
  filter_upwards [ae_all_iff.mpr hs,
    ae_all_iff.mpr (fun i ↦ finiteL2Coordinates_apply_ae volume (B f) i)] with x hx hy
  intro hxs
  apply PiLp.ext
  intro i
  exact (hy i).symm.trans (hx i hxs)

/-- The concrete real channel has exactly the support property required by
`normalCrossTerms_periodic_endpoints` (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_support
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) (f : R²) :
    ∀ᵐ x ∂volume, x ∉ tsupport μ →
      euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc f x = 0 := by
  let g := complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc
    (l2ComplexInclusion volume f)
  filter_upwards [euclideanRealPart.coeFn_compLpL g,
    complexEuclideanChannel_support A Z χ μ hA hZ hχ hχc hμ hμc
      (l2ComplexInclusion volume f)] with x hx hs
  intro hxs
  change l2RealPart volume g x = euclideanRealPart (g x) at hx
  change l2RealPart volume g x = 0
  rw [hx, hs hxs, map_zero]

/-- Real compression preserves the literal Hilbert adjoint of this same
concrete channel (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem euclideanChannel_adjoint
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ) (χ μ : E → ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ) :
    (euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint =
      realOutputCompression (complexEuclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc).adjoint := by
  have hi : (l2ComplexInclusion (ι := Fin d) (volume : Measure E)).adjoint =
      l2RealPart volume := by
    rw [← l2RealPart_adjoint, ContinuousLinearMap.adjoint_adjoint]
  simp only [euclideanChannel, realOutputCompression, ContinuousLinearMap.adjoint_comp,
    hi, l2RealPart_adjoint, adjoint_restrictScalars_complex, ContinuousLinearMap.comp_assoc]

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
