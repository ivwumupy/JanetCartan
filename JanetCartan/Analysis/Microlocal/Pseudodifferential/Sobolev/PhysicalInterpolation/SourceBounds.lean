module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation.Coordinates
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Realization

/-!
# Source Fréchet bounds from the physical coordinate budget

For `app:ch_regular_base:thm:actual-calculus`, the source-bound premises of
`Realization` follow from the actual physical coordinate derivatives.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff ENNReal
open JanetCartan.AmplitudeBound
namespace JanetCartan.Pseudodifferential

/-- `app:ch_regular_base:thm:actual-calculus`: insertion into the source half of
the physical position vector, as a continuous linear map. -/
def physicalSourceInclusion (d : ℕ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (2 * d)) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun y ↦ pairedPosition 0 y
    map_add' := by
      intro y z
      ext i
      simp only [pairedPosition, PiLp.toLp_apply, PiLp.add_apply]
      split_ifs <;> simp
    map_smul' := by
      intro r y
      ext i
      simp only [pairedPosition, PiLp.toLp_apply, PiLp.smul_apply]
      split_ifs <;> simp }

/-- `app:ch_regular_base:thm:actual-calculus`: fixing the output position is
an affine source inclusion. -/
theorem pairedPosition_eq_add_physicalSourceInclusion {d : ℕ}
    (x y : EuclideanSpace ℝ (Fin d)) :
    pairedPosition x y = pairedPosition x 0 + physicalSourceInclusion d y := by
  change pairedPosition x y = pairedPosition x 0 + pairedPosition 0 y
  ext i
  by_cases hi : i.val < d <;> simp [pairedPosition, hi]

/-- `app:ch_regular_base:thm:actual-calculus`: all finite source Fréchet bounds
are derived from the coordinate budget, uniformly in both positions and frequency.
The displayed constant depends only on dimension and derivative order. -/
theorem norm_iteratedFDeriv_source_le_physicalBudget {X : Type*} {d N : ℕ}
    {b : X → EuclideanSpace ℝ (Fin (2 * d)) → ℂ}
    (hb : ∀ ξ, ContDiff ℝ ∞ (b ξ)) {A : ℝ}
    (hA : HasAmplitudeDerivativeBound b N A) (ξ : X)
    (x y : EuclideanSpace ℝ (Fin d)) {k : ℕ} (hk : k ≤ N) :
    ‖iteratedFDeriv ℝ k (fun z ↦ b ξ (pairedPosition x z)) y‖ ≤
      ((2 * d : ℕ) : ℝ) ^ k * A * ‖physicalSourceInclusion d‖ ^ k := by
  let f := fun z ↦ b ξ (pairedPosition x 0 + z)
  have hf : ContDiff ℝ ∞ f := (hb ξ).comp (contDiff_const.add contDiff_id)
  have heq : (fun z ↦ b ξ (pairedPosition x z)) = f ∘ physicalSourceInclusion d := by
    funext z
    rw [pairedPosition_eq_add_physicalSourceInclusion]
    rfl
  rw [heq]
  apply (norm_iteratedFDeriv_comp_linear_le (physicalSourceInclusion d) f hf k y).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp [f]
  rw [iteratedFDeriv_comp_add_left]
  exact norm_iteratedFDeriv_le_amplitudeBudget hb hA ξ hk _

/-- `app:ch_regular_base:thm:actual-calculus`: the physical coordinate budget
alone discharges the additional source bounds in the low L² realization theorem.
There is no assumed PDO estimate or source-to-coordinate comparison. -/
theorem twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_physicalBudget
    {d : ℕ} (hd : 0 < d) (R : ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (A : ℝ)
    (hbound : HasAmplitudeDerivativeBound b (2 * (d + 1)) A)
    (u : EuclideanSpace ℝ (Fin d) → ℂ) (hu : MemLp u 2)
    (huc : ContDiff ℝ (d + 1) u) (hus : HasCompactSupport u) :
    twoPositionL2Operator hd R b hb hs A hbound (hu.toLp u) =ᵐ[volume]
      fullAmplitudeOperator (fun x y ξ ↦ b ξ (pairedPosition x y)) u := by
  apply twoPositionL2Operator_toLp_ae_fullAmplitudeOperator_of_sourceBounds
    hd R b hb hs A hbound u hu huc hus
    (fun _ k ↦ ((2 * d : ℕ) : ℝ) ^ k * A * ‖physicalSourceInclusion d‖ ^ k)
  intro x k hk y ξ
  exact norm_iteratedFDeriv_source_le_physicalBudget
    (fun ξ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hbound ξ x y (by omega)

end JanetCartan.Pseudodifferential
