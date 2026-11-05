module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Assembly
public import JanetCartan.Analysis.Operator.CoerciveInverse
import Mathlib.Tactic.Abel

/-!
# Transfer from the source inverse using strong raw-adjoint continuity

For `app:ch_background:prop:bg-inverse` and current positive-density admission,
normal operator-norm continuity plus residual continuity control the inverse.
The raw right inverse additionally needs the adjoint difference on the ONE
fixed reference inverse vector.  No operator-norm continuity of the moving
Fourier-integral row is assumed or inferred.

Actual producers: strong source/current coercivity gives the two gaps; task19
gives normal perturbation; task24 gives residual continuity; task33 gives the
strong raw-adjoint term.  The algebra below does not discharge that last
analytic producer. At fixed σ, its result combines with the checked high raw
bounds and Sobolev interpolation before the density synthesis.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace JanetCartan.PhysicalNormalInverse.ContinuityTransfer
open ContinuumRow CoerciveInverse

variable {n : ℕ} {ι : Type*} [Fintype ι]
    (A Aref : AugmentedInput n ι →L[ℝ] OutputL2 n)
    {γ γref : ℝ} (hγ : 0 < γ) (hγref : 0 < γref)
    (hgap : ∀ w, γ * ‖w‖ ^ 2 ≤ ‖A.adjoint w‖ ^ 2)
    (hgapref : ∀ w, γref * ‖w‖ ^ 2 ≤ ‖Aref.adjoint w‖ ^ 2)

include hγ hγref hgap hgapref

/-- Subtract the actual two inverse equations. Only the normal operators, not
the moving rows themselves, occur in the perturbation factor. -/
theorem normal_inverse_residual_identity (e eref : OutputL2 n) :
    (normalOperator A).inverse e - (normalOperator Aref).inverse eref =
      (normalOperator A).inverse (e - eref -
        (normalOperator A - normalOperator Aref) ((normalOperator Aref).inverse eref)) := by
  have href := CoerciveInverse.apply_inverse (normalOperator Aref) hγref
    (normalOperator_gap Aref hgapref) eref
  have hleft := CoerciveInverse.inverse_apply (normalOperator A) hγ
    (normalOperator_gap A hgap) ((normalOperator Aref).inverse eref)
  calc
    _ = (normalOperator A).inverse e -
        (normalOperator A).inverse (normalOperator A ((normalOperator Aref).inverse eref)) := by
      rw [hleft]
    _ = (normalOperator A).inverse
        (e - normalOperator A ((normalOperator Aref).inverse eref)) := by
      rw [map_sub]
    _ = _ := by
      congr 1
      rw [sub_apply, href]
      abel

/-- The inverse-vector difference is controlled by residual and NORMAL
operator differences, with the current gap constant. -/
theorem normal_inverse_apply_sub_le (e eref : OutputL2 n) :
    ‖(normalOperator A).inverse e - (normalOperator Aref).inverse eref‖ ≤
      γ⁻¹ * (‖e - eref‖ + ‖normalOperator A - normalOperator Aref‖ *
        ‖(normalOperator Aref).inverse eref‖) := by
  rw [normal_inverse_residual_identity A Aref hγ hγref hgap hgapref e eref]
  apply (norm_inverse_apply_le (normalOperator A) hγ (normalOperator_gap A hgap) _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hγ.le)
  exact (norm_sub_le _ _).trans (add_le_add le_rfl
    ((normalOperator A - normalOperator Aref).le_opNorm _))

/-- Raw right-inverse continuity requires only the adjoint difference on the
fixed reference vector. This is the exact algebraic consumer of task33's
strong-adjoint estimate; it never requests L² row operator-norm continuity. -/
theorem raw_rightInverse_sub_le (e eref : OutputL2 n) :
    ‖CoerciveInverse.rightInverse A e - CoerciveInverse.rightInverse Aref eref‖ ≤
      ‖A.adjoint‖ * (γ⁻¹ * (‖e - eref‖ +
        ‖normalOperator A - normalOperator Aref‖ * ‖(normalOperator Aref).inverse eref‖)) +
      ‖(A.adjoint - Aref.adjoint) ((normalOperator Aref).inverse eref)‖ := by
  have hsplit : CoerciveInverse.rightInverse A e - CoerciveInverse.rightInverse Aref eref =
      A.adjoint ((normalOperator A).inverse e - (normalOperator Aref).inverse eref) +
        (A.adjoint - Aref.adjoint) ((normalOperator Aref).inverse eref) := by
    simp only [CoerciveInverse.rightInverse, ContinuousLinearMap.comp_apply,
      map_sub, sub_apply]
    abel
  rw [hsplit]
  apply (norm_add_le _ _).trans
  exact add_le_add ((A.adjoint.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (normal_inverse_apply_sub_le A Aref hγ hγref hgap hgapref e eref) (norm_nonneg _))) le_rfl

end JanetCartan.PhysicalNormalInverse.ContinuityTransfer
