module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.MinorBounds.Algebra

/-!
# The upper normal-pairing bound from the fixed map budget

The principal-normal lower estimate in `app:ch_waves:thm:leading` needs an
upper bound for the actual Frobenius adjoint. Orthogonal projection contracts
the second derivative, so the fixed `C⁴` map budget supplies this bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.LeadingWave
open ProjectedStressFrame AmbientResponse

/-- The second form is bounded by the actual second jet, without an inverse
metric estimate. Used for the upper normal-pairing bound in
`app:ch_waves:thm:leading`. -/
theorem secondFundamentalForm_norm_le_stressJet {n N : ℕ}
    {F : Euclidean n → Euclidean N} {x : Euclidean n}
    (hF : ContDiffAt ℝ 2 F x) (i j : Fin n) :
    ‖secondFundamentalForm F x i j‖ ≤ ‖stressJet F x‖ := by
  have hp := (normalSpace F x).norm_orthogonalProjectionOnto_apply_le
    (partialDeriv (fun y ↦ partialDeriv F y j) x i)
  change ‖secondFundamentalForm F x i j‖ ≤ _ at hp
  rw [← stressJet_second_apply hF] at hp
  have h₁ := ((stressJet F x).2 (EuclideanSpace.single i 1)).le_opNorm
    (EuclideanSpace.single j 1)
  have h₂ := (stressJet F x).2.le_opNorm (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h₁ h₂
  exact hp.trans (h₁.trans (h₂.trans (le_max_right _ _)))

/-- The stipulated fixed `C⁴` map budget controls the literal adjoint of
`normalMapLinear`, in Frobenius norm. This discharges the operator premise
of `principalNormal_norm_lower_of_pencil_null` (`app:ch_waves:thm:leading`). -/
theorem normalMapLinear_adjoint_norm_le_cNorm_four {n N : ℕ}
    {F : Euclidean n → Euclidean N} {K : Set (Euclidean n)}
    (hK : IsCompact K) (hF : ∀ x ∈ K, ContDiffAt ℝ ∞ F x)
    {x : Euclidean n} (hx : x ∈ K) :
    ‖(normalMapLinear F x).adjoint.toContinuousLinearMap‖ ≤
      2 * n * cNorm K 4 F := by
  apply ((normalMapLinear F x).adjoint.toContinuousLinearMap).opNorm_le_bound
    (mul_nonneg (by positivity) (cNorm_nonneg K 4 F))
  intro w
  change ‖(normalMapLinear F x).adjoint w‖ ≤ _
  rw [adjoint_normalMapLinear]
  calc
    ‖normalPairing F (fun _ ↦ w) x‖ ≤ n * (‖w‖ * (2 * cNorm K 4 F)) := by
      apply ActualCarriers.frobenius_le_card_mul_entry_bound _
        (mul_nonneg (norm_nonneg w) (mul_nonneg (by norm_num) (cNorm_nonneg K 4 F)))
      intro i j
      exact (norm_inner_le_norm (𝕜 := ℝ) w (secondFundamentalForm F x i j)).trans
        (mul_le_mul_of_nonneg_left
          ((secondFundamentalForm_norm_le_stressJet
            ((hF x hx).of_le (by simp)) i j).trans
            (norm_stressJet_le_cNorm_four hK hF hx)) (norm_nonneg w))
    _ = (2 * n * cNorm K 4 F) * ‖w‖ := by ring

end JanetCartan.LeadingWave
