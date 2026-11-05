module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs.Compact
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.GapStability

import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity gaps on the protected angular set

The compactness argument in Step 2 of `app:ch_seed:prop:seed-actual-menu`.
The frozen pencil supplies the gaps without any actual-field assumptions.
The current pencil inherits them from explicit adjugate, determinant-value,
and actual determinant-differential comparison bounds. The resulting adjugate
and rank bounds do not assert the manuscript's numbered singular-value bound.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

open SignedPairs

private theorem signedRegularity_contDiff_cubeDeterminant {n : ℕ} :
    ContDiff ℝ ∞ (cubeDeterminant (n := n)) := by
  have hc (i : Fin n) : ContDiff ℝ ∞ (fun x : Euclidean n ↦ x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  change ContDiff ℝ ∞ (fun x : Euclidean n ↦ cubeDeterminant x)
  simp_rw [cubeDeterminant_eq]
  exact (contDiff_prod (fun i _ ↦ hc i)).sub
    ((contDiff_const.mul (ContDiff.sum (fun i _ ↦ hc i))).mul
      (ContDiff.sum (fun i _ ↦ contDiff_prod (fun j _ ↦ hc j))))

/-- The frozen adjugate has a uniform positive Frobenius norm on the protected
angular set (`app:ch_seed:prop:seed-actual-menu`, Step 2). This supplies the
adjugate tolerance in `exists_angular_pencil_regularity`. -/
theorem exists_frozen_angular_adjugate_gap {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ a : ℝ, 0 < a ∧ ∀ v ∈ angularSet n γ, a ≤ ‖(cubePencil v).adjugate‖ := by
  apply (isCompact_angularSet n γ).exists_forall_le'
    ((cubePencilContinuousLinearMap n).continuous.matrix_adjugate.norm.continuousOn)
  intro v hv
  apply norm_pos_iff.mpr
  intro hz
  have hr := (angularSet_regular hn hγ hv).1
  have hz' := (adjugate_eq_zero_iff_rank_add_two_le (by omega) (cubePencil v)).mp hz
  omega

/-- On the protected angular set, all scalar functions sufficiently close to
the frozen determinant in value and actual differential retain a uniform
positive differential norm at their zeros
(`app:ch_seed:prop:seed-actual-menu`, Step 2). In particular, zeros of the
perturbation need not be frozen zeros. -/
theorem exists_angular_determinant_perturbation_gap {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ d : ℝ, 0 < d ∧ ∀ p : Euclidean n → ℝ,
      (∀ v ∈ angularSet n γ, ‖p v - cubeDeterminant v‖ ≤ d) →
      (∀ v ∈ angularSet n γ,
        ‖fderiv ℝ p v - fderiv ℝ cubeDeterminant v‖ ≤ d) →
      ∀ v ∈ angularSet n γ, p v = 0 → d ≤ ‖fderiv ℝ p v‖ := by
  exact exists_fderiv_zero_perturbation_gap (isCompact_angularSet n γ)
    signedRegularity_contDiff_cubeDeterminant.continuous.continuousOn
    (signedRegularity_contDiff_cubeDeterminant.continuous_fderiv (by simp)).continuousOn
    (fun _ hv ↦ (angularSet_regular hn hγ hv).2)

/-- The uniform current-pencil deduction in Step 2 of
`app:ch_seed:prop:seed-actual-menu`: explicit adjugate and `C¹` determinant
errors preserve an adjugate gap, rank at least `n-1`, and a differential gap
at every actual determinant zero. The tolerances depend only on `n` and `γ`,
and may therefore be applied uniformly to an arbitrary family of frames.
The frame producer must prove the three comparison inputs. -/
theorem exists_angular_pencil_regularity {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℝ, 0 < d ∧
      (∀ v ∈ angularSet n γ, 2 * a ≤ ‖(cubePencil v).adjugate‖) ∧
      ∀ Q : Fin n → MetricTensor n,
        (∀ v ∈ angularSet n γ,
          ‖(pencil Q v).adjugate - (cubePencil v).adjugate‖ ≤ a) →
        (∀ v ∈ angularSet n γ, ‖determinant Q v - cubeDeterminant v‖ ≤ d) →
        (∀ v ∈ angularSet n γ,
          ‖fderiv ℝ (determinant Q) v - fderiv ℝ cubeDeterminant v‖ ≤ d) →
        ∀ v ∈ angularSet n γ,
          a ≤ ‖(pencil Q v).adjugate‖ ∧ n - 1 ≤ (pencil Q v).rank ∧
          (determinant Q v = 0 → d ≤ ‖fderiv ℝ (determinant Q) v‖) := by
  obtain ⟨b, hb, hgap⟩ := exists_frozen_angular_adjugate_gap hn hγ
  obtain ⟨d, hd, hdiff⟩ := exists_angular_determinant_perturbation_gap hn hγ
  refine ⟨b / 2, by linarith, d, hd, ?_, ?_⟩
  · intro v hv
    linarith [hgap v hv]
  · intro Q hA hp hD v hv
    have hnorm : b / 2 ≤ ‖(pencil Q v).adjugate‖ := by
      have ht : ‖(cubePencil v).adjugate‖ ≤
          ‖(pencil Q v).adjugate‖ + b / 2 := by
        calc
          _ ≤ ‖(pencil Q v).adjugate‖ +
              ‖(cubePencil v).adjugate - (pencil Q v).adjugate‖ := norm_le_insert' _ _
          _ ≤ _ := add_le_add (le_refl _) (by simpa [norm_sub_rev] using hA v hv)
      have := hgap v hv
      linarith
    refine ⟨hnorm, ?_, hdiff (determinant Q) hp hD v hv⟩
    have hne : (pencil Q v).adjugate ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hnorm)
    have := (adjugate_eq_zero_iff_rank_add_two_le (by omega) (pencil Q v)).not.mp hne
    omega

end JanetCartan.ActualCarriers
