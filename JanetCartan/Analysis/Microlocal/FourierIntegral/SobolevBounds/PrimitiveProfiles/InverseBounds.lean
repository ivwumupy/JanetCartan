module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.PrimitiveProfiles.NormalizedSeminorms
public import JanetCartan.Analysis.Matrix.InverseBounds

/-!
# Buffered normalized matrix inverse bounds

The inverse primitive in Step 3 of `app:ch_regular_base:thm:actual-calculus`
must be estimated from the actual matrix and its inverse gap. High derivatives
of the inverse are conclusions here. The mixed phase matrix will be substituted
for `f`; comparison of its seminorm with the phase's shifted seminorm is separate.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
open Filter
namespace JanetCartan.FourierIntegral.PrimitiveProfiles

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Buffered form of the one-high matrix inverse bound used for the actual
mixed inverse in Step 3, `app:ch_regular_base:thm:actual-calculus`.
Only the zeroth matrix seminorm and inverse gap enter the constant; global
smoothness and high inverse jets are not hypotheses. -/
theorem exists_cNorm_inverse_tame_on (z : E) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set E} (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : E → Matrix ι ι ℝ, ContDiffOn ℝ ∞ f U →
      cNorm (Metric.closedBall z ρ) 0 f ≤ M →
      (∀ p ∈ Metric.closedBall z ρ, IsUnit (f p)) →
      (∀ p ∈ Metric.closedBall z ρ, ‖(f p)⁻¹‖ ≤ B) →
      cNorm (Metric.closedBall z ρ) k (fun p ↦ (f p)⁻¹) ≤
        C * (1 + cNorm (Metric.closedBall z ρ) k f) := by
  obtain ⟨C, hC, hb⟩ := exists_cNorm_matrix_inv_le_tame_closedBall
    (ι := ι) z hρ (le_refl k) hM B
  refine ⟨C, hC, ?_⟩
  intro f hf hlow hu hgap
  obtain ⟨g, hg, _, _, he⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall z hρ hU hball hf
  have hc (j : ℕ) : cNorm (Metric.closedBall z ρ) j g =
      cNorm (Metric.closedBall z ρ) j f := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Set.image_congr
    intro p hp
    rw [((he p hp).iteratedFDeriv (𝕜 := ℝ) i).self_of_nhds]
  have hi : cNorm (Metric.closedBall z ρ) k (fun p ↦ (g p)⁻¹) =
      cNorm (Metric.closedBall z ρ) k (fun p ↦ (f p)⁻¹) := by
    unfold cNorm
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Set.image_congr
    intro p hp
    have hei : (fun p ↦ (g p)⁻¹) =ᶠ[nhds p] (fun p ↦ (f p)⁻¹) :=
      (he p hp).fun_comp (fun A ↦ A⁻¹)
    rw [(hei.iteratedFDeriv (𝕜 := ℝ) i).self_of_nhds]
  have h := hb g hg (by rwa [hc])
    (fun p hp ↦ by rw [(he p hp).self_of_nhds]; exact hu p hp)
    (fun p hp ↦ by rw [(he p hp).self_of_nhds]; exact hgap p hp)
  rwa [hi, hc] at h

variable {X Ξ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Ξ]

/-- Normalized high inverse seminorms follow from the actual inverse gap and
the original matrix seminorm, with zero derivative loss. The constant precedes
the field and all high seminorms. This is the inverse part of the primitive
endpoint comparison in `app:ch_regular_base:eq:fio-input`. -/
theorem exists_normalizedSeminorm_inverse_tame (z : X × Ξ) {ρ : ℝ} (hρ : 0 < ρ)
    {U : Set (X × Ξ)} (hU : IsOpen U) (hball : Metric.closedBall z ρ ⊆ U)
    (k : ℕ) {M : ℝ} (hM : 0 ≤ M) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : X × Ξ → Matrix ι ι ℝ,
      (∀ R : ℝ, 1 ≤ R → ContDiffOn ℝ ∞ (normalizedField R f) U) →
      BoundedNormalizedSeminorm (Metric.closedBall z ρ) k f →
      normalizedSeminorm (Metric.closedBall z ρ) 0 f ≤ M →
      (∀ R : ℝ, 1 ≤ R → ∀ p ∈ Metric.closedBall z ρ,
        IsUnit (normalizedField R f p)) →
      (∀ R : ℝ, 1 ≤ R → ∀ p ∈ Metric.closedBall z ρ,
        ‖(normalizedField R f p)⁻¹‖ ≤ B) →
      BoundedNormalizedSeminorm (Metric.closedBall z ρ) k (fun p ↦ (f p)⁻¹) ∧
      normalizedSeminorm (Metric.closedBall z ρ) k (fun p ↦ (f p)⁻¹) ≤
        C * (1 + normalizedSeminorm (Metric.closedBall z ρ) k f) := by
  obtain ⟨C, hC, hi⟩ := exists_cNorm_inverse_tame_on (ι := ι) z hρ hU hball k hM B
  refine ⟨C, hC, ?_⟩
  intro f hf hb hlow hu hgap
  have bound (R : {R : ℝ // 1 ≤ R}) :
      cNorm (Metric.closedBall z ρ) k (normalizedField R (fun p ↦ (f p)⁻¹)) ≤
        C * (1 + normalizedSeminorm (Metric.closedBall z ρ) k f) :=
    (hi (normalizedField R f) (hf R R.2)
      ((cNorm_normalizedField_le (hb.mono (Nat.zero_le k)) R.2).trans hlow)
      (hu R R.2) (hgap R R.2)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (cNorm_normalizedField_le hb R.2)) hC.le)
  refine ⟨⟨C * (1 + normalizedSeminorm (Metric.closedBall z ρ) k f), ?_⟩, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact bound R
  · apply Real.sSup_le _ (mul_nonneg hC.le
      (add_nonneg zero_le_one (normalizedSeminorm_nonneg (Metric.closedBall z ρ) k f)))
    rintro _ ⟨R, rfl⟩
    exact bound R

end JanetCartan.FourierIntegral.PrimitiveProfiles
