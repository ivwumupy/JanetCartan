module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.Pencil
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Adjugate

/-!
# Quantitative fixed minors

The matrix estimates used by the finite patches in Step 2 of
`app:ch_seed:prop:seed-actual-menu` and the finite low class in
`app:ch_regular_base:thm:sector`. All matrix norms here are Frobenius norms.
The cofactor indices agree with `NullTransport.rightNullvector` and
`NullTransport.leftNullvector`: entry `(r,c)` deletes row `c` and column `r`.
No singular-value estimate is asserted.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

/-- The ordered minor associated to adjugate entry `(r,c)`, used in
`app:ch_seed:prop:seed-actual-menu`, Step 2. Increasing `succAbove` maps
preserve the original real coordinate order. -/
def cofactorMinor {m : ℕ} (A : MetricTensor (m + 1)) (r c : Fin (m + 1)) :
    MetricTensor m := A.submatrix c.succAbove r.succAbove

/-- The exact cofactor sign for the selected nullvector coordinates
(`app:ch_seed:prop:seed-actual-menu`, Step 2). -/
theorem adjugate_eq_signed_cofactorMinor {m : ℕ} (A : MetricTensor (m + 1))
    (r c : Fin (m + 1)) :
    A.adjugate r c = (-1 : ℝ) ^ (c.val + r.val) * (cofactorMinor A r c).det :=
  Matrix.adjugate_fin_succ_eq_det_submatrix A r c

/-- Absolute determinants equal absolute cofactors, with the transpose of
indices required by the nullvector convention (`app:ch_waves:thm:leading`). -/
theorem abs_det_cofactorMinor {m : ℕ} (A : MetricTensor (m + 1))
    (r c : Fin (m + 1)) : |(cofactorMinor A r c).det| = |A.adjugate r c| := by
  rw [adjugate_eq_signed_cofactorMinor, abs_mul, abs_pow]
  simp

/-- An entry is bounded by the Frobenius norm. Used to control the inverse
minor in `app:ch_regular_base:thm:sector`. -/
theorem abs_entry_le_frobenius {m : ℕ} (A : MetricTensor m) (i j : Fin m) :
    |A i j| ≤ ‖A‖ := by
  exact (PiLp.norm_apply_le (WithLp.toLp 2 (A i)) j).trans
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (A i))) i)

/-- Entry bounds give a dimension-dependent Frobenius bound, used in the
cofactor selection and inverse estimate of `app:ch_regular_base:thm:sector`. -/
theorem frobenius_le_card_mul_entry_bound {m : ℕ} (A : MetricTensor m)
    {C : ℝ} (hC : 0 ≤ C) (hA : ∀ i j, |A i j| ≤ C) : ‖A‖ ≤ m * C := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  simp only [Real.norm_eq_abs, Real.rpow_two]
  calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, C ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
        pow_le_pow_left₀ (abs_nonneg _) (hA i j) 2
    _ = (m * C) ^ 2 := by simp; ring

/-- A positive Frobenius adjugate gap forces a cofactor at least `a/(m+1)`.
This selects the concrete minor for Step 2 of
`app:ch_seed:prop:seed-actual-menu`; it is not a singular-value claim. -/
theorem exists_large_cofactor {m : ℕ} (A : MetricTensor (m + 1))
    {a : ℝ} (hgap : a ≤ ‖A.adjugate‖) :
    ∃ r c : Fin (m + 1), a / (m + 1) ≤ |A.adjugate r c| := by
  obtain ⟨⟨r, c⟩, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1)))
    (fun p ↦ |A.adjugate p.1 p.2|) Finset.univ_nonempty
  refine ⟨r, c, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have h := frobenius_le_card_mul_entry_bound A.adjugate (abs_nonneg (A.adjugate r c))
    (fun i j ↦ hmax (i, j) (Finset.mem_univ _))
  push_cast at h
  linarith

private theorem abs_det_le_entry_bound {m : ℕ} (A : MetricTensor m)
    {C : ℝ} (hA : ∀ i j, |A i j| ≤ C) :
    |A.det| ≤ m.factorial * C ^ m := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin m), |(↑(↑(Equiv.Perm.sign σ) : ℤ) : ℝ) *
        ∏ i, A (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm (Fin m), ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      simp [abs_mul, ← Int.cast_abs, Finset.abs_prod]
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), ∏ _i : Fin m, C := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ hA (σ i) i)
    _ = _ := by simp [Fintype.card_perm]

/-- An explicit polynomial bound for the adjugate from entry bounds. This
bounds the numerator of the selected minor inverse in
`app:ch_regular_base:thm:sector`. The slightly coarse exponent also covers
zero-dimensional minors. -/
theorem frobenius_adjugate_le_entry_bound {m : ℕ} (A : MetricTensor m)
    {M : ℝ} (hA : ∀ i j, |A i j| ≤ M) :
    ‖A.adjugate‖ ≤ m * (m.factorial * (max 1 M) ^ m) := by
  apply frobenius_le_card_mul_entry_bound _ (by positivity)
  intro i j
  rw [Matrix.adjugate_apply]
  apply abs_det_le_entry_bound
  intro k l
  by_cases h : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    by_cases hl : l = i
    · subst l
      simp
    · simp [hl]
  · simpa [Matrix.updateRow_apply, h] using (hA k l).trans (le_max_right 1 M)

/-- A concrete Frobenius inverse bound in terms of dimension, entry upper
bound, and determinant gap (`app:ch_regular_base:thm:sector`). -/
theorem frobenius_inverse_le_det_gap {m : ℕ} (A : MetricTensor m)
    {M δ : ℝ} (hA : ∀ i j, |A i j| ≤ M) (hδ : 0 < δ)
    (hdet : δ ≤ |A.det|) :
    ‖A⁻¹‖ ≤ δ⁻¹ * (m * (m.factorial * (max 1 M) ^ m)) := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, norm_smul, norm_inv, Real.norm_eq_abs]
  exact mul_le_mul (by simpa only [one_div] using one_div_le_one_div_of_le hδ hdet)
    (frobenius_adjugate_le_entry_bound A hA) (norm_nonneg _) (by positivity)

/-- The chosen submatrix has its actual two-sided matrix inverse, uniformly
bounded in the Frobenius norm. This is the concrete invertibility input for
`app:ch_regular_base:thm:sector`, using the current pencil's upper norm bound. -/
theorem cofactorMinor_inverse_bounds {m : ℕ} (A : MetricTensor (m + 1))
    (r c : Fin (m + 1)) {M δ : ℝ} (hM : ‖A‖ ≤ M) (hδ : 0 < δ)
    (hgap : δ ≤ |A.adjugate r c|) :
    (cofactorMinor A r c) * (cofactorMinor A r c)⁻¹ = 1 ∧
    (cofactorMinor A r c)⁻¹ * (cofactorMinor A r c) = 1 ∧
    ‖(cofactorMinor A r c)⁻¹‖ ≤
      δ⁻¹ * (m * (m.factorial * (max 1 M) ^ m)) := by
  have hd : δ ≤ |(cofactorMinor A r c).det| := by rwa [abs_det_cofactorMinor]
  have hu : IsUnit (cofactorMinor A r c).det :=
    isUnit_iff_ne_zero.mpr (abs_pos.mp (hδ.trans_le hd))
  refine ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, ?_⟩
  exact frobenius_inverse_le_det_gap _
    (fun i j ↦ (abs_entry_le_frobenius A _ _).trans hM) hδ hd

end JanetCartan.ActualCarriers
