module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation.Factorization

/-!
# Uniform C¹ bounds for the actual image-channel commutator

The constants below are selected from dimension and primitive coefficient and
cutoff budgets before the varying coefficients or translation step. The producer
of coefficient jets is `ContinuumRow.ImageGeometry` / `ContinuumRow.HistoryImage`;
the parent must instantiate those jets and the fixed cutoff budgets for its SAME
row. The consumer is `periodicCoerciveInverseH1` after the parent adds the existing
carrier/exterior estimate from `Translation.Assembly`.
-/

@[expose] public noncomputable section

namespace JanetCartan.ContinuumCommutator.ImageChannelTranslation

open ContinuumRow

variable {n : ℕ}

private theorem norm_difference_comp_constant_le
    (A B : OutputL2 n →L[ℝ] OutputL2 n) (i : Fin n) (h : ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hA : ‖periodicConjugationDifference A i h‖ ≤ K)
    (hB : ‖B‖ ≤ 1) (hz : periodicConjugationDifference B i h = 0) :
    ‖periodicConjugationDifference (A ∘L B) i h‖ ≤ K := by
  have hb := norm_conjugationDifference_comp_le A B i h
  rw [hz, norm_zero, mul_zero, add_zero] at hb
  exact hb.trans ((mul_le_mul hA hB (norm_nonneg _) hK).trans_eq (mul_one _))

/-- Uniform bound for the finite principal-plus-connection factor `P J`,
deduced from the actual coefficient derivatives and Fourier factors
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_conjugationDifference_reduced_bessel_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, Differentiable ℝ (periodicLift (c j)))
    (i : Fin n) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ j x, ‖fderiv ℝ (periodicLift (c j)) x (EuclideanSpace.single i 1)‖ ≤ K)
    (h : ℝ) :
    ‖periodicConjugationDifference (reducedWeakOperator c ∘L periodicBesselLift) i h‖ ≤
      ((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * K := by
  rw [reduced_bessel_finite_sum, periodicConjugationDifference_add]
  simp only [periodicConjugationDifference_sum]
  calc
    _ ≤ (∑ j : Fin n, ∑ r : Fin n, ∑ s : Fin n, K) +
        ∑ r : Fin n, ∑ s : Fin n, K := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro j _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro r _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro s _
        exact norm_difference_comp_constant_le _ _ i h hK0
          (norm_conjugationDifference_coefficientMultiplier_le _ (hc _) r s i
            hK0 (hK _) h) (norm_besselDerivative_le j)
          (conjugationDifference_besselDerivative j i h)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro r _
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro s _
        exact norm_difference_comp_constant_le _ _ i h hK0
          (norm_conjugationDifference_coefficientMultiplier_le _ (hc _) r s i
            hK0 (hK _) h) norm_periodicBesselInverse_le
          (conjugationDifference_besselInverse i h)
    _ = _ := by simp; ring

private theorem norm_reduced_bessel_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ j x, |c j x| ≤ C) :
    ‖reducedWeakOperator c ∘L periodicBesselLift‖ ≤
      ((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * C := by
  calc
    _ ≤ ‖reducedWeakOperator c‖ * ‖periodicBesselLift (n := n)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ reducedCoefficientBound c * 1 := mul_le_mul
      (reducedWeakOperator_norm_le c) norm_periodicBesselLift_le (norm_nonneg _)
      (reducedCoefficientBound_nonneg c)
    _ ≤ (n : ℝ) ^ 3 * C + (n : ℝ) ^ 2 * C := by
      rw [mul_one]
      exact reducedCoefficientBound_le c hC0 hC0 (fun j r s ↦ hC _) (fun r s ↦ hC _)
    _ = _ := by ring

/-- The uniform image-channel difference estimate, with both literal masks.
Only primitive value and first-derivative budgets enter the constant
(`app:ch_background:eq:bg-commutator`). -/
theorem norm_conjugationDifference_imageChannel_le
    {C K M S Km Ks : ℝ} (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hM0 : 0 ≤ M) (hS0 : 0 ≤ S) (hKm0 : 0 ≤ Km) (hKs0 : 0 ≤ Ks)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, Differentiable ℝ (periodicLift (c j)))
    (hC : ∀ j x, |c j x| ≤ C)
    (χmeas χsrc : C(Torus n, ℝ))
    (hm : Differentiable ℝ (periodicLift χmeas))
    (hs : Differentiable ℝ (periodicLift χsrc))
    (hM : ∀ x, ‖χmeas x‖ ≤ M) (hS : ∀ x, ‖χsrc x‖ ≤ S)
    (i : Fin n)
    (hK : ∀ j x, ‖fderiv ℝ (periodicLift (c j)) x (EuclideanSpace.single i 1)‖ ≤ K)
    (hKm : ∀ x, ‖fderiv ℝ (periodicLift χmeas) x (EuclideanSpace.single i 1)‖ ≤ Km)
    (hKs : ∀ x, ‖fderiv ℝ (periodicLift χsrc) x (EuclideanSpace.single i 1)‖ ≤ Ks)
    (h : ℝ) :
    let L := (n : ℝ) ^ 3 + (n : ℝ) ^ 2
    ‖periodicConjugationDifference (imageChannel c χmeas χsrc) i h‖ ≤
      Km * (L * C * S) + M * (L * K * S + L * C * Ks) := by
  dsimp only
  have hmn : ‖cutoffMultiplier χmeas‖ ≤ M :=
    (cutoffMultiplier_norm_le _).trans ((ContinuousMap.norm_le _ hM0).mpr hM)
  have hsn : ‖cutoffMultiplier χsrc‖ ≤ S :=
    (cutoffMultiplier_norm_le _).trans ((ContinuousMap.norm_le _ hS0).mpr hS)
  have hmd := norm_periodicConjugationDifference_cutoffMultiplier_le χmeas hm i hKm0 hKm h
  have hsd := norm_periodicConjugationDifference_cutoffMultiplier_le χsrc hs i hKs0 hKs h
  have hpn := norm_reduced_bessel_le c hC0 hC
  have hpd := norm_conjugationDifference_reduced_bessel_le c hc i hK0 hK h
  have hpsn : ‖(reducedWeakOperator c ∘L periodicBesselLift) ∘L cutoffMultiplier χsrc‖ ≤
      (((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * C) * S :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hpn hsn (norm_nonneg _) (by positivity))
  have hpsd : ‖periodicConjugationDifference
      ((reducedWeakOperator c ∘L periodicBesselLift) ∘L cutoffMultiplier χsrc) i h‖ ≤
      ((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * K * S +
        ((n : ℝ) ^ 3 + (n : ℝ) ^ 2) * C * Ks := by
    apply (norm_conjugationDifference_comp_le _ _ i h).trans
    exact add_le_add (mul_le_mul hpd hsn (norm_nonneg _) (by positivity))
      (mul_le_mul hpn hsd (norm_nonneg _) (by positivity))
  have heq : imageChannel c χmeas χsrc = cutoffMultiplier χmeas ∘L
      ((reducedWeakOperator c ∘L periodicBesselLift) ∘L cutoffMultiplier χsrc) := by
    simp only [imageChannel, ContinuousLinearMap.comp_assoc]
  rw [heq]
  apply (norm_conjugationDifference_comp_le _ _ i h).trans
  exact add_le_add (mul_le_mul hmd hpsn (norm_nonneg _) hKm0)
    (mul_le_mul hmn hpsd (norm_nonneg _) hM0)

end JanetCartan.ContinuumCommutator.ImageChannelTranslation
