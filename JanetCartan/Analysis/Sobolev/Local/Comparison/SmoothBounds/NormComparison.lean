module

public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.SymmetricJets

/-!
# Comparison of Cartesian norms and sums of L² operator norms

The constants in `app:not:fourier` and `app:ch_regular_base:lem:ball-extension`
depend only on the domain dimension and derivative order.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace JanetCartan.LocalSobolev

/-- The squared real L² seminorm is its norm-square integral (`app:not:fourier`). -/
theorem eLpNorm_toReal_sq_eq_integral_norm_sq {X G : Type*} [MeasurableSpace X] [NormedAddCommGroup G]
    {μ : Measure X} {f : X → G} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (integral_nonneg fun x ↦ sq_nonneg _) _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun x ↦ sq_nonneg _)]
  norm_num

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cartesian evaluations are bounded by the sum of L² operator norms, with
an input-independent constant (`app:not:fourier`). This direction needs no symmetry. -/
theorem cartesianJetNorm_le_mul_jetL2Norm
    (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 (volume.restrict U)) :
    cartesianJetNorm U m J ≤
      Real.sqrt (BallExtension.cartesianEnergyComparisonConstant n m) * jetL2Norm U m J := by
  have hterm (α) (hα : α ∈ sobolevMultiindices n m) :
      (∫ x in U, ‖cartesianJetDerivative J (fun i ↦ α (some i)) x‖ ^ 2) ≤
        jetL2Norm U m J ^ 2 := by
    have ho : ∑ i, α (some i) ≤ m := by
      have := mem_sobolevMultiindices.mp hα
      omega
    have hd := memLp_cartesianJetDerivative (fun i ↦ α (some i)) (hJ _ ho)
    calc
      _ ≤ ∫ x in U, ‖J (∑ i, α (some i)) x‖ ^ 2 := by
        apply integral_mono (hd.integrable_norm_pow (by decide))
          ((hJ _ ho).integrable_norm_pow (by decide))
        intro x
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_cartesianJetDerivative_le J _ x) 2
      _ = (eLpNorm (J (∑ i, α (some i))) 2 (volume.restrict U)).toReal ^ 2 :=
        (eLpNorm_toReal_sq_eq_integral_norm_sq (hJ _ ho)).symm
      _ ≤ _ := by
        apply pow_le_pow_left₀ ENNReal.toReal_nonneg
        exact Finset.single_le_sum
          (f := fun j ↦ (eLpNorm (J j) 2 (volume.restrict U)).toReal)
          (s := Finset.range (m + 1)) (fun _ _ ↦ ENNReal.toReal_nonneg)
          (Finset.mem_range.mpr (by omega))
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (jetL2Norm_nonneg U m J))).mp
  rw [Real.sq_sqrt (cartesianJetEnergy_nonneg U m J), mul_pow,
    Real.sq_sqrt (BallExtension.cartesianEnergyComparisonConstant_pos n m).le]
  calc
    _ ≤ ∑ _α ∈ sobolevMultiindices n m, jetL2Norm U m J ^ 2 :=
      Finset.sum_le_sum hterm
    _ = ((sobolevMultiindices n m).card : ℝ) * jetL2Norm U m J ^ 2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by simp [BallExtension.cartesianEnergyComparisonConstant]) (sq_nonneg _)

end JanetCartan.LocalSobolev

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- For symmetric jets, the sum of L² operator norms is bounded by the Cartesian
norm (`app:not:fourier`). The symmetry premise is discharged for smooth jets below. -/
theorem jetL2Norm_le_mul_cartesianJetNorm_of_symmetric
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U) (m : ℕ)
    (J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] F)
    (hJ : ∀ j ≤ m, MemLp (J j) 2 (volume.restrict U))
    (hsym : ∀ x ∈ U, ∀ j ≤ m, ∀ v : Fin j → EuclideanSpace ℝ (Fin n),
      ∀ σ : Equiv.Perm (Fin j), J j x (v ∘ σ) = J j x v) :
    jetL2Norm U m J ≤
      Real.sqrt ((m + 1) * BallExtension.frechetEnergyComparisonConstant n m) *
        cartesianJetNorm U m J := by
  have hsq : (∑ j ∈ Finset.range (m + 1),
      (eLpNorm (J j) 2 (volume.restrict U)).toReal ^ 2) ≤
        BallExtension.frechetEnergyComparisonConstant n m * cartesianJetEnergy U m J := by
    have hi (j) (hj : j ∈ Finset.range (m + 1)) :
        IntegrableOn (fun x ↦ ‖J j x‖ ^ 2) U :=
      (hJ j (by simpa using hj)).integrable_norm_pow (by decide)
    have hc (α) (hα : α ∈ sobolevMultiindices n m) :
        IntegrableOn (fun x ↦ ‖cartesianJetDerivative J (fun i ↦ α (some i)) x‖ ^ 2) U := by
      have ho : ∑ i, α (some i) ≤ m := by
        have := mem_sobolevMultiindices.mp hα
        omega
      exact (memLp_cartesianJetDerivative _ (hJ _ ho)).integrable_norm_pow (by decide)
    calc
      _ = ∑ j ∈ Finset.range (m + 1), ∫ x in U, ‖J j x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact eLpNorm_toReal_sq_eq_integral_norm_sq (hJ j (by simpa using hj))
      _ ≤ _ := by
        unfold cartesianJetEnergy
        rw [← integral_finsetSum _ hi, ← integral_finsetSum _ hc, ← integral_const_mul]
        apply setIntegral_mono_on (integrable_finsetSum _ hi)
          ((integrable_finsetSum _ hc).const_mul _) hU
        intro x hx
        exact sum_sq_norm_symmetricJet_le m (fun j ↦ J j x) (hsym x hx)
  apply (sq_le_sq₀ (jetL2Norm_nonneg U m J)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by positivity)
    (BallExtension.frechetEnergyComparisonConstant_pos n m).le),
    Real.sq_sqrt (cartesianJetEnergy_nonneg U m J)]
  calc
    _ ≤ (m + 1) * ∑ j ∈ Finset.range (m + 1),
        (eLpNorm (J j) 2 (volume.restrict U)).toReal ^ 2 := by
      simpa only [jetL2Norm, Finset.card_range, Nat.cast_add, Nat.cast_one] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.range (m + 1))
          (f := fun j ↦ (eLpNorm (J j) 2 (volume.restrict U)).toReal))
    _ ≤ (m + 1) * (BallExtension.frechetEnergyComparisonConstant n m *
        cartesianJetEnergy U m J) := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

/-- On an open domain, smooth jets satisfy the reverse norm comparison with no
assumed estimate (`app:ch_regular_base:lem:ball-extension`). -/
theorem jetL2Norm_iteratedFDerivWithin_le_mul_cartesianJetNorm
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (m : ℕ)
    {f : EuclideanSpace ℝ (Fin n) → F} (hf : ContDiffOn ℝ ∞ f U)
    (hJ : ∀ j ≤ m, MemLp (iteratedFDerivWithin ℝ j f U) 2 (volume.restrict U)) :
    jetL2Norm U m (fun j ↦ iteratedFDerivWithin ℝ j f U) ≤
      Real.sqrt ((m + 1) * BallExtension.frechetEnergyComparisonConstant n m) *
        cartesianJetNorm U m (fun j ↦ iteratedFDerivWithin ℝ j f U) :=
  jetL2Norm_le_mul_cartesianJetNorm_of_symmetric hU.measurableSet m _ hJ
    (fun _ hx j _ v σ ↦
      BallExtension.iteratedFDerivWithin_comp_perm_of_contDiffOn hU hf hx j v σ)

end JanetCartan.LocalSobolev
