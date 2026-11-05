module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.ProductBounds.Derivatives.SobolevComparison

/-!
# Integer Sobolev estimates for weighted bilinear products

The analytic assembly for `main:lem:mean-recurrence` in paper.tex. The integrated
Leibniz bound and the jet/Sobolev comparisons retain the joint derivative budget
on the coefficient, lower factor, and higher factor. The constant depends only
on the order and torus dimension, never on the number or size of the weights.
-/

@[expose] public noncomputable section

namespace JanetCartan.CurrentMean

section Normed

variable {d : ℕ} {ι F G H V : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `main:lem:mean-recurrence`: square-sum weighted integer Sobolev size of the
higher-band factor, consumed by the mixed Hermitian product estimates. -/
def weightedPeriodicSobolevNorm (μ : ι → ℝ) (s : ℕ) (E : Torus d → ι → G) : ℝ :=
  Real.sqrt (∑ i, μ i * periodicSobolevNorm s (fun x ↦ E x i) ^ 2)

/-- `main:lem:mean-recurrence`: the coefficient applied to the actual weighted
bilinear field is smooth. This supplies the reverse jet/Sobolev comparison. -/
theorem isSmoothPeriodic_contracted_weightedBilinear
    (B : F →L[ℝ] G →L[ℝ] H) (μ : ι → ℝ)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i))
    (C : Torus d → H →L[ℝ] V) (hC : IsSmoothPeriodic C) :
    IsSmoothPeriodic (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i))) := by
  have h := isSmoothPeriodic_weightedBilinear B D E μ hD hE
  exact ⟨hC.1.clm_apply h.1, hC.2.clm_apply h.2⟩

end Normed

/-- `main:lem:mean-recurrence`: a uniform constant for the integer product
estimate. All finite sums count derivative terms only, not samples. -/
def periodicProductSobolevConstant (d s : ℕ) : ℝ :=
  max 1 (sobolevPeriodicJetConstant d s * periodicJetSobolevConstant d s *
    ∑ j ∈ Finset.range (s + 1),
      Real.sqrt (∑ a ∈ Finset.range (j + 1), (j-a+1 : ℕ) : ℕ) *
        ∑ a ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (j-a+1),
          (j.choose a : ℝ) * ((j-a).choose r : ℝ))

/-- `main:lem:mean-recurrence`: the product constant is at least one. -/
theorem one_le_periodicProductSobolevConstant (d s : ℕ) :
    1 ≤ periodicProductSobolevConstant d s := le_max_left _ _

section Hilbert

variable {d : ℕ} {ι F G H V : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: the actual weighted energy of order-`r` jets is
bounded by the weighted Sobolev size of order `t`, uniformly for `r ≤ t ≤ S`.
Nonnegative weights, including zero weights, require no division. -/
theorem weightedPeriodicL2Norm_periodicJet_le_sobolev_uniform
    (S : ℕ) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (E : Torus d → ι → G) (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i))
    {r t : ℕ} (hrt : r ≤ t) (htS : t ≤ S) :
    weightedPeriodicL2Norm μ (fun x i ↦ periodicJet r (fun x ↦ E x i) x) ≤
      periodicJetSobolevConstant d S * weightedPeriodicSobolevNorm μ t E := by
  have hA : 0 ≤ periodicJetSobolevConstant d S :=
    zero_le_one.trans (one_le_periodicJetSobolevConstant d S)
  unfold weightedPeriodicL2Norm weightedPeriodicSobolevNorm
  calc
    _ ≤ Real.sqrt (∑ i, μ i *
        (periodicJetSobolevConstant d S * periodicSobolevNorm t (fun x ↦ E x i)) ^ 2) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (periodicL2Norm_periodicJet_le_sobolev_uniform S (hE i) hrt htS) 2) (hμ i)
    _ = _ := by
      simp_rw [mul_pow, ← mul_assoc, mul_comm (μ _) (periodicJetSobolevConstant d S ^ 2),
        mul_assoc]
      rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA]

set_option backward.isDefEq.respectTransparency false in
/-- `main:lem:mean-recurrence`: the actual integer Sobolev product estimate.
The three orders remain `a`, `r`, and `s-a-r`; only the lower factor uses a
weighted C norm. The Hermitian specializations discharge the bilinear norm
bound with constant one. This is consumed by `MeanRecurrence.finite_mean_bounds`
after the parent substitutes the coefficient and band profiles. -/
theorem periodicSobolevNorm_contracted_weightedBilinear_le
    (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (D : Torus d → ι → F) (E : Torus d → ι → G)
    (hD : ∀ i, IsSmoothPeriodic (fun x ↦ D x i))
    (hE : ∀ i, IsSmoothPeriodic (fun x ↦ E x i))
    (C : Torus d → H →L[ℝ] V) (hC : IsSmoothPeriodic C) (s : ℕ) :
    periodicSobolevNorm s (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i))) ≤
      periodicProductSobolevConstant d s *
        ∑ a ∈ Finset.range (s + 1), ∑ r ∈ Finset.range (s-a+1),
          cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
            weightedPeriodicSobolevNorm μ (s-a-r) E := by
  let A := periodicJetSobolevConstant d s
  let R := sobolevPeriodicJetConstant d s
  let P (a r : ℕ) := cNorm (fundamentalCell d) a (periodicLift C) *
    weightedPeriodicCNorm μ r D * weightedPeriodicSobolevNorm μ (s-a-r) E
  let T := ∑ a ∈ Finset.range (s + 1), ∑ r ∈ Finset.range (s-a+1), P a r
  let K (j : ℕ) : ℝ :=
    Real.sqrt (∑ a ∈ Finset.range (j + 1), (j-a+1 : ℕ) : ℕ) *
      ∑ a ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (j-a+1),
        (j.choose a : ℝ) * ((j-a).choose r : ℝ)
  have hA : 0 ≤ A := zero_le_one.trans (one_le_periodicJetSobolevConstant d s)
  have hR : 0 ≤ R := zero_le_one.trans (one_le_sobolevPeriodicJetConstant d s)
  have hP (a r : ℕ) : 0 ≤ P a r :=
    mul_nonneg (mul_nonneg (cNorm_nonneg _ _ _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun r _ ↦ hP a r))
  have hterm (j : ℕ) (hj : j ≤ s) (a r : ℕ) (ha : a ≤ j) (hr : r ≤ j-a) :
      cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
        weightedPeriodicL2Norm μ (fun x i ↦ periodicJet (j-a-r) (fun x ↦ E x i) x) ≤ A * T := by
    calc
      _ ≤ cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
          (A * weightedPeriodicSobolevNorm μ (s-a-r) E) := by
        apply mul_le_mul_of_nonneg_left
          (weightedPeriodicL2Norm_periodicJet_le_sobolev_uniform s μ hμ E hE (by omega) (by omega))
          (mul_nonneg (cNorm_nonneg _ _ _) (Real.sqrt_nonneg _))
      _ = A * P a r := by dsimp [P]; ring
      _ ≤ A * T := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact (Finset.single_le_sum (fun r _ ↦ hP a r)
          (Finset.mem_range.mpr (show r < s-a+1 by omega))).trans
          (Finset.single_le_sum (f := fun a ↦ ∑ r ∈ Finset.range (s-a+1), P a r)
            (fun a _ ↦ Finset.sum_nonneg (fun r _ ↦ hP a r))
            (Finset.mem_range.mpr (show a < s+1 by omega)))
  have hj (j : ℕ) (hj : j ∈ Finset.range (s+1)) :
      periodicL2Norm (periodicJet j (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i)))) ≤
        K j * (A * T) := by
    apply (periodicL2Norm_periodicJet_contracted_weightedBilinear_le
      B hB μ hμ D E hD hE C hC j).trans
    dsimp only [K]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    calc
      _ = ((j.choose a : ℝ) * ((j-a).choose r : ℝ)) *
          (cNorm (fundamentalCell d) a (periodicLift C) * weightedPeriodicCNorm μ r D *
            weightedPeriodicL2Norm μ (fun x i ↦ periodicJet (j-a-r) (fun x ↦ E x i) x)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hterm j (by have := Finset.mem_range.mp hj; omega) a r (by have := Finset.mem_range.mp ha; omega)
          (by have := Finset.mem_range.mp hr; omega)) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc
    _ ≤ R * ∑ j ∈ Finset.range (s+1),
        periodicL2Norm (periodicJet j (fun x ↦ C x (∑ i, μ i • B (D x i) (E x i)))) :=
      periodicSobolevNorm_le_sum_periodicJet_uniform s
        (isSmoothPeriodic_contracted_weightedBilinear B μ D E hD hE C hC)
    _ ≤ R * ∑ j ∈ Finset.range (s+1), K j * (A * T) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hj) hR
    _ = (R * A * ∑ j ∈ Finset.range (s+1), K j) * T := by
      rw [← Finset.sum_mul]; ring
    _ ≤ periodicProductSobolevConstant d s * T :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hT

end Hilbert
end JanetCartan.CurrentMean
