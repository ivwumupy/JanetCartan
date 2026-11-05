module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.PrefixData

/-!
# Finite accumulation of the same canonical data

The data sums in `main:eq:variation` retain one full row, its grouped prefixes,
one detector family, one continuum inverse and the supplied residuals. Each
density is proved integrable before interchanging its finite sum and integral.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.CanonicalTailRealization
open RawInputPartition RawInputRealization CanonicalDataBounds

variable {n J : ℕ} {κ Y : Type*} [NormedAddCommGroup Y]
  [InnerProductSpace ℝ Y] [CompleteSpace Y]
  (I : Finset κ) (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
  (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y) (K : κ → ℝ) (r : κ → Y)

/-- The accumulated canonical Fourier density retains the largest original
cutoff (`main:eq:variation`). Support is correctly asserted almost everywhere
for the actual L² representatives. -/
theorem sum_fourierDensity_groupedPrefixRow_eq_zero_above_four_mul
    (hK : ∀ l ∈ I, 1 ≤ K l) {Kmax : ℝ} (hmax : ∀ l ∈ I, K l ≤ Kmax) :
    ∀ᵐ η ∂volume, 4 * Kmax < ‖η‖ →
      (∑ l ∈ I, fourierDensity β (groupedPrefixRow A (K l)) Q0 (r l) η) = 0 := by
  have hs := Filter.eventually_all.mpr (fun l : I ↦
    fourierDensity_groupedPrefixRow_eq_zero_above_four_mul β A Q0 (hK l l.property) (r l))
  filter_upwards [hs] with η hη hhigh
  apply Finset.sum_eq_zero
  intro l hl
  exact hη ⟨l, hl⟩ ((mul_le_mul_of_nonneg_left (hmax l hl) (by norm_num)).trans_lt hhigh)

/-- The sum of initial fields is the inverse Fourier integral of the sum of
their integrable densities, for the SAME row and inverse (`main:eq:variation`). -/
theorem sum_initialDatum_groupedPrefixRow_eq_fourierIntegral
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hb : ∀ i η, ‖β i η‖ ≤ M) :
    (fun x ↦ ∑ l ∈ I, initialDatum β (groupedPrefixRow A (K l)) Q0 (r l) x) =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (radianPairing n).toLinearMap₁₂
        (fun η ↦ ∑ l ∈ I, fourierDensity β (groupedPrefixRow A (K l)) Q0 (r l) η) := by
  funext x
  simp only [VectorFourier.fourierIntegral, Finset.smul_sum]
  rw [integral_finsetSum I]
  · rfl
  · intro l _
    exact (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar
      (radianPairing n).continuous₂ x).2
      (integrable_fourierDensity hβ hb (groupedPrefixRow A (K l)) Q0 (r l))

/-- Fourier variation is an actual finite sum of finite integrals. It bounds
the accumulated density without a cancellation premise (`main:eq:variation`). -/
theorem integral_norm_sum_fourierDensity_groupedPrefixRow_le
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hb : ∀ i η, ‖β i η‖ ≤ M) :
    (∫ η, ‖∑ l ∈ I, fourierDensity β (groupedPrefixRow A (K l)) Q0 (r l) η‖) ≤
      ∑ l ∈ I, ∫ η, ‖fourierDensity β (groupedPrefixRow A (K l)) Q0 (r l) η‖ := by
  have hi (l : κ) := integrable_fourierDensity hβ hb (groupedPrefixRow A (K l)) Q0 (r l)
  rw [← integral_finsetSum I (fun l _ ↦ (hi l).norm)]
  exact integral_mono (integrable_finsetSum I (fun l _ ↦ hi l)).norm
    (integrable_finsetSum I (fun l _ ↦ (hi l).norm)) (fun η ↦ norm_sum_le I _)

/-- The quantitative finite Fourier variation uses the same inverse and the
same residual budget. Constants precede all update data in
`main:eq:variation`; there is no factor from the number of cutoffs or samples. -/
theorem sum_integral_norm_fourierDensity_groupedPrefixRow_le
    (hn : 1 ≤ n) (hβ : ∀ i, Measurable (β i)) {M CA CQ Kmax ε : ℝ}
    (hM : 0 ≤ M) (hb : ∀ i η, ‖β i η‖ ≤ M) (hCA : 0 ≤ CA)
    (hmax0 : 0 ≤ Kmax) (hK : ∀ l ∈ I, 1 ≤ K l)
    (hKJ : ∀ l ∈ I, cutoffCount (K l) ≤ J) (hmax : ∀ l ∈ I, K l ≤ Kmax)
    (hA : ∀ l ∈ I, ‖groupedPrefixRow A (K l)‖ ≤ CA * Real.sqrt (K l))
    (hQ : ‖Q0‖ ≤ CQ) (hbudget : ∑ l ∈ I, ‖r l‖ ≤ ε) :
    (∑ l ∈ I, ∫ η, ‖fourierDensity β (groupedPrefixRow A (K l)) Q0 (r l) η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * CQ) *
        ε * Kmax ^ (((n : ℝ) + 1) / 2) := by
  have hCQ : 0 ≤ CQ := (norm_nonneg _).trans hQ
  have hconstant : 0 ≤ refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * CQ :=
    mul_nonneg (mul_nonneg (mul_nonneg (refinedFourierConstant_nonneg n hM)
      (by positivity)) hCA) hCQ
  calc
    _ ≤ (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * CQ) *
        Kmax ^ (((n : ℝ) + 1) / 2) * ∑ l ∈ I, ‖r l‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro l hl
      apply (integral_norm_fourierDensity_groupedPrefixRow_le hn hβ hM hb hCA
        (hK l hl) (hKJ l hl) A Q0 (hA l hl) hQ (r l)).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans (hK l hl)) (hmax l hl) (by positivity))
        hconstant) (norm_nonneg _)
    _ ≤ (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * CQ) *
        Kmax ^ (((n : ℝ) + 1) / 2) * ε :=
      mul_le_mul_of_nonneg_left hbudget (mul_nonneg hconstant (Real.rpow_nonneg hmax0 _))
    _ = _ := by ring

end JanetCartan.CanonicalTailRealization
