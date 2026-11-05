module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalTailRealization.FiniteData

/-!
# Actual support and bounds on every grouped data prefix

All data are restrictions of the same full annular Hilbert datum. These
finite-sum identities supply the individual Fourier bounds in
`app:ch_mean_pairs:eq:mean-canonical-bounds`, with the literal cutoff ceiling.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.CanonicalTailRealization
open RawInputPartition RawInputRealization CanonicalDataBounds

variable {n J L : ℕ}

private def prefixIndex (hL : L ≤ J) (i : RefinedIndex L) : RefinedIndex J :=
  (i.1.castLE hL, i.2)

private theorem prefixIndex_injective (hL : L ≤ J) : Function.Injective (prefixIndex hL) := by
  intro i j h
  apply Prod.ext
  · exact Fin.ext (congrArg (fun t : RefinedIndex J ↦ t.1.val) h)
  · exact congrArg (fun t : RefinedIndex J ↦ t.2) h

/-- Actual restriction of the full datum, keeping both pieces of every
retained band (`app:ch_waves:eq:sampling-prefix-normal`). -/
def prefixInput (hL : L ≤ J) (v : RefinedInput n J) : RefinedInput n L :=
  WithLp.toLp 2 (fun i ↦ v (i.1.castLE hL, i.2))

/-- Restricting the same datum costs no scale-count factor
(`app:ch_waves:eq:B-bounds`). -/
theorem norm_prefixInput_le (hL : L ≤ J) (v : RefinedInput n J) :
    ‖prefixInput hL v‖ ≤ ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_input_sq, norm_input_sq]
  exact Finset.sum_le_sum_of_injOn (prefixIndex hL) (prefixIndex_injective hL).injOn
    (Finset.subset_univ _) (fun _ _ ↦ le_rfl) (fun _ _ _ ↦ sq_nonneg _)

private theorem channelDensity_zero_ae {R : ℝ} (β : Euclidean (n - 1) → ℂ) :
    channelDensity β (0 : AnnularL2 n R) =ᵐ[volume] 0 := by
  simpa only [zero_smul] using channelDensity_smul β 0 (0 : AnnularL2 n R)

/-- The exact finite density sum of the grouped prefix. Zero L² components
are removed almost everywhere, as required for actual representatives
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem density_refinedPrefix_eq_sum (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
    (v : RefinedInput n J) (L : ℕ) :
    density β (refinedPrefix n J L v) =ᵐ[volume]
      fun η ↦ ∑ i : RefinedIndex J, if i.1.val < L then channelDensity (β i) (v i) η else 0 := by
  have hz := Filter.eventually_all.mpr (fun i : RefinedIndex J ↦
    channelDensity_zero_ae (R := refinedRadius i) (β i))
  filter_upwards [hz] with η hη
  apply Finset.sum_congr rfl
  intro i _
  rw [refinedPrefix_apply]
  split_ifs with hi
  · rfl
  · exact hη i

/-- The grouped prefix has exactly the density of the restricted datum;
this is reindexing, not an independent existential choice
(`app:ch_waves:eq:B-bounds`). -/
theorem density_refinedPrefix_eq_prefixInput
    (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
    (hL : L ≤ J) (v : RefinedInput n J) :
    density β (refinedPrefix n J L v) =ᵐ[volume]
      density (fun i : RefinedIndex L ↦ β (i.1.castLE hL, i.2)) (prefixInput hL v) := by
  apply (density_refinedPrefix_eq_sum β v L).trans
  apply Filter.Eventually.of_forall
  intro η
  symm
  apply Fintype.sum_of_injective (prefixIndex hL) (prefixIndex_injective hL)
  · intro i hi
    have hn : ¬i.1.val < L := by
      intro h
      exact hi ⟨(⟨i.1.val, h⟩, i.2), by ext <;> rfl⟩
    simp only [hn, ite_false]
  · intro i
    simp only [prefixIndex, Fin.val_castLE, i.1.isLt, ite_true]
    rfl

/-- Fourier support of the same prefix is bounded by its own dyadic ceiling,
even though its ambient Hilbert input was fixed at a larger ceiling
(`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem density_refinedPrefix_eq_zero_above_ceiling
    (β : RefinedIndex J → Euclidean (n - 1) → ℂ) (v : RefinedInput n J) (L : ℕ) :
    ∀ᵐ η ∂volume, (2 : ℝ) ^ L < ‖η‖ → density β (refinedPrefix n J L v) η = 0 := by
  filter_upwards [density_refinedPrefix_eq_sum β v L] with η hη hhigh
  rw [hη]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · apply channelDensity_eq_zero
    intro hmem
    have hnorm : ‖η‖ ≤ refinedRadius i := by simpa using hmem.1
    have hradius : refinedRadius i ≤ (2 : ℝ) ^ L :=
      pow_le_pow_right₀ (by norm_num) (by have := i.2.isLt; omega)
    exact (not_lt_of_ge (hnorm.trans hradius)) hhigh
  · rfl

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The actual canonical Fourier data use the literal `4*K` support ceiling
of the rounded grouped partition (`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem fourierDensity_groupedPrefixRow_eq_zero_above_four_mul
    (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y)
    {K : ℝ} (hK : 1 ≤ K) (r : Y) :
    ∀ᵐ η ∂volume, 4 * K < ‖η‖ → fourierDensity β (groupedPrefixRow A K) Q0 r η = 0 := by
  rw [fourierDensity, adjointInput_groupedPrefixRow]
  filter_upwards [density_refinedPrefix_eq_zero_above_ceiling β (A.adjoint (Q0 r))
    (cutoffCount K)] with η hη hhigh
  exact hη ((cutoffCount_ceiling hK).trans_lt hhigh)

/-- The canonical input already lies in the SAME grouped prefix; applying
that prefix a second time changes nothing (`main:eq:old-canonical`). -/
theorem refinedPrefix_adjointInput_groupedPrefixRow
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y) (K : ℝ) (r : Y) :
    refinedPrefix n J (cutoffCount K) (adjointInput (groupedPrefixRow A K) Q0 r) =
      adjointInput (groupedPrefixRow A K) Q0 r := by
  rw [adjointInput_groupedPrefixRow]
  apply PiLp.ext
  intro i
  by_cases hi : i.1.val < cutoffCount K <;> simp [refinedPrefix_apply, hi]

/-- On the fixed full input, the canonical Fourier density is exactly the
density of its own retained coordinates (`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem fourierDensity_groupedPrefixRow_eq_prefixInput
    (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y)
    {K : ℝ} (hKJ : cutoffCount K ≤ J) (r : Y) :
    fourierDensity β (groupedPrefixRow A K) Q0 r =ᵐ[volume]
      density (fun i : RefinedIndex (cutoffCount K) ↦ β (i.1.castLE hKJ, i.2))
        (prefixInput hKJ (adjointInput (groupedPrefixRow A K) Q0 r)) := by
  have h := density_refinedPrefix_eq_prefixInput β hKJ
    (adjointInput (groupedPrefixRow A K) Q0 r)
  rwa [refinedPrefix_adjointInput_groupedPrefixRow] at h

/-- The actual smaller-band initial field is unchanged by restricting to
retained coordinates (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem initialDatum_groupedPrefixRow_eq_prefixInput
    (β : RefinedIndex J → Euclidean (n - 1) → ℂ)
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y)
    {K : ℝ} (hKJ : cutoffCount K ≤ J) (r : Y) :
    initialDatum β (groupedPrefixRow A K) Q0 r =
      field (fun i : RefinedIndex (cutoffCount K) ↦ β (i.1.castLE hKJ, i.2))
        (prefixInput hKJ (adjointInput (groupedPrefixRow A K) Q0 r)) :=
  VectorFourier.fourierIntegral_congr_ae _ _ _
    (fourierDensity_groupedPrefixRow_eq_prefixInput β A Q0 hKJ r)

/-- The Fourier `L¹` estimate at EACH actual cutoff, retaining the full input
and its original individual-row bound (`app:ch_mean_pairs:eq:mean-canonical-bounds`).
The constants do not depend on the full ceiling or on the number of bands. -/
theorem integral_norm_fourierDensity_groupedPrefixRow_le
    (hn : 1 ≤ n) {β : RefinedIndex J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M CA CQ K : ℝ}
    (hM : 0 ≤ M) (hb : ∀ i η, ‖β i η‖ ≤ M)
    (hCA : 0 ≤ CA) (hK : 1 ≤ K) (hKJ : cutoffCount K ≤ J)
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y)
    (hA : ‖groupedPrefixRow A K‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ) (r : Y) :
    (∫ η, ‖fourierDensity β (groupedPrefixRow A K) Q0 r η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2) * CA * CQ) *
        K ^ (((n : ℝ) + 1) / 2) * ‖r‖ := by
  rw [integral_congr_ae ((fourierDensity_groupedPrefixRow_eq_prefixInput β A Q0 hKJ r).mono
    (fun _ he ↦ congrArg norm he))]
  have hraw (v : RefinedInput n J) :
      (∫ η, ‖density (fun i : RefinedIndex (cutoffCount K) ↦ β (i.1.castLE hKJ, i.2))
        (prefixInput hKJ v) η‖) ≤
      (refinedFourierConstant n M * 4 ^ ((n : ℝ) / 2)) * K ^ ((n : ℝ) / 2) * ‖v‖ :=
    (integral_norm_density_refined_rounded_le hn hK
      (fun i ↦ hβ (i.1.castLE hKJ, i.2)) hM
      (fun i ↦ hb (i.1.castLE hKJ, i.2)) (prefixInput hKJ v)).trans
        (mul_le_mul_of_nonneg_left (norm_prefixInput_le hKJ v)
          (mul_nonneg (mul_nonneg (refinedFourierConstant_nonneg n hM) (by positivity))
            (Real.rpow_nonneg (zero_le_one.trans hK) _)))
  have h := size_adjointInput_le (groupedPrefixRow A K) Q0 _
    (mul_nonneg (refinedFourierConstant_nonneg n hM) (by positivity)) hCA
    (zero_lt_one.trans_le hK) hA hQ hraw r
  simpa only [show (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 by ring] using h

/-- Initial derivative estimates at EACH retained cutoff on the same fixed
input, with the literal two-shell constant
(`app:ch_mean_pairs:eq:mean-canonical-bounds`). -/
theorem cNorm_initialDatum_groupedPrefixRow_le
    (hn : 1 ≤ n) {β : RefinedIndex J → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M CA CQ K : ℝ}
    (hM : 0 ≤ M) (hb : ∀ i η, ‖β i η‖ ≤ M)
    (hCA : 0 ≤ CA) (hK : 1 ≤ K) (hKJ : cutoffCount K ≤ J)
    (A : RefinedInput n J →L[ℝ] Y) (Q0 : Y →L[ℝ] Y)
    (hA : ‖groupedPrefixRow A K‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ)
    (r : Y) (m : ℕ) (S : Set (Euclidean (n - 1))) :
    cNorm S m (initialDatum β (groupedPrefixRow A K) Q0 r) ≤
      (((m + 1 : ℕ) : ℝ) * refinedFourierConstant n M *
        4 ^ ((m : ℝ) + (n : ℝ) / 2) * CA * CQ) *
        K ^ ((m : ℝ) + ((n : ℝ) + 1) / 2) * ‖r‖ := by
  rw [initialDatum_groupedPrefixRow_eq_prefixInput β A Q0 hKJ]
  have hraw (v : RefinedInput n J) :
      cNorm S m (field (fun i : RefinedIndex (cutoffCount K) ↦ β (i.1.castLE hKJ, i.2))
        (prefixInput hKJ v)) ≤
      (((m + 1 : ℕ) : ℝ) * refinedFourierConstant n M * 4 ^ ((m : ℝ) + (n : ℝ) / 2)) *
        K ^ ((m : ℝ) + (n : ℝ) / 2) * ‖v‖ :=
    (cNorm_field_refined_rounded_le hn hK
      (fun i ↦ hβ (i.1.castLE hKJ, i.2)) hM
      (fun i ↦ hb (i.1.castLE hKJ, i.2)) (prefixInput hKJ v) m S).trans
        (mul_le_mul_of_nonneg_left (norm_prefixInput_le hKJ v)
          (by have := refinedFourierConstant_nonneg n hM; positivity))
  have h := size_adjointInput_le (groupedPrefixRow A K) Q0 _
    (by have := refinedFourierConstant_nonneg n hM; positivity) hCA
    (zero_lt_one.trans_le hK) hA hQ hraw r
  simpa only [show (m : ℝ) + (n : ℝ) / 2 + 1 / 2 =
    (m : ℝ) + ((n : ℝ) + 1) / 2 by ring] using h

end JanetCartan.CanonicalTailRealization
