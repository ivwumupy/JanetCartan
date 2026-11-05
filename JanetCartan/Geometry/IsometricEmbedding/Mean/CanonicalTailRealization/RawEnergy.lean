module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.WeightedInput
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Carrier

/-!
# The actual full raw energy in the canonical cutoff estimate

The weighted membership and energy comparison required by
`RecurrenceTail.run_inductive_raw_tail_le` follow from the full initial scale
produced by `ContinuumInverse`. The finite carrier sum keeps its Hilbert norm,
and both auxiliary components retain their original periodic measure.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.CanonicalTailRealization
open ContinuumRow RawCutoffBounds CarrierSobolev

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Full initial regularity supplies every convergent energy in
`main:eq:linear-two-errors`, including both auxiliary channels. -/
theorem rawWeightedMem_of_augmentedInputLevel {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ (augmentedInputSobolevScale n ι).level s) :
    RawWeightedMem s (fun _ ↦ transverseBesselWeight s) u := by
  have h := (mem_augmentedInputLevel_iff s u).mp hu
  exact ⟨h.1, h.2.2, augmentedInput_carrierWeightedMem hu⟩

/-- The complete transverse energy is bounded by the SAME full initial norm
with constant one (`app:ch_background:eq:bg-r-inverse`). This is the `henergy`
input of `RecurrenceTail.run_inductive_raw_tail_le`; summing separate bounds
by the full norm would incorrectly introduce a carrier-count factor. -/
theorem rawWeightedNorm_le_augmentedInput_gradeNorm {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ (augmentedInputSobolevScale n ι).level s) :
    rawWeightedNorm s (fun _ ↦ transverseBesselWeight s) u
      (rawWeightedMem_of_augmentedInputLevel hu) ≤
        (augmentedInputSobolevScale n ι).gradeNorm s u := by
  have h := (mem_augmentedInputLevel_iff s u).mp hu
  have haux {v : OutputL2 n} (hv : v ∈ periodicSobolevLevel n (Euclidean n) s) :
      (periodicSobolevScale n (Euclidean n)).gradeNorm s v = periodicSobolevNorm s v := by
    rw [GradedScale.gradeNorm_eq _ hv]
    exact periodicSobolevSeminorm_eq s ⟨v, hv⟩
  have hc := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    pow_le_pow_left₀ (norm_nonneg _)
      (carrierWeightedNorm_transverseBesselWeight_le (h.2.1 i)) 2)
  unfold rawWeightedNorm
  apply (Real.sqrt_le_iff).mpr
  refine ⟨GradedScale.gradeNorm_nonneg _ _ _, ?_⟩
  rw [augmentedInputSobolevScale_gradeNorm_sq hu, haux h.1, haux h.2.2]
  exact add_le_add (add_le_add le_rfl hc) le_rfl

/-- The constructed dyadic square has the original auxiliary ceiling `K`
and carrier plateau `K`, with all weighted-domain premises discharged from
the full raw input domain (`main:eq:linear-two-errors`). -/
theorem rawSquaredCutoff_rounded_tail_of_augmentedInputLevel
    {K : ℝ} (hK : 1 ≤ K) {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ (augmentedInputSobolevScale n ι).level s) :
    ‖u - rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n K) u‖ ≤
      K ^ (-(s : ℝ)) * (augmentedInputSobolevScale n ι).gradeNorm s u := by
  exact (RawInputPartition.rawSquaredCutoff_rounded_tail hK s u
    (fun _ ↦ transverseBesselWeight s) (rawWeightedMem_of_augmentedInputLevel hu)
    (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ le_rfl)).trans
      (mul_le_mul_of_nonneg_left (rawWeightedNorm_le_augmentedInput_gradeNorm hu)
        (Real.rpow_nonneg (zero_le_one.trans hK) _))

/-- The literal carrier plateau may be `c*K` while BOTH auxiliary cutoffs
remain `K`. Its loss is `max 1 (c^(-s))`, not an unrecorded change of scale
(`main:eq:linear-two-errors`, `app:ch_background:defn:bg-mixed`). -/
theorem rawSquaredCutoff_scaled_rounded_tail_of_augmentedInputLevel
    {c K : ℝ} (hc : 0 < c) (hK : 1 ≤ K) (hcK : 1 ≤ c * K)
    {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ (augmentedInputSobolevScale n ι).level s) :
    ‖u - rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K)) u‖ ≤
      (max 1 (c ^ (-(s : ℝ))) * K ^ (-(s : ℝ))) *
        (augmentedInputSobolevScale n ι).gradeNorm s u := by
  let F := max 1 (c ^ (-(s : ℝ))) * K ^ (-(s : ℝ))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hF : 0 ≤ F := mul_nonneg ((zero_le_one.trans (le_max_left _ _)))
    (Real.rpow_nonneg hK0 _)
  have hiF : (K ^ s)⁻¹ ≤ F := by
    rw [← Real.rpow_natCast K s, ← Real.rpow_neg hK0]
    exact (one_mul (K ^ (-(s : ℝ)))).symm.le.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hK0 _))
  have hcF : ((c * K) ^ s)⁻¹ ≤ F := by
    rw [← Real.rpow_natCast (c * K) s, ← Real.rpow_neg (mul_nonneg hc.le hK0),
      Real.mul_rpow hc.le hK0]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hK0 _)
  have hm := rawWeightedMem_of_augmentedInputLevel hu
  have hi := (auxiliarySquaredCutoff_tail hK s u.fst.fst hm.image).trans
    (mul_le_mul_of_nonneg_right hiF (GradedScale.gradeNorm_nonneg _ _ _))
  have he := (auxiliarySquaredCutoff_tail hK s u.snd hm.exterior).trans
    (mul_le_mul_of_nonneg_right hiF (GradedScale.gradeNorm_nonneg _ _ _))
  have hcarrier (i : ι) :
      ‖u.fst.snd i - carrierSquaredCutoff (RawInputPartition.roundedCarrierMask n (c * K))
        (u.fst.snd i)‖ ≤
      F * carrierWeightedNorm (transverseBesselWeight s) (u.fst.snd i) (hm.carrier i) := by
    apply (carrierSquaredCutoff_tail hcK s _ _
      (RawInputPartition.roundedCarrierMask_mem n (c * K)) ?_
      (transverseBesselWeight s) (hm.carrier i)
      (Filter.Eventually.of_forall fun _ ↦ le_rfl)).trans
    · exact mul_le_mul_of_nonneg_right hcF (norm_nonneg _)
    · filter_upwards [RawInputPartition.roundedCarrierMask_eq_one (n := n) hcK] with x hx
      exact fun _ hxK ↦ hx hxK
  have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
  have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
  have hc2 := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦
    pow_le_pow_left₀ (norm_nonneg _) (hcarrier i) 2
  simp only [mul_pow, ← Finset.mul_sum] at hi2 he2 hc2
  have hnorm :
      ‖u - rawSquaredCutoff K (fun _ ↦ RawInputPartition.roundedCarrierMask n (c * K)) u‖ ≤
        F * rawWeightedNorm s (fun _ ↦ transverseBesselWeight s) u hm := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hF (Real.sqrt_nonneg _))).mp
    rw [mul_pow]
    rw [Real.sq_sqrt (by positivity)]
    simp [rawSquaredCutoff, WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    nlinarith only [hi2, he2, hc2]
  exact hnorm.trans
    (mul_le_mul_of_nonneg_left (rawWeightedNorm_le_augmentedInput_gradeNorm hu) hF)

end JanetCartan.CanonicalTailRealization
