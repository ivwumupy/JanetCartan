module

public import JanetCartan.Iteration.PhysicalRawInterpolation.Fourier

/-!
# Endpoint interpolation for the same full augmented raw input

For `app:ch_background:prop:bg-adjoint`, retain the actual Hilbert input used
by the current augmented normal inverse. Its two periodic auxiliary channels
and all full initial-variable carrier channels are included. The only finite
factor is the FIXED original continuum menu, never a sampled or band index.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace JanetCartan.PhysicalRawInterpolation

open ContinuumRow CarrierSobolev

variable {n : ℕ} {ι : Type*} [Fintype ι]

private theorem hilbert_pair_norm_le_sum {A B : Type*}
    [NormedAddCommGroup A] [NormedAddCommGroup B] (v : WithLp 2 (A × B)) :
    ‖v‖ ≤ ‖v.fst‖ + ‖v.snd‖ := by
  have hs := WithLp.prod_norm_sq_eq_of_L2 v
  have hpos := norm_nonneg v
  have hf := norm_nonneg v.fst
  have hg := norm_nonneg v.snd
  nlinarith [mul_nonneg hf hg]

private theorem hilbert_family_norm_le_sum (s : ℕ) (v : CarrierFamilySobolevSpace n ι s) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  have hs := PiLp.norm_sq_eq_of_L2 (fun _ : ι ↦ RawSobolevSpace n s) v
  have hb := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i ↦ ‖v i‖) (fun i _ ↦ norm_nonneg _)
  have hp : 0 ≤ ∑ i, ‖v i‖ := Finset.sum_nonneg (fun i _ ↦ norm_nonneg _)
  nlinarith [norm_nonneg v]

private theorem image_norm_le_grade {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) :
    periodicSobolevNorm s u.fst.fst ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  change periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s v.fst.fst) ≤ ‖v‖
  rw [← PeriodicSobolevSpace.norm_eq]
  exact (WithLp.norm_fst_le _ v.fst).trans (WithLp.norm_fst_le _ v)

private theorem exterior_norm_le_grade {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) :
    periodicSobolevNorm s u.snd ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  change periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s v.snd) ≤ ‖v‖
  rw [← PeriodicSobolevSpace.norm_eq]
  exact WithLp.norm_snd_le _ v

private theorem raw_norm_le_grade {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) (i : ι) :
    rawSobolevNorm s (u.fst.snd i) ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  change rawSobolevNorm s (RawSobolevSpace.toRawL2 s (v.fst.snd i)) ≤ ‖v‖
  rw [← RawSobolevSpace.norm_eq]
  exact (PiLp.norm_apply_le v.fst.snd i).trans
    ((WithLp.norm_snd_le _ v.fst).trans (WithLp.norm_fst_le _ v))

private theorem grade_le_sum_components {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) :
    (augmentedInputSobolevScale n ι).gradeNorm s u ≤
      periodicSobolevNorm s u.fst.fst + (∑ i, rawSobolevNorm s (u.fst.snd i)) +
        periodicSobolevNorm s u.snd := by
  obtain ⟨v, rfl⟩ := hu
  apply (augmentedInputSobolevScale_gradeNorm s v).le.trans
  change ‖v‖ ≤ periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s v.fst.fst) +
    (∑ i, rawSobolevNorm s (RawSobolevSpace.toRawL2 s (v.fst.snd i))) +
      periodicSobolevNorm s (PeriodicSobolevSpace.toL2 s v.snd)
  simp only [← PeriodicSobolevSpace.norm_eq, ← RawSobolevSpace.norm_eq]
  exact (hilbert_pair_norm_le_sum v).trans
    (add_le_add ((hilbert_pair_norm_le_sum v.fst).trans
      (add_le_add (le_refl _) (hilbert_family_norm_le_sum s v.fst.snd))) (le_refl _))

/-- Actual full augmented-input interpolation, with the fixed continuum-menu
constant `card ι + 2`. This is the raw high-order upgrade consumed by the
same-current inverse continuity argument. Every original raw and auxiliary
component is retained; only actual level membership is assumed
(`app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-r-inverse`). -/
theorem augmentedInput_gradeNorm_le_scaled_endpoints (s : ℕ) {K : ℝ} (hK : 1 ≤ K)
    (u : AugmentedInput n ι)
    (hu : u ∈ (augmentedInputSobolevScale n ι).level (s + 1)) :
    (augmentedInputSobolevScale n ι).gradeNorm s u ≤
      ((Fintype.card ι : ℝ) + 2) *
        (K ^ s * ‖u‖ + K⁻¹ * (augmentedInputSobolevScale n ι).gradeNorm (s + 1) u) := by
  classical
  have hc := (mem_augmentedInputLevel_iff (s + 1) u).mp hu
  let Z := K ^ s * ‖u‖ + K⁻¹ * (augmentedInputSobolevScale n ι).gradeNorm (s + 1) u
  have hi : periodicSobolevNorm s u.fst.fst ≤ Z := by
    apply (periodicSobolevNorm_le_scaled_endpoints s hK _ hc.1).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left ((WithLp.norm_fst_le _ u.fst).trans (WithLp.norm_fst_le _ u))
        (by positivity))
      (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using image_norm_le_grade hu)
        (by positivity))
  have he : periodicSobolevNorm s u.snd ≤ Z := by
    apply (periodicSobolevNorm_le_scaled_endpoints s hK _ hc.2.2).trans
    exact add_le_add (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le _ u) (by positivity))
      (mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using exterior_norm_le_grade hu)
        (by positivity))
  have hr (i : ι) : rawSobolevNorm s (u.fst.snd i) ≤ Z := by
    apply (rawSobolevNorm_le_scaled_endpoints s hK _ (hc.2.1 i)).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le u.fst.snd i).trans
        ((WithLp.norm_snd_le _ u.fst).trans (WithLp.norm_fst_le _ u))) (by positivity))
      (mul_le_mul_of_nonneg_left (raw_norm_le_grade hu i) (by positivity))
  calc
    (augmentedInputSobolevScale n ι).gradeNorm s u ≤
        periodicSobolevNorm s u.fst.fst + (∑ i, rawSobolevNorm s (u.fst.snd i)) +
          periodicSobolevNorm s u.snd := grade_le_sum_components (antitone_augmentedInputLevel (Nat.le_succ s) hu)
    _ ≤ Z + (∑ _i : ι, Z) + Z := add_le_add (add_le_add hi (Finset.sum_le_sum (fun i _ ↦ hr i))) he
    _ = ((Fintype.card ι : ℝ) + 2) * Z := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end JanetCartan.PhysicalRawInterpolation
