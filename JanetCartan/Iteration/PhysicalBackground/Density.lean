module

public import JanetCartan.Iteration.PhysicalBackground.Source
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.SourceInverse

/-!
# Exact factor-two synthesis for the current physical background

For v2 `app:ch_background:eq:bg-density-input`, construct ONE globally smooth
real representative from the current raw adjoint input. Its constants depend
only on the original masks and label domains. All initial positions are kept,
and almost-everywhere equality is upgraded before footpoint substitution.
Task22 produces raw regularity and estimates; no density, profile or positivity
success is assumed here. The original-data small source estimate remains open.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalBackground
open ContinuumRow CarrierSobolev UncutDensity PositiveBackground

variable {n N : ℕ} {ι : Type*} [Fintype ι]

private theorem raw_component_le {s : ℕ} {u : AugmentedInput n ι}
    (hu : u ∈ augmentedInputLevel n ι s) (i : ι) :
    rawSobolevNorm s (u.fst.snd i) ≤ (augmentedInputSobolevScale n ι).gradeNorm s u := by
  obtain ⟨v, rfl⟩ := hu
  apply le_trans _ (augmentedInputSobolevScale_gradeNorm s v).symm.le
  exact (RawSobolevSpace.norm_eq s (v.fst.snd i)).symm.le.trans
    ((PiLp.norm_apply_le v.fst.snd i).trans
      ((WithLp.norm_snd_le _ v.fst).trans (WithLp.norm_fst_le _ v)))

/-- Fixed masks give uniform global and original-label estimates for the SAME
factor-two current density. The constants precede the current carrier data,
raw input, source, scale and derivative order. The reserve is full initial
dimension plus two (`app:ch_background:eq:bg-current-profile`). -/
theorem exists_uncut_density_estimates
    (d₀ : ι → CarrierData n N)
    (hρsmooth : ∀ i, ContDiff ℝ ∞
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)))
    (hcρ : ∀ i, HasCompactSupport
      (fun p : CarrierVariable n ↦ ((d₀ i).angularCutoff p.1 p.2 : ℂ)))
    (hχsmooth : ∀ i, ContDiff ℝ ∞ (d₀ i).highCutoff)
    (hlow : ∀ i t, t ≤ 1 → (d₀ i).highCutoff t = 0)
    (hhi : ∀ i t, |(d₀ i).highCutoff t| ≤ 1)
    (hρ : ∀ i z η, |(d₀ i).angularCutoff z η| ≤ 1)
    (Kin : ι → Set (Euclidean (n - 1) × Euclidean 3))
    (hKin : ∀ i, IsCompact (Kin i)) :
    ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ d : ι → CarrierData n N,
      (∀ i, (d i).angularCutoff = (d₀ i).angularCutoff) →
      (∀ i, (d i).highCutoff = (d₀ i).highCutoff) →
      ∀ u : AugmentedInput n ι, (∀ s, u ∈ augmentedInputLevel n ι s) →
      ∃ v : ι → CarrierVariable n → ℝ,
        (∀ i, ContDiff ℝ ∞ (v i)) ∧
        (∀ i, v i =ᵐ[carrierMeasure n] initialDensity (d i) 2 (u.fst.snd i)) ∧
        (∀ i, ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
          ∀ y, v i (z, y) = initialDensity (d i) 2 (u.fst.snd i) (z, y)) ∧
        (∀ i s, cNorm univ s (v i) ≤ C s *
          (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u) ∧
        (∀ i s j, j ≤ s → ∀ p, ‖iteratedFDeriv ℝ j (v i) p‖ ≤ C s *
          (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u) ∧
        ∀ i s, cNorm (Kin i) s (densityOnInitialLabels (v i)) ≤ C s *
          (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u := by
  classical
  choose D hD hjet using fun i s ↦ CurrentMean.exists_initialDensityRepresentative_derivative_bound
    (d₀ i) (hρsmooth i) (hcρ i) (hχsmooth i) (hlow i) (hhi i) zero_le_one (hρ i) 2 s
  choose L hL hlabel using fun i s ↦ exists_cNorm_densityOnInitialLabels_le (hKin i) s
  let C := fun s ↦ 1 + ∑ i, ((s + 1 : ℕ) + L i s + 1) * D i s
  have hterm (i : ι) (s : ℕ) : 0 ≤ ((s + 1 : ℕ) + L i s + 1) * D i s := by
    exact mul_nonneg (by have := hL i s; positivity) (hD i s)
  have hC (s : ℕ) : 0 < C s := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ hterm i s)
    dsimp [C]
    linarith
  have hDC (i : ι) (s : ℕ) : D i s ≤ C s := by
    have ht := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hterm j s)
      (Finset.mem_univ i)
    have hlt : D i s ≤ ((s + 1 : ℕ) + L i s + 1) * D i s := by
      nlinarith [hD i s, hL i s, Nat.cast_nonneg (α := ℝ) (s + 1)]
    dsimp [C]
    linarith
  have hsumC (i : ι) (s : ℕ) : (s + 1 : ℕ) * D i s ≤ C s := by
    have ht := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hterm j s)
      (Finset.mem_univ i)
    dsimp [C]
    nlinarith [hD i s, hL i s]
  have hLC (i : ι) (s : ℕ) : L i s * D i s ≤ C s := by
    have ht := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hterm j s)
      (Finset.mem_univ i)
    dsimp [C]
    nlinarith [hD i s, Nat.cast_nonneg (α := ℝ) (s + 1)]
  refine ⟨C, hC, ?_⟩
  intro d hangular hhigh u hu
  have hraw (i : ι) (s : ℕ) : MemRawSobolev s (u.fst.snd i) :=
    ((mem_augmentedInputLevel_iff s u).mp (hu s)).2.1 i
  choose v hv he using fun i ↦ CurrentMean.exists_smooth_initialDensity
    (d₀ i) (hρsmooth i) (hcρ i) (hχsmooth i) (hlow i) (hhi i)
    zero_le_one (hρ i) 2 (u.fst.snd i) (hraw i)
  have hj (i : ι) (s j : ℕ) (hj : j ≤ s) (p : CarrierVariable n) :
      ‖iteratedFDeriv ℝ j (v i) p‖ ≤ D i s *
        (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u := by
    have h := (hjet i s (u.fst.snd i) (hraw i) (v i) (hv i) (he i) j hj p).trans
      (mul_le_mul_of_nonneg_left (raw_component_le (hu _) i) (hD i s))
    simpa only [Nat.add_assoc] using h
  have he' (i : ι) : v i =ᵐ[carrierMeasure n] initialDensity (d i) 2 (u.fst.snd i) := by
    rw [initialDensity_eq_of_masks (d i) (d₀ i) (hangular i) (hhigh i)]
    exact he i
  refine ⟨v, hv, he', ?_, ?_, ?_, ?_⟩
  · intro i
    rw [initialDensity_eq_of_masks (d i) (d₀ i) (hangular i) (hhigh i)]
    exact CurrentMean.initialDensity_ae_all_positions (d₀ i) (n + 1) (by omega)
      (hρsmooth i).continuous.measurable (hχsmooth i).continuous.measurable
      zero_le_one zero_le_one (hρ i) (hhi i) 2 _ (hraw i _) _ (hv i).continuous (he i)
  · intro i s
    have hb := cNorm_le_sum_of_bounds (s := univ) (r := s) (f := v i)
      (fun _ _ ↦ mul_nonneg (hD i s) ((augmentedInputSobolevScale n ι).gradeNorm_nonneg _ u))
      (fun j hjs p _ ↦ hj i s j hjs p)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hb
    exact hb.trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hsumC i s)
        ((augmentedInputSobolevScale n ι).gradeNorm_nonneg _ u))
  · intro i s j hjs p
    exact (hj i s j hjs p).trans (mul_le_mul_of_nonneg_right (hDC i s)
      ((augmentedInputSobolevScale n ι).gradeNorm_nonneg _ u))
  · intro i s
    have hb := hlabel i s (v i)
      (D i s * (augmentedInputSobolevScale n ι).gradeNorm (s + (3 + (n - 1)) + 2) u)
      (mul_nonneg (hD i s) ((augmentedInputSobolevScale n ι).gradeNorm_nonneg _ u))
      (hv i) (hj i s)
    exact hb.trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hLC i s)
        ((augmentedInputSobolevScale n ι).gradeNorm_nonneg _ u))

end JanetCartan.PhysicalBackground
