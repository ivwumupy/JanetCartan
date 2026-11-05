module

public import JanetCartan.Analysis.Operator.SmallSupport.Sobolev
public import JanetCartan.Analysis.Operator.SmallSupport.Cutoff

/-!
# Smooth local Sobolev estimates in dimensions at least two

The local embedding used in `app:ch_regular:thm:exact-correction` of `paper.tex`
follows by multiplying by a fixed smooth bump, applying the whole-space Sobolev
inequality, and comparing derivative norms on its compact support. The exponents
`q = 2n / (n + 1)` and `p = 2n / (n - 1)` work uniformly for `n ≥ 2`.
The derivative term uses the first jet convention of `app:not:fourier`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal ContDiff Topology

namespace JanetCartan.LocalSobolev

/-- Subcritical derivative exponents yield a target exponent above two in every
dimension at least two (`app:ch_regular:thm:exact-correction`). -/
theorem exists_local_sobolev_exponents {n : ℕ} (hn : 2 ≤ n) : ∃ p q : ℝ≥0,
    2 < p ∧ 1 ≤ q ∧ q ≤ 2 ∧
      (p : ℝ)⁻¹ = (q : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hminus : 0 < (n : ℝ) - 1 := by linarith
  have hplus : 0 < (n : ℝ) + 1 := by linarith
  refine ⟨⟨2 * n / (n - 1), by positivity⟩,
    ⟨2 * n / (n + 1), by positivity⟩, ?_, ?_, ?_, ?_⟩
  · change (2 : ℝ) < 2 * n / (n - 1)
    apply (lt_div_iff₀ hminus).mpr
    linarith
  · change (1 : ℝ) ≤ 2 * n / (n + 1)
    apply (le_div_iff₀ hplus).mpr
    linarith
  · change 2 * (n : ℝ) / (n + 1) ≤ 2
    apply (div_le_iff₀ hplus).mpr
    linarith
  · change (2 * (n : ℝ) / (n - 1))⁻¹ = (2 * (n : ℝ) / (n + 1))⁻¹ - (n : ℝ)⁻¹
    field_simp
    ring

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {c : EuclideanSpace ℝ (Fin n)}

/-- A fixed bump bounds the derivative of its product by the two H¹ terms,
with a constant independent of the smooth input (`app:not:fourier` and
`app:ch_regular:thm:exact-correction`). -/
theorem exists_bump_fderiv_two_bound (χ : ContDiffBump c) :
    ∃ D : ℝ≥0, ∀ g : EuclideanSpace ℝ (Fin n) → F,
      ContDiff ℝ ∞ g →
      eLpNorm (fderiv ℝ (fun x ↦ χ x • g x)) 2 volume ≤ D *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
  have hχ : ContDiff ℝ ∞ (χ : EuclideanSpace ℝ (Fin n) → ℝ) := χ.contDiff
  obtain ⟨B, hB⟩ := (χ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hD (x) : ‖fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ≤ D :=
    (hB x).trans (le_max_left _ _)
  refine ⟨D + 1, fun g hg ↦ ?_⟩
  have hfg := (hg.continuous_fderiv (by simp)).aestronglyMeasurable (μ := volume)
  have hgg := hg.continuous.aestronglyMeasurable (μ := volume)
  have hdg : eLpNorm (fderiv ℝ g) 2 volume ≤
      eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume := by
    apply eLpNorm_mono hfg
    intro x
    rw [norm_iteratedFDeriv_one]
  calc
    _ ≤ eLpNorm (fun x ↦ (D : ℝ) * ‖g x‖ + ‖fderiv ℝ g x‖) 2 volume := by
      apply eLpNorm_mono_real ((hχ.smul hg).continuous_fderiv (by simp)).aestronglyMeasurable
      intro x
      change ‖fderiv ℝ (fun y ↦ χ y • g y) x‖ ≤ _
      rw [fderiv_fun_smul (hχ.differentiable (by simp) x) (hg.differentiable (by simp) x)]
      apply (norm_add_le _ _).trans
      rw [add_comm]
      simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul]
      exact add_le_add (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))
        ((mul_le_mul_of_nonneg_right (SmallSupport.bump_norm_le_one χ x)
          (norm_nonneg _)).trans_eq (one_mul _))
    _ ≤ eLpNorm (fun x ↦ (D : ℝ) * ‖g x‖) 2 volume +
        eLpNorm (fun x ↦ ‖fderiv ℝ g x‖) 2 volume :=
      eLpNorm_add_le (by norm_num)
    _ = (D : ℝ≥0∞) * eLpNorm g 2 volume + eLpNorm (fderiv ℝ g) 2 volume := by
      rw [show (fun x ↦ (D : ℝ) * ‖g x‖) = (D : ℝ) • (fun x ↦ ‖g x‖) from rfl,
        eLpNorm_const_smul, eLpNorm_norm g hgg, eLpNorm_norm _ hfg]
      simp
    _ ≤ (D : ℝ≥0∞) * eLpNorm g 2 volume +
        eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume := by gcongr
    _ ≤ (D + 1 : ℝ≥0) *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
      push_cast
      rw [mul_add]
      apply add_le_add
      · gcongr
        exact le_add_of_nonneg_right (by positivity)
      · exact le_mul_of_one_le_left' (by simp)

/-- Finite-measure Hölder on a fixed compact support converts an L² bound to
an Lᵠ bound (`app:ch_regular:thm:exact-correction`). -/
theorem exists_eLpNorm_le_two_of_support_subset_compact {G : Type*} [NormedAddCommGroup G]
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    {q : ℝ≥0} (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → G,
      AEStronglyMeasurable f volume → Function.support f ⊆ K →
      eLpNorm f q volume ≤ A * eLpNorm f 2 volume := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq : 0 < q)
  have hq2' : (q : ℝ) ≤ 2 := by exact_mod_cast hq2
  have hexp : 0 ≤ 1 / (q : ℝ) - 1 / 2 := by
    have : (2 : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq0 hq2'
    simpa only [one_div, sub_nonneg] using this
  let A := ((volume K) ^ (1 / (q : ℝ) - 1 / 2)).toNNReal
  have hA : (A : ℝ≥0∞) = (volume K) ^ (1 / (q : ℝ) - 1 / 2) :=
    ENNReal.coe_toNNReal (ENNReal.rpow_lt_top_of_nonneg hexp hK.measure_lt_top.ne).ne
  refine ⟨A, fun f hf hs ↦ ?_⟩
  have hq2'' : (q : ℝ≥0∞) ≤ 2 := by exact_mod_cast hq2
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict K) hq2'' hf.restrict
  rw [eLpNorm_restrict_eq_of_support_subset hf hs,
    eLpNorm_restrict_eq_of_support_subset hf hs] at h
  simpa [hA, mul_comm] using h

/-- The smooth local H¹-to-Lᵖ estimate in every dimension at least two,
used in `app:ch_regular:thm:exact-correction`. A fixed bump equal to one on the
ball supplies the compact representative; the input itself needs no support
hypothesis. The H¹ terms follow `app:not:fourier`. -/
theorem exists_smooth_eLpNorm_le_ball_of_two_le_dimension [FiniteDimensional ℝ F]
    (hn : 2 ≤ n) (c : EuclideanSpace ℝ (Fin n))
    {R : ℝ} (hR : 0 < R) :
    ∃ p C : ℝ≥0, 2 < p ∧ 0 < C ∧
      ∀ g : EuclideanSpace ℝ (Fin n) → F,
        ContDiff ℝ ∞ g → MemLp g 2 volume →
        MemLp (iteratedFDeriv ℝ 1 g) 2 volume →
        eLpNorm g p (volume.restrict (ball c R)) ≤ C *
          (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
  obtain ⟨p, q, hp, hq, hq2, hpq⟩ := exists_local_sobolev_exponents hn
  let χ : ContDiffBump c := ⟨R, R + 1, hR, by linarith⟩
  obtain ⟨D, hD⟩ := exists_bump_fderiv_two_bound (F := F) χ
  obtain ⟨A, hA⟩ := exists_eLpNorm_le_two_of_support_subset_compact
    (G := EuclideanSpace ℝ (Fin n) →L[ℝ] F) _ χ.hasCompactSupport hq hq2
  let S : ℝ≥0 := SNormLESNormFDerivOfEqConst F
    (volume : Measure (EuclideanSpace ℝ (Fin n))) q
  refine ⟨p, S * A * D + 1, hp, by positivity, fun g hg _ _ ↦ ?_⟩
  have hχg : ContDiff ℝ ∞ (fun x ↦ χ x • g x) := χ.contDiff.smul hg
  have heq : g =ᵐ[volume.restrict (ball c R)] (fun x ↦ χ x • g x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]
  have hs : Function.support (fderiv ℝ (fun x ↦ χ x • g x)) ⊆
      tsupport (χ : EuclideanSpace ℝ (Fin n) → ℝ) :=
    (support_fderiv_subset ℝ).trans (tsupport_smul_subset_left _ _)
  have hSob : eLpNorm g p (volume.restrict (ball c R)) ≤
      S * eLpNorm (fderiv ℝ (fun x ↦ χ x • g x)) q volume := by
    apply SmallSupport.eLpNorm_le_of_compactRepresentative
      (hχg.of_le (by simp)) χ.hasCompactSupport.smul_right heq hq
    · simpa using (show 0 < n by omega)
    · simpa using hpq
  calc
    _ ≤ S * eLpNorm (fderiv ℝ (fun x ↦ χ x • g x)) q volume := hSob
    _ ≤ S * (A * eLpNorm (fderiv ℝ (fun x ↦ χ x • g x)) 2 volume) := by
      gcongr
      exact hA _ (hχg.continuous_fderiv (by simp)).aestronglyMeasurable hs
    _ ≤ S * (A * (D *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume))) := by
      gcongr
      exact hD g hg
    _ ≤ (S * A * D + 1 : ℝ≥0) *
        (eLpNorm g 2 volume + eLpNorm (iteratedFDeriv ℝ 1 g) 2 volume) := by
      push_cast
      simp only [← mul_assoc]
      gcongr
      exact le_add_of_nonneg_right (by positivity)

end JanetCartan.LocalSobolev
