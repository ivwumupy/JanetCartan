module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Interpolation

/-!
# Additive tame composition for the shifted phase

The consumer is the covector integrand of `app:ch_seed:eq:seed-quotient-integral`.
Both the phase gradient and its carrier substitution vary. Their high norms
must therefore enter additively. The baseline-one interpolation and partition
profile APIs give this estimate on fixed positive-radius buffered balls.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.FullPhaseCharts.InverseEstimates

open FourierIntegral.NormalOneHigh

variable {A B F : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]

/-- Two varying maps have an additive one-high composition estimate under
fixed primitive `C¹` bounds. The constant is chosen before both maps. This is
the composition step for the shifted phase gradient in
`app:ch_seed:eq:seed-quotient-integral`; no quotient or inverse estimate is
assumed. Smoothness is only on the displayed open neighborhoods. -/
theorem exists_cNorm_comp_le_additive_oneHigh
    (a : A) (b : B) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    {U : Set A} {V : Set B} (hU : IsOpen U) (hV : IsOpen V)
    (hballU : Metric.closedBall a ρ ⊆ U) (hballV : Metric.closedBall b σ ⊆ V)
    {k : ℕ} (hk : 2 ≤ k) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : A → B) (g : B → F),
      ContDiffOn ℝ ∞ f U → ContDiffOn ℝ ∞ g V →
      MapsTo f (Metric.closedBall a ρ) (Metric.closedBall b σ) →
      cNorm (Metric.closedBall a ρ) 1 f ≤ M →
      cNorm (Metric.closedBall b σ) 1 g ≤ N →
      cNorm (Metric.closedBall a ρ) k (g ∘ f) ≤
        C * (1 + cNorm (Metric.closedBall a ρ) k f +
          cNorm (Metric.closedBall b σ) k g) := by
  obtain ⟨Kf, hKf, hpf⟩ := exists_primitiveJet_profile_closedBall
    (F := B) a hρ hU hballU hk hM (T := 1) le_rfl
  obtain ⟨Kg, hKg, hpg⟩ := exists_primitiveJet_profile_closedBall
    (F := F) b hσ hV hballV hk hN (T := 1) le_rfl
  let D : ℕ → ℝ := fun j ↦ compositionBudget (fun _ ↦ Kg) (fun _ ↦ Kf) j
  have hD (j : ℕ) : 0 ≤ D j :=
    compositionBudget_nonneg (fun _ ↦ zero_le_one.trans hKg)
      (fun _ ↦ zero_le_one.trans hKf) j
  let C := 1 + ∑ j ∈ Finset.range (k + 1), (N + D j)
  have hC : 0 < C := by
    have := Finset.sum_nonneg (s := Finset.range (k + 1))
      (fun j _ ↦ add_nonneg hN (hD j))
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hmap hfM hgN
  let H := 1 + cNorm (Metric.closedBall a ρ) k f + cNorm (Metric.closedBall b σ) k g
  have hH : 1 ≤ H := by
    dsimp [H]
    linarith [cNorm_nonneg (Metric.closedBall a ρ) k f,
      cNorm_nonneg (Metric.closedBall b σ) k g]
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hfhigh : 1 + cNorm (Metric.closedBall a ρ) k f ≤ 1 * H := by
    dsimp [H]
    linarith [cNorm_nonneg (Metric.closedBall b σ) k g]
  have hghigh : 1 + cNorm (Metric.closedBall b σ) k g ≤ 1 * H := by
    dsimp [H]
    linarith [cNorm_nonneg (Metric.closedBall a ρ) k f]
  obtain ⟨_, hfj⟩ := hpf f H hf hH hfM hfhigh
  obtain ⟨hgval, hgj⟩ := hpg g H hg hH hgN hghigh
  have hbound : ∀ j ≤ k, ∀ x ∈ Metric.closedBall a ρ,
      ‖iteratedFDeriv ℝ j (g ∘ f) x‖ ≤ (N + D j) * H := by
    intro j hj x hx
    by_cases hj0 : j = 0
    · subst j
      simp only [norm_iteratedFDeriv_zero, Function.comp_apply]
      exact (hgval (f x) (hmap hx)).trans
        ((le_mul_of_one_le_right hN hH).trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hD 0)) hHpos.le))
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hp := norm_iteratedFDeriv_comp_le_profile
      (hf.contDiffAt (hU.mem_nhds (hballU hx)))
      (hg.contDiffAt (hV.mem_nhds (hballV (hmap hx))))
      hj1 hj hHpos (fun _ ↦ Kg) (fun _ ↦ Kf)
      (fun _ ↦ zero_le_one.trans hKg)
      (hgj (f x) (hmap hx)) (hfj x hx)
    have hkpos : (0 : ℝ) < k - 1 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have he : ((j : ℝ) - 1) / (k - 1) ≤ 1 :=
      (div_le_one hkpos).mpr (sub_le_sub_right (by exact_mod_cast hj) 1)
    apply hp.trans
    calc
      _ ≤ D j * H := mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow_of_exponent_le hH he).trans_eq (Real.rpow_one H)) (hD j)
      _ ≤ (N + D j) * H := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hN) hHpos.le
  apply (cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (add_nonneg hN (hD j)) hHpos.le) hbound).trans
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hHpos.le

end JanetCartan.FullPhaseCharts.InverseEstimates
