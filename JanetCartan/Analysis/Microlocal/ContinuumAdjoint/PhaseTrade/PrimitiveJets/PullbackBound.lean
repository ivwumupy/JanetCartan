module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.PhaseTrade.PrimitiveJets.PullbackBound.Graph
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.OneHigh.Interpolation
public import JanetCartan.Geometry.IsometricEmbedding.Normal.Profile.JetComposition

/-!
# Additive primitive bound for the pulled-back phase gradient

The consumer is the primitive rectangular-input estimate in `PrimitiveJets`,
via `exists_cNorm_transversePhaseInputs_le_gradientPullback`. Baseline-one
interpolation and the partition chain rule give a single additive high budget,
for `app:ch_background:eq:bg-derivative-trade` and
`app:ch_regular_base:lem:buffered-interpolation`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff
namespace JanetCartan.ContinuumAdjoint
open FourierIntegral.NormalOneHigh

/-- The pulled-back phase gradient is bounded by one additive primitive high
budget. The constant is chosen before the phase and carrier, under exactly their
primitive C³ bounds. This includes `k = 0` and uses the fixed reserve three.
Sources: `app:ch_background:eq:bg-derivative-trade` and
`app:ch_regular_base:lem:buffered-interpolation`. -/
theorem exists_cNorm_transversePhaseGradientPullback_le_primitives
    {n p : ℕ} (q₀ : Euclidean n × Euclidean p) {ρ R : ℝ}
    (hρ : 0 < ρ) (a : Euclidean n × Euclidean (n - 1)) (hR : 0 < R)
    {M : ℝ} (hM : 0 ≤ M) (k : ℕ) :
    ∃ C > 0, ∀ (S : Euclidean n → Euclidean (n - 1) → ℝ)
      (ζ : Euclidean p → Euclidean (n - 1)),
      ContDiff ℝ ∞ (Function.uncurry S) → ContDiff ℝ ∞ ζ →
      Set.MapsTo (fun q ↦ (q.1, ζ q.2)) (Metric.closedBall q₀ ρ)
        (Metric.closedBall a R) →
      cNorm (Metric.closedBall a R) 3 (Function.uncurry S) ≤ M →
      cNorm (Metric.closedBall q₀.2 ρ) 3 ζ ≤ M →
      cNorm (Metric.closedBall q₀ ρ) (k + 1) (transversePhaseGradientPullback S ζ) ≤
        C * (1 + cNorm (Metric.closedBall a R) (k + 3) (Function.uncurry S) +
          cNorm (Metric.closedBall q₀.2 ρ) (k + 3) ζ) := by
  let K := Metric.closedBall q₀ ρ
  let Kz := Metric.closedBall q₀.2 ρ
  let T := Metric.closedBall a R
  let s := k + 2
  let F₁ := cNorm K 1 (Prod.fst : Euclidean n × Euclidean p → Euclidean n)
  let Fs := cNorm K s (Prod.fst : Euclidean n × Euclidean p → Euclidean n)
  have hF₁ : 0 ≤ F₁ := cNorm_nonneg _ _ _
  have hFs : 0 ≤ Fs := cNorm_nonneg _ _ _
  let Tg : ℝ := 1 + (s + 1 : ℕ) * (Fs + 1)
  have hTg : 1 ≤ Tg := by
    dsimp [Tg]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (by linarith))
  obtain ⟨A, hA, houter⟩ := exists_primitiveJet_profile_closedBall
    (F := (Euclidean n × Euclidean (n - 1)) →L[ℝ] ℝ)
    a hR isOpen_univ (Set.subset_univ _) (show 2 ≤ s by omega) hM (le_refl (1 : ℝ))
  obtain ⟨B, hB, hinner⟩ := exists_primitiveJet_profile_closedBall
    (F := Euclidean n × Euclidean (n - 1)) q₀ hρ isOpen_univ (Set.subset_univ _)
    (show 2 ≤ s by omega) (show 0 ≤ 2 * (F₁ + M) by positivity) hTg
  let budget := compositionBudget (fun _ ↦ A) (fun _ ↦ B)
  have hbudget (j : ℕ) : 0 ≤ budget j :=
    compositionBudget_nonneg (fun _ ↦ zero_le_one.trans hA)
      (fun _ ↦ zero_le_one.trans hB) j
  let D := M + ∑ j ∈ Finset.range (k + 2), budget j + 1
  have hsum : 0 ≤ ∑ j ∈ Finset.range (k + 2), budget j :=
    Finset.sum_nonneg (fun j _ ↦ hbudget j)
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨(k + 2 : ℕ) * D, mul_pos (by positivity) hD, ?_⟩
  intro S ζ hS hζ hmap hSlow hζlow
  let H := 1 + cNorm T (k + 3) (Function.uncurry S) + cNorm Kz (k + 3) ζ
  have hSH := cNorm_nonneg T (k + 3) (Function.uncurry S)
  have hζH := cNorm_nonneg Kz (k + 3) ζ
  have hH : 1 ≤ H := by dsimp [H]; linarith
  let g := fderiv ℝ (Function.uncurry S)
  let f : Euclidean n × Euclidean p → Euclidean n × Euclidean (n - 1) :=
    fun q ↦ (q.1, ζ q.2)
  have hg : ContDiff ℝ ∞ g := hS.fderiv_right (by simp)
  have hf : ContDiff ℝ ∞ f := contDiff_fst.prodMk (hζ.comp contDiff_snd)
  have hglow : cNorm T 1 g ≤ M :=
    (GeometricProfile.cNorm_fderiv_le T 1 _).trans
      ((cNorm_mono_order (by omega : 1 + 1 ≤ 3)).trans hSlow)
  have hghigh : 1 + cNorm T s g ≤ 1 * H := by
    have hshift := GeometricProfile.cNorm_fderiv_le T s (Function.uncurry S)
    change cNorm T s g ≤ cNorm T (k + 3) (Function.uncurry S) at hshift
    dsimp [H]
    linarith
  have hflow : cNorm K 1 f ≤ 2 * (F₁ + M) := by
    have hb := cNorm_transverseCarrierGraph_le q₀ ρ 1 hζ
    have hz : cNorm Kz 1 ζ ≤ M := (cNorm_mono_order (by omega : 1 ≤ 3)).trans hζlow
    change cNorm K 1 f ≤ (1 + 1 : ℕ) * (F₁ + cNorm Kz 1 ζ) at hb
    norm_num at hb
    linarith
  have hfhigh : 1 + cNorm K s f ≤ Tg * H := by
    have hb := cNorm_transverseCarrierGraph_le q₀ ρ s hζ
    change cNorm K s f ≤ (s + 1 : ℕ) * (Fs + cNorm Kz s ζ) at hb
    have hz : cNorm Kz s ζ ≤ cNorm Kz (k + 3) ζ := cNorm_mono_order (by dsimp [s]; omega)
    have hzH : cNorm Kz s ζ ≤ H := by dsimp [H]; linarith
    have ht : 0 ≤ (s + 1 : ℕ) * Fs := mul_nonneg (by positivity) hFs
    have hmul := mul_le_mul_of_nonneg_left hzH (show 0 ≤ ((s + 1 : ℕ) : ℝ) by positivity)
    have hmul' := mul_le_mul_of_nonneg_left hH ht
    dsimp [Tg]
    nlinarith
  obtain ⟨hgzero, hgprof⟩ := houter g H hg.contDiffOn hH hglow hghigh
  obtain ⟨_, hfprof⟩ := hinner f H hf.contDiffOn hH hflow hfhigh
  have hpoint (j : ℕ) (hj : j ≤ k + 1) (q : Euclidean n × Euclidean p)
      (hq : q ∈ K) : ‖iteratedFDeriv ℝ j (g ∘ f) q‖ ≤ D * H := by
    have hbudgetD : budget j ≤ D := by
      have hjmem : j ∈ Finset.range (k + 2) := Finset.mem_range.mpr (by omega)
      have := Finset.single_le_sum (fun i _ ↦ hbudget i) hjmem
      dsimp [D]
      linarith
    by_cases hj0 : j = 0
    · subst j
      rw [norm_iteratedFDeriv_zero]
      have hb := hgzero (f q) (hmap hq)
      have hMD : M ≤ D := by dsimp [D]; linarith
      exact hb.trans (hMD.trans (le_mul_of_one_le_right hD.le hH))
    · have hjs : j ≤ s := by dsimp [s]; omega
      have hcomp := norm_iteratedFDeriv_comp_le_profile hf.contDiffAt hg.contDiffAt
        (show 1 ≤ j by omega) hjs (lt_of_lt_of_le zero_lt_one hH)
        (fun _ ↦ A) (fun _ ↦ B) (fun _ ↦ zero_le_one.trans hA)
        (hgprof (f q) (hmap hq)) (hfprof q hq)
      have hspos : (0 : ℝ) < s - 1 := by
        have hs : (2 : ℝ) ≤ s := by exact_mod_cast (show 2 ≤ s by omega)
        linarith
      have hθ : ((j : ℝ) - 1) / (s - 1) ≤ 1 :=
        (div_le_one hspos).mpr (sub_le_sub_right (by exact_mod_cast hjs) 1)
      have hpow : H ^ (((j : ℝ) - 1) / (s - 1)) ≤ H :=
        (Real.rpow_le_rpow_of_exponent_le hH hθ).trans_eq (Real.rpow_one H)
      exact hcomp.trans ((mul_le_mul_of_nonneg_left hpow (hbudget j)).trans
        (mul_le_mul_of_nonneg_right hbudgetD (zero_le_one.trans hH)))
  have hb := cNorm_le_sum_of_bounds
    (fun _ _ ↦ mul_nonneg hD.le (zero_le_one.trans hH)) hpoint
  change cNorm K (k + 1) (g ∘ f) ≤ (k + 2 : ℕ) * D * H
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
    Nat.add_assoc] using hb

end JanetCartan.ContinuumAdjoint
