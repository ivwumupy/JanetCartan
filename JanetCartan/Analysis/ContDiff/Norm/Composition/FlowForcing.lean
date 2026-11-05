module

public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.Partitions
public import JanetCartan.Analysis.ContDiff.Norm.Composition.FlowForcing.LocalInterpolation

/-!
# Baseline-one estimates for nonlinear flow forcing

The scalar Faà di Bruno forcing in
`app:ch_regular_base:lem:buffered-interpolation` of paper.tex. Lower jets
are induction inputs, never assumptions on the top forcing or its budget.
The closed-ball results derive their power profiles from actual interpolation,
including when the field and initial map are smooth only on explicit buffered
open neighborhoods. The consuming Hamilton-flow induction must supply the
strictly lower inner-map jet bounds from genuine flow estimates.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace JanetCartan.FlowForcing

open CompositionBounds

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `app:ch_regular_base:lem:buffered-interpolation`: the nonlinear scalar
forcing sum excludes the single-block top variational term. -/
def forcingSum (n : ℕ) (V : F → F) (f : E → F) (x : E) : ℝ :=
  ∑ p : OrderedFinpartition n with 2 ≤ p.length,
    ‖iteratedFDeriv ℝ p.length V (f x)‖ * ∏ i, ‖iteratedFDeriv ℝ (p.partSize i) f x‖

/-- `app:ch_regular_base:lem:buffered-interpolation`: a coefficient depending
only on the interpolation constants and the fixed lower-jet constants. -/
def forcingCoefficient (n : ℕ) (A : ℕ → ℝ) (K L : ℝ) : ℝ :=
  ∑ p : OrderedFinpartition n with 2 ≤ p.length,
    K * ∏ i, (A (p.partSize i) * (1 + K + L))

/-- `app:ch_regular_base:lem:buffered-interpolation`: nonnegativity of the
coefficient for nonnegative induction and interpolation constants. -/
theorem forcingCoefficient_nonneg (n : ℕ) {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) : 0 ≤ forcingCoefficient n A K L := by
  exact Finset.sum_nonneg (fun _ _ ↦ mul_nonneg hK
    (Finset.prod_nonneg (fun i _ ↦ mul_nonneg (hA _) (by positivity))))

/-- `app:ch_regular_base:lem:buffered-interpolation`: assembling supplied
C-norm profiles with lower-jet induction bounds. This intermediate lemma is
conditional on the profiles; the closed-ball theorem below derives them. -/
theorem forcingSum_le_of_cNorm_profiles {n : ℕ} (hn : 2 ≤ n)
    {s : Set E} {t : Set F} (ht : IsCompact t) {V : F → F} {σ f : E → F} {x : E}
    (hV : ∀ y ∈ t, ContDiffAt ℝ ∞ V y) (hx : f x ∈ t)
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {K L : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hVP : ∀ j, 1 ≤ j → j ≤ n → cNorm t j V ≤
      K * (1 + cNorm t n V) ^ (((j : ℝ) - 1) / (n - 1)))
    (hσP : ∀ j, 1 ≤ j → j ≤ n → cNorm s j σ ≤
      L * (1 + cNorm s n σ) ^ (((j : ℝ) - 1) / (n - 1)))
    (hjets : ∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤
      A j * (1 + cNorm t j V + cNorm s j σ)) :
    forcingSum n V f x ≤ forcingCoefficient n A K L *
      (1 + cNorm t n V + cNorm s n σ) := by
  let H := 1 + cNorm t n V + cNorm s n σ
  have hH : 1 ≤ H := by dsimp [H]; linarith [cNorm_nonneg t n V, cNorm_nonneg s n σ]
  have hn' : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hθ (j : ℕ) (hj : 1 ≤ j) : 0 ≤ ((j : ℝ) - 1) / (n - 1) :=
    div_nonneg (sub_nonneg.mpr (by exact_mod_cast hj)) hn'.le
  have hVP' (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      cNorm t j V ≤ K * H ^ (((j : ℝ) - 1) / (n - 1)) := by
    apply (hVP j hj hjn).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hK)
    exact Real.rpow_le_rpow (by linarith [cNorm_nonneg t n V])
      (by dsimp [H]; linarith [cNorm_nonneg s n σ]) (hθ j hj)
  have hσP' (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
      cNorm s j σ ≤ L * H ^ (((j : ℝ) - 1) / (n - 1)) := by
    apply (hσP j hj hjn).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hL)
    exact Real.rpow_le_rpow (by linarith [cNorm_nonneg s n σ])
      (by dsimp [H]; linarith [cNorm_nonneg t n V]) (hθ j hj)
  apply forcing_sum_le_of_power_profiles hn
    (fun j ↦ ‖iteratedFDeriv ℝ j V (f x)‖)
    (fun j ↦ ‖iteratedFDeriv ℝ j f x‖) (fun j ↦ A j * (1 + K + L))
    (lt_of_lt_of_le zero_lt_one hH) (zero_le_one.trans hK) (fun _ ↦ norm_nonneg _) ?_ ?_
  · intro q hq hqn
    apply (norm_iteratedFDeriv_le_cNorm (s := t) (r := q) ?_ le_rfl hx).trans
      (hVP' q (by omega) hqn)
    apply ht.bddAbove_image
    intro y hy
    exact ((hV y hy).continuousAt_iteratedFDeriv (by simp)).norm.continuousWithinAt
  · intro j hj hjn
    apply (hjets j hj hjn).trans
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hA j)
    have hv := hVP' j hj hjn.le
    have hσ := hσP' j hj hjn.le
    have hp := Real.one_le_rpow hH (hθ j hj)
    nlinarith

/-- `app:ch_regular_base:lem:buffered-interpolation`: a uniform baseline-one
bound for scalar nonlinear flow forcing on positive-radius closed parameter
and state balls, for globally smooth field and initial map. The constant is
quantified before both maps and all high norms. Only lower inner-map jets are
assumed. -/
theorem exists_forcingSum_le_closedBall [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) (b : F) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {n : ℕ} (hn : 2 ≤ n) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : F → F) (σ : E → F),
      ContDiff ℝ ∞ V → ContDiff ℝ ∞ σ →
      cNorm (Metric.closedBall b τ) 1 V ≤ M →
      cNorm (Metric.closedBall a ρ) 1 σ ≤ N →
      ∀ (f : E → F) (x : E), f x ∈ Metric.closedBall b τ →
      (∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤
        A j * (1 + cNorm (Metric.closedBall b τ) j V +
          cNorm (Metric.closedBall a ρ) j σ)) →
      forcingSum n V f x ≤ C * (1 + cNorm (Metric.closedBall b τ) n V +
        cNorm (Metric.closedBall a ρ) n σ) := by
  obtain ⟨K, hK, hKb⟩ := exists_uniform_cNorm_baseline_one_profile_closedBall (F := F) b hτ hn hM
  obtain ⟨L, hL, hLb⟩ := exists_uniform_cNorm_baseline_one_profile_closedBall (F := F) a hρ hn hN
  have hC := forcingCoefficient_nonneg n hA (zero_le_one.trans hK) (zero_le_one.trans hL)
  refine ⟨1 + forcingCoefficient n A K L, by linarith, ?_⟩
  intro V σ hV hσ hVM hσN f x hx hjets
  apply (forcingSum_le_of_cNorm_profiles hn (isCompact_closedBall b τ)
    (fun _ _ ↦ hV.contDiffAt) hx hA hK hL (hKb V hV hVM) (hLb σ hσ hσN) hjets).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (by
    linarith [cNorm_nonneg (Metric.closedBall b τ) n V,
      cNorm_nonneg (Metric.closedBall a ρ) n σ])

/-- `app:ch_regular_base:lem:buffered-interpolation`: the uniform baseline-one
bound for scalar nonlinear flow forcing on fixed positive-radius closed balls
inside explicit open smoothness domains. The constant precedes the field,
initial map, inner map, and evaluation point, and is independent of all their
high norms. Both power profiles are derived from localized interpolation.
Only jets of the inner map of orders `1 ≤ j < n` are induction inputs; the
Hamilton-flow induction consuming this estimate must prove those inputs. -/
theorem exists_forcingSum_le_closedBall_on
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (a : E) (b : F) {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ)
    {U : Set E} {W : Set F} (hU : IsOpen U) (hW : IsOpen W)
    (ha : Metric.closedBall a ρ ⊆ U) (hb : Metric.closedBall b τ ⊆ W)
    {n : ℕ} (hn : 2 ≤ n) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : F → F) (σ : E → F),
      ContDiffOn ℝ ∞ V W → ContDiffOn ℝ ∞ σ U →
      cNorm (Metric.closedBall b τ) 1 V ≤ M →
      cNorm (Metric.closedBall a ρ) 1 σ ≤ N →
      ∀ (f : E → F) (x : E), f x ∈ Metric.closedBall b τ →
      (∀ j, 1 ≤ j → j < n → ‖iteratedFDeriv ℝ j f x‖ ≤
        A j * (1 + cNorm (Metric.closedBall b τ) j V +
          cNorm (Metric.closedBall a ρ) j σ)) →
      forcingSum n V f x ≤ C * (1 + cNorm (Metric.closedBall b τ) n V +
        cNorm (Metric.closedBall a ρ) n σ) := by
  obtain ⟨K, hK, hKb⟩ := exists_uniform_cNorm_baseline_one_profile_closedBall_on
    (F := F) b hτ hW hb hn hM
  obtain ⟨L, hL, hLb⟩ := exists_uniform_cNorm_baseline_one_profile_closedBall_on
    (F := F) a hρ hU ha hn hN
  have hC := forcingCoefficient_nonneg n hA (zero_le_one.trans hK) (zero_le_one.trans hL)
  refine ⟨1 + forcingCoefficient n A K L, by linarith, ?_⟩
  intro V σ hV hσ hVM hσN f x hx hjets
  apply (forcingSum_le_of_cNorm_profiles hn (isCompact_closedBall b τ)
    (fun y hy ↦ hV.contDiffAt (hW.mem_nhds (hb hy))) hx hA hK hL
    (hKb V hV hVM) (hLb σ hσ hσN) hjets).trans
  exact mul_le_mul_of_nonneg_right (by linarith) (by
    linarith [cNorm_nonneg (Metric.closedBall b τ) n V,
      cNorm_nonneg (Metric.closedBall a ρ) n σ])

end JanetCartan.FlowForcing
