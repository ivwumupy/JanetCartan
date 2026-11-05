module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.RescaledCutoffs.ScalarJets

/-!
# Uniform dilation bounds from the original high-mask norms

For `app:ch_osc:prop:osc-normal`, Step 4', the primitive-density producer
needs bounds and differences for `h(t r)`, uniformly in `t ≥ 1`. The norms
below are measured on the existing high-mask chart, which contains the fixed
transition interval `[1,2]`. Common plateaus make the difference vanish off
that interval. No norm of a rescaled mask is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
open ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

private theorem rescaled_mask_jet_le
    (D : PrimitiveNormChart ℝ) (hD : Icc (1 : ℝ) 2 ⊆ D.carrier)
    {ε : ℝ} (hε : 0 < ε) (s : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {lo hi : ℝ} (hlo : ∀ x, x ≤ 1 → f x = lo) (hhi : ∀ x, 2 ≤ x → f x = hi)
    {t r : ℝ} (ht : 1 ≤ t) (hr : ε ≤ r) {j : ℕ} (hj : j ≤ s) :
    ‖iteratedFDeriv ℝ j (fun y ↦ f (t * y)) r‖ ≤
      max 1 (2 / ε) ^ s * (cNorm D.carrier s f + |lo| + |hi|) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hC : 1 ≤ max 1 (2 / ε) ^ s := one_le_pow₀ (le_max_left _ _)
  have hN := cNorm_nonneg D.carrier s f
  have he : ‖iteratedFDeriv ℝ j (fun y ↦ f (t * y)) r‖ =
      t ^ j * ‖iteratedFDeriv ℝ j f (t * r)‖ := by
    have hd := congrFun (iteratedFDeriv_comp_const_smul (i := j) t (hf.of_le (by simp))) r
    simpa only [smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg ht0 j)] using congrArg norm hd
  rw [he]
  have hconst (c : ℝ) (hc : f =ᶠ[𝓝 (t * r)] (fun _ ↦ c))
      (hcle : |c| ≤ cNorm D.carrier s f + |lo| + |hi|) :
      t ^ j * ‖iteratedFDeriv ℝ j f (t * r)‖ ≤
        max 1 (2 / ε) ^ s * (cNorm D.carrier s f + |lo| + |hi|) := by
    rw [(hc.iteratedFDeriv ℝ j).eq_of_nhds]
    by_cases hj0 : j = 0
    · subst j
      simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact hcle.trans (le_mul_of_one_le_left (by positivity) hC)
    · simp only [iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, norm_zero, mul_zero]
      positivity
  by_cases hlow : t * r < 1
  · apply hconst lo _ (by linarith [abs_nonneg hi])
    filter_upwards [Iio_mem_nhds hlow] with y hy
    exact hlo y hy.le
  by_cases hhigh : 2 < t * r
  · apply hconst hi _ (by linarith [abs_nonneg lo])
    filter_upwards [Ioi_mem_nhds hhigh] with y hy
    exact hhi y hy.le
  have hp : t * r ∈ D.carrier := hD ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩
  have hjet := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall D.center D.radius)
    (hf.of_le (by simp)) hp hj
  change ‖iteratedFDeriv ℝ j f (t * r)‖ ≤ cNorm D.carrier s f at hjet
  have htε : t ≤ 2 / ε := (le_div_iff₀ hε).mpr
    ((mul_le_mul_of_nonneg_left hr ht0).trans (le_of_not_gt hhigh))
  have hpow : t ^ j ≤ max 1 (2 / ε) ^ s :=
    (pow_le_pow_left₀ ht0 (htε.trans (le_max_right _ _)) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  exact (mul_le_mul hpow hjet (norm_nonneg _) (by positivity)).trans
    (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg lo, abs_nonneg hi]) (by positivity))

/-- The existing primitive high-mask norm controls all finite norms of its
dilations on any fixed positive radial set. The constant precedes the varying
mask, dilation and norm budget. Consumer: substituted primitive density in
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_rescaledHigh_cNorm_bound_of_primitive
    (D : CoefficientNormCharts n) (hD : Icc (1 : ℝ) 2 ⊆ D.high.carrier)
    {K : Set ℝ} {ε : ℝ} (hε : 0 < ε) (hK : ∀ r ∈ K, ε ≤ r) (s : ℕ) :
    ∃ C > 0, ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f →
      (∀ r, r ≤ 1 → f r = 0) → (∀ r, 2 ≤ r → f r = 1) →
      ∀ t : ℝ, 1 ≤ t → cNorm K s (fun r ↦ f (t * r)) ≤
        C * (1 + cNorm D.high.carrier s f) := by
  let C := ((s + 1 : ℕ) : ℝ) * max 1 (2 / ε) ^ s
  refine ⟨C, mul_pos (by positivity) (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _), ?_⟩
  intro f hf hz ho t ht
  have hn := cNorm_nonneg D.high.carrier s f
  have hb := cNorm_le_sum_of_bounds (s := K) (r := s)
    (C := fun _ ↦ max 1 (2 / ε) ^ s * (1 + cNorm D.high.carrier s f))
    (fun _ _ ↦ by positivity) (fun j hj r hr ↦ by
      simpa [add_comm] using rescaled_mask_jet_le D.high hD hε s hf hz ho ht (hK r hr) hj)
  simpa [C, Finset.sum_const, nsmul_eq_mul, mul_assoc] using hb

/-- Common zero and one plateaus give a uniform Lipschitz bound for rescaled
high-mask differences from the original norm on `D.high.carrier`. In particular
an input bound `B*d` remains linear in `d`. Consumer: the shell-density
difference producer for `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_rescaledHigh_cNorm_sub_bound_of_primitive
    (D : CoefficientNormCharts n) (hD : Icc (1 : ℝ) 2 ⊆ D.high.carrier)
    {K : Set ℝ} {ε : ℝ} (hε : 0 < ε) (hK : ∀ r ∈ K, ε ≤ r) (s : ℕ) :
    ∃ C > 0, ∀ (f g : ℝ → ℝ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      (∀ r, r ≤ 1 → f r = 0 ∧ g r = 0) →
      (∀ r, 2 ≤ r → f r = 1 ∧ g r = 1) →
      ∀ t : ℝ, 1 ≤ t → cNorm K s (fun r ↦ f (t * r) - g (t * r)) ≤
        C * cNorm D.high.carrier s (f - g) := by
  let C := ((s + 1 : ℕ) : ℝ) * max 1 (2 / ε) ^ s
  refine ⟨C, mul_pos (by positivity) (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _), ?_⟩
  intro f g hf hg hz ho t ht
  have hn := cNorm_nonneg D.high.carrier s (f - g)
  have hlo : ∀ r, r ≤ 1 → (f - g) r = 0 := by intro r hr; simp [(hz r hr).1, (hz r hr).2]
  have hhi : ∀ r, 2 ≤ r → (f - g) r = 0 := by intro r hr; simp [(ho r hr).1, (ho r hr).2]
  have hb := cNorm_le_sum_of_bounds (s := K) (r := s)
    (C := fun _ ↦ max 1 (2 / ε) ^ s * cNorm D.high.carrier s (f - g))
    (fun _ _ ↦ by positivity) (fun j hj r hr ↦ by
      simpa only [abs_zero, add_zero] using
        rescaled_mask_jet_le D.high hD hε s (f := f - g)
          (hf.sub hg) hlo hhi ht (hK r hr) hj)
  simpa [C, Finset.sum_const, nsmul_eq_mul, mul_assoc] using hb

end JanetCartan.ContinuumNormal.CarrierVariation.AmplitudeDifference
