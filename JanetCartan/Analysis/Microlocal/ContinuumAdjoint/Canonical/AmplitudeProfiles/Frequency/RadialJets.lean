module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Frequency.Regularity

/-!
# Uniform scaled jets of the literal half-order radial factor

On bounded scales, compactness bounds the derivatives of the actual smooth
radial factor. On larger scales its high cutoff is identically one near the
unit sphere, giving exact square-root scaling. This proves the endpoint's `W`
profile without assuming radial symbol estimates.
Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow DerivativeKernels

variable {n : ℕ}

private theorem scaled_radial_jet_bound_bounded {R : ℝ} (hR : 0 ≤ R) (hR4 : R ≤ 4)
    (p : AdjointSymbolPoint n) (hp : ‖p.2‖ = 1) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
      halfOrderRadialFactor FixedCutoffs.highFrequency (R • p.2)) p‖ ≤
      cNorm (closedBall (0 : Euclidean (n-1)) 4) i
        (halfOrderRadialFactor FixedCutoffs.highFrequency) * 4 ^ i := by
  let L : AdjointSymbolPoint n →L[ℝ] Euclidean (n-1) :=
    R • ContinuousLinearMap.snd ℝ (AdjointJetPoint n) (Euclidean (n-1))
  have hL : ‖L‖ ≤ 4 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro q
    change ‖R • q.2‖ ≤ 4 * ‖q‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
    exact mul_le_mul hR4 (norm_snd_le q) (norm_nonneg _) (by norm_num)
  change ‖iteratedFDeriv ℝ i
    (halfOrderRadialFactor FixedCutoffs.highFrequency ∘ L) p‖ ≤ _
  rw [L.iteratedFDeriv_comp_right halfOrderRadialFactor_contDiff p (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  have hjet : ‖iteratedFDeriv ℝ i
      (halfOrderRadialFactor FixedCutoffs.highFrequency) (L p)‖ ≤
      cNorm (closedBall (0 : Euclidean (n-1)) 4) i
        (halfOrderRadialFactor FixedCutoffs.highFrequency) := by
    apply norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
      (halfOrderRadialFactor_contDiff.of_le (by simp)) _ le_rfl
    change R • p.2 ∈ closedBall 0 4
    simpa only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hR, hp, mul_one] using hR4
  have hpow : (∏ _ : Fin i, ‖L‖) ≤ (4 : ℝ) ^ i := by
    simpa using pow_le_pow_left₀ (norm_nonneg L) hL i
  exact mul_le_mul hjet hpow (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    (cNorm_nonneg _ _ _)

private theorem scaled_radial_eventuallyEq {R : ℝ} (hR : 4 ≤ R)
    (p : AdjointSymbolPoint n) (hp : ‖p.2‖ = 1) :
    (fun q : AdjointSymbolPoint n ↦ halfOrderRadialFactor FixedCutoffs.highFrequency
      (R • q.2)) =ᶠ[𝓝 p]
      (fun q ↦ (Real.sqrt R / 2) •
        halfOrderRadialFactor FixedCutoffs.highFrequency ((4 : ℝ) • q.2)) := by
  have hRp : 0 ≤ R := by linarith
  have he : ∀ᶠ q : AdjointSymbolPoint n in 𝓝 p, (1/2 : ℝ) < ‖q.2‖ :=
    continuousAt_const.eventually_lt continuous_snd.norm.continuousAt (by rw [hp]; norm_num)
  filter_upwards [he] with q hq
  have h4 : 2 ≤ ‖(4 : ℝ) • q.2‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    linarith
  have hR' : 2 ≤ ‖R • q.2‖ := by
    rw [norm_smul, Real.norm_of_nonneg hRp]
    nlinarith [norm_nonneg q.2]
  dsimp only [halfOrderRadialFactor]
  rw [FixedCutoffs.highFrequency_one hR', FixedCutoffs.highFrequency_one h4]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [one_mul, norm_smul,
    Real.norm_of_nonneg hRp, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    Real.sqrt_mul hRp, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [hs4]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The actual radial profile has uniform scaled jets of every finite order.
In particular it supplies `W` through the required reserve `2*(n+1)` in
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound`
(`app:ch_background:prop:bg-adjoint`). -/
theorem exists_fixed_halfOrderRadialFactor_jet_bounds :
    ∃ W : ℕ → ℝ, (∀ i, 0 ≤ W i) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ p : AdjointSymbolPoint n, ‖p.2‖ = 1 →
        ∀ i, ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
          halfOrderRadialFactor FixedCutoffs.highFrequency (R • p.2)) p‖ ≤
            W i * Real.sqrt R := by
  let W : ℕ → ℝ := fun i ↦ cNorm (closedBall (0 : Euclidean (n-1)) 4) i
    (halfOrderRadialFactor FixedCutoffs.highFrequency) * 4 ^ i
  have hW : ∀ i, 0 ≤ W i := fun i ↦ mul_nonneg (cNorm_nonneg _ _ _) (by positivity)
  refine ⟨W, hW, ?_⟩
  intro R hR p hp i
  by_cases hR4 : R ≤ 4
  · exact (scaled_radial_jet_bound_bounded (zero_le_one.trans hR) hR4 p hp i).trans
      (le_mul_of_one_le_right (hW i) (Real.one_le_sqrt.mpr hR))
  · rw [(scaled_radial_eventuallyEq (le_of_not_ge hR4) p hp).iteratedFDeriv (𝕜 := ℝ) i |>.eq_of_nhds]
    rw [iteratedFDeriv_const_smul_apply'
      ((scaled_halfOrderRadialFactor_contDiff 4).contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))]
    calc
      _ ≤ (Real.sqrt R / 2) * W i := mul_le_mul_of_nonneg_left
        (scaled_radial_jet_bound_bounded (by norm_num) le_rfl p hp i)
        (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      _ ≤ W i * Real.sqrt R := by nlinarith [hW i, Real.sqrt_nonneg R]

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
