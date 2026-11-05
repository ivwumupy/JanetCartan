module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.HighFrequency

/-!
# Uniform jets of a fixed radial regularization

For Step 1 of `app:ch_background:prop:bg-frame`, the profile is fixed, smooth,
compactly supported, and constant near zero. The constants below depend only on
this profile and the jet order, never on the regularization radius `R ≥ 1`.
The squared version is the one used by `regularizedCoefficients`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {d : ℕ}

/-- Smoothness at the origin of the fixed radial cutoff used in
`app:ch_background:prop:bg-frame`, Step 1, follows from its constant core. -/
theorem contDiff_radialProfile {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcore : ∀ r : ℝ, 0 ≤ r → r < 1 → χ r = χ 0) :
    ContDiff ℝ ∞ (fun η : Euclidean d ↦ χ ‖η‖) := by
  rw [contDiff_iff_contDiffAt]
  intro η
  by_cases hη : η = 0
  · subst η
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : Euclidean d) zero_lt_one] with y hy
    exact hcore _ (norm_nonneg _) (by simpa using hy)
  · exact hχ.contDiffAt.comp _ (contDiffAt_id.norm ℝ hη)

/-- Compact support of the radial profile is inherited from the fixed scalar
cutoff (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem hasCompactSupport_radialProfile {χ : ℝ → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (fun η : Euclidean d ↦ χ ‖η‖) := by
  obtain ⟨B, _, hB⟩ := hc.exists_pos_le_norm
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Euclidean d) B)
  intro η hη
  apply hB
  simpa only [Real.norm_eq_abs, abs_norm] using
    (le_of_lt (not_le.mp (by simpa using hη)))

/-- Weighted jets of a fixed smooth compact profile are bounded. This is used
only for the fixed cutoff, not as an assumed bound for the normal amplitude.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_weighted_radialProfile_bound {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hcore : ∀ r : ℝ, 0 ≤ r → r < 1 → χ r = χ 0) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : Euclidean d,
      ‖iteratedFDeriv ℝ j (fun y : Euclidean d ↦ χ ‖y‖) η‖ * (1 + ‖η‖) ^ j ≤ C := by
  let f := fun η : Euclidean d ↦ χ ‖η‖
  have hf : ContDiff ℝ ∞ f := contDiff_radialProfile hχ hcore
  have hfc : HasCompactSupport f := hasCompactSupport_radialProfile hc
  have hcont : Continuous (fun η ↦ ‖iteratedFDeriv ℝ j f η‖ * (1 + ‖η‖) ^ j) :=
    (hf.continuous_iteratedFDeriv (by simp)).norm.mul
      ((continuous_const.add continuous_norm).pow j)
  have hcompact : HasCompactSupport
      (fun η ↦ ‖iteratedFDeriv ℝ j f η‖ * (1 + ‖η‖) ^ j) :=
    (hfc.iteratedFDeriv j).norm.mul_right
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcompact
  refine ⟨max 0 C, le_max_left _ _, fun η ↦ ?_⟩
  exact (le_abs_self _).trans ((hC η).trans (le_max_right _ _))

/-- All radial regularizations have symbol jets bounded by constants of the
fixed cutoff alone. The estimate includes the low-frequency region and has no
`R`-dependent low norm. Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_uniform_radialCutoff_symbol_bound {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hcore : ∀ r : ℝ, 0 ≤ r → r < 1 → χ r = χ 0) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ η : Euclidean d,
      ‖iteratedFDeriv ℝ j (fun y : Euclidean d ↦ χ (‖y‖ / R)) η‖ *
        (1 + ‖η‖) ^ j ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_weighted_radialProfile_bound (d := d) hχ hc hcore j
  refine ⟨C, hC, fun R hR η ↦ ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hi : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  have hile : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hn : ‖R⁻¹ • η‖ = R⁻¹ * ‖η‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hi]
  have he : (fun y : Euclidean d ↦ χ (‖y‖ / R)) =
      fun y ↦ (fun z : Euclidean d ↦ χ ‖z‖) (R⁻¹ • y) := by
    funext y
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hRpos, div_eq_mul_inv, mul_comm]
  rw [he, congrFun (iteratedFDeriv_comp_const_smul R⁻¹
    ((contDiff_radialProfile (d := d) hχ hcore).of_le (by simp))) η,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hi _)]
  calc
    _ = ‖iteratedFDeriv ℝ j (fun y : Euclidean d ↦ χ ‖y‖) (R⁻¹ • η)‖ *
        (R⁻¹ * (1 + ‖η‖)) ^ j := by rw [mul_pow]; ring
    _ ≤ ‖iteratedFDeriv ℝ j (fun y : Euclidean d ↦ χ ‖y‖) (R⁻¹ • η)‖ *
        (1 + ‖R⁻¹ • η‖) ^ j := by
      gcongr
      rw [hn]
      nlinarith
    _ ≤ C := hbound _

/-- The cutoff appears squared in the normal, exactly as in
`inputDensity_regularized`. Its uniform constants still depend only on `χ`.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_uniform_squared_radialCutoff_symbol_bound {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hcore : ∀ r : ℝ, 0 ≤ r → r < 1 → χ r = χ 0) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ η : Euclidean d,
      ‖iteratedFDeriv ℝ j (fun y : Euclidean d ↦ χ (‖y‖ / R) ^ 2) η‖ *
        (1 + ‖η‖) ^ j ≤ C := by
  apply exists_uniform_radialCutoff_symbol_bound (hχ.pow 2)
    (hc.comp_left (g := fun r : ℝ ↦ r ^ 2) (by simp))
  intro r hr hr'
  rw [hcore r hr hr']

end JanetCartan.ContinuumNormalReduction.TransportSymbol
