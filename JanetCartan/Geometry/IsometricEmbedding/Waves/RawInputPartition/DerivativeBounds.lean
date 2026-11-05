module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputPartition.Radial

/-!
# Uniform rescaled derivatives of the actual radial masks

The fixed profiles are the already constructed masks with label `1`, whose
dyadic scale is one. Compact support and global smoothness bound all of their
derivatives through any prescribed finite order. Exact dilation identities
then give bounds independent of the band label and prefix ceiling.

These are the radial-mask seminorms used in `app:ch_waves:thm:individual` and
`app:ch_waves:eq:B-bounds`. The given angular detector and high-pass require
their own estimates when multiplied into the raw-primary masks.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawInputPartition

/-- Compact support of the constructed band, used to bound the fixed profile
in `app:ch_waves:eq:B-bounds`. -/
theorem hasCompactSupport_radialBand (n j : ℕ) : HasCompactSupport (radialBand n j) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : Euclidean (n - 1)) (4 * dyadicScale j))
  intro η hη
  exact scalarBand_eq_zero_of_ge
    (le_of_lt (show 4 * dyadicScale j < ‖η‖ by simpa using hη))

/-- Compact support of the unchanged low-pass prefix, for the cutoff calculus
in `app:ch_background:defn:bg-mixed`. -/
theorem hasCompactSupport_radialPrefix (n J : ℕ) : HasCompactSupport (radialPrefix n J) := by
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : Euclidean (n - 1)) (2 * dyadicScale J))
  intro η hη
  exact scalarPrefix_eq_zero
    (le_of_lt (show 2 * dyadicScale J < ‖η‖ by simpa using hη))

/-- Every actual band is a dilation of the fixed unit-scale band
(`app:ch_waves:thm:individual`). -/
theorem radialBand_eq_rescale (n j : ℕ) :
    radialBand n j = fun η ↦ radialBand n 1 ((dyadicScale j)⁻¹ • η) := by
  funext η
  simp [radialBand, scalarBand, norm_smul, div_eq_mul_inv, dyadicScale, mul_comm]

/-- Every unchanged prefix is a dilation of its fixed unit-scale profile
(`app:ch_background:defn:bg-mixed`). -/
theorem radialPrefix_eq_rescale (n J : ℕ) :
    radialPrefix n J = fun η ↦ radialPrefix n 1 ((dyadicScale J)⁻¹ • η) := by
  funext η
  simp [radialPrefix, scalarPrefix, norm_smul, div_eq_mul_inv, dyadicScale, mul_comm]

/-- Exact derivative scaling of the actual bands, including at zero and at
the annular endpoints (`app:ch_waves:eq:B-bounds`). -/
theorem iteratedFDeriv_radialBand_rescale (n j m : ℕ) (η : Euclidean (n - 1)) :
    iteratedFDeriv ℝ m (radialBand n j) η =
      (dyadicScale j)⁻¹ ^ m •
        iteratedFDeriv ℝ m (radialBand n 1) ((dyadicScale j)⁻¹ • η) := by
  conv_lhs => rw [radialBand_eq_rescale n j]
  exact congrFun (iteratedFDeriv_comp_const_smul _ (contDiff_radialBand n 1)) η

/-- Exact derivative scaling of the unchanged prefixes
(`app:ch_background:defn:bg-mixed`). -/
theorem iteratedFDeriv_radialPrefix_rescale (n J m : ℕ) (η : Euclidean (n - 1)) :
    iteratedFDeriv ℝ m (radialPrefix n J) η =
      (dyadicScale J)⁻¹ ^ m •
        iteratedFDeriv ℝ m (radialPrefix n 1) ((dyadicScale J)⁻¹ • η) := by
  conv_lhs => rw [radialPrefix_eq_rescale n J]
  exact congrFun (iteratedFDeriv_comp_const_smul _ (contDiff_radialPrefix n 1)) η

/-- Exact scaling of the band derivative norms for the rescaled seminorms in
`app:ch_waves:eq:B-bounds`. -/
theorem norm_iteratedFDeriv_radialBand_rescale (n j m : ℕ) (η : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (radialBand n j) η‖ =
      (dyadicScale j)⁻¹ ^ m *
        ‖iteratedFDeriv ℝ m (radialBand n 1) ((dyadicScale j)⁻¹ • η)‖ := by
  rw [iteratedFDeriv_radialBand_rescale, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (dyadicScale_pos j).le) m)]

/-- Exact scaling of the unchanged prefix derivative norms for
`app:ch_background:defn:bg-mixed`. -/
theorem norm_iteratedFDeriv_radialPrefix_rescale (n J m : ℕ) (η : Euclidean (n - 1)) :
    ‖iteratedFDeriv ℝ m (radialPrefix n J) η‖ =
      (dyadicScale J)⁻¹ ^ m *
        ‖iteratedFDeriv ℝ m (radialPrefix n 1) ((dyadicScale J)⁻¹ • η)‖ := by
  rw [iteratedFDeriv_radialPrefix_rescale, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (dyadicScale_pos J).le) m)]

/-- A finite nonnegative constant bounds every rescaled band derivative
through order `m`, uniformly over all labels and frequencies. The constant is
obtained from compact support and continuity of the fixed profile derivatives,
as required for the masks in `app:ch_waves:eq:B-bounds`. -/
theorem exists_uniform_radialBand_derivative_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ m, ∀ j (η : Euclidean (n - 1)),
      ‖iteratedFDeriv ℝ k (radialBand n j) η‖ ≤ C * (dyadicScale j)⁻¹ ^ k := by
  obtain ⟨C, hC, hbound⟩ := (hasCompactSupport_radialBand n 1).exists_bound_iteratedFDeriv
    (contDiff_radialBand n 1) m
  refine ⟨C, hC, fun k hk j η ↦ ?_⟩
  rw [norm_iteratedFDeriv_radialBand_rescale, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound k hk _)
    (pow_nonneg (inv_nonneg.mpr (dyadicScale_pos j).le) k)

/-- The unchanged prefixes have uniform rescaled derivatives through every
finite order, with a constant independent of the prefix ceiling. This supplies
the prefix cutoff calculus in `app:ch_background:defn:bg-mixed` by the same
compact-profile argument as `app:ch_waves:eq:B-bounds`. -/
theorem exists_uniform_radialPrefix_derivative_bound (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ≤ m, ∀ J (η : Euclidean (n - 1)),
      ‖iteratedFDeriv ℝ k (radialPrefix n J) η‖ ≤ C * (dyadicScale J)⁻¹ ^ k := by
  obtain ⟨C, hC, hbound⟩ := (hasCompactSupport_radialPrefix n 1).exists_bound_iteratedFDeriv
    (contDiff_radialPrefix n 1) m
  refine ⟨C, hC, fun k hk J η ↦ ?_⟩
  rw [norm_iteratedFDeriv_radialPrefix_rescale, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound k hk _)
    (pow_nonneg (inv_nonneg.mpr (dyadicScale_pos J).le) k)

end JanetCartan.RawInputPartition
