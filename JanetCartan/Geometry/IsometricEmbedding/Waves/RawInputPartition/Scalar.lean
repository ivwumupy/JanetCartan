module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# The fixed scalar dyadic square partition

For `app:ch_waves:thm:individual` and `app:ch_waves:eq:sampling-prefix-normal`,
`bandProfile (ρ / dyadicScale j)` has support in `[κⱼ, 4κⱼ]`, where
`κⱼ = 2^j / 2`. The prefix through `j < J` has plateau `κⱼ` and outer
radius `2κⱼ`. Its square agrees with the band square sum at every `ρ ≥ 1`,
including the whole transition of the unchanged floor-one high-pass.
The continuous-cutoff rounding and Hilbert refinement are separate obligations.
-/

@[expose] public noncomputable section

namespace JanetCartan.RawInputPartition

/-- Fixed smooth angle for the radial masks in `app:ch_waves:thm:individual`. -/
def transitionAngle (t : ℝ) : ℝ := Real.pi / 2 * Real.smoothTransition (t - 1)

/-- The smooth scalar band in `app:ch_waves:thm:individual`. -/
def bandProfile (t : ℝ) : ℝ :=
  Real.sin (transitionAngle t) * Real.cos (transitionAngle (t / 2))

/-- The fixed band scales start at one half, so that the square partition
covers the complete floor-one high-pass (`app:ch_background:defn:bg-row`). -/
def dyadicScale (j : ℕ) : ℝ := (2 : ℝ) ^ j / 2

/-- Band label `j`, never relabelled when the prefix changes
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def scalarBand (j : ℕ) (ρ : ℝ) : ℝ := bandProfile (ρ / dyadicScale j)

/-- The low-pass mask for labels `j < J`. Its square agrees with their square
sum on the floor-one high-pass (`app:ch_background:defn:bg-mixed`). -/
def scalarPrefix (J : ℕ) (ρ : ℝ) : ℝ :=
  Real.cos (transitionAngle (ρ / dyadicScale J))

/-- The transition is flat below one (`app:ch_waves:thm:individual`). -/
theorem transitionAngle_eq_zero {t : ℝ} (ht : t ≤ 1) : transitionAngle t = 0 := by
  simp [transitionAngle, Real.smoothTransition.zero_of_nonpos (by linarith : t - 1 ≤ 0)]

/-- The transition is flat above two (`app:ch_waves:thm:individual`). -/
theorem transitionAngle_eq_pi_div_two {t : ℝ} (ht : 2 ≤ t) :
    transitionAngle t = Real.pi / 2 := by
  simp [transitionAngle, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t - 1)]

/-- Range of the fixed angle (`app:ch_waves:thm:individual`). -/
theorem transitionAngle_mem (t : ℝ) : transitionAngle t ∈ Set.Icc 0 (Real.pi / 2) := by
  constructor
  · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg _)
  · simpa [transitionAngle] using mul_le_mul_of_nonneg_left
      (Real.smoothTransition.le_one (t - 1)) (by positivity : 0 ≤ Real.pi / 2)

/-- Smoothness of the fixed angle (`app:ch_waves:thm:individual`). -/
theorem contDiff_transitionAngle {r : ℕ∞} : ContDiff ℝ r transitionAngle := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

/-- Smoothness of the scalar band (`app:ch_waves:thm:individual`). -/
theorem contDiff_bandProfile {r : ℕ∞} : ContDiff ℝ r bandProfile := by
  exact contDiff_transitionAngle.sin.mul
    (contDiff_transitionAngle.comp (contDiff_id.div_const 2)).cos

/-- The band is zero below its inner endpoint (`app:ch_waves:thm:individual`). -/
theorem bandProfile_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) : bandProfile t = 0 := by
  simp [bandProfile, transitionAngle_eq_zero ht]

/-- The band is zero above its outer endpoint (`app:ch_waves:thm:individual`). -/
theorem bandProfile_eq_zero_of_four_le {t : ℝ} (ht : 4 ≤ t) : bandProfile t = 0 := by
  simp [bandProfile, transitionAngle_eq_pi_div_two (by linarith : 2 ≤ t / 2)]

/-- Nonnegative contraction masks (`app:ch_waves:thm:individual`). -/
theorem bandProfile_mem (t : ℝ) : bandProfile t ∈ Set.Icc 0 1 := by
  have hs : 0 ≤ Real.sin (transitionAngle t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (transitionAngle_mem t).1
      ((transitionAngle_mem t).2.trans (by linarith [Real.pi_pos]))
  have hc : 0 ≤ Real.cos (transitionAngle (t / 2)) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [(transitionAngle_mem (t / 2)).1, Real.pi_pos],
      (transitionAngle_mem (t / 2)).2⟩
  exact ⟨mul_nonneg hs hc,
    (mul_le_mul_of_nonneg_right (Real.sin_le_one _) hc).trans (by simpa using Real.cos_le_one _)⟩

/-- The key exact telescoping identity; no partition identity is assumed
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem bandProfile_sq (t : ℝ) : bandProfile t ^ 2 =
    Real.sin (transitionAngle t) ^ 2 - Real.sin (transitionAngle (t / 2)) ^ 2 := by
  by_cases ht : t ≤ 2
  · have hz := transitionAngle_eq_zero (show t / 2 ≤ 1 by linarith)
    simp [bandProfile, hz]
  · have ho := transitionAngle_eq_pi_div_two (le_of_not_ge ht)
    have htrig := Real.sin_sq_add_cos_sq (transitionAngle (t / 2))
    simp only [bandProfile, ho, Real.sin_pi_div_two, one_mul]
    linarith

/-- Positivity of every fixed dyadic scale (`app:ch_waves:thm:individual`). -/
theorem dyadicScale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

/-- Exact successor indexing (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicScale_succ (j : ℕ) : dyadicScale (j + 1) = 2 * dyadicScale j := by
  simp only [dyadicScale, pow_succ]
  ring

/-- Exact band-square difference (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem scalarBand_sq (j : ℕ) (ρ : ℝ) : scalarBand j ρ ^ 2 =
    Real.sin (transitionAngle (ρ / dyadicScale j)) ^ 2 -
      Real.sin (transitionAngle (ρ / dyadicScale (j + 1))) ^ 2 := by
  rw [scalarBand, bandProfile_sq, dyadicScale_succ, div_div, mul_comm 2]

/-- Finite telescoping with the literal bottom scale one half
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem sum_scalarBand_sq (J : ℕ) (ρ : ℝ) :
    ∑ j ∈ Finset.range J, scalarBand j ρ ^ 2 =
      Real.sin (transitionAngle (2 * ρ)) ^ 2 -
        Real.sin (transitionAngle (ρ / dyadicScale J)) ^ 2 := by
  induction J with
  | zero => simp [dyadicScale, mul_comm]
  | succ J ih => rw [Finset.sum_range_succ, ih, scalarBand_sq]; ring

/-- Exact partition on the entire floor-one high-pass, not just above two
(`app:ch_background:defn:bg-mixed`). -/
theorem sum_scalarBand_sq_eq_prefix_sq (J : ℕ) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∑ j ∈ Finset.range J, scalarBand j ρ ^ 2 = scalarPrefix J ρ ^ 2 := by
  rw [sum_scalarBand_sq, transitionAngle_eq_pi_div_two (by linarith : 2 ≤ 2 * ρ)]
  have htrig := Real.sin_sq_add_cos_sq (transitionAngle (ρ / dyadicScale J))
  simp only [Real.sin_pi_div_two, one_pow, scalarPrefix]
  linarith

/-- Every prefix is a nonnegative contraction (`app:ch_background:defn:bg-mixed`). -/
theorem scalarPrefix_mem (J : ℕ) (ρ : ℝ) : scalarPrefix J ρ ∈ Set.Icc 0 1 := by
  exact ⟨Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [(transitionAngle_mem (ρ / dyadicScale J)).1, Real.pi_pos],
      (transitionAngle_mem _).2⟩, Real.cos_le_one _⟩

/-- The exact prefix plateau, with no change of labels
(`app:ch_background:defn:bg-mixed`). -/
theorem scalarPrefix_eq_one {J : ℕ} {ρ : ℝ} (hρ : ρ ≤ dyadicScale J) :
    scalarPrefix J ρ = 1 := by
  have ht : ρ / dyadicScale J ≤ 1 := (div_le_one (dyadicScale_pos J)).mpr hρ
  simp [scalarPrefix, transitionAngle_eq_zero ht]

/-- The exact prefix outer endpoint (`app:ch_background:defn:bg-mixed`). -/
theorem scalarPrefix_eq_zero {J : ℕ} {ρ : ℝ} (hρ : 2 * dyadicScale J ≤ ρ) :
    scalarPrefix J ρ = 0 := by
  have ht : 2 ≤ ρ / dyadicScale J := (le_div_iff₀ (dyadicScale_pos J)).mpr hρ
  simp [scalarPrefix, transitionAngle_eq_pi_div_two ht]

/-- The prefix square sum is exactly one on its high-pass plateau
(`app:ch_background:defn:bg-mixed`). -/
theorem sum_scalarBand_sq_eq_one {J : ℕ} {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hJ : ρ ≤ dyadicScale J) : ∑ j ∈ Finset.range J, scalarBand j ρ ^ 2 = 1 := by
  rw [sum_scalarBand_sq_eq_prefix_sq J hρ, scalarPrefix_eq_one hJ, one_pow]

/-- Literal support of each band (`app:ch_waves:thm:individual`). -/
theorem scalarBand_eq_zero_of_le {j : ℕ} {ρ : ℝ} (hρ : ρ ≤ dyadicScale j) :
    scalarBand j ρ = 0 :=
  bandProfile_eq_zero_of_le_one ((div_le_one (dyadicScale_pos j)).mpr hρ)

/-- Literal outer support of each band (`app:ch_waves:thm:individual`). -/
theorem scalarBand_eq_zero_of_ge {j : ℕ} {ρ : ℝ} (hρ : 4 * dyadicScale j ≤ ρ) :
    scalarBand j ρ = 0 :=
  bandProfile_eq_zero_of_four_le ((le_div_iff₀ (dyadicScale_pos j)).mpr hρ)

/-- The band labels strictly increase (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem dyadicScale_strictMono : StrictMono dyadicScale := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [dyadicScale_succ]
  linarith [dyadicScale_pos j]

/-- Bands with two or more intervening scale steps do not overlap
(`app:ch_waves:thm:individual`). -/
theorem scalarBand_nonzero_labels {i j : ℕ} {ρ : ℝ}
    (hi : scalarBand i ρ ≠ 0) (hj : scalarBand j ρ ≠ 0) : j ≤ i + 1 := by
  have hiρ : ρ < 4 * dyadicScale i := lt_of_not_ge (fun h ↦ hi (scalarBand_eq_zero_of_ge h))
  have hjρ : dyadicScale j < ρ := lt_of_not_ge (fun h ↦ hj (scalarBand_eq_zero_of_le h))
  by_contra h
  have he : dyadicScale (i + 2) ≤ dyadicScale j :=
    dyadicScale_strictMono.monotone (by omega)
  rw [show i + 2 = (i + 1) + 1 by omega, dyadicScale_succ, dyadicScale_succ] at he
  linarith

/-- Uniform overlap bound two, independent of the ceiling and accuracy
(`app:ch_waves:thm:individual`). -/
theorem scalarBand_overlap_card_le (s : Finset ℕ) (ρ : ℝ) :
    (s.filter (fun j ↦ scalarBand j ρ ≠ 0)).card ≤ 2 := by
  classical
  let t := s.filter (fun j ↦ scalarBand j ρ ≠ 0)
  change t.card ≤ 2
  by_cases ht : t.Nonempty
  · let i := t.min' ht
    have hi : scalarBand i ρ ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem t ht)).2
    have hsub : t ⊆ {i, i + 1} := by
      intro j hj
      have hle : i ≤ j := Finset.min'_le t j hj
      have hge := scalarBand_nonzero_labels hi (Finset.mem_filter.mp hj).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Finset.not_nonempty_iff_eq_empty.mp ht]

/-- The given high-pass multiplier is preserved literally; its only input
here is vanishing below the manuscript's floor one
(`app:ch_background:defn:bg-row`, `app:ch_background:defn:bg-mixed`). -/
theorem highPass_mul_sum_scalarBand_sq (χ : ℝ → ℝ)
    (hχ : ∀ ρ ≤ 1, χ ρ = 0) (J : ℕ) (ρ : ℝ) :
    χ ρ * (∑ j ∈ Finset.range J, scalarBand j ρ ^ 2) = χ ρ * scalarPrefix J ρ ^ 2 := by
  by_cases hρ : ρ ≤ 1
  · simp [hχ ρ hρ]
  · rw [sum_scalarBand_sq_eq_prefix_sq J (le_of_not_ge hρ)]

end JanetCartan.RawInputPartition
