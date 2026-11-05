module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Normalization

/-!
# Whole-image inverse ranges on normalized shells

The two-sided frequency comparison and the original source collar give one
fixed normalized annulus for all whole-image shells. The collar handles the
zeroth and first shells, where the Japanese bracket does not give a uniform
positive normalized frequency. This is the range input for the normalized
jets in `app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Fixed source annuli for all whole-image dyadic shells, including both low
shells. The radii precede the phase and shell index and depend only on the
original collar and the two frequency constants. This supplies the range
hypothesis for `NormalAmplitudeShellInputs` in actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_normalizedWholeImageInverse_shell_range
    {ε F C : ℝ} (hε : 0 < ε) (hF : 0 < F) (hC : 0 < C) :
    ∃ a > 0, ∃ b > a, ∀ (S : E → E → ℝ) (X D : Set E),
      (∀ u ∈ D, ε < ‖u‖) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * ‖u‖ ∧
        ‖u‖ ≤ C * ‖averagedGradient S x y u‖) →
      ∀ j : ℕ, MapsTo
        (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^j) (wholeImageInverse S D)))
        (normalDyadicShell (bufferedNormalDomain X D S) j)
        (X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b)) := by
  let a := min (ε / 4) (1 / (8 * F))
  let b := max (a + 1) (4 * C + 1)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hab : a < b := (by linarith : a < a + 1).trans_le (le_max_left _ _)
  refine ⟨a, ha, b, hab, ?_⟩
  intro S X D hcollar hfreq j q hq
  let ρ : ℝ := (2 : ℝ)^j
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hqmem : q.1 ∈ X ∧ q.2.1 ∈ X ∧ ρ • q.2.2 ∈ averagedGradient S q.1 q.2.1 '' D :=
    hq.1
  let u := wholeImageInverse S D q.1 q.2.1 (ρ • q.2.2)
  have hu : u ∈ D := wholeImageInverse_mem hqmem.2.2
  have he : averagedGradient S q.1 q.2.1 u = ρ • q.2.2 :=
    averagedGradient_wholeImageInverse hqmem.2.2
  obtain ⟨hforward, hreverse⟩ := hfreq q.1 hqmem.1 q.2.1 hqmem.2.1 u hu
  rw [he] at hforward hreverse
  have hshell : ρ / 2 < Real.sqrt (1 + ‖ρ • q.2.2‖ ^ 2) ∧
      Real.sqrt (1 + ‖ρ • q.2.2‖ ^ 2) < 4 * ρ := hq.2
  have hnorm : ‖ρ⁻¹ • u‖ = ‖u‖ / ρ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
    exact inv_mul_eq_div _ _
  have hlower : a < ‖u‖ / ρ := by
    have haε : a ≤ ε / 4 := min_le_left _ _
    have haF : a ≤ 1 / (8 * F) := min_le_right _ _
    have hcu := hcollar u hu
    rcases j with _ | j
    · have hρone : ρ = 1 := by simp [ρ]
      rw [hρone, div_one]
      linarith
    · rcases j with _ | j
      · have hρtwo : ρ = 2 := by norm_num [ρ]
        rw [hρtwo]
        linarith
      · have hρfour : 4 ≤ ρ := by
          dsimp [ρ]
          calc
            (4 : ℝ) = 2^2 := by norm_num
            _ ≤ 2^(j + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hsqrt : Real.sqrt (1 + ‖ρ • q.2.2‖ ^ 2) ≤ 1 + ‖ρ • q.2.2‖ := by
          apply (Real.sqrt_le_iff).mpr
          constructor
          · positivity
          · nlinarith [norm_nonneg (ρ • q.2.2)]
        have ht : ρ / 4 < ‖ρ • q.2.2‖ := by linarith [hshell.1]
        have hquot : 1 / (8 * F) < ‖u‖ / ρ := by
          apply (div_lt_div_iff₀ (by positivity : 0 < 8 * F) hρ).mpr
          nlinarith
        exact haF.trans_lt hquot
  have hupper : ‖u‖ / ρ < b := by
    have hnormsqrt : ‖ρ • q.2.2‖ ≤ Real.sqrt (1 + ‖ρ • q.2.2‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have hξ : ‖ρ • q.2.2‖ < 4 * ρ := hnormsqrt.trans_lt hshell.2
    have huupper : ‖u‖ < (4 * C) * ρ := by
      have := hreverse.trans_lt (mul_lt_mul_of_pos_left hξ hC)
      nlinarith
    have hb : 4 * C < b := (by linarith : 4 * C < 4 * C + 1).trans_le (le_max_right _ _)
    exact ((div_lt_iff₀ hρ).mpr huupper).trans hb
  change q.1 ∈ X ∧ q.2.1 ∈ X ∧ ρ⁻¹ • u ∈ normalizedSourceBand D ρ a b
  refine ⟨hqmem.1, hqmem.2.1, ?_, ?_⟩
  · change ρ • (ρ⁻¹ • u) ∈ D
    simpa [smul_inv_smul₀ hρ.ne'] using hu
  · change a < ‖ρ⁻¹ • u‖ ∧ ‖ρ⁻¹ • u‖ < b
    rw [hnorm]
    exact ⟨hlower, hupper⟩

end JanetCartan.FourierIntegral.WholeImageGeometry
