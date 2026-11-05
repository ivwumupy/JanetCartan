module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalScaleMargins

/-!
# Original scale margins for the corrected finite chart family

The returned scalar phase radii of the corrected event suffice. No auxiliary
normal geometry is chosen, and the original history exponents are retained.
-/

@[expose] public noncomputable section
open Set Filter
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase NormalComparison RawInputPartition
open SeparatedSampling MeasuredAmplitude MeasuredAmplitude.ColoredApplication

/-- One initial threshold supplies the literal corrected event's band and
transport margins at every original stage, for every chart and color. The
threshold precedes histories and radial labels, and uses the unchanged
carrier, ceiling and mesh exponents (`app:ch_waves:thm:sampling`,
`app:ch_mean_pairs:eq:mean-stage-window`). -/
theorem exists_corrected_sampling_originalScale_threshold
    {m : ℕ} {A : Type*} [Fintype A]
    {P : A → Patch (m + 1)} {U : A → Set (Euclidean (m + 1))}
    {hU : ∀ a, IsOpen (U a)}
    (T : ∀ a, PatchQuantitativeFamily (P a) (U a) (hU a))
    {c C : A → ℝ} (hP : ∀ a, (P a).IsValid (c a) (C a))
    {ρ e : A → ℝ} (hρ : ∀ a, 0 < ρ a) (he : ∀ a, 0 < e a)
    {Rmin : ℝ} (hRmin : 0 < Rmin) (eventThreshold : ℝ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ Rinit ≥ S, ∀ stage : ℕ,
      let Rstage := historyScale Rinit growthExponent stage
      let Λ := Rstage ^ (1 + meanSlack)
      let lam := Rstage ^ carrierExponent
      eventThreshold ≤ Λ ∧ 1 ≤ Λ ∧ 0 < lam ∧
      (∀ a, 2 * Λ / (Rmin * lam) ≤ e a) ∧
      ∀ (p : ℕ) (radial : A → (Fin 3 → Fin (p + 1)) → ℝ),
        (∀ a color, Rmin ≤ radial a color) → ∀ a color,
        0 < (radial a color * lam)⁻¹ ∧ (radial a color * lam)⁻¹ ≤ 1 ∧
        ∀ j : Fin (cutoffCount Λ),
          (radial a color * lam)⁻¹ * (2 : ℝ) ^ j.val ≤
            min (e a) (measuredPhaseRadius (T a) (hP a) (ρ := ρ a)) := by
  classical
  obtain ⟨d, hd, hdall⟩ := Pi.exists_forall_pos_add_lt
    (fun a ↦ lt_min (he a) (measuredPhaseRadius_pos (T a) (hρ a) (hP a)))
  have hdall' (a) : d ≤ min (e a) (measuredPhaseRadius (T a) (hP a) (ρ := ρ a)) := by
    simpa using (hdall a).le
  let Cscale := 1 + Rmin⁻¹ + 2 / (Rmin * d)
  have hC₁ : 1 ≤ Cscale := by
    dsimp [Cscale]
    have := inv_pos.mpr hRmin
    have := div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hRmin hd)
    linarith
  have hCR : Rmin⁻¹ ≤ Cscale := by
    dsimp [Cscale]
    have := div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hRmin hd)
    linarith
  have hCD : 2 / (Rmin * d) ≤ Cscale := by
    dsimp [Cscale]
    linarith [inv_pos.mpr hRmin]
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt Cscale
      (by norm_num [meanSlack, carrierExponent] : 1 + meanSlack < carrierExponent))
  refine ⟨max 2 (max S eventThreshold), le_max_left _ _, ?_⟩
  intro Rinit hRinit stage Rstage Λ lam
  have hRone : 1 ≤ Rinit := (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hRinit)
  have hstage : Rinit ≤ Rstage := le_historyScale hRone stage
  have hstageOne : 1 ≤ Rstage := hRone.trans hstage
  have hlarge : S ≤ Rstage :=
    ((le_max_left S eventThreshold).trans ((le_max_right _ _).trans hRinit)).trans hstage
  have hceiling : Rstage ≤ Λ :=
    Real.self_le_rpow_of_one_le hstageOne (by norm_num [meanSlack])
  have hΛ : 1 ≤ Λ := hstageOne.trans hceiling
  have hCscale : Cscale * Λ ≤ lam := hS _ hlarge
  have hClam : Cscale ≤ lam :=
    (le_mul_of_one_le_right (zero_le_one.trans hC₁) hΛ).trans hCscale
  have hlam : 0 < lam := zero_lt_one.trans_le (hC₁.trans hClam)
  have hRlam : 1 ≤ Rmin * lam := calc
    1 = Rmin * Rmin⁻¹ := (mul_inv_cancel₀ hRmin.ne').symm
    _ ≤ Rmin * lam := mul_le_mul_of_nonneg_left (hCR.trans hClam) hRmin.le
  have hbuffer : 2 * Λ / (Rmin * lam) ≤ d := by
    apply (div_le_iff₀ (mul_pos hRmin hlam)).mpr
    have hh := (mul_le_mul_of_nonneg_right hCD (zero_le_one.trans hΛ)).trans hCscale
    calc
      2 * Λ = (Rmin * d) * ((2 / (Rmin * d)) * Λ) := by field_simp
      _ ≤ (Rmin * d) * lam := mul_le_mul_of_nonneg_left hh (mul_pos hRmin hd).le
      _ = d * (Rmin * lam) := by ring
  refine ⟨((le_max_right S eventThreshold).trans ((le_max_right _ _).trans hRinit)).trans
      (hstage.trans hceiling), hΛ, hlam,
    fun a ↦ hbuffer.trans ((hdall' a).trans (min_le_left _ _)), ?_⟩
  intro p radial hradial a color
  have hradialpos := hRmin.trans_le (hradial a color)
  have hprod := mul_pos hradialpos hlam
  have hprod₁ : 1 ≤ radial a color * lam :=
    hRlam.trans (mul_le_mul_of_nonneg_right (hradial a color) hlam.le)
  refine ⟨inv_pos.mpr hprod, (inv_le_one₀ hprod).mpr hprod₁, ?_⟩
  intro j
  have hpow : (2 : ℝ) ^ j.val ≤ 2 * Λ := by
    rw [powTwo_eq_twice_dyadicScale]
    exact mul_le_mul_of_nonneg_left ((lt_cutoffCount_iff hΛ j.val).mp j.isLt) (by norm_num)
  have hinv : (radial a color * lam)⁻¹ ≤ (Rmin * lam)⁻¹ :=
    inv_anti₀ (mul_pos hRmin hlam) (mul_le_mul_of_nonneg_right (hradial a color) hlam.le)
  calc
    _ ≤ (Rmin * lam)⁻¹ * (2 * Λ) :=
      mul_le_mul hinv hpow (by positivity) (by positivity)
    _ = 2 * Λ / (Rmin * lam) := by ring
    _ ≤ d := hbuffer
    _ ≤ _ := hdall' a

end JanetCartan.Sampling
