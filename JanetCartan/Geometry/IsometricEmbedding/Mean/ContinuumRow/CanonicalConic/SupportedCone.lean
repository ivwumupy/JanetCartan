module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.Masks
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Smaller angular support inside the actual annular chart

These finite-dimensional buffer inequalities connect the frozen covector
center of the actual full-phase chart to the annular normalization used in
`ConicChart`. They are the support reduction in
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison ContinuumNormalReduction.ConicChart
open NormedSpace

variable {n : ℕ}

/-- The open cone over a smaller incidence/angular neighborhood. The
spectator is kept as a separate parameter (`app:ch_background:eq:bg-Psi`). -/
def supportedCone (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1)) (r a : ℝ) :
    Set (ℝ × Euclidean (n - 1)) :=
  {u | u.1 ∈ ball (z₀ 0) r ∧ u.2 ≠ 0 ∧ normalize u.2 ∈ ball θ₀ a}

/-- The supported cone is invariant under positive covector dilations,
with the incidence coordinate fixed (`app:ch_background:eq:bg-Psi`). -/
theorem radialScale_mem_supportedCone {z₀ : Euclidean 3} {θ₀ : Euclidean (n - 1)}
    {r a : ℝ} {u : ℝ × Euclidean (n - 1)} (hu : u ∈ supportedCone z₀ θ₀ r a)
    {t : ℝ} (ht : 0 < t) : radialScale t u ∈ supportedCone z₀ θ₀ r a := by
  exact ⟨hu.1, smul_ne_zero ht.ne' hu.2.1,
    by simpa only [radialScale, normalize_smul_of_pos ht] using hu.2.2⟩

/-- The actual normalized angular mask is supported strictly inside the
larger open cone (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem angularMask_mem_supportedCone (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1))
    {r a : ℝ} (hr : 0 < r) (ha : 0 < a)
    {z : CarrierParameter} {η : Euclidean (n - 1)} (hη : η ≠ 0)
    (h : angularMask z₀ θ₀ hr ha z (‖η‖⁻¹ • η) ≠ 0) :
    (z.1, η) ∈ supportedCone z₀ θ₀ r a ∧
      z.2 ∈ ball (spectatorCenter z₀) r := by
  obtain ⟨hs, hv, hθ⟩ := angularMask_nonzero z₀ θ₀ hr ha h
  exact ⟨⟨ball_subset_ball (by linarith) hs, hη,
    ball_subset_ball (by linarith) hθ⟩, ball_subset_ball (by linarith) hv⟩

/-- Openness of the actual supported cone, including the angular
normalization away from zero (`app:ch_background:eq:bg-Psi`). -/
theorem supportedCone_open (z₀ : Euclidean 3) (θ₀ : Euclidean (n - 1)) (r a : ℝ) :
    IsOpen (supportedCone z₀ θ₀ r a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro u hu
  have hnorm : ContinuousAt (fun v : ℝ × Euclidean (n - 1) ↦ normalize v.2) u :=
    ((continuous_snd.norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hu.2.1)).smul
      continuous_snd.continuousAt)
  exact Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds
    (isOpen_ball.mem_nhds hu.1))
    (Filter.inter_mem ((isOpen_ne_fun continuous_snd continuous_const).mem_nhds hu.2.1)
      (hnorm.preimage_mem_nhds (isOpen_ball.mem_nhds hu.2.2)))

/-- The narrow annulus fits the actual covector-centered chart after dilation
by the frozen transverse magnitude (`app:ch_background:prop:bg-frame`, Step 1).
This estimates a distance to `ηb`, not merely the input norm. -/
theorem annular_dilation_mem_dataSet (z₀ : Euclidean 3)
    {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) {r a : ℝ}
    (hbuffer : 2 * ‖ηb‖ * a ≤ r)
    {u : ℝ × Euclidean (n - 1)}
    (hu : u ∈ supportedCone z₀ (normalize ηb) r a)
    (hinner : 1 - a < ‖u.2‖) (houter : ‖u.2‖ < 1 + a) :
    radialScale ‖ηb‖ u ∈ dataSet z₀ ηb r := by
  refine ⟨hu.1, ?_⟩
  have hμ : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
  have hn : ‖normalize u.2‖ = 1 := norm_normalize hu.2.1
  have habs : |‖u.2‖ - 1| < a := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hdist : ‖normalize u.2 - normalize ηb‖ < a := mem_ball_iff_norm.mp hu.2.2
  have hid : ‖ηb‖ • u.2 - ηb =
      (‖ηb‖ * (‖u.2‖ - 1)) • normalize u.2 +
        ‖ηb‖ • (normalize u.2 - normalize ηb) := by
    rw [mul_smul, sub_smul, one_smul, norm_smul_normalize, smul_sub, smul_sub,
      norm_smul_normalize]
    abel
  rw [mem_ball_iff_norm]
  change ‖‖ηb‖ • u.2 - ηb‖ < r
  calc
    _ ≤ ‖(‖ηb‖ * (‖u.2‖ - 1)) • normalize u.2‖ +
        ‖‖ηb‖ • (normalize u.2 - normalize ηb)‖ := hid ▸ norm_add_le _ _
    _ = ‖ηb‖ * |‖u.2‖ - 1| + ‖ηb‖ * ‖normalize u.2 - normalize ηb‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg ηb), hn,
        mul_one]
    _ < ‖ηb‖ * a + ‖ηb‖ * a := add_lt_add
      (mul_lt_mul_of_pos_left habs hμ) (mul_lt_mul_of_pos_left hdist hμ)
    _ ≤ r := by linarith

/-- Positive annular/angular width chosen from the actual covector buffer.
It is independent of the current immersion (`app:ch_background:eq:bg-Psi`). -/
def angularWidth (ηb : Euclidean (n - 1)) (r : ℝ) : ℝ :=
  min (1 / 4) (r / (8 * ‖ηb‖))

/-- The fixed width fits the local chart and the strict normalization
inequalities of `ConicChart.AnnularData` (`app:ch_background:eq:bg-Psi`). -/
theorem angularWidth_spec {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    0 < angularWidth ηb r ∧ angularWidth ηb r ≤ 1 / 4 ∧
    2 * ‖ηb‖ * angularWidth ηb r < r ∧
    0 ≤ 1 - angularWidth ηb r ∧
    0 ≤ angularWidth ηb r / 4 ∧ angularWidth ηb r / 4 < 1 ∧
    (1 - angularWidth ηb r) * (1 + angularWidth ηb r / 4) < 1 ∧
    1 < (1 + angularWidth ηb r) * (1 - angularWidth ηb r / 4) := by
  have hμ := norm_pos_iff.mpr hηb
  have ha : 0 < angularWidth ηb r := lt_min (by norm_num) (by positivity)
  have hau : angularWidth ηb r ≤ 1 / 4 := min_le_left _ _
  have har : angularWidth ηb r ≤ r / (8 * ‖ηb‖) := min_le_right _ _
  have hm := (le_div_iff₀ (by positivity : 0 < 8 * ‖ηb‖)).mp har
  refine ⟨ha, hau, by nlinarith, by linarith, by positivity, by linarith, ?_, ?_⟩
  · nlinarith [sq_nonneg (angularWidth ηb r)]
  · nlinarith

end JanetCartan.ContinuumRow.CanonicalConic
