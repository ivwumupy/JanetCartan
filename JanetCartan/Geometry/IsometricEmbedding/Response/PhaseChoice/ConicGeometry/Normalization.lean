module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PhaseChoice.MixedGaps
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.ConicExtension

/-!
# A transverse slice retaining the entire primary compact

The cone for `app:ch_response:thm:response-compatible-choice` must contain all
selected carriers. Normalizing at the center of a ball need not retain its
outer rays. The slice below is placed at squared distance `‖v‖² - r²` and
therefore meets every ray through the transverse ball inside that same ball.
The canonical product retains its original maximum norm.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Topology

namespace JanetCartan.CompatibleResponse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The transverse normalization used to keep the entire selected primary
compact in the conic chart (`app:ch_response:thm:response-compatible-choice`). -/
def primaryBallNormalization (v : V) (r : ℝ) : (ℝ × V) →L[ℝ] ℝ :=
  (‖v‖ ^ 2 - r ^ 2)⁻¹ • (innerSL ℝ v).comp (ContinuousLinearMap.snd ℝ ℝ V)

/-- Every zero-energy ray through the transverse ball meets the selected
slice inside the same ball. This supplies the whole-compact containment in
`exists_primary_conic_normalization`, not only a buffer around one carrier
(`app:ch_response:thm:response-compatible-choice`). -/
theorem primaryBallNormalization_mem {v w : V} {r : ℝ}
    (hr : 0 < r) (hrv : r < ‖v‖) (hw : w ∈ ball v r) :
    0 < primaryBallNormalization v r (0, w) ∧
      (primaryBallNormalization v r (0, w))⁻¹ • ((0 : ℝ), w) ∈ ball (0, v) r := by
  let d := ‖v‖ ^ 2 - r ^ 2
  let t := ⟪v, w⟫_ℝ
  have hd : 0 < d := by dsimp [d]; nlinarith [norm_nonneg v]
  have hdist : ‖w - v‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have he := norm_sub_sq_real w v
  rw [real_inner_comm] at he
  have hbase : ‖w‖ ^ 2 + d < 2 * t := by
    dsimp [d, t]
    nlinarith [norm_nonneg (w - v)]
  have ht : 0 < t := by nlinarith [sq_nonneg ‖w‖]
  have hdt : d * ‖w‖ ^ 2 < t ^ 2 := by
    have hh := mul_lt_mul_of_pos_left hbase hd
    nlinarith [sq_nonneg (t - d)]
  have hl : primaryBallNormalization v r (0, w) = t / d := by
    simp [primaryBallNormalization, d, t, div_eq_mul_inv, mul_comm]
  refine ⟨by rw [hl]; exact div_pos ht hd, ?_⟩
  have hscale : (primaryBallNormalization v r (0, w))⁻¹ = d / t := by
    rw [hl, inv_div]
  have hs : 0 < d / t := div_pos hd ht
  have hst : d / t * t = d := div_mul_cancel₀ _ ht.ne'
  have hsbound : (d / t) ^ 2 * ‖w‖ ^ 2 < d := by
    have hh := mul_lt_mul_of_pos_left hdt (sq_pos_of_pos hs)
    have heq : (d / t) ^ 2 * t ^ 2 = d ^ 2 := by rw [← mul_pow, hst]
    rw [heq] at hh
    nlinarith
  have hn := norm_sub_sq_real ((d / t) • w) v
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, real_inner_smul_left,
    real_inner_comm] at hn
  have hnorm : ‖(d / t) • w - v‖ < r := by
    change ‖(d / t) • w - v‖ ^ 2 = ((d / t) * ‖w‖) ^ 2 -
      2 * (d / t * t) + ‖v‖ ^ 2 at hn
    rw [hst] at hn
    dsimp [d] at hsbound hn
    nlinarith [norm_nonneg ((d / t) • w - v)]
  simpa [hscale, mem_ball, Prod.dist_eq, dist_eq_norm] using hnorm

end JanetCartan.CompatibleResponse

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu FrozenPhaseReference CompatibleResponse

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The actual energy buffer cannot reach the zero covector; this also bounds
its radius by the transverse center norm
(`app:ch_response:thm:response-compatible-choice`). -/
theorem sectionEnergy_radius_le_center_norm :
    min T.family.radius (3 * T.family.sourceRadius) ≤
      ‖T.data.adapted.baseData.2.2‖ := by
  by_contra! h
  apply T.zero_notMem_sectionEnergyDomain
  simpa [sectionEnergyDomain, AdaptedSection.baseData] using h

/-- A single linear normalization whose open convex cone contains the entire
selected compact and normalizes into a strictly smaller energy ball. Both the
slice and the ball are chosen before the current frame
(`app:ch_response:thm:response-compatible-choice`). -/
theorem exists_primary_conic_normalization {c C : ℝ} (hP : P.IsValid c C) :
    ∃ (r : ℝ) (ℓ : (ℝ × Euclidean (n - 1)) →L[ℝ] ℝ),
      0 < r ∧ r < min T.family.radius (3 * T.family.sourceRadius) ∧
      T.primaryCanonicalCompact ⊆ ball T.data.adapted.baseData.2 r ∩
        canonicalCone ℓ (ball T.data.adapted.baseData.2 r) := by
  have hK := T.primaryCanonicalCompact_isCompact hP
  have hne : T.primaryCanonicalCompact.Nonempty := by
    refine ⟨T.primaryCanonical 0, 0, ?_, rfl⟩
    intro i
    simpa using hP.1.le
  obtain ⟨η, hη, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_id.dist (continuous_const (y := T.data.adapted.baseData.2))).continuousOn
  let R := min T.family.radius (3 * T.family.sourceRadius)
  have hR : 0 < R := lt_min T.family.radius_pos
    (mul_pos (by norm_num) T.family.sourceRadius_pos)
  have hηR : dist η T.data.adapted.baseData.2 < R :=
    T.primaryCanonicalCompact_subset hP hη
  let r := (dist η T.data.adapted.baseData.2 + R) / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [dist_nonneg (x := η) (y := T.data.adapted.baseData.2)]
  have hrR : r < R := by dsimp [r]; linarith
  have hsub : T.primaryCanonicalCompact ⊆ ball T.data.adapted.baseData.2 r := by
    intro θ hθ
    have hh : dist θ T.data.adapted.baseData.2 ≤
        dist η T.data.adapted.baseData.2 := hmax hθ
    change dist θ T.data.adapted.baseData.2 < r
    dsimp [r]
    linarith
  refine ⟨r, primaryBallNormalization T.data.adapted.baseData.2.2 r, hr, hrR, ?_⟩
  rintro θ hθ
  refine ⟨hsub hθ, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hθ
  have hw : T.reference.spatialPatch z ∈ ball T.data.adapted.baseData.2.2 r := by
    have hh := hsub ⟨z, hz, rfl⟩
    change max (dist 0 0) (dist (T.reference.spatialPatch z)
      T.data.adapted.baseData.2.2) < r at hh
    exact (max_lt_iff.mp hh).2
  exact primaryBallNormalization_mem hr
    (hrR.trans_le T.sectionEnergy_radius_le_center_norm) hw

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
