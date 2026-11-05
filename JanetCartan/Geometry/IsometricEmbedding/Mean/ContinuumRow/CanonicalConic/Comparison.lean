module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.ChartMap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportedCone

/-!
# Actual transverse comparison on the supported cone

Choose the primitive frame threshold after the fixed angular width, before
the immersion. Comparison on the actual covector-centered box and literal
homogeneity prove the relative transverse estimate on the entire cone.
This is the normalization premise of `ConicChart.AnnularData`, with its
producer discharged (`app:ch_background:prop:bg-frame`, Step 1).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormedSpace
open ContinuumNormalReduction.ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The stronger transverse comparison needed by the smaller annulus is
proved from primitive frame closeness, not added as a chart hypothesis.
The fixed physical/carrier boxes come from `exists_actual_local_charts`.
Source: `app:ch_background:eq:bg-Psi`, `app:ch_background:prop:bg-frame`. -/
theorem exists_supported_transverse_threshold {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r : ℝ} (hr : 0 < r) (hphys : 3 * r < T.family.radius / 8)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ physicalParameterSet z₀ r,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤
          (angularWidth ηb r / 4) * ‖u.2‖ := by
  have hμ : 0 < ‖ηb‖ := norm_pos_iff.mpr hηb
  obtain ⟨ha, _, hab, _⟩ := angularWidth_spec hηb hr
  have hc : closedBall (spectatorCenter z₀) r ×ˢ closedBall (z₀ 0) r ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2) :=
    fun q hq ↦ hcarrier ⟨closedBall_subset_closedBall (by linarith) hq.1,
      closedBall_subset_closedBall (by linarith) hq.2⟩
  obtain ⟨δ, hδ, e, he, hcomp⟩ := exists_frame_comparison_threshold T hP z₀ ηb
    (by linarith : r < T.family.radius / 8) hc
    (show 0 < ‖ηb‖ * (angularWidth ηb r / 4) by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ p hp u hu
  have hη : 0 < ‖u.2‖ := norm_pos_iff.mpr hu.2.1
  let t := ‖ηb‖ / ‖u.2‖
  have ht : 0 < t := div_pos hμ hη
  have hmul : t * ‖u.2‖ = ‖ηb‖ := div_mul_cancel₀ _ hη.ne'
  have htu : (radialScale t u).2 ∈ closedBall ηb r := by
    apply ball_subset_closedBall
    rw [mem_ball_iff_norm]
    have hid : t • u.2 - ηb = ‖ηb‖ • (NormedSpace.normalize u.2 - NormedSpace.normalize ηb) := by
      simp only [t, div_eq_mul_inv, NormedSpace.normalize, smul_sub,
        smul_smul, mul_inv_cancel₀ hμ.ne', one_smul]
    change ‖t • u.2 - ηb‖ < r
    rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
    have hd : ‖NormedSpace.normalize u.2 - NormedSpace.normalize ηb‖ < angularWidth ηb r :=
      mem_ball_iff_norm.mp hu.2.2
    have hh := mul_lt_mul_of_pos_left hd hμ
    nlinarith
  have hpt : (CanonicalCarrier.physicalCoordinates T p.2.1) ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using
      (ball_subset_closedBall hp.2.1 : p.2.1 ∈ closedBall 0 r)
  have hpt' : (CanonicalCarrier.physicalCoordinates T p.2.2) ∈ closedBall 0 r := by
    simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using
      (ball_subset_closedBall hp.2.2 : p.2.2 ∈ closedBall 0 r)
  have hraw := (hcomp Q hQ 0 (by simpa using he.le)).1
    (p.1, (CanonicalCarrier.physicalCoordinates T p.2.1,
      CanonicalCarrier.physicalCoordinates T p.2.2), radialScale t u)
    ⟨ball_subset_closedBall hp.1, ⟨hpt, hpt'⟩, ball_subset_closedBall hu.1, htu⟩
  have hclose : ‖(adaptedTransportChart T Q p (radialScale t u)).2 - t • u.2‖ <
      ‖ηb‖ * (angularWidth ηb r / 4) := by
    apply (norm_snd_le (adaptedTransportChart T Q p (radialScale t u) -
      frozenChart (fun s ↦ gradient (dispersion T) (spatialCarrier T (p.1,s)))
        (radialScale t u))).trans_lt
    simpa only [adaptedTransportChart_eq, fullChartFamily, phaseParameters] using hraw.1
  rw [adaptedTransportChart_radialScale] at hclose
  change ‖t • (adaptedTransportChart T Q p u).2 - t • u.2‖ < _ at hclose
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hclose
  have hh := mul_lt_mul_of_pos_right hclose hη
  rw [← hmul] at hh
  nlinarith

end JanetCartan.ContinuumRow.CanonicalConic
