module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.HistoryGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# Admitting the source histories after the measured row is fixed

The corrected measured selection takes place after its reference `H` is
fixed. Its amplitude and inverse-chart tolerances therefore need a new source
cap on this same reference. Stress dilation supplies that cap, and the actual
history displacement supplies the subsequent current-map neighborhood.

Consumers: the low map, metric, normal-gap and frame inputs of
`exists_reflected_profiles_on_initialized_density_geometry` and the sharp
retained baseline, with the same measured row and prescribed leading cells.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ProjectedStressFrame ContinuumRow CanonicalCarrier

/-- Every sufficiently small source contraction admits all literal finite
histories to an arbitrary subsequently prescribed continuum-row frame
tolerance. The complete fixed carrier low budget, metric gap and actual normal
gap are conclusions. The source cap precedes the contraction, derivative
budget and history threshold. No new reference or row is selected
(`app:ch_seed:setup:seed-current`, `main:eq:displacement-budget`,
`new:sec:order-of-choices`). -/
theorem exists_source_history_row_geometry {n : ℕ} (H : FlatReference n)
    {b R : ℝ} (hb : 0 < b) (hbR : b < R) (hR : R < H.domain.chartRadius)
    {δframe : ℝ} (hδframe : 0 < δframe) :
    ∃ cap > (0 : ℝ), cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap,
      ∀ {kMin : ℕ},
        displacementLoss n +
          bandExponent * ((canonicalCarrierLowOrder n : ℝ) + (n : ℝ) / 2) + 2 < kMin →
      ∀ {δimage : ℝ}, 0 < δimage →
      ∃ κ > (0 : ℝ), ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
        ∀ (stage : ℕ)
          (u : Fin stage → Torus n → Euclidean (embeddingDimension n))
          (ell : Fin stage → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        let F := finiteHistoryMap (sourceDilation H.map σ) u
        ContDiff ℝ ∞ F ∧ IsImmersionOn F (ball 0 R) ∧
        HasFullNormalRankOn F (ball 0 R) ∧
        cNorm (closedBall 0 b) (canonicalCarrierLowOrder n) F ≤
          cNorm (closedBall 0 b) (canonicalCarrierLowOrder n)
            (sourceDilation H.map σ) + 1 ∧
        (∀ x ∈ closedBall 0 b, ∀ v,
          (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
        (∀ x ∈ closedBall 0 b, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
        cNorm (closedBall 0 b) 6 (projectedStress F - fun _ ↦ cubeStress n) < δframe ∧
        ∀ a : ℝ, cNorm (closedBall 0 (6 * a)) 8
          (F - sourceDilation H.map σ) < δimage := by
  obtain ⟨_U, _hU, _hKU, cap₀, hcap₀, hcap₀one, _hsegments, _hsource, hbounds⟩ :=
    exists_projectedStress_dilation_bounds H (isCompact_closedBall (0 : Euclidean n) b)
  obtain ⟨C, hC, hbound⟩ := hbounds 6
  let cap := min cap₀ (δframe / (56 * C))
  have hcap : 0 < cap := lt_min hcap₀ (div_pos hδframe (by positivity))
  have hcapone : cap ≤ 1 := (min_le_left _ _).trans hcap₀one
  refine ⟨cap, hcap, hcapone, ?_⟩
  intro σ hσ kMin horder δimage hδimage
  let G := sourceDilationReference H hσ.1 (hσ.2.trans hcapone)
  have hreference (i : Fin n) :
      cNorm (closedBall (0 : Euclidean n) b) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < (δframe / 14) / 2 := by
    have hsmall : C * σ ≤ δframe / 56 := by
      have hσsmall : σ ≤ δframe / (56 * C) := hσ.2.trans (min_le_right _ _)
      have hmul := (le_div_iff₀ (show 0 < 56 * C by positivity)).mp hσsmall
      nlinarith
    exact (hbound σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩ i).trans_lt
      (hsmall.trans_lt (by linarith))
  obtain ⟨δgeom, hδgeom, _C₀, _hC₀, κ, hκ, hnear⟩ :=
    CurrentGeometricNeighborhood.exists_cube_frame_neighborhood G hb hbR hR
      (div_pos hδframe (by norm_num)) hreference
  have hgeometry (F : Euclidean n → Euclidean (embeddingDimension n))
      (hF : ContDiff ℝ ∞ F) (hclose : cNorm (closedBall 0 R) 8 (F - G.map) < δgeom) :
      IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
      (∀ x ∈ ball 0 R, ∀ v, (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      ∀ i, cNorm (closedBall 0 b) 6
        (fun x ↦ projectedStress F x i - cubeStress n i) < δframe / 14 := by
    obtain ⟨hi, hrank, _hlow, hmet, hnormal, _hsmooth, hframe⟩ :=
      hnear univ F isOpen_univ (subset_univ _) hF.contDiffOn hclose
    exact ⟨hi, hrank, hmet, hnormal, hframe⟩
  obtain ⟨S, hS, hhistory⟩ := exists_initialScale_for_initialized_row_inputs
    G hbR hδgeom hδframe hδimage hgeometry horder
  exact ⟨κ, hκ, S, hS, hhistory⟩

end JanetCartan.ContinuumInverse
