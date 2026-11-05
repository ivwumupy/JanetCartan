module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.StressComparison
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.MetricGap

/-!
# The geometric current neighborhood

The concrete C8 neighborhood of a fixed actual flat reference in
`app:ch_seed:setup:seed-current` and `app:ch_seed:rem:seed-map-topology`.
Constants precede the current map, its higher norms, scale, stage and history.
For `main:prop:current-scale` and `main:eq:displacement-budget`, the parent
construction must instantiate the reference and establish the C8 displacement
bound on the outer closed ball. No history or correction is constructed here.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open JanetCartan.ProjectedStressFrame
namespace JanetCartan.CurrentGeometricNeighborhood

/-- The reference has a uniform positive actual normal gap on the outer closed
ball, derived from its full rank and compactness
(`app:ch_seed:setup:seed-current`). -/
theorem exists_reference_normal_gap {n : ℕ} (G : FlatReference n)
    {R : ℝ} (hR : R < G.domain.chartRadius) :
    ∃ κ > 0, ∀ x ∈ Metric.closedBall (0 : Euclidean n) R,
      ∀ w ∈ normalSpace G.map x, κ * ‖w‖ ≤ ‖normalPairing G.map (fun _ ↦ w) x‖ := by
  obtain ⟨d, hd, L, hL, hu, hnear⟩ := exists_reference_jet_neighborhood G hR
  obtain ⟨κ, hκ, hgap⟩ := exists_normal_gap_of_compact_jets hL hu
  refine ⟨κ, hκ, fun x hx ↦ hgap G.map x
    (G.contDiff.contDiffAt.of_le (by simp)) (reference_isImmersion G x) ?_⟩
  exact hnear x hx (stressJet G.map x) (by
      rw [sub_self (stressJet G.map x), norm_zero (E := StressJet n (embeddingDimension n))]
      exact hd.le)

/-- Persistence of all geometric inputs of `app:ch_seed:setup:seed-current`
from the literal C8 map displacement. The normal gap is on the actual varying
normal spaces; the metric energy gap is the separate constant one quarter.
Coefficient norms are measured strictly inside the open working ball. -/
theorem exists_geometric_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (_hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ C₀ > 0, ∃ κ > 0,
      ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
      IsOpen U → Metric.closedBall 0 R ⊆ U → ContDiffOn ℝ ∞ F U →
      cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
      IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
      cNorm (Metric.closedBall 0 r) 4 F ≤ C₀ ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (Metric.ball 0 R)) ∧
      ∀ i, cNorm (Metric.closedBall 0 r) 6
        (fun x ↦ projectedStress F x i - projectedStress G.map x i) < η := by
  obtain ⟨d, hd, κ, hκ, hstress⟩ := exists_stress_neighborhood G hrR hR hη
  let K := Metric.closedBall (0 : Euclidean n) r
  let Kp := Metric.closedBall (0 : Euclidean n) R
  refine ⟨min d (1 / 2), lt_min hd (by norm_num), 1 + cNorm K 4 G.map,
    by linarith [cNorm_nonneg K 4 G.map], κ, hκ, ?_⟩
  intro U F hU hKU hF hclose
  obtain ⟨hi, hrank, hgap, hsmooth, hcomp⟩ :=
    hstress U F hU hKU hF (hclose.trans_le (min_le_left _ _))
  have hKp : IsCompact Kp := isCompact_closedBall _ _
  have hKKp : K ⊆ Kp := Metric.closedBall_subset_closedBall hrR.le
  have hFp (x) (hx : x ∈ Kp) := hF.contDiffAt (hU.mem_nhds (hKU hx))
  have hDp (x) (hx : x ∈ Kp) : ContDiffAt ℝ ∞ (F - G.map) x :=
    (hFp x hx).sub G.contDiff.contDiffAt
  have hhalf : cNorm Kp 8 (F - G.map) < 1 / 2 := hclose.trans_le (min_le_right _ _)
  refine ⟨hi, hrank, ?_, ?_, hgap, hsmooth, hcomp⟩
  · have hsum := cNorm_add_le_of_contDiffAt (isCompact_closedBall (0 : Euclidean n) r)
      (fun x hx ↦ (hDp x (hKKp hx)).of_le (by simp : (4 : ℕ∞ω) ≤ ∞))
      (fun _ _ ↦ G.contDiff.contDiffAt.of_le (by simp : (4 : ℕ∞ω) ≤ ∞))
    have he : F - G.map + G.map = F := sub_add_cancel _ _
    rw [he] at hsum
    have hsmall : cNorm K 4 (F - G.map) ≤ cNorm Kp 8 (F - G.map) :=
      (cNorm_mono_order (by norm_num : 4 ≤ 8)).trans
        (cNorm_mono_set_of_contDiffAt hKKp hKp
          (fun x hx ↦ (hDp x hx).of_le (by simp)))
    linarith
  · intro x hx
    apply (metric_gap_of_fderiv_close G F x ?_).2
    have hx' := Metric.ball_subset_closedBall hx
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt hKp
      (fun y hy ↦ (hDp y hy).of_le (by simp : (8 : ℕ∞ω) ≤ ∞)) hx' (by norm_num : 1 ≤ 8)
    rw [norm_iteratedFDeriv_one, fderiv_sub ((hFp x hx').differentiableAt (by simp))
      (G.contDiff.contDiffAt.differentiableAt (by simp))] at hb
    exact hb.trans_lt hhalf


/-- The exact cube-frame specialization of `app:ch_seed:setup:seed-current`.
The reference tolerance is supplied by the scaled-reference producer; the
current-field tolerance follows from C8 displacement and is not an input. -/
theorem exists_cube_frame_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {ε : ℝ} (hε : 0 < ε)
    (hreference : ∀ i, cNorm (Metric.closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < ε / 2) :
    ∃ δ > 0, ∃ C₀ > 0, ∃ κ > 0,
      ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
      IsOpen U → Metric.closedBall 0 R ⊆ U → ContDiffOn ℝ ∞ F U →
      cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
      IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
      cNorm (Metric.closedBall 0 r) 4 F ≤ C₀ ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (Metric.ball 0 R)) ∧
      ∀ i, cNorm (Metric.closedBall 0 r) 6
        (fun x ↦ projectedStress F x i - cubeStress n i) < ε := by
  obtain ⟨δ, hδ, C₀, hC₀, κ, hκ, hcurrent⟩ :=
    exists_geometric_neighborhood G hr hrR hR (half_pos hε)
  refine ⟨δ, hδ, C₀, hC₀, κ, hκ, ?_⟩
  intro U F hU hKU hF hclose
  obtain ⟨hi, hrank, hlow, hmet, hnormal, hQ, hcompare⟩ :=
    hcurrent U F hU hKU hF hclose
  refine ⟨hi, hrank, hlow, hmet, hnormal, hQ, ?_⟩
  intro i
  have hGW : ContDiffOn ℝ ∞ (fun x ↦ projectedStress G.map x i) (Metric.ball 0 R) :=
    contDiffOn_projectedStress Metric.isOpen_ball G.contDiff.contDiffOn
      (fun x _ ↦ reference_isImmersion G x)
      (fun x hx ↦ G.fullNormalRank x ((Metric.ball_subset_ball hR.le) hx)) i
  have hKW : Metric.closedBall (0 : Euclidean n) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have hf (x) (hx : x ∈ Metric.closedBall (0 : Euclidean n) r) :=
    (hQ i).contDiffAt (Metric.isOpen_ball.mem_nhds (hKW hx))
  have hg (x) (hx : x ∈ Metric.closedBall (0 : Euclidean n) r) :=
    hGW.contDiffAt (Metric.isOpen_ball.mem_nhds (hKW hx))
  have htri := cNorm_add_le_of_contDiffAt (isCompact_closedBall (0 : Euclidean n) r)
    (fun x hx ↦ ((hf x hx).sub (hg x hx)).of_le (by simp : (6 : ℕ∞ω) ≤ ∞))
    (fun x hx ↦ ((hg x hx).sub (contDiffAt_const (c := cubeStress n i))).of_le
      (by simp : (6 : ℕ∞ω) ≤ ∞))
  have he : (fun x ↦ projectedStress F x i - projectedStress G.map x i) +
      (fun x ↦ projectedStress G.map x i - cubeStress n i) =
      (fun x ↦ projectedStress F x i - cubeStress n i) := by
    ext x
    exact sub_add_sub_cancel _ _ _
  rw [he] at htri
  exact htri.trans_lt (by linarith [hcompare i, hreference i])

end JanetCartan.CurrentGeometricNeighborhood
