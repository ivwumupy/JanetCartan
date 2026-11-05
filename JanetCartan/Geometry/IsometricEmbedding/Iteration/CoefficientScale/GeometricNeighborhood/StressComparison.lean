module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.JetComparison
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.ReferenceJets
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricNeighborhood.NormalGap

/-! # Continuity of the literal current projected stress frame

The C8 neighborhood is chosen before the current map, on nested fixed domains,
as required by `app:ch_seed:rem:seed-map-topology`.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open JanetCartan.ProjectedStressFrame JanetCartan.AmbientResponse
open JanetCartan.HamiltonPhase.CompositionContinuity
namespace JanetCartan.CurrentGeometricNeighborhood

set_option maxHeartbeats 800000

/-- The actual second-jet formula gives rank, a uniform normal gap, smoothness,
and C6 frame continuity from C8 map closeness
(`app:ch_seed:setup:seed-current`, `app:ch_seed:rem:seed-map-topology`).
No current-frame or compact-range hypothesis is supplied by the caller. -/
theorem exists_stress_neighborhood {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hrR : r < R) (hR : R < G.domain.chartRadius)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∃ κ > 0,
      ∀ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean (embeddingDimension n)),
      IsOpen U → Metric.closedBall 0 R ⊆ U → ContDiffOn ℝ ∞ F U →
      cNorm (Metric.closedBall 0 R) 8 (F - G.map) < δ →
      IsImmersionOn F (Metric.ball 0 R) ∧ HasFullNormalRankOn F (Metric.ball 0 R) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x ↦ projectedStress F x i) (Metric.ball 0 R)) ∧
      ∀ i, cNorm (Metric.closedBall 0 r) 6
        (fun x ↦ projectedStress F x i - projectedStress G.map x i) < η := by
  classical
  let K := Metric.closedBall (0 : Euclidean n) r
  let Kp := Metric.closedBall (0 : Euclidean n) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKp : IsCompact Kp := isCompact_closedBall _ _
  have hKKp : K ⊆ Kp := Metric.closedBall_subset_closedBall hrR.le
  have hKW : K ⊆ Metric.ball 0 R := Metric.closedBall_subset_ball hrR
  obtain ⟨d, hd, L, hL, hunit, hnear⟩ := exists_reference_jet_neighborhood G hR
  have hGrange : Set.MapsTo (stressJet G.map) K L := by
    intro x hx
    exact hnear x (hKKp hx) (stressJet G.map x) (by
      rw [sub_self (stressJet G.map x), norm_zero (E := StressJet n (embeddingDimension n))]
      exact hd.le)
  have hcoeff (i : Fin n) (J) (hJ : J ∈ L) :
      ContDiffAt ℝ 6 (jetStress (cubeStress n i)) J :=
    (contDiffAt_jetStress (hunit J hJ).1 (hunit J hJ).2 _).of_le (by simp)
  have hcomp (i : Fin n) := exists_cNorm_comp_sub_lt hK hL (hcoeff i)
    (fun _ _ ↦ (contDiff_stressJet G.contDiff).contDiffAt.of_le (by simp)) hGrange hη
  choose e he hcomp using hcomp
  have hmin : ∀ s : Finset (Fin n), ∃ a > 0, ∀ i ∈ s, a ≤ e i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s _ ih =>
      obtain ⟨a, ha, hsmall⟩ := ih
      refine ⟨min (e i) a, lt_min (he i) ha, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hsmall j hj)
  obtain ⟨a, ha, hsmall⟩ := hmin Finset.univ
  obtain ⟨κ, hκ, hgap⟩ := exists_normal_gap_of_compact_jets hL hunit
  refine ⟨min (d / 2) (a / 2), lt_min (half_pos hd) (half_pos ha), κ, hκ, ?_⟩
  intro U F hU hKU hF hclose
  have hG := G.contDiff.contDiffOn (s := U)
  have hFpoint (x) (hx : x ∈ Kp) : ContDiffAt ℝ ∞ F x :=
    hF.contDiffAt (hU.mem_nhds (hKU hx))
  have hjet (x) (hx : x ∈ Kp) : stressJet F x ∈ L := by
    apply hnear x hx
    have h := norm_stressJet_sub_le hKp hU hKU hF hG hx
    have hc := lt_of_lt_of_le hclose (min_le_left (d / 2) (a / 2))
    linarith
  have hi (x) (hx : x ∈ Kp) : Function.Injective (fderiv ℝ F x) := by
    have hu := (hunit _ (hjet x hx)).1
    exact (fderiv ℝ F x).adjoint_comp_self_injective_iff.mp
      (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
  have hrank (x) (hx : x ∈ Kp) :
      Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean (embeddingDimension n))) := by
    apply normal_rank_of_ambient_isUnit
    rw [← jetAmbient_stressJet ((hFpoint x hx).of_le (by simp)) (hi x hx)]
    exact (hunit _ (hjet x hx)).2
  have hiW : IsImmersionOn F (Metric.ball 0 R) := fun x hx ↦ hi x (Metric.ball_subset_closedBall hx)
  have hrW : HasFullNormalRankOn F (Metric.ball 0 R) :=
    fun x hx ↦ hrank x (Metric.ball_subset_closedBall hx)
  have hFW := hF.mono (Metric.ball_subset_closedBall.trans hKU)
  refine ⟨hiW, hrW, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := Metric.ball_subset_closedBall hx
    exact hgap F x ((hFpoint x hx').of_le (by simp)) (hi x hx') (hjet x hx')
  · intro i
    exact contDiffOn_projectedStress Metric.isOpen_ball hFW hiW hrW i
  · intro i
    have hdiff : cNorm K 6 (stressJet F - stressJet G.map) < e i := by
      have h1 := cNorm_stressJet_sub_le hK hU (hKKp.trans hKU) hF hG 6
      have h2 : cNorm K 8 (F - G.map) ≤ cNorm Kp 8 (F - G.map) :=
        cNorm_mono_set_of_contDiffAt hKKp hKp
          (fun x hx ↦ ((hFpoint x hx).sub G.contDiff.contDiffAt).of_le (by simp))
      have hc := lt_of_lt_of_le hclose (min_le_right (d / 2) (a / 2))
      have ha' := hsmall i (Finset.mem_univ i)
      norm_num at h1
      linarith
    have hc := hcomp i (jetStress (cubeStress n i)) (stressJet F) (hcoeff i)
      (fun x hx ↦ ((contDiffOn_stressJet hU hF).contDiffAt
        (hU.mem_nhds (hKU (hKKp hx)))).of_le (by simp))
      (fun x hx ↦ hjet x (hKKp hx)) (by simpa only [sub_self, cNorm_zero] using he i) hdiff
    have heq : cNorm K 6
        (jetStress (cubeStress n i) ∘ stressJet F -
          jetStress (cubeStress n i) ∘ stressJet G.map) =
        cNorm K 6 (fun x ↦ projectedStress F x i - projectedStress G.map x i) := by
      apply GeometricProfile.cNorm_eq_of_eventuallyEq _ 6
      intro x hx
      filter_upwards [Metric.isOpen_ball.mem_nhds (hKW hx)] with y hy
      simp only [Pi.sub_apply, Function.comp_apply,
        jetStress_stressJet ((hFpoint y (Metric.ball_subset_closedBall hy)).of_le (by simp))
          (hiW y hy),
        jetStress_stressJet (G.contDiff.contDiffAt.of_le (by simp)) (reference_isImmersion G y)]
    rwa [heq] at hc

end JanetCartan.CurrentGeometricNeighborhood
