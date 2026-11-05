module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.JetBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Exact

/-!
# Estimates for the actual projected reconstruction

The complete multiplier in `app:ch_waves:eq:WKB-residual` has a one-high
bound with two immersion derivatives and one correction derivative. The
metric, normal and frame gaps supply its compact range; no inverse-Gram
or reconstructed-residual estimate is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.RawPrimary.AmbientStrain
open ProjectedStressFrame GeometricProfile NullTransport.CoefficientBounds
open ActualCarriers.ConstructedCarrierJets

variable {n : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

/-- The literal projected reconstruction of a complex covector obeys a
one-high bound. All constants precede the immersion and covector; the
original projected-frame admission supplies every inverse bound
(`app:ch_waves:eq:WKB-strain`). -/
theorem exists_projected_reconstruction_bounds (hn : 5 ≤ n)
    (a : Euclidean n × Z) {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hx : MapsTo Prod.fst (closedBall a ρ) K) (M L : ℝ)
    {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (U : Set (Euclidean n)) (Ω : Set (Euclidean n × Z)),
        IsOpen U → IsOpen Ω → K ⊆ U → closedBall a ρ ⊆ Ω → MapsTo Prod.fst Ω U →
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)),
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        ContDiffOn ℝ ∞ b Ω → cNorm K 4 F ≤ M → cNorm (closedBall a ρ) 1 b ≤ L →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        ∀ m, cNorm (closedBall a ρ) m
          (fun w ↦ WKB.stressReconstruction (projectedStress F w.1)
            (fun i ↦ complexReducedOperator F (projectedStress F)
              (fun x ↦ b (x, w.2)) w.1 i)) ≤
          C m * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) b) ∧
        ∀ w ∈ closedBall a ρ, ContDiffAt ℝ ∞
          (fun y ↦ WKB.stressReconstruction (projectedStress F y.1)
            (fun i ↦ complexReducedOperator F (projectedStress F)
              (fun x ↦ b (x, y.2)) y.1 i)) w := by
  obtain ⟨D, hD, hbnd⟩ := exists_reconstructionJet_tame (N := embeddingDimension n)
    a hρ (2 * M) (max 1 (κnormal^2)⁻¹) L hκmet (ambientStrainFrameGramGap_pos hn)
  obtain ⟨A, hA, hpull⟩ := exists_cNorm_fixed_pullback_le (G := StressJet n (embeddingDimension n))
    (isCompact_closedBall a ρ) hK (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  refine ⟨fun m ↦ D m * (1 + 2 * A m),
    fun m ↦ mul_pos (hD m) (by have := hA m; positivity), ?_⟩
  intro U Ω hU hΩ hKU hball hΩU F b hF hi hrank hb hFM hbL hmet hnormal hclose m
  have hFat : ∀ x ∈ K, ContDiffAt ℝ ∞ F x :=
    fun x hx ↦ hF.contDiffAt (hU.mem_nhds (hKU hx))
  let J : Euclidean n × Z → StressJet n (embeddingDimension n) := fun w ↦ stressJet F w.1
  have hJ : ContDiffOn ℝ ∞ J Ω := (contDiffOn_stressJet hU hF).comp contDiffOn_fst hΩU
  have hmap : MapsTo J (closedBall a ρ)
      (admissibleStrainJets n (embeddingDimension n) (2 * M) κmet
        (max 1 (κnormal^2)⁻¹) (ambientStrainFrameGramGap hn)) :=
    fun w hw ↦ stressJet_mem_admissibleStrainJets hn hU hK hKU hF hi hrank
      hκnormal hFM hmet hnormal hclose (hx hw)
  have hout := hbnd Ω hΩ hball J b hJ hb hmap hbL m
  have hJb : cNorm (closedBall a ρ) m J ≤ 2 * A m * cNorm K (m + 2) F := by
    exact ((hpull (stressJet F)
      (fun x hx ↦ (contDiffOn_stressJet hU hF).contDiffAt (hU.mem_nhds (hKU hx))) m).trans
        (mul_le_mul_of_nonneg_left (cNorm_stressJet_le hK hFat m) (hA m).le)).trans_eq
          (by ring)
  have he : cNorm (closedBall a ρ) m
      (fun w ↦ WKB.stressReconstruction (projectedStress F w.1)
        (fun i ↦ complexReducedOperator F (projectedStress F) (fun x ↦ b (x, w.2)) w.1 i)) =
      cNorm (closedBall a ρ) m (fun w ↦ reconstructionJet (J w, b w, fderiv ℝ b w)) := by
    apply cNorm_eq_of_eventuallyEq
    intro w hw
    filter_upwards [hΩ.mem_nhds (hball hw)] with y hy
    exact (reconstructionJet_actual (hF.contDiffAt (hU.mem_nhds (hΩU hy)))
      (hi y.1 (hΩU hy)) ((hb.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))).symm
  constructor
  · rw [he]
    apply hout.trans
    have htotal : 1 + cNorm (closedBall a ρ) m J + cNorm (closedBall a ρ) (m + 1) b ≤
        (1 + 2 * A m) * (1 + cNorm K (m + 2) F + cNorm (closedBall a ρ) (m + 1) b) := by
      have := hA m
      have := cNorm_nonneg K (m + 2) F
      have := cNorm_nonneg (closedBall a ρ) (m + 1) b
      nlinarith
    exact (mul_le_mul_of_nonneg_left htotal (hD m).le).trans_eq (by ring)
  · intro w hw
    have hwΩ := hball hw
    have hwp := hmap hw
    have hp : ContDiffAt ℝ ∞ (fun y ↦ (J y, b y, fderiv ℝ b y)) w :=
      (hJ.contDiffAt (hΩ.mem_nhds hwΩ)).prodMk
        ((hb.contDiffAt (hΩ.mem_nhds hwΩ)).prodMk
          ((hb.fderiv_of_isOpen hΩ (m := ∞) (by simp)).contDiffAt (hΩ.mem_nhds hwΩ)))
    have hjet : ContDiffAt ℝ ∞ (@reconstructionJet n (embeddingDimension n) Z _ _)
        (J w, b w, fderiv ℝ b w) := contDiffAt_reconstructionJet
      (isUnit_jetMetric_of_lower_bound hκmet hwp.1.2.1)
      (isUnit_jetAmbient_of_lower_bound hwp.1.2.2)
      (firstJetMetric_isUnit_of_gap hκmet hwp.1.2.1)
      (stressGram_isUnit_of_energy _ (ambientStrainFrameGramGap_pos hn) hwp.2)
    have hcomp : ContDiffAt ℝ ∞ (fun y ↦ reconstructionJet (J y, b y, fderiv ℝ b y)) w :=
      ContDiffAt.comp (f := fun y ↦ (J y, b y, fderiv ℝ b y))
        (g := @reconstructionJet n (embeddingDimension n) Z _ _) w hjet hp
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [hΩ.mem_nhds hwΩ] with y hy
    exact (reconstructionJet_actual (hF.contDiffAt (hU.mem_nhds (hΩU hy)))
      (hi y.1 (hΩU hy)) ((hb.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))).symm

end JanetCartan.RawPrimary.AmbientStrain
