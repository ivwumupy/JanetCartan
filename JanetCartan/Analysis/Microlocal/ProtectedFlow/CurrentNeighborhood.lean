module

public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ProjectedProtection
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReferenceBackground

/-!
# One primitive neighborhood for protection and the complete coefficient array

The common-neighborhood step in `app:ch_regular:thm:no-return`. The input
reference margin is exactly the componentwise frame-to-cube margin. The
current immersion, normal rank, projected-frame comparison, and full extended
low class are all conclusions of one primitive map neighborhood. The consumers
are `exists_projected_signed_protection` and the actual reduced response.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ProtectedFlow
open ProjectedStressFrame CurrentGeometricNeighborhood
open ActualCarriers.CurrentFullPhase

/-- Simultaneously produce the primitive projected-frame input for signed
protection and the full extended coefficient low class. The reference
tolerance precedes the reference; the current-map threshold precedes every
current map and its higher norms. For low order six the sole displacement
norm is `C⁸`. The fixed reference frame margin remains the scaled-reference
producer's input (`app:ch_regular:thm:no-return`). -/
theorem exists_current_frame_and_extension_neighborhood {n : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (hp0 : p.center = 0)
    {r R : ℝ} (hpr : p.radius ≤ r) (hrR : r < R)
    (m : ℕ) (hm : 6 ≤ m) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean n) r) m
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < η) →
      ∃ Z₀ : Euclidean n → Fin n × Fin n → ℝ, ContDiff ℝ ∞ Z₀ ∧
        ∃ δ > (0 : ℝ), ∀ F : Euclidean n → Euclidean (embeddingDimension n),
          ContDiff ℝ ∞ F → cNorm (closedBall 0 R) (m + 2) (F - G.map) < δ →
          IsImmersionOn F (ball 0 R) ∧ HasFullNormalRankOn F (ball 0 R) ∧
          (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
            (fun x ↦ projectedStress F x i - cubeStress n i) < d) ∧
          ContDiff ℝ ∞ (extendedReducedCoefficients p Z₀ F) ∧
          cNorm univ m
            (extendedReducedCoefficients p Z₀ F - reducedCoefficientBackground Z₀) < ε := by
  have hr : 0 < r := p.radius_pos.trans_le hpr
  obtain ⟨e, he, hlow⟩ := exists_reference_frame_extension_low_class p hp0
    (hpr.trans_lt hrR) m hε
  let η := min (d / 2) (e / (2 * (m + 1)))
  have hη : 0 < η := lt_min (half_pos hd) (div_pos he (by positivity))
  refine ⟨η, hη, ?_⟩
  intro G hR href
  have hGQ : ContDiffOn ℝ ∞ (projectedStress G.map - fun _ ↦ cubeStress n) (ball 0 R) :=
    (contDiffOn_pi.mpr (fun i ↦ contDiffOn_projectedStress isOpen_ball G.contDiff.contDiffOn
      (fun x _ ↦ reference_isImmersion G x)
      (fun x hx ↦ G.fullNormalRank x (ball_subset_ball hR.le hx)) i)).sub contDiffOn_const
  have hs : ∀ x ∈ closedBall (0 : Euclidean n) r,
      ContDiffAt ℝ m (projectedStress G.map - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ (hGQ.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball hrR hx))).of_le
      (by simp)
  have hjoint : cNorm (closedBall (0 : Euclidean n) r) m
      (projectedStress G.map - fun _ ↦ cubeStress n) < e := by
    apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _) hs he
    intro i
    exact (href i).trans_le (min_le_right _ _)
  have hpjoint : cNorm (closedBall (0 : Euclidean n) p.radius) m
      (projectedStress G.map - fun _ ↦ cubeStress n) < e :=
    (cNorm_mono_set_of_contDiffAt (closedBall_subset_closedBall hpr)
      (isCompact_closedBall _ _) hs).trans_lt hjoint
  obtain ⟨Z₀, hZ₀, _hZagree, dl, hdl, hcurrentLow⟩ := hlow G hR hpjoint
  have href6 (i : Fin n) : cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < d / 2 :=
    (cNorm_mono_order hm).trans_lt ((href i).trans_le (min_le_left _ _))
  obtain ⟨dg, hdg, C, _hC, κ, _hκ, hgeo⟩ :=
    exists_cube_frame_neighborhood G hr hrR hR hd href6
  refine ⟨Z₀, hZ₀, min dg dl, lt_min hdg hdl, ?_⟩
  intro F hF hclose
  have h8 : cNorm (closedBall (0 : Euclidean n) R) 8 (F - G.map) < dg :=
    (cNorm_mono_order (by omega : 8 ≤ m + 2)).trans_lt
      (hclose.trans_le (min_le_left _ _))
  obtain ⟨hi, hrank, _hbound, _hmetric, _hgap, _hsmooth, hframe⟩ :=
    hgeo univ F isOpen_univ (subset_univ _) hF.contDiffOn h8
  have hlowOrder : cNorm (closedBall (0 : Euclidean n) R) (max 8 (m + 2)) (F - G.map) < dl := by
    rw [max_eq_right (by omega : 8 ≤ m + 2)]
    exact hclose.trans_le (min_le_right _ _)
  obtain ⟨_hi, _hrank, hsmooth, hext⟩ := hcurrentLow F hF hlowOrder
  exact ⟨hi, hrank, hframe, hsmooth, hext⟩

end JanetCartan.ProtectedFlow
