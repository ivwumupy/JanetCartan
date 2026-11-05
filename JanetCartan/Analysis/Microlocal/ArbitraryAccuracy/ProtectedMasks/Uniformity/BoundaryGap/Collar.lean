module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap.Diagonal
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap.Variation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.BoundaryGap.SecondJets

/-!
# A coefficient-uniform elapsed boundary collar

The width depends only on the mask margin, the fixed strict target buffer and
the common phase C² budget extracted from the original coefficient C³ bound.
The geometry, external bases, orientation and requested accuracy come afterward.
The result is pointwise on the full closed shoulder and complementary support,
so it restricts to any actual closed total carrier in its original elapsed
interval. No elapsed operator is shortened and no compact coefficient class is
introduced. Source: the half-space argument in
`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph ConicPhase

variable {d : ℕ}

/-- Choose a common positive width and squared tangential-gradient gap
before the current chart or masks. The exact low-jet producer is
`twoTimePhase_secondJet_budget_of_rootFlow`, with `N = B 2 * (1 + M)`;
the exact margin producer is the diagonal branch of
`canonicalProofLocalizer_complete_image_closed_shoulder`.
The smaller closed target buffer leaves room to move in elapsed time.
Both orientations and the full diagonal, including elliptic inputs, are
retained (`app:ch_regular:lem:finite-chain`). -/
theorem exists_uniform_chart_boundary_collar
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean (d + 1))))
    (z : RootState (Euclidean d)) {β θ N : ℝ}
    (hβ : 0 < β) (hθ : 0 < θ) (hN : 0 ≤ N) :
    ∃ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (h : RootState (Euclidean d) → ℝ)
        (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
        (C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))),
        (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ →
        closedBall (z.1, z) (2 * β) ⊆ C.target →
        ContDiffOn ℝ ∞ (twoTimePhase C) C.target →
        cNorm (closedBall (z.1, z) (2 * β)) 2 (twoTimePhase C) ≤ N →
        ∀ (mi mo : LocalizerSymbol (d + 1)),
        (∀ a ∈ cthickening θ (tsupport mi), closedBall a θ ⊆ interior {q | mo q = 1}) →
        ∀ (backward : Bool) (x y : Euclidean (d + 1))
          (p : JointVariables (Euclidean (d + 1))) (r : ℝ),
        elapsedJointCoordinates (0, p) ∈ closedBall (boundaryBudgetCenter z) β →
        Φ ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
          (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2 →
        HasFDerivAt (twoTimePhase C)
          (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 p.1.1 p.2.1))
          (elapsedChartPoint 0 p.1.1 p.2.1) →
        (y, p.2.2.1) ∈ cthickening (θ / 2) (tsupport mi) →
        (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q) →
        |r| ≤ ε →
        δ ≤ Localization.phaseGradientSquare e
          (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (r, w)) p := by
  let A := ‖elapsedJointCoordinates (d := d)‖
  let H := N * A * ‖elapsedTangentialCoordinates (d := d)‖ +
    ‖elapsedTemporalCovector (d := d)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let ε := min (β / (1 + A)) (θ / (6 * (1 + H)))
  have hε : 0 < ε := lt_min (div_pos hβ (by positivity)) (div_pos hθ (by positivity))
  have hεA : A * ε ≤ β := by
    have hh := (le_div_iff₀ (by positivity : 0 < 1 + A)).mp (min_le_left
      (β / (1 + A)) (θ / (6 * (1 + H))))
    change ε * (1 + A) ≤ β at hh
    nlinarith
  have hεH : H * ε ≤ θ / 6 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6 * (1 + H))).mp (min_le_right
      (β / (1 + A)) (θ / (6 * (1 + H))))
    change ε * (6 * (1 + H)) ≤ θ at hh
    nlinarith
  have hepos := jointDirectionLoss_pos e
  refine ⟨ε, hε, (θ / 6 / jointDirectionLoss e) ^ 2, by positivity, ?_⟩
  intro h Φ C hC hbuffer hs hjet mi mo hmask backward x y p r hbase hi hphase hin hout hr
  have hbase' : elapsedJointCoordinates (0, p) ∈
      closedBall (boundaryBudgetCenter z) (2 * β) :=
    closedBall_subset_closedBall (by linarith) hbase
  have hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target :=
    hbuffer ((budgetCoordinates_mem_boundary_buffer z (2 * β)).mpr hbase')
  have hgap := elapsed_boundary_derivative_gap hθ hmask hC backward x y p hq hi hphase hin hout
  have hcoord : ‖elapsedJointCoordinates (r, p) - elapsedJointCoordinates (0, p)‖ ≤ A * |r| := by
    have hh := (elapsedJointCoordinates (d := d)).le_opNorm ((r, p) - (0, p))
    rw [map_sub] at hh
    simpa only [Prod.mk_sub_mk, sub_zero, sub_self, Prod.norm_mk, norm_zero,
      Real.norm_eq_abs, max_eq_left (abs_nonneg r)] using hh
  have hqr : elapsedJointCoordinates (r, p) ∈
      closedBall (boundaryBudgetCenter z) (2 * β) := by
    apply mem_closedBall.mpr
    have hdist : dist (elapsedJointCoordinates (r, p)) (elapsedJointCoordinates (0, p)) ≤ β :=
      (by simpa only [dist_eq_norm] using (hcoord.trans
        ((mul_le_mul_of_nonneg_left hr hA).trans hεA)))
    exact (dist_triangle _ (elapsedJointCoordinates (0, p)) _).trans
      ((add_le_add hdist (mem_closedBall.mp hbase)).trans_eq (by ring))
  obtain ⟨hsm, hj⟩ := chartPhase_secondJet_on_buffer z β C hbuffer hs hjet
  have hv := norm_elapsed_tangential_derivative_sub_le_of_secondJet backward (chartPhase C)
    x y (convex_closedBall _ _) hsm hN hj r p hqr hbase'
  change _ ≤ H * |r| at hv
  have hv' := hv.trans ((mul_le_mul_of_nonneg_left hr hH).trans hεH)
  have hn := norm_sub_norm_le
    (fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p)
    (fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (r, w)) p)
  rw [norm_sub_rev] at hn
  exact jointDerivative_gap_phaseGradientSquare e _ p (by positivity) (by linarith)

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
