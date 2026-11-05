module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.Stationarity
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.BufferedJets
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.Margins

/-!
# Quantitative separation at the full elapsed boundary

The diagonal branch of `exists_uniform_nested_physicalDirectLocalizers`,
transported by `canonicalProofLocalizer_complete_image_closed_shoulder`, supplies
the closed-ball plateau below. The gap uses no characteristic-energy condition
and retains the entire closed input shoulder and output complement. Consumer:
the common boundary collar in `app:ch_regular:lem:finite-chain` and
`app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open RegularSector.Characteristic RegularSector.Characteristic.EvolutionIntegral
open EvolutionIntegratedLocalization FiniteChain.Graph

variable {d : ℕ}

/-- The actual zero-time canonical derivatives are the full diagonal, at
every temporal covector (`app:ch_regular:eq:joint-stationary`). -/
theorem elapsed_boundary_canonical_derivatives
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    {u ξ : Euclidean (d + 1)} (hq : elapsedChartPoint 0 u ξ ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 u ξ)).2, 0) =
      (C.symm (elapsedChartPoint 0 u ξ)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 u ξ)) (elapsedChartPoint 0 u ξ)) :
    fderiv ℝ (fun v ↦ elapsedPhase (chartPhase C) 0 v ξ) u = innerSL ℝ ξ ∧
      fderiv ℝ (elapsedPhase (chartPhase C) 0 u) ξ = innerSL ℝ u := by
  have hrel := (forwardRelation_elapsedChartPhase_iff hphase).mpr ⟨rfl, rfl⟩
  obtain ⟨hb, hf⟩ := elapsed_graph_zero_diagonal hC hq hi hphase hrel
  exact ⟨by rw [(hasFDerivAt_elapsedChartPhase_output hphase).fderiv, hf],
    by rw [(hasFDerivAt_elapsedChartPhase_covector hphase).fderiv, hb]⟩

/-- Quantitative distance to the full diagonal from its two canonical
derivatives. The conic extension uses the same estimate after transferring
its zero-time germ (`app:ch_regular:eq:joint-stationary`). -/
theorem jointPhase_diagonal_distance_le
    (φ : Euclidean (d + 1) → Euclidean (d + 1) → ℝ)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hd : DifferentiableAt ℝ (Function.uncurry φ) (p.1.1, p.2.1))
    (hu : fderiv ℝ (fun v ↦ φ v p.2.1) p.1.1 = innerSL ℝ p.2.1)
    (hξ : fderiv ℝ (φ p.1.1) p.2.1 = innerSL ℝ p.1.1) :
    dist (x, p.2.2.2) (y, p.2.2.1) ≤ 3 * ‖fderiv ℝ (jointPhase backward φ x y) p‖ := by
  rw [Prod.dist_eq, max_le_iff]
  cases backward
  · obtain ⟨h1, h2, h3, h4, h5⟩ :=
      forward_joint_derivative_bounds φ x y p hd
    rw [hu, ← map_sub, innerSL_apply_norm] at h1
    rw [hξ, ← map_sub, innerSL_apply_norm] at h3
    constructor
    · have hh := (norm_sub_le_norm_sub_add_norm_sub x p.1.1 y).trans
        (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub p.1.1 p.1.2 y) _)
      rw [dist_eq_norm]
      change _ ≤ 3 * ‖fderiv ℝ (jointPhase false φ x y) p‖
      linarith
    · have hh := norm_sub_le_norm_sub_add_norm_sub p.2.2.2 p.2.1 p.2.2.1
      rw [norm_sub_rev p.2.2.2 p.2.1, norm_sub_rev p.2.1 p.2.2.1] at hh
      rw [dist_eq_norm]
      change _ ≤ 3 * ‖fderiv ℝ (jointPhase false φ x y) p‖
      linarith [norm_nonneg (fderiv ℝ (jointPhase false φ x y) p)]
  · obtain ⟨h1, h2, h3, h4, h5⟩ :=
      reverse_joint_derivative_bounds φ x y p hd
    rw [hu, ← map_sub, innerSL_apply_norm] at h1
    rw [hξ, ← map_sub, innerSL_apply_norm] at h3
    constructor
    · have hh := (norm_sub_le_norm_sub_add_norm_sub x p.1.2 y).trans
        (add_le_add_right (norm_sub_le_norm_sub_add_norm_sub p.1.2 p.1.1 y) _)
      rw [dist_eq_norm]
      change _ ≤ 3 * ‖fderiv ℝ (jointPhase true φ x y) p‖
      linarith
    · have hh := norm_sub_le_norm_sub_add_norm_sub p.2.2.2 p.2.1 p.2.2.1
      rw [norm_sub_rev p.2.2.2 p.2.1, norm_sub_rev p.2.1 p.2.2.1] at hh
      rw [dist_eq_norm]
      change _ ≤ 3 * ‖fderiv ℝ (jointPhase true φ x y) p‖
      linarith [norm_nonneg (fderiv ℝ (jointPhase true φ x y) p)]


/-- All five boundary equations quantitatively control distance to the full
diagonal, in either orientation. The constant is independent of the current
coefficient and chart (`app:ch_regular:lem:finite-chain`). -/
theorem elapsed_boundary_diagonal_distance_le
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
      (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 p.1.1 p.2.1))
      (elapsedChartPoint 0 p.1.1 p.2.1)) :
    dist (x, p.2.2.2) (y, p.2.2.1) ≤
      3 * ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p‖ := by
  obtain ⟨hu, hξ⟩ := elapsed_boundary_canonical_derivatives hC hq hi hphase
  change dist (x, p.2.2.2) (y, p.2.2.1) ≤
    3 * ‖fderiv ℝ (jointPhase backward (elapsedPhase (chartPhase C) 0) x y) p‖
  exact jointPhase_diagonal_distance_le (elapsedPhase (chartPhase C) 0) backward x y p
    (differentiableAt_elapsedChartPhase_uncurry hphase) hu hξ

/-- The producer's closed diagonal shoulder gives a quantitative boundary
gap on the full complementary support. The gap precedes the varying geometry
(`app:ch_regular:eq:chain-tail`). -/
theorem elapsed_boundary_derivative_gap
    {θ : ℝ} (hθ : 0 < θ) {mi mo : LocalizerSymbol (d + 1)}
    (hbuffer : ∀ a ∈ cthickening θ (tsupport mi),
      closedBall a θ ⊆ interior {q | mo q = 1})
    {h : RootState (Euclidean d) → ℝ}
    {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    {C : OpenPartialHomeomorph (TwoTimePoint (Euclidean d)) (TwoTimePoint (Euclidean d))}
    (hC : (C : TwoTimePoint (Euclidean d) → TwoTimePoint (Euclidean d)) = twoTimeProjection Φ)
    (backward : Bool) (x y : Euclidean (d + 1)) (p : JointVariables (Euclidean (d + 1)))
    (hq : elapsedChartPoint 0 p.1.1 p.2.1 ∈ C.target)
    (hi : Φ ((C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2, 0) =
      (C.symm (elapsedChartPoint 0 p.1.1 p.2.1)).2)
    (hphase : HasFDerivAt (twoTimePhase C)
      (twoTimePhaseDifferential h Φ C (elapsedChartPoint 0 p.1.1 p.2.1))
      (elapsedChartPoint 0 p.1.1 p.2.1))
    (hin : (y, p.2.2.1) ∈ cthickening (θ / 2) (tsupport mi))
    (hout : (x, p.2.2.2) ∈ tsupport (fun q ↦ 1 - mo q)) :
    θ / 3 ≤ ‖fderiv ℝ (fun w ↦ jointElapsedPhase backward (chartPhase C) x y (0, w)) p‖ := by
  have hsep : θ < dist (x, p.2.2.2) (y, p.2.2.1) := by
    by_contra hn
    exact notMem_complement_tsupport_of_mem_plateau
      (hbuffer _ (cthickening_mono (by linarith : θ / 2 ≤ θ) _ hin)
        (mem_closedBall.mpr (not_lt.mp hn))) hout
  have hd := elapsed_boundary_diagonal_distance_le hC backward x y p hq hi hphase
  linarith

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
