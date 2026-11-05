module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.AdaptedCoefficients
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Uniform finite null-direction norms under source contraction

For `app:ch_background:eq:bg-Nsigma` and
`app:ch_background:prop:bg-normalized`. The actual current direction is a
contracting linear pullback of the seed direction on a fixed ball. Consumer:
the uniform ODE-footpoint finite norms in `MatchedFlows`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open SourceMatching HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase NullTransport

/-- Every finite direction norm is bounded by the SAME seed norm, with
factor `m + 1`, for every positive contraction. The proof uses the exact
retained Hamilton matching and linear pullback estimates. No continuity of
an inverse or amplitude is assumed. Consumer: the actual ODE estimates in
`exists_retained_source_matched_null_flows`.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`. -/
theorem current_carrierTransportDirection_uniform_finite_bound
    {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    (row col : Fin n) {z₀ : Euclidean 3} {ρ r : ℝ} (hρr : ρ < r)
    (hpatch : ball ((0 : Euclidean n), z₀) r ⊆ ball 0 T.physicalRadius ×ˢ
      FrozenMenu.parameterCube (2 * P.radius))
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q₀ row col) (ball (0, z₀) r))
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ)) (m : ℕ) :
    ContDiffOn ℝ ∞ (carrierTransportDirection T Qσ row col) (ball (0, z₀) r) ∧
    cNorm (closedBall (0, z₀) ρ) m (carrierTransportDirection T Qσ row col) ≤
      (m + 1) * cNorm (closedBall (0, z₀) ρ) m (carrierTransportDirection T Q₀ row col) := by
  let L : (Euclidean n × Euclidean 3) →L[ℝ] (Euclidean n × Euclidean 3) :=
    (σ • ContinuousLinearMap.id ℝ (Euclidean n)).prodMap
      (ContinuousLinearMap.id ℝ (Euclidean 3))
  have hnorm (x : Euclidean n) : ‖σ • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
    exact mul_le_of_le_one_left (norm_nonneg x) hσ1
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro w
    change max ‖σ • w.1‖ ‖w.2‖ ≤ 1 * max ‖w.1‖ ‖w.2‖
    rw [one_mul]
    exact max_le_max (hnorm _) le_rfl
  have hmaps : MapsTo L (ball (0, z₀) r) (ball (0, z₀) r) := by
    intro w hw
    change (σ • w.1, w.2) ∈ ball (0, z₀) r
    simp only [mem_ball, Prod.dist_eq, max_lt_iff, dist_zero_right] at hw ⊢
    exact ⟨(hnorm _).trans_lt hw.1, hw.2⟩
  have hmapsK : MapsTo L (closedBall (0, z₀) ρ) (closedBall (0, z₀) ρ) := by
    intro w hw
    change (σ • w.1, w.2) ∈ closedBall (0, z₀) ρ
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff, dist_zero_right] at hw ⊢
    exact ⟨(hnorm _).trans hw.1, hw.2⟩
  have he : EqOn (carrierTransportDirection T Qσ row col)
      (carrierTransportDirection T Q₀ row col ∘ L) (ball (0, z₀) r) := by
    intro w hw
    change carrierTransportDirection T Qσ row col (w.1, w.2) =
      carrierTransportDirection T Q₀ row col (σ • w.1, w.2)
    have hp : w ∈ ball 0 T.physicalRadius ×ˢ
        FrozenMenu.parameterCube (2 * P.radius) := hpatch hw
    exact current_carrierTransportDirection_source_dilation T Q₀ Qσ hF hrank
      hphysical hseed htrans hσ hσ1 hscaled row col (x := w.1) hp.1 (z := w.2) hp.2
  refine ⟨(hd.comp L.contDiff.contDiffOn hmaps).congr he, ?_⟩
  have hnormeq : cNorm (closedBall (0, z₀) ρ) m (carrierTransportDirection T Qσ row col) =
      cNorm (closedBall (0, z₀) ρ) m (carrierTransportDirection T Q₀ row col ∘ L) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro w hw
    exact eventuallyEq_of_mem (isOpen_ball.mem_nhds (closedBall_subset_ball hρr hw))
      (fun v hv ↦ he hv)
  rw [hnormeq]
  exact
    FullPhaseCharts.InverseEstimates.cNorm_comp_contraction_le_on L hL
      (isCompact_closedBall _ _) isOpen_ball (closedBall_subset_ball hρr) hd hmapsK m

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
