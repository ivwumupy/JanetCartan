module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# Upper-endpoint normal bound on the original chart output mask

Apply the proved endpoint budget on the retained diagonal shell band with the
original family output. This discharges PDO index two in
`completeResidual_of_common_selected_chart`; its common output is applied only
after the original supported equation. The fixed low order remains unchanged.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets Characteristic.EndpointPdoBounds
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.AmplitudeBounds
open Characteristic.UniformAmplitudes Characteristic.PdoRealization
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution
open FinitePdo FinitePdo.RetainedConstruction
open AmplitudeBound FourierIntegral Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The SAME W₁ and radial band give the normal bound for the original output
mask, before common-mask localization (`energy-complete-residual`). -/
theorem exists_original_chart_endpoint_normal_bounds
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (hM : 0 ≤ M)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {L : ℝ} (hL : 0 < L) {ra rb : ℝ}
    (hcoverage : DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2
      ((f.chart p).bufferRadius/2) ra rb (selectedEndpointMultiplier f p L))
    (amplitudeCost : ℕ → ℝ) (hcost : ∀ m, 0 < amplitudeCost m) :
    let lc := f.chart p
    let e := coordinateSplit lc.index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    let J := bufferedJetSet lc.radialSection z (lc.bufferRadius/2) ra rb
    ∃ R > (0 : ℝ), ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
    ∀ Q : E → Fin (d+1) → Mat, ContDiffOn ℝ ∞ Q Ω →
      cNorm (closedBall x RQ) (sectorLowOrder d) Q ≤ M →
    ∀ B : E → Mat, cNorm (closedBall x RQ) (sectorLowOrder d) B ≤ M →
    ∀ (h : RootState (Euclidean d) → ℝ)
      (Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d))
      (C : OpenPartialHomeomorph (Characteristic.TwoTimePoint (Euclidean d))
        (Characteristic.TwoTimePoint (Euclidean d)))
      (V : Set (Characteristic.TwoTimePoint (Euclidean d))) (angular : Euclidean d → ℝ),
      let F := collared lc.radialSection 1 angular
        (bufferedMatrix V lc.timeMask
          (pencilAmplitudeFamily lc.index Q B h Φ C lc.row lc.col lc.sourceMask 1))
      let W := curryCharacteristicMatrix F
      ContDiff ℝ ∞ F →
      (∀ m, BoundedTwoTimeOrderSeminorm 1 J m W ∧
        twoTimeOrderSeminorm 1 J m W ≤ amplitudeCost m *
          (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
          (selectedEndpointSymbol f p L Q W)) R (D (2*(d+2)+1)*(1+M+M)) := by
  intro lc e z J
  obtain ⟨hout, hsource, hcout, hcsource, _⟩ := chartPhysicalMasks_properties f p
  have hsout := chartOutputMask_support_endpointBall f p
  obtain ⟨bound, hbound⟩ := (hcout.union hcsource).exists_bound_of_continuousOn
    continuous_id.continuousOn
  let R := |bound|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hoR y (hy : y ∈ tsupport (chartOutputMask f p)) : ‖y‖ ≤ R :=
    (hbound y (Or.inl hy)).trans (by dsimp [R]; linarith [le_abs_self bound])
  have hsR y (hy : y ∈ tsupport (chartInputMask f p)) : ‖y‖ ≤ R :=
    (hbound y (Or.inr hy)).trans (by dsimp [R]; linarith [le_abs_self bound])
  obtain ⟨cone, hcone, hconeBound⟩ :=
    exists_selectedEndpointMultiplier_temporal_cone f p hρb hsrcρ
  have hβ := selectedEndpointMultiplier_bounds f p L
  have hcover := hcoverage.selectedEndpoint_mapsTo f p
  have hr : 0 < 2*f.physicalRadius := mul_pos (by norm_num) f.physicalRadius_pos
  have hJ : IsCompact J := isCompact_bufferedJetSet _ _ _ _ _
  obtain ⟨D, hD, hbudgets⟩ := exists_supported_endpoint_pdo_budgets lc.index
    (isCompact_closedBall x RQ) hΩ hKΩ _ hr (selectedEndpoint_physical_ball_mapsTo f p)
    J hJ amplitudeCost hcost hM _ _ _ hout hsource hβ.1 hsout hcsource R hoR hsR
    zero_le_one hcone hβ.2 (hconeBound L hL) hcover
  refine ⟨R, hR, D, hD, ?_⟩
  intro Q hQ hQlow B hBlow h Φ C V angular F W hF hnorm
  exact (hbudgets Q hQ ((cNorm_mono_order (sectorLowOrder_bounds d).2.2).trans hQlow)
    B ((cNorm_mono_order (sectorLowOrder_bounds d).2.2).trans hBlow)
    h Φ C V lc.timeMask lc.radialSection angular lc.row lc.col lc.sourceMask hF hnorm).1

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
