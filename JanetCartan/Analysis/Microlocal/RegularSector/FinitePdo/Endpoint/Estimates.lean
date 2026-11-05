module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.RetainedConstruction
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SourceAgreement
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EndpointPdoBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteEvolution.CoordinateSobolev

/-!
# Endpoint estimates on the retained physical chart

Specialize the endpoint PDO producers to the exact physical multiplier and
the retained diagonal band. The constructor in `Construction` supplies the
literal supported amplitude on this same band. Both time variables remain
in its joint seminorm before restriction to the diagonal.
Source: `app:ch_regular_base:eq:energy-complete-residual` in `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.EvolutionIntegral.SymbolBudgets Characteristic.EndpointPdoBounds
open Characteristic.ConicPhase Characteristic.ConicAmplitude Characteristic.AmplitudeBounds
open Characteristic.UniformAmplitudes Characteristic.PdoRealization
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic FiniteEvolution RetainedConstruction
open AmplitudeBound FourierIntegral Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "H" => SpacetimeL2 d (d+1)

/-- The literal upper endpoint, index two of `directPDOSymbols`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
def selectedEndpointSymbol (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (L : ℝ) (Q : E → Fin (d+1) → Mat) (W : TwoTimeAmplitude d (d+1))
    (y ζ : E) : CMat :=
  selectedEndpointMultiplier f p L ζ •
    ((coefficient (f.chart p).index Q y 0).map Complex.ofReal *
      W (y 0) (y 0) (spatialPart y) (spatialPart ζ))

/-- The actual endpoint is the direct residual's index two for arbitrary
other ledger entries (`energy-complete-residual`). -/
theorem selectedEndpointSymbol_eq_directPDOSymbols_two
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → CMat) (W : TwoTimeAmplitude d (d+1))
    (bminus : E → E → CMat) (source : E → Euclidean d → ℂ) :
    selectedEndpointSymbol f p L Q W =
      directPDOSymbols (fun y a ↦ (coefficient (f.chart p).index Q y a).map Complex.ofReal)
        B W bminus source (selectedEndpointMultiplier f p L) 2 := rfl

/-- The smaller common output plateau, in the selected chart. Its actual
producer is `exists_finite_physical_evolution_data_with_diagonal`
(`energy-complete-residual`, `measured-adjoint`). -/
def endpointOutputMask (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (y : E) : ℂ :=
  output (physicalCoordinates (f.chart p).index y)

/-- The constructed smaller output has the precise physical support needed
by both PDO producers (`fixed-time-representation`). -/
theorem endpointOutputMask_properties
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {output : E → ℝ} (ho : ContDiff ℝ ∞ output) (hc : HasCompactSupport output)
    (hs : tsupport output ⊆ ball x f.physicalRadius) :
    ContDiff ℝ ∞ (endpointOutputMask f p output) ∧
      HasCompactSupport (endpointOutputMask f p output) ∧
      tsupport (endpointOutputMask f p output) ⊆
        closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius) := by
  let e := physicalCoordinates (f.chart p).index
  refine ⟨Complex.ofRealCLM.contDiff.comp (ho.comp e.contDiff),
    (hc.comp_left Complex.ofReal_zero).comp_homeomorph e.toHomeomorph, ?_⟩
  intro y hy
  have ht := tsupport_comp_subset_preimage (fun y ↦ (output y : ℂ)) e.continuous hy
  have hb := hs (tsupport_comp_subset Complex.ofReal_zero output ht)
  have he : dist (e y) x = dist y (e.symm x) := by
    conv_lhs => arg 2; rw [← e.apply_symm_apply x]
    rw [dist_eq_norm, ← map_sub, norm_physicalCoordinates, dist_eq_norm]
  change dist y (e.symm x) ≤ 2*f.physicalRadius
  have hh := mem_ball.mp hb
  rw [he] at hh
  linarith [f.physicalRadius_pos]

/-- Output certificate for the actual endpoint: supported low/high symbol
budgets and signed gain for the physical operator and its literal adjoint.
This is a conclusion of the construction, never an analytic assumption.
The original high reserve is `2*(d+2)+11` (`sector-theorem-residual`). -/
def EndpointPdoEstimates (i : Fin (d+1)) (KQ : Set E)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (χout χsource : E → ℂ)
    (c : E → E → CMat) (R M : ℝ) (D Dgain G : ℕ → ℝ) : Prop :=
  GraphNormalAmplitudeBounds (maskedPhysicalPDOCycleSymbol χout χsource c) R
    (D (2*(d+2)+1) * (1+M+M)) ∧
  (∀ ξ is, is.length ≤ 2*(d+2)+1 → ∀ z,
    (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
      (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
        D (2*(d+2)+1) * (1+M+M)) ∧
  (∀ m ξ is, is.length ≤ m → ∀ z,
    (1+‖ξ‖) * ‖matrixAmplitudeCoordinateDerivList is
      (maskedPhysicalPDOCycleSymbol χout χsource c ξ) z‖ ≤
        D m * (1+cNorm KQ (m+10) Q+cNorm KQ (m+10) B)) ∧
  ∀ n : ℕ,
    let T := physicalOperator i (maskedPhysicalPDO χout χsource c)
    let high := Dgain (2*(d+2)+(n+1)) *
      (1+cNorm KQ (n+(2*(d+2)+11)) Q+cNorm KQ (n+(2*(d+2)+11)) B)
    (∀ u : H, MemVectorFourierSobolev (n : ℝ) u →
      (MemVectorFourierSobolev ((n : ℝ)+1) (T u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (T u) ≤
          ((d+1 : ℝ)*(d+1)*G n) * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖)) ∧
      (MemVectorFourierSobolev ((n : ℝ)+1) (T.adjoint u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (T.adjoint u) ≤
          ((d+1 : ℝ)*(d+1)*G n) * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖))) ∧
    ∀ u : H,
      (MemVectorFourierSobolev (-(n : ℝ)) (T u) ∧
        vectorFourierSobolevNorm (-(n : ℝ)) (T u) ≤
          ((d+1 : ℝ)*(d+1)*((d+1 : ℝ)*(d+1)*G n)) *
            (1+high)*vectorFourierSobolevNorm (-((n : ℝ)+1)) u) ∧
      (MemVectorFourierSobolev (-(n : ℝ)) (T.adjoint u) ∧
        vectorFourierSobolevNorm (-(n : ℝ)) (T.adjoint u) ≤
          ((d+1 : ℝ)*(d+1)*((d+1 : ℝ)*(d+1)*G n)) *
            (1+high)*vectorFourierSobolevNorm (-((n : ℝ)+1)) u)

/-- Instantiate both endpoint PDO producers on the selected chart's exact
retained band and physical multiplier. `Construction` discharges the two
amplitude conclusions below for its SAME literal `W₁`; no endpoint budget
or operator bound is an input (`energy-complete-residual`). -/
theorem exists_selected_endpoint_constants
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (hM : 0 ≤ M)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    {L : ℝ} (hL : 0 < L) {ra rb : ℝ}
    (hcoverage : DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2
      ((f.chart p).bufferRadius/2) ra rb (selectedEndpointMultiplier f p L))
    (amplitudeCost : ℕ → ℝ) (hcost : ∀ m, 0 < amplitudeCost m)
    {output : E → ℝ} (ho : ContDiff ℝ ∞ output) (hc : HasCompactSupport output)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    let lc := f.chart p
    let e := coordinateSplit lc.index
    let z : RootState (Euclidean d) := ((e x).1, ((e x).2, (e p.val.val).2))
    let J := bufferedJetSet lc.radialSection z (lc.bufferRadius/2) ra rb
    ∃ R > (0 : ℝ), ∃ D Dgain G : ℕ → ℝ,
      (∀ m, 1 ≤ D m) ∧ (∀ m, 1 ≤ Dgain m) ∧ (∀ n, 0 ≤ G n) ∧
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
      EndpointPdoEstimates lc.index (closedBall x RQ) Q B
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p L Q W) R M D Dgain G := by
  intro lc e z J
  obtain ⟨hout, hcout, hsout⟩ := endpointOutputMask_properties f p ho hc hsupp
  obtain ⟨_, hsource, _, hcsource, _⟩ := chartPhysicalMasks_properties f p
  obtain ⟨bound, hbound⟩ := (hcout.union hcsource).exists_bound_of_continuousOn
    continuous_id.continuousOn
  let R := |bound|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hoR y (hy : y ∈ tsupport (endpointOutputMask f p output)) : ‖y‖ ≤ R :=
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
  obtain ⟨Dgain, G, hDgain, hG, hgain⟩ := exists_endpoint_integer_gain_constants lc.index
    (isCompact_closedBall x RQ) hΩ hKΩ _ hr (selectedEndpoint_physical_ball_mapsTo f p)
    J hJ amplitudeCost hcost hM _ _ _ hout hsource hβ.1 hsout hcsource R hoR hsR
    zero_le_one hcone hβ.2 (hconeBound L hL) hcover
  refine ⟨R, hR, D, Dgain, G, hD, hDgain, hG, ?_⟩
  intro Q hQ hQlow B hBlow h Φ C V angular F W hF hnorm
  have hq := (cNorm_mono_order (sectorLowOrder_bounds d).2.2).trans hQlow
  have hb := (cNorm_mono_order (sectorLowOrder_bounds d).2.2).trans hBlow
  have hbudget := hbudgets Q hQ hq B hb h Φ C V lc.timeMask lc.radialSection
    angular lc.row lc.col lc.sourceMask hF hnorm
  have hW : ContDiff ℝ ∞ (jointAmplitude W) := by
    rw [show W = curryCharacteristicMatrix F from rfl, jointAmplitude_curryCharacteristicMatrix]
    exact hF.comp evolutionToCharacteristicPoint.contDiff
  have hop := hgain Q hQ hq B hb W hW hnorm
  refine ⟨hbudget.1, hbudget.2.1, hbudget.2.2, ?_⟩
  intro n T high
  have hforward (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :=
    physicalOperator_sobolev_bound lc.index
      (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p L Q W))
      _ _ _ _ (fun v hv ↦ (hop n v hv).1) u hu
  have hadjoint (u : H) (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (T.adjoint u) ∧
      vectorFourierSobolevNorm ((n : ℝ)+1) (T.adjoint u) ≤
        ((d+1 : ℝ)*(d+1)*G n) * (vectorFourierSobolevNorm (n : ℝ) u+high*‖u‖) := by
    simpa only [T, physicalOperator_adjoint] using
      physicalOperator_sobolev_bound lc.index
        (maskedPhysicalPDO (endpointOutputMask f p output) (chartInputMask f p)
          (selectedEndpointSymbol f p L Q W)).adjoint
        _ _ _ _ (fun v hv ↦ (hop n v hv).2) u hu
  refine ⟨fun u hu ↦ ⟨hforward u hu, hadjoint u hu⟩, ?_⟩
  intro u
  have hconstant : 0 ≤ (d+1 : ℝ)*(d+1)*G n := mul_nonneg (by positivity) (hG n)
  have hhigh : 0 ≤ high := by
    apply mul_nonneg (zero_le_one.trans (hDgain _))
    linarith [cNorm_nonneg (closedBall x RQ) (n+(2*(d+2)+11)) Q,
      cNorm_nonneg (closedBall x RQ) (n+(2*(d+2)+11)) B]
  have hn := negativeVectorFourierSobolev_tame_bound_of_adjoint
    (t := (n : ℝ)+1) (Nat.cast_nonneg n) (by positivity) hconstant hhigh T hadjoint u
  have hna := negativeVectorFourierSobolev_tame_bound_of_adjoint
    (t := (n : ℝ)+1) (Nat.cast_nonneg n) (by positivity) hconstant hhigh T.adjoint
    (fun v hv ↦ by simpa only [ContinuousLinearMap.adjoint_adjoint] using hforward v hv) u
  simpa only [Nat.cast_add, Nat.cast_one] using And.intro hn hna

end JanetCartan.RegularSector.FinitePdo
