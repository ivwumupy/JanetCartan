module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.Endpoint

/-!
# Selected source and endpoint joint PDO grades

The source has order zero and the upper endpoint has order minus one, both
with offset zero. The derivatives include the complete packed amplitude's
covariables and both diagonal time slots of the SAME retained `W₁`. The
noncomparable grades retain the branch-radius weight. All profiles precede
the coefficients, slow scale, source frequency and requested accuracy.
The source threshold remains `2 * threshold` throughout.

The geometric inputs are retained by the selected finite construction;
the analytic inputs are the original coefficient profile and its retained
joint amplitude seminorm estimates. No PDO grade or operator bound is an
assumption. The parent combines these results with the algebraic branch.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`, and `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteAssembly RegularSector.FinitePdo
open RegularSector.FinitePdo.RetainedConstruction
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FiniteAlgebraic
open RegularSector.Characteristic RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EndpointPdoBounds RegularSector.Characteristic.ConicPhase
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FiniteChain.Graph FiniteChain.Graph.PhysicalShells
open FiniteChain.Graph.PhysicalShells.Comparable FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Z" => RootState (Euclidean d)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)

/-- The SAME retained upper endpoint supplies both symbol-grade inputs of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`,
on its exact `Kpdo` and every noncomparable shell. The original coefficient
reserve ten and nine is supplied by `exists_finite_direct_operator_bounds`
and transferred by `exists_selected_amplitude_order_profile`. The geometric
`hcoverage` is the `DiagonalFrequencyCoverage` component of
`SelectedChartEndpointAt`, produced by `exists_finite_physical_endpoint_pdos`.
The caller must retain it when selecting the SAME `ra,rb` used for the
amplitude seminorms: `FiniteAssembly.RetardedSums` currently selects that
component internally and projects it away in its separate band output. The
buffer inequalities, smoothness and seminorms come from the same finite
construction. Both orientations have order
minus one and offset zero, before the parent's common-order domination.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`,
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_selected_endpoint_completeFactor_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hΩ : IsOpen Ω) (hball : closedBall x RQ ⊆ Ω)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (hbuffer : ∀ p, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hmask : ∀ p, (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (ra rb : f.centers → ℝ)
    (hcoverage : ∀ p, DiagonalFrequencyCoverage (f.chart p).radialSection
      (coordinateSplit (f.chart p).index p.val.val).2 ((f.chart p).bufferRadius/2)
      (ra p) (rb p) (selectedEndpointMultiplier f p threshold))
    (cost : f.centers → ℕ → ℝ) (hcost : ∀ p m, 0 < cost p m)
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) {a b : ℝ} (ha : 0 < a) :
    let Kb := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    let Kpdo := fun p ↦ comparableJointCarrier 1 1 a b
      ((Prod.fst '' Kb p) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      (Kb p) (frequencyAnnulus a b)
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ (Rstar : ℕ), 10 ≤ Rstar → ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ (Q : E → Fin (d+1) → Mat) (B : E → Mat), ContDiffOn ℝ ∞ Q Ω →
      (∀ m, cNorm (closedBall x RQ) m Q ≤ AQ m * L ^ (m-Rstar)) →
      (∀ m, cNorm (closedBall x RQ) m B ≤ AQ m * L ^ (m-Rstar)) →
      ∀ (Φ : f.centers → Z × ℝ → Z) (C : f.centers → OpenPartialHomeomorph T T)
        (angular : f.centers → Euclidean d → ℝ),
      let J := fun p ↦
        let e := coordinateSplit (f.chart p).index
        let z : Z := ((e x).1, ((e x).2, (e p.val.val).2))
        bufferedJetSet (f.chart p).radialSection z ((f.chart p).bufferRadius/2) (ra p) (rb p)
      let W := fun p ↦ selectedConicAmplitude f p Q B (Φ p) (C p) (angular p)
      (∀ p, ContDiff ℝ ∞ (jointAmplitude (W p 1))) →
      (∀ p j m, BoundedTwoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ∧
        twoTimeOrderSeminorm (if j=0 then 0 else 1) (J p) m (W p j) ≤
          cost p m * (1+cNorm (closedBall x RQ) (m+10) Q+cNorm (closedBall x RQ) (m+9) B)) →
      ∀ p backward,
      let A := orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedEndpointSymbol f p threshold Q (W p 1))
      (∀ v ∈ Kpdo p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (-1 : ℝ) * D m * L ^ (m+0)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l)) ^ (-1 : ℝ) * D m * L ^ (m+0)) := by
  intro Kb Kpdo
  have hKb p : IsCompact (Kb p) :=
    (endpointOutputMask_properties f p ho hoc hout).2.1.prod
      (chartPhysicalMasks_properties f p).2.2.2.1
  have hKpdo p : IsCompact (Kpdo p) :=
    isCompact_comparableJointCarrier 1 1 a b
      (((hKb p).image continuous_fst).prod (isCompact_frequencyAnnulus _ _))
      (hKb p) (isCompact_frequencyAnnulus _ _)
  have hpos p : ∀ v ∈ Kpdo p, v.1.1 ∈ tsupport (endpointOutputMask f p output) :=
    fun _ hv ↦ hv.1.1.1
  have hfreq p : ∀ v ∈ Kpdo p, a / (16 * annulusFactor 1 1) ≤ ‖v.2.1‖ :=
    fun _ hv ↦ hv.1.2.1.1
  have ha' : 0 < a / (16 * annulusFactor 1 1) :=
    div_pos ha (by have := two_le_annulusFactor 1 1; positivity)
  obtain ⟨DW, hDW, hamp⟩ := exists_selected_amplitude_order_profile f ra rb cost hcost AQ hAQ
  obtain ⟨D, hD, hgrade⟩ := exists_selected_endpoint_symbol_grades f hΩ hball threshold ht hft
    output ho hoc hout hbuffer hmask ra rb hcoverage Kpdo hKpdo hpos ha' hfreq AQ DW hAQ hDW
  refine ⟨D, hD, ?_⟩
  intro Rstar hRstar L ρ hL hρ Q B hQ hQbound hBbound Φ C angular J W hW hb p backward A
  have hb' p m : BoundedTwoTimeOrderSeminorm 1 (J p) m (W p 1) ∧
      twoTimeOrderSeminorm 1 (J p) m (W p 1) ≤ DW m * L ^ m := by
    simpa only [show (1 : Fin 3) ≠ 0 by decide, ↓reduceIte] using
      hamp Rstar hRstar L hL Q B hQbound hBbound Φ C angular hb p 1 m
  simpa only [Real.rpow_neg_one] using
    hgrade Rstar L ρ hL hρ Q hQ hQbound (fun p ↦ W p 1) hW hb' p backward

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
