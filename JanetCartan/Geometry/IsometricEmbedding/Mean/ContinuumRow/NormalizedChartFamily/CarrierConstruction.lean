module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedChartFamily.LiftConstruction
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading.ChartAdapter

/-!
# Actual carrier charts with their autonomous ODE witness

The original coefficient domain, low bound, adapted buffer and existence time
are supplied before the immersion. Primitive coefficient outputs feed the
existing chart adapter. Both chart maps are literal restrictions of the same
constructed lift; no identity outside the flow tube is inferred from inverse
laws on that tube.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedChartFamily
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference.FlowConstruction

/-- Construct every ODE field of the existing `Chart` on the original supplied
buffers and retain the SAME smooth lift. The coefficient premises are precisely
the primitive outputs of
`CurrentCoefficientProfiles.exists_transport_coefficient_bounds_before_geometry`,
also retained by the full-leading producer. The formula for the inverse is
global, hence supplies the full-cylinder inverse-witness premise of
`NormalizedFlowProfiles`; the old inverse laws alone would not supply it
(`app:ch_waves:thm:leading`, `app:ch_waves:eq:joint-tame`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_carrier_chart_with_lift
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (hQ : Q.1 = ProjectedStressFrame.projectedStress F)
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {p₀ : Euclidean (n - 1) × Euclidean 3} {R B τ g : ℝ} {row col : Fin n}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hτ : τ = existenceTime R (liftedLowBound T B) / 4)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, p₀) R) K)
    (hk : ContDiffOn ℝ ∞ (carrierNullvector T Q col) Ω)
    (hl : ContDiffOn ℝ ∞ (carrierConullvector T Q row) Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    (hc : ContDiffOn ℝ ∞ (carrierTransportPotential T Q F row col) Ω)
    (hlow : cNorm K 1 (carrierTransportDirection T Q row col) ≤ B)
    (hsymm : ∀ w ∈ Ω, ∀ i, (Q.1 w.1 i).IsSymm)
    (hnull : ∀ w ∈ Ω,
      carrierNullvector T Q col w ≠ 0 ∧ carrierConullvector T Q row w ≠ 0 ∧
      reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
        (fun j ↦ carrierNullvector T Q col w j) = 0 ∧
      carrierConullvector T Q row w ᵥ*
        reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
      g ≤ |carrierAdaptedDenominator T Q row col w| ∧
      carrierAdaptedDenominator T Q row col w ≠ 0 ∧
      |(carrierAdaptedDenominator T Q row col w)⁻¹| ≤ g⁻¹) :
    ∃ c : Chart T Ω K p₀ R B τ row col F,
      ∃ Ψ : (ℝ × (Euclidean (n - 1) × Euclidean 3)) × ℝ →
          ℝ × (Euclidean (n - 1) × Euclidean 3),
        c.Q = Q ∧
        ODE.IsSmoothFlowOn (liftedDirection T c.Q row col) (0, p₀) R (R / 2)
          (existenceTime R (liftedLowBound T B)) Ψ ∧
        c.forward = forwardFromLift Ψ ∧ c.inverse = footpointFromLift Ψ := by
  subst τ
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  have hb (q) (hq : q ∈ closedBall ((0 : ℝ), p₀) R) :=
    liftedDirection_low_bounds T Q row col hΩ hd hK hKΩ hB hlow (hbuffer hq)
  obtain ⟨Ψ, hΨ, D, hD, hsmall, hbig, himage, hcoeff, hφ, hy, hφD, hyD,
    hi, hyφ, hφy, hφz, hyz, hode, hφwide, hywide⟩ :=
    exists_buffered_chart_with_lift (hΩ.preimage C.symm.continuous)
      (fun q hq ↦ hKΩ (hbuffer hq)) (contDiffOn_liftedDirection T Q row col hd)
      hR (liftedLowBound_nonneg T hB) hb (fun _ ↦ rfl) (fun _ ↦ rfl)
  let c := RetainedLeading.chartOfRetainedCarrierData T Q F hQ D
    (forwardFromLift Ψ) (footpointFromLift Ψ) hk hl hd hc hlow hsymm hnull
    himage hcoeff hφ hy hφz hyz hywide hD hsmall hbig hφD hyD hi hyφ hφy hode hφwide
  exact ⟨c, Ψ, rfl, hΨ, rfl, rfl⟩

end JanetCartan.ContinuumRow.NormalizedChartFamily
