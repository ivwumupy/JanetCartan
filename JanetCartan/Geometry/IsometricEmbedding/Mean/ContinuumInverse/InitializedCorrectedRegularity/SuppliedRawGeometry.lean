module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.SuppliedRaw
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.SuppliedNormalGeometry

/-!
# Raw adjoints from the original retained conic certificates

The physical profile cap is chosen before the incidence masks. On every
supplied mask below that cap, the original conic certificates produce all
normal jets and geometric fields required by the raw endpoint. The original
full-leading estimate produces its remaining amplitude and trade profiles.

Consumer: the actual admitted-history raw adjoints in the common measured
initializer. `RawCappedInitialization` retains the fixed buffer data and the
varying conic certificates used here, while its extra-cap field enforces this
theorem's `aCap` on the original masks.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumInverse
open ContinuumAdjoint ContinuumRow
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.NormalInputs
open DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude ProjectedStressFrame CarrierSobolev
open LeadingPrimitive LeadingWave.FullModulation CanonicalCarrier CanonicalConic
open ContinuumNormalReduction.TransportSymbol

/-- The actual retained conic data and original leading estimates give the
raw bound on any supplied carrier with its literal adjoint. Both the normal
jet estimate and every raw-profile input are proved by their concrete
producers. The cap precedes masks and all map/scalar budgets; the raw high
shift remains `2*(n+1)+14` (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_current_rawAdjoint_cap_on_supplied_geometry {n N : ℕ} (hn : 0 < n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hFball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    {J : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))} (hJ : IsCompact J)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E J)
    {z₀ : Euclidean 3} (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hcenter : chartCenter z₀ ∈ E) :
    ∃ aCap > (0 : ℝ), ∃ δ > (0 : ℝ),
    ∀ {aMask : ℝ} (haMask : 0 < aMask) (hcellMask : 4 * aMask < 1 / 2), aMask ≤ aCap →
    ∀ {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0) {rMask : ℝ} (hrMask : 0 < rMask),
    ∀ {r a ρ τ ε : ℝ},
      0 < r → 0 < a → 6 * a ≤ r → 6 * a < T.family.radius →
      rMask ≤ r → aMask ≤ a → 0 < ρ → 0 < τ → 0 < ε →
      4 * aMask < ρ → rMask ≤ ρ →
      (closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) →
    ∀ (D : CoefficientNormCharts n) (p₀ : InputVariables n),
      p₀ = (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) →
    ∀ (q₀ : ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
      (A : InputVariables n ≃L[ℝ] ContinuumNormalReduction.TransportSymbol.Variables n × Euclidean 2)
      {W Bi : Set (InputVariables n)},
      IsOpen W → closedBall p₀ ρ ⊆ W → IsCompact Bi → W ⊆ Bi →
      D.field.region ⊆ PhaseExtension.extensionDomain T →
    ∀ {It : Set ℝ}, IsOpen It → Icc (0 : ℝ) 1 ⊆ It →
      (∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region) →
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier) →
      (∀ p ∈ Bi, ε ≤ ‖p.2.2‖) →
    ∀ {β cJ : ℝ}, 0 < cJ →
    ∀ {Vinv Linv : Set (ℝ × Euclidean (n - 1))}, IsOpen Vinv → Linv ⊆ Vinv →
    ∀ G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) →
    ∀ {MF Mr κmet κ : ℝ}, 0 ≤ MF → 0 ≤ Mr → 0 < κmet → 0 < κ →
    ∃ Cbound : ℕ → ℝ, (∀ s, 0 ≤ Cbound s) ∧
    ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) →
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
        Vinv Linv β cJ G →
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖) →
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) →
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) →
      (∀ p ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) →
      (∀ x : ContinuumNormalReduction.TransportSymbol.Variables n,
        ‖x.2.2‖ = (1 / 4 : ℝ) → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb rMask aMask) → (x, v) ∈ closedBall q₀ τ) →
    ∀ (row col : Fin n)
      (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
      (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
      (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
      (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
      (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T → J ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      ContDiffOn ℝ ∞
        (fun w ↦ scalarAmplitude T Q F row col Φ Y initial w • nullvector T Q col w) O →
      (∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T Q F row col φ y initial w) →
      cNorm Kinitial (2 * (n + 1) + 14) initial ≤ Mr →
      (∀ j, cNorm J j (fullNormal T Q F row col Φ Y initial) ≤
        Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial)) →
    let d := data T Q F row col φ y initial haMask hcellMask
      (angularMask z₀ (NormedSpace.normalize ηb) haMask (angularWidth_spec hηb hrMask).1)
      FixedCutoffs.highFrequency
    ∀ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ w, Vop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral d w) →
      ∀ s : ℕ, ∀ v : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
        MemRawSobolev s (Vop.adjoint (PeriodicSobolevSpace.toL2 s v)) ∧
        rawSobolevNorm s (Vop.adjoint (PeriodicSobolevSpace.toL2 s v)) ≤
          Cbound s * (‖v‖ + (1 + cNorm K (s + 2 * (n + 1) + 14) F +
            cNorm Kinitial (s + 2 * (n + 1) + 14) initial) *
              ‖PeriodicSobolevSpace.toL2 s v‖) := by
  obtain ⟨aCap, haCap, aPhase, haPhase, hcapPhase, δ, hδ, hraw⟩ :=
    exists_generic_current_rawAdjoint_cap (N := N) hn hP T hK hKU hFball Kinitial hJ
      E hE hgraph hz₀ hcenter
  refine ⟨aCap, haCap, δ, hδ, ?_⟩
  intro aMask haMask hcellMask hmaskCap ηb hηb rMask hrMask r a ρ τ ε
    hr ha har haR hrr haa hρ hτ hε hphysical hradial hcarrier
    D p₀ hp₀ q₀ A W Bi hW hball hBi hWBi hphaseDomain
    It hIt hIT hsegI hseg hfrequency β cJ hcJ Vinv Linv hVinv hLVinv G
    Bfull hBfull MF Mr κmet κ hMF hMr hκmet hκ
  have hMaskPhase : aMask < aPhase := hmaskCap.trans_lt hcapPhase
  obtain ⟨Bnormal, _hBnormal, hnormalGeometry⟩ := exists_supplied_retained_normal_geometry
    (N := N) T hP hηb hr ha hrMask haMask har haR hrr haa hMaskPhase
    hρ hτ hε hphysical hradial hcarrier D p₀ hp₀ q₀ A hW hball hBi hWBi hphaseDomain
    hIt hIT hsegI hseg hfrequency hcJ hVinv hLVinv G hK hKU hFball hMF hκmet hκ
  obtain ⟨Cbound, hCbound, hraw⟩ := hraw haMask hcellMask hmaskCap hηb hrMask
    Bfull hBfull hMF hMr hκmet hκ Bnormal (cJ / ‖ηb‖)
  refine ⟨Cbound, hCbound, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow hclose Q
    hf hInv htrans houtput hrange hhalf hshell
    row col φ y Φ Y initial O Vcomp hO hOU hOdom hJO hgraphO hcompE hnull hcomp hIM hfull
  obtain ⟨_hn, hg, _hX, _hZ, _hΩ, _hΩunit, hrAmplitude, he, hei, hdom,
    hpush, hD, hΨ, hinj, hinverse, hphaseNormal, hJnormal, _hJdomain, hclosed, himage⟩ :=
    hnormalGeometry F hF hi hrank ((cNorm_mono_order (by omega)).trans hFM)
      hmet hnormal hlow hf hInv htrans houtput hrange hhalf hshell
  exact hraw F hF hi hrank hFM hmet hnormal hlow hclose
    row col φ y Φ Y initial O Vcomp hO hOU hOdom hJO hgraphO hcompE hnull hcomp hIM hfull
    (normalChart T Q z₀ ηb r (6 * a) aPhase)
    (normalJetRescaling T Q z₀ ηb r (6 * a) aPhase) hg hrAmplitude he hei hdom
    hpush hD hΨ hinj hinverse hphaseNormal hJnormal hclosed himage

end JanetCartan.ContinuumInverse
