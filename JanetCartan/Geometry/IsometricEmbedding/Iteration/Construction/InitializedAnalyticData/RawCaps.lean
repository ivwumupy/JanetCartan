module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.SuppliedRawGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.IncidenceMasks

/-!
# Raw-adjoint caps before the original incidence cover

The source/corrected inverse selector accepts a positive extra physical cap at
every candidate incidence and original cell. This module constructs that function
from the original leading geometry. At every cell which can actually be selected,
the value is the proved generic-current raw cap and its full continuation is retained.

Consumers: `RawCappedInitialization`'s `aExtra` argument and the same-row history raw
adjoint in `UniformHistoryCorrection` (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.InitializedAnalyticData
open ContinuumInverse ContinuumAdjoint ContinuumRow
open ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.RetainedCellAdjoint
open DerivativeKernels ModifiedNormalSymbol PhaseExtension AmplitudeProfiles
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude ProjectedStressFrame CarrierSobolev
open LeadingPrimitive LeadingWave.FullModulation Pseudodifferential RetainedLeading
open ContinuumRow.TransportKernel AmplitudeBound CanonicalCarrier CanonicalConic
open ContinuumNormalReduction.TransportSymbol

variable {n : ℕ} {D : CoverData n} {c C : ℝ}
  (hn : 0 < n) (hD : D.IsValid c C)
  {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
    PatchQuantitativeFamily (D.patches b l) U hU)
  (I : (b : Fin D.chartCount) → Fin (D.patchCount b) → Type*)
  {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
  (hball : ∀ b l, closedBall (0 : Euclidean n) (T b l).data.localReference.stateRadius ⊆ K)
  (Kinitial : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
    I b l → Set (Euclidean (n - 1) × Euclidean 3))
  (Jfull : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
    I b l → Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
  (hJfull : ∀ b l j, IsCompact (Jfull b l j))
  (E : (b : Fin D.chartCount) → (l : Fin (D.patchCount b)) →
    I b l → Set (Euclidean n × CarrierParameter))
  (hE : ∀ b l j, IsOpen (E b l j))
  (hgraph : ∀ b l j, MapsTo (carrierGraph (T b l)) (E b l j) (Jfull b l j))

/-- The actual extra mask cap for every candidate original incidence/cell.
On selectable cells it comes from the proved normal and phase cap producer;
elsewhere the positive default is harmless because the selector retains membership
in the chosen cell (`app:ch_background:defn:bg-row`, `new:sec:order-of-choices`). -/
def retainedIncidenceCurrentRawCap
    (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : I p.1.1 l) :
    {ε : ℝ // 0 < ε} := by
  classical
  by_cases hmem : chartCenter (D.roots p.1.1 l p.1.2) ∈ E p.1.1 l j
  · have hz := ((hD.2.2.2.2.1 p.1.1 l).2.2.1 p.1.2 p.2.2).1
    have hcap := exists_current_rawAdjoint_cap_on_supplied_geometry (N := embeddingDimension n)
      hn (hD.2.2.2.2.1 p.1.1 l).1 (T p.1.1 l) hK hKU (hball p.1.1 l)
      (Kinitial p.1.1 l j) (hJfull p.1.1 l j) (E p.1.1 l j) (hE p.1.1 l j)
      (hgraph p.1.1 l j) hz hmem
    exact ⟨hcap.choose, hcap.choose_spec.1⟩
  · exact ⟨1, zero_lt_one⟩

/-- On the SAME cell chosen by the original incidence cover, the cap used by
its masks retains all generic-current raw bounds. No new mask, operator or
normal chart is chosen in this deduction (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`). -/
theorem retainedIncidenceCurrentRawCap_spec
    (p : IncidenceCenter D) (l : Fin (D.patchCount p.1.1)) (j : I p.1.1 l)
    (hmem : chartCenter (D.roots p.1.1 l p.1.2) ∈ E p.1.1 l j) :
    let aCap := (retainedIncidenceCurrentRawCap hn hD T I hK hKU hball
      Kinitial Jfull hJfull E hE hgraph p l j).val
    let N := embeddingDimension n
    let P := D.patches p.1.1 l
    let T := T p.1.1 l
    let z₀ := D.roots p.1.1 l p.1.2
    let Kinitial := Kinitial p.1.1 l j
    let J := Jfull p.1.1 l j
    let E := E p.1.1 l j
    ∃ δ > (0 : ℝ),
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
  classical
  have hz := ((hD.2.2.2.2.1 p.1.1 l).2.2.1 p.1.2 p.2.2).1
  have hcap := exists_current_rawAdjoint_cap_on_supplied_geometry (N := embeddingDimension n)
    hn (hD.2.2.2.2.1 p.1.1 l).1 (T p.1.1 l) hK hKU (hball p.1.1 l)
    (Kinitial p.1.1 l j) (hJfull p.1.1 l j) (E p.1.1 l j) (hE p.1.1 l j)
    (hgraph p.1.1 l j) hz hmem
  simpa only [retainedIncidenceCurrentRawCap, dite_eq_left hmem] using hcap.choose_spec.2

end JanetCartan.InitializedAnalyticData
