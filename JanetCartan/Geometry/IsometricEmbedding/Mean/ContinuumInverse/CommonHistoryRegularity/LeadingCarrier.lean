module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.LeadingAmplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.InitializedCorrectedRegularity.SuppliedRawGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedChartNormal
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.DensityScalar
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar

/-!
# Applying the original leading solution to the capped carrier

The input is the original leading solution's reserve-thirteen null estimate
and reserve-fourteen joint estimate. The positive source scalar is constructed
from the density inside the proof. This gives the literal carrier's sharp low
and all high amplitude bounds, its actual normal identity and its raw adjoint
bounds. Every constant precedes the density and current leading solution.

The cap is exactly the one used by `retainedIncidenceCurrentRawCap`; the final
row retains the inequality before selecting its incidence cover. There is no
second carrier or mask selection. Consumer: the common history elliptic
bootstrap, `app:ch_background:prop:bg-inverse` and `app:ch_background:prop:bg-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius InnerProductSpace

namespace JanetCartan.ContinuumInverse
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open NullTransport ActualFlow FlowAmplitude LeadingWave.FullModulation ProjectedStressFrame
open ContinuumRow LeadingPrimitive CanonicalCarrier CanonicalConic TransportKernel CarrierNormalRealization
open ContinuumNormalReduction.TransportSymbol ContinuumNormal.RetainedFrozen
open ContinuumNormal.CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedRowGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2
open ContinuumAdjoint ContinuumAdjoint.Canonical CarrierSobolev
open ContinuumAdjoint.Canonical.AmplitudeProfiles AmbientResponse LeadingWave

/-- Apply the original joint leading theorem on its own flow, using the actual
source-positive scalar. No amplitude bound, raw-adjoint bound or normal identity
is an input. The primitive null and joint estimates are precisely projections
of `BandHistory.Initialization`'s retained `hsolution` continuation
(`app:ch_waves:eq:joint-tame`, `app:ch_background:eq:bg-commutator`,
`app:ch_background:eq:bg-derivative-trade`). -/
theorem exists_original_leading_carrier_profiles_on_capped_row {n : ℕ} (hn : 0 < n) {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (D : CoefficientNormCharts n)
    (zCell : Euclidean 3) {L : ℝ} (hL : 0 < L)
    {Jfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hJfull : IsCompact Jfull)
    (zFull : Euclidean 3 × Euclidean (n - 1)) {σfull : ℝ} (hσfull : 0 < σfull)
    (hJfullEq : Jfull = closedBall ((0 : Euclidean n), zFull) σfull)
    (hJphysical : closedBall (0 : Euclidean n) (2 * σfull) ⊆ K)
    (hJphase : closedBall ((0 : Euclidean n), zFull) (2 * σfull) ⊆ domain T)
    (Wfull : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
    (hWfull : IsCompact Wfull) (hJfullW : Jfull ⊆ Wfull)
    (E : Set (Euclidean n × CarrierParameter)) (hE : IsOpen E)
    (hgraph : MapsTo (carrierGraph T) E Jfull) (hDE : D.field.region ⊆ E)
    (hfield : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hphase : E ⊆ ball (0 : Euclidean n) T.family.radius ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (adet : Euclidean n × Euclidean 3) {ρdet : ℝ} (hρdet : 0 < ρdet)
    (hxdet : MapsTo Prod.fst (closedBall adet ρdet)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdet : closedBall adet ρdet ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hmaps : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, parameter p.2))
      D.field.carrier (closedBall adet ρdet))
    (z₀ : Euclidean 3) (hz₀ : z₀ ∈ parameterInterior P.radius)
    (hcenter : chartCenter z₀ ∈ E) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hcell : 4 * a' < 1 / 2)
    (hcap : a' ≤ (exists_current_rawAdjoint_cap_on_supplied_geometry
      (N := embeddingDimension n) hn hP T hK hKU hball
      (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) hJfull E hE hgraph hz₀ hcenter).choose)
    (ha : 0 < a) (har : 6 * a ≤ r) (haR : 6 * a < T.family.radius)
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    (houter : coefficientDomain z₀ r (6 * a) ⊆ E)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport z₀ (r := a') ⊆ D.field.carrier)
    (p₀ : InputVariables n)
    (hp₀ : p₀ = (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n))
    (q₀ : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτ : 0 < τ) (haρ : 4 * a' < ρ) (hrρ : r' ≤ ρ)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρ ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain z₀ ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap δgeometry : ℝ} (hε : 0 < ε) (hgap : 0 < gap) (hδgeometry : 0 < δgeometry)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    {β cJ : ℝ} (hcJ : 0 < cJ)
    {Vinv Linv : Set (ℝ × Euclidean (n - 1))} (hVinv : IsOpen Vinv) (hLVinv : Linv ⊆ Vinv)
    (Ginv : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))
    (hgeometry : ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (hF : ContDiffOn ℝ ∞ F U)
      (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < δgeometry →
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      RetainedSpectralGeometry T Q z₀ ηb r a ∧
      closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a) ∧
      MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
        (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
      (∀ p ∈ closedBall p₀ ρ, ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (transportPosition T Q)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
        (transportPosition T Q) p) ∧
      (closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
          symbolDomain T Q z₀ ηb r (6 * a)) ∧
      (∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
        (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
          conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) ∧
      (∀ p ∈ symbolDomain T Q z₀ ηb r (6 * a),
        ‖(symbolInverse T Q z₀ ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖) ∧
      ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q))
        (physicalParameterSet z₀ (6 * a) ×ˢ dataSet z₀ ηb (3 * r)) ∧
      BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ (6 * a))
        (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r))
        Vinv Linv β cJ Ginv ∧
      (∀ p ∈ physicalParameterSet z₀ (6 * a),
        ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
          ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖))
    {Ωflow Kflow : Set (Euclidean n × Euclidean 3)} {Rc Bflow τflow Mc : ℝ}
    (hRc : 0 < Rc) (hτflow : 0 < τflow) (hMc : 0 < Mc)
    (hEcylinder : MapsTo (densityCoordinates T) E
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hElabel : ∀ p ∈ E, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (hEtime : ∀ p ∈ E, |(densityCoordinates T p).1| < L / (64 * Mc))
    (hDouter : D.field.region ⊆ coefficientDomain z₀ r (6 * a)) :
    ∃ δ > (0 : ℝ), ∃ Cscalar > (0 : ℝ),
    ∀ (Bfull : ℕ → ℝ), (∀ j, 0 < Bfull j) → ∀ Bnull : ℕ → ℝ,
    ∀ {σ MF κmet κ : ℝ}, 0 < σ → 0 ≤ MF → 0 < κmet → 0 < κ →
    ∃ Cbaseline > (0 : ℝ), ∃ Cprofile Craw : ℕ → ℝ,
      (∀ s, 0 < Cprofile s) ∧ (∀ s, 0 ≤ Craw s) ∧
    ∀ (F : Euclidean n → Euclidean (embeddingDimension n)) (_hF : ContDiffOn ℝ ∞ F U)
      (_hi : IsImmersionOn F U) (_hrank : HasFullNormalRankOn F U),
      cNorm K (2 * (n + 1) + 14) F ≤ MF →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
    ∀ (row col : Fin n)
      (current : Chart T Ωflow Kflow ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F),
      cNorm (Icc (-τflow) τflow ×ˢ
        closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 current.forward ≤ Mc →
    ∀ (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
        Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
      (O : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))))
      (Vcomp : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))),
      IsOpen O → MapsTo Prod.fst O U → O ⊆ domain T →
      closedBall ((0 : Euclidean n), zFull) (2 * σfull) ⊆ O → Wfull ⊆ O →
      MapsTo (carrierGraph T) E O →
      MapsTo (fun p : Euclidean n × CarrierParameter ↦
        coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp →
      (∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ, ∀ q ∈ Vcomp,
        let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
        scalarAmplitude T current.Q F row col Φ Y initial
            (w.1, (w.2, T.reference.spatialPatch w.2)) =
          carrierScalarAmplitude T current.Q F row col current.forward current.inverse initial w) →
      (∀ initial : Euclidean (n - 1) × Euclidean 3 → ℝ,
        ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
        cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) 14 initial ≤ σ * Cscalar →
        (∀ p ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 8), σ * Real.sqrt (1 / 2) ≤ initial p) →
        let α := scalarAmplitude T current.Q F row col Φ Y initial
        let b₀ := fun w ↦ α w • nullvector T current.Q col w
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T current.Q w.1 w.2.2
        let ν := fun w ↦ LeadingWave.principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        ContDiffOn ℝ ∞ b₀ O ∧
        (∀ j, cNorm Wfull j α + cNorm Wfull j b₀ ≤
          Bnull j * (1 + cNorm K (j + 13) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (j + 13) initial)) ∧
        (∀ j, cNorm Jfull j (fun w ↦ phase T current.Q w.1 w.2.2) + cNorm Jfull j b₀ +
          cNorm Jfull j ν + cNorm Jfull j V +
            cNorm Jfull j (fun w ↦ LeadingWave.principalMatrix (ν w) (ξ w)) ≤
          Bfull j * (1 + cNorm K (j + 14) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (j + 14) initial))) →
    ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ p ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v p) →
      (∀ p ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v p ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
    let initial := fun p ↦ positiveDensityAmplitude σ (v p)
    let e := data T current.Q F row col current.forward current.inverse initial ha' hcell
      (angularMask z₀ (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency
    let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let b := fullReflectedMatrixAmplitude d (symbolJacobian T current.Q)
      (symbolInverse T current.Q z₀ ηb r (6 * a)) (symbolDomain T current.Q z₀ ηb r (6 * a))
      (closedBall (spectatorCenter z₀) (a' / 2))
    ∀ Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ f : carrierInitialTestSpace n,
        Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) →
      (∀ w, Vop.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) →
      ∃ hb : ContDiff ℝ ∞ (Function.uncurry b),
      ∃ hs : ∀ ξ i j, SupportedInCenteredBox (4 * a') (fun z ↦ b ξ z i j),
      ∃ hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
          (2 * (n + 1)) Cbaseline,
        (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
          (2 * (n + 1) + 1) Cbaseline) ∧
        (∀ p : ℕ, 2 ≤ p → ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
          p (Cprofile p * (1 + cNorm K (p + 14) F +
            cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) (p + 14) initial))) ∧
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn (4 * a') b hb hs Cbaseline hB)) ∧
        (∀ s : ℕ, ∀ w : PeriodicSobolevSpace n (EuclideanSpace ℂ (Fin n)) s,
          MemRawSobolev s (Vop.adjoint (PeriodicSobolevSpace.toL2 s w)) ∧
          rawSobolevNorm s (Vop.adjoint (PeriodicSobolevSpace.toL2 s w)) ≤
            Craw s * (‖w‖ + (1 + cNorm K (s + 2 * (n + 1) + 14) F +
              cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
                (s + 2 * (n + 1) + 14) initial) * ‖PeriodicSobolevSpace.toL2 s w‖)) := by
  classical
  let Kinitial := closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)
  have rawExists := exists_current_rawAdjoint_cap_on_supplied_geometry
    (N := embeddingDimension n) hn hP T hK hKU hball Kinitial hJfull E hE hgraph hz₀ hcenter
  obtain ⟨δraw, hδraw, hraw⟩ := rawExists.choose_spec.2
  have hgraphD : MapsTo (carrierGraph T) D.field.carrier Jfull :=
    hgraph.mono_left (D.field.ball_subset.trans hDE)
  have hgeometryAmplitude := fun F hF hi hrank hlow hclose ↦
    (hgeometry F hF hi hrank hlow hclose)
  obtain ⟨δamp, hδamp, hamp⟩ := exists_reflected_high_and_baseline_of_retained_leading
    T (N := embeddingDimension n) hP hK hKU hball D Kinitial hJfull hgraphD zFull hσfull hJfullEq hJphysical hJphase
    Wfull hWfull hJfullW E hDE hfield hphase adet hρdet hxdet hdet hmaps
    z₀ hηb hr hr' ha' hcell houter hsupport p₀ q₀ hρ hτ hW hKiW hBi hWBi hBiDom
    hfoot hIt hIIt hsegT hseg A hε hgap hδgeometry hfreq
    (fun F hF hi hrank hlow hclose ↦ by
      obtain ⟨hs, ho, hr, hh, hj, hp, hsh, hu, _, _, _⟩ := hgeometryAmplitude F hF hi hrank hlow hclose
      exact ⟨hs, ho, hr, hh, hj, hp, hsh, hu⟩)
  obtain ⟨C₁₅, hC₁₅, hscalar₁₅⟩ := DensityScalar.exists_initial_leading_bounds n
  obtain ⟨Cd, _hCd, hscalard⟩ := exists_density_initial_scalar_bound n (2 * (n + 1) + 14)
  let Cscalar := max C₁₅ Cd
  have hCscalar : 0 < Cscalar := hC₁₅.trans_le (le_max_left _ _)
  refine ⟨min δraw (min δamp δgeometry), lt_min hδraw (lt_min hδamp hδgeometry),
    Cscalar, hCscalar, ?_⟩
  intro Bfull hBfull Bnull σ MF κmet κ hσ hMF hκmet hκ
  have hMr : 0 ≤ σ * Cscalar := (mul_pos hσ hCscalar).le
  obtain ⟨Cbaseline, hCbaseline, Cprofile, hCprofile, hamp⟩ :=
    hamp Bfull hBfull Bnull hMF hMr hκmet hκ
  have hExt : D.field.region ⊆ PhaseExtension.extensionDomain T :=
    fun p hp ↦ ⟨(hfield (hDE hp)).1.2, (hphase (hDE hp)).2⟩
  obtain ⟨Craw, hCraw, hraw⟩ := hraw (β := β) ha' hcell hcap hηb hr' hr ha har haR hrr haa
    hρ hτ hε haρ hrρ hcarrier D p₀ hp₀ q₀ A hW hKiW hBi hWBi hExt
    hIt hIIt hsegT hseg hfreq hcJ hVinv hLVinv Ginv Bfull hBfull hMF hMr hκmet hκ
  refine ⟨Cbaseline, hCbaseline, Cprofile, Craw, hCprofile, hCraw, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose row col current hforward
    Φ Y O Vcomp hO hOU hOphase hJ₂O hWO hgraphO hcompE hcomp hsolution
    v hv hpos hinterval hvnorm initial e d b Vop htests hadjoint
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    simpa only [current.frame_eq] using current.Q.2.2
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
  have hQ : current.Q = Q := Subtype.ext current.frame_eq
  have hframeSmooth : ContDiffOn ℝ ∞ (projectedStress F - fun _ ↦ cubeStress n) U :=
    (contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)).sub contDiffOn_const
  have hframeBall : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) ≤
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) :=
    cNorm_mono_set_of_contDiffAt hball hK
      (fun x hx ↦ (hframeSmooth.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp))
  have hsmallAmp := hframeBall.trans_lt (hclose.trans_le
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hsmallGeometry := hframeBall.trans_lt (hclose.trans_le
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hspectral, houtput, hrange, hhalf, hJac, hpunctured, hshell, hupper,
    hf, hInv, htrans⟩ := hgeometry F hF hi hrank hlow hsmallGeometry
  obtain ⟨_, _, hinitial, hbound₁₅, hlower, _⟩ :=
    hscalar₁₅ _ hL hσ v hv hpos hinterval ((cNorm_mono_order (by omega)).trans hvnorm)
  have hbound := (hscalard _ hL hσ v hv hpos hinterval hvnorm).2.2.2
  have hbound₁₅' : cNorm Kinitial 15 initial ≤ σ * Cscalar := hbound₁₅.trans
    (mul_le_mul_of_nonneg_left (le_max_left C₁₅ Cd) hσ.le)
  have hbound' : cNorm Kinitial (2 * (n + 1) + 14) initial ≤ σ * Cscalar := hbound.trans
    (mul_le_mul_of_nonneg_left (le_max_right C₁₅ Cd) hσ.le)
  obtain ⟨hnull, hnullSum, hjointSum⟩ := hsolution initial hinitial
    ((cNorm_mono_order (by norm_num : 14 ≤ 15)).trans hbound₁₅') hlower
  have hnullBound j : cNorm Wfull j
      (fun w ↦ scalarAmplitude T current.Q F row col Φ Y initial w • nullvector T current.Q col w) ≤
      Bnull j * (1 + cNorm K (j + 13) F + cNorm Kinitial (j + 13) initial) :=
    (le_add_of_nonneg_left (cNorm_nonneg ..)).trans (hnullSum j)
  have hfullBound j : cNorm Jfull j (fullNormal T current.Q F row col Φ Y initial) ≤
      Bfull j * (1 + cNorm K (j + 14) F + cNorm Kinitial (j + 14) initial) := by
    have hsum := hjointSum j
    dsimp only at hsum
    change cNorm Jfull j (fun w ↦ LeadingWave.principalNormal (canonicalNormalCompletion F w.1)
      (phaseGradient T current.Q w.1 w.2.2)
      (scalarAmplitude T current.Q F row col Φ Y initial w • nullvector T current.Q col w)) ≤ _
    linarith only [hsum, cNorm_nonneg Jfull j (fun w ↦ phase T current.Q w.1 w.2.2),
      cNorm_nonneg Jfull j (fun w ↦ scalarAmplitude T current.Q F row col Φ Y initial w • nullvector T current.Q col w),
      cNorm_nonneg Jfull j (fun w ↦ reconstruction F (canonicalNormalCompletion F)
        (fun x ↦ scalarAmplitude T current.Q F row col Φ Y initial (x, w.2) •
          nullvector T current.Q col (x, w.2)) w.1),
      cNorm_nonneg Jfull j (fun w ↦ LeadingWave.principalMatrix
        (LeadingWave.principalNormal (canonicalNormalCompletion F w.1)
          (phaseGradient T current.Q w.1 w.2.2)
          (scalarAmplitude T current.Q F row col Φ Y initial w • nullvector T current.Q col w))
        (phaseGradient T current.Q w.1 w.2.2))]
  have hprofiles := hamp F hF hi hrank hFM hmet hnormal hlow hsmallAmp
    row col Φ Y current.forward current.inverse initial O Vcomp
    hO hOU hOphase hJ₂O hWO hgraphO hcompE
    (by simpa only [hQ] using hnull) (by simpa only [hQ] using hcomp initial) hbound'
    (by simpa only [hQ] using hnullBound) (by simpa only [hQ] using hfullBound)
  have hprofiles' : ContDiff ℝ ∞ (Function.uncurry b) ∧
      (∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1) + 1) Cbaseline) ∧
      ∀ p : ℕ, 2 ≤ p → ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
        p (Cprofile p * (1 + cNorm K (p + 14) F + cNorm Kinitial (p + 14) initial)) := by
    simpa only [b, d, e, hQ] using hprofiles
  obtain ⟨hb, hbase, hhigh⟩ := hprofiles'
  have hsupportBox : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' := by
    intro x hx j
    exact (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)))
  have hs := fullReflectedMatrixAmplitude_supportedInCenteredBox d (symbolJacobian T current.Q)
    (symbolInverse T current.Q z₀ ηb r (6 * a)) (symbolDomain T current.Q z₀ ηb r (6 * a))
    (closedBall (spectatorCenter z₀) (a' / 2)) (4 * a') hsupportBox
  have hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j)
      (2 * (n + 1)) Cbaseline := fun i j ξ is his ↦ hbase i j ξ is (by omega)
  have hEpatch : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)) :=
    fun p hp ↦ ⟨(hfield hp).1, (hphase hp).2⟩
  have hnormalIdentity := retained_chart_density_normal_eq_on_original_region
    hP T hF hi hrank current hRc hτflow hL hMc hforward E hEpatch hEcylinder hElabel hEtime
    D z₀ hηb hr hr' ha' hrr haa har' hcell haR houter hDouter hsupport
    p₀ q₀ hρ hτ hW hKiW hBi hWBi hBiDom hfoot hIt hIIt hsegT hseg A hε hgap hfreq
    (by simpa only [hQ] using hspectral) (by simpa only [hQ] using houtput)
    (by simpa only [hQ] using hrange) (by simpa only [hQ] using hhalf)
    (by simpa only [hQ] using hJac) (by simpa only [hQ] using hpunctured)
    (by simpa only [hQ] using hshell) (by simpa only [hQ] using hupper)
    v hv hpos (σ := σ) Vop htests (4 * a') hb hs Cbaseline hB
  have hJO : Jfull ⊆ O := by
    rw [hJfullEq]
    exact (closedBall_subset_closedBall (by linarith only [hσfull])).trans hJ₂O
  have hrawBound := hraw F hF hi hrank hFM hmet hnormal hlow
    (hclose.trans_le (min_le_left _ _)) hf hInv htrans houtput hrange hhalf hshell
    row col current.forward current.inverse Φ Y initial O Vcomp hO hOU hOphase hJO
    hgraphO hcompE (by simpa only [hQ] using hnull)
    (by simpa only [hQ] using hcomp initial) hbound' (by simpa only [hQ] using hfullBound)
    Vop (by simpa only [e, hQ] using hadjoint)
  refine ⟨hb, hs, hB, hbase, hhigh, hnormalIdentity, ?_⟩
  simpa only [Kinitial] using hrawBound

end JanetCartan.ContinuumInverse
