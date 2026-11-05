module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.RetainedDensityNormals
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.NormalWitnesses
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.OriginalDensityBuffers

/-!
# The retained normal with the supplied carrier and amplitude witnesses

Construct the actual density normal and identify its carrier by dense tests.
Then use the sharp baseline's own PDO witnesses on the unchanged amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection NormalizedCarrierProfiles
open PositiveReference PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude HamiltonPhase RetainedRowGeometry
open NormalizedBackground.SourceGeometry
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2 RetainedFrozen
open ActualConstruction SourceDensityLimitRealization

/-- The actual retained density normal uses any supplied carrier with its literal
integral action and the consumer's amplitude witnesses. The normal realization
is constructed from the retained geometry; density of smooth tests identifies
the carrier, and PDO test uniqueness identifies the separately bounded amplitude
operator. This supplies the same-row normal identity needed by
`exists_retained_history_elliptic_estimates_with_exterior`, preserving Lebesgue
and Haar measures, `2π` normalization and the reflected factor four
(`app:ch_background:eq:bg-full-complex-amplitude`, `app:ch_background:eq:bg-real-symbol`,
`app:ch_background:eq:bg-commutator`). -/
theorem retained_chart_density_normal_eq_for_supplied_carrier
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow Kflow : Set (Euclidean n × Euclidean 3)}
    {zCell : Euclidean 3} {Rc Bflow τflow L Mc R σ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (current : Chart T Ωflow Kflow ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (hRc : 0 < Rc) (hτflow : 0 < τflow) (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 current.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (zRoot : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (haR : 6 * a < T.family.radius)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hDouter : D.field.region ⊆ coefficientDomain zRoot r (6 * a))
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport zRoot (r := a') ⊆ D.field.carrier)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρi τi : ℝ} (hρi : 0 < ρi) (hτi : 0 < τi)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρi ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρi, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap : ℝ} (hε : 0 < ε) (hgap : 0 < gap)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    (hspectral : RetainedSpectralGeometry T current.Q zRoot ηb r a)
    (houtput : closedBall q₀ (2 * τi) ⊆ symbolDomain T current.Q zRoot ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T current.Q zRoot ηb r (6 * a)))
      (closedBall q₀ (2 * τi)) (closedBall p₀ ρi))
    (hgapA : ∀ p ∈ closedBall p₀ ρi, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (transportPosition T current.Q)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hJacLow : ∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (transportPosition T current.Q) p)
    (hpunctured : closure (augmentedTransportGradient (transportPosition T current.Q) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
        symbolDomain T current.Q zRoot ηb r (6 * a))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T current.Q) ''
        conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τi)
    (hupper : ∀ p ∈ symbolDomain T current.Q zRoot ηb r (6 * a),
      ‖(symbolInverse T current.Q zRoot ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)))
    (hpos : ∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) :
    let e := data T current.Q F row col current.forward current.inverse
      (fun q ↦ positiveDensityAmplitude σ (v q)) ha' hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency
    let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let J := symbolJacobian T current.Q
    let u := symbolInverse T current.Q zRoot ηb r (6 * a)
    let Ωi := symbolDomain T current.Q zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    ∀ (Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
    (∀ f : carrierInitialTestSpace n,
      Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) →
    ∀ (Rbox : ℝ)
      (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ωi S)))
      (hs : ∀ ξ i j, SupportedInCenteredBox Rbox
        (fun z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j))
      (Bbase : ℝ)
      (hbase : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j) (2 * (n + 1)) Bbase),
    carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator (by have := row.isLt; omega) Rbox
          (fullReflectedMatrixAmplitude d J u Ωi S) hb hs Bbase hbase)) := by
  intro e d J u Ωi S Vop htest Rbox hb hs Bbase hbase
  obtain ⟨Cnorm, _hCnorm, Cpdo, _hCpdo, hsupport, hb₀, hA, Uop,
    _hUnorm, _hUadj, _hUtest, _hUsupport, huniq, _hadj, hnormal⟩ :=
    exists_retained_chart_density_normal hP T hF hi hrank current
      hRc hτflow hL hMc hforward hRT hRU hRtime hV hVP hflow hlabel D hD
      zRoot hηb hr hr' ha' hrr haa har' hcell haR houter hDouter hsupportD
      p₀ q₀ hρi hτi hW hKiW hBi hWBi hBiDom hfoot hIt hIIt hsegT hseg A hε hgap hfreq
      hspectral houtput hrange hgapA hJacLow hpunctured hshell hupper v hv hpos (σ := σ)
  have heq : Vop = Uop := huniq Vop htest
  rw [heq]
  exact realized_normal_eq_of_amplitude_witnesses (by have := row.isLt; omega)
    (4 * a') Rbox _ _ hb₀ hb
    (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ωi S (4 * a') hsupport)
    hs Cpdo Bbase (fun i j ξ is his ↦ hA i j ξ is (by omega)) hbase rfl Uop hnormal

/-- Realize the supplied carrier's normal directly on the original initialized
outer region. Its complete coefficient product supplies the physical and
parameter buffers; the original time restriction supplies the radius bound.
No detector support is reduced, and incidence roots remain distinct from scalar
cell centers. All inputs are retained by
`exists_initialized_incidence_source_history_coercivity`; the literal normal
with the consumer's baseline witnesses supplies the same-row commutator
bootstrap (`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-inverse`). -/
theorem retained_chart_density_normal_eq_on_original_region
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow Kflow : Set (Euclidean n × Euclidean 3)}
    {zCell : Euclidean 3} {Rc Bflow τflow L Mc σ : ℝ} {row col : Fin n}
    {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (current : Chart T Ωflow Kflow ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (hRc : 0 < Rc) (hτflow : 0 < τflow) (hL : 0 < L) (hMc : 0 < Mc)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 current.forward ≤ Mc)
    (E : Set (Euclidean n × CarrierParameter))
    (hEpatch : E ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (parameter ⁻¹' parameterInterior (3 * P.radius / 2)))
    (hEcylinder : MapsTo (densityCoordinates T) E
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hElabel : ∀ p ∈ E, (densityCoordinates T p).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (hEtime : ∀ p ∈ E, |(densityCoordinates T p).1| < L / (64 * Mc))
    (D : CoefficientNormCharts n)
    (zRoot : Euclidean 3) {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {r a r' a' : ℝ} (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (haR : 6 * a < T.family.radius)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ E)
    (hDouter : D.field.region ⊆ coefficientDomain zRoot r (6 * a))
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport zRoot (r := a') ⊆ D.field.carrier)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρi τi : ℝ} (hρi : 0 < ρi) (hτi : 0 < τi)
    {W Bi : Set (InputVariables n)} (hW : IsOpen W)
    (hKiW : closedBall p₀ ρi ⊆ W) (hBi : IsCompact Bi) (hWBi : W ⊆ Bi)
    (hBiDom : Bi ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hfoot : ∀ p ∈ closedBall p₀ ρi, D.Contains p)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {ε gap : ℝ} (hε : 0 < ε) (hgap : 0 < gap)
    (hfreq : ∀ p ∈ Bi, ε ≤ ‖p.2.2‖)
    (hspectral : RetainedSpectralGeometry T current.Q zRoot ηb r a)
    (houtput : closedBall q₀ (2 * τi) ⊆ symbolDomain T current.Q zRoot ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T current.Q zRoot ηb r (6 * a)))
      (closedBall q₀ (2 * τi)) (closedBall p₀ ρi))
    (hgapA : ∀ p ∈ closedBall p₀ ρi, ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (transportPosition T current.Q)) p) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hJacLow : ∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (transportPosition T current.Q) p)
    (hpunctured : closure (augmentedTransportGradient (transportPosition T current.Q) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆
        symbolDomain T current.Q zRoot ηb r (6 * a))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T current.Q) ''
        conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τi)
    (hupper : ∀ p ∈ symbolDomain T current.Q zRoot ηb r (6 * a),
      ‖(symbolInverse T current.Q zRoot ηb r (6 * a) p).2‖ ≤ 2 * ‖p.1.2.2‖)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)))
    (hpos : ∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) :
    let e := data T current.Q F row col current.forward current.inverse
      (fun q ↦ positiveDensityAmplitude σ (v q)) ha' hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency
    let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let J := symbolJacobian T current.Q
    let u := symbolInverse T current.Q zRoot ηb r (6 * a)
    let Ωi := symbolDomain T current.Q zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    ∀ (Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
    (∀ f : carrierInitialTestSpace n,
      Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) →
    ∀ (Rbox : ℝ)
      (hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ωi S)))
      (hs : ∀ ξ i j, SupportedInCenteredBox Rbox
        (fun z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j))
      (Bbase : ℝ)
      (hbase : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ωi S ξ z i j) (2 * (n + 1)) Bbase),
    carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
      realOutputCompression (transferOperator
        (vectorTwoPositionL2Operator (by have := row.isLt; omega) Rbox
          (fullReflectedMatrixAmplitude d J u Ωi S) hb hs Bbase hbase)) := by
  have hn : 0 < n := by have := row.isLt; omega
  have haOuter : 0 < 6 * a := mul_pos (by norm_num) (ha'.trans_le haa)
  have hproducts := retained_coefficientDomain_source_buffers hn T hr haOuter
    houter hEpatch hEcylinder
  have htime := retained_coefficientDomain_radius_le_of_time_bound T hr haOuter
    hL hMc houter hEtime
  exact retained_chart_density_normal_eq_for_supplied_carrier hP T hF hi hrank current
    hRc hτflow hL hMc hforward hproducts.1 hproducts.2.1 htime
    (isOpen_ball.prod isOpen_ball) hproducts.2.2.1 hproducts.2.2.2
    (fun p hp ↦ hElabel p (houter hp)) D hDouter
    zRoot hηb hr hr' ha' hrr haa har' hcell haR Subset.rfl hDouter hsupportD
    p₀ q₀ hρi hτi hW hKiW hBi hWBi hBiDom hfoot hIt hIIt hsegT hseg A hε hgap hfreq
    hspectral houtput hrange hgapA hJacLow hpunctured hshell hupper v hv hpos (σ := σ)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
