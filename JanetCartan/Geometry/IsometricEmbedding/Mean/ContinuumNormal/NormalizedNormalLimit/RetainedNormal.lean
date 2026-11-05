module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RetainedMatching
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.RetainedAmplitudes

/-!
# Literal normalized normals of the retained source carriers

The source carrier and its common measurement restriction retain their exact
reflected PDO identities on the supplied radial comparison cone. The actual
full-amplitude equality and density of smooth compactly supported tests prove
that the old and new support and bound witnesses describe the same operator.
-/

open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic RetainedFrozen FrozenModel
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading RetainedRowGeometry WideDensity
open NullTransport ActualFlow FlowAmplitude HamiltonPhase NormalizedBackground.SourceGeometry
open NormalizedCarrierProfiles AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumCommutator

/-- Equal full amplitudes have the same literal L2 realization even when
support-box and budget witnesses differ. Dense smooth tests determine the
bounded operator; no existential operator choices are identified by fiat.
Consumer: retained source normal matching (bg-full-complex-amplitude,
app:ch_regular_base:thm:actual-calculus). -/
private theorem sourcePdo_eq_of_same_fullAmplitude
    {n : ℕ} (hn : 0 < n) (R R' : ℝ)
    (b b' : Euclidean n → Euclidean (2 * n) → Matrix (Fin n) (Fin n) ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hb' : ContDiff ℝ ∞ (Function.uncurry b'))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j))
    (hs' : ∀ ξ i j, SupportedInCenteredBox R' (fun z ↦ b' ξ z i j))
    (B B' : ℝ)
    (hB : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b ξ z i j) (2 * (n + 1)) B)
    (hB' : ∀ i j, HasAmplitudeDerivativeBound (fun ξ z ↦ b' ξ z i j) (2 * (n + 1)) B')
    (heq : b = b') :
    vectorTwoPositionL2Operator hn R b hb hs B hB =
      vectorTwoPositionL2Operator hn R' b' hb' hs' B' hB' := by
  subst b'
  apply DFunLike.coe_injective
  apply (Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure (Euclidean n)))
    (F := EuclideanSpace ℂ (Fin n)) (p := 2) (by norm_num)).denseRange_val.equalizer
    (map_continuous _) (map_continuous _)
  funext ⟨v, f, hv, hfs, hfc⟩
  simp only [Function.comp_apply]
  have hf : MemLp f 2 volume := hfc.continuous.memLp_of_hasCompactSupport hfs
  have he : v = hf.toLp f := Lp.ext (hv.trans hf.coeFn_toLp.symm)
  rw [he]
  apply Lp.ext
  exact (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R b hb hs B hB f hf
    (fun j ↦ ((contDiff_piLp 2).mp hfc j).of_le (by simp))
    (fun j ↦ hfs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)).trans
    (vectorTwoPositionL2Operator_ae_matrixFullAmplitudeOperator hn R' b hb' hs' B' hB' f hf
      (fun j ↦ ((contDiff_piLp 2).mp hfc j).of_le (by simp))
      (fun j ↦ hfs.comp_left (g := fun v : EuclideanSpace ℂ (Fin n) ↦ v j) rfl)).symm


/-- The SAME bounded retained carrier has the normalized reflected PDO as
its literal real normal on the supplied common radial cone. The old canonical
normal identity is the output of `exists_retained_chart_source_density_carrier`;
all amplitude equalities and inverse matching are derived from the retained
source geometry. The PDO is independent of its support-box and norm-budget
witnesses by equality on dense smooth tests, so the derived source-family
bounds can be used directly. The final clause proves the identity after the
supplied common measurement restriction, with the original angular mask,
spectator measure and reflected normalization unchanged.

Consumer: the literal `hnormal` input of
`exists_source_family_controlled_half_gap`, followed by SourceInverse.
Sources: app:ch_background:prop:bg-normalized, bg-full-complex-amplitude,
bg-real-symbol and app:ch_regular_base:thm:actual-calculus. -/
theorem retained_source_normal_eq_normalized_on_common_cone
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ωflow : Set (Euclidean n × Euclidean 3)} (hΩflow : IsOpen Ωflow)
    {zCell : Euclidean 3} {ρ Rc Bflow τflow : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρ ⊆ Ωflow)
    (hΩpatch : Ωflow ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτflow : 0 < τflow) (hτR : τflow ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρ))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius)
    (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a r' a' : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (current : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρ)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col (sourceDilation F σ))
    (hgeometry : RetainedSpectralGeometry T current.Q zRoot ηb r a)
    (Ωcommon : Set (Variables n × Euclidean 2))
    (hpunctured : closure (augmentedTransportGradient (normalizedTransportPosition T seed.Q σ) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆ Ωcommon)
    (Oinput : Set (InputVariables n))
    (hOinput : Oinput ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (uSource : Variables n × Euclidean 2 → SliceVariable n)
    (huRadial : MapsTo (inverseCoordinates uSource) Ωcommon
      (NormalizedSelection.radialInputDomain Oinput))
    (huEq : ∀ p ∈ Ωcommon,
      transportAveragedGradient (normalizedTransportPosition T seed.Q σ)
        (inverseCoordinates uSource p) = p.1.2.2)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ) (S : Set (Euclidean 2)) :
    let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
    let d := coefficientsOfCarrier
      (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
        (fun q ↦ σ * Real.sqrt (1 + v q)) ha' hcell angular FixedCutoffs.highFrequency)
      (FixedCutoffs.physical ha' 1)
    let aσ := coefficientsOfCarrier
      (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
        ha' hcell angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical ha' 1)
    let av := {aσ with
      normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T seed.inverse (σ, p))) •
        aσ.normal p}
    let Jσ := transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T seed.Q σ)
    let u := symbolInverse T current.Q zRoot ηb r (6 * a)
    let Ω := symbolDomain T current.Q zRoot ηb r (6 * a)
    let bActual := fullReflectedMatrixAmplitude d (symbolJacobian T current.Q) u Ω S
    let bSource := fullReflectedMatrixAmplitude av Jσ uSource Ωcommon S
    ∀ (Ractual Bactual : ℝ)
      (hbActual : ContDiff ℝ ∞ (Function.uncurry bActual))
      (hsActual : ∀ ξ i j, SupportedInCenteredBox Ractual (fun z ↦ bActual ξ z i j))
      (hBActual : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ bActual ξ z i j) (2 * (n + 1)) Bactual)
      (Vop : CarrierL2 n →L[ℂ] ComplexOutputL2 n),
      carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator (by have := row.isLt; omega) Ractual
            bActual hbActual hsActual Bactual hBActual)) →
      (∀ (Rsource Bsource : ℝ)
        (hbSource : ContDiff ℝ ∞ (Function.uncurry bSource))
        (hsSource : ∀ ξ i j, SupportedInCenteredBox Rsource (fun z ↦ bSource ξ z i j))
        (hBSource : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ bSource ξ z i j) (2 * (n + 1)) Bsource),
        carrierChannel Vop ∘L (carrierChannel Vop).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator (by have := row.isLt; omega) Rsource
              bSource hbSource hsSource Bsource hBSource))) ∧
      ∀ {rMeas : ℝ} (hrMeas : 0 < rMeas) (hcellMeas : 4 * rMeas < 1 / 2), 6 * rMeas < a' →
      let aMeas := coefficientsOfCarrier
        (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
          hrMeas hcellMeas angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical hrMeas 1)
      let avMeas := {aMeas with
        normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T seed.inverse (σ, p))) •
          aMeas.normal p}
      let bMeas := fullReflectedMatrixAmplitude avMeas Jσ uSource Ωcommon S
      ∀ (Rsource Bsource : ℝ)
        (hbSource : ContDiff ℝ ∞ (Function.uncurry bMeas))
        (hsSource : ∀ ξ i j, SupportedInCenteredBox Rsource (fun z ↦ bMeas ξ z i j))
        (hBSource : ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ bMeas ξ z i j) (2 * (n + 1)) Bsource),
      let Vmeas := CommonMeasurement.restrictCarrier (FixedCutoffs.periodic hrMeas hcellMeas 1) Vop
      carrierChannel Vmeas ∘L (carrierChannel Vmeas).adjoint =
        realOutputCompression (transferOperator
          (vectorTwoPositionL2Operator (by have := row.isLt; omega) Rsource
            bMeas hbSource hsSource Bsource hBSource)) := by
  intro angular d aσ av Jσ u Ω bActual bSource Ractual Bactual hbActual hsActual hBActual Vop hnormal
  have hn : 0 < n := by have := row.isLt; omega
  have hmatch := retained_source_fullAmplitudes_eq_normalized_on_common_cone hP T hΩflow hKΩ hΩpatch
    hRc hτflow hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hR hRT hRU hV hVP hflow D hD hηb hr hr' ha' hrr haa har' hcell houter
    hσ hσ1 current hgeometry Ωcommon hpunctured Oinput hOinput uSource huRadial huEq v S
  have heq : bActual = bSource := hmatch.2.2.1
  constructor
  · intro Rsource Bsource hbSource hsSource hBSource
    exact hnormal.trans (congrArg (fun A ↦ realOutputCompression (transferOperator A))
      (sourcePdo_eq_of_same_fullAmplitude hn Ractual Rsource bActual bSource
        hbActual hbSource hsActual hsSource Bactual Bsource hBActual hBSource heq))
  · intro rMeas hrMeas hcellMeas hMeas aMeas avMeas bMeas Rsource Bsource hbSource hsSource hBSource
    let β := FixedCutoffs.physical (n := n) hrMeas 1
    let dMeas := coefficientsOfCarrier
      (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
        (fun q ↦ σ * Real.sqrt (1 + v q)) hrMeas hcellMeas angular FixedCutoffs.highFrequency)
      (FixedCutoffs.physical hrMeas 1)
    have hdMeas : dMeas = CommonMeasurement.restrictCoefficients d β := by
      dsimp only [dMeas, d, β]
      unfold coefficientsOfCarrier CommonMeasurement.restrictCoefficients
      congr 1
      funext x
      exact (CommonMeasurement.physical_measurement_mul hrMeas ha'
        (by linarith : 3 * rMeas ≤ 2 * a') x).symm
    have hrestricted : CommonMeasurement.restrictAmplitude bActual β = bMeas := by
      rw [← CommonMeasurement.fullReflectedMatrixAmplitude_restrictCoefficients, ← hdMeas]
      exact (hmatch.2.2.2 hrMeas hcellMeas hMeas).2.2
    have hsRestricted : ∀ ξ i j, SupportedInCenteredBox Rsource
        (fun z ↦ CommonMeasurement.restrictAmplitude bActual β ξ z i j) := by
      rw [hrestricted]
      exact hsSource
    have hBRestricted : ∀ i j, HasAmplitudeDerivativeBound
        (fun ξ z ↦ CommonMeasurement.restrictAmplitude bActual β ξ z i j)
        (2 * (n + 1)) Bsource := by
      rw [hrestricted]
      exact hBSource
    have hmeasured := restricted_carrier_normal_eq hn Ractual Rsource bActual hbActual
      hsActual Bactual hBActual (FixedCutoffs.periodic hrMeas hcellMeas 1) β
      β.contDiff β.hasCompactSupport (FixedCutoffs.periodic_apply hrMeas hcellMeas 1)
      hsRestricted Bsource hBRestricted Vop hnormal
    exact hmeasured.trans (congrArg (fun A ↦ realOutputCompression (transferOperator A))
      (sourcePdo_eq_of_same_fullAmplitude hn Rsource Rsource
        (CommonMeasurement.restrictAmplitude bActual β) bMeas
        (contDiff_restrictAmplitude bActual hbActual β β.contDiff) hbSource
        hsRestricted hsSource Bsource Bsource hBRestricted hBSource hrestricted))

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
