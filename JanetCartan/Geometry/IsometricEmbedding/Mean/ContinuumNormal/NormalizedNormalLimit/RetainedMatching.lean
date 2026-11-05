module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RetainedSourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.CanonicalWeights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedCarrierProfiles.ActualCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.SourceCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceWeighted.TransportMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.SourceCompatibility
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.MeasuredData
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.CommonConicNormal

/-!
# Actual retained source amplitudes in the normalized comparison

The original seed and current charts share their retained minor, flow cylinder
and masks. Source uniqueness identifies the prescribed scalar and divided ODE
footpoints. Canonical coefficient and Jacobian identities then identify the
literal full amplitudes. The fixed comparison cone retains the complete
transported support, and inverse uniqueness identifies its supplied inverse.

Consumer: the current carrier-normal identity in normalized coercivity,
using NormalizedSelection.exists_retained_chart_source_density_carrier and
exists_source_fullAmplitude_sqrtFootpoints_tolerance. No new row is selected.
Sources: app:ch_background:prop:bg-normalized, bg-Nsigma, bg-Psi,
app:ch_background:eq:bg-full-complex-amplitude and bg-real-symbol.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic RetainedFrozen FrozenModel
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs
open PositiveReference PositiveReference.FlowConstruction RetainedLeading RetainedRowGeometry WideDensity
open NullTransport ActualFlow FlowAmplitude HamiltonPhase NormalizedBackground.SourceGeometry
open NormalizedCarrierProfiles

/-- The bounded retained source carrier's actual full amplitudes equal the
normalized amplitudes on the supplied fixed comparison cone, including the
radial-input constructor's general target. The target's containment in the
carrier's symbol domain follows from its supplied inverse range and equation;
no ball-shaped target or independent inverse choice is required. The scalar transport,
two divided ODE labels, canonical coefficients, literal absolute Jacobian
and whole-domain restriction are all identified by their concrete producers.
The comparison inverse is proved equal to the carrier inverse on the original
input cone, using its right-inverse equation and the retained injectivity.
Every mask, spectator measure and factor of sigma is retained.
The final clause retains the original angular mask under any supplied common
measurement restriction, as used by the final finite row.

This connects NormalizedSelection.exists_retained_chart_source_density_carrier
to exists_source_fullAmplitude_sqrtFootpoints_tolerance; no amplitude equality,
coefficient convergence or operator continuity is a premise.
Sources: app:ch_background:prop:bg-normalized, bg-Nsigma, bg-Psi,
app:ch_background:eq:bg-full-complex-amplitude and bg-real-symbol. -/
theorem retained_source_fullAmplitudes_eq_normalized_on_common_cone
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
    extendedDensity d (symbolJacobian T current.Q) u Ω = extendedDensity av Jσ uSource Ωcommon ∧
      fullComplexMatrixAmplitude d (symbolJacobian T current.Q) u Ω S =
        fullComplexMatrixAmplitude av Jσ uSource Ωcommon S ∧
      fullReflectedMatrixAmplitude d (symbolJacobian T current.Q) u Ω S =
        fullReflectedMatrixAmplitude av Jσ uSource Ωcommon S ∧
      ∀ {rMeas : ℝ} (hrMeas : 0 < rMeas) (hcellMeas : 4 * rMeas < 1 / 2), 6 * rMeas < a' →
      let dMeas := coefficientsOfCarrier
        (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
          (fun q ↦ σ * Real.sqrt (1 + v q)) hrMeas hcellMeas angular FixedCutoffs.highFrequency)
        (FixedCutoffs.physical hrMeas 1)
      let aMeas := coefficientsOfCarrier
        (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
          hrMeas hcellMeas angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical hrMeas 1)
      let avMeas := {aMeas with
        normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T seed.inverse (σ, p))) •
          aMeas.normal p}
      extendedDensity dMeas (symbolJacobian T current.Q) u Ω =
        extendedDensity avMeas Jσ uSource Ωcommon ∧
      fullComplexMatrixAmplitude dMeas (symbolJacobian T current.Q) u Ω S =
        fullComplexMatrixAmplitude avMeas Jσ uSource Ωcommon S ∧
      fullReflectedMatrixAmplitude dMeas (symbolJacobian T current.Q) u Ω S =
        fullReflectedMatrixAmplitude avMeas Jσ uSource Ωcommon S := by
  intro angular d aσ av Jσ u Ω
  have huRange : MapsTo (inverseCoordinates uSource) Ωcommon
      (symbolInputDomain zRoot ηb r (6 * a)) :=
    huRadial.mono_right (radialInputDomain_subset_symbolInputDomain hOinput)
  let E := ball (0 : Euclidean n) R ×ˢ V
  let W := symbolInputDomain zRoot ηb r (6 * a)
  have hpatch : Ωflow ⊆ ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro q hq
    exact ⟨(hΩpatch hq).1.2, fun j ↦ ((hΩpatch hq).2 j).le.trans (by linarith [hP.1])⟩
  obtain ⟨_, hfoot, hscalar, _, _⟩ := retained_charts_source_dilation
    T hΩflow hKΩ hpatch hRc hτflow hτR hbuffer hF hrank hphysical seed htrans hflat
      hσ hσ1 current
  obtain ⟨hY, _, hzero, hparam, _⟩ :=
    exists_retained_chart_source_primitive_convergence_on_outputCylinder hP T
      hΩflow hKΩ hΩpatch hRc hτflow hτR hbuffer hF hi hrank hphysical seed htrans hflat
      hR hRT hRU hV hVP hflow D (D.field.ball_subset.trans hD) a' ha' hcell
      angular FixedCutoffs.highFrequency
  have hsmall : MapsTo (densityCoordinates T) E current.D :=
    (hflow.mono_right (outputCylinder_spec hRc hτflow).2).mono_right current.small_subset
  let ac := coefficientsOfCarrier
    (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
      (fun _ ↦ σ) ha' hcell angular FixedCutoffs.highFrequency) (FixedCutoffs.physical ha' 1)
  have hfields (p : Euclidean n × CarrierParameter) (hp : p ∈ E) :
      ac.normal p = aσ.normal p ∧ ac.reduced p = aσ.reduced p := by
    apply coefficientsOfCarrier_current_eq_normalized_of_scalar_transport hP T seed.Q current.Q
      hF hrank hphysical seed.frame_eq htrans hσ hσ1 current.frame_eq
      row col seed.forward seed.inverse current.forward current.inverse (fun _ ↦ 1) (fun _ ↦ σ)
      ha' hcell angular FixedCutoffs.highFrequency (ball_subset_ball hRT hp.1)
      (fun j ↦ (hVP hp.2 j).trans (by linarith only [hP.1]))
    exact hscalar (hsmall hp)
  have hlabel (p : Euclidean n × CarrierParameter) (hp : p ∈ E) :
      densityFootpoint T current.inverse p = sourceDensityFootpointExtension T seed.inverse (σ, p) := by
    change current.inverse (densityCoordinates T p) = _
    rw [hfoot (hsmall hp)]
    exact (sourceDensityFootpointExtension_eq T hR hY hzero hparam hσ.ne'
      ⟨(convex_ball (0 : Euclidean n) R).smul_mem_of_zero_mem
        (mem_ball_self hR) hp.1 ⟨hσ.le, hσ1⟩, hp.2⟩).symm
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W E := by
    intro t ht p hp
    apply houter
    refine ⟨?_, hp.2.1, hp.1.1⟩
    have hh := (convex_ball (0 : Euclidean n) (6 * a)) hp.1.2.2 hp.1.2.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
    have he : (1 - t) • p.1.2 + t • p.1.1 = p.1.2 + t • (p.1.1 - p.1.2) := by module
    change p.1.2 + t • (p.1.1 - p.1.2) ∈ ball (0 : Euclidean n) (6 * a)
    exact he ▸ hh
  have hend (side : Bool) : MapsTo (densityEndpoint side) W E := by
    intro p hp
    cases side
    · simpa [densityEndpoint, transportSegmentInput_apply] using hseg 1 ⟨zero_le_one, le_rfl⟩ hp
    · simpa [densityEndpoint, transportSegmentInput_apply] using hseg 0 ⟨le_rfl, zero_le_one⟩ hp
  obtain ⟨haug, _, hJac⟩ := source_transport_on_retained_coefficient_domain (ηb := ηb)
    T seed.Q current.Q hP hF hrank hphysical seed.frame_eq htrans hσ hσ1 current.frame_eq
      hRT hV hVP houter
  obtain ⟨_, _, G, β, cJ, V₀, L₀, _, _, _, hf, hInv, htransverse, _⟩ := hgeometry
  have hJmatch : EqOn (symbolJacobian T current.Q) Jσ W :=
    fun p hp ↦ (symbolJacobian_eq_actual T current.Q hηb hr hf hp).trans (hJac hp)
  have hdweight : d = {ac with
      normal := fun p ↦ Real.sqrt (1 + v (densityFootpoint T current.inverse p)) • ac.normal p} :=
    canonical_coefficients_initial_mul_sqrtDensity T current.Q (sourceDilation F σ)
      row col current.forward current.inverse (fun _ ↦ σ) v ha' hcell angular FixedCutoffs.highFrequency
  have hiDensity (p : InputVariables n) (hp : p ∈ W) :
      inputDensity d (symbolJacobian T current.Q) p = inputDensity av Jσ p := by
    obtain ⟨hn₁, hq₁⟩ := hfields (densityEndpoint false p) (hend false hp)
    obtain ⟨hn₂, hq₂⟩ := hfields (densityEndpoint true p) (hend true hp)
    have hy₁ := hlabel (densityEndpoint false p) (hend false hp)
    have hy₂ := hlabel (densityEndpoint true p) (hend true hp)
    simp only [densityEndpoint, Bool.false_eq_true, ↓reduceIte] at hn₁ hn₂ hq₁ hq₂ hy₁ hy₂
    rw [hdweight]
    unfold inputDensity inputWeight
    dsimp only [av]
    rw [hn₁, hn₂, hq₁, hq₂, hy₁, hy₂, hJmatch hp]
    rfl
  have hright : ∀ p ∈ Ωcommon,
      transportAveragedGradient (transportPosition T current.Q) (inverseCoordinates uSource p) =
        p.1.2.2 := by
    intro p hp
    have heq : transportAveragedGradient (transportPosition T current.Q) (inverseCoordinates uSource p) =
        transportAveragedGradient (normalizedTransportPosition T seed.Q σ) (inverseCoordinates uSource p) :=
      congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) (haug (huRange hp))
    exact heq.trans (huEq p hp)
  have hsub : Ωcommon ⊆ Ω := by
    intro p hp
    change p ∈ symbolDomain T current.Q zRoot ηb r (6 * a)
    rw [symbolDomain_eq_image T current.Q hηb hr hInv htransverse]
    exact ⟨inverseCoordinates uSource p, huRange hp,
      augmentedTransportGradient_inverseCoordinates _ _ hright hp⟩
  have huMatch : EqOn uSource u Ωcommon :=
    inverse_eq_symbolInverse T current.Q hηb hr hInv htransverse huRange hright
  have hinput : conicMaskSupport zRoot ηb r' a' ⊆ W :=
    (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
  have hbufferCurrent : augmentedTransportGradient (transportPosition T current.Q) ''
      conicMaskSupport zRoot ηb r' a' ⊆ Ωcommon := by
    rintro _ ⟨p, hp, rfl⟩
    have heq := haug (hinput hp)
    rw [heq]
    apply hpunctured
    refine ⟨subset_closure ⟨p, hp, rfl⟩, ?_⟩
    have hn := transportGradient_ne_zero T current.Q hηb hr htransverse (hinput hp)
    have hgrad := congrArg (fun q : Variables n × Euclidean 2 ↦ q.1.2.2) heq
    intro hz
    exact hn (hgrad.trans hz)
  have heCommon : extendedDensity d (symbolJacobian T current.Q) u Ω =
      extendedDensity d (symbolJacobian T current.Q) uSource Ωcommon := by
    apply NormalizedSelection.extendedDensity_common_conic_target d
      (symbolJacobian T current.Q) (symbolJacobian T current.Q) u uSource
      (augmentedTransportGradient (transportPosition T current.Q)) hsub
      (symbolInverse_maps T current.Q hηb hr hInv htransverse)
      (augmentedTransportGradient_symbolInverse T current.Q hηb hr hInv htransverse)
      _ hbufferCurrent huMatch.symm (fun _ _ ↦ rfl)
    intro p hp hx hy hang _
    exact primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy hang
  have hext : extendedDensity d (symbolJacobian T current.Q) u Ω =
      extendedDensity av Jσ uSource Ωcommon := by
    rw [heCommon]
    funext p
    by_cases hp : p ∈ Ωcommon
    · simp only [extendedDensity, indicator_of_mem hp]
      exact hiDensity _ (huRange hp)
    · simp only [extendedDensity, indicator_of_notMem hp]
  have hamp : amplitude d (symbolJacobian T current.Q) u Ω S = amplitude av Jσ uSource Ωcommon S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hext (p, z)))
  refine ⟨hext, ?_, ?_, ?_⟩
  · funext ξ z
    ext i j
    simp only [fullComplexMatrixAmplitude, hamp]
  · funext ξ z
    ext i j
    simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]
  · intro rMeas hrMeas hcellMeas hMeas dMeas aMeas avMeas
    let χ := FixedCutoffs.physical (n := n) hrMeas 1
    have hdMeas : dMeas = CommonMeasurement.restrictCoefficients d χ := by
      dsimp only [dMeas, d, χ]
      unfold coefficientsOfCarrier CommonMeasurement.restrictCoefficients
      congr 1
      funext x
      exact (CommonMeasurement.physical_measurement_mul hrMeas ha'
        (by linarith : 3 * rMeas ≤ 2 * a') x).symm
    have haMeas : aMeas = CommonMeasurement.restrictCoefficients aσ χ :=
      NormalizedSelection.normalizedCarrierData_common_coefficients T seed.Q F row col
        seed.forward seed.inverse (fun _ ↦ 1) hrMeas ha' hcellMeas hcell angular
        FixedCutoffs.highFrequency σ hMeas
    have havMeas : avMeas = CommonMeasurement.restrictCoefficients av χ := by
      dsimp only [avMeas]
      rw [haMeas]
      rfl
    have hmext : extendedDensity dMeas (symbolJacobian T current.Q) u Ω =
        extendedDensity avMeas Jσ uSource Ωcommon := by
      rw [hdMeas, havMeas]
      funext p
      rw [CommonMeasurement.extendedDensity_restrictCoefficients,
        CommonMeasurement.extendedDensity_restrictCoefficients, hext]
    have hmamp : amplitude dMeas (symbolJacobian T current.Q) u Ω S =
        amplitude avMeas Jσ uSource Ωcommon S := by
      funext p
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hmext (p, z)))
    refine ⟨hmext, ?_, ?_⟩
    · funext ξ z
      ext i j
      simp only [fullComplexMatrixAmplitude, hmamp]
    · funext ξ z
      ext i j
      simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hmamp]

/-- The retained ball-cone comparison is the specialization of the supplied
common-cone identity. The original supported shell gives the complete mask
buffer, and actual source matching transfers that same image to the normalized
transport. This preserves the original public API used by the bounded-carrier
comparison (app:ch_background:eq:bg-full-complex-amplitude, bg-Psi,
app:ch_background:prop:bg-normalized). -/
theorem retained_source_fullAmplitudes_eq_normalized
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
    {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (q₀ : Variables n × Euclidean 2)
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T current.Q zRoot ηb r (6 * a))
    (hshell : ∀ p : Variables n, ‖p.2.2‖ = b → ∀ z : Euclidean 2,
      (p, z) ∈ closure (augmentedTransportGradient (transportPosition T current.Q) ''
        conicMaskSupport zRoot ηb r' a') → (p, z) ∈ closedBall q₀ τ)
    (uSource : Variables n × Euclidean 2 → SliceVariable n)
    (huRange : MapsTo (inverseCoordinates uSource) (conicTarget b q₀ τ)
      (symbolInputDomain zRoot ηb r (6 * a)))
    (huEq : ∀ p ∈ conicTarget b q₀ τ,
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
    let Ωcommon := conicTarget b q₀ τ
    extendedDensity d (symbolJacobian T current.Q) u Ω = extendedDensity av Jσ uSource Ωcommon ∧
      fullComplexMatrixAmplitude d (symbolJacobian T current.Q) u Ω S =
        fullComplexMatrixAmplitude av Jσ uSource Ωcommon S ∧
      fullReflectedMatrixAmplitude d (symbolJacobian T current.Q) u Ω S =
        fullReflectedMatrixAmplitude av Jσ uSource Ωcommon S ∧
      ∀ {rMeas : ℝ} (hrMeas : 0 < rMeas) (hcellMeas : 4 * rMeas < 1 / 2), 6 * rMeas < a' →
      let dMeas := coefficientsOfCarrier
        (data T current.Q (sourceDilation F σ) row col current.forward current.inverse
          (fun q ↦ σ * Real.sqrt (1 + v q)) hrMeas hcellMeas angular FixedCutoffs.highFrequency)
        (FixedCutoffs.physical hrMeas 1)
      let aMeas := coefficientsOfCarrier
        (normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
          hrMeas hcellMeas angular FixedCutoffs.highFrequency σ) (FixedCutoffs.physical hrMeas 1)
      let avMeas := {aMeas with
        normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T seed.inverse (σ, p))) •
          aMeas.normal p}
      extendedDensity dMeas (symbolJacobian T current.Q) u Ω =
        extendedDensity avMeas Jσ uSource Ωcommon ∧
      fullComplexMatrixAmplitude dMeas (symbolJacobian T current.Q) u Ω S =
        fullComplexMatrixAmplitude avMeas Jσ uSource Ωcommon S ∧
      fullReflectedMatrixAmplitude dMeas (symbolJacobian T current.Q) u Ω S =
        fullReflectedMatrixAmplitude avMeas Jσ uSource Ωcommon S := by
  have hretained := hgeometry
  obtain ⟨_, _, G, β, cJ, V₀, L₀, _, _, _, _, hInv, htransverse, _⟩ := hgeometry
  have hinput : conicMaskSupport zRoot ηb r' a' ⊆ symbolInputDomain zRoot ηb r (6 * a) :=
    (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
  have hne : ∀ p ∈ conicMaskSupport zRoot ηb r' a',
      transportAveragedGradient (transportPosition T current.Q) p ≠ 0 :=
    fun p hp ↦ transportGradient_ne_zero T current.Q hηb hr htransverse (hinput hp)
  have hpuncturedCurrent := mask_image_punctured_subset_conicTarget hb hτ q₀ hne hshell
  have haug := (source_transport_on_retained_coefficient_domain (ηb := ηb)
    T seed.Q current.Q hP hF hrank hphysical seed.frame_eq htrans hσ hσ1 current.frame_eq
      hRT hV hVP houter).1
  have himage : augmentedTransportGradient (transportPosition T current.Q) ''
      conicMaskSupport zRoot ηb r' a' =
      augmentedTransportGradient (normalizedTransportPosition T seed.Q σ) ''
        conicMaskSupport zRoot ηb r' a' :=
    Set.image_congr (fun p hp ↦ haug (hinput hp))
  have hpunctured : closure (augmentedTransportGradient (normalizedTransportPosition T seed.Q σ) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆ conicTarget b q₀ τ := by
    rw [← himage]
    exact hpuncturedCurrent
  have hsub := conicTarget_subset_symbolDomain T current.Q hb houtput
  have heq : conicTarget b q₀ τ ∩ symbolDomain T current.Q zRoot ηb r (6 * a) =
      conicTarget b q₀ τ := inter_eq_left.mpr hsub
  have hmatched := retained_source_fullAmplitudes_eq_normalized_on_common_cone hP T hΩflow hKΩ hΩpatch
    hRc hτflow hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hR hRT hRU hV hVP hflow D hD hηb hr hr' ha' hrr haa har' hcell houter
    hσ hσ1 current hretained
    (conicTarget b q₀ τ ∩ symbolDomain T current.Q zRoot ηb r (6 * a))
    (fun p hp ↦ ⟨hpunctured hp, hsub (hpunctured hp)⟩)
    (symbolInputDomain zRoot ηb r (6 * a)) Subset.rfl uSource
    ((huRange.mono_left inter_subset_left).mono_right (NormalizedSelection.subset_radialInputDomain _))
    (fun p hp ↦ huEq p hp.1) v S
  simpa only [heq] using hmatched

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
