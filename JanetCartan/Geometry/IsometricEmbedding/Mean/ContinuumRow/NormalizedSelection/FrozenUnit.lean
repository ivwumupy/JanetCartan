module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FrozenIdentification
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SeedZeroRealization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Output

/-!
# The original frozen unit carrier on admitted source geometry

Specialize the constructed genuine zero-density realization and transfer its
literal kernel and full reflected amplitude to the admitted source frame.
The original immersion, initial unit scalar, inverse labels and masks are fixed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalCarrier CanonicalConic ContinuumNormal FrozenModel RetainedFrozen
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry
open ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ContinuumNormal.CarrierVariation.FamilyInputs.WideDensity
open PositiveReference.FlowConstruction
open NullTransport ActualFlow FlowAmplitude NormalizedBackground.SourceGeometry
open Pseudodifferential AmplitudeBound PeriodicLocalL2 SourceDensityLimitRealization
open NormalizedNormalLimit RetainedFrozen.UnitRealization

/-- Construct the existing frozen-unit output using the original seed and the
selected geometry of one positive source. The zero-density realization provides
the bounded operator and literal adjoint; exact kernel and full-amplitude
identification retain that operator, and the original frozen-symbol formula
provides separation. No seed-frame spectral hypothesis, analytic gap or inverse
estimate is assumed. Consumer: `exists_retained_frozen_row_gap`, with the admitted
source frame and the original immersion (`new:lem:scaling`,
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, `app:ch_background:prop:bg-frame`). -/
theorem unitCarrierOutput_on_original_seed_of_source_geometry
    {n N : ℕ} {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {Ωflow : Set (Euclidean n × Euclidean 3)} (hΩflow : IsOpen Ωflow)
    {zCell : Euclidean 3} {ρc Rc Bflow τflow : ℝ} {row col : Fin n}
    (hKΩ : closedBall ((0 : Euclidean n), zCell) ρc ⊆ Ωflow)
    (hΩpatch : Ωflow ⊆ (U ∩ ball 0 T.physicalRadius) ×ˢ
      parameterInterior (3 * P.radius / 2))
    (hRc : 0 < Rc) (hτ : 0 < τflow) (hτR : τflow ≤ Rc / 16)
    (hbuffer : MapsTo (coordinates (adaptedCoordinates T.data.adapted)).symm
      (closedBall (0, ((0 : Euclidean (n - 1)), zCell)) Rc)
      (closedBall ((0 : Euclidean n), zCell) ρc))
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (seed : Chart T Ωflow (closedBall ((0 : Euclidean n), zCell) ρc)
      ((0 : Euclidean (n - 1)), zCell) Rc Bflow τflow row col F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU seed.Q.1 seed.Q.2.1).hp q,
        T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    {L Mc R : ℝ} (hL : 0 < L) (hMc : 0 < Mc) (hR : 0 < R)
    (hforward : cNorm (Icc (-τflow) τflow ×ˢ
      closedBall ((0 : Euclidean (n - 1)), zCell) (Rc / 8)) 1 seed.forward ≤ Mc)
    (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hRtime : R ≤ L / (64 * Mc))
    {V : Set CarrierParameter} (hV : IsOpen V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τflow))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (Qanchor : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {anchor : ℝ} (hanchor : 0 < anchor) (hanchor1 : anchor ≤ 1)
    (hanchorFrame : Qanchor.1 = ProjectedStressFrame.projectedStress (sourceDilation F anchor))
    (hgeometry : RetainedSpectralGeometry T Qanchor zRoot ηb r a)
    (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
    {ρ τ : ℝ} (hρ : 0 < ρ) (hτout : 0 < τ)
    {W K : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall p₀ ρ ⊆ W) (hK : IsCompact K) (hWK : W ⊆ K)
    (hKInput : K ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Qanchor zRoot ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Qanchor zRoot ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = 1 / 4 → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Qanchor) ''
        conicMaskSupport zRoot ηb r' a') → (x, v) ∈ closedBall q₀ τ)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegI : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W D.field.region)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
    (hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
    (hgap : ∀ p ∈ closedBall p₀ ρ,
      ‖A.symm.toContinuousLinearMap.comp
        (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Qanchor 0)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ transportAbsoluteJacobian (adaptedSliceCoordinates T)
      (normalizedTransportPosition T Qanchor 0) p)
    (hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
      carrierSupport zRoot (r := a') ⊆ D.field.carrier) :
    UnitCarrierOutput T Qanchor F row col seed.forward seed.inverse zRoot ηb r a r' a'
      hr' ha' hcell hηb (2 * (n + 1)) le_rfl := by
  classical
  let angular := angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1
  let e₀ := normalizedCarrierData T seed.Q F row col seed.forward seed.inverse (fun _ ↦ 1)
    ha' hcell angular FixedCutoffs.highFrequency 0
  let e := normalizedCarrierData T Qanchor F row col seed.forward seed.inverse (fun _ ↦ 1)
    ha' hcell angular FixedCutoffs.highFrequency 0
  let d := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
  let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Qanchor 0)
  let u := frozenSymbolInverse T Qanchor zRoot ηb r (6 * a)
  let Ω := frozenSymbolDomain T Qanchor zRoot ηb r (6 * a)
  let S := closedBall (spectatorCenter zRoot) (a' / 2)
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, hcJ, hVi, hLi, hf, hInv, hcone, hslice⟩ := hgeometry
  have hgeometry : RetainedSpectralGeometry T Qanchor zRoot ηb r a :=
    ⟨har, hcarrier, G, β, cJ, Vi, Li, hcJ, hVi, hLi, hf, hInv, hcone, hslice⟩
  have hcommon := frozenRefinedMaskImage_punctured_buffer T Qanchor hP hηb hr
    (ha'.trans_le haa) har hcarrier hf hcone hrr haa
  obtain ⟨_, _, B, hB, hreal⟩ := exists_retained_seed_zero_density_realization_of_source hP T
    hΩflow hKΩ hΩpatch hRc hτ hτR hbuffer hF hi hrank hphysical seed htrans hflat
    hL hMc hR hforward hRT hRU hRtime hV hVP hflow hlabel D hD
    hηb hr hr' ha' hrr haa har' hcell houter Qanchor hanchor hanchor1 hanchorFrame
    hgeometry p₀ q₀ hρ hτout hW hball hK hWK hKInput houtput hrange hshell
    hIt hIIt hsegI hseg A hδ hε hfreq hfoot hgap hJlow hsupportD Subset.rfl hcommon
  have hregular := hreal (fun _ ↦ 0) contDiffOn_const (by intro q hq; norm_num)
    (by intro q hq; norm_num [Set.mem_Icc]) (by
      change cNorm _ _ (0 : Euclidean (n - 1) × Euclidean 3 → ℝ) ≤ 1
      rw [cNorm_zero]
      norm_num) false
  obtain ⟨hb₀, hA₀, hs₀, Vop, _, _, htest₀, hadjoint₀, hunique₀, _, hnormal₀, _⟩ := hregular
  simp only [add_zero, Real.sqrt_one, one_smul, weightNormal] at hb₀ hA₀ hs₀ htest₀ hadjoint₀ hunique₀ hnormal₀
  have hangular : ∀ z η, angular z η ≠ 0 → parameter z ∈ parameterInterior (2 * P.radius) := by
    intro z η hz j
    have hm := angularMask_nonzero zRoot (NormedSpace.normalize ηb) ha'
      (angularWidth_spec hηb hr').1 hz
    have hsmall : a' / 2 ≤ 3 * r := by linarith
    have hh := hcarrier (a := (z.2, z.1)) ⟨closedBall_subset_closedBall hsmall (ball_subset_closedBall hm.2.1),
      closedBall_subset_closedBall hsmall (ball_subset_closedBall hm.1)⟩
    exact (hh j).trans (by linarith [hP.1])
  obtain ⟨_, htestEq, hadjointEq⟩ := normalized_zero_kernel_and_integrals_eq_of_source_frame
    T seed.Q Qanchor hF hrank hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame
    row col seed.forward seed.inverse (fun _ ↦ 1) ha' hcell angular FixedCutoffs.highFrequency hangular
  have htest : ∀ f : carrierInitialTestSpace n,
      Vop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val := by
    intro f
    rw [htestEq]
    exact htest₀ f
  have hadjoint : ∀ f : ComplexOutputL2 n, MemLp (carrierAdjointIntegral e f) 2 (carrierMeasure n) ∧
      Vop.adjoint f =ᵐ[carrierMeasure n] carrierAdjointIntegral e f := by
    intro f
    rw [hadjointEq]
    exact hadjoint₀ f
  have hunique : ∀ Wop : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
      (∀ f : carrierInitialTestSpace n,
        Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → Wop = Vop := by
    intro Wop hWop
    apply hunique₀ Wop
    intro f
    change Wop (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e₀ f.val
    rw [← htestEq]
    exact hWop f
  have hdom := frozenSymbolDomain_eq_of_source_dilation T seed.Q Qanchor hF hrank hphysical
    seed.frame_eq htrans hanchor hanchor1 hanchorFrame hP (ηb := ηb) hr har hcarrier
  have hamp := (normalized_zero_fullAmplitudes_eq_of_source_frame T seed.Q Qanchor hF hrank
    hphysical seed.frame_eq htrans hanchor hanchor1 hanchorFrame row col seed.forward seed.inverse
    (fun _ ↦ 1) hP hηb hr hgeometry ha' hcell angular FixedCutoffs.highFrequency
      (FixedCutoffs.physical ha' 1) S).2.2
  rw [← hdom] at hamp
  have hb : ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)) := by
    rw [hamp]
    exact hb₀
  have hA : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) (2 * (n + 1)) B := by
    rw [hamp]
    exact fun i j ξ is his ↦ hA₀ i j ξ is (his.trans (Nat.le_succ _))
  have hsupport : ∀ x, d.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' :=
    fun x hx j ↦ (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)))
  have hn : 0 < n := by have := row.isLt; omega
  refine ⟨hn, hsupport, B, hB, hb, hA, Vop, htest,
    carrierRealization_eq_zero_outside e Vop htest, hunique, hadjoint, ?_, ?_⟩
  · exact realized_normal_eq_of_amplitude_witnesses hn (4 * a') (4 * a') _ _ hb₀ hb
      hs₀ (fullReflectedMatrixAmplitude_supportedInCenteredBox d J u Ω S (4 * a') hsupport)
      B B (fun i j ξ is his ↦ hA₀ i j ξ is (his.trans (Nat.le_succ _)))
      (fun i j ξ is his ↦ hA i j ξ is (his.trans le_rfl)) hamp.symm Vop hnormal₀
  · intro ξ x y i j
    have he := fullReflectedMatrixAmplitude_normalizedCarrierData_zero
      T Qanchor F row col seed.forward seed.inverse (fun _ ↦ 1) angular FixedCutoffs.highFrequency
      (adaptedSliceCoordinates T) hP hηb hr har hcarrier hInv hcone ha' hcell S x y ξ
    simpa only [Matrix.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
      using congrFun (congrFun he i) j

end JanetCartan.ContinuumRow.NormalizedSelection
