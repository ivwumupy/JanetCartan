module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.RetainedKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Output

/-!
# The detector's unit operator on the density kernel's original masks

Specializing the retained frozen kernel at zero density perturbation realizes
the unit input of the detector gap, including its separated original symbol.
No kernel chart or smaller mask is selected for this specialization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel NullTransport
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity NormalizedBackground.SourceGeometry
open SourceDensityLimitRealization RetainedFrozen.UnitRealization
open Pseudodifferential AmplitudeBound PeriodicLocalL2

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)

set_option quotPrecheck false in
local notation "angular₀" => angularMask zRoot (NormedSpace.normalize ηb) ha'
  (angularWidth_spec hηb hr').1

include hr hrr haa har'


/-- Construct the unit carrier required by `initializedFrozenSeedGap_of_retained_normalized_family`
on the original frozen inverse, with its literal adjoint and separated symbol.
Use the retained zero-density kernel before its restriction to the common cone
(`app:ch_seed:eq:seed-frozen-detection`, `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-real-symbol`). -/
theorem unitCarrierOutput_of_retained_density_kernel
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hVP : V ⊆ parameter ⁻¹' parameterInterior (3 * P.radius / 2))
    (hb : ContDiffOn ℝ ∞ (fun q : Euclidean n × CarrierParameter ↦
      carrierScalarAmplitude T Q₀ F row col Φ Y (fun _ ↦ 1) (q.1, parameter q.2) •
        carrierNullvector T Q₀ col (q.1, parameter q.2)) (ball 0 R ×ˢ V))
    (hY : ContDiffOn ℝ ∞ (densityFootpoint T Y) (ball 0 R ×ˢ V))
    (hzero : ∀ z ∈ V, (densityFootpoint T Y (0, z)).1 = 0)
    (hparam : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityFootpoint T Y p).2 = parameter p.2)
    {zCell : Euclidean 3} {L s₀ : ℝ} (hL : 0 < L) (hs₀ : 0 < s₀)
    (hsource : ∀ σ ∈ Ioc (0 : ℝ) s₀,
      MapsTo (densityFootpoint T (sourceTransportFlow Y σ)) (ball 0 R ×ˢ V)
        (ball ((0 : Euclidean (n - 1)), zCell) (L / 16)))
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {β cJ : ℝ} {Vphase Lphase : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart T Q₀))
      (physicalParameterSet zRoot (6 * a) ×ˢ dataSet zRoot ηb (3 * r)))
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q₀) (physicalParameterSet zRoot (6 * a))
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r))
      Vphase Lphase β cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot (6 * a),
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q₀ p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
    (hVphase : IsOpen Vphase) (hLphase : Lphase ⊆ Vphase) (hcJ : 0 < cJ)
    (hslice : ∀ p ∈ physicalParameterSet zRoot (6 * a), ∀ u ∈ dataBox zRoot ηb (2 * r),
      ‖G.symm.toContinuousLinearMap.comp (fderiv ℝ (adaptedTransportChart T Q₀ p) u) -
        ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) Z
    let u := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    let Ω := frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
    let S := closedBall (spectatorCenter zRoot) (a' / 2)
    ∀ (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      {ρ τ : ℝ} (_hρ : 0 < ρ) (_hτ : 0 < τ)
      {W K : Set (InputVariables n)} (_hW : IsOpen W)
      (_hball : closedBall p₀ ρ ⊆ W) (_hK : IsCompact K) (_hWK : W ⊆ K)
      (_hKInput : K ⊆ symbolInputDomain zRoot ηb r (6 * a))
      (_houtput : closedBall q₀ τ ⊆ Ω)
      {I : Set ℝ} (_hI : IsOpen I) (_hII : Icc (0 : ℝ) 1 ⊆ I)
      (_hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W D.field.region)
      (_hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
      {δ ε ℓ : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε)
      (_hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
      (_hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
      (_hℓ : 0 < ℓ) (_hlow : 2 * ℓ ≤ 1)
      (_hrange : MapsTo (inverseCoordinates u) (closedBall q₀ τ) (closedBall p₀ ρ))
      (_hgap : ∀ p ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient Z) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
      (_hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ J p)
      (_hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v ∈ S,
        (x, v) ∈ closure (augmentedTransportGradient Z '' conicMaskSupport zRoot ηb r' a') →
          (x, v) ∈ closedBall q₀ τ)
      (_hsupportD : tsupport (FixedCutoffs.physical (n := n) ha' 1) ×ˢ
        carrierSupport zRoot (r := a') ⊆ D.field.carrier),
    UnitCarrierOutput T Q₀ F row col Φ Y zRoot ηb r a r' a' hr' ha' hcell hηb
      (2 * (n + 1)) le_rfl := by
  classical
  intro Z J u Ω S p₀ q₀ ρ τ hρ hτ W K hW hball hK hWK hKInput houtput
    I hI hII hsegI hseg A δ ε ℓ hδ hε hfreq hfoot hℓ hlow hrange hgap hJlow hshell hsupportD
  let e₀ := normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1)
    ha' hcell angular₀ FixedCutoffs.highFrequency 0
  let a₀ := coefficientsOfCarrier e₀ (FixedCutoffs.physical ha' 1)
  obtain ⟨_, _, B, hB, _, _, hreal⟩ := exists_retained_source_zero_density_limit_realization
    T Q₀ F row col Φ Y hηb hr hr' ha' hrr haa har' hcell hP hseed hF hi hrank hR hRT hRU hV
    houter hVP hb hY hzero hparam hL hs₀ hsource D hD har hcarrier hf hInv htrans hVphase hLphase
    hcJ hslice p₀ q₀ hρ hτ hW hball hK hWK hKInput houtput hI hII hsegI hseg A hδ hε hfreq
    hfoot hℓ hlow hrange hgap hJlow hshell hsupportD
  have hregular := hreal (fun _ ↦ 0) contDiffOn_const (by intro q hq; norm_num)
    (by intro q hq; norm_num [Set.mem_Icc]) (by
      change cNorm _ _ (0 : Euclidean (n - 1) × Euclidean 3 → ℝ) ≤ 1
      rw [cNorm_zero]
      norm_num) false
  obtain ⟨hb₀, hA, _, Vop, _, _, htest, hsupp, hunique, hadjoint, _, hnormal, _⟩ := hregular
  simp only [add_zero, Real.sqrt_one, one_smul, weightNormal] at hb₀ hA htest hsupp hunique hadjoint hnormal
  have hsupport : ∀ x, a₀.measurement x ≠ 0 → ∀ j, |x j| ≤ 4 * a' :=
    fun x hx j ↦ (PiLp.norm_apply_le x j).trans
      (mem_closedBall_zero_iff.mp (FixedCutoffs.physical_tsupport_four ha' 1 (subset_tsupport _ hx)))
  have hn : 0 < n := by have := row.isLt; omega
  refine ⟨hn, hsupport, B, hB, hb₀, (fun j k ξ is his ↦ hA j k ξ is (his.trans (Nat.le_succ _))),
    Vop, htest, hsupp, hunique, hadjoint, hnormal, ?_⟩
  intro ξ x y i j
  have he := fullReflectedMatrixAmplitude_normalizedCarrierData_zero
    T Q₀ F row col Φ Y (fun _ ↦ 1) angular₀ FixedCutoffs.highFrequency (adaptedSliceCoordinates T)
    hP hηb hr har hcarrier hInv htrans ha' hcell S x y ξ
  simpa only [Matrix.smul_apply, Pi.smul_apply, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
    using congrFun (congrFun he i) j

end JanetCartan.ContinuumNormal.ActualConstruction
