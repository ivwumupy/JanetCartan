module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.SourceAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.NormalSmallness

/-!
# Small realized reflected normals for the supplied normalized source

Apply the concrete full-amplitude limit to the existing PDO L² subtraction
estimate. The source cap precedes the scale, density and operator realization.
The same full reflected amplitudes and existing Fourier measures occur in
both literal normal identities. Full-mask geometry and row realization remain
obligations of the selection producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport NormalizedBackground.SourceGeometry
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity AmplitudeBound Pseudodifferential PeriodicLocalL2

/-- The actual normalized full-amplitude limit gives an arbitrarily small
reflected carrier-normal difference through exactly `2 * (n + 1)` derivatives,
uniformly over the ORIGINAL positive density class. The same-row normal
identifications are retained literally, and reflection is counted only once.
No row-operator continuity or normal-difference hypothesis occurs.

Consumer: `exists_reflected_amplitude_half_gap_tolerance` and the actual
normalized comparison in `both-normal-coercivity`, followed by `SourceInverse`.
For a finite row, use the carrier share of the gap before choosing its common
source cap. Sources: `app:ch_background:prop:bg-normalized`,
`bg-full-complex-amplitude`, `bg-real-symbol`, and
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_source_reflectedNormal_tolerance
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    {V : Set CarrierParameter} (hV : IsOpen V)
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
    (ha : ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean (n - 1) ↦ angular p.1 p.2))
    (hh : ContDiff ℝ ∞ high)
    (hhighZero : ∀ r, r ≤ 1 → high r = 0) (hhighOne : ∀ r, 2 ≤ r → high r = 1)
    {u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {K W : Set (InputVariables n)} {Q Ω : Set (Variables n × Euclidean 2)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hQ : IsCompact Q) (hΩ : IsOpen Ω) (hQΩ : Q ⊆ Ω)
    (hrange : ∀ p ∈ K, D.Contains p)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {e δ : ℝ} (he : 0 < e) (hδ : 0 < δ)
    (hjoint : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (normalizedTransportPosition T Q₀ q.1) q.2)
        (Ioo (-e) e ×ˢ W))
    (hfamily : ∀ σ ∈ Ioo (-e) e,
      ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
      (∀ q ∈ Ω, transportAveragedGradient (normalizedTransportPosition T Q₀ σ)
        (inverseCoordinates (u σ) q) = q.1.2.2) ∧
      (∀ p ∈ K,
        ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (normalizedTransportPosition T Q₀ σ)) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
      (∀ p ∈ K, δ ≤ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
        (normalizedTransportPosition T Q₀ σ) p))
    {sourceCap : ℝ} (hsourceCap : 0 < sourceCap)
    (hend : ∀ side, MapsTo (densityEndpoint side) W D.field.region)
    (hfreqW : ∀ p ∈ W, p.2.2 ≠ 0)
    {η : ℝ} (hη : 0 < η) (hfreq : ∀ p ∈ K, η ≤ ‖p.2.2‖)
    (Zmask : Set (InputVariables n))
    (hmask : ∀ p ∈ W, FixedCutoffs.physical hr 1 p.1.1 ≠ 0 →
      FixedCutoffs.physical hr 1 p.1.2 ≠ 0 →
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
    {S : Set (Euclidean 2)} (hS : IsCompact S)
    {Cupper ℓ : ℝ} (hCupper : 0 ≤ Cupper) (hℓ : 0 < ℓ) (hlow : Cupper * ℓ ≤ 1)
    (hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ Ω ↔ p ∈ Ω)
    (hglobal : ∀ σ ∈ Icc (0 : ℝ) sourceCap,
      let Z := normalizedTransportPosition T Q₀
      let J := fun t ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) (Z t)
      ContDiffOn ℝ ∞ (J σ) W ∧ (∀ p ∈ W, J σ p ≠ 0) ∧
      MapsTo (inverseCoordinates (u σ)) Ω W ∧
      (closure (augmentedTransportGradient (Z σ) '' Zmask) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω) ∧
      (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ Cupper * ‖p.1.2.2‖) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        u σ (scaleFrequency t p.1, p.2) = ((u σ p).1, t • (u σ p).2)) ∧
      (∀ t : ℝ, 0 < t → ∀ p ∈ Ω,
        J σ (scaleInput t (inverseCoordinates (u σ) p)) = t * J σ (inverseCoordinates (u σ) p)) ∧
      (∀ p : Variables n, ‖p.2.2‖ = ℓ → ∀ v ∈ S,
        (p, v) ∈ closure (augmentedTransportGradient (Z σ) '' Zmask) ∪
          closure (augmentedTransportGradient (Z 0) '' Zmask) → (p, v) ∈ Q))
    (hn : 0 < n) (Rbox : ℝ) :
    let μ := 2 * (n + 1)
    let a := fun σ ↦ TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular high σ)
      (FixedCutoffs.physical hr 1)
    let J := fun σ ↦ transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T)
      (normalizedTransportPosition T Q₀ σ)
    let foot := fun σ p ↦ sourceDensityFootpointExtension T Y (σ, p)
    let b := fun σ (v : Euclidean (n - 1) × Euclidean 3 → ℝ) ↦
      fullReflectedMatrixAmplitude
        {(a σ) with normal := fun p ↦ Real.sqrt (1 + v (foot σ p)) • (a σ).normal p}
        (J σ) (u σ) Ω S
    ∀ ε > 0, ∃ cap > 0, cap ≤ sourceCap ∧ cap ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap, ∀ d₀ : ℕ, μ + 1 ≤ d₀ →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), ContDiffAt ℝ ∞ v y) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) d₀ v ≤ 1 →
      (∀ y ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8), (1 / 2 : ℝ) ≤ 1 + v y) →
      let pair := fun t : Fin 2 ↦ b (![σ, 0] t) v
      ∀ (hb : ∀ t, ContDiff ℝ ∞ (Function.uncurry (pair t)))
        (hs : ∀ t ξ i j, SupportedInCenteredBox Rbox (fun z ↦ pair t ξ z i j))
        (B : Fin 2 → ℝ)
        (hB : ∀ t i j, HasAmplitudeDerivativeBound (fun ξ z ↦ pair t ξ z i j) μ (B t))
        (Urow : Fin 2 → CarrierL2 n →L[ℂ] ComplexOutputL2 n),
        (∀ t, carrierChannel (Urow t) ∘L (carrierChannel (Urow t)).adjoint =
          realOutputCompression (transferOperator
            (vectorTwoPositionL2Operator hn Rbox (pair t) (hb t) (hs t) (B t) (hB t)))) →
        ‖carrierChannel (Urow 0) ∘L (carrierChannel (Urow 0)).adjoint -
          carrierChannel (Urow 1) ∘L (carrierChannel (Urow 1)).adjoint‖ ≤ ε := by
  intro μ a J foot b ε hε
  let Kpdo := (n : ℝ) ^ 2 * fixedBoxAmplitudeConstant n Rbox
  have hKpdo : 0 ≤ Kpdo := mul_nonneg (sq_nonneg _) (fixedBoxAmplitudeConstant_nonneg _ _)
  let tol := ε / (Kpdo + 1)
  have htol : 0 < tol := div_pos hε (by positivity)
  obtain ⟨cap, hcap, hsourceBound, hcap1, hsmall⟩ :=
    exists_source_fullAmplitude_sqrtFootpoints_tolerance T Q₀ F row col Φ Y hr hcell angular high
      hP hseed hF hi hrank hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource
      D hD ha hh hhighZero hhighOne hK hconv hW hKW hQ hΩ hQΩ hrange A he hδ
      hjoint hfamily hsourceCap hend hfreqW hη hfreq Zmask hmask hS hCupper hℓ hlow hcone hglobal
      tol htol
  refine ⟨cap, hcap, hsourceBound, hcap1, ?_⟩
  intro σ hσ d₀ horder v hv hvm hpos pair hbpair hs B hB Urow hnormal
  have hd : ∀ i j, HasAmplitudeDerivativeBound
      (fun ξ z ↦ (pair 0 - pair 1) ξ z i j) μ tol :=
    fun i j ↦ (hsmall σ hσ d₀ horder v hv hvm hpos i j).2
  have hsupport : ∀ ξ i j, SupportedInCenteredBox Rbox
      (fun z ↦ (pair 0 - pair 1) ξ z i j) := by
    intro ξ i j z hz
    by_cases hzero : pair 0 ξ z i j = 0
    · exact hs 1 ξ i j z (by
        simpa only [Pi.sub_apply, Matrix.sub_apply, hzero, zero_sub, neg_ne_zero] using hz)
    · exact hs 0 ξ i j z hzero
  rw [hnormal 0, hnormal 1]
  apply ((vectorTwoPositionL2Operator_sub_bounds hn Rbox (pair 0) (pair 1)
    (hbpair 0) (hbpair 1) ((hbpair 0).sub (hbpair 1)) (hs 0) (hs 1) hsupport
    (B 0) (B 1) tol (hB 0) (hB 1) μ le_rfl hd).2.2).trans
  have hcancel : (Kpdo + 1) * tol = ε := mul_div_cancel₀ ε (by positivity)
  rw [← mul_assoc]
  change Kpdo * tol ≤ ε
  nlinarith only [htol, hcancel]

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
