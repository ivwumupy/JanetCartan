module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.ZeroCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.ActualConstruction.DensityFreezing.PositionLocalization
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.SupportedShell.PrimitiveBudget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.Primitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedSupport

/-!
# Uniform reflected-amplitude bounds for both literal density limits

Instantiate the supported primitive-amplitude theorem on the same normalized
unit seed with the two original density weights. All coefficient and geometry
norms, and all weighted primitive regularity, are discharged here. The conic
inverse equations, buffers and support containment are the published primitive
inputs of the retained geometry producer; its same-family instantiation is
still required. No normal-operator identity is assumed or asserted here.

Consumer: `exists_sourceDensityLimit_frozen_error_constant`, which absorbs
the two-position spatial error in the local frozen gap. The required order
is exactly `μ+1`; the density class remains the original `μ+14` class.
Sources: `app:ch_background:prop:bg-frame`, `bg-mixed-input`,
`bg-full-complex-amplitude`, `bg-real-symbol`, `bg-Nsigma`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.ActualConstruction
open ActualCarriers FrozenMenu CurrentFullPhase ContinuumRow CanonicalCarrier FrozenModel
open NullTransport ContinuumNormalReduction.TransportSymbol NormalizedBackground.SourceGeometry
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.PositiveReference
open CarrierVariation.FamilyInputs.WideDensity
open CarrierNormalRealization AmplitudeBound

/-- Apply the supported full-amplitude producer to both literal zero-scale
density weights. One positive bound precedes the density. The normalized seed
producer proves its coefficient norms, the original-domain ODE producer proves
its label ranges, and the actual frozen transport proves its geometry norms.
All masks, inverse, Jacobian, spectator set and reflected normalization agree
on both sides. No amplitude bound or coefficient control is a hypothesis.

The remaining geometric hypotheses are the existing supported primitive
constructor inputs, as used by
`NormalizedCarrierProfiles.exists_actual_source_density_reflected_bounds`.
The retained normalized selection must instantiate them on the SAME full mask
support. Primitive regularity is needed only in the original physical ball;
the exact measurement-localization identity transfers the bound to the original
inverse domain. This theorem does not select replacement masks. Consumer:
`exists_sourceDensityLimit_frozen_error_constant`
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-local-bound`). -/
theorem exists_source_zero_density_reflected_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (ha : ContDiff ℝ ∞ (Function.uncurry angular))
    {c C : ℝ} (hP : P.IsValid c C) (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    {R : ℝ} (hR : 0 < R) (hRT : R ≤ T.physicalRadius) (hRU : ball (0 : Euclidean n) R ⊆ U)
    (hMeasR : 3 * r ≤ R)
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
    (D : CoefficientNormCharts n) (hD : D.field.region ⊆ ball (0 : Euclidean n) R ×ˢ V) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
    let a := TransportKernel.coefficientsOfCarrier
      (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular
        FixedCutoffs.highFrequency 0) (FixedCutoffs.physical hr 1)
    let physicalPositions := {p : Variables n × Euclidean 2 |
      p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
    ∀ (p₀ : InputVariables n) (q₀ : Variables n × Euclidean 2)
      {ρ τ : ℝ} (_hρ : 0 < ρ) (_hτ : 0 < τ)
      {W K : Set (InputVariables n)} (_hW : IsOpen W)
      (_hball : closedBall p₀ ρ ⊆ W) (_hK : IsCompact K) (_hWK : W ⊆ K)
      {O : Set (Variables n × Euclidean 2)} (_hO : IsOpen O)
      (_houtput : closedBall q₀ τ ⊆ O)
      {I : Set ℝ} (_hI : IsOpen I) (_hII : Icc (0 : ℝ) 1 ⊆ I)
      (_hsegI : ∀ t ∈ I, MapsTo (transportSegmentInput n t) W D.field.region)
      (_hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W D.field.carrier)
      (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
      {δ ε Cupper ℓ : ℝ} (_hδ : 0 < δ) (_hε : 0 < ε)
      (_hfreq : ∀ p ∈ closedBall p₀ ρ, ε ≤ ‖p.2.2‖)
      (_hfoot : ∀ p ∈ closedBall p₀ ρ, D.Contains p)
      (_hCupper : 0 ≤ Cupper) (_hℓ : 0 < ℓ) (_hℓone : ℓ ≤ 1) (_hlow : Cupper * ℓ ≤ 1)
      {S : Set (Euclidean 2)} (_hS : IsCompact S)
      (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
      {Ω : Set (Variables n × Euclidean 2)} (_hΩ : IsOpen (Ω ∩ physicalPositions)) (_hOΩ : O ⊆ (Ω ∩ physicalPositions))
      (_hu : ContDiffOn ℝ ∞ u (Ω ∩ physicalPositions))
      (_hrange : MapsTo (inverseCoordinates u) (closedBall q₀ τ) (closedBall p₀ ρ))
      (_hgap : ∀ p ∈ closedBall p₀ ρ,
        ‖A.symm.toContinuousLinearMap.comp (fderiv ℝ (augmentedTransportGradient Z) p) -
          ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
      (_heq : ∀ p ∈ (Ω ∩ physicalPositions), transportAveragedGradient Z (inverseCoordinates u p) = p.1.2.2)
      (_hJne : ∀ p ∈ W, J p ≠ 0)
      (_hJlow : ∀ p ∈ closedBall p₀ ρ, δ ≤ J p)
      {Uinput Zmask : Set (InputVariables n)}
      (_hJ : ContDiffOn ℝ ∞ J Uinput)
      (_hInputJ : ∀ p ∈ Uinput, J p ≠ 0)
      (_hInputFreq : ∀ p ∈ Uinput, p.2.2 ≠ 0)
      (_hend : ∀ side, MapsTo (densityEndpoint side) Uinput D.field.region)
      (_hmap : MapsTo (inverseCoordinates u) (Ω ∩ physicalPositions) Uinput)
      (_hmask : ∀ p ∈ Uinput, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
        a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ Zmask)
      (_hpunctured : closure (augmentedTransportGradient Z '' Zmask) ∩
        {p | p.1.2.2 ≠ 0} ⊆ (Ω ∩ physicalPositions))
      (_hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v ∈ S,
        (x, v) ∈ closure (augmentedTransportGradient Z '' Zmask) →
          (x, v) ∈ closedBall q₀ τ)
      (_hcone : ∀ t : ℝ, 0 < t → ∀ p, (scaleFrequency t p.1, p.2) ∈ (Ω ∩ physicalPositions) ↔ p ∈ (Ω ∩ physicalPositions))
      (_huScale : ∀ t : ℝ, 0 < t → ∀ p ∈ (Ω ∩ physicalPositions),
        u (scaleFrequency t p.1, p.2) = ((u p).1, t • (u p).2))
      (_hJScale : ∀ t : ℝ, 0 < t → ∀ p ∈ (Ω ∩ physicalPositions),
        J (scaleInput t (inverseCoordinates u p)) = t * J (inverseCoordinates u p))
      (_hupper : ∀ p ∈ (Ω ∩ physicalPositions), ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖),
    ∃ B > (0 : ℝ), ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)) →
      (∀ q ∈ ball ((0 : Euclidean (n - 1)), zCell) (L / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
        1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8))
        (2 * (n + 1) + 14) v ≤ 1 →
      let aActual := {a with
        normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, p))) • a.normal p}
      let aFrozen := {a with
        normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p}
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude aActual J u Ω S)) ∧
        ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude aFrozen J u Ω S)) ∧
        (∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude aActual J u Ω S ξ z i j)
          (2 * (n + 1) + 1) B) ∧
        (∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude aFrozen J u Ω S ξ z i j)
          (2 * (n + 1) + 1) B) := by
  let s := 2 * (n + 1) + 1
  obtain ⟨Mc, hMc, Bc, hBc, hcoeff⟩ :=
    exists_source_zero_density_coefficient_controls T Q₀ F row col Φ Y hr hcell
      angular FixedCutoffs.highFrequency (FixedCutoffs.physical hr 1)
      hP hseed hF hi hrank hR hRT hRU hV hVP hb hY hzero hparam hL hs₀ hsource
      D hD (FixedCutoffs.physical hr 1).contDiff.contDiffOn ha.contDiffOn
      FixedCutoffs.highFrequency_smooth.contDiffOn
  dsimp only
  let Z := normalizedTransportPosition T Q₀ 0
  let J := transportAbsoluteJacobian (CanonicalConic.adaptedSliceCoordinates T) Z
  let a := TransportKernel.coefficientsOfCarrier
    (normalizedCarrierData T Q₀ F row col Φ Y (fun _ ↦ 1) hr hcell angular
      FixedCutoffs.highFrequency 0) (FixedCutoffs.physical hr 1)
  intro p₀ q₀ ρ τ hρ hτ W K hW hball hK hWK O hO houtput I hI hII hsegI hseg
    A δ ε Cupper ℓ hδ hε hfreq hfoot hCupper hℓ hℓone hlow S hS
    u Ω hΩ hOΩ hu hrange hgap heq hJne hJlow Uinput Zmask hJ hInputJ hInputFreq
    hend hmap hmask hpunctured hshell hcone huScale hJScale hupper
  let Ωlocal := Ω ∩ {p | p.1.1 ∈ ball (0 : Euclidean n) R ∧ p.1.2.1 ∈ ball 0 R}
  have hZ : ContDiffOn ℝ ∞ Z D.field.region :=
    (normalizedTransportPosition_zero_smooth T Q₀ hP).mono
      (fun p hp ↦ ⟨mem_univ _, hVP (hD hp).2⟩)
  let Mp := cNorm D.field.carrier 3 Z
  let Bp := 1 + cNorm D.field.carrier (s + 2) Z
  have hMp : 0 ≤ Mp := cNorm_nonneg ..
  have hBp : 0 ≤ Bp := add_nonneg zero_le_one (cNorm_nonneg ..)
  obtain ⟨B, hB, hbudget⟩ :=
    exists_fullReflectedMatrixAmplitude_supported_bounds_of_primitiveNorms
      (N := N) (CanonicalConic.adaptedSliceCoordinates T) p₀ q₀ hρ hτ hW hball hK hWK
      hO houtput D.field.isOpen_region (isCompact_closedBall ..) D.field.ball_subset
      hI hII hsegI hseg A hMp hMc.le hBc hδ hε hBp hfreq D hfoot
      hCupper hℓ hℓone hlow hS s (by dsimp [s]; omega)
      FixedCutoffs.highFrequency_smooth (fun _ ht ↦ FixedCutoffs.highFrequency_zero ht)
      (fun _ ht ↦ FixedCutoffs.highFrequency_one ht)
  refine ⟨B, hB, ?_⟩
  intro v hv hpos hinterval hvnorm
  obtain ⟨hcActual, hcFrozen⟩ := hcoeff v hv hpos hinterval hvnorm
  let aActual := {a with
    normal := fun p ↦ Real.sqrt (1 + v (sourceDensityFootpointExtension T Y (0, p))) • a.normal p}
  let aFrozen := {a with
    normal := fun p ↦ Real.sqrt (1 + v (0, parameter p.2)) • a.normal p}
  have hEach (d : Coefficients n N)
      (hc : D.Controls s Mc Bc 1 d)
      (hm : d.measurement = a.measurement) (hang : d.angular = a.angular)
      (hhigh : d.high = FixedCutoffs.highFrequency) :
      ContDiff ℝ ∞ (Function.uncurry (fullReflectedMatrixAmplitude d J u Ω S)) ∧
        ∀ i j, HasAmplitudeDerivativeBound
          (fun ξ z ↦ fullReflectedMatrixAmplitude d J u Ω S ξ z i j) s B := by
    have hmSmooth : ContDiff ℝ ∞ d.measurement := by
      rw [hm]
      exact (FixedCutoffs.physical hr 1).contDiff
    have hreg : PrimitiveRegularity d J Uinput := {
      leftMeasurement := hmSmooth.comp_contDiffOn contDiffOn_fst.fst
      rightMeasurement := hmSmooth.comp_contDiffOn contDiffOn_fst.snd
      angular := by rw [hang]; exact ha
      high := by rw [hhigh]; exact FixedCutoffs.highFrequency_smooth
      leftNormal := hc.normal.smooth.comp (densityEndpoint_contDiff false).contDiffOn (hend false)
      rightNormal := hc.normal.smooth.comp (densityEndpoint_contDiff true).contDiffOn (hend true)
      leftReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
        (densityEndpoint_contDiff false).contDiffOn (hend false)
      rightReduced := fun j ↦ (contDiffOn_pi.mp hc.reduced.smooth j).comp
        (densityEndpoint_contDiff true).contDiffOn (hend true)
      jacobian := hJ
      jacobian_ne_zero := hInputJ
      covector_ne_zero := hInputFreq }
    have hRfreq : IsOpen {p : Variables n | p.2.2 ≠ 0} :=
      isOpen_compl_singleton.preimage continuous_snd.snd
    have hX : {p : Variables n | ‖p.2.2‖ = ℓ} ⊆ {p | p.2.2 ≠ 0} := by
      intro p hp
      exact norm_ne_zero_iff.mp (hp.trans_ne hℓ.ne')
    obtain ⟨hb', hAb, _⟩ := hbudget d Z u J Ωlocal Uinput Zmask
      {p | ‖p.2.2‖ = ℓ} {p | p.2.2 ≠ 0} 1 hZ le_rfl hΩ hOΩ hu hrange hgap heq
      (fun _ _ ↦ rfl) hJne hJlow le_rfl (by simp only [Bp, mul_one]; exact le_rfl)
      hreg hmap (by simpa only [hm, hang] using hmask) hRfreq hX
      (fun p hp ↦ hpunctured ⟨hp.1, hp.2.1⟩)
      (fun x hx v' hv' hxv ↦ hshell x hx v' hv' hxv) hc hcone huScale hJScale hupper
      hpunctured (CanonicalConic.scaleFrequency_mem_fixed_sphere hℓ)
    have hd : {d with high := FixedCutoffs.highFrequency} = d := by
      rw [← hhigh]
    rw [hd] at hb' hAb
    have hlocalization : fullReflectedMatrixAmplitude d J u Ωlocal S =
        fullReflectedMatrixAmplitude d J u Ω S :=
      fullReflectedMatrixAmplitude_inter_fixed_measurement_ball hr hMeasR d hm J u Ω S
    rw [hlocalization] at hb' hAb
    exact ⟨hb', by simpa only [mul_one] using hAb⟩
  obtain ⟨hActual, hActualBound⟩ := hEach aActual hcActual rfl rfl rfl
  obtain ⟨hFrozen, hFrozenBound⟩ := hEach aFrozen hcFrozen rfl rfl rfl
  exact ⟨hActual, hFrozen, hActualBound, hFrozenBound⟩

end JanetCartan.ContinuumNormal.ActualConstruction
