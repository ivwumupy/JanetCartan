module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedFrozenGap.Normalization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RetainedCharts

/-!
# Frozen carrier identification under an admitted source frame

The selected positive source supplies the inverse geometry used by the frozen
spectral gap. Its frozen coefficients agree with those of the original seed
when the original immersion, scalar, masks and measures are kept fixed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal FrozenModel NormalizedNormalLimit
open ContinuumNormal.CarrierVariation.FamilyInputs SourceMatching
open NormalizedBackground NormalizedBackground.SourceGeometry
open NullTransport ActualFlow FlowAmplitude HamiltonPhase
open CarrierVariation RetainedFrozen ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ q ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp q, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ))
    (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

include hF hrank hphysical hseed htrans hσ hσ1 hscaled

/-- At zero scale an admitted source frame has the original seed's transport,
covector, normal and stress value, with the original immersion and scalar.
Consumer: the unit carrier for the selected frozen gap
(`new:lem:scaling`, `app:ch_background:eq:bg-Nsigma`). -/
theorem normalized_zero_carrier_fields_eq_of_source_frame
    (x : Euclidean n) {z : CarrierParameter}
    (hz : parameter z ∈ parameterInterior (2 * P.radius)) :
    normalizedTransportPosition T Qσ 0 (x, z) = normalizedTransportPosition T Q₀ 0 (x, z) ∧
    normalizedCovector T Qσ 0 x z = normalizedCovector T Q₀ 0 x z ∧
    normalizedNormal T Qσ F row col Φ Y initial 0 x z =
      normalizedNormal T Q₀ F row col Φ Y initial 0 x z ∧ Qσ.1 0 = Q₀.1 0 := by
  have hz' : parameter z ∈ parameterCube (2 * P.radius) := fun i ↦ (hz i).le
  have hx : (0 : Euclidean n) ∈ ball 0 T.physicalRadius := mem_ball_self T.physicalRadius_pos
  have h0U : (0 : Euclidean n) ∈ U :=
    (carrierPhase_gradient_mem_domain (T.currentChart Q₀) T.reference.spatialPatch
      (T.target_contains_closed hx hz')).1
  have hgrad := current_carrierGradient_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled hx hz'
  have hnull := current_carrierNullvector_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ1 hscaled col hx hz'
  simp only [smul_zero] at hgrad hnull
  refine ⟨normalized_zero_transport_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical
    hseed htrans hσ hσ1 hscaled (T.target_contains_closed hx hz'), ?_, ?_, ?_⟩
  · simpa only [normalizedCovector_zero] using
      seedCovector_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical
        hseed htrans hσ hσ1 hscaled (ζ := T.reference.spatialPatch (parameter z))
          (T.target_contains_closed hx hz')
  · simp only [normalizedNormal_zero, normalField, carrierScalarAmplitude_origin,
      hgrad, hnull]
  · rw [hscaled, hseed]
    simpa only [smul_zero] using
      funext (ProjectedStressFrame.projectedStress_sourceDilation hσ hF 0
        (by simpa only [smul_zero] using hrank 0 h0U))

/-- The literal frozen kernel and both integral actions agree under source-frame
replacement on the original supported labels. Neither the immersion nor the
scalar is rescaled. Consumer: identify the unit realization used by the frozen
gap with the original seed carrier by its dense-test actions
(`app:ch_background:defn:bg-row`, `app:ch_background:prop:bg-adjoint`). -/
theorem normalized_zero_kernel_and_integrals_eq_of_source_frame
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hangular : ∀ z η, angular z η ≠ 0 → parameter z ∈ parameterInterior (2 * P.radius)) :
    let eσ := normalizedCarrierData T Qσ F row col Φ Y initial hr hcell angular high 0
    let e₀ := normalizedCarrierData T Q₀ F row col Φ Y initial hr hcell angular high 0
    carrierKernel eσ = carrierKernel e₀ ∧
    carrierTestIntegral eσ = carrierTestIntegral e₀ ∧
    carrierAdjointIntegral eσ = carrierAdjointIntegral e₀ := by
  intro eσ e₀
  have hkernel : carrierKernel eσ = carrierKernel e₀ := by
    funext x u
    by_cases hx : x ∈ PeriodicLocalL2.torusChart (closedBall (0 : Euclidean n) (4 * r))
    · by_cases ha : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
      · simp [eσ, e₀, carrierKernel, normalizedCarrierData, data, hx,
          carrierAmplitude, ha]
      obtain ⟨ht, hg, hn, hq⟩ := normalized_zero_carrier_fields_eq_of_source_frame
        T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled row col Φ Y initial
        (AmplitudeBound.centeredTorusRepresentative x) (hangular _ _ ha)
      simp only [eσ, e₀, carrierKernel, normalizedCarrierData, data, hx,
        indicator_of_mem, carrierPhase, carrierAmplitude, reducedCovector,
        zero_smul, ht, hg, hn, hq]
    · simp [eσ, e₀, carrierKernel, normalizedCarrierData, data, hx]
  refine ⟨hkernel, ?_, ?_⟩
  · funext f x
    simp only [carrierTestIntegral, hkernel]
  · funext w u
    simp only [carrierAdjointIntegral, hkernel]


/-- Transfer the entire frozen spectator density, complex amplitude and reflected
amplitude to the admitted source frame. The canonical inverse and Jacobian are
identified on their original domain; both positions, the scalar, measurement
and spectator measure remain fixed. Consumer: construct `UnitCarrierOutput`
for the original seed on the selected source geometry
(`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_background:eq:bg-real-symbol`, `app:ch_background:prop:bg-frame`). -/
theorem normalized_zero_fullAmplitudes_eq_of_source_frame
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hgeometry : RetainedSpectralGeometry T Qσ zRoot ηb r a)
    {rMask : ℝ} (hrMask : 0 < rMask) (hcell : 4 * rMask < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (measurement : Euclidean n → ℝ) (S : Set (Euclidean 2)) :
    let eσ := normalizedCarrierData T Qσ F row col Φ Y initial hrMask hcell angular high 0
    let e₀ := normalizedCarrierData T Q₀ F row col Φ Y initial hrMask hcell angular high 0
    let dσ := coefficientsOfCarrier eσ measurement
    let d₀ := coefficientsOfCarrier e₀ measurement
    let Jσ := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Qσ 0)
    let J₀ := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q₀ 0)
    let uσ := frozenSymbolInverse T Qσ zRoot ηb r (6 * a)
    let u₀ := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    let Ωσ := frozenSymbolDomain T Qσ zRoot ηb r (6 * a)
    let Ω₀ := frozenSymbolDomain T Q₀ zRoot ηb r (6 * a)
    extendedDensity dσ Jσ uσ Ωσ = extendedDensity d₀ J₀ u₀ Ω₀ ∧
      fullComplexMatrixAmplitude dσ Jσ uσ Ωσ S = fullComplexMatrixAmplitude d₀ J₀ u₀ Ω₀ S ∧
      fullReflectedMatrixAmplitude dσ Jσ uσ Ωσ S = fullReflectedMatrixAmplitude d₀ J₀ u₀ Ω₀ S := by
  intro eσ e₀ dσ d₀ Jσ J₀ uσ u₀ Ωσ Ω₀
  have hu : uσ = u₀ := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical
    hseed htrans hσ hσ1 hscaled hP hηb hr hgeometry
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, _hcJ, _hVi, _hLi, _hf, hInv, hcone, _hslice⟩ := hgeometry
  have hΩ : Ωσ = Ω₀ := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical
    hseed htrans hσ hσ1 hscaled hP hr har hcarrier
  have hJ := (source_frozen_transport_geometry_eq T Q₀ Qσ hF hrank hphysical
    hseed htrans hσ hσ1 hscaled hP (ηb := ηb) hr har hcarrier).2.2
  have hext : extendedDensity dσ Jσ uσ Ωσ = extendedDensity d₀ J₀ u₀ Ω₀ := by
    funext p
    by_cases hp : p ∈ Ωσ
    · have hinput := frozenSymbolInverse_maps T Qσ hηb hr hInv hcone hp
      have hz : parameter (inverseCoordinates uσ p).2.1 ∈ parameterInterior (2 * P.radius) :=
        fun j ↦ (carrierInterior_of_frozenInputDomain hr har hcarrier hinput j).trans (by linarith [hP.1])
      obtain ⟨_, hgx, hnx, hq⟩ := normalized_zero_carrier_fields_eq_of_source_frame
        T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled row col Φ Y initial p.1.1 hz
      obtain ⟨_, hgy, hny, _⟩ := normalized_zero_carrier_fields_eq_of_source_frame
        T Q₀ Qσ hF hrank hphysical hseed htrans hσ hσ1 hscaled row col Φ Y initial p.1.2.1 hz
      have hj := hJ hinput
      change Jσ (inverseCoordinates uσ p) = J₀ (inverseCoordinates uσ p) at hj
      rw [← hΩ, ← hu]
      simp only [extendedDensity, indicator_of_mem hp, inputDensity, inputWeight,
        dσ, d₀, coefficientsOfCarrier, eσ, e₀, normalizedCarrierData, data,
        reducedCovector, zero_smul, hj]
      simp only [inverseCoordinates] at hgx hgy hnx hny
      simp only [inverseCoordinates, hgx, hgy, hnx, hny, hq]
    · rw [← hΩ]
      simp only [extendedDensity, indicator_of_notMem hp]
  have hamp : amplitude dσ Jσ uσ Ωσ S = amplitude d₀ J₀ u₀ Ω₀ S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hext (p, z)))
  refine ⟨hext, ?_, ?_⟩
  · funext ξ z i j
    simp only [fullComplexMatrixAmplitude, hamp]
  · funext ξ z i j
    simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]

end JanetCartan.ContinuumRow.NormalizedSelection
