module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.NormalWitnesses
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.PrimitiveRealization.Kernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RadialMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.CommonConicNormal

/-!
# The genuine zero-density limit on the supplied common radial cone

The common inverse is identified by the original frozen phase's left inverse
on its retained range. The entire transported mask is kept; both spatial
weights survive the exact change of inverse domain. Consumers: the zero and
frozen normal branches of `exists_initialized_source_family_coercivity` and
`exists_source_family_controlled_half_gap`. Sources: `bg-normalized`,
`bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`, and `bg-frame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel NormalizedSelection
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization ConicChart
open CarrierVariation

/-- Radial extension of the retained input buffer stays in the SAME frozen
cone. Only frequency changes (`bg-Psi`, `bg-full-complex-amplitude`). -/
theorem radialInputDomain_subset_frozenInputDomain
    {n : ℕ} {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {O : Set (InputVariables n)} (hO : O ⊆ frozenInputDomain zRoot ηb r a) :
    radialInputDomain O ⊆ frozenInputDomain zRoot ηb r a := by
  rintro p ⟨t, ht, hp⟩
  have hscaled := hO hp
  refine ⟨hscaled.1, ?_⟩
  have hback := radialScale_mem_supportedCone hscaled.2 (inv_pos.mpr ht)
  simpa only [radialScale, scaleInput, originInput, inv_smul_smul₀ ht.ne'] using hback

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (har : 6 * a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter zRoot) (3 * r) ×ˢ closedBall (zRoot 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {b cJ : ℝ} {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet zRoot (6 * a))
      (dataBox zRoot ηb r) (dataSet zRoot ηb (2 * r)) (dataBox zRoot ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet zRoot (6 * a),
      ∀ u ∈ supportedCone zRoot (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)

include hP hηb hr har hcarrier hInv htrans

/-- The supplied common inverse is the original frozen inverse on its
retained range. Its right-inverse equation also proves containment in the
original image; no equality of arbitrary inverse extensions is assumed
(`bg-Psi`, `bg-normalized`). The range is supplied by the radial comparison
constructor and `inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range`. -/
theorem frozenInverse_eq_on_common_radial_cone
    {Ωcommon : Set (Variables n × Euclidean 2)}
    {Oinput : Set (InputVariables n)}
    (hOinput : Oinput ⊆ frozenInputDomain zRoot ηb r (6 * a))
    (u₀ : Variables n × Euclidean 2 → SliceVariable n)
    (hrange : MapsTo (inverseCoordinates u₀) Ωcommon (radialInputDomain Oinput))
    (hright : ∀ p ∈ Ωcommon, transportAveragedGradient (normalizedTransportPosition T Q 0)
      (inverseCoordinates u₀ p) = p.1.2.2) :
    Ωcommon ⊆ frozenSymbolDomain T Q zRoot ηb r (6 * a) ∧
      EqOn u₀ (frozenSymbolInverse T Q zRoot ηb r (6 * a)) Ωcommon := by
  have hm : MapsTo (inverseCoordinates u₀) Ωcommon (frozenInputDomain zRoot ηb r (6 * a)) :=
    fun p hp ↦ radialInputDomain_subset_frozenInputDomain hOinput (hrange hp)
  have he : ∀ p ∈ Ωcommon, augmentedTransportGradient (normalizedTransportPosition T Q 0)
      (inverseCoordinates u₀ p) = p :=
    augmentedTransportGradient_inverseCoordinates _ _ hright
  constructor
  · intro p hp
    rw [frozenSymbolDomain_eq_image T Q hP hηb hr har hcarrier hInv htrans]
    exact ⟨inverseCoordinates u₀ p, hm hp, he p hp⟩
  · intro p hp
    have hleft := frozenInverse_augmentedGradient T Q hP hηb hr har hcarrier hInv htrans (hm hp)
    rw [he p hp] at hleft
    exact (congrArg (fun q : InputVariables n ↦ (q.2.1.1, q.2.2)) hleft).symm

/-- Exact transfer of a spatially weighted zero carrier's complete density
and reflected amplitude to the supplied common radial cone. The weight is
arbitrary, so the genuine divided-footpoint density and the distinct frozen
label are both covered without identifying them. The original Lebesgue
spectator, Fourier normalization and both measurement factors are unchanged
(`bg-Nsigma`, `bg-full-complex-amplitude`, `bg-real-symbol`). -/
theorem zero_weighted_fullAmplitudes_eq_common_cone
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {r' a' : ℝ} (hr' : 0 < r') (ha' : 0 < a') (hcell : 4 * a' < 1 / 2)
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r')
    {Ωcommon : Set (Variables n × Euclidean 2)}
    {Oinput : Set (InputVariables n)}
    (hOinput : Oinput ⊆ frozenInputDomain zRoot ηb r (6 * a))
    (u₀ : Variables n × Euclidean 2 → SliceVariable n)
    (hrange : MapsTo (inverseCoordinates u₀) Ωcommon (radialInputDomain Oinput))
    (hright : ∀ p ∈ Ωcommon, transportAveragedGradient (normalizedTransportPosition T Q 0)
      (inverseCoordinates u₀ p) = p.1.2.2)
    (hbuffer : closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport zRoot ηb r' a') ∩ {p | p.1.2.2 ≠ 0} ⊆ Ωcommon)
    (w : Euclidean n × CarrierParameter → ℝ) (S : Set (Euclidean 2)) :
    let e := normalizedCarrierData T Q F row col Φ Y (fun _ ↦ 1) ha' hcell
      (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
      FixedCutoffs.highFrequency 0
    let a₀ := coefficientsOfCarrier e (FixedCutoffs.physical ha' 1)
    let d := {a₀ with normal := fun p ↦ w p • a₀.normal p}
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) (normalizedTransportPosition T Q 0)
    let uf := frozenSymbolInverse T Q zRoot ηb r (6 * a)
    let Ωf := frozenSymbolDomain T Q zRoot ηb r (6 * a)
    extendedDensity d J uf Ωf = extendedDensity d J u₀ Ωcommon ∧
      fullComplexMatrixAmplitude d J uf Ωf S = fullComplexMatrixAmplitude d J u₀ Ωcommon S ∧
      fullReflectedMatrixAmplitude d J uf Ωf S = fullReflectedMatrixAmplitude d J u₀ Ωcommon S := by
  intro e a₀ d J uf Ωf
  obtain ⟨hsub, hinverse⟩ := frozenInverse_eq_on_common_radial_cone T Q hP hηb hr har
    hcarrier hInv htrans hOinput u₀ hrange hright
  have hinput : conicMaskSupport zRoot ηb r' a' ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hi := (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num))) hp
    have hz : (0 : Euclidean n) ∈ ball 0 (6 * a) := mem_ball_self (by linarith)
    exact ⟨⟨hi.1.1, hz, hz⟩, hi.2⟩
  have hbuffer' : augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
      conicMaskSupport zRoot ηb r' a' ⊆ Ωcommon := by
    rintro _ ⟨p, hp, rfl⟩
    refine hbuffer ⟨subset_closure ⟨p, hp, rfl⟩, ?_⟩
    change transportAveragedGradient (normalizedTransportPosition T Q 0) p ≠ 0
    rw [frozenForward_eq_origin T Q hP hr har hcarrier (hinput hp)]
    exact transportGradient_ne_zero T Q hηb hr htrans (hinput hp)
  have hext : extendedDensity d J uf Ωf = extendedDensity d J u₀ Ωcommon := by
    apply extendedDensity_common_conic_target d J J uf u₀
      (augmentedTransportGradient (normalizedTransportPosition T Q 0)) hsub
      (frozenSymbolInverse_maps T Q hηb hr hInv htrans)
      (augmentedFrozenGradient_inverse T Q hP hηb hr har hcarrier hInv htrans)
      _ hbuffer' hinverse.symm (fun _ _ ↦ rfl)
    intro p hp hx hy hang _
    exact primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy hang
  have hamp : amplitude d J uf Ωf S = amplitude d J u₀ Ωcommon S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hext (p, z)))
  refine ⟨hext, ?_, ?_⟩
  · funext ξ z i j
    simp only [fullComplexMatrixAmplitude, hamp]
  · funext ξ z i j
    simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
