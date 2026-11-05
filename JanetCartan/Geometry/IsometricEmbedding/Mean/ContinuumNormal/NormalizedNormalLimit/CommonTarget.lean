module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.ComplexAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.CommonTarget
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.RefinedKernel.Support

/-!
# Full supported amplitudes on a fixed comparison cone

The constructed carrier uses its actual conic image; the normalized comparison
uses one fixed target. Original mask support and the canonical inverse show
that these domains produce the same full amplitude, including the spectator
integral, physical Fourier normalization and reflected factor four.

Consumer: the same-row normal identities from
NormalizedSelection.exists_retained_chart_source_density_carrier and the
source-amplitude convergence theorem. No detector support is discarded.
Sources: app:ch_background:eq:bg-full-complex-amplitude, bg-Psi,
bg-real-symbol and app:ch_background:prop:bg-normalized.
-/

@[expose] public noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic RetainedFrozen
open ContinuumNormalReduction TransportSymbol TransportKernel CarrierNormalRealization
open CarrierVariation CarrierVariation.FamilyInputs.RetainedRowGeometry

/-- Restricting the inverse domain to a set containing the full transported
primitive support leaves its extended density unchanged. The support inclusion
is derived from the original masks and inverse equation; no transformed
amplitude equality is assumed (app:ch_background:eq:bg-full-complex-amplitude).
Consumer: the canonical common-target identity below. -/
private theorem extendedDensity_eq_on_supported_target
    {n N : ℕ} (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Fwd : InputVariables n → Variables n × Euclidean 2)
    {Ωcommon Ω : Set (Variables n × Euclidean 2)} {W Z : Set (InputVariables n)}
    (hsub : Ωcommon ⊆ Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, Fwd (inverseCoordinates u p) = p)
    (hmask : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ Z)
    (hfreq : ∀ p ∈ Ω, p.1.2.2 ≠ 0)
    (hbuffer : closure (Fwd '' Z) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ωcommon) :
    extendedDensity a J u Ωcommon = extendedDensity a J u Ω := by
  funext p
  by_cases hp : p ∈ Ωcommon
  · simp only [extendedDensity, indicator_of_mem hp, indicator_of_mem (hsub hp)]
  · have hzero : extendedDensity a J u Ω p = 0 := by
      by_contra hn
      have hpΩ : p ∈ Ω := by
        by_contra hm
        exact hn (by simp [extendedDensity, hm])
      exact hp (hbuffer ⟨subset_closure
        (support_extendedDensity_subset a J u Fwd hmap hright hmask hn), hfreq p hpΩ⟩)
    simpa only [extendedDensity, indicator_of_notMem hp] using hzero.symm

/-- The actual retained carrier has exactly the same extended density and
full complex/reflected amplitudes on the fixed common comparison cone as on
its original varying symbol domain. Its entire transported mask is retained,
by the original supported-shell geometry. The initial scalar is arbitrary,
so this covers the original sigma*sqrt(1+v) class with no density restriction.

Consumer: applying exists_source_fullAmplitude_sqrtFootpoints_tolerance to
the literal normals constructed by
NormalizedSelection.exists_retained_chart_source_density_carrier.
Sources: app:ch_background:eq:bg-full-complex-amplitude, bg-Psi,
bg-real-symbol and app:ch_background:prop:bg-normalized. -/
theorem canonical_fullAmplitudes_eq_on_common_target
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)}
    {r a r' a' : ℝ} (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a) (har' : a' ≤ r') (hcell : 4 * a' < 1 / 2)
    (hgeometry : RetainedSpectralGeometry T Q₀ zRoot ηb r a)
    {b τ : ℝ} (hb : 0 < b) (hτ : 0 < τ) (q₀ : Variables n × Euclidean 2)
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Q₀ zRoot ηb r (6 * a))
    (hshell : ∀ p : Variables n, ‖p.2.2‖ = b → ∀ z : Euclidean 2,
      (p, z) ∈ closure (augmentedTransportGradient (transportPosition T Q₀) ''
        conicMaskSupport zRoot ηb r' a') → (p, z) ∈ closedBall q₀ τ)
    (S : Set (Euclidean 2)) :
    let d := coefficientsOfCarrier
      (data T Q₀ F row col Φ Y initial ha' hcell
        (angularMask zRoot (NormedSpace.normalize ηb) ha' (angularWidth_spec hηb hr').1)
        FixedCutoffs.highFrequency) (FixedCutoffs.physical ha' 1)
    let J := symbolJacobian T Q₀
    let u := symbolInverse T Q₀ zRoot ηb r (6 * a)
    let Ω := symbolDomain T Q₀ zRoot ηb r (6 * a)
    let Ωcommon := conicTarget b q₀ τ
    extendedDensity d J u Ωcommon = extendedDensity d J u Ω ∧
      fullComplexMatrixAmplitude d J u Ωcommon S = fullComplexMatrixAmplitude d J u Ω S ∧
      fullReflectedMatrixAmplitude d J u Ωcommon S = fullReflectedMatrixAmplitude d J u Ω S := by
  intro d J u Ω Ωcommon
  obtain ⟨_, _, G, β, cJ, V, L, _, _, _, _, hInv, htrans, _⟩ := hgeometry
  have hinput : conicMaskSupport zRoot ηb r' a' ⊆ symbolInputDomain zRoot ηb r (6 * a) :=
    (conicMaskSupport_subset hηb hr' ha' har').trans
      (symbolInputDomain_mono zRoot ηb hrr (mul_le_mul_of_nonneg_left haa (by norm_num)))
  have hne : ∀ p ∈ conicMaskSupport zRoot ηb r' a',
      transportAveragedGradient (transportPosition T Q₀) p ≠ 0 :=
    fun p hp ↦ transportGradient_ne_zero T Q₀ hηb hr htrans (hinput hp)
  have hbuffer := mask_image_punctured_subset_conicTarget hb hτ q₀ hne hshell
  have hfreq : ∀ p ∈ Ω, p.1.2.2 ≠ 0 := by
    intro p hp hz
    have hn := supportedOutput_transverse_ne_zero T Q₀ hηb hr hInv htrans hp
    apply hn
    change ((adaptedSliceCoordinates T).equiv p.1.2.2).2 = 0
    rw [hz, map_zero]
    rfl
  have hd : extendedDensity d J u Ωcommon = extendedDensity d J u Ω := by
    apply extendedDensity_eq_on_supported_target d J u
      (augmentedTransportGradient (transportPosition T Q₀))
      (conicTarget_subset_symbolDomain T Q₀ hb houtput)
      (symbolInverse_maps T Q₀ hηb hr hInv htrans)
      (augmentedTransportGradient_symbolInverse T Q₀ hηb hr hInv htrans) _ hfreq hbuffer
    intro p hp hx hy ha _
    exact primitive_masks_mem_conicMaskSupport hηb hr' ha' hp.2.2.1 hx hy ha
  have hamp : amplitude d J u Ωcommon S = amplitude d J u Ω S := by
    funext p
    exact integral_congr_ae (Filter.Eventually.of_forall (fun z ↦ congrFun hd (p, z)))
  refine ⟨hd, ?_, ?_⟩
  · funext ξ z
    ext i j
    simp only [fullComplexMatrixAmplitude, hamp]
  · funext ξ z
    ext i j
    simp only [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, hamp]

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
