module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.RetainedSourceGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Realization.KernelGeometry

/-!
# The canonical frozen inverse on the selected common cone

The original retained spectral geometry gives all global zero-scale inputs
for the normalized source comparison. The normalized inverse range and mask
image come from the same finite incidence choice. The two physical positions,
scalar domains and masks remain unchanged.
-/

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic NormalizedSelection FrozenModel RetainedFrozen
open ContinuumNormalReduction.TransportSymbol
open CarrierVariation.FamilyInputs CarrierVariation.FamilyInputs.RetainedRowGeometry

/-- The SAME frozen canonical inverse satisfies the global geometry required
by the normalized full-amplitude comparison. The actual Jacobian is smooth,
strictly positive and homogeneous on the original radial input buffer; its
measurable kernel extension agrees there. The full transported mask closure
and its normalized shell stay in the supplied targets. Consumer: the zero
branch of `exists_source_reflectedPdo_control_nonneg`, alongside the positive
branch from `retained_source_canonical_comparison_geometry`. This makes no
identification between the divided ODE label and the origin-frozen density
(`app:ch_background:eq:bg-Psi`, `bg-jacobian`, `bg-full-complex-amplitude`). -/
theorem retained_frozen_canonical_comparison_geometry
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {zRoot : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hgeometry : RetainedSpectralGeometry T Q₀ zRoot ηb r a)
    {W Zmask : Set (InputVariables n)} {Qc Ω : Set (Variables n × Euclidean 2)}
    (hWinput : W ⊆ symbolInputDomain zRoot ηb r (6 * a))
    (hQc : IsCompact Qc) (hQcΩ : Qc ⊆ Ω)
    (hΩinput : Ω ⊆ frozenSymbolDomain T Q₀ zRoot ηb r (6 * a))
    (hne : ∀ q ∈ Ω, q.1.2.2 ≠ 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω)
    (hnormalized : MapsTo (fun q ↦ inverseCoordinates (frozenSymbolInverse T Q₀ zRoot ηb r (6 * a))
      (normalizeOutputRadius b q)) Ω W)
    (hmask : ∀ p ∈ Zmask, normalizeOutputRadius b
      (augmentedTransportGradient (normalizedTransportPosition T Q₀ 0) p) ∈ Qc) :
    let Z := normalizedTransportPosition T Q₀ 0
    let J := transportAbsoluteJacobian (adaptedSliceCoordinates T) Z
    let u := frozenSymbolInverse T Q₀ zRoot ηb r (6 * a)
    ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Ω (radialInputDomain W) ∧
    (∀ q ∈ Ω, transportAveragedGradient Z (inverseCoordinates u q) = q.1.2.2) ∧
    ContDiffOn ℝ ∞ J (radialInputDomain W) ∧
    (∀ p ∈ radialInputDomain W, 0 < J p) ∧
    EqOn (frozenKernelJacobian T Q₀) J (radialInputDomain W) ∧
    (∀ q ∈ Ω, ‖(u q).2‖ ≤ 2 * ‖q.1.2.2‖) ∧
    (∀ t : ℝ, 0 < t → ∀ q,
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
    (∀ t : ℝ, 0 < t → ∀ q ∈ Ω,
      J (scaleInput t (inverseCoordinates u q)) = t * J (inverseCoordinates u q)) ∧
    (closure (augmentedTransportGradient Z '' Zmask) ∩ {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
    ∀ q ∈ closure (augmentedTransportGradient Z '' Zmask), ‖q.1.2.2‖ = b → q ∈ Qc := by
  intro Z J u
  obtain ⟨har, hcarrier, G, β, cJ, V₀, L₀, hcJ, _, hLV, hf, hInv, htransverse, _⟩ := hgeometry
  have hradial : radialInputDomain W ⊆ frozenInputDomain zRoot ηb r (6 * a) := by
    intro p hp
    have hinput := radialInputDomain_subset_symbolInputDomain hWinput hp
    exact ⟨⟨hinput.1.1, mem_ball_self (by positivity), mem_ball_self (by positivity)⟩, hinput.2⟩
  have huScale (t : ℝ) (ht : 0 < t) (q : Variables n × Euclidean 2) :
      u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2) :=
    symbolInverse_scale_all T Q₀ hηb hr hInv htransverse t ht (originOutput q)
  have huRadial := inverseCoordinates_mapsTo_radialInputDomain_of_normalized_range hb hne
    hnormalized (fun t ht q _ ↦ huScale t ht q)
  have huInput := (frozenSymbolInverse_maps T Q₀ hηb hr hInv htransverse).mono_left hΩinput
  obtain ⟨hpunctured, hshell⟩ :=
    transport_mask_closure_geometry_of_normalized_image hb hQc hQcΩ hcone hmask
  exact ⟨(frozenSymbolInverse_smooth T Q₀ hηb hr hInv htransverse hLV).mono hΩinput,
    huRadial,
    fun q hq ↦ frozenTransportGradient_inverse T Q₀ hP hηb hr har hcarrier hInv htransverse (hΩinput hq),
    (frozenJacobian_smooth T Q₀ hP hηb hr har hcarrier hInv htransverse hf hcJ).mono hradial,
    fun p hp ↦ frozenJacobian_pos T Q₀ hP hηb hr har hcarrier hInv htransverse hf hcJ (hradial hp),
    fun p hp ↦ frozenKernelJacobian_eq_actual T Q₀ hP hηb hr har hcarrier hf (hradial hp),
    fun q hq ↦ frozenSymbolInverse_norm_le_two T Q₀ hηb hr hInv htransverse (hΩinput hq),
    huScale,
    fun t ht q hq ↦ frozenJacobian_scaling T Q₀ hP hηb hr har hcarrier hf hInv htransverse (huInput hq) ht,
    hpunctured, hshell⟩

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
