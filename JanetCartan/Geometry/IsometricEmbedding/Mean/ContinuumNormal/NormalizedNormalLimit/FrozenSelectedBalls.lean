module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.NormalizedNormalLimit.FrozenSourceMatching
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.UnitRealization.Support
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedRowGeometry.CommonTarget

/-!
# Retain the selected balls under spatial freezing

The current shell contains all normalized original mask points. Splicing its
physical and frequency coordinates proves the frozen shell on the same ball,
without a new radius choice or a smaller detector. The current inverse range
then supplies the frozen range even when the supplied centers are not written
with zero physical coordinates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.NormalizedNormalLimit
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic FrozenModel RetainedFrozen NullTransport
open ContinuumNormalReduction TransportSymbol
open CarrierVariation.FamilyInputs.RetainedRowGeometry

/-- The selected current output ball and inverse range also serve its frozen
phase. The shell of the ENTIRE original mask forces the physical-position
bounds, so neither a centered-ball hypothesis nor a new mask-size inequality
is added. This closes the local-ball inputs of the genuine zero-density
realization on the supplied selection (`app:ch_background:eq:bg-Psi`,
`bg-full-complex-amplitude`, `app:ch_background:prop:bg-normalized`). -/
theorem retained_frozen_output_geometry_of_current
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a)
    (hgeometry : RetainedSpectralGeometry T Q z₀ ηb r a)
    {p₀ : InputVariables n} {q₀ : Variables n × Euclidean 2} {ρ τ ℓ : ℝ}
    (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Q z₀ ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Q) ''
        conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) :
    (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q z₀ ηb r (6 * a)) ∧
    MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
    ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q 0) ''
        conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ := by
  obtain ⟨har, hcarrier, G, β, cJ, Vi, Li, _hcJ, _hVi, _hLi, _hf, _hInv, htrans, _hslice⟩ := hgeometry
  have ha : 0 < a := ha'.trans_le haa
  have hmaskInput : conicMaskSupport z₀ ηb r' a' ⊆ symbolInputDomain z₀ ηb r (6 * a) :=
    (conicMaskSupport_mono z₀ ηb hrr haa).trans
      (conicMaskSupport_subset hηb hr ha (by linarith))
  have hnorm (p : InputVariables n) (hp : p ∈ conicMaskSupport z₀ ηb r' a') :
      normalizeOutputRadius ℓ (augmentedTransportGradient (transportPosition T Q) p) ∈
        closedBall q₀ τ :=
    (mask_image_mem_compactTarget hℓ q₀
      (fun p hp ↦ transportGradient_ne_zero T Q hηb hr htrans (hmaskInput hp)) hshell p hp).1
  let pz : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  have hpz : pz ∈ conicMaskSupport z₀ ηb r' a' := by
    refine ⟨⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩,
      ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩, hηb,
      mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize hηb), mem_closedBall_self ?_⟩
    exact div_nonneg (angularWidth_spec hηb hr').1.le (by norm_num)
  have hzeroPositions : dist (0 : Euclidean n) q₀.1.1 ≤ τ ∧
      dist (0 : Euclidean n) q₀.1.2.1 ≤ τ := by
    have hh := hnorm pz hpz
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hh
    exact ⟨hh.1.1, hh.1.2.1⟩
  have horigin {p : Variables n × Euclidean 2} (hp : p ∈ closedBall q₀ (2 * τ)) :
      originOutput p ∈ closedBall q₀ (2 * τ) := by
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hp ⊢
    exact ⟨⟨hzeroPositions.1.trans (by linarith),
      hzeroPositions.2.trans (by linarith), hp.1.2.2⟩, hp.2⟩
  refine ⟨fun _ hp ↦ houtput (horigin hp), ?_, ?_⟩
  · intro p hp
    have hi := hrange hp
    have hz := hrange (horigin hp)
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hi hz ⊢
    exact ⟨hi.1, hz.2⟩
  · apply supported_shell_of_normalized_image hℓ
    intro p hp
    have horg := originInput_mem_conicMaskSupport ha'.le hp
    have hi := hnorm p hp
    have hz := hnorm (originInput p) horg
    have hpFrozen : p ∈ frozenInputDomain z₀ ηb r (6 * a) := hmaskInput horg
    have he := frozenForward_eq_origin T Q hP hr har hcarrier hpFrozen
    simp only [mem_closedBall, Prod.dist_eq, max_le_iff] at hi hz ⊢
    exact ⟨⟨hi.1.1, hi.1.2.1, by simpa only [normalizeOutputRadius,
      augmentedTransportGradient, scaleFrequency, he] using hz.1.2.2⟩, hi.2⟩


/-- Transfer the SAME selected output ball, frozen inverse range and full
supported shell from one admitted positive source to the original seed.
The original masks and centers are unchanged. The phase and inverse equalities
come from Hamilton matching, including the canonical zero extension; no
spectral geometry of the unscaled seed is assumed. Consumer: local geometry
for `SourceDensityLimitRealization.exists_source_zero_density_limit_realization`
(`app:ch_background:prop:bg-normalized`, `bg-Nsigma`, `bg-Psi`). -/
theorem seed_frozen_output_geometry_of_source
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hscaled : Qσ.1 = ProjectedStressFrame.projectedStress
      (sourceDilation F σ))
    {c C : ℝ} (hP : P.IsValid c C)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a r' a' : ℝ}
    (hηb : ηb ≠ 0) (hr : 0 < r) (hr' : 0 < r') (ha' : 0 < a')
    (hrr : r' ≤ r) (haa : a' ≤ a)
    (hgeometry : RetainedSpectralGeometry T Qσ z₀ ηb r a)
    {p₀ : InputVariables n} {q₀ : Variables n × Euclidean 2} {ρ τ ℓ : ℝ}
    (hτ : 0 < τ) (hℓ : 0 < ℓ)
    (houtput : closedBall q₀ (2 * τ) ⊆ symbolDomain T Qσ z₀ ηb r (6 * a))
    (hrange : MapsTo (inverseCoordinates (symbolInverse T Qσ z₀ ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ))
    (hshell : ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (transportPosition T Qσ) ''
        conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ) :
    (closedBall q₀ (2 * τ) ⊆ frozenSymbolDomain T Q₀ z₀ ηb r (6 * a)) ∧
    MapsTo (inverseCoordinates (frozenSymbolInverse T Q₀ z₀ ηb r (6 * a)))
      (closedBall q₀ (2 * τ)) (closedBall p₀ ρ) ∧
    ∀ x : Variables n, ‖x.2.2‖ = ℓ → ∀ v : Euclidean 2,
      (x, v) ∈ closure (augmentedTransportGradient (normalizedTransportPosition T Q₀ 0) ''
        conicMaskSupport z₀ ηb r' a') → (x, v) ∈ closedBall q₀ τ := by
  obtain ⟨ho, hi, hs⟩ := retained_frozen_output_geometry_of_current T Qσ hP hηb hr hr' ha'
    hrr haa hgeometry hτ hℓ houtput hrange hshell
  have hd := frozenSymbolDomain_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr hgeometry.1 hgeometry.2.1
  have hu := frozenSymbolInverse_eq_of_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP hηb hr hgeometry
  have he := (source_frozen_transport_geometry_eq T Q₀ Qσ hF hrank hphysical hseed htrans
    hσ hσ1 hscaled hP (ηb := ηb) hr hgeometry.1 hgeometry.2.1).1
  have hm : conicMaskSupport z₀ ηb r' a' ⊆ frozenInputDomain z₀ ηb r (6 * a) := by
    intro p hp
    exact conicMaskSupport_subset hηb hr (ha'.trans_le haa) (by linarith only [hgeometry.1, ha'.trans_le haa])
      (conicMaskSupport_mono z₀ ηb hrr haa (originInput_mem_conicMaskSupport ha'.le hp))
  rw [hd] at ho
  rw [hu] at hi
  rw [(he.mono hm).image_eq] at hs
  exact ⟨ho, hi, hs⟩

end JanetCartan.ContinuumNormal.NormalizedNormalLimit
