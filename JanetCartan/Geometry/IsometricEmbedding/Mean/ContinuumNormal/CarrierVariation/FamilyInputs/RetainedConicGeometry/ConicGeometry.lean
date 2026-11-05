module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.MaskBuffers

/-!
# Common retained geometry on the whole punctured cone

Extend the constructed local inverses homogeneously after fixing smaller
original masks. All domains, masks and tolerances precede the varying
transport. The compact target is a radial section, whereas the open target
contains the punctured closure of the complete uncut support.

Consumers: `exists_retained_conic_primitives_sub_tolerance`,
`exists_retained_conic_densityPair_comparison`, and the retained weighted
assembly. Sources: `app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian`, `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison

/-- Fixed conic domains and original uncut masks for all small primitive
perturbations of the SAME retained reference. The reference central half-gap
is renormalized before masks are chosen. The actual immersion comparison
supplies the `C²` premise; this theorem does not assume inverse continuity,
a varying image, or finite support of the uncut cone (`bg-Psi`, `bg-jacobian`). -/
theorem exists_retained_common_conic_geometry {n : ℕ}
    (D : PrimitiveNormChart (Euclidean n × ContinuumRow.CarrierParameter))
    {z₀ : Euclidean 3} (hcenter : D.center = (0, (z₀ 0, spectatorCenter z₀)))
    {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {H : Set (InputVariables n)} (hH : IsOpen H)
    (hpH : (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ∈ H)
    {Y₀ : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1)}
    (hY₀ : ContDiffOn ℝ ∞ Y₀ D.region)
    (A₀ : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hgap₀ : ‖A₀.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient Y₀) ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2)
    (hne : transportAveragedGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ≠ 0)
    (slice : TransportSliceCoordinates n)
    {rmax amax : ℝ} (hrmax : 0 < rmax) (hamax : 0 < amax) :
    let b := ‖transportAveragedGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)‖
    ∃ E : CoefficientNormCharts n, E.field = D ∧
    ∃ Ki W Bi : Set (InputVariables n),
      IsCompact Ki ∧ Convex ℝ Ki ∧ IsOpen W ∧ Ki ⊆ W ∧ IsCompact Bi ∧ W ⊆ Bi ∧ Bi ⊆ H ∧
      (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ∈ interior Ki ∧
      (∀ p ∈ W, ‖ηb‖ / 2 < ‖p.2.2‖) ∧ (∀ p ∈ Ki, E.Contains p) ∧
      (∀ side, MapsTo (WideDensity.densityEndpoint side) W E.field.carrier) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W E.field.carrier) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, MapsTo (transportSegmentInput n t) W E.field.region) ∧
    ∃ A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2,
    ∃ Q Ω : Set (Variables n × Euclidean 2), IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧ (∀ q ∈ Ω, q.1.2.2 ≠ 0) ∧
      augmentedTransportGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = b) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ a > (0 : ℝ), a ≤ amax ∧ a ≤ r ∧
    ∃ gap > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ Y : Euclidean n × ContinuumRow.CarrierParameter → Euclidean (n - 1),
        ContDiffOn ℝ ∞ Y E.field.region → cNorm E.field.carrier 2 (Y - Y₀) < δ →
      ∃ u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
        ContDiffOn ℝ ∞ u Ω ∧ MapsTo (inverseCoordinates u) Q Ki ∧
        MapsTo (fun q ↦ inverseCoordinates u (normalizeOutputRadius b q)) Ω Ki ∧
        (∀ q ∈ Ω, transportAveragedGradient Y (inverseCoordinates u q) = q.1.2.2) ∧
        (∀ p ∈ Ki, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient Y) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ Bi, gap ≤ transportAbsoluteJacobian slice Y p) ∧
        ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice Y) W ∧
        InjOn (augmentedTransportGradient Y) Ki ∧
        (∀ t : ℝ, 0 < t → ∀ q, u (scaleFrequency t q.1, q.2) = ((u q).1, t • (u q).2)) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ Ki ∧ transportAveragedGradient Y p ≠ 0 ∧
          normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q ∧
          scaleInput (b / ‖transportAveragedGradient Y p‖) p ∈ Ki ∧
          inverseCoordinates u (augmentedTransportGradient Y p) = p) ∧
        (closure (augmentedTransportGradient Y '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
        (∀ (v : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)) (q),
          q ∈ Q → inverseCoordinates v q ∈ Ki →
          transportAveragedGradient Y (inverseCoordinates v q) = q.1.2.2 → u q = v q) := by
  dsimp only
  let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  let b := ‖transportAveragedGradient Y₀ p₀‖
  have hb : 0 < b := norm_pos_iff.mpr hne
  obtain ⟨E, hED, Ki, W, Bi, hKi, hconv, hW, hKiW, hBi, hWBi, hBiH, hpKi,
    hfreq, hcontains, hend, hseg, hsegT, A, Q, Ω, hQ, hΩ, hQΩ, hpQ, gap, hgap,
    δ₀, hδ₀, hinv⟩ := exists_retained_local_geometry D hcenter hηb hH hpH hY₀ A₀ hgap₀ slice
  have hIIt : Icc (0 : ℝ) 1 ⊆ Ioo (-1 : ℝ) 2 :=
    fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hY₀E : ContDiffOn ℝ ∞ Y₀ E.field.region := hED ▸ hY₀
  obtain ⟨r, hr, hrr, a, ha, haa, har, δM, hδM, hmask⟩ :=
    exists_retained_normalized_mask_buffer hηb hKi hW hKiW hBi hWBi hpKi
      E.field.isOpen_region (isCompact_closedBall E.field.center E.field.radius)
      E.field.ball_subset isOpen_Ioo hIIt hsegT hseg hY₀E A hpQ hne hrmax hamax
  let Q' := Q ∩ {q : Variables n × Euclidean 2 | ‖q.1.2.2‖ = b}
  have hQ'Ω : Q' ⊆ normalizedConicTarget b Ω := by
    intro q hq
    refine ⟨norm_pos_iff.mp (hq.2 ▸ hb), ?_⟩
    rw [normalizeOutputRadius_eq_self hb hq.2]
    exact hQΩ hq.1
  refine ⟨E, hED, Ki, W, Bi, hKi, hconv, hW, hKiW, hBi, hWBi, hBiH, hpKi,
    hfreq, hcontains, hend, hseg, hsegT, A, Q', normalizedConicTarget b Ω,
    hQ.inter_right (isClosed_eq continuous_fst.snd.snd.norm continuous_const),
    normalizedConicTarget_isOpen _ hΩ, hQ'Ω, fun _ hq ↦ hq.1, ⟨interior_subset hpQ, rfl⟩,
    fun _ hq ↦ hq.2, fun t ht q ↦ normalizedConicTarget_smul_iff _ _ q ht,
    r, hr, hrr, a, ha, haa, har, gap, hgap, min δ₀ δM, lt_min hδ₀ hδM, ?_⟩
  intro Y hY hsmall
  obtain ⟨u, hu, hrangeΩ, hrange, heq, hdiff, hJac, hJs, hinj, huniq⟩ :=
    hinv Y hY (hsmall.trans_le (min_le_left _ _))
  have hm := hmask Y hY (hsmall.trans_le (min_le_right _ _))
  refine ⟨radialExtensionInverse b u, radialExtensionInverse_smooth b hΩ hu, ?_, ?_,
    fun _ hq ↦ radialExtensionInverse_right_inverse hb heq hq,
    hdiff, hJac, hJs, hinj, fun t ht q ↦ radialExtensionInverse_smul b u q ht, ?_,
    normalized_mask_image_punctured_buffer hQ.isClosed hQΩ (fun p hp ↦ (hm p hp).2.2.1), ?_⟩
  · intro q hq
    have hh : radialExtensionInverse b u q = u q := radialExtensionInverse_eq_on_sphere hb u hq.2
    simpa only [inverseCoordinates, hh] using hrange hq.1
  · intro q hq
    have hnormq : ‖(normalizeOutputRadius b q).1.2.2‖ = b := by
      change ‖(b / ‖q.1.2.2‖) • q.1.2.2‖ = b
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hb (norm_pos_iff.mpr hq.1)),
        div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hq.1)]
    have hh := radialExtensionInverse_eq_on_sphere hb u hnormq
    change inverseCoordinates (radialExtensionInverse b u) (normalizeOutputRadius b q) ∈ Ki
    simpa only [inverseCoordinates, hh] using interior_subset (hrangeΩ hq.2)
  · intro p hp
    obtain ⟨hi, hn, ho, hscaled⟩ := hm p hp
    refine ⟨hi, hn, ⟨ho, ?_⟩, hscaled,
      radialExtensionInverse_left_inverse hb hinj hrange hQΩ heq hn ho hscaled⟩
    change ‖(b / ‖transportAveragedGradient Y p‖) • transportAveragedGradient Y p‖ = b
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hb (norm_pos_iff.mpr hn)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hn)]
  · intro v q hq hv he
    rw [radialExtensionInverse_eq_on_sphere hb u hq.2]
    exact huniq v q (hQΩ hq.1) hv he

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
