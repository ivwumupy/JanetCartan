module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.RadialInputGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.MaskBuffers
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.SourceCompatibility

/-!
# Simultaneous common conic geometry for normalized source selection

Construct one local inverse and extend it in frequency together with its
input domain. The masks are chosen against that same target before source
scale. The full punctured support and compact shell, literal Jacobian, and
original inverse equations supply the normalized normal-limit consumer.
-/

open Set Metric Filter
open scoped ContDiff Topology
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace JanetCartan.ContinuumRow.NormalizedSelection
open ContinuumNormalReduction.TransportSymbol
open ContinuumNormal.CarrierVariation.FamilyInputs
open CanonicalConic FullPhaseCharts.ActualComparison

/-- Construct one common conic inverse, its full open input domain and all
original masks from the source forward map. The seed differential supplies
the inverse and literal Jacobian gaps. Radial extension proves the entire
uncut inverse range and Jacobian scaling. The same compact output section
contains the full supported shell for every sufficiently small scale.
Consumer: `NormalizedNormalLimit.exists_source_family_half_gap`, specifically
its `hfamily` and `hglobal` inputs (`app:ch_background:eq:bg-Psi`,
`app:ch_background:eq:bg-jacobian`, `bg-full-complex-amplitude`). -/
theorem exists_source_conic_geometry_with_radial_input
    {n : ℕ} (hn : 0 < n)
    (slice : TransportSliceCoordinates n)
    {Y : ℝ → Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {I : Set ℝ} {O : Set (InputVariables n)}
    (hI : IsOpen I) (hO : IsOpen O) (h0 : (0 : ℝ) ∈ I)
    (hp₀ : (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ∈ O)
    (hfreq : ∀ p ∈ O, p.2.2 ≠ 0 ∧ ‖p.2.2‖ ≤ 1)
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (I ×ˢ O))
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    (hA : fderiv ℝ (augmentedTransportGradient (Y 0))
      (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) = A.toContinuousLinearMap)
    {rmax amax : ℝ} (hrmax : 0 < rmax) (hamax : 0 < amax) :
    let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
    let b := ‖transportAveragedGradient (Y 0) p₀‖
    0 < b ∧
    ∃ K W : Set (InputVariables n),
      IsCompact K ∧ Convex ℝ K ∧ IsOpen W ∧ K ⊆ W ∧
      K ⊆ O ∧ W ⊆ radialInputDomain O ∧ p₀ ∈ interior K ∧
      (∀ p ∈ W, p.2.2 ≠ 0) ∧
      (∀ t : ℝ, 0 < t → ∀ p, scaleInput t p ∈ W ↔ p ∈ W) ∧
    ∃ Q Ω : Set (Variables n × Euclidean 2),
      IsCompact Q ∧ IsOpen Ω ∧ Q ⊆ Ω ∧
      augmentedTransportGradient (Y 0) p₀ ∈ Q ∧
      (∀ q ∈ Q, ‖q.1.2.2‖ = b) ∧
      (∀ t : ℝ, 0 < t → ∀ q, (scaleFrequency t q.1, q.2) ∈ Ω ↔ q ∈ Ω) ∧
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ a > (0 : ℝ), a ≤ amax ∧ a ≤ r ∧ 4 * a < 1 / 2 ∧
    ∃ e > (0 : ℝ), Ioo (-e) e ⊆ I ∧ ∃ gap > (0 : ℝ),
    ∃ u : ℝ → Variables n × Euclidean 2 → ℝ × Euclidean (n - 1),
      ContDiffOn ℝ ∞ (fun q : ℝ × InputVariables n ↦
        augmentedTransportGradient (Y q.1) q.2) (Ioo (-e) e ×ˢ W) ∧
      ∀ σ ∈ Ioo (-e) e,
        ContDiffOn ℝ ∞ (u σ) Ω ∧ MapsTo (inverseCoordinates (u σ)) Q K ∧
        MapsTo (inverseCoordinates (u σ)) Ω W ∧
        (∀ q ∈ Ω, transportAveragedGradient (Y σ) (inverseCoordinates (u σ) q) = q.1.2.2) ∧
        (∀ p ∈ K, ‖A.symm.toContinuousLinearMap.comp
          (fderiv ℝ (augmentedTransportGradient (Y σ)) p) -
            ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2) ∧
        (∀ p ∈ K, gap ≤ transportAbsoluteJacobian slice (Y σ) p) ∧
        ContDiffOn ℝ ∞ (transportAbsoluteJacobian slice (Y σ)) W ∧
        (∀ p ∈ W, 0 < transportAbsoluteJacobian slice (Y σ) p) ∧
        (∀ p ∈ Ω, ‖(u σ p).2‖ ≤ b⁻¹ * ‖p.1.2.2‖) ∧
        (∀ t : ℝ, 0 < t → ∀ q,
          u σ (scaleFrequency t q.1, q.2) = ((u σ q).1, t • (u σ q).2)) ∧
        (∀ p ∈ W, ∀ t : ℝ, 0 < t →
          transportAbsoluteJacobian slice (Y σ) (scaleInput t p) =
            t * transportAbsoluteJacobian slice (Y σ) p) ∧
        (∀ p ∈ conicMaskSupport z₀ ηb r a,
          p ∈ W ∧ transportAveragedGradient (Y σ) p ≠ 0 ∧
          normalizeOutputRadius b (augmentedTransportGradient (Y σ) p) ∈ Q ∧
          inverseCoordinates (u σ) (augmentedTransportGradient (Y σ) p) = p) ∧
        (closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) ∩
          {q | q.1.2.2 ≠ 0} ⊆ Ω) ∧
        (∀ q ∈ closure (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a),
          ‖q.1.2.2‖ = b → q ∈ Q) := by
  intro p₀ b
  have hslice : ContDiffOn ℝ ∞ (augmentedTransportGradient (Y 0)) O :=
    hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hp ↦ ⟨h0, hp⟩)
  have hgap0 : ‖A.symm.toContinuousLinearMap.comp
      (fderiv ℝ (augmentedTransportGradient (Y 0)) p₀) -
        ContinuousLinearMap.id ℝ (InputVariables n)‖ ≤ 1 / 2 := by
    rw [hA]
    have heq : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ (InputVariables n) := by
      apply ContinuousLinearMap.ext
      intro p
      exact A.symm_apply_apply p
    rw [heq, sub_self, norm_zero]
    norm_num
  have hnonzero : transportAveragedGradient (Y 0) p₀ ≠ 0 :=
    retained_transport_nonzero_of_augmented_gap hηb
      ((hslice.contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)) A hgap0
  have hb : 0 < b := norm_pos_iff.mpr hnonzero
  obtain ⟨rJ, hrJ, _, eJ, heJ, _, gap, hgap, hJac⟩ :=
    exists_local_positive_transport_jacobian slice hI hO h0 hp₀ hf A hA
  let O' := O ∩ ball p₀ rJ
  let I' := I ∩ Ioo (-eJ) eJ
  have hO' : IsOpen O' := hO.inter isOpen_ball
  have hI' : IsOpen I' := hI.inter isOpen_Ioo
  have hpO' : p₀ ∈ O' := ⟨hp₀, mem_ball_self hrJ⟩
  have h0I' : (0 : ℝ) ∈ I' := ⟨h0, neg_neg_of_pos heJ, heJ⟩
  have hf' := hf.mono (prod_mono (show I' ⊆ I from inter_subset_left)
    (show O' ⊆ O from inter_subset_left))
  obtain ⟨ρ, hρ, hKO', e₀, he₀, heI', Q₀, Ω₀, hQ₀, hΩ₀, hQΩ, hcenter,
    cD, _, v, hjoint, hlocal⟩ :=
    exists_local_common_transport_inverse hI' hO' h0I' hpO' hf' A hA
  let K := closedBall p₀ ρ
  let W := radialInputDomain O'
  have hpK : p₀ ∈ interior K := mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds _ hρ)
  have hcont : ContinuousAt (fun q : ℝ × InputVariables n ↦
      augmentedTransportGradient (Y q.1) q.2) (0, p₀) :=
    hjoint.continuousOn.continuousAt ((isOpen_Ioo.prod hO').mem_nhds
      ⟨⟨neg_neg_of_pos he₀, he₀⟩, hpO'⟩)
  obtain ⟨rm, hrm, am, ham, _, em, hem, hmask₀⟩ :=
    exists_source_normalized_mask_buffer hηb hpK hcont hcenter hnonzero
  let r := min rm rmax
  let a := min am (min amax (min r (1 / 16)))
  have hr : 0 < r := lt_min hrm hrmax
  have ha : 0 < a := lt_min ham (lt_min hamax (lt_min hr (by norm_num)))
  have hrrm : r ≤ rm := min_le_left _ _
  have haam : a ≤ am := min_le_left _ _
  have haa : a ≤ amax := (min_le_right _ _).trans (min_le_left _ _)
  have har : a ≤ r := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hacell : 4 * a < 1 / 2 := by
    have ha16 : a ≤ 1 / 16 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
    linarith
  let Q := Q₀ ∩ {q : Variables n × Euclidean 2 | ‖q.1.2.2‖ = b}
  let Ω := normalizedConicTarget b Ω₀
  have hQ : IsCompact Q := hQ₀.inter_right
    (isClosed_eq continuous_fst.snd.snd.norm continuous_const)
  have hQΩ' : Q ⊆ Ω := by
    intro q hq
    refine ⟨norm_pos_iff.mp (hq.2 ▸ hb), ?_⟩
    rw [normalizeOutputRadius_eq_self hb hq.2]
    exact hQΩ hq.1
  have hWO : W ⊆ radialInputDomain O := by
    rintro p ⟨t, ht, hp⟩
    exact ⟨t, ht, hp.1⟩
  refine ⟨hb, K, W, isCompact_closedBall _ _, convex_closedBall _ _,
    isOpen_radialInputDomain hO', hKO'.trans (subset_radialInputDomain O'),
    hKO'.trans inter_subset_left, hWO, hpK,
    fun p hp ↦ frequency_ne_zero_on_radialInputDomain (fun q hq ↦ (hfreq q hq).1) p (hWO hp),
    fun t ht p ↦ scaleInput_mem_radialInputDomain_iff ht p,
    Q, Ω, hQ, normalizedConicTarget_isOpen b hΩ₀, hQΩ',
    ⟨interior_subset hcenter, rfl⟩, fun _ hq ↦ hq.2,
    fun t ht q ↦ normalizedConicTarget_smul_iff b Ω₀ q ht,
    r, hr, min_le_right _ _, a, ha, haa, har, hacell,
    min e₀ em, lt_min he₀ hem,
    fun σ hσ ↦ (heI' ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hσ.1,
      hσ.2.trans_le (min_le_left _ _)⟩).1, gap, hgap,
    fun σ ↦ radialExtensionInverse b (v σ), ?_, ?_⟩
  · exact (contDiffOn_augmentedTransport_radialInputDomain (Y := Y) isOpen_Ioo hO' hjoint).mono
      (prod_mono (fun σ hσ ↦ ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hσ.1,
        hσ.2.trans_le (min_le_left _ _)⟩) Subset.rfl)
  intro σ hσ
  have hσ₀ : σ ∈ Ioo (-e₀) e₀ :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hσ.1, hσ.2.trans_le (min_le_left _ _)⟩
  have hσm : σ ∈ Ioo (-em) em :=
    ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hσ.1, hσ.2.trans_le (min_le_right _ _)⟩
  obtain ⟨hforward, hv, hrangeOpen, hrange, hright, hhalf, _, hinj⟩ := hlocal σ hσ₀
  have hJacO' : ∀ p ∈ O', gap ≤ transportAbsoluteJacobian slice (Y σ) p :=
    fun p hp ↦ hJac σ (heI' hσ₀).2 p (ball_subset_closedBall hp.2)
  obtain ⟨hJpos, hJsmooth, hJscale⟩ := transportJacobian_radialInputDomain slice hn hO'
    hforward (fun p hp ↦ hgap.trans_le (hJacO' p hp))
  have hmask : ∀ p ∈ conicMaskSupport z₀ ηb r a,
      scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧ transportAveragedGradient (Y σ) p ≠ 0 ∧
      normalizeOutputRadius b (augmentedTransportGradient (Y σ) p) ∈ Q₀ ∧
      scaleInput (b / ‖transportAveragedGradient (Y σ) p‖) p ∈ K :=
    fun p hp ↦ hmask₀ σ hσm p (conicMaskSupport_mono z₀ ηb hrrm haam hp)
  have hmaskQ : ∀ p ∈ conicMaskSupport z₀ ηb r a,
      normalizeOutputRadius b (augmentedTransportGradient (Y σ) p) ∈ Q := by
    intro p hp
    refine ⟨(hmask p hp).2.2.1, ?_⟩
    change ‖(b / ‖transportAveragedGradient (Y σ) p‖) • transportAveragedGradient (Y σ) p‖ = b
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hb (norm_pos_iff.mpr (hmask p hp).2.1)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hmask p hp).2.1)]
  refine ⟨radialExtensionInverse_smooth b hΩ₀ hv, ?_,
    radialExtensionInverse_mapsTo_radialInputDomain hb (hrangeOpen.mono_right
      (ball_subset_closedBall.trans hKO')),
    fun q hq ↦ radialExtensionInverse_right_inverse hb hright hq,
    hhalf, fun p hp ↦ hJacO' p (hKO' hp), hJsmooth, hJpos, ?_,
    fun t ht q ↦ radialExtensionInverse_smul b (v σ) q ht, hJscale, ?_,
    normalized_mask_image_punctured_buffer hQ₀.isClosed hQΩ
      (fun p hp ↦ (hmask p hp).2.2.1), ?_⟩
  · intro q hq
    simpa only [inverseCoordinates, radialExtensionInverse_eq_on_sphere hb _ hq.2] using hrange hq.1
  · intro q hq
    have hm := (hfreq _ (hKO' (ball_subset_closedBall (hrangeOpen hq.2))).1).2
    change ‖(‖q.1.2.2‖ / b) • (v σ (normalizeOutputRadius b q)).2‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (norm_pos_iff.mpr hq.1) hb)]
    calc
      _ ≤ ‖q.1.2.2‖ / b * 1 := mul_le_mul_of_nonneg_left hm (div_nonneg (norm_nonneg _) hb.le)
      _ = b⁻¹ * ‖q.1.2.2‖ := by rw [mul_one, div_eq_mul_inv, mul_comm]
  · intro p hp
    obtain ⟨hinput, hne, houtput, hscaled⟩ := hmask p hp
    exact ⟨⟨‖ηb‖ / ‖p.2.2‖, div_pos (norm_pos_iff.mpr hηb)
      (norm_pos_iff.mpr hp.2.2.1), hKO' hinput⟩, hne, hmaskQ p hp,
      radialExtensionInverse_left_inverse hb hinj hrange hQΩ hright hne houtput hscaled⟩
  · intro q hq hnorm
    have hne : q.1.2.2 ≠ 0 := norm_pos_iff.mp (hnorm ▸ hb)
    have hmem := (normalizeOutputRadius_continuousAt b hne).continuousWithinAt.mem_closure hq
      (show MapsTo (normalizeOutputRadius b)
        (augmentedTransportGradient (Y σ) '' conicMaskSupport z₀ ηb r a) Q from by
          rintro _ ⟨p, hp, rfl⟩; exact hmaskQ p hp)
    rw [hQ.isClosed.closure_eq, normalizeOutputRadius_eq_self hb hnorm] at hmem
    exact hmem

end JanetCartan.ContinuumRow.NormalizedSelection
