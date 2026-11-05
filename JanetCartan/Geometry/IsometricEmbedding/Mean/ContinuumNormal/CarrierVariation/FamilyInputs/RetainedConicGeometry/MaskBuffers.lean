module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedConicGeometry.LocalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.CommonCharts.MaskBuffers

/-!
# Fixed uncut masks for perturbations of the retained positive transport

Choose the original masks using continuity of the reference forward map and
then use the proved finite forward estimate to retain them for every small
primitive perturbation. Only radial representatives enter the compact input
and target sets; the uncut cone has no upper frequency bound.

Consumer: the common conic inverse construction for
`exists_retained_conic_primitives_sub_tolerance` and
`exists_retained_conic_densityPair_comparison`.
Sources: `app:ch_background:eq:bg-Psi`, `app:ch_background:eq:bg-jacobian`,
and `app:ch_osc:prop:osc-normal`, Step 4'.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow.CanonicalConic
open FullPhaseCharts.ActualComparison

/-- Common original masks from the retained reference and the actual `C²`
transport difference. The primitive difference is supplied by
`RetainedLeading.exists_originalScalar_immersion_sub_tolerance` at order zero.
This constructs both radial input buffers and the normalized output buffer;
no support or inverse continuity hypothesis is used (`bg-full-complex-amplitude`). -/
theorem exists_retained_normalized_mask_buffer {n : ℕ}
    {Y₀ : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1)}
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} (hηb : ηb ≠ 0)
    {K W B : Set (InputVariables n)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hB : IsCompact B) (hWB : W ⊆ B)
    (hpK : (((0, 0), (z₀ 0, spectatorCenter z₀), ηb) : InputVariables n) ∈ interior K)
    {V L : Set (Euclidean n × (ℝ × Euclidean 2))}
    (hV : IsOpen V) (hL : IsCompact L) (hLV : L ⊆ V)
    {It : Set ℝ} (hIt : IsOpen It) (hIIt : Icc (0 : ℝ) 1 ⊆ It)
    (hsegT : ∀ t ∈ It, MapsTo (transportSegmentInput n t) W V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (transportSegmentInput n t) W L)
    (hY₀ : ContDiffOn ℝ ∞ Y₀ V)
    (A : InputVariables n ≃L[ℝ] Variables n × Euclidean 2)
    {Q : Set (Variables n × Euclidean 2)}
    (hpQ : augmentedTransportGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ∈ interior Q)
    (hne : transportAveragedGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb) ≠ 0)
    {rmax amax : ℝ} (hrmax : 0 < rmax) (hamax : 0 < amax) :
    let b := ‖transportAveragedGradient Y₀ ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)‖
    ∃ r > (0 : ℝ), r ≤ rmax ∧ ∃ a > (0 : ℝ), a ≤ amax ∧ a ≤ r ∧
    ∃ δ > (0 : ℝ), ∀ Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1),
      ContDiffOn ℝ ∞ Y V → cNorm L 2 (Y - Y₀) < δ →
      ∀ p ∈ conicMaskSupport z₀ ηb r a,
        scaleInput (‖ηb‖ / ‖p.2.2‖) p ∈ K ∧
        transportAveragedGradient Y p ≠ 0 ∧
        normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q ∧
        scaleInput (b / ‖transportAveragedGradient Y p‖) p ∈ K := by
  dsimp only
  let p₀ : InputVariables n := ((0, 0), (z₀ 0, spectatorCenter z₀), ηb)
  let q₀ := augmentedTransportGradient Y₀ p₀
  let b := ‖q₀.1.2.2‖
  have hb : 0 < b := norm_pos_iff.mpr hne
  have hnorm : ContinuousAt (fun q : InputVariables n × (Variables n × Euclidean 2) ↦
      normalizeOutputRadius b q.2) (p₀, q₀) :=
    (normalizeOutputRadius_continuousAt b hne).comp continuousAt_snd
  have hnorm0 : normalizeOutputRadius b q₀ = q₀ := normalizeOutputRadius_eq_self hb rfl
  have htarget : ∀ᶠ q : InputVariables n × (Variables n × Euclidean 2) in 𝓝 (p₀, q₀),
      normalizeOutputRadius b q.2 ∈ Q := hnorm (by
    change Q ∈ 𝓝 (normalizeOutputRadius b q₀)
    rw [hnorm0]
    exact mem_interior_iff_mem_nhds.mp hpQ)
  have hnonzero : ∀ᶠ q : InputVariables n × (Variables n × Euclidean 2) in 𝓝 (p₀, q₀),
      q.2.1.2.2 ≠ 0 :=
    (isOpen_ne_fun continuous_snd.fst.snd.snd continuous_const).mem_nhds hne
  have hinput : ∀ᶠ q : InputVariables n × (Variables n × Euclidean 2) in 𝓝 (p₀, q₀),
      q.1 ∈ K := continuousAt_fst (mem_interior_iff_mem_nhds.mp hpK)
  have hscaled : ContinuousAt (fun q : InputVariables n × (Variables n × Euclidean 2) ↦
      scaleInput (b / ‖q.2.1.2.2‖) q.1) (p₀, q₀) :=
    continuousAt_fst.fst.prodMk (continuousAt_fst.snd.fst.prodMk
      ((continuousAt_const.div continuousAt_snd.fst.snd.snd.norm
        (norm_ne_zero_iff.mpr hne)).smul continuousAt_fst.snd.snd))
  have hscaled0 : scaleInput (b / ‖q₀.1.2.2‖) p₀ = p₀ := by
    simp only [show ‖q₀.1.2.2‖ = b from rfl, div_self hb.ne', scaleInput, one_smul]
  have hscaledK : ∀ᶠ q : InputVariables n × (Variables n × Euclidean 2) in 𝓝 (p₀, q₀),
      scaleInput (b / ‖q.2.1.2.2‖) q.1 ∈ K := hscaled (by
    change K ∈ 𝓝 (scaleInput (b / ‖q₀.1.2.2‖) p₀)
    rw [hscaled0]
    exact mem_interior_iff_mem_nhds.mp hpK)
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff_ball.mp
    (hinput.and (hnonzero.and (htarget.and hscaledK)))
  have hf₀ := augmentedTransportGradient_contDiffOn hW hV hIt hIIt hsegT hY₀
  have hforward₀ : ∀ᶠ p in 𝓝 p₀, dist (augmentedTransportGradient Y₀ p) q₀ < d / 2 :=
    (hf₀.continuousOn.continuousAt (hW.mem_nhds (hKW (interior_subset hpK))))
      (ball_mem_nhds q₀ (half_pos hd))
  obtain ⟨e, he, heforward⟩ := Metric.eventually_nhds_iff_ball.mp hforward₀
  obtain ⟨r, hr, hrr, hrd, a, ha, haa, har, had⟩ :=
    exists_refined_mask_radii hrmax hamax (lt_min hd he)
  obtain ⟨C, hC, hforward⟩ := exists_transportForward_sub_le
    hKW hW hB hWB hV hL hLV hIt hIIt hsegT hseg A 0
  refine ⟨r, hr, hrr, a, ha, haa, har, (d / 2) / C,
    div_pos (half_pos hd) hC, ?_⟩
  intro Y hY hsmall p hp
  let t := ‖ηb‖ / ‖p.2.2‖
  let p' := scaleInput t p
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hηb) (norm_pos_iff.mpr hp.2.2.1)
  have hp' : p' ∈ ball p₀ (min d e) :=
    conicMaskSupport_radial_section_mem_ball hηb hr ha had hrd hp
  have hp'd : p' ∈ ball p₀ d := ball_subset_ball (min_le_left _ _) hp'
  have hp'e : p' ∈ ball p₀ e := ball_subset_ball (min_le_right _ _) hp'
  have hp'K : p' ∈ K := (hnear (p', q₀) (by
    rw [mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
    exact ⟨hp'd, hd⟩)).1
  have hfs := augmentedTransportGradient_contDiffOn hW hV hIt hIIt hsegT hY
  have hjet := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 0) hK
    (fun q hq ↦ ((hfs.sub hf₀).contDiffAt (hW.mem_nhds (hKW hq))).of_le (by simp))
    hp'K (le_refl 0)
  rw [norm_iteratedFDeriv_zero] at hjet
  have hclose : dist (augmentedTransportGradient Y p') (augmentedTransportGradient Y₀ p') < d / 2 := by
    rw [dist_eq_norm]
    exact hjet.trans_lt (((hforward Y Y₀ hY hY₀).2.1).trans_lt (by
      have hh := (lt_div_iff₀ hC).mp hsmall
      exact (mul_le_mul_of_nonneg_left (cNorm_mono_order (by omega : 0 + 1 ≤ 2)) hC.le).trans_lt
        (by simpa only [mul_comm] using hh)))
  have hh := hnear (p', augmentedTransportGradient Y p') (by
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨hp'd, (dist_triangle _ _ _).trans_lt (by linarith [heforward p' hp'e])⟩)
  refine ⟨hh.1, ?_, ?_, ?_⟩
  · intro hz
    exact hh.2.1 (by
      change transportAveragedGradient Y (scaleInput t p) = 0
      rw [transportAveragedGradient_smul, hz, smul_zero])
  · change normalizeOutputRadius b (augmentedTransportGradient Y p) ∈ Q
    simpa only [p', augmentedTransportGradient_scaleInput, normalizeOutputRadius_scale b _ ht]
      using hh.2.2.1
  · have hh' := hh.2.2.2
    change scaleInput (b / ‖transportAveragedGradient Y (scaleInput t p)‖) (scaleInput t p) ∈ K at hh'
    rw [transportAveragedGradient_smul] at hh'
    have hscale : scaleInput (b / ‖t • transportAveragedGradient Y p‖) (scaleInput t p) =
        scaleInput (b / ‖transportAveragedGradient Y p‖) p := by
      simp only [scaleInput, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul]
      congr 3
      field_simp
    exact hscale ▸ hh'

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
